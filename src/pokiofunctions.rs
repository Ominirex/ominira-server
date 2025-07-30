use pqcrypto_sphincsplus::sphincssha2128fsimple::{
    keypair, detached_sign, verify_detached_signature,
    PublicKey, SecretKey, DetachedSignature
};
use pqcrypto_traits::sign::{PublicKey as PublicKeyTrait, SecretKey as SecretKeyTrait };
use pqcrypto_traits::sign::DetachedSignature as DetachedSignatureTrait;
use hex::decode;
use num_traits::identities::Zero;
use num_traits::ToPrimitive;
use num_traits::Num;
use serde::{Serialize, Deserialize};
use tiny_keccak::{Hasher, Keccak};
use sha2::{Sha256, Digest};
use num_bigint::BigUint;
use num_bigint::BigInt;
use hex;
use eyre::Result;
use sha3::{Keccak256};
use std::cmp::max; 
use eyre::anyhow;
use std::str::FromStr;
use sled::IVec;
use std::error::Error;
use serde_json::json;
use serde_json::Value;
use std::time::{SystemTime, UNIX_EPOCH};
use std::collections::HashMap;
use chrono::Local;
use std::collections::VecDeque;
use std::sync::Mutex;
use once_cell::sync::Lazy;
use std::io::{BufReader as iBufReader, Write as iWrite};
use std::net::{TcpListener as nTcpListener, TcpStream as nTcpStream};
use std::io::BufRead;
use monero::{blockdata::block::Block as MoneroBlock, consensus::encode::deserialize, consensus::encode::serialize};
use hex::FromHex;
use blake3;
use hex::encode;
use std::collections::HashSet;

use crate::constants::*;
use crate::merkle::*;
use crate::config;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct INTXO {
	pub txid: String,
	pub vout: u32,
	pub extrasize: String,
	pub extra: String,
	pub sequence: u64,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RawTransaction {
	pub inputcount: String,
	pub inputs: Vec<INTXO>,
	pub outputcount: String,
	pub outputs: Vec<(String, u64)>,
	pub fee: u64,
	pub sigpub: String,
	pub signature: String,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Block {
	pub height: u64,
	pub hash: String,
	pub prev_hash: String,
	pub timestamp: u64,
	pub nonce: String,
	pub transactions: String,
	// pub transactions: Vec<String>,
	pub miner: String,
	pub difficulty: u64,
	pub block_reward: u64,
	pub state_root: String,
	pub receipts_root: String,
	pub logs_bloom: String,
	pub extra_data: String,
	pub version: u32,
	pub signature: String,
}

#[derive(Debug)]
pub struct MinerInfo {
	pub id: String,
	pub target: String,
	pub hr: String,
	pub timestamp: u64,
	pub mined_blocks: u64,
}

pub static BLOCK_HISTORY: Lazy<Mutex<VecDeque<(u64, u64, u64, u8)>>> = Lazy::new(|| {
	Mutex::new(VecDeque::new())
});

pub fn add_block_to_history(height: u64, timestamp: u64, difficulty: u64, is_local: u8) {
	let mut history = BLOCK_HISTORY.lock().unwrap();
	let pos = history.iter().position(|(h, _, _, _)| *h < height).unwrap_or(history.len());
	history.insert(pos, (height, timestamp, difficulty, is_local));
	if history.len() > 600 {
		history.pop_back();
	}
}

pub fn sum_recent_difficulty(seconds: u64, is_local_filter: u8) -> u64 {
	let _now = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.expect("Time went backwards")
		.as_secs();
	let cutoff = config::actual_timestamp() - seconds;
	let history = BLOCK_HISTORY.lock().unwrap();
	history.iter()
		.filter(|(_, timestamp, _, is_local)| {
			*timestamp >= cutoff && (is_local_filter == 0 || *is_local == 1)
		})
		.map(|(_, _, difficulty, _)| *difficulty)
		.sum()
}

pub fn get_block_tx_hashes(blockhash: &str) -> Option<String> {
	let db = config::db();
	let blockhash_key = format!("txblock:{}", blockhash);
	let txs = db.get(blockhash_key).ok().flatten()?;
	let txs_str = String::from_utf8(txs.to_vec()).ok()?;
	Some(txs_str)
}

pub fn keccak256(data: &str) -> String {
	let mut hasher = Keccak::v256();
	let mut output = [0u8; 32];
	hasher.update(data.as_bytes());
	hasher.finalize(&mut output);
	hex::encode(output)
}

pub fn calculate_reward(height: u64) -> u64 {
    if height == 1 {
        10000000000000
    } else if height > 1 && height < 4200000 {
        1000000000
    } else if height >= 4200000 && height < 8400000 {
        5000000000
    } else if height >= 8400000 && height < 12600000 {
        2500000000
    } else {
        10000000
    }
}

pub fn calculate_rx_diff(height: u64) -> u64 {
	if height <= 17 {
		10000
	} else {
		let expectedtime: u64 = 16 * 120;
		let Some((blocktime, totaldiff)) = get_block_range_analysis(height-1) else { return 1200000 };
		let x = (expectedtime * totaldiff) / blocktime / 16;
		max(12000, x)
	}
}


pub fn get_latest_block_info() -> (u64, String, u64) {
	(config::actual_height(), config::actual_hash(), config::actual_timestamp())
}

pub fn set_latest_block_info() {
	let db = config::db();
	if let Some(latest) = db.get("chain:latest_block").unwrap() {
		let latest_height = u64::from_be_bytes(latest.as_ref().try_into().unwrap());
		let block_key = format!("block:{:08}", latest_height);
		if let Some(block_data) = db.get(block_key).unwrap() {
			let block: Block = bincode::deserialize(&block_data).unwrap();
			config::update_actual_height(block.height);
			config::update_actual_hash(block.hash);
			config::update_actual_timestamp(block.timestamp);
			return;
		}
	}
	config::update_actual_height(0);
	config::update_actual_hash("0000000000000000000000000000000000000000000000000000000000000000".to_string());
	config::update_actual_timestamp(0);
}

pub fn generate_reward_tx(nonce: &str, miner_address: &str, reward_amount: u64) -> eyre::Result<String> {

	let (height, _, _) = get_latest_block_info();
	let height_hex = format!("{:x}", height);
	let mut extra = format!("{}{}", height_hex, nonce);
	if extra.len() % 2 != 0 {
		extra = format!("0{}", extra);
	}
	let extra_len = extra.len();
	let mut extra_len_hex = format!("{:x}", extra_len);
	if extra_len_hex.len() % 2 != 0 {
		extra_len_hex = format!("0{}", extra_len_hex);
	}

	let intxo = INTXO {
		txid: "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
		vout: 999,
		extrasize: extra_len_hex,
		extra: extra,
		sequence: 0
	};
	
	let outputs = vec![(miner_address.to_string(), reward_amount)];
	
	let rawtx = RawTransaction {
		inputcount: "01".to_string(),
		inputs: vec![intxo.clone()],
		outputcount: "01".to_string(),
		outputs,
		fee: 0,
		sigpub: "".to_string(),
		signature: "".to_string()
	};
	
	let tx_binary = bincode::serialize(&rawtx).unwrap(); // Necesitas `bincode`
	let rawtx_hex = hex::encode(tx_binary);
	let b3_tx_hash = blake3::hash(rawtx_hex.as_bytes());
	let tx_hash = hex::encode(b3_tx_hash.as_bytes());

	Ok(rawtx_hex.to_string())
}

pub fn get_mining_template(miner: &str) -> String {
	let (height, prevhash, _ts) = get_latest_block_info();
	let diff_dec = calculate_rx_diff(height + 1);
	let diff = format!("{:016X}", diff_dec);
	let nonce = "0000"; //extra_nonce
	let reward_amount = calculate_reward(height + 1);
	let raw_tx: String;
	match generate_reward_tx(nonce, miner, reward_amount) {
		Ok(tx) => {
			raw_tx = tx;
		}
		Err(_e) => {
			raw_tx = String::new();
		}
	}
	format!("0000000000000000-{}-{}-{}-{}-{}", diff, height+1, prevhash, miner, raw_tx).to_lowercase()
}

pub fn fix_blockchain(last_valid_height: u64) -> Option<Block> {
	if config::async_status() == 0
	{
		while config::sync_status() == 1 {
			std::thread::sleep(std::time::Duration::from_millis(10));
		}
	}
	config::update_sync(1);
	if last_valid_height > UNLOCK_OFFSET {
		let db = config::db();
		let latest = db.get("chain:latest_block").unwrap();
		if let Some(latest) = latest {
			let latest_height = u64::from_be_bytes(latest.as_ref().try_into().unwrap());
			for h in last_valid_height + 1..=latest_height {
				let key_to_delete = format!("block:{:08}", h);
				if let Some(block_data) = db.get(&key_to_delete).unwrap() {
					if let Ok(block) = bincode::deserialize::<Block>(&block_data) {
						let parts: Vec<&str> = block.extra_data.split(':').collect();
						if parts.len() >= 2 {
							let blobmining = parts[0];
							let blob_prefix_mining = &blobmining[..78.min(blobmining.len())];
							let blobsave = format!("{}{}", blob_prefix_mining, block.nonce);
							let pooldb = config::pooldb();
							let _ = pooldb.remove(blobsave.as_str());
						}
					}
				}
				db.remove(&key_to_delete).unwrap();
			}
			let _ = db.insert("chain:latest_block", &last_valid_height.to_be_bytes()).unwrap();
			let block_key = format!("block:{:08}", last_valid_height);
			if let Some(block_data) = db.get(block_key).unwrap() {
				let block: Block = bincode::deserialize(&block_data).unwrap();
				config::update_actual_height(block.height);
				config::update_actual_hash(block.hash);
				config::update_actual_timestamp(block.timestamp);
			}
			print_log_message(format!("Blockchain reordered"), 1);
		}
	}
	config::update_sync(0);
	None
}

pub fn preload_block_history() {
	let db = config::db();
	if let Some(latest) = db.get("chain:latest_block").unwrap() {
		let mut height = u64::from_be_bytes(latest.as_ref().try_into().unwrap());
		for _ in 0..600 {
			let key = format!("block:{:08}", height);
			if let Some(block_data) = db.get(&key).unwrap() {
				if let Ok(block) = bincode::deserialize::<Block>(&block_data) {
					let is_local = 0;
					add_block_to_history(block.height, block.timestamp, block.difficulty, is_local);
				}
			}
			if height == 0 {
				break;
			} else {
				height -= 1;
			}
		}
	}
}

pub fn check_integrity() -> Option<Block> {
	let db = config::db();
	if let Some(latest) = db.get("chain:latest_block").unwrap() {
		let latest_height = u64::from_be_bytes(latest.as_ref().try_into().unwrap());
		let mut block_key = format!("block:{:08}", latest_height);

		for i in 0..UNLOCK_OFFSET {
			if let Some(block_data) = db.get(&block_key).unwrap() {
				let block: Block = bincode::deserialize(&block_data).unwrap();

				if i == UNLOCK_OFFSET - 1 {
					return Some(block);
				}

				if block.prev_hash.is_empty() {
					break;
				}

				if let Some(prev_height) = db.get(format!("hash:{}", block.prev_hash)).unwrap() {
					let prev_height = u64::from_be_bytes(prev_height.as_ref().try_into().unwrap());
					let prev_block_key = format!("block:{:08}", prev_height);

					if let Some(prev_block_data) = db.get(&prev_block_key).unwrap() {
						let prev_block: Block = bincode::deserialize(&prev_block_data).unwrap();

						if prev_block.hash != block.prev_hash {
							print_log_message(format!("Reordering blockchain..."), 1);
							config::update_full_sync(1);
							fix_blockchain(block.height - FIX_BC_OFFSET);
							config::update_full_sync(0);
							return None;
						}
						block_key = prev_block_key;
					} else {
						config::update_full_sync(1);
						fix_blockchain(block.height - FIX_BC_OFFSET);
						config::update_full_sync(0);
						break;
					}
				} else {
					config::update_full_sync(1);
					fix_blockchain(block.height - FIX_BC_OFFSET);
					config::update_full_sync(0);
					break;
				}
			} else {
				break;
			}
		}
	}
	None
}

pub fn get_block_range_analysis(height: u64) -> Option<(u64, u64)> {
	let db = config::db();
	if height <= 16 {
		return None;
	}
	let (start, end) = (height - 16, height);
	let mut timestamps = Vec::new();
	let mut diff_count = 0;
	for h in start..end {
		let key = format!("block:{:08}", h);
		if let Some(data) = db.get(&key).unwrap() {
			let block: Block = bincode::deserialize(&data).unwrap();
			timestamps.push(block.timestamp);
			let diff = block.difficulty as u64;
			diff_count = diff_count + diff;
		} else {
			return None;
		}
	}
	if let (Some(first), Some(last)) = (timestamps.first(), timestamps.last()) {
		let duration = last.saturating_sub(*first);

		Some((
			duration,
			diff_count
		))
	} else {
		None
	}
}



pub fn get_block_as_json(block_number: u64) -> Value {
	let db = config::db();
	let block_key = format!("block:{:08}", block_number);

	if let Some(block_data) = db.get(block_key).ok().flatten() {
		if let Ok(block) = bincode::deserialize::<Block>(&block_data) {
			return serde_json::to_value(block).unwrap()
		}
	}

	json!(null)
}

pub fn print_log_message(message: String, level: u64) {
	let actual_level = config::log_level();
	if level <= actual_level {
		let now = Local::now();
		let timestamp = now.format("[%d %b %H:%M:%S]").to_string();
		println!("{} {}", timestamp, message);
	}
}

pub fn get_next_blocks(start_height: u64) -> Value {
	let mut blocks = Vec::new();
	let db = config::db();
	for i in 0..1000 {
		let height = start_height + i;
		let key = format!("block:{:08}", height);

		if let Some(serialized_block) = db.get(&key).unwrap() {
			if let Ok(block) = bincode::deserialize::<Block>(&serialized_block) {
				blocks.push(block);
			}
		} else {
			break;
		}
	}
	json!(blocks)
}

pub fn get_rawtx_status(rawtx: &str) -> Option<String> {
	let db = config::db();
	let rawtx_key = format!("{}", rawtx);
	let txs = db.get(rawtx_key).ok().flatten()?;
	let txs_str = String::from_utf8(txs.to_vec()).ok()?;
	Some(txs_str)
}

pub fn get_receipt_info(_txhash: &str) -> Option<(String, u64)> {
	/*let db = config::db();
	let receipt_key = format!("receipt:{}", txhash);
	let receiptblock_key = format!("receiptblock:{}", txhash);
	let receipt = db.get(receipt_key).ok().flatten()?;
	let block_bytes = db.get(receiptblock_key).ok().flatten()?;
	let receipt_str = String::from_utf8(receipt.to_vec()).ok()?;
	let txheight = u64::from_be_bytes(block_bytes.as_ref().try_into().ok()?);*/
	let (actual_height, actual_hash, _) = get_latest_block_info();
	//Some((receipt_str, txheight))
	Some((actual_hash, actual_height - 1))
}

pub fn store_raw_transaction(raw_tx: String) -> String {
    let mempooldb = config::mempooldb();
    let db = config::db();

    if let Some(status) = get_rawtx_status(&raw_tx) {
        if status == "confirmed" {
            let _ = mempooldb.remove(&raw_tx);
            return String::new();
        }
    }

    let _ = mempooldb.insert(raw_tx.clone(), IVec::from(raw_tx.as_bytes()));
    
    mempooldb.flush().expect("Failed to flush mempool DB");
    db.flush().expect("Failed to flush main DB");

    let b3_tx_hash = blake3::hash(raw_tx.as_bytes());
    hex::encode(b3_tx_hash.as_bytes())
}

pub fn difficulty_to_target(difficulty: u64) -> String {
	let max_target = 0xffff_ffff_u64;
	let target = max_target / difficulty;
	let target_bytes = target.to_le_bytes();
	hex::encode(&target_bytes[..4])
}

pub fn compute_randomx_hash(blob_hex: &str, nonce_hex: &str) -> Result<String, Box<dyn std::error::Error + Send + Sync>> {
	let mut blob = hex::decode(blob_hex)?;
	let nonce_bytes = hex::decode(nonce_hex)?;
	if nonce_bytes.len() != 4 {
		return Err("Invalid nonce".into());
	}
	if blob.len() < 43 {
		return Err("Invalid blob".into());
	}
	blob[39..43].copy_from_slice(&nonce_bytes);
	let hash = config::with_vm(|vm| vm.calculate_hash(&blob))?;
	Ok(hex::encode(hash))
}

pub fn dynamic_compute_randomx_hash(blob_hex: &str, nonce_hex: &str, seed_hex: &str) -> Result<String, Box<dyn std::error::Error + Send + Sync>> {
	
	let seed = match config::current_dynamic_seed() {
		Some(seed) => seed,
		None => "".to_string(),
	};
	
	if seed_hex != seed {
		config::set_dynamic_vm(seed_hex);
		print_log_message(format!("New dynamic seed: {:?}", config::current_dynamic_seed()), 1);
	}

	let mut blob = hex::decode(blob_hex)?;
	let nonce_bytes = hex::decode(nonce_hex)?;
	if nonce_bytes.len() != 4 {
		return Err("Invalid nonce".into());
	}
	if blob.len() < 43 {
		return Err("Invalid blob".into());
	}
	blob[39..43].copy_from_slice(&nonce_bytes);

	let hash_result = config::with_dynamic_vm(|vm| vm.calculate_hash(&blob));

	match hash_result {
		Some(Ok(hash)) => Ok(hex::encode(hash)),
		Some(Err(e)) => Err(Box::new(e)),
		None => Err("Dynamic VM not initialized".into()),
	}
}


pub fn rx_hash_to_difficulty(hash_hex: &str) -> Result<u64, Box<dyn std::error::Error>> {
	let hash_bytes = hex::decode(hash_hex)?;
	if hash_bytes.len() != 32 {
		return Err("Invalid hash".into());
	}
	let mut reversed_bytes = hash_bytes.clone();
	reversed_bytes.reverse();
	let hash_num = BigUint::from_bytes_be(&reversed_bytes);
	let base_diff = BigUint::from_bytes_be(&[0xff; 32]);
	let hash_diff = if hash_num.is_zero() {
		BigUint::zero()
	} else {
		&base_diff / hash_num
	};
	Ok(hash_diff.to_u64().unwrap_or(u64::MAX))
}

pub fn save_block_to_db(new_block: &mut Block, checkpoint: u8) -> Result<(), Box<dyn Error>> {
	if config::async_status() == 0
	{
		while config::sync_status() == 1 {
			std::thread::sleep(std::time::Duration::from_millis(10));
		}
	}
	config::update_sync(1);
	let result = (|| {
		let db = config::db();
		let utxodb = config::utxodb();
		let pooldb = config::pooldb();
		let mempooldb = config::mempooldb();
		let (actual_height, prev_hash, ts) = get_latest_block_info();
		let expected_height: u64 = actual_height.clone() + 1;
		if expected_height == new_block.height && prev_hash == new_block.prev_hash {
			if  checkpoint > 0
			{
				if new_block.timestamp < ts {
					return Err(format!(
						"Invalid timestamp for block {}: expected >= {}, got {}",
						new_block.height, ts, new_block.timestamp
					).into());
				}
				let receipts_root = merkle_tree(&new_block.transactions);
				if receipts_root != new_block.receipts_root {
					return Err(format!(
						"Merkle check mismatch at block {}: expected {}, got {}",
						new_block.height, receipts_root, new_block.receipts_root
					).into());
				}
				let rx_difficulty = calculate_rx_diff(actual_height + 1);
				if rx_difficulty != new_block.difficulty {
					return Err(format!(
						"Difficulty mismatch at block {}: expected {}, got {}",
						new_block.height, rx_difficulty, new_block.difficulty
					).into());
				}
				let hash = new_block.hash.clone();
				new_block.signature = "".to_string();
				new_block.hash = "".to_string();
				let unhashed_serialized_block = serde_json::to_string_pretty(&new_block).unwrap();
				let block_hash = keccak256(&unhashed_serialized_block);
				if hash != block_hash {
					return Err(format!(
						"Hash mismatch for block {}: expected {}, got {}",
						new_block.height, block_hash, hash
					).into());
				}
				new_block.hash = block_hash;
				let unsigned_serialized_block = serde_json::to_string_pretty(&new_block).unwrap();
				let block_signature = keccak256(&unsigned_serialized_block);
				new_block.signature = block_signature;
				let diff_hex = format!("{:016X}", new_block.difficulty);
				let tx_parts: Vec<&str> = new_block.transactions.split('-').collect();
				let first_two_txs = tx_parts.iter().take(1).cloned().collect::<Vec<&str>>().join("-");
				let mut seedhash = "";
				if new_block.difficulty == rx_difficulty {
					let ts_hex = format!("{:010x}", ts);
					let target = difficulty_to_target(new_block.difficulty);
					let rx_first_two_txs = tx_parts.iter().take(1).cloned().collect::<Vec<&str>>().join("");
					let rx_blob = match new_block.extra_data.len() {
						0..=3 => format!(
							"0101{}{}0000000001{}{}",
							ts_hex,
							prev_hash,
							target,
							rx_first_two_txs
						),
						4 => format!(
							"{}{}{}0000000001{}{}",
							new_block.extra_data,
							ts_hex,
							prev_hash,
							target,
							rx_first_two_txs
						),
						_ => {
							let parts: Vec<&str> = new_block.extra_data.split(':').collect();
							if parts.len() == 3 {
								let (blobmining, blobblock, blobseed) = (parts[0], parts[1], parts[2]);
								let blob_prefix_mining = &blobmining[..78.min(blobmining.len())];
								let blobsave = format!("{}{}", blob_prefix_mining, new_block.nonce);
								let blob_prefix_block = &blobblock[..78.min(blobblock.len())];
								if blob_prefix_mining != blob_prefix_block {
									return Err(format!("Blobmining and Blobblock prefix mismatch").into());
								}
								if pooldb.contains_key(&blobsave)? {
									return Err(format!("Duplicated mining blob").into());
								}
								//println!("blobsave: {}", blobsave);
								let _ = pooldb.insert(blobsave.clone(), IVec::from(blobsave.as_bytes()));
								let blob_bytes = Vec::from_hex(blobblock)?;
								let mut block: MoneroBlock = deserialize(&blob_bytes)?;
								{
									if block.header.major_version < monero::VarInt(16) {
										return Err(format!("Invalid major version").into());
									}
									if block.header.timestamp < monero::VarInt(ts-240) || block.header.timestamp > monero::VarInt(ts+3600) {
										return Err(format!("Invalid block date").into());
									}
								}
								let valid_seedhash = blobseed.len() == 64 && hex::decode(blobseed).is_ok();
								let valid_blobs = blobmining.len() > 64 && blobblock.len() > blobmining.len();
								if valid_seedhash && valid_blobs {
									seedhash = blobseed;
									blobmining.to_string()
								} else {
									return Err(format!("Invalid merged blob data").into());
								}
							} else if parts.len() == 2 {
								let (blobmining, blobseed) = (parts[0], parts[1]);
								let blob_prefix_mining = &blobmining[..78.min(blobmining.len())];
								let blobblock = format!("{}{}{}", blob_prefix_mining, new_block.nonce, MONERO_RX_RANDOM_DATA);
								let blobsave = format!("{}{}", blob_prefix_mining, new_block.nonce);
								if pooldb.contains_key(&blobsave)? {
									return Err(format!("Duplicated mining blob").into());
								}
								let _ = pooldb.insert(blobsave.clone(), IVec::from(blobsave.as_bytes()));
								let blob_bytes = Vec::from_hex(&blobblock)?;
								let mut block: MoneroBlock = deserialize(&blob_bytes)?;
								{
									if block.header.major_version < monero::VarInt(16) {
										return Err(format!("Invalid major version").into());
									}
									if block.header.timestamp < monero::VarInt(ts-240) || block.header.timestamp > monero::VarInt(ts+3600) {
										return Err(format!("Invalid block date").into());
									}
								}
								let valid_seedhash = blobseed.len() == 64 && hex::decode(blobseed).is_ok();
								let valid_blobs = blobmining.len() > 64 && hex::decode(blobmining).is_ok();
								if valid_seedhash && valid_blobs {
									seedhash = blobseed;
									blobmining.to_string()
								} else {
									return Err(format!("Invalid merged blob data").into());
								}
							} else {
								return Err(format!("Invalid extra_data field").into());
							}
						}
					};
					let mut rx_hashdiff = 0;
					
					if let Ok(mut stream) = nTcpStream::connect("127.0.0.1:16789") {
						let request = json!({
							"blob": &rx_blob, 
							"nonce": &new_block.nonce,
							"seed": &seedhash
						});
						if let Ok(req_str) = serde_json::to_string(&request) {
							let _ = stream.write_all(req_str.as_bytes());
							let _ = stream.write_all(b"\n");
							let mut reader = iBufReader::new(stream);
							let mut response = String::new();
							if let Ok(_) = reader.read_line(&mut response) {
								if let Ok(json_resp) = serde_json::from_str::<serde_json::Value>(&response) {
									if json_resp["status"] == "ok" {
										if let Some(hash_str) = json_resp["hash"].as_str() {
											if let Ok(diff) = rx_hash_to_difficulty(hash_str) {
												rx_hashdiff = diff;
											}
										}
									}
								}
							}
						}
					}
					if new_block.extra_data.len() > 4 && rx_hashdiff > MAX_MONERO_DIFF {
						return Err(format!(
							"Difficulty too high for block {}",
							new_block.height
						).into());
					}
					if rx_hashdiff < rx_difficulty {
						return Err(format!(
							"Difficulty mismatch for block {}: expected {}, got {}",
							new_block.height, rx_difficulty, rx_hashdiff
						).into());
					}
				}
				/*let unsigned_serialized_block = serde_json::to_string_pretty(&new_block).unwrap();
				let block_signature = keccak256(&unsigned_serialized_block);
				new_block.signature = block_signature;
				let serialized_block = bincode::serialize(&new_block).unwrap();
				let unsigned_serialized_block = serde_json::to_string_pretty(&new_block).unwrap();*/
			}
						let block_transactions: Vec<&str> = new_block.transactions.split('-').collect();
			let mut txcount: u8 = 0;
			let mut sender_address: String = "".to_string();
			let mut pending_inputs: Vec<(String, Vec<u8>)> = Vec::new();
			let mut pending_outputs: Vec<(String, Vec<u8>)> = Vec::new();
			let mut spent_utxos_in_block: HashSet<String> = HashSet::new();

			for tx_str in block_transactions {
				if let Err(e) = mempooldb.remove(&tx_str) { eprintln!("Error deleting mempool entry: {:?}", e); }
				if tx_str == "" { continue; }
				if db.contains_key(tx_str)? { continue; }
				if let Ok(tx_bytes) = hex::decode(&tx_str) {
					if let Ok(raw_tx) = bincode::deserialize::<RawTransaction>(&tx_bytes) {
						if txcount > 0 {
							let rtx = RawTransaction {
								inputcount: raw_tx.inputcount.clone(),
								inputs: raw_tx.inputs.clone(),
								outputcount: raw_tx.outputcount.clone(),
								outputs: raw_tx.outputs.clone(),
								fee: raw_tx.fee,
								sigpub: raw_tx.sigpub.clone(),
								signature: "".to_string(),
							};
							
							let tx_binary = bincode::serialize(&rtx)
								.map_err(|e| format!("Failed to serialize transaction: {}", e))?;
							let tx_hash = blake3::hash(&tx_binary);
							
							let bytes_decoded_signature = hex::decode(&raw_tx.signature)
								.map_err(|e| format!("Error decoding signature: {}", e))?;
							let decoded_signature = <pqcrypto_sphincsplus::sphincssha2128fsimple::DetachedSignature as DetachedSignatureTrait>::from_bytes(&bytes_decoded_signature)
								.map_err(|e| format!("Error in signature reconstruction: {}", e))?;
							
							let pk_bytes = hex::decode(&raw_tx.sigpub)
								.map_err(|e| format!("Invalid pubkey: {}", e))?;
							let pk = PublicKey::from_bytes(&pk_bytes)
								.map_err(|e| format!("Invalid pubkey format: {}", e))?;
							
							let address_hash = blake3::hash(pk.as_bytes());
							sender_address = hex::encode(address_hash.as_bytes());

							verify_detached_signature(&decoded_signature, tx_hash.as_bytes(), &pk)
								.map_err(|e| format!("Invalid signature: {}", e))?;

							let mut total_inputs_amount = 0u64;
							for input in &raw_tx.inputs {
								let key = format!("{}:{}", input.txid, input.vout);
								
								if spent_utxos_in_block.contains(&key) {
									return Err(format!("Double spending detected in block for UTXO: {}", key).into());
								}
								
								if let Some(utxo_bytes) = utxodb.get(&key)? {
									let utxo_value: serde_json::Value = serde_json::from_slice(&utxo_bytes)
										.map_err(|e| format!("Failed to parse UTXO JSON: {}", e))?;
									let amount = utxo_value["amount"].as_u64().ok_or("Invalid amount in UTXO")?;
									let owner = utxo_value["address"].as_str().ok_or("Invalid address in UTXO")?;
										
									total_inputs_amount += amount;
									
									if sender_address != owner {
										return Err("TX with invalid UTXO".into());
									}
									
									let spent_value = serde_json::json!({
										"address": utxo_value["address"].as_str().ok_or("Invalid address in UTXO")?,
										"amount": 0
									});
									pending_inputs.push((key.clone(), spent_value.to_string().into_bytes()));
									spent_utxos_in_block.insert(key);
								} else {
									return Err("Referenced UTXO not found".into());
								}
							}
							
							let total_outputs_amount: u64 = raw_tx.outputs.iter().map(|(_, amount)| amount).sum();
							let required_amount = total_outputs_amount + raw_tx.fee;
							
							if total_inputs_amount < required_amount {
								return Err(format!(
									"Insufficient funds: inputs {} < outputs + fee {}",
									total_inputs_amount, required_amount
								).into());
							}
						} else {
							let total_outputs_amount: u64 = raw_tx.outputs.iter().map(|(_, amount)| amount).sum();
							let required_amount = total_outputs_amount + raw_tx.fee;
							
							if new_block.block_reward < required_amount {
								return Err(format!(
									"Insufficient funds: inputs {} < outputs + fee {}",
									new_block.block_reward, required_amount
								).into());
							}
						}
						
						for (vout, (output_address, amount)) in raw_tx.outputs.iter().enumerate() {
							let b3_tx_hash = blake3::hash(&tx_str.as_bytes());
							let tx_hash = hex::encode(b3_tx_hash.as_bytes());
							let key = format!("{}:{}", tx_hash, vout);
							let value = serde_json::json!({
								"address": output_address,
								"amount": amount
							});
							let value_str = value.to_string();
							pending_outputs.push((key, value_str.into_bytes()));
						}
					}
				}
				txcount = txcount + 1;
			}


			for (key, value) in pending_inputs {
				utxodb.insert(key, value)?;
			}

			for (key, value) in pending_outputs {
				utxodb.insert(key, value)?;
			}
			let serialized_block = bincode::serialize(new_block)?;
			let _ = db.insert(format!("block:{:08}", new_block.height), serialized_block)?;
			let _ = db.insert(format!("hash:{}", new_block.hash), &new_block.height.to_be_bytes())?;
			let _ = db.insert("chain:latest_block", &new_block.height.to_be_bytes())?;
			config::update_actual_height(new_block.height.clone());
			config::update_actual_hash(new_block.hash.clone());
			config::update_actual_timestamp(new_block.timestamp.clone());
			print_log_message(format!("Block {} successfully saved in DB", new_block.height), 3);
			let _ = check_integrity();
		}	
		Ok(())
	})();
	config::update_sync(0);
	result
}

pub fn save_mined_block(new_block: &mut Block, miningid: &str) -> Result<(), Box<dyn Error>> {
	let result = (|| {
		let db = config::pooldb();
		new_block.miner = new_block.miner.to_lowercase();
		let serialized_block = bincode::serialize(&new_block)?;
		db.insert(format!("block:{:08}", new_block.height), serialized_block)?;
		let counter_key = format!("minedblocks:{}:{}", new_block.miner, miningid);
		let current_count = db
			.get(&counter_key)?
			.map(|val| {
				let bytes: [u8; 8] = val.as_ref().try_into().unwrap_or([0u8; 8]);
				u64::from_be_bytes(bytes)
			})
			.unwrap_or(0);
		let new_count = current_count + 1;
		db.insert(counter_key, &new_count.to_be_bytes())?;
		print_log_message(
			format!(
				"Block {} saved. Total blocks mined by {}: {}",
				new_block.height,
				new_block.miner,
				new_count
			),
			3,
		);

		Ok(())
	})();
	result
}

pub fn get_all_miningids_for_miner(miner: &str) -> Result<Vec<(String, u64)>, Box<dyn std::error::Error>> {
	let db = config::pooldb();
	let miner_lower = miner.to_lowercase();
	let prefix = format!("minedblocks:{}:", miner_lower);
	let mut results = Vec::new();
	for item in db.scan_prefix(prefix.as_bytes()) {
		let (key, value) = item?;
		let key_str = std::str::from_utf8(&key)?;
		let parts: Vec<&str> = key_str.splitn(3, ':').collect();
		if parts.len() == 3 {
			let miningid = parts[2].to_string();
			let count_bytes: [u8; 8] = value.as_ref().try_into().unwrap_or([0u8; 8]);
			let count = u64::from_be_bytes(count_bytes);
			results.push((miningid, count));
		}
	}
	Ok(results)
}

pub fn get_blocks_paginated(limit: usize, offset: usize) -> Result<Vec<Block>, Box<dyn std::error::Error>> {
	let db = config::pooldb();
	let mut blocks = Vec::new();
	let mut skipped = 0;
	for item in db.iter().rev() {
		let (key, value) = item?;
		let key_str = std::str::from_utf8(&key)?;
		if key_str.starts_with("block:") {
			if skipped < offset {
				skipped += 1;
				continue;
			}

			let block: Block = bincode::deserialize(&value)?;
			blocks.push(block);

			if blocks.len() >= limit {
				break;
			}
		}
	}
	Ok(blocks)
}

pub fn get_mempool_records() -> Result<serde_json::Value, sled::Error> {
	let mut records = Vec::new();
	let mempooldb = config::mempooldb();
	let db = config::db();

	for result in mempooldb.iter() {
		if let Ok((_, value)) = result {
			if let Ok(raw_tx) = std::str::from_utf8(&value) {
				if db.contains_key(raw_tx)? {
					if let Err(e) = mempooldb.remove(&raw_tx) {
						eprintln!("Error deleting mempool entry: {:?}", e);
					}
					continue;
				}
				records.push(raw_tx.to_string());
			}
		}
	}
	Ok(json!(records))
}

pub fn save_miner(miner: &str, id: &str, coins: &str, hr: &str) {
	let db = config::pooldb();
	let timestamp = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.unwrap()
		.as_millis();

	let miner_data = json!({
		"miner": miner,
		"id": id,
		"target" : coins,
		"hr" : hr,
		"timestamp": timestamp
	});

	let key = format!("miner_{}", id);
	let _ = db.insert(key, serde_json::to_vec(&miner_data).unwrap()).unwrap();
}

pub fn count_active_miners(seconds: u64) -> HashMap<String, Vec<MinerInfo>> {
	let db = config::pooldb();
	let mut miners_map: HashMap<String, Vec<MinerInfo>> = HashMap::new();
	let now = SystemTime::now()
		.duration_since(UNIX_EPOCH)
		.unwrap()
		.as_millis();
	let mut miningid_block_counts: HashMap<String, u64> = HashMap::new();
	for item in db.iter() {
		if let Ok((key, value)) = item {
			let key_str = String::from_utf8_lossy(&key);
			if key_str.starts_with("miner_") {
				if let Ok(json) = serde_json::from_slice::<Value>(&value) {
					if let (Some(miner), Some(id), Some(target), Some(hr), Some(timestamp)) = (
						json["miner"].as_str(),
						json["id"].as_str(),
						json["target"].as_str(),
						json["hr"].as_str(),
						json["timestamp"].as_u64(),
					) {
						if now - timestamp as u128 <= (seconds * 1000) as u128 {
							let miner_str = miner.to_string();
							if !miningid_block_counts.contains_key(id) {
								if let Ok(mined_blocks_data) = get_all_miningids_for_miner(miner) {
									for (miningid, count) in mined_blocks_data {
										miningid_block_counts.insert(miningid, count);
									}
								}
							}
							let mined_blocks = *miningid_block_counts.get(id).unwrap_or(&0);

							let miner_info = MinerInfo {
								id: id.to_string(),
								target: target.to_string(),
								hr: hr.to_string(),
								timestamp,
								mined_blocks,
							};

							miners_map.entry(miner_str)
								.or_insert(Vec::new())
								.push(miner_info);
						}
					}
				}
			}
		}
	}

	miners_map
}
