use pqcrypto_sphincsplus::sphincssha2128fsimple::{
    keypair, detached_sign, verify_detached_signature,
    PublicKey, SecretKey, DetachedSignature
};
use std::collections::HashSet;
use pqcrypto_traits::sign::{PublicKey as PublicKeyTrait, SecretKey as SecretKeyTrait };
use pqcrypto_traits::sign::DetachedSignature as DetachedSignatureTrait;
use sled;
use serde::{Serialize, Deserialize};
use std::time::{SystemTime, UNIX_EPOCH};
use tiny_keccak::{Hasher, Keccak};
use sha2::{Sha256, Digest};
use hex;
use std::str::FromStr;
use eyre::Result;
use futures::future::join_all;
use tokio;
use warp::Filter;
use serde_json::json;
use sha3::{Keccak256};
use eyre::anyhow;
use std::thread;
use serde_json::Value;
use std::cmp::max; 
use nng::{Socket, Protocol};
use std::sync::{Arc, Mutex};
use reqwest::Client;
use sled::IVec;
use nng::options::protocol::pubsub::Subscribe;
use nng::options::Options;
use std::error::Error;
use std::collections::HashMap;
use std::env;
use std::time::{Instant, Duration};
use std::io::{self, BufRead};
use std::process;
use warp::filters::addr::remote;
use tokio::time::{sleep, Duration as tDuration};
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader, AsyncBufReadExt};
use dashmap::DashMap;
use uuid::Uuid;
use tokio::sync::{Mutex as tMutex};
use std::io::{BufReader as iBufReader, Write as iWrite};
use std::net::{TcpListener as nTcpListener, TcpStream as nTcpStream};
use blake3;

mod config;
mod constants;
use constants::*;
mod pokiofunctions;
use pokiofunctions::*;
use pokiofunctions::{MinerInfo, Block};
mod merkle;
use merkle::*;
mod nngutils;
use nngutils::*;

use randomx_rs::{RandomXCache, RandomXVM, RandomXFlag};
use hex::decode;
use hex::encode;
use std::convert::TryInto;
use once_cell::sync::Lazy;
use tokio::net::tcp::OwnedWriteHalf;

pub struct JobState {
    pub worker_id: String,
    pub job_id: String,
    pub miner: String,
    pub difficulty: u64,
    pub target: String,
    pub shares: u64,
    pub coins: u64,
	pub blob: String,
    pub writer: Arc<tMutex<OwnedWriteHalf>>,
}

type SharedState = Arc<DashMap<String, JobState>>;

static HOST: &str = "0.0.0.0";
static PORT: u16 = 9876;

pub fn start_local_hash_server() -> std::io::Result<()> {
    let listener = nTcpListener::bind("127.0.0.1:16789")?;
	print_log_message(format!("RandomX hash server listening on 127.0.0.1:16789"), 1);

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                handle_hash_connection(stream);
            }
            Err(e) => {
                eprintln!("Error accepting connection: {}", e);
            }
        }
    }

    Ok(())
}

fn handle_hash_connection(mut stream: nTcpStream) {
    let peer = stream.peer_addr().unwrap_or_else(|_| "unknown".parse().unwrap());

    let mut reader = iBufReader::new(stream.try_clone().unwrap());
    let mut request_line = String::new();

    if reader.read_line(&mut request_line).is_ok() {
        if let Ok(json_req) = serde_json::from_str::<Value>(&request_line) {
            let blob = json_req["blob"].as_str().unwrap_or("");
            let nonce = json_req["nonce"].as_str().unwrap_or("");
			let seed = json_req["seed"].as_str().unwrap_or("");
			let response;
			if seed == "" {
				response = match compute_randomx_hash(blob, nonce) {
					Ok(hash) => json!({
						"status": "ok",
						"hash": hash,
					}),
					Err(e) => json!({
						"status": "error",
						"message": e.to_string(),
					}),
				};
			} else {
				response = match dynamic_compute_randomx_hash(blob, nonce, seed) {
					Ok(hash) => json!({
						"status": "ok",
						"hash": hash,
					}),
					Err(e) => json!({
						"status": "error",
						"message": e.to_string(),
					}),
				};
			}

            let response_text = serde_json::to_string(&response).unwrap() + "\n";
            let _ = stream.write_all(response_text.as_bytes());
        } else {
            let _ = stream.write_all(b"{\"status\":\"error\",\"message\":\"invalid json\"}\n");
        }
    }
}


pub async fn start_block_monitor(state: SharedState) {
    tokio::spawn(async move {
        let mut last_known_height = 0;

        loop {
            sleep(tDuration::from_millis(25)).await;

            let (height, hash, ts) = get_latest_block_info();
            if height != last_known_height {
                last_known_height = height;
                broadcast_new_job(&state, height, hash, ts).await;
            }
        }
    });
}

pub async fn broadcast_new_job(state: &SharedState, height: u64, hash: String, ts: u64) {
    use tokio::io::AsyncWriteExt;

    let ts_hex = format!("{:010x}", ts);
    let nonce = "0000";
    for mut entry in state.iter_mut() {
        let job_state = entry.value_mut();
		let (ah, _, _) = get_latest_block_info();
		let extra_data = job_state.worker_id.replace("-", "")[..4].to_lowercase();
		
        let difficulty = calculate_rx_diff(ah + 1);
        let target = difficulty_to_target(difficulty);
        let job_id = Uuid::new_v4().to_string();

		let reward_amount = calculate_reward(height + 1);
        let raw_tx = generate_reward_tx(nonce, &job_state.miner, reward_amount).unwrap_or_default();

        let blob = format!(
            "{}{}{}0000000001{}{}",
			extra_data,
            ts_hex,
            hash,
            target,
            raw_tx
        );

        job_state.job_id = job_id.clone();
        job_state.target = target.clone();
		job_state.blob = blob.to_string();

        let response = json!({
            "jsonrpc": "2.0",
            "method": "job",
            "params": {
                "blob": blob,
                "job_id": job_id,
                "target": target,
                "height": height + 1,
                "seed_hash": "b38737d8f08e1b0b033611bb268bd79b236c3089a756b79906eff085c67a7e31",
                "algo": "rx/0"
            }
        });

        let response_text = serde_json::to_string(&response).unwrap() + "\n";

        let mut writer = job_state.writer.lock().await;
        let _ = writer.write_all(response_text.as_bytes()).await;
    }
}

pub async fn start_server() -> Result<(), Box<dyn Error>> {
	let shared_state: SharedState = Arc::new(DashMap::new());
	start_block_monitor(shared_state.clone()).await;
    let addr = format!("{}:{}", HOST, PORT);
    let listener = TcpListener::bind(addr).await?;
    print_log_message(format!("Stratum listening on {}:{}", HOST, PORT), 1);

    loop {
        let (socket, addr) = listener.accept().await?;
        let state = shared_state.clone();
        print_log_message(format!("New stratum connection: {}", addr), 2);
        tokio::spawn(async move {
            if let Err(e) = handle_connection(socket, state).await {
                eprintln!("Connection error {}: {}", addr, e);
            }
        });
    }
}

pub async fn handle_connection(mut socket: TcpStream, state: SharedState) -> Result<(), Box<dyn Error>> {
    let mut reader = BufReader::new(socket);
    let mut line = String::new();
	let (reader_inner, writer_raw) = reader.into_inner().into_split();
	let writer = Arc::new(tMutex::new(writer_raw));
	let mut reader = BufReader::new(reader_inner);

    loop {
        line.clear();
        let bytes_read = reader.read_line(&mut line).await?;
        if bytes_read == 0 {
            break;
        }

        match serde_json::from_str::<serde_json::Value>(line.trim_end()) {
            Ok(msg) => {
                match msg.get("method").and_then(|m| m.as_str()) {
					Some("login") => {
						let login_str = msg.get("params")
							.and_then(|p| p.get("login"))
							.and_then(|l| l.as_str())
							.unwrap_or("");
						let is_valid_wallet = login_str.len() == 64
							&& login_str.chars().skip(2).all(|c| c.is_ascii_hexdigit());

						if !is_valid_wallet {
							let response = json!({
								"id": msg.get("id").cloned().unwrap_or(json!(1)),
								"jsonrpc": "2.0",
								"error": {
									"code": -1,
									"message": "invalid wallet address"
								}
							});

							let response_text = serde_json::to_string(&response)? + "\n";
							let mut writer_lock = writer.lock().await;
							writer_lock.write_all(response_text.as_bytes()).await?;
							continue;
						}
						let (actual_height, actual_hash, actual_ts) = get_latest_block_info();
						let worker_uuid = Uuid::new_v4();
						let worker_id = worker_uuid.to_string();
						let extra_data = worker_id.replace("-", "")[..4].to_lowercase();

						let job_id = Uuid::new_v4().to_string();
						let coins = 50;
						let difficulty: u64 = calculate_rx_diff(actual_height + 1);
						let target = difficulty_to_target(difficulty);
						let ts_hex = format!("{:010x}", actual_ts);
						//let diff_dec = calculate_diff(coins_dec, height.clone());
						let nonce = "0000";
						let reward_amount = calculate_reward(actual_height + 1);
						let raw_tx;
						match generate_reward_tx(nonce, login_str, reward_amount) {
							Ok(tx) => {
								raw_tx = tx;
							}
							Err(_e) => {
								raw_tx = String::new();
							}
						}
						
						let blob = format!(
							"{}{}{}0000000001{}{}",
							extra_data,
							ts_hex,
							actual_hash,
							target,
							raw_tx
						);

						state.insert(worker_id.clone(), JobState {
							worker_id: worker_id.clone(),
							job_id: job_id.clone(),
							miner: login_str.to_string(),
							difficulty: difficulty,
							target: target.clone(),
							shares: 0,
							coins,
							writer: writer.clone(),
							blob: blob.to_string(),
						});
						
						print_log_message(format!("New login {}:{}", login_str, worker_id), 2);
						save_miner(&login_str.to_lowercase(), &worker_id, &coins.to_string(), "0");

						let response = json!({
							"id": msg.get("id").cloned().unwrap_or(json!(1)),
							"jsonrpc": "2.0",
							"error": null,
							"result": {
								"id": worker_id,
								"job": {
									"blob": blob,
									"job_id": job_id,
									"target": target,
									"height": actual_height + 1,
									"seed_hash": "b38737d8f08e1b0b033611bb268bd79b236c3089a756b79906eff085c67a7e31",
									"blockHash": actual_hash,
									"algo": "rx/0"
								},
								"status": "OK"
							}
						});

						let response_text = serde_json::to_string(&response)? + "\n";
						print_log_message(format!("[SEND] {}", response_text.trim_end()), 4);
						let mut writer_lock = writer.lock().await;
						writer_lock.write_all(response_text.as_bytes()).await?;
					}

                    Some("submit") => {
                        if let Some(params) = msg.get("params") {
                            let job_id = params.get("job_id").and_then(|v| v.as_str()).unwrap_or("");
                            let worker_id = params.get("id").and_then(|v| v.as_str()).unwrap_or("");
                            let nonce = params.get("nonce").and_then(|v| v.as_str()).unwrap_or("");
                            let client_result = params.get("result").and_then(|v| v.as_str()).unwrap_or("");

                            if let Some(mut job_state) = state.get_mut(worker_id) {
								
								let mut hashdiff = 0;

								if let Ok(mut stream) = nTcpStream::connect("127.0.0.1:16789") {
									let request = json!({
										"blob": &job_state.blob,
										"nonce": nonce
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
															hashdiff = diff;
														}
													}
												}
											}
										}
									}
								}
								
                                if job_state.job_id == job_id {
									if hashdiff >= job_state.difficulty {
										let status = "OK";
										job_state.shares += 1;
										let response = json!({
											"id": msg.get("id").cloned().unwrap_or(json!(1)),
											"jsonrpc": "2.0",
											"error": null,
											"result": {
												"status": status
											}
										});
										let response_text = serde_json::to_string(&response)? + "\n";
										let mut writer = job_state.writer.lock().await;
										writer.write_all(response_text.as_bytes()).await?;
										let (actual_height, _actual_hash, _actual_ts) = get_latest_block_info();
										let extra_data = job_state.worker_id.replace("-", "")[..4].to_lowercase();
										let _ = mine_block(&job_state.miner, nonce, worker_id, &extra_data, None);
									}
									else {
										let status = "ERROR";
										job_state.shares += 1;
										let response = json!({
											"id": msg.get("id").cloned().unwrap_or(json!(1)),
											"jsonrpc": "2.0",
											"error": null,
											"result": {
												"status": status
											}
										});
										let response_text = serde_json::to_string(&response)? + "\n";
										let mut writer = job_state.writer.lock().await;
										writer.write_all(response_text.as_bytes()).await?;
									}
                                }
                            }
                        }
                    }
					Some("coins") => {
						if let Some(params) = msg.get("params") {
							let worker_id = msg.get("id").and_then(|v| v.as_str()).unwrap_or("");
							let hashrate = params.get("hashrate").and_then(|v| v.as_f64()).unwrap_or(0.0);

							let coins = (hashrate / 1000.0).round() as u64;
							let coins = coins.max(10);
							let (ah, _, _) = get_latest_block_info();
							let difficulty = calculate_rx_diff(ah + 1);
							let target = difficulty_to_target(difficulty);

							if let Some(mut job_state) = state.get_mut(worker_id) {
								if coins > 0 { //job_state.coins != coins {
									job_state.coins = coins;
									let extra_data = job_state.worker_id.replace("-", "")[..4].to_lowercase();
									
									job_state.difficulty = difficulty;
									job_state.target = target.clone();

									let (actual_height, actual_hash, actual_ts) = get_latest_block_info();
									let ts_hex = format!("{:010x}", actual_ts);
									let nonce = "0000";
									let reward_amount = calculate_reward(actual_height + 1);
									let raw_tx = generate_reward_tx(nonce, &job_state.miner, reward_amount).unwrap_or_default();

									let blob = format!(
										"{}{}{}0000000001{}{}",
										extra_data,
										ts_hex,
										actual_hash,
										target,
										raw_tx
									);
									
									job_state.blob = blob.to_string();

									let new_job_id = Uuid::new_v4().to_string();
									job_state.job_id = new_job_id.clone();

									save_miner(&job_state.miner.to_lowercase(), &job_state.worker_id, &job_state.coins.to_string(), &hashrate.to_string());

									let response = json!({
										"jsonrpc": "2.0",
										"method":"job",
										"params": {
											"blob": blob,
											"job_id": new_job_id,
											"target": target,
											"id": msg.get("id").cloned().unwrap_or(json!(1)),
											"height": actual_height + 1,
											"seed_hash": "b38737d8f08e1b0b033611bb268bd79b236c3089a756b79906eff085c67a7e31",
											"algo": "rx/0"
										}
									});

									let response_text = serde_json::to_string(&response)? + "\n";
									let mut writer = job_state.writer.lock().await;
									writer.write_all(response_text.as_bytes()).await?;
								} else {
									let response_text = "\n";
									let mut writer = job_state.writer.lock().await;
									writer.write_all(response_text.as_bytes()).await?;
									continue;
								}
							}
						}
					}
                    _ => {
						let response_text = "\n";
						let mut writer_lock = writer.lock().await;
						writer_lock.write_all(response_text.as_bytes()).await?;
						continue;
					}
                }
            }
            Err(e) => {
                print_log_message(format!("Error parsing JSON: {}", e), 2);
				let response_text = "\n";
				let mut writer_lock = writer.lock().await;
				writer_lock.write_all(response_text.as_bytes()).await?;
				continue;
            }
        }
    }

    Ok(())
}

fn mine_block(miner: &str, nonce: &str, id: &str, extra_data: &str, rhash: Option<&mut String>) -> sled::Result<()> {	
	let result = (|| {
		let mining_template = get_mining_template(&miner);
		let mut modified_password = nonce.to_string();
		if mining_template.len() > 16 {
			modified_password.push_str(&mining_template[16..]);
		}
		let parts: Vec<&str> = mining_template.split('-').collect();
		let (actual_height, actual_hash, actual_ts) = get_latest_block_info();
		let block_difficulty = calculate_rx_diff(actual_height + 1);
		let mining_transaction = parts[5];
		let block_transactions = format!("{}", mining_transaction);

		let db = config::db();
		let utxodb = config::utxodb();
		let now_secs = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as i64;
		let ts_diff = config::ts_diff();
		let ts_result = now_secs + ts_diff;
		let pre_timestamp = ts_result as u64;
		let valid_timestamp;
		if pre_timestamp < actual_ts {
			valid_timestamp = actual_ts;
		} else {
			valid_timestamp = pre_timestamp;
		}
		
		let block_reward = calculate_reward(actual_height + 1);
		
		let mut new_block = Block {
			height: actual_height + 1,
			hash: "".to_string(),
			prev_hash: actual_hash,
			timestamp: valid_timestamp,
			nonce: nonce.to_string(),
			//transactions: vec!["tx1".to_string(), "tx2".to_string()],
			transactions: block_transactions.to_string(),
			miner: miner.to_string(),
			difficulty: block_difficulty,
			block_reward: block_reward,
			state_root: "".to_string(),
			receipts_root: "".to_string(),
			logs_bloom: "".to_string(),
			extra_data: extra_data.to_string(),
			version: 1,
			signature: "".to_string(),
		};
		let mempooldb = config::mempooldb();
		let mut transactions_list = block_transactions.clone();
		let mut transactions_hash_list = "".to_string();
		let mut spent_utxos_in_block: HashSet<String> = HashSet::new();
		
		for entry in mempooldb.iter() {
			match entry {
				Ok((key, value)) => {
					if let Err(e) = mempooldb.remove(&key) {
						eprintln!("Error deleting mempool entry: {:?}", e);
					}
					let tx_value_str = String::from_utf8(value.to_vec()).unwrap_or_else(|_| String::from("Invalid UTF-8"));
					let tx_str = tx_value_str.clone();
					if db.contains_key(tx_str.clone())? {
       		            continue;
                    }
					
					if let Ok(tx_bytes) = hex::decode(&tx_value_str) {
						if let Ok(raw_tx) = bincode::deserialize::<RawTransaction>(&tx_bytes) {
							let rtx = RawTransaction {
								inputcount: raw_tx.inputcount,
								inputs: raw_tx.inputs.clone(),
								outputcount: raw_tx.outputcount,
								outputs: raw_tx.outputs.clone(),
								fee: raw_tx.fee,
								sigpub: raw_tx.sigpub.clone(),
								signature: "".to_string(),
							};
										
							let mut total_inputs_amount = 0u64;
							let total_outputs_amount: u64 = raw_tx.outputs.iter().map(|(_, amount)| amount).sum();
							let mut required_amount = total_outputs_amount + raw_tx.fee;
										
							let tx_binary = bincode::serialize(&rtx).expect("Failed to serialize transaction");
							let tx_hash = blake3::hash(&tx_binary);
										
							let bytes_decoded_signature = hex::decode(&raw_tx.signature).expect("Error decoding signature");
							let decoded_signature = <pqcrypto_sphincsplus::sphincssha2128fsimple::DetachedSignature as DetachedSignatureTrait>::from_bytes(&bytes_decoded_signature)
								.expect("Error in signature reconstruction");
										
							let pk_bytes = hex::decode(&raw_tx.sigpub).expect("Invalid pubkey");
							let pk = PublicKey::from_bytes(&pk_bytes).expect("Invalid pubkey format");
										
							let address_hash = blake3::hash(pk.as_bytes());
							let sender_address = hex::encode(address_hash.as_bytes());

							match verify_detached_signature(&decoded_signature, tx_hash.as_bytes(), &pk) {
								Ok(_) => print_log_message(format!("TX received with valid key pair"), 2),
								Err(e) => {
									print_log_message(format!("TX received with error: Private and public keys don't form a valid pair"), 2);
									print_log_message(format!("Details: {}", e), 3);
									required_amount = 9999999999999999;
								}
							}
										
							for input in &raw_tx.inputs {
								let utxokey = format!("{}:{}", input.txid, input.vout);
								
								if spent_utxos_in_block.contains(&utxokey) {
									required_amount = 9999999999999999;
									break;
								}
								
								if let Ok(Some(utxo_bytes)) = utxodb.get(&utxokey) {
									let utxo_value: serde_json::Value = serde_json::from_slice(&utxo_bytes).expect("Failed to parse UTXO JSON");
									let amount = utxo_value["amount"].as_u64().expect("Invalid amount in UTXO");
									let owner = utxo_value["address"].as_str().expect("Invalid amount in UTXO");
									if owner != sender_address {
										required_amount = 9999999999999999;
										break;
									}
									total_inputs_amount += amount;
									spent_utxos_in_block.insert(utxokey);
								} else {
									required_amount = 9999999999999999;
									break;
								}
							}
										
							if total_inputs_amount >= required_amount {
								transactions_list = format!("{}-{}", transactions_list, tx_value_str);
							} else {
								print_log_message(format!("Wrong TX deleted from system"), 3);
							}
						}
					}
				}
				Err(e) => {
					eprintln!("Error reading mempool entry: {:?}", e);
				}
			}
		}
		new_block.transactions = transactions_list;
		//get merkle tx's receipt
		new_block.receipts_root = merkle_tree(&new_block.transactions);
		//get blockhash
		let unhashed_serialized_block = serde_json::to_string_pretty(&new_block).unwrap();
		let block_hash = keccak256(&unhashed_serialized_block);
		print_log_message(format!("Block {} found for {} {} by miner: {} ({})", new_block.height, new_block.block_reward as f64 / 100000000.0, COIN_SYMBOL, new_block.miner, id), 1);
		
		new_block.hash = block_hash;
		if let Some(var) = rhash {
			*var = new_block.hash.to_string();
		}
		
		if let Err(e) = save_block_to_db(&mut new_block, 1) {
			eprintln!("Error saving block: {}", e);
		} else {
			add_block_to_history(new_block.height, new_block.timestamp, new_block.difficulty, 1);
			let _ = save_mined_block(&mut new_block, id);
		}
		Ok(())
	})();
	result
}

#[tokio::main]
async fn main() -> sled::Result<()> {	
	let args: Vec<String> = env::args().collect();
	
	let help_mode = args.iter().any(|arg| arg == "--help") as u8;
	
	if help_mode == 1 {
		println!("Options:");
		println!("  --http           Use HTTP protocol instead of NNG for peer communications.");
		println!("  --nonng          Disable the NNG server startup (no NNG socket connections).");
		println!("  --server addr    Connect to a specific server IP or domain for synchronization.");
		println!("  --help           Display this help menu.");
		println!();
		println!("Example:");
		println!("  ominirex --async --http --nonng --fee 4 --server node1.ominirex.xyz");
		process::exit(0);
	}
	
	let http_mode = args.iter().any(|arg| arg == "--http") as u8;
	let nng_mode = args.iter().any(|arg| arg == "--nonng") as u8;	
	let mut server_address = "ominirex.xyz".to_string();
	if let Some(pos) = args.iter().position(|arg| arg == "--server") {
		if let Some(addr) = args.get(pos + 1) {
			server_address = addr.clone();
		} else {
			eprintln!("Error: --server option requires an address (e.g., IP or domain).");
			std::process::exit(1);
		}
	}
	
	config::load();
	let utxodb = config::utxodb();
	
	let response = reqwest::get("https://pokio.xyz/ts.php").await;
    if let Ok(resp) = response {
        if let Ok(text) = resp.text().await {
            if let Ok(remote_ts) = text.trim().parse::<u64>() {
                let local_ts = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                let mut diff = remote_ts as i64 - local_ts as i64;
				if diff > 0 {
					diff = diff - 1;
				}
				config::update_ts_diff(diff);
            }
        }
    }
	print_log_message(format!("Adjusted timestamp diff: {} seconds", config::ts_diff()), 1);
	print_log_message(format!("checkpoint: {}, {}", CHECKPOINTS[0].height, CHECKPOINTS[0].hash), 1);
	
	set_latest_block_info();
	preload_block_history();
	print_log_message(format!("Chain started with height: {}, hash: {}", config::actual_height(), config::actual_hash()), 1);
	
	thread::spawn(|| {
		if let Err(e) = start_local_hash_server() {
			eprintln!("Local hash server error: {}", e);
		}
	});

	sleep(tDuration::from_millis(1300));

	if let Ok(mut stream) = nTcpStream::connect("127.0.0.1:16789") {
		let request = json!({
			"blob": "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
			"nonce": "11111111"
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
							print_log_message(format!("RandomX VM started: {}", hash_str), 1);
						}
					}
				}
			}
		}
	}

	println!("");
	println!("Available commands:");
	println!("  help        - Show this help message");
	println!("  version     - Show server version");
	println!("  miners      - Show active miners in the last 600 seconds");
	println!("  lastblock   - Show details of the most recently mined block");
	println!("  setloglevel - Set log level (1 to 4)");
	println!("");
	
	// i/o thread
	thread::spawn(move || {
		loop {
			let mut input = String::new();
			io::stdin().read_line(&mut input).unwrap();
			let parts: Vec<&str> = input.trim().split_whitespace().collect();

			if parts.is_empty() {
				continue;
			}

			match parts[0] {
				"version" => {
					println!("Ominira server 1.0");
				}
				"help" => {
					println!("Available commands:");
					println!("  help        - Show this help message");
					println!("  version     - Show server version");
					println!("  miners      - Show active miners in the last 600 seconds");
					println!("  lastblock   - Show details of the most recently mined block");
					println!("  setloglevel - Set log level (1 to 4)");
				}
				"miners" => {
					println!("Miners in last 600 seconds:");
					let seconds = 600;
					let mut active_workers = 0;
					let active_miners = count_active_miners(seconds);
					println!("Total active miners: {}", active_miners.len());
					for (_miner, workers) in &active_miners {
						active_workers += workers.len();
					}
					println!("Total active workers: {}", active_workers);
				}
				"lastblock" => {
					println!("Last mined block:");
					let (actual_height, actual_hash, actual_ts) = get_latest_block_info();
					println!("Height: {}, Hash: {}, Timestamp: {}", actual_height, actual_hash, actual_ts);
				}
				"setloglevel" => {
					if parts.len() < 2 {
						println!("Please specify a log level (1 to 4).");
						continue;
					}
					match parts[1].parse::<u64>() {
						Ok(level) if level >= 1 && level <= 4 => {
							config::update_log_level(level);
							println!("Log level set to {}", level);
						}
						_ => {
							println!("Wrong log level value");
						}
					}
				}
				_ => {
					println!("Unknown command. Type 'help' to see available commands.");
				}
			}
		}
	});
	
	let servers = vec![
		"node1.ominirex.xyz".to_string(),
		"node2.ominirex.xyz".to_string(),
		"omi.pokio.xyz".to_string(),
	];
	
	//-- sync at start
	print_log_message(format!("Starting sync..."), 1);
	config::update_full_sync(1);
	for server in &servers {
		print_log_message(format!("Syncing from {}", server), 4);
		let _ = tokio::spawn(full_sync_blocks(server.clone())).await.unwrap();
	}
	config::update_full_sync(0);
	print_log_message("Sync ended. Starting server...".to_string(), 1);

	if nng_mode == 0 {
		print_log_message("Starting NNG server...".to_string(), 1);
		start_nng_server(servers.clone());
	}
	
	let server_task = tokio::spawn(async {
        start_server().await.unwrap();
    });
	
	//tokio::spawn(async { let _ = connect_to_http_server("node1.ominirex.xyz".to_string()); });


	if http_mode == 0 {
		//-- nng connect
		for server in &servers {
			let server = server.clone();
			tokio::spawn(async {
				let _ = connect_to_nng_server(server);
			});
		}

		//-- http connect
		for (i, server) in servers.iter().enumerate() {
			let server = server.clone();
			tokio::spawn(async {
				sleep(tDuration::from_millis(1300));
				let _ = connect_to_http_server(server);
			});
		}
	} else {
		//-- http connect
		for (i, server) in servers.iter().enumerate() {
			let server = server.clone();
			tokio::spawn(async {
				sleep(tDuration::from_millis(1300));
				let _ = connect_to_http_server(server);
			});
		}
	}

	let rpc_route = warp::path("rpc")
		.and(warp::post())
		.and(remote())
		.and(warp::body::json())
		.map(|addr: Option<std::net::SocketAddr>, data: serde_json::Value| {
			
			if let Some(addr) = addr {
				print_log_message(format!("Request from IP: {}", addr.ip()), 4);
			} else {
				print_log_message("Request from unknown IP".to_string(), 4);
			}
			
			print_log_message(format!("Received JSON: {}", data), 4);
			
			let id = data["id"].as_str().unwrap_or("unknown");
			let method = data["method"].as_str().unwrap_or("");
			
			let response = match method {
				"get_info" => {
					let (height, top_block_hash, adjusted_time) = get_latest_block_info();
					let cumulative_difficulty = calculate_rx_diff(height);
					let current_difficulty = calculate_rx_diff(height);
					let start_time = adjusted_time.clone();
					
					json!({
						"id": id,
						"jsonrpc": "2.0",
						"result": {
							"adjusted_time": adjusted_time,
							"busy_syncing": false,
							"cumulative_difficulty": cumulative_difficulty,
							"cumulative_difficulty_top64": 0,
							"difficulty": current_difficulty,
							"grey_peerlist_size": 4999,
							"height": height,
							"height_without_bootstrap": height,
							"incoming_connections_count": 4,
							"mainnet": true,
							"nettype": "mainnet",
							"offline": false,
							"outgoing_connections_count": 3,
							"rpc_connections_count": 1,
							"stagenet": false,
							"start_time": start_time,
							"status": "OK",
							"synchronized": true,
							"target": 120,
							"target_height": height.saturating_sub(8),
							"testnet": false,
							"top_block_hash": top_block_hash,
							"top_hash": "",
							"tx_count": 0,
							"tx_pool_size": 0,
							"untrusted": false,
							"version": "1.0",
							"white_peerlist_size": 1000,
							"wide_cumulative_difficulty": format!("0x{:x}", cumulative_difficulty),
							"wide_difficulty": format!("0x{:x}", current_difficulty)
						}
					})
				},
				"getlastblockheader" => {
					let (height, hash, ts) = get_latest_block_info();
					let diff = calculate_rx_diff(height);
					
					json!({
						"id": id,
						"jsonrpc": "2.0",
						"result": {
							"block_header": {
								"block_size": 5500,
								"block_weight": 5500,
								"cumulative_difficulty": diff,
								"cumulative_difficulty_top64": 0,
								"depth": 0,
								"difficulty": diff,
								"difficulty_top64": 0,
								"hash": hash,
								"height": height,
								"long_term_weight": 5500,
								"major_version": 1,
								"miner_tx_hash": "",
								"minor_version": 1,
								"nonce": 249602367,
								"num_txes": 0,
								"orphan_status": false,
								"pow_hash": "",
								"prev_hash": "",
								"reward": calculate_reward(height),
								"timestamp": ts,
								"wide_cumulative_difficulty": format!("0x{:x}", diff),
								"wide_difficulty": format!("0x{:x}", diff),
							},
							"credits": 0,
							"status": "OK",
							"top_hash": "",
							"untrusted": false
						}
					})
				},
				"getblock" | "getblockheaderbyheight" => {
					let empty_params = serde_json::Map::new();
					let params = data["params"].as_object().unwrap_or(&empty_params);
					let height = params.get("height").and_then(|v| v.as_u64()).unwrap_or(0);
					let block_json = get_block_as_json(height);
					
					let timestamp = block_json["timestamp"].as_u64().unwrap_or(0);
					let ts_hex = format!("{:010x}", timestamp);
					let difficulty = calculate_rx_diff(height);
					let target = difficulty_to_target(difficulty);
					
					let blob = format!(
						"0000{}{}{}01{}",
						ts_hex,
						block_json["hash"].as_str().unwrap_or(""),
						block_json["nonce"].as_str().unwrap_or(""),
						target
					);
					
					let (ah, _, _) = get_latest_block_info();
					
					json!({
						"id": id,
						"jsonrpc": "2.0",
						"result": {
							"blob": blob,
							"block_header": {
								"block_size": 1000,
								"block_weight": 1000,
								"cumulative_difficulty": 0,
								"cumulative_difficulty_top64": 0,
								"depth": ah - height,
								"difficulty": block_json["difficulty"].as_u64().unwrap_or(0),
								"difficulty_top64": 0,
								"hash": block_json["hash"].as_str().unwrap_or(""),
								"height": height,
								"long_term_weight": 176470,
								"major_version": 1,
								"miner_tx_hash": "",
								"minor_version": 1,
								"nonce": block_json["nonce"].as_str().unwrap_or(""),
								"num_txes": 0,
								"orphan_status": false,
								"pow_hash": "",
								"prev_hash": block_json["prev_hash"].as_str().unwrap_or(""),
								"reward": block_json["block_reward"].as_u64().unwrap_or(0),
								"timestamp": block_json["timestamp"].as_u64().unwrap_or(0),
								"wide_cumulative_difficulty": format!("0x{:x}", 0),
								"wide_difficulty": format!("0x{:x}", difficulty)
							},
							"credits": 0,
							"miner_tx_hash": "",
							"status": "OK",
							"top_hash": "",
							"untrusted": false
						}
					})
				},
				"getblocktemplate" => {
					let empty_params = serde_json::Map::new();
					let params = data["params"].as_object().unwrap_or(&empty_params);
    
					let wallet_address = params.get("wallet_address")
						.and_then(|v| v.as_str())
						.unwrap_or("");
					
					let reserve_size = params.get("reserve_size")
						.and_then(|v| v.as_u64())
						.unwrap_or(0);

					let (height, hash, ts) = get_latest_block_info();
					let ts_hex = format!("{:010x}", ts);
					let nonce = "0000";
					let difficulty = calculate_rx_diff(height + 1);
					let target = difficulty_to_target(difficulty);

					let reward_amount = calculate_reward(height + 1);
					let raw_tx = generate_reward_tx(nonce, wallet_address, reward_amount).unwrap_or_default();

					let blob = format!(
						"0000{}{}0000000001{}{}",
						ts_hex,
						hash,
						target,
						raw_tx
					);
					
					json!({
						"id": id,
						"jsonrpc": "2.0",
						"result": {
							"blockhashing_blob": blob,
							"blocktemplate_blob": blob,
							"difficulty": difficulty,
							"difficulty_top64": 0,
							"expected_reward": reward_amount,
							"height": height + 1,
							"next_seed_hash": "",
							"prev_hash": hash,
							"reserved_offset": 130,
							"seed_hash": "b38737d8f08e1b0b033611bb268bd79b236c3089a756b79906eff085c67a7e31",
							"seed_height": 0,
							"status": "OK",
							"untrusted": false,
							"wide_difficulty": format!("0x{}", target)
						}
					})
				},
				"submitblock" => {
					let nonce = data["params"]
						.get(0)
						.and_then(|v| v.as_str())
						.unwrap_or("000000000000");
						
					let extranonce = data["params"]
						.get(1)
						.and_then(|v| v.as_str())
						.unwrap_or("000000000000");
						
					let miner = data["params"]
						.get(2)
						.and_then(|v| v.as_str())
						.unwrap_or("000000000000000000000000000000000000000000000000000000000000000000000000dead");
					
					let short_nonce = &nonce[..8.min(nonce.len())];
					
					let mut rhash = String::from("");
					
					match mine_block(miner, short_nonce, id, extranonce, Some(&mut rhash)) {
						Ok(_) => {
							json!({"jsonrpc": "2.0", "id": id, "result": {"hash" : rhash} })
						}
						Err(_) => {
							json!({"jsonrpc": "2.0", "id": id, "error": { "code": -7, "message": "Block not accepted" } })
						}
					}
				},
				"pokio_getBlocks" => {
					let block_number = data["params"]
						.get(0)
						.and_then(|v| v.as_str())
						.and_then(|s| s.parse::<u64>().ok())
						.unwrap_or(1);
					let blocks = get_next_blocks(block_number);
					json!({"jsonrpc": "2.0", "id": id, "result": blocks})
				},
				"pokio_getBlockByHeight" => {
					let block_number = data["params"]
						.get(0)
						.and_then(|v| v.as_str())
						.and_then(|s| s.parse::<u64>().ok())
						.unwrap_or(1);
					let block_json = get_block_as_json(block_number);
					json!({ "jsonrpc": "2.0", "id": id, "result": block_json })
				},
				"pokio_blockNumber" => {
					let (actual_height, _actual_hash, _) = get_latest_block_info();
					let block_number = format!("0x{:x}", actual_height);
					json!({"jsonrpc": "2.0", "id": id, "result": block_number})
				},
				"pokio_getMempool" => {
					match get_mempool_records() {
						Ok(mempool) => {
							json!({"jsonrpc": "2.0", "id": id, "result": mempool})
						},
						Err(e) => {
							json!({
								"jsonrpc": "2.0",
								"id": id,
								"error": {
									"code": -32000,
									"message": format!("Error getting mempool records: {}", e)
								}
							})
						}
					}
				},
				"pokio_sendRawTransaction" => {
					let mut txhash = String::from("");
					if let Some(params) = data["params"].as_array() {
						if let Some(raw_tx) = params.get(0) {
							if let Some(raw_tx_str) = raw_tx.as_str() {
								print_log_message(format!("Get rawtx: {}", raw_tx_str), 2);
								if let Ok(tx_bytes) = hex::decode(&raw_tx_str) {
									if let Ok(raw_tx) = bincode::deserialize::<RawTransaction>(&tx_bytes) {
										
										let rtx = RawTransaction {
											inputcount: raw_tx.inputcount,
											inputs: raw_tx.inputs.clone(),
											outputcount: raw_tx.outputcount,
											outputs: raw_tx.outputs.clone(),
											fee: raw_tx.fee,
											sigpub: raw_tx.sigpub.clone(),
											signature: "".to_string(),
										};
										
										let mut total_inputs_amount = 0u64;
										let total_outputs_amount: u64 = raw_tx.outputs.iter().map(|(_, amount)| amount).sum();
										let mut required_amount = total_outputs_amount + raw_tx.fee;
										
										let tx_binary = bincode::serialize(&rtx)
											.expect("Failed to serialize transaction");
										let tx_hash = blake3::hash(&tx_binary);
										
										let bytes_decoded_signature = hex::decode(&raw_tx.signature).expect("Error decoding signature");
										let decoded_signature = <pqcrypto_sphincsplus::sphincssha2128fsimple::DetachedSignature as DetachedSignatureTrait>::from_bytes(&bytes_decoded_signature)
											.expect("Error in signature reconstruction");
										
										let pk_bytes = hex::decode(&raw_tx.sigpub).expect("Invalid pubkey");
										let pk = PublicKey::from_bytes(&pk_bytes).expect("Invalid pubkey format");
										
										let address_hash = blake3::hash(pk.as_bytes());
										let sender_address = hex::encode(address_hash.as_bytes());

										match verify_detached_signature(&decoded_signature, tx_hash.as_bytes(), &pk) {
											Ok(_) => print_log_message(format!("TX received with valid key pair"), 2),
											Err(e) => {
												print_log_message(format!("TX received with error: Private and public keys don't form a valid pair"), 2);
												print_log_message(format!("Details: {}", e), 3);
												required_amount = 9999999999999999;
											}
										}
										
										for input in &raw_tx.inputs {
											let key = format!("{}:{}", input.txid, input.vout);
											if let Ok(Some(utxo_bytes)) = utxodb.get(&key) {
												let utxo_value: serde_json::Value = serde_json::from_slice(&utxo_bytes).expect("Failed to parse UTXO JSON");
												let amount = utxo_value["amount"].as_u64().expect("Invalid amount in UTXO");
												let owner = utxo_value["address"].as_str().expect("Invalid amount in UTXO");
												if owner != sender_address {
													required_amount = 9999999999999999;
													break;
												}
												total_inputs_amount += amount;
											} else {
												required_amount = 9999999999999999;
												break;
											}
										}
										
										if total_inputs_amount >= required_amount {
											store_raw_transaction(raw_tx_str.to_string());
											let b3_tx_hash = blake3::hash(&raw_tx_str.as_bytes());
											txhash = hex::encode(b3_tx_hash.as_bytes());
											print_log_message(format!("TX stored in mempool: {}", txhash), 3);
										} else {
											let b3_tx_hash = blake3::hash(&raw_tx_str.as_bytes());
											let etxhash = hex::encode(b3_tx_hash.as_bytes());
											print_log_message(format!("TX rejected: {}", etxhash), 3);
										}
										
									}
								}								
							}
						}
						
						
					}
					json!({"jsonrpc": "2.0", "id": id, "result": format!("{}", txhash)})
				},
				_ => {
					print_log_message(format!("Received JSON: {}", data), 3);
					json!({"jsonrpc": "2.0", "id": id, "error": {"code": -32600, "message": "The method does not exist/is not available"}})
				}
			};
			warp::reply::json(&response)
		});
	
	type CacheKey = (u64, String, String);
	type MiningCache = Arc<Mutex<HashMap<CacheKey, String>>>;

	let mining_cache: MiningCache = Arc::new(Mutex::new(HashMap::new()));
	let cache = mining_cache.clone();
	
	let mining_route = warp::path("mining")
		.and(warp::post())
		.and(remote())
		.and(warp::body::json())
		.map(move |addr: Option<std::net::SocketAddr>, data: serde_json::Value| {
			
			if let Some(addr) = addr {
				print_log_message(format!("Request from IP: {}", addr.ip()), 4);
			} else {
				print_log_message("Request from unknown IP".to_string(), 4);
			}
			
			let id = data["id"].as_str().unwrap_or("unknown");
			let method = data["method"].as_str().unwrap_or("");
			let response = match method {
				"getMiningTemplate" => {
					let (actual_height, _, _) = get_latest_block_info();
					let mut coins = data["coins"].as_str().unwrap_or("1000").to_string();
					let miner = data["miner"].as_str().unwrap_or("");
					let hr = data["hr"].as_str().unwrap_or("");
					let key = (actual_height, coins.clone(), miner.to_string());

					{
						let mut guard = cache.lock().unwrap();
						guard.retain(|(height, _, _), _| *height >= actual_height);
					}

					let cached_template = {
						let guard = cache.lock().unwrap();
						guard.get(&key).cloned()
					};

					let mining_template: String = match cached_template {
						Some(template) => {
							template
						}
						None => {
							let new_template = get_mining_template(miner);
							cache.lock().unwrap().insert(key, new_template.clone());
							save_miner(&miner.to_lowercase(), id, &coins, hr);
							new_template
						}
					};

					json!({"jsonrpc": "2.0", "id": id, "result": mining_template})
				},
				"getMinersCount" => {
					let seconds = 600;
					let active_miners = count_active_miners(seconds);					
					let seconds = 600;
					let mut active_workers = 0;
					let active_miners = count_active_miners(seconds);
					for (_miner, workers) in &active_miners {
						active_workers += workers.len();
					}
					json!({"jsonrpc": "2.0", "id": id, "result": { "miners" : active_miners.len(), "workers" : active_workers } })
					
				},
				"getWorkers" => {
					let miner = data["params"]
						.get(0)
						.and_then(|v| v.as_str())
						.unwrap_or("");

					let seconds = 600;
					let active_miners = count_active_miners(seconds);
					let db = config::pooldb();
					let mut result = vec![];
					if let Some(workers) = active_miners.get(&miner.to_lowercase()) {
						for worker in workers {
							let mut worker_data = json!({
								"hr": worker.hr,
								"id": worker.id,
								"miner": miner,
								"target": worker.target,
								"timestamp": worker.timestamp,
								"mined_blocks": worker.mined_blocks,
							});
							let key = format!("miner_{}", worker.id);
							if let Ok(Some(data)) = db.get(key) {
								if let Ok(json_data) = serde_json::from_slice::<Value>(&data) {
									for (k, v) in json_data.as_object().unwrap_or(&serde_json::Map::new()) {
										worker_data[k] = v.clone();
									}
								}
							}
							result.push(worker_data);
						}
					}
					json!({ "jsonrpc": "2.0", "id": id, "result": result })
				},
				"getMinedBlocks" => {
					let block_number = data["params"]
						.get(0)
						.and_then(|v| v.as_str())
						.and_then(|s| s.parse::<usize>().ok())
						.unwrap_or(0);

					match get_blocks_paginated(50, block_number) {
						Ok(blocks) => json!({"jsonrpc": "2.0", "id": id, "result": blocks}),
						Err(e) => json!({"jsonrpc": "2.0", "id": id, "error": { "code": -32000, "message": e.to_string() }}),
					}
				},
				"getPoolDifficulty" => {
					let total_hr = sum_recent_difficulty(600, 1);
					json!({"jsonrpc": "2.0", "id": id, "result": total_hr})
				},
				"getNetDifficulty" => {
					let total_hr = sum_recent_difficulty(600, 0);
					json!({"jsonrpc": "2.0", "id": id, "result": total_hr})
				},
				"getFee" => {
					json!({"jsonrpc": "2.0", "id": id, "result": config::mining_fee() })
				},
				"submitBlock" => {
					let miner = data["miner"].as_str().unwrap_or("");
					let nonce = data["nonce"].as_str().unwrap_or("0000000000000000");
					let ip_str = addr.map(|a| a.ip().to_string());

					match mine_block(miner, nonce, id, "", None) {
						Ok(_) => {
							json!({"jsonrpc": "2.0", "id": id, "result": "ok"})
						}
						Err(_) => {
							json!({"jsonrpc": "2.0", "id": id, "result": "error"})
						}
					}
				},
				/*"submitMergedBlock" => {
					let miner = data["params"]["miner"].as_str().unwrap_or("");
					let nonce = data["params"]["nonce"].as_str().unwrap_or("00000000");
					let extra_data = data["params"]["extra_data"].as_str().unwrap_or("");
					match mine_block( miner, nonce, id, extra_data, None) {
						Ok(_) => {
							json!({"jsonrpc": "2.0", "id": id, "result": "ok"})
						}
						Err(_) => {
							json!({"jsonrpc": "2.0", "id": id, "result": "ok"})
						}
					}
				},*/
				"putBlock" => {
					match serde_json::from_value::<String>(data["block"].clone()) {
						Ok(block_str) => {
							match serde_json::from_str::<serde_json::Value>(&block_str) {
								Ok(block_json) => {
									let mut new_block = Block {
										height: block_json.get("height").and_then(|v| v.as_u64()).expect("Missing height"),
										hash: block_json.get("hash").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										prev_hash: block_json.get("prev_hash").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										timestamp: block_json.get("timestamp").and_then(|v| v.as_u64()).expect("Missing timestamp"),
										nonce: block_json.get("nonce").and_then(|v| v.as_str()).map_or_else(|| "0000000000000000".to_string(), String::from),
										transactions: block_json.get("transactions").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										miner: block_json.get("miner").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										difficulty: block_json.get("difficulty").and_then(|v| v.as_u64()).expect("Missing difficulty"),
										block_reward: block_json.get("block_reward").and_then(|v| v.as_u64()).expect("Missing block_reward"),
										state_root: block_json.get("state_root").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										receipts_root: block_json.get("receipts_root").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										logs_bloom: block_json.get("logs_bloom").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										extra_data: block_json.get("extra_data").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
										version: block_json.get("version").and_then(|v| v.as_u64()).map(|v| v as u32).expect("Missing version"),
										signature: block_json.get("signature").and_then(|v| v.as_str()).map_or_else(|| "".to_string(), String::from),
									};
									
									print_log_message(format!("New block received: {:?}", new_block.height), 1);
									
									if let Err(e) = save_block_to_db(&mut new_block, 1) {
										eprintln!("Error saving block: {}", e);
										json!({"jsonrpc": "2.0", "id": id, "result": "error"})
									} else {
										add_block_to_history(new_block.height, new_block.timestamp, new_block.difficulty, 0);
										json!({"jsonrpc": "2.0", "id": id, "result": "ok"})
									}
								}
								Err(_) => json!({"jsonrpc": "2.0", "id": id, "result": "error"}),
							}
						}
						Err(_) => json!({"jsonrpc": "2.0", "id": id, "result": "error"}),
					}
				},
				_ => json!({"jsonrpc": "2.0", "id": id, "error": {"code": -32600, "message": "The method does not exist/is not available"}}),
			};
			
			warp::reply::json(&response)
			
			
		});

	let routes = rpc_route.or(mining_route);
	warp::serve(routes).run(([0, 0, 0, 0], 40404)).await;
	Ok(())
}

async fn full_sync_blocks(pserver: String) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
	let client = Client::builder()
		.timeout(Duration::from_secs(5))
		.build()
		.expect("Failed to build HTTP client");
	let rpc_url = format!("http://{}:40404/rpc", pserver);
	let db = config::db();
	loop {
		let max_block_response = client.post(&rpc_url)
			.json(&json!({ "jsonrpc": "2.0", "id": 1, "method": "pokio_blockNumber", "params": [] }))
			.send()
			.await?;
		let max_block_json: serde_json::Value = max_block_response.json().await?;
		let max_block = u64::from_str_radix(max_block_json["result"].as_str().unwrap().trim_start_matches("0x"), 16)?;
		let (mut actual_height, mut _actual_hash, _) = get_latest_block_info();
		while actual_height < max_block {
			let blocks_response = client.post(&rpc_url)
				.json(&json!({ "jsonrpc": "2.0", "id": 1, "method": "pokio_getBlocks", "params": [(actual_height+1).to_string()] }))
				.send()
				.await?;
			let blocks_json: serde_json::Value = blocks_response.json().await?;
			if let Some(blocks_array) = blocks_json["result"].as_array() {
				for (_i, block) in blocks_array.iter().enumerate() {
					let first_block = block;
					let mut new_block = Block {
						height: first_block.get("height").and_then(|v| v.as_u64()).expect("REASON"),
						hash: first_block.get("hash").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						prev_hash: first_block.get("prev_hash").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						timestamp: first_block.get("timestamp").and_then(|v| v.as_u64()).expect("REASON"),
						nonce: first_block.get("nonce").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("0000000000000000")),
						transactions: first_block.get("transactions").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						miner: first_block.get("miner").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						difficulty: first_block.get("difficulty").and_then(|v| v.as_u64()).expect("REASON"),
						block_reward: first_block.get("block_reward").and_then(|v| v.as_u64()).expect("REASON"),
						state_root: first_block.get("state_root").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						receipts_root: first_block.get("receipts_root").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						logs_bloom: first_block.get("logs_bloom").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						extra_data: first_block.get("extra_data").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
						version: first_block.get("version").and_then(|v| v.as_u64()).map(|v| v as u32).expect("REASON"),
						signature: first_block.get("signature").and_then(|v| v.as_str()).map(|s| s.to_string()).unwrap_or_else(|| String::from("")),
					};
					let mut is_checkpoint = false;

					for checkpoint in CHECKPOINTS.iter() {
						if new_block.height == checkpoint.height {
							is_checkpoint = true;
							if new_block.hash != checkpoint.hash {
								eprintln!("Block hash mismatch at height {}!", new_block.height);
								process::exit(1);
							}
							print_log_message(format!("Checkpoint passed, block: {}", new_block.height), 1);
							break;
						}
					}

					let last_checkpoint_height = CHECKPOINTS.last().unwrap().height;

					if is_checkpoint || new_block.height <= last_checkpoint_height {
						if let Err(e) = save_block_to_db(&mut new_block, 0) {
							eprintln!("Error saving block: {}", e);
						}
					} else {
						if let Err(e) = save_block_to_db(&mut new_block, 1) {
							eprintln!("Error saving block: {}", e);
						}
					}
				}
			} else {
				print_log_message(format!("Sync error, stopping..."), 1);
				break;
			}
			(actual_height, _actual_hash, _) = get_latest_block_info();
			print_log_message(format!("Block {} synced...", actual_height), 1);
		}
		break;
	}
	Ok(())
}
