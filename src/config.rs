use serde::Deserialize;
use std::str::FromStr;
use std::sync::{Mutex, OnceLock, atomic::{AtomicI64, AtomicU64, AtomicU8, AtomicUsize, Ordering}};
use sled;

use once_cell::unsync::Lazy;
use randomx_rs::{RandomXFlag, RandomXCache, RandomXVM};
use std::cell::RefCell;

static DB: OnceLock<sled::Db> = OnceLock::new();
static MEMPOOLDB: OnceLock<sled::Db> = OnceLock::new();
static POOLDB: OnceLock<sled::Db> = OnceLock::new();
static UTXODB: OnceLock<sled::Db> = OnceLock::new();
static SYNC_STATUS: OnceLock<AtomicUsize> = OnceLock::new();
static FULL_SYNC_STATUS: OnceLock<AtomicUsize> = OnceLock::new();
static TS_DIFF: OnceLock<AtomicI64> = OnceLock::new();
static MINING_FEE: OnceLock<AtomicUsize> = OnceLock::new();
static ACTUAL_HEIGHT: OnceLock<AtomicU64> = OnceLock::new();
static ACTUAL_HASH: OnceLock<Mutex<String>> = OnceLock::new();
static ACTUAL_TIMESTAMP: OnceLock<AtomicU64> = OnceLock::new();
static LOG_LEVEL: OnceLock<AtomicU64> = OnceLock::new();
static ASYNC: OnceLock<AtomicU8> = OnceLock::new();

thread_local! {
    static DYNAMIC_VM: RefCell<Option<(Vec<u8>, RandomXVM)>> = RefCell::new(None);
}

thread_local! {
    static THREAD_VM: Lazy<RefCell<RandomXVM>> = Lazy::new(|| {
        let key_hex = "b38737d8f08e1b0b033611bb268bd79b236c3089a756b79906eff085c67a7e31";
        let key = hex::decode(key_hex).expect("clave inválida");
        let flags = RandomXFlag::FLAG_DEFAULT | RandomXFlag::FLAG_JIT | RandomXFlag::FLAG_HARD_AES;
        let cache = RandomXCache::new(flags, &key).expect("RandomX cache creation error");
        let vm = RandomXVM::new(flags, Some(cache), None).expect("RandomX VM creation error");
        RefCell::new(vm)
    });
}

#[derive(Deserialize)]
struct KeyFile {
    privatekey: String,
}

pub fn load() {
    let db = sled::open("blockchain_db").expect("Failed to open blockchain database");
    DB.set(db).expect("Database was already initialized");
    
    let mempooldb = sled::open("mempool_db").expect("Failed to open mempool database");
    MEMPOOLDB.set(mempooldb).expect("Mempool was already initialized");
    
    let pooldb = sled::open("pool_db").expect("Failed to open mempool database");
    POOLDB.set(pooldb).expect("Mempool was already initialized");
	
	let utxodb = sled::open("utxo_db").expect("Failed to open vm database");
    UTXODB.set(utxodb).expect("VM was already initialized");

    SYNC_STATUS.set(AtomicUsize::new(0)).expect("Sync status already initialized");
	FULL_SYNC_STATUS.set(AtomicUsize::new(0)).expect("Full sync status already initialized");
	MINING_FEE.set(AtomicUsize::new(3)).expect("Mining fee status already initialized");
	TS_DIFF.set(AtomicI64::new(0)).expect("Timestamp diff status already initialized");
	
	ACTUAL_HEIGHT.set(AtomicU64::new(0)).expect("Actual height already initialized");
	ACTUAL_HASH.set(Mutex::new("0000000000000000000000000000000000000000000000000000000000000000".to_string())).expect("Actual hash key was started");
	ACTUAL_TIMESTAMP.set(AtomicU64::new(0)).expect("Actual timestamp already initialized");
	
	LOG_LEVEL.set(AtomicU64::new(1)).expect("Actual height already initialized");
	ASYNC.set(AtomicU8::new(1)).expect("Async status already initialized");
}

pub fn db() -> &'static sled::Db {
    DB.get().expect("Database not loaded")
}

pub fn mempooldb() -> &'static sled::Db {
    MEMPOOLDB.get().expect("Database not loaded")
}

pub fn pooldb() -> &'static sled::Db {
    POOLDB.get().expect("Database not loaded")
}

pub fn utxodb() -> &'static sled::Db {
    UTXODB.get().expect("Database not loaded")
}

pub fn mining_fee() -> usize {
    MINING_FEE.get().expect("Sync status not initialized").load(Ordering::SeqCst)
}

pub fn update_mining_fee(value: usize) {
    if let Some(status) = MINING_FEE.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Mining fee not initialized");
    }
}

pub fn ts_diff() -> i64 {
    TS_DIFF.get().expect("Timestamp diff not initialized").load(Ordering::SeqCst)
}

pub fn update_ts_diff(value: i64) {
    if let Some(status) = TS_DIFF.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Timestamp diff not initialized");
    }
}

pub fn sync_status() -> usize {
    SYNC_STATUS.get().expect("Sync status not initialized").load(Ordering::SeqCst)
}

pub fn update_sync(value: usize) {
    if let Some(status) = SYNC_STATUS.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Sync status not initialized");
    }
}

pub fn full_sync_status() -> usize {
    FULL_SYNC_STATUS.get().expect("Sync status not initialized").load(Ordering::SeqCst)
}

pub fn update_full_sync(value: usize) {
    if let Some(status) = FULL_SYNC_STATUS.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Sync status not initialized");
    }
}

pub fn async_status() -> u8 {
    ASYNC.get().expect("Actual height not initialized").load(Ordering::SeqCst)
}

pub fn update_async(value: u8) {
    if let Some(status) = ASYNC.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Actual height not initialized");
    }
}

pub fn log_level() -> u64 {
    LOG_LEVEL.get().expect("Actual height not initialized").load(Ordering::SeqCst)
}

pub fn update_log_level(value: u64) {
    if let Some(status) = LOG_LEVEL.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Actual height not initialized");
    }
}

pub fn actual_height() -> u64 {
    ACTUAL_HEIGHT.get().expect("Actual height not initialized").load(Ordering::SeqCst)
}

pub fn update_actual_height(value: u64) {
    if let Some(status) = ACTUAL_HEIGHT.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Actual height not initialized");
    }
}

pub fn update_actual_hash(value: String) {
    if let Some(hash_mutex) = ACTUAL_HASH.get() {
        let mut hash = hash_mutex.lock().expect("Failed to lock hash mutex");
        *hash = value;
    } else {
        panic!("Actual hash not initialized");
    }
}

pub fn actual_hash() -> String {
    ACTUAL_HASH
        .get()
        .expect("Actual hash not loaded")
        .lock()
        .expect("Failed to lock hash mutex")
        .clone()
}

pub fn actual_timestamp() -> u64 {
    ACTUAL_TIMESTAMP.get().expect("Actual timestamp not initialized").load(Ordering::SeqCst)
}

pub fn update_actual_timestamp(value: u64) {
    if let Some(status) = ACTUAL_TIMESTAMP.get() {
        status.store(value, Ordering::SeqCst);
    } else {
        panic!("Actual timestamp not initialized");
    }
}

pub fn with_vm<F, R>(f: F) -> R
where
    F: FnOnce(&mut RandomXVM) -> R,
{
    THREAD_VM.with(|cell| {
        let mut vm = cell.borrow_mut();
        f(&mut vm)
    })
}

pub fn set_dynamic_vm(seed_hex: &str) {
    let seed = hex::decode(seed_hex).expect("Seed hash inválido");
    let flags = RandomXFlag::FLAG_DEFAULT | RandomXFlag::FLAG_JIT | RandomXFlag::FLAG_HARD_AES;

    let cache = RandomXCache::new(flags, &seed).expect("Error creando cache RandomX");
    let vm = RandomXVM::new(flags, Some(cache), None).expect("Error creando VM RandomX");

    DYNAMIC_VM.with(|cell| {
        *cell.borrow_mut() = Some((seed, vm));
    });
}

pub fn with_dynamic_vm<F, R>(f: F) -> Option<R>
where
    F: FnOnce(&mut RandomXVM) -> R,
{
    DYNAMIC_VM.with(|cell| {
        let mut opt = cell.borrow_mut();
        opt.as_mut().map(|(_, vm)| f(vm))
    })
}


pub fn current_dynamic_seed() -> Option<String> {
    DYNAMIC_VM.with(|cell| {
        let opt = cell.borrow();
        opt.as_ref().map(|(seed, _)| hex::encode(seed))
    })
}
