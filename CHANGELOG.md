# Changelog

## 0.3.0

- Switch to `blake3` as the main hashing algorithm (instead of `SHA3`)
- Expose `Ratchet::key_derivation_data` and `Ratchet::derive_key_with` to customize key derivation from ratchets

## 0.2.1

- Fix `Ratchet` serialization & test that it round-trips.
