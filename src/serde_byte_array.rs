use serde::{Deserialize, Deserializer, Serializer};

pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
where
    D: Deserializer<'de>,
{
    let bytes: Vec<u8> = Vec::deserialize(deserializer)?;
    let slice: [u8; 32] = bytes
        .try_into()
        .map_err(|x: Vec<u8>| serde::de::Error::invalid_length(x.len(), &"32"))?;
    Ok(slice)
}

pub(crate) fn serialize<S>(bytes: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_bytes(bytes)
}
