<div align="center">
  <a href="https://github.com/WebNativeFileSystem" target="_blank">
    <img src="https://raw.githubusercontent.com/WebNativeFileSystem/rs-skip-ratchet/main/assets/logo.svg" alt="Skip Ratchet Logo" width="100" height="100"></img>
  </a>

  <h1 align="center">Skip Ratchet</h1>
</div>

This library implements the [Skip Ratchet paper][paper]. Skip ratchet is a data structure for deriving keys that maintain backward secrecy. Unlike hash chains, this data structure is capable of efficiently making large leaps in hash count.

## Usage

#### Creating a new ratchet and advancing it.

```rs
use skip_ratchet::Ratchet;

let mut ratchet = Ratchet::new();
ratchet.inc_by(10);

println!("{:?}", ratchet.derive_key());
```

#### Getting the previous versions of a ratchet.

```rs
use skip_ratchet::Ratchet;

let mut old_ratchet = Ratchet::new();
old_ratchet.inc_by(5);

let mut recent_ratchet = old_ratchet.clone();
recent_ratchet.inc_by(10);

for revision in recent_ratchet.previous(&old_ratchet, 10).unwrap() {
    println!("{:?}", String::from(&revision));
}
```

## Building the Project

- Clone the repository.

  ```bash
  git clone https://github.com/WebNativeFileSystem/rs-skip-ratchet.git
  ```

- Change directory

  ```bash
  cd rs-skip-ratchet
  ```

- Run tests

  ```bash
  cargo test --release
  ```

## Other Implementations

- [Typescript][ts-impl]
- [Go][go-impl]

[ts-impl]: https://github.com/fission-suite/webnative/blob/matheus23/wnfs2/src/fs/data/private/spiralratchet.ts
[go-impl]: https://github.com/qri-io/wnfs-go/tree/master/private/ratchet
[paper]: https://github.com/fission-codes/skip-ratchet-paper/blob/main/spiral-ratchet.pdf
