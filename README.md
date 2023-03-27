<div align="center">
  <a href="https://github.com/WebNativeFileSystem" target="_blank">
    <img src="https://raw.githubusercontent.com/WebNativeFileSystem/rs-skip-ratchet/main/assets/logo.svg" alt="Skip Ratchet Logo" width="100" height="100"></img>
  </a>

  <h1 align="center">Skip Ratchet</h1>

  <p>
    <a href="https://crates.io/crates/skip_ratchet">
      <img src="https://img.shields.io/crates/v/skip_ratchet?label=crates" alt="Crate Information">
    </a>
    <a href="https://codecov.io/gh/wnfs-wg/rs-skip-ratchet">
      <img src="https://codecov.io/gh/wnfs-wg/rs-skip-ratchet/branch/main/graph/badge.svg?token=95YHXFMFF4" alt="Code Coverage"/>
    </a>
    <a href="https://github.com/wnfs-wg/rs-skip-ratchet/actions?query=">
      <img src="https://github.com/wnfs-wg/rs-skip-ratchet/actions/workflows/checks.yaml/badge.svg" alt="Build Status">
    </a>
    <a href="https://github.com/wnfs-wg/rs-skip-ratchet/blob/main/LICENSE">
      <img src="https://img.shields.io/badge/License-Apache%202.0-blue.svg" alt="License">
    </a>
    <a href="https://docs.rs/skip-ratchet">
      <img src="https://img.shields.io/static/v1?label=Docs&message=docs.rs&color=blue" alt="Docs">
    </a>
    <a href="https://discord.gg/zAQBDEq">
      <img src="https://img.shields.io/static/v1?label=Discord&message=join%20us!&color=mediumslateblue" alt="Discord">
    </a>
  </p>
</div>

This library implements the [Skip Ratchet paper][paper]. Skip ratchet is a data structure for deriving keys that maintain backward secrecy. Unlike hash chains, this data structure is capable of efficiently making large leaps in hash count.

## Outline

- [Usage](#usage)
- [Building the Project](#building-the-project)
- [Testing the Project](#testing-the-project)
- [Contributing](#contributing)
- [Getting Help](#getting-help)
- [License](#license)

## Usage

#### Creating a new ratchet and advancing it.

```rust
use skip_ratchet::Ratchet;

let mut ratchet = Ratchet::new();
ratchet.inc_by(10);

println!("{:?}", ratchet.derive_key());
```

#### Getting the previous versions of a ratchet.

```rust
use skip_ratchet::Ratchet;

let mut old_ratchet = Ratchet::new();
old_ratchet.inc_by(5);

let mut recent_ratchet = old_ratchet.clone();
recent_ratchet.inc_by(10);

for revision in recent_ratchet.previous(&old_ratchet, 10).unwrap() {
    println!("{:#?}", revision);
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

- Build the project

  ```bash
  cargo build
  ```

## Testing the Project

- Run tests

  ```bash
  cargo test
  ```

## Contributing

### Pre-commit Hook

This library recommends using [pre-commit][pre-commit] for running pre-commit hooks. Please run this before every commit and/or push.

- Once installed, Run `pre-commit install` to setup the pre-commit hooks locally.  This will reduce failed CI builds.
- If you are doing interim commits locally, and for some reason if you _don't_ want pre-commit hooks to fire, you can run
  `git commit -a -m "Your message here" --no-verify`.

### Conventional Commits

This project *lightly* follows the [Conventional Commits convention][commit-spec-site]
to help explain commit history and tie in with our release process. The full
specification can be found [here][commit-spec]. We recommend prefixing your
commits with a type of `fix`, `feat`, `docs`, `ci`, `refactor`, etc...,
structured like so:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

## Getting Help

For usage questions, usecases, or issues reach out to us in our [Discord webnative-fs channel](https://discord.gg/YbT6x7Wkvk).
We would be happy to try to answer your question or try opening a new issue on Github.

## License

This project is licensed under the [Apache License 2.0](https://github.com/wnfs-wg/rs-skip-ratchet/blob/main/LICENSE).

[commit-spec]: https://www.conventionalcommits.org/en/v1.0.0/#specification
[commit-spec-site]: https://www.conventionalcommits.org/
[paper]: https://eprint.iacr.org/2022/1078.pdf
[pre-commit]: https://pre-commit.com/
