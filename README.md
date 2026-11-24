# A finite-state lower bound for fourteen-symbol superpermutations

Jaehun Jung · Independent Researcher, Republic of Korea

The submission proves that every fourteen-symbol superpermutation has at least 93,891,141,157 letters. The formal entry is `AlmanacSubmission.lower_fourteen` in `AlmanacSolution.lean`. The proof uses the finite-state geometry and packing lemmas in `LitBound/Next14/`. The paper gives the mathematical derivation and identifies the publicly recorded upper endpoint.

The paper's companion supplement, `fourteen-symbol-verification.zip` (SHA-256 `60d28965395db30a7841933ac6d298af2c6e286b35b843b84206732ea002df0d`), contains the data and checkers for its additional construction. The lower-bound entry builds from the sources in this repository.

## Build

Install the version in `lean-toolchain` with elan. From this repository's root, run:

```sh
lake exe cache get
lake build AlmanacSolution
```

The three reserved challenge files come from the Almanac's official version 5 batch scaffold. The sole direct package dependency is the required mathlib revision, pinned in `lake-manifest.json`. The third-party proof modules copied from Jay Pantone's public formalization at revision `ad72ab5010e945b5c8768a918281778c834dcc40` retain their source bytes. `SOURCE-PROVENANCE.tsv` records their original paths and SHA-256 digests. See `LICENSE`, `NOTICE` and `licenses/` for upstream notices. The original paper's authorship and AI disclosure are in `paper/`.

[Almanac Lean submissions](https://superpermutations.com/docs/lean) · [Pantone's formalization](https://github.com/jaypantone/2026-10-superpermutation-lower-palomar/tree/ad72ab5010e945b5c8768a918281778c834dcc40)
