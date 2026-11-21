# Weak-Head Normalizability of λenv and its Characterization by Intersection Types

Isabelle/HOL formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Weak-Head Normalizability of λenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

## Main result

For every raw term `M` of the calculus λenv with first-class environments
(theory `Final`, theorem `lambda_env_WHN_characterization`):

```
theorem lambda_env_WHN_characterization:
  "Typ M <-> CFWHN M"   "Typ M <-> CFWHSN M"
```

- `Typ M`: `M` has an essential type (a type not equivalent to ω) in the intersection
  type system with environment types, in some environment-type context.
- `CFWHN M`: `M` weak-head reduces to a clash-free weak-head normal form.
- `CFWHSN M`: every weak-head reduction sequence from `M` is finite and every weak-head
  normal form reachable from `M` is clash-free.

Weak-head reduction is full σ-reduction together with head β-reduction. Further results:

- Pure λ-terms (theory `Readback`, `E1`): for a pure `M`, the de Bruijn readback of `M`
  is weak-head normalizable in the λ-calculus iff `CFWHN M`, iff `CFWHSN M`; hence
  `Typ M` holds iff the readback is weak-head normalizable (`Main_Results`,
  `pure_characterization`).
- Agreement with the classical intersection type system on λ-terms (theories `CDV`,
  `Classical`): a λ-term is weak-head normalizable iff it has an essential type in the
  classical system (`classical_WHN`); hence, for a pure `M`, `Typ M` holds iff the
  readback of `M` is typable there (`E2`).
- Uniqueness of weak-head normal forms (theory `Uniform`, `WHNF_unique`).

## Theories

The session `LambdaEnvWeakHead` consists of 16 theories (about 4,000 lines).

| Theory | Contents | Main results |
| --- | --- | --- |
| `ARS`, `Syntax` | abstract rewriting, terms; normal forms, SN | |
| `Reduction` | σ-reduction, head β-reduction, weak-head reduction, finite branching | `sig_SN` |
| `Sig_Confluence` | critical pairs, Newman's lemma | `sig_confluent` |
| `WHNF_Classes` | neutral terms, values, clashes | `WHNF_iff_classes` |
| `Lambda`, `Readback` | de Bruijn λ-calculus, readback | `E1` |
| `Typing` | types, subtyping, typing, generation lemmas | `narrowing`, `gen_*` |
| `Completeness` | subject expansion | `subject_expansion`, `completeness` |
| `Soundness` | realizability interpretation, basic lemma | `soundness`, `clash_not_Typ`, `main_characterization` |
| `Main_Results` | the characterization restricted to pure terms | `pure_characterization` |
| `Uniform` | weak and strong weak-head normalization coincide | `CFWHN_imp_CFWHSN_general`, `WHNF_unique` |
| `CDV`, `Classical` | classical intersection types on λ-terms | `classical_WHN`, `E2` |
| `Examples` | the examples of the paper | |
| `Final` | summary | `lambda_env_WHN_characterization` |

The theories contain no `sorry`, `oops`, `axiomatization`, `ML` code, `consts` or other
unchecked declarations, and the session is built with `quick_and_dirty` and
`skip_proofs` disabled. The only use of choice is Hilbert's ε (`SOME`) to name the
σ-normal form, which is part of standard HOL.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).

```bash
isabelle build -d isabelle LambdaEnvWeakHead
```

To also produce the theory documents (requires LaTeX):

```bash
isabelle build -o document=pdf -d isabelle LambdaEnvWeakHead
```

The output is written to `isabelle/output/`.

## File layout

```
isabelle/ROOT             session LambdaEnvWeakHead
isabelle/*.thy            the 16 theories
isabelle/document/root.tex
docs/document.pdf         theory document: all theories with proofs
docs/outline.pdf          theory document: all theories with proofs omitted
```

## Related repositories

- Lean 4 port of this development:
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types-lean>
- Call-by-value counterpart (Isabelle/HOL):
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types>,
  and its Lean 4 port:
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types-lean>
- The same questions for λpenv:
  <https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types>,
  <https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types>

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Please cite the paper:

> Shin-ya Nishizaki and Shogo Murasaki.
> Weak-Head Normalizability of λenv and its Characterization by Intersection Types,
> Formalized in Isabelle/HOL.
