# The Erdős–Rado negative stepping-up lemma

A Lean 4 formalisation of the negative stepping-up lemma for ordinal order
types: if some colouring of the `(r+3)`-subsets of `κ` in `μ` colours admits no
monochromatic subset of `κ` of order type `ω^α`, then some colouring of the
`(r+4)`-subsets of `2^κ` admits none either.

    κ ↛ (ω^α)ʳ⁺³_μ  ⟹  2^κ ↛ (ω^α)ʳ⁺⁴_μ

The presentation followed is D. J. de Graaf, *"A partition calculus in set
theory" by Erdős and Rado for readers from the twenty-first century*,
MoL-2021-07, ILLC, University of Amsterdam, 2021, where this is Theorem 4.18;
the result is Section 24 of Erdős–Hajnal–Máté–Rado, *Combinatorial Set Theory:
Partition Relations for Cardinals*, North-Holland 1984.

## Layout

| path | |
|---|---|
| `OrdinalStepUp/Solution.lean` | the development, importing nothing but Mathlib |
| `OrdinalStepUp/Challenge.lean` | the same statement with a `sorry`, for Comparator |
| `comparator.json` | names the declarations Comparator compares |
| `formalization.yaml` | submission metadata (formalization.yaml v0.4) |

`Solution.lean` serves as the Solution directly, so Comparator checks the
development itself rather than a restatement of it. The two files declare the
same six definitions and the same theorem, and `#print` of each agrees byte for
byte under `pp.universes` and `pp.numericTypes`.

## Building

    lake build              -- the development; no sorry
    lake build Challenge    -- the Challenge; one deliberate sorry

`Challenge` is kept out of `defaultTargets` so that its `sorry` does not warn on
every build.

`noHomog_stepUp` and `stepUp_noHomog` depend on `propext`, `Classical.choice`
and `Quot.sound`, and on nothing else.

## Licence

Apache-2.0
