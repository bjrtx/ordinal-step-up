/-
  # Challenge: the Erdős–Rado negative stepping-up lemma

  A negative partition relation `κ ↛ (β)ʳ_μ` says there is a colouring of the
  `r`-subsets of `κ` in `μ` colours with no monochromatic set of order type
  `β`. The stepping-up lemma propagates such a failure one exponent up:

      κ ↛ (θ)ʳ⁺³_μ  ⟹  2^κ ↛ (θ)ʳ⁺⁴_μ

  for `θ` additively indecomposable (meaning of the form `ω^α` with `0 < α`)
  and at least two colours. See Section 24 of
  Erdős–Hajnal–Máté–Rado, *Combinatorial Set Theory: Partition Relations for
  Cardinals*, North-Holland 1984; the presentation followed is D. J. de Graaf,
  *"A partition calculus in set theory" by Erdős and Rado for readers from the
  twenty-first century*, MoL-2021-07, ILLC, University of Amsterdam, 2021,
  where this is Theorem 4.18.

  This module is deliberately self-contained: it imports only Mathlib, states
  the vocabulary it needs, and leaves the theorem as `sorry`.

  ## Reading the statement

  A subset of `κ` is a set of ordinals, so a colouring that witnesses
  κ ↛ (θ)ʳ⁺³_μ takes `Finset Ordinal` and produces an ordinal `< μ`, hence
  the colouring type `Finset Ordinal → Set.Iio μ`. Note that the colouring's
  values on sets that are not `(r+3)`-subsets of `κ` are immaterial.

  Similarly, via the bijection `𝒫(κ) = 2^κ`, a colouring of its `(r+4)`-subsets is
  a map `Finset (Set Ordinal) → Set.Iio μ`, again with junk values at sets that are not
  `(r+4)`-subsets of `𝒫(κ)`.
  "No monochromatic set of order type `θ`" is `NoHomog`; the
  downstairs form, for colourings of `Finset Ordinal`, is `NoHomogOrd`.

  Since the colourings are total, `κ` enters instead as a bound on the sets
  quantified over: `𝒜 ⊆ Set.Iio κ` downstairs and `𝒜 ⊆ 𝒫(Set.Iio κ)`
  upstairs. The bound is not a convenience. Without it these say that *no*
  set of ordinals of type `θ` is monochromatic, which the positive
  Erdős–Rado theorem rules out -- so the hypothesis would be unsatisfiable
  and the implication empty.

  Order types are taken with respect to a fixed but arbitrary well-order on
  `2^κ` (`WO`) upstairs, and with respect to the ordinals' own ordering
  (`ordWO`) downstairs. Both colourings are existentially quantified, so no
  particular construction appears in the statement.
-/
import Mathlib.SetTheory.Ordinal.Exponential

universe u

namespace OrdinalStepUp.ErdosRado

open Ordinal

/-- An arbitrary well-order on `2^κ`. -/
abbrev WO : WellOrder := ⟨Set Ordinal, WellOrderingRel, WellOrderingRel.isWellOrder⟩

/-- The usual ordering of the ordinals. -/
abbrev ordWO : WellOrder := ⟨Ordinal, (· < ·), inferInstance⟩

/-- `𝒜` is monochromatic in colour `ι` for the `r`-subset-colouring `f`. -/
def Mono {μ : Ordinal} {V : Type*} (f : Finset V → Set.Iio μ) (r : ℕ) (𝒜 : Set V)
    (ι : Set.Iio μ) : Prop :=
  ∀ 𝒯 : Finset V, ↑𝒯 ⊆ 𝒜 → 𝒯.card = r → f 𝒯 = ι

/-- The order type of a set with respect to a well-order on the ambient type. -/
noncomputable def otpOf (wo : WellOrder) (𝒜 : Set wo.α) : Ordinal.{u} :=
  .type (Subrel wo.r (· ∈ 𝒜))

/-- No colour of `f` has a homogeneous subset of `κ` of order type `θ`: the
negative arrow `κ ↛ (θ)ʳ`, downstairs. -/
def NoHomogOrd {μ : Ordinal} (κ : Ordinal) (f : Finset Ordinal → Set.Iio μ) (r : ℕ)
    (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set Ordinal, 𝒜 ⊆ Set.Iio κ → otpOf ordWO 𝒜 = θ → ∀ ι, ¬ Mono f r 𝒜 ι

/-- The same one level up, on `𝒫(κ) ≃ 2^κ`: `2^κ ↛ (θ)ʳ`. -/
def NoHomog {μ : Ordinal} (κ : Ordinal) (f : Finset (Set Ordinal) → Set.Iio μ) (r : ℕ)
    (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set (Set Ordinal), 𝒜 ⊆ Set.powerset (Set.Iio κ) → otpOf WO 𝒜 = θ →
    ∀ ι, ¬ Mono f r 𝒜 ι

variable {r : ℕ} {κ : Ordinal}

/-- **The Erdős–Rado negative stepping-up lemma** (de Graaf 2021, Theorem 4.18;
Erdős–Hajnal–Máté–Rado §24).

If some colouring of the `(r+3)`-subsets of `κ` in `μ` colours has no
monochromatic set of order type `ω^α`, then neither does some colouring of the
`(r+4)`-subsets of `2^κ`. -/
theorem noHomog_stepUp {μ α : Ordinal} (hα : 0 < α) (hμ : 1 < μ)
    (h : ∃ g : Finset Ordinal → Set.Iio μ, NoHomogOrd κ g (r + 3) (ω^α)) :
    ∃ f : Finset (Set Ordinal) → Set.Iio μ, NoHomog κ f (r + 4) (ω^α) := by
  sorry

end OrdinalStepUp.ErdosRado
