/-
# The Erdős–Rado negative stepping-up lemma

This module proves the Erdős–Rado negative stepping-up lemma, an implication
that (when it applies) propagates negative partition relations. It takes the
form

    κ ↛ (β)ʳ_μ  ⟹  2^κ ↛ (β)^{r+1}_μ          (1)

for `r ≥ 3`, `μ` a cardinal, `β > 0` an ordinal and `κ` a cardinal. Here
κ ↛ (β)ʳ_μ means that there is a function (colouring) from the `r`-subsets of `κ` to
`μ` such that no subset of `κ` of order-type `β` is
monochromatic, meaning that all of its `r`-subsets are mapped to the same
value.

We prove (1) in the case where `β > 0` is additively indecomposable
(a.k.a. additively principal), meaning that either of the following
equivalent conditions hold:
* `β` is not the sum of two smaller ordinals,
* `β` is of the form `ω^γ` for some ordinal `γ`.
(See e.g. mathlib's `Ordinal.isPrincipal_add_iff_zero_or_omega0_opow` for the
equivalence.)

The proof follows the recent exposition [dG21], in which this result is
Theorem 4.18. In particular, every numbered result named below is from
[dG21]. The original references [ER56, EHMR] may prove difficult for modern readers.

## Sources

* [EHMR] P. Erdős, A. Hajnal, A. Máté and R. Rado, *Combinatorial Set Theory:
  Partition Relations for Cardinals*, Studies in Logic and the Foundations of
  Mathematics 106, North-Holland, 1984.
* [dG21] D. J. de Graaf, *"A partition calculus in set theory" by Erdős and
  Rado for readers from the twenty-first century*, MoL-2021-07, Master of
  Logic Thesis, ILLC, University of Amsterdam, 2021.
  <https://eprints.illc.uva.nl/id/eprint/1797>
* [ER56] P. Erdős and R. Rado, *A partition calculus in set theory*, Bulletin
  of the American Mathematical Society 62 (1956), 427-489.

## The idea

Via `𝒫(κ) ≃ 2^κ`, any point of `2^κ` is a set of ordinals. We equip `2^κ` with
* an arbitrary well-order `≺w`,
* the lexicographic order `≺` where `x ≺ y ↔ x ≠ y ∧ min (x Δ y) ∈ y`.

Given a finite `≺w`-chain `u₀ ≺w ⋯ ≺w uᵣ`, two objects record the
interplay of these two orders:
* the **`η`-pattern**, one bit per consecutive pair, saying whether the two
  orders *agree* there (`AgreeAt`);
* the **`δ`-sequence** `δⱼ = min (uⱼ Δ uⱼ₊₁)` of `r` ordinals.

The chain is *`K`-good* when its `η`-pattern is constant (meaning that said
chain is either increasing or decreasing under `≺`), and *`P₀`-good* when
moreover its discrepancies rise (`InP0`).

The stepped-up colouring `stepUpColour` spends two colours marking the chains
that fail these conditions in the first possible place — pattern `0,1` or
`1,0` (`InK01`, `InK10`), discrepancies rising then falling or the reverse
(`InP01`, `InP10`) — and on the `P₀` chains it simply copies `g` applied to
the discrepancy set `σ u` (`sigmaOf`).

## The shape of the proof

Suppose a set `𝒜 ⊆ 2^κ` of order type `θ` were homogeneous for the stepped-up
colouring. Whichever colour it takes, it must avoid one of the two marked
patterns, and the argument then shrinks `𝒜` twice while keeping order type `θ`:

* **Lemma 4.16** (`exists_homogeneous`): avoiding a mixed `η`-pattern yields a
  subset that is `K`-good.
* **Lemma 4.17** (`exists_all_disc_up`): avoiding a mixed `δ`-pattern then
  yields a subset whose discrepancies rise across every triple.
* **Lemma 4.14** (`lemma414`): on such a subset the stepped-up colouring is
  literally `g ∘ σ`, and `σ` is an order isomorphism onto its image, so a
  homogeneous set upstairs pushes down to one of the same order type for `g`
  downstairs — contradicting the hypothesis.

Both shrinking steps need that a set of type `θ` keeps type `θ` after an
initial piece is removed. That is **Lemma 4.15** (`otpOf_final_seg`), and
it requires `θ` to be additively indecomposable (`IsIndec`).
-/
import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases

namespace OrdinalStepUp.ErdosRado

open Ordinal

universe u

abbrev SetOrd := Set Ordinal
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}

noncomputable def disc (a b : SetOrd) : Ordinal := sInf (symmDiff a b)

lemma disc_comm (a b : SetOrd) : disc a b = disc b a := by
  rw [disc, disc, symmDiff_comm]

lemma disc_mem_symmDiff (_ : a ≠ b) : disc a b ∈ (a \ b) ∪ (b \ a) := by
  apply csInf_mem
  simp_all [← Set.symmDiff_def]

/-- Below the discrepancy, `a` and `b` agree. -/
lemma mem_iff_of_lt_disc (h : α < disc a b) : α ∈ a ↔ α ∈ b := by
  have : α ∉ (a \ b) ∪ (b \ a) := fun hmem => absurd (csInf_le' hmem) (not_le.mpr h)
  constructor <;> simp_all

/-- The lexicographic order on sets of ordinals -/
def LexLT (a b : SetOrd) : Prop := disc a b ∈ b \ a
scoped infix:50 " ≺ " => LexLT

/-- If `a` and `b` agree below `t`, `a` lacks the bit at `t` and `b` has it,
then `t` is exactly `disc a b`. -/
lemma disc_eq_of_agree_before_and_differ_at
    (hagree : ∀ β < α, (β ∈ a ↔ β ∈ b)) (ha : α ∉ a) (hb : α ∈ b) :
    disc a b = α := by
  have hab : a ≠ b := (·.symm ▸ hb |> ha)
  refine le_antisymm (csInf_le' (Or.inr ⟨hb, ha⟩)) (not_lt.1 fun hlt => ?_)
  rcases disc_mem_symmDiff hab <;> simp_all [hagree _ hlt]

/-- Matching lemma for `LexLT` itself. -/
lemma lexLT_of_agree_before_and_differ_at
    (hagree : ∀ β < α, (β ∈ a ↔ β ∈ b)) (ha : α ∉ a) (hb : α ∈ b) : a ≺ b := by
  split_ands <;> simp_all [disc_eq_of_agree_before_and_differ_at hagree ha hb]

/-- Transitivity of the lexicographic order. -/
lemma lexLT_trans (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c := by
  unfold LexLT at *
  -- Below either split point `a` and `c` agree, both agreeing with `b` there.
  have key {s t} (h1: t ≤ disc a b) (h2: t ≤ disc b c) (hs: s < t): (s ∈ a ↔ s ∈ c) :=
    (mem_iff_of_lt_disc (hs.trans_le h1)).trans (mem_iff_of_lt_disc (hs.trans_le h2))
  -- The earlier split wins. The middle case is impossible: `b` would both
  -- contain and lack the common split point.
  rcases lt_trichotomy (disc a b) (disc b c) with hlt | heqdisc | hlt
  · exact lexLT_of_agree_before_and_differ_at (@key · _ le_rfl hlt.le) hab.2
      (mem_iff_of_lt_disc hlt |>.mp hab.1)
  · simp_all
  · exact lexLT_of_agree_before_and_differ_at (@key · _ hlt.le le_rfl)
      (mem_iff_of_lt_disc hlt |>.mp · |> hbc.2) hbc.1

/-- Consecutive discrepancies along a lexicographically increasing triple are
distinct. -/
lemma disc_ne_disc_of_lexLT (hab : a ≺ b) (hbc : b ≺ c) : disc a b ≠ disc b c :=
  (· ▸ hab.1 |> hbc.2)

/-- Observation 4.2: the earlier split wins. If `a` and `b` part company
strictly before `b` and `c` do, then `a` and `c` part company at exactly the
same place as `a` and `b`. -/
lemma disc_eq_of_disc_lt_disc (hab : a ≠ b) (h : disc a b < disc b c) : disc a c = disc a b := by
  have hagree α (hα : α < disc a b) : (α ∈ a ↔ α ∈ c) :=
    (mem_iff_of_lt_disc hα).trans (mem_iff_of_lt_disc (hα.trans h))
  have hbc : disc a b ∈ b ↔ disc a b ∈ c := mem_iff_of_lt_disc h
  rcases disc_mem_symmDiff hab with hd | hd
  · rw [disc_comm]
    exact disc_eq_of_agree_before_and_differ_at (hagree · · |>.symm) (hbc.2 · |> hd.2) hd.1
  · exact disc_eq_of_agree_before_and_differ_at hagree hd.2 (hbc.1 hd.1)

instance instIsStrictTotalOrderLexLT : IsStrictTotalOrder SetOrd LexLT where
  irrefl := by simp [LexLT]
  trichotomous := by grind only [LexLT, disc_comm, !disc_mem_symmDiff, = Set.mem_union]
  trans := by apply lexLT_trans

/-! ## The auxiliary well-order

The second of the two orders, whose only notable property is being a
well-order. -/

/-- An arbitrary well-order on `2^κ`, unrelated to the lexicographic one. -/
abbrev WO : WellOrder := ⟨Set Ordinal, WellOrderingRel, WellOrderingRel.isWellOrder⟩

@[inherit_doc WO] scoped infix:50 " ≺w " => WO.r

/-! ## Agreement of the two orders

The whole construction turns on a single bit attached to a pair `a ≺w b`: do
`≺w` and `≺` rank the pair the same way? -/

/-- The two orders agree on `{a, b}`. -/
def Agree (a b : SetOrd) : Prop := a ≺w b ↔ a ≺ b

/-- On a `≺w`-ordered pair, agreement says exactly that `≺` runs the same way. -/
lemma agree_iff_lexLT (hab : a ≺w b) : Agree a b ↔ a ≺ b := by simp_all [Agree]

lemma agree_comm : Agree a b ↔ Agree b a := by
  rcases eq_or_ne a b with rfl | hne
  · rfl
  have hw : (a ≺w b) ↔ ¬ b ≺w a :=
    ⟨asymm, fun h => (trichotomous_of WO.r a b).resolve_right (·.elim hne h)⟩
  have hl : (a ≺ b) ↔ ¬ b ≺ a :=
    ⟨asymm, fun h => (trichotomous_of LexLT a b).resolve_right (·.elim hne h)⟩
  exact (iff_congr hw hl).trans not_iff_not

/-- Distinct points are `≺`-comparable, so failing to increase means decreasing. -/
lemma lexLT_of_not_lexLT (hab : a ≺w b) (h : ¬ a ≺ b) : b ≺ a := by
  by_contra
  have e : a = b := by grind [trichotomous_of LexLT a b]
  exact irrefl b (e ▸ hab)

/-! ## Order-type-valued arrows -/

/-- `𝒜` is monochromatic in colour `ι` for the `r`-subset colouring `f`. -/
def Mono {V : Type*} (f : Finset V → Set.Iio μ) (r : ℕ) (𝒜 : Set V) (ι : Set.Iio μ) : Prop :=
  ∀ 𝒯 : Finset V, ↑𝒯 ⊆ 𝒜 → 𝒯.card = r → f 𝒯 = ι

/-- The order type of a set with respect to a well-order on the ambient type. -/
noncomputable def otpOf (wo : WellOrder)
    (𝒜 : Set wo.α) : Ordinal.{u} := .type (Subrel wo.r (· ∈ 𝒜))
/-- The order type of `𝒜 ⊆ 2^κ` under `≺w`: [dG21]'s `otp(𝒜, <)`. -/
noncomputable abbrev otp := otpOf WO

/-- `θ → (τ ι)ʳ_{ι<μ}` with order-type targets: under every colouring of the
`r`-subsets of a set of order type `θ` by fewer than `μ` colours, some colour
`ι` has a monochromatic subset of order type `τ ι`. -/
def ArrowsOrdToOrd (wo : WellOrder) (r : ℕ) (μ : Ordinal) (τ : Set.Iio μ → Ordinal.{u}) : Prop :=
  ∀ 𝒜 : Set _, otpOf wo 𝒜 = θ →
  ∀ f : Finset _ → Set.Iio μ,
    ∃ ι : Set.Iio μ, ∃ ℬ ⊆ 𝒜, otpOf wo ℬ = τ ι ∧ Mono f r ℬ ι

/-! ## Chains and their patterns

A colouring upstairs takes an `(r+1)`-subset of `2^κ`; we start by
putting its points in `≺w`-increasing order. -/

/-- A finite sequence `Fin n → SetOrd` that is strictly increasing for `≺w`. -/
abbrev FinChain (n : ℕ) := @RelEmbedding (Fin n) _ (· < ·) WO.r

/-- Build a chain from a strictly increasing map. -/
def FinChain.mk (f : Fin n → SetOrd)
    (mono : ∀ i j : Fin n, i < j → f i ≺w f j) : FinChain n :=
  RelEmbedding.ofMonotone f mono

@[simp] lemma FinChain.mk_apply (f : Fin n → SetOrd)
    (mono : ∀ i j : Fin n, i < j → f i ≺w f j) (i : Fin n) :
    FinChain.mk f mono i = f i := rfl

/-! ### The `η`-pattern, and the sets `K`

The pattern of a chain is the string of bits `AgreeAt u 0, AgreeAt u 1, …`. A
chain is well behaved when that string is constant: `K₀` if the two orders
agree everywhere along it, `K₁` if they disagree everywhere. The colouring only
ever needs to detect the *first* deviation, so the named exceptional classes
are the two ways a pattern can start `0,1` or `1,0`. -/

def AgreeAt (u : FinChain (n + 1)) (j : Fin n) : Prop := u j.castSucc ≺ u j.succ
  /- j.castSucc is j + 1 as a Fin (n + 1), i.e. a valid index. -/

/-- `K₀`: the two orders agree on every consecutive pair. -/
def InK0 (u : FinChain (n + 1)) : Prop := ∀ j, AgreeAt u j

/-- `K₁`: they disagree on every consecutive pair. -/
def InK1 (u : FinChain (n + 1)) : Prop := ∀ j, ¬ AgreeAt u j

/-- `K(0,1)`: the pattern begins `0, 1`. -/
def InK01 (u : FinChain (n + 3)) : Prop := AgreeAt u 0 ∧ ¬ AgreeAt u 1

/-- `K(1,0)`: the pattern begins `1, 0`. -/
def InK10 (u : FinChain (n + 3)) : Prop := ¬ AgreeAt u 0 ∧ AgreeAt u 1

/-- A chain whose pattern begins `0, 1` is in neither `K₀` nor `K₁`. -/
lemma not_inK_of_inK01 {u : FinChain (n + 3)} (h : InK01 u) : ¬ (InK0 ⊔ InK1) u :=
  (Or.elim · (h.2 <| · 1) (·  0 h.1))

/-! ### The `δ`-sequence, and the sets `P`

`δ(u)` is the sequence of discrepancies of consecutive pairs. -/

/-- `δ(u)`: the discrepancies of the consecutive pairs. -/
noncomputable def discSeq (u : FinChain (n + 1)) (j : Fin n) : Ordinal :=
  disc (u j.castSucc) (u j.succ)

/-- `P₀`: `u ∈ K₀ ∪ K₁` and its discrepancies increase along the chain. -/
def InP0 (u : FinChain (n + 2)) : Prop :=
  (InK0 ⊔ InK1) u ∧ ∀ j : Fin n, discSeq u j.castSucc < discSeq u j.succ

/-! ## Lemma 4.15: final segments keep their order type -/


/-- [dG21]'s *additively indecomposable* ordinals: not the sum of two
smaller ordinals, and past the degenerate cases `0` and `1`. These are exactly
the `ω^γ` with `0 < γ`, but that description is not needed below — what the
proofs use is the absorption property `α < θ → α + θ = θ`. -/
structure IsIndec (θ : Ordinal) : Prop where
  principal : Ordinal.IsPrincipal (· + ·) θ
  one_lt : 1 < θ

lemma IsIndec.ne_zero (hθ : IsIndec θ) : θ ≠ 0 :=
  fun h0 => absurd (h0 ▸ hθ.one_lt) (by simp)

/-- If `o` is additively principal and splits as `α + β` with `α < o`, then the
second summand is all of `o`. -/
lemma IsIndec.eq_of_add_eq_of_isPrincipal (hθ : IsIndec θ)
  (hα : α < θ) (h : α + β = θ) : β = θ :=
  add_left_cancel (h.trans (hθ.principal.add_eq_right hα).symm)

/- Lemma 4.15 in[dG21] states that a nonempty final segment of a set of order type `ω^γ`
again has order type `ω^γ`. That is two independent facts glued together:

* the order-theoretic half — splitting a well-order at a final
  segment adds the two order types, `otp 𝒜 = otp (𝒜 \ ℬ) + otp ℬ`;
* the arithmetic half  — an additively principal ordinal is not a sum
  of two strictly smaller ordinals.

`otpOf_final_seg` glues them, and `otpOf_final_seg_at` specialises to the
segments [dG21] actually cuts -- `{x ∈ 𝒜 | ¬ wo.r x x₀}` for a point `x₀ ∈ 𝒜`. -/

/-- **As well-orders, `𝒜` is `𝒜 \ ℬ` followed by `ℬ`.** If `ℬ` is a final
segment of `𝒜` then everything outside it precedes everything inside, so `𝒜`
is the lexicographic sum of the two pieces. -/
lemma nonempty_splitIso {𝒜 ℬ : Set wo.α} (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ) :
    Nonempty (Sum.Lex (Subrel wo.r (· ∈ 𝒜 \ ℬ)) (Subrel wo.r (· ∈ ℬ))
      ≃r Subrel wo.r (· ∈ 𝒜)) := by
  rcases ℬ.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · -- nothing is removed, and the second summand is empty
    rw [Set.sdiff_empty]; exact ⟨RelIso.sumLexEmpty _ _⟩
  -- `m` is the least element of `ℬ`; this is the point we cut at.
  set m := wo.wo.wf.min ℬ ⟨y₀, hy₀⟩ with hm
  have hmB : m ∈ ℬ := wo.wo.wf.min_mem _ _
  -- Being outside `ℬ` is the same as lying below the cut: below by minimality
  -- of `m`, and above only if `hfinal` has already pulled the point into `ℬ`.
  have key {a} : a ∈ 𝒜 → (wo.r a m ↔ a ∉ ℬ) := fun haA =>
    ⟨fun h hB => wo.wo.wf.not_lt_min _ hB h,
     fun hnB => (trichotomous_of wo.r a m).resolve_right fun h =>
       hnB (h.elim (· ▸ hmB) (hfinal m hmB a haA))⟩
  set R := Subrel wo.r (· ∈ 𝒜) with hR
  set x : {a // a ∈ 𝒜} := ⟨m, hBA hmB⟩ with hx
  -- A predicate on `𝒜` that describes membership of some `𝒟 ⊆ 𝒜` cuts out `𝒟`.
  have cut {p : {a // a ∈ 𝒜} → Prop} {𝒟 : Set wo.α} (h𝒟 : 𝒟 ⊆ 𝒜)
      (hp : ∀ a (h : a ∈ 𝒜), p ⟨a, h⟩ ↔ a ∈ 𝒟) : Subrel R p ≃r Subrel wo.r (· ∈ 𝒟) :=
    ⟨⟨fun q => ⟨q.1.1, (hp _ q.1.2).1 q.2⟩, fun q => ⟨⟨q.1, h𝒟 q.2⟩, (hp _ (h𝒟 q.2)).2 q.2⟩,
      fun _ => rfl, fun _ => rfl⟩, Iff.rfl⟩
  -- `key` says exactly that below the cut is `𝒜 \ ℬ`, and at or above it is `ℬ`.
  have e1 : Subrel R (R · x) ≃r Subrel wo.r (· ∈ 𝒜 \ ℬ) :=
    cut Set.sdiff_subset fun _ h => ⟨fun hr => ⟨h, (key h).1 hr⟩, fun hd => (key h).2 hd.2⟩
  have e2 : Subrel R (¬ R · x) ≃r Subrel wo.r (· ∈ ℬ) :=
    cut hBA fun _ h => (not_congr (key h)).trans not_not
  -- and a well-order is the lexicographic sum of the two sides of any cut.
  classical
  exact ⟨(RelIso.sumLexCongr e1.symm e2.symm).trans (RelIso.sumLexComplLeft R x)⟩


/-- Lemma 4.15. A final segment of a set of order type `θ` has order type
`θ` again, provided the part it omits is short. -/
lemma otpOf_final_seg
    {𝒜 ℬ : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ)
    (hsmall : otpOf wo (𝒜 \ ℬ) < otpOf wo 𝒜) :
    otpOf wo ℬ = otpOf wo 𝒜 :=
  have : otpOf _ (𝒜 \ ℬ) + otpOf _ ℬ = otpOf _ 𝒜 := by
    rw [otpOf, otpOf, otpOf, ← type_sum_lex]
    exact type_eq.2 (nonempty_splitIso hBA hfinal)
  hA.eq_of_add_eq_of_isPrincipal hsmall this

/-- The part of `𝒜` strictly below a point of `𝒜` is one of the initial
segments of `𝒜`'s own well-order, hence has strictly smaller order type. This
is what makes the smallness hypothesis of `otpOf_final_seg` automatic. -/
lemma otpOf_initial_lt {𝒜 : Set _} {x₀ : wo.α} (hx₀ : x₀ ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | wo.r y x₀} < otpOf wo 𝒜 := by
  have h : otpOf _ {x ∈ 𝒜 | wo.r x x₀} = typein (Subrel wo.r (· ∈ 𝒜)) ⟨x₀, hx₀⟩ := by
    rw [otpOf, ← type_subrel]
    exact type_eq.2 ⟨⟨⟨fun v ↦ ⟨⟨v.1, v.2.1⟩, v.2.2⟩, fun b ↦ ⟨b.1.1, b.1.2, b.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩⟩
  rw [h, otpOf]
  apply typein_lt_type

/-- Lemma 4.15 in the form [dG21] actually uses it: the final segment of
`𝒜` cut at a point `x₀ ∈ 𝒜` has the same order type `θ` as `𝒜` itself. -/
lemma otpOf_final_seg_at
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hx : x ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | ¬ wo.r y x} = otpOf wo 𝒜 := by
  refine otpOf_final_seg hA (fun _ hx => hx.1) ?_ ?_
  · exact fun _ ⟨hyB, hy⟩ _ hxA hyx ↦ ⟨hxA, hy ∘ (_root_.trans hyx)⟩
  · simp [otpOf_initial_lt hx]

/-! ## Lemma 4.16: a homogeneous subset of full order type -/
/-- If no subset of `𝒜` of full order type is
`P`-homogeneous, then some three-chain in `𝒜` has `P` on its first pair and not
on its second. -/
lemma exists_three_chain
    (P : wo.α → wo.α → Prop) {𝒜 : Set wo.α} (hA : IsIndec (otpOf wo 𝒜))
    (hD : ∀ ℬ, ℬ ⊆ 𝒜 → otpOf wo ℬ = otpOf wo 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → P u v) ∨ (∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → ¬ P u v))) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ P a b ∧ ¬ P b c := by
  by_contra hcon
  -- Missing the pattern means `P` propagates one step up any three-chain.
  have hstep : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, wo.r a b → wo.r b c → P a b → P b c := by
    grind only
  -- `𝒜` itself is not homogeneous, so somewhere `P` does hold on a pair.
  obtain ⟨a, ha, b, hb, hab, hPab⟩ : ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, wo.r a b ∧ P a b := by
    grind only
  -- Its top element then has `P` with everything above it, ...
  have hb_all {c} (hc : c ∈ 𝒜) (hbc : wo.r b c) : P b c := hstep a ha b hb c hc hab hbc hPab
  -- ... and that spreads to every pair of the final segment at `b`.
  refine hD {x ∈ 𝒜 | ¬ wo.r x b} (fun _ hx => hx.1) (otpOf_final_seg_at hA hb) (Or.inl ?_)
  rintro u ⟨huA, hub⟩ v ⟨hvA, -⟩ huv
  rcases trichotomous_of wo.r u b with h | h | h <;> try simp_all
  · exact hstep b hb u huA v hvA h huv (hb_all huA h)

/-- The mirror of `exists_three_chain`: a three-chain with `P` failing on the
first pair and holding on the second. -/
lemma exists_three_chain'
    (P : wo.α → wo.α → Prop) {𝒜 : Set wo.α} (hA : IsIndec (otpOf wo 𝒜))
    (hD : ∀ ℬ, ℬ ⊆ 𝒜 → otpOf wo ℬ = otpOf wo 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → P u v) ∨ (∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → ¬ P u v))) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ ¬ P a b ∧ P b c := by
  have := exists_three_chain (¬ P · · ) hA (by grind only)
  simp_all

/-- Every pair of `𝒜` agrees. For `|𝒜| ≥ r` this is what `[𝒜]ʳ ⊆ K₀` says,
since any two elements of `𝒜` are consecutive in some `r`-subset. -/
def AllAgree (𝒜 : Set SetOrd) : Prop := 𝒜.Pairwise Agree
/-- Every pair of `𝒜` disagrees: the same reading of `[𝒜]ʳ ⊆ K₁`. -/
def AllDisagree (𝒜 : Set SetOrd) : Prop := 𝒜.Pairwise (¬ Agree · ·)
abbrev HomAgree (𝒜 : Set SetOrd) : Prop := AllAgree 𝒜 ∨ AllDisagree 𝒜

/-- Lemma 4.16, at the level of pairs: if `𝒜` has order type `θ` and misses
one of the two three-point patterns, it has a homogeneous subset of the same
order type. The two hypotheses are [dG21]'s (i) and (ii), with `K(0,1)` and
`K(1,0)` unwound to the three-chains that witness them. -/
theorem exists_homogeneous (hA : IsIndec (otp 𝒜))
    (h : (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c) ∨
         (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ ¬ a ≺ b ∧ b ≺ c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧ HomAgree ℬ := by
  by_contra hcon
  have hcon : ∀ ℬ, ℬ ⊆ 𝒜 → otp ℬ = otp 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, u ≺w v → u ≺ v) ∨
         (∀ u ∈ ℬ, ∀ v ∈ ℬ, u ≺w v → ¬ u ≺ v)) := fun ℬ h1 h2 hor => hcon ⟨ℬ, h1, h2, by
    rcases hor with hag | hdis
    · left
      intro u hu v hv hne
      rcases trichotomous_of WO.r u v with huv | rfl | hvu
      · exact (agree_iff_lexLT huv).2 (hag u hu v hv huv)
      · exact absurd rfl hne
      · exact agree_comm.2 ((agree_iff_lexLT hvu).2 (hag v hv u hu hvu))
    · right
      intro u hu v hv hne
      rcases trichotomous_of WO.r u v with huv | rfl | hvu
      · exact mt (agree_iff_lexLT huv).1 (hdis u hu v hv huv)
      · exact absurd rfl hne
      · exact fun hag => mt (agree_iff_lexLT hvu).1 (hdis v hv u hu hvu) (agree_comm.1 hag)⟩
  rcases h with h1 | h2
  · exact h1 (exists_three_chain (· ≺ ·) hA hcon)
  · exact h2 (exists_three_chain' (· ≺ ·) hA hcon)

/-! ## Towards Lemma 4.17

Lemma 4.17 runs the same shape of argument one level up. Where 4.16 read the
`ε`-pattern of a chain, 4.17 reads the `δ`-sequence, whose own pattern is just
whether consecutive discrepancies increase or decrease. For that to be a
*two*-valued pattern, consecutive discrepancies must never be equal, and that
is where 4.17's homogeneity hypothesis (`[𝒜]ʳ ⊆ K₀` or `[𝒜]ʳ ⊆ K₁`) is spent. -/

/-- In a homogeneous set the auxiliary well-order and the lexicographic order
run either together (`K₀`) or exactly opposite (`K₁`). Either way the middle
element of a `≺w`-increasing triple lies lexicographically between the outer
two, and that is what keeps its two discrepancies apart. -/
lemma disc_ne_of_homogeneous (hA : HomAgree 𝒜)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a b ≠ disc b c := by
  have ne₁ : a ≠ b := fun e => irrefl _ (e ▸ hab)
  have ne₂ : b ≠ c := fun e => irrefl _ (e ▸ hbc)
  rcases hA with h | h
  · exact disc_ne_disc_of_lexLT ((agree_iff_lexLT hab).1 (h ha hb ne₁))
      ((agree_iff_lexLT hbc).1 (h hb hc ne₂))
  · -- Disagreement reverses the lexicographic order, so the triple runs backwards.
    have rev : ∀ {x y}, x ∈ 𝒜 → y ∈ 𝒜 → x ≠ y → x ≺w y → y ≺ x := fun hx hy hne hxy =>
      lexLT_of_not_lexLT hxy (mt (agree_iff_lexLT hxy).2 (h hx hy hne))
    exact fun heq => disc_ne_disc_of_lexLT (rev hb hc ne₂ hbc) (rev ha hb ne₁ hab)
      (by rw [disc_comm c b, disc_comm b a]; exact heq.symm)

/-- A singleton has order type `1`. -/
lemma otpOf_singleton {v}: otpOf wo {v} = 1 := by simp [otpOf]

/-- The part of `𝒜` strictly above one of its points still has order type
`θ`. This is `otpOf_final_seg_at` with the cut point itself removed: the
removed part has type `1`, and `θ` absorbs it. -/
lemma otpOf_gt_seg
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : wo.α} (hv : v ∈ 𝒜) : otpOf wo {x ∈ 𝒜 | wo.r v x} = otpOf wo 𝒜 := by
  have hcut := otpOf_final_seg_at hA hv
  refine Eq.trans (otpOf_final_seg (𝒜 := {x ∈ 𝒜 | ¬ wo.r x v}) (hcut ▸ hA)
    (fun _ hx => ⟨hx.1, asymm hx.2⟩) (fun _ hy _ hx hyx => ⟨hx.1, _root_.trans hy.2 hyx⟩) ?_) hcut
  have hdiff : {x ∈ 𝒜 | ¬ wo.r x v} \ {x ∈ 𝒜 | wo.r v x} = {v} := by
    ext
    grind only [irrefl_of wo.r, trichotomous_of wo.r, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
  rw [hdiff, otpOf_singleton, hcut]
  exact hA.one_lt

/-- A set of indecomposable order type is nonempty. -/
lemma nonempty_of_otpOf_eq
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) : 𝒜.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro rfl
  exact hA.ne_zero (show otpOf _ ∅ = 0 by simp [otpOf])

/-- A set of indecomposable order type has no greatest element. -/
lemma exists_wo_gt
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : _} (hv : v ∈ 𝒜) : ∃ w ∈ 𝒜, wo.r v w := by
  -- the part of `𝒜` strictly above `v` still has type `otpOf wo 𝒜`, so it is
  -- nonempty; any of its points is above `v`.
  have : IsIndec (otpOf wo {x ∈ 𝒜 | wo.r v x}) := by
    rw [otpOf_gt_seg hA hv]; exact hA
  obtain ⟨w, hw⟩ := nonempty_of_otpOf_eq this
  exact ⟨w, hw.1, hw.2⟩

/-- No set of full order type has its discrepancy going *down* across every
triple. -/
lemma not_all_down
    (d : wo.α → wo.α → Ordinal) {𝒞 : Set _} (hC : IsIndec (otpOf wo 𝒞))
    (hdown : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, wo.r a b → wo.r b c → d b c < d a b) : False := by
  set ℰ : SetOrd := {o | ∃ u ∈ 𝒞, ∃ v ∈ 𝒞, wo.r u v ∧ d u v = o} with hE
  obtain ⟨u, hu⟩ := nonempty_of_otpOf_eq hC
  obtain ⟨v, hv, huv⟩ := exists_wo_gt hC hu
  obtain ⟨u₀, hu₀, v₀, hv₀, hu₀v₀, hdeq⟩ : sInf ℰ ∈ ℰ := csInf_mem ⟨d u v, _, hu, _, hv, huv, rfl⟩
  obtain ⟨w, hw, hv₀w⟩ := exists_wo_gt hC hv₀
  have hlt : d v₀ w < sInf ℰ := hdeq ▸ hdown u₀ hu₀ v₀ hv₀ w hw hu₀v₀ hv₀w
  exact absurd hlt (not_lt.2 (csInf_le' ⟨v₀, hv₀, w, hw, hv₀w, rfl⟩))

/-- Lemma 4.17, with the discrepancy abstracted to an arbitrary `d`.

The two hypotheses are [dG21]'s (i) and (ii): `[𝒜]ʳ ∩ P(0,1) = ∅` says no
four-chain has its discrepancy go up then down, which -- since `hne` rules out
ties -- is the implication "up forces up again"; (ii) is the mirror. -/
theorem exists_all_up
    (d : wo.α → wo.α → Ordinal) {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    (hne : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, wo.r a b → wo.r b c → d a b ≠ d b c)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d a b < d b c → d b c < d c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d b c < d a b → d c e < d b c)) :
    ∃ ℬ ⊆ 𝒜, otpOf wo ℬ = otpOf wo 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, wo.r a b → wo.r b c → d a b < d b c := by
  rcases h with hi | hii
  · -- Case (i). Some triple goes up, ...
    obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hup⟩ :
        ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ d a b < d b c := by
      by_contra hno
      refine not_all_down d hA (fun a ha b hb c hc hab hbc => ?_)
      exact ((lt_trichotomy (d a b) (d b c)).resolve_left
        (fun h1 => hno ⟨a, ha, b, hb, c, hc, hab, hbc, h1⟩)).resolve_left
        (hne a ha b hb c hc hab hbc)
    -- ... and shifting the window one step at a time carries `up` past `c`.
    have h1 : ∀ e ∈ 𝒜, wo.r c e → d b c < d c e :=
      fun e he hce => hi _ ha _ hb _ hc _ he hab hbc hce hup
    have h2 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, wo.r c u → wo.r u v → d c u < d u v :=
      fun u hu v hv hcu huv => hi b hb c hc u hu v hv hbc hcu huv (h1 u hu hcu)
    have h3 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, ∀ w ∈ 𝒜, wo.r c u → wo.r u v → wo.r v w → d u v < d v w :=
      fun u hu v hv w hw hcu huv hvw => hi c hc u hu v hv w hw hcu huv hvw (h2 u hu v hv hcu huv)
    exact ⟨{x ∈ 𝒜 | wo.r c x}, fun _ hx => hx.1, otpOf_gt_seg hA hc,
      fun u hu v hv w hw huv hvw => h3 u hu.1 v hv.1 w hw.1 hu.2 huv hvw⟩
  · -- Case (ii). A single `down` triple would spread over a whole final segment.
    refine ⟨𝒜, subset_rfl, rfl, fun a ha b hb c hc hab hbc => ?_⟩
    rcases lt_trichotomy (d a b) (d b c) with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (hne a ha b hb c hc hab hbc)
    · exfalso
      have k1 : ∀ e ∈ 𝒜, wo.r c e → d c e < d b c :=
        (hii a ha b hb c hc · · hab hbc · h1)
      have k2 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, wo.r c u → wo.r u v → d u v < d c u :=
        fun u hu v hv hcu huv => hii b hb c hc u hu v hv hbc hcu huv (k1 u hu hcu)
      have k3 : ∀ u ∈ 𝒜, ∀ v ∈ 𝒜, ∀ w ∈ 𝒜, wo.r c u → wo.r u v → wo.r v w → d v w < d u v :=
        fun u hu v hv w hw hcu huv hvw => hii c hc u hu v hv w hw hcu huv hvw (k2 u hu v hv hcu huv)
      exact not_all_down d ((otpOf_gt_seg hA hc) ▸ hA)
        (fun u hu v hv w hw huv hvw => k3 u hu.1 v hv.1 w hw.1 hu.2 huv hvw)

/-- Lemma 4.17 for the actual discrepancy.-/
theorem exists_all_disc_up (hA : IsIndec (otp 𝒜)) (hom : HomAgree 𝒜)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc a b < disc b c → disc b c < disc c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc b c < disc a b → disc c e < disc b c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, a ≺w b → b ≺w c → disc a b < disc b c :=
  exists_all_up disc hA
    (fun _ ha _ hb _ hc hab hbc => disc_ne_of_homogeneous hom ha hb hc hab hbc) h

/-! ## Towards Lemma 4.14

Lemma 4.14 transfers a homogeneous set `𝒟 ⊆ 2^κ` for the stepped-up colouring
back down to a homogeneous set `𝒜 ⊆ κ` for the original one, by sending `𝒟`'s
increasing enumeration `⟨h_ξ⟩` to the discrepancies
`δ_ξ = disc (h_ξ) (h_{ξ+1})` of its consecutive pairs. -/

/-- On an all-`up` set, skipping ahead does not move a discrepancy: the pair
`a, c` parts company exactly where `a` and its nearer companion `b` do. This is
Observation 4.2 with the `P₀` hypothesis supplying its comparison. -/
lemma disc_eq_of_allUp
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a c = disc a b :=
  disc_eq_of_disc_lt_disc (fun h => irrefl _ (h ▸ hab)) (hB a ha b hb c hc hab hbc)

/-- On an all-`up` set, discrepancies of disjoint pairs compare: from `a ≺w b`,
`b = c` or `b ≺w c`, and `c ≺w e`, it follows that `disc a b < disc c e`. With
`b = c` this is the hypothesis itself; with `b ≺w c` it is two applications
chained. -/
lemma disc_lt_disc_of_allUp
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b = c ∨ b ≺w c) (hce : c ≺w e) : disc a b < disc c e := by
  rcases hbc with rfl | hbc
  · exact hB a ha b hb e he hab hce
  · exact lt_trans (hB a ha b hb c hc hab hbc) (hB b hb c hc e he hbc hce)

/-- A map that is strictly increasing on `𝒜` is an order isomorphism onto its
image, so it carries the order type across unchanged. -/
lemma otpOf_image {𝒜 : Set _} {f} (hf : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, wo.r a b → wo'.r (f a) (f b)) :
    otpOf wo' (f '' 𝒜) = otpOf wo 𝒜 := by
  have hmono : ∀ a b : {x // x ∈ 𝒜}, Subrel wo.r (· ∈ 𝒜) a b →
      Subrel wo'.r (· ∈ f '' 𝒜) ⟨f a.1, a.1, a.2, rfl⟩ ⟨f b.1, b.1, b.2, rfl⟩ :=
    fun a b => hf a.1 a.2 b.1 b.2
  refine type_eq.2 ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ hmono) ?_).symm⟩
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The least element of `𝒜` strictly above `x`, or `x` itself if there is
none. In a well-order every non-maximal point has an immediate successor, so
this replaces [dG21]'s enumeration `⟨h_ξ⟩` and its index arithmetic. -/
noncomputable def nextIn (𝒜 : Set wo.α) (x : wo.α) : wo.α :=
  open Classical in
  if h : ∃ y, y ∈ 𝒜 ∧ wo.r x y then wo.wo.wf.min {y | y ∈ 𝒜 ∧ wo.r x y} h else x

lemma nextIn_mem {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : nextIn 𝒜 x ∈ 𝒜 := by
  rw [nextIn, dif_pos h]; exact (wo.wo.wf.min_mem _ h).1

lemma wo_nextIn {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : wo.r x (nextIn 𝒜 x) := by
  rw [nextIn, dif_pos h]; exact (wo.wo.wf.min_mem _ h).2

/-- Nothing of `𝒜` sits strictly between `x` and `nextIn wo 𝒜 x`. -/
lemma nextIn_le {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) {z : wo.α} (hz : z ∈ 𝒜)
    (hxz : wo.r x z) :
    nextIn 𝒜 x = z ∨ wo.r (nextIn 𝒜 x) z := by
  rcases trichotomous_of wo.r (nextIn 𝒜 x) z with hlt | heq | hgt
  · exact Or.inr hlt
  · exact Or.inl heq
  · rw [nextIn, dif_pos h] at hgt
    exact absurd hgt (wo.wo.wf.not_lt_min {y | y ∈ 𝒜 ∧ wo.r x y} ⟨hz, hxz⟩)

/-- The ordinals under their own ordering, bundled. -/
abbrev ordWO : WellOrder := ⟨Ordinal, (· < ·), inferInstance⟩

/-- Order type of a set of ordinals under their own ordering: the target side
of Lemma 4.14's transfer. -/
noncomputable abbrev otpOrd := otpOf ordWO

/-- [dG21]'s `δ_ξ`: the discrepancy from a point of `𝒜` to the next one. -/
noncomputable def discNext (𝒜 : Set SetOrd) (a : SetOrd) : Ordinal :=
  disc a (nextIn (wo := WO) 𝒜 a)


/-- On a `P₀`-homogeneous set the next-point discrepancy is the discrepancy to
*any* later point of the set. This is the step [dG21]
takes with Observation 4.2 after checking `δ_{ξᵢ} < δ(h_{ξᵢ+1}, h_{ξᵢ₊₁})`. -/
lemma discNext_eq
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a = disc a b := by
  have hex : ∃ b, b ∈ 𝒜 ∧ a ≺w b := ⟨b, hb, hab⟩
  rcases nextIn_le hex hb hab with heq | hlt
  · rw [discNext, heq]
  · exact (disc_eq_of_allUp hup ha (nextIn_mem hex) hb (wo_nextIn hex) hlt).symm

/-- `discNext` is strictly increasing on a `P₀`-homogeneous set of full type.
Rewriting the lower value with `discNext_eq` turns this into one instance of
the `P₀` hypothesis, on `a ≺ b ≺ nextIn b`. -/
lemma discNext_strictMono (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a < discNext 𝒜 b := by
  have hex : ∃ y, y ∈ 𝒜 ∧ b ≺w y := exists_wo_gt hA hb
  rw [discNext_eq hup ha hb hab, discNext]
  exact hup a ha b hb _ (nextIn_mem hex) hab (wo_nextIn hex)

/-- The converse: `discNext` reflects the order, so a chain of values pulls back
to a chain of points. With `discNext_strictMono` this makes `discNext` an order
isomorphism onto its image. -/
lemma wo_of_discNext_lt (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (h : discNext 𝒜 a < discNext 𝒜 b) :
    a ≺w b :=
  (trichotomous_of WO.r a b).resolve_right fun hr => hr.elim
    (fun e => absurd (e ▸ h) (irrefl _))
    (fun hba => absurd (discNext_strictMono hA hup hb ha hba) (asymm h))

/-- Lemma 4.14, order-type half. On a `P₀`-homogeneous set of type `θ` the map
"discrepancy to the next point" is strictly increasing, so its image -- the
source's `𝒜 ⊆ κ` -- has the same order type. -/
theorem otpOrd_discNext_image (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c) :
    otpOrd (discNext 𝒜 '' 𝒜) = otp 𝒜 :=
  otpOf_image (wo := WO) (wo' := ordWO) (f := discNext 𝒜)
    (fun _ ha _ hb hab => discNext_strictMono hA hup ha hb hab)

/-- Lemma 4.14, transfer half. Every chain of discrepancies in the image comes
from a chain of points of `𝒟` one longer: pull each value back through
`discNext` (which reflects the order, so the points come out in the right
order), then append the next point after the top one.

This is [dG21]'s `{δ_i | i < r - 1} = σ ({h_{ξᵢ} | i < r})`, with the last
index `ξ_{r-1} = ξ_{r-2} + 1` appearing here as `nextIn`. -/
theorem exists_chain_discSeq (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (w : Fin (n + 1) → Ordinal) (hmono : StrictMono w)
    (hw : ∀ i, w i ∈ discNext 𝒟 '' 𝒟) :
    ∃ u : FinChain (n + 2), (∀ i, u i ∈ 𝒟) ∧ ∀ j, discSeq u j = w j := by
  choose x hxD hxw using fun i => hw i
  -- The pulled-back points inherit the order, because `discNext` reflects it.
  have hxmono : ∀ i j : Fin (n + 1), i < j → x i ≺w x j := fun i j hij =>
    wo_of_discNext_lt hD hup (hxD i) (hxD j) (by rw [hxw i, hxw j]; exact hmono hij)
  set t : SetOrd := nextIn 𝒟 (x (Fin.last n)) with ht
  have hex : ∃ y, y ∈ 𝒟 ∧ x (Fin.last n) ≺w y := exists_wo_gt hD (hxD _)
  have htD : t ∈ 𝒟 := nextIn_mem hex
  have hlt : ∀ i : Fin (n + 1), x i ≺w t := by
    intro i
    rcases eq_or_lt_of_le (Fin.le_last i) with h | h
    · exact h ▸ wo_nextIn hex
    · exact _root_.trans (hxmono i _ h) (wo_nextIn hex)
  refine ⟨FinChain.mk (Fin.snoc x t) ?_, ?_, ?_⟩
  · -- the extended family is still increasing
    intro i j
    refine Fin.lastCases ?_ ?_ j
    · intro hij
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), i = i'.castSucc :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), (Fin.castSucc_castPred _ _).symm⟩
      simpa using hlt i'
    · intro j' hij
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), i = i'.castSucc :=
        ⟨i.castPred (Fin.ne_last_of_lt (hij.trans (Fin.castSucc_lt_last j'))),
          (Fin.castSucc_castPred _ _).symm⟩
      simpa using hxmono i' j' (by simpa using hij)
  · -- every point is in `𝒟`
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using htD
    · intro i'; simpa using hxD i'
  · -- and the discrepancies are the values we started from
    intro j
    change disc (Fin.snoc (α := fun _ => SetOrd) x t j.castSucc)
      (Fin.snoc (α := fun _ => SetOrd) x t j.succ) = w j
    rw [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ ?_ j
    · rw [Fin.succ_last, Fin.snoc_last]
      exact hxw _
    · intro j'
      rw [Fin.succ_castSucc, Fin.snoc_castSucc,
        ← discNext_eq hup (hxD _) (hxD _) (hxmono _ _ (Fin.castSucc_lt_succ (i := j')))]
      exact hxw _

/-! ## Finsets and chains

A colouring takes a `Finset`, but every property above is a property of a
chain. The two views are interchangeable: a finite subset of `2^κ` has exactly
one `≺w`-increasing enumeration, so sorting and forgetting the order are
mutually inverse (`chainOfFinset`, `FinChain.toFinset`). `mono_iff_chains` is
the payoff -- it lets the rest of the development speak only of chains. -/

/-- The reflexive closure of `≺w`. -/
def WOle (a b : SetOrd) : Prop := a = b ∨ a ≺w b

noncomputable instance : DecidableRel WOle := fun _ _ => Classical.dec _

instance : IsTrans SetOrd WOle := ⟨by
  rintro a b c (rfl | h) (rfl | h')
  exacts [Or.inl rfl, Or.inr h', Or.inr h, Or.inr (_root_.trans h h')]⟩

instance : Std.Antisymm WOle := ⟨fun a _ hab hba =>
  Or.elim hab id fun h => Or.elim hba Eq.symm fun h' =>
    absurd (_root_.trans h h') (irrefl a)⟩

instance : Std.Total WOle := ⟨by
  intro a b
  rcases WellOrderingRel.isWellOrder.toTrichotomous.rel_or_eq_or_rel_swap (a := a) (b := b)
  with h | rfl | h
  exacts [Or.inl (Or.inr h), Or.inl (Or.inl rfl), Or.inr (Or.inr h)]⟩

/-- The `≺w`-increasing enumeration of a finite subset of `2^κ`: the canonical
way to view a `Finset` as a chain. -/
noncomputable def chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) :
    FinChain n :=
  FinChain.mk (fun i => (𝒯.sort WOle).get (i.cast (by rw [Finset.length_sort, hT])))
    (fun {i j} hij => by
      have hp := (List.pairwise_iff_get.1 (Finset.pairwise_sort (r := WOle) 𝒯))
        (i.cast (by rw [Finset.length_sort, hT])) (j.cast (by rw [Finset.length_sort, hT])) hij
      rcases hp with heq | hlt
      · exact absurd (((𝒯.sort WOle).nodup_iff_injective_get.1 (Finset.sort_nodup _ _)) heq)
          (by simpa using hij.ne)
      · exact hlt)

lemma mem_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) (i : Fin n) :
    (chainOfFinset 𝒯 hT) i ∈ 𝒯 := by
  rw [← Finset.mem_sort (r := WOle)]
  exact List.get_mem _ _

/-- Every point of `T` is hit by its enumeration. -/
lemma exists_eq_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n)
    (ha : a ∈ 𝒯) : ∃ i, (chainOfFinset 𝒯 hT) i = a := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 ((Finset.mem_sort (r := WOle)).2 ha)
  refine ⟨k.cast (by rw [Finset.length_sort, hT]), by rw [← hk]; rfl⟩

open scoped Classical in
/-- The underlying finite set of a chain: the other half of the bridge. -/
noncomputable def FinChain.toFinset (u : FinChain n) : Finset SetOrd :=
  Finset.image u Finset.univ

lemma FinChain.mem_toFinset (u : FinChain n) {x : SetOrd} :
    x ∈ u.toFinset ↔ ∃ i, u i = x := by
  simp [FinChain.toFinset]

@[simp] lemma FinChain.card_toFinset (u : FinChain n) : u.toFinset.card = n := by
  rw [FinChain.toFinset, Finset.card_image_of_injective _ u.injective, Finset.card_univ,
    Fintype.card_fin]

/-- Sorting a finite set and then forgetting the order gives it back. -/
@[simp] lemma toFinset_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) :
    (chainOfFinset 𝒯 hT).toFinset = 𝒯 := by
  ext x
  rw [FinChain.mem_toFinset]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ mem_chainOfFinset 𝒯 hT i, exists_eq_chainOfFinset 𝒯 hT⟩

/-- The bridge's payoff: a colouring is monochromatic on `𝒜` exactly when it is
constant on the chains of `𝒜`. This is what lets the chain-shaped lemmas above
meet `ArrowsToOrd`, whose colourings eat `Finset`s. -/
lemma mono_iff_chains {f : Finset SetOrd → Set.Iio μ} {r : ℕ}
    {ι : Set.Iio μ} :
    Mono f r 𝒜 ι ↔ ∀ u : FinChain r, (∀ j, u j ∈ 𝒜) → f u.toFinset = ι := by
  constructor
  · intro h u hu
    exact h u.toFinset (fun _ hx => by
      obtain ⟨j, rfl⟩ := (FinChain.mem_toFinset u).1 hx
      exact hu j) u.card_toFinset
  · intro h T hTA hTcard
    rw [← toFinset_chainOfFinset T hTcard]
    exact h _ (hTA <| mem_chainOfFinset T hTcard ·)

/-! ## Lemma 4.14: pushing a homogeneous set back down

On a set whose discrepancies rise across every triple, the map
`x ↦ disc x (next x)` is strictly increasing, so it carries the set's order
type across unchanged; and the discrepancy set `σ u` of a chain is exactly
the image of that chain. Together these say the stepped-up colouring,
restricted to such a set, is a faithful copy of `g` — so a homogeneous set
here is a homogeneous set downstairs, of the same order type. -/

open scoped Classical in
/-- `σ u`: the discrepancies of `u`'s consecutive pairs, as a finite set. A
chain of `r + 1` points has `r` of them, and on a `P₀`-set they are distinct
because they strictly increase. -/
noncomputable def sigmaOf (u : FinChain (n + 1)) : Finset Ordinal :=
  Finset.image (discSeq u) Finset.univ

/-- Lemma 4.14. A colouring `g` of `r`-sets of `κ`, pulled back along `σ` to
`(r+1)`-sets of `2^κ`, and made constant on a `P₀`-homogeneous `𝒟` of type
`θ`, is already constant on an `𝒜 ⊆ κ` of type `θ` -- namely the set of
`𝒟`'s next-point discrepancies.

Both halves are in place above: the image has the right order type because
`discNext` is strictly increasing, and every `r`-subset of it is some chain's
`σ` because chains of discrepancies lift. -/
theorem lemma414 {𝒟 : Set SetOrd} (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (g : Finset Ordinal → Set.Iio μ) (ι : Set.Iio μ)
    (hg : ∀ u : FinChain (n + 2), (∀ j, u j ∈ 𝒟) → g (sigmaOf u) = ι) :
    ∃ 𝒜 : SetOrd, otpOrd 𝒜 = otp 𝒟 ∧ 𝒜 ⊆ ⋃₀ 𝒟 ∧ Mono g (n + 1) 𝒜 ι := by
  refine ⟨discNext 𝒟 '' 𝒟, otpOrd_discNext_image hD hup, ?_, ?_⟩
  · -- A discrepancy lies in the symmetric difference of the two points it
    -- separates, so the transferred set never leaves `⋃₀ 𝒟`. This is what
    -- keeps the transfer inside `κ` when the points of `𝒟` are subsets of `κ`.
    rintro _ ⟨a, ha, rfl⟩
    have hex := exists_wo_gt hD ha
    rcases disc_mem_symmDiff (ne_of_irrefl (wo_nextIn hex)) with h | h
    · exact ⟨a, ha, h.1⟩
    · exact ⟨_, nextIn_mem hex, h.1⟩
  intro T hTA hTcard
  -- Enumerate `T` increasingly; `Ordinal` is linearly ordered, so this is direct.
  set w : Fin (n + 1) → Ordinal := ⇑(T.orderEmbOfFin hTcard) with hw
  have hwmono : StrictMono w := (T.orderEmbOfFin hTcard).strictMono
  have hwmem : ∀ i, w i ∈ discNext 𝒟 '' 𝒟 := (hTA  <|T.orderEmbOfFin_mem hTcard ·)
  obtain ⟨u, huD, hudisc⟩ := exists_chain_discSeq hD hup w hwmono hwmem
  -- `σ u` is exactly `T`, so the pulled-back colour is `g T`.
  have hsigma : sigmaOf u = T := by
    rw [sigmaOf, funext hudisc, hw]
    exact T.image_orderEmbOfFin_univ hTcard
  rw [← hsigma]
  exact hg u huD

/-! ## Extending short chains

Theorem 4.18's hypotheses speak about `(r+1)`-sets, while Lemmas 4.16 and 4.17
consume three- and four-chains. The bridge is that in a set of type `θ` a
short chain is always the front of a chain of any length: the set has no
greatest element, so `nextIn` can be iterated forever. -/

/-- Iterating `nextIn` from a point: an increasing sequence of any length. -/
def iterNext (𝒜 : Set SetOrd) (x : SetOrd) (n : ℕ) : SetOrd
  := (nextIn (wo := WO) 𝒜)^[n] x

lemma iterNext_mem {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) : ∀ k, iterNext 𝒜 x k ∈ 𝒜
  | 0 => hx
  | k + 1 => by
      simp only [iterNext, Function.iterate_succ_apply']
      exact nextIn_mem (exists_wo_gt hA (iterNext_mem hA hx k))

lemma iterNext_lt_succ {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) (k : ℕ) :
    iterNext 𝒜 x k ≺w iterNext 𝒜 x (k + 1) := by
  simp only [iterNext, Function.iterate_succ_apply']
  exact wo_nextIn (exists_wo_gt hA (iterNext_mem hA hx k))

lemma iterNext_strictMono {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) {j k : ℕ} (hjk : j < k) :
    iterNext 𝒜 x j ≺w iterNext 𝒜 x k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | rfl
    · exact _root_.trans (ih h) (iterNext_lt_succ hA hx k)
    · exact iterNext_lt_succ hA hx j

/-- Any nonempty chain of a set of full order type is the front of a chain of
any greater length: keep the head and pad above its top by iterating `nextIn`.-/
lemma exists_chain_head {𝒜 : Set SetOrd} {j L : ℕ} (hA : IsIndec (otp 𝒜))
    (hjL : j + 1 ≤ L) (v : Fin (j + 1) → SetOrd) (hv : ∀ i, v i ∈ 𝒜)
    (hvmono : ∀ i i' : Fin (j + 1), i < i' → v i ≺w v i') :
    ∃ u : FinChain L, (∀ i, u i ∈ 𝒜) ∧
      ∀ i : Fin (j + 1), u ⟨i, lt_of_lt_of_le i.isLt hjL⟩ = v i := by
  set top : SetOrd := v (Fin.last j) with htop
  set F : ℕ → SetOrd :=
    fun k => if h : k < j + 1 then v ⟨k, h⟩ else iterNext 𝒜 top (k - j) with hF
  have hFlt {k} (h : k < j + 1) : F k = v ⟨k, h⟩ := dif_pos h
  have hFge : ∀ k : ℕ, j + 1 ≤ k → F k = iterNext 𝒜 top (k - j) :=
    fun k h => dif_neg (by omega)
  have hcmem : ∀ k, iterNext 𝒜 top k ∈ 𝒜 := iterNext_mem hA (hv _)
  -- everything in the head sits at or below `top`, hence below all the padding
  have hlift {y : SetOrd} (hy: y = top ∨ y ≺w top) {k : ℕ} :  y ≺w iterNext 𝒜 top (k + 1) := by
    have hstep : top ≺w iterNext 𝒜 top (k + 1) :=
      iterNext_strictMono hA (hv _) (Nat.succ_pos k)
    rcases hy with rfl | hy
    · exact hstep
    · exact _root_.trans hy hstep
  have hFmem k: F k ∈ 𝒜 := by
    rcases Nat.lt_or_ge k (j + 1) with h | h
    · rw [hFlt h]; exact hv _
    · rw [hFge k h]; exact hcmem _
  have hFmono p q (hpq : p < q) : F p ≺w F q := by
    rcases Nat.lt_or_ge p (j + 1) with hp | hp
    · rcases Nat.lt_or_ge q (j + 1) with hq | hq
      · rw [hFlt hp, hFlt hq]
        exact hvmono _ _ (by simpa [Fin.lt_def] using hpq)
      · rw [hFlt hp, hFge q hq, (by omega: q - j = (q - j - 1) + 1)]
        refine hlift ?_
        rcases eq_or_lt_of_le (Fin.le_last (⟨p, hp⟩ : Fin (j + 1))) with h | h
        · exact Or.inl (by rw [htop, ← h])
        · exact Or.inr (hvmono _ _ h)
    · rw [hFge p hp, hFge q (by omega)]
      exact iterNext_strictMono hA (hv _) (by omega)
  exact ⟨FinChain.mk (fun i => F i) (hFmono · ·), fun _ => hFmem _, fun i => hFlt i.isLt⟩

/-! ## The `δ`-pattern classes `P(0,1)` and `P(1,0)`

These constrain the first two entries of the pattern *of the discrepancy
sequence*, so they need four points: a `FinChain (n + 4)` has `n + 3`
discrepancies, and the indices `0, 1, 2` into them stay distinct. -/

/-- `P(0,1)`: the chain lies in `K`, and its discrepancies rise then fall. The
`K` conjunct is not decoration -- Theorem 4.18 needs `J₁ ⊆ K ∪ K(0,1)`, which
fails without it. -/
def InP01 (u : FinChain (n + 4)) : Prop :=
  (InK0 ⊔ InK1) u ∧ discSeq u 0 < discSeq u 1 ∧ discSeq u 2 < discSeq u 1

/-- `P(1,0)`: in `K`, with discrepancies falling then rising. -/
def InP10 (u : FinChain (n + 4)) : Prop :=
  (InK0 ⊔ InK1) u ∧ discSeq u 1 < discSeq u 0 ∧ discSeq u 1 < discSeq u 2

lemma inP0_disc01 {u : FinChain (n + 4)} (h : InP0 u) : discSeq u 0 < discSeq u 1 := by
  simpa using h.2 0

lemma inP0_disc12 {u : FinChain (n + 4)} (h : InP0 u) : discSeq u 1 < discSeq u 2 := by
  simpa using h.2 1

/-- `P₀` is disjoint from `P(0,1)`: an all-rising sequence never falls. -/
lemma not_inP01_of_inP0 {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP01 u :=
  fun h01 => (asymm (inP0_disc12 h)) h01.2.2

/-- `P₀` is disjoint from `P(1,0)` for the same reason, one step earlier. -/
lemma not_inP10_of_inP0 {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP10 u :=
  fun h10 => (asymm (inP0_disc01 h)) h10.2.1

/-- `P(0,1)` and `P(1,0)` are disjoint from each other. -/
lemma not_inP10_of_inP01 {u : FinChain (n + 4)} (h : InP01 u) : ¬ InP10 u :=
  fun h10 => (asymm h10.2.1) h.2.1

/-- A chain whose pattern begins `1, 0` is in neither `K₀` nor `K₁`. -/
lemma not_inK_of_inK10 {u : FinChain (n + 3)} (h : InK10 u) : ¬ (InK0 ⊔ InK1) u :=
  fun hK => hK.elim (fun h0 => h.1 (h0 0)) fun h1 => h1 1 h.2

/-- `K(0,1)` and `K(1,0)` are disjoint. -/
lemma not_inK10_of_inK01 {u : FinChain (n + 3)} (h : InK01 u) : ¬ InK10 u :=
  fun h10 => h10.1 h.1

/-! ### Homogeneity, transported between sets and chains -/

/-- On an all-agreeing set every chain lies in `K₀`. -/
lemma inK0_of_allAgree (h : AllAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : InK0 u := fun j =>
  have hm : u j.castSucc ≺w u j.succ := u.map_rel_iff.2 (Fin.castSucc_lt_succ (i := j))
  (agree_iff_lexLT hm).1 (h (hu _) (hu _) fun e => irrefl _ (e ▸ hm))

/-- On an all-disagreeing set every chain lies in `K₁`. -/
lemma inK1_of_allDisagree (h : AllDisagree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : InK1 u := fun j =>
  have hm : u j.castSucc ≺w u j.succ := u.map_rel_iff.2 (Fin.castSucc_lt_succ (i := j))
  mt (agree_iff_lexLT hm).2 (h (hu _) (hu _) fun e => irrefl _ (e ▸ hm))

/-- On a homogeneous set every chain lies in `K`. -/
lemma inK_of_homog (h : HomAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : (InK0 ⊔ InK1) u :=
  h.imp (inK0_of_allAgree · hu) (inK1_of_allDisagree · hu)

/-- A four-chain of `𝒜` is the front of a chain of length `n + 4`, at the
literal indices `0, 1, 2, 3` that `InK01` and `InP01` read. -/
lemma exists_chain_of_four (hA : IsIndec (otp 𝒜))
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) (hce : c ≺w e) :
    ∃ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) ∧
      u 0 = a ∧ u 1 = b ∧ u 2 = c ∧ u 3 = e := by
  have hvmem : ∀ i, (![a, b, c, e] : Fin 4 → SetOrd) i ∈ 𝒜 := by
    intro i; fin_cases i <;> simpa
  have hvmono : ∀ i i' : Fin 4, i < i' →
      (![a, b, c, e] : Fin 4 → SetOrd) i ≺w ![a, b, c, e] i' := by
    -- the three composites, so every case is a hypothesis lookup
    have hac := _root_.trans hab hbc
    have hbe := _root_.trans hbc hce
    have hae := _root_.trans hac hce
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp_all
  obtain ⟨u, hu, heq⟩ :=
    exists_chain_head (j := 3) (L := n + 4) hA (by omega) ![a, b, c, e] hvmem hvmono
  refine ⟨u, hu, ?_, ?_, ?_, ?_⟩
  · simpa using heq 0
  · simpa using heq 1
  · rw [show (2 : Fin (n + 4)) = ⟨2, by omega⟩ from Fin.ext (by simp)]; simpa using heq 2
  · rw [show (3 : Fin (n + 4)) = ⟨3, by omega⟩ from Fin.ext (by simp)]; simpa using heq 3

/-! ### Reading a padded four-chain

`InK01` and `InP01` look only at a chain's first few points, so once a
four-chain has been padded out to length `n + 4` its classification is
determined by the four points it started from. -/

lemma agreeAt_of_four {u : FinChain (n + 4)}
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) :
    (AgreeAt u 0 ↔ a ≺ b) ∧ (AgreeAt u 1 ↔ b ≺ c) := by
  constructor
  · rw [AgreeAt, show ((0 : Fin (n + 3)).castSucc) = (0 : Fin (n + 4)) from by first | rfl,
      show ((0 : Fin (n + 3)).succ) = (1 : Fin (n + 4)) from by first | rfl, h0, h1]
  · rw [AgreeAt, show ((1 : Fin (n + 3)).castSucc) = (1 : Fin (n + 4)) from by first | rfl,
      show ((1 : Fin (n + 3)).succ) = (2 : Fin (n + 4)) from by first | rfl, h1, h2]

lemma discSeq_of_four {u : FinChain (n + 4)}
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) (h3 : u 3 = e) :
    discSeq u 0 = disc a b ∧ discSeq u 1 = disc b c ∧ discSeq u 2 = disc c e := by
  refine ⟨?_, ?_, ?_⟩
  · rw [discSeq, show ((0 : Fin (n + 3)).castSucc) = (0 : Fin (n + 4)) from by first | rfl,
      show ((0 : Fin (n + 3)).succ) = (1 : Fin (n + 4)) from by first | rfl, h0, h1]
  · rw [discSeq, show ((1 : Fin (n + 3)).castSucc) = (1 : Fin (n + 4)) from by first | rfl,
      show ((1 : Fin (n + 3)).succ) = (2 : Fin (n + 4)) from by first | rfl, h1, h2]
  · rw [discSeq, show ((2 : Fin (n + 3)).castSucc) = (2 : Fin (n + 4)) from by first | rfl,
      show ((2 : Fin (n + 3)).succ) = (3 : Fin (n + 4)) from by first | rfl, h2, h3]

/-! ### Turning `(r+1)`-set hypotheses into the shapes 4.16 and 4.17 consume -/

/-- Lemma 4.16's hypothesis (i), from `[𝒜]ⁿ⁺⁴ ∩ K(0,1) = ∅`. -/
lemma no_pattern01_of_no_inK01 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InK01 u) :
    ¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c := by
  rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hag, hdis⟩
  obtain ⟨d, hd, hcd⟩ := exists_wo_gt hA hc
  obtain ⟨u, hu, h0, h1, h2, _⟩ := exists_chain_of_four hA ha hb hc hd hab hbc hcd
  obtain ⟨e0, e1⟩ := agreeAt_of_four h0 h1 h2
  exact h u hu ⟨e0.2 hag, hdis ∘ e1.1⟩

/-- Lemma 4.16's hypothesis (ii), from `[𝒜]ⁿ⁺⁴ ∩ K(1,0) = ∅`. -/
lemma no_pattern10_of_no_inK10 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InK10 u) :
    ¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ ¬ a ≺ b ∧ b ≺ c := by
  rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hdis, hag⟩
  obtain ⟨d, hd, hcd⟩ := exists_wo_gt hA hc
  obtain ⟨u, hu, h0, h1, h2, _⟩ := exists_chain_of_four hA ha hb hc hd hab hbc hcd
  obtain ⟨e0, e1⟩ := agreeAt_of_four h0 h1 h2
  exact h u hu ⟨hdis ∘ e0.1, e1.2 hag⟩

/-- Lemma 4.17's hypothesis (i), from `[𝒜]ⁿ⁺⁴ ∩ P(0,1) = ∅`. -/
lemma up_forces_up_of_no_inP01 (hA : IsIndec (otp 𝒜))
    (hom : HomAgree 𝒜)
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InP01 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
      disc a b < disc b c → disc b c < disc c e := by
  intro a ha b hb c hc e he hab hbc hce hup
  by_contra! hcon
  obtain ⟨u, hu, h0, h1, h2, h3⟩ := exists_chain_of_four hA ha hb hc he hab hbc hce
  obtain ⟨d0, d1, d2⟩ := discSeq_of_four h0 h1 h2 h3
  refine h u hu ⟨inK_of_homog hom hu, by rw [d0, d1]; exact hup, ?_⟩
  rw [d1, d2]
  exact lt_of_le_of_ne hcon (disc_ne_of_homogeneous hom hb hc he hbc hce).symm

/-- Lemma 4.17's hypothesis (ii), from `[𝒜]ⁿ⁺⁴ ∩ P(1,0) = ∅`. -/
lemma down_forces_down_of_no_inP10 (hA : IsIndec (otp 𝒜))
    (hom : HomAgree 𝒜)
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InP10 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
      disc b c < disc a b → disc c e < disc b c := by
  intro a ha b hb c hc e he hab hbc hce hdown
  by_contra! hcon
  obtain ⟨u, hu, h0, h1, h2, h3⟩ := exists_chain_of_four hA ha hb hc he hab hbc hce
  obtain ⟨d0, d1, d2⟩ := discSeq_of_four h0 h1 h2 h3
  refine h u hu ⟨inK_of_homog hom hu, by rw [d0, d1]; exact hdown, ?_⟩
  rw [d1, d2]
  exact lt_of_le_of_ne hcon (disc_ne_of_homogeneous hom hb hc he hbc hce)

/-- From "every chain lies in `P₀`" to the pointwise form Lemma 4.14 wants. -/
lemma allUp_of_inP0 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → InP0 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c := by
  intro a ha b hb c hc hab hbc
  obtain ⟨e, he, hce⟩ := exists_wo_gt hA hc
  obtain ⟨u, hu, h0, h1, h2, h3⟩ := exists_chain_of_four hA ha hb hc he hab hbc hce
  obtain ⟨d0, d1, _⟩ := discSeq_of_four h0 h1 h2 h3
  have := inP0_disc01 (h u hu)
  rwa [d0, d1] at this

/-- A chain is recovered from its own finite set: the increasing enumeration
is unique. Both lists are `WOle`-sorted and permutations of one another, and
`WOle` is antisymmetric, so they are equal. -/
lemma chainOfFinset_toFinset (u : FinChain n) :
    chainOfFinset u.toFinset u.card_toFinset = u := by
  have hlist : u.toFinset.sort WOle = List.ofFn u := by
    refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _)
      (List.pairwise_ofFn.2 fun i j hij => Or.inr (u.map_rel_iff.2 hij)) ?_
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_ofFn.2 u.injective)]
    intro a
    rw [Finset.mem_sort, List.mem_ofFn, FinChain.mem_toFinset]
  refine DFunLike.coe_injective (funext fun i => ?_)
  change (u.toFinset.sort WOle).get _ = _
  simp [hlist]

/-- On a homogeneous all-rising set every chain lies in `P₀`. -/
lemma inP0_of_allUp (hom : HomAgree 𝒞)
    (hup : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, a ≺w b → b ≺w c → disc a b < disc b c)
    {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒞) : InP0 u := by
  refine ⟨inK_of_homog hom hu, fun j ↦ ?_⟩
  rw [discSeq, discSeq, show (Fin.castSucc j).succ = (Fin.succ j).castSucc from
    (Fin.succ_castSucc j).symm]
  exact hup _ (hu _) _ (hu _) _ (hu _)
    (u.map_rel_iff.2 (by simp [Fin.lt_def])) (u.map_rel_iff.2 (by simp [Fin.lt_def]))

/-! ## Theorem 4.18: the negative stepping-up lemma

Everything above is now assembled. A homogeneous set for the stepped-up
colouring is shrunk twice — first to make its `ε`-pattern constant, then to
make its discrepancies rise — and on the result the colouring is literally
`g ∘ σ`, which hands back a homogeneous set downstairs and contradicts the
hypothesis. -/

/-- No colour of `f` has a homogeneous subset of `κ` of order type `θ`: the
negative arrow `κ ↛ (θ)ʳ`. -/
def NoHomogOrd (κ : Ordinal) (f : Finset Ordinal → Set.Iio μ) (r : ℕ) (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set Ordinal, 𝒜 ⊆ Set.Iio κ → otpOf ordWO 𝒜 = θ → ∀ ι, ¬ Mono f r 𝒜 ι

/-- The same, one level up on `𝒫(κ) ≃ 2^κ`: `2^κ ↛ (θ)ʳ⁺¹`. -/
def NoHomog (κ : Ordinal) (f : Finset (Set Ordinal) → Set.Iio μ) (r : ℕ) (θ : Ordinal) : Prop :=
  ∀ 𝒜 : Set (Set Ordinal), 𝒜 ⊆ Set.powerset (Set.Iio κ) → otpOf WO 𝒜 = θ →
    ∀ ι, ¬ Mono f r 𝒜 ι

/-- The two colours stepping up reserves for itself. They exist as soon as
there are two colours at all, meaning `1 < μ`. -/
def colour₀ (hμ : 1 < μ) : Set.Iio μ := ⟨0, zero_lt_one.trans hμ⟩

@[inherit_doc colour₀]
def colour₁ (hμ : 1 < μ) : Set.Iio μ := ⟨1, hμ⟩

/-- The two reserved colours are distinct. -/
lemma colour₀_ne_colour₁ (hμ : 1 < μ) : colour₀ hμ ≠ colour₁ hμ :=
  fun h => zero_ne_one (congrArg Subtype.val h)

open scoped Classical in
/-- The stepped-up colouring. A chain is
looked at through its two patterns, and gets:

* colour `1` if it deviates *first one way* — `ε`-pattern beginning `0,1`, or
  discrepancies rising then falling;
* `g (σ u)` if it is well behaved (`P₀`): pattern constant, discrepancies
  rising. This is [dG21]'s `Iₙ*`;
* colour `0` otherwise, which includes the other first deviation — pattern
  `1,0`, or discrepancies falling then rising.

Splitting the two deviations between colours `1` and `0` is the point. A
homogeneous set of colour `1` can contain no chain of the second kind, and a
homogeneous set of any other colour none of the first, so *whichever* colour it
takes it avoids one of the two exceptional patterns — which is exactly the
hypothesis Lemmas 4.16 and 4.17 need in order to shrink it. Note no colour
beyond `g`'s own range and `{0, 1}` is used.

Sets of the wrong size are parked on colour `0`; they are never looked at. -/
noncomputable def stepUpColour (hμ : 1 < μ) (g : Finset Ordinal → Set.Iio μ)
    (T : Finset SetOrd) : Set.Iio μ :=
  if h : T.card = n + 4 then
    if (InK01 ⊔ InP01) (chainOfFinset T h) then colour₁ hμ
    else if InP0 (chainOfFinset T h) then g (sigmaOf (chainOfFinset T h)) else colour₀ hμ
  else colour₀ hμ

/-- **Theorem 4.18, the negative stepping-up lemma.** If no colour of `g` has a
homogeneous set of order type `θ` for `(n+3)`-sets of ordinals, then the
stepped-up colouring has none for `(n+4)`-sets of `2^κ`.

The three cases are [dG21]'s. Colour `1` is the one that absorbs `K(0,1)`
and `P(0,1)`, so a homogeneous set for it must avoid `K(1,0)` and then
`P(1,0)`; every other colour must avoid `K(0,1)` and `P(0,1)` instead. Either
way Lemma 4.16 delivers a `K`-homogeneous `ℬ`, Lemma 4.17 an all-rising `𝒞`
inside it, and on `𝒞` the colouring is `g ∘ σ`, so Lemma 4.14 hands
back a homogeneous set downstairs -- which was assumed not to exist. -/
theorem stepUp_noHomog {g : Finset Ordinal → Set.Iio μ} (hμ : 1 < μ) (hθ : IsIndec θ)
    (hg : NoHomogOrd κ g (n + 3) (θ)) :
    NoHomog κ (stepUpColour (n := n) hμ g) (n + 4) θ := by
  intro 𝒜 hAκ hA ι hmono
  have hAi : IsIndec (otpOf WO 𝒜) := hA ▸ hθ
  rw [mono_iff_chains] at hmono
  -- Read the colouring off chains.
  open Classical in
  have hval {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) :
      (if (InK01 ⊔ InP01) u then colour₁ hμ
       else if InP0 u then g (sigmaOf u) else colour₀ hμ) = ι := by
    have := hmono u hu
    rwa [stepUpColour, dif_pos u.card_toFinset, chainOfFinset_toFinset] at this
  -- The three values the colouring can take, read straight off `hval`.
  have hone {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : (InK01 ⊔ InP01) u) :
      colour₁ hμ = ι := by rw [← hval hu, if_pos h]
  have hzero {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : ¬ (InK01 ⊔ InP01) u)
      (h0 : ¬ InP0 u) : colour₀ hμ = ι := by rw [← hval hu, if_neg h, if_neg h0]
  have hgval {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : ¬ (InK01 ⊔ InP01) u)
      (h0 : InP0 u) : g (sigmaOf u) = ι := by rw [← hval hu, if_neg h, if_pos h0]
  -- The endgame, once `ℬ` is `K`-homogeneous and `𝒞 ⊆ ℬ` all-rising.
  have finish : ∀ ℬ 𝒞 : Set SetOrd, ℬ ⊆ 𝒜 → 𝒞 ⊆ ℬ → otp 𝒞 = θ → HomAgree ℬ →
      (∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, a ≺w b → b ≺w c → disc a b < disc b c) → False := by
    intro ℬ 𝒞 hBA hCB hC homB hupC
    have hsig : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒞) → g (sigmaOf u) = ι := fun u hu =>
      have hP0 : InP0 u := inP0_of_allUp (homB.imp (·.mono hCB) (·.mono hCB)) hupC hu
      hgval (fun j => hBA (hCB (hu j))) (by
        rintro (hk | hp)
        · exact not_inK_of_inK01 hk hP0.1
        · exact not_inP01_of_inP0 hP0 hp) hP0
    obtain ⟨𝒜', hA', hsub, hmono'⟩ := lemma414 (n := n + 2) (hC ▸ hθ) hupC g ι hsig
    -- The transferred set is made of discrepancies between points of `𝒞 ⊆ 𝒜`,
    -- so it stays below `κ`, and the hypothesis downstairs applies to it.
    refine hg 𝒜' (fun ξ hξ => ?_) (hA'.trans hC) ι hmono'
    obtain ⟨a, ha, hξa⟩ := hsub hξ
    exact hAκ (hBA (hCB ha)) hξa
  by_cases hι : ι = colour₁ hμ
  · -- Colour `1`: avoid `K(1,0)`, then `P(1,0)`.
    subst hι
    have hK10 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒜) → ¬ InK10 u := fun u hu h10 =>
      colour₀_ne_colour₁ hμ (hzero hu (by
        rintro (hk | hp)
        · exact not_inK10_of_inK01 hk h10
        · exact not_inK_of_inK10 h10 hp.1) (not_inK_of_inK10 h10 ·.1))
    obtain ⟨ℬ, hBA, hB, homB⟩ :=
      exists_homogeneous hAi (Or.inr (no_pattern10_of_no_inK10 hAi hK10))
    have hP10 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ ℬ) → ¬ InP10 u := fun u hu h10 =>
      colour₀_ne_colour₁ hμ (hzero (fun j => hBA (hu j)) (by
        rintro (hk | hp)
        · exact not_inK_of_inK01 hk h10.1
        · exact not_inP10_of_inP01 hp h10) (not_inP10_of_inP0 · h10))
    obtain ⟨𝒞, hCB, hC, hupC⟩ :=
      exists_all_disc_up (hB ▸ hAi) homB
        (Or.inr (down_forces_down_of_no_inP10 (hB ▸ hAi) homB hP10))
    exact finish ℬ 𝒞 hBA hCB (hC.trans (hB.trans hA)) homB hupC
  · -- Any other colour: avoid `K(0,1)`, then `P(0,1)`.
    have hK01 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒜) → ¬ InK01 u :=
      fun u hu h01 => hι (hone hu (Or.inl h01)).symm
    obtain ⟨ℬ, hBA, hB, homB⟩ :=
      exists_homogeneous hAi (Or.inl (no_pattern01_of_no_inK01 hAi hK01))
    have hP01 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ ℬ) → ¬ InP01 u :=
      fun u hu h01 => hι (hone (fun j => hBA (hu j)) (Or.inr h01)).symm
    obtain ⟨𝒞, hCB, hC, hupC⟩ :=
      exists_all_disc_up (hB ▸ hAi) homB (Or.inl (up_forces_up_of_no_inP01 (hB ▸ hAi) homB hP01))
    exact finish ℬ 𝒞 hBA hCB (hC.trans (hB.trans hA)) homB hupC


/-- **Theorem 4.18 as a negative partition arrow.** If `κ ↛ (ω^α)ʳ⁺³_μ` is
witnessed by some colouring of the `(r+3)`-subsets of `κ`, then
`2^κ ↛ (ω^α)ʳ⁺⁴_μ` holds one level up -- with the *same* number of colours,
since stepping up reuses `0` and `1` rather than introducing any. -/
theorem noHomog_stepUp {μ α : Ordinal} (hα : 0 < α) (hμ : 1 < μ)
    (h : ∃ g : Finset Ordinal → Set.Iio μ, NoHomogOrd κ g (r + 3) (ω^α)) :
    ∃ f : Finset (Set Ordinal) → Set.Iio μ, NoHomog κ f (r + 4) (ω^α) := by
  obtain ⟨g, hg⟩ := h
  have hθ : IsIndec (ω ^ α) :=
    ⟨isPrincipal_add_omega0_opow α, one_lt_opow.2 ⟨one_lt_omega0, hα.ne'⟩⟩
  exact ⟨stepUpColour hμ g, stepUp_noHomog hμ hθ hg⟩

end OrdinalStepUp.ErdosRado
