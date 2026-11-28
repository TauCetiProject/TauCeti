/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Model
import Mathlib.Topology.Algebra.Indicator
import TauCeti.MeasureTheory.Group.Integral

/-!
# Lattice vacua

Let `β` be a Heisenberg datum on an abelian topological group `W` and `L` an open subgroup of `W`
of measure one for a translation-invariant measure `μ`. Suppose that `L` is *self-dual* for `β²`:
every `y` such that `z ↦ β z y ^ 2` is trivial on `L` lies in `L`. A *semicharacter* of `L` for
`β` is a function `σ`, continuous on `L`, with values `±1` on `L` and
`σ (a + b) = σ a * σ b * β a b` for `a, b ∈ L`. Then the extension of `σ` by zero,
`L.indicator σ`, is a vacuum for `β` and `μ` (`TauCeti.HeisenbergDatum.isVacuum_indicator`).

This is the vacuum at the finite places: for the finite adeles `𝔸_f ^ n` of a CM field, with `L`
the standard lattice `Ô ^ n` and `σ` a quadratic semicharacter, the vacuum of the Weil
representation is of this form, and self-duality of `L` is self-duality of `Ô` for the additive
character. Its counterpart at the real places is a Gaussian.

The twisted convolution identity of the vacuum is an average over `L`: when `y ∈ L` the integrand
is constant on `L`, and when `y ∉ L` but `x - y ∈ L` it is a multiple of the character
`z ↦ β z y ^ 2` of `L`, which is nontrivial by self-duality and so has integral zero.

The translates of the vacuum vector by `L` are its multiples: `ϱ l e = σ l • e` for `l ∈ L`
(`TauCeti.ReproducingModel.heisenbergRep_vacuum_of_mem`).

## Main results

* `TauCeti.HeisenbergDatum.isVacuum_indicator`: the extension by zero of a semicharacter of a
  self-dual open subgroup of measure one is a vacuum.
* `TauCeti.HeisenbergDatum.indicator_add_of_mem`,
  `TauCeti.HeisenbergDatum.apply_mul_indicator_sub_of_mem`: the translation laws of the lattice
  vacuum by elements of `L`.
* `TauCeti.ReproducingModel.heisenbergRep_vacuum_of_mem`: the Heisenberg operators of `L` act on
  the vacuum vector by `σ`.

## Provenance

The statement is the abstract form, for any Heisenberg datum and open subgroup, of the lattice
vacuum of the finite adeles in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC), `src/Lib/Weil/Construction/FiniteMultiplier.lean`
(`New.stdLattice.isVacuum_finVac`), whose proof averages characters over `Ô ^ n`; the formal proof
here is written independently.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace TauCeti

namespace HeisenbergDatum

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] (β : HeisenbergDatum W)
  {L : AddSubgroup W} {σ : W → ℂ}

section Semicharacter

variable {β} (hσ : ∀ a ∈ L, ∀ b ∈ L, σ (a + b) = σ a * σ b * β a b)
include hσ

/-- Translation of the extension by zero of a semicharacter by an element of `L`. -/
theorem indicator_add_of_mem {l : W} (hl : l ∈ L) (w : W) :
    (L : Set W).indicator σ (w + l) = (L : Set W).indicator σ w * σ l * β w l := by
  by_cases hw : w ∈ L
  · simp [indicator_of_mem, hw, L.add_mem hw hl, hσ w hw l hl]
  · have hwl : w + l ∉ L := fun h ↦ hw (by simpa using L.sub_mem h hl)
    simp [indicator_of_notMem, hw, hwl]

/-- A function with the semicharacter law on `L` that is even and takes the value `1` at `0` has
values `±1` on `L`: `σ a ^ 2 = σ a * σ (-a) = σ 0 = 1`. -/
private theorem semichar_sq_of_zero_of_neg (h0 : σ 0 = 1) (hneg : ∀ a ∈ L, σ (-a) = σ a) {a : W}
    (ha : a ∈ L) : σ a ^ 2 = 1 := by
  have h := hσ a ha (-a) (L.neg_mem ha)
  rw [add_neg_cancel, h0, hneg a ha, apply_neg, apply_self, mul_one] at h
  rw [sq, h]

variable (hσ₂ : ∀ a ∈ L, σ a ^ 2 = 1)
include hσ₂

/-- A Heisenberg datum that admits a semicharacter on `L` is symmetric there, so its square is
trivial on `L × L`. -/
private theorem apply_sq_eq_one_of_mem {a b : W} (ha : a ∈ L) (hb : b ∈ L) : β a b ^ 2 = 1 := by
  have hne : σ a * σ b ≠ 0 := mul_ne_zero (fun h ↦ by simpa [h] using hσ₂ a ha)
    (fun h ↦ by simpa [h] using hσ₂ b hb)
  have hsymm : β a b = β b a := by
    have h := hσ b hb a ha
    rw [add_comm, hσ a ha b hb, mul_comm (σ b)] at h
    exact mul_left_cancel₀ hne h
  rw [sq]
  nth_rw 2 [hsymm]
  exact β.apply_mul_apply_swap a b

private theorem semichar_zero : σ 0 = 1 := by
  simpa [← sq, hσ₂ 0 L.zero_mem] using hσ 0 L.zero_mem 0 L.zero_mem

private theorem semichar_neg {a : W} (ha : a ∈ L) : σ (-a) = σ a := by
  have h := hσ a ha (-a) (L.neg_mem ha)
  rw [add_neg_cancel, semichar_zero hσ hσ₂, apply_neg, apply_self, mul_one] at h
  linear_combination (-σ (-a)) * hσ₂ a ha - σ a * h

/-- Translation of the extension by zero of a semicharacter by the negative of an element of `L`.
-/
private theorem indicator_sub_of_mem {l : W} (hl : l ∈ L) (w : W) :
    (L : Set W).indicator σ (w - l) = (L : Set W).indicator σ w * σ l * β l w := by
  rw [sub_eq_add_neg, indicator_add_of_mem hσ (L.neg_mem hl), semichar_neg hσ hσ₂ hl, apply_neg]

/-- The extension by zero of a semicharacter is an eigenfunction of the Heisenberg translations
by `L`: `β l x * e (x - l) = σ l * e x` for `l ∈ L`. -/
theorem apply_mul_indicator_sub_of_mem {l : W} (hl : l ∈ L) (x : W) :
    β l x * (L : Set W).indicator σ (x - l) = σ l * (L : Set W).indicator σ x := by
  rw [indicator_sub_of_mem hσ hσ₂ hl]
  by_cases hx : x ∈ L
  · linear_combination σ l * (L : Set W).indicator σ x * apply_sq_eq_one_of_mem hσ hσ₂ hl hx
  · simp [indicator_of_notMem, hx]

end Semicharacter

/-- The integrand of the twisted convolution of the extension by zero of a function on `L`
vanishes everywhere when `x - y ∉ L`. -/
private theorem indicator_mul_indicator_sub_eq_zero {x y : W} (hxy : x - y ∉ L) (z : W) :
    (L : Set W).indicator σ z *
      (β z y * (β (z + y) x * (L : Set W).indicator σ (x - (z + y)))) = 0 := by
  by_cases hz : z ∈ L
  · have hsplit : x - y = x - (z + y) + z := by abel
    have : x - (z + y) ∉ L := fun h ↦ hxy (hsplit ▸ L.add_mem h hz)
    simp [indicator_of_notMem this]
  · simp [indicator_of_notMem hz]

section Vacuum

variable [MeasurableSpace W] {μ : Measure W}

/-- For `y ∈ L` the twisted convolution integral of the extension by zero `e` of a semicharacter
is `e y * e x`: its integrand is the constant `σ y * σ x` on `L` when `x ∈ L`, and vanishes when
`x ∉ L`. -/
private theorem integral_mul_indicator_of_mem (hLm : MeasurableSet (L : Set W)) (hμ : μ L = 1)
    (hσ : ∀ a ∈ L, ∀ b ∈ L, σ (a + b) = σ a * σ b * β a b) (hσ₂ : ∀ a ∈ L, σ a ^ 2 = 1) {y : W}
    (hy : y ∈ L) (x : W) :
    ∫ z, (L : Set W).indicator σ z * (β z y * (β (z + y) x * (L : Set W).indicator σ (x - (z + y))))
      ∂μ = (L : Set W).indicator σ y * (L : Set W).indicator σ x := by
  by_cases hx : x ∈ L
  · have hconst (c : ℂ) : ∫ z, (L : Set W).indicator (fun _ ↦ c) z ∂μ = c := by
      simp [integral_indicator hLm, Measure.real, hμ]
    rw [indicator_of_mem hy, indicator_of_mem hx, ← hconst (σ y * σ x)]
    congr 1 with z
    by_cases hz : z ∈ L
    · have hzy := L.add_mem hz hy
      rw [indicator_sub_of_mem hσ hσ₂ hzy, hσ z hz y hy]
      simp only [indicator_of_mem hz, indicator_of_mem hx]
      linear_combination (σ y * σ x * β z y ^ 2 * β (z + y) x ^ 2) * hσ₂ z hz +
        (σ y * σ x * β (z + y) x ^ 2) * apply_sq_eq_one_of_mem hσ hσ₂ hz hy +
        (σ y * σ x) * apply_sq_eq_one_of_mem hσ hσ₂ hzy hx
    · simp [indicator_of_notMem, hz]
  · have hxy : x - y ∉ L := fun h ↦ hx (by simpa using L.add_mem h hy)
    simp [β.indicator_mul_indicator_sub_eq_zero hxy, indicator_of_notMem hx]

/-- For `y ∉ L` the twisted convolution integral of the extension by zero of a semicharacter
vanishes when `L` is self-dual: if `x - y ∈ L` its integrand is a multiple of the character
`z ↦ β z y ^ 2` of `L`, which is nontrivial, and otherwise it vanishes. -/
private theorem integral_mul_indicator_of_notMem [MeasurableAdd W] [μ.IsAddLeftInvariant]
    (hdual : ∀ y, (∀ z ∈ L, β z y ^ 2 = 1) → y ∈ L)
    (hσ : ∀ a ∈ L, ∀ b ∈ L, σ (a + b) = σ a * σ b * β a b) (hσ₂ : ∀ a ∈ L, σ a ^ 2 = 1) {y : W}
    (hy : y ∉ L) (x : W) :
    ∫ z, (L : Set W).indicator σ z * (β z y * (β (z + y) x * (L : Set W).indicator σ (x - (z + y))))
      ∂μ = 0 := by
  by_cases hxy : x - y ∈ L
  · obtain ⟨l, hl, rfl⟩ : ∃ l ∈ L, x = y + l := ⟨x - y, hxy, by abel⟩
    obtain ⟨z₀, hz₀, hne⟩ : ∃ z₀ ∈ L, β z₀ y ^ 2 ≠ 1 := by
      by_contra! h
      exact hy (hdual y h)
    have hchar : ∫ z, (L : Set W).indicator (fun z ↦ β z y ^ 2) z ∂μ = 0 := by
      refine integral_eq_zero_of_add_left_eq_smul (g := z₀) hne fun z ↦ ?_
      by_cases hz : z ∈ L
      · simp [indicator_of_mem, hz, L.add_mem hz₀ hz, map_add_left, mul_pow]
      · have : z₀ + z ∉ L := fun h ↦ hz (by simpa using L.sub_mem h hz₀)
        simp [indicator_of_notMem, hz, this]
    rw [← mul_zero (σ l * β y l), ← hchar, ← integral_const_mul]
    congr 1 with z
    by_cases hz : z ∈ L
    · have hshift : y + l - (z + y) = l - z := by abel
      rw [hshift, indicator_sub_of_mem hσ hσ₂ hz, map_add_left, map_add_right, map_add_right,
        apply_self]
      simp only [indicator_of_mem hz, indicator_of_mem hl]
      linear_combination (σ l * β y l * β z y ^ 2 * β z l ^ 2) * hσ₂ z hz +
        (σ l * β y l * β z y ^ 2) * apply_sq_eq_one_of_mem hσ hσ₂ hz hl
    · simp [indicator_of_notMem hz]
  · simp [β.indicator_mul_indicator_sub_eq_zero hxy]

/-- The extension by zero of a semicharacter `σ` of an open subgroup `L` of measure one, for a
Heisenberg datum `β` for which `L` is self-dual (every `y` with `β z y ^ 2 = 1` for all `z ∈ L`
lies in `L`), is a vacuum for `β` and any translation-invariant measure `μ`. -/
theorem isVacuum_indicator [OpensMeasurableSpace W] [MeasurableAdd W]
    [μ.IsAddLeftInvariant] (hL : IsOpen (L : Set W)) (hμ : μ L = 1)
    (hdual : ∀ y, (∀ z ∈ L, β z y ^ 2 = 1) → y ∈ L) (hσc : ContinuousOn σ L)
    (hσ : ∀ a ∈ L, ∀ b ∈ L, σ (a + b) = σ a * σ b * β a b) (hσ₂ : ∀ a ∈ L, σ a ^ 2 = 1) :
    β.IsVacuum μ ((L : Set W).indicator σ) := by
  -- `L` is closed, being its own dual: the intersection of the closed sets `β z · ^ 2 = 1`.
  have hLc : IsClosed (L : Set W) := by
    have hdual' : (L : Set W) = ⋂ z ∈ L, {y | β z y ^ 2 = 1} := Set.ext fun y ↦
      ⟨fun hy ↦ mem_iInter₂.2 fun z hz ↦ apply_sq_eq_one_of_mem hσ hσ₂ hz hy,
        fun h ↦ hdual y (mem_iInter₂.1 h)⟩
    rw [hdual']
    exact isClosed_biInter fun z _ ↦ isClosed_eq (by fun_prop) continuous_const
  have hLm : MeasurableSet (L : Set W) := hL.measurableSet
  have hsq (a : W) (ha : a ∈ L) : σ a = 1 ∨ σ a = -1 := sq_eq_one_iff.mp (hσ₂ a ha)
  refine
    { continuous := continuous_indicator (by simp [isClopen_iff_frontier_eq_empty.mp ⟨hLc, hL⟩])
        (by rwa [hLc.closure_eq])
      integrable := (integrable_indicator_iff hLm).mpr <|
        .of_bound (by simp [hμ]) (hσc.aestronglyMeasurable hLm) 1 <|
          (ae_restrict_iff' hLm).mpr <| .of_forall fun a ha ↦ by
            rcases hsq a ha with h | h <;> simp [h]
      apply_zero := by simp [semichar_zero hσ hσ₂]
      apply_neg := fun x ↦ by
        by_cases hx : x ∈ L
        · simp [indicator_of_mem, hx, semichar_neg hσ hσ₂ hx]
        · simp [indicator_of_notMem, hx]
      conj_apply := fun x ↦ by
        by_cases hx : x ∈ L
        · rcases hsq x hx with h | h <;> simp [indicator_of_mem, hx, h]
        · simp [indicator_of_notMem, hx]
      integral_mul_apply := fun y x ↦ ?_ }
  by_cases hy : y ∈ L
  · exact β.integral_mul_indicator_of_mem hLm hμ hσ hσ₂ hy x
  · rw [β.integral_mul_indicator_of_notMem hdual hσ hσ₂ hy x, indicator_of_notMem hy, zero_mul]

end Vacuum

end HeisenbergDatum

namespace ReproducingModel

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {β : HeisenbergDatum W}
  {μ : Measure W} [μ.IsAddLeftInvariant] {L : AddSubgroup W} {σ : W → ℂ}
  [he : β.IsVacuum μ ((L : Set W).indicator σ)]

/-- The Heisenberg operators of `L` act on the vacuum vector of a lattice vacuum by the
semicharacter: `ϱ l e = σ l • e` for `l ∈ L`, when the vacuum is the extension by zero of a
function `σ` with `σ (a + b) = σ a * σ b * β a b` on `L`. -/
theorem heisenbergRep_vacuum_of_mem (hσ : ∀ a ∈ L, ∀ b ∈ L, σ (a + b) = σ a * σ b * β a b)
    {l : W} (hl : l ∈ L) :
    heisenbergRep l (vacuum : ReproducingModel β μ ((L : Set W).indicator σ)) =
      σ l • vacuum := by
  -- A vacuum is even with value `1` at `0`, which forces `σ a ^ 2 = 1` on `L`.
  have hσ₂ (a : W) (ha : a ∈ L) : σ a ^ 2 = 1 :=
    HeisenbergDatum.semichar_sq_of_zero_of_neg hσ (by simpa using he.apply_zero)
      (fun b hb ↦ by simpa [hb] using he.apply_neg b) ha
  refine ReproducingModel.ext fun x ↦ ?_
  rw [heisenbergRep_apply, vacuum_apply, smul_apply, vacuum_apply]
  exact β.apply_mul_indicator_sub_of_mem hσ hσ₂ hl x

end ReproducingModel

end TauCeti
