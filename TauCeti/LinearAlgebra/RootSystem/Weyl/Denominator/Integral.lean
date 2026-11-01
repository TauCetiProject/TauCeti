/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Invariant
import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber

/-!
# The dot alternatization and the Weyl denominator identity for a root datum

Let `P` be a root datum, a root pairing over `ℤ`, with a base and weight lattice `M`, and let
`ℤ[M]` be its integral group algebra, with `e^x` the basis element at `x`. In a root datum the Weyl
vector `ρ` need not be a weight (for `PGL₂` it is half a root), but for every Weyl-group element
`w` the difference `ρ - w ρ = ∑_{β > 0, w⁻¹ β < 0} β` is a sum of roots. This file defines the
**dot alternatization**

`J(f) = ∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} w(f)`,

a `ℤ`-linear endomorphism of `ℤ[M]` (`RootPairing.dotAlternatization`). On a basis element it is
the alternating sum `J(e^x) = ∑_w sgn(w) e^{w ⬝ x}` over the dot orbit `w ⬝ x = w(x + ρ) - ρ`,
the Weyl numerator of `x` (compare `TauCeti.weylNumerator`, which needs `ρ` to be a weight). Its
basic properties are that it is linear over the Weyl-invariant elements, and that it is
antisymmetric for the twisted simple reflections, `J(e^{-αᵢ} sᵢ(f)) = -J(f)`.

The main result is the **Weyl denominator identity** for a root datum:

`J(1) = ∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} = ∏_{α > 0} (1 - e^{-α}) = Δ`.

The version `TauCeti.weylDenominator_eq_weylNumerator_zero` is stated for a root system over an
ordered ring in which `2` is invertible, so that `ρ` is a weight and the roots span. Neither holds
for a general root datum such as that of `GLₙ` (roots do not span) or `PGL₂` (`ρ` is not a weight).
The identity here is the form needed for the integral Demazure operators of
`TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic`, which live on such root data.

## The argument

Write `T_w(f) = e^{-(ρ - w ρ)} w(f)`, the twisted reindexing `TauCeti.twistedWeylReindex`. Since
`ρ - v w ρ = (ρ - v ρ) + v(ρ - w ρ)`, the `T_w` compose like the group, `T_v T_w = T_{v w}`, and so
`T_v J = sgn(v) J`; also `T_w Δ = sgn(w) Δ`. Hence
`J(1) - Δ` is alternating for the twisted action. Such an element is determined by its coefficients
on the dominant chamber: every weight `x` has a Weyl translate `w ⬝ x` with `2(w ⬝ x) + 2ρ = w(2x +
2ρ)` dominant, and if `w ⬝ x` is not itself dominant it pairs to `-1` with some simple coroot, so
the twisted simple reflection fixes it and changes the sign of its coefficient. Only `2ρ`, which is
always a weight, enters. On the dominant chamber both `J(1)` and `Δ` have only the constant term
`1`: a weight `-(ρ - w ρ)` is dominant only for `w = 1`, because `2ρ` is strictly dominant
(`TauCeti.twoWeylVector_mem_openDominantChamber`), and the Weyl denominator has only its constant
term there (`TauCeti.coeff_weylDenominator_of_mem_dominantChamber`).

## Main definitions

* `RootPairing.dotAlternatization`: the dot alternatization `J` of `ℤ[M]`.

## Main results

* `RootPairing.dotAlternatization_apply` and `RootPairing.dotAlternatization_single`: the defining
  formula, and its value on a basis element.
* `RootPairing.dotAlternatization_mul_of_isWeylInvariant`: `J(g f) = g J(f)` for Weyl-invariant
  `g`.
* `RootPairing.dotAlternatization_single_neg_root_mul`: `J(e^{-αᵢ} sᵢ(f)) = -J(f)` for a simple
  root `αᵢ`.
* `RootPairing.dotAlternatization_one`: **the Weyl denominator identity** `J(1) = Δ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Ch. VI, §3, no. 3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, §5.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra TauCeti

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) [Finite ι]
  (b : P.Base)

/-! ### The shift `ρ - w ρ` and the twisted reindexing `T_w` -/

/-- The shift `ρ - w ρ = ∑_{β > 0, w⁻¹ β < 0} β`, which is a weight even when `ρ` is not. -/
private abbrev rhoShift (w : P.weylGroup) : M := ∑ i ∈ inversionsFinset P b w⁻¹, P.root i

omit [Finite ι] in
include P in
/-- The weight lattice of a root datum is torsion free, so `2` can be cancelled. -/
private lemma eq_of_two_smul_eq {x y : M} (h : (2 : ℤ) • x = (2 : ℤ) • y) : x = y := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  exact smul_right_injective M two_ne_zero h

private lemma smul_twoWeylVector_eq (w : P.weylGroup) :
    w • twoWeylVector P b = twoWeylVector P b - (2 : ℤ) • rhoShift P b w := by
  rw [sub_eq_iff_eq_add.mp (smul_twoWeylVector_sub_twoWeylVector P b w), neg_smul]
  abel

/-- The cocycle identity `ρ - v w ρ = (ρ - v ρ) + v(ρ - w ρ)`, proved through `2ρ`. -/
private lemma rhoShift_mul (v w : P.weylGroup) :
    rhoShift P b (v * w) = rhoShift P b v + v • rhoShift P b w := by
  refine eq_of_two_smul_eq P ?_
  have h := smul_twoWeylVector_eq P b (v * w)
  rw [mul_smul, smul_twoWeylVector_eq, smul_sub, smul_twoWeylVector_eq, smul_comm v (2 : ℤ)] at h
  rw [smul_add]
  generalize v • rhoShift P b w = a at h ⊢
  linear_combination (norm := module) h

private lemma rhoShift_one : rhoShift P b 1 = 0 := by
  simp [rhoShift, inversionsFinset_one]

/-- `2(w ⬝ x) + 2ρ = w(2x + 2ρ)`, where `w ⬝ x = w x - (ρ - w ρ)`. -/
private lemma two_smul_smul_sub_rhoShift_add (w : P.weylGroup) (x : M) :
    (2 : ℤ) • (w • x - rhoShift P b w) + twoWeylVector P b =
      w • ((2 : ℤ) • x + twoWeylVector P b) := by
  rw [smul_add, smul_twoWeylVector_eq, smul_comm w (2 : ℤ) x]
  generalize w • x = a
  module

/-- The twisted reindexing `T_w(f) = e^{-(ρ - w ρ)} w(f)`, under which `e^x ↦ e^{w ⬝ x}`. -/
private abbrev dotReindex (w : P.weylGroup) : AddMonoidAlgebra ℤ M →ₗ[ℤ] AddMonoidAlgebra ℤ M :=
  twistedWeylReindex P (-rhoShift P b w) w

private lemma dotReindex_dotReindex (v w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b v (dotReindex P b w f) = dotReindex P b (v * w) f := by
  simp only [twistedWeylReindex_apply, map_mul, weylReindex_mul, ← mul_assoc, rhoShift_mul,
    weylReindex_single, single_mul_single, mul_one, smul_neg, neg_add]

/-- The coefficient of `T_w(f)` at `w ⬝ x` is the coefficient of `f` at `x`. -/
private lemma coeff_dotReindex (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) (x : M) :
    (dotReindex P b w f).coeff (w • x - rhoShift P b w) = f.coeff x := by
  rw [coeff_twistedWeylReindex, sub_neg_eq_add, sub_add_cancel, inv_smul_smul]

variable [P.IsReduced]

private lemma rhoShift_ofIdx {i : ι} (hi : i ∈ b.support) :
    rhoShift P b (weylGroup.ofIdx P i) = P.root i := by
  simp [rhoShift, inversionsFinset_ofIdx P b hi]

private lemma dotReindex_ofIdx {i : ι} (hi : i ∈ b.support) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b (weylGroup.ofIdx P i) f =
      single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
  rw [twistedWeylReindex_apply, rhoShift_ofIdx P b hi, weylReindex_ofIdx]

/-- The Weyl denominator is alternating for the twisted action: `T_w Δ = sgn(w) Δ`. -/
private lemma dotReindex_weylDenominator (w : P.weylGroup) :
    dotReindex P b w (weylDenominator P b) = (weylSign P b w : ℤ) • weylDenominator P b := by
  have hcancel : single (-rhoShift P b w) (1 : ℤ) * single (rhoShift P b w) 1 = 1 := by
    rw [single_mul_single, neg_add_cancel, mul_one, one_def]
  have hsign : single (rhoShift P b w) ((-1 : ℤ) ^ (inversionsFinset P b w⁻¹).card) =
      (weylSign P b w : ℤ) • single (rhoShift P b w) 1 := by
    rw [smul_single', mul_one, card_inversionsFinset, ncard_inversions_inv, weylSign_apply]
    simp
  rw [twistedWeylReindex_apply, weylReindex_apply, mapDomain_smul_weylDenominator, hsign,
    smul_mul_assoc, mul_smul_comm, ← mul_assoc, hcancel, one_mul]

/-- The coefficient form of alternation for the twisted action. -/
private lemma coeff_smul_sub_rhoShift {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ w, dotReindex P b w f = (weylSign P b w : ℤ) • f) (w : P.weylGroup) (x : M) :
    f.coeff (w • x - rhoShift P b w) = (weylSign P b w : ℤ) * f.coeff x := by
  have h := coeff_dotReindex P b w f x
  rw [hf w, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at h
  rw [← h, ← mul_assoc, Int.units_coe_mul_self, one_mul]

/-- An element alternating for the twisted action and vanishing on the dominant chamber is `0`. -/
private lemma eq_zero_of_coeff_dominantChamber {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ w, dotReindex P b w f = (weylSign P b w : ℤ) • f)
    (h : ∀ y ∈ dominantChamber P b, f.coeff y = 0) : f = 0 := by
  have := P.finite_weylGroup_of_base b
  refine AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_)
  obtain ⟨w, hw⟩ :=
    exists_mem_dominantChamber_of_finite_weylGroup P b ((2 : ℤ) • x + twoWeylVector P b)
  rw [← two_smul_smul_sub_rhoShift_add] at hw
  have hcoeff := coeff_smul_sub_rhoShift P b hf w x
  suffices hy : f.coeff (w • x - rhoShift P b w) = 0 by
    rw [hy, eq_comm, mul_eq_zero] at hcoeff
    exact hcoeff.resolve_left (Units.ne_zero _)
  set y := w • x - rhoShift P b w
  by_cases hdom : y ∈ dominantChamber P b
  · exact h y hdom
  -- Off the dominant chamber, `2y + 2ρ` lies on the wall of some simple root `αᵢ`, so `y` is fixed
  -- by the twisted simple reflection, which changes the sign of its coefficient.
  obtain ⟨i, hi, hlt⟩ : ∃ i ∈ b.support, P.coroot' i y < 0 := by
    simpa [mem_dominantChamber] using hdom
  have h2 := (mem_dominantChamber P b _).mp hw i hi
  rw [map_add, map_zsmul, coroot'_twoWeylVector P b hi, smul_eq_mul] at h2
  have hm : P.coroot' i y = -1 := by omega
  have hfix : weylGroup.ofIdx P i • y - rhoShift P b (weylGroup.ofIdx P i) = y := by
    rw [rhoShift_ofIdx P b hi, weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply, hm]
    simp
  have hsign := coeff_smul_sub_rhoShift P b hf (weylGroup.ofIdx P i) y
  rw [hfix, weylSign_ofIdx] at hsign
  simp only [Units.val_neg, Units.val_one, neg_mul, one_mul] at hsign
  omega

/-! ### The dot alternatization -/

variable [Fintype P.weylGroup]

/-- **The dot alternatization** `J(f) = ∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} w(f)` of the integral group
algebra of a root datum, where `ρ - w ρ = ∑_{β > 0, w⁻¹ β < 0} β`. On a basis element it is the
alternating sum `J(e^x) = ∑_w sgn(w) e^{w ⬝ x}` over the dot orbit `w ⬝ x = w(x + ρ) - ρ`
(`RootPairing.dotAlternatization_single`). -/
def dotAlternatization : AddMonoidAlgebra ℤ M →ₗ[ℤ] AddMonoidAlgebra ℤ M :=
  ∑ w : P.weylGroup, (weylSign P b w : ℤ) • dotReindex P b w

private lemma dotAlternatization_eq_sum (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b f = ∑ w : P.weylGroup, (weylSign P b w : ℤ) • dotReindex P b w f := by
  simp [dotAlternatization]

/-- The defining formula of `RootPairing.dotAlternatization`. -/
theorem dotAlternatization_apply (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b f = ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      (single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 * mapDomain (w • ·) f) := by
  simp only [dotAlternatization_eq_sum, twistedWeylReindex_apply, weylReindex_apply]

/-- The dot alternatization of a basis element `e^x` is `∑_w sgn(w) e^{w x - (ρ - w ρ)}`, the
alternating sum over the dot orbit of `x`. -/
theorem dotAlternatization_single (x : M) :
    dotAlternatization P b (single x 1) = ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      single (w • x - ∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 := by
  rw [dotAlternatization_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [mapDomain_single, single_mul_single, mul_one, neg_add_eq_sub]

private lemma dotAlternatization_dotReindex (v : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b (dotReindex P b v f) =
      (weylSign P b v : ℤ) • dotAlternatization P b f := by
  simp only [dotAlternatization_eq_sum, dotReindex_dotReindex, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulRight v) _ _ fun w ↦ ?_
  rw [Equiv.coe_mulRight, map_mul, Units.val_mul, mul_left_comm, Int.units_coe_mul_self, mul_one]

private lemma dotReindex_dotAlternatization (v : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b v (dotAlternatization P b f) =
      (weylSign P b v : ℤ) • dotAlternatization P b f := by
  simp only [dotAlternatization_eq_sum, map_sum, map_zsmul, dotReindex_dotReindex,
    Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun w ↦ ?_
  rw [Equiv.coe_mulLeft, map_mul, Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

/-- **The dot alternatization is linear over the Weyl-invariant elements**: `J(g f) = g J(f)`. -/
theorem dotAlternatization_mul_of_isWeylInvariant {g : AddMonoidAlgebra ℤ M}
    (hg : IsWeylInvariant P g) (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b (g * f) = g * dotAlternatization P b f := by
  simp only [dotAlternatization_eq_sum, Finset.mul_sum, mul_smul_comm, hg.twistedWeylReindex_mul]

/-- **The dot alternatization is antisymmetric for a twisted simple reflection**:
`J(e^{-αᵢ} sᵢ(f)) = -J(f)`. -/
theorem dotAlternatization_single_neg_root_mul {i : ι} (hi : i ∈ b.support)
    (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b
        (single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f) =
      -dotAlternatization P b f := by
  rw [← dotReindex_ofIdx P b hi, dotAlternatization_dotReindex, weylSign_ofIdx]
  simp

/-- On the dominant chamber, `J(1) = ∑_w sgn(w) e^{-(ρ - w ρ)}` has only its constant term `1`: a
weight `-(ρ - w ρ)` is dominant only for `w = 1`, because `2ρ` is strictly dominant. -/
private lemma coeff_dotAlternatization_one {y : M} (hy : y ∈ dominantChamber P b) :
    (dotAlternatization P b 1).coeff y = (1 : AddMonoidAlgebra ℤ M).coeff y := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ N := .of_isPerfPair P.flip.toLinearMap
  simp only [dotAlternatization_eq_sum, twistedWeylReindex_apply, map_one, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_smul_apply]
  rw [Fintype.sum_eq_single 1 fun w hw ↦ ?_]
  · simp [rhoShift_one, one_def]
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne, smul_zero]
  rintro rfl
  refine hw (eq_one_of_smul_mem_dominantChamber P b w (twoWeylVector_mem_openDominantChamber P b)
    ((mem_dominantChamber P b _).mpr fun i hi ↦ ?_))
  rw [smul_twoWeylVector_eq, map_sub, map_zsmul, coroot'_twoWeylVector P b hi, smul_eq_mul]
  have := (mem_dominantChamber P b _).mp hy i hi
  rw [map_neg] at this
  linarith

/-- **The Weyl denominator identity for a root datum**:

`∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} = ∏_{α > 0} (1 - e^{-α})`,

where `ρ - w ρ = ∑_{β > 0, w⁻¹ β < 0} β`. Unlike `TauCeti.weylDenominator_eq_weylNumerator_zero`,
this needs neither `ρ` to be a weight nor the roots to span. -/
@[simp]
theorem dotAlternatization_one : dotAlternatization P b 1 = weylDenominator P b := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ N := .of_isPerfPair P.flip.toLinearMap
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_dominantChamber P b (fun w ↦ ?_) fun y hy ↦ ?_
  · rw [map_sub, dotReindex_dotAlternatization, dotReindex_weylDenominator, smul_sub]
  · rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_dotAlternatization_one P b hy,
      coeff_weylDenominator_of_mem_dominantChamber P b hy, sub_self]

end RootPairing
