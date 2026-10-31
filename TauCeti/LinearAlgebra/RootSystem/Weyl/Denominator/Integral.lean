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

Write `T_w(f) = e^{-(ρ - w ρ)} w(f)`. Since `ρ - v w ρ = (ρ - v ρ) + v(ρ - w ρ)`, the `T_w` compose
like the group, `T_v T_w = T_{v w}`, and so `T_v J = sgn(v) J`; also `T_w Δ = sgn(w) Δ`. Hence
`J(1) - Δ` is alternating for the twisted action. Such an element is determined by its coefficients
on the dominant chamber: every weight `x` has a Weyl translate `w ⬝ x` with `2(w ⬝ x) + 2ρ = w(2x +
2ρ)` dominant, and if `w ⬝ x` is not itself dominant it pairs to `-1` with some simple coroot, so
the twisted simple reflection fixes it and changes the sign of its coefficient. Only `2ρ`, which is
always a weight, enters. On the dominant chamber both `J(1)` and `Δ` have only the constant term
`1`: a weight `-(ρ - w ρ)` is dominant only for `w = 1`, because `2ρ` is strictly dominant, and a
dominant weight `-ν` with `ν` a sum of positive roots is `0`, because the sum `2ρ^∨` of the positive
coroots is nonnegative on the dominant chamber and positive on the positive roots.

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

omit [Finite ι] in
/-- The reindexing of `ℤ[M]` along a Weyl-group element, as a ring homomorphism, is
`AddMonoidAlgebra.mapDomain` along its action. -/
private lemma mapDomainRingHom_toAddMonoidHom (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w) f = mapDomain (w • ·) f := by
  -- The coercion of `DistribSMul.toAddMonoidHom M w` is `(w • ·)` by definition.
  rw [mapDomainRingHom_apply]
  rfl

omit [Finite ι] in
/-- The reindexing of `ℤ[M]` along a Weyl-group element composes like the group. -/
private lemma mapDomainRingHom_mul (v w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M (v * w)) f =
      mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M v)
        (mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w) f) := by
  have h : DistribSMul.toAddMonoidHom M (v * w) =
      (DistribSMul.toAddMonoidHom M v).comp (DistribSMul.toAddMonoidHom M w) :=
    AddMonoidHom.ext fun x ↦ mul_smul v w x
  rw [h, mapDomainRingHom_comp, RingHom.comp_apply]

omit [Finite ι] in
/-- The reindexing of `ℤ[M]` along a simple reflection, in the form used by the Demazure
operators. -/
private lemma mapDomainRingHom_ofIdx (i : ι) (f : AddMonoidAlgebra ℤ M) :
    mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M (weylGroup.ofIdx P i)) f =
      mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x c => simp

omit [Finite ι] in
/-- The reindexing of `ℤ[M]` along a Weyl-group element fixes the Weyl-invariant elements. -/
private lemma mapDomainRingHom_of_isWeylInvariant {g : AddMonoidAlgebra ℤ M}
    (hg : IsWeylInvariant P g) (w : P.weylGroup) :
    mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w) g = g := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_)
  obtain ⟨y, rfl⟩ : ∃ y, w • y = x := ⟨w⁻¹ • x, smul_inv_smul w x⟩
  have hinj : Function.Injective (DistribSMul.toAddMonoidHom M w) := MulAction.injective w
  rw [mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
  exact (Finsupp.mapDomain_apply_of_injective hinj g.coeff y).trans (hg.coeff_smul w y).symm

/-- The twisted reindexing `T_w(f) = e^{-(ρ - w ρ)} w(f)`, under which `e^x ↦ e^{w ⬝ x}`. -/
private def dotReindex (w : P.weylGroup) : AddMonoidAlgebra ℤ M →ₗ[ℤ] AddMonoidAlgebra ℤ M :=
  LinearMap.mulLeft ℤ (single (-rhoShift P b w) 1) ∘ₗ
    (mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w)).toIntAlgHom.toLinearMap

private lemma dotReindex_apply (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b w f =
      single (-rhoShift P b w) 1 * mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w) f :=
  (rfl)

private lemma dotReindex_mul (w : P.weylGroup) (f g : AddMonoidAlgebra ℤ M) :
    dotReindex P b w (f * g) =
      dotReindex P b w f * mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w) g := by
  simp only [dotReindex_apply, map_mul, mul_assoc]

private lemma dotReindex_dotReindex (v w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b v (dotReindex P b w f) = dotReindex P b (v * w) f := by
  simp only [dotReindex_apply, map_mul, mapDomainRingHom_mul, ← mul_assoc, rhoShift_mul]
  congr 1
  simp only [mapDomainRingHom_apply, mapDomain_single, single_mul_single, mul_one,
    DistribSMul.toAddMonoidHom_apply, smul_neg, neg_add]

/-- The coefficient of `T_w(f)` at `w ⬝ x` is the coefficient of `f` at `x`. -/
private lemma coeff_dotReindex (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) (x : M) :
    (dotReindex P b w f).coeff (w • x - rhoShift P b w) = f.coeff x := by
  have hinj : Function.Injective (DistribSMul.toAddMonoidHom M w) := MulAction.injective w
  rw [dotReindex_apply, sub_eq_neg_add, coeff_single_mul_add, one_mul, mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
  exact Finsupp.mapDomain_apply_of_injective hinj f.coeff x

variable [P.IsReduced]

private lemma rhoShift_ofIdx {i : ι} (hi : i ∈ b.support) :
    rhoShift P b (weylGroup.ofIdx P i) = P.root i := by
  simp [rhoShift, inversionsFinset_ofIdx P b hi]

private lemma dotReindex_ofIdx {i : ι} (hi : i ∈ b.support) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b (weylGroup.ofIdx P i) f =
      single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
  rw [dotReindex_apply, rhoShift_ofIdx P b hi, mapDomainRingHom_ofIdx]

/-- The Weyl denominator is alternating for the twisted action: `T_w Δ = sgn(w) Δ`. -/
private lemma dotReindex_weylDenominator (w : P.weylGroup) :
    dotReindex P b w (weylDenominator P b) = (weylSign P b w : ℤ) • weylDenominator P b := by
  rw [dotReindex_apply, mapDomainRingHom_toAddMonoidHom, mapDomain_smul_weylDenominator,
    ← mul_assoc, single_mul_single, neg_add_cancel, one_mul, ← mul_one ((-1 : ℤ) ^ _),
    ← smul_single', ← one_def, smul_mul_assoc, one_mul, card_inversionsFinset,
    ncard_inversions_inv, weylSign_apply]
  simp

/-- The coefficient form of alternation for the twisted action. -/
private lemma coeff_smul_sub_rhoShift {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ w, dotReindex P b w f = (weylSign P b w : ℤ) • f) (w : P.weylGroup) (x : M) :
    f.coeff (w • x - rhoShift P b w) = (weylSign P b w : ℤ) * f.coeff x := by
  have h := coeff_dotReindex P b w f x
  rw [hf w, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at h
  rw [← h, ← mul_assoc]
  rcases Int.units_eq_one_or (weylSign P b w) with hw | hw <;> simp [hw]

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
    rcases Int.units_eq_one_or (weylSign P b w) with h' | h' <;> simp_all
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

/-- A dominant weight `y` with `-y` a sum of positive roots is `0`. The sum `2ρ^∨` of the positive
coroots pairs to `2` with every simple root and nonnegatively with every dominant weight. -/
private lemma eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone {y : M}
    (hy : y ∈ dominantChamber P b) (hcone : -y ∈ posRootCone P b) : y = 0 := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ N := .of_isPerfPair P.flip.toLinearMap
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp hcone
  have hsimple (j : ι) (hj : j ∈ b.support) :
      P.toLinearMap (P.root j) (twoWeylVector P.flip b.flip) = 2 :=
    coroot'_twoWeylVector P.flip b.flip hj
  have hnonneg : 0 ≤ P.toLinearMap y (twoWeylVector P.flip b.flip) := by
    rw [twoWeylVector_def, map_sum]
    refine Finset.sum_nonneg fun β hβ ↦ coroot'_nonneg_of_mem_posRoots P b hy ?_
    rw [mem_posRootsFinset, mem_posRoots, Base.isPos_flip_iff] at hβ
    exact (mem_posRoots P b β).mpr hβ
  have hval : P.toLinearMap (-y) (twoWeylVector P.flip b.flip) =
      2 * ∑ j ∈ b.support, (c j : ℤ) := by
    rw [hc, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [map_nsmul, LinearMap.smul_apply, hsimple j hj, nsmul_eq_mul, mul_comm]
  have hsum : ∑ j ∈ b.support, (c j : ℤ) = 0 := by
    rw [map_neg, LinearMap.neg_apply] at hval
    have : 0 ≤ ∑ j ∈ b.support, (c j : ℤ) := Finset.sum_nonneg fun _ _ ↦ by positivity
    linarith
  have hc0 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ Nat.cast_nonneg _).mp hsum
  rw [← neg_neg y, hc, Finset.sum_eq_zero fun j hj ↦ by simp [Nat.cast_eq_zero.mp (hc0 j hj)],
    neg_zero]

/-- On the dominant chamber the Weyl denominator has only its constant term `1`. -/
private lemma coeff_weylDenominator_of_mem_dominantChamber {y : M}
    (hy : y ∈ dominantChamber P b) :
    (weylDenominator P b).coeff y = (1 : AddMonoidAlgebra ℤ M).coeff y := by
  by_cases h : (weylDenominator P b).coeff y = 0
  · rw [h, one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
    rintro rfl
    simp at h
  · obtain rfl := eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone P b hy
      (neg_mem_posRootCone_of_coeff_weylDenominator_ne_zero P b h)
    simp [one_def]

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
  simp only [dotAlternatization_eq_sum, dotReindex_apply, mapDomainRingHom_toAddMonoidHom]

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
  simp only [Equiv.coe_mulRight, map_mul, Units.val_mul]
  congr 1
  rcases Int.units_eq_one_or (weylSign P b v) with h | h <;> simp [h]

private lemma dotReindex_dotAlternatization (v : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    dotReindex P b v (dotAlternatization P b f) =
      (weylSign P b v : ℤ) • dotAlternatization P b f := by
  simp only [dotAlternatization_eq_sum, map_sum, map_zsmul, dotReindex_dotReindex,
    Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun w ↦ ?_
  simp only [Equiv.coe_mulLeft, map_mul, Units.val_mul]
  congr 1
  rcases Int.units_eq_one_or (weylSign P b v) with h | h <;> simp [h]

/-- **The dot alternatization is linear over the Weyl-invariant elements**: `J(g f) = g J(f)`. -/
theorem dotAlternatization_mul_of_isWeylInvariant {g : AddMonoidAlgebra ℤ M}
    (hg : IsWeylInvariant P g) (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b (g * f) = g * dotAlternatization P b f := by
  simp only [dotAlternatization_eq_sum, Finset.mul_sum, mul_smul_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [mul_comm g, dotReindex_mul, mapDomainRingHom_of_isWeylInvariant P hg, mul_comm]

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
  have hρ : twoWeylVector P b ∈ openDominantChamber P b :=
    (mem_openDominantChamber P b _).mpr fun i hi ↦ by rw [coroot'_twoWeylVector P b hi]; norm_num
  simp only [dotAlternatization_eq_sum, dotReindex_apply, map_one, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_smul_apply]
  rw [Fintype.sum_eq_single 1 fun w hw ↦ ?_]
  · simp [rhoShift_one, one_def]
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne, smul_zero]
  rintro rfl
  refine hw (eq_one_of_smul_mem_dominantChamber P b w hρ ((mem_dominantChamber P b _).mpr
    fun i hi ↦ ?_))
  rw [smul_twoWeylVector_eq, map_sub, map_zsmul, coroot'_twoWeylVector P b hi, smul_eq_mul]
  have := (mem_dominantChamber P b _).mp hy i hi
  rw [map_neg] at this
  linarith

/-- **The Weyl denominator identity for a root datum**:

`∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} = ∏_{α > 0} (1 - e^{-α})`,

where `ρ - w ρ = ∑_{β > 0, w⁻¹ β < 0} β`. Unlike `TauCeti.weylDenominator_eq_weylNumerator_zero`,
this needs neither `ρ` to be a weight nor the roots to span. -/
theorem dotAlternatization_one : dotAlternatization P b 1 = weylDenominator P b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_dominantChamber P b (fun w ↦ ?_) fun y hy ↦ ?_
  · rw [map_sub, dotReindex_dotAlternatization, dotReindex_weylDenominator, smul_sub]
  · rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_dotAlternatization_one P b hy,
      coeff_weylDenominator_of_mem_dominantChamber P b hy, sub_self]

end RootPairing
