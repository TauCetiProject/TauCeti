/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.Algebra.Lie.Sl2.Kostant.GroupScheme
public import TauCeti.Algebra.Lie.Sl2.Weyl.Standard
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Weyl

/-!
# The Weyl involution in the rank-one Kostant carrier

For the full-weight `A₁` carrier constructed from the standard two-dimensional `sl₂` module, this
file specializes the integral Weyl representative

```text
n = x₀(1) x₁(-1) x₀(1)
```

to a point of the carrier over an arbitrary commutative ring.  It proves the rank-one Chevalley
relation

```text
n² = h(-1),
```

where `h(s) = diag(s, s⁻¹)` is the represented full-weight torus.  Consequently the image of `n`
in the pointwise normalizer quotient has square one.  Over a nontrivial ring this image is not the
identity: the Weyl matrix has a nonzero off-diagonal entry, whereas every torus point is diagonal.

This is the first quotient-level Weyl relation for the Kostant carriers.  It is the rank-one input
for comparing the normalizer of the represented torus with the Weyl group in the pinned
Chevalley--Demazure construction.

## Main declarations

* `TauCeti.Sl2Std.rankOneCarrierPoints`: the matrix-valued points of the full-weight rank-one
  carrier.
* `TauCeti.Sl2Std.rankOneCarrierTorusPoints`: its represented split-torus subgroup.
* `TauCeti.Sl2Std.rankOneWeylPoint`: the canonical Weyl representative in the carrier.
* `TauCeti.Sl2Std.rankOneWeylPoint_sq`: the relation `n² = h(-1)`.
* `TauCeti.Sl2Std.rankOneWeylClass`: the representative's class in the torus normalizer quotient.
* `TauCeti.Sl2Std.rankOneWeylClass_sq` and
  `TauCeti.Sl2Std.orderOf_rankOneWeylClass`: this class has order two.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.

This advances Layer 9, "Pinned Chevalley--Demazure group schemes over `ℤ`", of the
ReductiveGroups roadmap by establishing the first torus-normalizer quotient relation for the
full-weight rank-one carrier.
-/

public section

open TensorProduct

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

universe u v

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => repEnveloping ℚ 1
local notation "M" => Submodule.toAddSubgroup (integralLattice 1)
local notation "b" => integralLatticeAddSubgroupBasis 1
local notation "hnil" => isNilpotent_repEnveloping_root ℚ 1
local notation "hM" => kostantForm_apply_mem_integralLattice 1
local notation "wℤ" =>
  kostantWeylRestrict e h ρ M hM (hnil 0) (hnil 1)
local notation "wPts" =>
  kostantWeylPoints e h ρ M hM (hnil 0) (hnil 1)

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Carrier, torus, and Weyl points -/

/-- The points of the full-weight rank-one Kostant carrier, embedded in `GL₂`. -/
noncomputable abbrev rankOneCarrierPoints (A : Type u) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) A) :=
  kostantToralPointsSubgroup e h ρ M hM hnil b rankOneWeight A

/-- The represented full-weight torus homomorphism into the points of the rank-one carrier. -/
noncomputable def rankOneCarrierTorusHom (A : Type u) [CommRing A] :
    (Fin 1 → Aˣ) →* rankOneCarrierPoints A :=
  kostantToralWeightTorusPoints e h ρ M hM hnil b rankOneWeight A

/-- A represented full-weight torus point in the rank-one carrier. -/
noncomputable abbrev rankOneCarrierTorusPoint (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) :
    rankOneCarrierPoints A :=
  rankOneCarrierTorusHom A s

/-- The represented full-weight torus subgroup inside the points of the rank-one carrier. -/
noncomputable def rankOneCarrierTorusPoints (A : Type u) [CommRing A] :
    Subgroup (rankOneCarrierPoints A) :=
  (rankOneCarrierTorusHom A).range

/-- The canonical Weyl representative `x₀(1) x₁(-1) x₀(1)` in the rank-one carrier. -/
noncomputable def rankOneWeylPoint (A : Type u) [CommRing A] : rankOneCarrierPoints A :=
  kostantToralWeylPoint e h ρ M hM hnil b rankOneWeight 0 1 A

/-- The Weyl representative is natural in the ring of points. -/
theorem map_rankOneWeylPoint {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    GeneralLinear.mapHopfIdealPointsSubgroup 2
        (kostantToralDefiningIdeal e h ρ M hM hnil b rankOneWeight) φ.toIntAlgHom
        (MulEquiv.subgroupCongr
          (kostantToralPointsSubgroup_def e h ρ M hM hnil b rankOneWeight A)
          (rankOneWeylPoint A)) =
      MulEquiv.subgroupCongr
        (kostantToralPointsSubgroup_def e h ρ M hM hnil b rankOneWeight B)
        (rankOneWeylPoint B) := by
  exact map_kostantToralWeylPoint e h ρ M hM hnil b rankOneWeight φ 0 1

/-- In the standard basis, a carrier torus point is `diag(s, s⁻¹)`. -/
@[simp]
theorem coe_rankOneCarrierTorusPoint (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) :
    (rankOneCarrierTorusPoint A s : Matrix.GeneralLinearGroup (Fin 2) A) =
      diagGL ![s 0, (s 0)⁻¹] := by
  change (kostantToralWeightTorusPoints e h ρ M hM hnil b rankOneWeight A s :
    Matrix.GeneralLinearGroup (Fin 2) A) = _
  rw [coe_kostantToralWeightTorusPoints]
  rw [kostantTorusMatrix_apply]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeight_zero, rankOneWeight_one, diagGL_apply]

/-- The integral rank-one Weyl automorphism sends a standard lattice basis vector to the reversed
basis vector with the usual sign. -/
private theorem rankOneKostantWeylRestrict_apply_basis (j : Fin 2) :
    wℤ (b j) = ((-1 : ℤ) ^ (1 - (j : ℕ))) • b j.rev := by
  apply Subtype.ext
  rw [Sl2Std.coe_kostantWeylRestrict_apply]
  rw [AddSubgroupClass.coe_zsmul, coe_integralLatticeAddSubgroupBasis_apply,
    coe_integralLatticeAddSubgroupBasis_apply]
  rw [← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  exact Sl2Std.weylUnit_apply_basis ℚ 1 j

/-- The matrix of the rank-one Kostant Weyl automorphism has the signed reversal entries. -/
private theorem basisMatrix_rankOneKostantWeylGL_apply (A : Type u) [CommRing A]
    (i j : Fin 2) :
    ((Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange A)).toMonoidHom
        (kostantWeylGL e h ρ M hM (hnil 0) (hnil 1) A) :
          Matrix.GeneralLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j.rev then (-1 : A) ^ (i : ℕ) else 0 := by
  simp only [Units.coe_map]
  change (LinearMap.toMatrixAlgEquiv ((b).baseChange A)
    (kostantWeylGL e h ρ M hM (hnil 0) (hnil 1) A).val) i j = _
  rw [kostantWeylGL_val, LinearMap.toMatrixAlgEquiv_apply,
    Module.Basis.baseChange_apply]
  change (((b).baseChange A).repr (wPts A (1 ⊗ₜ[ℤ] b j))) i = _
  rw [kostantWeylPoints_apply_tmul, rankOneKostantWeylRestrict_apply_basis]
  fin_cases i <;> fin_cases j <;> simp

/-- The `(i,j)` entry of the rank-one Weyl representative is `(-1)^i` when `i` is the reversal
of `j`, and zero otherwise. -/
@[simp]
theorem coe_rankOneWeylPoint_apply (A : Type u) [CommRing A] (i j : Fin 2) :
    ((rankOneWeylPoint A : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) i j =
      if i = j.rev then (-1 : A) ^ (i : ℕ) else 0 := by
  rw [rankOneWeylPoint, coe_kostantToralWeylPoint]
  exact basisMatrix_rankOneKostantWeylGL_apply A i j

/-! ## The square relation -/

/-- **The rank-one Chevalley relation `n² = h(-1)` in the carrier.** -/
theorem rankOneWeylPoint_sq (A : Type u) [CommRing A] :
    rankOneWeylPoint A ^ 2 =
      rankOneCarrierTorusPoint A (fun _ ↦ (-1 : Aˣ)) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, coe_rankOneWeylPoint_apply, coe_rankOneCarrierTorusPoint,
      diagGL_apply, Matrix.mul_apply]

/-- The inverse rank-one Weyl representative is its product with the central torus point
`h(-1)`. -/
theorem rankOneWeylPoint_inv (A : Type u) [CommRing A] :
    (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierTorusPoint A (fun _ ↦ (-1 : Aˣ)) * rankOneWeylPoint A := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc, ← pow_two, rankOneWeylPoint_sq, ← map_mul]
  rw [show ((fun _ ↦ (-1 : Aˣ)) * fun _ ↦ (-1 : Aˣ)) = 1 by
    funext q
    fin_cases q
    simp, map_one]

/-- Conjugation by the rank-one Weyl representative inverts the represented torus. -/
theorem rankOneWeylPoint_conj_torus (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) :
    rankOneWeylPoint A * rankOneCarrierTorusPoint A s *
        (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierTorusPoint A (fun _ ↦ (s 0)⁻¹) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeylPoint_inv, coe_rankOneWeylPoint_apply, coe_rankOneCarrierTorusPoint,
      diagGL_apply, Matrix.mul_apply]

/-- The rank-one Weyl representative belongs to the normalizer of the represented torus. -/
theorem rankOneWeylPoint_mem_normalizer (A : Type u) [CommRing A] :
    rankOneWeylPoint A ∈
      _root_.Subgroup.normalizer
        ((rankOneCarrierTorusPoints A : Subgroup (rankOneCarrierPoints A)) :
          Set (rankOneCarrierPoints A)) := by
  rw [_root_.Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ ↦ (s 0)⁻¹, (rankOneWeylPoint_conj_torus A s).symm⟩
  · rintro ⟨s, hs⟩
    have hconj := rankOneWeylPoint_conj_torus A (fun _ ↦ (s 0)⁻¹)
    have hf : (fun _ ↦ ((s 0)⁻¹)⁻¹) = s := by
      funext q
      fin_cases q
      simp
    rw [hf] at hconj
    refine ⟨fun _ ↦ (s 0)⁻¹, ?_⟩
    apply (MulAut.conj (rankOneWeylPoint A)).injective
    change rankOneWeylPoint A * rankOneCarrierTorusPoint A (fun _ ↦ (s 0)⁻¹) *
        (rankOneWeylPoint A)⁻¹ = rankOneWeylPoint A * x * (rankOneWeylPoint A)⁻¹
    simpa using hconj.trans hs

/-! ## The normalizer-quotient involution -/

/-- The Weyl representative, regarded as a point of the torus normalizer. -/
noncomputable def rankOneWeylNormalizerPoint (A : Type u) [CommRing A] :
    _root_.Subgroup.normalizer
      ((rankOneCarrierTorusPoints A : Subgroup (rankOneCarrierPoints A)) :
        Set (rankOneCarrierPoints A)) :=
  ⟨rankOneWeylPoint A, rankOneWeylPoint_mem_normalizer A⟩

/-- The class of the Weyl representative in the pointwise torus normalizer quotient. -/
noncomputable def rankOneWeylClass (A : Type u) [CommRing A] :
    TauCeti.Subgroup.normalizerQuotient (rankOneCarrierTorusPoints A) :=
  TauCeti.Subgroup.normalizerQuotientMk (rankOneCarrierTorusPoints A)
    (rankOneWeylNormalizerPoint A)

/-- The Weyl class in the torus normalizer quotient has square one. -/
@[simp]
theorem rankOneWeylClass_sq (A : Type u) [CommRing A] :
    rankOneWeylClass A ^ 2 = 1 := by
  rw [rankOneWeylClass, ← map_pow]
  apply (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff
    (rankOneCarrierTorusPoints A) ((rankOneWeylNormalizerPoint A) ^ 2)).mpr
  change rankOneWeylPoint A ^ 2 ∈ rankOneCarrierTorusPoints A
  rw [rankOneWeylPoint_sq]
  exact ⟨fun _ ↦ (-1 : Aˣ), rfl⟩

/-- Over a nontrivial ring, the Weyl representative does not belong to the represented torus. -/
theorem rankOneWeylPoint_not_mem_torus (A : Type u) [CommRing A] [Nontrivial A] :
    rankOneWeylPoint A ∉ rankOneCarrierTorusPoints A := by
  rintro ⟨s, hs⟩
  change rankOneCarrierTorusPoint A s = rankOneWeylPoint A at hs
  have hentry := congrArg
    (fun g : rankOneCarrierPoints A ↦ ((g : Matrix.GeneralLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) 0 1) hs
  simp [coe_rankOneCarrierTorusPoint, coe_rankOneWeylPoint_apply,
    diagGL_apply] at hentry

/-- Over a nontrivial ring, the Weyl class in the torus normalizer quotient is not the identity.
-/
theorem rankOneWeylClass_ne_one (A : Type u) [CommRing A] [Nontrivial A] :
    rankOneWeylClass A ≠ 1 := by
  intro hclass
  have hm := (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff
    (rankOneCarrierTorusPoints A) (rankOneWeylNormalizerPoint A)).mp hclass
  exact rankOneWeylPoint_not_mem_torus A hm

/-- Over a nontrivial ring, the Weyl class has order exactly two in the pointwise torus
normalizer quotient. -/
@[simp]
theorem orderOf_rankOneWeylClass (A : Type u) [CommRing A] [Nontrivial A] :
    orderOf (rankOneWeylClass A) = 2 :=
  orderOf_eq_prime (rankOneWeylClass_sq A) (rankOneWeylClass_ne_one A)

end TauCeti.Sl2Std
