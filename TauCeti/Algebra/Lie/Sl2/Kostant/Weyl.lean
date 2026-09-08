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
# The rank-one Weyl representative in the Kostant carrier

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

This quotient-level Weyl relation supplies the rank-one input for comparing the normalizer of the
represented torus with the Weyl group in the pinned Chevalley--Demazure construction.

## Main declarations

* `TauCeti.Sl2Std.rankOneWeylPoint`: the canonical Weyl representative in the carrier.
* `TauCeti.Sl2Std.rankOneWeylPoint_sq`: the relation `n² = h(-1)`.
* `TauCeti.Sl2Std.rankOneWeylPoint_conj_rootSubgroupPoint`: conjugation by `n` interchanges the
  two carrier-valued root subgroups.
* `TauCeti.Sl2Std.rankOneWeylClass`: the representative's class in the torus normalizer quotient.
* `TauCeti.Sl2Std.rankOneWeylClass_sq` and
  `TauCeti.Sl2Std.orderOf_rankOneWeylClass`: this class has square one over every commutative ring
  and order exactly two over a nontrivial ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
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

/-! ## The Weyl point -/

/-- The canonical Weyl representative `x₀(1) x₁(-1) x₀(1)` in the rank-one carrier. -/
noncomputable def rankOneWeylPoint (A : Type u) [CommRing A] : rankOneCarrierPoints A :=
  (MulEquiv.subgroupCongr (rankOneCarrierPoints_def A)).symm
    (kostantToralWeylPoint e h ρ M hM hnil b rankOneWeight 0 1 A)

/-- The Weyl representative is natural in the ring of points. -/
@[simp]
theorem map_rankOneWeylPoint {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    rankOneCarrierPointsMap φ (rankOneWeylPoint A) = rankOneWeylPoint B := by
  apply Subtype.ext
  rw [coe_rankOneCarrierPointsMap]
  simp only [rankOneWeylPoint, MulEquiv.subgroupCongr_symm_apply]
  have hmap := congrArg Subtype.val
    (map_kostantToralWeylPoint e h ρ M hM hnil b rankOneWeight φ 0 1)
  have hring : φ.toIntAlgHom.toRingHom = φ := RingHom.ext (RingHom.toIntAlgHom_apply φ)
  simpa only [GeneralLinear.coe_mapHopfIdealPointsSubgroup,
    MulEquiv.subgroupCongr_apply, hring] using hmap

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
  -- The mapped unit's value is definitionally the basis matrix of its underlying endomorphism.
  change (LinearMap.toMatrixAlgEquiv ((b).baseChange A)
    (kostantWeylGL e h ρ M hM (hnil 0) (hnil 1) A).val) i j = _
  rw [kostantWeylGL_val, LinearMap.toMatrixAlgEquiv_apply,
    Module.Basis.baseChange_apply]
  rw [LinearEquiv.coe_coe, kostantWeylPoints_apply_tmul,
    rankOneKostantWeylRestrict_apply_basis]
  fin_cases i <;> fin_cases j <;> simp

/-- The carrier-valued Weyl point is the matrix of the integral Weyl automorphism. -/
theorem coe_rankOneWeylPoint (A : Type u) [CommRing A] :
    (rankOneWeylPoint A : Matrix.GeneralLinearGroup (Fin 2) A) =
      Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange A)).toMulEquiv
        (kostantWeylGL e h ρ M hM (hnil 0) (hnil 1) A) := by
  rw [rankOneWeylPoint, MulEquiv.subgroupCongr_symm_apply,
    coe_kostantToralWeylPoint]

/-- The `(i,j)` entry of the rank-one Weyl representative is `(-1)^i` when `i` is the reversal
of `j`, and zero otherwise. -/
@[simp]
theorem coe_rankOneWeylPoint_apply (A : Type u) [CommRing A] (i j : Fin 2) :
    ((rankOneWeylPoint A : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) i j =
      if i = j.rev then (-1 : A) ^ (i : ℕ) else 0 := by
  rw [coe_rankOneWeylPoint]
  exact basisMatrix_rankOneKostantWeylGL_apply A i j

/-! ## The square relation -/

/-- **The rank-one Chevalley relation `n² = h(-1)` in the carrier.** -/
@[simp]
theorem rankOneWeylPoint_sq (A : Type u) [CommRing A] :
    rankOneWeylPoint A ^ 2 =
      rankOneCarrierTorusPoint A (fun _ ↦ (-1 : Aˣ)) := by
  apply Subtype.ext
  rw [coe_rankOneCarrierTorusPoint]
  rw [Subgroup.coe_pow, coe_rankOneWeylPoint]
  rw [← map_pow, pow_two]
  apply Units.ext
  simp only [Units.coe_map, Units.val_mul, kostantWeylGL_val, Module.End.mul_eq_comp]
  rw [kostantWeylPoints_comp_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrixAlgEquiv_apply, diagGL_apply]

/-- The inverse rank-one Weyl representative is its product with the central torus point
`h(-1)`. -/
@[simp]
theorem rankOneWeylPoint_inv (A : Type u) [CommRing A] :
    (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierTorusPoint A (fun _ ↦ (-1 : Aˣ)) * rankOneWeylPoint A := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc, ← pow_two, rankOneWeylPoint_sq, ← map_mul]
  have hnegOneSq : ((fun _ : Fin 1 ↦ (-1 : Aˣ)) * fun _ ↦ (-1 : Aˣ)) = 1 := by
    funext q
    fin_cases q
    simp
  rw [hnegOneSq, map_one]

private theorem isSl2Triple_repEnveloping_rankOne : IsSl2Triple
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h 0)))
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e 0)))
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e 1))) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    repEnveloping_ι_slFinTwoBasis]
  exact isSl2Triple_diag_raise_lower (K := ℚ) (n := 1) (by norm_num)

private theorem lie_cartan_root_one_eq_neg_smul (q : Fin 1) :
    ⁅h q, e 1⁆ = -((rankOneRootWeight 0 q : ℚ) • e 1) := by
  rw [lie_cartan_root_eq_smul]
  fin_cases q
  simp [rankOneRootWeight_zero, rankOneRootWeight_one]

private theorem rankOneWeylPoint_conj_rootSubgroupPoint_zero
    (A : Type u) [CommRing A] (t : A) :
    rankOneWeylPoint A *
        rankOneCarrierRootSubgroupPoint 0 A (Multiplicative.ofAdd t) *
        (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierRootSubgroupPoint 1 A (Multiplicative.ofAdd (-t)) := by
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_rootSubgroupPoints (wt := rankOneWeight)
      (i := 0) (j := 1) e h ρ M hM hnil b isSl2Triple_repEnveloping_rankOne A t)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rankOneWeylPoint,
    coe_rankOneCarrierRootSubgroupPoint, coe_kostantToralWeylPoint,
    coe_kostantToralRootSubgroupPoints] using hconj

/-- Conjugation by the rank-one Weyl representative interchanges the two root subgroups and
negates their parameters. -/
theorem rankOneWeylPoint_conj_rootSubgroupPoint
    (A : Type u) [CommRing A] (i : Fin 2) (t : Multiplicative A) :
    rankOneWeylPoint A * rankOneCarrierRootSubgroupPoint i A t *
        (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierRootSubgroupPoint i.rev A
        (Multiplicative.ofAdd (-Multiplicative.toAdd t)) := by
  fin_cases i
  · exact rankOneWeylPoint_conj_rootSubgroupPoint_zero A (Multiplicative.toAdd t)
  · have hzero := rankOneWeylPoint_conj_rootSubgroupPoint_zero A
      (-Multiplicative.toAdd t)
    simp only [neg_neg] at hzero
    have hof : Multiplicative.ofAdd (Multiplicative.toAdd t) = t := rfl
    rw [hof] at hzero
    let z := rankOneCarrierTorusPoint A (fun _ ↦ (-1 : Aˣ))
    let x := rankOneCarrierRootSubgroupPoint 0 A
      (Multiplicative.ofAdd (-Multiplicative.toAdd t))
    have hcomm : z * x = x * z := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro r s
      fin_cases r <;> fin_cases s <;>
        simp [z, x, Matrix.mul_apply, Fin.sum_univ_two]
    change rankOneWeylPoint A * rankOneCarrierRootSubgroupPoint 1 A t *
        (rankOneWeylPoint A)⁻¹ = x
    rw [← hzero]
    calc
      rankOneWeylPoint A * (rankOneWeylPoint A * x * (rankOneWeylPoint A)⁻¹) *
          (rankOneWeylPoint A)⁻¹ =
          rankOneWeylPoint A ^ 2 * x * (rankOneWeylPoint A ^ 2)⁻¹ := by
        rw [pow_two]
        group
      _ = z * x * z⁻¹ := by rw [rankOneWeylPoint_sq]
      _ = x := by rw [hcomm]; group

/-- Conjugation by the rank-one Weyl representative inverts the represented torus. -/
theorem rankOneWeylPoint_conj_torus (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) :
    rankOneWeylPoint A * rankOneCarrierTorusPoint A s *
        (rankOneWeylPoint A)⁻¹ =
      rankOneCarrierTorusPoint A (fun _ ↦ (s 0)⁻¹) := by
  have hreflect : weylReflectTorusPoint (rankOneRootWeight 0) 0 s =
      (fun _ ↦ (s 0)⁻¹) := by
    funext q
    have hq : q = 0 := Subsingleton.elim _ _
    subst q
    rw [weylReflectTorusPoint_apply_same, rankOneRootWeight_zero, torusCharacter_singleton]
    group
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_weightTorusPoints (wt := rankOneWeight)
      (i := 0) (j := 1) (c := 0) (α := rankOneRootWeight 0) e h ρ M hM hnil b
      isSl2Triple_repEnveloping_rankOne (lie_cartan_root_eq_smul 0)
      lie_cartan_root_one_eq_neg_smul isCartanWeightVector_integralLatticeAddSubgroupBasis A s)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kostantToralWeylPoint,
    coe_kostantToralWeightTorusPoints, hreflect, kostantTorusMatrix_apply] at hconj
  have hdiag (t : Fin 1 → Aˣ) :
      (fun i ↦ torusCharacter t (rankOneWeight i)) = ![t 0, (t 0)⁻¹] := by
    funext i
    fin_cases i
    · change torusCharacter t (rankOneWeight 0) = t 0
      rw [rankOneWeight_zero, torusCharacter_singleton]
      simp
    · change torusCharacter t (rankOneWeight 1) = (t 0)⁻¹
      rw [rankOneWeight_one, torusCharacter_singleton]
      simp
  rw [hdiag s, hdiag (fun _ ↦ (s 0)⁻¹)] at hconj
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rankOneWeylPoint,
    coe_rankOneCarrierTorusPoint] using hconj

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
    rw [rankOneWeylPoint_conj_torus]
    exact ⟨fun _ ↦ (s 0)⁻¹, rfl⟩
  · rintro ⟨s, hs⟩
    refine ⟨(fun _ ↦ (s 0)⁻¹), ?_⟩
    apply (MulAut.conj (rankOneWeylPoint A)).injective
    have hconj := rankOneWeylPoint_conj_torus A (fun _ ↦ (s 0)⁻¹)
    have hinv : (fun _ : Fin 1 ↦ ((s 0)⁻¹)⁻¹) = s := by
      funext q
      fin_cases q
      simp
    rw [hinv] at hconj
    exact hconj.trans hs

/-! ## The normalizer-quotient involution -/

/-- The Weyl representative, regarded as a point of the torus normalizer. -/
noncomputable def rankOneWeylNormalizerPoint (A : Type u) [CommRing A] :
    _root_.Subgroup.normalizer
      ((rankOneCarrierTorusPoints A : Subgroup (rankOneCarrierPoints A)) :
        Set (rankOneCarrierPoints A)) :=
  ⟨rankOneWeylPoint A, rankOneWeylPoint_mem_normalizer A⟩

/-- The underlying carrier point of the packaged normalizer element is the Weyl representative. -/
@[simp]
theorem coe_rankOneWeylNormalizerPoint (A : Type u) [CommRing A] :
    ((rankOneWeylNormalizerPoint A :
        _root_.Subgroup.normalizer
          ((rankOneCarrierTorusPoints A : Subgroup (rankOneCarrierPoints A)) :
            Set (rankOneCarrierPoints A))) : rankOneCarrierPoints A) =
      rankOneWeylPoint A :=
  by rw [rankOneWeylNormalizerPoint]

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
  have hsquare : rankOneWeylPoint A ^ 2 ∈ rankOneCarrierTorusPoints A := by
    rw [rankOneWeylPoint_sq]
    exact ⟨fun _ ↦ (-1 : Aˣ), rfl⟩
  simpa only [Subgroup.coe_pow, coe_rankOneWeylNormalizerPoint] using hsquare

/-- Over a nontrivial ring, the Weyl representative does not belong to the represented torus. -/
theorem rankOneWeylPoint_notMem_rankOneCarrierTorusPoints
    (A : Type u) [CommRing A] [Nontrivial A] :
    rankOneWeylPoint A ∉ rankOneCarrierTorusPoints A := by
  rintro ⟨s, hs⟩
  have hs' : rankOneCarrierTorusPoint A s = rankOneWeylPoint A := by
    simpa only [rankOneCarrierTorusPoint] using hs
  have hentry := congrArg
    (fun g : rankOneCarrierPoints A ↦ ((g : Matrix.GeneralLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) 0 1) hs'
  rw [coe_rankOneCarrierTorusPoint, coe_rankOneWeylPoint_apply] at hentry
  simp [diagGL_apply] at hentry

/-- Over a nontrivial ring, the Weyl class in the torus normalizer quotient is not the identity.
-/
theorem rankOneWeylClass_ne_one (A : Type u) [CommRing A] [Nontrivial A] :
    rankOneWeylClass A ≠ 1 := by
  intro hclass
  rw [rankOneWeylClass] at hclass
  have hm := (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff
    (rankOneCarrierTorusPoints A) (rankOneWeylNormalizerPoint A)).mp hclass
  exact rankOneWeylPoint_notMem_rankOneCarrierTorusPoints A
    (by simpa only [coe_rankOneWeylNormalizerPoint] using hm)

/-- Over a nontrivial ring, the Weyl class has order exactly two in the pointwise torus
normalizer quotient. -/
@[simp]
theorem orderOf_rankOneWeylClass (A : Type u) [CommRing A] [Nontrivial A] :
    orderOf (rankOneWeylClass A) = 2 :=
  orderOf_eq_prime (rankOneWeylClass_sq A) (rankOneWeylClass_ne_one A)

end TauCeti.Sl2Std
