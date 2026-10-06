/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.PointsFunctor
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Weyl
import TauCeti.Algebra.Algebra.Hom

/-!
# Simple Weyl representatives in the type-`A` carrier

At the Bourbaki node `i` of the type `A_r` carrier `TauCeti.SlStd.groupScheme r`, the numbered
root subgroups `x_{α_i}` and `x_{-α_i}` give the Weyl representative

```text
n_i = x_{α_i}(1) x_{-α_i}(-1) x_{α_i}(1),
```

a point of the carrier over every commutative ring (`TauCeti.SlStd.simpleWeylPoint`). Conjugation
by `n_i` interchanges the two root subgroups at `i`, negating the parameter, reflects the weight
torus by the root `α_i`, and so normalizes the torus.

In coordinates `n_i` is the signed permutation matrix of the transposition of `i` and `i + 1`,
sending `e_i` to `-e_{i+1}` and `e_{i+1}` to `e_i`. It satisfies the Chevalley relation
`n_i² = h_i(-1)`, where `h_i(-1)` is the torus point with value `-1` at `i` and `1` elsewhere, and
over a nontrivial ring its class in the pointwise normalizer quotient of the torus has order
exactly two.

## Main declarations

* `TauCeti.SlStd.simpleWeylPoint`: the Weyl representative at a node, as a carrier point.
* `TauCeti.SlStd.simpleWeylPoint_conj_rootSubgroupPoints`: `n_i x_{α_i}(u) n_i⁻¹ = x_{-α_i}(-u)`.
* `TauCeti.SlStd.simpleWeylPoint_conj_weightTorusPoints` and
  `TauCeti.SlStd.simpleWeylPoint_mem_normalizer`: `n_i` reflects and normalizes the weight torus.
* `TauCeti.SlStd.coe_simpleWeylPoint_apply`: the matrix entries of `n_i`.
* `TauCeti.SlStd.simpleWeylPoint_sq`: the Chevalley relation `n_i² = h_i(-1)`.
* `TauCeti.SlStd.orderOf_simpleWeylClass`: the class of `n_i` in the torus normalizer quotient has
  order two over a nontrivial ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.SlStd

open TauCeti.UniversalEnvelopingAlgebra

universe u v

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- The points of the type `A_r` carrier are the points of the generic Kostant toral closure it is
cut out from. -/
theorem points_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    points r A =
      kostantToralPointsSubgroup (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A := by
  rw [points_def, kostantToralPointsSubgroup_def, definingIdeal_def]

/-- The standard representation carries the numbered `sl₂` triple at node `i` to an `sl₂` triple
of endomorphisms of the standard module. -/
theorem isSl2Triple_rep (i : Fin r) :
    IsSl2Triple (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator r i)))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inl i))))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inr i)))) := by
  refine (isSl2Triple_rootGenerator r i).map
    ((rep r).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) fun hzero => ?_
  have h := congrFun (DFunLike.congr_fun hzero (Pi.single i.castSucc 1)) i.castSucc
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, rep_ι_apply, val_cartanGenerator,
    LinearMap.zero_apply, Pi.zero_apply] at h
  simp [(Fin.castSucc_lt_succ (i := i)).ne'] at h

/-- **The Weyl representative at the node `i`**: `x_{α_i}(1) x_{-α_i}(-1) x_{α_i}(1)`, as a point of
the type `A_r` carrier. -/
noncomputable def simpleWeylPoint (i : Fin r) (A : Type v) [CommRing A] : points r A :=
  (MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup r A)).symm
    (kostantToralWeylPoint (rootGenerator r) (cartanGenerator r) (rep r)
      (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (.inl i) (.inr i) A)

/-- In the coordinate basis, the Weyl representative is the matrix of the integral Weyl
automorphism of the standard lattice. -/
theorem coe_simpleWeylPoint (i : Fin r) (A : Type v) [CommRing A] :
    (simpleWeylPoint r i A : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      Units.map (LinearMap.toMatrixAlgEquiv ((latticeBasis r).baseChange A)).toMulEquiv
        (kostantWeylGL (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r (.inl i)) (isNilpotent_rep_rootGenerator r (.inr i))
          A) := by
  rw [simpleWeylPoint, MulEquiv.subgroupCongr_symm_apply, coe_kostantToralWeylPoint]

/-- The Weyl representative is natural in the ring of points. -/
@[simp]
theorem map_simpleWeylPoint (i : Fin r) {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    (pointsPresentation r A).map (pointsPresentation r B) φ (simpleWeylPoint r i A) =
      simpleWeylPoint r i B := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map]
  simp only [simpleWeylPoint, MulEquiv.subgroupCongr_symm_apply]
  have hmap := congrArg Subtype.val
    (map_kostantToralWeylPoint (rootGenerator r) (cartanGenerator r) (rep r)
      (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) φ (.inl i) (.inr i))
  simpa only [GeneralLinear.coe_mapHopfIdealPointsSubgroup, MulEquiv.subgroupCongr_apply,
    RingHom.toIntAlgHom_toRingHom] using hmap

/-- **Conjugation by the Weyl representative at `i` interchanges the root subgroups at `i`**:
`n_i x_{α_i}(u) n_i⁻¹ = x_{-α_i}(-u)`. -/
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin r) (A : Type v) [CommRing A] (u : A) :
    simpleWeylPoint r i A * rootSubgroupPoints r (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint r i A)⁻¹ =
      rootSubgroupPoints r (.inr i) A (Multiplicative.ofAdd (-u)) := by
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_rootSubgroupPoints (wt := weight r) (i := .inl i) (j := .inr i)
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (isNilpotent_rep_rootGenerator r)
      (latticeBasis r) (isSl2Triple_rep r i) A u)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint, coe_rootSubgroupPoints,
    coe_kostantToralWeylPoint, coe_kostantToralRootSubgroupPoints] using hconj

private theorem lie_cartanGenerator_rootGenerator_inr (i q : Fin r) :
    ⁅cartanGenerator r q, rootGenerator r (.inr i)⁆ =
      -(((rootGeneratorWeight r (.inl i) q : ℤ) : ℚ) • rootGenerator r (.inr i)) := by
  rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inr, rootGeneratorWeight_inl,
    Int.cast_neg, neg_smul]

/-- **Conjugation by the Weyl representative at `i` reflects the weight torus** by the root
`α_i`. -/
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin r) (A : Type v) [CommRing A]
    (s : Fin r → Aˣ) :
    simpleWeylPoint r i A * weightTorusPoints r A s * (simpleWeylPoint r i A)⁻¹ =
      weightTorusPoints r A (weylReflectTorusPoint (rootGeneratorWeight r (.inl i)) i s) := by
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_weightTorusPoints (wt := weight r) (i := .inl i) (j := .inr i)
      (c := i) (α := rootGeneratorWeight r (.inl i)) (rootGenerator r) (cartanGenerator r)
      (rep r) (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (isSl2Triple_rep r i)
      (fun q => lie_cartanGenerator_rootGenerator r (.inl i) q)
      (lie_cartanGenerator_rootGenerator_inr r i) (isCartanWeightVector_latticeBasis r) A s)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint, coe_weightTorusPoints,
    coe_kostantToralWeylPoint, coe_kostantToralWeightTorusPoints] using hconj

/-- The Weyl representative at `i` normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer (i : Fin r) (A : Type v) [CommRing A] :
    simpleWeylPoint r i A ∈ Subgroup.normalizer
      (((weightTorusPoints r A).range : Subgroup (points r A)) : Set (points r A)) := by
  let carrierEquiv : points r A ≃*
      kostantToralPointsSubgroup (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A :=
    MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup r A)
  have htorusPoint (s : Fin r → Aˣ) :
      carrierEquiv (weightTorusPoints r A s) =
        kostantToralWeightTorusPoints (rootGenerator r) (cartanGenerator r) (rep r)
          (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A s := by
    apply Subtype.ext
    simp only [carrierEquiv, MulEquiv.subgroupCongr_apply]
    rw [coe_weightTorusPoints, coe_kostantToralWeightTorusPoints]
  have htorus : (weightTorusPoints r A).range.map carrierEquiv.toMonoidHom =
      (kostantToralWeightTorusPoints (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (htorusPoint s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨weightTorusPoints r A s, ⟨s, rfl⟩, htorusPoint s⟩
  rw [← Subgroup.mem_map_iff_mem (f := carrierEquiv.toMonoidHom) carrierEquiv.injective,
    Subgroup.map_equiv_normalizer_eq, htorus]
  simpa [simpleWeylPoint, carrierEquiv] using
    (kostantToralWeylPoint_mem_normalizer_weightTorusPoints (i := .inl i) (j := .inr i)
      (c := i) (α := rootGeneratorWeight r (.inl i)) (rootGenerator r) (cartanGenerator r)
      (rep r) (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (isSl2Triple_rep r i)
      (fun q => lie_cartanGenerator_rootGenerator r (.inl i) q)
      (lie_cartanGenerator_rootGenerator_inr r i) (isCartanWeightVector_latticeBasis r) A)

/-! ## The matrix of the Weyl representative -/

private theorem exp_rep_rootGenerator (k : Fin r ⊕ Fin r) :
    IsNilpotent.exp (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) =
      1 + rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) := by
  rw [IsNilpotent.exp_eq_sum (pow_two_rep_rootGenerator_eq_zero r k)]
  simp [Finset.sum_range_succ]

private theorem exp_neg_rep_rootGenerator (k : Fin r ⊕ Fin r) :
    IsNilpotent.exp (-rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) =
      1 - rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) := by
  have hsq : (-rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) ^ 2 = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [pow_two, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.neg_apply, map_neg, neg_neg,
      rep_rootGenerator_rep_rootGenerator_eq_zero, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hsq]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

/-- The Weyl element at `i` sends `e_i` to `-e_{i+1}`, sends `e_{i+1}` to `e_i`, and fixes the
other coordinate vectors. -/
private theorem weylUnit_apply_single (i : Fin r) (j : Fin (r + 1)) :
    ((weylUnit (isNilpotent_rep_rootGenerator r (.inl i))
        (isNilpotent_rep_rootGenerator r (.inr i)) : (Module.End ℚ (Fin (r + 1) → ℚ))ˣ) :
          Module.End ℚ (Fin (r + 1) → ℚ)) (Pi.single j 1) =
      (if j = i.castSucc then (-1 : ℚ) else 1) •
        Pi.single (Equiv.swap i.castSucc i.succ j) 1 := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  rw [coe_weylUnit, exp_rep_rootGenerator, exp_neg_rep_rootGenerator]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_add, map_sub, rep_rootGenerator_apply, rootSource_inl, rootTarget_inl, rootSource_inr,
    rootTarget_inr]
  by_cases hc : j = i.castSucc
  · subst hc
    simp [hne.symm]
  · by_cases hs : j = i.succ
    · subst hs
      simp [hne, hne.symm]
    · simp [hc, Equiv.swap_apply_of_ne_of_ne hc hs, Pi.single_apply, Ne.symm hc, Ne.symm hs]

private theorem kostantWeylRestrict_latticeBasis (i : Fin r) (j : Fin (r + 1)) :
    kostantWeylRestrict (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r (.inl i)) (isNilpotent_rep_rootGenerator r (.inr i))
        (latticeBasis r j) =
      (if j = i.castSucc then (-1 : ℤ) else 1) •
        latticeBasis r (Equiv.swap i.castSucc i.succ j) := by
  apply Subtype.ext
  rw [coe_kostantWeylRestrict_apply, AddSubgroupClass.coe_zsmul, coe_latticeBasis,
    coe_latticeBasis, ← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  exact weylUnit_apply_single r i j

/-- **The matrix of the Weyl representative at `i`** is the signed permutation matrix of the
transposition of `i` and `i + 1`: its column `j` is `-e_{i+1}` for `j = i`, `e_i` for `j = i + 1`,
and `e_j` otherwise. -/
theorem coe_simpleWeylPoint_apply (i : Fin r) (A : Type v) [CommRing A] (a b : Fin (r + 1)) :
    ((simpleWeylPoint r i A : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) a b =
      if a = Equiv.swap i.castSucc i.succ b then (if b = i.castSucc then -1 else 1) else 0 := by
  rw [coe_simpleWeylPoint, Units.coe_map]
  -- The mapped unit's value is definitionally the basis matrix of its underlying endomorphism.
  change (LinearMap.toMatrixAlgEquiv ((latticeBasis r).baseChange A)
    (kostantWeylGL (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r (.inl i)) (isNilpotent_rep_rootGenerator r (.inr i))
      A).val) a b = _
  rw [kostantWeylGL_val, LinearMap.toMatrixAlgEquiv_apply, Module.Basis.baseChange_apply,
    LinearEquiv.coe_coe, kostantWeylPoints_apply_tmul, kostantWeylRestrict_latticeBasis]
  by_cases hb : b = i.castSucc
  · subst hb
    by_cases ha : a = i.succ <;> simp [ha]
  · simp [hb, Finsupp.single_apply, eq_comm]

/-- **The Chevalley relation `n_i² = h_i(-1)`**: the square of the Weyl representative at `i` is
the torus point with value `-1` at `i` and `1` elsewhere. -/
@[simp]
theorem simpleWeylPoint_sq (i : Fin r) (A : Type v) [CommRing A] :
    simpleWeylPoint r i A ^ 2 = weightTorusPoints r A (Pi.mulSingle i (-1)) := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two, Matrix.mul_apply,
    Finset.sum_eq_single (Equiv.swap i.castSucc i.succ b)]
  · simp only [coe_weightTorusPoints, kostantTorusMatrix_apply, diagGL_apply,
      torusCharacter_mulSingle, weight_def]
    by_cases hab : a = b
    · subst hab
      by_cases hc : a = i.castSucc
      · subst hc
        simp [coe_simpleWeylPoint_apply, hne, hne.symm]
      · by_cases hs : a = i.succ
        · subst hs
          simp [coe_simpleWeylPoint_apply, hne.symm]
        · simp [coe_simpleWeylPoint_apply, hc, hs, Equiv.swap_apply_of_ne_of_ne hc hs]
    · simp [coe_simpleWeylPoint_apply, hab]
  · intro c _ hc
    simp [coe_simpleWeylPoint_apply r i A c b, hc]
  · simp

/-- Conjugation by the Weyl representative at `i` sends the negative root subgroup at `i` to the
positive one, negating the parameter: `n_i x_{-α_i}(u) n_i⁻¹ = x_{α_i}(-u)`. -/
theorem simpleWeylPoint_conj_rootSubgroupPoints_inr (i : Fin r) (A : Type v) [CommRing A]
    (u : A) :
    simpleWeylPoint r i A * rootSubgroupPoints r (.inr i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint r i A)⁻¹ =
      rootSubgroupPoints r (.inl i) A (Multiplicative.ofAdd (-u)) := by
  have hpos := simpleWeylPoint_conj_rootSubgroupPoints r i A (-u)
  rw [neg_neg] at hpos
  let n := simpleWeylPoint r i A
  let x := rootSubgroupPoints r (.inl i) A (Multiplicative.ofAdd (-u))
  -- The torus point `h_i(-1) = n_i²` fixes `x_{α_i}`, since `α_i(h_i(-1)) = (-1) ^ 2 = 1`.
  have hfix : weightTorusPoints r A (Pi.mulSingle i (-1)) * x *
      (weightTorusPoints r A (Pi.mulSingle i (-1)))⁻¹ = x := by
    have hconj := congrArg Subtype.val
      (kostantToralWeightTorusPoints_conj_rootSubgroupPoints (i := .inl i)
        (α := rootGeneratorWeight r (.inl i)) (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
        (isCartanWeightVector_latticeBasis r)
        (fun q => lie_cartanGenerator_rootGenerator r (.inl i) q) A (Pi.mulSingle i (-1))
        (Multiplicative.ofAdd (-u)))
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_weightTorusPoints, coe_rootSubgroupPoints,
      x] at hconj ⊢
    simpa [CartanMatrix.A] using hconj
  rw [← hpos]
  calc
    n * (n * x * n⁻¹) * n⁻¹ = n ^ 2 * x * (n ^ 2)⁻¹ := by
      rw [pow_two]
      group
    _ = x := by rw [simpleWeylPoint_sq, hfix]

/-! ## The normalizer class -/

/-- The Weyl representative at `i`, as a point of the normalizer of the weight torus. -/
noncomputable def simpleWeylNormalizerPoint (i : Fin r) (A : Type v) [CommRing A] :
    Subgroup.normalizer
      (((weightTorusPoints r A).range : Subgroup (points r A)) : Set (points r A)) :=
  ⟨simpleWeylPoint r i A, simpleWeylPoint_mem_normalizer r i A⟩

@[simp]
theorem coe_simpleWeylNormalizerPoint (i : Fin r) (A : Type v) [CommRing A] :
    (simpleWeylNormalizerPoint r i A : points r A) = simpleWeylPoint r i A :=
  (rfl)

/-- The class of the Weyl representative at `i` in the normalizer quotient of the weight torus. -/
noncomputable def simpleWeylClass (i : Fin r) (A : Type v) [CommRing A] :
    Subgroup.normalizerQuotient (weightTorusPoints r A).range :=
  Subgroup.normalizerQuotientMk _ (simpleWeylNormalizerPoint r i A)

/-- The Weyl class at `i` has square one. -/
@[simp]
theorem simpleWeylClass_sq (i : Fin r) (A : Type v) [CommRing A] :
    simpleWeylClass r i A ^ 2 = 1 := by
  rw [simpleWeylClass, ← map_pow]
  apply (Subgroup.normalizerQuotientMk_eq_one_iff _ _).mpr
  have hsquare : simpleWeylPoint r i A ^ 2 ∈ (weightTorusPoints r A).range := by
    rw [simpleWeylPoint_sq]
    exact ⟨Pi.mulSingle i (-1), rfl⟩
  simpa only [Subgroup.coe_pow, coe_simpleWeylNormalizerPoint] using hsquare

/-- Over a nontrivial ring, the Weyl representative at `i` is not a torus point: its `(i, i + 1)`
entry is `1`, while torus points are diagonal. -/
theorem simpleWeylPoint_notMem_range (i : Fin r) (A : Type v) [CommRing A] [Nontrivial A] :
    simpleWeylPoint r i A ∉ (weightTorusPoints r A).range := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  rintro ⟨s, hs⟩
  have hentry := congrArg
    (fun g : points r A ↦ ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A) i.castSucc i.succ) hs
  simp only [coe_weightTorusPoints, kostantTorusMatrix_apply, diagGL_apply,
    coe_simpleWeylPoint_apply] at hentry
  simp [hne, hne.symm] at hentry

/-- Over a nontrivial ring, the Weyl class at `i` is not the identity. -/
theorem simpleWeylClass_ne_one (i : Fin r) (A : Type v) [CommRing A] [Nontrivial A] :
    simpleWeylClass r i A ≠ 1 := by
  intro hclass
  rw [simpleWeylClass] at hclass
  have hm := (Subgroup.normalizerQuotientMk_eq_one_iff _ _).mp hclass
  exact simpleWeylPoint_notMem_range r i A
    (by simpa only [coe_simpleWeylNormalizerPoint] using hm)

/-- **Over a nontrivial ring, the Weyl class at `i` has order exactly two** in the normalizer
quotient of the weight torus. -/
@[simp]
theorem orderOf_simpleWeylClass (i : Fin r) (A : Type v) [CommRing A] [Nontrivial A] :
    orderOf (simpleWeylClass r i A) = 2 :=
  orderOf_eq_prime (simpleWeylClass_sq r i A) (simpleWeylClass_ne_one r i A)

end TauCeti.SlStd
