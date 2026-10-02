/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.Algebra.Module.NatInt

/-!
# The standard representation of the type-B spin carrier

The full-weight type-`Bₙ₊₁` spin carrier is a closed subgroup of `GL_(2^(n+1))`. After base
change to a commutative ring `R`, its standard representation is therefore the corestriction of
the standard general-linear comodule along the quotient coordinate morphism.

This file proves that the resulting representation, the spin representation of the carrier, is
faithful over every commutative ring and simple over every field. For simplicity, restriction to
the spin weight torus separates a nonzero invariant vector into its one-dimensional weight
components, since the spin weights are pairwise distinct. A numbered simple root generator acts
on an exterior basis vector by creating and contracting coordinates, so whenever the corresponding
spin weight pairs to `∓1` with the simple coroot, the positive or negative simple-root element at
parameter one moves that basis vector to its simple reflection, up to sign. The spin weights form
a single orbit of the simple reflections, so a coordinate vector reaches every other one.

## Main declarations

* `TauCeti.TypeBSpinCarrier.standardComodule`: the standard comodule on `R^(2^(n+1))`.
* `TauCeti.TypeBSpinCarrier.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.TypeBSpinCarrier.mulVec_mem` and `TauCeti.TypeBSpinCarrier.points_mulVec_mem`:
  subcomodules are stable under carrier-valued points and under concrete carrier points.
* `TauCeti.TypeBSpinCarrier.torusCorestrict_eq_ofWeights`: restricted to the weight torus, the
  standard comodule is the direct sum of the spin weight lines.
* `TauCeti.TypeBSpinCarrier.instIsSimpleOrderSubcomodule`: simplicity over a field.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.

The corestriction, faithfulness, and point-action arguments, and the shape of the simplicity
proof, follow the type-`E₆` minuscule carrier in
`TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`.
-/

public section

open CategoryTheory Module WithConv
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix TensorProduct

namespace TauCeti.TypeBSpinCarrier

universe u

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized type-`Bₙ₊₁` spin carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R) :=
  let _ := GeneralLinear.standardComodule R (dimension n)
  Comodule.Corestrict (coordinateMap n R).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard carrier coaction is the standard general-linear coaction followed by the
quotient coordinate morphism. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R (dimension n)
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R (dimension n))
        (D := coordinateHopfAlgebra n R) (M := Fin (dimension n) → R)
        (coordinateMap n R).hom.toCoalgHom =
      TensorProduct.map LinearMap.id
          (coordinateMap n R).hom.toCoalgHom.toLinearMap ∘ₗ
        GeneralLinear.standardCoact R (dimension n) := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- **The standard comodule of the specialized type-`Bₙ₊₁` spin carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra n R)
      (V := Fin (dimension n) → R) :=
  Comodule.isFaithful_corestrict_of_surjective (coordinateMap n R).hom
    (coordinateMap_surjective n R) (GeneralLinear.isFaithful_standardComodule R (dimension n))

/-- **A subcomodule of the standard carrier comodule is stable under every carrier-valued
point.** -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (g : WithConv (coordinateHopfAlgebra n R →ₐ[R] R)) {w : Fin (dimension n) → R}
    (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear (dimension n)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (dimension n)) (baseChangeDefiningIdeal n R)
          (CommAlgCat.of R R) g) : Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈
      N := by
  have h := Comodule.basePointsRepresentation_mem N g hw
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap n R).hom g,
    GeneralLinear.basePointsRepresentation_eq_mulVec] at h
  have hpoint :
      AlgHom.mapDomain (coordinateMap n R).hom g =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (dimension n)) (baseChangeDefiningIdeal n R)
          (CommAlgCat.of R R) g :=
    mapPointsFunctor_coordinateMap_app n R g
  rwa [hpoint] at h

/-- A subcomodule of the standard carrier comodule is stable under every concrete carrier
point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (g : points n R) {w : Fin (dimension n) → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈ N := by
  have h := mulVec_mem n R N ((baseChangePointsMulEquiv n R (CommAlgCat.of R R)).symm g) hw
  rw [quotientPointsHom_baseChangePointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## The numbered simple root generators on the coordinate basis -/

/-- A positive numbered simple root generator moves an exterior basis vector whose spin weight
pairs to `-1` with the simple coroot to the basis vector of the reflected sign set, up to sign. -/
private theorem exists_rep_rootGenerator_inl_exteriorBasis (i : Fin (n + 1))
    (s t : Finset (Fin (n + 1))) (hs : DynkinType.typeBSpinWeight s i = -1)
    (ht : DynkinType.typeBSpinReflection i s = t) :
    ∃ c : ℤˣ, rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily (.inl i)))
        ((polarizationBasis n).ExteriorAlgebra s) =
      c • (polarizationBasis n).ExteriorAlgebra t := by
  subst ht
  revert hs
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro hs
    have hlt : ¬((Fin.last n : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp
    rw [DynkinType.typeBSpinWeight_apply, ite_eq_right hlt] at hs
    have hlast : Fin.last n ∉ s := fun h ↦ by simp [h] at hs
    have hrefl : DynkinType.typeBSpinReflection (Fin.last n) s = insert (Fin.last n) s := by
      ext a
      rw [DynkinType.mem_typeBSpinReflection_iff_of_last hlt]
      by_cases ha : a = Fin.last n
      · simp [ha, hlast]
      · simp [ha]
    rw [rep_rootGenerator_inl_last, TauCeti.ExteriorAlgebra.involute_basis, mul_smul_comm,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_right hlast, hrefl]
    exact ⟨_, neg_one_pow_smul_units_smul _ _ _⟩
  · intro hs
    have hlt : ((j.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp
    rw [DynkinType.typeBSpinWeight_apply, ite_eq_left hlt, Fin.orderSucc_castSucc] at hs
    have hj : j.castSucc ∉ s := fun h ↦ by
      simp only [h, ite_true] at hs
      split_ifs at hs <;> omega
    have hsucc : j.succ ∈ s := by
      by_contra h
      simp only [h, ite_false] at hs
      split_ifs at hs
      omega
    have hne : (j.castSucc : Fin (n + 1)) ≠ j.succ := Fin.castSucc_lt_succ.ne
    have hrefl : DynkinType.typeBSpinReflection j.castSucc s =
        insert j.castSucc (s.erase j.succ) := by
      ext a
      rw [DynkinType.mem_typeBSpinReflection_iff_of_lt hlt, Fin.orderSucc_castSucc]
      by_cases ha : a = j.castSucc
      · simp [ha, hsucc]
      · by_cases hb : a = j.succ
        · simp [hb, hj, hne.symm]
        · simp [Equiv.swap_apply_of_ne_of_ne ha hb, ha, hb]
    rw [rep_rootGenerator_inl_castSucc, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
      ite_eq_left hsucc, mul_smul_comm, TauCeti.ExteriorAlgebra.ι_mul_basis,
      ite_eq_right (by simp [hj]), smul_smul, hrefl]
    exact ⟨_, rfl⟩

/-- A negative numbered simple root generator moves an exterior basis vector whose spin weight
pairs to `1` with the simple coroot to the basis vector of the reflected sign set, up to sign. -/
private theorem exists_rep_rootGenerator_inr_exteriorBasis (i : Fin (n + 1))
    (s t : Finset (Fin (n + 1))) (hs : DynkinType.typeBSpinWeight s i = 1)
    (ht : DynkinType.typeBSpinReflection i s = t) :
    ∃ c : ℤˣ, rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily (.inr i)))
        ((polarizationBasis n).ExteriorAlgebra s) =
      c • (polarizationBasis n).ExteriorAlgebra t := by
  subst ht
  revert hs
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro hs
    have hlt : ¬((Fin.last n : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp
    rw [DynkinType.typeBSpinWeight_apply, ite_eq_right hlt] at hs
    have hlast : Fin.last n ∈ s := by
      by_contra h
      simp [h] at hs
    have hrefl : DynkinType.typeBSpinReflection (Fin.last n) s = s.erase (Fin.last n) := by
      ext a
      rw [DynkinType.mem_typeBSpinReflection_iff_of_last hlt]
      by_cases ha : a = Fin.last n
      · simp [ha, hlast]
      · simp [ha]
    rw [rep_rootGenerator_inr_last, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
      ite_eq_left hlast, Units.smul_def, map_zsmul, TauCeti.ExteriorAlgebra.involute_basis,
      smul_comm, ← Units.smul_def, hrefl]
    exact ⟨_, neg_one_pow_smul_units_smul _ _ _⟩
  · intro hs
    have hlt : ((j.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp
    rw [DynkinType.typeBSpinWeight_apply, ite_eq_left hlt, Fin.orderSucc_castSucc] at hs
    have hj : j.castSucc ∈ s := by
      by_contra h
      simp only [h, ite_false] at hs
      split_ifs at hs <;> omega
    have hsucc : j.succ ∉ s := fun h ↦ by
      simp only [h, ite_true] at hs
      split_ifs at hs
      omega
    have hne : (j.castSucc : Fin (n + 1)) ≠ j.succ := Fin.castSucc_lt_succ.ne
    have hrefl : DynkinType.typeBSpinReflection j.castSucc s =
        insert j.succ (s.erase j.castSucc) := by
      ext a
      rw [DynkinType.mem_typeBSpinReflection_iff_of_lt hlt, Fin.orderSucc_castSucc]
      by_cases ha : a = j.castSucc
      · simp [ha, hsucc, hne]
      · by_cases hb : a = j.succ
        · simp [hb, hj]
        · simp [Equiv.swap_apply_of_ne_of_ne ha hb, ha, hb]
    rw [rep_rootGenerator_inr_castSucc, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
      ite_eq_left hj, mul_smul_comm, TauCeti.ExteriorAlgebra.ι_mul_basis,
      ite_eq_right (by simp [hsucc]), smul_smul, hrefl]
    exact ⟨_, rfl⟩

/-- The integral matrix of a represented numbered simple root generator in the lattice basis. -/
private noncomputable def rootGeneratorMatrix (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  fun r s ↦ (latticeBasis n).repr
    ⟨rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n s),
      rep_kostantForm_mem_lattice n _ (rootVector_mem_kostantForm _ _ j) _ (latticeBasis n s).2⟩ r

private theorem rep_rootGenerator_latticeBasis (j : Fin (n + 1) ⊕ Fin (n + 1))
    (s : Fin (dimension n)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n s : ExteriorAlgebra ℚ (polarization n).W) =
      ∑ r, rootGeneratorMatrix n j r s •
        (latticeBasis n r : ExteriorAlgebra ℚ (polarization n).W) := by
  have h := congrArg Subtype.val ((latticeBasis n).sum_repr
    ⟨rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n s),
      rep_kostantForm_mem_lattice n _ (rootVector_mem_kostantForm _ _ j) _ (latticeBasis n s).2⟩)
  rw [AddSubmonoidClass.coe_finsetSum] at h
  simp only [AddSubgroupClass.coe_zsmul] at h
  exact h.symm

/-- If a represented root generator sends one lattice basis vector to a signed second one, the
corresponding column of its integral matrix is that signed coordinate vector. -/
private theorem rootGeneratorMatrix_apply_of_eq (j : Fin (n + 1) ⊕ Fin (n + 1))
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) (r : Fin (dimension n)) :
    rootGeneratorMatrix n j r a = if r = a' then (c : ℤ) else 0 := by
  have hvec :
      (⟨rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
          (latticeBasis n a),
        rep_kostantForm_mem_lattice n _ (rootVector_mem_kostantForm _ _ j) _
          (latticeBasis n a).2⟩ : (lattice n).toAddSubgroup) =
        (c : ℤ) • latticeBasis n a' := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_zsmul]
    rw [Units.smul_def] at h
    exact h
  refine (congrArg (fun y ↦ (latticeBasis n).repr y r) hvec).trans ?_
  rw [map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases hr : r = a'
  · simp only [hr, ite_true, smul_eq_mul, mul_one]
  · simp only [hr, Ne.symm hr, ite_false, smul_zero]

/-- At parameter one, a numbered simple-root point moves a coordinate vector by the signed
coordinate vector its root generator produces. -/
private theorem rootSubgroupPoints_mulVec_single_sub (j : Fin (n + 1) ⊕ Fin (n + 1))
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) :
    ((rootSubgroupPoints n j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ Pi.single a 1 -
        Pi.single a 1 =
      ((c : ℤ) : R) • Pi.single a' 1 := by
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_one_add_smul _ _ _ _ _ _ _ _
    (rootGeneratorMatrix n j) (nilpotencyClass_rep_rootGenerator_le_two n j)
    (rep_rootGenerator_latticeBasis n j)]
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, one_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    add_sub_cancel_left, Matrix.mulVec_single_one]
  funext r
  simp [rootGeneratorMatrix_apply_of_eq n j h, Pi.single_apply]

/-- The character of the spin weight torus attached to a spin-basis index. -/
noncomputable abbrev basisCharacter (a : Fin (dimension n)) :
    Multiplicative (Fin (n + 1) →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (basisWeight n a))

private theorem basisCharacter_injective : Function.Injective (basisCharacter n) := by
  intro a b h
  have hw : basisWeight n a = basisWeight n b :=
    Finsupp.equivFunOnFinite.symm.injective (Multiplicative.ofAdd.injective h)
  exact (Fintype.equivFin (Finset (Fin (n + 1)))).symm.injective
    (DynkinType.typeBSpinWeight_injective hw)

/-- **Restricting the standard carrier comodule to the spin weight torus gives the direct sum of
the distinct spin weight lines.** Corestricting along `weightTorusToBaseChangeCoordinateMap`
turns the standard comodule on `Fin (dimension n) → R` into the comodule in which the coordinate
basis vector at `a` spans the weight line of the torus character `basisCharacter n a`. -/
theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule n R
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap n R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  let _ := GeneralLinear.standardComodule R (dimension n)
  let _ := standardComodule n R
  apply Comodule.ext
  rw [Comodule.corestrict_coact,
    ← Comodule.corestrictCoact_comp (coordinateMap n R).hom.toCoalgHom
      (weightTorusToBaseChangeCoordinateMap n R).hom.toCoalgHom]
  have hcomp :
      _root_.CoalgHom.comp ((weightTorusToBaseChangeCoordinateMap n R).hom.toCoalgHom)
          ((coordinateMap n R).hom.toCoalgHom) =
        (GeneralLinear.weightTorusCoordinateBialgHom (S := R) (basisWeight n)).toCoalgHom := by
    have hb :
        (weightTorusToBaseChangeCoordinateMap n R).hom.comp (coordinateMap n R).hom =
          GeneralLinear.weightTorusCoordinateBialgHom (S := R) (basisWeight n) := by
      rw [← _root_.CommHopfAlgCat.hom_comp,
        coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
        GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
    apply DFunLike.ext _ _
    intro x
    exact DFunLike.congr_fun hb x
  rw [hcomp]
  simpa only [Comodule.corestrict_coact] using
    congrArg (fun c : Comodule R _ (Fin (dimension n) → R) ↦ c.coact)
      (GeneralLinear.corestrict_standardComodule_weightTorusCoordinateBialgHom_eq_ofWeights
        (basisWeight n))

/-! ## Simplicity over a field -/

section Simple

variable (k : Type u) [Field k]

/-- If a numbered simple root generator sends one lattice basis vector to a signed second one,
then a subcomodule containing the first coordinate vector contains the second. -/
private theorem single_mem_of_rep_rootGenerator_eq
    (N : Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k))
    (j : Fin (n + 1) ⊕ Fin (n + 1)) {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W))
    (ha : Pi.single a 1 ∈ N) : Pi.single a' 1 ∈ N := by
  have hsub := N.toSubmodule.sub_mem
    (points_mulVec_mem n k N (rootSubgroupPoints n j k (Multiplicative.ofAdd 1)) ha) ha
  rw [rootSubgroupPoints_mulVec_single_sub n k j h] at hsub
  have hc : ((c : ℤ) : k) ≠ 0 := by
    rcases Int.units_eq_one_or c with rfl | rfl <;> simp
  exact (Submodule.smul_mem_iff _ hc).1 hsub

/-- The `i`-th simple reflection on the finite-ordinal spin-basis indices. -/
private noncomputable def basisReflection (i : Fin (n + 1)) (a : Fin (dimension n)) :
    Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin (n + 1))) (DynkinType.typeBSpinReflection i (signSet n a))

private theorem signSet_basisReflection (i : Fin (n + 1)) (a : Fin (dimension n)) :
    signSet n (basisReflection n i a) = DynkinType.typeBSpinReflection i (signSet n a) := by
  simp [basisReflection, signSet]

private theorem basisReflection_involutive (i : Fin (n + 1)) :
    Function.Involutive (basisReflection n i) := by
  intro a
  simp [basisReflection, signSet]

private theorem foldl_basisReflection (l : List (Fin (n + 1))) (t : Finset (Fin (n + 1))) :
    l.foldl (fun b j ↦ basisReflection n j b) (Fintype.equivFin (Finset (Fin (n + 1))) t) =
      Fintype.equivFin (Finset (Fin (n + 1)))
        (l.foldl (fun t j ↦ DynkinType.typeBSpinReflection j t) t) := by
  induction l generalizing t with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    simp [basisReflection, signSet]

/-- Invariance under the two simple-root points makes membership of coordinate basis vectors
stable under every simple reflection. -/
private theorem single_basisReflection_mem
    (N : Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k))
    (a : Fin (dimension n)) (i : Fin (n + 1)) (ha : Pi.single a 1 ∈ N) :
    Pi.single (basisReflection n i a) 1 ∈ N := by
  rcases DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n a) i with
    hneg | hzero | hpos
  · obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inl_exteriorBasis n i _ _ hneg
      (signSet_basisReflection n i a).symm
    refine single_mem_of_rep_rootGenerator_eq n k N (.inl i) (c := c) ?_ ha
    rw [coe_latticeBasis n a, coe_latticeBasis n (basisReflection n i a)]
    exact hc
  · have hfix : basisReflection n i a = a := by
      rw [basisReflection, (DynkinType.typeBSpinReflection_eq_self_iff i _).2 hzero]
      simp [signSet]
    rwa [hfix]
  · obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inr_exteriorBasis n i _ _ hpos
      (signSet_basisReflection n i a).symm
    refine single_mem_of_rep_rootGenerator_eq n k N (.inr i) (c := c) ?_ ha
    rw [coe_latticeBasis n a, coe_latticeBasis n (basisReflection n i a)]
    exact hc

/-- **The standard comodule of the specialized type-`Bₙ₊₁` spin carrier is simple over every
field.** -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k)) :=
  Subcomodule.isSimpleOrder_of_corestrict_eq_ofWeights
    (weightTorusToBaseChangeCoordinateMap n k).hom.toCoalgHom (basisCharacter n)
    (basisCharacter_injective n) (torusCorestrict_eq_ofWeights n k)
    (basisReflection n) (basisReflection_involutive n)
    (fun N a i ↦ single_basisReflection_mem n k N a i)
    (Fintype.equivFin (Finset (Fin (n + 1))) ∅) fun a ↦ by
      obtain ⟨l, hl⟩ := DynkinType.exists_typeBSpinReflections_eq (signSet n a)
      exact ⟨l, by rw [foldl_basisReflection, hl]; simp [signSet]⟩

end Simple

end TauCeti.TypeBSpinCarrier
