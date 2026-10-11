/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointConjugation
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Weight spaces of a closed subgroup in a representation

Let `H` be the coordinate Hopf algebra of an affine group `G`, let the Hopf ideal `I` cut out a
closed subgroup `N`, and let `V` be a representation of `G`. A character of `N` is a group-like
element `χ` of `H ⧸ I`, and the `χ`-weight space of `V` consists of the vectors on which `N` acts
through `χ`: those whose coaction, restricted to `N`, is `v ↦ v ⊗ χ`. Characters and weight spaces
are scheme-theoretic, so nonreduced subgroups such as `μ_p` are allowed. Matrix coefficients
of a weight vector are right semi-invariants with the same character.

A rational point `g` of `G` normalizing `N` restricts to an automorphism of `N`, whose coordinate
map is a bialgebra endomorphism of `H ⧸ I`. Acting by `g` carries the `χ`-weight space into the
weight space of the character `n ↦ χ (g⁻¹ n g)`. Every rational point normalizes a normal
subgroup, so the sum of the weight spaces of a normal subgroup is stable under all rational
points. Over an algebraically closed field and for reduced `H` of finite type, rational points
detect subcomodules, so this sum is a subrepresentation of `V`; over a field the sum is direct.

This is the first step of the classical proof that a normal subgroup is the kernel of a
representation: by Chevalley's theorem `N` is the stabilizer of a line, which lies in one weight
space of `N`, and `G` acts on the block-diagonal endomorphisms of the sum of the weight spaces with
kernel `N`.

## Main declarations

* `TauCeti.HopfIdeal.weightSpace`: the weight space of a character of the closed subgroup.
* `TauCeti.HopfIdeal.basePointsRepresentation_mem_weightSpace`: normalizing points permute the
  weight spaces.
* `TauCeti.HopfIdeal.IsNormal.map_basePointsRepresentation_weightSpace`: a rational point maps
  each weight space of a normal subgroup onto the weight space of the conjugate character.
* `TauCeti.HopfIdeal.IsNormal.iSupWeightSpaceSubcomodule`: the sum of the weight spaces of a
  normal subgroup, as a subrepresentation.
* `TauCeti.HopfIdeal.iSupIndep_weightSpace`: over a field the weight spaces are independent.
* `TauCeti.HopfIdeal.weightSpace_subcomodule`: weight spaces restrict to subrepresentations
  when the ambient and subgroup coordinate algebras are flat over the base.
* `TauCeti.HopfIdeal.IsNormal.iSup_weightSpace_iSupWeightSpaceSubcomodule_eq_top`: the
  weight-sum subrepresentation is spanned by its own subgroup weight spaces.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* A. Borel, *Linear Algebraic Groups*, §5.5.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v w

section Weights

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
variable (I : HopfIdeal R H) (V : Type w) [AddCommMonoid V] [Module R V] [Comodule R H V]

/-- The weight space of a character `χ` of the closed subgroup `N` cut out by `I` in a
representation `V` of the ambient group: the vectors on which `N` acts through `χ`. In
coordinates, `χ` is a group-like element of `H ⧸ I`, and the coaction of `V`, restricted to `N`,
sends a weight vector `v` to `v ⊗ χ`. -/
noncomputable def weightSpace (χ : GroupLike R (H ⧸ I.toIdeal)) : Submodule R V :=
  letI : Comodule R (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (Bialgebra.Quotient.mkBialgHom I.toIdeal).toCoalgHom
  _root_.GroupLike.weightSpace (M := V) χ

variable {I V}

/-- Membership in a weight space of a closed subgroup, in terms of the coaction of the ambient
group: restricting the coefficients to the subgroup gives `v ⊗ χ`. -/
@[simp]
theorem mem_weightSpace {χ : GroupLike R (H ⧸ I.toIdeal)} {v : V} :
    v ∈ I.weightSpace V χ ↔
      TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
          (Comodule.coact (R := R) (C := H) (M := V) v) =
        v ⊗ₜ[R] χ.val :=
  letI : Comodule R (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (Bialgebra.Quotient.mkBialgHom I.toIdeal).toCoalgHom
  _root_.GroupLike.mem_weightSpace

/-- A matrix coefficient of a subgroup weight vector is a right semi-invariant, with the
same subgroup character. -/
theorem map_comul_matrixCoefficient_of_mem_weightSpace
    (I : HopfIdeal R H) (χ : GroupLike R (H ⧸ I.toIdeal))
    {m : V} (hm : m ∈ I.weightSpace V χ) (φ : Module.Dual R V) :
    TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
        (Coalgebra.comul (R := R) (Comodule.matrixCoefficient (C := H) φ m)) =
      Comodule.matrixCoefficient (C := H) φ m ⊗ₜ[R] χ.val := by
  rw [Comodule.comul_matrixCoefficient]
  have h := congrArg
    (TensorProduct.map (Comodule.matrixCoefficientLinear (C := H) φ) LinearMap.id)
    (mem_weightSpace.mp hm)
  simpa only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id,
    TensorProduct.map_tmul, LinearMap.id_apply, Comodule.matrixCoefficientLinear_apply] using h

/-- A weight vector of a closed subgroup is detected by the universal point of the subgroup, the
quotient map `H → H ⧸ I`, even over a nonreduced base ring. -/
theorem mem_weightSpace_iff_endOfPoint (χ : GroupLike R (H ⧸ I.toIdeal)) (v : V) :
    v ∈ I.weightSpace V χ ↔
      Comodule.endOfPoint V (Ideal.Quotient.mkₐ R I.toIdeal) (1 ⊗ₜ[R] v) = χ.val ⊗ₜ[R] v := by
  rw [mem_weightSpace, Comodule.endOfPoint_tmul, one_smul, LinearMap.lTensor_def]
  constructor
  · intro h
    rw [h, TensorProduct.comm_tmul]
  · intro h
    apply (TensorProduct.comm R V (H ⧸ I.toIdeal)).injective
    simpa only [TensorProduct.comm_tmul] using h

/-- A point of the closed subgroup acts on the `χ`-weight space by its value on `χ`. -/
theorem endOfPoint_comp_mkₐ_tmul_of_mem_weightSpace {A : Type*} [CommSemiring A] [Algebra R A]
    (f : H ⧸ I.toIdeal →ₐ[R] A) (a : A) {χ : GroupLike R (H ⧸ I.toIdeal)} {v : V}
    (hv : v ∈ I.weightSpace V χ) :
    Comodule.endOfPoint V (f.comp (Ideal.Quotient.mkₐ R I.toIdeal)) (a ⊗ₜ[R] v) =
      (a * f χ.val) ⊗ₜ[R] v := by
  have h := mem_weightSpace.mp hv
  rw [← LinearMap.lTensor_def] at h
  rw [Comodule.endOfPoint_tmul, AlgHom.comp_toLinearMap, LinearMap.lTensor_comp,
    LinearMap.comp_apply, h]
  simp [TensorProduct.smul_tmul']

/-- **Normalizing points permute weight spaces.** If a rational point `g` normalizes the closed
subgroup `N` cut out by `I`, then acting by `g` carries the `χ`-weight space of `N` into the weight
space of the conjugate character `n ↦ χ (g⁻¹ n g)`. -/
theorem basePointsRepresentation_mem_weightSpace (g : WithConv (H →ₐ[R] R))
    (hg : I ≤ I.conjugate g⁻¹) {χ : GroupLike R (H ⧸ I.toIdeal)} {v : V}
    (hv : v ∈ I.weightSpace V χ) :
    Comodule.basePointsRepresentation (H := H) V g v ∈
      I.weightSpace V (GroupLike.map (I.quotientPointConjugation g⁻¹ hg) χ) := by
  rw [mem_weightSpace_iff_endOfPoint, GroupLike.val_map]
  apply Comodule.endOfPoint_one_tmul_basePointsRepresentation_of_conj
  have hσ : (Ideal.Quotient.mkₐ R I.toIdeal).comp (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (I.quotientPointConjugation g⁻¹ hg : H ⧸ I.toIdeal →ₐ[R] H ⧸ I.toIdeal).comp
        (Ideal.Quotient.mkₐ R I.toIdeal) := by
    ext x
    simp
  rw [hσ, endOfPoint_comp_mkₐ_tmul_of_mem_weightSpace _ 1 hv, one_mul, BialgHom.coe_toAlgHom]

/-- The weight spaces of a normal closed subgroup are permuted by every rational point, so their
sum is stable under the action of rational points. -/
theorem IsNormal.basePointsRepresentation_mem_iSup_weightSpace (hI : I.IsNormal)
    (g : WithConv (H →ₐ[R] R)) {v : V} (hv : v ∈ ⨆ χ, I.weightSpace V χ) :
    Comodule.basePointsRepresentation (H := H) V g v ∈ ⨆ χ, I.weightSpace V χ := by
  have hle : (⨆ χ, I.weightSpace V χ) ≤
      (⨆ χ, I.weightSpace V χ).comap (Comodule.basePointsRepresentation (H := H) V g) :=
    iSup_le fun _ _ hw ↦ Submodule.mem_iSup_of_mem _
      (basePointsRepresentation_mem_weightSpace g (hI.le_conjugate g⁻¹) hw)
  exact hle hv

/-- **Rational points permute the weight spaces of a normal subgroup.** A rational point `g` maps
the `χ`-weight space of a normal closed subgroup `N` onto the weight space of the conjugate
character `n ↦ χ (g⁻¹ n g)`. -/
theorem IsNormal.map_basePointsRepresentation_weightSpace (hI : I.IsNormal)
    (g : WithConv (H →ₐ[R] R)) (χ : GroupLike R (H ⧸ I.toIdeal)) :
    (I.weightSpace V χ).map (Comodule.basePointsRepresentation (H := H) V g) =
      I.weightSpace V
        (GroupLike.map (I.quotientPointConjugation g⁻¹ (hI.le_conjugate g⁻¹)) χ) := by
  refine le_antisymm ?_ fun v hv ↦ ⟨Comodule.basePointsRepresentation (H := H) V g⁻¹ v, ?_,
    Representation.self_inv_apply _ g v⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact basePointsRepresentation_mem_weightSpace g _ hv
  · have hcomp (q : H ⧸ I.toIdeal) :
        I.quotientPointConjugation g⁻¹⁻¹ (hI.le_conjugate _)
          (I.quotientPointConjugation g⁻¹ (hI.le_conjugate _) q) = q := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [quotientPointConjugation_mk, quotientPointConjugation_mk, ← AlgHom.comp_apply,
        ← HopfAlgebra.pointConjugationAlgHom_mul, mul_inv_cancel,
        HopfAlgebra.pointConjugationAlgHom_one, AlgHom.id_apply]
    have hχ : GroupLike.map (I.quotientPointConjugation g⁻¹⁻¹ (hI.le_conjugate _))
        (GroupLike.map (I.quotientPointConjugation g⁻¹ (hI.le_conjugate _)) χ) = χ :=
      _root_.GroupLike.val_injective (by simp only [GroupLike.val_map, hcomp])
    have hv' := basePointsRepresentation_mem_weightSpace g⁻¹ (hI.le_conjugate _) hv
    rw [hχ] at hv'
    exact hv'

/-- The weight space of a closed subgroup in a subrepresentation is the preimage of its
weight space in the ambient representation, when the coordinate algebras of the group and
subgroup are flat over the base. -/
@[simp]
theorem weightSpace_subcomodule [Module.Flat R H] (I : HopfIdeal R H)
    [Module.Flat R (H ⧸ I.toIdeal)] (W : Subcomodule R H V)
    (χ : GroupLike R (H ⧸ I.toIdeal)) :
    I.weightSpace W χ = (I.weightSpace V χ).comap (SMulMemClass.subtype W) := by
  have hinj : Function.Injective ((SMulMemClass.subtype W).baseChange (H ⧸ I.toIdeal)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  ext w
  rw [Submodule.mem_comap, mem_weightSpace_iff_endOfPoint,
    mem_weightSpace_iff_endOfPoint, ← hinj.eq_iff]
  have h := LinearMap.congr_fun
    (Comodule.baseChange_comp_endOfPoint W.subtype (Ideal.Quotient.mkₐ R I.toIdeal))
    (1 ⊗ₜ[R] w)
  simp only [LinearMap.comp_apply, Subcomodule.subtype_toLinearMap,
    LinearMap.baseChange_tmul, SMulMemClass.subtype_apply] at h ⊢
  rw [h]

end Weights

section Field

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (I : HopfIdeal k H) (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

/-- Over a field, the weight spaces of a closed subgroup belonging to distinct characters are
independent. -/
theorem iSupIndep_weightSpace : iSupIndep (I.weightSpace V) :=
  letI : Comodule k (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (Bialgebra.Quotient.mkBialgHom I.toIdeal).toCoalgHom
  Comodule.iSupIndep_groupLikeWeightSpace

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]

/-- **The weight spaces of a normal subgroup span a subrepresentation.** For a normal closed
subgroup `N` of a reduced affine group of finite type over an algebraically closed field, the sum
of the weight spaces of `N` in a representation `V` is a subcomodule of `V`. -/
noncomputable def IsNormal.iSupWeightSpaceSubcomodule {I : HopfIdeal k H} (hI : I.IsNormal) :
    Subcomodule k H V :=
  Subcomodule.ofEndOfPointStable (K := k) (⨆ χ, I.weightSpace V χ) fun g m hm ↦ by
    have h := hI.basePointsRepresentation_mem_iSup_weightSpace (toConv g) hm
    rw [Comodule.basePointsRepresentation_apply, ofConv_toConv] at h
    rw [← (TensorProduct.lid k V).symm_apply_apply (Comodule.endOfPoint V g (1 ⊗ₜ[k] m)),
      TensorProduct.lid_symm_apply]
    exact Submodule.tmul_mem_baseChange_of_mem _ h

/-- The subrepresentation spanned by the weight spaces of a normal subgroup has the expected
underlying subspace. -/
@[simp]
theorem IsNormal.iSupWeightSpaceSubcomodule_toSubmodule {I : HopfIdeal k H} (hI : I.IsNormal) :
    (hI.iSupWeightSpaceSubcomodule V).toSubmodule = ⨆ χ, I.weightSpace V χ :=
  Subcomodule.ofEndOfPointStable_toSubmodule _ _

/-- The weight-sum subrepresentation is spanned by its own subgroup weight spaces. -/
-- Simplify the sum before restricting its individual weight spaces to the subrepresentation.
@[simp↓]
theorem IsNormal.iSup_weightSpace_iSupWeightSpaceSubcomodule_eq_top {I : HopfIdeal k H}
    (hI : I.IsNormal) :
    (⨆ χ, I.weightSpace (hI.iSupWeightSpaceSubcomodule V) χ) = ⊤ := by
  let W := hI.iSupWeightSpaceSubcomodule V
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  have hrange : LinearMap.range (SMulMemClass.subtype W) =
      ⨆ χ ∈ (Set.univ : Set (GroupLike k (H ⧸ I.toIdeal))), I.weightSpace V χ := by
    simp only [iSup_univ]
    exact (Submodule.range_subtype W.toSubmodule).trans
      (hI.iSupWeightSpaceSubcomodule_toSubmodule V)
  have htop := Submodule.biSup_comap_eq_top_of_range_eq_biSup
    (τ₁₂ := RingHom.id k) Set.univ ⟨1, Set.mem_univ _⟩
    (I.weightSpace V) (SMulMemClass.subtype W) hrange
  simpa only [iSup_univ, ← weightSpace_subcomodule] using htop

end Field

end TauCeti.HopfIdeal
