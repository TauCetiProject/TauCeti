/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum

/-!
# Overlattices of ADE root lattices glued along glue words

Let `t : ι → DynkinType` be a finite family of valid simply-laced components, `R` the orthogonal
sum of their root lattices, and `H` a quadratically isotropic subgroup of the module of glue
words `⊕ i, (t i).glueAlphabet`.  Transporting `H` to the discriminant group of `R` through
`TauCeti.DynkinType.glueWordIsometry` and applying the isotropic gluing construction
`TauCeti.IntegralLattice.ofIsotropicSubgroup` gives the even overlattice

`R_H = {x ∈ Rᵛ | the glue word of x + R lies in H}`

(`TauCeti.DynkinType.gluedRootLattice`).  This is the construction of a lattice from a reducible
root system and a glue code in Conway--Sloane, Chapter 4 §3 and Chapter 16 §1, where the rootful
rank-`24` even unimodular lattices are described by their root systems and glue codes in this
way.

This file develops the properties of `R_H` that hold uniformly in the components and the glue
code: its carrier formula in glue-word coordinates, the inclusion `R ≤ R_H` with index `|H|`,
evenness, positive-definiteness, rank `∑ i, rank (t i)`, the identification of its discriminant
quadratic module with `H⊥ / H` in glue-word coordinates, and the unimodularity criterion: `R_H`
is unimodular exactly when `H` is Lagrangian, equivalently when `|H|²` is the number of glue
words.  The root sublattice of `R_H` is computed from the glue minima in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Roots`.

## Main declarations

* `TauCeti.DynkinType.gluedRootLattice`: the overlattice `R_H` of the orthogonal sum of root
  lattices glued along a quadratically isotropic subgroup `H` of glue words.
* `TauCeti.DynkinType.mem_gluedRootLattice_carrier_iff`: a vector lies in `R_H` exactly when it
  is a dual vector of `R` whose glue word lies in `H`.
* `TauCeti.DynkinType.relIndex_gluedRootLattice`: `R` has index `|H|` in `R_H`.
* `TauCeti.DynkinType.isEven_gluedRootLattice`, `TauCeti.DynkinType.isPosDef_gluedRootLattice`,
  `TauCeti.DynkinType.finrank_gluedRootLattice`: `R_H` is even, positive definite, and of rank
  `∑ i, rank (t i)`.
* `TauCeti.DynkinType.gluedRootLatticeDiscriminantIsometry`: the isometry
  `A_(R_H) ≅ H⊥ / H` of finite quadratic modules, in glue-word coordinates.
* `TauCeti.DynkinType.isUnimodular_gluedRootLattice_iff_isLagrangian`,
  `TauCeti.DynkinType.isUnimodular_gluedRootLattice_iff_natCard_sq`: `R_H` is unimodular exactly
  when `H` is Lagrangian, equivalently when `|H|²` is the order of the module of glue words.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §3, and Chapter 16, §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)
  (hv : ∀ i, (t i).Valid)
  (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
  (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)

/-- **The overlattice of an orthogonal sum of ADE root lattices glued along glue words.**  For
a finite family of valid simply-laced components and a quadratically isotropic subgroup `H` of
the module of glue words, this is the even overlattice `R_H` of the orthogonal sum `R` of the
root lattices whose classes in the discriminant group of `R` are the glue words in `H`. -/
noncomputable def gluedRootLattice : IntegralLattice (∀ i, Fin (t i).rank → ℚ) :=
  (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
    (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
    (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)

/-- The glued root lattice is the isotropic gluing of the orthogonal sum of root lattices along
the image of `H` under the glue-word isometry. -/
theorem gluedRootLattice_def :
    gluedRootLattice t ht hv H hH =
      (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
        (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
        (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH) := (rfl)

/-! The basic properties below apply the general `ofIsotropicSubgroup` API to the definition of
`gluedRootLattice`, which unfolds in this file. -/

/-- Gluing keeps the form of the orthogonal sum of root lattices. -/
@[simp]
theorem gluedRootLattice_form :
    (gluedRootLattice t ht hv H hH).form = (pi fun i ↦ (t i).rootLattice (ht i)).form :=
  ofIsotropicSubgroup_form _ _ _ _

/-- **The carrier of a glued root lattice**: a vector lies in `R_H` exactly when it is a dual
vector of the orthogonal sum `R` of root lattices whose discriminant class has glue word in
`H`. -/
theorem mem_gluedRootLattice_carrier_iff (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedRootLattice t ht hv H hH).carrier ↔
      ∃ hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier,
        (glueWordIsometry t ht hv).symm (Submodule.Quotient.mk ⟨x, hx⟩) ∈ H :=
  (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) x).trans
    ((mem_intermediateCarrierOfDiscriminantSubgroup_iff _ _ x).trans
      (exists_congr fun _ ↦ AddSubgroup.mem_map_equiv))

/-- The orthogonal sum of root lattices is a sublattice of every lattice glued from it. -/
theorem carrier_le_gluedRootLattice_carrier :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier ≤ (gluedRootLattice t ht hv H hH).carrier :=
  fun _ hx ↦ (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) _).mpr
    (((pi fun i ↦ (t i).rootLattice (ht i)).intermediateCarrierOfDiscriminantSubgroup _).2.1 hx)

/-- **The orthogonal sum of root lattices has index `|H|` in the lattice glued along `H`.** -/
theorem relIndex_gluedRootLattice :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier.toAddSubgroup.relIndex
        (gluedRootLattice t ht hv H hH).carrier.toAddSubgroup = Nat.card H := by
  have hcarrier : (gluedRootLattice t ht hv H hH).carrier = _ :=
    ofIsotropicSubgroup_carrier _ _ _ _
  rw [hcarrier, ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup]
  exact AddSubgroup.card_map_of_injective (glueWordIsometry t ht hv).toAddEquiv.injective

/-- A glued root lattice is nondegenerate. -/
instance instIsNondegenerateGluedRootLattice :
    (gluedRootLattice t ht hv H hH).IsNondegenerate :=
  instIsNondegenerateOfIsotropicSubgroup _ _ _ _

/-- **A glued root lattice is even.** -/
theorem isEven_gluedRootLattice : (gluedRootLattice t ht hv H hH).IsEven :=
  isEven_ofIsotropicSubgroup _ _ _ _

/-- **A glued root lattice is positive definite.** -/
theorem isPosDef_gluedRootLattice : (gluedRootLattice t ht hv H hH).IsPosDef :=
  (isPosDef_ofIsotropicSubgroup_iff _ _ _ _).mpr (isPosDef_pi_rootLattice t ht)

/-- **The rank of a glued root lattice is the sum of the ranks of the components.** -/
@[simp]
theorem finrank_gluedRootLattice :
    Module.finrank ℤ (gluedRootLattice t ht hv H hH) = ∑ i, (t i).rank := by
  rw [finrank_carrier, ← finrank_carrier (pi fun i ↦ (t i).rootLattice (ht i)),
    finrank_pi_rootLattice]

/-! ## The discriminant form and unimodularity -/

/-- The glued root lattice is the lattice carried by the even intermediate carrier attached to
the image of `H`. -/
private theorem gluedRootLattice_eq_toIntegralLattice :
    gluedRootLattice t ht hv H hH =
      (((pi fun i ↦ (t i).rootLattice (ht i)).isEven_intermediateCarrierOfDiscriminantSubgroup_iff
        (isEven_pi_rootLattice t ht)
        (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)).mpr
        (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr
          hH)).isIntegral.toIntegralLattice :=
  IntegralLattice.ext
    ((ofIsotropicSubgroup_carrier _ _ _ _).trans
      (IntermediateCarrier.IsIntegral.toIntegralLattice_carrier _).symm)
    ((ofIsotropicSubgroup_form _ _ _ _).trans
      (IntermediateCarrier.IsIntegral.toIntegralLattice_form _).symm)

/-- Every dual vector of a glued root lattice is a dual vector of the orthogonal sum of root
lattices. -/
theorem dualCarrier_gluedRootLattice_le :
    (gluedRootLattice t ht hv H hH).dualCarrier ≤
      (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
  rw [gluedRootLattice_eq_toIntegralLattice]
  exact IntermediateCarrier.IsIntegral.dualCarrier_le _

/-- The class of a dual vector of a glued root lattice in the discriminant group of the
orthogonal sum of root lattices does not depend on the presentation of the glued lattice. -/
private theorem mk_dualCarrierEquiv_ofEq_gluedRootLattice
    (y : (gluedRootLattice t ht hv H hH).dualCarrier) :
    (Submodule.Quotient.mk ⟨_, IntermediateCarrier.IsIntegral.dualCarrier_le _
        ((Isometry.ofEq (gluedRootLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv
          y).2⟩ : (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      Submodule.Quotient.mk ⟨y, dualCarrier_gluedRootLattice_le t ht hv H hH y.2⟩ :=
  congrArg Submodule.Quotient.mk (Subtype.ext (by
    rw [Isometry.coe_dualCarrierEquiv_apply, Isometry.ofEq_apply]))

/-- **The discriminant form of a glued root lattice in glue-word coordinates**: the isometry
`A_(R_H) ≅ H⊥ / H` of finite quadratic modules, where `H⊥` is the orthogonal complement of `H`
in the module of glue words. -/
noncomputable def gluedRootLatticeDiscriminantIsometry :
    FiniteQuadraticModule.Isometry
      ((gluedRootLattice t ht hv H hH).discriminantQuadraticModule
        (isEven_gluedRootLattice t ht hv H hH))
      ((FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).orthogonalQuotient H hH) :=
  ((Isometry.discriminantQuadraticIsometry
      (Isometry.ofEq (gluedRootLattice_eq_toIntegralLattice t ht hv H hH))
      (isEven_gluedRootLattice t ht hv H hH)).trans
    ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantOrthogonalQuotientIsometryOfSubgroup
      (isEven_pi_rootLattice t ht)
      (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH))).trans
    ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm

/-- **The glue word of a dual vector of a glued root lattice is orthogonal to the glue code.**
A dual vector `y` of `R_H` is a dual vector of `R`, and the glue word of its class lies in the
orthogonal complement `H⊥` for the polar pairing on glue words. -/
theorem glueWordIsometry_symm_mk_mem_orthogonalComplement
    (y : (gluedRootLattice t ht hv H hH).dualCarrier) :
    (glueWordIsometry t ht hv).symm
        (Submodule.Quotient.mk ⟨y, dualCarrier_gluedRootLattice_le t ht hv H hH y.2⟩) ∈
      (FiniteQuadraticModule.pi fun i ↦
        (t i).glueAlphabet (ht i)).toFiniteBilinearModule.orthogonalComplement H := by
  have hmem := IntermediateCarrier.IsIntegral.dualClassHom_mem_orthogonalComplement _
    ((Isometry.ofEq (gluedRootLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv y)
  rw [discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    IntermediateCarrier.IsIntegral.dualClassHom_apply] at hmem
  -- The pairing of the glue word with `w ∈ H` is the pairing of the class of `y` with the class
  -- of `w`, which vanishes because the class of `y` is orthogonal to the image of `H`.
  refine (FiniteBilinearModule.mem_orthogonalComplement_iff _ _ _).mpr fun w hw ↦ ?_
  have hw' := (FiniteBilinearModule.mem_orthogonalComplement_iff _ _ _).mp hmem
    (glueWordIsometry t ht hv w) ⟨w, hw, rfl⟩
  refine ((glueWordIsometry t ht hv).toHom.map_pairing _ _).symm.trans (Eq.trans ?_ hw')
  rw [FiniteQuadraticModule.Isometry.toHom_apply, FiniteQuadraticModule.Isometry.toHom_apply]
  exact congrArg (fun a ↦ (pi fun i ↦ (t i).rootLattice (ht i)).discriminantBilinearModule.pairing
    a (glueWordIsometry t ht hv w)) (((glueWordIsometry t ht hv).apply_symm_apply _).trans
      (mk_dualCarrierEquiv_ofEq_gluedRootLattice t ht hv H hH y).symm)

/-- The discriminant isometry of a glued root lattice sends the class of a dual vector `y` to
the class in `H⊥ / H` of the glue word of `y`. -/
theorem gluedRootLatticeDiscriminantIsometry_mk
    (y : (gluedRootLattice t ht hv H hH).dualCarrier) :
    gluedRootLatticeDiscriminantIsometry t ht hv H hH (Submodule.Quotient.mk y) =
      (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).orthogonalQuotientMk H hH
        ⟨_, glueWordIsometry_symm_mk_mem_orthogonalComplement t ht hv H hH y⟩ := by
  have h2 := Isometry.discriminantQuadraticIsometry_mk
    (Isometry.ofEq (gluedRootLattice_eq_toIntegralLattice t ht hv H hH))
    (isEven_gluedRootLattice t ht hv H hH) y
  have h3 := discriminantOrthogonalQuotientIsometryOfSubgroup_mk _ (isEven_pi_rootLattice t ht)
    (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)
    ((Isometry.ofEq (gluedRootLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv y)
  -- Evaluate the three factors of the composite one at a time.
  refine (congrArg (fun z ↦ ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm
    ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantOrthogonalQuotientIsometryOfSubgroup
      (isEven_pi_rootLattice t ht)
      (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH) z)) h2).trans ?_
  refine (congrArg ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm h3).trans ?_
  refine (FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv_symm_orthogonalQuotientMk
    _ _ _ _).trans ?_
  exact congrArg _ (Subtype.ext (congrArg (glueWordIsometry t ht hv).symm
    ((IntermediateCarrier.IsIntegral.dualClassHom_apply _ _).trans
      (mk_dualCarrierEquiv_ofEq_gluedRootLattice t ht hv H hH y))))

/-- **A glued root lattice is unimodular exactly when its glue code is Lagrangian.** -/
theorem isUnimodular_gluedRootLattice_iff_isLagrangian :
    (gluedRootLattice t ht hv H hH).IsUnimodular ↔
      (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsLagrangian H :=
  (isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _ _).trans <|
    (and_iff_right (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)).symm.trans <|
      (FiniteQuadraticModule.isLagrangian_def _ _).symm.trans
        (FiniteQuadraticModule.Isometry.isLagrangian_map_iff _ (glueWordIsometry t ht hv) H)

/-- **The unimodularity criterion for a glued root lattice**: `R_H` is unimodular exactly when
`|H|²` is the number of glue words, which is the discriminant of `R`. -/
theorem isUnimodular_gluedRootLattice_iff_natCard_sq :
    (gluedRootLattice t ht hv H hH).IsUnimodular ↔
      Nat.card H ^ 2 = Nat.card (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) := by
  rw [isUnimodular_gluedRootLattice_iff_isLagrangian]
  exact ⟨fun h ↦ h.toFiniteBilinearModule.card_sq _ (isNondegenerate_pi_glueAlphabet t ht hv),
    hH.isLagrangian_of_card_sq_eq _ (isNondegenerate_pi_glueAlphabet t ht hv)⟩

end TauCeti.DynkinType
