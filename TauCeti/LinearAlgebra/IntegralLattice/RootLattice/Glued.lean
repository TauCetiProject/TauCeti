/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum

/-!
# Gluing an orthogonal sum of ADE root lattices along glue words

Let `t : ι → DynkinType` be a finite family of valid simply-laced components, `R` the orthogonal
sum of their root lattices, and `H` a quadratically isotropic subgroup of the module of glue words
`⊕ i, (t i).glueAlphabet`.  Conway--Sloane describe an overlattice of `R` by such a subgroup,
written in the component labels.  This file transports `H` to the discriminant group of `R`
through `TauCeti.DynkinType.glueWordIsometry` and applies the isotropic gluing construction
`TauCeti.IntegralLattice.ofIsotropicSubgroup`, uniformly in the components.

The resulting lattice `TauCeti.DynkinType.gluedLattice t ht hv H hH` lives in the same rational
ambient space as `R` and carries the same form.  Its carrier is the inverse image of `H` in the
dual of `R` (`mem_gluedLattice_carrier_iff`), it contains `R` with index `|H|`, it is even and
positive definite of rank `∑ i, rank (t i)`, and it is unimodular exactly when `H` is Lagrangian,
equivalently when `|H|² = |⊕ i, (t i).glueAlphabet|`.  Gluing along the zero subgroup gives `R`
back.

The root sublattice of a glued lattice is computed from the coset minima of the glue words in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Roots`.

## Main declarations

* `TauCeti.DynkinType.gluedLattice`: the overlattice of the orthogonal sum of root lattices glued
  along an isotropic subgroup of glue words.
* `TauCeti.DynkinType.mem_gluedLattice_carrier_iff`: the carrier is the set of dual vectors whose
  glue word lies in `H`.
* `TauCeti.DynkinType.relIndex_gluedLattice`: the root lattice has index `|H|`.
* `TauCeti.DynkinType.isEven_gluedLattice`, `isPosDef_gluedLattice`, `finrank_gluedLattice`.
* `TauCeti.DynkinType.isUnimodular_gluedLattice_iff`,
  `TauCeti.DynkinType.isUnimodular_gluedLattice_iff_natCard_sq_eq`: the unimodularity criteria.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §3 and Chapter 16 §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)
  (hv : ∀ i, (t i).Valid)

/-- **The overlattice of an orthogonal sum of ADE root lattices glued along glue words.**  For a
quadratically isotropic subgroup `H` of the glue words of the components `t`, this is the even
overlattice of `⊥ i, (t i).rootLattice` cut out by the image of `H` in its discriminant group
under `TauCeti.DynkinType.glueWordIsometry`. -/
noncomputable def gluedLattice
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H) :
    IntegralLattice (∀ i, Fin (t i).rank → ℚ) :=
  (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
    (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
    (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)

variable (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
  (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)

/-- The glued lattice is the isotropic gluing of the orthogonal sum of root lattices along the
image of `H` in its discriminant group. -/
theorem gluedLattice_def :
    gluedLattice t ht hv H hH =
      (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
        (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
        (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH) :=
  (rfl)

/-- Gluing keeps the form of the orthogonal sum of root lattices. -/
@[simp]
theorem gluedLattice_form :
    (gluedLattice t ht hv H hH).form = (pi fun i ↦ (t i).rootLattice (ht i)).form :=
  ofIsotropicSubgroup_form _ _ _ _

/-- **The carrier of a glued lattice**: a vector lies in it exactly when it lies in the dual of
the orthogonal sum of root lattices and the glue word of its discriminant class lies in `H`. -/
theorem mem_gluedLattice_carrier_iff (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier,
        (glueWordIsometry t ht hv).toAddEquiv.symm (Submodule.Quotient.mk ⟨x, hx⟩) ∈ H := by
  refine (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) x).trans
    ((mem_intermediateCarrierOfDiscriminantSubgroup_iff _ _ x).trans ?_)
  exact exists_congr fun _ ↦ AddSubgroup.mem_map_equiv

/-- The orthogonal sum of root lattices is a sublattice of every lattice glued from it. -/
theorem carrier_le_gluedLattice_carrier :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier ≤ (gluedLattice t ht hv H hH).carrier :=
  fun _ hx ↦ (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) _).mpr
    (((pi fun i ↦ (t i).rootLattice (ht i)).intermediateCarrierOfDiscriminantSubgroup _).2.1 hx)

/-- **The orthogonal sum of root lattices has index `|H|` in the lattice glued along `H`.** -/
theorem relIndex_gluedLattice :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier.toAddSubgroup.relIndex
        (gluedLattice t ht hv H hH).carrier.toAddSubgroup = Nat.card H := by
  have hcarrier : (gluedLattice t ht hv H hH).carrier = _ := ofIsotropicSubgroup_carrier _ _ _ _
  rw [hcarrier, ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup]
  exact AddSubgroup.card_map_of_injective (glueWordIsometry t ht hv).toAddEquiv.injective

/-- A glued lattice is nondegenerate. -/
instance isNondegenerate_gluedLattice : (gluedLattice t ht hv H hH).IsNondegenerate :=
  instIsNondegenerateOfIsotropicSubgroup _ _ _ _

/-- **A glued lattice is even.** -/
theorem isEven_gluedLattice : (gluedLattice t ht hv H hH).IsEven :=
  isEven_ofIsotropicSubgroup _ _ _ _

/-- **A glued lattice is positive definite.** -/
theorem isPosDef_gluedLattice : (gluedLattice t ht hv H hH).IsPosDef :=
  (isPosDef_ofIsotropicSubgroup_iff _ _ _ _).mpr (isPosDef_pi_rootLattice t ht)

/-- **A glued lattice has rank `∑ i, rank (t i)`**, the rank of the orthogonal sum of the root
lattices. -/
@[simp]
theorem finrank_gluedLattice :
    Module.finrank ℤ (gluedLattice t ht hv H hH) = ∑ i, (t i).rank := by
  rw [finrank_carrier, ← finrank_carrier (pi fun i ↦ (t i).rootLattice (ht i)),
    finrank_pi_rootLattice]

/-- **A glued lattice is unimodular exactly when its glue subgroup is Lagrangian.** -/
theorem isUnimodular_gluedLattice_iff :
    (gluedLattice t ht hv H hH).IsUnimodular ↔
      (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsLagrangian H := by
  refine (isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _ _).trans
    (Iff.trans ?_ ((glueWordIsometry t ht hv).isLagrangian_map_iff _ H))
  exact ⟨fun h ↦ (FiniteQuadraticModule.isLagrangian_def _ _).mpr
      ⟨((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH, h⟩,
    fun h ↦ h.toFiniteBilinearModule⟩

/-- **A glued lattice is unimodular exactly when `|H|²` is the number of glue words**, the
discriminant of the orthogonal sum of root lattices. -/
theorem isUnimodular_gluedLattice_iff_natCard_sq_eq :
    (gluedLattice t ht hv H hH).IsUnimodular ↔
      Nat.card H ^ 2 = Nat.card (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) := by
  rw [isUnimodular_gluedLattice_iff]
  exact ⟨fun h ↦ FiniteBilinearModule.IsLagrangian.card_sq _ h.toFiniteBilinearModule
      (isNondegenerate_pi_glueAlphabet t ht hv),
    hH.isLagrangian_of_card_sq_eq _ (isNondegenerate_pi_glueAlphabet t ht hv)⟩

/-- Gluing along the zero subgroup of glue words returns the orthogonal sum of root lattices. -/
@[simp]
theorem gluedLattice_bot :
    gluedLattice t ht hv ⊥ (FiniteQuadraticModule.isIsotropic_bot _) =
      pi fun i ↦ (t i).rootLattice (ht i) := by
  -- The isotropy proof depends on the subgroup, so rewrite `H.map _ = ⊥` by generalizing it.
  have key : ∀ K hK, K = ⊥ →
      (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht) K hK =
        pi fun i ↦ (t i).rootLattice (ht i) := by
    rintro _ _ rfl
    exact ofIsotropicSubgroup_bot _ _
  exact key _ _ (AddSubgroup.map_bot _)

end TauCeti.DynkinType
