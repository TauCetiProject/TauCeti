/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2.Basic
public import TauCeti.RingTheory.PiTensorProduct.Surjective

/-!
# Trivial F₂ coefficients in the tensor-induction Mackey formula

The coefficient identification for tensor induction multiplies the tensor factors. The Mackey
comparison regroups those factors by double cosets, so normalization after that comparison is
normalization in each orbit followed by multiplication over the orbits. The theorem
`smoothTensorInducedTrivialF2Iso_mackey` establishes this as an equality of linear maps, not just
on pure tensors. It is the coefficient compatibility needed to read the double-coset formula for
the Evens norm in canonical trivial coefficients.

The subgroup receiving the restriction need not be open or have finite index. Only the subgroup
from which tensor induction is taken must be open and have finite index. We state the square on
the underlying modules of the smooth Mackey comparison, retaining the original coefficient
carrier in every factor; restriction and conjugation change its action, not its carrier.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §6, Proposition 2.
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal)

/-- The finite coset set indexing the original tensor induction. -/
noncomputable local instance mackeyTrivialF2QuotientFintype : Fintype (G ⧸ U) :=
  U.fintypeQuotientOfFiniteIndex
/-- The finite set of orbits of `V` on the original coset set. -/
noncomputable local instance mackeyTrivialF2DoubleCosetFintype :
    Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G)) := Fintype.ofFinite _
/-- The finite coset set indexing one orbitwise tensor induction. -/
noncomputable local instance mackeyTrivialF2OrbitFintype
    (D : DoubleCoset.Quotient (V : Set G) (U : Set G)) :
    Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) :=
  ((mackeySubgroup (r D) U V).subgroupOf V).fintypeQuotientOfFiniteIndex

/-- On orbitwise pure tensors, the Mackey comparison followed by coefficient normalization is
multiplication of all the orbitwise coefficient values. The transversal correction disappears
because the coefficients have trivial action. -/
theorem smoothTensorInducedTrivialF2Iso_mackey_tprod :
    letI : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
    ∀ m : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (mackeySubgroup (r D) U V).subgroupOf V → (DiscreteRep.trivialF2 U).V,
    trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
      (Subgroup.tensorInducedMackey U V r hr t (DiscreteRep.trivialF2 U).ρ s
        (PiTensorProduct.tprod ℤ fun D ↦ PiTensorProduct.tprod ℤ (m D)))) =
      ∏ D, ∏ q, trivialF2Equiv U (m D q) := by
  let : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
  intro m
  have hρ : ∀ (g : U) x, (DiscreteRep.trivialF2 U).ρ g x = x :=
    trivialF2_ρ_apply_apply U
  rw [Subgroup.tensorInducedMackey_tprod]
  simp only [hρ]
  exact (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G U hU s _).trans
    (((mackeyQuotientEquiv U V r hr).symm.prod_comp
      (fun p ↦ trivialF2Equiv U (m p.1 p.2))).trans (Fintype.prod_sigma _))

/-- Coefficient normalization commutes with the Mackey comparison on the underlying modules of
smooth tensor induction. On the right, first multiply within each double-coset orbit, then
multiply over the orbits. Both sides are linear maps on arbitrary tensors. -/
theorem smoothTensorInducedTrivialF2Iso_mackey :
    letI : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
    letI : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
    ((trivialF2Equiv G).toIntLinearEquiv
      (modM := (trivialF2 G).hV2)).toLinearMap ∘ₗ
        (smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom.toLinearMap ∘ₗ
          (Subgroup.tensorInducedMackey U V r hr t
            (DiscreteRep.trivialF2 U).ρ s).toLinearEquiv.toLinearMap =
      (PiTensorProduct.constantAlgEquivOfSurjective
          (ZMod.ringHom_surjective (algebraMap ℤ (ZMod 2)))).toLinearMap ∘ₗ
        PiTensorProduct.map (fun D ↦
          (PiTensorProduct.constantAlgEquivOfSurjective
              (ZMod.ringHom_surjective (algebraMap ℤ (ZMod 2)))).toLinearMap ∘ₗ
            PiTensorProduct.map (fun _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V ↦
              ((trivialF2Equiv U).toIntLinearEquiv
                (modM := (DiscreteRep.trivialF2 U).module)).toLinearMap)) := by
  let : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
  let : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
  apply PiTensorProduct.ext_sigma_tprod
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod,
    AlgEquiv.toLinearMap_apply, PiTensorProduct.constantAlgEquivOfSurjective_tprod]
  exact smoothTensorInducedTrivialF2Iso_mackey_tprod G U V hU r hr t s m

end TauCeti
