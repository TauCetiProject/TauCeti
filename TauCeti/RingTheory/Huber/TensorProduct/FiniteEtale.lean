/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.FiniteAlgebra
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Finite étale completed base change

The coprojection from a complete Hausdorff Huber pair into its completed tensor product
with a finite étale pair is finite étale. This includes the natural module topology and
the integral-closure plus ring, not just finite étaleness of the underlying ring map.
Neither sheafiness nor noetherianity is required. The original base and the finite étale
factor need not be complete; both structure maps must be adic.

The proof uses the canonical finite projective comparison
`Pair.finiteAlgebra.baseChangeEquiv` and its exact transport of plus rings. Thus no
uniformisation or replacement of the specified plus ring by power-bounded elements occurs.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Lemma 7.3(ii).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371
  (2015), §8.2, Definition 8.2.16 and the following base-extension assertion.
-/

public section

open TensorProduct Algebra.TensorProduct

namespace TauCeti.Huber.Pair

variable {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T2Space C]
  [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]

private theorem isFiniteEtale_inl_finiteAlgebra [Module.Finite A B] [Algebra.Etale A B]
    [IsModuleTopology A B] (S : Pair A) (T : Pair C)
    (f : Hom S T) (hf : f.toRingHom = algebraMap A C) :
    (completedTensor.inl A T (S.finiteAlgebra B)).IsFiniteEtale := by
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let : TopologicalSpace (C ⊗[A] B) := moduleTopology C (C ⊗[A] B)
  have : IsModuleTopology C (C ⊗[A] B) := ⟨rfl⟩
  let : IsTopologicalRing (C ⊗[A] B) := IsModuleTopology.isTopologicalRing C _
  let : IsHuberRing (C ⊗[A] B) := IsHuberRing.of_isModuleTopology (A := C)
  let : Algebra C (CompletedTensor A C B) := (CompletedTensor.inl A C B).toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] CompletedTensor A C B :=
    { finiteAlgebra.baseChangeEquiv A C B with
      commutes' := fun c ↦ by
        simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply] }
  have he : IsHomeomorph e := finiteAlgebra.isHomeomorph_baseChangeEquiv A C B
  have : Module.Finite C (CompletedTensor A C B) := Module.Finite.equiv e.toLinearEquiv
  have : Algebra.Etale C (CompletedTensor A C B) := Algebra.Etale.of_equiv e
  have htop : IsModuleTopology C (CompletedTensor A C B) :=
    IsModuleTopology.iso
      { e.toLinearEquiv with
        continuous_toFun := he.continuous
        continuous_invFun := e.toEquiv.continuous_symm_iff.mpr he.isOpenMap }
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [completedTensor.toRingHom_inl, ← RingHom.algebraMap_toAlgebra (CompletedTensor.inl A C B)]
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.etale_algebraMap.mpr inferInstance
  · simpa only [_root_.toAlgebra_algebraMap] using htop
  · rw [← finiteAlgebra_plus]
    apply le_antisymm
    · rw [← finiteAlgebra.map_plus_baseChangeEquiv S T f hf]
      rintro _ ⟨x, hx, rfl⟩
      simpa [e] using (finiteAlgebra.lift
        (finiteAlgebra.algebraHom T (CompletedTensor A C B)) (by simp)
        e.toAlgHom).map_mem_plus x hx
    · intro x hx
      have hmem := (finiteAlgebra.lift (completedTensor.inl A T (S.finiteAlgebra B))
        (by simp [RingHom.algebraMap_toAlgebra]) (AlgHom.id C _)).map_mem_plus x hx
      rwa [finiteAlgebra.lift_toRingHom] at hmem

/-- **Finite étale morphisms of Huber pairs are stable under completed base change.**
The new base `C` is complete Hausdorff, and both structure maps are adic. The algebras
are arbitrary compatible presentations of the two given pair maps. -/
theorem completedTensor.isFiniteEtale_inl
    {S : Pair A} {T : Pair C} {U : Pair B}
    (f : Hom S T) (hf : f.toRingHom = algebraMap A C)
    (g : Hom S U) (hg : g.toRingHom = algebraMap A B) (h : g.IsFiniteEtale) :
    (completedTensor.inl A T U).IsFiniteEtale := by
  have : Module.Finite A B := RingHom.finite_algebraMap.mp (hg ▸ h.finite)
  have : Algebra.Etale A B := RingHom.etale_algebraMap.mp (hg ▸ h.etale)
  have htopB := h.isModuleTopology
  rw [hg, _root_.toAlgebra_algebraMap] at htopB
  have : IsModuleTopology A B := htopB
  have hplus := h.plus_eq
  rw [hg] at hplus
  have hU : U = S.finiteAlgebra B := Pair.ext (by simpa only [finiteAlgebra_plus] using hplus)
  subst U
  exact isFiniteEtale_inl_finiteAlgebra S T f hf

end TauCeti.Huber.Pair
