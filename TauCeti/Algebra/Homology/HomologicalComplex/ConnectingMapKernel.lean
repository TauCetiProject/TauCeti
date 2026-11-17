/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# Lifting the connecting map of a short exact sequence of complexes along a kernel

Let `S : A ⟶ X ⟶ Q` be a short exact sequence of complexes in an abelian category and `b : X ⟶ Y` a
quasi-isomorphism such that the composite `A ⟶ X ⟶ Y` is an epimorphism, with kernel `K` presented
by a second short exact sequence `T : K ⟶ A ⟶ Y`. Then the connecting map `Hᵢ(Q) ⟶ Hⱼ(A)` of `S`
lifts along `K ⟶ A` to an isomorphism

`Hᵢ(Q) ≅ Hⱼ(K)`

(`CategoryTheory.ShortComplex.ShortExact.liftδIso`,
`CategoryTheory.ShortComplex.ShortExact.liftδIso_hom_comp_homologyMap`). It is the connecting map of
the short exact sequence `K ⟶ ker b ⟶ Q`
(`TauCeti.kernelCokernelCompSequence_shortExact_of_mono_of_epi`), whose middle term is acyclic
because `b` is an epimorphic quasi-isomorphism.

This computes the relative homology of a pair of spaces whose ambient space is weakly equivalent
to a space onto which the subspace maps surjectively on chains, such as a covering space: the
relative homology is then the shifted homology of the kernel of that surjection.
-/

public section

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex Limits

variable {S T : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (hT : T.ShortExact)
  (e : T.X₂ ≅ S.X₁) (b : S.X₂ ⟶ T.X₃) (hb : e.hom ≫ S.f ≫ b = T.g)

/-- The sequence `T.X₁ ⟶ kernel b ⟶ S.X₃`, through which the connecting map of `S` factors. -/
private noncomputable abbrev kernelShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (kernel.lift b (T.f ≫ e.hom ≫ S.f)
      (by rw [Category.assoc, Category.assoc, hb, T.zero])) (kernel.ι b ≫ S.g) (by simp)

include hS hT hb in
private lemma kernelShortComplex_shortExact : (kernelShortComplex e b hb).ShortExact := by
  have := hS.mono_f
  have : Epi (S.f ≫ b) := by
    have : Epi (e.hom ≫ S.f ≫ b) := hb ▸ hT.epi_g
    exact epi_of_epi e.hom _
  -- `T.X₁` is a kernel of `S.f ≫ b` and `S.X₃` a cokernel of `S.f`, so the sequence is the
  -- short exact sequence `kernel (S.f ≫ b) ⟶ kernel b ⟶ cokernel S.f`.
  have hT' : (ShortComplex.mk (T.f ≫ e.hom) (S.f ≫ b)
      (by rw [Category.assoc, hb, T.zero])).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := T) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp [hb])) hT
  let e₁ := (kernelIsKernel (S.f ≫ b)).conePointUniqueUpToIso hT'.fIsKernel
  let e₃ := (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel
  have h₁ : e₁.hom ≫ T.f ≫ e.hom = kernel.ι (S.f ≫ b) := by
    simpa using (kernelIsKernel (S.f ≫ b)).conePointUniqueUpToIso_hom_comp hT'.fIsKernel
      WalkingParallelPair.zero
  have h₃ : cokernel.π S.f ≫ e₃.hom = S.g := by
    simpa using (cokernelIsCokernel S.f).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel
      WalkingParallelPair.one
  refine ShortComplex.shortExact_of_iso ?_
    (TauCeti.kernelCokernelCompSequence_shortExact_of_mono_of_epi S.f b)
  refine ShortComplex.isoMk e₁ (Iso.refl _) e₃ ?_ ?_
  · rw [← cancel_mono (kernel.ι b)]
    simp [reassoc_of% h₁]
  · simp [h₃]

variable (hq : _root_.QuasiIso b)

include hT hb hq in
private lemma acyclic_kernel : (kernel b).Acyclic := by
  have : Epi b := by
    have : Epi (e.hom ≫ S.f ≫ b) := hb ▸ hT.epi_g
    have : Epi (S.f ≫ b) := epi_of_epi e.hom _
    exact epi_of_epi S.f b
  exact (TauCeti.kernelSequence_shortExact b).acyclic_X₁ hq

/-- **The connecting map lifted along a kernel.** Let `S : A ⟶ X ⟶ Q` and `T : K ⟶ A' ⟶ Y` be
short exact sequences of complexes, with an isomorphism `e : A' ≅ A`, and let `b : X ⟶ Y` be a
quasi-isomorphism with `e ≫ S.f ≫ b = T.g`; so `K` is the kernel of the composite `A ⟶ X ⟶ Y`.
Then `Hᵢ(Q) ≅ Hⱼ(K)` whenever `c.Rel i j`. Composed with the map `Hⱼ(K) ⟶ Hⱼ(A)`, it is the
connecting map of `S` (`CategoryTheory.ShortComplex.ShortExact.liftδIso_hom_comp_homologyMap`).

For instance, if `S` is the short exact sequence of singular chains of a pair `(D, D₀)` and `b` is
induced by a weak homotopy equivalence `D ⟶ B`, then the relative homology of the pair is the
shifted homology of the kernel of the chain map induced by `D₀ ⟶ B`. -/
noncomputable def liftδIso (i j : ι) (hij : c.Rel i j) : S.X₃.homology i ≅ T.X₁.homology j :=
  (kernelShortComplex_shortExact hS hT e b hb).δIso i j hij
    ((acyclic_kernel hT e b hb hq i).isZero_homology)
    ((acyclic_kernel hT e b hb hq j).isZero_homology)

/-- The isomorphism `liftδIso`, followed by the map `Hⱼ(K) ⟶ Hⱼ(A)`, is the connecting map of
`S`. -/
@[reassoc]
lemma liftδIso_hom_comp_homologyMap (i j : ι) (hij : c.Rel i j) :
    (hS.liftδIso hT e b hb hq i j hij).hom ≫ HomologicalComplex.homologyMap (T.f ≫ e.hom) j =
      hS.δ i j hij := by
  have h := HomologySequence.δ_naturality
    (S₁ := kernelShortComplex e b hb) (S₂ := S)
    { τ₁ := T.f ≫ e.hom
      τ₂ := kernel.ι b
      τ₃ := 𝟙 _ } (kernelShortComplex_shortExact hS hT e b hb) hS i j hij
  dsimp only at h
  rwa [HomologicalComplex.homologyMap_id, Category.id_comp] at h

end CategoryTheory.ShortComplex.ShortExact
