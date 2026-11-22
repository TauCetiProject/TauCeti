/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Basic

/-!
# Continuous differentials of open quotients

When `B → C` is an open quotient map between complete Hausdorff nonarchimedean rings with
`A → B` adic, the base-change map `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` in the conormal sequence is
surjective without any finite-type or noetherian hypotheses
(`TauCeti.Huber.ContinuousKaehlerDifferential.mapBaseChange_surjective_of_isOpenQuotientMap`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(ii).
-/

public section

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

/-- **Surjectivity in the conormal sequence for open quotients** (Huber 1996,
Proposition 1.6.3(ii)): when `B → C` is an open quotient map between complete Hausdorff
nonarchimedean rings with `A → B` adic, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective, with no
finite-type or noetherian hypotheses. -/
theorem mapBaseChange_surjective_of_isOpenQuotientMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [TopologicalSpace A] [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [CompleteSpace B] [T0Space B] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C] [IsAdicHom (algebraMap A B)]
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) :=
      haveI : IsHuberRing B :=
        ⟨⟨(inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition.choose_spec.choose⟩⟩
      IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
    Function.Surjective (mapBaseChange A B C hBC.continuous) := by
  have : IsAdicHom (algebraMap A C) :=
    haveI : IsHuberRing B :=
      ⟨⟨(inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition.choose_spec.choose⟩⟩
    IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
  have hBC_comp : (algebraMap B C).comp (algebraMap A B) = algebraMap A C := by
    ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm
  let F := CompletedTensor.map (RingHom.id A) (algebraMap B C) (algebraMap B C)
    hBC_comp hBC_comp hBC.continuous hBC.continuous
  have hF := (CompletedTensor.isOpenQuotientMap_map hBC_comp hBC_comp hBC hBC).surjective
  intro ω
  obtain ⟨⟨y, hy⟩, rfl⟩ := fromIdeal_surjective A C ω
  obtain ⟨x, hxF⟩ := hF y
  let b := mulRingHom A B x
  have hb : algebraMap B C b = 0 := by
    rw [← CompletedTensor.mulRingHom_map (RingHom.id A) (algebraMap B C) hBC_comp hBC.continuous x,
      show F x = y from hxF, mem_ideal_iff.mp hy]
  refine ⟨1 ⊗ₜ[B] fromIdeal A B ⟨x - inl A B B b, mem_ideal_iff.mpr (by simp [b])⟩, ?_⟩
  simp only [mapBaseChange_tmul, one_smul, mapSemilinear_fromIdeal]
  congr 1; ext; change F (x - inl A B B b) = y; simp [F, hxF, hb]

end TauCeti.Huber.ContinuousKaehlerDifferential
