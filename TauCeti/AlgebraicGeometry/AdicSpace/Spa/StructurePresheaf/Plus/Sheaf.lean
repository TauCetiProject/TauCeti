/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Plus.Basic
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf condition for integral sections

The plus presheaf on `Spa(A, A⁺)` consists of sections whose germ is integral at every point.
The condition can be checked on any open cover: germs of a glued section are germs of its local
restrictions. Consequently, if the structure presheaf is a sheaf, so is the plus
presheaf. This supplies the gluing of plus subrings used when affinoid charts are compared in
the construction of adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

namespace TauCeti.ValuationSpectrum

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : Huber.PairOfDefinition A} {Aplus : Subring A}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → Huber.IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- Integrality of a section is local on the open set: if all restrictions to an open
cover are integral, then so is the section. -/
theorem mem_presentationLimitPlusSubring_of_forall_restrict {ι : Type*}
    (U : ι → Opens ↥(spa Aplus))
    (f : (presentationLimitPresheafInCommRingCat P Aplus).obj (op (iSup U)))
    (hf : ∀ i, (presentationLimitPresheafInCommRingCat P Aplus).map
      (Opens.leSupr U i).op f ∈ presentationLimitPlusSubring hAplus hP (U i)) :
    f ∈ presentationLimitPlusSubring hAplus hP (iSup U) := by
  rw [mem_presentationLimitPlusSubring_iff]
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have hi := (mem_presentationLimitPlusSubring_iff hAplus hP).mp (hf i) x hxi
  rw [← (presentationLimitPresheafInCommRingCat P Aplus).germ_res_apply
    (Opens.leSupr U i) x hxi f]
  exact hi

/-- If the structure presheaf of `Spa(A,A⁺)` is a sheaf of commutative rings, then its integral
sections form a sheaf of commutative rings as well. -/
theorem isSheaf_presentationLimitPlusPresheaf_of_isSheaf
    (hF : (presentationLimitPresheafInCommRingCat P Aplus).IsSheaf) :
    (presentationLimitPlusPresheaf hAplus hP).IsSheaf := by
  let F := presentationLimitPresheafInCommRingCat P Aplus
  let G := presentationLimitPlusPresheaf hAplus hP
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing G).2
  intro ι U sf hc
  let e (W : Opens ↥(spa Aplus)) :
      G.obj (op W) ≃ presentationLimitPlusSubring hAplus hP W :=
    ((forget CommRingCat).mapIso
      (eqToIso (presentationLimitPlusPresheaf_obj hAplus hP (op W)))).toEquiv
  let sec (W : Opens ↥(spa Aplus)) (t : G.obj (op W)) :
      presentationLimitPlusSubring hAplus hP W := e W t
  have sec_map {W W' : Opens ↥(spa Aplus)} (i : W' ⟶ W)
      (t : G.obj (op W)) :
      (sec W' (G.map i.op t)).1 = F.map i.op (sec W t).1 := by
    have h := congrArg (fun f ↦ f t)
      (presentationLimitPlusPresheaf_map hAplus hP i.op)
    exact congrArg Subtype.val h
  have sec_injective (W : Opens ↥(spa Aplus)) : Function.Injective (sec W) := by
    exact (e W).injective
  let sfF (i : ι) : F.obj (op (U i)) := (sec (U i) (sf i)).1
  have hcF : F.IsCompatible U sfF := by
    intro i j
    rw [← sec_map, ← sec_map]
    exact congrArg (fun t ↦ (sec (U i ⊓ U j) t).1) (hc i j)
  obtain ⟨s, hs, hu⟩ := hF.isSheafUniqueGluing U sfF hcF
  have hsplus : s ∈ presentationLimitPlusSubring hAplus hP (iSup U) := by
    apply mem_presentationLimitPlusSubring_of_forall_restrict hAplus hP U s
    intro i
    -- The goal uses the local name `F`; expose the underlying presheaf map
    -- for the membership lemma.
    change F.map (Opens.leSupr U i).op s ∈ _
    rw [hs i]
    exact (sec (U i) (sf i)).2
  let t : G.obj (op (iSup U)) := (e (iSup U)).symm ⟨s, hsplus⟩
  have htval : (sec (iSup U) t).1 = s := by
    simp only [sec, t, Equiv.apply_symm_apply]
  refine ⟨t, ?_, ?_⟩
  · intro i
    apply sec_injective
    apply Subtype.ext
    -- Unfold `sfF` only to expose the ambient section used by `sec_map`.
    change (sec (U i) (G.map (Opens.leSupr U i).op t)).1 = sfF i
    rw [sec_map]
    rw [htval]
    exact hs i
  · intro t' ht
    apply sec_injective
    apply Subtype.ext
    rw [htval]
    apply hu
    intro i
    have h := congrArg (fun z ↦ (sec (U i) z).1) (ht i)
    rw [sec_map] at h
    exact h

/-- When the structure presheaf of `Spa(A,A⁺)` is a sheaf of complete separated rings, its
integral sections form a sheaf of rings as well. -/
theorem isSheaf_presentationLimitPlusPresheaf
    (hFtop : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    (presentationLimitPlusPresheaf hAplus hP).IsSheaf := by
  have hF : (presentationLimitPresheafInCommRingCat P Aplus).IsSheaf := by
    rw [presentationLimitPresheafInCommRingCat_def]
    exact Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology _)
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι)
      (forget₂ TopCommRingCat CommRingCat)
      (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology _)
        (presentationLimitPresheaf P Aplus) TopCommRingCat.isCompleteSeparated.ι hFtop)
  exact isSheaf_presentationLimitPlusPresheaf_of_isSheaf hAplus hP hF

end TauCeti.ValuationSpectrum

end
