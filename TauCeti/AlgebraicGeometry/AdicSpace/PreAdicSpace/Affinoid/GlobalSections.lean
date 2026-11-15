/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Plus
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Sheaf

/-!
# Global sections determine maps into affinoid spectra

For an arbitrary pre-adic space `X`, a morphism `X → Spa(A, A⁺)` induces a continuous ring map
`A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)`. Its composite with the germ at a point recovers the
valuation of the image point, without choosing a representative value group.

If the structure presheaf of `X` is a sheaf, this global-sections map determines the entire
morphism, not just its map on points. On each rational open of the target, the universal property
of completed rational localisation determines the map on sections from its values on `A`.
The sheaf property of the source then gives equality on all opens. In particular this applies
to every adic source, without affinoidness or quasi-compactness assumptions.

This proves the injectivity direction of the correspondence between morphisms into affinoids
and continuous, integral-section-preserving maps on global sections. It does not construct a
morphism from such a ring map.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  513–551, Proposition 2.1(ii).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
  {X : PreAdicSpace.{u}}

/-- The global-sections map of a morphism into an affinoid spectrum is continuous, for an
arbitrary pre-adic source. -/
theorem continuous_presentationLimitAppTop
    (f : X ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP) :
    Continuous (presentationLimitAppTop P Aplus hAplus hP f) := by
  rw [presentationLimitAppTop_def]
  exact ((presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv ≫
    TopCommRingCat.isCompleteSeparated.ι.map
      (PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map f).op)).2

/-- Pullback on global sections carries the plus ring of the target pair into the integral
sections of the source. No sheaf condition on either space is required. -/
theorem presentationLimitAppTop_mem_plus
    (f : X ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP) {a : A} (ha : a ∈ Aplus) :
    presentationLimitAppTop P Aplus hAplus hP f a ∈ X.plusSubring ⊤ := by
  refine PreAdicSpace.mem_plusSubring_iff.mpr fun x _ ↦ ?_
  have hx := ((mem_spa_iff Aplus (f.base x : spa Aplus).1).mp (f.base x : spa Aplus).2).2 a ha
  rw [base_eq_comap_presentationLimitAppTop, comap_vle] at hx
  -- The source section ring is also the section ring of its ring-valued presheaf, but `rw`
  -- does not unfold the forgetful functor enough to identify the carrier of the inner comap.
  erw [comap_vle, map_one, map_one] at hx
  exact hx

/-- Equal coefficient pullbacks give equal components on the whole target spectrum. -/
private theorem Γ_map_eq_of_presentationLimitAppTop_eq
    {f g : X ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP}
    (h : presentationLimitAppTop P Aplus hAplus hP f =
      presentationLimitAppTop P Aplus hAplus hP g) :
    PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map f).op =
      PresheafedSpace.Γ.map (PreAdicSpace.forgetToPresheafedSpace.map g).op := by
  rw [presentationLimitAppTop_def, presentationLimitAppTop_def] at h
  exact TopCommRingCat.isCompleteSeparated.ι.map_injective <|
    (cancel_epi (presentationLimitPreAdicSpaceTopIso P Aplus hAplus hP).inv).mp <|
      (forget₂ _root_.TopCommRingCat CommRingCat).map_injective <| CommRingCat.hom_ext h

/-- Naturality determines the coefficient pullback on a rational open from that on the whole
spectrum. -/
private theorem toPresentationLimit_comp_app_spaBasicOpen {C : TopCat.{u}}
    (b : C ⟶ TopCat.of ↥(spa Aplus)) (F : C.Presheaf CompleteSeparatedTopCommRingCat.{u})
    (c : presentationLimitPresheaf P Aplus ⟶
      (TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat b).obj F)
    (i : PresentationIndex (P := P) Aplus ⊤) :
    toPresentationLimit Aplus _ ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus i.pres.num i.pres.den))).symm ≫
        c.app (Opposite.op (spaBasicOpen Aplus i.pres.num i.pres.den)) =
      toPresentationLimit Aplus ⊤ ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫
        c.app (Opposite.op ⊤) ≫
        ((TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat b).obj F).map
          (homOfLE le_top).op := by
  rw [← c.naturality, presentationLimitPresheaf_map]
  simp

/-- A morphism from a sheafy pre-adic space into an affinoid spectrum is determined by its
pullback on global sections. In particular the source may be any adic space. -/
theorem presentationLimitAppTop_injective (hX : PreAdicSpace.isSheafy X) :
    Function.Injective (presentationLimitAppTop P Aplus hAplus hP (X := X)) := by
  intro f g h
  have hbase : f.base = g.base := by
    ext x
    exact Subtype.ext (by
      rw [base_eq_comap_presentationLimitAppTop, base_eq_comap_presentationLimitAppTop, h])
  have htop := Γ_map_eq_of_presentationLimitAppTop_eq P Aplus hAplus hP h
  rw [PresheafedSpace.Γ_map_op, PresheafedSpace.Γ_map_op, PreAdicSpace.forgetToPresheafedSpace_map,
    PreAdicSpace.forgetToPresheafedSpace_map] at htop
  ext1
  clear h
  generalize f.toHom = F at hbase htop ⊢
  generalize g.toHom = G at hbase htop ⊢
  rcases F with ⟨fb, fc⟩
  rcases G with ⟨gb, gc⟩
  dsimp only at hbase htop
  subst hbase
  congr 1
  -- Equality on the rational basis suffices because the pushforward of the source presheaf is
  -- a sheaf. Completed rational localisation supplies uniqueness on each basis member.
  refine TopCat.Sheaf.hom_ext (X := TopCat.of ↥(spa Aplus)) _
    ⟨_, TopCat.Sheaf.pushforward_sheaf_of_sheaf fb hX⟩ (isBasis_range_spaBasicOpen P Aplus)
    fun ⟨p, hp⟩ ↦ ?_
  let i : PresentationIndex (P := P) Aplus ⊤ := ⟨p, hp, le_top⟩
  refine (cancel_epi (eqToHom (presentationLimitPresheaf_obj P Aplus
    (Opposite.op (spaBasicOpen Aplus p.num p.den))).symm)).mp
      (presentationLimit_spaBasicOpen_hom_ext Aplus hAplus p hp ?_)
  exact (toPresentationLimit_comp_app_spaBasicOpen P Aplus fb _ fc i).trans
    (Eq.trans (congrArg (fun k ↦ toPresentationLimit Aplus ⊤ ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op ⊤)).symm ≫ k ≫
        ((TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat fb).obj
          X.toPresheafedSpace.presheaf).map (homOfLE le_top).op) htop)
      (toPresentationLimit_comp_app_spaBasicOpen P Aplus fb _ gc i).symm)

end TauCeti.ValuationSpectrum
