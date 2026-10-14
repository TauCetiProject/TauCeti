/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion

/-!
# Descent of closed immersions along open target covers

A morphism of pre-adic spaces is a closed immersion if its restrictions over an open cover
of the target are closed immersions. The local quotient models on the cover give quotient
models on the original target: an open of a restricted space is identified with its open image,
and the same identification applies to its inverse image in the source.

This allows closed subspaces specified on affinoid charts to be recognized globally. No
finiteness condition on the cover, or Tate, noetherianity, or sheafiness assumption on the
ambient spaces, is needed; the local models already include closed ideals and sheafy quotients.
The result is descent along a cover. Stability under restricting a closed immersion to an
arbitrary target open, for sheafy targets, is
`TauCeti.PreAdicSpace.IsClosedImmersion.restrictPreimage`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 7.38 and §8.3.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

universe u

variable {X Y : PreAdicSpace.{u}}

/-- Closed immersions descend along any open cover of the target. In particular, closed
quotient models on a covering family of affinoid charts suffice to give a closed immersion
of the original pre-adic spaces. -/
theorem IsClosedImmersion.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y)
    (hV : iSup V = ⊤) (hf : ∀ i, IsClosedImmersion (f.restrictPreimage (V i))) :
    IsClosedImmersion f := by
  rw [isClosedImmersion_iff]
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ y : y ∈ iSup V)
  obtain ⟨W, hy, A, _, _, _, _, S, P, hP, J, hJ, hs, eW, eU, hfac⟩ :=
    (isClosedImmersion_iff _).mp (hf i) ⟨y, hi⟩
  let V' : Opens Y := (V i).isOpenEmbedding.isOpenMap.functor.obj W
  let U := (Opens.map f.base).obj (V i)
  let U' := (Opens.map (f.restrictPreimage (V i)).base).obj W
  -- Both open subspaces of `X` have precisely the points mapping into the image of `W`.
  have hr : Set.range ((X.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      X.ofRestrict U.isOpenEmbedding).base =
      Set.range (X.ofRestrict ((Opens.map f.base).obj V').isOpenEmbedding).base := by
    ext x
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      have hzW : (⟨f.base z.1, z.2⟩ : Y.restrict (V i).isOpenEmbedding) ∈ W := by
        rw [← Hom.restrictPreimage_base_apply]
        exact Opens.mem_map.mp hz
      exact ⟨⟨z.1, ⟨⟨f.base z.1, z.2⟩, hzW, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨x, z, hz, hzx⟩, rfl⟩
      have hxV : f.base x ∈ V i := hzx ▸ z.2
      let x' : X.restrict U.isOpenEmbedding := ⟨x, Opens.mem_map.mpr hxV⟩
      refine ⟨⟨x', ?_⟩, rfl⟩
      have heq : (f.restrictPreimage (V i)).base x' = z :=
        (f.restrictPreimage_base_apply (V i) x').trans (Subtype.ext hzx.symm)
      exact Opens.mem_map.mpr (heq.symm ▸ hz)
  let e := IsOpenImmersion.isoOfRangeEq
    ((X.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫ X.ofRestrict U.isOpenEmbedding)
    (X.ofRestrict ((Opens.map f.base).obj V').isOpenEmbedding) hr
  refine ⟨V', ⟨⟨y, hi⟩, hy, rfl⟩, A, inferInstance, inferInstance, inferInstance, inferInstance,
    S, P, hP, J, hJ, hs, (restrictRestrictIso Y (V i).isOpenEmbedding W).symm ≪≫ eW,
    e.symm ≪≫ eU, ?_⟩
  -- Transport the local quotient square through the two identifications of open subspaces.
  -- Compose the identities as terms: rewriting inside the restricted objects would require
  -- identifying the topology of a restriction with its underlying subtype topology.
  have hsource := congrArg (fun g ↦ g ≫ f)
    (IsOpenImmersion.isoOfRangeEq_inv_comp _ _ hr)
  have hsquare := congrArg (fun g ↦ g ≫ Y.ofRestrict (V i).isOpenEmbedding) hfac
  have htarget := congrArg
    (fun g ↦ eU.hom ≫
      ValuationSpectrum.presentationLimitPreAdicSpaceQuotientComap S P hP J hs ≫ eW.inv ≫ g)
    (restrictRestrictIso_hom_ofRestrict Y (V i).isOpenEmbedding W)
  simp only [Category.assoc] at hsource htarget
  simp only [Category.assoc, Hom.restrictPreimage_ofRestrict] at hsquare
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    hsource.symm.trans (congrArg (fun g ↦ e.inv ≫ g) (hsquare.trans htarget.symm))

end TauCeti.PreAdicSpace
