/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.ArrowExtension.Basic

/-!
# Classification of extensions by arrow families

Every short exact sequence of quiver representations is isomorphic, with its end terms
fixed, to an extension given by upper triangular arrow matrices. Two arrow families
give equivalent extensions precisely when their difference is in the range of the Hom
differential. Thus the cokernel of that differential parametrizes extensions with fixed
end terms, rather than just detecting whether an extension splits.

These results work over any field and require neither finiteness nor acyclicity of the
quiver. Equivalence here fixes both end terms; an isomorphism of middle representations
alone does not suffice.

## References

H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1,
for extensions described by arrow maps modulo changes of vertex splittings.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- Every morphism of arrow extensions fixing both end terms has an upper triangular
coordinate form with identity diagonal. -/
theorem exists_homVertex_of_arrowExtension_hom_fixing_ends (c c' : HomArrow M N)
    (e : arrowExtension M N c ⟶ arrowExtension M N c')
    (hinl : arrowExtensionInl M N c ≫ e = arrowExtensionInl M N c')
    (hsnd : e ≫ arrowExtensionSnd M N c' = arrowExtensionSnd M N c) :
    ∃ h : HomVertex M N, ∀ (i : Q) (x : vertexSpace k Q N i × vertexSpace k Q M i),
      (e.app ((Paths.of Q).obj i)).hom x = (x.1 + h i x.2, x.2) := by
  let eₗ (i : Q) : (vertexSpace k Q N i × vertexSpace k Q M i) →ₗ[k]
      (vertexSpace k Q N i × vertexSpace k Q M i) :=
    (e.app ((Paths.of Q).obj i)).hom
  let h : HomVertex M N := fun i ↦
    (LinearMap.fst k _ _).comp ((eₗ i).comp (LinearMap.inr k _ _))
  refine ⟨h, ?_⟩
  intro i x
  have hf (z : vertexSpace k Q N i) :
      eₗ i (z, 0) = (z, (0 : vertexSpace k Q M i)) := by
    have hv := congrArg (fun f ↦ (f.app ((Paths.of Q).obj i)).hom z) hinl
    -- Retype the composite to apply the inclusion's coordinate API.
    change eₗ i (((arrowExtensionInl M N c).app ((Paths.of Q).obj i)).hom z) =
      ((arrowExtensionInl M N c').app ((Paths.of Q).obj i)).hom z at hv
    simpa only [arrowExtensionInl_app_apply] using hv
  have hg : (eₗ i x).2 = x.2 := by
    have hv := congrArg (fun f ↦ (f.app ((Paths.of Q).obj i)).hom x) hsnd
    -- Retype the composite to apply the projection's coordinate API.
    change ((arrowExtensionSnd M N c').app ((Paths.of Q).obj i)).hom (eₗ i x) =
      ((arrowExtensionSnd M N c).app ((Paths.of Q).obj i)).hom x at hv
    rw [arrowExtensionSnd_app_apply, arrowExtensionSnd_app_apply] at hv
    exact hv
  have hadd := (eₗ i).map_add (x.1, 0) (0, x.2)
  simp only [Prod.mk_add_mk, add_zero, zero_add, hf] at hadd
  -- Retype the component as the linear map used in the decomposition.
  change eₗ i x = (x.1 + h i x.2, x.2)
  apply Prod.ext
  · simpa only [Prod.fst_add, h, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.inr_apply] using congrArg Prod.fst hadd
  · exact hg

/-- Two arrow extensions are equivalent with fixed end terms if and only if their
arrow families have the same class in the Hom cokernel. -/
@[simp]
theorem exists_arrowExtension_hom_fixing_ends_iff (c c' : HomArrow M N) :
    (∃ e : arrowExtension M N c ⟶ arrowExtension M N c',
      arrowExtensionInl M N c ≫ e = arrowExtensionInl M N c' ∧
        e ≫ arrowExtensionSnd M N c' = arrowExtensionSnd M N c) ↔
      (Submodule.Quotient.mk c : HomArrow M N ⧸ (homDifferential M N).range) =
        Submodule.Quotient.mk c' := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨e, hinl, hsnd⟩
    obtain ⟨h, he⟩ := exists_homVertex_of_arrowExtension_hom_fixing_ends M N c c'
      e hinl hsnd
    refine ⟨h, ?_⟩
    ext i j a x
    have hn := congrArg (fun f ↦ f.hom ((0 : vertexSpace k Q N i), x))
      (e.naturality ((Paths.of Q).map a))
    -- Naturality is stated on path objects; retype it between the vertex products.
    change (e.app ((Paths.of Q).obj j)).hom
        ((arrowExtension M N c).map a.toPath ((0 : vertexSpace k Q N i), x)) =
      (arrowExtension M N c').map a.toPath
        ((e.app ((Paths.of Q).obj i)).hom ((0 : vertexSpace k Q N i), x)) at hn
    -- `erw` sees the exposed product vertex spaces across the path-object retyping.
    erw [he i ((0 : vertexSpace k Q N i), x)] at hn
    simp only [arrowExtension_map_toPath] at hn
    erw [he] at hn
    have hx := congrArg Prod.fst hn
    simp only [map_zero, zero_add] at hx
    simp only [homDifferential_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.sub_apply]
    apply (sub_eq_sub_iff_add_eq_add).mpr
    exact hx.symm
  · rintro ⟨h, hh⟩
    exact ⟨arrowExtensionHom M N c c' h hh,
      arrowExtensionInl_arrowExtensionHom M N c c' h hh,
      arrowExtensionHom_arrowExtensionSnd M N c c' h hh⟩

variable {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)}
variable (sp : ∀ i : Q,
  (S.map ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i))).Splitting)

/-- The vertex decompositions assemble into a presentation of the extension. -/
noncomputable def vertexSplittingHom :
    arrowExtension S.X₃ S.X₁ (vertexSplittingArrow sp) ⟶ S.X₂ :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    ((homVertex S.X₁ S.X₂ S.f i).coprod (vertexSplittingSection sp i))) (by
    intro i j a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hn : homVertex S.X₁ S.X₂ S.f j (mapₗ k Q S.X₁ a.toPath x.1) =
        mapₗ k Q S.X₂ a.toPath (homVertex S.X₁ S.X₂ S.f i x.1) :=
      homVertex_naturality _ _ _ i j a x.1
    -- Retype the path objects as vertices before applying the arrow-action API.
    change vertexSpace k Q S.X₁ i × vertexSpace k Q S.X₃ i at x
    change homVertex S.X₁ S.X₂ S.f j
        ((arrowExtension S.X₃ S.X₁ (vertexSplittingArrow sp)).map a.toPath x).1 +
        vertexSplittingSection sp j
          ((arrowExtension S.X₃ S.X₁ (vertexSplittingArrow sp)).map a.toPath x).2 =
      mapₗ k Q S.X₂ a.toPath
        (homVertex S.X₁ S.X₂ S.f i x.1 + vertexSplittingSection sp i x.2)
    simp only [arrowExtension_map_toPath, map_add, hn]
    rw [add_assoc, vertexSplittingArrow_defect])

/-- The presentation morphism is the sum of the inclusion and the chosen vertex section. -/
@[simp]
theorem vertexSplittingHom_app_apply (i : Q)
    (x : vertexSpace k Q S.X₁ i × vertexSpace k Q S.X₃ i) :
    ((vertexSplittingHom sp).app ((Paths.of Q).obj i)).hom x =
      homVertex S.X₁ S.X₂ S.f i x.1 + vertexSplittingSection sp i x.2 := (rfl)

/-- The presentation morphism fixes the inclusion of the subrepresentation. -/
@[reassoc (attr := simp)]
theorem arrowExtensionInl_vertexSplittingHom :
    arrowExtensionInl S.X₃ S.X₁ (vertexSplittingArrow sp) ≫ vertexSplittingHom sp = S.f := by
  ext i x
  -- Retype the path vertex and composite to apply the component API.
  change Q at i
  change vertexSpace k Q S.X₁ i at x
  change ((vertexSplittingHom sp).app ((Paths.of Q).obj i)).hom
      (((arrowExtensionInl S.X₃ S.X₁ (vertexSplittingArrow sp)).app
        ((Paths.of Q).obj i)).hom x) = (S.f.app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionInl_app_apply, vertexSplittingHom_app_apply,
    ← homVertex_apply]
  simp only [map_zero, add_zero]
  rfl

/-- The presentation morphism fixes the projection onto the quotient representation. -/
@[reassoc (attr := simp)]
theorem vertexSplittingHom_comp_g :
    vertexSplittingHom sp ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ (vertexSplittingArrow sp) := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  -- Retype the composite to use the presentation's vertex-coordinate formula.
  change Q at i
  change vertexSpace k Q S.X₁ i × vertexSpace k Q S.X₃ i at x
  change (S.g.app ((Paths.of Q).obj i)).hom
      (((vertexSplittingHom sp).app ((Paths.of Q).obj i)).hom x) =
    ((arrowExtensionSnd S.X₃ S.X₁ (vertexSplittingArrow sp)).app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionSnd_app_apply]
  -- `erw` sees the product vertex spaces across the path-object retyping.
  erw [← homVertex_apply]
  rw [vertexSplittingHom_app_apply, map_add, vertexSplittingSection_comp_g]
  have hzero : homVertex S.X₂ S.X₃ S.g i (homVertex S.X₁ S.X₂ S.f i x.1) = 0 := by
    erw [homVertex_apply, homVertex_apply]
    exact congrArg (fun p ↦ (p.app ((Paths.of Q).obj i)).hom x.1) S.zero
  rw [hzero, zero_add]

/-- Every short exact sequence has an upper triangular arrow-matrix presentation,
with the subrepresentation and quotient fixed. -/
theorem exists_arrowExtension_iso_fixing_ends (hS : S.ShortExact) :
    ∃ (c : HomArrow S.X₃ S.X₁) (e : arrowExtension S.X₃ S.X₁ c ≅ S.X₂),
      arrowExtensionInl S.X₃ S.X₁ c ≫ e.hom = S.f ∧
        e.hom ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c := by
  let sp := vertexSplitting hS
  have : IsIso (vertexSplittingHom sp) := isIso_of_arrowExtension_fixing_ends hS
    (vertexSplittingArrow sp) (vertexSplittingHom sp)
    (arrowExtensionInl_vertexSplittingHom sp) (vertexSplittingHom_comp_g sp)
  exact ⟨vertexSplittingArrow sp, asIso (vertexSplittingHom sp),
    arrowExtensionInl_vertexSplittingHom sp, vertexSplittingHom_comp_g sp⟩

/-- Two presentations of the same extension fixing its end terms determine the same
class in the Hom cokernel. -/
theorem quotientMk_eq_of_arrowExtension_iso_fixing_ends {c c' : HomArrow S.X₃ S.X₁}
    (e : arrowExtension S.X₃ S.X₁ c ≅ S.X₂)
    (he₁ : arrowExtensionInl S.X₃ S.X₁ c ≫ e.hom = S.f)
    (he₂ : e.hom ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c)
    (e' : arrowExtension S.X₃ S.X₁ c' ≅ S.X₂)
    (he'₁ : arrowExtensionInl S.X₃ S.X₁ c' ≫ e'.hom = S.f)
    (he'₂ : e'.hom ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c') :
    (Submodule.Quotient.mk c : HomArrow S.X₃ S.X₁ ⧸ (homDifferential S.X₃ S.X₁).range) =
      Submodule.Quotient.mk c' := by
  apply (exists_arrowExtension_hom_fixing_ends_iff S.X₃ S.X₁ c c').mp
  refine ⟨e.hom ≫ e'.inv, ?_, ?_⟩
  · rw [← Category.assoc, he₁, ← he'₁]
    simp
  · rw [← he'₂, ← he₂]
    simp

end TauCeti.QuiverRep

namespace TauCeti

open CategoryTheory QuiverRep

/-- An extension splits if its vertex-and-arrow Hom differential is surjective. No
finiteness or acyclicity hypothesis is needed. -/
theorem nonempty_splitting_of_surjective_homDifferential
    {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
    {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)} (hS : S.ShortExact)
    (hsurj : Function.Surjective (homDifferential S.X₃ S.X₁)) : Nonempty S.Splitting := by
  obtain ⟨c, e, hf, hg⟩ := exists_arrowExtension_iso_fixing_ends hS
  obtain ⟨sp⟩ := (nonempty_splitting_arrowExtensionComplex_iff S.X₃ S.X₁ c).mpr
    (LinearMap.mem_range.mpr (hsurj c))
  let s : S.X₃ ⟶ arrowExtension S.X₃ S.X₁ c := sp.s
  have hsection : (s ≫ e.hom) ≫ S.g = 𝟙 S.X₃ := by
    rw [Category.assoc, hg]
    exact sp.s_g
  exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact (s ≫ e.hom)
    hsection hS.mono_f⟩

end TauCeti

namespace TauCeti.QuiverRep

open CategoryTheory

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- The Hom differential is surjective if and only if every short exact sequence with
quotient `M` and subrepresentation `N` splits. -/
theorem homDifferential_surjective_iff_all_extensions_split :
    Function.Surjective (homDifferential M N) ↔
      ∀ (E : QuiverRep.{u, v, w, t} k Q) (f : N ⟶ E) (g : E ⟶ M)
        (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
          Nonempty (ShortComplex.mk f g hfg).Splitting := by
  constructor
  · intro h E f g hfg hS
    exact TauCeti.nonempty_splitting_of_surjective_homDifferential hS h
  · intro h c
    have hs := h _ (arrowExtensionInl M N c) (arrowExtensionSnd M N c)
      (arrowExtensionComplex M N c).zero (arrowExtensionComplex_shortExact M N c)
    exact (nonempty_splitting_arrowExtensionComplex_iff M N c).mp hs

end TauCeti.QuiverRep
