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

/-- A change of vertex splittings induces a map between the corresponding extensions,
fixing both end terms. -/
noncomputable def arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtension M N c ⟶ arrowExtension M N c' :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    (((LinearMap.fst k _ _) + (h i).comp (LinearMap.snd k _ _)).prod
      (LinearMap.snd k _ _))) (by
    intro i j a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun d ↦ d i j a x.2) hh
    simp only [homDifferential_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.sub_apply] at hx
    -- Path-category objects are retyped as vertices to expose the product coordinates.
    change (mapₗ k Q N a.toPath x.1 + c i j a x.2 +
        h j (mapₗ k Q M a.toPath x.2), mapₗ k Q M a.toPath x.2) =
      (mapₗ k Q N a.toPath (x.1 + h i x.2) + c' i j a x.2,
        mapₗ k Q M a.toPath x.2)
    apply Prod.ext
    · rw [map_add]
      have hc := (sub_eq_sub_iff_add_eq_add).mp hx
      grind only
    · rfl)

/-- The change of splittings acts by an upper triangular matrix with identity diagonal. -/
@[simp]
theorem arrowExtensionHom_app (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') (i : Q)
    (x : vertexSpace k Q N i × vertexSpace k Q M i) :
    ((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom x =
      (x.1 + h i x.2, x.2) := (rfl)

/-- A change of splittings fixes the inclusion of the subrepresentation. -/
@[reassoc (attr := simp)]
theorem arrowExtensionInl_arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtensionInl M N c ≫ arrowExtensionHom M N c c' h hh =
      arrowExtensionInl M N c' := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  -- Retype the path-category vertex so the component API applies.
  change Q at i
  change vertexSpace k Q N i at x
  -- The composite is retyped between the fixed end terms before rewriting.
  change ((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom
    (((arrowExtensionInl M N c).app ((Paths.of Q).obj i)).hom x) =
      ((arrowExtensionInl M N c').app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionInl_app_apply, arrowExtensionInl_app_apply, arrowExtensionHom_app]
  simp only [map_zero, add_zero]
  rfl

/-- A change of splittings fixes the projection to the quotient representation. -/
@[reassoc (attr := simp)]
theorem arrowExtensionHom_arrowExtensionSnd (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtensionHom M N c c' h hh ≫ arrowExtensionSnd M N c' =
      arrowExtensionSnd M N c := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  -- Retype the path-category vertex so the component API applies.
  change Q at i
  change vertexSpace k Q N i × vertexSpace k Q M i at x
  -- The composite is retyped between the fixed end terms before rewriting.
  change ((arrowExtensionSnd M N c').app ((Paths.of Q).obj i)).hom
    (((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom x) =
      ((arrowExtensionSnd M N c).app ((Paths.of Q).obj i)).hom x
  exact (arrowExtensionSnd_app_apply M N c' i _).trans
    ((congrArg Prod.snd (arrowExtensionHom_app M N c c' h hh i x)).trans
      (arrowExtensionSnd_app_apply M N c i x).symm)

/-- Every change of splittings is an isomorphism of extensions. -/
instance isIso_arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    IsIso (arrowExtensionHom M N c c' h hh) := by
  let φ : arrowExtensionComplex M N c ⟶ arrowExtensionComplex M N c' :=
    { τ₁ := 𝟙 N
      τ₂ := arrowExtensionHom M N c c' h hh
      τ₃ := 𝟙 M
      comm₁₂ := by
        rw [arrowExtensionComplex_f, arrowExtensionComplex_f]
        exact (Category.id_comp _).trans
          (arrowExtensionInl_arrowExtensionHom M N c c' h hh).symm
      comm₂₃ := by
        rw [arrowExtensionComplex_g, arrowExtensionComplex_g]
        exact (arrowExtensionHom_arrowExtensionSnd M N c c' h hh).trans
          (Category.comp_id _).symm }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 N))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (𝟙 M))
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (arrowExtensionComplex_shortExact M N c) (arrowExtensionComplex_shortExact M N c')

/-- Two arrow extensions are equivalent with fixed end terms if and only if their
arrow families have the same class in the Hom cokernel. -/
theorem exists_arrowExtension_iso_iff (c c' : HomArrow M N) :
    (∃ e : arrowExtension M N c ≅ arrowExtension M N c',
      arrowExtensionInl M N c ≫ e.hom = arrowExtensionInl M N c' ∧
        e.hom ≫ arrowExtensionSnd M N c' = arrowExtensionSnd M N c) ↔
      (Submodule.Quotient.mk c : HomArrow M N ⧸ (homDifferential M N).range) =
        Submodule.Quotient.mk c' := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨e, hinl, hsnd⟩
    -- Retype the middle isomorphism once as a family of maps of vertex products.
    let eₗ (i : Q) : (vertexSpace k Q N i × vertexSpace k Q M i) →ₗ[k]
        (vertexSpace k Q N i × vertexSpace k Q M i) :=
      (e.hom.app ((Paths.of Q).obj i)).hom
    let h : HomVertex M N := fun i ↦
      (LinearMap.fst k _ _).comp ((eₗ i).comp (LinearMap.inr k _ _))
    have he (i : Q) (x : vertexSpace k Q N i × vertexSpace k Q M i) :
        eₗ i x = (x.1 + h i x.2, x.2) := by
      have hf (z : vertexSpace k Q N i) :
          eₗ i (z, 0) = (z, (0 : vertexSpace k Q M i)) := by
        have hv := congrArg (fun f ↦ (f.app ((Paths.of Q).obj i)).hom z) hinl
        exact ((congrArg (eₗ i) (arrowExtensionInl_app_apply M N c i z)).symm.trans hv).trans
          (arrowExtensionInl_app_apply M N c' i z)
      have hg : (eₗ i x).2 = x.2 := by
        have hv := congrArg (fun f ↦ (f.app ((Paths.of Q).obj i)).hom x) hsnd
        exact (arrowExtensionSnd_app_apply M N c' i (eₗ i x)).symm.trans
          (hv.trans (arrowExtensionSnd_app_apply M N c i x))
      have hadd := (eₗ i).map_add (x.1, 0) (0, x.2)
      simp only [Prod.mk_add_mk, add_zero, zero_add, hf] at hadd
      apply Prod.ext
      · simpa only [Prod.fst_add, h, LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.inr_apply] using congrArg Prod.fst hadd
      · exact hg
    refine ⟨h, ?_⟩
    ext i j a x
    have hn := congrArg (fun f ↦ f.hom ((0 : vertexSpace k Q N i), x))
      (e.hom.naturality ((Paths.of Q).map a))
    -- Naturality is stated on path objects; retype it between the vertex products.
    change eₗ j (mapₗ k Q N a.toPath 0 + c i j a x, mapₗ k Q M a.toPath x) =
      (mapₗ k Q N a.toPath (eₗ i (0, x)).1 + c' i j a (eₗ i (0, x)).2,
        mapₗ k Q M a.toPath (eₗ i (0, x)).2) at hn
    rw [he, he] at hn
    have hx := congrArg Prod.fst hn
    simp only [map_zero, zero_add] at hx
    simp only [homDifferential_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.sub_apply]
    apply (sub_eq_sub_iff_add_eq_add).mpr
    exact hx.symm
  · rintro ⟨h, hh⟩
    exact ⟨asIso (arrowExtensionHom M N c c' h hh),
      arrowExtensionInl_arrowExtensionHom M N c c' h hh,
      arrowExtensionHom_arrowExtensionSnd M N c c' h hh⟩

/-- Every short exact sequence has an upper triangular arrow-matrix presentation,
with the subrepresentation and quotient fixed. -/
theorem exists_arrowExtension_iso {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)}
    (hS : S.ShortExact) :
    ∃ (c : HomArrow S.X₃ S.X₁) (e : arrowExtension S.X₃ S.X₁ c ≅ S.X₂),
      arrowExtensionInl S.X₃ S.X₁ c ≫ e.hom = S.f ∧
        e.hom ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c := by
  classical
  -- Split the sequence at each vertex using projectivity of vector spaces.
  let E (i : Q) := (evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)
  have (i : Q) : (E i).PreservesZeroMorphisms := inferInstanceAs
    (((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)).PreservesZeroMorphisms)
  have (i : Q) : PreservesFiniteLimits (E i) := inferInstanceAs
    (PreservesFiniteLimits ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)))
  have (i : Q) : PreservesFiniteColimits (E i) := inferInstanceAs
    (PreservesFiniteColimits ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)))
  let sp (i : Q) : (S.map (E i)).Splitting :=
    (hS.map_of_exact (E i)).splittingOfProjective
  let f : HomVertex S.X₁ S.X₂ := fun i ↦ (S.f.app ((Paths.of Q).obj i)).hom
  let g : HomVertex S.X₂ S.X₃ := fun i ↦ (S.g.app ((Paths.of Q).obj i)).hom
  let s : HomVertex S.X₃ S.X₂ := fun i ↦ (sp i).s.hom
  let r : HomVertex S.X₂ S.X₁ := fun i ↦ (sp i).r.hom
  have hsg (i : Q) (x : vertexSpace k Q S.X₃ i) : g i (s i x) = x :=
    congrArg (fun p ↦ p x) (sp i).s_g
  have hid (i : Q) (x : vertexSpace k Q S.X₂ i) :
      f i (r i x) + s i (g i x) = x :=
    congrArg (fun p ↦ p x) (sp i).id
  -- The upper right arrow block is computed in these vertex splittings.
  let c : HomArrow S.X₃ S.X₁ := fun i j a ↦
    (r j).comp ((mapₗ k Q S.X₂ a.toPath).comp (s i))
  have hc (i j : Q) (a : i ⟶ j) (x : vertexSpace k Q S.X₃ i) :
      f j (c i j a x) + s j (mapₗ k Q S.X₃ a.toPath x) =
        mapₗ k Q S.X₂ a.toPath (s i x) := by
    have hn : g j (mapₗ k Q S.X₂ a.toPath (s i x)) =
        mapₗ k Q S.X₃ a.toPath (g i (s i x)) :=
      congrArg (fun p ↦ p (s i x)) (S.g.naturality ((Paths.of Q).map a))
    exact (congrArg (fun z ↦ f j (r j (mapₗ k Q S.X₂ a.toPath (s i x))) + s j z)
      (hn.trans (congrArg (mapₗ k Q S.X₃ a.toPath) (hsg i x))).symm).trans
        (hid j (mapₗ k Q S.X₂ a.toPath (s i x)))
  -- The vertex decompositions commute with the resulting triangular arrow maps.
  let α : arrowExtension S.X₃ S.X₁ c ⟶ S.X₂ :=
    Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom ((f i).coprod (s i))) (by
      intro i j a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hn : f j (mapₗ k Q S.X₁ a.toPath x.1) =
          mapₗ k Q S.X₂ a.toPath (f i x.1) :=
        congrArg (fun p ↦ p x.1) (S.f.naturality ((Paths.of Q).map a))
      -- Expose the products after retyping the path objects as vertices.
      change f j (mapₗ k Q S.X₁ a.toPath x.1 + c i j a x.2) +
          s j (mapₗ k Q S.X₃ a.toPath x.2) =
        mapₗ k Q S.X₂ a.toPath (f i x.1 + s i x.2)
      simp only [map_add, hn]
      rw [add_assoc, hc])
  have hα (i : Q) (x : vertexSpace k Q S.X₁ i × vertexSpace k Q S.X₃ i) :
      (α.app ((Paths.of Q).obj i)).hom x = f i x.1 + s i x.2 := rfl
  -- Check that the assembled morphism fixes both ends of the sequence.
  have hf : arrowExtensionInl S.X₃ S.X₁ c ≫ α = S.f := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    ext x
    -- Retype the composite on its vertex space to apply the coordinate formulas.
    change Q at i
    change vertexSpace k Q S.X₁ i at x
    change (α.app ((Paths.of Q).obj i)).hom
      (((arrowExtensionInl S.X₃ S.X₁ c).app ((Paths.of Q).obj i)).hom x) = f i x
    rw [arrowExtensionInl_app_apply, hα]
    simp only [map_zero, add_zero]
    rfl
  have hg : α ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    ext x
    -- Retype the composite on its vertex space to apply the coordinate formulas.
    change Q at i
    change vertexSpace k Q S.X₁ i × vertexSpace k Q S.X₃ i at x
    change g i ((α.app ((Paths.of Q).obj i)).hom x) =
      ((arrowExtensionSnd S.X₃ S.X₁ c).app ((Paths.of Q).obj i)).hom x
    have hz : g i (f i x.1) = 0 :=
      congrArg (fun p ↦ (p.app ((Paths.of Q).obj i)).hom x.1) S.zero
    rw [hα, map_add, hz, hsg, zero_add, arrowExtensionSnd_app_apply]
  -- The short five lemma upgrades the middle morphism to an isomorphism.
  let φ : arrowExtensionComplex S.X₃ S.X₁ c ⟶ S :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := α
      τ₃ := 𝟙 S.X₃
      comm₁₂ := (Category.id_comp _).trans hf.symm
      comm₂₃ := hg.trans (Category.comp_id _).symm }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 S.X₁))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (𝟙 S.X₃))
  have : IsIso α := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (arrowExtensionComplex_shortExact S.X₃ S.X₁ c) hS
  exact ⟨c, asIso α, hf, hg⟩

end TauCeti.QuiverRep
