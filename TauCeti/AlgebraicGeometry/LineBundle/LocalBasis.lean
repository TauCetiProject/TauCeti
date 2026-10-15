/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Morphisms from a line bundle onto local bases

Let `L` be an invertible sheaf on a scheme `X` and `φ : L ⟶ N` a morphism of `𝒪_X`-modules.
Suppose that every point of `X` has an open neighbourhood `V` and a section `s` of `L` over `V`
whose image `φ(s)` is a basis of `N` over `V`: on every open `W ⊆ V`, every section of `N` is a
unique regular multiple of the restriction of `φ(s)`. Then `φ` is an isomorphism.

Near a point, write `s = r • e` for a basis section `e` of `L`. Then `φ(e) = c • φ(s)` for a
regular function `c`, and `φ(s) = r c • φ(s)` forces `r c = 1`, so `φ` sends the basis `e` of `L`
to the basis `c • φ(s)` of `N`. Hence `φ` is bijective on sections over every small enough open,
and being an isomorphism is local.

This recognizes a morphism of line bundles as an isomorphism from the image of a single local
section, without knowing the sections of the source `L` explicitly. It applies when `L` is a
pullback, whose sections are not described concretely.
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The local step: near a point where `φ` carries a section of `L` to a basis of `N`, the morphism
`φ` is bijective on sections over every small enough open. -/
private theorem exists_forall_bijective_app {L N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (φ : L ⟶ N) {x : X}
    {V : X.Opens} (hxV : x ∈ V) (s : Γ(L, V))
    (hs : ∀ (W : X.Opens) (i : W ⟶ V),
      Function.Bijective fun r : Γ(X, W) ↦ r • N.presheaf.map i.op (φ.app V s)) :
    ∃ V' : X.Opens, x ∈ V' ∧ ∀ (W : X.Opens) (_ : W ⟶ V'), Function.Bijective (φ.app W) := by
  obtain ⟨V₁, t, hx₁⟩ := exists_mem_trivialization L x
  let i : V ⊓ V₁ ⟶ V := homOfLE inf_le_left
  let i₁ : V ⊓ V₁ ⟶ V₁ := homOfLE inf_le_right
  have hnat {U W : X.Opens} (j : W ⟶ U) (y : Γ(L, U)) :
      φ.app W (L.presheaf.map j.op y) = N.presheaf.map j.op (φ.app U y) := by
    simpa only [mapPresheaf_app, unop_op] using φ.mapPresheaf.naturality_apply j.op y
  -- Write `s = r • e` and `φ(e) = c • φ(s)` on `V ⊓ V₁`, where `e` is the basis section of `t`.
  obtain ⟨r, hr, -⟩ := existsUnique_eq_smul_map_trivializationGenerator L t i₁
    (L.presheaf.map i.op s)
  obtain ⟨c, hc⟩ := (hs (V ⊓ V₁) i).2 (φ.app (V ⊓ V₁)
    (L.presheaf.map i₁.op (trivializationGenerator L t)))
  beta_reduce at hc
  have hrc : r * c = 1 := by
    refine (hs (V ⊓ V₁) i).1 ?_
    beta_reduce
    rw [one_smul, mul_smul, hc, ← Hom.app_smul, ← hr, hnat]
  refine ⟨V ⊓ V₁, ⟨hxV, hx₁⟩, fun W j ↦ ?_⟩
  -- On `W`, the morphism `φ` sends `q • e` to `q c • φ(s)`.
  have hφ (q : Γ(X, W)) : φ.app W (q • L.presheaf.map (j ≫ i₁).op (trivializationGenerator L t)) =
      (q * X.presheaf.map j.op c) • N.presheaf.map (j ≫ i).op (φ.app V s) := by
    rw [Hom.app_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hnat, ← hc,
      Modules.map_smul, mul_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hcW : IsUnit (X.presheaf.map j.op c) :=
    .of_mul_eq_one_right _ (by rw [← map_mul, hrc, map_one])
  refine ⟨fun y₁ y₂ hy ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨q₁, rfl, -⟩ := existsUnique_eq_smul_map_trivializationGenerator L t (j ≫ i₁) y₁
    obtain ⟨q₂, rfl, -⟩ := existsUnique_eq_smul_map_trivializationGenerator L t (j ≫ i₁) y₂
    rw [hφ, hφ] at hy
    rw [hcW.mul_left_inj.mp ((hs W (j ≫ i)).1 hy)]
  · obtain ⟨p, rfl⟩ := (hs W (j ≫ i)).2 z
    refine ⟨(p * X.presheaf.map j.op r) • L.presheaf.map (j ≫ i₁).op (trivializationGenerator L t),
      ?_⟩
    rw [hφ, mul_assoc, ← map_mul, hrc, map_one, mul_one]

/-- **A morphism from a line bundle onto local bases is an isomorphism.** Let `L` be an invertible
sheaf. If every point has an open neighbourhood `V` and a section `s` of `L` over `V` such that
`φ(s)` is a basis of `N` over `V`, in the sense that for every open `W ⊆ V` every section of `N`
over `W` is a unique regular multiple of the restriction of `φ(s)`, then `φ : L ⟶ N` is an
isomorphism. -/
theorem isIso_of_forall_exists_bijective_smul {L N : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (φ : L ⟶ N)
    (h : ∀ x : X, ∃ (V : X.Opens) (_ : x ∈ V) (s : Γ(L, V)), ∀ (W : X.Opens) (i : W ⟶ V),
      Function.Bijective fun r : Γ(X, W) ↦ r • N.presheaf.map i.op (φ.app V s)) :
    IsIso φ := by
  choose V hxV s hs using h
  choose V' hxV' hV' using fun x ↦ exists_forall_bijective_app φ (hxV x) (s x) (hs x)
  have hcover : IsOpenCover V' :=
    IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV' x⟩)
  refine (isIso_iff_of_isOpenCover hcover φ).mpr fun x ↦ ?_
  -- Pullback along the inclusion of `V' x` is restriction, whose sections over `W` are the
  -- sections over the image of `W`, on which `φ` is bijective.
  refine (NatIso.isIso_map_iff (restrictFunctorIsoPullback (V' x).ι) φ).mp ?_
  refine Hom.isIso_iff_isIso_app.mpr fun W ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hV' x _ (homOfLE ((V' x).ι_image_le W))

end AlgebraicGeometry.Scheme.Modules
