/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.KSheaf
public import TauCeti.Topology.Sets.Compacts

/-!
# Pullback of K-sheaves along injective maps

A K-presheaf on a space `Y` (`TopCat.KPresheaf`) is a contravariant functor on the compact
subsets of `Y`. A continuous map `f : X ⟶ Y` takes compact subsets of `X` to compact subsets of
`Y` (`TopologicalSpace.Compacts.map`), so a K-presheaf `P` on `Y` pulls back to the K-presheaf
`f^* P` on `X` with

`(f^* P)(K) = P(f(K))`

(`TopCat.KPresheaf.pullback`). This file proves that pullback along an injective map preserves
K-sheaves when `X` is locally compact Hausdorff and `Y` is Hausdorff
(`TopCat.KPresheaf.IsKSheaf.pullback`), which is the K-sheaf case of Pardon's Definition A.3.6,
the restriction of K-sheaves along an injective map.

* Taking images preserves `⊥` and `⊔`, and `⊓` because `f` is injective
  (`TopologicalSpace.Compacts.map_inf`), so the first two K-sheaf axioms for `f^* P` are those of
  `P` at the images.
* The third axiom asks that `P(f(K))` be the colimit of the `P(f(K'))` over the compact
  neighbourhoods `K'` of `K`. The images `f(K')` are not neighbourhoods of `f(K)`, so this is not
  a restriction of the third axiom of `P` along a cofinal map. Instead, the images are cofinal
  among the compact neighbourhoods `L` of `f(K)`, in the sense that every such `L` contains some
  `f(K')` (`TopologicalSpace.Compacts.exists_map_le_of_mem_compactNhds`, which needs `X` locally
  compact). A cocone `s` over the `P(f(K'))` therefore induces a cocone over the `P(L)`, sending
  `L` to the restriction to some `f(K') ⊆ L` followed by `s`; the choice of `K'` does not matter
  because the compact neighbourhoods of `K` are directed. The third axiom of `P` at `f(K)` turns
  it into a map out of `P(f(K))`, and the third axiom at each `f(K')` shows that this map extends
  `s`.

Injectivity is used only for intersections. For a map that is not injective, `K ↦ P(f(K))` is in
general not a K-sheaf: if `f` identifies two points `a ≠ b`, the second axiom at `K₁ = {a}`,
`K₂ = {b}` would make `P({f(a)})` the product of two copies of itself.

Pullback of K-sheaves along an injective map is the functor `TopCat.KSheaf.pullback`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.3, Definition A.3.6.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

variable {A : Type u} [Category.{v} A] {X Y : TopCat.{w}}

namespace KPresheaf

/-- The pullback of K-presheaves along a continuous map `f : X ⟶ Y`: the value of the pullback of
`P` on a compact `K ⊆ X` is the value of `P` on the compact image `f(K)`. -/
def pullback (f : X ⟶ Y) : KPresheaf A Y ⥤ KPresheaf A X :=
  (Functor.whiskeringLeft _ _ A).obj (Compacts.map_mono f f.hom.continuous).functor.op

variable (f : X ⟶ Y)

@[simp]
lemma pullback_obj_obj (P : KPresheaf A Y) (K : (Compacts X)ᵒᵖ) :
    ((pullback f).obj P).obj K = P.obj (op (Compacts.map f f.hom.continuous K.unop)) :=
  (rfl)

@[simp]
lemma pullback_obj_map (P : KPresheaf A Y) {K L : (Compacts X)ᵒᵖ} (g : K ⟶ L) :
    ((pullback f).obj P).map g =
      P.map (opHomOfLE (Compacts.map_mono f f.hom.continuous (leOfHom g.unop))) :=
  (rfl)

@[simp]
lemma pullback_map_app {P Q : KPresheaf A Y} (φ : P ⟶ Q) (K : (Compacts X)ᵒᵖ) :
    ((pullback f).map φ).app K = φ.app (op (Compacts.map f f.hom.continuous K.unop)) :=
  (rfl)

variable [T2Space X] {P : KPresheaf A Y} {K : Compacts X}
  (s : Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ (pullback f).obj P))

/-- For a compact neighbourhood `L` of `f(K)`, the composite of the restriction from `L` to the
image `f(K')` of a compact neighbourhood `K'` of `K` with `f(K') ⊆ L`, and the leg of `s` at `K'`,
does not depend on `K'`. -/
private lemma map_comp_ι_app_eq {L : Compacts Y} {K₁ K₂ : K.compactNhds}
    (h₁ : Compacts.map f f.hom.continuous K₁ ≤ L) (h₂ : Compacts.map f f.hom.continuous K₂ ≤ L) :
    P.map (opHomOfLE h₁) ≫ s.ι.app (op K₁) = P.map (opHomOfLE h₂) ≫ s.ι.app (op K₂) := by
  -- Both composites factor through the image of the compact neighbourhood `K₁ ⊓ K₂`.
  have h₁₂ (K' : K.compactNhds) (hle : K₁ ⊓ K₂ ≤ K') (h : Compacts.map f f.hom.continuous K' ≤ L) :
      P.map (opHomOfLE h) ≫ s.ι.app (op K') =
        P.map (opHomOfLE ((Compacts.map_mono f f.hom.continuous hle).trans h)) ≫
          s.ι.app (op (K₁ ⊓ K₂)) := by
    rw [← s.w (homOfLE hle).op]
    exact (P.map_comp_assoc _ _ _).symm
  rw [h₁₂ K₁ inf_le_left h₁, h₁₂ K₂ inf_le_right h₂]

variable [LocallyCompactSpace X]

/-- A compact neighbourhood of `K` whose image lies in the compact neighbourhood `L` of `f(K)`
(`TopologicalSpace.Compacts.exists_map_le_of_mem_compactNhds`). -/
private noncomputable def chosenNhd (L : (Compacts.map f f.hom.continuous K).compactNhds) :
    K.compactNhds :=
  ⟨_, (Compacts.exists_map_le_of_mem_compactNhds f.hom.continuous L.property).choose_spec.1⟩

omit [T2Space X] in
private lemma map_chosenNhd_le (L : (Compacts.map f f.hom.continuous K).compactNhds) :
    Compacts.map f f.hom.continuous (chosenNhd f L) ≤ L :=
  (Compacts.exists_map_le_of_mem_compactNhds f.hom.continuous L.property).choose_spec.2

/-- The cocone over the compact neighbourhoods `L` of `f(K)` induced by a cocone `s` over the
images of the compact neighbourhoods of `K`: its leg at `L` is the restriction to the image of a
compact neighbourhood `K'` of `K` with `f(K') ⊆ L`, followed by the leg of `s` at `K'`. -/
private noncomputable def imageCocone :
    Cocone ((Set.mono_coe (Compacts.map f f.hom.continuous K).compactNhds).functor.op ⋙ P) where
  pt := s.pt
  ι.app L := P.map (opHomOfLE (map_chosenNhd_le f L.unop)) ≫ s.ι.app (op (chosenNhd f L.unop))
  ι.naturality L M g := by
    rw [Functor.const_obj_map]
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (P.map_comp_assoc _ _ _).symm.trans
      (map_comp_ι_app_eq f s ((map_chosenNhd_le f M.unop).trans
        (leOfHom g.unop : (M.unop : Compacts Y) ≤ L.unop)) (map_chosenNhd_le f L.unop))

private lemma imageCocone_ι_app_eq (L : (Compacts.map f f.hom.continuous K).compactNhds) :
    (imageCocone f s).ι.app (op L) =
      P.map (opHomOfLE (map_chosenNhd_le f L)) ≫ s.ι.app (op (chosenNhd f L)) :=
  (rfl)

/-- The leg of `imageCocone f s` at `L` is the restriction to the image of any compact
neighbourhood `K'` of `K` with `f(K') ⊆ L`, followed by the leg of `s` at `K'`. -/
private lemma imageCocone_ι_app {L : (Compacts.map f f.hom.continuous K).compactNhds}
    {K' : K.compactNhds} (h : Compacts.map f f.hom.continuous K' ≤ L) :
    (imageCocone f s).ι.app (op L) = P.map (opHomOfLE h) ≫ s.ι.app (op K') :=
  (imageCocone_ι_app_eq f s L).trans (map_comp_ι_app_eq f s (map_chosenNhd_le f L) h)

variable {f} [T2Space Y]

/-- **Pullback along an injective map preserves K-sheaves** (Pardon, Definition A.3.6). If `X` is
locally compact Hausdorff, `Y` is Hausdorff and `P` is a K-sheaf on `Y`, then its pullback
`K ↦ P(f(K))` along an injective continuous map `f : X ⟶ Y` is a K-sheaf on `X`. -/
theorem IsKSheaf.pullback (hf : Function.Injective f) (hP : P.IsKSheaf) :
    ((KPresheaf.pullback f).obj P).IsKSheaf where
  nonempty_isTerminal := by
    simpa only [pullback_obj_obj, unop_op, Compacts.map_bot] using hP.nonempty_isTerminal
  -- The square of the pullback is, by definition, the square of `P` at the images.
  isPullback {K₁ K₂ K₃ K₄} h :=
    hP.isPullback (K₁ := Compacts.map f f.hom.continuous K₁)
      (K₂ := Compacts.map f f.hom.continuous K₂) (K₃ := Compacts.map f f.hom.continuous K₃)
      (K₄ := Compacts.map f f.hom.continuous K₄)
      ⟨by rw [← Compacts.map_sup, h.sup_eq], by rw [← Compacts.map_inf _ hf, h.inf_eq]⟩
  nonempty_isColimit_coconeOfCompacts K := by
    let hK := (hP.nonempty_isColimit_coconeOfCompacts (Compacts.map f f.hom.continuous K)).some
    refine ⟨{ desc s := hK.desc (imageCocone f s), fac s K' := ?_, uniq s m hm := ?_ }⟩
    · -- Both sides are maps out of `P(f(K'))`, the colimit of the `P(L)` over the compact
      -- neighbourhoods `L` of `f(K')`, which are also compact neighbourhoods of `f(K)`.
      have hK' := (hP.nonempty_isColimit_coconeOfCompacts
        (Compacts.map f f.hom.continuous K'.unop)).some
      refine hK'.hom_ext fun L ↦ ?_
      have hKL : L.unop.val ∈ (Compacts.map f f.hom.continuous K).compactNhds := fun x ↦
        L.unop.property ⟨x, Set.image_mono
          (Compacts.subset_of_mem_compactNhds K'.unop.property) x.property⟩
      have h := hK.fac (imageCocone f s) (op ⟨_, hKL⟩)
      rw [imageCocone_ι_app f s (K' := K'.unop)
        (Compacts.subset_of_mem_compactNhds L.unop.property)] at h
      exact (P.map_comp_assoc _ _ _).symm.trans h
    · -- A map out of `P(f(K))` is determined by its composites with the restrictions from the
      -- compact neighbourhoods `L` of `f(K)`, each of which factors through some `P(f(K'))`.
      refine hK.hom_ext fun L ↦ Eq.trans ?_ (hK.fac (imageCocone f s) L).symm
      obtain ⟨K', hK', hle⟩ :=
        Compacts.exists_map_le_of_mem_compactNhds f.hom.continuous L.unop.property
      refine Eq.trans ?_ (imageCocone_ι_app f s (L := L.unop) (K' := ⟨K', hK'⟩) hle).symm
      rw [← hm]
      exact (P.map_comp_assoc _ _ _)

end KPresheaf

namespace KSheaf

variable [T2Space X] [LocallyCompactSpace X] [T2Space Y]

/-- The pullback of K-sheaves along an injective continuous map `f : X ⟶ Y`, with `X` locally
compact Hausdorff and `Y` Hausdorff: the K-sheaf `K ↦ P(f(K))`
(`TopCat.KPresheaf.IsKSheaf.pullback`). -/
def pullback (f : X ⟶ Y) (hf : Function.Injective f) : KSheaf A Y ⥤ KSheaf A X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ KPresheaf.pullback f)
    fun P ↦ P.property.pullback hf

variable (f : X ⟶ Y) (hf : Function.Injective f)

@[simp]
lemma pullback_obj_obj (P : KSheaf A Y) :
    ((pullback f hf).obj P).obj = (KPresheaf.pullback f).obj P.obj :=
  (rfl)

@[simp]
lemma pullback_map_hom {P Q : KSheaf A Y} (φ : P ⟶ Q) :
    ((pullback f hf).map φ).hom = (KPresheaf.pullback f).map φ.hom :=
  (rfl)

end KSheaf

end TopCat
