/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.BaseChange

/-!
# Descent of morphisms of finitely presented schemes along cofiltered limits

Let `D : I ⥤ Scheme` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`, so that `S = lim Dⱼ`. Mathlib proves that for a scheme `X`
locally of finite presentation over a base, morphisms from `S` to `X` over the base are the
filtered colimit of the morphisms from the `Dⱼ` (Stacks, Proposition 32.6.1 (01ZC)). Applied to the
base changes `Dⱼ ×_{Dᵢ} X` of `CategoryTheory.Functor.pullbackOver`, which have limit
`S ×_{Dᵢ} X`, this shows that morphisms over the limit between base changes of schemes over a
member `Dᵢ` descend to some `Dⱼ` (Stacks, Lemma 32.10.1 (01ZM)), and that a morphism of schemes
of finite presentation over `Dᵢ` is an isomorphism over some `Dⱼ` as soon as it is one over the
limit (Stacks, Lemma 32.8.11 (081E)): the inverse over the limit descends, and the two composites,
being the identity over the limit, are the identity at some later stage.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_pullbackMap_comp_eq_of_isLimit`: a morphism over the
  limit between base changes of schemes over `Dᵢ`, the target of finite presentation, descends to
  some `Dⱼ`.
* `TauCeti.AlgebraicGeometry.Scheme.pullbackMap_iff_of_pullbackMap_comp_eq`: the base change to the
  limit of such a descended morphism is the original morphism, up to isomorphism.
* `TauCeti.AlgebraicGeometry.Scheme.exists_isIso_pullbackMap_of_isLimit`: a morphism of schemes
  of finite presentation over `Dᵢ` whose base change to the limit is an isomorphism is an
  isomorphism over some `Dⱼ`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `X` and `Y` be schemes over a member `Dᵢ`, with `X` quasi-compact and
quasi-separated over `Dᵢ` and `Y` locally of finite presentation over `Dᵢ`. Every morphism
`X ×_{Dᵢ} S ⟶ Y ×_{Dᵢ} S` over `S` is the base change of a morphism `X ×_{Dᵢ} Dⱼ ⟶ Y ×_{Dᵢ} Dⱼ`
over some `Dⱼ`. Stacks, Lemma 32.10.1 (01ZM), descent of morphisms. -/
theorem exists_pullbackMap_comp_eq_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation q]
    (a : pullback (c.π.app i) p ⟶ pullback (c.π.app i) q)
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _) :
    ∃ (j : I) (hji : j ⟶ i) (b : pullback (D.map hji) p ⟶ pullback (D.map hji) q),
      b ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫ b =
          a ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y) (𝟙 _) (by simp)
            (by simp) := by
  let t : D.pullbackOver p ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd _ _ ≫ p
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc p f] }
  -- The composite of `a` with the projection to `Y` descends to some member.
  obtain ⟨j, g', hg'₁, hg'₂⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D.pullbackOver p) t q _ (hc.pullbackOver p)
      (a ≫ pullback.snd _ _ : pullback (c.π.app i) p ⟶ Y) (by
        ext j
        simp only [t, NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app,
          Category.assoc]
        rw [Cone.pullbackOver_π_app_snd_assoc, ← pullback.condition, ← pullback.condition,
          reassoc_of% ha])
  refine ⟨j.left, j.hom, pullback.lift (pullback.fst _ _) g' (by rw [hg'₂]; exact
    pullback.condition), by simp, ?_⟩
  apply pullback.hom_ext
  · simp [reassoc_of% ha]
  · rw [Category.assoc, pullback.lift_snd]
    exact hg'₁.trans (by simp)

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- Let `c` be a cone over `D`, and let `b : X ×_{Dᵢ} Dⱼ ⟶ Y ×_{Dᵢ} Dⱼ` over `Dⱼ` descend a morphism
`a : X ×_{Dᵢ} S ⟶ Y ×_{Dᵢ} S` over `S`, as in `exists_pullbackMap_comp_eq_of_isLimit`. Then the
base change of `b` to `S` is `a` up to the canonical isomorphisms, so it has every property of
morphisms respecting isomorphisms that `a` has. -/
theorem pullbackMap_iff_of_pullbackMap_comp_eq (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {i j : I} (hji : j ⟶ i) {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    {a : pullback (c.π.app i) p ⟶ pullback (c.π.app i) q}
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _)
    {b : pullback (D.map hji) p ⟶ pullback (D.map hji) q}
    (hb₁ : b ≫ pullback.fst _ _ = pullback.fst _ _)
    (hb₂ : pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫
      b = a ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y) (𝟙 _) (by simp)
        (by simp)) :
    P (pullback.map (c.π.app j) (pullback.fst (D.map hji) p) (c.π.app j)
      (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁])) ↔ P a := by
  -- `S ×_{Dⱼ} (Dⱼ ×_{Dᵢ} Z) ≅ S ×_{Dᵢ} Z`.
  let ψ {Z : Scheme.{u}} (s : Z ⟶ D.obj i) :
      pullback (c.π.app j) (pullback.fst (D.map hji) s) ≅ pullback (c.π.app i) s :=
    pullbackRightPullbackFstIso (D.map hji) s (c.π.app j) ≪≫ pullback.congrHom (c.w hji) rfl
  have : pullback.map (c.π.app j) (pullback.fst (D.map hji) p) (c.π.app j)
      (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb₁]) =
      (ψ p).hom ≫ a ≫ (ψ q).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply pullback.hom_ext
    · simp [ψ, ha]
    · have h := congrArg (· ≫ pullback.snd (D.map hji) q) hb₂
      simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at h
      have key : (ψ p).hom ≫ pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 _) (𝟙 _)
          (by simp) (by simp) = pullback.snd _ _ := by
        apply pullback.hom_ext <;> simp [ψ, pullback.condition]
      rw [Category.assoc, Category.assoc, ← h, reassoc_of% key]
      simp [ψ]
  rw [this, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `g : X ⟶ Y` a morphism of schemes over a member `Dᵢ`, with `X` locally of
finite presentation and quasi-compact over `Dᵢ`, and `Y` locally of finite type, quasi-compact and
quasi-separated over `Dᵢ`. If the base change of `g` to `S` is an isomorphism, then so is its base
change to some `Dⱼ`. Stacks, Lemma 32.8.11 (081E). -/
theorem exists_isIso_pullbackMap_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [LocallyOfFiniteType q]
    [QuasiCompact q] [QuasiSeparated q] (g : X ⟶ Y) (hg : g ≫ q = p)
    [IsIso (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i),
      IsIso (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  -- The members of `D` over `i` base changed to `X` and to `Y`, and their limits.
  let DX := D.pullbackOver p
  let DY := D.pullbackOver q
  have hcX := hc.pullbackOver p
  have hcY := hc.pullbackOver q
  let t {Z : Scheme.{u}} (r : Z ⟶ D.obj i) :
      D.pullbackOver r ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd _ _ ≫ r
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc r f] }
  -- The base change `φ` of `g` to the limit, and its base changes `φB j` to the members.
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have : IsIso φ := ‹_›
  let φB (j : Over i) : DX.obj j ⟶ DY.obj j :=
    pullback.map (D.map j.hom) p (D.map j.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have φB_fst (j : Over i) : φB j ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [φB]
  have φB_snd (j : Over i) : φB j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g := by simp [φB]
  have π_φB (j : Over i) :
      (c.pullbackOver p).π.app j ≫ φB j = φ ≫ (c.pullbackOver q).π.app j := by
    apply pullback.hom_ext <;> simp [φB, φ]
  have map_φB {j k : Over i} (f : j ⟶ k) : DX.map f ≫ φB k = φB j ≫ DY.map f := by
    apply pullback.hom_ext
    · rw [Category.assoc, φB_fst, Functor.pullbackOver_map_fst, Category.assoc,
        Functor.pullbackOver_map_fst, reassoc_of% φB_fst]
    · rw [Category.assoc, φB_snd, Functor.pullbackOver_map_snd_assoc, Category.assoc,
        Functor.pullbackOver_map_snd, φB_snd]
  have inv_fst : inv φ ≫ pullback.fst (c.π.app i) p = pullback.fst (c.π.app i) q := by
    rw [IsIso.inv_comp_eq]; simp [φ]
  have inv_snd : inv φ ≫ pullback.snd (c.π.app i) p ≫ g = pullback.snd (c.π.app i) q := by
    rw [IsIso.inv_comp_eq]; simp [φ]
  -- The inverse of `φ` followed by the projection to `X` descends to some member.
  obtain ⟨j, g', hg'₁, hg'₂⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation DY (t q) p _ hcY
      (inv φ ≫ pullback.snd _ _ : pullback (c.π.app i) q ⟶ X) (by
        ext j
        simp only [t, NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app,
          Category.assoc]
        rw [Cone.pullbackOver_π_app_snd_assoc, ← pullback.condition, ← pullback.condition,
          reassoc_of% inv_fst])
  -- Both composites of `φB j` with this descent are the identity on the limit, hence on some
  -- later member.
  obtain ⟨k, hkj, hk⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType DY (t q) q _ hcY
      (g' ≫ g) (pullback.snd _ _) (by simp [hg, hg'₂]) rfl (by
        rw [reassoc_of% hg'₁, Cone.pullbackOver_π_app_snd, inv_snd])
  obtain ⟨k', hk'j, hk'⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType DX (t p) p _ hcX
      (φB j ≫ g') (pullback.snd _ _) (by simp [hg'₂, t, reassoc_of% φB_snd, hg]) rfl (by
        rw [reassoc_of% π_φB, hg'₁, IsIso.hom_inv_id_assoc, Cone.pullbackOver_π_app_snd])
  obtain ⟨l, hlk, hlk', hl⟩ := IsCofiltered.cospan hkj hk'j
  refine ⟨l.left, l.hom,
    ⟨pullback.lift (pullback.fst _ _) (DY.map (hlk ≫ hkj) ≫ g') ?_, ?_, ?_⟩⟩
  · rw [Category.assoc, hg'₂]
    simp [t, DY, pullback.condition]
  · apply pullback.hom_ext
    · simp
    · -- The base change of `g` to `Dₗ` in the goal is `φB l` by definition.
      change φB l ≫ _ ≫ _ = _
      rw [pullback.lift_snd, ← Category.assoc, ← map_φB, hl, Functor.map_comp, Category.assoc,
        Category.assoc, hk', Functor.pullbackOver_map_snd, Functor.pullbackOver_map_snd,
        Category.id_comp]
  · apply pullback.hom_ext
    · simp
    · -- The base change of `g` to `Dₗ` in the goal is `φB l` by definition.
      change _ ≫ φB l ≫ _ = _
      rw [φB_snd, pullback.lift_snd_assoc, Functor.map_comp, Category.assoc, Category.assoc, hk,
        Functor.pullbackOver_map_snd, Functor.pullbackOver_map_snd, Category.id_comp]

end TauCeti.AlgebraicGeometry.Scheme
