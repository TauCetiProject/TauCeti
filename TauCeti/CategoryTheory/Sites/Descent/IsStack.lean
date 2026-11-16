/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

/-!
# Transitivity and base-change locality of effective descent

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
This file establishes closure properties for prestacks, stacks, and the local conditions
`F.IsPrestackFor` and `F.IsStackFor`:

## Main results

* Monotonicity in the topology (`IsPrestack.of_le`, `IsStack.of_le`): a (pre)stack for a finer
  topology is a (pre)stack for any coarser topology.
* Gluing and separation of morphisms over covering sieves (`existsUnique_map_eq_of_isPrestack`,
  `hom_ext_of_isPrestack`) for a prestack `F`.
* Refinement and base-change locality for `IsPrestackFor` (`IsPrestackFor.of_le`,
  `IsPrestackFor.of_pullback`): descent of morphisms passes from a finer sieve `R₁ ≤ R₂` when all
  pullbacks of `R₁` along arrows of `R₂` satisfy `IsPrestackFor`, and is local along any
  `J`-`1`-hypercover when `F` is a `J`-prestack.
* Transitivity along compositions (`IsPrestackFor.of_comp`, `IsStackFor.of_comp`): if `F` is a
  prestack for `J`, `p : ∀ j, Y j ⟶ S` satisfies descent (resp. effective descent), and each
  `u j : ∀ k, X j k ⟶ Y j` is a `J`-covering family (resp. also satisfies effective descent),
  then the composite family `u j k ≫ p j` satisfies descent (resp. effective descent).
* Base-change locality (`IsStackFor.of_pullback`): if `F` is a prestack for `J`, `f` and `v` are
  `J`-covering families of `S`, `F` has effective descent for `v`, and `F` has effective descent
  for the pullback of `f` along each `v a`, then `F` has effective descent for `f`. This follows
  from `IsStackFor.of_comp` and Mathlib's `IsStackFor.of_le'`.
* Small precoverage criteria (`IsPrestack.of_precoverage_of_small`,
  `IsStack.of_precoverage_of_small`): for a `t`-small precoverage `J`, checking `IsPrestackFor`
  (resp. `IsStackFor`) on `t`-small `0`-hypercovers suffices to show `F` is a (pre)stack for
  `J.toGrothendieck`.

## References

* Jean Giraud, *Cohomologie non abélienne*, Chapter II, §1.2.
* The Stacks Project, Section 8.5, *Stacks*, Tag 026F.
-/

public section

universe t t' v' v u' u

open CategoryTheory Limits Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A prestack for a Grothendieck topology `J₂` is a prestack for any coarser topology `J₁ ≤ J₂`.
-/
lemma IsPrestack.of_le {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) [F.IsPrestack J₂] :
    F.IsPrestack J₁ where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_of_le _ (fun _ _ hR ↦ h _ hR)
      ((isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J₂ M N))

/-- A stack for a Grothendieck topology `J₂` is a stack for any coarser topology `J₁ ≤ J₂`. -/
lemma IsStack.of_le {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) [F.IsStack J₂] :
    F.IsStack J₁ :=
  have := IsPrestack.of_le F h
  ⟨fun _ hR ↦ IsStack.essSurj_of_sieve F _ (h _ hR)⟩

section IsPrestack

variable {F} {J : GrothendieckTopology C} [F.IsPrestack J]

/-- If `F` is a prestack for `J`, two morphisms `M₁ ⟶ M₂` in `F.obj (.mk (op W))` are equal if
their pullbacks along every morphism in a `J`-covering sieve `R ∈ J W` agree. -/
lemma hom_ext_of_isPrestack {W : C} {M₁ M₂ : F.obj (.mk (op W))} {R : Sieve W} (hR : R ∈ J W)
    {φ ψ : M₁ ⟶ M₂}
    (h : ∀ ⦃Z : C⦄ (r : Z ⟶ W), R r →
      (F.map r.op.toLoc).toFunctor.map φ = (F.map r.op.toLoc).toFunctor.map ψ) :
    φ = ψ := by
  have hR' : Sieve.generate ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows ∈
      (J.over W) (Over.mk (𝟙 W)) := by
    rw [Sieve.generate_sieve, GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    exact hR
  refine F.presheafHomObjHomEquiv.injective ?_
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    (IsPrestack.isSheaf J M₁ M₂)).isSheafFor _ hR').isSeparatedFor.ext fun Z g hg ↦ ?_
  rw [presheafHom_map_presheafHomObjHomEquiv, presheafHom_map_presheafHomObjHomEquiv]
  have hr : R Z.hom := by
    have : R g.left := hg
    rwa [show g.left = Z.hom by simpa using Over.w g] at this
  exact h Z.hom hr

/-- If `F` is a prestack for `J`, a family of morphisms `r^* M₁ ⟶ r^* M₂` over a `J`-covering
sieve `R ∈ J W` that is compatible with `pullHom` descends to a unique morphism `M₁ ⟶ M₂`. -/
lemma existsUnique_map_eq_of_isPrestack {W : C} {M₁ M₂ : F.obj (.mk (op W))} {R : Sieve W}
    (hR : R ∈ J W)
    (m : ∀ ⦃Z : C⦄ (r : Z ⟶ W), R r →
      ((F.map r.op.toLoc).toFunctor.obj M₁ ⟶ (F.map r.op.toLoc).toFunctor.obj M₂))
    (hm : ∀ ⦃Z' Z : C⦄ (g : Z' ⟶ Z) (r : Z ⟶ W) (hr : R r),
      m (g ≫ r) (R.downward_closed hr g) = pullHom (m r hr) g (g ≫ r) (g ≫ r) rfl rfl) :
    ∃! φ : M₁ ⟶ M₂, ∀ ⦃Z : C⦄ (r : Z ⟶ W) (hr : R r),
      (F.map r.op.toLoc).toFunctor.map φ = m r hr := by
  have hR' : Sieve.generate ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows ∈
      (J.over W) (Over.mk (𝟙 W)) := by
    rw [Sieve.generate_sieve, GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    exact hR
  have hsh := ((isSheaf_iff_isSheaf_of_type _ _).1
    (IsPrestack.isSheaf J M₁ M₂)).isSheafFor _ hR'
  let x : Presieve.FamilyOfElements (F.presheafHom M₁ M₂)
      ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows := fun Z g hg ↦
    m Z.hom (by have : R g.left := hg; rwa [show g.left = Z.hom by simpa using Over.w g] at this)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z Z' g f hg
    have hg' : R Z.hom := by
      have : R g.left := hg
      rwa [show g.left = Z.hom by simpa using Over.w g] at this
    have haux : ∀ {w : Z'.left ⟶ W} (hw : f.left ≫ Z.hom = w),
        m w (by rw [← hw]; exact R.downward_closed hg' f.left) =
          pullHom (m Z.hom hg') f.left w w (by simp [hw]) (by simp [hw]) := by
      rintro w rfl
      exact hm f.left Z.hom hg'
    exact haux (Over.w f)
  obtain ⟨y, hy, _⟩ := hsh x hx
  let φ : M₁ ⟶ M₂ := F.presheafHomObjHomEquiv.symm y
  have hφ : ∀ ⦃Z : C⦄ (r : Z ⟶ W) (hr : R r), (F.map r.op.toLoc).toFunctor.map φ = m r hr := by
    intro Z r hr
    let g : Over.mk r ⟶ Over.mk (𝟙 W) := Over.homMk r (Category.comp_id r)
    have hmem : ((Sieve.overEquiv (Over.mk (𝟙 W))).symm R).arrows g := hr
    have h1 := hy g hmem
    rw [← Equiv.apply_symm_apply F.presheafHomObjHomEquiv y,
      presheafHom_map_presheafHomObjHomEquiv] at h1
    exact h1
  exact ⟨φ, hφ, fun ψ hψ ↦ hom_ext_of_isPrestack hR fun Z r hr ↦ (hψ r hr).trans (hφ r hr).symm⟩

end IsPrestack

namespace OfComp

variable {F} {J : GrothendieckTopology C} [F.IsPrestack J]
  {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S}
  {ι : κ → Type t'} {X : ∀ j, ι j → C} {u : ∀ j k, X j k ⟶ Y j}

/-- Transport a factorization `f ≫ g = h` in `C` to `g.op.toLoc ≫ f.op.toLoc = h.op.toLoc` in
`LocallyDiscrete Cᵒᵖ`. -/
private lemma toLoc_comp {A B D : C} {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (e : f ≫ g = h) :
    g.op.toLoc ≫ f.op.toLoc = h.op.toLoc := by
  subst e
  rfl

/-- Pentagon identity for `mapComp'` on a triple `c ≫ b ≫ a`. -/
private lemma mapComp'_triple_hom {A B D E : C} (a : B ⟶ A) (b : D ⟶ B) (c : E ⟶ D)
    (ab : D ⟶ A) (bc : E ⟶ B) (abc : E ⟶ A)
    (hab : b ≫ a = ab) (hbc : c ≫ b = bc) (habc : c ≫ ab = abc)
    (M : F.obj (.mk (op A))) :
    (F.mapComp' a.op.toLoc bc.op.toLoc abc.op.toLoc
        (toLoc_comp (by rw [← hbc, Category.assoc, hab, habc]))).hom.toNatTrans.app M ≫
      (F.mapComp' b.op.toLoc c.op.toLoc bc.op.toLoc (toLoc_comp hbc)).hom.toNatTrans.app _ ≫
      (F.map c.op.toLoc).toFunctor.map
        ((F.mapComp' a.op.toLoc b.op.toLoc ab.op.toLoc (toLoc_comp hab)).inv.toNatTrans.app M) =
      (F.mapComp' ab.op.toLoc c.op.toLoc abc.op.toLoc (toLoc_comp habc)).hom.toNatTrans.app M := by
  simpa using (F.mapComp'₀₂₃_hom_app a.op.toLoc b.op.toLoc c.op.toLoc ab.op.toLoc bc.op.toLoc
    abc.op.toLoc (toLoc_comp hab) (toLoc_comp hbc) (toLoc_comp habc) M).symm

/-- Inverse pentagon identity for `mapComp'` on a triple `c ≫ b ≫ a`. -/
private lemma mapComp'_triple_inv {A B D E : C} (a : B ⟶ A) (b : D ⟶ B) (c : E ⟶ D)
    (ab : D ⟶ A) (bc : E ⟶ B) (abc : E ⟶ A)
    (hab : b ≫ a = ab) (hbc : c ≫ b = bc) (habc : c ≫ ab = abc)
    (M : F.obj (.mk (op A))) :
    (F.map c.op.toLoc).toFunctor.map
        ((F.mapComp' a.op.toLoc b.op.toLoc ab.op.toLoc (toLoc_comp hab)).hom.toNatTrans.app M) ≫
      (F.mapComp' b.op.toLoc c.op.toLoc bc.op.toLoc (toLoc_comp hbc)).inv.toNatTrans.app _ ≫
      (F.mapComp' a.op.toLoc bc.op.toLoc abc.op.toLoc
        (toLoc_comp (by rw [← hbc, Category.assoc, hab, habc]))).inv.toNatTrans.app M =
      (F.mapComp' ab.op.toLoc c.op.toLoc abc.op.toLoc (toLoc_comp habc)).inv.toNatTrans.app M := by
  simpa using (F.mapComp'₀₂₃_inv_app a.op.toLoc b.op.toLoc c.op.toLoc ab.op.toLoc bc.op.toLoc
    abc.op.toLoc (toLoc_comp hab) (toLoc_comp hbc) (toLoc_comp habc) M).symm

/-- Restrict a descent datum along the composite family `u j k ≫ p j` to the covering `u j` of
`Y j`. -/
private def restrictDatum (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (j : κ) : F.DescentData (u j) where
  obj k := D.obj ⟨j, k⟩
  hom _ q k₁ k₂ f₁ f₂ hf₁ hf₂ :=
    D.hom (q ≫ p j) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) f₁ f₂
      (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
  pullHom_hom _ _ g q q' hq k₁ k₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    D.pullHom_hom g (q ≫ p j) (q' ≫ p j) (by rw [← Category.assoc, hq])
      (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) f₁ f₂
      (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂]) gf₁ gf₂ hgf₁ hgf₂
  hom_self _ q k g hg :=
    D.hom_self (q ≫ p j) (i := ⟨j, k⟩) g (by rw [← Category.assoc, hg])
  hom_comp _ q k₁ k₂ k₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    D.hom_comp (q ≫ p j) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) (i₃ := ⟨j, k₃⟩) f₁ f₂ f₃
      (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
      (by rw [← Category.assoc, hf₃])

/-- The component morphism `(u j k ≫ p j)^* N₁ ⟶ (u j k ≫ p j)^* N₂` extracted from `γ`, with
explicit domain and codomain types to avoid transparency mismatches during rewriting. -/
private def γHom {N₁ N₂ : F.obj (.mk (op S))}
    (γ : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₁ ⟶
      (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₂)
    (j : κ) (k : ι j) :
    (F.map (u j k ≫ p j).op.toLoc).toFunctor.obj N₁ ⟶
      (F.map (u j k ≫ p j).op.toLoc).toFunctor.obj N₂ :=
  γ.hom ⟨j, k⟩

/-- Restrict a morphism of `ofObj` descent data along `u j k ≫ p j` to a morphism of `ofObj`
descent data along `u j` between `(p j)^* N₁` and `(p j)^* N₂`. -/
private def restrictOfObjHom {N₁ N₂ : F.obj (.mk (op S))}
    (γ : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₁ ⟶
      (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₂) (j : κ) :
    (F.toDescentData (u j)).obj ((F.map (p j).op.toLoc).toFunctor.obj N₁) ⟶
      (F.toDescentData (u j)).obj ((F.map (p j).op.toLoc).toFunctor.obj N₂) where
  hom k :=
    (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
        (toLoc_comp rfl)).inv.toNatTrans.app N₁ ≫
      γHom γ j k ≫
      (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
        (toLoc_comp rfl)).hom.toNatTrans.app N₂
  comm W q k₁ k₂ f₁ f₂ hf₁ hf₂ := by
    have hγ : (F.map f₁.op.toLoc).toFunctor.map (γHom γ j k₁) ≫
        (F.mapComp' (u j k₁ ≫ p j).op.toLoc f₁.op.toLoc (q ≫ p j).op.toLoc
          (toLoc_comp (by rw [← Category.assoc, hf₁]))).inv.toNatTrans.app N₂ ≫
        (F.mapComp' (u j k₂ ≫ p j).op.toLoc f₂.op.toLoc (q ≫ p j).op.toLoc
          (toLoc_comp (by rw [← Category.assoc, hf₂]))).hom.toNatTrans.app N₂ =
        ((F.mapComp' (u j k₁ ≫ p j).op.toLoc f₁.op.toLoc (q ≫ p j).op.toLoc
          (toLoc_comp (by rw [← Category.assoc, hf₁]))).inv.toNatTrans.app N₁ ≫
        (F.mapComp' (u j k₂ ≫ p j).op.toLoc f₂.op.toLoc (q ≫ p j).op.toLoc
          (toLoc_comp (by rw [← Category.assoc, hf₂]))).hom.toNatTrans.app N₁) ≫
        (F.map f₂.op.toLoc).toFunctor.map (γHom γ j k₂) :=
      γ.comm (q ≫ p j) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) f₁ f₂
        (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
    dsimp only [toDescentData, DescentData.ofObj]
    simp only [Functor.map_comp, Category.assoc]
    rw [← cancel_epi ((F.mapComp' (u j k₁).op.toLoc f₁.op.toLoc q.op.toLoc
      (toLoc_comp hf₁)).hom.toNatTrans.app ((F.map (p j).op.toLoc).toFunctor.obj N₁))]
    rw [← cancel_epi ((F.mapComp' (p j).op.toLoc q.op.toLoc (q ≫ p j).op.toLoc
      (toLoc_comp rfl)).hom.toNatTrans.app N₁)]
    rw [← cancel_mono ((F.mapComp' (u j k₂).op.toLoc f₂.op.toLoc q.op.toLoc
      (toLoc_comp hf₂)).inv.toNatTrans.app ((F.map (p j).op.toLoc).toFunctor.obj N₂))]
    rw [← cancel_mono ((F.mapComp' (p j).op.toLoc q.op.toLoc (q ≫ p j).op.toLoc
      (toLoc_comp rfl)).inv.toNatTrans.app N₂)]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    have hL₁ := mapComp'_triple_hom (F := F) (p j) (u j k₁) f₁ (u j k₁ ≫ p j) q (q ≫ p j)
      rfl hf₁ (by rw [← Category.assoc, hf₁]) N₁
    have hR₁ := mapComp'_triple_inv (F := F) (p j) (u j k₁) f₁ (u j k₁ ≫ p j) q (q ≫ p j)
      rfl hf₁ (by rw [← Category.assoc, hf₁]) N₂
    have hL₂ := mapComp'_triple_hom (F := F) (p j) (u j k₂) f₂ (u j k₂ ≫ p j) q (q ≫ p j)
      rfl hf₂ (by rw [← Category.assoc, hf₂]) N₁
    have hR₂ := mapComp'_triple_inv (F := F) (p j) (u j k₂) f₂ (u j k₂ ≫ p j) q (q ≫ p j)
      rfl hf₂ (by rw [← Category.assoc, hf₂]) N₂
    rw [reassoc_of% hL₁, reassoc_of% hL₂, hR₁, hR₂]
    rw [← cancel_mono ((F.mapComp' (u j k₂ ≫ p j).op.toLoc f₂.op.toLoc (q ≫ p j).op.toLoc
      (toLoc_comp (by rw [← Category.assoc, hf₂]))).hom.toNatTrans.app N₂)]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
    rw [hγ]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Cat.Hom.comp_toFunctor,
      Functor.comp_obj, Category.comp_id]

/-- Conjugate `(r ≫ a)^* (ψ j)` along `mapComp'` to `b^* (γHom γ j k)` using `hψ`. -/
private lemma map_comp_conj_eq {N₁ N₂ : F.obj (.mk (op S))}
    (γ : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₁ ⟶
      (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₂)
    (ψ : ∀ j, (F.map (p j).op.toLoc).toFunctor.obj N₁ ⟶
      (F.map (p j).op.toLoc).toFunctor.obj N₂)
    (hψ : ∀ j k, (F.map (u j k).op.toLoc).toFunctor.map (ψ j) =
      (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (toLoc_comp rfl)).inv.toNatTrans.app N₁ ≫
        γHom γ j k ≫
        (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (toLoc_comp rfl)).hom.toNatTrans.app N₂)
    {W Z : C} {q : W ⟶ S} (r : Z ⟶ W) {j : κ} {k : ι j} {a : W ⟶ Y j} (b : Z ⟶ X j k)
    (ha : a ≫ p j = q) (hb : b ≫ u j k = r ≫ a) :
    (F.mapComp' (p j).op.toLoc (r ≫ a).op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [Category.assoc, ha]))).hom.toNatTrans.app N₁ ≫
      (F.mapComp' a.op.toLoc r.op.toLoc (r ≫ a).op.toLoc (toLoc_comp rfl)).hom.toNatTrans.app _ ≫
      (F.map r.op.toLoc).toFunctor.map ((F.map a.op.toLoc).toFunctor.map (ψ j)) ≫
      (F.mapComp' a.op.toLoc r.op.toLoc (r ≫ a).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app _ ≫
      (F.mapComp' (p j).op.toLoc (r ≫ a).op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [Category.assoc, ha]))).inv.toNatTrans.app N₂ =
    (F.mapComp' (u j k ≫ p j).op.toLoc b.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb, Category.assoc, ha]))).hom.toNatTrans.app N₁ ≫
      (F.map b.op.toLoc).toFunctor.map (γHom γ j k) ≫
      (F.mapComp' (u j k ≫ p j).op.toLoc b.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb, Category.assoc, ha]))).inv.toNatTrans.app N₂ := by
  rw [F.mapComp'_naturality_2_assoc a.op.toLoc r.op.toLoc (r ≫ a).op.toLoc (toLoc_comp rfl) (ψ j),
    ← F.mapComp'_naturality_2 (u j k).op.toLoc b.op.toLoc (r ≫ a).op.toLoc (toLoc_comp hb) (ψ j),
    hψ j k]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (mapComp'_triple_hom (F := F) (p j) (u j k) b (u j k ≫ p j) (r ≫ a) (r ≫ q)
    rfl hb (by rw [← Category.assoc, hb, Category.assoc, ha]) N₁),
    mapComp'_triple_inv (F := F) (p j) (u j k) b (u j k ≫ p j) (r ≫ a) (r ≫ q)
    rfl hb (by rw [← Category.assoc, hb, Category.assoc, ha]) N₂]

/-- Auxiliary commutation for `IsPrestackFor.of_comp`: if `ψ j` pulls back along `u j k` to the
conjugate of `γHom γ j k`, then `r^* (a₁^* (ψ j₁) ≫ can_{N₂}) = r^* (can_{N₁} ≫ a₂^* (ψ j₂))`
whenever `r ≫ a₁` and `r ≫ a₂` factor through `u j₁ k₁` and `u j₂ k₂`. -/
private lemma prestack_of_comp_comm_local {N₁ N₂ : F.obj (.mk (op S))}
    (γ : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₁ ⟶
      (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N₂)
    (ψ : ∀ j, (F.map (p j).op.toLoc).toFunctor.obj N₁ ⟶
      (F.map (p j).op.toLoc).toFunctor.obj N₂)
    (hψ : ∀ j k, (F.map (u j k).op.toLoc).toFunctor.map (ψ j) =
      (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (toLoc_comp rfl)).inv.toNatTrans.app N₁ ≫
        γHom γ j k ≫
        (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (toLoc_comp rfl)).hom.toNatTrans.app N₂)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    (F.map r.op.toLoc).toFunctor.map
        ((F.map a₁.op.toLoc).toFunctor.map (ψ j₁) ≫
          ((F.toDescentData p).obj N₂).hom q a₁ a₂ ha₁ ha₂) =
      (F.map r.op.toLoc).toFunctor.map
        (((F.toDescentData p).obj N₁).hom q a₁ a₂ ha₁ ha₂ ≫
          (F.map a₂.op.toLoc).toFunctor.map (ψ j₂)) := by
  have hγ : (F.map b₁.op.toLoc).toFunctor.map (γHom γ j₁ k₁) ≫
      (F.mapComp' (u j₁ k₁ ≫ p j₁).op.toLoc b₁.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb₁, Category.assoc, ha₁]))).inv.toNatTrans.app N₂ ≫
      (F.mapComp' (u j₂ k₂ ≫ p j₂).op.toLoc b₂.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]))).hom.toNatTrans.app N₂ =
      ((F.mapComp' (u j₁ k₁ ≫ p j₁).op.toLoc b₁.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb₁, Category.assoc, ha₁]))).inv.toNatTrans.app N₁ ≫
      (F.mapComp' (u j₂ k₂ ≫ p j₂).op.toLoc b₂.op.toLoc (r ≫ q).op.toLoc
        (toLoc_comp (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]))).hom.toNatTrans.app N₁) ≫
      (F.map b₂.op.toLoc).toFunctor.map (γHom γ j₂ k₂) :=
    γ.comm (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, ha₂])
  dsimp only [toDescentData, DescentData.ofObj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((F.map r.op.toLoc).toFunctor.map
      ((F.mapComp' (p j₁).op.toLoc a₁.op.toLoc q.op.toLoc (toLoc_comp ha₁)).hom.toNatTrans.app N₁)),
    ← cancel_epi ((F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc
      (toLoc_comp rfl)).hom.toNatTrans.app N₁),
    ← cancel_mono ((F.map r.op.toLoc).toFunctor.map
      ((F.mapComp' (p j₂).op.toLoc a₂.op.toLoc q.op.toLoc (toLoc_comp ha₂)).inv.toNatTrans.app N₂)),
    ← cancel_mono ((F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc
      (toLoc_comp rfl)).inv.toNatTrans.app N₂)]
  simp only [Category.assoc]
  have hcancel (j : κ) (a : W ⟶ Y j) (ha : a ≫ p j = q) (N : F.obj (.mk (op S))) :
      (F.map r.op.toLoc).toFunctor.map
        ((F.mapComp' (p j).op.toLoc a.op.toLoc q.op.toLoc (toLoc_comp ha)).hom.toNatTrans.app N) ≫
      (F.map r.op.toLoc).toFunctor.map
        ((F.mapComp' (p j).op.toLoc a.op.toLoc q.op.toLoc (toLoc_comp ha)).inv.toNatTrans.app N) =
      𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.hom_inv_id_toNatTrans_app, Functor.map_id]
  rw [reassoc_of% (hcancel j₂ a₂ ha₂ N₂), reassoc_of% (hcancel j₁ a₁ ha₁ N₁)]
  have hL (j : κ) (a : W ⟶ Y j) (ha : a ≫ p j = q) :
      (F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc (toLoc_comp rfl)).hom.toNatTrans.app N₁ ≫
        (F.map r.op.toLoc).toFunctor.map
          ((F.mapComp' (p j).op.toLoc a.op.toLoc q.op.toLoc
            (toLoc_comp ha)).hom.toNatTrans.app N₁) =
        (F.mapComp' (p j).op.toLoc (r ≫ a).op.toLoc (r ≫ q).op.toLoc
          (toLoc_comp (by rw [Category.assoc, ha]))).hom.toNatTrans.app N₁ ≫
        (F.mapComp' a.op.toLoc r.op.toLoc (r ≫ a).op.toLoc
          (toLoc_comp rfl)).hom.toNatTrans.app _ := by
    rw [← mapComp'_triple_hom (F := F) (p j) a r q (r ≫ a) (r ≫ q) ha rfl rfl N₁]
    simp [← Functor.map_comp]
  have hR (j : κ) (a : W ⟶ Y j) (ha : a ≫ p j = q) :
      (F.map r.op.toLoc).toFunctor.map
          ((F.mapComp' (p j).op.toLoc a.op.toLoc q.op.toLoc
            (toLoc_comp ha)).inv.toNatTrans.app N₂) ≫
        (F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app N₂ =
        (F.mapComp' a.op.toLoc r.op.toLoc (r ≫ a).op.toLoc
          (toLoc_comp rfl)).inv.toNatTrans.app _ ≫
        (F.mapComp' (p j).op.toLoc (r ≫ a).op.toLoc (r ≫ q).op.toLoc
          (toLoc_comp (by rw [Category.assoc, ha]))).inv.toNatTrans.app N₂ := by
    rw [← mapComp'_triple_inv (F := F) (p j) a r q (r ≫ a) (r ≫ q) ha rfl rfl N₂]
    simp [← Functor.map_comp_assoc]
  rw [reassoc_of% (hL j₁ a₁ ha₁), reassoc_of% (hL j₂ a₂ ha₂), hR j₁ a₁ ha₁, hR j₂ a₂ ha₂,
    map_comp_conj_eq γ ψ hψ r b₁ ha₁ hb₁, map_comp_conj_eq γ ψ hψ r b₂ ha₂ hb₂]
  rw [← cancel_mono ((F.mapComp' (u j₂ k₂ ≫ p j₂).op.toLoc b₂.op.toLoc (r ≫ q).op.toLoc
    (toLoc_comp (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]))).hom.toNatTrans.app N₂)]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  rw [hγ]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Cat.Hom.comp_toFunctor,
    Functor.comp_obj, Category.comp_id]

/-- The component isomorphism `(u j k)^* (M j) ≅ D.obj ⟨j, k⟩` extracted from `α j`, with explicit
domain and codomain types to avoid transparency mismatches during rewriting. -/
private def αIso (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (F.map (u j k).op.toLoc).toFunctor.obj (M j) ≅ D.obj ⟨j, k⟩ where
  hom := (α j).hom.hom k
  inv := (α j).inv.hom k
  hom_inv_id := congr($(Iso.hom_inv_id (α j)).hom k)
  inv_hom_id := congr($(Iso.inv_hom_id (α j)).hom k)

/-- Given a descent datum `D` for `u j k ≫ p j`, objects `M j` on `Y j`, and isomorphisms
`α j : (toDescentData (u j)).obj (M j) ≅ restrictDatum D j`, this is the local transition map
`r^* a₁^* M j₁ ⟶ r^* a₂^* M j₂` obtained from factorizations `b₁ ≫ u j₁ k₁ = r ≫ a₁` and
`b₂ ≫ u j₂ k₂ = r ≫ a₂`. -/
private def localHom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    (F.map r.op.toLoc).toFunctor.obj ((F.map a₁.op.toLoc).toFunctor.obj (M j₁)) ⟶
      (F.map r.op.toLoc).toFunctor.obj ((F.map a₂.op.toLoc).toFunctor.obj (M j₂)) :=
  (F.mapComp' a₁.op.toLoc r.op.toLoc (r ≫ a₁).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app (M j₁) ≫
    (F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc (r ≫ a₁).op.toLoc
      (toLoc_comp hb₁)).hom.toNatTrans.app (M j₁) ≫
    (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
    D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) ≫
    (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv ≫
    (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc (r ≫ a₂).op.toLoc
      (toLoc_comp hb₂)).inv.toNatTrans.app (M j₂) ≫
    (F.mapComp' a₂.op.toLoc r.op.toLoc (r ≫ a₂).op.toLoc (toLoc_comp rfl)).hom.toNatTrans.app (M j₂)

private lemma localHom_unique (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ k₁' : ι j₁} {k₂ k₂' : ι j₂}
    (b₁ : Z ⟶ X j₁ k₁) (b₁' : Z ⟶ X j₁ k₁') (b₂ : Z ⟶ X j₂ k₂) (b₂' : Z ⟶ X j₂ k₂')
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₁' : b₁' ≫ u j₁ k₁' = r ≫ a₁)
    (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) (hb₂' : b₂' ≫ u j₂ k₂' = r ≫ a₂) :
    localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ = localHom D M α ha₁ ha₂ r b₁' b₂' hb₁' hb₂' := by
  have h1 : (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
      D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₁, k₁'⟩) b₁ b₁'
        (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
        (by rw [← Category.assoc, hb₁', Category.assoc, ha₁]) =
      ((F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc (r ≫ a₁).op.toLoc
          (toLoc_comp hb₁)).inv.toNatTrans.app (M j₁) ≫
        (F.mapComp' (u j₁ k₁').op.toLoc b₁'.op.toLoc (r ≫ a₁).op.toLoc
          (toLoc_comp hb₁')).hom.toNatTrans.app (M j₁)) ≫
      (F.map b₁'.op.toLoc).toFunctor.map (αIso D M α j₁ k₁').hom := by
    have h := (α j₁).hom.comm (r ≫ a₁) b₁ b₁' hb₁ hb₁'
    dsimp only [toDescentData, DescentData.ofObj, restrictDatum] at h
    simpa only [αIso, Category.assoc, ha₁] using h
  have h2 : (F.map b₂'.op.toLoc).toFunctor.map (αIso D M α j₂ k₂').inv ≫
      ((F.mapComp' (u j₂ k₂').op.toLoc b₂'.op.toLoc (r ≫ a₂).op.toLoc
          (toLoc_comp hb₂')).inv.toNatTrans.app (M j₂) ≫
        (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc (r ≫ a₂).op.toLoc
          (toLoc_comp hb₂)).hom.toNatTrans.app (M j₂)) =
      D.hom (r ≫ q) (i₁ := ⟨j₂, k₂'⟩) (i₂ := ⟨j₂, k₂⟩) b₂' b₂
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) ≫
      (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv := by
    have h := (α j₂).inv.comm (r ≫ a₂) b₂' b₂ hb₂' hb₂
    dsimp only [toDescentData, DescentData.ofObj, restrictDatum] at h
    simpa only [αIso, Category.assoc, ha₂] using h
  have hD : D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) =
      D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₁, k₁'⟩) b₁ b₁'
        (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
        (by rw [← Category.assoc, hb₁', Category.assoc, ha₁]) ≫
      D.hom (r ≫ q) (i₁ := ⟨j₁, k₁'⟩) (i₂ := ⟨j₂, k₂'⟩) b₁' b₂'
        (by rw [← Category.assoc, hb₁', Category.assoc, ha₁])
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂]) ≫
      D.hom (r ≫ q) (i₁ := ⟨j₂, k₂'⟩) (i₂ := ⟨j₂, k₂⟩) b₂' b₂
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) := by
    simp [DescentData.hom_comp]
  unfold localHom
  rw [hD]
  simp only [Category.assoc]
  rw [reassoc_of% h1, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, ← reassoc_of% h2,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

private lemma localHom_self (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k : ι j} (b : Z ⟶ X j k) (hb : b ≫ u j k = r ≫ a) :
    localHom D M α ha ha r b b hb hb = 𝟙 _ := by
  unfold localHom
  rw [D.hom_self _ (i := ⟨j, k⟩) _ (by rw [← Category.assoc, hb, Category.assoc, ha]),
    Category.id_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  rfl

private lemma localHom_comp (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ j₃ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂} {a₃ : W ⟶ Y j₃}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (ha₃ : a₃ ≫ p j₃ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} {k₃ : ι j₃}
    (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂) (b₃ : Z ⟶ X j₃ k₃)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂)
    (hb₃ : b₃ ≫ u j₃ k₃ = r ≫ a₃) :
    localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ ≫ localHom D M α ha₂ ha₃ r b₂ b₃ hb₂ hb₃ =
      localHom D M α ha₁ ha₃ r b₁ b₃ hb₁ hb₃ := by
  unfold localHom
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp, D.hom_comp_assoc]

private lemma localHom_precomp (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z Z' : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (g : Z' ⟶ Z) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    localHom D M α ha₁ ha₂ (g ≫ r) (g ≫ b₁) (g ≫ b₂)
        (by rw [Category.assoc, hb₁, Category.assoc])
        (by rw [Category.assoc, hb₂, Category.assoc]) =
      pullHom (localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂) g (g ≫ r) (g ≫ r) rfl rfl := by
  unfold localHom
  dsimp only [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_app_assoc a₁.op.toLoc r.op.toLoc g.op.toLoc
    (r ≫ a₁).op.toLoc (g ≫ r).op.toLoc ((g ≫ r) ≫ a₁).op.toLoc
    (toLoc_comp rfl) (toLoc_comp rfl) (toLoc_comp rfl) (M j₁)]
  rw [F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc (u j₁ k₁).op.toLoc b₁.op.toLoc g.op.toLoc
    (r ≫ a₁).op.toLoc (g ≫ b₁).op.toLoc ((g ≫ r) ≫ a₁).op.toLoc
    (toLoc_comp hb₁) (toLoc_comp rfl) (toLoc_comp (Category.assoc g r a₁).symm) (M j₁)]
  rw [← F.mapComp'_naturality_2_assoc b₁.op.toLoc g.op.toLoc (g ≫ b₁).op.toLoc (toLoc_comp rfl)
    (αIso D M α j₁ k₁).hom]
  rw [← D.pullHom_hom g (r ≫ q) (g ≫ r ≫ q) rfl
    (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
    (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
    (by rw [← Category.assoc, hb₂, Category.assoc, ha₂])
    (g ≫ b₁) (g ≫ b₂) rfl rfl]
  dsimp only [pullHom]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rw [← F.mapComp'_naturality_2_assoc b₂.op.toLoc g.op.toLoc (g ≫ b₂).op.toLoc (toLoc_comp rfl)
    (αIso D M α j₂ k₂).inv]
  simp only [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rw [← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (u j₂ k₂).op.toLoc b₂.op.toLoc
    g.op.toLoc (r ≫ a₂).op.toLoc (g ≫ b₂).op.toLoc ((g ≫ r) ≫ a₂).op.toLoc
    (toLoc_comp hb₂) (toLoc_comp rfl) (toLoc_comp (Category.assoc g r a₂).symm) (M j₂)]
  rw [F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app a₂.op.toLoc r.op.toLoc g.op.toLoc
    (r ≫ a₂).op.toLoc (g ≫ r).op.toLoc ((g ≫ r) ≫ a₂).op.toLoc
    (toLoc_comp rfl) (toLoc_comp rfl) (toLoc_comp (Category.assoc g r a₂).symm) (M j₂)]

/-- Existence and uniqueness of the glued transition morphism `a₁^* (M j₁) ⟶ a₂^* (M j₂)` on `W`
matching `localHom` over the covering intersection sieve of `a₁^* (u j₁)` and `a₂^* (u j₂)`. -/
private lemma existsUnique_gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) :
    ∃! φ : (F.map a₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (M j₂),
      ∀ ⦃Z : C⦄ (r : Z ⟶ W) {k₁ : ι j₁} {k₂ : ι j₂}
        (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
        (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂),
        (F.map r.op.toLoc).toFunctor.map φ = localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ := by
  let R : Sieve W :=
    Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
      Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂))
  have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
    (J.pullback_stable a₂ (hu j₂))
  have fac₁ {Z : C} {r : Z ⟶ W} (hr : R r) : ∃ k₁ b₁, b₁ ≫ u j₁ k₁ = r ≫ a₁ := by
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    exact ⟨k₁, b₁, hb₁⟩
  have fac₂ {Z : C} {r : Z ⟶ W} (hr : R r) : ∃ k₂ b₂, b₂ ≫ u j₂ k₂ = r ≫ a₂ := by
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
    exact ⟨k₂, b₂, hb₂⟩
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_map_eq_of_isPrestack hR
    (fun Z r hr ↦ localHom D M α ha₁ ha₂ r (fac₁ hr).choose_spec.choose
      (fac₂ hr).choose_spec.choose (fac₁ hr).choose_spec.choose_spec
      (fac₂ hr).choose_spec.choose_spec)
    (fun Z' Z g r hr ↦ by
      rw [← localHom_precomp D M α ha₁ ha₂ g r (fac₁ hr).choose_spec.choose
        (fac₂ hr).choose_spec.choose (fac₁ hr).choose_spec.choose_spec
        (fac₂ hr).choose_spec.choose_spec]
      exact localHom_unique D M α ha₁ ha₂ (g ≫ r) _ _ _ _ _ _ _ _)
  refine ⟨φ, fun Z r k₁ k₂ b₁ b₂ hb₁ hb₂ ↦ ?_, fun ψ hψ ↦ huniq ψ fun Z r hr ↦
    hψ r _ _ (fac₁ hr).choose_spec.choose_spec (fac₂ hr).choose_spec.choose_spec⟩
  have hr : R r := ⟨⟨_, b₁, _, ⟨k₁⟩, hb₁⟩, ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩⟩
  exact (hφ r hr).trans (localHom_unique D M α ha₁ ha₂ r _ b₁ _ b₂ _ hb₁ _ hb₂)

/-- The glued transition morphism `a₁^* (M j₁) ⟶ a₂^* (M j₂)` on `W`. -/
private noncomputable def gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) :
    (F.map a₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (M j₂) :=
  (existsUnique_gluedHom hu D M α q a₁ a₂ ha₁ ha₂).choose

private lemma map_gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    (F.map r.op.toLoc).toFunctor.map (gluedHom hu D M α q a₁ a₂ ha₁ ha₂) =
      localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ :=
  (existsUnique_gluedHom hu D M α q a₁ a₂ ha₁ ha₂).choose_spec.1 r b₁ b₂ hb₁ hb₂

/-- The descent datum along `p` assembled from the descended objects `M j` and transition
isomorphisms `gluedHom`. -/
private noncomputable def gluedDatum (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) :
    F.DescentData p where
  obj := M
  hom _ q _ _ a₁ a₂ ha₁ ha₂ := gluedHom hu D M α q a₁ a₂ ha₁ ha₂
  pullHom_hom W' W g q q' hq j₁ j₂ a₁ a₂ ha₁ ha₂ ga₁ ga₂ hga₁ hga₂ := by
    subst hga₁ hga₂ hq
    let R : Sieve W' :=
      Sieve.pullback (g ≫ a₁) (Sieve.ofArrows (X j₁) (u j₁)) ⊓
        Sieve.pullback (g ≫ a₂) (Sieve.ofArrows (X j₂) (u j₂))
    have hR : R ∈ J W' := J.intersection_covering (J.pullback_stable _ (hu j₁))
      (J.pullback_stable _ (hu j₂))
    refine hom_ext_of_isPrestack hR fun Z r hr ↦ ?_
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
    rw [map_gluedHom hu D M α (g ≫ q) (g ≫ a₁) (g ≫ a₂) _ _ r b₁ b₂ hb₁ hb₂]
    have h1 := map_gluedHom hu D M α q a₁ a₂ ha₁ ha₂ (r ≫ g) b₁ b₂
      (by rw [hb₁, Category.assoc]) (by rw [hb₂, Category.assoc])
    dsimp only [pullHom]
    simp only [Functor.map_comp]
    rw [← cancel_epi ((F.mapComp' (g ≫ a₁).op.toLoc r.op.toLoc (r ≫ g ≫ a₁).op.toLoc
      (toLoc_comp rfl)).hom.toNatTrans.app (M j₁)),
      ← cancel_mono ((F.mapComp' (g ≫ a₂).op.toLoc r.op.toLoc (r ≫ g ≫ a₂).op.toLoc
      (toLoc_comp rfl)).inv.toNatTrans.app (M j₂))]
    unfold localHom
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    have hL := mapComp'_triple_hom (F := F) a₁ g r (g ≫ a₁) (r ≫ g) (r ≫ g ≫ a₁)
      rfl rfl rfl (M j₁)
    have hR := mapComp'_triple_inv (F := F) a₂ g r (g ≫ a₂) (r ≫ g) (r ≫ g ≫ a₂)
      rfl rfl rfl (M j₂)
    rw [← reassoc_of% hL, ← hR]
    rw [← Functor.map_comp_assoc ((F.map r.op.toLoc).toFunctor)
        ((F.mapComp' a₁.op.toLoc g.op.toLoc (g ≫ a₁).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app
          (M j₁)),
      Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id, Category.id_comp,
      ← Functor.map_comp_assoc ((F.map r.op.toLoc).toFunctor)
        ((F.mapComp' a₂.op.toLoc g.op.toLoc (g ≫ a₂).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app
          (M j₂)),
      Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id, Category.id_comp]
    rw [F.mapComp'_naturality_2_assoc g.op.toLoc r.op.toLoc (r ≫ g).op.toLoc (toLoc_comp rfl)
      (gluedHom hu D M α q a₁ a₂ ha₁ ha₂), h1]
    unfold localHom
    have haux : ∀ x₁ x₂
        (hx₁ : (r ≫ g) ≫ a₁ = x₁) (hx₂ : (r ≫ g) ≫ a₂ = x₂)
        (hb₁' : b₁ ≫ u j₁ k₁ = x₁) (hb₂' : b₂ ≫ u j₂ k₂ = x₂),
        (F.mapComp' a₁.op.toLoc (r ≫ g).op.toLoc (r ≫ g ≫ a₁).op.toLoc
            (toLoc_comp (Category.assoc r g a₁))).hom.toNatTrans.app (M j₁) ≫
          ((F.mapComp' a₁.op.toLoc (r ≫ g).op.toLoc x₁.op.toLoc
              (toLoc_comp hx₁)).inv.toNatTrans.app (M j₁) ≫
            (F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc x₁.op.toLoc
              (toLoc_comp hb₁')).hom.toNatTrans.app (M j₁) ≫
            (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
            D.hom (r ≫ g ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
              (by rw [← Category.assoc, hb₁, Category.assoc, Category.assoc, ha₁])
              (by rw [← Category.assoc, hb₂, Category.assoc, Category.assoc, ha₂]) ≫
            (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv ≫
            (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc x₂.op.toLoc
              (toLoc_comp hb₂')).inv.toNatTrans.app (M j₂) ≫
            (F.mapComp' a₂.op.toLoc (r ≫ g).op.toLoc x₂.op.toLoc
              (toLoc_comp hx₂)).hom.toNatTrans.app (M j₂)) ≫
          (F.mapComp' a₂.op.toLoc (r ≫ g).op.toLoc (r ≫ g ≫ a₂).op.toLoc
            (toLoc_comp (Category.assoc r g a₂))).inv.toNatTrans.app (M j₂) =
          (F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc (r ≫ g ≫ a₁).op.toLoc
            (toLoc_comp hb₁)).hom.toNatTrans.app (M j₁) ≫
          (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
          D.hom (r ≫ g ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
            (by rw [← Category.assoc, hb₁, Category.assoc, Category.assoc, ha₁])
            (by rw [← Category.assoc, hb₂, Category.assoc, Category.assoc, ha₂]) ≫
          (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv ≫
          (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc (r ≫ g ≫ a₂).op.toLoc
            (toLoc_comp hb₂)).inv.toNatTrans.app (M j₂) := by
      rintro x₁ x₂ hx₁ hx₂ hb₁' hb₂'
      have e₁ : r ≫ g ≫ a₁ = x₁ := (Category.assoc r g a₁).symm.trans hx₁
      have e₂ : r ≫ g ≫ a₂ = x₂ := (Category.assoc r g a₂).symm.trans hx₂
      subst e₁ e₂
      simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
        Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    have hq : (r ≫ g) ≫ q = r ≫ g ≫ q := Category.assoc r g q
    have haux' := haux ((r ≫ g) ≫ a₁) ((r ≫ g) ≫ a₂) rfl rfl (by rw [hb₁, Category.assoc])
      (by rw [hb₂, Category.assoc])
    simpa only [Category.assoc, hq] using haux'
  hom_self W q j a ha := by
    have hR : Sieve.pullback a (Sieve.ofArrows (X j) (u j)) ∈ J W :=
      J.pullback_stable a (hu j)
    refine hom_ext_of_isPrestack hR fun Z r hr ↦ ?_
    obtain ⟨_, b, _, ⟨k⟩, hb⟩ := hr
    rw [Functor.map_id, map_gluedHom hu D M α q a a ha ha r b b hb hb,
      localHom_self D M α ha r b hb]
  hom_comp W q j₁ j₂ j₃ a₁ a₂ a₃ ha₁ ha₂ ha₃ := by
    let R : Sieve W :=
      Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
        (Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂)) ⊓
          Sieve.pullback a₃ (Sieve.ofArrows (X j₃) (u j₃)))
    have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
      (J.intersection_covering (J.pullback_stable a₂ (hu j₂)) (J.pullback_stable a₃ (hu j₃)))
    refine hom_ext_of_isPrestack hR fun Z r hr ↦ ?_
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2.1
    obtain ⟨_, b₃, _, ⟨k₃⟩, hb₃⟩ := hr.2.2
    rw [Functor.map_comp,
      map_gluedHom hu D M α q a₁ a₂ ha₁ ha₂ r b₁ b₂ hb₁ hb₂,
      map_gluedHom hu D M α q a₂ a₃ ha₂ ha₃ r b₂ b₃ hb₂ hb₃,
      map_gluedHom hu D M α q a₁ a₃ ha₁ ha₃ r b₁ b₃ hb₁ hb₃,
      localHom_comp D M α ha₁ ha₂ ha₃ r b₁ b₂ b₃ hb₁ hb₂ hb₃]

/-- Explicit formula for `gluedHom` evaluated on morphisms already factored as `f₁ ≫ u j₁ k₁` and
`f₂ ≫ u j₂ k₂`. -/
private lemma gluedHom_comp (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {jk₁ jk₂ : Σ j, ι j}
    (f₁ : W ⟶ X jk₁.1 jk₁.2) (f₂ : W ⟶ X jk₂.1 jk₂.2)
    (hf₁ : f₁ ≫ u jk₁.1 jk₁.2 ≫ p jk₁.1 = q) (hf₂ : f₂ ≫ u jk₂.1 jk₂.2 ≫ p jk₂.1 = q) :
    gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2)
        (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂]) =
      (F.mapComp' (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc
        (toLoc_comp rfl)).hom.toNatTrans.app (M jk₁.1) ≫
      (F.map f₁.op.toLoc).toFunctor.map (αIso D M α jk₁.1 jk₁.2).hom ≫
      D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
      (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
        (toLoc_comp rfl)).inv.toNatTrans.app (M jk₂.1) := by
  have ha₁ : (f₁ ≫ u jk₁.1 jk₁.2) ≫ p jk₁.1 = q := by rw [Category.assoc, hf₁]
  have ha₂ : (f₂ ≫ u jk₂.1 jk₂.2) ≫ p jk₂.1 = q := by rw [Category.assoc, hf₂]
  have hglued := map_gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂
    (𝟙 W) f₁ f₂ (by simp) (by simp)
  rw [← pullHom_id (gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂)]
  dsimp only [pullHom]
  rw [hglued]
  unfold localHom
  have haux : ∀ (x₁ : W ⟶ Y jk₁.1) (x₂ : W ⟶ Y jk₂.1) (zq : W ⟶ S)
      (hx₁ : 𝟙 W ≫ f₁ ≫ u jk₁.1 jk₁.2 = x₁) (hx₂ : 𝟙 W ≫ f₂ ≫ u jk₂.1 jk₂.2 = x₂)
      (_ : 𝟙 W ≫ q = zq)
      (hf₁' : f₁ ≫ u jk₁.1 jk₁.2 = x₁) (hf₂' : f₂ ≫ u jk₂.1 jk₂.2 = x₂)
      (h1 : f₁ ≫ u jk₁.1 jk₁.2 ≫ p jk₁.1 = zq) (h2 : f₂ ≫ u jk₂.1 jk₂.2 ≫ p jk₂.1 = zq),
      (F.mapComp' (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc (𝟙 W).op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc
          (by simp)).hom.toNatTrans.app (M jk₁.1) ≫
        ((F.mapComp' (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc (𝟙 W).op.toLoc x₁.op.toLoc
            (toLoc_comp hx₁)).inv.toNatTrans.app (M jk₁.1) ≫
          (F.mapComp' (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc x₁.op.toLoc
            (toLoc_comp hf₁')).hom.toNatTrans.app (M jk₁.1) ≫
          (F.map f₁.op.toLoc).toFunctor.map (αIso D M α jk₁.1 jk₁.2).hom ≫
          D.hom zq (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ h1 h2 ≫
          (F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
          (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc x₂.op.toLoc
            (toLoc_comp hf₂')).inv.toNatTrans.app (M jk₂.1) ≫
          (F.mapComp' (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc (𝟙 W).op.toLoc x₂.op.toLoc
            (toLoc_comp hx₂)).hom.toNatTrans.app (M jk₂.1)) ≫
        (F.mapComp' (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc (𝟙 W).op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
          (by simp)).inv.toNatTrans.app (M jk₂.1) =
        (F.mapComp' (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc
          (toLoc_comp rfl)).hom.toNatTrans.app (M jk₁.1) ≫
        (F.map f₁.op.toLoc).toFunctor.map (αIso D M α jk₁.1 jk₁.2).hom ≫
        D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
        (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
          (toLoc_comp rfl)).inv.toNatTrans.app (M jk₂.1) := by
    rintro x₁ x₂ zq hx₁ hx₂ hzq hf₁' hf₂' h1 h2
    have e₁ : f₁ ≫ u jk₁.1 jk₁.2 = x₁ := (Category.id_comp _).symm.trans hx₁
    have e₂ : f₂ ≫ u jk₂.1 jk₂.2 = x₂ := (Category.id_comp _).symm.trans hx₂
    have eq : q = zq := (Category.id_comp _).symm.trans hzq
    subst e₁ e₂ eq
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  exact haux _ _ _ rfl rfl rfl (by simp) (by simp) _ _

/-- Combining the descent isomorphism `β : toDescentData p N ≅ gluedDatum ...` with the local
isomorphisms `α j : toDescentData (u j) (M j) ≅ restrictDatum D j` produces an isomorphism
`(toDescentData (u j k ≫ p j)).obj N ≅ D`. -/
private noncomputable def descendIso (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α) :
    (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N ≅ D :=
  let βIso (j : κ) : (F.map (p j).op.toLoc).toFunctor.obj N ≅ M j :=
    { hom := β.hom.hom j
      inv := β.inv.hom j
      hom_inv_id := congr($(β.hom_inv_id).hom j)
      inv_hom_id := congr($(β.inv_hom_id).hom j) }
  DescentData.isoMk
    (fun jk ↦ (Cat.Hom.toNatIso (F.mapComp' (p jk.1).op.toLoc (u jk.1 jk.2).op.toLoc
        (u jk.1 jk.2 ≫ p jk.1).op.toLoc (toLoc_comp rfl))).app N ≪≫
      (F.map (u jk.1 jk.2).op.toLoc).toFunctor.mapIso (βIso jk.1) ≪≫
      αIso D M α jk.1 jk.2)
    (fun W q jk₁ jk₂ f₁ f₂ hf₁ hf₂ ↦ by
      have ha₁ : (f₁ ≫ u jk₁.1 jk₁.2) ≫ p jk₁.1 = q := by rw [Category.assoc, hf₁]
      have ha₂ : (f₂ ≫ u jk₂.1 jk₂.2) ≫ p jk₂.1 = q := by rw [Category.assoc, hf₂]
      have hβ : (F.map (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc).toFunctor.map (βIso jk₁.1).hom ≫
          gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂ =
          ((F.mapComp' (p jk₁.1).op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc q.op.toLoc
              (toLoc_comp ha₁)).inv.toNatTrans.app N ≫
            (F.mapComp' (p jk₂.1).op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc q.op.toLoc
              (toLoc_comp ha₂)).hom.toNatTrans.app N) ≫
          (F.map (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc).toFunctor.map (βIso jk₂.1).hom := by
        have h := β.hom.comm q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂
        dsimp only [toDescentData, DescentData.ofObj, gluedDatum] at h
        exact h
      rw [gluedHom_comp hu D M α q f₁ f₂ hf₁ hf₂] at hβ
      dsimp only [toDescentData, DescentData.ofObj, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Iso.app_hom, Cat.Hom.toNatIso_hom, Functor.map_comp, Category.assoc]
      have hL := F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app (p jk₁.1).op.toLoc
        (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc (u jk₁.1 jk₁.2 ≫ p jk₁.1).op.toLoc
        (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc q.op.toLoc
        (toLoc_comp rfl) (toLoc_comp rfl) (toLoc_comp ha₁) N
      have hR := F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app (p jk₂.1).op.toLoc
        (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (u jk₂.1 jk₂.2 ≫ p jk₂.1).op.toLoc
        (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc q.op.toLoc
        (toLoc_comp rfl) (toLoc_comp rfl) (toLoc_comp ha₂) N
      rw [← cancel_epi ((F.mapComp' (u jk₁.1 jk₁.2 ≫ p jk₁.1).op.toLoc f₁.op.toLoc q.op.toLoc
        (toLoc_comp hf₁)).hom.toNatTrans.app N),
        ← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv),
        ← cancel_mono ((F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc
          (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc (toLoc_comp rfl)).inv.toNatTrans.app (M jk₂.1))]
      simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      rw [← reassoc_of% hL, ← F.mapComp'_naturality_1_assoc (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc
        (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc (toLoc_comp rfl) (βIso jk₁.1).hom,
        Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      rw [hβ, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      rw [← reassoc_of% hR, ← F.mapComp'_naturality_1_assoc (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc
        (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc (toLoc_comp rfl) (βIso jk₂.1).hom,
        Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
        Category.id_comp, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id])

end OfComp

/-- **Transitivity of `IsPrestackFor` along `J`-covering compositions.** If `F` is a prestack for
`J`, `F` satisfies descent of morphisms for `p : ∀ j, Y j ⟶ S`, and each `u j : ∀ k, X j k ⟶ Y j`
is a `J`-covering family, then `F` satisfies descent of morphisms for the composite family
`u j k ≫ p j`. -/
theorem IsPrestackFor.of_comp {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S} (hp : F.IsPrestackFor (.ofArrows Y p))
    {ι : κ → Type t'} {X : ∀ j, ι j → C} (u : ∀ j k, X j k ⟶ Y j)
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j)) :
    F.IsPrestackFor (.ofArrows (fun jk : Σ j, ι j ↦ X jk.1 jk.2)
      (fun jk ↦ u jk.1 jk.2 ≫ p jk.1)) := by
  rw [isPrestackFor_ofArrows_iff] at hp ⊢
  obtain ⟨hff⟩ := hp
  have : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).Faithful :=
    { map_injective {N₁ N₂ φ₁ φ₂} hφ := by
        refine hff.map_injective (DescentData.hom_ext fun j ↦ ?_)
        refine (F.fullyFaithfulToDescentData (u j) (hu j)).map_injective
          (DescentData.hom_ext fun k ↦ ?_)
        have hk : (F.map (u j k ≫ p j).op.toLoc).toFunctor.map φ₁ =
            (F.map (u j k ≫ p j).op.toLoc).toFunctor.map φ₂ := congr($(hφ).hom ⟨j, k⟩)
        let mc := F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (OfComp.toLoc_comp rfl)
        have hnat₁ : (F.map (u j k ≫ p j).op.toLoc).toFunctor.map φ₁ ≫ mc.hom.toNatTrans.app N₂ =
            mc.hom.toNatTrans.app N₁ ≫
              (F.map (u j k).op.toLoc).toFunctor.map ((F.map (p j).op.toLoc).toFunctor.map φ₁) :=
          mc.hom.toNatTrans.naturality φ₁
        have hnat₂ : (F.map (u j k ≫ p j).op.toLoc).toFunctor.map φ₂ ≫ mc.hom.toNatTrans.app N₂ =
            mc.hom.toNatTrans.app N₁ ≫
              (F.map (u j k).op.toLoc).toFunctor.map ((F.map (p j).op.toLoc).toFunctor.map φ₂) :=
          mc.hom.toNatTrans.naturality φ₂
        change (F.map (u j k).op.toLoc).toFunctor.map ((F.map (p j).op.toLoc).toFunctor.map φ₁) =
          (F.map (u j k).op.toLoc).toFunctor.map ((F.map (p j).op.toLoc).toFunctor.map φ₂)
        rw [← cancel_epi (mc.hom.toNatTrans.app N₁), ← hnat₁, ← hnat₂, hk] }
  have : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).Full :=
    { map_surjective {N₁ N₂} γ := by
        let ψ (j : κ) : (F.map (p j).op.toLoc).toFunctor.obj N₁ ⟶
            (F.map (p j).op.toLoc).toFunctor.obj N₂ :=
          (F.fullyFaithfulToDescentData (u j) (hu j)).preimage (OfComp.restrictOfObjHom γ j)
        have hψ (j : κ) (k : ι j) : (F.map (u j k).op.toLoc).toFunctor.map (ψ j) =
            (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
                (OfComp.toLoc_comp rfl)).inv.toNatTrans.app N₁ ≫
              OfComp.γHom γ j k ≫
              (F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
                (OfComp.toLoc_comp rfl)).hom.toNatTrans.app N₂ :=
          congr($((F.fullyFaithfulToDescentData (u j) (hu j)).map_preimage
            (OfComp.restrictOfObjHom γ j)).hom k)
        let ψ_data : (F.toDescentData p).obj N₁ ⟶ (F.toDescentData p).obj N₂ :=
          { hom := ψ
            comm W q j₁ j₂ a₁ a₂ ha₁ ha₂ := by
              let R : Sieve W :=
                Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
                  Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂))
              have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
                (J.pullback_stable a₂ (hu j₂))
              refine hom_ext_of_isPrestack hR fun Z r hr ↦ ?_
              obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
              obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
              exact OfComp.prestack_of_comp_comm_local γ ψ hψ ha₁ ha₂ r b₁ b₂ hb₁ hb₂ }
        refine ⟨hff.preimage ψ_data, DescentData.hom_ext fun ⟨j, k⟩ ↦ ?_⟩
        have hpre : (F.map (p j).op.toLoc).toFunctor.map (hff.preimage ψ_data) = ψ j :=
          congr($(hff.map_preimage ψ_data).hom j)
        let mc := F.mapComp' (p j).op.toLoc (u j k).op.toLoc (u j k ≫ p j).op.toLoc
          (OfComp.toLoc_comp rfl)
        have hnat : (F.map (u j k ≫ p j).op.toLoc).toFunctor.map (hff.preimage ψ_data) ≫
              mc.hom.toNatTrans.app N₂ =
            mc.hom.toNatTrans.app N₁ ≫
              (F.map (u j k).op.toLoc).toFunctor.map
                ((F.map (p j).op.toLoc).toFunctor.map (hff.preimage ψ_data)) :=
          mc.hom.toNatTrans.naturality (hff.preimage ψ_data)
        change (F.map (u j k ≫ p j).op.toLoc).toFunctor.map (hff.preimage ψ_data) =
          OfComp.γHom γ j k
        rw [← cancel_epi (mc.inv.toNatTrans.app N₁), ← cancel_mono (mc.hom.toNatTrans.app N₂),
          Category.assoc, Category.assoc, ← hψ j k, ← hpre, hnat,
          Cat.Hom.inv_hom_id_toNatTrans_app_assoc] }
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- **Transitivity of effective descent (`IsStackFor`) along `J`-covering compositions.** If `F`
is a prestack for `J`, `F` has effective descent for `p : ∀ j, Y j ⟶ S`, and each
`u j : ∀ k, X j k ⟶ Y j` is a `J`-covering family for which `F` has effective descent, then `F`
has effective descent for the composite family `u j k ≫ p j`. -/
theorem IsStackFor.of_comp {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S} (hp : F.IsStackFor (.ofArrows Y p))
    {ι : κ → Type t'} {X : ∀ j, ι j → C} (u : ∀ j k, X j k ⟶ Y j)
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (hu_stack : ∀ j, F.IsStackFor (.ofArrows (X j) (u j))) :
    F.IsStackFor (.ofArrows (fun jk : Σ j, ι j ↦ X jk.1 jk.2) (fun jk ↦ u jk.1 jk.2 ≫ p jk.1)) := by
  have hpre := IsPrestackFor.of_comp F hp.isPrestackFor u hu
  rw [isPrestackFor_ofArrows_iff] at hpre
  obtain ⟨hff⟩ := hpre
  have := hff.full
  have := hff.faithful
  rw [isStackFor_ofArrows_iff] at hp ⊢
  have hu_eqv (j : κ) : (F.toDescentData (u j)).IsEquivalence :=
    (isStackFor_ofArrows_iff F (u j)).1 (hu_stack j)
  have : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).EssSurj := ⟨fun D ↦ by
    let M (j : κ) := (F.toDescentData (u j)).objPreimage (OfComp.restrictDatum D j)
    let α (j : κ) := (F.toDescentData (u j)).objObjPreimageIso (OfComp.restrictDatum D j)
    let Dp := OfComp.gluedDatum hu D M α
    let N := (F.toDescentData p).objPreimage Dp
    let β := (F.toDescentData p).objObjPreimageIso Dp
    exact ⟨N, ⟨OfComp.descendIso hu D M α N β⟩⟩⟩
  exact {}

/-- **Base-change locality of effective descent.** If `F` is a prestack for `J`, `f` and `v` are
`J`-covering families of `S`, `F` has effective descent for `v`, and `F` has effective descent for
the pullback of `f` along every `v a`, then `F` has effective descent for `f`. -/
theorem IsStackFor.of_pullback [HasPullbacks C] {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ S} (hf : Sieve.ofArrows X f ∈ J S)
    {κ : Type t'} {V : κ → C} {v : ∀ a, V a ⟶ S} (hv : Sieve.ofArrows V v ∈ J S)
    (hv_stack : F.IsStackFor (.ofArrows V v))
    (hf' : ∀ a, F.IsStackFor (.ofArrows (fun i ↦ pullback (f i) (v a))
      (fun i ↦ pullback.snd (f i) (v a)))) :
    F.IsStackFor (.ofArrows X f) := by
  have hu (a : κ) : Sieve.ofArrows (fun i ↦ pullback (f i) (v a))
      (fun i ↦ pullback.snd (f i) (v a)) ∈ J (V a) := by
    refine J.superset_covering ?_ (J.pullback_stable (v a) hf)
    rintro W g ⟨_, r, _, ⟨i⟩, fac⟩
    exact ⟨_, pullback.lift r g fac, _, ⟨i⟩, pullback.lift_snd _ _ _⟩
  have hcomp := IsStackFor.of_comp F hv_stack (fun a i ↦ pullback.snd (f i) (v a)) hu hf'
  let R₁ : Sieve S := Sieve.ofArrows (fun ai : Σ _ : κ, ι ↦ pullback (f ai.2) (v ai.1))
    (fun ai ↦ pullback.snd (f ai.2) (v ai.1) ≫ v ai.1)
  have hR₁_mem : R₁ ∈ J S := by
    refine J.transitive hv _ fun W g hg ↦ ?_
    obtain ⟨_, r, _, ⟨a⟩, rfl⟩ := hg
    refine J.superset_covering ?_ (J.pullback_stable r (hu a))
    rintro Z t ⟨_, s, _, ⟨i⟩, fac⟩
    exact ⟨pullback (f i) (v a), s, pullback.snd (f i) (v a) ≫ v a,
      Presieve.ofArrows.mk (⟨a, i⟩ : Σ _ : κ, ι), by rw [← Category.assoc, fac, Category.assoc]⟩
  have hle : R₁ ≤ Sieve.ofArrows X f := by
    rintro W g ⟨_, r, _, ⟨⟨a, i⟩⟩, rfl⟩
    exact ⟨X i, r ≫ pullback.fst (f i) (v a), f i, Presieve.ofArrows.mk i,
      by simp [pullback.condition]⟩
  rw [← IsStackFor_generate_iff] at hcomp ⊢
  exact hcomp.of_le' F hR₁_mem hle

/-- Pulling back `(Sieve.overEquiv (Over.mk (𝟙 S))).symm R` along `g : Y ⟶ Over.mk (𝟙 S)` and
applying `Sieve.overEquiv Y` yields `R.pullback g.left`. -/
private lemma overEquiv_pullback_overEquiv_symm {S : C} (R : Sieve S) {Y : Over S}
    (g : Y ⟶ Over.mk (𝟙 S)) :
    Sieve.overEquiv Y (((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).pullback g) =
      R.pullback g.left := by
  ext Z f
  rw [Sieve.overEquiv_iff, Sieve.pullback_apply, Sieve.overEquiv_symm_iff]
  rfl

/-- **Refinement for `IsPrestackFor`.** If `R₁ ≤ R₂` are sieves on `S`, `F` satisfies descent of
morphisms for `R₁`, and `F` satisfies descent of morphisms for `R₁.pullback g` for every arrow `g`
in `R₂`, then `F` satisfies descent of morphisms for `R₂`. -/
theorem IsPrestackFor.of_le {S : C} {R₁ R₂ : Sieve S} (h : R₁ ≤ R₂)
    (h₁ : F.IsPrestackFor R₁.arrows)
    (h₂ : ∀ ⦃Y : C⦄ (g : Y ⟶ S), R₂ g → F.IsPrestackFor (R₁.pullback g).arrows) :
    F.IsPrestackFor R₂.arrows := by
  rw [isPrestackFor_iff_isSheafFor] at h₁ ⊢
  intro M N
  refine Presieve.isSheafFor_subsieve_aux (F.presheafHom M N)
    (S := (Sieve.overEquiv (Over.mk (𝟙 S))).symm R₁)
    ((Sieve.overEquiv _).symm.monotone h) (h₁ M N) fun Y g hg ↦ ?_
  have hg' : R₂ g.left := (Sieve.overEquiv_symm_iff R₂ g).1 hg
  exact (IsPrestackFor.isSheafFor' Y
    (by rw [overEquiv_pullback_overEquiv_symm]; exact h₂ g.left hg') M N).isSeparatedFor

/-- Lift a `J`-`1`-hypercover of `S` to a `(J.over S)`-`1`-hypercover of `Over.mk (𝟙 S)`. -/
private def oneHypercoverOverMkId {J : GrothendieckTopology C} {S : C}
    (E : J.OneHypercover.{t} S) : (J.over S).OneHypercover.{t} (Over.mk (𝟙 S)) where
  I₀ := E.I₀
  X i := Over.mk (E.f i)
  f i := Over.homMk (E.f i) (Category.comp_id _)
  I₁ := E.I₁
  Y _ _ k := Over.mk (E.p₁ k ≫ E.f _)
  p₁ _ _ k := Over.homMk (E.p₁ k) rfl
  p₂ _ _ k := Over.homMk (E.p₂ k) (E.w k).symm
  w _ _ k := Over.OverMorphism.ext (E.w k)
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ E.mem₀
    rintro Z g ⟨_, a, _, ⟨i⟩, fac⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨Over.mk (E.f i), Over.homMk a (by simpa using fac),
      Over.homMk (E.f i) (Category.comp_id _), Presieve.ofArrows.mk i, by ext; simpa using fac⟩
  mem₁ i₁ i₂ W q₁ q₂ hw := by
    rw [GrothendieckTopology.mem_over_iff]
    have hw' : q₁.left ≫ E.f i₁ = q₂.left ≫ E.f i₂ := by
      simpa using congrArg CommaMorphism.left hw
    refine J.superset_covering ?_ (E.mem₁ i₁ i₂ q₁.left q₂.left hw')
    rintro Z g ⟨k, h, h₁, h₂⟩
    rw [Sieve.overEquiv_iff]
    refine ⟨k, Over.homMk h ?_, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩
    dsimp
    rw [← Category.assoc, ← h₁, Category.assoc]
    exact congrArg (g ≫ ·) (Over.w q₁)

/-- **Base-change locality for `IsPrestackFor` along a `1`-hypercover.** If `F` is a prestack for
`J`, `E` is a `J`-`1`-hypercover of `S`, and a sieve `R` on `S` satisfies `IsPrestackFor` after
pullback along every `E.f i` and every `E.p₁ k ≫ E.f i`, then `F.IsPrestackFor R.arrows`. -/
theorem IsPrestackFor.of_pullback {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {R : Sieve S} (E : J.OneHypercover.{t} S)
    (h₁ : ∀ i, F.IsPrestackFor (R.pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.IsPrestackFor (R.pullback (E.p₁ k ≫ E.f i)).arrows) :
    F.IsPrestackFor R.arrows := by
  rw [isPrestackFor_iff_isSheafFor]
  intro M N
  refine (oneHypercoverOverMkId E).isSheafFor_sieve_of_pullback
    ((isSheaf_iff_isSheaf_of_type _ _).1 (IsPrestack.isSheaf J M N)) (fun i ↦ ?_) (fun i j k ↦ ?_)
  · exact IsPrestackFor.isSheafFor' _
      (by rw [overEquiv_pullback_overEquiv_symm]; exact h₁ i) M N
  · exact (IsPrestackFor.isSheafFor' _
      (by rw [overEquiv_pullback_overEquiv_symm]; exact h₂ k) M N).isSeparatedFor

/-- If `J` is a `t`-small precoverage satisfying `HasIsos`, `IsStableUnderBaseChange`, and
`IsStableUnderComposition`, then to show that `F` is a prestack for `J.toGrothendieck` it suffices
to check `F.IsPrestackFor E.presieve₀` on `t`-small `0`-hypercovers `E` of `J`. -/
theorem IsPrestack.of_precoverage_of_small [HasPullbacks C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] [Precoverage.Small.{t} J]
    (hF : ∀ (X : C) (E : Precoverage.ZeroHypercover.{t} J X), F.IsPrestackFor E.presieve₀) :
    F.IsPrestack J.toGrothendieck := by
  refine IsPrestack.of_precoverage fun X R hR ↦ ?_
  obtain ⟨E₀, rfl⟩ := R.exists_eq_preZeroHypercover
  let E : Precoverage.ZeroHypercover J X := ⟨E₀, hR⟩
  let E' := E.restrictIndexOfSmall.{t}
  rw [← IsPrestackFor_generate_iff]
  refine IsPrestackFor.of_le F (Sieve.generate_mono (by simp [E, E']))
    ((IsPrestackFor_generate_iff F _).2 (hF X E')) fun Y g _ ↦ ?_
  rw [← Sieve.pullbackArrows_comm, IsPrestackFor_generate_iff,
    ← PreZeroHypercover.presieve₀_pullback₁,
    ← Precoverage.ZeroHypercover.pullback₂_toPreZeroHypercover]
  exact hF Y (E'.pullback₂ g)

/-- If `J` is a `t`-small precoverage satisfying `HasIsos`, `IsStableUnderBaseChange`, and
`IsStableUnderComposition`, then to show that `F` is a stack for `J.toGrothendieck` it suffices
to check `F.IsStackFor E.presieve₀` on `t`-small `0`-hypercovers `E` of `J`. -/
theorem IsStack.of_precoverage_of_small [HasPullbacks C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] [Precoverage.Small.{t} J]
    (hF : ∀ (X : C) (E : Precoverage.ZeroHypercover.{t} J X), F.IsStackFor E.presieve₀) :
    F.IsStack J.toGrothendieck := by
  have : F.IsPrestack J.toGrothendieck :=
    IsPrestack.of_precoverage_of_small F fun X E ↦ (hF X E).isPrestackFor
  refine IsStack.of_precoverage fun X R hR ↦ ?_
  obtain ⟨E₀, rfl⟩ := R.exists_eq_preZeroHypercover
  let E : Precoverage.ZeroHypercover J X := ⟨E₀, hR⟩
  let E' := E.restrictIndexOfSmall.{t}
  exact (hF X E').of_le F (Precoverage.generate_mem_toGrothendieck E'.mem₀) (by simp [E, E'])

end CategoryTheory.Pseudofunctor
