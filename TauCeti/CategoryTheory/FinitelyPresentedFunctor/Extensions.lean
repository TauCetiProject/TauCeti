/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# Extensions of finitely presented functors

Let `C` be a preadditive category with binary biproducts, and let `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` be a
short exact sequence of functors `Cᵒᵖ ⥤ AddCommGrpCat`. If `F'` and `F''` are finitely presented,
then so is `F` (`TauCeti.IsFinitelyPresentedFunctor.of_shortExact`). Similarly, if
`F' ⟶ F ⟶ F'' ⟶ 0` is exact and `F'`, `F''` are finitely generated, then `F` is finitely generated
(`TauCeti.IsFinitelyGeneratedFunctor.of_exact`). So the category `mod C` of finitely presented
functors is closed under extensions in the category of all functors.

The proof is the horseshoe argument. The functor `F` is additive
(`CategoryTheory.ShortComplex.Exact.additive_X₂`). If `F'` and `F''` are presented by `f' : X' ⟶ Y'`
and `f'' : X'' ⟶ Y''`, lift the projection `(-, Y'') ⟶ F''` to `s : (-, Y'') ⟶ F`, which is possible
because `F` is additive (`CategoryTheory.exists_comp_eq_preadditiveYoneda_obj_of_epi`). Then
`(-, f'') ≫ s` factors through `F'`, hence through `(-, w)` for some `w : X'' ⟶ Y'`, and `F` is
presented by `(-, Y' ⊞ Y'') ⟶ F` and the morphism `X' ⊞ X'' ⟶ Y' ⊞ Y''` with matrix
`[[f', -w], [0, f'']]`.

## Main declarations

* `TauCeti.epi_preadditiveYoneda_biprod`: the epimorphism `(-, Y' ⊞ Y'') ⟶ F` built from
  epimorphisms onto the outer terms of an exact sequence.
* `TauCeti.IsFinitelyGeneratedFunctor.of_exact`: an extension of finitely generated functors is
  finitely generated.
* `TauCeti.IsFinitelyPresentedFunctor.of_shortExact`: an extension of finitely presented functors
  is finitely presented, which gives Mathlib's `ObjectProperty.IsClosedUnderExtensions` for `mod C`.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v})}

/-- The morphism `(-, Y' ⊞ Y'') ⟶ F` restricting to `p ≫ f` and to `s` on the two summands sends
`y` to `f (p (y ≫ fst)) + s (y ≫ snd)`. -/
private theorem biprod_comp_add_app_apply {Y' Y'' : C} {F' F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (p : preadditiveYoneda.obj Y' ⟶ F') (f : F' ⟶ F) (s : preadditiveYoneda.obj Y'' ⟶ F) (Z : Cᵒᵖ)
    (y : Z.unop ⟶ Y' ⊞ Y'') :
    (preadditiveYoneda.map (biprod.fst : Y' ⊞ Y'' ⟶ _) ≫ p ≫ f +
      preadditiveYoneda.map biprod.snd ≫ s).app Z y =
      f.app Z (p.app Z (y ≫ biprod.fst)) + s.app Z (y ≫ biprod.snd) :=
  rfl

/-- In an exact sequence `F' ⟶ F ⟶ F''`, an epimorphism `p : (-, Y') ⟶ F'` together with a
morphism `s : (-, Y'') ⟶ F` whose composite to `F''` is an epimorphism give an epimorphism
`(-, Y' ⊞ Y'') ⟶ F`, restricting to `p ≫ f` and to `s` on the two summands. -/
theorem epi_preadditiveYoneda_biprod (hS : S.Exact) {Y' Y'' : C}
    (p : preadditiveYoneda.obj Y' ⟶ S.X₁) [Epi p] (s : preadditiveYoneda.obj Y'' ⟶ S.X₂)
    [Epi (s ≫ S.g)] :
    Epi (preadditiveYoneda.map (biprod.fst : Y' ⊞ Y'' ⟶ _) ≫ p ≫ S.f +
      preadditiveYoneda.map biprod.snd ≫ s) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Z
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  -- Write `S.g x` as the image of some `b : Z ⟶ Y''`; then `x - s b` comes from `F'`, so it is
  -- the image of some `a : Z ⟶ Y'`, and `x` is the image of `(a, b) : Z ⟶ Y' ⊞ Y''`.
  obtain ⟨(b : Z.unop ⟶ Y''), hb⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((s ≫ S.g).app Z)).1 inferInstance (S.g.app Z x)
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    ((ShortComplex.exact_iff_evaluation _).1 hS Z) (x - s.app Z b)
    ((map_sub _ _ _).trans (sub_eq_zero.2 hb.symm))
  obtain ⟨(a : Z.unop ⟶ Y'), rfl⟩ :=
    (AddCommGrpCat.epi_iff_surjective (p.app Z)).1 inferInstance y
  refine ⟨biprod.lift a b, (biprod_comp_add_app_apply p S.f s Z _).trans ?_⟩
  rw [biprod.lift_fst, biprod.lift_snd]
  exact eq_sub_iff_add_eq.1 hy

/-- The functor `F` in an exact sequence `F' ⟶ F ⟶ F'' ⟶ 0` with `F'` and `F''` finitely generated
is finitely generated. -/
theorem IsFinitelyGeneratedFunctor.of_exact (hS : S.Exact) [Epi S.g]
    (h₁ : IsFinitelyGeneratedFunctor S.X₁) (h₃ : IsFinitelyGeneratedFunctor S.X₃) :
    IsFinitelyGeneratedFunctor S.X₂ := by
  obtain ⟨Y', p', hp'⟩ := isFinitelyGeneratedFunctor_def.1 h₁
  obtain ⟨Y'', p'', hp''⟩ := isFinitelyGeneratedFunctor_def.1 h₃
  have := h₁.additive
  have := h₃.additive
  have := hS.additive_X₂
  obtain ⟨s, hs⟩ := exists_comp_eq_preadditiveYoneda_obj_of_epi S.g p''
  have : Epi (s ≫ S.g) := hs ▸ hp''
  exact isFinitelyGeneratedFunctor_def.2 ⟨Y' ⊞ Y'', _, epi_preadditiveYoneda_biprod hS p' s⟩

/-- Exactness at `(-, Y' ⊞ Y'')` of the horseshoe presentation of `F`: given presentations of `F'`
and `F''` by `f'` and `f''`, a lift `s` of `p''` to `F`, and `w` with `(-, w) ≫ p' ≫ S.f` equal to
`(-, f'') ≫ s`, the morphism with matrix `[[f', -w], [0, f'']]` presents `F`. -/
private theorem exact_horseshoe [Mono S.f] {X' Y' X'' Y'' : C} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {w : X'' ⟶ Y'} {p' : preadditiveYoneda.obj Y' ⟶ S.X₁} {p'' : preadditiveYoneda.obj Y'' ⟶ S.X₃}
    {s : preadditiveYoneda.obj Y'' ⟶ S.X₂} {hfp' : preadditiveYoneda.map f' ≫ p' = 0}
    {hfp'' : preadditiveYoneda.map f'' ≫ p'' = 0} (hE' : (ShortComplex.mk _ _ hfp').Exact)
    (hE'' : (ShortComplex.mk _ _ hfp'').Exact) (hs : s ≫ S.g = p'')
    (hwf : preadditiveYoneda.map w ≫ p' ≫ S.f = preadditiveYoneda.map f'' ≫ s)
    (hP : preadditiveYoneda.map
        (biprod.lift (biprod.fst ≫ f' - biprod.snd ≫ w) (biprod.snd ≫ f'') :
          X' ⊞ X'' ⟶ Y' ⊞ Y'') ≫
      (preadditiveYoneda.map biprod.fst ≫ p' ≫ S.f + preadditiveYoneda.map biprod.snd ≫ s) = 0) :
    (ShortComplex.mk _ _ hP).Exact := by
  have hS' := (exact_preadditiveYoneda_map_iff f' p' hfp').1 hE'
  have hS'' := (exact_preadditiveYoneda_map_iff f'' p'' hfp'').1 hE''
  rw [exact_preadditiveYoneda_map_iff]
  intro V y hy
  have hy : S.f.app (op V) (p'.app (op V) (y ≫ biprod.fst)) + s.app (op V) (y ≫ biprod.snd) = 0 :=
    (biprod_comp_add_app_apply p' S.f s (op V) y).symm.trans hy
  -- Applying `S.g` shows that `p'' (y ≫ snd) = 0`, so `y ≫ snd = c ≫ f''` for some `c`.
  have h₃ : p''.app (op V) (y ≫ biprod.snd) = 0 := by
    have h0 : S.g.app (op V) (S.f.app (op V) (p'.app (op V) (y ≫ biprod.fst))) = 0 :=
      (S.map ((evaluation _ _).obj (op V))).ab_zero_apply _
    calc _ = (s ≫ S.g).app (op V) (y ≫ biprod.snd) := by rw [hs]
      _ = S.g.app (op V)
          (S.f.app (op V) (p'.app (op V) (y ≫ biprod.fst)) + s.app (op V) (y ≫ biprod.snd)) := by
        rw [map_add, h0, zero_add, NatTrans.comp_app]
        exact ConcreteCategory.comp_apply _ _ _
      _ = 0 := by rw [hy, map_zero]
  obtain ⟨c, hc⟩ := hS'' _ h₃
  -- Then `s (y ≫ snd) = S.f (p' (c ≫ w))`, so `S.f (p' (y ≫ fst + c ≫ w)) = 0`; as `S.f` is
  -- injective, `y ≫ fst + c ≫ w = d ≫ f'` for some `d`.
  have hcw : s.app (op V) (y ≫ biprod.snd) = S.f.app (op V) (p'.app (op V) (c ≫ w)) := by
    rw [← hc]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app hwf (op V)) c).symm
  have h₁ : p'.app (op V) (y ≫ biprod.fst + c ≫ w) = 0 := by
    refine (AddCommGrpCat.mono_iff_injective (S.f.app (op V))).1 inferInstance ?_
    rw [map_zero, ← hy, hcw]
    exact (congrArg (S.f.app (op V)) (map_add (p'.app (op V)).hom _ _)).trans (map_add _ _ _)
  obtain ⟨d, hd⟩ := hS' _ h₁
  -- The components of `(d, c) ≫ g` are read off from `hd` and `hc`.
  refine ⟨biprod.lift d c, biprod.hom_ext _ _ ?_ ?_⟩ <;>
    simp [Preadditive.comp_sub, hd, hc]

/-- The functor `F` in a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` with `F'` and `F''` finitely
presented is finitely presented. -/
theorem IsFinitelyPresentedFunctor.of_shortExact (hS : S.ShortExact)
    (h₁ : IsFinitelyPresentedFunctor S.X₁) (h₃ : IsFinitelyPresentedFunctor S.X₃) :
    IsFinitelyPresentedFunctor S.X₂ := by
  obtain ⟨X', Y', f', p', hfp', hp', hE'⟩ := isFinitelyPresentedFunctor_def.1 h₁
  obtain ⟨X'', Y'', f'', p'', hfp'', hp'', hE''⟩ := isFinitelyPresentedFunctor_def.1 h₃
  have := hS.mono_f
  have := hS.epi_g
  have := h₁.additive
  have := h₃.additive
  have := hS.exact.additive_X₂
  -- Lift `p''` to `s : (-, Y'') ⟶ F`; then `(-, f'') ≫ s` is killed by `S.g`, so it factors
  -- through `S.f`, and then through `p'` as `(-, w)`.
  obtain ⟨s, hs⟩ := exists_comp_eq_preadditiveYoneda_obj_of_epi S.g p''
  have : Epi (s ≫ S.g) := hs ▸ hp''
  have hst : (preadditiveYoneda.map f'' ≫ s) ≫ S.g = 0 := by
    simp [hs, hfp'']
  obtain ⟨w, hw⟩ := exists_preadditiveYoneda_map_comp_eq p' (hS.exact.lift _ hst)
  have hwf : preadditiveYoneda.map w ≫ p' ≫ S.f = preadditiveYoneda.map f'' ≫ s := by
    simp [reassoc_of% hw]
  -- `F` is presented by `[p' ≫ S.f, s] : (-, Y' ⊞ Y'') ⟶ F` and `[[f', -w], [0, f'']]`.
  let P := preadditiveYoneda.map (biprod.fst : Y' ⊞ Y'' ⟶ _) ≫ p' ≫ S.f +
    preadditiveYoneda.map biprod.snd ≫ s
  let g : X' ⊞ X'' ⟶ Y' ⊞ Y'' := biprod.lift (biprod.fst ≫ f' - biprod.snd ≫ w) (biprod.snd ≫ f'')
  have hfst : preadditiveYoneda.map g ≫ preadditiveYoneda.map biprod.fst =
      preadditiveYoneda.map (biprod.fst ≫ f' - biprod.snd ≫ w) := by
    simp [g, ← Functor.map_comp]
  have hsnd : preadditiveYoneda.map g ≫ preadditiveYoneda.map biprod.snd =
      preadditiveYoneda.map (biprod.snd ≫ f'') := by
    simp [g, ← Functor.map_comp]
  have hP : preadditiveYoneda.map g ≫ P = 0 := by
    simp only [P, Preadditive.comp_add, reassoc_of% hfst, reassoc_of% hsnd, Functor.map_sub,
      Functor.map_comp, Preadditive.sub_comp, Category.assoc, reassoc_of% hfp', hwf, comp_zero,
      zero_comp, zero_sub, neg_add_cancel]
  exact isFinitelyPresentedFunctor_def.2 ⟨X' ⊞ X'', Y' ⊞ Y'', g, P, hP,
    epi_preadditiveYoneda_biprod hS.exact p' s, exact_horseshoe hE' hE'' hs hwf hP⟩

/-- `mod C` is closed under extensions in the category of all functors `Cᵒᵖ ⥤ AddCommGrpCat`. -/
instance : (isFinitelyPresentedFunctor C).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := IsFinitelyPresentedFunctor.of_shortExact hS h₁ h₃

end TauCeti
