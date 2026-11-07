/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# The Freyd-Auslander criterion

Let `C` be a preadditive category with binary biproducts. The finitely presented functors
`Cᵒᵖ ⥤ AddCommGrpCat` (`TauCeti.isFinitelyPresentedFunctor C`, the category `mod C`) are closed
under kernels in the functor category exactly when `C` has weak kernels
(`TauCeti.hasWeakKernels_iff_isClosedUnderKernels`).

Since `mod C` already contains zero (for nonempty `C`) and is closed under cokernels and finite
products, Mathlib's instance for subcategories of abelian categories closed under kernels and
cokernels then makes `(isFinitelyPresentedFunctor C).FullSubcategory` abelian, with kernels and
cokernels computed in the functor category, whenever `C` has weak kernels. Abelian and
pretriangulated categories have weak kernels.

The proof goes through representable functors. If `C` has weak kernels, the kernel of any
morphism `(-, Z) ⟶ F` to a finitely presented functor `F` is the image of `(-, w)` for some
`w : W ⟶ Z`: if `F` is presented by `f : X ⟶ Y` and the morphism is `(-, u)` followed by the
projection `(-, Y) ⟶ F`, take for `w` a weak kernel of `[u, f] : Z ⊞ X ⟶ Y` followed by the
projection to `Z`. Applying this twice presents the kernel of a morphism of finitely presented
functors. Conversely, if the kernel of `(-, g)` is finitely presented, it is a quotient of some
representable `(-, X)`, and the corresponding morphism `X ⟶ Y` is a weak kernel of `g`.

## Main declarations

* `TauCeti.IsFinitelyPresentedFunctor.exists_exact_preadditiveYoneda_map`: with weak kernels,
  the kernel of a morphism from a representable functor to a finitely presented functor is the
  image of a representable functor.
* `TauCeti.IsFinitelyPresentedFunctor.of_isLimit_kernelFork`: with weak kernels, the kernel of a
  morphism of finitely presented functors is finitely presented.
* `TauCeti.hasWeakKernels_of_isClosedUnderKernels`: the converse.
* `TauCeti.hasWeakKernels_iff_isClosedUnderKernels`: the Freyd-Auslander criterion.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
* P. Freyd, *Representations in abelian categories*, Proceedings of the Conference on Categorical
  Algebra (La Jolla, 1965), Springer, 1966, 95-120.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

section WeakKernels

variable [HasWeakKernels C] [HasBinaryBiproducts C]

/-- If `C` has weak kernels, the kernel of a morphism `α : (-, Z) ⟶ F` to a finitely presented
functor is the image of `(-, w)` for some morphism `w : W ⟶ Z` of `C`. -/
theorem IsFinitelyPresentedFunctor.exists_exact_preadditiveYoneda_map
    (hF : IsFinitelyPresentedFunctor F) {Z : C} (α : preadditiveYoneda.obj Z ⟶ F) :
    ∃ (W : C) (w : W ⟶ Z) (h : preadditiveYoneda.map w ≫ α = 0),
      (ShortComplex.mk _ _ h).Exact := by
  obtain ⟨X, Y, f, p, hfp, hp, hS⟩ := isFinitelyPresentedFunctor_def.1 hF
  obtain ⟨u, rfl⟩ := exists_preadditiveYoneda_map_comp_eq p α
  rw [exact_preadditiveYoneda_map_iff] at hS
  -- `z : V ⟶ Z` is killed exactly when `z ≫ u = x ≫ f` for some `x`, that is, when
  -- `biprod.lift z (-x)` is killed by `[u, f] : Z ⊞ X ⟶ Y`; so `w` is a weak kernel of `[u, f]`
  -- followed by the first projection.
  have hk : weakKernel.ι (biprod.desc u f) ≫ biprod.fst ≫ u =
      (-(weakKernel.ι (biprod.desc u f) ≫ biprod.snd)) ≫ f := by
    have h : weakKernel.ι (biprod.desc u f) ≫ (biprod.fst ≫ u + biprod.snd ≫ f) = 0 := by
      rw [← biprod.desc_eq, weakKernel.condition]
    rw [Preadditive.comp_add] at h
    rw [Preadditive.neg_comp, Category.assoc, ← sub_eq_zero, sub_neg_eq_add, h]
  refine ⟨weakKernel (biprod.desc u f), weakKernel.ι (biprod.desc u f) ≫ biprod.fst, ?_, ?_⟩
  · rw [← Category.assoc, ← Functor.map_comp, Category.assoc, hk, Functor.map_comp,
      Category.assoc, hfp, comp_zero]
  · rw [exact_preadditiveYoneda_map_iff]
    intro V z hz
    obtain ⟨x, hx⟩ := hS (z ≫ u) hz
    have hzx : biprod.lift z (-x) ≫ biprod.desc u f = 0 := by
      simp [hx]
    exact ⟨weakKernel.lift _ _ hzx, by simp⟩

/-- If `C` has weak kernels, the kernel of a morphism of finitely presented functors is finitely
presented. -/
theorem IsFinitelyPresentedFunctor.of_isLimit_kernelFork {φ : F ⟶ G} {c : KernelFork φ}
    (hc : IsLimit c) (hF : IsFinitelyPresentedFunctor F) (hG : IsFinitelyPresentedFunctor G) :
    IsFinitelyPresentedFunctor c.pt := by
  obtain ⟨Y, p, hp⟩ := isFinitelyGeneratedFunctor_def.1 hF.isFinitelyGeneratedFunctor
  -- `(-, w) ≫ p : (-, W) ⟶ F` has image the kernel of `φ`, so it factors through `c` by an
  -- epimorphism `r`; the kernel of `r` is then the image of some `(-, w')`.
  obtain ⟨W, w, hw, hwS⟩ := hG.exists_exact_preadditiveYoneda_map (p ≫ φ)
  obtain ⟨W', w', hw', hw'S⟩ :=
    hF.exists_exact_preadditiveYoneda_map (preadditiveYoneda.map w ≫ p)
  obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' hc (preadditiveYoneda.map w ≫ p)
    (by rw [Category.assoc, hw])
  have hι : Mono c.ι := Fork.IsLimit.mono hc
  rw [exact_preadditiveYoneda_map_iff] at hwS hw'S
  refine isFinitelyPresentedFunctor_def.2 ⟨W', W, w', r,
    by rw [← cancel_mono c.ι, Category.assoc, hr, hw', zero_comp], ?_, ?_⟩
  · -- Pointwise: lift `c.ι t` along `p` to some `y : V ⟶ Y`, which is killed by `p ≫ φ` and so
    -- factors as `x ≫ w`; then `r` sends `x` to `t`, as `c.ι` is injective.
    rw [NatTrans.epi_iff_epi_app]
    intro V
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective (p.app V)).1 inferInstance (c.ι.app V t)
    have hφ : (p ≫ φ).app V y = 0 := by
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hy, ← ConcreteCategory.comp_apply,
        ← NatTrans.comp_app, KernelFork.condition]
      simp
    obtain ⟨x, rfl⟩ := hwS (V := V.unop) y hφ
    refine ⟨x, (AddCommGrpCat.mono_iff_injective (c.ι.app V)).1 inferInstance ?_⟩
    -- Both sides of `hr`, evaluated at `x`, unfold to `c.ι (r x)` and `p (x ≫ w)`.
    exact (congrArg (fun ψ ↦ ψ.app V x) hr).trans hy
  · rw [exact_preadditiveYoneda_map_iff]
    intro V x hx
    -- As above, `hr` evaluated at `x` says `c.ι (r x) = p (x ≫ w)`.
    exact hw'S x ((congrArg (fun ψ ↦ ψ.app (op V) x) hr).symm.trans
      ((congrArg (c.ι.app (op V)) hx).trans (map_zero _)))

/-- If `C` has weak kernels, the finitely presented functors are closed under kernels in the
functor category. -/
instance : (isFinitelyPresentedFunctor C).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨_, k, hk, hF, hG⟩
    exact IsFinitelyPresentedFunctor.of_isLimit_kernelFork hk hF hG

end WeakKernels

/-- If the finitely presented functors are closed under kernels in the functor category, then `C`
has weak kernels: a weak kernel of `g : Y ⟶ Z` is given by a representable functor mapping onto
the kernel of `(-, g)`. -/
theorem hasWeakKernels_of_isClosedUnderKernels
    [(isFinitelyPresentedFunctor C).IsClosedUnderKernels] : HasWeakKernels C where
  hasWeakLimit {Y Z} g := by
    obtain ⟨X, q, hq⟩ := isFinitelyGeneratedFunctor_def.1
      ((isFinitelyPresentedFunctor C).prop_kernel (preadditiveYoneda.map g)
      (isFinitelyPresentedFunctor_preadditiveYoneda_obj Y)
      (isFinitelyPresentedFunctor_preadditiveYoneda_obj Z)).isFinitelyGeneratedFunctor
    obtain ⟨w, hw⟩ := preadditiveYoneda.map_surjective (q ≫ kernel.ι _)
    have hwg : w ≫ g = 0 := preadditiveYoneda.map_injective (by
      rw [Functor.map_comp, hw, Category.assoc, kernel.condition, comp_zero, Functor.map_zero])
    refine HasWeakLimit.mk ⟨KernelFork.ofι w hwg, Fork.IsWeakLimit.mk' _ fun s ↦ ?_⟩
    -- `(-, s.ι)` factors through the kernel of `(-, g)`, and lifts along the epimorphism `q`.
    have hl := exists_preadditiveYoneda_map_comp_eq q
      (kernel.lift _ (preadditiveYoneda.map s.ι) (by
        rw [← Functor.map_comp, KernelFork.condition, Functor.map_zero]))
    refine ⟨hl.choose, preadditiveYoneda.map_injective ?_⟩
    rw [Fork.ι_ofι, Functor.map_comp, hw, ← Category.assoc, hl.choose_spec, kernel.lift_ι]

/-- **The Freyd-Auslander criterion.** A preadditive category `C` with binary biproducts has weak
kernels exactly when the finitely presented functors `Cᵒᵖ ⥤ AddCommGrpCat` are closed under
kernels in the functor category. For nonempty `C`, this makes `mod C` an abelian category, with
kernels and cokernels computed in the functor category. -/
theorem hasWeakKernels_iff_isClosedUnderKernels [HasBinaryBiproducts C] :
    HasWeakKernels C ↔ (isFinitelyPresentedFunctor C).IsClosedUnderKernels :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ hasWeakKernels_of_isClosedUnderKernels⟩

-- With weak kernels, `mod C` is abelian by Mathlib's instance for full subcategories of abelian
-- categories containing zero and closed under kernels, cokernels and finite products.
noncomputable example [HasWeakKernels C] [HasBinaryBiproducts C] [Nonempty C] :
    Abelian (isFinitelyPresentedFunctor C).FullSubcategory :=
  inferInstance

end TauCeti
