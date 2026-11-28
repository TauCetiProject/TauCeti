/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Homology.Ext.Presentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.LinearAlgebra.Dual.Opposite

/-!
# The regular dual of Ext over the opposite ring

For a right module `M` over a ring `A`, the group `Extⁿ(M, A)`, taken in right modules, is a
left `A`-module by postcomposition with left multiplication on the regular bimodule. Use
`open scoped ModuleCat.RightRegularExt` to enable this action. If `M` is finitely generated
and `A` is Noetherian on both sides, this Ext module is finitely generated on the left.

Over a right Noetherian ring, if the left regular module embeds in a finitely generated
projective-injective left module, the left regular dual of this Ext module vanishes for every
finitely generated right module in every positive degree. In degree one this follows by dualizing
a projective presentation. Higher degrees follow by dimension shifting. The vanishing supplies
the grade-zero step in the left-right symmetry of dominant dimension.

## References

* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280,
  Lemma 1.1 and the proof of the main theorem in Section 2, p. 277.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Abelian TauCeti

universe u

namespace ModuleCat

variable {A : Type u} [Ring A]

namespace RightRegularExt

/-- The left action on Ext into the right regular module is restriction of the target endomorphism
action along left multiplication. -/
scoped instance rightRegularExtModule (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    Module A (Ext M (ModuleCat.of Aᵐᵒᵖ A) n) :=
  Module.compHom _ ((RingEquiv.moduleEndSelfOp A).trans (ModuleCat.endRingEquiv
    (ModuleCat.of Aᵐᵒᵖ A)).symm).toRingHom

end RightRegularExt

end ModuleCat

open scoped ModuleCat.RightRegularExt

namespace ModuleCat

variable {A : Type u} [Ring A]

/-- Left multiplication on the right regular module induces the left action on Ext. -/
theorem rightRegularExt_smul_def {M : ModuleCat.{u} Aᵐᵒᵖ} {n : ℕ}
    (a : A) (x : Ext M (ModuleCat.of Aᵐᵒᵖ A) n) :
    a • x = x.comp (Ext.mk₀ (ModuleCat.ofHom (RingEquiv.moduleEndSelfOp A a))) (add_zero n) :=
  (rfl)

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

variable {A : Type u} [Ring A] {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)

/-- Pushing out a short exact sequence by maps from its kernel to the right regular module is
linear for the left actions. -/
def rightRegularExtBoundary :
    (S.X₁ →ₗ[Aᵐᵒᵖ] A) →ₗ[A] Ext S.X₃ (ModuleCat.of Aᵐᵒᵖ A) 1 where
  toFun f := homBoundary ℤ hS _ (ModuleCat.ofHom f)
  map_add' f g := by simp only [ModuleCat.ofHom_add, map_add]
  map_smul' a f := by
    have hs : ModuleCat.ofHom (a • f) =
        ModuleCat.ofHom f ≫ ModuleCat.ofHom (RingEquiv.moduleEndSelfOp A a) := by
      ext x
      rfl
    simp only [RingHom.id_apply, homBoundary_apply, ModuleCat.rightRegularExt_smul_def, hs,
      ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The regular-module boundary pushes out along the given right-linear map. -/
@[simp]
theorem rightRegularExtBoundary_apply (f : S.X₁ →ₗ[Aᵐᵒᵖ] A) :
    rightRegularExtBoundary hS f = hS.extClass.comp (Ext.mk₀ (ModuleCat.ofHom f)) (add_zero 1) :=
  homBoundary_apply ℤ hS _ _

/-- The kernel of the regular-module boundary consists of the functional restrictions from the
middle term. -/
theorem exact_lcomp_rightRegularExtBoundary :
    Function.Exact (S.f.hom.lcomp A A) hS.rightRegularExtBoundary := by
  intro f
  have h : hS.rightRegularExtBoundary f = 0 ↔
      ModuleCat.ofHom f ∈ (Linear.leftComp ℤ (ModuleCat.of Aᵐᵒᵖ A) S.f).range := by
    rw [← ker_homBoundary]
    exact Iff.rfl
  rw [h]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.hom, congrArg ModuleCat.Hom.hom hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ModuleCat.ofHom g, rfl⟩

/-- Every degree-one class is represented by a map from the kernel of a projective presentation. -/
theorem rightRegularExtBoundary_surjective [Projective S.X₂] :
    Function.Surjective (rightRegularExtBoundary hS) := by
  intro x
  obtain ⟨f, hf⟩ := homBoundary_surjective ℤ hS (ModuleCat.of Aᵐᵒᵖ A) x
  exact ⟨f.hom, by simpa using hf⟩

/-- Dimension shifting with regular coefficients respects the left action on Ext. -/
def rightRegularExtSuccEquiv [Projective S.X₂] (n : ℕ) :
    Ext S.X₁ (ModuleCat.of Aᵐᵒᵖ A) (n + 1) ≃ₗ[A]
      Ext S.X₃ (ModuleCat.of Aᵐᵒᵖ A) (n + 2) :=
  LinearEquiv.ofBijective
    { toFun := fun x ↦ hS.extClass.comp x (by omega)
      map_add' := fun x y ↦ Ext.comp_add _ x y _
      map_smul' := fun a x ↦ by simp [ModuleCat.rightRegularExt_smul_def] }
    (precomp_extClass_bijective hS _ n)

/-- The dimension shift is Yoneda composition with the presentation's extension class. -/
@[simp]
theorem rightRegularExtSuccEquiv_apply [Projective S.X₂] (n : ℕ)
    (x : Ext S.X₁ (ModuleCat.of Aᵐᵒᵖ A) (n + 1)) :
    rightRegularExtSuccEquiv hS n x = hS.extClass.comp x (by omega) :=
  (rfl)

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat

variable {A : Type u} [Ring A]

/-- Positive Ext groups of a finitely generated right module into the regular bimodule are
finitely generated left modules over a two-sided Noetherian ring. -/
theorem finite_rightRegularExt_succ [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] (n : ℕ) :
    Module.Finite A (Ext M (ModuleCat.of Aᵐᵒᵖ A) (n + 1)) := by
  induction n generalizing M with
  | zero =>
    obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ M
    let hS := q.shortExact_shortComplexKer hq
    obtain ⟨r, p, hp⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ q.ker
    have := Module.Finite.of_injective (p.lcomp A A) (p.lcomp_injective_of_surjective hp)
    exact Module.Finite.of_surjective hS.rightRegularExtBoundary
      hS.rightRegularExtBoundary_surjective
  | succ n ih =>
    obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ M
    have := ih (ModuleCat.of Aᵐᵒᵖ q.ker)
    exact Module.Finite.equiv ((q.shortExact_shortComplexKer hq).rightRegularExtSuccEquiv n)

section Vanishing

variable {I : Type u} [AddCommGroup I] [Module A I]
  [Module.Finite A I] [Module.Projective A I] [Module.Injective A I]

/-- A functional on the extension group vanishes on every class obtained from the kernel. -/
private theorem comp_rightRegularExtBoundary_eq_zero
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)
    [Module.Finite Aᵐᵒᵖ S.X₁] [Module.Finite Aᵐᵒᵖ S.X₂] [Module.Projective Aᵐᵒᵖ S.X₂]
    (g : Ext S.X₃ (ModuleCat.of Aᵐᵒᵖ A) 1 →ₗ[A] I) :
    g.comp hS.rightRegularExtBoundary = 0 := by
  let l := g.comp hS.rightRegularExtBoundary
  have hl (a : S.X₂ →ₗ[Aᵐᵒᵖ] A) : l (S.f.hom.lcomp A A a) = 0 := by
    simp [l, hS.exact_lcomp_rightRegularExtBoundary.apply_apply_eq_zero]
  have := hS.mono_f
  have hf := (ModuleCat.mono_iff_injective S.f).mp inferInstance
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ S.X₁
  obtain ⟨L, hL⟩ := Module.Injective.extension_property A I _ _ _
    (q.lcomp_injective_of_surjective hq) l
  obtain ⟨r, p, hp⟩ := Module.Finite.exists_fin' A I
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  -- Each coordinate of the extension is evaluation on the finite free module.
  let x (j : Fin r) :=
    (unopDualEvalEquiv A (Fin m → Aᵐᵒᵖ)).symm ((LinearMap.proj j).comp (s.comp L))
  have hx (j : Fin r) (a : S.X₁ →ₗ[Aᵐᵒᵖ] A) : a (q (x j)) = s (l a) j := by
    calc
      a (q (x j)) = q.lcomp A A a (x j) := (LinearMap.lcomp_apply q a (x j)).symm
      _ = s (L (q.lcomp A A a)) j := apply_unopDualEvalEquiv_symm A _ _ _
      _ = s (l a) j := congrArg (fun y ↦ s y j) (LinearMap.congr_fun hL a)
  have hz (j : Fin r) : q (x j) = 0 := by
    apply hf
    rw [map_zero]
    apply (unopDualEvalEquiv A S.X₂).injective
    apply LinearMap.ext
    intro g
    rw [unopDualEvalEquiv_apply, unopDualEvalEquiv_apply, map_zero]
    -- Restrictions vanish under the given map, so they evaluate to zero at this coordinate.
    calc
      g (S.f (q (x j))) = (S.f.hom.lcomp A A g) (q (x j)) :=
        (LinearMap.lcomp_apply S.f.hom g (q (x j))).symm
      _ = s (l (S.f.hom.lcomp A A g)) j := hx j _
      _ = 0 := by simp [hl]
  have hinj : Function.Injective s :=
    Function.LeftInverse.injective (f := s) (g := p) (fun y ↦ LinearMap.congr_fun hs y)
  apply LinearMap.ext
  intro a
  apply hinj
  funext j
  simpa only [hz, map_zero, LinearMap.zero_apply, Pi.zero_apply] using (hx j a).symm

private theorem subsingleton_hom_rightRegularExtOne [IsNoetherianRing Aᵐᵒᵖ]
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] :
    Subsingleton (Ext M (ModuleCat.of Aᵐᵒᵖ A) 1 →ₗ[A] I) := by
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ M
  let hS := q.shortExact_shortComplexKer hq
  apply subsingleton_of_forall_eq 0
  intro g
  exact (LinearMap.cancel_right hS.rightRegularExtBoundary_surjective).mp
    ((comp_rightRegularExtBoundary_eq_zero hS g).trans
      (LinearMap.zero_comp hS.rightRegularExtBoundary).symm)

/-- Over a right Noetherian ring, positive Ext from a finitely generated right module into the
right regular module has no nonzero left-linear maps to a finitely generated
projective-injective left module. -/
theorem subsingleton_hom_rightRegularExt_succ [IsNoetherianRing Aᵐᵒᵖ]
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] (n : ℕ) :
    Subsingleton (Ext M (ModuleCat.of Aᵐᵒᵖ A) (n + 1) →ₗ[A] I) := by
  induction n generalizing M with
  | zero => exact subsingleton_hom_rightRegularExtOne M
  | succ n ih =>
    obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ M
    have := ih (ModuleCat.of Aᵐᵒᵖ q.ker)
    let e := (q.shortExact_shortComplexKer hq).rightRegularExtSuccEquiv n
    exact (e.surjective.injective_linearMapComp_right (g := e.toLinearMap)).subsingleton

/-- If the left regular module embeds in a finitely generated projective-injective module, the
left regular dual of every positive regular Ext group of a finitely generated right module
vanishes. -/
theorem subsingleton_dual_rightRegularExt_succ [IsNoetherianRing Aᵐᵒᵖ]
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] (n : ℕ)
    (i : A →ₗ[A] I) (hi : Function.Injective i) :
    Subsingleton (Module.Dual A (Ext M (ModuleCat.of Aᵐᵒᵖ A) (n + 1))) := by
  have := subsingleton_hom_rightRegularExt_succ (I := I) M n
  exact hi.injective_linearMapComp_left.subsingleton

end Vanishing

end ModuleCat
