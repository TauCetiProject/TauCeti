/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Limits.Final

/-!
# Cofinal subsequences of module towers

Restriction of compatible families to a cofinal monotone sequence of indices is a linear
equivalence. Repeated indices are allowed, and no surjectivity or Mittag--Leffler condition
on the transitions is needed. The inverse is characterized at any original index by
transition from any later index in the subsequence. In particular it makes no choice of
an inverse to a transition map.

The equivalence is natural in morphisms of towers. It uses Mathlib's cofinality criterion
`Monotone.final_functor_iff` and `Functor.Initial.isLimitWhiskerEquiv`, applied to
`ModuleTower.isLimitLimCone`, rather than reconstructing the categorical limit.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Limits Opposite

universe v u

variable {R : Type u} [Ring R]

/-- The module tower sampled along a monotone sequence of indices. -/
abbrev subsequence (F : ModuleTower.{v} R) (φ : ℕ →o ℕ) : ModuleTower.{v} R :=
  φ.monotone.functor.op ⋙ F

variable (F : ModuleTower.{v} R) (φ : ℕ →o ℕ)

@[simp]
theorem subsequence_transitionOfLE {n m : ℕ} (h : n ≤ m) :
    (F.subsequence φ).transitionOfLE h = F.transitionOfLE (φ.monotone h) := by
  rw [transitionOfLE_def, transitionOfLE_def]
  -- Precomposition maps this order morphism to the unique morphism between the selected indices.
  rfl

@[simp]
theorem subsequence_transition (n : ℕ) :
    (F.subsequence φ).transition n = F.transitionOfLE (φ.monotone (Nat.le_succ n)) := by
  rw [← transitionOfLE_succ, subsequence_transitionOfLE]

private def limSubsequenceIso (hφ : ∀ n, ∃ m, n ≤ φ m) :
    ModuleCat.of R F.lim ≅ ModuleCat.of R (F.subsequence φ).lim :=
  (F.isLimitLimCone.whiskerOfCofinal φ hφ).conePointUniqueUpToIso
    (F.subsequence φ).isLimitLimCone

private theorem limSubsequenceIso_hom_comp_π (hφ : ∀ n, ∃ m, n ≤ φ m) (n : ℕ) :
    (F.limSubsequenceIso φ hφ).hom ≫ ModuleCat.ofHom ((F.subsequence φ).limπ n) =
      ModuleCat.ofHom (F.limπ (φ n)) := by
  have h := congrArg ModuleCat.Hom.hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (F.isLimitLimCone.whiskerOfCofinal φ hφ)
      (F.subsequence φ).isLimitLimCone (op n))
  simp only [ModuleCat.hom_comp, Cone.whisker_π, Functor.whiskerLeft_app] at h
  -- The selected leg has source the cone point, definitionally the concrete limit module.
  erw [(F.subsequence φ).limCone_π_app n, F.limCone_π_app (φ n)] at h
  exact ModuleCat.hom_ext h

/-- Restricting compatible families to a cofinal monotone sequence preserves the inverse
limit. The forward map is restriction, even when the sequence repeats indices. -/
def limSubsequenceEquiv (hφ : ∀ n, ∃ m, n ≤ φ m) :
    F.lim ≃ₗ[R] (F.subsequence φ).lim :=
  (F.limSubsequenceIso φ hφ).toLinearEquiv

/-- The cofinal comparison restricts a compatible family to the selected indices. -/
@[simp]
theorem coe_limSubsequenceEquiv_apply (hφ : ∀ n, ∃ m, n ≤ φ m)
    (x : F.lim) (n : ℕ) :
    (F.limSubsequenceEquiv φ hφ x : (F.subsequence φ).Product) n =
      (x : F.Product) (φ n) := by
  have h := congrArg (fun y : (F.subsequence φ).lim ↦ (y : (F.subsequence φ).Product) n)
    (CategoryTheory.Iso.toLinearEquiv_apply (F.limSubsequenceIso φ hφ) x)
  refine h.trans ?_
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, limπ_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (F.limSubsequenceIso_hom_comp_π φ hφ n)) x

/-- Recover an original coordinate by transition from any later selected coordinate.
This also shows that reconstruction is independent of the selected later index. -/
theorem coe_limSubsequenceEquiv_symm_apply (hφ : ∀ n, ∃ m, n ≤ φ m)
    (x : (F.subsequence φ).lim) {n m : ℕ} (hnm : n ≤ φ m) :
    ((F.limSubsequenceEquiv φ hφ).symm x : F.Product) n =
      F.transitionOfLE hnm ((x : (F.subsequence φ).Product) m) := by
  have hx := F.coe_limSubsequenceEquiv_apply φ hφ ((F.limSubsequenceEquiv φ hφ).symm x) m
  rw [LinearEquiv.apply_symm_apply] at hx
  rw [hx, transitionOfLE_coe_lim]

variable {F} {G : ModuleTower.{v} R}

/-- Cofinal restriction is natural in morphisms of module towers. -/
theorem limSubsequenceEquiv_naturality (hφ : ∀ n, ∃ m, n ≤ φ m) (f : F ⟶ G) :
    (G.limSubsequenceEquiv φ hφ).toLinearMap ∘ₗ limMap f =
      limMap (Functor.whiskerLeft φ.monotone.functor.op f) ∘ₗ
        (F.limSubsequenceEquiv φ hφ).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  simp [productMap_apply]

end TauCeti.ModuleTower
