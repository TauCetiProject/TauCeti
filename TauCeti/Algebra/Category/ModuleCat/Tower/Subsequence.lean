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
`ModuleTower.isLimitLimCone`, rather than reconstructing the categorical limit. In particular, a
morphism of towers that is an isomorphism from some index on induces a bijection on `lim`
(`TauCeti.ModuleTower.limMap_bijective_of_isIso_of_le`).

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

/-- Restriction of a product family along `φ`. -/
def subsequenceRestriction : F.Product →ₗ[R] (F.subsequence φ).Product :=
  LinearMap.pi fun n ↦ LinearMap.proj (φ n)

@[simp]
theorem subsequenceRestriction_apply (x : F.Product) (n : ℕ) :
    F.subsequenceRestriction φ x n = x (φ n) :=
  (rfl)

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

/-- Restriction along `φ` commutes with the product map of a morphism of towers. -/
theorem subsequenceRestriction_natural_apply (f : F ⟶ G) (x : F.Product) :
    G.subsequenceRestriction φ (productMap f x) =
      productMap (Functor.whiskerLeft φ.monotone.functor.op f) (F.subsequenceRestriction φ x) := by
  funext n
  simp [productMap_apply]

/-- Shifting a morphism of module towers that is an isomorphism from index `N` on yields an
isomorphism along a cofinal subsequence. -/
theorem exists_cofinal_isIso_whiskerLeft_of_isIso_of_le (f : F ⟶ G) (N : ℕ)
    (hf : ∀ n, N ≤ n → IsIso (f.app (op n))) :
    ∃ (φ : ℕ →o ℕ), (∀ n, ∃ m, n ≤ φ m) ∧
      IsIso (Functor.whiskerLeft φ.monotone.functor.op f) := by
  let φ : ℕ →o ℕ := ⟨(N + ·), fun _ _ h ↦ Nat.add_le_add_left h N⟩
  refine ⟨φ, fun n ↦ ⟨n, Nat.le_add_left n N⟩, ?_⟩
  have : ∀ n, IsIso ((Functor.whiskerLeft φ.monotone.functor.op f).app n) :=
    fun ⟨n⟩ ↦ hf (N + n) (Nat.le_add_right N n)
  exact NatIso.isIso_of_isIso_app _

/-- A morphism of module towers that is an isomorphism from some index on induces a bijection on
inverse limits. -/
theorem limMap_bijective_of_isIso_of_le (f : F ⟶ G) (N : ℕ)
    (hf : ∀ n, N ≤ n → IsIso (f.app (op n))) :
    Function.Bijective (limMap f) := by
  obtain ⟨φ, hφ, hIso⟩ := exists_cofinal_isIso_whiskerLeft_of_isIso_of_le f N hf
  let f' : F.subsequence φ ⟶ G.subsequence φ := Functor.whiskerLeft φ.monotone.functor.op f
  have hbij : Function.Bijective (limMap f' ∘ₗ (F.limSubsequenceEquiv φ hφ).toLinearMap) := by
    have h1 : ⇑(limEquivOfIso (asIso f')) = ⇑(limMap f') := funext (limEquivOfIso_apply _)
    rw [LinearMap.coe_comp, ← h1]
    exact (limEquivOfIso (asIso f')).bijective.comp (F.limSubsequenceEquiv φ hφ).bijective
  rw [← limSubsequenceEquiv_naturality φ hφ f] at hbij
  exact (Function.Bijective.of_comp_iff' (G.limSubsequenceEquiv φ hφ).bijective _).1 hbij

end TauCeti.ModuleTower
