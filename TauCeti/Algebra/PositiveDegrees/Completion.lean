/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Grading
public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient

/-!
# Degree completions as products of homogeneous pieces

The completion of a module supported on a positive degree monoid is linearly
equivalent to the product of its homogeneous pieces. Finite degree cutoffs
reconstruct each quotient from an arbitrary family of homogeneous coefficients.
Conversely, a coefficient of a
compatible quotient family is read at any cutoff containing its degree.

The construction uses Mathlib's internal direct-sum decomposition and the existing
compatible-family limit `ModuleTower.lim` of the degree-submodule quotients. The
submodule family is supplied with its identification with the degree submodules,
so the comparison applies to existing completion carriers. No basis or finiteness
assumption on the homogeneous modules is needed.

Adapted from `Mei/Algebra/PositiveDegrees/Completion.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti.PositiveDegrees

open _root_.DirectSum

variable {N R M : Type*} [AddCommMonoid N] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq N] (d : PositiveDegrees N) (ℳ : N → Submodule R M)
  [Decomposition ℳ]

variable (J : ℕ → Submodule R M) (hJ : Antitone J)
  (hJd : ∀ k, J k = d.degreeSubmodule ℳ k)

local notation "π" => ModuleTower.quotientsπ J hJ

private def componentLinear (n : N) : M →ₗ[R] ℳ n :=
  (DirectSum.component R N (fun n => ℳ n) n).comp (decomposeLinearEquiv ℳ).toLinearMap

/-- A homogeneous component descends to any quotient retaining its degree. -/
def quotientComponent (k : ℕ) (n : N) (hn : d.degree n ≤ k) :
    (ModuleTower.quotients J hJ).obj (Opposite.op k) →ₗ[R] ℳ n :=
  ModuleTower.quotientsLift J hJ k
    (componentLinear ℳ n) (by
    intro x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact (d.mem_degreeSubmodule_iff ℳ).mp ((hJd k) ▸ hx) n hn)

/-- The component of a quotient class is the corresponding homogeneous component. -/
@[simp]
theorem quotientComponent_mk (k : ℕ) (n : N) (hn : d.degree n ≤ k) (x : M) :
    d.quotientComponent ℳ J hJ hJd k n hn (π k x) = decompose ℳ x n :=
  ModuleTower.quotientsLift_quotientsπ _ _ _ _ _ x

/-- Components already retained at the lower cutoff commute with quotient transitions. -/
@[simp]
theorem quotientComponent_transition {k l : ℕ} (h : k ≤ l) (n : N)
    (hn : d.degree n ≤ k) (x : (ModuleTower.quotients J hJ).obj (Opposite.op l)) :
    d.quotientComponent ℳ J hJ hJd k n hn ((ModuleTower.quotients J hJ).transitionOfLE h x) =
      d.quotientComponent ℳ J hJ hJd l n (hn.trans (Int.ofNat_le.mpr h)) x := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ l x
  simp

/-- A finite-degree quotient is determined by the components it retains. -/
theorem quotient_ext {k : ℕ} {x y : (ModuleTower.quotients J hJ).obj (Opposite.op k)}
    (h : ∀ n (hn : d.degree n ≤ k),
      d.quotientComponent ℳ J hJ hJd k n hn x =
        d.quotientComponent ℳ J hJ hJd k n hn y) : x = y := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ k x
  obtain ⟨y, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ k y
  apply (ModuleTower.quotientsπ_eq_quotientsπ_iff _ _).mpr
  rw [hJd k, d.mem_degreeSubmodule_iff ℳ]
  intro n hn
  have he := congrArg Subtype.val (h n hn)
  simpa only [quotientComponent_mk, decompose_sub, DirectSum.sub_apply,
    Submodule.coe_sub, sub_eq_zero] using he

/-- The degree-`n` coefficient of a completed module element. -/
def completionComponent (n : N) : (ModuleTower.quotients J hJ).lim →ₗ[R] ℳ n :=
  (d.quotientComponent ℳ J hJ hJd (d.degree n).toNat n (Int.self_le_toNat _)).comp
    ((ModuleTower.quotients J hJ).limπ (d.degree n).toNat)

/-- Any cutoff containing the degree computes the same completed component. -/
theorem completionComponent_eq_quotientComponent (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) (x : (ModuleTower.quotients J hJ).lim) :
    d.completionComponent ℳ J hJ hJd n x =
      d.quotientComponent ℳ J hJ hJd k n hn ((ModuleTower.quotients J hJ).limπ k x) := by
  have hnk : (d.degree n).toNat ≤ k := by omega
  rw [completionComponent, LinearMap.comp_apply,
    ← LinearMap.congr_fun ((ModuleTower.quotients J hJ).transitionOfLE_comp_limπ hnk) x,
    LinearMap.comp_apply, quotientComponent_transition]

/-- Completed components of canonical elements are their original homogeneous components. -/
@[simp]
theorem completionComponent_of (n : N) (x : M) :
    d.completionComponent ℳ J hJ hJd n (ModuleTower.toLimQuotients J hJ x) = decompose ℳ x n := by
  rw [completionComponent, LinearMap.comp_apply, ModuleTower.limπ_apply,
    ModuleTower.coe_toLimQuotients_apply, quotientComponent_mk]

/-- A completed element has order at least `k + 1` exactly when its coefficients
through order `k` vanish. -/
theorem mem_ker_limπ_iff (x : (ModuleTower.quotients J hJ).lim) (k : ℕ) :
    x ∈ LinearMap.ker ((ModuleTower.quotients J hJ).limπ k) ↔
      ∀ n, d.degree n ≤ k → d.completionComponent ℳ J hJ hJd n x = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx n hn
    rw [completionComponent_eq_quotientComponent d ℳ J hJ hJd n k hn, hx, map_zero]
  · intro hx
    apply d.quotient_ext ℳ J hJ hJd
    intro n hn
    rw [map_zero, ← completionComponent_eq_quotientComponent]
    exact hx n hn

private noncomputable def finiteApprox (k : ℕ) : (∀ n, ℳ n) →ₗ[R] M :=
  ∑ n ∈ (d.finite_cutoff k).toFinset, (ℳ n).subtype.comp (LinearMap.proj n)

variable (hℳ : ∀ n, n ∉ d.monoid → ℳ n = ⊥)

include hℳ in
private theorem decompose_finiteApprox (k : ℕ) (x : ∀ n, ℳ n) (n : N)
    (hn : d.degree n ≤ k) :
    decompose ℳ (d.finiteApprox ℳ k x) n = x n := by
  classical
  apply Subtype.ext
  by_cases hP : n ∈ d.monoid
  · have hn' : n ∈ (d.finite_cutoff k).toFinset := by simp [hP, hn]
    simp only [finiteApprox, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply, decompose_sum, DirectSum.sum_apply,
      Submodule.coe_sum]
    rw [Finset.sum_eq_single n]
    · exact decompose_of_mem_same ℳ (x n).property
    · intro m _ hmn
      exact decompose_of_mem_ne ℳ (x m).property hmn
    · exact fun h => (h hn').elim
  · have hb : ℳ n = ⊥ := hℳ n hP
    have hz (y : ℳ n) : (y : M) = 0 := by simpa only [hb, Submodule.mem_bot] using y.property
    exact (hz _).trans (hz _).symm

private noncomputable def piToQuotient (k : ℕ) :
    (∀ n, ℳ n) →ₗ[R] (ModuleTower.quotients J hJ).obj (Opposite.op k) :=
  (π k).comp (d.finiteApprox ℳ k)

include hℳ in
private theorem quotientComponent_piToQuotient (k : ℕ) (n : N)
    (hn : d.degree n ≤ k) (x : ∀ n, ℳ n) :
    d.quotientComponent ℳ J hJ hJd k n hn (d.piToQuotient ℳ J hJ k x) = x n := by
  rw [piToQuotient, LinearMap.comp_apply, quotientComponent_mk]
  exact d.decompose_finiteApprox ℳ hℳ k x n hn

include hℳ in
private noncomputable def piToCompletion : (∀ n, ℳ n) →ₗ[R] (ModuleTower.quotients J hJ).lim :=
  (ModuleTower.quotients J hJ).limLift (d.piToQuotient ℳ J hJ) (by
    intro k
    apply LinearMap.ext
    intro x
    apply d.quotient_ext ℳ J hJ hJd
    intro n hn
    rw [← ModuleTower.transitionOfLE_succ]
    simp only [LinearMap.comp_apply, quotientComponent_transition,
      d.quotientComponent_piToQuotient ℳ J hJ hJd hℳ])

private theorem completionComponent_piToCompletion (n : N) (x : ∀ n, ℳ n) :
    d.completionComponent ℳ J hJ hJd n (d.piToCompletion ℳ J hJ hJd hℳ x) = x n := by
  simpa only [completionComponent, LinearMap.comp_apply, piToCompletion,
    ModuleTower.limπ_apply, ModuleTower.coe_limLift_apply] using
    d.quotientComponent_piToQuotient ℳ J hJ hJd hℳ (d.degree n).toNat n (Int.self_le_toNat _) x

include hℳ in
/-- The degree completion of a module supported on the positive monoid is the product of its
homogeneous pieces. Finite degree cutoffs reconstruct the inverse. -/
noncomputable def completionEquivPi : (ModuleTower.quotients J hJ).lim ≃ₗ[R] ∀ n, ℳ n :=
  LinearEquiv.ofLinearMap (LinearMap.pi (d.completionComponent ℳ J hJ hJd))
    (d.piToCompletion ℳ J hJ hJd hℳ)
    (by
      apply LinearMap.ext
      intro x
      funext n
      exact d.completionComponent_piToCompletion ℳ J hJ hJd hℳ n x)
    (by
      apply LinearMap.ext
      intro x
      apply ModuleTower.lim_ext
      intro k
      apply d.quotient_ext ℳ J hJ hJd
      intro n hn
      rw [← completionComponent_eq_quotientComponent,
        ← completionComponent_eq_quotientComponent]
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.id_apply,
        d.completionComponent_piToCompletion ℳ J hJ hJd hℳ])

/-- The product comparison reads the completed homogeneous components. -/
@[simp]
theorem completionEquivPi_apply (x : (ModuleTower.quotients J hJ).lim) (n : N) :
    d.completionEquivPi ℳ J hJ hJd hℳ x n = d.completionComponent ℳ J hJ hJd n x := (rfl)

/-- The inverse product comparison has the prescribed homogeneous coefficients. -/
@[simp]
theorem completionComponent_completionEquivPi_symm (x : ∀ n, ℳ n) (n : N) :
    d.completionComponent ℳ J hJ hJd n ((d.completionEquivPi ℳ J hJ hJd hℳ).symm x) = x n :=
  d.completionComponent_piToCompletion ℳ J hJ hJd hℳ n x

/-- At order `k`, the inverse product comparison is the class of the finite sum
of coefficients in the degree cutoff. -/
theorem projection_completionEquivPi_symm (x : ∀ n, ℳ n) (k : ℕ) :
    (ModuleTower.quotients J hJ).limπ k ((d.completionEquivPi ℳ J hJ hJd hℳ).symm x) =
      π k (∑ n ∈ (d.finite_cutoff k).toFinset, (x n : M)) := by
  classical
  calc
    _ = d.piToQuotient ℳ J hJ k x :=
      LinearMap.congr_fun ((ModuleTower.quotients J hJ).limπ_comp_limLift _ _ k) x
    _ = _ := by
      simp only [piToQuotient, LinearMap.comp_apply,
        finiteApprox, LinearMap.sum_apply, LinearMap.proj_apply, Submodule.subtype_apply]

include hℳ in
/-- A finite projection is reconstructed from the completed components in its cutoff. -/
theorem projection_eq_sum_completionComponent (k : ℕ) (x : (ModuleTower.quotients J hJ).lim) :
    (ModuleTower.quotients J hJ).limπ k x = π k
      (∑ n ∈ (d.finite_cutoff k).toFinset, (d.completionComponent ℳ J hJ hJd n x : M)) := by
  have h := d.projection_completionEquivPi_symm ℳ J hJ hJd hℳ
    (d.completionEquivPi ℳ J hJ hJd hℳ x) k
  simpa only [LinearEquiv.symm_apply_apply, completionEquivPi_apply] using h

end TauCeti.PositiveDegrees
