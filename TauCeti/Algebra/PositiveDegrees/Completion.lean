/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Grading
public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient
import TauCeti.Algebra.DirectSum.Internal

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

The component formulas for maps are adapted from
`Mei/Algebra/PositiveDegrees/Naturality.lean` in the same repository, commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
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

section Map

variable {K S P : Type*} [AddCommMonoid K] [Ring S] [AddCommGroup P] [Module S P]
  [DecidableEq K] (e : PositiveDegrees K) (𝓝 : K → Submodule S P) [Decomposition 𝓝]
  (L : ℕ → Submodule S P) (hL : Antitone L) (hLe : ∀ k, L k = e.degreeSubmodule 𝓝 k)
  {τ : R →+* S} (f : M →ₛₗ[τ] P) (σ : N → K)
  (hσ : ∀ n x, x ∈ ℳ n → f x ∈ 𝓝 (σ n))
  (hf : ∀ k, ∃ l, J l ≤ (L k).comap f)

include hℳ hσ in
open Classical in
/-- A component of a homogeneous semilinear map on completions sums the images of the source
components over the corresponding fiber. The source cutoff can be any cutoff which computes the
chosen target quotient. -/
theorem completionComponent_limQuotientsMap_eq_sum {m k : ℕ}
    (hm : J m ≤ (L k).comap f) {j : K} (hj : e.degree j ≤ k)
    (x : (ModuleTower.quotients J hJ).lim) :
    (e.completionComponent 𝓝 L hL hLe j (ModuleTower.limQuotientsMap hJ hL f hf x) : P) =
      ∑ n ∈ (d.finite_cutoff m).toFinset with σ n = j,
        f (d.completionComponent ℳ J hJ hJd n x : M) := by
  have hx := (d.projection_eq_sum_completionComponent ℳ J hJ hJd hℳ m x).symm
  rw [e.completionComponent_eq_quotientComponent 𝓝 L hL hLe j k hj,
    ModuleTower.limπ_limQuotientsMap hJ hL f hf hm hx, quotientComponent_mk, map_sum]
  have hproj (n : N) :
      (decompose 𝓝 (f (d.completionComponent ℳ J hJ hJd n x : M)) j : P) =
        if σ n = j then f (d.completionComponent ℳ J hJ hJd n x : M) else 0 := by
    have hn := hσ n _ (d.completionComponent ℳ J hJ hJd n x).property
    split_ifs with h
    · exact decompose_of_mem_same 𝓝 (h ▸ hn)
    · exact decompose_of_mem_ne 𝓝 hn h
  simp only [decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [hproj]
  rw [Finset.sum_filter]

include hσ in
/-- For an injective regrading, the completed map commutes with taking a homogeneous
component. This holds even if the grading has nonzero pieces outside the positive monoid. -/
theorem completionComponent_limQuotientsMap_of_injective (hinj : Function.Injective σ)
    (n : N) (x : (ModuleTower.quotients J hJ).lim) :
    (e.completionComponent 𝓝 L hL hLe (σ n) (ModuleTower.limQuotientsMap hJ hL f hf x) : P) =
      f (d.completionComponent ℳ J hJ hJd n x : M) := by
  let k := (e.degree (σ n)).toNat
  obtain ⟨m, hm⟩ := hf k
  let l := max m (d.degree n).toNat
  have hnl : d.degree n ≤ l :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.mpr (le_max_right _ _))
  have hl : J l ≤ (L k).comap f := (hJ (le_max_left _ _)).trans hm
  obtain ⟨a, ha⟩ :=
    ModuleTower.quotientsπ_surjective J hJ l ((ModuleTower.quotients J hJ).limπ l x)
  rw [e.completionComponent_eq_quotientComponent 𝓝 L hL hLe (σ n) k (Int.self_le_toNat _),
    ModuleTower.limπ_limQuotientsMap hJ hL f hf hl ha, quotientComponent_mk,
    d.completionComponent_eq_quotientComponent ℳ J hJ hJd n l hnl, ← ha,
    quotientComponent_mk]
  exact (DirectSum.map_decompose_shift ℳ 𝓝 f.toAddMonoidHom σ hinj hσ n a).symm

end Map

end TauCeti.PositiveDegrees
