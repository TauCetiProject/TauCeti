/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralCutoff
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Eigenbasis functional calculus for compact resolvent

For a self-adjoint partial linear map `A` with compact resolvent on a Hilbert space `H`, any
function `f : ℝ → ℂ` defines a closed partial operator `A.eigenCalculus hA h f`, and any bounded
`f : ℝ → ℂ` defines a bounded operator `A.boundedEigenCalculus hA h f hf` acting diagonally by
`f (λᵢ)` in any orthonormal eigenbasis of `A`.

## Main definitions

* `LinearPMap.eigenCalculus`: the unbounded eigenbasis functional calculus `f(A)`.
* `LinearPMap.boundedEigenCalculus`: the bounded eigenbasis functional calculus `f(A)`.

## Main results

* `LinearPMap.eigenCalculus_eq_diagonalPMap`, `LinearPMap.eigenCalculus_id`,
  `LinearPMap.isClosed_eigenCalculus`, `LinearPMap.adjoint_eigenCalculus`.
* `LinearPMap.boundedEigenCalculus_eq_diagonal`,
  `LinearPMap.isCompactOperator_boundedEigenCalculus`,
  `LinearPMap.boundedEigenCalculus_unitaryConj`,
  `LinearPMap.mul_boundedEigenCalculus_of_anticommute`.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal InnerProductSpace lp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

section EigenCalculus

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

private def chosenIndex (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) : Type :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose

private def chosenBasis (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    HilbertBasis (chosenIndex hA h) ℂ H :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose_spec.choose

private def chosenEigval (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    chosenIndex hA h → ℝ :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose

private theorem chosenBasis_spec (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (k : chosenIndex hA h) :
    ∃ hk : chosenBasis hA h k ∈ A.domain,
      A ⟨chosenBasis hA h k, hk⟩ = (chosenEigval hA h k : ℂ) • chosenBasis hA h k :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose_spec k

/-- **Unbounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and any function `f : ℝ → ℂ`, `A.eigenCalculus hA h f` is the diagonal partial linear
map acting by multiplication by `f (λᵢ)` in any orthonormal eigenbasis of `A`. It does not depend
on the choice of eigenbasis (`LinearPMap.eigenCalculus_eq_diagonalPMap`). -/
def eigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  (chosenBasis hA h).diagonalPMap fun k ↦ f (chosenEigval hA h k)

/-- Characterization of `eigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem eigenCalculus_eq_diagonalPMap {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i) (f : ℝ → ℂ) :
    A.eigenCalculus hA h f = b.diagonalPMap fun i ↦ f (lam i) :=
  hA.isFormalAdjoint.diagonalPMap_eq_diagonalPMap (chosenBasis_spec hA h) hb f

/-- Applying the eigenbasis functional calculus to the identity function recovers `A`. -/
@[simp]
theorem eigenCalculus_id : A.eigenCalculus hA h (fun t ↦ (t : ℂ)) = A :=
  (hA.eq_diagonalPMap (chosenBasis_spec hA h)).symm

/-- Every operator in the eigenbasis functional calculus is closed. -/
theorem isClosed_eigenCalculus (f : ℝ → ℂ) : (A.eigenCalculus hA h f).IsClosed :=
  (chosenBasis hA h).isClosed_diagonalPMap _

/-- The adjoint of `f(A)` is `(star f)(A)`. -/
@[simp]
theorem adjoint_eigenCalculus (f : ℝ → ℂ) :
    (A.eigenCalculus hA h f)† = A.eigenCalculus hA h (star f) :=
  (chosenBasis hA h).adjoint_diagonalPMap _

/-- A real-valued function of `A` is self-adjoint. -/
theorem isSelfAdjoint_eigenCalculus {f : ℝ → ℂ} (hf : ∀ t, star (f t) = f t) :
    IsSelfAdjoint (A.eigenCalculus hA h f) :=
  (chosenBasis hA h).isSelfAdjoint_diagonalPMap (funext fun _ ↦ hf _)

/-- On an eigenvector of `A` with real eigenvalue `r`, `f(A)` is defined and acts as scalar
multiplication by `f r`. -/
theorem eigenCalculus_apply_of_apply_eq_smul (f : ℝ → ℂ) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    ∃ hmem : (x : H) ∈ (A.eigenCalculus hA h f).domain,
      A.eigenCalculus hA h f ⟨x, hmem⟩ = f r • (x : H) := by
  have hgraph : ((x : H), f r • (x : H)) ∈ (A.eigenCalculus hA h f).graph := by
    rw [eigenCalculus, HilbertBasis.mem_graph_diagonalPMap_iff]
    intro k
    rw [inner_smul_right]
    by_cases hkr : chosenEigval hA h k = r
    · rw [hkr]
    · obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
      simp [hA.isFormalAdjoint.inner_eq_zero_of_apply_eq_smul
        (x := ⟨chosenBasis hA h k, hk⟩) (y := x) hAk hx (Complex.ofReal_injective.ne hkr)]
  obtain ⟨⟨y, hy⟩, hyx, hfu⟩ := (mem_graph_iff _).1 hgraph
  dsimp only at hyx hfu
  subst hyx
  exact ⟨hy, hfu⟩

private def boundedFamily {ι : Type*} (lam : ι → ℝ) (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    ℓ^∞(ι, ℂ) :=
  ⟨fun i ↦ f (lam i), memℓp_infty <| by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC (lam i)⟩⟩

/-- **Bounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and a bounded function `f : ℝ → ℂ`, `A.boundedEigenCalculus hA h f hf` is the bounded
diagonal operator acting by multiplication by `f (λᵢ)` in any orthonormal eigenbasis of `A`. -/
def boundedEigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) : H →L[ℂ] H :=
  (chosenBasis hA h).diagonal (boundedFamily (chosenEigval hA h) f hf)

/-- Viewed as an everywhere-defined partial linear map, `boundedEigenCalculus` coincides with
`eigenCalculus`. -/
theorem boundedEigenCalculus_toPMap (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤) = A.eigenCalculus hA h f :=
  ((chosenBasis hA h).diagonalPMap_eq_toPMap _).symm

/-- Characterization of `boundedEigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem boundedEigenCalculus_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = f (lam i)) :
    A.boundedEigenCalculus hA h f hf = b.diagonal m := by
  have hPMap : ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤) =
      ((b.diagonal m : H →ₗ[ℂ] H).toPMap ⊤) := by
    rw [boundedEigenCalculus_toPMap, eigenCalculus_eq_diagonalPMap hA h b hb f,
      ← b.diagonalPMap_eq_toPMap m]
    congr 1; exact funext fun i ↦ (hm i).symm
  ext x
  exact @(LinearPMap.ext_iff.1 hPMap).2 x Submodule.mem_top Submodule.mem_top

/-- `boundedEigenCalculus` depends only on the function `f`. -/
theorem boundedEigenCalculus_congr {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∀ t, f t = g t) :
    A.boundedEigenCalculus hA h f hf = A.boundedEigenCalculus hA h g hg := by
  have hm : boundedFamily (chosenEigval hA h) f hf = boundedFamily (chosenEigval hA h) g hg :=
    lp.ext (funext fun k ↦ by simp [boundedFamily, hfg])
  rw [boundedEigenCalculus, boundedEigenCalculus, hm]

/-- On an eigenvector of `A` with real eigenvalue `r`, `boundedEigenCalculus` acts as scalar
multiplication by `f r`. -/
theorem boundedEigenCalculus_apply_of_apply_eq_smul {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedEigenCalculus hA h f hf x = f r • (x : H) := by
  obtain ⟨hmem, hfx⟩ := A.eigenCalculus_apply_of_apply_eq_smul hA h f x hx
  have hgraph : ((x : H), f r • (x : H)) ∈
      ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤).graph := by
    rw [A.boundedEigenCalculus_toPMap hA h f hf, ← hfx]
    exact (A.eigenCalculus hA h f).mem_graph ⟨x, hmem⟩
  obtain ⟨u, hu, hfu⟩ := (mem_graph_iff _).1 hgraph
  dsimp only at hu hfu; rw [← hfu, ← hu]; rfl

/-- `0(A) = 0`. -/
@[simp]
theorem boundedEigenCalculus_zero (h0 : ∃ C, ∀ _ : ℝ, ‖(0 : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun _ ↦ 0) h0 = 0 := by
  rw [boundedEigenCalculus_eq_diagonal hA h (chosenBasis hA h) (chosenBasis_spec hA h) _ _ 0
    (fun _ ↦ rfl), _root_.map_zero]

/-- `1(A) = 1`. -/
@[simp]
theorem boundedEigenCalculus_one (h1 : ∃ C, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun _ ↦ 1) h1 = 1 := by
  rw [boundedEigenCalculus_eq_diagonal hA h (chosenBasis hA h) (chosenBasis_spec hA h) _ _ 1
    (fun _ ↦ rfl), _root_.map_one]

/-- `(f + g)(A) = f(A) + g(A)`. -/
theorem boundedEigenCalculus_add {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∃ C, ∀ t, ‖f t + g t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ f t + g t) hfg =
      A.boundedEigenCalculus hA h f hf + A.boundedEigenCalculus hA h g hg := by
  have hm : boundedFamily (chosenEigval hA h) (fun t ↦ f t + g t) hfg =
      boundedFamily (chosenEigval hA h) f hf + boundedFamily (chosenEigval hA h) g hg :=
    lp.ext (funext fun _ ↦ rfl)
  rw [boundedEigenCalculus, boundedEigenCalculus, boundedEigenCalculus, hm, _root_.map_add]

/-- `(c • f)(A) = c • f(A)`. -/
theorem boundedEigenCalculus_smul (c : ℂ) {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hcf : ∃ C, ∀ t, ‖c * f t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ c * f t) hcf =
      c • A.boundedEigenCalculus hA h f hf := by
  have hm : boundedFamily (chosenEigval hA h) (fun t ↦ c * f t) hcf =
      c • boundedFamily (chosenEigval hA h) f hf :=
    lp.ext (funext fun k ↦ by simp [boundedFamily])
  rw [boundedEigenCalculus, boundedEigenCalculus, hm, _root_.map_smul]

/-- `(f * g)(A) = f(A) * g(A)`. -/
theorem boundedEigenCalculus_mul {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∃ C, ∀ t, ‖f t * g t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ f t * g t) hfg =
      A.boundedEigenCalculus hA h f hf * A.boundedEigenCalculus hA h g hg := by
  have hm : boundedFamily (chosenEigval hA h) (fun t ↦ f t * g t) hfg =
      boundedFamily (chosenEigval hA h) f hf * boundedFamily (chosenEigval hA h) g hg :=
    lp.ext (funext fun k ↦ by simp [boundedFamily])
  rw [boundedEigenCalculus, boundedEigenCalculus, boundedEigenCalculus, hm, _root_.map_mul]

/-- `star (f(A)) = (star f)(A)`. -/
theorem star_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hfs : ∃ C, ∀ t, ‖star (f t)‖ ≤ C) :
    star (A.boundedEigenCalculus hA h f hf) =
      A.boundedEigenCalculus hA h (fun t ↦ star (f t)) hfs := by
  have hm : star (boundedFamily (chosenEigval hA h) f hf) =
      boundedFamily (chosenEigval hA h) (fun t ↦ star (f t)) hfs :=
    lp.ext (funext fun k ↦ by simp [boundedFamily])
  rw [boundedEigenCalculus, boundedEigenCalculus, HilbertBasis.star_diagonal, hm]

/-- A bounded real-valued function of `A` is a self-adjoint bounded operator. -/
theorem isSelfAdjoint_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hreal : ∀ t, star (f t) = f t) : IsSelfAdjoint (A.boundedEigenCalculus hA h f hf) :=
  (chosenBasis hA h).isSelfAdjoint_diagonal (by ext k; exact hreal _)

/-- Operator norm bound: if `‖f t‖ ≤ C` for all `t` with `0 ≤ C`, then `‖f(A)‖ ≤ C`. -/
theorem norm_boundedEigenCalculus_le {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) {C : ℝ}
    (hC₀ : 0 ≤ C) (hC : ∀ t, ‖f t‖ ≤ C) : ‖A.boundedEigenCalculus hA h f hf‖ ≤ C := by
  rw [boundedEigenCalculus, HilbertBasis.norm_diagonal]
  exact lp.norm_le_of_forall_le hC₀ fun k ↦ hC _

/-- If `f : ℝ → ℂ` vanishes at infinity (`cocompact ℝ`), then `f(A)` is a compact operator. -/
theorem isCompactOperator_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hlim : Tendsto f (cocompact ℝ) (𝓝 0)) :
    IsCompactOperator (A.boundedEigenCalculus hA h f hf) := by
  rw [boundedEigenCalculus, HilbertBasis.isCompactOperator_diagonal_iff]
  have hN : Northcott fun k ↦ |chosenEigval hA h k| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      h.northcott_norm_of_orthonormal (chosenBasis hA h).orthonormal (chosenBasis_spec hA h)
  have hlim_eig : Tendsto (chosenEigval hA h) cofinite (cocompact ℝ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simpa only [Real.norm_eq_abs] using (northcott_iff_tendsto _).1 hN
  exact hlim.comp hlim_eig

/-- The bounded functional calculus applied to `t ↦ (1 + t²)⁻¹` equals `A.invOneAddSq`. -/
theorem boundedEigenCalculus_invOneAddSq
    (hf : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ (((1 + t ^ 2)⁻¹ : ℝ) : ℂ)) hf = A.invOneAddSq := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    invOneAddSq_apply_of_apply_eq_smul hA.I_mem_resolventSet hA.neg_I_mem_resolventSet ⟨_, hj⟩ hAj]
  push_cast; rfl

/-- Unitary conjugation commutes with the bounded eigenbasis functional calculus. -/
theorem boundedEigenCalculus_unitaryConj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (f : ℝ → ℂ)
    (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (unitaryConj U A).boundedEigenCalculus (isSelfAdjoint_unitaryConj hA)
      ((hasCompactResolvent_unitaryConj_iff U).2 h) f hf =
      U.conjStarAlgEquiv (A.boundedEigenCalculus hA h f hf) := by
  set b := chosenBasis hA h
  set lam := chosenEigval hA h
  have hb' : ∀ k, ∃ hk : b.mapₗᵢ U k ∈ (unitaryConj U A).domain,
      unitaryConj U A ⟨b.mapₗᵢ U k, hk⟩ = (lam k : ℂ) • b.mapₗᵢ U k := fun k ↦ by
    obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
    refine ⟨by rw [HilbertBasis.mapₗᵢ_apply]; exact map_mem_unitaryConj_domain U A ⟨b k, hk⟩, ?_⟩
    simp only [HilbertBasis.mapₗᵢ_apply]
    rw [unitaryConj_apply_map U A ⟨b k, hk⟩, hAk, _root_.map_smul]
  refine (b.mapₗᵢ U).ext_inner_apply (b.mapₗᵢ U) fun i j ↦ ?_
  obtain ⟨hj', hAj'⟩ := hb' j
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul _ _ hf ⟨_, hj'⟩ hAj',
    LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, HilbertBasis.mapₗᵢ_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    HilbertBasis.mapₗᵢ_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨b j, hj⟩ hAj, _root_.map_smul]

/-- **Anticommutation with odd functions.** If a bounded operator `γ` preserves the domain of `A`
and anticommutes with `A` on `D(A)`, then `γ` anticommutes with `f(A)` for every bounded odd
function `f`. -/
theorem mul_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.2⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hodd : ∀ t, f (-t) = -f t) :
    γ * A.boundedEigenCalculus hA h f hf = -(A.boundedEigenCalculus hA h f hf * γ) := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig := apply_eq_neg_smul_of_anticommute hγdom hγA ⟨_, hj⟩ hAj
  rw [← Complex.ofReal_neg] at hγeig
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, _root_.neg_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hγdom _ hj⟩ hγeig,
    hodd, _root_.map_smul, _root_.neg_smul, neg_neg]

/-- **Commutation with even functions.** If a bounded operator `γ` preserves the domain of `A` and
anticommutes with `A` on `D(A)`, then `γ` commutes with `f(A)` for every bounded even function
`f`. -/
theorem commute_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.2⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (heven : ∀ t, f (-t) = f t) :
    Commute γ (A.boundedEigenCalculus hA h f hf) := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig := apply_eq_neg_smul_of_anticommute hγdom hγA ⟨_, hj⟩ hAj
  rw [← Complex.ofReal_neg] at hγeig
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hγdom _ hj⟩ hγeig,
    heven, _root_.map_smul]

end EigenCalculus

end LinearPMap
