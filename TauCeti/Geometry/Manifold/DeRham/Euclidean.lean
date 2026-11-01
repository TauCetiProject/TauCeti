/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.RealLine
import TauCeti.Geometry.Manifold.DeRham.Sphere
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Compactly supported de Rham cohomology of `ℝⁿ`

On a finite-dimensional real normed space `E` of dimension `n`, the compactly supported de Rham
cohomology `H^k_c(E)` vanishes in every degree `k ≠ n`
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`), and in degree `n`
integration `H^n_c(E) → ℝ` is an isomorphism for either orientation of `E`
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`). In degree zero and
above the dimension the vanishing is already known on every connected noncompact manifold,
respectively on every `n`-manifold; the content is the range `0 < k ≤ n`. Compact supports are not
homotopy invariant, so none of this follows from the cohomology `H^•_dR(E)`. The top degree is
the base case for computing the top compactly supported cohomology of a connected oriented
manifold, and with it the mapping degree.

Both proofs transfer to an inner product space and run through the complement of a large closed
ball. Let `ω` be a compactly supported closed `k`-form with `0 < k ≤ n`, supported in the closed
ball of radius `r`. By the Poincaré lemma `ω = dη` for a smooth `(k - 1)`-form `η`, which is closed
on the complement `E \ closedBall 0 r`. That complement deformation retracts onto the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`), and it is connected for `n ≥ 2`.

* For `k < n`, the cohomology of `Sⁿ⁻¹` vanishes in degree `k - 1` when `k ≥ 2`, so `η` is exact on
  the complement, and `η` is constant there when `k = 1`. A cut-off at infinity then turns `η` into
  a compactly supported primitive of `ω`
  (`TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and its
  degree-zero form).
* For `k = n ≥ 2`, the cohomology of `Sⁿ⁻¹` in degree `n - 1` is a line. So for two compactly
  supported top forms the classes of their primitives on the complement are linearly dependent,
  and the same cut-off shows that a nontrivial combination of the two forms has a compactly
  supported primitive. Hence `H^n_c(E)` has rank at most one. Integration vanishes on compactly
  supported exact forms by Stokes' theorem and takes the value `±1` on a normalized bump function
  times a determinant form, so it is an isomorphism. The cases `n = 0` (a point) and `n = 1` (the
  line, `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_real`) are treated
  separately.

## Main results

* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E) = 0` for
  `k ≠ dim E`.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`: integration
  `H^n_c(E) → ℝ` is bijective for `n = dim E`, for every orientation of `E`.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E)` is one-dimensional
  for `k = dim E` and zero otherwise.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, *Cohomology with Compact
  Support*, Lemma 17.27 and Theorem 17.28 (the compactly supported cohomology of `ℝⁿ`).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set TopologicalSpace Metric Module Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth function on the open subset `⊤` of `E` that vanishes near the closed ball of radius
`R` and equals one off a larger ball: one minus a bump function. -/
private theorem exists_cutoff_compl_closedBall (R : ℝ) :
    ∃ ρ : (⊤ : Opens E) → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ ∧
      (∀ x : (⊤ : Opens E), (x : E) ∉
          (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) →
        ∀ᶠ y in 𝓝 x, ρ y = 0) ∧
      HasCompactSupport fun x ↦ 1 - ρ x := by
  let b : ContDiffBump (0 : E) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x ↦ 1 - b x, contMDiff_const.sub (b.contDiff.contMDiff.comp contMDiff_subtype_val),
    fun x hx ↦ ?_, ?_⟩
  · have hxb : (x : E) ∈ ball (0 : E) (max R 0 + 1) := by
      simp only [Opens.mem_mk, mem_compl_iff, not_not, mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      linarith [le_max_left R 0]
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hxb)] with y hy
    simp [b.one_of_mem_closedBall (ball_subset_closedBall hy)]
  · simpa [Function.comp_def] using b.hasCompactSupport.comp_homeomorph
      (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) ⊤ rfl).toHomeomorph

omit [FiniteDimensional ℝ E] in
/-- On a real inner product space `E`, read as the open subset `⊤` of itself, a closed
`(j + 1)`-form supported in the closed ball of radius `R` is the exterior derivative of a
smooth form that is closed on the complement of that ball. -/
private theorem exists_mextDerivₗ_eq_and_mpullback_mem_closedForms {j : ℕ} {R : ℝ}
    {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (j + 1)}
    (hφ : φ ∈ closedForms 𝓘(ℝ, E) (⊤ : Opens E) (j + 1))
    (hR : Subtype.val '' _root_.tsupport (α := E [⋀^Fin (j + 1)]→L[ℝ] ℝ) φ.1 ⊆
      closedBall (0 : E) R) :
    ∃ η : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ j, mextDerivₗ 𝓘(ℝ, E) j η = φ ∧
      SmoothForm.mpullback (Opens.inclusion (le_top : (⟨(closedBall (0 : E) R)ᶜ,
          isClosed_closedBall.isOpen_compl⟩ : Opens E) ≤ ⊤)) (contMDiff_inclusion le_top) η ∈
        closedForms 𝓘(ℝ, E)
          (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) j := by
  -- `⊤` is diffeomorphic to `E`, so by the Poincaré lemma `φ = dη` for a smooth form `η`.
  have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :=
    have := subsingleton_deRhamCohomology_normedSpace E j
    (deRhamCohomology.equivOfDiffeomorph (Diffeomorph.ofTop (⊤ : Opens E) rfl)
      (j + 1)).symm.toEquiv.subsingleton
  have hφe := (deRhamCohomology.mk_eq_zero_iff _ _ ⟨φ, hφ⟩).mp (Subsingleton.elim _ _)
  rw [exactForms_succ] at hφe
  obtain ⟨η, rfl⟩ := hφe
  -- The form `η` is closed off the ball, where `dη` vanishes.
  refine ⟨η, rfl, ?_⟩
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback]
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [SmoothForm.coe_mpullback, mpullback_inclusion_apply]
  -- The value of `dη` vanishes off its support; the two zeros differ only through the
  -- identification of the fibre at `x` with the model fibre.
  exact (image_eq_zero_of_notMem_tsupport fun hx ↦ x.2 (hR ⟨_, hx, rfl⟩)).trans rfl

/-- On a finite-dimensional real inner product space `E`, read as the open subset `⊤` of itself,
every compactly supported closed form of degree `0 < k < dim E` is the exterior derivative of a
compactly supported form. -/
private theorem mem_exactCompactlySupportedForms_top {k : ℕ} (hk : 0 < k)
    (hkE : k < finrank ℝ E) {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ k}
    (hφ : φ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) k) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) k := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n + 1 := ⟨finrank ℝ E - 1, by omega⟩
  have : Fact (finrank ℝ E = n + 1) := ⟨hn⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hφc, hφd⟩ := (mem_compactlySupportedClosedForms _).mp hφ
  -- `φ` is supported in a closed ball of radius `R ≥ 0`; let `U` be its complement. Then
  -- `φ = dη` for a smooth form `η` closed on `U`.
  obtain ⟨r, hr⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max r 0
  have hR : 0 ≤ R := le_max_right r 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  obtain ⟨η, rfl, hηU⟩ := exists_mextDerivₗ_eq_and_mpullback_mem_closedForms hφd
    (hr.trans (closedBall_subset_closedBall (le_max_left r 0)))
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  rcases j with _ | j
  · -- In degree one, `η` is a function, constant on the connected set `U`.
    have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp <|
      isPreconnected_compl_closedBall (by rw [← finrank_eq_rank]; exact_mod_cast hkE) 0 R
    have hUc : IsCompact {x : (⊤ : Opens E) | (x : E) ∉ U} := by
      let Φ : (⊤ : Opens E) ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E := Diffeomorph.ofTop _ rfl
      have : {x : (⊤ : Opens E) | (x : E) ∉ U} = Φ ⁻¹' closedBall 0 R := by
        ext x
        simp [U, Φ]
      rw [this]
      exact Φ.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 R)
    exact mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_closedForms hUW hUc hηU
  · -- In degree `j + 2 < dim E`, the class of `η` on `U ≃ Sⁿ` vanishes.
    have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) U (j + 1)) :=
      have := subsingleton_deRhamCohomology_sphere (E := E) (n := n) (k := j + 1) j.succ_pos
        (by omega)
      (deRhamCohomology.closedBallComplEquivSphere E n hR (j + 1)).toEquiv.subsingleton
    exact mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU hρc
      ((deRhamCohomology.mk_eq_zero_iff _ _ ⟨_, hηU⟩).mp (Subsingleton.elim _ _))

/-- On a real inner product space `E` of dimension `m + 2`, read as the open subset `⊤` of itself,
two compactly supported top forms have a nontrivial linear combination that is the exterior
derivative of a compactly supported form. -/
private theorem exists_smul_add_smul_mem_exactCompactlySupportedForms_top {m : ℕ}
    (hm : finrank ℝ E = m + 2) {φ ψ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (m + 2)}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (m + 2))
    (hψ : ψ ∈ compactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (m + 2)) :
    ∃ s t : ℝ, (s = 0 → t ≠ 0) ∧
      s • φ + t • ψ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (m + 2) := by
  have : Fact (finrank ℝ E = m + 1 + 1) := ⟨hm⟩
  -- Both forms are supported in the closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r₁, hr₁⟩ := (((mem_compactlySupportedForms _).mp hφ).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  obtain ⟨r₂, hr₂⟩ := (((mem_compactlySupportedForms _).mp hψ).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max (max r₁ r₂) 0
  have hR : 0 ≤ R := le_max_right _ 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  -- Primitives `η` of `φ` and `θ` of `ψ`, both closed on `U`.
  obtain ⟨η, rfl, hη⟩ := exists_mextDerivₗ_eq_and_mpullback_mem_closedForms
    (mem_closedForms_of_finrank_le _ hm.le φ)
    (hr₁.trans (closedBall_subset_closedBall ((le_max_left r₁ r₂).trans (le_max_left _ 0))))
  obtain ⟨θ, rfl, hθ⟩ := exists_mextDerivₗ_eq_and_mpullback_mem_closedForms
    (mem_closedForms_of_finrank_le _ hm.le ψ)
    (hr₂.trans (closedBall_subset_closedBall ((le_max_right r₁ r₂).trans (le_max_left _ 0))))
  -- Their classes on `U`, whose cohomology in degree `m + 1` is a line, are linearly dependent.
  have hU : finrank ℝ (deRhamCohomology 𝓘(ℝ, E) U (m + 1)) = 1 :=
    (deRhamCohomology.closedBallComplEquivSphere E (m + 1) hR (m + 1)).finrank_eq.trans
      (finrank_deRhamCohomology_sphere_self m.succ_pos)
  have : Module.Finite ℝ (deRhamCohomology 𝓘(ℝ, E) U (m + 1)) :=
    Module.finite_of_finrank_eq_succ hU
  have hdep : ¬LinearIndependent ℝ
      ![deRhamCohomology.mk 𝓘(ℝ, E) (m + 1) ⟨_, hη⟩,
        deRhamCohomology.mk 𝓘(ℝ, E) (m + 1) ⟨_, hθ⟩] := fun h ↦
    absurd (h.fintype_card_le_finrank.trans_eq hU) (by simp)
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨s, t, h0, hst⟩ := hdep
  refine ⟨s, t, hst, ?_⟩
  -- So `s η + t θ` is exact on `U`, and a cut-off turns it into a compactly supported primitive.
  have hex : SmoothForm.mpullback (Opens.inclusion hUW) (contMDiff_inclusion hUW) (s • η + t • θ) ∈
      exactForms 𝓘(ℝ, E) U (m + 1) := by
    have h := (deRhamCohomology.mk_eq_zero_iff _ _ (s • ⟨_, hη⟩ + t • ⟨_, hθ⟩)).mp
      (by rw [map_add, map_smul, map_smul, h0])
    simpa using h
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  simpa using mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU
    hρc hex

/-- On a real inner product space `E` of dimension `m + 2`, read as the open subset `⊤` of itself,
the top compactly supported de Rham cohomology has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_top_le_one {m : ℕ}
    (hm : finrank ℝ E = m + 2) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (m + 2)) ≤ 1 := by
  rw [rank_le_one_iff]
  by_cases h : ∃ c₀ : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (m + 2), c₀ ≠ 0
  · obtain ⟨c₀, hc₀⟩ := h
    refine ⟨c₀, fun c ↦ ?_⟩
    obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ c
    obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ c₀
    obtain ⟨s, t, hst, he⟩ := exists_smul_add_smul_mem_exactCompactlySupportedForms_top hm
      ((mem_compactlySupportedClosedForms _).mp φ.2).1
      ((mem_compactlySupportedClosedForms _).mp ψ.2).1
    have h0 : s • compactlySupportedDeRhamCohomology.mk 𝓘(ℝ, E) (m + 2) φ +
        t • compactlySupportedDeRhamCohomology.mk 𝓘(ℝ, E) (m + 2) ψ = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, compactlySupportedDeRhamCohomology.mk_eq_zero_iff]
      simpa using he
    -- The coefficient of `φ` is nonzero, since the class of `ψ` is.
    have hs : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add, smul_eq_zero] at h0
      exact h0.elim (hst rfl) hc₀
    refine ⟨-t / s, ?_⟩
    rw [div_eq_inv_mul, mul_smul, neg_smul, ← eq_neg_of_add_eq_zero_left h0, inv_smul_smul₀ hs]
  · push Not at h
    exact ⟨0, fun c ↦ ⟨0, by rw [h c, smul_zero]⟩⟩

/-- `H^k_c(E) = 0` for `0 < k < dim E`, on a finite-dimensional real inner product space `E`. -/
private theorem subsingleton_compactlySupportedDeRhamCohomology_innerProductSpace {k : ℕ}
    (hk : 0 < k) (hkE : k < finrank ℝ E) :
    Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) := by
  have : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) k) := by
    refine subsingleton_of_forall_eq 0 fun c ↦ ?_
    obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ k c
    exact (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ k φ).mpr
      (mem_exactCompactlySupportedForms_top hk hkE φ.2)
  exact (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (⊤ : Opens E) rfl) k).toEquiv.subsingleton

/-- The top compactly supported de Rham cohomology of a real inner product space of dimension at
least two has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_innerProductSpace_le_one
    (hE : 2 ≤ finrank ℝ E) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) ≤ 1 := by
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 2 := ⟨finrank ℝ E - 2, by omega⟩
  rw [hm]
  exact (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (⊤ : Opens E) rfl) (m + 2)).rank_eq.trans_le
    (rank_compactlySupportedDeRhamCohomology_top_le_one hm)

end InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The compactly supported de Rham cohomology of `ℝⁿ` vanishes outside the top degree.** On a
finite-dimensional real normed space `E`, `H^k_c(E) = 0` for every `k ≠ dim E`. -/
theorem subsingleton_compactlySupportedDeRhamCohomology_normedSpace {k : ℕ}
    (hk : k ≠ finrank ℝ E) : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) := by
  rcases hk.lt_or_gt with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos hk
      exact subsingleton_compactlySupportedDeRhamCohomology_zero 𝓘(ℝ, E) E
    -- Transfer from the Euclidean space of the same dimension.
    have := subsingleton_compactlySupportedDeRhamCohomology_innerProductSpace
      (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) hk₀ (by rwa [finrank_euclideanSpace_fin])
    exact (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
      (toEuclidean (E := E)).toDiffeomorph k).symm.toEquiv.subsingleton
  · exact subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt 𝓘(ℝ, E) E hk

/-- The top compactly supported de Rham cohomology of a finite-dimensional real normed space has
rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_finrank_le_one :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) ≤ 1 := by
  obtain h | h | h : finrank ℝ E = 0 ∨ finrank ℝ E = 1 ∨ 2 ≤ finrank ℝ E := by omega
  · -- A zero-dimensional space is a point, so compactly supported and ordinary cohomology agree.
    have : Subsingleton E := Module.finrank_zero_iff.mp h
    have : CompactSpace E := Finite.compactSpace
    have hfin := finrank_deRhamCohomology_zero 𝓘(ℝ, E) E
    have : Module.Finite ℝ (deRhamCohomology 𝓘(ℝ, E) E 0) := Module.finite_of_finrank_eq_succ hfin
    rw [h, (LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective 𝓘(ℝ, E) 0)).rank_eq,
      ← Module.finrank_eq_rank, hfin, Nat.cast_one]
  · -- A one-dimensional space is a copy of the real line.
    rw [h]
    let Φ := (ContinuousLinearEquiv.ofFinrankEq (h.trans (finrank_self ℝ).symm)).toDiffeomorph
    let o : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1) :=
      Manifold.Orientation.model (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp)
    refine Cardinal.lift_le_one_iff.mp <|
      (compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ 1).lift_rank_eq.symm.trans_le ?_
    rw [Cardinal.lift_le_one_iff, (compactlySupportedDeRhamCohomologyRealEquiv o).rank_eq,
      rank_self]
  · -- Transfer from the Euclidean space of the same dimension.
    have := rank_compactlySupportedDeRhamCohomology_innerProductSpace_le_one
      (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) (by rwa [finrank_euclideanSpace_fin])
    rw [finrank_euclideanSpace_fin] at this
    exact Cardinal.lift_le_one_iff.mp <| (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
      (toEuclidean (E := E)).toDiffeomorph _).lift_rank_eq.symm.trans_le
        (Cardinal.lift_le_one_iff.mpr this)

/-- For every orientation of `E`, integration does not vanish on the top compactly supported
de Rham cohomology. -/
private theorem exists_integral_ne_zero {n : ℕ} (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) :
    ∃ c, compactlySupportedDeRhamCohomology.integral o c ≠ 0 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hn : finrank ℝ E = n := by simpa using o.card_eq.symm
  let b : Module.Basis (Fin n) ℝ E := Module.finBasisOfFinrankEq ℝ E hn
  let f : E → ℝ := (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : E)).normed b.addHaar
  let D : E [⋀^Fin n]→L[ℝ] ℝ := AlternatingMap.toContinuousAlternatingMap b.det
  let φ : RoughForm 𝓘(ℝ, E) E ℝ n := fun x ↦ f x • D
  have hs : IsSmoothForm 𝓘(ℝ, E) ∞ φ :=
    isSmoothForm_modelSpace_iff.mpr ((ContDiffBump.contDiff_normed _).smul contDiff_const)
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin n]→L[ℝ] ℝ) φ) :=
    (ContDiffBump.hasCompactSupport_normed _).isCompact.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_smul_subset_left f fun _ ↦ D)
  let ψ : compactlySupportedClosedForms 𝓘(ℝ, E) E n :=
    ⟨⟨φ, hs.mem_smoothBundleForms⟩, (mem_compactlySupportedClosedForms _).mpr
      ⟨(mem_compactlySupportedForms _).mpr hc, mem_closedForms_of_finrank_le _ hn.le _⟩⟩
  -- Against the orientation of `b`, the integral of `φ` is the integral of the normalized bump.
  let o₀ : Manifold.Orientation 𝓘(ℝ, E) E (Fin n) :=
    Manifold.Orientation.model b.orientation (by simp [hn])
  have hφb (x : E) : φ x b = f x := by
    have h : (f x • D) b = f x := by simp [D, Module.Basis.det_self]
    -- `φ x` is `f x • D` read in the tangent fibre at `x`, which is `E` by definition.
    exact h
  have h₁ : integralTopForm o₀ φ = 1 := by
    rw [integralTopForm_model_eq_integral _ _ (hs.of_le (by simp)) hc b rfl, funext hφb]
    exact ContDiffBump.integral_normed _
  refine ⟨compactlySupportedDeRhamCohomology.mk _ n ψ, ?_⟩
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  rcases Manifold.Orientation.eq_or_eq_neg o o₀ with rfl | rfl
  · exact h₁ ▸ one_ne_zero
  · rw [integralTopForm_neg]
    exact h₁ ▸ neg_ne_zero.mpr one_ne_zero

/-- **The top compactly supported de Rham cohomology of `ℝⁿ`.** For every orientation `o` of a
finite-dimensional real normed space `E`, integration `H^n_c(E) → ℝ` is bijective, where
`n = dim E`. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_normedSpace {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  have hn : finrank ℝ E = n := by simpa using o.card_eq.symm
  subst hn
  obtain ⟨c, hc⟩ := exists_integral_ne_zero E o
  -- Every class is a multiple of one class `v₀`, and integration does not vanish on `v₀`.
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp (rank_compactlySupportedDeRhamCohomology_finrank_le_one E)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦
    ⟨(y / compactlySupportedDeRhamCohomology.integral o c) • c, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc]⟩⟩
  obtain ⟨a, rfl⟩ := hv₀ x
  obtain ⟨b, rfl⟩ := hv₀ c
  rw [map_smul, smul_eq_mul] at hx hc
  rw [(mul_eq_zero.mp hx).resolve_right (right_ne_zero_of_mul hc), zero_smul]

/-- **The top compactly supported de Rham cohomology of `ℝⁿ` is a line.** On a
finite-dimensional real normed space `E`, `H^n_c(E)` is one-dimensional for `n = dim E`. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace_self :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) = 1 :=
  (LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace E
    (Manifold.Orientation.model (Module.finBasisOfFinrankEq ℝ E rfl).orientation
      (Fintype.card_fin _)))).finrank_eq.trans (finrank_self ℝ)

/-- **The compactly supported de Rham cohomology of `ℝⁿ`.** On a finite-dimensional real normed
space `E`, `H^k_c(E)` is one-dimensional in degree `k = dim E` and zero in every other degree. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace (k : ℕ) :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) =
      if k = finrank ℝ E then 1 else 0 := by
  split_ifs with h
  · exact h ▸ finrank_compactlySupportedDeRhamCohomology_normedSpace_self E
  · have := subsingleton_compactlySupportedDeRhamCohomology_normedSpace E h
    exact finrank_zero_of_subsingleton

end TauCeti
