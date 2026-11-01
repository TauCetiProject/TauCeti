/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
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
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`), and integration
against any orientation of `E` is a linear isomorphism `H^n_c(E) ≃ ℝ`
(`TauCeti.compactlySupportedDeRhamCohomologyNormedSpaceEquiv`). In degree zero and above the
dimension the vanishing is already known on every connected noncompact manifold, respectively on
every `n`-manifold; the content is the range `0 < k ≤ n`. Compact supports are not homotopy
invariant, so none of this follows from the vanishing of `H^k_dR(E)` in positive degrees.

The proof transfers to an inner product space and runs through the complement of a large closed
ball. Let `ω` be a compactly supported closed `k`-form with `0 < k ≤ n`, supported in the closed
ball of radius `r`. By the Poincaré lemma `ω = dη` for a smooth `(k - 1)`-form `η`, which is closed
on the complement `E \ closedBall 0 r`. That complement deformation retracts onto the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`), whose cohomology vanishes in degrees
strictly between `0` and `n - 1`, and it is connected for `n ≥ 2`. So `η` is exact on it when
`2 ≤ k < n`, and constant on it when `k = 1 < n`. A cut-off at infinity then turns `η` into a
compactly supported primitive of `ω`
(`TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and its
degree-zero form).

In the top degree `k = n ≥ 2`, the cohomology `Hⁿ⁻¹(Sⁿ⁻¹)` is one-dimensional
(`TauCeti.finrank_deRhamCohomology_sphere_self`). For two compactly supported closed `n`-forms
`ω = dη` and `ω' = dη'`, the classes of `η` and `η'` on the complement of a ball containing both
supports are therefore linearly dependent, and the same cut-off shows that the corresponding
combination of `ω` and `ω'` is the exterior derivative of a compactly supported form. Hence
`H^n_c(E)` has rank at most one. For `n = 1` this follows from the computation on the real line
(`TauCeti.compactlySupportedDeRhamCohomologyRealEquiv`), and for `n = 0`, where `E` is a point, from
the constant classes in degree zero. A normalized bump function times a
determinant form has integral one against the constant orientation of a basis, so integration is
surjective, and therefore bijective.

## Main results

* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E) = 0` for
  `k ≠ dim E`.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`: integration
  `H^n_c(E) → ℝ` is bijective for `n = dim E` and every orientation of `E`.
* `TauCeti.compactlySupportedDeRhamCohomologyNormedSpaceEquiv`: the resulting isomorphism
  `H^n_c(E) ≃ₗ[ℝ] ℝ`.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace`: `H^n_c(E)` is
  one-dimensional.

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
/-- **The Poincaré lemma on `E`**, read as the open subset `⊤` of itself: every closed form of
positive degree is the exterior derivative of a smooth form. -/
private theorem exists_mextDerivₗ_eq_top {j : ℕ} {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (j + 1)}
    (hφ : φ ∈ closedForms 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :
    ∃ η : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ j, mextDerivₗ 𝓘(ℝ, E) j η = φ := by
  have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :=
    have := subsingleton_deRhamCohomology_normedSpace E j
    (deRhamCohomology.equivOfDiffeomorph
      (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) ⊤ rfl) (j + 1)).symm.toEquiv.subsingleton
  have hφe := (deRhamCohomology.mk_eq_zero_iff _ _ ⟨φ, hφ⟩).mp (Subsingleton.elim _ _)
  rw [exactForms_succ] at hφe
  exact hφe

omit [FiniteDimensional ℝ E] in
/-- A smooth form `η` on `E`, read as `⊤`, whose exterior derivative is supported in the closed
ball of radius `R` is closed on the complement of that ball. -/
private theorem mpullback_mem_closedForms_compl_closedBall {j : ℕ} {R : ℝ}
    {η : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ j}
    (hR : Subtype.val '' _root_.tsupport (α := E [⋀^Fin (j + 1)]→L[ℝ] ℝ)
      (mextDerivₗ 𝓘(ℝ, E) j η).1 ⊆ closedBall (0 : E) R) :
    SmoothForm.mpullback (Opens.inclusion (le_top :
        (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ≤ ⊤))
      (contMDiff_inclusion le_top) η ∈
      closedForms 𝓘(ℝ, E) (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E)
        j := by
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
  -- By the Poincaré lemma `φ = dη` for a smooth form `η`.
  obtain ⟨η, rfl⟩ := exists_mextDerivₗ_eq_top hφd
  -- `dη` is supported in a closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r, hr⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max r 0
  have hR : 0 ≤ R := le_max_right r 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  -- The form `η` is closed on `U`, where `dη` vanishes.
  have hηU := mpullback_mem_closedForms_compl_closedBall
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

/-- On a finite-dimensional real inner product space `E` of dimension `k + 2`, read as the open
subset `⊤` of itself, any two compactly supported closed top forms are linearly dependent modulo
exterior derivatives of compactly supported forms. -/
private theorem exists_smul_add_smul_mem_exactCompactlySupportedForms_top {k : ℕ}
    (hkE : finrank ℝ E = k + 2) {φ ψ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (k + 2)}
    (hφ : φ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) (k + 2))
    (hψ : ψ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) (k + 2)) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      a • φ + b • ψ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (k + 2) := by
  have : Fact (finrank ℝ E = (k + 1) + 1) := ⟨hkE⟩
  obtain ⟨hφc, hφd⟩ := (mem_compactlySupportedClosedForms _).mp hφ
  obtain ⟨hψc, hψd⟩ := (mem_compactlySupportedClosedForms _).mp hψ
  -- By the Poincaré lemma `φ = dη` and `ψ = dθ` for smooth forms `η` and `θ`.
  obtain ⟨η, rfl⟩ := exists_mextDerivₗ_eq_top hφd
  obtain ⟨θ, rfl⟩ := exists_mextDerivₗ_eq_top hψd
  -- `dη` and `dθ` are supported in a closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r, hr⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  obtain ⟨s, hs⟩ := (((mem_compactlySupportedForms _).mp hψc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max (max r s) 0
  have hR : 0 ≤ R := le_max_right _ 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  -- Both primitives are closed on `U`, where their exterior derivatives vanish.
  have hηU := mpullback_mem_closedForms_compl_closedBall (hr.trans
    (closedBall_subset_closedBall ((le_max_left r s).trans (le_max_left _ 0))))
  have hθU := mpullback_mem_closedForms_compl_closedBall (hs.trans
    (closedBall_subset_closedBall ((le_max_right r s).trans (le_max_left _ 0))))
  -- `U` has the cohomology of the sphere `Sᵏ⁺¹`, which is one-dimensional in degree `k + 1`, so
  -- the classes of the two primitives on `U` are linearly dependent.
  have hU : finrank ℝ (deRhamCohomology 𝓘(ℝ, E) U (k + 1)) = 1 :=
    (deRhamCohomology.closedBallComplEquivSphere E (k + 1) hR (k + 1)).finrank_eq.trans
      (finrank_deRhamCohomology_sphere_self k.succ_pos)
  let X : closedForms 𝓘(ℝ, E) U (k + 1) := ⟨_, hηU⟩
  let Y : closedForms 𝓘(ℝ, E) U (k + 1) := ⟨_, hθU⟩
  obtain ⟨a, b, hab, h⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      deRhamCohomology.mk 𝓘(ℝ, E) (k + 1) (a • X + b • Y) = 0 := by
    simp only [map_add, map_smul]
    by_cases hy : deRhamCohomology.mk 𝓘(ℝ, E) (k + 1) Y = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, by rw [hy, zero_smul, smul_zero, add_zero]⟩
    · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy).mp hU
        (deRhamCohomology.mk 𝓘(ℝ, E) (k + 1) X)
      exact ⟨1, -c, Or.inl one_ne_zero, by rw [← hc, one_smul, neg_smul, add_neg_cancel]⟩
  -- The corresponding combination of the primitives is exact on `U`, so a cut-off at infinity
  -- makes the combination of `dη` and `dθ` the exterior derivative of a compactly supported form.
  rw [deRhamCohomology.mk_eq_zero_iff] at h
  have hU' : SmoothForm.mpullback (Opens.inclusion hUW) (contMDiff_inclusion hUW) (a • η + b • θ) ∈
      exactForms 𝓘(ℝ, E) U (k + 1) := by
    rw [map_add, map_smul, map_smul]
    exact h
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  refine ⟨a, b, hab, ?_⟩
  have := mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU hρc hU'
  rwa [map_add, map_smul, map_smul] at this

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

/-- On a finite-dimensional real inner product space `E` of dimension `k + 2`, read as the open
subset `⊤` of itself, the top compactly supported de Rham cohomology has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_top_le_one {k : ℕ}
    (hkE : finrank ℝ E = k + 2) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (k + 2)) ≤ 1 := by
  rw [rank_le_one_iff]
  by_cases h : ∀ v : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (k + 2), v = 0
  · exact ⟨0, fun v ↦ ⟨0, by rw [h v, smul_zero]⟩⟩
  obtain ⟨v₀, hv₀⟩ := not_forall.mp h
  refine ⟨v₀, fun v ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ v
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ v₀
  obtain ⟨a, b, hab, h⟩ := exists_smul_add_smul_mem_exactCompactlySupportedForms_top hkE φ.2 ψ.2
  rw [← Submodule.coe_smul, ← Submodule.coe_smul, ← Submodule.coe_add,
    ← compactlySupportedDeRhamCohomology.mk_eq_zero_iff, map_add, map_smul, map_smul] at h
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_smul, zero_add, smul_eq_zero] at h
    exact absurd (h.resolve_left (hab.resolve_left fun h ↦ h rfl)) hv₀
  · refine ⟨-(a⁻¹ * b), ?_⟩
    have := congrArg (a⁻¹ • ·) h
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at this
    rw [neg_smul, neg_eq_iff_add_eq_zero]
    exact (add_comm _ _).trans this

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

/-- The top compactly supported de Rham cohomology `H^n_c(E)` of a real normed space `E` of
finite dimension `n` has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_le_one {k : ℕ} (hkE : finrank ℝ E = k) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) ≤ 1 := by
  obtain _ | _ | k := k
  · -- In dimension zero `E` is a point, so `H⁰_c(E) = H⁰_dR(E)` consists of constant classes.
    have : Subsingleton E := Module.finrank_zero_iff.mp hkE
    rw [(LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective 𝓘(ℝ, E) 0)).rank_eq,
      rank_le_one_iff]
    exact ⟨deRhamCohomology.const 𝓘(ℝ, E) E 1, fun c ↦ (deRhamCohomology.exists_eq_const c).imp
      fun r hr ↦ by rw [hr, ← map_smul, smul_eq_mul, mul_one]⟩
  · -- In dimension one, transfer the computation on the real line.
    let Φ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, ℝ)⟯ ℝ :=
      (ContinuousLinearEquiv.ofFinrankEq (by rw [hkE, finrank_self])).toDiffeomorph
    have h : Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, ℝ) ℝ 1) ≤ 1 := by
      rw [(compactlySupportedDeRhamCohomologyRealEquiv (Manifold.Orientation.model
        (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp))).rank_eq, rank_self]
    exact Cardinal.lift_le_one_iff.mp
      ((compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ 1).lift_rank_eq.symm.trans_le
        (Cardinal.lift_le_one_iff.mpr h))
  · -- In dimension `k + 2`, transfer from the Euclidean space of that dimension.
    let F := EuclideanSpace ℝ (Fin (k + 2))
    have hF : finrank ℝ F = k + 2 := finrank_euclideanSpace_fin
    let Φ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F :=
      (ContinuousLinearEquiv.ofFinrankEq (hkE.trans hF.symm)).toDiffeomorph
    have h : Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, F) F (k + 2)) ≤ 1 := by
      rw [(compactlySupportedDeRhamCohomology.equivOfDiffeomorph
        (Diffeomorph.ofTop (I := 𝓘(ℝ, F)) (n := ∞) ⊤ rfl) (k + 2)).rank_eq]
      exact rank_compactlySupportedDeRhamCohomology_top_le_one hF
    exact Cardinal.lift_le_one_iff.mp
      ((compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ (k + 2)).lift_rank_eq.symm.trans_le
        (Cardinal.lift_le_one_iff.mpr h))

/-- A compactly supported closed top form on `E` with integral one against the constant
orientation of a basis `b`: a normalized bump function times the determinant of `b`. -/
private theorem exists_integralTopForm_model_eq_one (b : Module.Basis (Fin (finrank ℝ E)) ℝ E) :
    ∃ φ : compactlySupportedClosedForms 𝓘(ℝ, E) E (finrank ℝ E),
      integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, E)) b.orientation (by simp))
        φ.1.1 = 1 := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let f : E → ℝ := (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : E)).normed b.addHaar
  let D : E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ := AlternatingMap.toContinuousAlternatingMap b.det
  let φ : RoughForm 𝓘(ℝ, E) E ℝ (finrank ℝ E) := fun x ↦ f x • D
  have hs : IsSmoothForm 𝓘(ℝ, E) ∞ φ :=
    isSmoothForm_modelSpace_iff.mpr (ContDiffBump.contDiff_normed _ |>.smul contDiff_const)
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) φ) :=
    (ContDiffBump.hasCompactSupport_normed _).isCompact.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_smul_subset_left f fun _ ↦ D)
  refine ⟨⟨⟨φ, hs.mem_smoothBundleForms⟩, (mem_compactlySupportedClosedForms _).mpr
    ⟨(mem_compactlySupportedForms _).mpr hc, mem_closedForms_of_finrank_le _ le_rfl _⟩⟩, ?_⟩
  have hφb (x : E) : φ x b = f x := by
    have h : (f x • D) b = f x := by simp [D, Module.Basis.det_self]
    -- `φ x` is `f x • D` read in the tangent fibre at `x`, which is `E` by definition.
    exact h
  rw [integralTopForm_model_eq_integral _ _ (hs.of_le (by simp)) hc b rfl, funext hφb]
  exact ContDiffBump.integral_normed _

variable {E} in
/-- **Top compactly supported cohomology of `ℝⁿ`.** On a real normed space `E` of finite
dimension `n`, integration `H^n_c(E) → ℝ` against any orientation `o` of `E` is bijective. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_normedSpace
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  -- The class `x₁` of a bump form has nonzero integral.
  let b := Module.finBasis ℝ E
  obtain ⟨φ₁, hφ₁⟩ := exists_integralTopForm_model_eq_one E b
  set x₁ := compactlySupportedDeRhamCohomology.mk 𝓘(ℝ, E) _ φ₁
  have hx₁ : compactlySupportedDeRhamCohomology.integral o x₁ ≠ 0 := by
    rw [compactlySupportedDeRhamCohomology.integral_mk]
    rcases Manifold.Orientation.eq_or_eq_neg o
      (Manifold.Orientation.model (I := 𝓘(ℝ, E)) b.orientation (by simp)) with rfl | rfl
    · rw [hφ₁]
      exact one_ne_zero
    · rw [integralTopForm_neg, hφ₁]
      exact neg_ne_zero.mpr one_ne_zero
  -- Every class is a multiple of a single class, hence of `x₁`.
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp (rank_compactlySupportedDeRhamCohomology_le_one E rfl)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦
    ⟨(y / compactlySupportedDeRhamCohomology.integral o x₁) • x₁, by simp [hx₁]⟩⟩
  obtain ⟨r, rfl⟩ := hv₀ x
  obtain ⟨s, hs⟩ := hv₀ x₁
  rw [map_smul, smul_eq_mul, mul_eq_zero] at hx
  rcases hx with rfl | hx
  · exact zero_smul _ _
  · exact absurd (by rw [← hs, map_smul, hx, smul_zero]) hx₁

variable {E} in
/-- **Top compactly supported cohomology of `ℝⁿ`.** On a real normed space `E` of finite
dimension `n`, integration against an orientation `o` of `E` is a linear isomorphism
`H^n_c(E) ≃ₗ[ℝ] ℝ`. -/
def compactlySupportedDeRhamCohomologyNormedSpaceEquiv
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))) :
    compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E) ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace o)

variable {E} in
/-- The isomorphism `H^n_c(E) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyNormedSpaceEquiv_apply
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E)))
    (x : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) :
    compactlySupportedDeRhamCohomologyNormedSpaceEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

/-- The top compactly supported de Rham cohomology `H^n_c(E)` of a real normed space `E` of
finite dimension `n` is one-dimensional. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) = 1 :=
  (compactlySupportedDeRhamCohomologyNormedSpaceEquiv (Manifold.Orientation.model
    (I := 𝓘(ℝ, E)) (Module.finBasis ℝ E).orientation (by simp))).finrank_eq.trans
    (finrank_self ℝ)

end TauCeti
