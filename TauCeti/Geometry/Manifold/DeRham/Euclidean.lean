/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.RealLine
import TauCeti.Geometry.Manifold.DeRham.Sphere
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
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`), and for every orientation
of `E` integration is an isomorphism `H^n_c(E) ≃ ℝ`
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`). Equivalently, a
compactly supported top form is the exterior derivative of a compactly supported form exactly when
its integral vanishes
(`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace`).
In degree zero and above the dimension the vanishing is already known on every connected
noncompact manifold, respectively on every `n`-manifold. Compact supports are not homotopy
invariant, so none of this follows from the vanishing of `H^k_dR(E)` in positive degrees.

The proofs transfer to an inner product space and run through the complement of a large closed
ball. Let `ω` be a compactly supported closed `k`-form with `0 < k ≤ n`, supported in the closed
ball of radius `r`. By the Poincaré lemma `ω = dη` for a smooth `(k - 1)`-form `η`, which is closed
on the complement `E \ closedBall 0 r`. That complement deformation retracts onto the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`), and whenever the class of `η` vanishes
there, a cut-off at infinity turns `η` into a compactly supported primitive of `ω`
(`TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and its
degree-zero form).

* For `0 < k < n` the cohomology of `Sⁿ⁻¹` vanishes in degree `k - 1` when `k ≥ 2`, and the
  complement is connected when `k = 1`, so `ω` is always compactly supported exact.
* For `k = n ≥ 2` the cohomology `H^{n-1}(Sⁿ⁻¹)` is one-dimensional, so for any two compactly
  supported top forms some nontrivial linear combination is compactly supported exact. Hence
  `H^n_c(E)` has rank at most one, and integration, which is nonzero on a normalized bump function
  times a determinant, is an isomorphism. For `n = 1` the rank bound comes from the real line
  (`TauCeti.compactlySupportedDeRhamCohomology.injective_integral_real`), and for `n = 0`, where
  `E` is a point, from `H⁰_c(E) = H⁰(E)`.

The argument needs no integration over spheres. Bott and Tu instead integrate along the fibres of
`ℝⁿ → ℝⁿ⁻¹` and induct on the dimension.

## Main results

* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E) = 0` for
  `k ≠ dim E`.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`: integration
  `H^n_c(E) → ℝ` is bijective, `n = dim E`.
* `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace`: a compactly
  supported top form is compactly supported exact if and only if its integral vanishes.
* `TauCeti.compactlySupportedDeRhamCohomologyNormedSpaceEquiv`: the isomorphism
  `H^n_c(E) ≃ₗ[ℝ] ℝ` given by integration.
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
/-- The Poincaré lemma on the open subset `⊤` of a real inner product space: every closed form of
positive degree is exact. -/
private theorem exists_mextDerivₗ_eq_top {j : ℕ} {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (j + 1)}
    (hφ : φ ∈ closedForms 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :
    ∃ η, mextDerivₗ 𝓘(ℝ, E) j η = φ := by
  have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :=
    have := subsingleton_deRhamCohomology_normedSpace E j
    (deRhamCohomology.equivOfDiffeomorph (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) ⊤ rfl)
      (j + 1)).symm.toEquiv.subsingleton
  have hφe := (deRhamCohomology.mk_eq_zero_iff _ _ ⟨φ, hφ⟩).mp (Subsingleton.elim _ _)
  rwa [exactForms_succ] at hφe

omit [FiniteDimensional ℝ E] in
/-- A form `η` on the open subset `⊤` of `E` is closed on every open set `U` missing the support
of `dη`. -/
private theorem mpullback_mem_closedForms_of_notMem_tsupport {j : ℕ} {U : Opens E} (hUW : U ≤ ⊤)
    {η : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ j}
    (hU : ∀ x : (⊤ : Opens E),
      x ∈ _root_.tsupport (α := E [⋀^Fin (j + 1)]→L[ℝ] ℝ) (mextDerivₗ 𝓘(ℝ, E) j η).1 →
        (x : E) ∉ U) :
    SmoothForm.mpullback (Opens.inclusion hUW) (contMDiff_inclusion hUW) η ∈
      closedForms 𝓘(ℝ, E) U j := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback]
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [SmoothForm.coe_mpullback, mpullback_inclusion_apply]
  -- The value of `dη` vanishes off its support; the two zeros differ only through the
  -- identification of the fibre at `x` with the model fibre.
  exact (image_eq_zero_of_notMem_tsupport fun hx ↦ hU _ hx x.2).trans rfl

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
  have hηU := mpullback_mem_closedForms_of_notMem_tsupport hUW fun x hx hxU ↦
    hxU (closedBall_subset_closedBall (le_max_left r 0) (hr ⟨_, hx, rfl⟩))
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  rcases j with _ | j
  · -- In degree one, `η` is a function, constant on the connected set `U`.
    have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp <|
      isPreconnected_compl_closedBall (by rw [← finrank_eq_rank]; exact_mod_cast hkE) 0 R
    let Φ : (⊤ : Opens E) ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E := Diffeomorph.ofTop _ rfl
    have hUc : IsCompact {x : (⊤ : Opens E) | (x : E) ∉ U} := by
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

/-- On a real inner product space `E` of dimension `m + 2`, read as the open subset `⊤` of itself,
let `η₁`, `η₂` be forms of degree `m + 1` whose exterior derivatives are supported in the closed
ball of radius `R`. Then `d(s η₁ + t η₂)` is compactly supported exact for some `(s, t) ≠ 0`: the
complement of the ball retracts onto `Sᵐ⁺¹`, so its cohomology in degree `m + 1` is
one-dimensional, and a combination of `η₁` and `η₂` is exact there. -/
private theorem exists_mextDerivₗ_smul_add_smul_mem_exactCompactlySupportedForms_of_closedBall
    {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)] {R : ℝ} (hR : 0 ≤ R)
    {η₁ η₂ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (m + 1)}
    (h₁ : ∀ x : (⊤ : Opens E),
      x ∈ _root_.tsupport (α := E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (mextDerivₗ 𝓘(ℝ, E) (m + 1) η₁).1 →
        (x : E) ∈ closedBall (0 : E) R)
    (h₂ : ∀ x : (⊤ : Opens E),
      x ∈ _root_.tsupport (α := E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (mextDerivₗ 𝓘(ℝ, E) (m + 1) η₂).1 →
        (x : E) ∈ closedBall (0 : E) R) :
    ∃ s t : ℝ, ¬(s = 0 ∧ t = 0) ∧ mextDerivₗ 𝓘(ℝ, E) (m + 1) (s • η₁ + t • η₂) ∈
      exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (m + 2) := by
  have hUW : (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) ≤ ⊤ := le_top
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  obtain ⟨s, t, hne, hst⟩ := exists_smul_add_smul_mem_exactForms
    ((deRhamCohomology.closedBallComplEquivSphere E (m + 1) hR (m + 1)).finrank_eq.trans
      (finrank_deRhamCohomology_sphere_self m.succ_pos))
    (mpullback_mem_closedForms_of_notMem_tsupport hUW fun x hx hxU ↦ hxU (h₁ x hx))
    (mpullback_mem_closedForms_of_notMem_tsupport hUW fun x hx hxU ↦ hxU (h₂ x hx))
  refine ⟨s, t, hne,
    mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU hρc ?_⟩
  rwa [map_add, map_smul, map_smul]

/-- On a real inner product space `E` of dimension `n + 1 ≥ 2`, read as the open subset `⊤` of
itself, any two classes in `H^{n+1}_c(E)` are linearly dependent. -/
private theorem not_linearIndependent_top {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 0 < n)
    (x y : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (n + 1)) :
    ¬LinearIndependent ℝ ![x, y] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ x
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ _ y
  obtain ⟨hφc, hφd⟩ := (mem_compactlySupportedClosedForms _).mp φ.2
  obtain ⟨hψc, hψd⟩ := (mem_compactlySupportedClosedForms _).mp ψ.2
  -- By the Poincaré lemma `φ = dη₁` and `ψ = dη₂`.
  obtain ⟨η₁, hη₁⟩ := exists_mextDerivₗ_eq_top hφd
  obtain ⟨η₂, hη₂⟩ := exists_mextDerivₗ_eq_top hψd
  -- Both supports lie in a closed ball of radius `R ≥ 0`.
  obtain ⟨r₁, hr₁⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  obtain ⟨r₂, hr₂⟩ := (((mem_compactlySupportedForms _).mp hψc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  have hex := exists_mextDerivₗ_smul_add_smul_mem_exactCompactlySupportedForms_of_closedBall
    (le_max_right (max r₁ r₂) 0)
    (fun x hx ↦ closedBall_subset_closedBall ((le_max_left r₁ r₂).trans (le_max_left _ 0))
      (hr₁ ⟨_, hη₁ ▸ hx, rfl⟩))
    (fun x hx ↦ closedBall_subset_closedBall ((le_max_right r₁ r₂).trans (le_max_left _ 0))
      (hr₂ ⟨_, hη₂ ▸ hx, rfl⟩))
  obtain ⟨s, t, hne, h⟩ := hex
  rw [map_add, map_smul, map_smul, hη₁, hη₂] at h
  rw [LinearIndependent.pair_iff]
  refine fun hind ↦ hne (hind s t ?_)
  have h' :=
    (compactlySupportedDeRhamCohomology.mk_eq_zero_iff 𝓘(ℝ, E) (m + 2) (s • φ + t • ψ)).mpr h
  rwa [map_add, map_smul, map_smul] at h'

/-- On a real inner product space `E` of dimension `n + 1 ≥ 2`, the top compactly supported
de Rham cohomology `H^{n+1}_c(E)` has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_innerProductSpace_le_one {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (hn : 0 < n) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (n + 1)) ≤ 1 := by
  rw [(compactlySupportedDeRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) ⊤ rfl) (n + 1)).rank_eq]
  by_contra h
  rw [not_le] at h
  have : Nontrivial (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (n + 1)) :=
    rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  obtain ⟨x, hx⟩ := exists_ne (0 : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (n + 1))
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx
  exact not_linearIndependent_top hn x y hy

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

variable {E}

/-- The top compactly supported de Rham cohomology `H^n_c(E)` of a real normed space `E` of
finite dimension `n` has rank at most one. -/
private theorem rank_compactlySupportedDeRhamCohomology_le_one {k : ℕ} (hk : finrank ℝ E = k) :
    Module.rank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) ≤ 1 := by
  rcases k with _ | _ | n
  · -- In dimension zero `E` is a point, so `H⁰_c(E) = H⁰(E)` is one-dimensional.
    have : Subsingleton E := Module.finrank_zero_iff.mp hk
    have h1 := finrank_deRhamCohomology_zero (I := 𝓘(ℝ, E)) (M := E)
    have : Module.Finite ℝ (deRhamCohomology 𝓘(ℝ, E) E 0) := Module.finite_of_finrank_eq_succ h1
    rw [(LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective 𝓘(ℝ, E) 0)).rank_eq,
      ← Module.finrank_eq_rank, h1, Nat.cast_one]
  · -- In dimension one, transfer from the real line, where integration is injective.
    let e : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hk)
    have h := (LinearMap.rank_le_of_injective _
      (compactlySupportedDeRhamCohomology.injective_integral_real
        (Manifold.Orientation.model (Module.Basis.singleton (Fin 1) ℝ).orientation
          (by simp)))).trans_eq (rank_self ℝ)
    have := Cardinal.lift_le_one_iff.mpr h
    rw [(compactlySupportedDeRhamCohomology.equivOfDiffeomorph e.toDiffeomorph 1).lift_rank_eq]
      at this
    exact Cardinal.lift_le_one_iff.mp this
  · -- In dimension at least two, transfer from Euclidean space.
    have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = n + 1 + 1) := ⟨by simp⟩
    let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
      ContinuousLinearEquiv.ofFinrankEq (by simpa using hk)
    have := Cardinal.lift_le_one_iff.mpr
      (rank_compactlySupportedDeRhamCohomology_innerProductSpace_le_one
        (E := EuclideanSpace ℝ (Fin (n + 2))) n.succ_pos)
    rw [(compactlySupportedDeRhamCohomology.equivOfDiffeomorph e.toDiffeomorph
      (n + 2)).lift_rank_eq] at this
    exact Cardinal.lift_le_one_iff.mp this

/-- Every orientation of a finite-dimensional real normed space integrates some compactly supported
top-degree class to a nonzero number: a normalized bump function times a determinant. -/
private theorem exists_integral_ne_zero {k : ℕ} (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k)) :
    ∃ x, compactlySupportedDeRhamCohomology.integral o x ≠ 0 := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hk : Fintype.card (Fin k) = finrank ℝ E := o.card_eq
  let b : Module.Basis (Fin k) ℝ E := Module.finBasisOfFinrankEq ℝ E (by simpa using hk.symm)
  let g : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : E → ℝ := g.normed b.addHaar
  let D : E [⋀^Fin k]→L[ℝ] ℝ := AlternatingMap.toContinuousAlternatingMap b.det
  let φ : RoughForm 𝓘(ℝ, E) E ℝ k := fun x ↦ f x • D
  have hs : IsSmoothForm 𝓘(ℝ, E) ∞ φ :=
    isSmoothForm_modelSpace_iff.mpr (ContDiffBump.contDiff_normed _ |>.smul contDiff_const)
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ) :=
    (ContDiffBump.hasCompactSupport_normed _).isCompact.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_smul_subset_left f fun _ ↦ D)
  let ψ : compactlySupportedClosedForms 𝓘(ℝ, E) E k :=
    ⟨⟨φ, hs.mem_smoothBundleForms⟩, (mem_compactlySupportedClosedForms _).mpr
      ⟨(mem_compactlySupportedForms _).mpr hc,
        mem_closedForms_of_finrank_le 𝓘(ℝ, E) (by simpa using hk.symm.le) _⟩⟩
  -- Against the constant orientation of `b`, the integral of `ψ` is that of `f`, which is one.
  have h₁ : integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, E)) b.orientation hk) φ = 1 := by
    have hφb (x : E) : φ x b = f x := by
      have h : (f x • D) b = f x := by simp [D, Module.Basis.det_self]
      -- `φ x` is `f x • D` read in the tangent fibre at `x`, which is `E` by definition.
      exact h
    rw [integralTopForm_model_eq_integral _ hk (hs.of_le (by simp)) hc b rfl, funext hφb]
    exact g.integral_normed
  refine ⟨compactlySupportedDeRhamCohomology.mk _ k ψ, ?_⟩
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  rcases Manifold.Orientation.eq_or_eq_neg o (Manifold.Orientation.model b.orientation hk)
    with rfl | rfl
  · exact h₁ ▸ one_ne_zero
  · rw [integralTopForm_neg]
    exact h₁ ▸ neg_ne_zero.mpr one_ne_zero

/-- **Top compactly supported cohomology of `ℝⁿ`** [Lee, Thm. 17.28]. For an orientation `o` of a
real normed space `E` of finite dimension `n`, integration `H^n_c(E) → ℝ` is bijective. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_normedSpace {k : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k)) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  obtain ⟨x₀, hx₀⟩ := exists_integral_ne_zero o
  -- Every class is a multiple of a single class `v`, whose integral is nonzero.
  obtain ⟨v, hv⟩ := rank_le_one_iff.mp
    (rank_compactlySupportedDeRhamCohomology_le_one (E := E) (by simpa using o.card_eq.symm))
  obtain ⟨c, rfl⟩ := hv x₀
  rw [map_smul, smul_eq_mul] at hx₀
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦
    ⟨(y / integral o v) • v, by simp [right_ne_zero_of_mul hx₀]⟩⟩
  obtain ⟨a, rfl⟩ := hv x
  rw [map_smul, smul_eq_mul, mul_eq_zero] at hx
  rw [hx.resolve_right (right_ne_zero_of_mul hx₀), zero_smul]

/-- **The compactly supported Poincaré lemma in top degree** [Lee, Lemma 17.27]. On an oriented
real normed space `E` of finite dimension `n`, a compactly supported smooth `n`-form whose integral
vanishes is the exterior derivative of a compactly supported form. -/
theorem mem_exactCompactlySupportedForms_of_integralTopForm_eq_zero_normedSpace {k : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k)) {φ : SmoothForm 𝓘(ℝ, E) E ℝ k}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, E) E k) (h : integralTopForm o φ.1 = 0) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) E k := by
  let ψ : compactlySupportedClosedForms 𝓘(ℝ, E) E k :=
    ⟨φ, (mem_compactlySupportedClosedForms _).mpr
      ⟨hφ, mem_closedForms_of_finrank_le 𝓘(ℝ, E) (by simpa using o.card_eq.symm.le) φ⟩⟩
  refine (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ k ψ).mp
    ((injective_iff_map_eq_zero _).mp
      (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace o).1 _ ?_)
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  exact h

/-- **The compactly supported Poincaré lemma in top degree**, as a characterization. On an oriented
real normed space `E` of finite dimension `n`, a compactly supported smooth `n`-form is the exterior
derivative of a compactly supported form if and only if its integral vanishes. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace {k : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k)) {φ : SmoothForm 𝓘(ℝ, E) E ℝ k}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, E) E k) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) E k ↔ integralTopForm o φ.1 = 0 :=
  ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o,
    mem_exactCompactlySupportedForms_of_integralTopForm_eq_zero_normedSpace o hφ⟩

/-- **Top compactly supported cohomology of `ℝⁿ`.** For an orientation `o` of a real normed space
`E` of finite dimension `n`, integration is a linear isomorphism `H^n_c(E) ≃ₗ[ℝ] ℝ`. -/
def compactlySupportedDeRhamCohomologyNormedSpaceEquiv {k : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k)) :
    compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace o)

/-- The isomorphism `H^n_c(E) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyNormedSpaceEquiv_apply {k : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin k))
    (x : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) :
    compactlySupportedDeRhamCohomologyNormedSpaceEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

variable (E) in
/-- The top compactly supported de Rham cohomology `H^n_c(E)` of a real normed space `E` of finite
dimension `n` is one-dimensional. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (finrank ℝ E)) = 1 :=
  (compactlySupportedDeRhamCohomologyNormedSpaceEquiv (Manifold.Orientation.model (I := 𝓘(ℝ, E))
    (Module.finBasis ℝ E).orientation (by simp))).finrank_eq.trans (finrank_self ℝ)

end TauCeti
