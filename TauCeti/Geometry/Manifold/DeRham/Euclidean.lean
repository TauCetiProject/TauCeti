/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.RealLine
import TauCeti.Geometry.Manifold.DeRham.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.LinearAlgebra.Dimension.FinrankOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Compactly supported de Rham cohomology of `ℝⁿ`

On a finite-dimensional real normed space `E` of dimension `n`, the compactly supported de Rham
cohomology `H^k_c(E)` vanishes in every degree `k ≠ n`
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`). In degree zero and above
the dimension this is already known on every connected noncompact manifold, respectively on every
`n`-manifold; the content is the range `0 < k < n`. Compact supports are not homotopy invariant,
so this does not follow from the vanishing of `H^k_dR(E)` in positive degrees.

The proof transfers to an inner product space and runs through the complement of a large closed
ball. Let `ω` be a compactly supported closed `k`-form with `0 < k < n`, supported in the closed
ball of radius `r`. By the Poincaré lemma `ω = dη` for a smooth `(k - 1)`-form `η`, which is closed
on the complement `E \ closedBall 0 r`. That complement deformation retracts onto the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`), whose cohomology vanishes in degrees
strictly between `0` and `n - 1`, and it is connected for `n ≥ 2`. So `η` is exact on it when
`k ≥ 2`, and constant on it when `k = 1`. A cut-off at infinity then turns `η` into a compactly
supported primitive of `ω`
(`TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and its
degree-zero form).

In the top degree `H^n_c(E)` is a line
(`TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace`), and for every orientation of
`E` integration `H^n_c(E) → ℝ` is an isomorphism
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`,
`TauCeti.compactlySupportedDeRhamCohomologyNormedSpaceEquiv`). Equivalently, a compactly supported
top form is the exterior derivative of a compactly supported form exactly when its integral
vanishes (`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace`).
A normalized bump function times a determinant form has integral one, so integration is onto and it
remains to bound the dimension.
For `n ≥ 2` the same argument applies in degree `n`: if `ω₁ = dη₁` and `ω₂ = dη₂` are compactly
supported closed `n`-forms, then `η₁` and `η₂` are closed on the complement of a large closed ball,
whose `(n - 1)`-st cohomology is that of `Sⁿ⁻¹`, a line. A nontrivial combination
`a η₁ + b η₂` is therefore exact there, and the cut-off at infinity makes `a ω₁ + b ω₂` compactly
supported exact. The case `n = 1` is the real line
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_real`), and for `n = 0` compactly
supported and ordinary cohomology of the point agree.

These are the base cases of the computation of top compactly supported cohomology and of Poincaré
duality on oriented manifolds, which proceed by Mayer–Vietoris arguments over coordinate balls.

## Main results

* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E) = 0` for
  `k ≠ dim E`.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace`: `H^n_c(E)` is one-dimensional
  for `n = dim E`.
* `TauCeti.finrank_compactlySupportedDeRhamCohomology_normedSpace_eq_ite`: `H^k_c(E)` is
  one-dimensional for `k = dim E` and zero otherwise.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`: for an
  orientation of `E`, integration `H^n_c(E) → ℝ` is bijective.
* `TauCeti.compactlySupportedDeRhamCohomologyNormedSpaceEquiv`: the resulting isomorphism
  `H^n_c(E) ≃ₗ[ℝ] ℝ`.
* `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace`: a compactly
  supported top form is compactly supported exact if and only if its integral vanishes.

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

/-- For every orientation `o` of a finite-dimensional real normed space `E` of dimension `n`,
integration `H^n_c(E) → ℝ` is nonzero: the class of a bump form has integral one. -/
private theorem compactlySupportedDeRhamCohomology.exists_integral_ne_zero_normedSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) :
    ∃ v, compactlySupportedDeRhamCohomology.integral o v ≠ 0 := by
  obtain ⟨v, hv⟩ := compactlySupportedDeRhamCohomology.surjective_integral o 1
  exact ⟨v, hv.trans_ne one_ne_zero⟩

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
/-- On a real inner product space `E`, read as the open subset `⊤` of itself, every closed form of
positive degree is exact: the Poincaré lemma. -/
private theorem mem_exactForms_top {j : ℕ} {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (j + 1)}
    (hφ : φ ∈ closedForms 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :
    φ ∈ exactForms 𝓘(ℝ, E) (⊤ : Opens E) (j + 1) := by
  let Φ : (⊤ : Opens E) ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E := Diffeomorph.ofTop _ rfl
  have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :=
    have := subsingleton_deRhamCohomology_normedSpace E j
    (deRhamCohomology.equivOfDiffeomorph Φ (j + 1)).symm.toEquiv.subsingleton
  exact (deRhamCohomology.mk_eq_zero_iff _ _ ⟨φ, hφ⟩).mp (Subsingleton.elim _ _)

omit [FiniteDimensional ℝ E] in
/-- A smooth form on `E`, read as the open subset `⊤` of itself, whose exterior derivative is
supported in the closed ball of radius `r` is closed on the complement of the closed ball of every
radius `R ≥ r`. -/
private theorem mpullback_mem_closedForms_compl_closedBall {k : ℕ} {r R : ℝ} (hrR : r ≤ R)
    {η : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ k}
    (hr : Subtype.val '' _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (mextDerivₗ 𝓘(ℝ, E) k η).1 ⊆ closedBall 0 r) :
    SmoothForm.mpullback (Opens.inclusion (le_top : (⟨(closedBall (0 : E) R)ᶜ,
        isClosed_closedBall.isOpen_compl⟩ : Opens E) ≤ ⊤)) (contMDiff_inclusion le_top) η ∈
      closedForms 𝓘(ℝ, E)
        (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) k := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback]
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [SmoothForm.coe_mpullback, mpullback_inclusion_apply]
  -- The value of `dη` vanishes off its support; the two zeros differ only through the
  -- identification of the fibre at `x` with the model fibre.
  refine (image_eq_zero_of_notMem_tsupport fun hx ↦ x.2 ?_).trans rfl
  exact closedBall_subset_closedBall hrR (hr ⟨_, hx, rfl⟩)

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
  have hφe := mem_exactForms_top hφd
  rw [exactForms_succ] at hφe
  obtain ⟨η, rfl⟩ := hφe
  -- `dη` is supported in a closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r, hr⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max r 0
  have hR : 0 ≤ R := le_max_right r 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  -- The form `η` is closed on `U`, where `dη` vanishes.
  have hηU := mpullback_mem_closedForms_compl_closedBall (le_max_left r 0) hr
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  rcases j with _ | j
  · -- In degree one, `η` is a function, constant on the connected set `U`.
    have : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp <|
      isPathConnected_compl_closedBall (by rw [← finrank_eq_rank]; exact_mod_cast hkE) 0 R
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

/-- On a real inner product space `E` of dimension `n + 2`, read as the open subset `⊤` of itself,
any two compactly supported closed top forms have a nontrivial linear combination that is the
exterior derivative of a compactly supported form. -/
private theorem exists_smul_add_smul_mem_exactCompactlySupportedForms_top {n : ℕ}
    (hE : finrank ℝ E = n + 2) {φ ψ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ (n + 2)}
    (hφ : φ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) (n + 2))
    (hψ : ψ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) (n + 2)) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      a • φ + b • ψ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) (n + 2) := by
  have : Fact (finrank ℝ E = n + 1 + 1) := ⟨hE⟩
  obtain ⟨hφc, hφd⟩ := (mem_compactlySupportedClosedForms _).mp hφ
  obtain ⟨hψc, hψd⟩ := (mem_compactlySupportedClosedForms _).mp hψ
  -- By the Poincaré lemma `φ = dη` and `ψ = dθ` for smooth forms `η` and `θ`.
  have hφe := mem_exactForms_top hφd
  have hψe := mem_exactForms_top hψd
  rw [exactForms_succ] at hφe hψe
  obtain ⟨η, rfl⟩ := hφe
  obtain ⟨θ, rfl⟩ := hψe
  -- Both supports lie in a closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r₁, hr₁⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  obtain ⟨r₂, hr₂⟩ := (((mem_compactlySupportedForms _).mp hψc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max (max r₁ r₂) 0
  have hR : 0 ≤ R := le_max_right _ 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  have hηU := mpullback_mem_closedForms_compl_closedBall
    ((le_max_left r₁ r₂).trans (le_max_left _ 0)) hr₁
  have hθU := mpullback_mem_closedForms_compl_closedBall
    ((le_max_right r₁ r₂).trans (le_max_left _ 0)) hr₂
  -- On `U`, whose cohomology is that of the sphere `Sⁿ⁺¹`, the top degree is a line, so the
  -- classes of `η` and `θ` are linearly dependent.
  have hU : finrank ℝ (deRhamCohomology 𝓘(ℝ, E) U (n + 1)) = 1 :=
    (deRhamCohomology.closedBallComplEquivSphere E (n + 1) hR (n + 1)).finrank_eq.trans
      (finrank_deRhamCohomology_sphere_self n.succ_pos)
  obtain ⟨a, b, hab, h0⟩ := exists_smul_add_smul_eq_zero_of_finrank_eq_one hU
    (deRhamCohomology.mk 𝓘(ℝ, E) (n + 1) ⟨_, hηU⟩) (deRhamCohomology.mk 𝓘(ℝ, E) (n + 1) ⟨_, hθU⟩)
  refine ⟨a, b, hab, ?_⟩
  -- So `a η + b θ` is exact on `U`, and a cut-off at infinity gives a compactly supported
  -- primitive of `a φ + b ψ`.
  have h0 : SmoothForm.mpullback (Opens.inclusion hUW) (contMDiff_inclusion hUW) (a • η + b • θ) ∈
      exactForms 𝓘(ℝ, E) U (n + 1) := by
    simpa only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul] using
      (deRhamCohomology.mk_eq_zero_iff _ _ (a • ⟨_, hηU⟩ + b • ⟨_, hθU⟩)).mp
        (by rwa [map_add, map_smul, map_smul])
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  simpa only [map_add, map_smul] using
    mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU hρc h0

/-- On a real inner product space `E` of dimension `n + 2`, the top compactly supported de Rham
cohomology `H^(n+2)_c(E)` is one-dimensional. -/
private theorem finrank_compactlySupportedDeRhamCohomology_innerProductSpace {n : ℕ}
    (hE : finrank ℝ E = n + 2) :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E (n + 2)) = 1 := by
  -- A class `v₀` with nonzero integral is nonzero.
  have hn : Fintype.card (Fin (n + 2)) = finrank ℝ E := by simp [hE]
  obtain ⟨v₀, hv₀⟩ := compactlySupportedDeRhamCohomology.exists_integral_ne_zero_normedSpace
    (Manifold.Orientation.model (Module.finBasisOfFinrankEq ℝ E hE).orientation hn)
  replace hv₀ : v₀ ≠ 0 := fun h ↦ hv₀ (by rw [h, map_zero])
  refine (finrank_eq_one_iff_of_ne_zero' v₀ hv₀).mpr fun w ↦ ?_
  -- Read `w` and `v₀` on the open subset `⊤`, where any two top classes are dependent.
  let e := compactlySupportedDeRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) (⊤ : Opens E) rfl) (n + 2)
  obtain ⟨φ, hφ⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ (n + 2) (e w)
  obtain ⟨ψ, hψ⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ (n + 2) (e v₀)
  obtain ⟨a, b, hab, h⟩ := exists_smul_add_smul_mem_exactCompactlySupportedForms_top hE φ.2 ψ.2
  have h0 : a • w + b • v₀ = 0 := e.injective <| by
    simpa [← hφ, ← hψ] using
      (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ _ (a • φ + b • ψ)).mpr h
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add, smul_eq_zero] at h0
    exact hv₀ (h0.resolve_left (hab.resolve_left (not_not.mpr rfl)))
  refine ⟨-(a⁻¹ * b), ?_⟩
  linear_combination (norm := match_scalars <;> field_simp <;> ring) (-a⁻¹) • h0

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

/-- **The top compactly supported de Rham cohomology of `ℝⁿ` is a line.** On a
finite-dimensional real normed space `E` of dimension `k`, `H^k_c(E)` is one-dimensional. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace {k : ℕ} (hk : finrank ℝ E = k) :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) = 1 := by
  obtain rfl | rfl | ⟨n, rfl⟩ : k = 0 ∨ k = 1 ∨ ∃ n, k = n + 2 := by
    rcases k with _ | _ | n <;> simp
  · -- `E` is a point: compactly supported and ordinary cohomology agree, and `H⁰` is a line.
    have : Subsingleton E := Module.finrank_zero_iff.mp hk
    rw [(LinearEquiv.ofBijective _
      (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective 𝓘(ℝ, E) 0)).finrank_eq]
    exact finrank_deRhamCohomology_zero 𝓘(ℝ, E) E
  · -- `E` is a line: transfer from `ℝ`, where integration is an isomorphism.
    let Φ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, ℝ)⟯ ℝ :=
      (ContinuousLinearEquiv.ofFinrankEq (hk.trans (finrank_self ℝ).symm)).toDiffeomorph
    rw [← (compactlySupportedDeRhamCohomology.equivOfDiffeomorph Φ 1).finrank_eq,
      (LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_real
        Manifold.Orientation.real)).finrank_eq, finrank_self]
  · -- Transfer from the Euclidean space of the same dimension.
    rw [← (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
      (toEuclidean (E := E)).toDiffeomorph (n + 2)).finrank_eq]
    exact finrank_compactlySupportedDeRhamCohomology_innerProductSpace
      (by rw [finrank_euclideanSpace_fin, hk])

/-- **The compactly supported de Rham cohomology of `ℝⁿ`.** On a finite-dimensional real normed
space `E`, `H^k_c(E)` is one-dimensional in degree `k = dim E` and zero in every other degree. -/
theorem finrank_compactlySupportedDeRhamCohomology_normedSpace_eq_ite (k : ℕ) :
    finrank ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) =
      if k = finrank ℝ E then 1 else 0 := by
  split_ifs with h
  · exact finrank_compactlySupportedDeRhamCohomology_normedSpace E h.symm
  · have := subsingleton_compactlySupportedDeRhamCohomology_normedSpace E h
    exact finrank_zero_of_subsingleton

variable {E}

/-- **The top compactly supported de Rham cohomology of `ℝⁿ`.** For every orientation `o` of a
finite-dimensional real normed space `E` of dimension `n`, integration `H^n_c(E) → ℝ` is
bijective. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_normedSpace {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  have : IsSimpleModule ℝ (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E n) :=
    isSimpleModule_iff_finrank_eq_one.mpr
      (finrank_compactlySupportedDeRhamCohomology_normedSpace E (by simpa using o.card_eq.symm))
  obtain ⟨v, hv⟩ := compactlySupportedDeRhamCohomology.exists_integral_ne_zero_normedSpace o
  exact LinearMap.bijective_of_ne_zero fun h ↦ hv (by rw [h, LinearMap.zero_apply])

/-- **The compactly supported Poincaré lemma in top degree** [Lee, Lemma 17.27]. On an oriented
finite-dimensional real normed space `E` of dimension `n`, a compactly supported smooth `n`-form
whose integral vanishes is the exterior derivative of a compactly supported form. -/
theorem mem_exactCompactlySupportedForms_of_integralTopForm_eq_zero_normedSpace {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) {φ : SmoothForm 𝓘(ℝ, E) E ℝ n}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, E) E n) (h : integralTopForm o φ.1 = 0) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) E n := by
  let ψ : compactlySupportedClosedForms 𝓘(ℝ, E) E n :=
    ⟨φ, (mem_compactlySupportedClosedForms _).mpr
      ⟨hφ, mem_closedForms_of_finrank_le 𝓘(ℝ, E) (by simpa using o.card_eq.symm.le) φ⟩⟩
  refine (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ n ψ).mp
    ((injective_iff_map_eq_zero _).mp
      (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace o).1 _ ?_)
  rw [compactlySupportedDeRhamCohomology.integral_mk]
  exact h

/-- **The compactly supported Poincaré lemma in top degree**, as a characterization. On an oriented
finite-dimensional real normed space `E` of dimension `n`, a compactly supported smooth `n`-form is
the exterior derivative of a compactly supported form if and only if its integral vanishes. -/
theorem mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero_normedSpace {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) {φ : SmoothForm 𝓘(ℝ, E) E ℝ n}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, E) E n) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) E n ↔ integralTopForm o φ.1 = 0 :=
  ⟨integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o,
    mem_exactCompactlySupportedForms_of_integralTopForm_eq_zero_normedSpace o hφ⟩

/-- **The top compactly supported de Rham cohomology of `ℝⁿ`.** For an orientation `o` of a
finite-dimensional real normed space `E` of dimension `n`, integration is a linear isomorphism
`H^n_c(E) ≃ₗ[ℝ] ℝ`. -/
def compactlySupportedDeRhamCohomologyNormedSpaceEquiv {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n)) :
    compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E n ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_normedSpace o)

/-- The isomorphism `H^n_c(E) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyNormedSpaceEquiv_apply {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) E (Fin n))
    (x : compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E n) :
    compactlySupportedDeRhamCohomologyNormedSpaceEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

end TauCeti
