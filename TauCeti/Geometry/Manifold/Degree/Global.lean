/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Integral
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.Sard.EqualDimension

/-!
# The mapping degree

Let `f : M → N` be a smooth map from a compact oriented boundaryless manifold to a connected
oriented boundaryless manifold of the same dimension `k`, both Hausdorff, with `N` σ-compact.
For a regular value `y` of `f`, the signed count `TauCeti.degreeAtRegularValue o o' f y` of the
fibre over `y` computes integrals of pulled-back top forms:
$$\int_M f^*\varphi = \deg_y(f) \int_N \varphi$$
for every compactly supported smooth `k`-form `φ` on `N`
(`TauCeti.integralTopForm_mpullback_eq_degreeAtRegularValue_mul`), and not only for forms
supported near `y`. Equivalently, on top compactly supported de Rham cohomology, integration
over `M` after pullback is `deg_y(f)` times integration over `N`
(`TauCeti.compactlySupportedDeRhamCohomology.integral_map_eq_degreeAtRegularValue_mul`).

The left side does not mention `y`, so the signed count is the same at every regular value
(`TauCeti.degreeAtRegularValue_eq_of_isRegularValue`). Hence the *mapping degree*
`TauCeti.degree o o' f`, defined as the signed count at some regular value (and `0` when there
is none), equals the signed count at every regular value
(`TauCeti.degree_eq_degreeAtRegularValue`). Regular values exist by Sard's theorem, so the
formula `∫_M f^*φ = deg(f) ∫_N φ` holds with no regular value named
(`TauCeti.integralTopForm_mpullback_eq_degree_mul`). A map of nonzero degree is surjective
(`TauCeti.surjective_of_degree_ne_zero`).

The cohomological form of the formula gives the basic calculus of the degree. Smoothly homotopic
maps induce the same map on top compactly supported cohomology of the compact manifold `M`
(`TauCeti.compactlySupportedDeRhamCohomology.map_eq_of_homotopy`), so they have the same degree
(`TauCeti.degree_eq_of_homotopy`). Pullback is contravariantly functorial, so the degree is
multiplicative, `deg (g ∘ f) = deg g · deg f`, for maps between compact connected manifolds
(`TauCeti.degree_comp`).

As in the local computation, `M` and `N` are modelled on the same vector space `E`.

The proof is Lee's. Near `y` the formula holds by the stack-of-records computation
`TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`; choose a closed
top form `θ` of integral one supported there. On the connected manifold `N` integration is an
isomorphism `H^k_c(N) ≃ ℝ` (`TauCeti.compactlySupportedDeRhamCohomology.injective_integral`), so
every class is `(∫_N c) • [θ]`. Pullback along `f`, which is proper as `M` is compact, and
integration over `M` are linear, and the integral over `M` of `f^*θ` is `deg_y(f)`.

## Main results

* `TauCeti.compactlySupportedDeRhamCohomology.integral_map_eq_degreeAtRegularValue_mul`,
  `TauCeti.compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul`: pullback on top
  compactly supported cohomology, read through integration, is multiplication by the degree.
* `TauCeti.integralTopForm_mpullback_eq_degreeAtRegularValue_mul`,
  `TauCeti.integralTopForm_mpullback_eq_degree_mul`: `∫_M f^*φ = deg(f) ∫_N φ`.
* `TauCeti.degreeAtRegularValue_eq_of_isRegularValue`: the signed count does not depend on the
  regular value.
* `TauCeti.degree_eq_degreeAtRegularValue`: the degree is the signed count at every regular value.
* `TauCeti.surjective_of_degree_ne_zero`: a map of nonzero degree is surjective.
* `TauCeti.degree_eq_of_homotopy`: smoothly homotopic maps have the same degree.
* `TauCeti.degree_comp`: the degree of a composite is the product of the degrees.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory, Theorem 17.35.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (the degree through top compactly supported cohomology).
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N] {k : ℕ}

namespace compactlySupportedDeRhamCohomology

/-- Pulling a top compactly supported class back to the compact manifold `M` and integrating
gives `deg_y(f)` times its integral over `N`, for any regular value `y` of `f`. The pullback is
along `f`, which is proper since `M` is compact. -/
theorem integral_map_eq_degreeAtRegularValue_mul (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) (c : compactlySupportedDeRhamCohomology J N k) :
    integral o (map f hf hf.continuous.isProperMap k c) =
      degreeAtRegularValue o o' f y * integral o' c := by
  obtain ⟨V, hV, hloc⟩ :=
    exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul o o'
      (hf.of_le (by simp)) hy
  obtain ⟨θ, hθV, hθ⟩ := exists_compactlySupportedClosedForms_integralTopForm_eq_one o' y hV
  -- On the connected manifold `N`, the class of `θ` spans `H^k_c(N)`.
  have hc : c = integral o' c • mk J k θ :=
    injective_integral o' (by simp [hθ])
  have hb : Module.Basis (Fin k) ℝ E :=
    Module.finBasisOfFinrankEq ℝ E (by simpa using o'.card_eq.symm)
  have hθi : IntegrableTopForm θ.1.1 :=
    θ.1.isSmoothForm.integrableTopForm
      ((mem_compactlySupportedForms J).mp ((mem_compactlySupportedClosedForms J).mp θ.2).1) hb
  conv_lhs => rw [hc]
  rw [map_smul, map_smul, map_mk, integral_mk, compactlySupportedClosedForms.coe_coe_mpullback,
    hloc _ hθi hθV, hθ, smul_eq_mul]
  ring

end compactlySupportedDeRhamCohomology

/-- **The degree formula** at a regular value: for a compactly supported smooth top form `φ` on
`N`, `∫_M f^*φ = deg_y(f) ∫_N φ`, for any regular value `y` of `f`. -/
theorem integralTopForm_mpullback_eq_degreeAtRegularValue_mul
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) {φ : RoughForm J N ℝ k}
    (hφ : IsSmoothForm J ∞ φ) (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ)) :
    integralTopForm o (mpullback I J f φ) =
      degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  let ψ := compactlySupportedForms.toClosedOfFinrankLe J (by simpa using o'.card_eq.ge)
    ⟨⟨φ, hφ.mem_smoothBundleForms⟩, (mem_compactlySupportedForms J).mpr hc⟩
  have h := compactlySupportedDeRhamCohomology.integral_map_eq_degreeAtRegularValue_mul o o' hf hy
    (compactlySupportedDeRhamCohomology.mk J k ψ)
  rwa [compactlySupportedDeRhamCohomology.map_mk, compactlySupportedDeRhamCohomology.integral_mk,
    compactlySupportedDeRhamCohomology.integral_mk,
    compactlySupportedClosedForms.coe_coe_mpullback,
    compactlySupportedForms.coe_toClosedOfFinrankLe] at h

/-- **Independence of the regular value.** The signed counts of the fibres of `f` over any two
regular values agree. -/
theorem degreeAtRegularValue_eq_of_isRegularValue (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f) {y y' : N}
    (hy : IsRegularValue I J f y) (hy' : IsRegularValue I J f y') :
    degreeAtRegularValue o o' f y = degreeAtRegularValue o o' f y' := by
  obtain ⟨θ, -, hθ⟩ :=
    exists_compactlySupportedClosedForms_integralTopForm_eq_one o' y (U := univ) Filter.univ_mem
  have h := (compactlySupportedDeRhamCohomology.integral_map_eq_degreeAtRegularValue_mul o o' hf hy
    (compactlySupportedDeRhamCohomology.mk J k θ)).symm.trans
    (compactlySupportedDeRhamCohomology.integral_map_eq_degreeAtRegularValue_mul o o' hf hy'
      (compactlySupportedDeRhamCohomology.mk J k θ))
  rw [compactlySupportedDeRhamCohomology.integral_mk, hθ, mul_one, mul_one] at h
  exact_mod_cast h

/-- The degree is the signed count of the fibre over every regular value. -/
theorem degree_eq_degreeAtRegularValue (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) :
    degree o o' f = degreeAtRegularValue o o' f y := by
  have h : ∃ y, IsRegularValue I J f y := ⟨y, hy⟩
  rw [degree_eq_degreeAtRegularValue_choose h]
  exact degreeAtRegularValue_eq_of_isRegularValue o o' hf h.choose_spec hy

/-- Pullback on top compactly supported cohomology, read through integration, is multiplication by
the degree. -/
theorem compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J ∞ f) (c : compactlySupportedDeRhamCohomology J N k) :
    integral o (map f hf hf.continuous.isProperMap k c) = degree o o' f * integral o' c := by
  -- Sard's theorem provides a regular value.
  obtain ⟨y, hy⟩ := (dense_isRegularValue rfl (hf.mdifferentiable (by simp))).nonempty
  rw [degree_eq_degreeAtRegularValue o o' hf hy]
  exact integral_map_eq_degreeAtRegularValue_mul o o' hf hy c

/-- **The degree formula** [Lee, Thm. 17.35]: for a compactly supported smooth top form `φ` on `N`,
`∫_M f^*φ = deg(f) ∫_N φ`. -/
theorem integralTopForm_mpullback_eq_degree_mul (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f)
    {φ : RoughForm J N ℝ k} (hφ : IsSmoothForm J ∞ φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ)) :
    integralTopForm o (mpullback I J f φ) = degree o o' f * integralTopForm o' φ := by
  -- Sard's theorem provides a regular value.
  obtain ⟨y, hy⟩ := (dense_isRegularValue rfl (hf.mdifferentiable (by simp))).nonempty
  rw [degree_eq_degreeAtRegularValue o o' hf hy]
  exact integralTopForm_mpullback_eq_degreeAtRegularValue_mul o o' hf hy hφ hc

/-- A smooth map of nonzero degree from a compact manifold to a connected manifold of the same
dimension is surjective. -/
theorem surjective_of_degree_ne_zero (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f)
    (h : degree o o' f ≠ 0) : Surjective f := by
  intro y
  by_contra hy
  rw [← mem_range] at hy
  exact h ((degree_eq_degreeAtRegularValue o o' hf (isRegularValue_of_notMem_range hy)).trans
    (degreeAtRegularValue_of_notMem_range hy))

/-- **Homotopy invariance of the degree.** If `F : M × [0, 1] → N` is a smooth homotopy from `f`
to `g`, then `f` and `g` have the same degree. -/
theorem degree_eq_of_homotopy (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f g : M → N} (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff I J ∞ g) {F : M × Icc (0 : ℝ) 1 → N} (hF : ContMDiff (I.prod (𝓡∂ 1)) J ∞ F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = g x) :
    degree o o' f = degree o o' g := by
  -- Compare the integrals of the pullbacks of a class of integral one.
  obtain ⟨c, hc⟩ := compactlySupportedDeRhamCohomology.surjective_integral o' 1
  have h := compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul o o' hf c
  rw [compactlySupportedDeRhamCohomology.map_eq_of_homotopy hf hg hf.continuous.isProperMap
    hg.continuous.isProperMap hF h₀ h₁,
    compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul o o' hg, hc, mul_one,
    mul_one] at h
  exact_mod_cast h.symm

omit [SigmaCompactSpace N] in
/-- **Multiplicativity of the degree.** For smooth maps `f : M → N` and `g : N → P` between
compact connected oriented boundaryless manifolds of the same dimension,
`deg (g ∘ f) = deg g · deg f`. -/
theorem degree_comp {H'' P : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ E H''}
    [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P] [BoundarylessManifold K P]
    [T2Space P] [SigmaCompactSpace P] [ConnectedSpace P] [CompactSpace N]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k))
    (o'' : Manifold.Orientation K P (Fin k)) {f : M → N} {g : N → P} (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff J K ∞ g) :
    degree o o'' (g ∘ f) = degree o' o'' g * degree o o' f := by
  -- Pull a class of integral one back along `g` and then along `f`.
  obtain ⟨c, hc⟩ := compactlySupportedDeRhamCohomology.surjective_integral o'' 1
  have h := compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul o o'' (hg.comp hf) c
  rw [compactlySupportedDeRhamCohomology.map_comp f g hf hg hf.continuous.isProperMap
    hg.continuous.isProperMap, LinearMap.comp_apply,
    compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul o o' hf,
    compactlySupportedDeRhamCohomology.integral_map_eq_degree_mul o' o'' hg, hc, mul_one, mul_one,
    mul_comm] at h
  exact_mod_cast h.symm

end TauCeti
