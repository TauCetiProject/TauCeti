/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DistributionalRegularity
public import TauCeti.Geometry.Manifold.DifferentialOperator.WaveFrontSet
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalBesov
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Local elliptic regularity for differential operators on bundles

Let `E` be a finite-dimensional real inner product space, `M` a manifold modelled on `E`, and
`P : Γ(V) → Γ(W)` a differential operator of order at most `r` between smooth sections of
finite-rank vector bundles, in Grothendieck's sense. Its transpose `T ↦ T ∘ P`
(`TauCeti.BundleTest.localOperatorDualCLM`) acts on functionals on bundle tests, for instance on
distributional sections of `W`. This file proves **interior elliptic regularity** for this action
when `W` has rank one: if the principal symbol `σ(P)(ξ) : V_x → W_x`
(`TauCeti.sectionPrincipalSymbol`) kills a fixed vector `u ∈ V_x` at no covector `ξ ≠ 0` at `x`,
then `T` is as regular near `x` as `T ∘ P`, with a gain of `r` orders:

`T ∘ P ∈ H^{s,p}` near `x` ⟹ `T ∈ H^{s + r,p}` near `x`, for `1 < p < ∞`

(`TauCeti.BundleTest.IsLocallyMemSobolevAt.of_localOperatorDualCLM`), and the same on the Sobolev
scale `H^s` (`TauCeti.BundleTest.IsLocallySobolevAt.of_localOperatorDualCLM`) and on the Besov
scale `B^s_{p,q}`, `1 < p ≤ ∞` (`TauCeti.BundleTest.IsLocallyMemBesovAt.of_localOperatorDualCLM`).
For a line bundle `V` the condition on `u ≠ 0` is ellipticity of `P` at `x`. If `P` is elliptic in
this sense at every point, the `H^{s + r}` singular support of `T` lies in the `H^s` singular
support of `T ∘ P`
(`TauCeti.BundleTest.sobolevSingularSupport_subset_sobolevSingularSupport_localOperatorDualCLM`).

## The argument

The three statements are instances of one transfer principle
(`TauCeti.BundleTest.IsLocallyAt.of_localOperatorDualCLM`): for invariant notions of local
regularity `A` and `B` on `E` (`Distribution.IsInvariantLocalRegularity`), if elliptic
differential operators of order at most `r` on `C^∞(E)` improve `A` to `B` by transposition, then
so do elliptic differential operators on bundles. Fix a chart `c` at `x` over which both bundles
are trivial, frames `tV` and `tW`, the coefficients `v` of `u` in `tV`, a basis vector `b 0` of the
model fibre of `W`, and a cutoff `χ` equal to `1` on a neighbourhood `U` of `c x`. Over `U`, the
component of `T ∘ P` along `v` is the transpose `φ ↦ S (D φ)` of the component `S` of `T` along
`b 0` by the `(b 0)*, v` entry `D` of the chart compression of `P`
(`TauCeti.BundleTest.restrictCLM_chartComponent_localOperatorDualCLM_apply`). Its principal symbol
at `c x` is read off from `σ(P)(ξ) u`
(`smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators_ne_zero` in the namespace
`OpenPartialHomeomorph`), so `D` is elliptic at `c x`, and the Euclidean statement applies to `S`.
This chart argument follows the proof of microlocal elliptic regularity on bundles,
`TauCeti.BundleTest.IsMicrolocallySmoothAt.of_localOperatorDualCLM` in
`TauCeti/Geometry/Manifold/DifferentialOperator/WaveFrontSet.lean`, and shares its chart steps.
For the Sobolev and Besov scales this is
`Distribution.IsLocallyMemSobolevAt.of_mem_differentialOperators` and its analogues, which rest on
the parametrix of the pseudodifferential calculus on `ℝⁿ`; so the three statements above are for
manifolds modelled on `ℝⁿ` (`TauCeti.CoordinateSpace n`).

## Main results

* `TauCeti.BundleTest.IsLocallyAt.of_localOperatorDualCLM`: the transfer principle.
* `TauCeti.BundleTest.IsLocallyMemSobolevAt.of_localOperatorDualCLM`,
  `TauCeti.BundleTest.IsLocallySobolevAt.of_localOperatorDualCLM`,
  `TauCeti.BundleTest.IsLocallyMemBesovAt.of_localOperatorDualCLM`: interior elliptic regularity on
  `H^{s,p}`, `H^s` and `B^s_{p,q}` for differential operators into a line bundle.
* `TauCeti.BundleTest.sobolevSingularSupport_subset_sobolevSingularSupport_localOperatorDualCLM`:
  elliptic operators shift the `H^s` singular support by their order.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11) (local elliptic regularity), and Lecture II, (3.1)–(3.8) (the `H^{s,p}`
  version).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 and Appendix B.1 (local Sobolev spaces on manifolds, defined chart by chart).
-/

public section

noncomputable section

open Set Function TopologicalSpace Distribution
open scoped ContDiff Manifold Distributions Topology CompactConvergenceCLM ENNReal

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

section TransferPrinciple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W 𝓘(ℝ, E)]
  {P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯}

/-- **Local elliptic regularity for differential operators into a line bundle**, for invariant
notions of local regularity `A` and `B` on `E`. Suppose that elliptic differential operators of
order at most `r` on `C^∞(E)` improve `A` to `B` by transposition: whenever `D` is such an operator,
elliptic at `y`, and the transpose `φ ↦ S (D φ)` of a distribution `S` satisfies `A` near `y`, then
`S` satisfies `B` near `y`. Let `P : Γ(V) → Γ(W)` be a differential operator of order at most `r`
into a bundle `W` of rank one, and `u ∈ V_x` a vector killed by the principal symbol
`σ(P)(ξ) : V_x → W_x` at no covector `ξ ≠ 0` at `x`. If the transpose `T ∘ P` of a functional `T`
on the bundle tests of `W` satisfies `A` near `x`, then `T` satisfies `B` near `x`. -/
theorem IsLocallyAt.of_localOperatorDualCLM {A B : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}
    (hA : IsInvariantLocalRegularity A) (hB : IsInvariantLocalRegularity B) {r : ℕ}
    (hAB : ∀ (Ω : Opens E) (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
      (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ r) (S R : 𝓓'(Ω, ℂ)) (y : E),
      (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) →
      (∀ η : E, η ≠ 0 → smoothPrincipalSymbol 𝓘(ℝ, E) (x := y)
        BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ (innerSL ℝ η : E →L[ℝ] ℝ) ≠ 0) →
      A Ω R y → B Ω S y)
    (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} {u : V x}
    (hσ : ∀ ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ, ξ ≠ 0 →
      sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ u ≠ 0)
    (h : IsLocallyAt A (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x) :
    IsLocallyAt B T x := by
  -- A chart `c` of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  have hy : c x ∈ c.target := c.map_source hxc
  -- The coefficients `v` of `u` in the frame of `V`, and a basis `b 0` of the line `F'`.
  set v := (trivializationAt F V x).continuousLinearMapAt ℝ x u
  have hu : (trivializationAt F V x).symmL ℝ x v = u :=
    (trivializationAt F V x).symmL_continuousLinearMapAt (hV hxc) u
  let b := Module.finBasisOfFinrankEq ℝ F' hF'
  have hℓ : Injective (LinearMap.toContinuousLinearMap (b.coord 0)) :=
    (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)).injective
  -- A cutoff `χ` equal to `1` on a neighbourhood `U` of `c x` in the chart target.
  obtain ⟨χ, U, hUt, hyU, hU1⟩ :=
    TestFunction.exists_opens_le_forall_eq_one (n := ⊤) (Ω := ⟨c.target, c.open_target⟩) hy
  -- The `(b 0)*, v` entry `D` of the chart compression of `P` by `χ` is elliptic at `c x`.
  let D := c.sectionChartCompressionDifferentialOperators he _ hV _ hW χ χ
    (LinearMap.toContinuousLinearMap (b.coord 0)) v r ⟨P, hP⟩
  have hD : ∀ η : E, η ≠ 0 → smoothPrincipalSymbol 𝓘(ℝ, E) (x := c x)
      BoundarylessManifold.isInteriorPoint D (innerSL ℝ η : E →L[ℝ] ℝ) ≠ 0 := fun η hη ↦ by
    -- The covector `⟪η, ·⟫ ∘ dc` is nonzero, since `dc ∘ dc⁻¹ = id` at `c x`.
    have hne : (innerSL ℝ η : E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm (c x))) ≠ 0 := by
      intro h0
      have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm (c x))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x) η) = η :=
        congr($((OpenPartialHomeomorph.MDifferentiable.comp_symm_deriv
          ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hy)) η)
      have h1 : inner ℝ η (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm (c x))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x) η)) = 0 :=
        congr($h0 (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x) η))
      rw [hd] at h1
      exact hη (inner_self_eq_zero.1 h1)
    rw [c.left_inv hxc] at hne
    exact c.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators_ne_zero he _ hV _ hW
      hℓ hxc (by simp [hU1 _ hyU]) (by simp [hU1 _ hyU]) (hu ▸ hσ _ hne)
  -- Over `U`, the component of `T ∘ P` along `v` is the transpose of the component of `T` along
  -- `b 0` by `D`, so the Euclidean statement applies to the restrictions to `U`.
  have hS : B _ ((trivializationAt F' W x).chartComponent c hc hW T (b 0)) (c x) := by
    rw [← hB.restrictCLM_iff hUt hyU]
    exact hAB U D.val D.property _ _ (c x)
      (fun _ _ _ hf hψ ↦
        restrictCLM_chartComponent_localOperatorDualCLM_apply hP he hV hW hUt hU1 v b 0 hf hψ T)
      hD ((hA.restrictCLM_iff hUt hyU).2 ((isLocallyAt_iff hA _ hc hcs hV hxc).1 h v))
  -- Every component of `T` is a multiple of its component along `b 0`.
  refine (isLocallyAt_iff hB T hc hcs hW hxc).2 fun w ↦ ?_
  rw [chartComponent_eq_sum _ c hc hW b T w]
  exact hB.sum hy fun i _ ↦ by
    rw [Subsingleton.elim i 0]
    exact hB.smul _ hS

end TransferPrinciple

section CoordinateSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [T2Space M] [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, CoordinateSpace n)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F', W⟯} {r : ℕ}

/-- **Interior elliptic regularity on `H^{s,p}` for differential operators into a line bundle.**
Let `1 < p < ∞`, let `P : Γ(V) → Γ(W)` be a differential operator of order at most `r` into a
bundle `W` of rank one, and `u ∈ V_x` a vector killed by the principal symbol
`σ(P)(ξ) : V_x → W_x` at no covector `ξ ≠ 0` at `x`. If the transpose `T ∘ P` of a functional `T`
on the bundle tests of `W` is `H^{s,p}` near `x`, then `T` is `H^{s + r,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.of_localOperatorDualCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F, V⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, CoordinateSpace n) F' W →L_c[ℝ] ℝ} {x : M} {u : V x} {s : ℝ}
    (hσ : ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P, hP⟩ ξ u ≠ 0)
    (h : IsLocallyMemSobolevAt s p (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x) :
    IsLocallyMemSobolevAt (s + r) p T x :=
  isLocallyMemSobolevAt_def.2 <| IsLocallyAt.of_localOperatorDualCLM
    (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top)
    (isInvariantLocalRegularity_isLocallyMemSobolevAt (s + r) hp hp_top)
    (fun _ _ hD _ _ _ hR hσ' ↦ IsLocallyMemSobolevAt.of_mem_differentialOperators hp hp_top hD hR
      hσ') hF' hP hσ (isLocallyMemSobolevAt_def.1 h)

/-- **Interior elliptic regularity on `H^s` for differential operators into a line bundle.** Let
`P : Γ(V) → Γ(W)` be a differential operator of order at most `r` into a bundle `W` of rank one,
and `u ∈ V_x` a vector killed by the principal symbol `σ(P)(ξ) : V_x → W_x` at no covector `ξ ≠ 0`
at `x`. If the transpose `T ∘ P` of a functional `T` on the bundle tests of `W` is `H^s` near `x`,
then `T` is `H^(s + r)` near `x`. -/
theorem IsLocallySobolevAt.of_localOperatorDualCLM (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F, V⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, CoordinateSpace n) F' W →L_c[ℝ] ℝ} {x : M} {u : V x} {s : ℝ}
    (hσ : ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P, hP⟩ ξ u ≠ 0)
    (h : IsLocallySobolevAt s (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x) :
    IsLocallySobolevAt (s + r) T x :=
  isLocallySobolevAt_def.2 <| IsLocallyAt.of_localOperatorDualCLM
    (isInvariantLocalRegularity_isLocallySobolevAt s)
    (isInvariantLocalRegularity_isLocallySobolevAt (s + r))
    (fun _ _ hD _ _ _ hR hσ' ↦ IsLocallySobolevAt.of_mem_differentialOperators hD hR hσ') hF' hP
    hσ (isLocallySobolevAt_def.1 h)

/-- **Interior elliptic regularity on Besov spaces for differential operators into a line
bundle.** Let `1 < p ≤ ∞` and `1 ≤ q ≤ ∞`, let `P : Γ(V) → Γ(W)` be a differential operator of
order at most `r` into a bundle `W` of rank one, and `u ∈ V_x` a vector killed by the principal
symbol `σ(P)(ξ) : V_x → W_x` at no covector `ξ ≠ 0` at `x`. If the transpose `T ∘ P` of a
functional `T` on the bundle tests of `W` is `B^s_{p,q}` near `x`, then `T` is `B^{s + r}_{p,q}`
near `x`. -/
theorem IsLocallyMemBesovAt.of_localOperatorDualCLM {ρ : ContDiffBump (0 : CoordinateSpace n)}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F, V⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, CoordinateSpace n) F' W →L_c[ℝ] ℝ} {x : M} {u : V x} {s : ℝ}
    (hσ : ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P, hP⟩ ξ u ≠ 0)
    (h : IsLocallyMemBesovAt ρ s p q (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x) :
    IsLocallyMemBesovAt ρ (s + r) p q T x :=
  isLocallyMemBesovAt_def.2 <| IsLocallyAt.of_localOperatorDualCLM
    (isInvariantLocalRegularity_isLocallyMemBesovAt ρ p q s)
    (isInvariantLocalRegularity_isLocallyMemBesovAt ρ p q (s + r))
    (fun _ _ hD _ _ _ hR hσ' ↦ IsLocallyMemBesovAt.of_mem_differentialOperators hp hD hR hσ') hF'
    hP hσ (isLocallyMemBesovAt_def.1 h)

/-- **Elliptic differential operators shift the `H^s` singular support by their order.** Let
`P : Γ(V) → Γ(W)` be a differential operator of order at most `r` into a bundle `W` of rank one,
elliptic at every point `x` in the sense that some `u ∈ V_x` is killed by the principal symbol
`σ(P)(ξ)` at no covector `ξ ≠ 0` at `x`. Then `T` is `H^(s + r)` wherever `T ∘ P` is `H^s`. -/
theorem sobolevSingularSupport_subset_sobolevSingularSupport_localOperatorDualCLM
    (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F, V⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F', W⟯ r)
    (hσ : ∀ x : M, ∃ u : V x, ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint
        ⟨P, hP⟩ ξ u ≠ 0)
    (s : ℝ) (T : BundleTest 𝓘(ℝ, CoordinateSpace n) F' W →L_c[ℝ] ℝ) :
    sobolevSingularSupport 𝓘(ℝ, CoordinateSpace n) (s + r) T ⊆
      sobolevSingularSupport 𝓘(ℝ, CoordinateSpace n) s (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) := by
  intro x hx
  rw [mem_sobolevSingularSupport_iff] at hx ⊢
  obtain ⟨u, hu⟩ := hσ x
  exact fun h ↦ hx (IsLocallySobolevAt.of_localOperatorDualCLM hF' hP hu h)

end CoordinateSpace

end TauCeti.BundleTest
