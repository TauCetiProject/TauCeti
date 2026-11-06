/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.VectorField.Related

/-!
# Involutivity of differential kernels

The vertical vector fields of a map `f` are the fields annihilated by `df`. Their Lie bracket
is again vertical: both fields are related to the zero field on the target, so naturality of
the bracket applies. The pointwise statement only requires verticality near the point.

Consequently `x ↦ ker (mfderiv f x)` is an involutive distribution, also locally on any set
where `f` is sufficiently smooth. No submersion or constant-rank hypothesis is needed for
involutivity. Such hypotheses are needed separately to make these kernels a smooth vector
bundle; the submersion construction is in `Distribution.Submersion`.

These results apply to source-vertical fields on groupoids and to vertical fields on fibre
bundles. They impose no separation or countability assumptions on either manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 8 (naturality of the Lie bracket) and Chapter 19 (involutive distributions).
-/

public section

open Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (minSmoothness 𝕜 2) M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J (minSmoothness 𝕜 2) N]
  {f : M → N} {V W : Π x : M, TangentSpace I x} {x : M}

/-- The bracket of differentiable vector fields annihilated by `df` near `x` is annihilated
by `df` at `x`. Over `ℝ` or `ℂ`, `C²` regularity of `f` suffices. -/
theorem ContMDiffAt.mlieBracket_mem_ker_mfderiv
    (hf : ContMDiffAt I J n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hV : MDifferentiableAt I I.tangent (T% V) x)
    (hW : MDifferentiableAt I I.tangent (T% W) x)
    (hVker : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    (hWker : ∀ᶠ y in 𝓝 x, W y ∈ (mfderiv I J f y).ker) :
    mlieBracket I V W x ∈ (mfderiv I J f x).ker := by
  have : IsManifold J 2 N := .of_le (le_minSmoothness (𝕜 := 𝕜))
  have hzero : MDifferentiableAt J J.tangent (T% (0 : Π y : N, TangentSpace J y)) (f x) :=
    (Bundle.contMDiff_zeroSection 𝕜 (TangentSpace J) (n := 2)).mdifferentiableAt two_ne_zero
  have h := TauCeti.mfderiv_mlieBracket_of_eventually_related hf hn hV hW hzero hzero
    (hVker.mono fun y hy ↦ by
      simpa only [Pi.zero_apply, ContinuousLinearMap.coe_coe] using LinearMap.mem_ker.mp hy)
    (hWker.mono fun y hy ↦ by
      simpa only [Pi.zero_apply, ContinuousLinearMap.coe_coe] using LinearMap.mem_ker.mp hy)
  simpa only [mlieBracket_self, Pi.zero_apply, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] using h

/-- On any set where `f` is sufficiently smooth, its differential kernels are involutive.
The bracket test is on open subsets of that set, so `s` itself need not be open. -/
theorem ContMDiffOn.isInvolutiveDistributionOn_ker_mfderiv {s : Set M}
    (hf : ContMDiffOn I J n f s) (hn : minSmoothness 𝕜 2 ≤ n) :
    TauCeti.IsInvolutiveDistributionOn I (fun x ↦ (mfderiv I J f x).ker) s := by
  apply TauCeti.isInvolutiveDistributionOn_iff.mpr
  intro U hU hUs V W hV hW hVker hWker x hx
  have hUx := hU.mem_nhds hx
  exact ((hf.mono hUs).contMDiffAt hUx).mlieBracket_mem_ker_mfderiv hn
    ((hV x hx).mdifferentiableAt hUx) ((hW x hx).mdifferentiableAt hUx)
    (Filter.eventually_of_mem hUx hVker) (Filter.eventually_of_mem hUx hWker)

/-- The differential kernels of a sufficiently smooth map form an involutive distribution.
In particular this applies to the vertical distribution of a smooth submersion, without
requiring surjectivity or constant rank for this conclusion. -/
theorem ContMDiff.isInvolutiveDistribution_ker_mfderiv
    (hf : ContMDiff I J n f) (hn : minSmoothness 𝕜 2 ≤ n) :
    TauCeti.IsInvolutiveDistribution I (fun x ↦ (mfderiv I J f x).ker) := by
  exact TauCeti.isInvolutiveDistributionOn_univ.mp
    (hf.contMDiffOn.isInvolutiveDistributionOn_ker_mfderiv hn)
