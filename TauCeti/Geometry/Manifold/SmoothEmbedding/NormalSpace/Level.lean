/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# Normal spaces of embeddings cut out by equations

Let `f : M → N` be a smooth embedding into a manifold modelled on a finite-dimensional space `F`,
and let `g : N → V` be a map to a normed space which is constant on the image of `f` near `x`,
has `f x` as a regular point (surjective differential), and such that the dimensions add up:
`dim E + dim V = dim F`, where `E` is the model of `M`. This is the situation of a submanifold
cut out by `dim V` independent equations. Then the tangent sequence

`0 → T_x M → T_{f x} N → V → 0`,

formed by the differentials of `f` and of `g`, is exact. Its injectivity on the left is the
immersion property of `f`; exactness in the middle
(`TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv`,
`TauCeti.SmoothEmbedding.exact_mfderiv_mfderiv`) is the tangent space of a regular level,
`TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`. Consequently the differential of `g` induces
an isomorphism from the intrinsic normal space of `f` at `x` onto `V`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`), sending the normal class of an ambient tangent
vector `v` to `dg(v)`.

The constancy hypothesis only asks that `g ∘ f` be locally constant; `f` need not be the inclusion
of a whole level set of `g`. The surjectivity and dimension hypotheses are what force the image
of `df` to fill the kernel of `dg`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.38, for the tangent space of a regular level set.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) {g : N → V} {c : V}
  (hgf : ∀ᶠ y in 𝓝 x, g (f y) = c) (hsurj : IsRegularPoint J 𝓘(𝕜, V) g (f x))
  (hdim : Module.finrank 𝕜 E + Module.finrank 𝕜 V = Module.finrank 𝕜 F)
include hn hgf hsurj hdim

/-- **The tangent space of an embedding cut out by equations is the kernel of their differential.**
If `g` is constant on the image of the embedding `f` near `x`, has surjective differential at
`f x`, and the dimension of the source of `f` plus that of the target of `g` is the ambient
dimension, then the tangent range of `f` at `x` is the kernel of the differential of `g`. -/
theorem tangentRange_eq_ker_mfderiv :
    f.tangentRange x hn = (mfderiv J 𝓘(𝕜, V) g (f x)).ker :=
  hsurj.range_mfderiv_eq_ker_mfderiv hgf (f.isImmersion.mfderiv_injective hn x) hdim

/-- **The tangent sequence of an embedding cut out by equations is exact in the middle.** Under the
hypotheses of `TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv`, the differentials
`T_x M → T_{f x} N → V` of `f` and of `g` form an exact sequence. -/
theorem exact_mfderiv_mfderiv :
    Function.Exact (mfderiv I J f x) (mfderiv J 𝓘(𝕜, V) g (f x)) :=
  LinearMap.exact_iff.2 (f.tangentRange_eq_ker_mfderiv x hn hgf hsurj hdim).symm

omit [FiniteDimensional 𝕜 F] hn hgf hsurj hdim in
/-- The differential of `g`, read with values in the model space `V`. -/
private noncomputable abbrev mfderivV (g : N → V) : TangentSpace J (f x) →ₗ[𝕜] V :=
  (mfderiv J 𝓘(𝕜, V) g (f x)).toLinearMap

/-- The linear equivalence underlying `TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel`: the
tangent range is the kernel of `dg`, so the first isomorphism theorem applies. -/
private noncomputable def normalSpaceLinearEquivOfLevel : f.NormalSpace x hn ≃ₗ[𝕜] V :=
  (Submodule.quotEquivOfEq _ _ (f.tangentRange_eq_ker_mfderiv x hn hgf hsurj hdim)).trans
    ((mfderivV f x g).quotKerEquivOfSurjective (isRegularPoint_iff.1 hsurj))

/-- `TauCeti.SmoothEmbedding.normalSpaceLinearEquivOfLevel` sends the normal class of `v` to
`dg(v)`. -/
private theorem normalSpaceLinearEquivOfLevel_normalClass (v : TangentSpace J (f x)) :
    f.normalSpaceLinearEquivOfLevel x hn hgf hsurj hdim (f.normalClass x hn v) =
      mfderivV f x g v := by
  rw [normalClass_def]
  -- `quotEquivOfEq` fixes classes, so this is the first isomorphism theorem on the class of `v`.
  exact (mfderivV f x g).quotKerEquivOfSurjective_apply_mk (isRegularPoint_iff.1 hsurj) v

variable [CompleteSpace 𝕜]

/-- **The normal space of an embedding cut out by equations.** Under the hypotheses of
`TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv`, the differential of `g` at `f x` induces a
continuous linear equivalence from the normal space of `f` at `x` onto `V`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel_normalClass`). -/
noncomputable def normalSpaceEquivOfLevel : f.NormalSpace x hn ≃L[𝕜] V :=
  -- Tangent spaces are their model spaces, so the normal space is finite-dimensional.
  haveI : FiniteDimensional 𝕜 (TangentSpace J (f x)) := inferInstanceAs (FiniteDimensional 𝕜 F)
  haveI : FiniteDimensional 𝕜 (f.NormalSpace x hn) :=
    inferInstanceAs (FiniteDimensional 𝕜 (TangentSpace J (f x) ⧸ f.tangentRange x hn))
  (f.normalSpaceLinearEquivOfLevel x hn hgf hsurj hdim).toContinuousLinearEquiv

/-- The normal-space equivalence induced by `g` sends the normal class of an ambient tangent
vector `v` to the differential of `g` applied to `v`. -/
@[simp]
theorem normalSpaceEquivOfLevel_normalClass (v : TangentSpace J (f x)) :
    f.normalSpaceEquivOfLevel x hn hgf hsurj hdim (f.normalClass x hn v) =
      mfderiv J 𝓘(𝕜, V) g (f x) v := by
  simp only [normalSpaceEquivOfLevel, LinearEquiv.coe_toContinuousLinearEquiv']
  exact f.normalSpaceLinearEquivOfLevel_normalClass x hn hgf hsurj hdim v

end TauCeti.SmoothEmbedding
