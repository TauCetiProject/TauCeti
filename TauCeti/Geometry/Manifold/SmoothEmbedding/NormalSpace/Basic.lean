/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
public import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Normal spaces of smooth embeddings

At a point of a smoothly embedded submanifold, the normal space is the ambient tangent space
modulo the image of the differential of the embedding. This quotient is intrinsic: it needs no
metric or choice of complementary subspace. It is the normal space
`Manifold.IsImmersion.NormalSpace` of the underlying immersion `f.isImmersion`, where its
algebraic and topological structure, its quotient map and its dimension are developed. This file
adds the results that are stated for bundled embeddings.

An ambient tangent equivalence carrying one tangent range onto another induces an equivalence of
normal spaces (`TauCeti.SmoothEmbedding.normalSpaceEquivOfMapTangentRange`). A continuous linear
map out of the ambient tangent space whose kernel is exactly the tangent range identifies the
normal space with any target of the same dimension
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfKer`).

The inclusion of an open subset is the extreme case: it is tangent to every ambient direction
(`TauCeti.SmoothEmbedding.tangentRange_ofOpens`), so its normal spaces are zero
(`TauCeti.SmoothEmbedding.subsingleton_normalSpace_ofOpens`).

For the tubular-neighbourhood application of normal bundles, see M. Hirsch,
*Differential Topology*, Theorem 6.3.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

section Equiv

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H' G' : Type*} [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  {M' N' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {m : ℕ∞ω}
  (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
  (x : M) (y : M') (hn : n ≠ 0) (hm : m ≠ 0)

/-- An ambient tangent equivalence carrying one embedding's tangent range onto the other's
induces an equivalence of their intrinsic normal spaces. -/
noncomputable def normalSpaceEquivOfMapTangentRange
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (g y))
    (h : (f.isImmersion.tangentRange x hn).map e.toLinearMap = g.isImmersion.tangentRange y hm) :
    f.isImmersion.NormalSpace x hn ≃L[𝕜] g.isImmersion.NormalSpace y hm :=
  e.quotientEquiv (f.isImmersion.tangentRange x hn) (g.isImmersion.tangentRange y hm) h

/-- The normal-space equivalence induced by an ambient tangent equivalence applies it to
representatives. -/
@[simp]
theorem normalSpaceEquivOfMapTangentRange_normalClass
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (g y))
    (h : (f.isImmersion.tangentRange x hn).map e.toLinearMap = g.isImmersion.tangentRange y hm)
    (w : TangentSpace J (f x)) :
    f.normalSpaceEquivOfMapTangentRange g x y hn hm e h (f.isImmersion.normalClass x hn w) =
      g.isImmersion.normalClass y hm (e w) := by
  rw [Manifold.IsImmersion.normalClass_apply, Manifold.IsImmersion.normalClass_apply]
  exact e.quotientEquiv_mk (f.isImmersion.tangentRange x hn) (g.isImmersion.tangentRange y hm) h w

end Equiv

/-- The tangent spaces of a positive-regularity embedding into a manifold with
finite-dimensional model space are finite-dimensional, since the differential is injective. -/
theorem finiteDimensional_tangentSpace (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (TangentSpace I x) :=
  .of_injective (mfderiv I J (f : M → N) x).toLinearMap (f.isImmersion.mfderiv_injective hn x)

section KerEquiv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
  [T2Space V]

/-- A continuous linear map out of the ambient tangent space whose kernel is exactly the tangent
range, into a space of the dimension of the normal space, descends to a continuous linear
equivalence from the normal space: the normal class `[v]` corresponds to `g v`. -/
noncomputable def normalSpaceEquivOfKer (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 V) :
    f.isImmersion.NormalSpace x hn ≃L[𝕜] V :=
  let φ := f.isImmersion.normalLiftL x hn g fun v ↦ (hg v).2
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw ↦ ?_
    obtain ⟨v, rfl⟩ := f.isImmersion.normalClass_surjective x hn w
    rw [Manifold.IsImmersion.normalLiftL_normalClass, hg] at hw
    exact (f.isImmersion.normalClass_eq_zero_iff x hn v).2 hw
  (φ.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv

/-- The normal class `[v]` corresponds to `g v`. -/
@[simp]
theorem normalSpaceEquivOfKer_normalClass (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 V)
    (v : TangentSpace J (f x)) :
    f.normalSpaceEquivOfKer x hn g hg hdim (f.isImmersion.normalClass x hn v) = g v := by
  rw [normalSpaceEquivOfKer, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.linearEquivOfInjective_apply, ContinuousLinearMap.coe_coe,
        Manifold.IsImmersion.normalLiftL_normalClass]

/-- The value `g v` corresponds to the normal class `[v]`. -/
@[simp]
theorem normalSpaceEquivOfKer_symm_apply (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 V)
    (v : TangentSpace J (f x)) :
    (f.normalSpaceEquivOfKer x hn g hg hdim).symm (g v) = f.isImmersion.normalClass x hn v :=
  (ContinuousLinearEquiv.symm_apply_eq _).2
    (f.normalSpaceEquivOfKer_normalClass x hn g hg hdim v).symm

end KerEquiv

/-- The inclusion of an open subset is tangent to every ambient direction: its tangent range is the
whole tangent space, since the inclusion is a local diffeomorphism. -/
@[simp]
theorem tangentRange_ofOpens [IsManifold I n M] (s : TopologicalSpace.Opens M) (x : s)
    (hn : n ≠ 0) : (ofOpens (I := I) (n := n) s).isImmersion.tangentRange x hn = ⊤ := by
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_subtype_val (I := I) (n := n) x).isInvertible_mfderiv hn
  refine eq_top_iff.2 fun v _ ↦ (Manifold.IsImmersion.mem_tangentRange_iff _ x hn v).2 ?_
  rw [coe_ofOpens, ← he]
  exact e.surjective v

/-- The normal spaces of the inclusion of an open subset are zero. -/
instance subsingleton_normalSpace_ofOpens [IsManifold I n M] (s : TopologicalSpace.Opens M)
    (x : s) (hn : n ≠ 0) : Subsingleton
        ((ofOpens (I := I) (n := n) s).isImmersion.NormalSpace x hn) :=
  Submodule.Quotient.subsingleton_iff.2 (tangentRange_ofOpens s x hn)

end TauCeti.SmoothEmbedding
