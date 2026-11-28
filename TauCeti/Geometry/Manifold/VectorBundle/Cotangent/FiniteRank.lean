/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.FiniteRank

/-!
# Finite-rank bundle core presentation of the cotangent bundle

Let `M` be a `C^1` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a finite basis `b : Module.Basis (Fin r) 𝕜 E` of its model space.
Taking the dual core of `TauCeti.tangentFiniteRankCore I M b` presents the cotangent bundle
`CotangentBundle I M` as a point-indexed finite-rank bundle core
`TauCeti.cotangentFiniteRankCore I M b` of rank `r`.

## Main declarations

* `TauCeti.cotangentFiniteRankCore`: the dual core `(tangentFiniteRankCore I M b).dual`.
* `TauCeti.isContMDiff_cotangentFiniteRankCore`: on a `C^(n+1)` manifold,
  `cotangentFiniteRankCore I M b` is a `C^n` core.
* `TauCeti.coordChange_cotangentFiniteRankCore`: its transitions are the transposes of the inverse
  tangent coordinate changes `tangentCoordChange I x₁ x₀ x` conjugated by `b.equivFunL`.
* `TauCeti.cotangentFiniteRankCoreTotalSpaceDiffeomorph`: canonical `C^n` diffeomorphism
  identifying `(cotangentFiniteRankCore I M b).core.TotalSpace` with `CotangentBundle I M`,
  sending a coordinate vector `w` over `x` to the covector `v ↦ ∑ k, b.repr v k * w k`,
  `Pi.single i 1` to `v ↦ b.repr v i`, and inversely a covector `α` to `i ↦ α (b i)`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1, §1.
-/

public section

open Bundle CategoryTheory FiberBundle Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section CotangentFiniteRank

variable [IsManifold I 1 M] {r : ℕ}

variable (I M) in
/-- The finite-rank bundle core presenting the cotangent bundle of `M`, constructed as the general
dual core `(tangentFiniteRankCore I M b).dual`. -/
noncomputable abbrev cotangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) : FiniteRankBundleCore 𝕜 M :=
  (tangentFiniteRankCore I M b).dual

omit [IsManifold I 1 M] in
/-- On a `C^(n+1)` manifold, `cotangentFiniteRankCore I M b` is a `C^n` core. -/
theorem isContMDiff_cotangentFiniteRankCore {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (b : Basis (Fin r) 𝕜 E) :
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (cotangentFiniteRankCore I M b).core.IsContMDiff I n :=
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentFiniteRankCore I M b).core.IsContMDiff I n := isContMDiff_tangentFiniteRankCore b
  FiniteRankBundleCore.isContMDiff_dual (tangentFiniteRankCore I M b)

/-- On the overlap of the charts at `x₀` and `x₁`, the transition map of
`cotangentFiniteRankCore I M b` is the transpose of the inverse tangent coordinate change
`tangentCoordChange I x₁ x₀ x` conjugated by `b.equivFunL`. -/
theorem coordChange_cotangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentFiniteRankCore I M b).core.coordChange x₀ x₁ x =
      (b.equivFunL.toContinuousLinearMap.comp
        ((tangentCoordChange I x₁ x₀ x).comp
          b.equivFunL.symm.toContinuousLinearMap)).piTranspose :=
  (FiniteRankBundleCore.coordChange_dual (tangentFiniteRankCore I M b) x₀ x₁ x).trans
    (congrArg ContinuousLinearMap.piTranspose (coordChange_tangentFiniteRankCore b hx₁ hx₀))

variable (I M) in
/-- Canonical `C^n` diffeomorphism (biholomorphism for `I = 𝓘(ℂ, E)`, `n = ∞`) identifying the dual
core total space `(cotangentFiniteRankCore I M b).core.TotalSpace` with `CotangentBundle I M`.
Under this dual convention, a coordinate vector `w` over `x` is the covector
`v ↦ ∑ k, b.repr v k * w k`. -/
noncomputable def cotangentFiniteRankCoreTotalSpaceDiffeomorph (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (cotangentFiniteRankCore I M b).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b).rank → 𝕜), I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯
      CotangentBundle I M :=
  FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph b.equivFunL (TangentSpace I) I n

@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).core.TotalSpace) :
    (cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n p).proj = p.proj := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph_apply]

@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_symm_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : CotangentBundle I M) :
    ((cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n).symm p).proj = p.proj := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph_symm_apply]

/-- Explicit dual pairing convention for `cotangentFiniteRankCoreTotalSpaceDiffeomorph`: a
coordinate vector `w` over `x` evaluates on a tangent vector `v` as `∑ k, b.repr v k * w k`. -/
@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_apply_snd_apply (b : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (x : M) (w : Fin r → 𝕜) (v : TangentSpace I x) :
    (cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n ⟨x, w⟩).snd v =
      ∑ k, b.repr v k * w k := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleDualFiberEquiv_apply_apply,
    TangentBundle.trivializationAt_apply_self]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg (· * w k) (b.equivFunL_apply (v : E) k)

/-- Explicit dual-basis convention: the `i`th standard basis vector `Pi.single i 1` over `x` maps
to the `i`th coordinate covector `v ↦ b.repr v i`. -/
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_single_apply (b : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (x : M) (i : Fin r) (v : TangentSpace I x) :
    (cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n ⟨x, (Pi.single i 1 : Fin r → 𝕜)⟩).snd v =
      b.repr v i :=
  (cotangentFiniteRankCoreTotalSpaceDiffeomorph_apply_snd_apply b n x
    (Pi.single i 1 : Fin r → 𝕜) v).trans (by simp [Pi.single_apply])

/-- Inversely, `cotangentFiniteRankCoreTotalSpaceDiffeomorph` records the coordinates of a covector
`α` over `x` as its evaluations `i ↦ α (b i)` on the basis `b`. -/
@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_symm_apply_snd_apply (b : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (x : M) (α : TangentSpace I x →L[𝕜] 𝕜) (i : Fin r) :
    ((cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n).symm ⟨x, α⟩).snd i = α (b i) := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph_symm_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleDualFiberEquiv_symm_apply,
    TangentBundle.trivializationAt_symm_apply_self]
  simp only [Basis.equivFunL_symm_apply, Fintype.sum_single_smul, one_smul]

end CotangentFiniteRank

end TauCeti
