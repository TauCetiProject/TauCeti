/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.FiniteRank
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ExteriorPower

/-!
# The determinant of the cotangent bundle and the canonical line bundle

Let `M` be a `C^1` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a basis `b : Module.Basis (Fin r) 𝕜 E` of its model space.
Applying `FiniteRankBundleCore.det` to `TauCeti.cotangentFiniteRankCore I M b` gives the
rank-one determinant line bundle `(TauCeti.cotangentFiniteRankCore I M b).det`, whose transitions
are scalar multiplication by the Jacobian determinants
`LinearMap.det (tangentCoordChange I x₁ x₀ x)` (`TauCeti.coordChange_det_cotangentFiniteRankCore`),
independent of `b`. Whenever `M` is `C^(n+1)` (and automatically at `n = ∞` for a complex
manifold), this determinant core is `C^n` (`TauCeti.isContMDiff_det_cotangentFiniteRankCore`).

For `r = Module.finrank 𝕜 E`, `TauCeti.detCotangentTotalSpaceDiffeomorph` gives the canonical
`C^n` diffeomorphism (biholomorphism for `𝕜 = ℂ` and `n = ∞`) and fibrewise `𝕜`-linear
identification between `(cotangentFiniteRankCore I M b).det.core.TotalSpace` and the canonical
line bundle `TauCeti.CanonicalBundle I M`. Under this top-exterior-power convention:

* a coordinate vector `v` over `x` corresponds to
  `detScalarEquiv _ v • CanonicalBundle.coordForm I x b x`, so the unit coordinate `fun _ ↦ 1` maps
  to `CanonicalBundle.coordForm I x b x`
  (`TauCeti.detCotangentTotalSpaceDiffeomorph_apply_const_one`);
* inversely, a top-degree form `η` evaluates on the basis `b`
  (`TauCeti.detCotangentTotalSpaceDiffeomorph_symm_apply_snd_apply`);
* over any chart domain `(chartAt H x₀).source`, the core chart coordinate at `x₀` is the
  coefficient of `CanonicalBundle.coordForm I x₀ b`
  (`TauCeti.detCotangentTotalSpaceDiffeomorph_apply_snd_eq_smul_coordForm`);
* changing the model basis from `b₁` to `b₂` via
  `FiniteRankBundleCore.ofBundleDualDetChangeDiffeomorph` commutes strictly with
  `detCotangentTotalSpaceDiffeomorph`
  (`TauCeti.detCotangentTotalSpaceDiffeomorph_changeDiffeomorph`).

General determinant-of-dual and basis-change isomorphisms on cores (`dualDetIsoDetDual`,
`dualDetDiffeomorphDetDual`, `ofBundleDualDetChangeIso`, `ofBundleDualDetChangeDiffeomorph`) live in
`TauCeti.Topology.VectorBundle.FiniteRank.Determinant` and
`TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant`.

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

section DeterminantCore

variable [IsManifold I 1 M] {r : ℕ}

omit [IsManifold I 1 M] in
/-- On a `C^(n+1)` manifold, the determinant line `(cotangentFiniteRankCore I M b).det` is a
`C^n` core. -/
theorem isContMDiff_det_cotangentFiniteRankCore {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (b : Basis (Fin r) 𝕜 E) :
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (cotangentFiniteRankCore I M b).det.core.IsContMDiff I n :=
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (cotangentFiniteRankCore I M b).core.IsContMDiff I n :=
    isContMDiff_cotangentFiniteRankCore b
  FiniteRankBundleCore.isContMDiff_det (cotangentFiniteRankCore I M b)

/-- On the overlap of the charts at `x₀` and `x₁`, the transition map of the determinant line
`(cotangentFiniteRankCore I M b).det` is scalar multiplication by the Jacobian determinant
`LinearMap.det (tangentCoordChange I x₁ x₀ x)`, independent of the basis `b`. -/
theorem coordChange_det_cotangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentFiniteRankCore I M b).det.core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜) := by
  have h : ((trivializationAt E (TangentSpace I) x₁).coordChangeL 𝕜
      (trivializationAt E (TangentSpace I) x₀) x : E →L[𝕜] E) = tangentCoordChange I x₁ x₀ x :=
    (tangentBundleCore I M).trivializationAt_coordChangeL (α := x₁) (β := x₀) (x := x) ⟨hx₁, hx₀⟩
  exact (FiniteRankBundleCore.coordChange_ofBundle_dual_det b.equivFunL (TangentSpace I)
    x₀ x₁ x).trans
    (congrArg (fun T : E →L[𝕜] E ↦ LinearMap.det (T : E →ₗ[𝕜] E) •
      ContinuousLinearMap.id 𝕜 (Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜)) h)

end DeterminantCore

/-! ### Identification with the canonical line bundle -/

section Canonical

variable [IsManifold I 1 M]

variable (I M) in
/-- Canonical `C^n` diffeomorphism (biholomorphism for `I = 𝓘(ℂ, E)`, `n = ∞`) identifying the
determinant line bundle `(cotangentFiniteRankCore I M b).det` with the canonical line bundle
`CanonicalBundle I M`. Under this top-exterior-power convention, the unit coordinate `fun _ ↦ 1`
over `x` corresponds to `CanonicalBundle.coordForm I x b x`, and inversely a top-degree form `η` is
sent to its evaluation `η b` on the basis `b`. -/
noncomputable def detCotangentTotalSpaceDiffeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω) :
    (cotangentFiniteRankCore I M b).det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
      TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph b (TangentSpace I) I n

@[simp]
theorem detCotangentTotalSpaceDiffeomorph_proj (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).proj = p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_apply]

@[simp]
theorem detCotangentTotalSpaceDiffeomorph_symm_proj (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    ((detCotangentTotalSpaceDiffeomorph I M b n).symm p).proj = p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_symm_apply]

/-- Evaluated on a tuple of tangent vectors `u` at `x`, `detCotangentTotalSpaceDiffeomorph` sends
`⟨x, v⟩` to `detScalarEquiv _ v * b.det u`. -/
@[simp]
theorem detCotangentTotalSpaceDiffeomorph_apply_snd_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (n : ℕ∞ω) (x : M) (v : Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜)
    (u : Fin (finrank 𝕜 E) → TangentSpace I x) :
    (detCotangentTotalSpaceDiffeomorph I M b n ⟨x, v⟩).snd u =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) v * b.det u := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_apply,
    FiniteRankBundleCore.ofBundleDualDetFiberEquiv_apply_apply]
  simp only [TangentBundle.trivializationAt_apply_self]

/-- Explicit top-exterior-power formula on fibres: `detCotangentTotalSpaceDiffeomorph` sends a
point `p` over `x` to `detScalarEquiv _ p.snd • CanonicalBundle.coordForm I x b x`. -/
theorem detCotangentTotalSpaceDiffeomorph_apply_snd (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).snd =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) p.snd •
        CanonicalBundle.coordForm I p.proj b p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_apply]
  dsimp only
  ext u
  refine (FiniteRankBundleCore.ofBundleDualDetFiberEquiv_apply_apply b (TangentSpace I)
    p.proj p.snd u).trans ?_
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, CanonicalBundle.coordForm_apply]
  simp only [TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self,
    TangentBundle.trivializationAt_apply_self]

/-- Under `detCotangentTotalSpaceDiffeomorph`, the unit coordinate `fun _ ↦ 1` over `x` maps to the
coordinate top-degree form `CanonicalBundle.coordForm I x b x`. -/
theorem detCotangentTotalSpaceDiffeomorph_apply_const_one (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (n : ℕ∞ω) (x : M) :
    detCotangentTotalSpaceDiffeomorph I M b n ⟨x, fun _ ↦ 1⟩ =
      ⟨x, CanonicalBundle.coordForm I x b x⟩ := by
  have h := detCotangentTotalSpaceDiffeomorph_apply_snd (I := I) b n ⟨x, fun _ ↦ 1⟩
  rw [FiniteRankBundleCore.detScalarEquiv_const, one_smul] at h
  exact TotalSpace.ext (detCotangentTotalSpaceDiffeomorph_proj b n ⟨x, fun _ ↦ 1⟩) (heq_of_eq h)

/-- Inversely, `detCotangentTotalSpaceDiffeomorph` sends a top-degree form `η` at `x` to the
constant scalar coordinate `η b`. -/
@[simp]
theorem detCotangentTotalSpaceDiffeomorph_symm_apply_snd_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (n : ℕ∞ω) (x : M) (η : CanonicalBundle I M x)
    (i : Fin (cotangentFiniteRankCore I M b).det.rank) :
    ((detCotangentTotalSpaceDiffeomorph I M b n).symm ⟨x, η⟩).snd i = η b := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_symm_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleDualDetFiberEquiv_symm_apply]
  congr 1; funext k
  exact TangentBundle.trivializationAt_symm_apply_self x (b k)

/-- Over the source of any chart at `x₀`, `detCotangentTotalSpaceDiffeomorph` expresses the image
of `p` as its core chart coordinate at `x₀` times the chart coordinate form
`CanonicalBundle.coordForm I x₀ b p.proj`. -/
theorem detCotangentTotalSpaceDiffeomorph_apply_snd_eq_smul_coordForm
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω) {x₀ : M}
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace)
    (hx : p.proj ∈ (chartAt H x₀).source) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).snd =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b)
          (((cotangentFiniteRankCore I M b).det.core.localTriv x₀ p).2) •
        CanonicalBundle.coordForm I x₀ b p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_apply]
  refine (CanonicalBundle.eq_smul_coordForm (b := b) hx _).trans ?_
  congr 1
  rw [FiniteRankBundleCore.trivializationAt_ofBundleDualDetFiberEquiv_snd b (TangentSpace I)
    x₀ (by simpa using hx) p.snd, Module.Basis.topFormEquiv_symm_apply, b.det_self, mul_one]

/-- Changing the model basis commutes strictly with the canonical-bundle identification
`detCotangentTotalSpaceDiffeomorph`. -/
theorem detCotangentTotalSpaceDiffeomorph_changeDiffeomorph
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b₁).det.core.TotalSpace) :
    detCotangentTotalSpaceDiffeomorph I M b₂ n
        (FiniteRankBundleCore.ofBundleDualDetChangeDiffeomorph b₁ b₂ (TangentSpace I) I n p) =
      detCotangentTotalSpaceDiffeomorph I M b₁ n p :=
  FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph_changeDiffeomorph b₁ b₂
    (TangentSpace I) p

end Canonical

end TauCeti
