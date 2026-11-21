/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ExteriorPower
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The cotangent bundle, its determinant, and the canonical line bundle from finite-rank cores

Let `M` be a `C^1` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a basis `b : Module.Basis (Fin r) 𝕜 E` of its model space.
Applying the general finite-rank vector-bundle-core API (`FiniteRankBundleCore.ofBundleEquiv`,
`FiniteRankBundleCore.dual`, and `FiniteRankBundleCore.det`) produces three bundles from the same
construction:

* `TauCeti.tangentFiniteRankCore I M b`: the finite-rank core presenting the tangent bundle `TM`,
  with transitions `b ∘ tangentCoordChange I x₀ x₁ x ∘ b⁻¹`
  (`TauCeti.coordChange_tangentFiniteRankCore`);
* `TauCeti.cotangentFiniteRankCore I M b`: its dual core `(tangentFiniteRankCore I M b).dual`,
  with transitions the transposes of the inverse tangent coordinate changes
  (`TauCeti.coordChange_cotangentFiniteRankCore`);
* `(TauCeti.cotangentFiniteRankCore I M b).det`: its rank-one determinant line bundle, whose
  transitions are scalar multiplication by the Jacobian determinants
  `LinearMap.det (tangentCoordChange I x₁ x₀ x)`
  (`TauCeti.coordChange_det_cotangentFiniteRankCore`), independent of `b`.

Whenever `TangentSpace I` is a `C^n` vector bundle (in particular for any `C^(n+1)` manifold, and
automatically at `n = ∞` for a complex manifold modelled on `𝓘(ℂ, E)`), all three cores are `C^n`
by `FiniteRankBundleCore.isContMDiff_ofBundleEquiv`, `FiniteRankBundleCore.isContMDiff_dual`, and
`FiniteRankBundleCore.isContMDiff_det`, giving the holomorphic tangent bundle, holomorphic
cotangent bundle, and holomorphic determinant / canonical line bundle when `𝕜 = ℂ` and `n = ∞`.

Each reconstructed total space is `C^n` diffeomorphic (biholomorphic for `𝕜 = ℂ`, `n = ∞`) and
fibrewise `𝕜`-linearly equivalent to the corresponding native bundle, with explicit conventions
recorded in the declarations:

* **Dual convention** (`TauCeti.cotangentFiniteRankCoreTotalSpaceDiffeomorph`): a dual coordinate
  vector `w : Fin r → 𝕜` over `x` corresponds to the covector `v ↦ ∑ k, b.repr v k * w k` in
  `CotangentBundle I M`; the `i`th standard basis vector `Pi.single i 1` corresponds to the `i`th
  dual basis covector `v ↦ b.repr v i`, and the inverse evaluates a covector `α` on `b i`.
* **Determinant-of-dual convention** (`TauCeti.detCotangentIsoDualDetTangent`,
  `TauCeti.detCotangentDiffeomorphDualDetTangent`): `det(T*M) ≅ (det TM)*` identifies the unit
  scalar coordinate of `(cotangentFiniteRankCore I M b).det` with that of
  `(tangentFiniteRankCore I M b).det.dual`.
* **Top-exterior-power / canonical-bundle convention**
  (`TauCeti.detCotangentTotalSpaceDiffeomorph`, for `r = Module.finrank 𝕜 E`): a coordinate vector
  `v` over `x` corresponds to `detScalarEquiv _ v • CanonicalBundle.coordForm I x b x`, so the
  unit coordinate `fun _ ↦ 1` maps to `CanonicalBundle.coordForm I x b x`, the inverse evaluates a
  top-degree form `η` on the basis `b`, and over any chart domain `(chartAt H x₀).source` the core
  chart coordinate at `x₀` is the coefficient of `CanonicalBundle.coordForm I x₀ b`
  (`TauCeti.detCotangentTotalSpaceDiffeomorph_eq_smul_coordForm`). Changing the model basis from
  `b₁` to `b₂` acts by `b₁.det b₂`, agrees with the functorial image under `dualMap` and
  `exteriorPower`, and commutes strictly with `detCotangentTotalSpaceDiffeomorph`.

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

section FiniteRankCores

variable [IsManifold I 1 M] {r : ℕ}

variable (I M) in
/-- The finite-rank bundle core presenting the tangent bundle `TangentSpace I` of `M`, using a
model-space basis `b : Basis (Fin r) 𝕜 E`. -/
noncomputable abbrev tangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) : FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofBundleEquiv b.equivFunL (TangentSpace I)

variable (I M) in
/-- The finite-rank bundle core presenting the cotangent bundle of `M`, constructed as the general
dual core `(tangentFiniteRankCore I M b).dual`. -/
noncomputable abbrev cotangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) : FiniteRankBundleCore 𝕜 M :=
  (tangentFiniteRankCore I M b).dual

/-! ### Regularity -/

omit [IsManifold I 1 M] in
/-- On a `C^(n+1)` manifold, `tangentFiniteRankCore I M b` is a `C^n` core. -/
theorem isContMDiff_tangentFiniteRankCore {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (b : Basis (Fin r) 𝕜 E) :
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentFiniteRankCore I M b).core.IsContMDiff I n :=
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  FiniteRankBundleCore.isContMDiff_ofBundleEquiv b.equivFunL (TangentSpace I : M → Type _)

omit [IsManifold I 1 M] in
/-- On a `C^(n+1)` manifold, `cotangentFiniteRankCore I M b` is a `C^n` core. -/
theorem isContMDiff_cotangentFiniteRankCore {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (b : Basis (Fin r) 𝕜 E) :
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (cotangentFiniteRankCore I M b).core.IsContMDiff I n :=
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentFiniteRankCore I M b).core.IsContMDiff I n := isContMDiff_tangentFiniteRankCore b
  FiniteRankBundleCore.isContMDiff_dual (tangentFiniteRankCore I M b)

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

/-! ### Transition functions and Jacobian determinants -/

/-- On the overlap of the charts at `x₀` and `x₁`, the transition map of
`tangentFiniteRankCore I M b` is `tangentCoordChange I x₀ x₁ x` conjugated by `b.equivFunL`. -/
theorem coordChange_tangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (tangentFiniteRankCore I M b).core.coordChange x₀ x₁ x =
      b.equivFunL.toContinuousLinearMap.comp
        ((tangentCoordChange I x₀ x₁ x).comp b.equivFunL.symm.toContinuousLinearMap) := by
  have h : ((trivializationAt E (TangentSpace I) x₀).coordChangeL 𝕜
      (trivializationAt E (TangentSpace I) x₁) x : E →L[𝕜] E) = tangentCoordChange I x₀ x₁ x :=
    (tangentBundleCore I M).trivializationAt_coordChangeL (α := x₀) (β := x₁) (x := x) ⟨hx₀, hx₁⟩
  exact (FiniteRankBundleCore.coordChange_ofBundleEquiv b.equivFunL (TangentSpace I) x₀ x₁ x).trans
    (congrArg (fun T : E →L[𝕜] E ↦ b.equivFunL.toContinuousLinearMap.comp
      (T.comp b.equivFunL.symm.toContinuousLinearMap)) h)

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
  exact (FiniteRankBundleCore.coordChange_ofBundleEquiv_dual_det b.equivFunL (TangentSpace I)
    x₀ x₁ x).trans
    (congrArg (fun T : E →L[𝕜] E ↦ LinearMap.det (T : E →ₗ[𝕜] E) •
      ContinuousLinearMap.id 𝕜 (Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜)) h)

/-! ### Total-space diffeomorphisms and explicit conventions -/

variable (I M) in
/-- Canonical `C^n` diffeomorphism identifying `(tangentFiniteRankCore I M b).core.TotalSpace` with
`TangentBundle I M` over the identity of `M`, sending a coordinate vector `v` over `x` to
`b.equivFunL.symm v`. -/
noncomputable def tangentFiniteRankCoreTotalSpaceDiffeomorph (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (tangentFiniteRankCore I M b).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (tangentFiniteRankCore I M b).rank → 𝕜), I.prod 𝓘(𝕜, E)⟯
      TangentBundle I M :=
  FiniteRankBundleCore.ofBundleEquivTotalSpaceDiffeomorph b.equivFunL (TangentSpace I) I n

@[simp]
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_apply (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (tangentFiniteRankCore I M b).core.TotalSpace) :
    tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n p = ⟨p.proj, b.equivFunL.symm p.snd⟩ :=
  (FiniteRankBundleCore.ofBundleEquivTotalSpaceDiffeomorph_apply b.equivFunL (TangentSpace I)
    p).trans <|
    congrArg (TotalSpace.mk' E p.proj) <|
      (FiniteRankBundleCore.ofBundleEquivFiberEquiv_apply b.equivFunL (TangentSpace I) p.proj
        p.snd).trans (TangentBundle.trivializationAt_symm_apply_self p.proj _)

/-- The `i`th standard basis vector over `x` in `tangentFiniteRankCore I M b` corresponds to the
tangent vector `b i` in `TangentBundle I M`. -/
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_single (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (x : M) (i : Fin r) :
    tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n ⟨x, (Pi.single i 1 : Fin r → 𝕜)⟩ =
      ⟨x, b i⟩ :=
  (tangentFiniteRankCoreTotalSpaceDiffeomorph_apply b n ⟨x, (Pi.single i 1 : Fin r → 𝕜)⟩).trans <|
    congrArg (TotalSpace.mk' E x) (Basis.equivFun_symm_single b i)

@[simp]
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_symm_apply (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : TangentBundle I M) :
    (tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n).symm p = ⟨p.proj, b.equivFunL p.snd⟩ := by
  rw [tangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivTotalSpaceDiffeomorph_symm_apply,
    FiniteRankBundleCore.ofBundleEquivFiberEquiv_symm_apply,
    TangentBundle.trivializationAt_apply_self]

variable (I M) in
/-- Canonical `C^n` diffeomorphism (biholomorphism for `I = 𝓘(ℂ, E)`, `n = ∞`) identifying the dual
core total space `(cotangentFiniteRankCore I M b).core.TotalSpace` with `CotangentBundle I M`.
Under this dual convention, a coordinate vector `w` over `x` is the covector
`v ↦ ∑ k, b.repr v k * w k`. -/
noncomputable def cotangentFiniteRankCoreTotalSpaceDiffeomorph (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (cotangentFiniteRankCore I M b).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b).rank → 𝕜), I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯
      CotangentBundle I M :=
  FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph b.equivFunL (TangentSpace I) I n

@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).core.TotalSpace) :
    (cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n p).proj = p.proj := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph_apply]

@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_symm_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : CotangentBundle I M) :
    ((cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n).symm p).proj = p.proj := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph_symm_apply]

/-- Explicit dual pairing convention for `cotangentFiniteRankCoreTotalSpaceDiffeomorph`: a
coordinate vector `w` over `x` evaluates on a tangent vector `v` as `∑ k, b.repr v k * w k`. -/
@[simp]
theorem cotangentFiniteRankCoreTotalSpaceDiffeomorph_apply_snd_apply (b : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (x : M) (w : Fin r → 𝕜) (v : TangentSpace I x) :
    (cotangentFiniteRankCoreTotalSpaceDiffeomorph I M b n ⟨x, w⟩).snd v =
      ∑ k, b.repr v k * w k := by
  rw [cotangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleEquivDualFiberEquiv_apply_apply,
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
    FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph_symm_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleEquivDualFiberEquiv_symm_apply,
    TangentBundle.trivializationAt_symm_apply_self]
  simp only [Basis.equivFunL_symm_apply, Fintype.sum_single_smul, one_smul]

variable (I M) in
/-- Canonical core isomorphism `det(T*M) ≅ (det TM)*` identifying the determinant of the cotangent
core with the dual of the determinant of the tangent core, preserving the unit scalar
coordinate. -/
noncomputable def detCotangentIsoDualDetTangent (b : Basis (Fin r) 𝕜 E) :
    (cotangentFiniteRankCore I M b).det ≅ (tangentFiniteRankCore I M b).det.dual :=
  FiniteRankBundleCore.dualDetIsoDetDual (tangentFiniteRankCore I M b)

/-- Under `detCotangentIsoDualDetTangent`, reading the image in `(det TM)*` via `detScalarEquiv`
gives the original scalar coordinate in `det(T*M)`. -/
@[simp]
theorem detScalarEquiv_detCotangentIsoDualDetTangent_hom (b : Basis (Fin r) 𝕜 E) (x : M)
    (v : Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (tangentFiniteRankCore I M b)
        ((detCotangentIsoDualDetTangent I M b).hom.fiberMap x v) =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) v :=
  FiniteRankBundleCore.detScalarEquiv_dualDetIsoDetDual_hom (tangentFiniteRankCore I M b) x v

/-- Inversely, under `detCotangentIsoDualDetTangent`, reading the image in `det(T*M)` via
`detScalarEquiv` gives the original scalar coordinate in `(det TM)*`. -/
@[simp]
theorem detScalarEquiv_detCotangentIsoDualDetTangent_inv (b : Basis (Fin r) 𝕜 E) (x : M)
    (v : Fin (tangentFiniteRankCore I M b).det.dual.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b)
        ((detCotangentIsoDualDetTangent I M b).inv.fiberMap x v) =
      FiniteRankBundleCore.detScalarEquiv (tangentFiniteRankCore I M b) v :=
  FiniteRankBundleCore.detScalarEquiv_dualDetIsoDetDual_inv (tangentFiniteRankCore I M b) x v

variable (I M) in
/-- Canonical `C^n` diffeomorphism (biholomorphism for `I = 𝓘(ℂ, E)`, `n = ∞`) realizing
`det(T*M) ≅ (det TM)*` on total spaces. -/
noncomputable def detCotangentDiffeomorphDualDetTangent (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (cotangentFiniteRankCore I M b).det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (tangentFiniteRankCore I M b).det.dual.rank → 𝕜)⟯
      (tangentFiniteRankCore I M b).det.dual.core.TotalSpace :=
  FiniteRankBundleCore.dualDetDiffeomorphDetDual (tangentFiniteRankCore I M b) I n

@[simp]
theorem detCotangentDiffeomorphDualDetTangent_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    (detCotangentDiffeomorphDualDetTangent I M b n p).proj = p.proj := by
  rw [detCotangentDiffeomorphDualDetTangent,
    FiniteRankBundleCore.dualDetDiffeomorphDetDual_apply, CoordinateHom.totalSpaceMap_proj]

@[simp]
theorem detCotangentDiffeomorphDualDetTangent_symm_proj (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (tangentFiniteRankCore I M b).det.dual.core.TotalSpace) :
    ((detCotangentDiffeomorphDualDetTangent I M b n).symm p).proj = p.proj := by
  rw [detCotangentDiffeomorphDualDetTangent,
    FiniteRankBundleCore.dualDetDiffeomorphDetDual_symm_apply, CoordinateHom.totalSpaceMap_proj]

@[simp]
theorem detScalarEquiv_detCotangentDiffeomorphDualDetTangent_snd (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    FiniteRankBundleCore.detScalarEquiv (tangentFiniteRankCore I M b)
        (detCotangentDiffeomorphDualDetTangent I M b n p).snd =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) p.snd :=
  FiniteRankBundleCore.detScalarEquiv_dualDetDiffeomorphDetDual_snd
    (tangentFiniteRankCore I M b) p

@[simp]
theorem detScalarEquiv_detCotangentDiffeomorphDualDetTangent_symm_snd (b : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (p : (tangentFiniteRankCore I M b).det.dual.core.TotalSpace) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b)
        ((detCotangentDiffeomorphDualDetTangent I M b n).symm p).snd =
      FiniteRankBundleCore.detScalarEquiv (tangentFiniteRankCore I M b) p.snd :=
  FiniteRankBundleCore.detScalarEquiv_dualDetDiffeomorphDetDual_symm_snd
    (tangentFiniteRankCore I M b) p

/-! ### Basis-change compatibility -/

variable (I M) in
/-- Changing the model basis from `b₁` to `b₂` induces a canonical isomorphism between the
determinant line cores `(cotangentFiniteRankCore I M b₁).det` and
`(cotangentFiniteRankCore I M b₂).det`, scaling scalar coordinates by `b₁.det b₂`. -/
noncomputable def detCotangentChangeIso (b₁ b₂ : Basis (Fin r) 𝕜 E) :
    (cotangentFiniteRankCore I M b₁).det ≅ (cotangentFiniteRankCore I M b₂).det :=
  FiniteRankBundleCore.ofBundleEquivDualDetChangeIso b₁ b₂ (TangentSpace I)

/-- Under `detCotangentChangeIso`, changing basis from `b₁` to `b₂` scales scalar coordinates by
`b₁.det b₂`. -/
@[simp]
theorem detScalarEquiv_detCotangentChangeIso_hom (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M)
    (v : Fin (cotangentFiniteRankCore I M b₁).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₂)
        ((detCotangentChangeIso I M b₁ b₂).hom.fiberMap x v) =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₁) v :=
  FiniteRankBundleCore.detScalarEquiv_ofBundleEquivDualDetChangeIso_hom b₁ b₂ (TangentSpace I) x v

/-- Inversely, `(detCotangentChangeIso I M b₁ b₂).inv` scales scalar coordinates by `b₂.det b₁`. -/
@[simp]
theorem detScalarEquiv_detCotangentChangeIso_inv (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M)
    (v : Fin (cotangentFiniteRankCore I M b₂).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₁)
        ((detCotangentChangeIso I M b₁ b₂).inv.fiberMap x v) =
      b₂.det b₁ * FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₂) v :=
  FiniteRankBundleCore.detScalarEquiv_ofBundleEquivDualDetChangeIso_inv b₁ b₂ (TangentSpace I) x v

variable (I M) in
/-- Changing the model basis from `b₁` to `b₂` induces a `C^n` diffeomorphism of determinant-line
total spaces over the identity of `M`. -/
noncomputable def detCotangentChangeDiffeomorph (b₁ b₂ : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (cotangentFiniteRankCore I M b₁).det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b₁).det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (cotangentFiniteRankCore I M b₂).det.rank → 𝕜)⟯
      (cotangentFiniteRankCore I M b₂).det.core.TotalSpace :=
  FiniteRankBundleCore.ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ (TangentSpace I) I n

/-- `detCotangentChangeDiffeomorph` preserves the base projection. -/
@[simp]
theorem detCotangentChangeDiffeomorph_proj (b₁ b₂ : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b₁).det.core.TotalSpace) :
    (detCotangentChangeDiffeomorph I M b₁ b₂ n p).proj = p.proj := by
  rw [detCotangentChangeDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetChangeDiffeomorph_apply,
    CoordinateHom.totalSpaceMap_proj]

/-- The inverse of `detCotangentChangeDiffeomorph` preserves the base projection. -/
@[simp]
theorem detCotangentChangeDiffeomorph_symm_proj (b₁ b₂ : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b₂).det.core.TotalSpace) :
    ((detCotangentChangeDiffeomorph I M b₁ b₂ n).symm p).proj = p.proj := by
  rw [detCotangentChangeDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetChangeDiffeomorph_symm_apply,
    CoordinateHom.totalSpaceMap_proj]

/-- `detCotangentChangeDiffeomorph` scales scalar coordinates by `b₁.det b₂`. -/
@[simp]
theorem detScalarEquiv_detCotangentChangeDiffeomorph_snd (b₁ b₂ : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b₁).det.core.TotalSpace) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₂)
        (detCotangentChangeDiffeomorph I M b₁ b₂ n p).snd =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₁) p.snd :=
  FiniteRankBundleCore.detScalarEquiv_ofBundleEquivDualDetChangeDiffeomorph_snd b₁ b₂
    (TangentSpace I) p

/-- The inverse of `detCotangentChangeDiffeomorph` scales scalar coordinates by `b₂.det b₁`. -/
@[simp]
theorem detScalarEquiv_detCotangentChangeDiffeomorph_symm_snd (b₁ b₂ : Basis (Fin r) 𝕜 E)
    (n : ℕ∞ω) (p : (cotangentFiniteRankCore I M b₂).det.core.TotalSpace) :
    FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₁)
        ((detCotangentChangeDiffeomorph I M b₁ b₂ n).symm p).snd =
      b₂.det b₁ * FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b₂) p.snd :=
  FiniteRankBundleCore.detScalarEquiv_ofBundleEquivDualDetChangeDiffeomorph_symm_snd b₁ b₂
    (TangentSpace I) p

/-- The basis-change isomorphism `detCotangentChangeIso` agrees with the functorial image of the
tangent-core basis change under `dualMap` and `exteriorPower`. -/
theorem detCotangentChangeIso_hom_eq_exteriorPower_dualMap (b₁ b₂ : Basis (Fin r) 𝕜 E) :
    (detCotangentChangeIso I M b₁ b₂).hom =
      (eqToIso (FiniteRankBundleCore.det_def (cotangentFiniteRankCore I M b₁))).hom ≫
        (FiniteRankBundleCore.exteriorPower 𝕜 M r).map
          (FiniteRankBundleCore.dualMap
            (FiniteRankBundleCore.ofBundleEquivChangeIso b₂.equivFunL b₁.equivFunL
              (TangentSpace I)).hom) ≫
        (eqToIso (FiniteRankBundleCore.det_def (cotangentFiniteRankCore I M b₂))).inv :=
  FiniteRankBundleCore.ofBundleEquivDualDetChangeIso_hom_eq_exteriorPower_dualMap b₁ b₂
    (TangentSpace I)

end FiniteRankCores

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
  FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph b (TangentSpace I) I n

@[simp]
theorem detCotangentTotalSpaceDiffeomorph_proj (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).proj = p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_apply]

@[simp]
theorem detCotangentTotalSpaceDiffeomorph_symm_proj (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    ((detCotangentTotalSpaceDiffeomorph I M b n).symm p).proj = p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_symm_apply]

/-- Evaluated on a tuple of tangent vectors `u` at `x`, `detCotangentTotalSpaceDiffeomorph` sends
`⟨x, v⟩` to `detScalarEquiv _ v * b.det u`. -/
@[simp]
theorem detCotangentTotalSpaceDiffeomorph_apply_snd_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (n : ℕ∞ω) (x : M) (v : Fin (cotangentFiniteRankCore I M b).det.rank → 𝕜)
    (u : Fin (finrank 𝕜 E) → TangentSpace I x) :
    (detCotangentTotalSpaceDiffeomorph I M b n ⟨x, v⟩).snd u =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) v * b.det u := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_apply,
    FiniteRankBundleCore.ofBundleEquivDualDetFiberEquiv_apply_apply]
  simp only [TangentBundle.trivializationAt_apply_self]

/-- Explicit top-exterior-power formula on fibres: `detCotangentTotalSpaceDiffeomorph` sends a
point `p` over `x` to `detScalarEquiv _ p.snd • CanonicalBundle.coordForm I x b x`. -/
theorem detCotangentTotalSpaceDiffeomorph_apply_snd (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).snd =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b) p.snd •
        CanonicalBundle.coordForm I p.proj b p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_apply]
  dsimp only
  ext u
  refine (FiniteRankBundleCore.ofBundleEquivDualDetFiberEquiv_apply_apply b (TangentSpace I)
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
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_symm_apply]
  dsimp only
  rw [FiniteRankBundleCore.ofBundleEquivDualDetFiberEquiv_symm_apply]
  congr 1; funext k
  exact TangentBundle.trivializationAt_symm_apply_self x (b k)

/-- Over the source of any chart at `x₀`, `detCotangentTotalSpaceDiffeomorph` expresses the image
of `p` as its core chart coordinate at `x₀` times the chart coordinate form
`CanonicalBundle.coordForm I x₀ b p.proj`. -/
theorem detCotangentTotalSpaceDiffeomorph_eq_smul_coordForm (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (n : ℕ∞ω) {x₀ : M} (p : (cotangentFiniteRankCore I M b).det.core.TotalSpace)
    (hx : p.proj ∈ (chartAt H x₀).source) :
    (detCotangentTotalSpaceDiffeomorph I M b n p).snd =
      FiniteRankBundleCore.detScalarEquiv (cotangentFiniteRankCore I M b)
          (((cotangentFiniteRankCore I M b).det.core.localTriv x₀ p).2) •
        CanonicalBundle.coordForm I x₀ b p.proj := by
  rw [detCotangentTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_apply]
  refine (CanonicalBundle.eq_smul_coordForm (b := b) hx _).trans ?_
  congr 1
  rw [FiniteRankBundleCore.trivializationAt_ofBundleEquivDualDetFiberEquiv_snd b (TangentSpace I)
    x₀ (by simpa using hx) p.snd, Module.Basis.topFormEquiv_symm_apply, b.det_self, mul_one]

/-- Changing the model basis commutes strictly with the canonical-bundle identification
`detCotangentTotalSpaceDiffeomorph`. -/
theorem detCotangentTotalSpaceDiffeomorph_changeDiffeomorph
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (n : ℕ∞ω)
    (p : (cotangentFiniteRankCore I M b₁).det.core.TotalSpace) :
    detCotangentTotalSpaceDiffeomorph I M b₂ n (detCotangentChangeDiffeomorph I M b₁ b₂ n p) =
      detCotangentTotalSpaceDiffeomorph I M b₁ n p :=
  FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph_changeDiffeomorph b₁ b₂
    (TangentSpace I) p

end Canonical

end TauCeti
