/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.LinearEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Finite-rank cotangent cores, their determinants, and the canonical line bundle

Let `M` be a `C¹` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a finite basis `b : Basis (Fin r) 𝕜 E` of the model space. Using
the model-coordinate core constructor `FiniteRankBundleCore.ofLinearEquiv`, this file presents the
tangent bundle, the cotangent bundle, and (when `r = finrank 𝕜 E`) the canonical bundle inside the
category `FiniteRankBundleCore 𝕜 M`, and relates the finite-rank determinant of the cotangent core
to `TauCeti.CanonicalBundle I M` under explicit coordinate conventions:

1. **Primal and dual model coordinates.** Vectors in `E` are read in `b.equivFunL`. Covectors in
   `E →L[𝕜] 𝕜` are read in `FiniteRankBundleCore.dualCoords b.equivFunL`, which sends `p` to
   `i ↦ p (b i)` (`FiniteRankBundleCore.dualCoords_equivFunL_apply`). Passing between two bases `b₁`
   and `b₂` acts on dual coordinates by a matrix of determinant `b₁.det b₂`
   (`FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans`).
2. **Tangent and cotangent cores.** `TauCeti.tangentCore I b M` and `TauCeti.cotangentCore I b M`
   present `TangentSpace I` and `fun x ↦ TangentSpace I x →L[𝕜] 𝕜` as finite-rank cores of rank `r`.
   On the overlap of the charts at `x₀` and `x₁`, `tangentCore` changes coordinates by
   `tangentCoordChange I x₀ x₁ x` conjugated by `b.equivFunL` (`coordChange_tangentCore`), while
   `cotangentCore` changes coordinates by the transpose of the reverse Jacobian
   `tangentCoordChange I x₁ x₀ x` (`coordChange_cotangentCore`). On a `C^(k+1)` manifold both cores
   and `(cotangentCore I b M).det` are `C^k` cores (`isContMDiff_tangentCore`,
   `isContMDiff_cotangentCore`, `isContMDiff_cotangentCore_det`); on a complex manifold
   (`I = 𝓘(ℂ, E)`, `k = ∞`) these are holomorphic cores. Moreover `(tangentCore I b M).dual` is
   canonically isomorphic to `cotangentCore I b M` (`tangentDualCotangentIso`,
   `tangentDualCotangentDiffeomorph`).
3. **Top-exterior-power convention and comparison with the canonical bundle.** When
   `b : Basis (Fin (finrank 𝕜 E)) 𝕜 E`, the determinant core `(cotangentCore I b M).det` has
   transitions given by scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`
   (`coordChange_cotangentCore_det`), matching the Jacobian-determinant transition law of
   `CanonicalBundle I M`. Evaluating model top-degree forms on `b` yields the core
   `TauCeti.canonicalCore I b M`, canonically isomorphic to `(cotangentCore I b M).det`
   (`cotangentDetCanonicalCoreIso`). Composing with the reconstruction diffeomorphism gives
   `TauCeti.cotangentDetCanonicalDiffeomorph` (and `cotangentDetCanonicalHomeomorph`), which sends
   the unit scalar coordinate in the chart at `x₀` to the coordinate form
   `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b`
   (`cotangentDetCanonicalFiberEquiv_localTriv_symm_one`) and commutes with changes of model basis
   (`cotangentDetCanonicalFiberEquiv_changeBasis`).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1,
  Section 1.
-/

public section

open Bundle CategoryTheory Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Finite-rank tangent and cotangent cores -/

section Cores

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- The finite-rank core presenting `TangentSpace I` on `M` in the coordinates `b.equivFunL` of a
basis `b : Basis (Fin r) 𝕜 E`. -/
noncomputable abbrev tangentCore {r : ℕ} (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv b.equivFunL (TangentSpace I : M → Type _)

/-- The finite-rank core presenting the cotangent bundle `fun x ↦ TangentSpace I x →L[𝕜] 𝕜` on `M`
in the dual coordinates `FiniteRankBundleCore.dualCoords b.equivFunL` (`p ↦ fun i ↦ p (b i)`). -/
noncomputable abbrev cotangentCore {r : ℕ} (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)

section Basic

variable {r : ℕ} {I : ModelWithCorners 𝕜 E H} (b : Basis (Fin r) 𝕜 E)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section ManifoldOne

variable [IsManifold I 1 M]

theorem rank_tangentCore : (tangentCore I b M).rank = r := (rfl)

theorem rank_cotangentCore : (cotangentCore I b M).rank = r := (rfl)

theorem baseSet_tangentCore (x₀ : M) :
    (tangentCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  simp [tangentCore]

theorem baseSet_cotangentCore (x₀ : M) :
    (cotangentCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  simp [cotangentCore]

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `tangentCore I b M` is the
Jacobian `tangentCoordChange I x₀ x₁ x` written in the basis `b`. -/
theorem coordChange_tangentCore {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (tangentCore I b M).core.coordChange x₀ x₁ x =
      b.equivFunL.arrowCongr b.equivFunL (tangentCoordChange I x₀ x₁ x) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₁).baseSet :=
    ⟨by simpa using hx₀, by simpa using hx₁⟩
  exact congrArg (b.equivFunL.arrowCongr b.equivFunL)
    ((tangentBundleCore I M).trivializationAt_coordChangeL hx)

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `cotangentCore I b M` is the
transpose of the reverse Jacobian `tangentCoordChange I x₁ x₀ x` written in the basis `b`. -/
theorem coordChange_cotangentCore {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentCore I b M).core.coordChange x₀ x₁ x =
      (b.equivFunL.arrowCongr b.equivFunL (tangentCoordChange I x₁ x₀ x)).piTranspose := by
  have ht₀ : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx₀
  have ht₁ : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet := by simpa using hx₁
  refine (FiniteRankBundleCore.coordChange_ofLinearEquiv_dualCoords b.equivFunL
    (TangentSpace I : M → Type _) ht₀ ht₁).trans ?_
  rw [FiniteRankBundleCore.coordChange_dual]
  exact congrArg ContinuousLinearMap.piTranspose (coordChange_tangentCore b hx₁ hx₀)

/-- Reconstructed total space of `cotangentCore I b M` identified `C^k`-diffeomorphically with
`CotangentBundle I M`. -/
noncomputable def cotangentCoreTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).core.TotalSpace ≃ₘ^k⟮I.prod 𝓘(𝕜, Fin (cotangentCore I b M).rank → 𝕜),
      I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M :=
  FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) I k

/-- At `x`, the inverse of `cotangentCoreTotalSpaceDiffeomorph` reads a covector `p` by evaluating
it on the basis vectors `b i` (regarded in `TangentSpace I x` via the chart at `x`). -/
@[simp] theorem cotangentCoreTotalSpaceDiffeomorph_symm_apply
    (k : ℕ∞ω) (x : M) (p : TangentSpace I x →L[𝕜] 𝕜) :
    (cotangentCoreTotalSpaceDiffeomorph I b M k).symm ⟨x, p⟩ =
      ⟨x, fun i ↦ p ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i))⟩ := by
  rw [cotangentCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_symm_apply]
  refine congrArg (TotalSpace.mk' _ x) (funext fun i ↦ ?_)
  rw [FiniteRankBundleCore.ofLinearEquivFiberEquiv_symm_apply]
  refine (FiniteRankBundleCore.dualCoords_equivFunL_apply b _ i).trans ?_
  have hself := CotangentBundle.continuousLinearMapAt_trivializationAt_self (I := I) x p
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
    (mem_baseSet_trivializationAt (E →L[𝕜] 𝕜) (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x)] at hself
  rw [Manifold.symmL_trivializationAt_self]
  exact congrArg (· (b i)) hself

/-- `(tangentCore I b M).dual` is canonically isomorphic in `FiniteRankBundleCore 𝕜 M` to
`cotangentCore I b M` by the identity on every coordinate fibre. -/
noncomputable def tangentDualCotangentIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (tangentCore I b M).dual ≅ cotangentCore I b M :=
  FiniteRankBundleCore.ofLinearEquivDualIso b.equivFunL (TangentSpace I : M → Type _)

/-- The `C^k` diffeomorphism of total spaces induced by `tangentDualCotangentIso`. -/
noncomputable def tangentDualCotangentDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (tangentCore I b M).dual.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (tangentCore I b M).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).rank → 𝕜)⟯
        (cotangentCore I b M).core.TotalSpace :=
  FiniteRankBundleCore.ofLinearEquivDualDiffeomorph b.equivFunL (TangentSpace I : M → Type _) I k

end ManifoldOne

/-! ### Smooth and holomorphic core regularity -/

/-- On a `C^(k+1)` manifold, `tangentCore I b M` is a `C^k` core (holomorphic when `I = 𝓘(ℂ, E)` and
`k = ∞`). -/
theorem isContMDiff_tangentCore {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (tangentCore I b M).core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  let : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  infer_instance

/-- On a `C^(k+1)` manifold, `cotangentCore I b M` is a `C^k` core (holomorphic when `I = 𝓘(ℂ, E)`
and `k = ∞`). -/
theorem isContMDiff_cotangentCore {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (cotangentCore I b M).core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  let : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact FiniteRankBundleCore.isContMDiff_ofLinearEquiv
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] Trivial M 𝕜 x)

/-- On a `C^(k+1)` manifold, the determinant line `(cotangentCore I b M).det` is a `C^k` line core
(holomorphic when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
theorem isContMDiff_cotangentCore_det {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (cotangentCore I b M).det.core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  have := isContMDiff_cotangentCore (I := I) (M := M) (k := k) b
  infer_instance

end Basic

/-! ### Comparison of `(cotangentCore I b M).det` with `CanonicalBundle I M` -/

section CanonicalComparison

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Scalar coordinate equivalence on the model fibre `E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜` of
`CanonicalBundle I M` determined by `b`: evaluates a model top-degree form on `b` and views the
resulting scalar in `Fin 1 → 𝕜`. -/
noncomputable def canonicalModelCoords (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) ≃L[𝕜] (Fin 1 → 𝕜) :=
  b.topFormEquiv.trans (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm

@[simp] theorem canonicalModelCoords_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (η : E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (i : Fin 1) :
    canonicalModelCoords b η i = η b :=
  b.topFormEquiv_apply η

@[simp] theorem canonicalModelCoords_symm_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (u : Fin 1 → 𝕜) :
    (canonicalModelCoords b).symm u = u 0 • b.continuousDet :=
  b.topFormEquiv_symm_eq_smul (u 0)

variable [IsManifold I 1 M]

/-- The finite-rank line core presenting `CanonicalBundle I M` in `canonicalModelCoords b`. -/
noncomputable abbrev canonicalCore (I : ModelWithCorners 𝕜 E H)
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv (canonicalModelCoords b) (CanonicalBundle I M)

theorem rank_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (canonicalCore I b M).rank = 1 := (rfl)

theorem baseSet_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    (canonicalCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  simp [canonicalCore]

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `(cotangentCore I b M).det` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`, independent of `b`. -/
theorem coordChange_cotangentCore_det (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentCore I b M).det.core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (cotangentCore I b M).det.rank → 𝕜) := by
  rw [FiniteRankBundleCore.coordChange_det, coordChange_cotangentCore b hx₀ hx₁]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _)
    ((ContinuousLinearMap.det_piTranspose _).trans (b.equivFunL.det_arrowCongr_self _))

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `canonicalCore I b M` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`. -/
theorem coordChange_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (canonicalCore I b M).core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) := by
  rw [FiniteRankBundleCore.coordChange_ofLinearEquiv]
  ext u i
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  have hb₀ : x ∈ (trivializationAt F (CanonicalBundle I M) x₀).baseSet := by simpa [F] using hx₀
  have hb₁ : x ∈ (trivializationAt F (CanonicalBundle I M) x₁).baseSet := by simpa [F] using hx₁
  rw [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.coe_coe,
    canonicalModelCoords_apply, Trivialization.coordChangeL_apply _ _ ⟨hb₀, hb₁⟩,
    CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul hx₀ hx₁ _ b,
    Trivialization.apply_mk_symm _ hb₀, canonicalModelCoords_symm_apply]
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [b.det_self]

/-- Core-level isomorphism in `FiniteRankBundleCore 𝕜 M` between the finite-rank determinant of the
cotangent core `(cotangentCore I b M).det` and `canonicalCore I b M`, preserving scalar
coordinates. -/
noncomputable def cotangentDetCanonicalCoreIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det ≅ canonicalCore I b M :=
  FiniteRankBundleCore.constIso
    (fun x₀ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore, baseSet_canonicalCore])
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm)
    fun x₀ x₁ x hx₀ hx₁ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀ hx₁
      ext u : 1
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        coordChange_cotangentCore_det b hx₀ hx₁, coordChange_canonicalCore b hx₀ hx₁]
      simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul]
      rfl

/-- Fibrewise continuous linear equivalence identifying `(cotangentCore I b M).det.core.Fiber x`
with `CanonicalBundle I M x` by multiplying `CanonicalBundle.coordForm I x b x` by the scalar
coordinate `detScalarEquiv (cotangentCore I b M)`. -/
noncomputable def cotangentDetCanonicalFiberEquiv
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (x : M) :
    (cotangentCore I b M).det.core.Fiber x ≃L[𝕜] CanonicalBundle I M x :=
  ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm).trans
    (VectorBundle.continuousLinearEquivAt 𝕜 (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
      (CanonicalBundle I M) x).symm

@[simp] theorem cotangentDetCanonicalFiberEquiv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b M x u =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u •
        CanonicalBundle.coordForm I x b x := by
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  have hx : x ∈ (trivializationAt F (CanonicalBundle I M) x).baseSet :=
    mem_baseSet_trivializationAt F (CanonicalBundle I M) x
  have h : cotangentDetCanonicalFiberEquiv I b M x u =
      (trivializationAt F (CanonicalBundle I M) x).symm x
        (b.topFormEquiv.symm (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u)) := rfl
  rw [h, ← (trivializationAt F (CanonicalBundle I M) x).symmL_apply (R := 𝕜) hx,
    b.topFormEquiv_symm_eq_smul, map_smul, Trivialization.symmL_apply _ hx,
    ← CanonicalBundle.trivializationAt_apply_snd_coordForm (I := I) (b := b)
      (mem_chart_source H x),
    Trivialization.symm_apply_apply_mk _ hx]

@[simp] theorem cotangentDetCanonicalFiberEquiv_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (η : CanonicalBundle I M x) :
    (cotangentDetCanonicalFiberEquiv I b M x).symm η =
      (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm
        (η fun i ↦ (trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)) := by
  apply (cotangentDetCanonicalFiberEquiv I b M x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, cotangentDetCanonicalFiberEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  have htriv : (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x
      ⟨x, η⟩).2 b = η fun i ↦ (trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i) := by
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd]
    rfl
  rw [← htriv]
  exact CanonicalBundle.eq_smul_coordForm (b := b) (mem_chart_source H x) η

/-- `C^k` diffeomorphism of total spaces induced by `cotangentDetCanonicalCoreIso I b M`. -/
noncomputable def cotangentDetCanonicalCoreDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (canonicalCore I b M).rank → 𝕜)⟯ (canonicalCore I b M).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (cotangentDetCanonicalCoreIso I b M).hom (cotangentDetCanonicalCoreIso I b M).inv
    (cotangentDetCanonicalCoreIso I b M).hom_inv_id
    (cotangentDetCanonicalCoreIso I b M).inv_hom_id
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_of_mem_baseSet _
      ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
        (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm).toContinuousLinearMap
      fun x x₀ hx₀ v ↦ by
        rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀
        rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_hom,
          coordChange_canonicalCore b (mem_chart_source H x) hx₀,
          coordChange_cotangentCore_det b (mem_chart_source H x) hx₀]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact (((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
          (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm).map_smul _ v).symm)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_of_mem_baseSet _
      ((ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).trans
        (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm).toContinuousLinearMap
      fun x x₀ hx₀ v ↦ by
        rw [baseSet_canonicalCore] at hx₀
        rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_inv,
          coordChange_cotangentCore_det b (mem_chart_source H x) hx₀,
          coordChange_canonicalCore b (mem_chart_source H x) hx₀]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact (((ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).trans
          (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm).map_smul _ v).symm)

/-- The reconstructed total space of `(cotangentCore I b M).det` is `C^k` diffeomorphic over `M` to
the total space of `CanonicalBundle I M` at every regularity `k` (and in particular biholomorphic on
a complex manifold when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
noncomputable def cotangentDetCanonicalDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalCoreDiffeomorph I b M k).trans
    (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph (canonicalModelCoords b)
      (CanonicalBundle I M) I k)

/-- Topological bundle equivalence underlying `cotangentDetCanonicalDiffeomorph`. -/
noncomputable def cotangentDetCanonicalHomeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det.core.TotalSpace ≃ₜ
      TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalDiffeomorph I b M 0).toHomeomorph

@[simp] theorem cotangentDetCanonicalDiffeomorph_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : (cotangentCore I b M).det.core.TotalSpace) :
    cotangentDetCanonicalDiffeomorph I b M k p =
      ⟨p.proj, cotangentDetCanonicalFiberEquiv I b M p.proj p.2⟩ := by
  rcases p with ⟨x, u⟩
  rw [cotangentDetCanonicalDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    cotangentDetCanonicalCoreDiffeomorph, CoordinateHom.coe_toDiffeomorphOfInv,
    CoordinateHom.totalSpaceMap_mk, cotangentDetCanonicalCoreIso,
    FiniteRankBundleCore.fiberMap_constIso_hom,
    FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_apply]
  dsimp only
  refine congrArg (TotalSpace.mk' _ x) ?_
  refine (FiniteRankBundleCore.ofLinearEquivFiberEquiv_apply
    (canonicalModelCoords b) (CanonicalBundle I M) x _).trans ?_
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  refine (congrArg ((trivializationAt F (CanonicalBundle I M) x).symm x)
    (canonicalModelCoords_symm_apply b _)).trans ?_
  exact congrArg ((trivializationAt F (CanonicalBundle I M) x).symm x)
    (b.topFormEquiv_symm_eq_smul
      (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u)).symm

@[simp] theorem cotangentDetCanonicalDiffeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (cotangentDetCanonicalDiffeomorph I b M k).symm p =
      ⟨p.proj, (cotangentDetCanonicalFiberEquiv I b M p.proj).symm p.2⟩ := by
  apply EquivLike.injective (cotangentDetCanonicalDiffeomorph I b M k)
  rw [Diffeomorph.apply_symm_apply, cotangentDetCanonicalDiffeomorph_apply,
    ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem cotangentDetCanonicalDiffeomorph_toHomeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    (cotangentDetCanonicalDiffeomorph I b M k).toHomeomorph =
      cotangentDetCanonicalHomeomorph I b M := by
  apply Homeomorph.ext
  intro p
  exact (cotangentDetCanonicalDiffeomorph_apply b k p).trans
    (cotangentDetCanonicalDiffeomorph_apply b 0 p).symm

/-- Over the domain of the chart at `x₀`, the unit scalar coordinate `1` in the `x₀`-trivialization
of `(cotangentCore I b M).det` corresponds under `cotangentDetCanonicalFiberEquiv` to the local
coordinate top-form `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b x`. -/
theorem cotangentDetCanonicalFiberEquiv_localTriv_symm_one
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x : M} (hx₀ : x ∈ (chartAt H x₀).source) :
    cotangentDetCanonicalFiberEquiv I b M x
        (((cotangentCore I b M).det.core.localTriv x₀).symm x
          ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)) =
      CanonicalBundle.coordForm I x₀ b x := by
  have hb₀ : x ∈ ((cotangentCore I b M).det.core.localTriv x₀).baseSet := by
    rwa [FiniteRankBundleCore.localTriv_baseSet_det, baseSet_cotangentCore]
  have hsymm := ((cotangentCore I b M).det.core).localTriv_symm_apply (i := x₀) hb₀
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)
  rw [hsymm, (cotangentCore I b M).det.indexAt_eq, cotangentDetCanonicalFiberEquiv_apply,
    coordChange_cotangentCore_det b hx₀ (mem_chart_source H x)]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (CanonicalBundle.coordForm_eq_det_smul_coordForm hx₀ (mem_chart_source H x)).symm

/-! ### Dual-tangent determinant and change-of-basis compatibility -/

/-- Determinant isomorphism `(tangentCore I b M).dual.det ≅ (cotangentCore I b M).det` induced by
`tangentDualCotangentIso I b M`. -/
noncomputable def tangentDualDetCotangentDetIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (tangentCore I b M).dual.det ≅ (cotangentCore I b M).det :=
  FiniteRankBundleCore.detIso (finrank 𝕜 E) (tangentDualCotangentIso I b M)
    ((FiniteRankBundleCore.rank_dual _).trans (FiniteRankBundleCore.rank_ofLinearEquiv _ _))
    (FiniteRankBundleCore.rank_ofLinearEquiv _ _)

theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_hom
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (tangentCore I b M).dual.det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)
        ((tangentDualDetCotangentDetIso I b M).hom.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual u := by
  rw [tangentDualDetCotangentDetIso, FiniteRankBundleCore.detIso_hom,
    FiniteRankBundleCore.detMap_def,
    FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    FiniteRankBundleCore.detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    FiniteRankBundleCore.fiberMap_exteriorPower_map, tangentDualCotangentIso,
    FiniteRankBundleCore.fiberMap_ofLinearEquivDualIso_hom]
  refine (FiniteRankBundleCore.topExteriorScalarEquiv_exteriorPowerCoords_self
    (ContinuousLinearMap.id 𝕜 (Fin (finrank 𝕜 E) → 𝕜)) _).trans ?_
  rw [ContinuousLinearMap.det_id, one_mul]
  exact FiniteRankBundleCore.topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom
    (tangentCore I b M).dual _ x u

/-- Determinant isomorphism `(cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det` induced by
changing the model basis from `b₁` to `b₂`. -/
noncomputable def cotangentDetChangeBasisIso
    (I : ModelWithCorners 𝕜 E H) (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det :=
  FiniteRankBundleCore.detIso (finrank 𝕜 E)
    (FiniteRankBundleCore.ofLinearEquivChangeIso
      (FiniteRankBundleCore.dualCoords b₁.equivFunL)
      (FiniteRankBundleCore.dualCoords b₂.equivFunL)
      (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))
    (FiniteRankBundleCore.rank_ofLinearEquiv _ _)
    (FiniteRankBundleCore.rank_ofLinearEquiv _ _)

/-- Changing the model basis from `b₁` to `b₂` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₁.det b₂`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M) u := by
  refine (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso
    (FiniteRankBundleCore.dualCoords b₁.equivFunL)
    (FiniteRankBundleCore.dualCoords b₂.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans ?_
  exact congrArg (· * _) (FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans b₁ b₂)

/-- The canonical identification `cotangentDetCanonicalFiberEquiv` commutes with changes of model
basis: the scaling `b₁.det b₂` of cotangent determinant coordinates cancels the inverse scaling of
`CanonicalBundle.coordForm`. -/
theorem cotangentDetCanonicalFiberEquiv_changeBasis
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b₂ M x
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      cotangentDetCanonicalFiberEquiv I b₁ M x u := by
  rw [cotangentDetCanonicalFiberEquiv_apply, cotangentDetCanonicalFiberEquiv_apply,
    detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom,
    CanonicalBundle.coordForm_basis_change x b₁ b₂ x, smul_smul, mul_comm]

end CanonicalComparison

end Cores

end TauCeti
