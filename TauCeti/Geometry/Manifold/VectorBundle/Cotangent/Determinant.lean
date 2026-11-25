/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.FiniteRank
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant of the cotangent core and comparison with the canonical line bundle

Develops the determinant line `(cotangentCore I b M).det` for a basis `b : Basis (Fin r) 𝕜 E` on a
`C¹` manifold `M` modelled on `I : ModelWithCorners 𝕜 E H` over a complete field `𝕜`, and
identifies it smoothly (and biholomorphically on complex manifolds) with `CanonicalBundle I M`:

1. **Rank-generic cotangent determinant:** `coordChange_cotangentCore_det`,
   `isContMDiff_cotangentCore_det`, `tangentDualDetCotangentDetIso`, and
   `cotangentDetChangeBasisIso` (scaling coordinates by `b₁.det b₂`).
2. **Comparison with `CanonicalBundle I M`:** for `b : Basis (Fin (finrank 𝕜 E)) 𝕜 E`,
   `canonicalCore`, `canonicalCoreTotalSpaceDiffeomorph`, `cotangentDetCanonicalCoreIso`,
   `cotangentDetCanonicalCoreDiffeomorph`, `cotangentDetCanonicalFiberEquiv`,
   `cotangentDetCanonicalDiffeomorph`, `cotangentDetCanonicalHomeomorph`,
   `cotangentDetCanonicalFiberEquiv_localTriv_symm_one`, and
   `cotangentDetCanonicalFiberEquiv_changeBasis`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1, Section 1.
-/

public section

open Bundle CategoryTheory Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-! ### Rank-generic determinant of the cotangent core -/

section CotangentDeterminant

variable {r : ℕ} {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On a `C^(k+1)` manifold, `(cotangentCore I b M).det` is a `C^k` line core (holomorphic when
`I = 𝓘(ℂ, E)` and `k = ∞`). -/
theorem isContMDiff_cotangentCore_det (b : Basis (Fin r) 𝕜 E) {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (cotangentCore I b M).det.core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  have := isContMDiff_cotangentCore (I := I) (M := M) (k := k) b
  infer_instance

variable [IsManifold I 1 M]

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `(cotangentCore I b M).det` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`, independent of `b`. -/
theorem coordChange_cotangentCore_det (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentCore I b M).det.core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (cotangentCore I b M).det.rank → 𝕜) := by
  rw [FiniteRankBundleCore.coordChange_det, coordChange_cotangentCore b hx₀ hx₁]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _)
    ((ContinuousLinearMap.det_piTranspose _).trans (b.equivFunL.det_arrowCongr_self _))

/-- Determinant isomorphism `(tangentCore I b M).dual.det ≅ (cotangentCore I b M).det` induced by
`tangentDualCotangentIso I b M`. -/
noncomputable def tangentDualDetCotangentDetIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (tangentCore I b M).dual.det ≅ (cotangentCore I b M).det :=
  FiniteRankBundleCore.detIso r (tangentDualCotangentIso I b M)
    ((FiniteRankBundleCore.rank_dual _).trans (rank_tangentCore b))
    (rank_cotangentCore b)

/-- The forward map of `tangentDualDetCotangentDetIso` preserves determinant scalar coordinates. -/
theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_hom
    (b : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (tangentCore I b M).dual.det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)
        ((tangentDualDetCotangentDetIso I b M).hom.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual u := by
  rw [tangentDualDetCotangentDetIso, FiniteRankBundleCore.detIso_hom,
    FiniteRankBundleCore.detScalarEquiv_fiberMap_detMap]
  have hid : FiniteRankBundleCore.normalizedFiberMap (tangentDualCotangentIso I b M).hom
      ((FiniteRankBundleCore.rank_dual _).trans (rank_tangentCore b))
      (rank_cotangentCore b) x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
    FiniteRankBundleCore.normalizedFiberMap_eq_of_heq _ _ _ x _
      (heq_of_eq (fiberMap_tangentDualCotangentIso_hom b x))
  rw [hid, ContinuousLinearMap.det_id, one_mul]

/-- The inverse map of `tangentDualDetCotangentDetIso` preserves determinant scalar coordinates. -/
theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_inv
    (b : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual
        ((tangentDualDetCotangentDetIso I b M).inv.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [← detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_hom b x
      ((tangentDualDetCotangentDetIso I b M).inv.fiberMap x u),
    ← ContinuousLinearMap.comp_apply, ← FiniteRankBundleCore.fiberMap_comp,
    Iso.inv_hom_id, FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.id_apply]

/-- Determinant isomorphism `(cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det` induced by
changing the model basis from `b₁` to `b₂`. -/
noncomputable def cotangentDetChangeBasisIso
    (I : ModelWithCorners 𝕜 E H) (b₁ b₂ : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det :=
  FiniteRankBundleCore.detIso r
    (FiniteRankBundleCore.ofLinearEquivChangeIso
      b₁.equivFunL.dualCoords b₂.equivFunL.dualCoords
      (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))
    (rank_cotangentCore b₁) (rank_cotangentCore b₂)

/-- Changing from a model basis to itself is the identity isomorphism on
`(cotangentCore I b M).det`. -/
@[simp] theorem cotangentDetChangeBasisIso_self (b : Basis (Fin r) 𝕜 E) :
    cotangentDetChangeBasisIso I b b M = Iso.refl (cotangentCore I b M).det :=
  (congrArg (fun e : cotangentCore I b M ≅ cotangentCore I b M ↦
      FiniteRankBundleCore.detIso r e (rank_cotangentCore b) (rank_cotangentCore b))
    (FiniteRankBundleCore.ofLinearEquivChangeIso_self
      b.equivFunL.dualCoords _)).trans
    (FiniteRankBundleCore.detIso_refl r (cotangentCore I b M) (rank_cotangentCore b))

/-- Inverting a change-of-basis isomorphism on `(cotangentCore I · M).det` reverses the two
bases. -/
@[simp] theorem cotangentDetChangeBasisIso_symm (b₁ b₂ : Basis (Fin r) 𝕜 E) :
    (cotangentDetChangeBasisIso I b₁ b₂ M).symm = cotangentDetChangeBasisIso I b₂ b₁ M :=
  (FiniteRankBundleCore.detIso_symm r _ (rank_cotangentCore b₁) (rank_cotangentCore b₂)).trans
    (congrArg (fun e : cotangentCore I b₂ M ≅ cotangentCore I b₁ M ↦
        FiniteRankBundleCore.detIso r e (rank_cotangentCore b₂) (rank_cotangentCore b₁))
      (FiniteRankBundleCore.ofLinearEquivChangeIso_symm
        b₁.equivFunL.dualCoords b₂.equivFunL.dualCoords _))

/-- Composing two change-of-basis isomorphisms on `(cotangentCore I · M).det` yields the direct
change-of-basis isomorphism. -/
@[simp] theorem cotangentDetChangeBasisIso_trans (b₁ b₂ b₃ : Basis (Fin r) 𝕜 E) :
    (cotangentDetChangeBasisIso I b₁ b₂ M).trans (cotangentDetChangeBasisIso I b₂ b₃ M) =
      cotangentDetChangeBasisIso I b₁ b₃ M :=
  (FiniteRankBundleCore.detIso_trans r _ _
      (rank_cotangentCore b₁) (rank_cotangentCore b₂) (rank_cotangentCore b₃)).trans
    (congrArg (fun e : cotangentCore I b₁ M ≅ cotangentCore I b₃ M ↦
        FiniteRankBundleCore.detIso r e (rank_cotangentCore b₁) (rank_cotangentCore b₃))
      (FiniteRankBundleCore.ofLinearEquivChangeIso_trans
        b₁.equivFunL.dualCoords b₂.equivFunL.dualCoords b₃.equivFunL.dualCoords _))

/-- Composing the forward maps of successive change-of-basis isomorphisms yields the direct
change-of-basis morphism. -/
@[simp] theorem cotangentDetChangeBasisIso_hom_comp (b₁ b₂ b₃ : Basis (Fin r) 𝕜 E) :
    (cotangentDetChangeBasisIso I b₁ b₂ M).hom ≫
        (cotangentDetChangeBasisIso I b₂ b₃ M).hom =
      (cotangentDetChangeBasisIso I b₁ b₃ M).hom :=
  congrArg Iso.hom (cotangentDetChangeBasisIso_trans b₁ b₂ b₃)

/-- Composing the inverse maps of successive change-of-basis isomorphisms yields the direct
inverse change-of-basis morphism. -/
@[simp] theorem cotangentDetChangeBasisIso_inv_comp (b₁ b₂ b₃ : Basis (Fin r) 𝕜 E) :
    (cotangentDetChangeBasisIso I b₂ b₃ M).inv ≫
        (cotangentDetChangeBasisIso I b₁ b₂ M).inv =
      (cotangentDetChangeBasisIso I b₁ b₃ M).inv := by
  simpa only [← Iso.symm_hom, cotangentDetChangeBasisIso_symm] using
    cotangentDetChangeBasisIso_hom_comp b₃ b₂ b₁

/-- Changing the model basis from `b₁` to `b₂` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₁.det b₂`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M) u :=
  (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_hom
    b₁.equivFunL.dualCoords b₂.equivFunL.dualCoords
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans
    (congrArg (· * _) (b₁.det_dualCoords_equivFunL_symm_trans b₂))

/-- The inverse change-of-basis map from `b₂` to `b₁` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₂.det b₁`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_inv
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₂ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).inv.fiberMap x u) =
      b₂.det b₁ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M) u :=
  (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_inv
    b₁.equivFunL.dualCoords b₂.equivFunL.dualCoords
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans
    (congrArg (· * _) (b₂.det_dualCoords_equivFunL_symm_trans b₁))

end CotangentDeterminant

/-! ### Comparison of `(cotangentCore I b M).det` with `CanonicalBundle I M` -/

section CanonicalComparison

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Scalar coordinate equivalence on the model fibre `E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜` of
`CanonicalBundle I M`, evaluating a model top-degree form on `b` in `Fin 1 → 𝕜`. -/
noncomputable def canonicalModelCoords (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) ≃L[𝕜] (Fin 1 → 𝕜) :=
  b.topFormEquiv.trans (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm

/-- `canonicalModelCoords b` evaluates a model top-degree alternating form on the basis `b`. -/
@[simp] theorem canonicalModelCoords_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (η : E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (i : Fin 1) :
    canonicalModelCoords b η i = η b :=
  b.topFormEquiv_apply η

/-- The inverse of `canonicalModelCoords b` scales `b.continuousDet` by the unique coordinate. -/
@[simp] theorem canonicalModelCoords_symm_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (u : Fin 1 → 𝕜) :
    (canonicalModelCoords b).symm u = u 0 • b.continuousDet :=
  b.topFormEquiv_symm_eq_smul (u 0)

variable [IsManifold I 1 M]

/-- The finite-rank line core presenting `CanonicalBundle I M` in `canonicalModelCoords b`. -/
noncomputable def canonicalCore (I : ModelWithCorners 𝕜 E H)
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv (canonicalModelCoords b) (CanonicalBundle I M)

/-- The canonical line core has rank one. -/
@[simp] theorem rank_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (canonicalCore I b M).rank = 1 := (rfl)

/-- The chart domain of `canonicalCore I b M` at `x₀` is `(chartAt H x₀).source`. -/
theorem baseSet_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    (canonicalCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  rw [canonicalCore, FiniteRankBundleCore.baseSet_ofLinearEquiv]
  simp

/-- The base set of the local trivialization of `canonicalCore I b M` at `x₀` is the chart
source. -/
@[simp] theorem localTriv_baseSet_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    ((canonicalCore I b M).core.localTriv x₀).baseSet = (chartAt H x₀).source :=
  baseSet_canonicalCore b x₀

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `canonicalCore I b M` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`. -/
theorem coordChange_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (canonicalCore I b M).core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (canonicalCore I b M).rank → 𝕜) := by
  refine (FiniteRankBundleCore.coordChange_ofLinearEquiv (canonicalModelCoords b)
    (CanonicalBundle I M) x₀ x₁ x).trans ?_
  ext (u : Fin 1 → 𝕜) (i : Fin 1)
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  have hb₀ : x ∈ (trivializationAt F (CanonicalBundle I M) x₀).baseSet := by simpa [F] using hx₀
  rw [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.coe_coe,
    canonicalModelCoords_apply, Trivialization.coordChangeL_apply _ _ ⟨hb₀, by simpa [F] using hx₁⟩,
    CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul hx₀ hx₁ _ b,
    Trivialization.apply_mk_symm _ hb₀, canonicalModelCoords_symm_apply]
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, b.continuousDet_apply, b.det_self,
    mul_one]
  -- `(canonicalCore I b M).rank` is definitionally `1`, so scalar multiplication on `Fin _ → 𝕜`
  -- agrees definitionally.
  rfl

private theorem baseSet_cotangentCore_det_eq_canonicalCore
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    (cotangentCore I b M).det.core.baseSet x₀ = (canonicalCore I b M).core.baseSet x₀ := by
  rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore, baseSet_canonicalCore]

/-- Scalar-coordinate equivalence from `(cotangentCore I b M).det` to `canonicalCore I b M`,
reading both rank-one cores at index `0`. -/
private noncomputable def cotangentDetCanonicalCoords
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (Fin (cotangentCore I b M).det.rank → 𝕜) ≃L[𝕜]
      (Fin (canonicalCore I b M).rank → 𝕜) :=
  (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm

@[simp] private theorem cotangentDetCanonicalCoords_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) (i : Fin (canonicalCore I b M).rank) :
    cotangentDetCanonicalCoords (I := I) (M := M) b u i =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := rfl

private theorem coordChange_comp_cotangentDetCanonicalCore
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (cotangentCore I b M).det.core.baseSet x₀)
    (hx₁ : x ∈ (cotangentCore I b M).det.core.baseSet x₁) :
    ((cotangentDetCanonicalCoords (I := I) (M := M) b).toContinuousLinearMap.comp
        ((cotangentCore I b M).det.core.coordChange x₀ x₁ x)) =
      ((canonicalCore I b M).core.coordChange x₀ x₁ x).comp
        (cotangentDetCanonicalCoords (I := I) (M := M) b).toContinuousLinearMap := by
  rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀ hx₁
  let e := cotangentDetCanonicalCoords (I := I) (M := M) b
  ext u : 1
  refine (congrArg e (DFunLike.congr_fun (coordChange_cotangentCore_det b hx₀ hx₁) u)).trans ?_
  refine (e.map_smul _ u).trans ?_
  exact (DFunLike.congr_fun (coordChange_canonicalCore b hx₀ hx₁) (e u)).symm

omit [IsManifold I 1 M] in
/-- On a `C^(k+1)` manifold, `canonicalCore I b M` is a `C^k` line core (holomorphic when
`I = 𝓘(ℂ, E)` and `k = ∞`). -/
theorem isContMDiff_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {k : ℕ∞ω}
    [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (canonicalCore I b M).core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  have := isContMDiff_cotangentCore_det (I := I) (M := M) (k := k) b
  exact FiniteRankBundleCore.isContMDiff_of_constIntertwine
    (baseSet_cotangentCore_det_eq_canonicalCore b)
    (cotangentDetCanonicalCoords (I := I) (M := M) b)
    (fun _ _ _ hx₀ hx₁ ↦ coordChange_comp_cotangentDetCanonicalCore b hx₀ hx₁)

/-- Reconstructed total space of `canonicalCore I b M` identified `C^k`-diffeomorphically with
`CanonicalBundle I M`. -/
noncomputable def canonicalCoreTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (canonicalCore I b M).core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (canonicalCore I b M).rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph
    (canonicalModelCoords b) (CanonicalBundle I M) I k

/-- At `p.proj`, `canonicalCoreTotalSpaceDiffeomorph` scales `CanonicalBundle.coordForm I p.proj b
p.proj` by the unique coordinate of `p.snd`. -/
@[simp] theorem canonicalCoreTotalSpaceDiffeomorph_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : (canonicalCore I b M).core.TotalSpace) :
    canonicalCoreTotalSpaceDiffeomorph I b M k p =
      ⟨p.proj, p.snd ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩ •
        CanonicalBundle.coordForm I p.proj b p.proj⟩ := by
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  refine (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_apply
    (canonicalModelCoords b) (CanonicalBundle I M) (I := I) (n := k) p).trans ?_
  refine congrArg (TotalSpace.mk' F p.proj) ?_
  refine (FiniteRankBundleCore.ofLinearEquivFiberEquiv_apply
    (canonicalModelCoords b) (CanonicalBundle I M) p.proj p.snd).trans ?_
  refine (congrArg (VectorBundle.continuousLinearEquivAt 𝕜 F (CanonicalBundle I M) p.proj).symm
    (canonicalModelCoords_symm_apply b p.snd)).trans ?_
  rw [map_smul, CanonicalBundle.continuousLinearEquivAt_symm_continuousDet]
  exact congrArg (· • CanonicalBundle.coordForm I p.proj b p.proj)
    (congrArg p.snd (Subsingleton.elim (0 : Fin 1)
      ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩))

/-- At `p.proj`, the inverse of `canonicalCoreTotalSpaceDiffeomorph` evaluates `p.snd` on the
chart basis vectors `(trivializationAt E (TangentSpace I) p.proj).symmL 𝕜 p.proj (b i)`. -/
@[simp] theorem canonicalCoreTotalSpaceDiffeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (canonicalCoreTotalSpaceDiffeomorph I b M k).symm p =
      ⟨p.proj, fun _ ↦ p.snd fun i ↦
        (trivializationAt E (TangentSpace I) p.proj).symmL 𝕜 p.proj (b i)⟩ := by
  rcases p with ⟨x, η⟩
  refine (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_symm_apply
    (canonicalModelCoords b) (CanonicalBundle I M) (I := I) (n := k) ⟨x, η⟩).trans ?_
  refine congrArg (TotalSpace.mk' _ x) ?_
  refine (FiniteRankBundleCore.ofLinearEquivFiberEquiv_symm_apply
    (canonicalModelCoords b) (CanonicalBundle I M) x η).trans ?_
  refine funext fun i ↦ ?_
  exact (canonicalModelCoords_apply b _ i).trans
    (CanonicalBundle.trivializationAt_apply_snd_basis x η b)

/-- Core-level isomorphism in `FiniteRankBundleCore 𝕜 M` between `(cotangentCore I b M).det` and
`canonicalCore I b M`, preserving scalar coordinates. -/
noncomputable def cotangentDetCanonicalCoreIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det ≅ canonicalCore I b M :=
  FiniteRankBundleCore.constIso
    (fun i ↦ (baseSet_cotangentCore_det_eq_canonicalCore b i).le)
    (cotangentDetCanonicalCoords (I := I) (M := M) b)
    fun _ _ _ hx₀ hx₁ ↦ coordChange_comp_cotangentDetCanonicalCore b hx₀ hx₁

/-- `C^k` diffeomorphism of total spaces upgrading `cotangentDetCanonicalCoreIso I b M` at every
regularity `k`, without smoothness assumptions beyond `[IsManifold I 1 M]`. -/
noncomputable def cotangentDetCanonicalCoreDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (canonicalCore I b M).rank → 𝕜)⟯ (canonicalCore I b M).core.TotalSpace :=
  FiniteRankBundleCore.isoToDiffeomorph (cotangentDetCanonicalCoreIso I b M)
    (by
      rw [cotangentDetCanonicalCoreIso]
      exact FiniteRankBundleCore.contMDiff_totalSpaceMap_constIso_hom _ _ _)
    (by
      rw [cotangentDetCanonicalCoreIso]
      exact FiniteRankBundleCore.contMDiff_totalSpaceMap_constIso_inv
        (baseSet_cotangentCore_det_eq_canonicalCore b) _ _)

@[simp] theorem coe_cotangentDetCanonicalCoreDiffeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    ⇑(cotangentDetCanonicalCoreDiffeomorph I b M k) =
      (cotangentDetCanonicalCoreIso I b M).hom.totalSpaceMap :=
  FiniteRankBundleCore.coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_cotangentDetCanonicalCoreDiffeomorph_symm
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    ⇑(cotangentDetCanonicalCoreDiffeomorph I b M k).symm =
      (cotangentDetCanonicalCoreIso I b M).inv.totalSpaceMap :=
  FiniteRankBundleCore.coe_isoToDiffeomorph_symm _ _ _

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u` is
`detScalarEquiv (cotangentCore I b M) u`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_hom_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) (i : Fin (canonicalCore I b M).rank) :
    (cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u i =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_hom,
    ContinuousLinearEquiv.coe_coe]
  exact cotangentDetCanonicalCoords_apply b u i

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w` is the unique
coordinate entry of `w` in `canonicalCore I b M`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_inv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (w : Fin (canonicalCore I b M).rank → 𝕜) (i : Fin (cotangentCore I b M).det.rank) :
    (cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w i =
      w ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩ := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_inv,
    ContinuousLinearEquiv.coe_coe]
  have hi : i = ⟨0, (cotangentCore I b M).rank_det ▸ Nat.zero_lt_one⟩ :=
    Fin.ext (Nat.lt_one_iff.mp (i.isLt.trans_eq (cotangentCore I b M).rank_det))
  rw [hi, ← FiniteRankBundleCore.detScalarEquiv_apply (cotangentCore I b M)
      ((cotangentDetCanonicalCoords (I := I) (M := M) b).symm w),
    ← cotangentDetCanonicalCoords_apply (I := I) (M := M) b _
      ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Fibrewise continuous linear equivalence identifying `(cotangentCore I b M).det.core.Fiber x`
with `CanonicalBundle I M x` via `detScalarEquiv` and `CanonicalBundle.coordForm`. -/
noncomputable def cotangentDetCanonicalFiberEquiv
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (x : M) :
    (cotangentCore I b M).det.core.Fiber x ≃L[𝕜] CanonicalBundle I M x :=
  ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm).trans
    (VectorBundle.continuousLinearEquivAt 𝕜 (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
      (CanonicalBundle I M) x).symm

/-- `cotangentDetCanonicalFiberEquiv` sends `u` to the corresponding scalar multiple of
`CanonicalBundle.coordForm I x b x`. -/
@[simp] theorem cotangentDetCanonicalFiberEquiv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b M x u =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u •
        CanonicalBundle.coordForm I x b x := by
  refine (ContinuousLinearEquiv.trans_apply
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm)
    (VectorBundle.continuousLinearEquivAt 𝕜 (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
      (CanonicalBundle I M) x).symm u).trans ?_
  rw [ContinuousLinearEquiv.trans_apply, b.topFormEquiv_symm_eq_smul, map_smul,
    CanonicalBundle.continuousLinearEquivAt_symm_continuousDet]

/-- The inverse of `cotangentDetCanonicalFiberEquiv` evaluates `η` on the coordinate basis vectors
`(trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)`. -/
@[simp] theorem cotangentDetCanonicalFiberEquiv_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (η : CanonicalBundle I M x) :
    (cotangentDetCanonicalFiberEquiv I b M x).symm η =
      (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm
        (η fun i ↦ (trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)) := by
  apply (cotangentDetCanonicalFiberEquiv I b M x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, cotangentDetCanonicalFiberEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply, ← CanonicalBundle.trivializationAt_apply_snd_basis]
  exact CanonicalBundle.eq_smul_coordForm (b := b) (mem_chart_source H x) η

/-- The reconstructed total space of `(cotangentCore I b M).det` is `C^k` diffeomorphic over `M` to
`CanonicalBundle I M` at every regularity `k` (biholomorphic when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
noncomputable def cotangentDetCanonicalDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalCoreDiffeomorph I b M k).trans
    (canonicalCoreTotalSpaceDiffeomorph I b M k)

/-- Topological bundle equivalence underlying `cotangentDetCanonicalDiffeomorph`. -/
noncomputable def cotangentDetCanonicalHomeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det.core.TotalSpace ≃ₜ
      TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalDiffeomorph I b M 0).toHomeomorph

/-- On total spaces, `cotangentDetCanonicalDiffeomorph` acts fibrewise by
`cotangentDetCanonicalFiberEquiv`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : (cotangentCore I b M).det.core.TotalSpace) :
    cotangentDetCanonicalDiffeomorph I b M k p =
      ⟨p.proj, cotangentDetCanonicalFiberEquiv I b M p.proj p.snd⟩ := by
  rcases p with ⟨x, u⟩
  rw [cotangentDetCanonicalDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    coe_cotangentDetCanonicalCoreDiffeomorph, CoordinateHom.totalSpaceMap_mk,
    canonicalCoreTotalSpaceDiffeomorph_apply]
  refine (congrArg
    (fun c ↦ TotalSpace.mk' _ x (c • CanonicalBundle.coordForm I x b x))
    (fiberMap_cotangentDetCanonicalCoreIso_hom_apply b x u _)).trans ?_
  exact congrArg (TotalSpace.mk' _ x)
    (cotangentDetCanonicalFiberEquiv_apply b x u).symm

/-- On total spaces, the inverse of `cotangentDetCanonicalDiffeomorph` acts fibrewise by
`(cotangentDetCanonicalFiberEquiv I b M p.proj).symm`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (cotangentDetCanonicalDiffeomorph I b M k).symm p =
      ⟨p.proj, (cotangentDetCanonicalFiberEquiv I b M p.proj).symm p.snd⟩ := by
  rw [cotangentDetCanonicalDiffeomorph, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Function.comp_apply, coe_cotangentDetCanonicalCoreDiffeomorph_symm,
    CoordinateHom.totalSpaceMap_def, canonicalCoreTotalSpaceDiffeomorph_symm_apply,
    cotangentDetCanonicalFiberEquiv_symm_apply]
  refine congrArg (TotalSpace.mk' _ p.proj) (funext fun i ↦ ?_)
  exact (fiberMap_cotangentDetCanonicalCoreIso_inv_apply b p.proj _ i).trans
    (FiniteRankBundleCore.detScalarEquiv_symm_apply (cotangentCore I b M) _ i).symm

/-- On total spaces, `cotangentDetCanonicalHomeomorph` acts fibrewise by
`cotangentDetCanonicalFiberEquiv`. -/
@[simp] theorem cotangentDetCanonicalHomeomorph_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (p : (cotangentCore I b M).det.core.TotalSpace) :
    cotangentDetCanonicalHomeomorph I b M p =
      ⟨p.proj, cotangentDetCanonicalFiberEquiv I b M p.proj p.snd⟩ :=
  cotangentDetCanonicalDiffeomorph_apply b 0 p

/-- On total spaces, the inverse of `cotangentDetCanonicalHomeomorph` acts fibrewise by
`(cotangentDetCanonicalFiberEquiv I b M p.proj).symm`. -/
@[simp] theorem cotangentDetCanonicalHomeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (cotangentDetCanonicalHomeomorph I b M).symm p =
      ⟨p.proj, (cotangentDetCanonicalFiberEquiv I b M p.proj).symm p.snd⟩ :=
  cotangentDetCanonicalDiffeomorph_symm_apply b 0 p

/-- The underlying homeomorphism of `cotangentDetCanonicalDiffeomorph` at any regularity `k` agrees
with `cotangentDetCanonicalHomeomorph`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_toHomeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    (cotangentDetCanonicalDiffeomorph I b M k).toHomeomorph =
      cotangentDetCanonicalHomeomorph I b M :=
  Homeomorph.ext fun p ↦ (cotangentDetCanonicalDiffeomorph_apply b k p).trans
    (cotangentDetCanonicalHomeomorph_apply b p).symm

/-- Over the chart at `x₀`, the unit scalar coordinate `1` in the `x₀`-trivialization of
`(cotangentCore I b M).det` maps to `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b x`. -/
theorem cotangentDetCanonicalFiberEquiv_localTriv_symm_one
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x : M} (hx₀ : x ∈ (chartAt H x₀).source) :
    cotangentDetCanonicalFiberEquiv I b M x
        (((cotangentCore I b M).det.core.localTriv x₀).symm x
          ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)) =
      CanonicalBundle.coordForm I x₀ b x := by
  have hb₀ : x ∈ ((cotangentCore I b M).det.core.localTriv x₀).baseSet := by
    rwa [FiniteRankBundleCore.localTriv_baseSet_det, baseSet_cotangentCore]
  rw [((cotangentCore I b M).det.core).localTriv_symm_apply (i := x₀) hb₀,
    (cotangentCore I b M).det.indexAt_eq, cotangentDetCanonicalFiberEquiv_apply,
    coordChange_cotangentCore_det b hx₀ (mem_chart_source H x)]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (CanonicalBundle.coordForm_eq_det_smul_coordForm hx₀ (mem_chart_source H x)).symm

/-- The canonical identification `cotangentDetCanonicalFiberEquiv` commutes with changes of model
basis. -/
theorem cotangentDetCanonicalFiberEquiv_changeBasis
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b₂ M x
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      cotangentDetCanonicalFiberEquiv I b₁ M x u := by
  rw [cotangentDetCanonicalFiberEquiv_apply, cotangentDetCanonicalFiberEquiv_apply,
    detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom,
    CanonicalBundle.coordForm_basis_change x b₁ b₂ x, smul_smul, mul_comm]

end CanonicalComparison

end TauCeti
