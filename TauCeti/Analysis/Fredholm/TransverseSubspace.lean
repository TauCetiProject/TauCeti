/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange

/-!
# Transverse subspaces and Fredholm stability

Let `T₀ : E →L[𝕜] F` be a continuous linear operator from a normed space `E` into a Hilbert space
`F`, and let `V ≤ E` be a subspace transverse to `ker T₀` (`Disjoint V T₀.ker`, i.e.
`V ⊓ T₀.ker = ⊥`). Following Atiyah and Singer, consider for any operator `T : E →L[𝕜] F` the
coproduct operator
$$\Phi_T = (T \circ \iota_V) \oplus \iota_{(T₀(V))^{\perp}} : V \times (T₀(V))^{\perp} \to F.$$
Because the domain `V × (T₀(V))ᗮ` is independent of `T` and `T ↦ Φ_T` is continuous in operator
norm, invertibility of `Φ_T` is an open condition in `E →L[𝕜] F`:

* **Pointwise consequences of invertibility of `Φ_T`:** whenever `Φ_T` is invertible, `V` remains
  transverse to `ker T` (`Disjoint V T.ker`), `T` restricts to a topological isomorphism
  `V ≃L[𝕜] V.map T`, the image `V.map T` is closed and topologically complementary to the fixed
  orthogonal complement `(V.map T₀)ᗮ`, and `F ⧸ V.map T ≃L[𝕜] (V.map T₀)ᗮ`.
* **Openness at `T₀`:** when `V` and `F` are complete (for instance when `E` and `F` are complete
  and `V` is closed), `V.map T₀` is closed, and `Disjoint V T₀.ker`, Banach's open mapping theorem
  (via `ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl`) makes `Φ_{T₀}` invertible, so `Φ_T`
  stays invertible for all `T` in an operator-norm neighborhood of `T₀`.
* **Finite-dimensional `V`:** when `F` is complete, `V` is finite-dimensional, and
  `Disjoint V T₀.ker`, completeness of `V` and closedness of `V.map T₀` are automatic without
  completeness of `E`, so `Disjoint V T.ker` and `(V.map T).IsTopCompl (V.map T₀)ᗮ` hold
  throughout a neighborhood of `T₀`.
* **Closed finite-codimension `V`:** when `V` is closed of finite codimension and `(V.map T₀)ᗮ` is
  finite-dimensional, invertibility of `Φ_T` forces `T` to be Fredholm (in particular, to have
  closed range) by Bourbaki's restriction criterion
  `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`, with
  $$\dim \ker T \le \operatorname{codim} V, \qquad
    \dim \operatorname{coker} T \le \dim (T₀(V))^{\perp},$$
  and index `T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 (V.map T₀)ᗮ`. When `Φ_{T₀}` is also
  invertible (for instance when `V` and `F` are complete, `V.map T₀` is closed, and
  `Disjoint V T₀.ker`), this equals `T₀.index`, so kernel and cokernel dimensions change by equal
  signed amounts between `T₀` and `T` (dropping when `V` complements `T₀.ker`, such as
  `V = (T₀.ker)ᗮ`). Specializing to `V = (T₀.ker)ᗮ` for any closed-range operator `T₀` between
  Hilbert spaces gives invertibility of `Φ_T` near `T₀`, and when `T₀` is Fredholm yields
  Atiyah–Singer's geometric openness, upper semicontinuity, and index invariance package around
  `T₀`.

## Main declarations

* `ContinuousLinearMap.transverseCoprod`: the operator
  `(T.comp V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL : (V × (V.map T₀)ᗮ) →L[𝕜] F`.
* `ContinuousLinearMap.disjoint_ker_of_isInvertible_transverseCoprod` and
  `ContinuousLinearMap.isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod`: transversality
  `Disjoint V T.ker` and topological splitting `(V.map T).IsTopCompl (V.map T₀)ᗮ`.
* `ContinuousLinearMap.restrictTransverseEquiv`: canonical equivalence `V ≃L[𝕜] V.map T` (while
  `ContinuousLinearMap.quotientRangeEquiv` identifies
  `(F ⧸ (T.comp V.subtypeL).range) ≃L[𝕜] (V.map T₀)ᗮ`).
* `ContinuousLinearMap.isInvertible_transverseCoprod_self`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod_of_isInvertible`, and
  `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod`: invertibility of `Φ_{T₀}`
  and openness in `𝓝 T₀`.
* `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod_of_finiteDimensional`:
  neighborhood stability for finite-dimensional transverse subspaces.
* `ContinuousLinearMap.isFredholm_of_isInvertible_transverseCoprod`,
  `ContinuousLinearMap.finrank_ker_le_of_isInvertible_transverseCoprod`,
  `ContinuousLinearMap.finrank_coker_le_of_isInvertible_transverseCoprod`, and
  `ContinuousLinearMap.index_eq_of_isInvertible_transverseCoprod`: Fredholmness, dimension bounds,
  and index formula for closed finite-codimension transverse subspaces.
* `ContinuousLinearMap.isInvertible_transverseCoprod_orthogonal_ker_self` and
  `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod_orthogonal_ker`:
  specialization to `V = (T₀.ker)ᗮ` for any closed-range operator between Hilbert spaces.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. (2) **87**
  (1968), 484–530 (§6, pp. 519–520).
* N. Bourbaki, *Théories Spectrales*, Chapitre III, §3, n° 2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Filter Function Module Submodule Topology
open scoped InnerProduct

namespace ContinuousLinearMap

/-! ### The transverse coproduct and its pointwise consequences -/

section Pointwise

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Given a reference operator `T₀ : E →L[𝕜] F` and a subspace `V ≤ E`, `T₀.transverseCoprod V T`
is the continuous linear map `(V × (V.map T₀)ᗮ) →L[𝕜] F` sending `(v, w) ↦ T v + w`. -/
noncomputable def transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F) :
    (V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) →L[𝕜] F :=
  (T.comp V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL

/-- Definitional formula for `transverseCoprod`. -/
theorem transverseCoprod_def (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F) :
    T₀.transverseCoprod V T =
      (T.comp V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL :=
  (rfl)

/-- Pointwise formula for `transverseCoprod`. -/
@[simp]
theorem transverseCoprod_apply (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F)
    (p : V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) :
    T₀.transverseCoprod V T p = T p.1 + p.2 :=
  (rfl)

/-- If `T₀.transverseCoprod V T` is invertible, `V` is disjoint from `ker T`. -/
theorem disjoint_ker_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    Disjoint V T.ker := by
  rw [Submodule.disjoint_def]
  intro v hv hTv
  have hv0 : T v = 0 := hTv
  have happ : T₀.transverseCoprod V T (⟨v, hv⟩, 0) = T₀.transverseCoprod V T 0 := by
    simp [hv0]
  exact congrArg Subtype.val (congrArg Prod.fst (hΦ.injective happ))

/-- If `T₀.transverseCoprod V T` is invertible, then `T(V)` and `(T₀(V))ᗮ` are topological
complements in `F`. -/
theorem isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (V.map (T : E →ₗ[𝕜] F)).IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  let A : V →L[𝕜] F := T.comp V.subtypeL
  let B : Wᗮ →L[𝕜] F := Wᗮ.subtypeL
  have hBA : (B.coprod A).IsInvertible := by
    rw [← coprod_comp_prodComm _ _ _ A B, isInvertible_comp_equiv]
    simpa only [transverseCoprod_def] using hΦ
  have hrange : A.range = V.map (T : E →ₗ[𝕜] F) := by
    simp [A, LinearMap.range_comp]
  have hker : (B.quotientRangeCoordinate A).ker = Wᗮ := by
    simp [B, ker_quotientRangeCoordinate hBA]
  exact hrange ▸ hker ▸ A.isTopCompl_range_ker_of_leftInverse (B.quotientRangeCoordinate A)
    (quotientRangeCoordinate_apply_right hBA)

/-- If `T₀.transverseCoprod V T` is invertible, then `V.map T` is closed in `F`. -/
theorem isClosed_map_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    IsClosed ((V.map (T : E →ₗ[𝕜] F)) : Set F) :=
  (isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ).isClosed

/-- If `T₀.transverseCoprod V T` is invertible, `T` restricts to a continuous linear equivalence
`V ≃L[𝕜] V.map T`. -/
noncomputable def restrictTransverseEquiv {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    V ≃L[𝕜] V.map (T : E →ₗ[𝕜] F) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem)
    (.fst 𝕜 V (V.map (T₀ : E →ₗ[𝕜] F))ᗮ ∘L (T₀.transverseCoprod V T).inverse ∘L
      (V.map (T : E →ₗ[𝕜] F)).subtypeL)
    (ContinuousLinearMap.ext fun y ↦ by
      obtain ⟨v, hv, hTv⟩ := y.property
      rw [ContinuousLinearMap.coe_coe] at hTv
      rw [← Subtype.coe_inj]
      have h := congrArg Prod.fst (hΦ.inverse_apply_self ((⟨v, hv⟩ : V), 0))
      simp only [transverseCoprod_apply, ZeroMemClass.coe_zero, add_zero, hTv] at h
      simp only [comp_apply, subtypeL_apply, coe_fst', coe_restrict_apply, id_apply, h]
      exact hTv)
    (ContinuousLinearMap.ext fun u ↦ by
      have h := congrArg Prod.fst (hΦ.inverse_apply_self (u, 0))
      simpa only [comp_apply, subtypeL_apply, coe_restrict_apply, coe_fst',
        transverseCoprod_apply, ZeroMemClass.coe_zero, add_zero, id_apply] using h)

/-- As a continuous linear map, `restrictTransverseEquiv` is the restriction of `T` to `V`. -/
theorem toContinuousLinearMap_restrictTransverseEquiv {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (restrictTransverseEquiv hΦ : V →L[𝕜] V.map (T : E →ₗ[𝕜] F)) =
      T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem :=
  (rfl)

/-- `restrictTransverseEquiv` acts on `V` by `T`. -/
@[simp]
theorem coe_restrictTransverseEquiv_apply {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) (u : V) :
    (restrictTransverseEquiv hΦ u : F) = T u :=
  (rfl)

/-- Explicit formula for the inverse of `restrictTransverseEquiv`. -/
theorem restrictTransverseEquiv_symm_apply {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) (y : V.map (T : E →ₗ[𝕜] F)) :
    (restrictTransverseEquiv hΦ).symm y = ((T₀.transverseCoprod V T).inverse (y : F)).1 :=
  (rfl)

/-- Applying `T` to `(restrictTransverseEquiv hΦ).symm y` recovers `y`. -/
@[simp]
theorem apply_restrictTransverseEquiv_symm {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) (y : V.map (T : E →ₗ[𝕜] F)) :
    T ((restrictTransverseEquiv hΦ).symm y) = (y : F) := by
  rw [← coe_restrictTransverseEquiv_apply hΦ, (restrictTransverseEquiv hΦ).apply_symm_apply]

/-- If `T₀.transverseCoprod V T` is invertible, the restriction `V →L[𝕜] V.map T` of `T` is
invertible. -/
theorem isInvertible_restrict_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem).IsInvertible :=
  ⟨restrictTransverseEquiv hΦ, (toContinuousLinearMap_restrictTransverseEquiv hΦ).symm⟩

/-- Kernel dimension bound when `T₀.transverseCoprod V T` is invertible and `V` has finite
codimension. -/
theorem finrank_ker_le_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [V.CoFG] (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) :=
  Submodule.finrank_le_finrank_quotient_of_disjoint
    (disjoint_ker_of_isInvertible_transverseCoprod hΦ)

/-- Cokernel dimension bound when `T₀.transverseCoprod V T` is invertible and `(V.map T₀)ᗮ` is
finite-dimensional. -/
theorem finrank_coker_le_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  let A := T.comp V.subtypeL
  let B := (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL
  let e := (A.quotientRangeEquiv B (by simpa only [transverseCoprod_def] using hΦ)).toLinearEquiv
  have : FiniteDimensional 𝕜 (F ⧸ A.range) := e.symm.finiteDimensional
  have hle : A.range ≤ T.range := LinearMap.range_comp_le_range _ _
  exact (LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hle)).trans_eq
    e.finrank_eq

end Pointwise

/-! ### Fredholmness and index from a finite-codimension transverse subspace -/

section CoFG

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Fredholmness from a finite-codimension transverse subspace.** If `V ≤ E` is closed of finite
codimension, `(V.map T₀)ᗮ` is finite-dimensional, and `T₀.transverseCoprod V T` is invertible, then
`T` is Fredholm (and in particular `T.range` is closed). -/
theorem isFredholm_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    T.IsFredholm := by
  have hcompl := isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Submodule.FG.cofg_of_isCompl hcompl.isCompl.symm .of_finite
  exact .of_isInvertible_restrict hV hcompl.isClosed (fun _ ↦ Submodule.mem_map_of_mem)
    (isInvertible_restrict_of_isInvertible_transverseCoprod hΦ)

/-- **Index formula from a finite-codimension transverse subspace.** Under the hypotheses of
`isFredholm_of_isInvertible_transverseCoprod`, the index of `T` equals
`finrank 𝕜 (E ⧸ V) - finrank 𝕜 (V.map T₀)ᗮ`, independent of `T`. -/
theorem index_eq_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  have hTF : T.IsFredholm := isFredholm_of_isInvertible_transverseCoprod hV hΦ
  have hVF : V.subtypeL.IsFredholm := V.isFredholm_subtypeL hV
  have hcomp_idx := hTF.index_comp hVF
  have hinj : Injective ((T ∘L V.subtypeL) : V →ₗ[𝕜] F) := by
    rw [toLinearMap_comp, Submodule.toLinearMap_subtypeL]
    exact LinearMap.injective_domRestrict_iff.mpr (disjoint_ker_of_isInvertible_transverseCoprod hΦ)
  have hcoker : finrank 𝕜 (F ⧸ ((T ∘L V.subtypeL) : V →ₗ[𝕜] F).range) =
      finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ :=
    ((T.comp V.subtypeL).quotientRangeEquiv (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL
      (by simpa only [transverseCoprod_def] using hΦ)).toLinearEquiv.finrank_eq
  rw [LinearMap.index_of_injective hinj, hcoker, Submodule.toLinearMap_subtypeL,
    LinearMap.index_subtype, ← T.index_def] at hcomp_idx
  omega

/-- Whenever both `Φ_{T₀}` and `Φ_T` are invertible, the signed changes
`(finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker` and
`(finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range)` between `T₀` and `T` are equal. -/
theorem finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_transverseCoprod
    {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E} (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ₀ : (T₀.transverseCoprod V T₀).IsInvertible)
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) := by
  have hidx₀ := index_eq_of_isInvertible_transverseCoprod hV hΦ₀
  have hidx := index_eq_of_isInvertible_transverseCoprod hV hΦ
  rw [T₀.index_eq_finrank_sub] at hidx₀
  rw [T.index_eq_finrank_sub] at hidx
  omega

end CoFG

/-! ### Operator-norm continuity and openness around `T₀` -/

section Normed

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `T ↦ T₀.transverseCoprod V T` is continuous in operator norm. -/
theorem continuous_transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) :
    Continuous (T₀.transverseCoprod V) := by
  unfold transverseCoprod
  fun_prop

section CompleteCodom

variable [CompleteSpace F]

/-- **Invertibility of `Φ_{T₀}`.** When `V ≤ E` and `F` are complete, `V.map T₀` is closed in `F`,
and `Disjoint V T₀.ker`, the coproduct `T₀.transverseCoprod V T₀` is invertible. -/
theorem isInvertible_transverseCoprod_self (T₀ : E →L[𝕜] F) {V : Submodule 𝕜 E}
    [CompleteSpace V] (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    (T₀.transverseCoprod V T₀).IsInvertible := by
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  have : W.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.mpr hTV
  have : CompleteSpace Wᗮ := W.isClosed_orthogonal.completeSpace_coe
  have hrange : (T₀.comp V.subtypeL).range = W := by
    simp [W, LinearMap.range_comp]
  have hcompl : IsCompl (T₀.comp V.subtypeL).range Wᗮ := by
    simpa only [hrange] using W.isCompl_orthogonal
  have hker : (T₀.comp V.subtypeL).ker = ⊥ := by
    rw [toLinearMap_comp, Submodule.toLinearMap_subtypeL, LinearMap.ker_eq_bot]
    exact LinearMap.injective_domRestrict_iff.mpr hdisj
  refine ⟨(T₀.comp V.subtypeL).coprodSubtypeLEquivOfIsCompl hcompl hker, ?_⟩
  rw [coprodSubtypeLEquivOfIsCompl, ContinuousLinearEquiv.coe_ofBijective, transverseCoprod_def]

/-- **Openness of transverse-coproduct invertibility.** Whenever `T₀.transverseCoprod V T` is
invertible and `F` is complete, `T₀.transverseCoprod V S` stays invertible for `S` in an
operator-norm neighborhood of `T`. -/
theorem eventually_nhds_isInvertible_transverseCoprod_of_isInvertible {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    ∀ᶠ S in 𝓝 T, (T₀.transverseCoprod V S).IsInvertible := by
  have : CompleteSpace (V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) := completeSpace_of_isInvertible hΦ
  exact (T₀.continuous_transverseCoprod V).continuousAt.eventually hΦ.eventually_nhds

/-- **Openness of the transverse-subspace condition.** Under the hypotheses of
`isInvertible_transverseCoprod_self`, `T₀.transverseCoprod V T` stays invertible for all `T` in an
operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_transverseCoprod (T₀ : E →L[𝕜] F) {V : Submodule 𝕜 E}
    [CompleteSpace V] (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod V T).IsInvertible :=
  eventually_nhds_isInvertible_transverseCoprod_of_isInvertible
    (T₀.isInvertible_transverseCoprod_self hTV hdisj)

/-- **Finite-dimensional transverse subspace stability.** If `F` is complete, `V ≤ E` is
finite-dimensional, and `Disjoint V T₀.ker`, then `T₀.transverseCoprod V T₀` is invertible without
explicit closedness hypotheses or completeness of `E`. -/
theorem isInvertible_transverseCoprod_self_of_finiteDimensional (T₀ : E →L[𝕜] F)
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    (T₀.transverseCoprod V T₀).IsInvertible := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) := Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  exact T₀.isInvertible_transverseCoprod_self
    (V.map (T₀ : E →ₗ[𝕜] F)).isClosed_of_finiteDimensional hdisj

/-- **Finite-dimensional transverse subspace openness.** If `F` is complete, `V ≤ E` is
finite-dimensional, and `Disjoint V T₀.ker`, then `T₀.transverseCoprod V T` is invertible for all
`T` near `T₀` (so in particular `Disjoint V T.ker` and `(V.map T).IsTopCompl (V.map T₀)ᗮ` hold
near `T₀`), without completeness of `E`. -/
theorem eventually_nhds_isInvertible_transverseCoprod_of_finiteDimensional (T₀ : E →L[𝕜] F)
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod V T).IsInvertible :=
  eventually_nhds_isInvertible_transverseCoprod_of_isInvertible
    (T₀.isInvertible_transverseCoprod_self_of_finiteDimensional V hdisj)

end CompleteCodom

end Normed

/-! ### Canonical specialization to `V = (T₀.ker)ᗮ` on Hilbert spaces -/

section OrthogonalKer

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- At a closed-range operator `T₀` between Hilbert spaces, `T₀.transverseCoprod (T₀.ker)ᗮ T₀`
is invertible. -/
theorem isInvertible_transverseCoprod_orthogonal_ker_self (T₀ : E →L[𝕜] F)
    (hT₀ : IsClosed (T₀.range : Set F)) :
    (T₀.transverseCoprod (T₀.ker)ᗮ T₀).IsInvertible := by
  have : CompleteSpace (T₀.ker)ᗮ := T₀.ker.isClosed_orthogonal.completeSpace_coe
  refine T₀.isInvertible_transverseCoprod_self ?_ T₀.ker.orthogonal_disjoint.symm
  simpa only [LinearMap.map_orthogonal_ker_eq_range] using hT₀

/-- Near a closed-range operator `T₀` between Hilbert spaces, `T₀.transverseCoprod (T₀.ker)ᗮ T`
stays invertible. -/
theorem eventually_nhds_isInvertible_transverseCoprod_orthogonal_ker (T₀ : E →L[𝕜] F)
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod (T₀.ker)ᗮ T).IsInvertible :=
  eventually_nhds_isInvertible_transverseCoprod_of_isInvertible
    (T₀.isInvertible_transverseCoprod_orthogonal_ker_self hT₀)

end OrthogonalKer

end ContinuousLinearMap

end
