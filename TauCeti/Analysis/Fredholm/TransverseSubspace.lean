/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange

/-!
# The transverse-subspace lemma and Fredholm stability

Let `T : E →L[𝕜] F` be a continuous linear map, `V ≤ E`, and `W ≤ F`. Whenever the coproduct
operator
$$\Phi_T = (T \circ \iota_V) \oplus \iota_W : V \times W \to F, \qquad (v, w) \mapsto T v + w,$$
is invertible, without any completeness, norm, or inner-product assumptions on `E`, `F`, `V`, or
`W`, `V` meets `ker T` trivially, `W` is a topological complement of `T(V)` in `F`, `T` restricts to
a continuous linear equivalence `ContinuousLinearMap.restrictMapEquiv : V ≃L[𝕜] V.map T`, and
quotient-coordinate bounds hold for `dim ker T ≤ codim V` and `dim coker T ≤ dim W`. If moreover
`V` is closed of finite codimension and `W` is finite-dimensional, then `T` is Fredholm of index
`codim V - dim W`.

On normed spaces with complete codomain `F`, invertibility of `(T ∘L V.subtypeL).coprod W.subtypeL`
holds whenever `V` and `W` are complete, `Disjoint V T.ker`, and `IsCompl (V.map T) W`, and
persists on an operator-norm neighborhood of `T` (without completeness of `E` or explicit closedness
of `V`). When `E` and `F` are Banach spaces and `V` is closed, invertibility of
`(T ∘L V.subtypeL).coprod W.subtypeL` is equivalent to `Disjoint V T.ker ∧ IsTopCompl (V.map T) W`,
yielding the classical Atiyah–Singer transverse-subspace lemma and Fredholm stability. On a Hilbert
space codomain `F`, specializing `W = (V.map T₀)ᗮ` gives orthogonal transverse stability and
canonical `V = (T₀.ker)ᗮ` stability for closed-range operators.

## Main declarations

* `ContinuousLinearMap.disjoint_ker_of_isInvertible_comp_subtypeL_coprod` and
  `ContinuousLinearMap.isTopCompl_map_of_isInvertible_comp_subtypeL_coprod`: pointwise
  transversality `Disjoint V T.ker` and topological splitting `(V.map T).IsTopCompl W` in full
  TVS generality.
* `ContinuousLinearMap.restrictMapEquiv`: canonical equivalence `V ≃L[𝕜] V.map T` induced by an
  invertible `(T ∘L V.subtypeL).coprod W.subtypeL`.
* `ContinuousLinearMap.finrank_ker_le_of_isInvertible_comp_subtypeL_coprod`,
  `ContinuousLinearMap.finrank_coker_le_of_isInvertible_comp_subtypeL_coprod`,
  `ContinuousLinearMap.isFredholm_of_isInvertible_comp_subtypeL_coprod`, and
  `ContinuousLinearMap.index_eq_of_isInvertible_comp_subtypeL_coprod`: dimension bounds,
  Fredholmness, and index formula `codim V - dim W` over topological vector spaces.
* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible`, and
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod`: invertibility and
  operator-norm openness for complete `V`, `W`, `F` without completeness of `E`.
* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_iff`: `(v, w) ↦ T v + w` is invertible on
  `V × W` exactly when `V` meets `ker T` trivially and `W` is a topological complement of `T(V)`.
* `ContinuousLinearMap.eventually_disjoint_ker_and_isTopCompl_map`: the transverse-subspace lemma;
  both conditions persist in an operator-norm neighbourhood of `T₀`.
* `ContinuousLinearMap.isFredholm_of_disjoint_ker_of_isTopCompl_map` and
  `ContinuousLinearMap.index_eq_of_disjoint_ker_of_isTopCompl_map`: under both conditions, with
  `V` closed of finite codimension and `W` finite-dimensional, `T` is Fredholm of index
  `codim V - dim W`.
* `ContinuousLinearMap.eventually_isFredholm_and_index_eq_of_isTopCompl_map`: near `T₀`, every
  operator is Fredholm with `dim ker T ≤ codim V`, `dim coker T ≤ dim W`, and index
  `codim V - dim W`.
* `ContinuousLinearMap.eventually_finrank_ker_sub_finrank_ker_eq_of_isTopCompl_map`: near `T₀`,
  every operator satisfies `dim ker T₀ - dim ker T = dim coker T₀ - dim coker T`.
* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_orthogonal_map`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod_orthogonal_map`
  (plus finite-dimensional variants),
  `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_orthogonal_ker`, and
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod_orthogonal_ker`:
  orthogonal Hilbert-space specializations for `W = (V.map T₀)ᗮ` and `V = (T₀.ker)ᗮ`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. (2) **87**
  (1968), 484–530 (§6, pp. 519–520).
* N. Bourbaki, *Théories Spectrales*, Chapitre III, §3, n° 2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Filter Function Module Submodule Topology

namespace ContinuousLinearMap

/-! ### Pointwise TVS consequences of invertible `(T ∘L V.subtypeL).coprod W.subtypeL` -/

section Pointwise

variable {𝕜 E F : Type*} [Ring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, then `V` meets `ker T` trivially. -/
theorem disjoint_ker_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    Disjoint V T.ker := by
  rw [Submodule.disjoint_def]
  intro v hv hTv
  have hv0 : T v = 0 := hTv
  have happ : (T ∘L V.subtypeL).coprod W.subtypeL (⟨v, hv⟩, 0) =
      (T ∘L V.subtypeL).coprod W.subtypeL 0 := by
    simp [hv0]
  exact congrArg Subtype.val (congrArg Prod.fst (hΦ.injective happ))

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, then `W` is a topological complement
of `V.map T` in `F`. -/
theorem isTopCompl_map_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (V.map (T : E →ₗ[𝕜] F)).IsTopCompl W := by
  let A : V →L[𝕜] F := T ∘L V.subtypeL
  let B : W →L[𝕜] F := W.subtypeL
  have hBA : (B.coprod A).IsInvertible := by
    rw [← coprod_comp_prodComm _ _ _ A B, isInvertible_comp_equiv]
    exact hΦ
  have hrange : A.range = V.map (T : E →ₗ[𝕜] F) := by
    simp [A, LinearMap.range_comp]
  have hker : (B.quotientRangeCoordinate A).ker = W := by
    simp [B, ker_quotientRangeCoordinate hBA]
  exact hrange ▸ hker ▸ A.isTopCompl_range_ker_of_leftInverse (B.quotientRangeCoordinate A)
    (quotientRangeCoordinate_apply_right hBA)

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible and `W` is `T1`, then `V.map T` is
closed in `F`. -/
theorem isClosed_map_of_isInvertible_comp_subtypeL_coprod
    {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [T1Space W] [ContinuousSub F]
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    IsClosed ((V.map (T : E →ₗ[𝕜] F)) : Set F) :=
  (isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ).isClosed

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, `T` restricts to a continuous linear
equivalence `V ≃L[𝕜] V.map T`. -/
noncomputable def restrictMapEquiv {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    V ≃L[𝕜] V.map (T : E →ₗ[𝕜] F) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem)
    (.fst 𝕜 V W ∘L ((T ∘L V.subtypeL).coprod W.subtypeL).inverse ∘L
      (V.map (T : E →ₗ[𝕜] F)).subtypeL)
    (ContinuousLinearMap.ext fun y ↦ by
      obtain ⟨v, hv, hTv⟩ := y.property
      rw [ContinuousLinearMap.coe_coe] at hTv
      rw [← Subtype.coe_inj]
      have h := congrArg Prod.fst (hΦ.inverse_apply_self ((⟨v, hv⟩ : V), 0))
      simp only [coprod_apply, comp_apply, subtypeL_apply, ZeroMemClass.coe_zero, add_zero, hTv]
        at h
      simp only [comp_apply, subtypeL_apply, coe_fst', coe_restrict_apply, id_apply, h]
      exact hTv)
    (ContinuousLinearMap.ext fun u ↦ by
      have h := congrArg Prod.fst (hΦ.inverse_apply_self (u, 0))
      simpa only [comp_apply, subtypeL_apply, coe_restrict_apply, coe_fst', coprod_apply,
        ZeroMemClass.coe_zero, add_zero, id_apply] using h)

/-- As a continuous linear map, `restrictMapEquiv` is the restriction of `T` to `V`. -/
theorem toContinuousLinearMap_restrictMapEquiv {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (restrictMapEquiv hΦ : V →L[𝕜] V.map (T : E →ₗ[𝕜] F)) =
      T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem :=
  (rfl)

/-- `restrictMapEquiv` acts on `V` by `T`. -/
@[simp]
theorem coe_restrictMapEquiv_apply {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) (u : V) :
    (restrictMapEquiv hΦ u : F) = T u :=
  (rfl)

/-- Explicit formula for the inverse of `restrictMapEquiv`. -/
theorem restrictMapEquiv_symm_apply {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[𝕜] F)) :
    (restrictMapEquiv hΦ).symm y =
      (((T ∘L V.subtypeL).coprod W.subtypeL).inverse (y : F)).1 :=
  (rfl)

/-- Applying `T` to `(restrictMapEquiv hΦ).symm y` recovers `y`. -/
@[simp]
theorem apply_restrictMapEquiv_symm {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[𝕜] F)) :
    T ((restrictMapEquiv hΦ).symm y) = (y : F) := by
  rw [← coe_restrictMapEquiv_apply hΦ, (restrictMapEquiv hΦ).apply_symm_apply]

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, the restriction `V →L[𝕜] V.map T` of
`T` is invertible. -/
theorem isInvertible_restrict_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (T.restrict (q := V.map (T : E →ₗ[𝕜] F)) fun _ ↦ Submodule.mem_map_of_mem).IsInvertible :=
  ⟨restrictMapEquiv hΦ, (toContinuousLinearMap_restrictMapEquiv hΦ).symm⟩

end Pointwise

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]

/-- Kernel dimension bound when `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible and `V` has
finite codimension. -/
theorem finrank_ker_le_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [V.CoFG]
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) :=
  Submodule.finrank_le_finrank_quotient_of_disjoint
    (disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ)

/-- Cokernel dimension bound when `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible and `W` is
finite-dimensional. -/
theorem finrank_coker_le_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [FiniteDimensional 𝕜 W]
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W := by
  let A := T ∘L V.subtypeL
  let e := (A.quotientRangeEquiv W.subtypeL hΦ).toLinearEquiv
  have : FiniteDimensional 𝕜 (F ⧸ A.range) := e.symm.finiteDimensional
  have hle : A.range ≤ T.range := LinearMap.range_comp_le_range _ _
  exact (LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hle)).trans_eq
    e.finrank_eq

end DivisionRing

/-! ### Fredholmness and index from a finite-codimension transverse subspace -/

section CoFG

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

/-- **Fredholmness from a finite-codimension transverse subspace.** If `V ≤ E` is closed of finite
codimension, `W ≤ F` is finite-dimensional, and `(T ∘L V.subtypeL).coprod W.subtypeL` is
invertible, then `T` is Fredholm (and in particular `T.range` is closed). -/
theorem isFredholm_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [T1Space W] (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    T.IsFredholm := by
  have hcompl := isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Submodule.FG.cofg_of_isCompl hcompl.isCompl.symm .of_finite
  exact .of_isInvertible_restrict hV hcompl.isClosed (fun _ ↦ Submodule.mem_map_of_mem)
    (isInvertible_restrict_of_isInvertible_comp_subtypeL_coprod hΦ)

/-- **Index formula from a finite-codimension transverse subspace.** Under the hypotheses of
`isFredholm_of_isInvertible_comp_subtypeL_coprod`, the index of `T` equals
`finrank 𝕜 (E ⧸ V) - finrank 𝕜 W`, independent of `T`. -/
theorem index_eq_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [T1Space W] (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W := by
  have hTF : T.IsFredholm := isFredholm_of_isInvertible_comp_subtypeL_coprod hV hΦ
  have hVF : V.subtypeL.IsFredholm := V.isFredholm_subtypeL hV
  have hcomp_idx := hTF.index_comp hVF
  have hinj : Injective ((T ∘L V.subtypeL) : V →ₗ[𝕜] F) := by
    rw [toLinearMap_comp, Submodule.toLinearMap_subtypeL]
    exact LinearMap.injective_domRestrict_iff.mpr
      (disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ)
  have hcoker : finrank 𝕜 (F ⧸ ((T ∘L V.subtypeL) : V →ₗ[𝕜] F).range) = finrank 𝕜 W :=
    ((T ∘L V.subtypeL).quotientRangeEquiv W.subtypeL hΦ).toLinearEquiv.finrank_eq
  rw [LinearMap.index_of_injective hinj, hcoker, Submodule.toLinearMap_subtypeL,
    LinearMap.index_subtype, ← T.index_def] at hcomp_idx
  omega

/-- Whenever both `(T₀ ∘L V.subtypeL).coprod W.subtypeL` and `(T ∘L V.subtypeL).coprod W.subtypeL`
are invertible, the signed changes `(finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker` and
`(finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range)` between `T₀` and `T` are equal. -/
theorem finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_comp_subtypeL_coprod
    {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [T1Space W]
    (hV : IsClosed (V : Set E)) [V.CoFG] [FiniteDimensional 𝕜 W]
    (hΦ₀ : ((T₀ ∘L V.subtypeL).coprod W.subtypeL).IsInvertible)
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) := by
  have hidx₀ := index_eq_of_isInvertible_comp_subtypeL_coprod hV hΦ₀
  have hidx := index_eq_of_isInvertible_comp_subtypeL_coprod hV hΦ
  rw [T₀.index_eq_finrank_sub] at hidx₀
  rw [T.index_eq_finrank_sub] at hidx
  omega

end CoFG

/-! ### Normed and Banach transverse-subspace stability -/

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}

section CompleteCodom

variable [CompleteSpace F]

/-- When `V`, `W`, and `F` are complete, `V` meets `ker T` trivially, and `W` is an algebraic
complement of `T(V)` in `F`, the coproduct `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible,
without completeness of `E` or explicit closedness of `V`. -/
theorem isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl [CompleteSpace V]
    [CompleteSpace W] (hker : Disjoint V T.ker)
    (hW : IsCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible := by
  have hrange : (T ∘L V.subtypeL).range = V.map (T : E →ₗ[𝕜] F) := by
    simp [LinearMap.range_comp]
  have hker' : (T ∘L V.subtypeL).ker = ⊥ := by
    rw [toLinearMap_comp, Submodule.toLinearMap_subtypeL, LinearMap.ker_eq_bot]
    exact LinearMap.injective_domRestrict_iff.mpr hker
  exact ⟨(T ∘L V.subtypeL).coprodSubtypeLEquivOfIsCompl (hrange ▸ hW) hker',
    coe_coprodSubtypeLEquivOfIsCompl ..⟩

/-- **Openness of transverse-coproduct invertibility.** Whenever
`((T ∘L V.subtypeL).coprod W.subtypeL)` is invertible and `F` is complete, it stays invertible in
an operator-norm neighborhood of `T` (without completeness of `E`, `V`, or `W`). -/
theorem eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    ∀ᶠ S in 𝓝 T, ((S ∘L V.subtypeL).coprod W.subtypeL).IsInvertible := by
  have : CompleteSpace (V × W) := completeSpace_of_isInvertible hΦ
  have hcont : Continuous fun S : E →L[𝕜] F ↦ (S ∘L V.subtypeL).coprod W.subtypeL := by fun_prop
  exact hcont.continuousAt.eventually hΦ.eventually_nhds

/-- **Openness of the transverse-subspace condition.** Under the hypotheses of
`isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl`,
`(T ∘L V.subtypeL).coprod W.subtypeL` stays invertible for all `T` in an operator-norm neighborhood
of `T₀`, without completeness of `E`. -/
theorem eventually_nhds_isInvertible_comp_subtypeL_coprod [CompleteSpace V] [CompleteSpace W]
    (hker : Disjoint V T₀.ker) (hW : IsCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) :
    ∀ᶠ T in 𝓝 T₀, ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    (isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl hker hW)

/-- For a closed subspace `V` of a Banach space `E` and a subspace `W` of a Banach space `F`, the
map `V × W → F`, `(v, w) ↦ T v + w`, is invertible exactly when `V` meets the kernel of `T`
trivially and `W` is a topological complement of `T(V)`. -/
theorem isInvertible_comp_subtypeL_coprod_iff [CompleteSpace E] (hV : IsClosed (V : Set E)) :
    ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible ↔
      Disjoint V T.ker ∧ IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W := by
  refine ⟨fun hΦ ↦ ⟨disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ,
      isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ⟩, fun ⟨hker, hW⟩ ↦ ?_⟩
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  exact isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl hker hW.isCompl

/-- **The transverse-subspace lemma** (Atiyah–Singer). Let `V` be a closed subspace of a Banach
space `E` meeting the kernel of `T₀ : E →L[𝕜] F` trivially, and `W` a topological complement of
`T₀(V)` in the Banach space `F`. Then for every `T` close enough to `T₀` in the operator norm,
`V` meets the kernel of `T` trivially and `W` is a topological complement of `T(V)`. -/
theorem eventually_disjoint_ker_and_isTopCompl_map [CompleteSpace E] (hV : IsClosed (V : Set E))
    (hker : Disjoint V T₀.ker) (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀, Disjoint V T.ker ∧ IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W := by
  filter_upwards [eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩)] with T hT
  exact (isInvertible_comp_subtypeL_coprod_iff hV).mp hT

section Fredholm

variable [CompleteSpace 𝕜] [CompleteSpace E]

/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then `T` is Fredholm. -/
theorem isFredholm_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.IsFredholm :=
  isFredholm_of_isInvertible_comp_subtypeL_coprod hV
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩)

/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then the index of `T` is `codim V - dim W`. -/
theorem index_eq_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 W :=
  index_eq_of_isInvertible_comp_subtypeL_coprod hV
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩)

/-- **The transverse-subspace lemma, Fredholm form.** Let `V` be a closed finite-codimensional
subspace of a Banach space `E` meeting the kernel of `T₀ : E →L[𝕜] F` trivially, and `W` a
finite-dimensional topological complement of `T₀(V)` in the Banach space `F`. Then every `T` close
enough to `T₀` in the operator norm is Fredholm, with `dim ker T ≤ codim V`, `dim coker T ≤ dim W`
and index `codim V - dim W`. -/
theorem eventually_isFredholm_and_index_eq_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T₀.ker)
    (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀, T.IsFredholm ∧ finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) ∧
      finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W ∧
      T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 W := by
  filter_upwards [eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩)] with T hΦ
  exact ⟨isFredholm_of_isInvertible_comp_subtypeL_coprod hV hΦ,
    finrank_ker_le_of_isInvertible_comp_subtypeL_coprod hΦ,
    finrank_coker_le_of_isInvertible_comp_subtypeL_coprod hΦ,
    index_eq_of_isInvertible_comp_subtypeL_coprod hV hΦ⟩

/-- **The transverse-subspace lemma, dimension form.** Under the hypotheses of
`eventually_isFredholm_and_index_eq_of_isTopCompl_map`, every `T` close enough to `T₀` in the
operator norm has the index `codim V - dim W` of `T₀`, so
`dim ker T₀ - dim ker T = dim coker T₀ - dim coker T`. The index equality alone is Mathlib's
`ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq`. -/
theorem eventually_finrank_ker_sub_finrank_ker_eq_of_isTopCompl_map (hV : IsClosed (V : Set E))
    [V.CoFG] [FiniteDimensional 𝕜 W] (hker : Disjoint V T₀.ker)
    (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀, (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      finrank 𝕜 (F ⧸ T₀.range) - finrank 𝕜 (F ⧸ T.range) := by
  have hΦ₀ := (isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩
  filter_upwards [eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible hΦ₀] with T hΦ
  exact finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_comp_subtypeL_coprod hV hΦ₀ hΦ

end Fredholm

end CompleteCodom

end Normed

/-! ### Orthogonal Hilbert-space specializations -/

section Hilbert

open scoped InnerProduct

section OrthogonalMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- When `V ≤ E` and the Hilbert space `F` are complete, `V.map T₀` is closed in `F`, and
`Disjoint V T₀.ker`, the orthogonal transverse coproduct
`(T₀ ∘L V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL` is invertible. -/
theorem isInvertible_comp_subtypeL_coprod_orthogonal_map (T₀ : E →L[𝕜] F) {V : Submodule 𝕜 E}
    [CompleteSpace V] (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    ((T₀ ∘L V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible := by
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  have : W.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.mpr hTV
  have : CompleteSpace Wᗮ := W.isClosed_orthogonal.completeSpace_coe
  exact isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl hdisj W.isCompl_orthogonal

/-- Under the hypotheses of `isInvertible_comp_subtypeL_coprod_orthogonal_map`,
`(T ∘L V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL` stays invertible in an operator-norm neighborhood
of `T₀`. -/
theorem eventually_nhds_isInvertible_comp_subtypeL_coprod_orthogonal_map (T₀ : E →L[𝕜] F)
    {V : Submodule 𝕜 E} [CompleteSpace V] (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T ∘L V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    (T₀.isInvertible_comp_subtypeL_coprod_orthogonal_map hTV hdisj)

/-- **Finite-dimensional orthogonal transverse stability.** If `F` is a Hilbert space, `V ≤ E` is
finite-dimensional, and `Disjoint V T₀.ker`, then `(T₀ ∘L V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL`
is invertible without explicit closedness hypotheses or completeness of `E`. -/
theorem isInvertible_comp_subtypeL_coprod_orthogonal_map_of_finiteDimensional (T₀ : E →L[𝕜] F)
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ((T₀ ∘L V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) := Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  exact T₀.isInvertible_comp_subtypeL_coprod_orthogonal_map
    (V.map (T₀ : E →ₗ[𝕜] F)).isClosed_of_finiteDimensional hdisj

/-- **Finite-dimensional orthogonal transverse openness.** If `F` is a Hilbert space, `V ≤ E` is
finite-dimensional, and `Disjoint V T₀.ker`, then `(T ∘L V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL`
stays invertible for all `T` near `T₀` without completeness of `E`. -/
theorem eventually_nhds_isInvertible_comp_subtypeL_coprod_orthogonal_map_of_finiteDimensional
    (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T ∘L V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    (T₀.isInvertible_comp_subtypeL_coprod_orthogonal_map_of_finiteDimensional V hdisj)

end OrthogonalMap

section OrthogonalKer

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- At a closed-range operator `T₀` between Hilbert spaces,
`(T₀ ∘L (T₀.ker)ᗮ.subtypeL).coprod T₀.rangeᗮ.subtypeL` is invertible. -/
theorem isInvertible_comp_subtypeL_coprod_orthogonal_ker (T₀ : E →L[𝕜] F)
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ((T₀ ∘L (T₀.ker)ᗮ.subtypeL).coprod T₀.rangeᗮ.subtypeL).IsInvertible := by
  have : CompleteSpace (T₀.ker)ᗮ := T₀.ker.isClosed_orthogonal.completeSpace_coe
  have hΦ := T₀.isInvertible_comp_subtypeL_coprod_orthogonal_map
    (by simpa only [LinearMap.map_orthogonal_ker_eq_range] using hT₀)
    T₀.ker.orthogonal_disjoint.symm
  rwa [LinearMap.map_orthogonal_ker_eq_range] at hΦ

/-- Near a closed-range operator `T₀` between Hilbert spaces,
`(T ∘L (T₀.ker)ᗮ.subtypeL).coprod T₀.rangeᗮ.subtypeL` stays invertible. -/
theorem eventually_nhds_isInvertible_comp_subtypeL_coprod_orthogonal_ker (T₀ : E →L[𝕜] F)
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ∀ᶠ T in 𝓝 T₀, ((T ∘L (T₀.ker)ᗮ.subtypeL).coprod T₀.rangeᗮ.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible
    (T₀.isInvertible_comp_subtypeL_coprod_orthogonal_ker hT₀)

end OrthogonalKer

end Hilbert

end ContinuousLinearMap

end
