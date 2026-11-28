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
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
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
and quotient-coordinate bounds hold for `dim ker T ≤ codim V` and `dim coker T ≤ dim W`. If moreover
`V` has finite codimension and `W` is finite-dimensional, then `T` has index `codim V - dim W`; if
`V` is closed over a complete scalar field (with `W` `T1`), then `T` is Fredholm.

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
* `ContinuousLinearMap.index_eq_of_disjoint_ker_of_isCompl_map`,
  `ContinuousLinearMap.index_eq_of_disjoint_ker_of_isTopCompl_map`,
  `ContinuousLinearMap.finrank_ker_sub_eq_finrank_coker_sub_of_disjoint_ker_of_isCompl_map`,
  `ContinuousLinearMap.finrank_ker_le_of_isInvertible_comp_subtypeL_coprod`,
  `ContinuousLinearMap.finrank_coker_le_of_isInvertible_comp_subtypeL_coprod`,
  `ContinuousLinearMap.index_eq_of_isInvertible_comp_subtypeL_coprod`, and
  `ContinuousLinearMap.isFredholm_of_isInvertible_comp_subtypeL_coprod`: dimension bounds,
  index formula `codim V - dim W` (from algebraic/topological complementation or invertible
  coproduct), and Fredholmness over topological vector spaces.
* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_of_disjoint_ker_of_isCompl`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod_of_isInvertible`, and
  `ContinuousLinearMap.eventually_nhds_isInvertible_comp_subtypeL_coprod`: invertibility and
  operator-norm openness for complete `V`, `W`, `F` without completeness of `E`.
* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_iff`: `(v, w) ↦ T v + w` is invertible on
  `V × W` exactly when `V` meets `ker T` trivially and `W` is a topological complement of `T(V)`.
* `ContinuousLinearMap.eventually_disjoint_ker_and_isTopCompl_map`: the transverse-subspace lemma;
  both conditions persist in an operator-norm neighbourhood of `T₀`.
* `ContinuousLinearMap.isFredholm_of_disjoint_ker_of_isTopCompl_map`: under `Disjoint V T.ker` and
  `IsTopCompl (V.map T) W`, with `V` closed of finite codimension and `W` finite-dimensional, `T` is
  Fredholm.
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

private theorem isInvertible_subtypeL_coprod_comp {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (W.subtypeL.coprod (T ∘L V.subtypeL)).IsInvertible := by
  rwa [← coprod_comp_prodComm _ _ _ (T ∘L V.subtypeL) W.subtypeL, isInvertible_comp_equiv]

private theorem quotientRangeCoordinate_apply_comp_subtypeL {T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) (v : V) :
    W.subtypeL.quotientRangeCoordinate (T ∘L V.subtypeL) (T v) = v :=
  quotientRangeCoordinate_apply_right (isInvertible_subtypeL_coprod_comp hΦ) v

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, then `V` meets `ker T` trivially. -/
theorem disjoint_ker_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    Disjoint V T.ker := by
  rw [Submodule.disjoint_def]
  intro v hv hTv
  have hv0 : T v = 0 := hTv
  have h := quotientRangeCoordinate_apply_comp_subtypeL hΦ ⟨v, hv⟩
  rw [hv0, map_zero] at h
  exact congrArg Subtype.val h.symm

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, then `W` is a topological complement
of `V.map T` in `F`. -/
theorem isTopCompl_map_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (V.map (T : E →ₗ[𝕜] F)).IsTopCompl W := by
  have hBA := isInvertible_subtypeL_coprod_comp hΦ
  have hrange : (T ∘L V.subtypeL).range = V.map (T : E →ₗ[𝕜] F) := by
    simp [LinearMap.range_comp]
  have hker : (W.subtypeL.quotientRangeCoordinate (T ∘L V.subtypeL)).ker = W := by
    simp [ker_quotientRangeCoordinate hBA]
  exact hrange ▸ hker ▸ (T ∘L V.subtypeL).isTopCompl_range_ker_of_leftInverse
    (W.subtypeL.quotientRangeCoordinate (T ∘L V.subtypeL))
    (quotientRangeCoordinate_apply_comp_subtypeL hΦ)

/-- If `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible, `T` restricts to a continuous linear
equivalence `V ≃L[𝕜] V.map T`. -/
noncomputable def restrictMapEquiv {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    V ≃L[𝕜] V.map (T : E →ₗ[𝕜] F) :=
  ({ __ := LinearEquiv.ofLeftInverse
        (f := ((T ∘L V.subtypeL : V →L[𝕜] F) : V →ₗ[𝕜] F))
        (quotientRangeCoordinate_apply_comp_subtypeL hΦ)
     continuous_toFun := (T ∘L V.subtypeL).continuous.subtype_mk _
     continuous_invFun :=
       (W.subtypeL.quotientRangeCoordinate (T ∘L V.subtypeL)).continuous.comp
         continuous_subtypeVal } :
    V ≃L[𝕜] LinearMap.range ((T ∘L V.subtypeL : V →L[𝕜] F) : V →ₗ[𝕜] F)).trans
    (ContinuousLinearEquiv.ofEq _ _ (by simp [LinearMap.range_comp]))

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
      (((T ∘L V.subtypeL).coprod W.subtypeL).inverse (y : F)).1 := by
  change W.subtypeL.quotientRangeCoordinate (T ∘L V.subtypeL) (y : F) = _
  have hswap : W.subtypeL.coprod (T ∘L V.subtypeL) =
      ((T ∘L V.subtypeL).coprod W.subtypeL) ∘L
        (ContinuousLinearEquiv.prodComm 𝕜 W V : (W × V) →L[𝕜] (V × W)) := by
    rw [coprod_comp_prodComm]
  rw [quotientRangeCoordinate_def, hswap, inverse_comp_equiv]
  rfl

/-- Applying `T` to `(restrictMapEquiv hΦ).symm y` recovers `y`. -/
@[simp]
theorem apply_restrictMapEquiv_symm {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[𝕜] F)) :
    T ((restrictMapEquiv hΦ).symm y) = (y : F) := by
  rw [← coe_restrictMapEquiv_apply hΦ, (restrictMapEquiv hΦ).apply_symm_apply]

end Pointwise

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- **Index formula from an algebraic complement of `V.map T`.** If `V ≤ E` has finite
codimension, `W ≤ F` is finite-dimensional, `Disjoint V T.ker`, and `IsCompl (V.map T) W`,
then `T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 W`. -/
theorem index_eq_of_disjoint_ker_of_isCompl_map {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [V.CoFG] [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W := by
  have hinj : Injective ((T : E →ₗ[𝕜] F) ∘ₗ V.subtype) :=
    LinearMap.injective_domRestrict_iff.mpr hker
  have : FiniteDimensional 𝕜 (T : E →ₗ[𝕜] F).ker :=
    Module.Finite.of_injective (V.mkQ.domRestrict (T : E →ₗ[𝕜] F).ker)
      (LinearMap.injective_domRestrict_iff.mpr (V.ker_mkQ.symm ▸ hker.symm))
  have : FiniteDimensional 𝕜 V.subtype.ker := by
    rw [Submodule.ker_subtype]
    infer_instance
  have : FiniteDimensional 𝕜 (E ⧸ V.subtype.range) := by
    rw [Submodule.range_subtype]
    infer_instance
  let e : (F ⧸ ((T : E →ₗ[𝕜] F) ∘ₗ V.subtype).range) ≃ₗ[𝕜] W :=
    (Submodule.quotEquivOfEq _ (V.map (T : E →ₗ[𝕜] F))
      (by simp [LinearMap.range_comp])).trans
      ((V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hW)
  have : FiniteDimensional 𝕜 (F ⧸ ((T : E →ₗ[𝕜] F) ∘ₗ V.subtype).range) :=
    e.symm.finiteDimensional
  have : FiniteDimensional 𝕜 (F ⧸ (T : E →ₗ[𝕜] F).range) :=
    Module.Finite.of_surjective
      (Submodule.factor (LinearMap.range_comp_le_range V.subtype (T : E →ₗ[𝕜] F)))
      (Submodule.factor_surjective _)
  have hcomp_idx := LinearMap.index_comp (T : E →ₗ[𝕜] F) V.subtype
  rw [LinearMap.index_of_injective hinj, e.finrank_eq, LinearMap.index_subtype,
    ← T.index_def] at hcomp_idx
  omega

/-- If `T` is injective on a finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then the index of `T` is `codim V - dim W`. -/
theorem index_eq_of_disjoint_ker_of_isTopCompl_map {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [V.CoFG] [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W :=
  index_eq_of_disjoint_ker_of_isCompl_map hker hW.isCompl

/-- Whenever `V ≤ E` has finite codimension, `W ≤ F` is finite-dimensional, `V` meets both
`T₀.ker` and `T.ker` trivially, and `W` complements both `V.map T₀` and `V.map T`, the signed
dimension changes `(finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker` and
`(finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range)` between `T₀` and `T` are equal. -/
theorem finrank_ker_sub_eq_finrank_coker_sub_of_disjoint_ker_of_isCompl_map
    {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [V.CoFG] [FiniteDimensional 𝕜 W]
    (hker₀ : Disjoint V T₀.ker) (hW₀ : IsCompl (V.map (T₀ : E →ₗ[𝕜] F)) W)
    (hker : Disjoint V T.ker) (hW : IsCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) := by
  have hidx₀ := index_eq_of_disjoint_ker_of_isCompl_map hker₀ hW₀
  have hidx := index_eq_of_disjoint_ker_of_isCompl_map hker hW
  rw [T₀.index_eq_finrank_sub] at hidx₀
  rw [T.index_eq_finrank_sub] at hidx
  omega

section

variable [ContinuousAdd F]

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

/-- **Index formula from a finite-codimension transverse subspace.** If `V ≤ E` has finite
codimension, `W ≤ F` is finite-dimensional, and `(T ∘L V.subtypeL).coprod W.subtypeL` is
invertible, then the index of `T` equals `finrank 𝕜 (E ⧸ V) - finrank 𝕜 W`, independent of
`T`. -/
theorem index_eq_of_isInvertible_comp_subtypeL_coprod {T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    {W : Submodule 𝕜 F} [V.CoFG] [FiniteDimensional 𝕜 W]
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W :=
  index_eq_of_disjoint_ker_of_isTopCompl_map
    (disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ)
    (isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ)

/-- Whenever both `(T₀ ∘L V.subtypeL).coprod W.subtypeL` and `(T ∘L V.subtypeL).coprod W.subtypeL`
are invertible, the signed changes `(finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker` and
`(finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range)` between `T₀` and `T` are equal. -/
theorem finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_comp_subtypeL_coprod
    {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [V.CoFG] [FiniteDimensional 𝕜 W]
    (hΦ₀ : ((T₀ ∘L V.subtypeL).coprod W.subtypeL).IsInvertible)
    (hΦ : ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible) :
    (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) :=
  finrank_ker_sub_eq_finrank_coker_sub_of_disjoint_ker_of_isCompl_map
    (disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ₀)
    (isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ₀).isCompl
    (disjoint_ker_of_isInvertible_comp_subtypeL_coprod hΦ)
    (isTopCompl_map_of_isInvertible_comp_subtypeL_coprod hΦ).isCompl

end

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
    ⟨restrictMapEquiv hΦ, rfl⟩

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
    index_eq_of_isInvertible_comp_subtypeL_coprod hΦ⟩

omit [CompleteSpace 𝕜] in
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
  exact finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_comp_subtypeL_coprod hΦ₀ hΦ

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
