/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Restriction
public import TauCeti.Analysis.Normed.Operator.Banach
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange

/-!
# The transverse-subspace lemma and Fredholm stability

Let `T₀ : E →L[𝕜] F` be a continuous linear map between Banach spaces, `V` a closed subspace of
`E` meeting the kernel of `T₀` trivially, and `W` a topological complement of `T₀(V)` in `F`. Then
the map `V × W → F`, `(v, w) ↦ T₀ v + w`, is a continuous linear equivalence, and since invertible
operators form an open set, so is `(v, w) ↦ T v + w` for every `T` close enough to `T₀` in the
operator norm. For such `T`, the subspace `V` still meets `ker T` trivially and `W` is still a
topological complement of `T(V)`.

When `V` has finite codimension and `W` is finite-dimensional, this controls every operator near
`T₀` directly: `T` restricts to an isomorphism between the closed finite-codimensional subspaces
`V` and `T(V)`, so it is Fredholm, its kernel has dimension at most `codim V`, its cokernel has
dimension at most `dim W`, and its index is `codim V - dim W`. Evaluating at `T₀` shows that the
index of `T` equals that of `T₀`, so `dim ker T₀ - dim ker T = dim coker T₀ - dim coker T`.

Neither `V` nor `W` is required to be orthogonal to anything, and `V` need not be
finite-dimensional or finite-codimensional for the first part. On a Hilbert space `F` one may take
`W = (V.map T₀)ᗮ` whenever `V.map T₀` is closed, through `Submodule.isTopCompl_orthogonal`.
Setting `W = (V.map T₀)ᗮ` defines the fixed coproduct operator
$$\Phi_T = (T \circ \iota_V) \oplus \iota_{(T₀(V))^{\perp}} : V \times (T₀(V))^{\perp} \to F,$$
which also yields pointwise consequences of invertibility of `Φ_T` without completeness of `E`,
the explicit equivalence `ContinuousLinearMap.restrictTransverseEquiv : V ≃L[𝕜] V.map T`,
finite-dimensional transverse stability without completeness of `E`, and specialization to
`V = (T₀.ker)ᗮ` for closed-range operators between Hilbert spaces.

## Main declarations

* `ContinuousLinearMap.isInvertible_comp_subtypeL_coprod_iff`: `(v, w) ↦ T v + w` is invertible on
  `V × W` exactly when `V` meets `ker T` trivially and `W` is a topological complement of `T(V)`.
* `ContinuousLinearMap.eventually_disjoint_ker_and_isTopCompl_map`: the transverse-subspace lemma;
  both conditions persist in an operator-norm neighbourhood of `T₀`.
* `ContinuousLinearMap.isFredholm_of_disjoint_ker_of_isTopCompl_map` and
  `ContinuousLinearMap.index_eq_of_disjoint_ker_of_isTopCompl_map`: under both conditions, with
  `V` closed of finite codimension and `W` finite-dimensional, `T` is Fredholm of index
  `codim V - dim W`.
* `ContinuousLinearMap.eventually_isFredholm_and_index_eq_of_isTopCompl_map`: near `T₀`, every
  operator is Fredholm with `dim ker T ≤ codim V`, `dim coker T ≤ dim W` and index
  `codim V - dim W`.
* `ContinuousLinearMap.eventually_finrank_ker_sub_finrank_ker_eq_of_isTopCompl_map`: near `T₀`,
  every operator satisfies `dim ker T₀ - dim ker T = dim coker T₀ - dim coker T`.
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

section TransverseCoprod

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

end TransverseCoprod

section BanachTransverse

open Topology Module Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}

/-- For a closed subspace `V` of a Banach space `E` and a subspace `W` of a Banach space `F`, the
map `V × W → F`, `(v, w) ↦ T v + w`, is invertible exactly when `V` meets the kernel of `T`
trivially and `W` is a topological complement of `T(V)`. -/
theorem isInvertible_comp_subtypeL_coprod_iff [CompleteSpace E] [CompleteSpace F]
    (hV : IsClosed (V : Set E)) :
    ((T ∘L V.subtypeL).coprod W.subtypeL).IsInvertible ↔
      Disjoint V T.ker ∧ IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W := by
  have hrange : (T ∘L V.subtypeL).range = V.map (T : E →ₗ[𝕜] F) := by
    rw [toLinearMap_comp, LinearMap.range_comp, Submodule.toLinearMap_subtypeL,
      Submodule.range_subtype]
  constructor
  · rintro ⟨e, he⟩
    have he' (x : V × W) : e x = T x.1 + x.2 := by
      rw [← ContinuousLinearEquiv.coe_coe, he, coprod_apply]
      simp
    have hleft (v : V) : e.symm (T v) = (v, 0) := e.symm_apply_eq.mpr (by simp [he'])
    refine ⟨Submodule.disjoint_def.mpr fun x hxV hxK ↦ ?_, ?_⟩
    · have h0 : e.symm (T x) = 0 := by simp [show T x = 0 by simpa [LinearMap.mem_ker] using hxK]
      simpa using congr(($((hleft ⟨x, hxV⟩).symm.trans h0)).1)
    -- `T ∘ V.subtype` has the continuous left inverse `fst ∘ e⁻¹`, whose kernel is `W`.
    have hinv : Function.LeftInverse (fst 𝕜 V W ∘L (e.symm : F →L[𝕜] V × W))
        (T ∘L V.subtypeL) := fun v ↦ by simp [hleft]
    have hker : (fst 𝕜 V W ∘L (e.symm : F →L[𝕜] V × W)).ker = W := by
      ext y
      simp only [LinearMap.mem_ker, coe_coe, coe_comp, ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, coe_fst']
      refine ⟨fun h ↦ ?_, fun hy ↦ ?_⟩
      · rw [← e.apply_symm_apply y, he', h]
        simp
      · rw [show y = e (0, ⟨y, hy⟩) by simp [he']]
        simp
    rw [← hrange, ← hker]
    exact (T ∘L V.subtypeL).isTopCompl_range_ker_of_leftInverse _ hinv
  · rintro ⟨hker, hW⟩
    have : CompleteSpace V := hV.isComplete.completeSpace_coe
    have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
    exact ⟨(T ∘L V.subtypeL).coprodSubtypeLEquivOfIsCompl (hrange ▸ hW.isCompl)
      (LinearMap.ker_eq_bot.2 (LinearMap.injective_domRestrict_iff.2 hker)),
      coe_coprodSubtypeLEquivOfIsCompl ..⟩

/-- **The transverse-subspace lemma** (Atiyah–Singer). Let `V` be a closed subspace of a Banach
space `E` meeting the kernel of `T₀ : E →L[𝕜] F` trivially, and `W` a topological complement of
`T₀(V)` in the Banach space `F`. Then for every `T` close enough to `T₀` in the operator norm,
`V` meets the kernel of `T` trivially and `W` is a topological complement of `T(V)`. -/
theorem eventually_disjoint_ker_and_isTopCompl_map [CompleteSpace E] [CompleteSpace F]
    (hV : IsClosed (V : Set E)) (hker : Disjoint V T₀.ker)
    (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀, Disjoint V T.ker ∧ IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W := by
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  have hcont : Continuous fun T : E →L[𝕜] F ↦ (T ∘L V.subtypeL).coprod W.subtypeL := by
    fun_prop
  filter_upwards [hcont.tendsto T₀ |>.eventually
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩).eventually_nhds] with T hT
  exact (isInvertible_comp_subtypeL_coprod_iff hV).mp hT

section Fredholm

variable [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- A subspace `T(V)` with a finite-dimensional complement has finite codimension. -/
private theorem cofg_map_of_isTopCompl [FiniteDimensional 𝕜 W]
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
  FG.cofg_of_isCompl hW.isCompl.symm .of_finite

/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then `T` is Fredholm. -/
theorem isFredholm_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.IsFredholm :=
  have := cofg_map_of_isTopCompl hW
  .of_isInvertible_restrict hV hW.isClosed _
    (isInvertible_restrict_map_of_disjoint_ker hV hker hW.isClosed)

/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then the index of `T` is `codim V - dim W`. -/
theorem index_eq_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 W := by
  have := cofg_map_of_isTopCompl hW
  have hinv := isInvertible_restrict_map_of_disjoint_ker hV hker hW.isClosed
  have h := index_restrict hV hW.isClosed _ hinv.isFredholm
  obtain ⟨e, he⟩ := hinv
  rw [← he, ContinuousLinearEquiv.index_eq_zero,
    (quotientEquivOfIsCompl _ _ hW.isCompl).finrank_eq] at h
  lia

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
  filter_upwards [eventually_disjoint_ker_and_isTopCompl_map hV hker hW] with T ⟨hkerT, hWT⟩
  have hFred := isFredholm_of_disjoint_ker_of_isTopCompl_map hV hkerT hWT
  have : FiniteDimensional 𝕜 T.ker := hFred.finite_ker
  refine ⟨hFred, ?_, ?_, index_eq_of_disjoint_ker_of_isTopCompl_map hV hkerT hWT⟩
  · -- The kernel of `T` injects into `E ⧸ V`.
    refine LinearMap.finrank_le_finrank_of_injective (f := V.mkQ ∘ₗ T.ker.subtype) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, ker_mkQ, ← disjoint_iff_comap_eq_bot]
    exact hkerT.symm
  · -- `W` maps onto `F ⧸ range T`, since `T(V) ⊔ W = ⊤` and `T(V) ≤ range T`.
    have htop : W.map T.range.mkQ = ⊤ := by
      rw [map_mkQ_eq_top]
      exact top_unique (hWT.isCompl.sup_eq_top ▸ sup_le_sup_right LinearMap.map_le_range W)
    have h := W.finrank_map_le T.range.mkQ
    rwa [htop, finrank_top] at h

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
  filter_upwards [eventually_isFredholm_and_index_eq_of_isTopCompl_map hV hker hW]
    with T ⟨_, _, _, hT⟩
  have hT₀ := index_eq_of_disjoint_ker_of_isTopCompl_map hV hker hW
  rw [index_eq_finrank_sub] at hT hT₀
  lia

end Fredholm

end ContinuousLinearMap

end BanachTransverse

end
