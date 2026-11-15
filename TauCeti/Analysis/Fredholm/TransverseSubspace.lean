/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.Restriction
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Transverse subspaces, coproduct stability, and Fredholm defect bounds

Let `T₀ : E →L[𝕜] F` be a continuous linear operator and let `V ≤ E` be a closed subspace
transverse to `ker T₀` (`Disjoint V T₀.ker`) whose image `T₀(V)` admits a topological complement
`W ≤ F` — for instance `W = (T₀(V))ᗮ` whenever `F` is a Hilbert space and `T₀(V)` is closed.
For any operator `T : E →L[𝕜] F`, the coproduct

`(T.domRestrict V).coprod W.subtypeL : (V × W) →L[𝕜] F`

is invertible at `T = T₀` by Banach's open mapping theorem, and therefore remains invertible on an
operator-norm neighborhood of `T₀` whenever `V` and `F` are complete.

At every operator `T` where `(T.domRestrict V).coprod W.subtypeL` is invertible:

* `V` remains transverse to `ker T` (`Disjoint V T.ker`),
* `T` restricts to a continuous linear equivalence `V ≃L[𝕜] T(V)`,
* `T(V)` is closed and remains topologically complemented by the fixed subspace `W`
  (`IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W`), identifying `F ⧸ T(V)` with `W` via
  `ContinuousLinearMap.quotientRangeEquiv`.

This single mechanism specializes in two complementary regimes:

1. **Finite-dimensional `V` on a Hilbert target** (Atiyah–Singer I, §3, pp. 519–520): if `V` is
   finite-dimensional and `Disjoint V T₀.ker`, then `V` and `T₀(V)` are automatically complete, so
   for all `T` near `T₀` the operator `T₀.transverseCoprod V T` is invertible, `Disjoint V T.ker`,
   and `T(V)` is a closed topological complement of `(T₀(V))ᗮ`.
2. **Closed finite-codimension `V` (`[V.CoFG]`, `[FiniteDimensional 𝕜 W]`)**: invertibility of
   `(T.domRestrict V).coprod W.subtypeL` implies directly — via
   `ContinuousLinearMap.IsFredholm.of_isInvertible_restrict`, without invoking openness of
   Fredholm operators — that `T` is Fredholm with closed range, satisfies the dimension bounds
   `finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)` and `finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W`, and has
   index `(finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W`. Taking `V = (ker T₀)ᗮ` and `W = ker T₀†` for a
   Fredholm operator `T₀` between Hilbert spaces yields local upper semicontinuity of nullity and
   conullity together with the exact natural-number defect identity
   `finrank 𝕜 T₀.ker - finrank 𝕜 T.ker = finrank 𝕜 (F ⧸ T₀.range) - finrank 𝕜 (F ⧸ T.range)`.

## Main declarations

* `ContinuousLinearMap.disjoint_ker_of_isInvertible_domRestrict_coprod`,
  `ContinuousLinearMap.domRestrictEquivMap`,
  `ContinuousLinearMap.isTopCompl_map_of_isInvertible_domRestrict_coprod`: algebraic and
  topological consequences of `((T.domRestrict V).coprod W.subtypeL).IsInvertible`.
* `ContinuousLinearMap.isFredholm_of_isInvertible_domRestrict_coprod`,
  `ContinuousLinearMap.index_eq_of_isInvertible_domRestrict_coprod`: Fredholmness and index formula
  in the finite-codimension regime.
* `ContinuousLinearMap.isInvertible_domRestrict_coprod_self`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_domRestrict_coprod`: basepoint and neighborhood
  invertibility on Banach spaces.
* `ContinuousLinearMap.transverseCoprod`: the Hilbert-target coproduct
  `(T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL`.
* `ContinuousLinearMap.eventually_nhds_transverse_of_finiteDimensional`: the finite-dimensional
  Atiyah–Singer transverse-subspace theorem.
* `ContinuousLinearMap.eventually_nhds_transverse_of_coFG`,
  `ContinuousLinearMap.IsFredholm.eventually_nhds_transverse_orthogonal_ker`: the
  finite-codimension and orthogonal-kernel perturbation theorems and defect identities.

## References

* M. F. Atiyah, I. M. Singer, *The Index of Elliptic Operators: I*, Annals of Mathematics **87**
  (1968), 484–530, §3, pp. 519–520.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1.
-/

public section

noncomputable section

open Filter Function Module Submodule Topology
open scoped InnerProduct

namespace ContinuousLinearMap

/-! ### Pointwise consequences of an invertible restricted coproduct -/

section TVS

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  {T : E →L[R] F} {V : Submodule R E} {W : Submodule R F}

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible, then `V` is disjoint from `ker T`. -/
theorem disjoint_ker_of_isInvertible_domRestrict_coprod
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    Disjoint V T.ker := by
  rw [disjoint_iff]
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot, coe_coe]
  refine ⟨fun ⟨hxV, hxT⟩ ↦ ?_, fun hx ↦ by simp [hx]⟩
  have hzero : ((T.domRestrict V).coprod W.subtypeL) (⟨x, hxV⟩, 0) = 0 := by
    simp [hxT]
  exact congrArg (fun p : V × W ↦ (p.1 : E)) (hinv.injective (hzero.trans (map_zero _).symm))

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `T` restricts to a continuous linear
equivalence between `V` and its image `V.map (T : E →ₗ[R] F)`. -/
def domRestrictEquivMap (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    V ≃L[R] V.map (T : E →ₗ[R] F) :=
  ContinuousLinearEquiv.equivOfInverse
    (T.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx)
    (fst R V W ∘L ((T.domRestrict V).coprod W.subtypeL).inverse ∘L
      (V.map (T : E →ₗ[R] F)).subtypeL)
    (fun v ↦ by
      have h := congrArg Prod.fst (hinv.inverse_apply_self (v, 0))
      simpa only [comp_apply, coe_fst', Submodule.subtypeL_apply, coe_restrict_apply,
        coprod_apply, domRestrict_apply, map_zero, add_zero] using h)
    (fun y ↦ by
      rcases y with ⟨_, v, hv, rfl⟩
      apply Subtype.ext
      have h := congrArg Prod.fst (hinv.inverse_apply_self (⟨v, hv⟩, 0))
      simp only [coprod_apply, domRestrict_apply, map_zero, add_zero] at h
      simp only [comp_apply, coe_fst', Submodule.subtypeL_apply, coe_restrict_apply, coe_coe, h])

@[simp]
theorem coe_domRestrictEquivMap_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (v : V) :
    (domRestrictEquivMap hinv v : F) = T v :=
  (rfl)

@[simp]
theorem domRestrictEquivMap_symm_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[R] F)) :
    (domRestrictEquivMap hinv).symm y =
      (((T.domRestrict V).coprod W.subtypeL).inverse (y : F)).1 :=
  (rfl)

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, the restriction
`T.restrict : V →L[R] V.map (T : E →ₗ[R] F)` is invertible. -/
theorem isInvertible_restrict_map_of_isInvertible_domRestrict_coprod
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    (T.restrict (fun _ hx ↦ Submodule.mem_map_of_mem hx :
      Set.MapsTo T V (V.map (T : E →ₗ[R] F)))).IsInvertible :=
  ⟨domRestrictEquivMap hinv, rfl⟩

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `V.map (T : E →ₗ[R] F)` and `W` are
topological complements in `F`. -/
theorem isTopCompl_map_of_isInvertible_domRestrict_coprod
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    IsTopCompl (V.map (T : E →ₗ[R] F)) W := by
  have hcompl := W.subtypeL.isTopCompl_range_ker_of_leftInverse
    ((T.domRestrict V).quotientRangeCoordinate W.subtypeL)
    (quotientRangeCoordinate_apply_right hinv)
  rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype,
    ker_quotientRangeCoordinate hinv, toLinearMap_domRestrict,
    LinearMap.range_domRestrict] at hcompl
  exact hcompl.symm

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible and `W` is `T₁`, the image `T(V)` is
closed in `F`. -/
theorem isClosed_map_of_isInvertible_domRestrict_coprod [T1Space W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    IsClosed (V.map (T : E →ₗ[R] F) : Set F) :=
  (isTopCompl_map_of_isInvertible_domRestrict_coprod hinv).isClosed

end TVS

/-! ### Dimension bounds, Fredholmness, and index in finite codimension -/

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible and `V` has finite codimension, then
`finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)`. -/
theorem finrank_ker_le_of_isInvertible_domRestrict_coprod [V.CoFG]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) := by
  have hdisj := disjoint_ker_of_isInvertible_domRestrict_coprod hinv
  refine (V.mkQ.domRestrict T.ker).finrank_le_finrank_of_injective ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  exact disjoint_iff_comap_eq_bot.mp hdisj.symm

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible and `W` is finite-dimensional, then
`finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W`. -/
theorem finrank_quotient_range_le_of_isInvertible_domRestrict_coprod [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W := by
  have hTop := isTopCompl_map_of_isInvertible_domRestrict_coprod hinv
  let e := (V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl
  refine ((Submodule.factor LinearMap.map_le_range).comp e.symm.toLinearMap)
    |>.finrank_le_finrank_of_surjective ?_
  exact (Submodule.factor_surjective LinearMap.map_le_range).comp e.symm.surjective

end DivisionRing

section FiniteCodimension

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}

/-- **Fredholmness from an invertible finite-codimension transverse coproduct.** If `V` is closed
of finite codimension, `W` is finite-dimensional, and `(T.domRestrict V).coprod W.subtypeL` is
invertible, then `T` is Fredholm (and in particular has closed range). -/
theorem isFredholm_of_isInvertible_domRestrict_coprod
    (hV : IsClosed (V : Set E)) [V.CoFG] [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    T.IsFredholm := by
  have hTop := isTopCompl_map_of_isInvertible_domRestrict_coprod hinv
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Module.Finite.equiv ((V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl).symm
  exact IsFredholm.of_isInvertible_restrict hV hTop.isClosed
    (fun _ hx ↦ Submodule.mem_map_of_mem hx)
    (isInvertible_restrict_map_of_isInvertible_domRestrict_coprod hinv)

/-- Under the hypotheses of `isFredholm_of_isInvertible_domRestrict_coprod`, the Fredholm index of
`T` equals `(finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W`. -/
theorem index_eq_of_isInvertible_domRestrict_coprod
    (hV : IsClosed (V : Set E)) [V.CoFG] [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W := by
  have hTop := isTopCompl_map_of_isInvertible_domRestrict_coprod hinv
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Module.Finite.equiv ((V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl).symm
  have hMaps : Set.MapsTo T V (V.map (T : E →ₗ[𝕜] F)) := fun _ hx ↦ Submodule.mem_map_of_mem hx
  have hReq : T.restrict hMaps = (domRestrictEquivMap hinv : V →L[𝕜] V.map (T : E →ₗ[𝕜] F)) := rfl
  have hRfred : (T.restrict hMaps).IsFredholm := hReq ▸ (domRestrictEquivMap hinv).isFredholm
  have hidx := T.index_restrict hV hTop.isClosed hMaps hRfred
  have hRzero : (T.restrict hMaps).index = 0 := hReq ▸ (domRestrictEquivMap hinv).index_eq_zero
  have hWdim : finrank 𝕜 (F ⧸ V.map (T : E →ₗ[𝕜] F)) = finrank 𝕜 W :=
    ((V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl).finrank_eq
  omega

end FiniteCodimension

/-! ### Basepoint and neighborhood invertibility on Banach spaces -/

section Banach

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[fun_prop]
theorem continuous_domRestrict_coprod (V : Submodule 𝕜 E) (W : Submodule 𝕜 F) :
    Continuous fun T : E →L[𝕜] F ↦ (T.domRestrict V).coprod W.subtypeL := by
  have hEq : (fun T : E →L[𝕜] F ↦ (T.domRestrict V).coprod W.subtypeL) =
      fun T ↦ (T ∘L V.subtypeL) ∘L fst 𝕜 V W + W.subtypeL ∘L snd 𝕜 V W := by
    refine funext fun T ↦ ContinuousLinearMap.ext fun p ↦ ?_
    simp [coprod_apply]
  rw [hEq]
  fun_prop

variable [CompleteSpace F]

/-- **Basepoint invertibility of a transverse restricted coproduct.** If `V` is complete, `W` is a
topological complement of `V.map (T₀ : E →ₗ[𝕜] F)` in a Banach space `F`, and `Disjoint V T₀.ker`,
then `(T₀.domRestrict V).coprod W.subtypeL : (V × W) →L[𝕜] F` is invertible. -/
theorem isInvertible_domRestrict_coprod_self {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [CompleteSpace V]
    (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod W.subtypeL).IsInvertible := by
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  have hinj : ((T₀.domRestrict V).coprod W.subtypeL).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro ⟨v, w⟩ hvw
    rw [LinearMap.mem_ker, coe_coe, coprod_apply, domRestrict_apply, Submodule.subtypeL_apply,
      add_eq_zero_iff_eq_neg] at hvw
    have hv_mem : T₀ v ∈ V.map (T₀ : E →ₗ[𝕜] F) ⊓ W :=
      ⟨Submodule.mem_map_of_mem v.2, hvw ▸ neg_mem w.2⟩
    rw [hW.isCompl.disjoint.eq_bot, Submodule.mem_bot] at hv_mem
    have hw0 : w = 0 := Subtype.ext (neg_eq_zero.mp (hvw.symm.trans hv_mem))
    have hv_ker : (v : E) ∈ V ⊓ T₀.ker := ⟨v.2, hv_mem⟩
    rw [hdisj.eq_bot, Submodule.mem_bot] at hv_ker
    exact Prod.ext (Subtype.ext hv_ker) hw0
  have hsurj : ((T₀.domRestrict V).coprod W.subtypeL).range = ⊤ := by
    rw [range_coprod, toLinearMap_domRestrict, LinearMap.range_domRestrict,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype, hW.isCompl.sup_eq_top]
  exact ⟨ContinuousLinearEquiv.ofBijective _ hinj hsurj, rfl⟩

/-- **Neighborhood invertibility of a transverse restricted coproduct.** Under the hypotheses of
`isInvertible_domRestrict_coprod_self`, `(T.domRestrict V).coprod W.subtypeL` remains invertible for
all `T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_domRestrict_coprod {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [CompleteSpace V]
    (hW : IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod W.subtypeL).IsInvertible := by
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  exact (continuous_domRestrict_coprod V W).tendsto T₀ |>.eventually
    (isInvertible_domRestrict_coprod_self hW hdisj).eventually_nhds

end Banach

/-! ### Hilbert-target transverse coproducts and defect identities -/

section HilbertCodomain

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Given a reference operator `T₀ : E →L[𝕜] F` into a Hilbert space `F` and a subspace `V ≤ E`,
`T₀.transverseCoprod V T` is the coproduct `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` out of
`V × (T₀(V))ᗮ`. -/
def transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F) :
    (V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) →L[𝕜] F :=
  (T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL

theorem transverseCoprod_def (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F) :
    T₀.transverseCoprod V T = (T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL :=
  (rfl)

@[simp]
theorem transverseCoprod_apply (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F)
    (p : V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) :
    T₀.transverseCoprod V T p = T p.1 + p.2 :=
  (rfl)

@[fun_prop]
theorem continuous_transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) :
    Continuous (T₀.transverseCoprod V) :=
  continuous_domRestrict_coprod V (V.map (T₀ : E →ₗ[𝕜] F))ᗮ

variable [CompleteSpace F]

/-- When `V` is complete, `T₀(V)` has an orthogonal projection in `F`, and `Disjoint V T₀.ker`, the
Hilbert transverse coproduct `T₀.transverseCoprod V T₀` is invertible. -/
theorem isInvertible_transverseCoprod_self {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E} [CompleteSpace V]
    [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection] (hdisj : Disjoint V T₀.ker) :
    (T₀.transverseCoprod V T₀).IsInvertible :=
  isInvertible_domRestrict_coprod_self (V.map (T₀ : E →ₗ[𝕜] F)).isTopCompl_orthogonal hdisj

/-- Under the hypotheses of `isInvertible_transverseCoprod_self`, `T₀.transverseCoprod V T` is
invertible throughout a neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_transverseCoprod {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod V T).IsInvertible :=
  eventually_nhds_isInvertible_domRestrict_coprod
    (V.map (T₀ : E →ₗ[𝕜] F)).isTopCompl_orthogonal hdisj

/-- **Atiyah–Singer finite-dimensional transverse-subspace lemma.** If `V ≤ E` is
finite-dimensional and `Disjoint V T₀.ker`, then for every operator `T` in a neighborhood of `T₀`,
`T₀.transverseCoprod V T` is invertible, `V` remains disjoint from `ker T`, and `T(V)` is a
topological complement of `(T₀(V))ᗮ` in `F`. -/
theorem eventually_nhds_transverse_of_finiteDimensional {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀,
      (T₀.transverseCoprod V T).IsInvertible ∧
      Disjoint V T.ker ∧
      IsTopCompl (V.map (T : E →ₗ[𝕜] F)) (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have hfinMap : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) :=
    Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  have : CompleteSpace (V.map (T₀ : E →ₗ[𝕜] F)) := FiniteDimensional.completeSpace 𝕜 _
  filter_upwards [eventually_nhds_isInvertible_transverseCoprod hdisj] with T hinv
  exact ⟨hinv, disjoint_ker_of_isInvertible_domRestrict_coprod hinv,
    isTopCompl_map_of_isInvertible_domRestrict_coprod hinv⟩

/-- **Finite-codimension transverse-subspace perturbation theorem.** Let `E` be a Banach space,
`F` a Hilbert space, and `V ≤ E` a closed finite-codimensional subspace with `Disjoint V T₀.ker`
whose image `T₀(V)` is closed of finite codimension in `F`. Then every `T` near `T₀` satisfies
`Disjoint V T.ker`, `IsTopCompl (T(V)) (T₀(V))ᗮ`, `T.IsFredholm`, the dimension bounds
`finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)` and `finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (T₀(V))ᗮ`, and the
defect identity `(finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
(finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range)`. -/
theorem eventually_nhds_transverse_of_coFG [CompleteSpace E] {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hV : IsClosed (V : Set E)) [V.CoFG]
    (hMapClosed : IsClosed (V.map (T₀ : E →ₗ[𝕜] F) : Set F)) [(V.map (T₀ : E →ₗ[𝕜] F)).CoFG]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀,
      (T₀.transverseCoprod V T).IsInvertible ∧
      Disjoint V T.ker ∧
      IsTopCompl (V.map (T : E →ₗ[𝕜] F)) (V.map (T₀ : E →ₗ[𝕜] F))ᗮ ∧
      T.IsFredholm ∧
      finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) ∧
      finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ ∧
      (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
        (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) := by
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  let : CompleteSpace (V.map (T₀ : E →ₗ[𝕜] F)) := hMapClosed.isComplete.completeSpace_coe
  have hTop₀ := (V.map (T₀ : E →ₗ[𝕜] F)).isTopCompl_orthogonal
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ :=
    Module.Finite.equiv ((V.map (T₀ : E →ₗ[𝕜] F)).quotientEquivOfIsCompl _ hTop₀.isCompl)
  have hinv₀ := isInvertible_transverseCoprod_self hdisj
  have hidx₀ := index_eq_of_isInvertible_domRestrict_coprod hV hinv₀
  filter_upwards [eventually_nhds_isInvertible_transverseCoprod hdisj] with T hinv
  have hidx := index_eq_of_isInvertible_domRestrict_coprod hV hinv
  rw [index_eq_finrank_sub] at hidx hidx₀
  exact ⟨hinv, disjoint_ker_of_isInvertible_domRestrict_coprod hinv,
    isTopCompl_map_of_isInvertible_domRestrict_coprod hinv,
    isFredholm_of_isInvertible_domRestrict_coprod hV hinv,
    finrank_ker_le_of_isInvertible_domRestrict_coprod hinv,
    finrank_quotient_range_le_of_isInvertible_domRestrict_coprod hinv, by omega⟩

end HilbertCodomain

section HilbertDomain

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- When `ker T` admits an orthogonal projection, `T` maps `(ker T)ᗮ` onto `range T`. -/
@[simp]
theorem map_orthogonal_ker_eq_range (T : E →L[𝕜] F) [T.ker.HasOrthogonalProjection] :
    T.kerᗮ.map (T : E →ₗ[𝕜] F) = T.range := by
  have hker : T.ker.map (T : E →ₗ[𝕜] F) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨_, hx, rfl⟩
    exact hx
  rw [LinearMap.range_eq_map, ← T.ker.isCompl_orthogonal.symm.codisjoint.eq_top,
    Submodule.map_sup, hker, sup_bot_eq]

end HilbertDomain

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Orthogonal-kernel transverse perturbation and exact defect identity.** For any Fredholm
operator `T₀ : E →L[𝕜] F` between Hilbert spaces, every operator `T` sufficiently close to `T₀` in
operator norm is Fredholm with `Disjoint T₀.kerᗮ T.ker` and `IsTopCompl (T(T₀.kerᗮ)) (T₀†).ker`,
satisfies `finrank 𝕜 T.ker ≤ finrank 𝕜 T₀.ker` and
`finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (F ⧸ T₀.range)`, and obeys the exact `ℕ`-valued defect
identity
`finrank 𝕜 T₀.ker - finrank 𝕜 T.ker = finrank 𝕜 (F ⧸ T₀.range) - finrank 𝕜 (F ⧸ T.range)`. -/
theorem IsFredholm.eventually_nhds_transverse_orthogonal_ker {T₀ : E →L[𝕜] F}
    (hT₀ : T₀.IsFredholm) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀,
      Disjoint T₀.kerᗮ T.ker ∧
      IsTopCompl (T₀.kerᗮ.map (T : E →ₗ[𝕜] F)) (T₀†).ker ∧
      T.IsFredholm ∧
      finrank 𝕜 T.ker ≤ finrank 𝕜 T₀.ker ∧
      finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (F ⧸ T₀.range) ∧
      finrank 𝕜 T₀.ker - finrank 𝕜 T.ker =
        finrank 𝕜 (F ⧸ T₀.range) - finrank 𝕜 (F ⧸ T.range) := by
  have := hT₀.finite_ker
  have := hT₀.finite_coker
  have : T₀.kerᗮ.CoFG :=
    Module.Finite.equiv (T₀.kerᗮ.quotientEquivOfIsCompl T₀.ker T₀.ker.isCompl_orthogonal.symm).symm
  have hMap : T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F) = T₀.range := T₀.map_orthogonal_ker_eq_range
  have hMapClosed : IsClosed (T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F) : Set F) :=
    hMap ▸ hT₀.isClosed_range
  have : (T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F)).CoFG := hMap ▸ ‹T₀.range.CoFG›
  have hKerDim : finrank 𝕜 (E ⧸ T₀.kerᗮ) = finrank 𝕜 T₀.ker :=
    (T₀.kerᗮ.quotientEquivOfIsCompl T₀.ker T₀.ker.isCompl_orthogonal.symm).finrank_eq
  have hCokerDim : finrank 𝕜 (T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F))ᗮ = finrank 𝕜 (F ⧸ T₀.range) := by
    let : CompleteSpace T₀.range := hT₀.isClosed_range.isComplete.completeSpace_coe
    rw [hMap]
    exact (T₀.range.quotientEquivOfIsCompl T₀.rangeᗮ T₀.range.isCompl_orthogonal).finrank_eq.symm
  filter_upwards [eventually_nhds_transverse_of_coFG T₀.ker.isClosed_orthogonal hMapClosed
    T₀.ker.isCompl_orthogonal.symm.disjoint] with T hT
  rcases hT with ⟨-, hdisj, hTop, hFred, hkerLe, hcokerLe, hdefect⟩
  rw [hMap, T₀.orthogonal_range] at hTop
  rw [hKerDim] at hkerLe
  rw [hCokerDim] at hcokerLe
  exact ⟨hdisj, hTop, hFred, hkerLe, hcokerLe, by zify [hkerLe, hcokerLe]; exact hdefect⟩

end Hilbert

end ContinuousLinearMap

end
