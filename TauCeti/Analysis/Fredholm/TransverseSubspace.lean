/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange

/-!
# Transverse subspaces, coproduct stability, and Fredholm defect bounds

Let `T₀ : E →L[𝕜] F` be a continuous linear operator and let `V ≤ E` be a complete subspace
transverse to `ker T₀` (`Disjoint V T₀.ker`) whose image `T₀(V)` admits a complete algebraic
complement `W ≤ F` in a Banach space `F` — for instance `W = (T₀(V))ᗮ` whenever `F` is a Hilbert
space and `T₀(V)` is closed. For any operator `T : E →L[𝕜] F`, the coproduct

`(T.domRestrict V).coprod W.subtypeL : (V × W) →L[𝕜] F`

is invertible at `T = T₀` by Banach's open mapping theorem (`isInvertible_coprod_domRestrict`), and
therefore remains invertible on an operator-norm neighborhood of `T₀`
(`eventually_nhds_isInvertible_coprod_domRestrict`).

At every operator `T` where `(T.domRestrict V).coprod W.subtypeL` is invertible:

* `V` remains transverse to `ker T` (`disjoint_ker_of_isInvertible_coprod_domRestrict`),
* `T` restricts to a continuous linear equivalence `V ≃L[𝕜] T(V)` (`domRestrictEquivMap`),
* `T(V)` remains topologically complemented by the fixed subspace `W`
  (`isTopCompl_map_of_isInvertible_coprod_domRestrict`) and is closed whenever `W` is `T₁`
  (`isClosed_map_of_isInvertible_coprod_domRestrict`), identifying `F ⧸ T(V)` with `W` via
  `ContinuousLinearMap.quotientRangeEquiv`.

This single mechanism specializes in two complementary regimes:

1. **Finite-dimensional `V` on a Hilbert target** (Atiyah–Singer I, §6, pp. 519–520): if `V` is
   finite-dimensional and `Disjoint V T₀.ker`, then `V` and `T₀(V)` are automatically complete, so
   `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible at `T₀` and on a neighborhood of `T₀`
   (`eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`).
2. **Finite-codimension `V` (`[V.CoFG]`, `[FiniteDimensional 𝕜 W]`)**: invertibility of
   `(T.domRestrict V).coprod W.subtypeL` implies the dimension bounds
   `finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)` and `finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W`, the index
   formula `T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W`, and — when `V` is closed in a
   topological vector space over a complete scalar field — `T.IsFredholm`. On a Hilbert target,
   completeness of `V` and `[(V.map T₀).CoFG]` automatically force `T₀(V)` to be closed
   (`eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_coFG`); for any closed-range
   operator `T₀` between Hilbert spaces, taking `V = (ker T₀)ᗮ` and `W = ker T₀†` gives
   neighborhood invertibility of `(T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL`
   (`eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker`).

## Main declarations

* `ContinuousLinearMap.disjoint_ker_of_isInvertible_coprod_domRestrict`,
  `ContinuousLinearMap.domRestrictEquivMap`,
  `ContinuousLinearMap.isTopCompl_map_of_isInvertible_coprod_domRestrict`: algebraic and
  topological consequences of `((T.domRestrict V).coprod W.subtypeL).IsInvertible`.
* `ContinuousLinearMap.index_eq_of_isInvertible_coprod_domRestrict`,
  `ContinuousLinearMap.isFredholm_of_isInvertible_coprod_domRestrict`: index formula and
  Fredholmness in the finite-codimension regime.
* `ContinuousLinearMap.isInvertible_coprod_domRestrict`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_coprod_domRestrict`: basepoint and neighborhood
  invertibility on Banach spaces.
* `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_coFG`,
  `ContinuousLinearMap.eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker`:
  finite-dimensional, finite-codimension, and orthogonal-kernel transverse coproduct stability on
  Hilbert spaces.

## References

* M. F. Atiyah, I. M. Singer, *The Index of Elliptic Operators: I*, Annals of Mathematics **87**
  (1968), 484–530, §6, pp. 519–520.
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
theorem disjoint_ker_of_isInvertible_coprod_domRestrict
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    Disjoint V T.ker :=
  LinearMap.injective_domRestrict_iff.mp fun v₁ v₂ hv ↦
    congrArg Prod.fst <| hinv.injective (a₁ := (v₁, 0)) (a₂ := (v₂, 0)) <| by simpa using hv

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `T` restricts to a continuous linear
equivalence between `V` and its image `V.map (T : E →ₗ[R] F)`. -/
def domRestrictEquivMap (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    V ≃L[R] V.map (T : E →ₗ[R] F) :=
  have hfst (v : V) : (((T.domRestrict V).coprod W.subtypeL).inverse (T v)).1 = v := by
    simpa using congrArg Prod.fst (hinv.inverse_apply_self (v, 0))
  ContinuousLinearEquiv.equivOfInverse
    (T.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx)
    (fst R V W ∘L ((T.domRestrict V).coprod W.subtypeL).inverse ∘L
      (V.map (T : E →ₗ[R] F)).subtypeL)
    (fun v ↦ by simp [hfst])
    (fun ⟨_, v, hv, rfl⟩ ↦ by
      apply Subtype.ext
      simp [hfst ⟨v, hv⟩])

@[simp]
theorem toContinuousLinearMap_domRestrictEquivMap
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    (domRestrictEquivMap hinv : V →L[R] V.map (T : E →ₗ[R] F)) =
      T.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx := by
  rw [domRestrictEquivMap, ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse]

@[simp]
theorem coe_domRestrictEquivMap_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (v : V) :
    (domRestrictEquivMap hinv v : F) = T v := by
  rw [← ContinuousLinearEquiv.coe_coe, toContinuousLinearMap_domRestrictEquivMap,
    coe_restrict_apply]

@[simp]
theorem domRestrictEquivMap_symm_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[R] F)) :
    (domRestrictEquivMap hinv).symm y =
      (((T.domRestrict V).coprod W.subtypeL).inverse (y : F)).1 := by
  simp [domRestrictEquivMap]

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, the restriction
`T.restrict : V →L[R] V.map (T : E →ₗ[R] F)` is invertible. -/
theorem isInvertible_restrict_map_of_isInvertible_coprod_domRestrict
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    (T.restrict (fun _ hx ↦ Submodule.mem_map_of_mem hx :
      Set.MapsTo T V (V.map (T : E →ₗ[R] F)))).IsInvertible :=
  ⟨domRestrictEquivMap hinv, toContinuousLinearMap_domRestrictEquivMap hinv⟩

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `V.map (T : E →ₗ[R] F)` and `W` are
topological complements in `F`. -/
theorem isTopCompl_map_of_isInvertible_coprod_domRestrict
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
theorem isClosed_map_of_isInvertible_coprod_domRestrict [T1Space W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    IsClosed (V.map (T : E →ₗ[R] F) : Set F) :=
  (isTopCompl_map_of_isInvertible_coprod_domRestrict hinv).isClosed

end TVS

/-! ### Dimension bounds, index, and Fredholmness in finite codimension -/

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible and `V` has finite codimension, then
`finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)`. -/
theorem finrank_ker_le_of_isInvertible_coprod_domRestrict [V.CoFG]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) := by
  refine (V.mkQ.domRestrict T.ker).finrank_le_finrank_of_injective ?_
  rw [LinearMap.injective_domRestrict_iff, Submodule.ker_mkQ]
  exact (disjoint_ker_of_isInvertible_coprod_domRestrict hinv).symm

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible and `W` is finite-dimensional, then
`finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W`. -/
theorem finrank_quotient_range_le_of_isInvertible_coprod_domRestrict [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W := by
  have hTop := isTopCompl_map_of_isInvertible_coprod_domRestrict hinv
  let e := (V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl
  refine ((Submodule.factor LinearMap.map_le_range).comp e.symm.toLinearMap)
    |>.finrank_le_finrank_of_surjective ?_
  exact (Submodule.factor_surjective LinearMap.map_le_range).comp e.symm.surjective

/-- If `V` has finite codimension, `W` is finite-dimensional, and
`(T.domRestrict V).coprod W.subtypeL` is invertible, then the index of `T` equals
`(finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W`. -/
theorem index_eq_of_isInvertible_coprod_domRestrict [V.CoFG] [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W := by
  have hdisj := disjoint_ker_of_isInvertible_coprod_domRestrict hinv
  have hTop := isTopCompl_map_of_isInvertible_coprod_domRestrict hinv
  let e := (V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl
  have : FiniteDimensional 𝕜 T.ker :=
    Module.Finite.of_injective (V.mkQ.domRestrict T.ker)
      (LinearMap.injective_domRestrict_iff.mpr (by simpa only [Submodule.ker_mkQ] using hdisj.symm))
  have : FiniteDimensional 𝕜 (F ⧸ V.map (T : E →ₗ[𝕜] F)) := e.symm.finiteDimensional
  have hle : V.map (T : E →ₗ[𝕜] F) ≤ T.range := LinearMap.map_le_range
  have : FiniteDimensional 𝕜 (F ⧸ T.range) :=
    Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : FiniteDimensional 𝕜 V.subtype.ker := by
    rw [Submodule.ker_subtype]
    infer_instance
  have : FiniteDimensional 𝕜 (E ⧸ V.subtype.range) := by
    rw [Submodule.range_subtype]
    infer_instance
  have hcomp := LinearMap.index_comp (T : E →ₗ[𝕜] F) V.subtype
  have hinj : Injective ((T : E →ₗ[𝕜] F) ∘ₗ V.subtype) :=
    LinearMap.injective_domRestrict_iff.mpr hdisj
  rw [LinearMap.index_of_injective hinj, LinearMap.range_comp, Submodule.range_subtype,
    LinearMap.index_subtype, e.finrank_eq, ← T.index_def] at hcomp
  omega

end DivisionRing

section FiniteCodimension

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  {T : E →L[𝕜] F} {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [T1Space W]

/-- **Fredholmness from an invertible finite-codimension transverse coproduct.** If `V` is closed
of finite codimension, `W` is `T₁` and finite-dimensional, and `(T.domRestrict V).coprod W.subtypeL`
is invertible, then `T` is Fredholm (and in particular has closed range). -/
theorem isFredholm_of_isInvertible_coprod_domRestrict
    (hV : IsClosed (V : Set E)) [V.CoFG] [FiniteDimensional 𝕜 W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    T.IsFredholm := by
  have hTop := isTopCompl_map_of_isInvertible_coprod_domRestrict hinv
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Module.Finite.equiv ((V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsCompl W hTop.isCompl).symm
  exact IsFredholm.of_isInvertible_restrict hV hTop.isClosed
    (fun _ hx ↦ Submodule.mem_map_of_mem hx)
    (isInvertible_restrict_map_of_isInvertible_coprod_domRestrict hinv)

end FiniteCodimension

/-! ### Basepoint and neighborhood invertibility on Banach spaces -/

section Banach

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[fun_prop]
theorem continuous_coprod_domRestrict (V : Submodule 𝕜 E) (W : Submodule 𝕜 F) :
    Continuous fun T : E →L[𝕜] F ↦ (T.domRestrict V).coprod W.subtypeL := by
  simp only [domRestrict]
  fun_prop

variable [CompleteSpace F]

/-- **Basepoint invertibility of a transverse restricted coproduct.** If `V` and `W` are complete,
`W` is an algebraic complement of `V.map (T₀ : E →ₗ[𝕜] F)` in a Banach space `F`, and
`Disjoint V T₀.ker`, then `(T₀.domRestrict V).coprod W.subtypeL : (V × W) →L[𝕜] F` is
invertible. -/
theorem isInvertible_coprod_domRestrict {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [CompleteSpace V] [CompleteSpace W]
    (hW : IsCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod W.subtypeL).IsInvertible := by
  refine ⟨(T₀.domRestrict V).coprodSubtypeLEquivOfIsCompl
    (by simpa [LinearMap.range_domRestrict] using hW)
    (by simpa [LinearMap.ker_domRestrict, Submodule.disjoint_iff_comap_eq_bot] using hdisj), ?_⟩
  rw [coprodSubtypeLEquivOfIsCompl, ContinuousLinearEquiv.coe_ofBijective]

/-- **Neighborhood invertibility of a transverse restricted coproduct.** Under the hypotheses of
`isInvertible_coprod_domRestrict`, `(T.domRestrict V).coprod W.subtypeL` remains invertible for all
`T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} {W : Submodule 𝕜 F} [CompleteSpace V] [CompleteSpace W]
    (hW : IsCompl (V.map (T₀ : E →ₗ[𝕜] F)) W) (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod W.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict V W).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict hW hdisj).eventually_nhds

end Banach

/-! ### Hilbert-target transverse coproducts -/

section HilbertCodomain

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- When `V` is complete, `T₀(V)` admits an orthogonal projection in `F`, and `Disjoint V T₀.ker`,
the Hilbert transverse coproduct `(T₀.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible. -/
theorem isInvertible_coprod_domRestrict_orthogonal {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  isInvertible_coprod_domRestrict (V.map (T₀ : E →ₗ[𝕜] F)).isCompl_orthogonal hdisj

/-- Under the hypotheses of `isInvertible_coprod_domRestrict_orthogonal`,
`(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible throughout a neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  eventually_nhds_isInvertible_coprod_domRestrict
    (V.map (T₀ : E →ₗ[𝕜] F)).isCompl_orthogonal hdisj

/-- Basepoint invertibility of `(T₀.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` for a
finite-dimensional subspace `V` disjoint from `ker T₀`. -/
theorem isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) := Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  have : CompleteSpace (V.map (T₀ : E →ₗ[𝕜] F)) := FiniteDimensional.completeSpace 𝕜 _
  exact isInvertible_coprod_domRestrict_orthogonal hdisj

/-- **Atiyah–Singer finite-dimensional transverse-subspace lemma.** If `V ≤ E` is
finite-dimensional and `Disjoint V T₀.ker`, then `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is
invertible for every `T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional
    {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E} [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict V _).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional hdisj).eventually_nhds

/-- Basepoint invertibility of `(T₀.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` when `V` is complete,
`T₀(V)` has finite codimension in `F`, and `Disjoint V T₀.ker` (closedness of `T₀(V)` is
automatic). -/
theorem isInvertible_coprod_domRestrict_orthogonal_of_coFG {T₀ : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).CoFG] (hdisj : Disjoint V T₀.ker) :
    ((T₀.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible := by
  have : FiniteDimensional 𝕜 (F ⧸ (T₀.domRestrict V).range) := by
    rw [toLinearMap_domRestrict, LinearMap.range_domRestrict]
    infer_instance
  have hMapClosed : IsClosed (V.map (T₀ : E →ₗ[𝕜] F) : Set F) := by
    rw [← LinearMap.range_domRestrict, ← toLinearMap_domRestrict]
    exact (T₀.domRestrict V).isClosed_range_of_finite_coker
  let : CompleteSpace (V.map (T₀ : E →ₗ[𝕜] F)) := hMapClosed.isComplete.completeSpace_coe
  exact isInvertible_coprod_domRestrict_orthogonal hdisj

/-- **Finite-codimension transverse-subspace stability.** If `V ≤ E` is complete, `T₀(V)` has
finite codimension in the Hilbert space `F`, and `Disjoint V T₀.ker`, then
`(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL` is invertible for all `T` near `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_coFG {T₀ : E →L[𝕜] F}
    {V : Submodule 𝕜 E} [CompleteSpace V] [(V.map (T₀ : E →ₗ[𝕜] F)).CoFG]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict V).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict V _).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict_orthogonal_of_coFG hdisj).eventually_nhds

end HilbertCodomain

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- For a closed-range operator `T₀ : E →L[𝕜] F` between Hilbert spaces, the restricted coproduct
`(T₀.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL` is invertible. -/
theorem isInvertible_coprod_domRestrict_orthogonal_ker {T₀ : E →L[𝕜] F}
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ((T₀.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL).IsInvertible := by
  let : CompleteSpace T₀.range := hT₀.isComplete.completeSpace_coe
  have hCompl : IsCompl (T₀.kerᗮ.map (T₀ : E →ₗ[𝕜] F)) (T₀†).ker := by
    rw [LinearMap.map_orthogonal_ker_eq_range, ← T₀.orthogonal_range]
    exact T₀.range.isCompl_orthogonal
  exact isInvertible_coprod_domRestrict hCompl T₀.ker.isCompl_orthogonal.symm.disjoint

/-- **Orthogonal-kernel transverse coproduct stability.** For any closed-range operator
`T₀ : E →L[𝕜] F` between Hilbert spaces (in particular any Fredholm operator via
`IsFredholm.isClosed_range`), `(T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL` remains
invertible for every `T` in an operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker {T₀ : E →L[𝕜] F}
    (hT₀ : IsClosed (T₀.range : Set F)) :
    ∀ᶠ T in 𝓝 T₀, ((T.domRestrict T₀.kerᗮ).coprod (T₀†).ker.subtypeL).IsInvertible :=
  (continuous_coprod_domRestrict T₀.kerᗮ (T₀†).ker).tendsto T₀ |>.eventually
    (isInvertible_coprod_domRestrict_orthogonal_ker hT₀).eventually_nhds

end Hilbert

end ContinuousLinearMap

end
