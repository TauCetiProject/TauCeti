/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import TauCeti.Analysis.Fredholm.Restriction
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.InnerProductSpace.QuotientRange
import TauCeti.Analysis.Normed.Operator.QuotientRange

/-!
# Transverse subspaces, coproduct stability, and Fredholm defect bounds

Let `T₀ : E →L[𝕜] F` be a continuous linear operator and let `V ≤ E` be a complete subspace
transverse to `ker T₀` (`Disjoint V T₀.ker`) whose image `T₀(V)` admits a complete algebraic
complement `W ≤ F` in a Banach space `F` — for instance `W = (T₀(V))ᗮ` whenever `F` is a Hilbert
space and `T₀(V)` is closed. The general restricted-coproduct API for
`(T.domRestrict V).coprod W.subtypeL : (V × W) →L[𝕜] F` lives below Fredholm theory:

* Pointwise algebraic and topological consequences
  (`disjoint_ker_of_isInvertible_coprod_domRestrict`, `domRestrictEquivMap`,
  `isInvertible_restrict_map_of_isInvertible_coprod_domRestrict`,
  `isTopCompl_map_of_isInvertible_coprod_domRestrict`,
  `isClosed_map_of_isInvertible_coprod_domRestrict`) live in
  `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange`.
* Continuity, Banach-space basepoint invertibility, and neighborhood stability
  (`continuous_coprod_domRestrict`, `isInvertible_coprod_domRestrict`,
  `eventually_nhds_isInvertible_coprod_domRestrict`) live in
  `TauCeti.Analysis.Normed.Operator.QuotientRange`.
* Hilbert-space orthogonal specializations — the general orthogonal coproduct
  (`isInvertible_coprod_domRestrict_orthogonal`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal`), the Atiyah–Singer
  finite-dimensional transverse-subspace lemma
  (`isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_finiteDimensional`), and the
  closed-range orthogonal-kernel specialization (`isInvertible_coprod_domRestrict_orthogonal_ker`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_ker`) — live in
  `TauCeti.Analysis.InnerProductSpace.QuotientRange`.

This file develops the Fredholm and Banach transverse-subspace consequences:

1. **Finite-codimension `V` (`[V.CoFG]`, `[FiniteDimensional 𝕜 W]`)**: invertibility of
   `(T.domRestrict V).coprod W.subtypeL` implies the dimension bounds
   `finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)` and `finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 W`, the index
   formula `T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 W`, and — when `V` is closed in a
   topological vector space over a complete scalar field — `T.IsFredholm`.
2. **Banach `IsTopCompl` characterization and neighborhood stability**: when `E` and `F` are Banach
   spaces and `V ≤ E` is closed, `(T ∘L V.subtypeL).coprod W.subtypeL` is invertible if and only if
   `Disjoint V T.ker` and `IsTopCompl (V.map T) W` (`isInvertible_comp_subtypeL_coprod_iff`), so
   both conditions, Fredholmness, defect bounds, and index equality persist in an operator-norm
   neighborhood of `T₀` (`eventually_disjoint_ker_and_isTopCompl_map`,
   `eventually_isFredholm_and_index_eq_of_isTopCompl_map`,
   `eventually_finrank_ker_sub_finrank_ker_eq_of_isTopCompl_map`).
3. **Finite-codimension image in a Hilbert target (`[(V.map T₀).CoFG]`)**: completeness of `V` and
   finite codimension of `T₀(V)` automatically force `T₀(V)` to be closed via
   `ContinuousLinearMap.isClosed_range_of_finite_coker`, yielding basepoint invertibility and
   neighborhood stability of `(T.domRestrict V).coprod (T₀(V))ᗮ.subtypeL`
   (`isInvertible_coprod_domRestrict_orthogonal_of_coFG`,
   `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_coFG`).

## Main declarations

In `ContinuousLinearMap`:

* `finrank_ker_le_of_isInvertible_coprod_domRestrict`,
  `finrank_quotient_range_le_of_isInvertible_coprod_domRestrict`,
  `index_eq_of_isInvertible_coprod_domRestrict`,
  `isFredholm_of_isInvertible_coprod_domRestrict`: defect bounds, index formula, and Fredholmness
  from an invertible finite-codimension transverse coproduct.
* `isInvertible_comp_subtypeL_coprod_iff`,
  `eventually_disjoint_ker_and_isTopCompl_map`,
  `isFredholm_of_disjoint_ker_of_isTopCompl_map`,
  `index_eq_of_disjoint_ker_of_isTopCompl_map`,
  `eventually_isFredholm_and_index_eq_of_isTopCompl_map`,
  `eventually_finrank_ker_sub_finrank_ker_eq_of_isTopCompl_map`: Banach-space `IsTopCompl`
  characterization and Atiyah–Singer transverse-subspace stability.
* `isInvertible_coprod_domRestrict_orthogonal_of_coFG`,
  `eventually_nhds_isInvertible_coprod_domRestrict_orthogonal_of_coFG`: basepoint invertibility and
  neighborhood stability of the orthogonal restricted coproduct when `T₀(V)` has finite codimension
  in a Hilbert space `F`.

## References

* M. F. Atiyah, I. M. Singer, *The Index of Elliptic Operators: I*, Annals of Mathematics **87**
  (1968), 484–530, §6, pp. 519–520.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1.
-/

public section

open Filter Function Module Submodule Topology

namespace ContinuousLinearMap

/-! ### Dimension bounds, index, and Fredholmness in finite codimension -/

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
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

/-! ### Banach `IsTopCompl` characterization and stability -/

section Banach

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
  change ((T.domRestrict V).coprod W.subtypeL).IsInvertible ↔ _
  refine ⟨fun h ↦ ⟨disjoint_ker_of_isInvertible_coprod_domRestrict h,
      isTopCompl_map_of_isInvertible_coprod_domRestrict h⟩, fun ⟨hker, hW⟩ ↦ ?_⟩
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  exact isInvertible_coprod_domRestrict hW.isCompl hker

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
  filter_upwards [eventually_nhds_isInvertible_coprod_domRestrict hW.isCompl hker] with T hT
  exact (isInvertible_comp_subtypeL_coprod_iff hV).mp hT

section BanachFredholm

variable [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]

/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then `T` is Fredholm. -/
theorem isFredholm_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.IsFredholm :=
  isFredholm_of_isInvertible_coprod_domRestrict hV
    ((isInvertible_comp_subtypeL_coprod_iff hV).mpr ⟨hker, hW⟩)

omit [CompleteSpace 𝕜] in
/-- If `T` is injective on a closed finite-codimensional subspace `V` and `T(V)` has a
finite-dimensional topological complement `W`, then the index of `T` is `codim V - dim W`. -/
theorem index_eq_of_disjoint_ker_of_isTopCompl_map (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 W] (hker : Disjoint V T.ker)
    (hW : IsTopCompl (V.map (T : E →ₗ[𝕜] F)) W) :
    T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 W :=
  index_eq_of_isInvertible_coprod_domRestrict
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
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  have : CompleteSpace W := hW.isClosed'.isComplete.completeSpace_coe
  filter_upwards [eventually_nhds_isInvertible_coprod_domRestrict hW.isCompl hker] with T hT
  exact ⟨isFredholm_of_isInvertible_coprod_domRestrict hV hT,
    finrank_ker_le_of_isInvertible_coprod_domRestrict hT,
    finrank_quotient_range_le_of_isInvertible_coprod_domRestrict hT,
    index_eq_of_isInvertible_coprod_domRestrict hT⟩

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
  omega

end BanachFredholm

end Banach

/-! ### Finite-codimension orthogonal coproducts -/

section HilbertCodomain

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

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

end ContinuousLinearMap
