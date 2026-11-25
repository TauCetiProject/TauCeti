/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Fredholm.Restriction
public import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The transverse-subspace lemma

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
`W = (V.map T₀)ᗮ` whenever `V.map T₀` is closed, through `Submodule.isTopCompl_orthogonal`; this
covers in particular every finite-dimensional `V` with `V ⊓ ker T₀ = ⊥`.

## Main results

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

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. **87** (1968),
  484–530, pp. 519–520.
-/

public section

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
