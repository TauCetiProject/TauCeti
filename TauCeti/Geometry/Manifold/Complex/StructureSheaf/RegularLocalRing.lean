/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MaximalIdeal
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison

import Mathlib.Algebra.Module.SpanRankOperations
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dimension
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Regularity and Krull dimension of holomorphic stalks

Let `X` be a finite-dimensional complex manifold without boundary modelled on `E`. The stalk
`𝒪_{X, x}` of the holomorphic structure sheaf at any point `x : X` is a regular local ring of
Krull dimension `Module.finrank ℂ E`.

On a finite-dimensional model space `V : Type`, the stalk `𝒪_{V, v}` is Noetherian
(`TauCeti.holomorphicStructureSheaf.stalkIsNoetherianRing`), its cotangent space has dimension
`Module.finrank ℂ V` (`OpenPartialHomeomorph.finrank_cotangentSpace_holomorphicStalk`), so its
maximal ideal has minimal generator count `Module.finrank ℂ V`, and its Krull dimension is at least
`Module.finrank ℂ V` (`TauCeti.holomorphicStructureSheaf.finrank_le_ringKrullDim_stalk_modelSpace`).
Mathlib's `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` (which uses Krull's height theorem)
therefore makes `𝒪_{V, v}` a regular local ring of Krull dimension `Module.finrank ℂ V`.

Composing an extended chart with a continuous linear equivalence `E ≃L[ℂ] (Fin n → ℂ)` identifies
the stalk at `x` of any complex manifold (with model `E` in any universe) with a stalk on
`Fin n → ℂ` (`TauCeti.holomorphicStructureSheaf.stalkPullback_comp_extChartAt_bijective`),
transporting regularity, Krull dimension, maximal-ideal `spanFinrank`, and cotangent dimension to
`holomorphicStructureSheaf I X`, and via `smoothStalkIso` to Mathlib's `smoothSheafCommRing`.

In any holomorphic chart `e` at `x` on a manifold modelled on `𝓘(ℂ, E)`, the centered linear
coordinate germs along any basis of `E` generate the maximal ideal in `Module.finrank ℂ E` elements
and hence form a regular system of parameters; in particular, any duplicate-free list of centered
coordinate germs forms a regular sequence on `𝒪_{X, x}`
(`OpenPartialHomeomorph.isRegular_map_holomorphicLinearCoordinateGerm`).

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkIsRegularLocalRing`: holomorphic stalks are regular local
  rings.
* `TauCeti.holomorphicStructureSheaf.ringKrullDim_stalk`: the Krull dimension of a holomorphic
  stalk equals `Module.finrank ℂ E`.
* `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_stalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_stalk`: the minimal number of
  generators of the maximal ideal and the embedding dimension equal `Module.finrank ℂ E`.
* `TauCeti.holomorphicStructureSheaf.smoothStalkIsRegularLocalRing`,
  `TauCeti.holomorphicStructureSheaf.ringKrullDim_smoothStalk`,
  `TauCeti.holomorphicStructureSheaf.spanFinrank_maximalIdeal_smoothStalk`,
  `TauCeti.holomorphicStructureSheaf.finrank_cotangentSpace_smoothStalk`: the corresponding results
  for Mathlib's complex-smooth structure sheaf.
* `OpenPartialHomeomorph.isRegular_map_holomorphicLinearCoordinateGerm`,
  `OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`: any duplicate-free tuple
  of centered coordinate germs of a holomorphic chart along a basis forms a regular sequence on
  `𝒪_{X, x}`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §2.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open Filter IsManifold Module Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section ModelSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- On a finite-dimensional complex normed space, the minimal number of generators of the maximal
ideal of a holomorphic stalk equals the complex dimension of the space. -/
private theorem spanFinrank_maximalIdeal_stalk_modelSpace (v : V) :
    (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v)).spanFinrank
      = finrank ℂ V := by
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact (chartAt V v).finrank_cotangentSpace_holomorphicStalk v (mem_chart_source V v)
    (chart_mem_maximalAtlas v)

/-- On a finite-dimensional complex normed space, every holomorphic stalk is a regular local
ring. -/
private theorem isRegularLocalRing_stalk_modelSpace (v : V) :
    IsRegularLocalRing ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v) := by
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [spanFinrank_maximalIdeal_stalk_modelSpace]
  exact finrank_le_ringKrullDim_stalk_modelSpace v

/-- On a finite-dimensional complex normed space, the Krull dimension of every holomorphic stalk
equals the complex dimension of the space. -/
private theorem ringKrullDim_stalk_modelSpace (v : V) :
    ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk v) = finrank ℂ V := by
  have := isRegularLocalRing_stalk_modelSpace v
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, spanFinrank_maximalIdeal_stalk_modelSpace]

end ModelSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a regular local ring. -/
instance stalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have := isRegularLocalRing_stalk_modelSpace ((e ∘ extChartAt I x) x)
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective (I := I) x e))

/-- The Krull dimension of the holomorphic stalk at any point of a finite-dimensional complex
manifold without boundary equals the complex dimension of its model space. -/
theorem ringKrullDim_stalk (x : X) :
    ringKrullDim ((holomorphicStructureSheaf I X).presheaf.stalk x) = finrank ℂ E := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have h := ringKrullDim_eq_of_ringEquiv
    (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective (I := I) x e))
  rw [← h, ringKrullDim_stalk_modelSpace, finrank_pi]
  simp

/-- The minimal number of generators of the maximal ideal of a holomorphic stalk equals the complex
dimension of the manifold model. -/
theorem spanFinrank_maximalIdeal_stalk (x : X) :
    (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x)).spanFinrank =
      finrank ℂ E := by
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (holomorphicStructureSheaf I X).presheaf.stalk x)).trans (ringKrullDim_stalk x)

/-- The embedding dimension of a holomorphic stalk on any finite-dimensional complex manifold
without boundary equals the complex dimension of its model space. -/
theorem finrank_cotangentSpace_stalk (x : X) :
    finrank (IsLocalRing.ResidueField ((holomorphicStructureSheaf I X).presheaf.stalk x))
        (IsLocalRing.CotangentSpace ((holomorphicStructureSheaf I X).presheaf.stalk x)) =
      finrank ℂ E := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_stalk x

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a regular local ring, via its comparison with holomorphic germs. -/
instance smoothStalkIsRegularLocalRing (x : X) :
    IsRegularLocalRing ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (smoothStalkIso I X x).commRingCatIsoToRingEquiv

/-- The Krull dimension of a stalk of Mathlib's complex-smooth structure sheaf on a
finite-dimensional complex manifold without boundary equals the complex dimension of its model. -/
theorem ringKrullDim_smoothStalk (x : X) :
    ringKrullDim ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) = finrank ℂ E := by
  rw [← (smoothStalkIso I X x).commRingCatIsoToRingEquiv.ringKrullDim]
  exact ringKrullDim_stalk x

/-- The minimal number of generators of the maximal ideal of a stalk of Mathlib's complex-smooth
structure sheaf equals the complex dimension of its model. -/
theorem spanFinrank_maximalIdeal_smoothStalk (x : X) :
    (IsLocalRing.maximalIdeal ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).spanFinrank =
      finrank ℂ E := by
  exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)).trans (ringKrullDim_smoothStalk x)

/-- The embedding dimension of a stalk of Mathlib's complex-smooth structure sheaf equals the
complex dimension of its model. -/
theorem finrank_cotangentSpace_smoothStalk (x : X) :
    finrank (IsLocalRing.ResidueField ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x))
        (IsLocalRing.CotangentSpace ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x)) =
      finrank ℂ E := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_smoothStalk x

end Manifold

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X)

omit [FiniteDimensional ℂ E] in
include he in
/-- Pullback along a holomorphic chart followed by a continuous linear equivalence to a normed
space in `Type` identifies the stalk at a point of the chart source with a model-space stalk. -/
private theorem stalkPullback_comp_chart_bijective {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {x : X} (hx : x ∈ e.source) (L : E ≃L[ℂ] V) :
    Function.Bijective (stalkPullback (I := 𝓘(ℂ, E)) (J := 𝓘(ℂ, V)) (f := L ∘ e) (a := x)
      (by
        filter_upwards [e.open_source.mem_nhds hx] with y hy
        exact L.contDiff.contMDiff.contMDiffAt.comp y
          (contMDiffAt_of_mem_maximalAtlas he hy))) := by
  have hmem : ∀ᶠ z in 𝓝 (L (e x)), L.symm z ∈ e.target := by
    have h := L.symm.continuous.tendsto (L (e x))
    rw [L.symm_apply_apply] at h
    exact h.eventually (e.open_target.mem_nhds (e.map_source hx))
  refine stalkPullback_bijective _ (g := e.symm ∘ L.symm) ?_ ?_ ?_
  · filter_upwards [hmem] with z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas he hz).comp z
      L.symm.contDiff.contMDiff.contMDiffAt
  · filter_upwards [e.open_source.mem_nhds hx] with y hy
    simpa using e.left_inv hy
  · filter_upwards [hmem] with z hz
    simp only [Function.comp_apply, e.right_inv hz, ContinuousLinearEquiv.apply_symm_apply]

include he in
/-- The holomorphic stalk at any point in the domain of a holomorphic chart is a regular local
ring, with no global manifold assumption beyond the chart itself. -/
theorem isRegularLocalRing_holomorphicStalk {x : X} (hx : x ∈ e.source) :
    IsRegularLocalRing ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
  let L : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have := stalkIsRegularLocalRing (I := 𝓘(ℂ, Fin (finrank ℂ E) → ℂ)) (L (e x))
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (e.stalkPullback_comp_chart_bijective he hx L))

include he in
/-- The Krull dimension of the holomorphic stalk at any point in the domain of a holomorphic chart
equals `Module.finrank ℂ E`. -/
theorem ringKrullDim_holomorphicStalk {x : X} (hx : x ∈ e.source) :
    ringKrullDim ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) = finrank ℂ E := by
  let L : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have h := ringKrullDim_eq_of_ringEquiv
    (RingEquiv.ofBijective _ (e.stalkPullback_comp_chart_bijective he hx L))
  rw [← h, ringKrullDim_stalk, finrank_pi]
  simp

/-- **Centered local coordinates form a regular sequence.** For any holomorphic chart `e` at `x`,
any basis `b` of `E`, and any duplicate-free list `l` of indices of `b`, the centered linear
coordinate germs `y ↦ b.coord i (e y - e x)` along `l` form a regular sequence on `𝒪_{X, x}`. -/
theorem isRegular_map_holomorphicLinearCoordinateGerm {ι : Type*} (b : Basis ι ℂ E) {x : X}
    (hx : x ∈ e.source) {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (l.map fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  classical
  have := e.isRegularLocalRing_holomorphicStalk he hx
  have := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  let z : ι → (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x :=
    fun i ↦ e.holomorphicLinearCoordinateGerm he x
      (LinearMap.toContinuousLinearMap (b.coord i)) hx
  -- Extend `l` by the remaining basis indices to a duplicate-free listing of all of `ι`.
  let l' : List ι := (Finset.univ \ l.toFinset).toList
  have hmem : ∀ i : ι, i ∈ l ++ l' := fun i ↦ by
    by_cases hi : i ∈ l
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (by simp [l', hi])
  have hnodup : (l ++ l').Nodup :=
    List.nodup_append.2 ⟨hl, Finset.nodup_toList _, fun i hi j hj hij ↦ by
      simp [l', hij ▸ hi] at hj⟩
  have hspan : Ideal.ofList ((l ++ l').map z) =
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
    rw [maximalIdeal_stalk, e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx]
    dsimp only [Ideal.ofList]
    congr 1
    ext s
    simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range, z]
    exact ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, hmem i, hi⟩⟩
  have hlen : ((l ++ l').map z).length ≤
      (IsLocalRing.maximalIdeal
        ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank := by
    have hcard : (l ++ l').length = finrank ℂ E := by
      rw [finrank_eq_card_basis b, ← List.toFinset_card_of_nodup hnodup]
      congr 1
      ext i
      simpa using hmem i
    have hrank : (IsLocalRing.maximalIdeal
        ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank = finrank ℂ E := by
      exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal
        (R := (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).trans
        (e.ringKrullDim_holomorphicStalk he hx)
    rw [List.length_map, hcard, hrank]
  have hfull := TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal hspan hlen
  rw [List.map_append] at hfull
  refine ⟨((RingTheory.Sequence.isWeaklyRegular_append_iff _ _ _).1 hfull.toIsWeaklyRegular).1,
    fun htop ↦ hfull.top_ne_smul ?_⟩
  exact (top_le_iff.1 (htop.le.trans (Submodule.smul_mono_left
    (by rw [Ideal.ofList_append]; exact le_sup_left)))).symm

/-- The centered coordinate germs along a `Fin n`-indexed basis of `E` form a regular sequence on
the holomorphic stalk. -/
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm {n : ℕ} (b : Basis (Fin n) ℂ E) {x : X}
    (hx : x ∈ e.source) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  rw [List.ofFn_eq_map]
  exact e.isRegular_map_holomorphicLinearCoordinateGerm he b hx (List.nodup_finRange n)

end OpenPartialHomeomorph
