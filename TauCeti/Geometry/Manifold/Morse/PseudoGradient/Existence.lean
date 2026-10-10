/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic

/-!
# Existence of adapted pseudo-gradients

Every Morse function on a compact boundaryless manifold, modelled on a finite-dimensional real
normed space, has a pseudo-gradient field adapted to it
(`TauCeti.IsMorse.exists_isAdaptedPseudoGradient`).

The proof follows Audin and Damian. Near each critical point the field is the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` of a Morse chart, pulled back to the manifold (`TauCeti.MorseChart.field`). Near a
regular point it is a constant field in a chart, chosen in a direction in which `f` decreases
(`TauCeti.chartConstField`). These local fields are glued by Mathlib's
partition-of-unity theorem for sections with values in fibrewise convex sets,
`exists_contMDiffSection_forall_mem_convex_of_local`. The convex set at a point asks for
`df(X) < 0` if the point is regular, and for equality with the Morse field if the point lies in a
closed neighbourhood of a critical point. These neighbourhoods are chosen pairwise disjoint, which
is possible because a Morse function on a compact manifold has finitely many critical points
(`TauCeti.IsMorse.finite_setOf_mfderiv_eq_zero`).

## Main declarations

* `TauCeti.MorseChart.field`: the linear field of a Morse chart, on the manifold, with
  `TauCeti.MorseChart.mvfderiv_field_apply_lt_zero` and `TauCeti.MorseChart.mfderiv_eq_zero_iff`.
* `TauCeti.IsMorse.finite_setOf_mfderiv_eq_zero`: finiteness of the critical set.
* `TauCeti.IsMorse.exists_isAdaptedPseudoGradient`: existence of adapted pseudo-gradients.

The chart calculus used here is general and lives in
`TauCeti/Geometry/Manifold/MFDeriv/ModelChart.lean` and
`TauCeti/Geometry/Manifold/VectorField/ModelChart.lean`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.2.3 and its proof.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

section MorseChartField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] {x : M}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The quadratic normal form of a Morse chart, as a function on the model space. -/
noncomputable def quadratic (z : E) : ℝ :=
  f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * (φ.coord z i) ^ 2

/-- The negative gradient `z ↦ L⁻¹ (-(wᵢ (L z)ᵢ)ᵢ)` of the quadratic normal form, read in the
coordinates of the Morse chart. -/
noncomputable def linearField (z : E) : E :=
  φ.coord.symm fun i ↦ -(φ.weight i * φ.coord z i)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- On the source of a Morse chart, `f` is the quadratic normal form read in the chart. -/
theorem eqOn_quadratic : EqOn f (φ.quadratic ∘ φ.toChart) φ.toChart.source := fun y hy ↦ by
  simp only [comp_apply, quadratic]
  exact φ.eq_quadratic y hy

/-- The coordinate change of a Morse chart, as a continuous linear equivalence. -/
noncomputable def coordL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  φ.coord.toContinuousLinearEquiv

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `coordL` is `coord`. -/
@[simp]
theorem coordL_apply (z : E) : φ.coordL z = φ.coord z := by
  simp [coordL]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form. -/
theorem hasFDerivAt_quadratic (z : E) :
    HasFDerivAt φ.quadratic
      ((∑ i, (φ.weight i * φ.coord z i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
          (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))) z := by
  have h := (hasFDerivAt_diagonalQuadratic (f x) φ.weight (φ.coordL z)).comp z
    φ.coordL.hasFDerivAt
  convert h using 1
  · ext v
    simp [quadratic, sq]
  · simp

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form is `v ↦ Σᵢ wᵢ (L z)ᵢ (L v)ᵢ`. -/
theorem fderiv_quadratic_apply (z v : E) :
    fderiv ℝ φ.quadratic z v = ∑ i, φ.weight i * φ.coord z i * φ.coord v i := by
  rw [(φ.hasFDerivAt_quadratic z).fderiv]
  simp

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The quadratic normal form is differentiable. -/
theorem differentiableAt_quadratic (z : E) : DifferentiableAt ℝ φ.quadratic z :=
  (φ.hasFDerivAt_quadratic z).differentiableAt

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The quadratic normal form has a single critical point, the origin. -/
theorem fderiv_quadratic_eq_zero_iff {z : E} : fderiv ℝ φ.quadratic z = 0 ↔ z = 0 := by
  constructor
  · intro h0
    have hz : φ.coord z = 0 := by
      ext i
      have := congrArg (fun T : E →L[ℝ] ℝ ↦ T (φ.coord.symm (Pi.single i (φ.weight i))))
        h0
      simp only [fderiv_quadratic_apply, LinearEquiv.apply_symm_apply,
        zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
      simp only [Pi.single_eq_same] at this
      rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] at this <;> simpa using this
    simpa using congrArg φ.coord.symm hz
  · rintro rfl
    ext v
    simp [fderiv_quadratic_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the quadratic normal form along the linear field is `-Σᵢ (L z)ᵢ²`. -/
theorem fderiv_quadratic_linearField (z : E) :
    fderiv ℝ φ.quadratic z (φ.linearField z) = -∑ i, (φ.coord z i) ^ 2 := by
  rw [fderiv_quadratic_apply]
  simp only [linearField, LinearEquiv.apply_symm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases φ.weight_eq_neg_one_or_eq_one i with hw | hw <;> rw [hw] <;> ring

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The linear field of a Morse chart is smooth. -/
theorem contDiff_linearField : ContDiff ℝ ∞ φ.linearField := by
  have h1 : ContDiff ℝ ∞ (fun z : E ↦ fun i ↦ -(φ.weight i * φ.coordL z i)) :=
    contDiff_pi.2 fun i ↦
      (contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp φ.coordL.contDiff)).neg
  have : φ.linearField = φ.coordL.symm ∘ fun z i ↦ -(φ.weight i * φ.coordL z i) := by
    ext z
    simp [linearField, coordL]
  rw [this]
  exact φ.coordL.symm.contDiff.comp h1

/-- The linear field of a Morse chart, as a vector field on the model space. -/
noncomputable def linearVectorField : (z : E) → TangentSpace 𝓘(ℝ, E) z := φ.linearField

/-- The pullback to the manifold of the linear field of a Morse chart. -/
noncomputable def field : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart φ.linearVectorField

/-- The field of a Morse chart is smooth on the source of the chart. -/
theorem contMDiffOn_field :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, φ.field y⟩ : TangentBundle 𝓘(ℝ, E) M)) φ.toChart.source :=
  contMDiffOn_mpullback φ.mem_maximalAtlas φ.contDiff_linearField.contDiffOn

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Restricting a Morse chart to an open neighbourhood of its centre does not change its field. -/
@[simp]
theorem restr_field {s : Set M} (hs : IsOpen s) (hx : x ∈ s) : (φ.restr hs hx).field = φ.field := by
  have hlin : (φ.restr hs hx).linearField = φ.linearField := by
    ext z
    simp only [linearField, restr_coord, restr_weight]
  rw [field, field, linearVectorField, linearVectorField, hlin, restr_toChart,
    OpenPartialHomeomorph.restr_apply]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- In the coordinates of the Morse chart, the field is `z ↦ (-wᵢ zᵢ)ᵢ`. -/
theorem coord_mfderiv_field {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (φ.field y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [field, mfderiv_mpullback_apply φ.mem_maximalAtlas _ hy]
  simp [linearVectorField, linearField]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of `f` along the field of a Morse chart is `-Σᵢ (L (ψ y))ᵢ²`. -/
theorem mvfderiv_field_apply {y : M} (hy : y ∈ φ.toChart.source) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) = -∑ i, (φ.coord (φ.toChart y) i) ^ 2 := by
  rw [field, mvfderiv_mpullback_apply φ.mem_maximalAtlas φ.eqOn_quadratic _ hy
    (φ.differentiableAt_quadratic _)]
  exact φ.fderiv_quadratic_linearField _

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The centre is the only point of the source sent to `0`. -/
theorem toChart_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) : φ.toChart y = 0 ↔ y = x := by
  refine ⟨fun h ↦ φ.toChart.injOn hy φ.mem_source ?_, fun h ↦ h ▸ φ.apply_self⟩
  rw [h, φ.apply_self]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `f` strictly decreases along the field away from the centre of the chart. -/
theorem mvfderiv_field_apply_lt_zero {y : M} (hy : y ∈ φ.toChart.source) (hyx : y ≠ x) :
    mvfderiv 𝓘(ℝ, E) f y (φ.field y) < 0 := by
  rw [φ.mvfderiv_field_apply hy, neg_lt_zero]
  have hne : φ.coord (φ.toChart y) ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff, φ.toChart_eq_zero_iff hy]
    exact hyx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
    ⟨i, Finset.mem_univ _, by simpa using (sq_pos_of_ne_zero hi : (0 : ℝ) < _)⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The centre is the only critical point of `f` in the source of a Morse chart. -/
theorem mfderiv_eq_zero_iff {y : M} (hy : y ∈ φ.toChart.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ y = x := by
  rw [mfderiv_eq_zero_iff_of_eqOn φ.mem_maximalAtlas φ.eqOn_quadratic hy
    (φ.differentiableAt_quadratic _), φ.fderiv_quadratic_eq_zero_iff, φ.toChart_eq_zero_iff hy]

end MorseChart

end MorseChartField

section Existence

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **A Morse function on a compact manifold has finitely many critical points.** They form a
closed set, each of them is isolated by its Morse chart, and a closed discrete subset of a compact
space is finite. -/
theorem IsMorse.finite_setOf_mfderiv_eq_zero [CompactSpace M] (hf : IsMorse 𝓘(ℝ, E) f) :
    {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0}.Finite := by
  have hclosed : IsClosed {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0} := by
    have := (isOpen_setOf_mfderiv_ne_zero hf.contMDiff).isClosed_compl
    simpa only [compl_ofPred, ne_eq, not_not] using this
  refine hclosed.isCompact.finite (isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx ↦ ?_)
  obtain ⟨φ⟩ := hf.nonempty_morseChart hx
  refine ⟨φ.toChart.source, φ.toChart.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    exact (φ.mfderiv_eq_zero_iff hy).1 hyc
  · rintro rfl
    exact ⟨φ.mem_source, hx⟩

/-- **Existence of adapted pseudo-gradients** (Audin--Damian, Proposition 2.2.3). Every Morse
function on a compact manifold has a pseudo-gradient field adapted to it. -/
theorem IsMorse.exists_isAdaptedPseudoGradient [CompactSpace M] [T2Space M]
    (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x, IsAdaptedPseudoGradient f X := by
  classical
  set C := {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0}
  have hC : C.Finite := hf.finite_setOf_mfderiv_eq_zero
  let φ : ∀ x ∈ C, MorseChart E f x := fun x hx ↦ (hf.nonempty_morseChart hx).some
  obtain ⟨W, hW, hWdisj⟩ := hC.t2_separation
  have hK : ∀ x (hx : x ∈ C), ∃ K, K ∈ 𝓝 x ∧ IsClosed K ∧ K ⊆ (φ x hx).toChart.source ∩ W x :=
    fun x hx ↦ exists_mem_nhds_isClosed_subset
      (Filter.inter_mem ((φ x hx).toChart.open_source.mem_nhds (φ x hx).mem_source)
        ((hW x).2.mem_nhds (hW x).1))
  choose K hKn hKc hKsub using hK
  let K' : M → Set M := fun x ↦ if hx : x ∈ C then K x hx else ∅
  have hK' : ∀ x (hx : x ∈ C), K' x = K x hx := fun x hx ↦ by simp [K', hx]
  let ℓ : (y : M) → (TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) := fun y ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y
  let t : (y : M) → Set (TangentSpace 𝓘(ℝ, E) y) := fun y ↦
    {v | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} ∩
      ⋂ x, ⋂ (hx : x ∈ C), ⋂ (_ : y ∈ K x hx), {(φ x hx).field y}
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    refine Convex.inter ?_ (convex_iInter fun x ↦ convex_iInter fun hx ↦
      convex_iInter fun _ ↦ convex_singleton _)
    by_cases hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0
    · have : {v : TangentSpace 𝓘(ℝ, E) y | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} = univ := by
        ext v
        simp [hy]
      rw [this]
      exact convex_univ
    · have : {v : TangentSpace 𝓘(ℝ, E) y | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 → ℓ y v < 0} =
          {v | ℓ y v < 0} := by
        ext v
        simp [hy]
      rw [this]
      exact convex_halfSpace_lt (ℓ y).isLinear (0 : ℝ)
  have hloc : ∀ y₀ : M, ∃ U ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧ ∀ y ∈ U, s y ∈ t y := by
    intro y₀
    by_cases h : ∃ x, ∃ hx : x ∈ C, y₀ ∈ K x hx
    · obtain ⟨x, hx, hy₀⟩ := h
      have hUo : IsOpen ((φ x hx).toChart.source ∩ W x) :=
        (φ x hx).toChart.open_source.inter (hW x).2
      refine ⟨_, hUo.mem_nhds (hKsub x hx hy₀), (φ x hx).field,
        (φ x hx).contMDiffOn_field.mono inter_subset_left, fun y hy ↦ ⟨fun hcrit ↦ ?_, ?_⟩⟩
      · have hyx : y ≠ x := by
          rintro rfl
          exact hcrit hx
        exact (φ x hx).mvfderiv_field_apply_lt_zero hy.1 hyx
      · simp only [mem_iInter, mem_singleton_iff]
        intro x' hx' hy'
        have hxx' : x = x' := by
          by_contra hne
          exact Set.disjoint_left.1 (hWdisj hx hx' hne) hy.2 ((hKsub x' hx' hy').2)
        subst hxx'
        rfl
    · simp only [not_exists] at h
      have hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0 := fun h0 ↦
        h y₀ h0 (mem_of_mem_nhds (hKn y₀ h0))
      obtain ⟨v, U, hU, hUc, hUneg⟩ :=
        exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf.contMDiff hcrit
      have hclosed : IsClosed (⋃ x ∈ C, K' x) :=
        hC.isClosed_biUnion fun x hx ↦ by rw [hK' x hx]; exact hKc x hx
      have hy₀K : y₀ ∈ (⋃ x ∈ C, K' x)ᶜ := by
        simp only [mem_compl_iff, mem_iUnion, not_exists]
        intro x hx hmem
        rw [hK' x hx] at hmem
        exact h x hx hmem
      refine ⟨_, Filter.inter_mem (hclosed.isOpen_compl.mem_nhds hy₀K) hU,
        chartConstField E y₀ v,
        (contMDiffOn_chartConstField y₀ v).mono fun y hy ↦ hUc hy.2,
        fun y hy ↦ ⟨fun _ ↦ ?_, ?_⟩⟩
      · exact hUneg y hy.2
      · simp only [mem_iInter, mem_singleton_iff]
        intro x hx hyK
        exfalso
        refine hy.1 (mem_iUnion₂.2 ⟨x, hx, ?_⟩)
        rw [hK' x hx]
        exact hyK
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (TangentSpace 𝓘(ℝ, E)) t ht hloc
  refine ⟨fun y ↦ s y, s.contMDiff, fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · exact (hs y).1 hy
  have hxC : x ∈ C := hx
  refine ⟨(φ x hxC).restr isOpen_interior (mem_interior_iff_mem_nhds.2 (hKn x hxC)),
    fun y hy ↦ ?_⟩
  rw [MorseChart.restr_source] at hy
  have hyK : y ∈ K x hxC := interior_subset hy.2
  have hsy : s y = (φ x hxC).field y := by
    have := (hs y).2
    simp only [mem_iInter, mem_singleton_iff] at this
    exact this x hxC hyK
  have hchart : ⇑((φ x hxC).restr isOpen_interior
      (mem_interior_iff_mem_nhds.2 (hKn x hxC))).toChart = (φ x hxC).toChart := by
    rw [MorseChart.restr_toChart, OpenPartialHomeomorph.restr_apply]
  rw [hsy, hchart, MorseChart.restr_coord, MorseChart.restr_weight]
  exact (φ x hxC).coord_mfderiv_field hy.1

end Existence

end TauCeti
