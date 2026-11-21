/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Basic
public import TauCeti.Analysis.Distribution.TestFunction.IntegrationCurrent
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Approximate
import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Uniqueness

/-!
# Integer-rectifiable currents

A `k`-current `T` on an open subset `Ω` of a finite-dimensional real inner product space `V` is
*integer-rectifiable* (`Distribution.IsIntegerRectifiable`) when it integrates test forms over a
countably `k`-rectifiable set with an integer multiplicity, in the orientation of its approximate
tangent planes:

`T ω = ∫ θ(x) ω_x(τ(x)) dμHE[k](x)`

(`Distribution.frameCurrent`), for a measurable integer multiplicity `θ : V → ℤ`, locally integrable
on `Ω` for the normalized Hausdorff measure `μHE[k]`, whose support `{θ ≠ 0}` is countably
`k`-rectifiable, and measurable orthonormal frames `τ` such that at almost every point of the
support in `Ω` the plane spanned by `τ(x)` is an approximate tangent plane of the support: the part
of the support outside every cone about that plane has density zero at `x`
(`TauCeti.DensityZeroOutsideCones`). This is the class of Federer and Fleming, written `τ(M, θ, ξ)`
by Simon, with orientation `ξ = τ₁ ∧ ⋯ ∧ τₖ`. Such a current has locally finite mass
(`Distribution.IsIntegerRectifiable.hasLocallyFiniteMass`).

The integer-rectifiable currents form an additive subgroup of the real `k`-currents on `Ω`
(`Distribution.integerRectifiableCurrents`), although they are not a real vector space. The point
is closure under addition. At almost every point where the supports of two such currents meet,
their approximate tangent planes agree, since an approximate tangent plane of the union of the
supports is one of each support, and approximate tangent planes are unique almost everywhere
(`TauCeti.CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones`). There the two orthonormal
frames span the same plane, so they differ by an orthogonal change of frame of determinant `±1`,
and the sum is the frame current of the first frame with multiplicity `θ₁ ± θ₂`. Uniqueness of
approximate tangent planes is a local statement, proved for sets of locally finite measure in `V`;
here the support only has locally finite measure in `Ω`, and the statement is localized to the
balls compactly contained in `Ω`.

For example the integration current `[[Ω]]` of the open set in top degree is integer-rectifiable
(`Distribution.isIntegerRectifiable_integrationCurrent`), with multiplicity one on `Ω` and a
constant orthonormal frame.

## Main declarations

* `TauCeti.DensityZeroOutsideCones`: the cone-density condition of an approximate tangent plane.
* `TauCeti.CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones`: approximate tangent
  planes exist and are unique almost everywhere on a countably rectifiable set of locally finite
  measure in an open set.
* `Distribution.IsIntegerRectifiable`: integer-rectifiable currents.
* `Distribution.integerRectifiableCurrents`: their additive subgroup.
* `Distribution.isIntegerRectifiable_integrationCurrent`: the integration current of an open set.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.24 and §4.1.28 (rectifiable currents).
* H. Federer and W. H. Fleming, *Normal and integral currents*, Ann. of Math. **72** (1960),
  458–520.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 3, §1 (approximate tangent planes),
  and Chapter 6, §3 (integer multiplicity rectifiable currents).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction MeasureTheory Module
open scoped Distributions ENNReal Topology RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ}

/-- The **cone-density condition** of an approximate tangent plane: the part of `S` outside every
cone about the `k`-plane `x + P` has `k`-dimensional density zero at `x`. Together with positive
density, which holds almost everywhere on a countably `k`-rectifiable set of locally finite measure,
this says that `P` is an approximate tangent plane of `S` at `x`. -/
def DensityZeroOutsideCones (k : ℕ) (S : Set V) (x : V) (P : Submodule ℝ V) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun r ↦
    μHE[k] {z ∈ S ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

omit [FiniteDimensional ℝ V] in
/-- The cone-density condition passes to subsets. -/
theorem DensityZeroOutsideCones.mono {S T : Set V} {x : V} {P : Submodule ℝ V}
    (h : DensityZeroOutsideCones k T x P) (hST : S ⊆ T) : DensityZeroOutsideCones k S x P :=
  fun ε hε ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) fun _ ↦ ENNReal.div_le_div_right (measure_mono fun _ hz ↦ by
      exact ⟨⟨hST hz.1.1, hz.1.2⟩, hz.2⟩) _

omit [FiniteDimensional ℝ V] in
/-- The cone-density condition at `x` only depends on the set near `x`. -/
theorem densityZeroOutsideCones_inter_iff {S B : Set V} {x : V} {P : Submodule ℝ V} {δ : ℝ}
    (hδ : 0 < δ) (hB : closedBall x δ ⊆ B) :
    DensityZeroOutsideCones k (S ∩ B) x P ↔ DensityZeroOutsideCones k S x P := by
  refine forall₂_congr fun ε _ ↦ tendsto_congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  congr 3
  ext z
  simp only [mem_inter_iff, and_congr_left_iff]
  intro _ hz
  exact and_iff_left (hB (closedBall_subset_closedBall hr.le hz))

/-- **Approximate tangent planes in an open set.** Let `S` be a measurable, countably
`k`-rectifiable set whose intersections with the compact subsets of an open set `Ω` have finite
`μHE[k]` measure. At almost every point of `S` in `Ω` there is a unique `k`-plane outside every
cone about which `S` has density zero. -/
theorem CountablyRectifiable.ae_existsUnique_densityZeroOutsideCones {Ω S : Set V} (hΩ : IsOpen Ω)
    (hS : CountablyRectifiable k S) (hSm : MeasurableSet S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S ∩ K) ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S → ∃ P : Submodule ℝ V, finrank ℝ P = k ∧
      DensityZeroOutsideCones k S x P ∧
        ∀ Q : Submodule ℝ V, finrank ℝ Q = k → DensityZeroOutsideCones k S x Q → Q = P := by
  -- Cover `Ω` by countably many balls whose closures lie in `Ω`.
  have hr (x : Ω) : ∃ r > 0, closedBall (x : V) r ⊆ Ω := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x x.property
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose r hr0 hrΩ using hr
  obtain ⟨T, hTc, hTU⟩ :=
    isOpen_iUnion_countable (fun x : Ω ↦ ball (x : V) (r x)) fun _ ↦ isOpen_ball
  -- On each closed ball the set has finite measure, where the existence and uniqueness theorems
  -- apply; inside the open ball the cone-density condition is that of `S`.
  have hpiece (c : Ω) : ∀ᵐ x ∂μHE[k], x ∈ ball (c : V) (r c) → x ∈ S →
      ∃ P : Submodule ℝ V, finrank ℝ P = k ∧ DensityZeroOutsideCones k S x P ∧
        ∀ Q : Submodule ℝ V, finrank ℝ Q = k → DensityZeroOutsideCones k S x Q → Q = P := by
    set Sc := S ∩ closedBall (c : V) (r c)
    have hfc : μHE[k] Sc ≠ ∞ := hfin _ (isCompact_closedBall _ _) (hrΩ c)
    have : IsFiniteMeasure (μHE[k].restrict Sc) := isFiniteMeasure_restrict.2 hfc
    have hSc : CountablyRectifiable k Sc := hS.mono inter_subset_left
    have hScm : NullMeasurableSet Sc μHE[k] :=
      (hSm.inter isClosed_closedBall.measurableSet).nullMeasurableSet
    filter_upwards [hSc.ae_exists_submodule_tendsto_measure_outside_cone_div hScm,
      hSc.ae_eq_of_tendsto_measure_outside_cone_div hScm] with x hex huniq hxb hxS
    have hxSc : x ∈ Sc := ⟨hxS, ball_subset_closedBall hxb⟩
    have hδ : 0 < r c - dist x c := sub_pos.2 hxb
    have hiff (P : Submodule ℝ V) :
        DensityZeroOutsideCones k Sc x P ↔ DensityZeroOutsideCones k S x P :=
      densityZeroOutsideCones_inter_iff hδ (closedBall_subset_closedBall' (by linarith))
    obtain ⟨P, hP, hPc⟩ := hex hxSc
    exact ⟨P, hP, (hiff P).1 hPc, fun Q hQ hQc ↦ huniq hxSc Q P hQ hP ((hiff Q).2 hQc) hPc⟩
  have : Countable T := hTc.to_subtype
  filter_upwards [ae_all_iff.2 fun c : T ↦ hpiece c] with x hx hxΩ hxS
  have hxT : x ∈ ⋃ i ∈ T, ball (i : V) (r i) :=
    hTU ▸ mem_iUnion.2 ⟨⟨x, hxΩ⟩, mem_ball_self (hr0 _)⟩
  obtain ⟨c, hcT, hxc⟩ := mem_iUnion₂.1 hxT
  exact hx ⟨c, hcT⟩ hxc hxS

/-- At almost every point of the union of two such sets in `Ω`, the plane outside whose cones
either set has density zero is one for the union. In particular, where the two sets meet, their
planes agree. -/
theorem CountablyRectifiable.ae_densityZeroOutsideCones_union {Ω S₁ S₂ : Set V} (hΩ : IsOpen Ω)
    (hS₁ : CountablyRectifiable k S₁) (hS₁m : MeasurableSet S₁)
    (hfin₁ : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S₁ ∩ K) ≠ ∞)
    (hS₂ : CountablyRectifiable k S₂) (hS₂m : MeasurableSet S₂)
    (hfin₂ : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] (S₂ ∩ K) ≠ ∞)
    {P₁ P₂ : V → Submodule ℝ V} (hP₁ : ∀ x ∈ S₁, finrank ℝ (P₁ x) = k)
    (hP₂ : ∀ x ∈ S₂, finrank ℝ (P₂ x) = k)
    (hP₁c : ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S₁ → DensityZeroOutsideCones k S₁ x (P₁ x))
    (hP₂c : ∀ᵐ x ∂μHE[k], x ∈ Ω → x ∈ S₂ → DensityZeroOutsideCones k S₂ x (P₂ x)) :
    ∀ᵐ x ∂μHE[k], x ∈ Ω →
      (x ∈ S₁ → DensityZeroOutsideCones k (S₁ ∪ S₂) x (P₁ x)) ∧
      (x ∈ S₂ → DensityZeroOutsideCones k (S₁ ∪ S₂) x (P₂ x)) ∧
      (x ∈ S₁ → x ∈ S₂ → P₁ x = P₂ x) := by
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → μHE[k] ((S₁ ∪ S₂) ∩ K) ≠ ∞ := fun K hK hKΩ ↦ by
    rw [union_inter_distrib_right]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin₁ K hK hKΩ, hfin₂ K hK hKΩ⟩)
      (measure_union_le _ _)
  filter_upwards [(hS₁.union hS₂).ae_existsUnique_densityZeroOutsideCones hΩ (hS₁m.union hS₂m)
      hfin, hS₁.ae_existsUnique_densityZeroOutsideCones hΩ hS₁m hfin₁,
      hS₂.ae_existsUnique_densityZeroOutsideCones hΩ hS₂m hfin₂, hP₁c, hP₂c]
    with x hU h₁ h₂ hc₁ hc₂ hxΩ
  -- The plane `Q` of the union is a plane of each set, so it is the unique plane of each.
  have key (hx : x ∈ S₁ ∪ S₂) : ∃ Q : Submodule ℝ V, DensityZeroOutsideCones k (S₁ ∪ S₂) x Q ∧
      (x ∈ S₁ → P₁ x = Q) ∧ (x ∈ S₂ → P₂ x = Q) := by
    obtain ⟨Q, hQ, hQc, -⟩ := hU hxΩ hx
    refine ⟨Q, hQc, fun hx₁ ↦ ?_, fun hx₂ ↦ ?_⟩
    · obtain ⟨P, -, -, hPu⟩ := h₁ hxΩ hx₁
      exact (hPu (P₁ x) (hP₁ x hx₁) (hc₁ hxΩ hx₁)).trans
        (hPu Q hQ (hQc.mono subset_union_left)).symm
    · obtain ⟨P, -, -, hPu⟩ := h₂ hxΩ hx₂
      exact (hPu (P₂ x) (hP₂ x hx₂) (hc₂ hxΩ hx₂)).trans
        (hPu Q hQ (hQc.mono subset_union_right)).symm
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_, fun hx₁ hx₂ ↦ ?_⟩
  · obtain ⟨Q, hQc, h, -⟩ := key (Or.inl hx)
    rwa [h hx]
  · obtain ⟨Q, hQc, -, h⟩ := key (Or.inr hx)
    rwa [h hx]
  · obtain ⟨Q, -, h, h'⟩ := key (Or.inl hx₁)
    rw [h hx₁, h' hx₂]

end TauCeti

namespace Distribution

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞} {k : ℕ}

/-- A `k`-current on `Ω` is **integer-rectifiable** when it is the frame current
`ω ↦ ∫ θ(x) ω_x(τ(x)) dμHE[k](x)` of a measurable integer multiplicity `θ`, locally integrable on
`Ω`, whose support `{θ ≠ 0}` is countably `k`-rectifiable, with measurable frames `τ`, orthonormal
on the support, such that at almost every point of the support in `Ω` the support has density zero
outside every cone about the plane spanned by `τ(x)`: that plane is the approximate tangent plane
of the support, oriented by the frame. -/
def IsIntegerRectifiable (T : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) : Prop :=
  ∃ (θ : V → ℤ) (τ : V → Fin k → V), Measurable θ ∧ Measurable τ ∧
    CountablyRectifiable k {x | θ x ≠ 0} ∧ LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k] ∧
    (∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) ∧
    (∀ᵐ x ∂μHE[k], x ∈ Ω → θ x ≠ 0 →
      DensityZeroOutsideCones k {x | θ x ≠ 0} x (Submodule.span ℝ (range (τ x)))) ∧
    T = frameCurrent (fun x ↦ (θ x : ℝ)) τ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The support of an integer multiplicity, locally integrable on `Ω`, has finite measure on the
compact subsets of `Ω`, since the multiplicity has absolute value at least one there. -/
theorem measure_setOf_ne_zero_inter_ne_top {θ : V → ℤ} (hθm : Measurable θ)
    (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k]) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : μHE[k] ({x | θ x ≠ 0} ∩ K) ≠ ∞ := by
  have hS : MeasurableSet {x | θ x ≠ 0} := hθm (measurableSet_singleton 0).compl
  refine ne_top_of_le_ne_top (hθ.integrableOn_compact_subset hKΩ hK).2.ne ?_
  rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : θ x = 0
  · simp [hx]
  · rw [indicator_of_mem (show x ∈ {x | θ x ≠ 0} from hx), Pi.one_apply,
      Real.eNorm_eq_ofReal_abs]
    have h1 : (1 : ℝ) ≤ |((θ x : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hx
    exact ENNReal.one_le_ofReal.2 h1

/-- An integer-rectifiable current has locally finite mass. -/
theorem IsIntegerRectifiable.hasLocallyFiniteMass {T : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : IsIntegerRectifiable T) : HasLocallyFiniteMass T := by
  obtain ⟨θ, τ, -, -, -, hθ, hτo, -, rfl⟩ := hT
  exact hasLocallyFiniteMass_frameCurrent hθ fun x hx ↦ hτo x (by exact_mod_cast hx)

/-- The zero current is integer-rectifiable. -/
theorem isIntegerRectifiable_zero :
    IsIntegerRectifiable (0 : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ⟨0, 0, measurable_const, measurable_const, by simp [CountablyRectifiable.empty], by
    simpa [Pi.zero_def] using
      (integrable_zero V ℝ μHE[k]).locallyIntegrable.locallyIntegrableOn (Ω : Set V),
    by simp, by simp, by
    rw [show (fun x : V ↦ (((0 : V → ℤ) x : ℤ) : ℝ)) = 0 from funext fun _ ↦ by simp,
      frameCurrent_zero]⟩

/-- The negative of an integer-rectifiable current is integer-rectifiable. -/
theorem IsIntegerRectifiable.neg {T : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : IsIntegerRectifiable T) : IsIntegerRectifiable (-T) := by
  obtain ⟨θ, τ, hθm, hτ, hS, hθ, hτo, hc, rfl⟩ := hT
  refine ⟨-θ, τ, hθm.neg, hτ, by simpa using hS, by convert hθ.neg using 1; funext x; simp,
    by simpa using hτo,
    by simpa using hc, ?_⟩
  rw [← frameCurrent_neg]
  congr 1
  funext x
  simp

/-- The sign `±1` of the change of orthonormal frame from `σ` to `τ`, read off from the determinant
of the overlap matrix; the frames span the same plane in the cases of interest. -/
private def frameSign (σ τ : Fin k → V) : ℤ :=
  if 0 ≤ (Matrix.of fun j i ↦ ⟪σ i, τ j⟫).det then 1 else -1

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem abs_frameSign (σ τ : Fin k → V) : |(frameSign σ τ : ℝ)| = 1 := by
  by_cases h : 0 ≤ (Matrix.of fun j i ↦ ⟪σ i, τ j⟫).det <;> simp [frameSign, h]

private theorem measurable_frameSign {σ τ : V → Fin k → V} (hσ : Measurable σ)
    (hτ : Measurable τ) : Measurable fun x ↦ frameSign (σ x) (τ x) :=
  Measurable.ite (measurableSet_le measurable_const (hσ.det_inner hτ)) measurable_const
    measurable_const

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- On forms, an orthonormal frame `τ` in the plane of an orthonormal frame `σ` is `σ` times the
sign of the change of frame. -/
private theorem frameSign_mul_apply {σ τ : Fin k → V} (hσ : Orthonormal ℝ σ)
    (hτ : Orthonormal ℝ τ) (h : ∀ j, τ j ∈ Submodule.span ℝ (range σ))
    (ω : V [⋀^Fin k]→L[ℝ] ℝ) : (frameSign σ τ : ℝ) * ω σ = ω τ := by
  have hω : ω τ = (Matrix.of fun j i ↦ ⟪σ i, τ j⟫).det * ω σ := by
    simpa using ω.toAlternatingMap.map_eq_det_inner_smul_of_mem_span hσ h
  rcases Orthonormal.det_inner_eq_one_or_eq_neg_one hσ hτ h with hd | hd <;>
    simp [frameSign, hd, hω]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A sum `θ₁ + ε θ₂` of locally integrable multiplicities with a measurable sign `ε` is locally
integrable. -/
private theorem locallyIntegrableOn_add_mul {θ₁ θ₂ ε : V → ℤ}
    (hθ₁ : LocallyIntegrableOn (fun x ↦ (θ₁ x : ℝ)) Ω μHE[k])
    (hθ₂ : LocallyIntegrableOn (fun x ↦ (θ₂ x : ℝ)) Ω μHE[k]) (hθ₂m : Measurable θ₂)
    (hεm : Measurable ε) (hε : ∀ x, |(ε x : ℝ)| = 1) :
    LocallyIntegrableOn (fun x ↦ ((θ₁ x + ε x * θ₂ x : ℤ) : ℝ)) Ω μHE[k] := by
  have h2 : LocallyIntegrableOn (fun x ↦ (ε x : ℝ) * θ₂ x) Ω μHE[k] := fun x hx ↦ by
    obtain ⟨t, ht, hint⟩ := hθ₂ x hx
    refine ⟨t, ht, Integrable.mono hint ?_ (ae_of_all _ fun y ↦ ?_)⟩
    · exact ((measurable_from_top.comp hεm).mul
        (measurable_from_top.comp hθ₂m)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (ε y : ℝ), hε, one_mul]
  convert hθ₁.add h2 using 1
  funext x
  simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The pointwise identity behind the addition of frame currents: the multiplicity `θ₁ + e θ₂` on
the frame equal to `τ₁` where `θ₁ ≠ 0` and to `τ₂` elsewhere pairs with a form as the sum of the two
pairings, provided `τ₂` is `e` times that frame on the form where `θ₂ ≠ 0`. -/
private theorem intCast_add_mul_mul_apply_ite {θ₁ θ₂ e : ℤ} {τ₁ τ₂ : Fin k → V}
    (ω : V [⋀^Fin k]→L[ℝ] ℝ) (h : θ₂ ≠ 0 → (e : ℝ) * ω (if θ₁ ≠ 0 then τ₁ else τ₂) = ω τ₂) :
    ((θ₁ + e * θ₂ : ℤ) : ℝ) * ω (if θ₁ ≠ 0 then τ₁ else τ₂) = θ₁ * ω τ₁ + θ₂ * ω τ₂ := by
  have h1 : (θ₁ : ℝ) * ω (if θ₁ ≠ 0 then τ₁ else τ₂) = θ₁ * ω τ₁ := by
    by_cases h' : θ₁ ≠ 0
    · simp [h']
    · simp [not_not.1 h']
  by_cases h2 : θ₂ = 0
  · rw [h2, mul_zero, add_zero, h1, Int.cast_zero, zero_mul, add_zero]
  · rw [← h h2, ← h1]
    push_cast
    ring

/-- **Integer-rectifiable currents are closed under addition.** At almost every common point of
the two supports in `Ω`, the two frames span the same approximate tangent plane, so they differ by
an orthogonal change of frame, of determinant `ε = ±1`; the sum is the frame current of the first
frame on the first support and of the second frame elsewhere, with multiplicity `θ₁ + ε θ₂`. -/
theorem IsIntegerRectifiable.add {T₁ T₂ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (h₁ : IsIntegerRectifiable T₁) (h₂ : IsIntegerRectifiable T₂) :
    IsIntegerRectifiable (T₁ + T₂) := by
  classical
  obtain ⟨θ₁, τ₁, hθ₁m, hτ₁, hS₁, hθ₁, hτo₁, hc₁, rfl⟩ := h₁
  obtain ⟨θ₂, τ₂, hθ₂m, hτ₂, hS₂, hθ₂, hτo₂, hc₂, rfl⟩ := h₂
  have hS₁m : MeasurableSet {x | θ₁ x ≠ 0} := hθ₁m (measurableSet_singleton 0).compl
  have hS₂m : MeasurableSet {x | θ₂ x ≠ 0} := hθ₂m (measurableSet_singleton 0).compl
  -- The frame `σ` is `τ₁` on the first support and `τ₂` elsewhere.
  set σ : V → Fin k → V := fun x ↦ if θ₁ x ≠ 0 then τ₁ x else τ₂ x
  have hσ : Measurable σ := Measurable.ite hS₁m hτ₁ hτ₂
  have hσo (x : V) (hx : θ₁ x ≠ 0 ∨ θ₂ x ≠ 0) : Orthonormal ℝ (σ x) := by
    by_cases h : θ₁ x ≠ 0
    · simpa [σ, h] using hτo₁ x h
    · simpa [σ, not_not.1 h] using hτo₂ x (hx.resolve_left h)
  -- The sign `ε` of the change of frame from `σ` to `τ₂`.
  set ε : V → ℤ := fun x ↦ frameSign (σ x) (τ₂ x)
  have hεm : Measurable ε := measurable_frameSign hσ hτ₂
  set θ : V → ℤ := fun x ↦ θ₁ x + ε x * θ₂ x
  have hsupp : {x | θ x ≠ 0} ⊆ {x | θ₁ x ≠ 0} ∪ {x | θ₂ x ≠ 0} := fun x hx ↦ by_contra fun h ↦
    hx (by simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h; simp [θ, h.1, h.2])
  -- At almost every point of the supports, the two frames span the plane of the union.
  have hU := hS₁.ae_densityZeroOutsideCones_union Ω.isOpen hS₁m
    (fun K hK hKΩ ↦ measure_setOf_ne_zero_inter_ne_top hθ₁m hθ₁ hK hKΩ) hS₂ hS₂m
    (fun K hK hKΩ ↦ measure_setOf_ne_zero_inter_ne_top hθ₂m hθ₂ hK hKΩ)
    (P₁ := fun x ↦ Submodule.span ℝ (range (τ₁ x)))
    (P₂ := fun x ↦ Submodule.span ℝ (range (τ₂ x)))
    (fun x hx ↦ by simpa using finrank_span_eq_card (hτo₁ x hx).linearIndependent)
    (fun x hx ↦ by simpa using finrank_span_eq_card (hτo₂ x hx).linearIndependent) hc₁ hc₂
  -- Hence `τ₂` is `ε` times the frame `σ` on forms, where `θ₂` does not vanish.
  have hpt : ∀ᵐ x ∂μHE[k], x ∈ Ω → θ₂ x ≠ 0 → ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ,
      (ε x : ℝ) * ω (σ x) = ω (τ₂ x) := by
    filter_upwards [hU] with x hx hxΩ h2 ω
    refine frameSign_mul_apply (hσo x (Or.inr h2)) (hτo₂ x h2) (fun j ↦ ?_) ω
    by_cases h1 : θ₁ x ≠ 0
    · simp only [σ, h1, ite_true, ne_eq, not_false_eq_true]
      rw [(hx hxΩ).2.2 h1 h2]
      exact Submodule.subset_span ⟨j, rfl⟩
    · simp only [σ, h1, ite_false]
      exact Submodule.subset_span ⟨j, rfl⟩
  have hθli : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k] :=
    locallyIntegrableOn_add_mul hθ₁ hθ₂ hθ₂m hεm fun x ↦ abs_frameSign _ _
  refine ⟨θ, σ, hθ₁m.add (hεm.mul hθ₂m), hσ, (hS₁.union hS₂).mono hsupp, hθli,
    fun x hx ↦ hσo x (by simpa using hsupp hx), ?_, ?_⟩
  · filter_upwards [hU] with x hx hxΩ hθx
    refine DensityZeroOutsideCones.mono ?_ hsupp
    by_cases h1 : θ₁ x ≠ 0
    · simpa [σ, h1] using (hx hxΩ).1 h1
    · simpa [σ, not_not.1 h1] using (hx hxΩ).2.1 ((hsupp hθx).resolve_left h1)
  · have hθo (x : V) (hx : ((θ x : ℤ) : ℝ) ≠ 0) : Orthonormal ℝ (σ x) :=
      hσo x (by simpa using hsupp (show θ x ≠ 0 by exact_mod_cast hx))
    refine (frameCurrent_add (θ := fun x ↦ (θ x : ℝ)) hθli hσ hθo hθ₁ hτ₁
      (fun x hx ↦ hτo₁ x (by exact_mod_cast hx)) hθ₂ hτ₂
      (fun x hx ↦ hτo₂ x (by exact_mod_cast hx)) ?_).symm
    · filter_upwards [hpt] with x hx hxΩ ω
      exact intCast_add_mul_mul_apply_ite ω fun h2 ↦ hx hxΩ h2 ω

variable (Ω n k) in
/-- The **integer-rectifiable currents** of degree `k` on `Ω`, an additive subgroup of the real
`k`-currents (`Distribution.IsIntegerRectifiable`). -/
def integerRectifiableCurrents : AddSubgroup (𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  carrier := {T | IsIntegerRectifiable T}
  zero_mem' := isIntegerRectifiable_zero
  add_mem' := IsIntegerRectifiable.add
  neg_mem' := IsIntegerRectifiable.neg

@[simp]
theorem mem_integerRectifiableCurrents {T : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    T ∈ integerRectifiableCurrents Ω n k ↔ IsIntegerRectifiable T :=
  Iff.rfl

/-- **The integration current of an open set is integer-rectifiable.** In top degree `m`, for an
orthonormal basis `b`, the integration current `[[Ω]]` for the orientation of `b` is the frame
current of the multiplicity one on `Ω` and the constant frame `b`; the approximate tangent plane is
the whole space. -/
theorem isIntegerRectifiable_integrationCurrent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ V) :
    IsIntegerRectifiable
      (b.toBasis.orientation.integrationCurrent Ω : 𝓓^{n}(Ω, V [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  classical
  have hm : finrank ℝ V = m := by simpa using finrank_eq_card_basis b.toBasis
  have hμ : (μHE[m] : Measure V) = volume := by
    rw [← hm]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  set θ : V → ℤ := fun x ↦ if x ∈ (Ω : Set V) then 1 else 0
  have hθm : Measurable θ := Measurable.ite Ω.isOpen.measurableSet measurable_const measurable_const
  have hS : {x | θ x ≠ 0} = (Ω : Set V) := by
    ext x
    by_cases hx : x ∈ Ω <;> simp [θ, hx]
  have hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[m] := by
    rw [hμ]
    exact ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _).mono
      (measurable_from_top.comp hθm).aestronglyMeasurable (ae_of_all _ fun y ↦ by
        by_cases hy : y ∈ Ω <;> simp [θ, hy])
  refine ⟨θ, fun _ ↦ b, hθm, measurable_const, ?_, hθ, fun _ _ ↦ b.orthonormal,
    ae_of_all _ fun x _ _ ε hε ↦ ?_, ?_⟩
  · rw [hS]
    simpa using (CountablyRectifiable.isometryEquiv_image_iff
      (e := b.repr.toIsometryEquiv) (s := (Ω : Set V))).1 (CountablyRectifiable.euclidean _)
  · -- The plane spanned by `b` is the whole space, so no point lies outside the cones.
    have hspan : Submodule.span ℝ (range (b : Fin m → V)) = ⊤ := b.toBasis.span_eq.trans rfl
    refine tendsto_const_nhds.congr fun r ↦ ?_
    rw [hspan, Submodule.top_coe]
    have hempty : {z ∈ {x | θ x ≠ 0} ∩ closedBall x r |
        ε * dist z x < infDist (z - x) (univ : Set V)} = ∅ := by
      ext z
      simp only [infDist_zero_of_mem (mem_univ _), mem_sep_iff, mem_empty_iff_false, iff_false,
        not_and, not_lt]
      exact fun _ ↦ mul_nonneg hε.le dist_nonneg
    rw [hempty, measure_empty, ENNReal.zero_div]
  · ext ω
    rw [frameCurrent_apply hθ measurable_const (fun _ _ ↦ b.orthonormal),
      Orientation.integrationCurrent_apply_eq_integral_volume _ b rfl, hμ]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ Ω
    · simp [θ, hx]
    · simp [θ, hx, image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (ω.tsupport_subset hmem)]

end Distribution

