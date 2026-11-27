/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Basic
public import TauCeti.Analysis.Distribution.TestFunction.IntegrationCurrent
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Local
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.SpecialFunctions.FrameSign

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
(`TauCeti.CountablyRectifiable.ae_densityZeroOutsideCones_union`, for sets of locally finite
measure in `Ω`). There the two orthonormal frames span the same plane, so they differ by an
orthogonal change of frame of determinant `±1`, and the sum is the frame current of the first frame
with multiplicity `θ₁ ± θ₂`.

The basic examples are carried by affine planes. An integer multiplicity vanishing off an affine
plane `x₀ + span e` of an orthonormal family `e`, with the constant frame `e`, gives an
integer-rectifiable current (`Distribution.isIntegerRectifiable_frameCurrent_of_sub_mem_span`): the
plane is the approximate tangent plane at each point of the support. For example the integration
current `[[Ω]]` of the open set in top degree is integer-rectifiable
(`Distribution.isIntegerRectifiable_integrationCurrent`), with multiplicity one on `Ω` and a
constant orthonormal frame.

## Main declarations

* `Distribution.IsIntegerRectifiable`: integer-rectifiable currents.
* `Distribution.integerRectifiableCurrents`: their additive subgroup.
* `Distribution.isIntegerRectifiable_frameCurrent_of_sub_mem_span`: currents carried by an affine
  plane with a constant frame.
* `Distribution.isIntegerRectifiable_integrationCurrent`: the integration current of an open set.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.24 and §4.1.28 (rectifiable currents).
* H. Federer and W. H. Fleming, *Normal and integral currents*, Ann. of Math. **72** (1960),
  458–520.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction MeasureTheory Module
open scoped Distributions ENNReal Topology RealInnerProductSpace

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

/-- Unfolding `Distribution.IsIntegerRectifiable` into its multiplicity and frame data. -/
theorem isIntegerRectifiable_iff {T : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    IsIntegerRectifiable T ↔ ∃ (θ : V → ℤ) (τ : V → Fin k → V), Measurable θ ∧ Measurable τ ∧
      CountablyRectifiable k {x | θ x ≠ 0} ∧ LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k] ∧
      (∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) ∧
      (∀ᵐ x ∂μHE[k], x ∈ Ω → θ x ≠ 0 →
        DensityZeroOutsideCones k {x | θ x ≠ 0} x (Submodule.span ℝ (range (τ x)))) ∧
      T = frameCurrent (fun x ↦ (θ x : ℝ)) τ :=
  Iff.rfl

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

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A sum `θ₁ + ε θ₂` of locally integrable multiplicities with a measurable sign `ε` is locally
integrable. -/
private theorem locallyIntegrableOn_add_mul {θ₁ θ₂ ε : V → ℤ}
    (hθ₁ : LocallyIntegrableOn (fun x ↦ (θ₁ x : ℝ)) Ω μHE[k])
    (hθ₂ : LocallyIntegrableOn (fun x ↦ (θ₂ x : ℝ)) Ω μHE[k]) (hεm : Measurable ε)
    (hε : ∀ x, |(ε x : ℝ)| = 1) :
    LocallyIntegrableOn (fun x ↦ ((θ₁ x + ε x * θ₂ x : ℤ) : ℝ)) Ω μHE[k] := by
  have h2 : LocallyIntegrableOn (fun x ↦ (ε x : ℝ) * θ₂ x) Ω μHE[k] :=
    hθ₂.bdd_mul_of_ne_zero (measurable_from_top.comp hεm).aestronglyMeasurable
      (ae_of_all _ fun x _ ↦ (Real.norm_eq_abs _).trans_le (hε x).le)
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
  · simpa [h2] using h1
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
  have hεm : Measurable ε := hσ.frameSign hτ₂
  set θ : V → ℤ := fun x ↦ θ₁ x + ε x * θ₂ x
  have hsupp : {x | θ x ≠ 0} ⊆ {x | θ₁ x ≠ 0} ∪ {x | θ₂ x ≠ 0} := fun x hx ↦ by_contra fun h ↦
    hx (by simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h; simp [θ, h.1, h.2])
  -- At almost every point of the supports, the two frames span the plane of the union.
  have hU := hS₁.ae_densityZeroOutsideCones_union Ω.isOpen hS₁m.nullMeasurableSet
    (fun _ ↦ hθ₁.measure_setOf_intCast_ne_zero_inter_ne_top) hS₂ hS₂m.nullMeasurableSet
    (fun _ ↦ hθ₂.measure_setOf_intCast_ne_zero_inter_ne_top)
    (P₁ := fun x ↦ Submodule.span ℝ (range (τ₁ x)))
    (P₂ := fun x ↦ Submodule.span ℝ (range (τ₂ x)))
    (fun x hx ↦ by simpa using finrank_span_eq_card (hτo₁ x hx).linearIndependent)
    (fun x hx ↦ by simpa using finrank_span_eq_card (hτo₂ x hx).linearIndependent) hc₁ hc₂
  -- Hence `τ₂` is `ε` times the frame `σ` on forms, where `θ₂` does not vanish.
  have hpt : ∀ᵐ x ∂μHE[k], x ∈ Ω → θ₂ x ≠ 0 → ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ,
      (ε x : ℝ) * ω (σ x) = ω (τ₂ x) := by
    filter_upwards [hU] with x hx hxΩ h2 ω
    have hspan : Submodule.span ℝ (range (σ x)) = Submodule.span ℝ (range (τ₂ x)) := by
      by_cases h1 : θ₁ x ≠ 0
      · simpa [σ, h1] using (hx hxΩ).2.2 h1 h2
      · simp [σ, not_not.1 h1]
    simpa [ε, zsmul_eq_mul] using (ω.toAlternatingMap.map_eq_frameSign_smul_of_mem_span
      (hσo x (Or.inr h2)) (hτo₂ x h2) fun j ↦ hspan ▸ Submodule.subset_span ⟨j, rfl⟩).symm
  have hθli : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k] :=
    locallyIntegrableOn_add_mul hθ₁ hθ₂ hεm fun x ↦ by exact_mod_cast abs_frameSign _ _
  refine ⟨θ, σ, hθ₁m.add (hεm.mul hθ₂m), hσ, (hS₁.union hS₂).mono hsupp, hθli,
    fun x hx ↦ hσo x (by simpa using hsupp hx), ?_, ?_⟩
  · filter_upwards [hU] with x hx hxΩ hθx
    refine DensityZeroOutsideCones.mono ?_ hsupp
    by_cases h1 : θ₁ x ≠ 0
    · simpa [σ, h1] using (hx hxΩ).1 h1
    · simpa [σ, not_not.1 h1] using (hx hxΩ).2.1 ((hsupp hθx).resolve_left h1)
  · have hθo (x : V) (hx : ((θ x : ℤ) : ℝ) ≠ 0) : Orthonormal ℝ (σ x) :=
      hσo x (by simpa using hsupp (show θ x ≠ 0 by exact_mod_cast hx))
    refine (frameCurrent_eq_add_of_ae (θ := fun x ↦ (θ x : ℝ)) hθli hσ hθo hθ₁ hτ₁
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

/-- **A current carried by an affine plane is integer-rectifiable.** If an integer multiplicity
`θ`, measurable and locally integrable on `Ω`, vanishes off the affine plane `x₀ + span e` of an
orthonormal family `e : Fin k → V`, then its frame current with the constant frame `e` is
integer-rectifiable: the support lies in a `k`-dimensional affine plane, which is its approximate
tangent plane at each of its points. -/
theorem isIntegerRectifiable_frameCurrent_of_sub_mem_span {θ : V → ℤ} {e : Fin k → V}
    (he : Orthonormal ℝ e) (x₀ : V) (hθm : Measurable θ)
    (hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[k])
    (hθe : ∀ x, θ x ≠ 0 → x - x₀ ∈ Submodule.span ℝ (range e)) :
    IsIntegerRectifiable
      (frameCurrent (fun x ↦ (θ x : ℝ)) (fun _ ↦ e) : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  set P := Submodule.span ℝ (range e)
  have hP : finrank ℝ P = k := by simpa using finrank_span_eq_card he.linearIndependent
  refine ⟨θ, fun _ ↦ e, hθm, measurable_const, ?_, hθ, fun _ _ ↦ he,
    ae_of_all _ fun x _ hx ↦ densityZeroOutsideCones_of_forall_sub_mem fun z hz ↦ ?_, rfl⟩
  · -- The support lies in the translate `P + x₀` of the `k`-dimensional subspace `P`.
    have h := (CountablyRectifiable.isometry_image_iff (isometry_add_right x₀)).2
      P.countablyRectifiable
    rw [hP] at h
    exact h.mono fun x hx ↦ ⟨x - x₀, hθe x hx, sub_add_cancel x x₀⟩
  · simpa using P.sub_mem (hθe z hz) (hθe x hx)

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
  have hθ : LocallyIntegrableOn (fun x ↦ (θ x : ℝ)) Ω μHE[m] := by
    rw [hμ]
    exact ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _).mono
      (measurable_from_top.comp hθm).aestronglyMeasurable (ae_of_all _ fun y ↦ by
        by_cases hy : y ∈ Ω <;> simp [θ, hy])
  have hT : (b.toBasis.orientation.integrationCurrent Ω : 𝓓^{n}(Ω, V [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      frameCurrent (fun x ↦ (θ x : ℝ)) (fun _ ↦ b) := by
    ext ω
    rw [frameCurrent_apply hθ measurable_const (fun _ _ ↦ b.orthonormal),
      Orientation.integrationCurrent_apply_eq_integral_volume _ b rfl, hμ]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ Ω
    · simp [θ, hx]
    · simp [θ, hx, image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (ω.tsupport_subset hmem)]
  -- The plane spanned by `b` is the whole space.
  rw [hT]
  refine isIntegerRectifiable_frameCurrent_of_sub_mem_span b.orthonormal 0 hθm hθ fun x _ ↦ ?_
  rw [← b.coe_toBasis, b.toBasis.span_eq]
  exact Submodule.mem_top

end Distribution

