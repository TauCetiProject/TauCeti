/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.AlongMap

/-!
# Localized coefficient directions for the Floer operator

At a fixed domain point, compactly supported smooth variations of the `ds` component of the
Hamiltonian perturbation realize every vector in the target of the Floer operator. The
perturbation is supported in any specified neighborhood of the domain/target point. In
particular, it can be confined to a compact core, leaving the cylindrical end data unchanged.

The realization is an exact affine identity for the nonlinear operator, not only a formal
linearization: adding `r δK_s` changes its value by `r v`. Consequently its parameter derivative
is `v`. There is no immersion or nonconstancy hypothesis on the map. This distinguishes
Hamiltonian variations from variations of the almost complex structure, which multiply the
perturbed derivative of the map.

The same holds for whole fields along the map: a single localized variation `δK` changes the
operator by any prescribed smooth compactly supported field `ξ`
(`SymplecticForm.exists_contDiff_floerOperator_add_const_mul_left_eq_add`). Dually, these
variations detect cokernel elements. A field `η` of covectors that annihilates the change of the
Floer operator under every variation `δK` supported in a neighborhood `W` of the graph of `u`
over an open set `Ω` vanishes on `Ω`: almost everywhere when `η` is locally integrable
(`SymplecticForm.ae_eq_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`), and
everywhere on `Ω` when `η` is continuous
(`SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`). Taking `Ω`
inside a compact core of a punctured domain, this is the step of the transversality argument in
which an element of the cokernel of the universal linearized operator is shown to vanish on the
core, for constant as well as nonconstant maps.

These are coordinate-level statements. They do not assert surjectivity of a Sobolev
operator, unique continuation, or regularity of any moduli space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian variations in the universal inhomogeneous Cauchy–Riemann operator.
-/

public section

open Set Topology Filter MeasureTheory

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Floer operator is affine in a differentiable Hamiltonian variation of its `ds`
component. Neither the map nor the endomorphism field needs to be differentiable for this
pointwise identity. -/
theorem floerOperator_add_const_mul_left (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt δK : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    (hδK : DifferentiableAt ℝ (δK z) (u z)) (r : ℝ) :
    ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
      ω.floerOperator J Ks Kt u z - r • ω.hamiltonianVectorField (δK z) (u z) := by
  have hX := ω.hamiltonianVectorField_const_mul_add_const_mul hKs hδK 1 r
  simp only [one_mul, one_smul] at hX
  simp only [floerOperator_def, hX]
  abel

/-- A smooth Hamiltonian variation supported in any neighborhood of `(z, u z)` realizes any
prescribed direction of the Floer operator. The formula holds for every real parameter, and
also when `u` is constant. Only the original `ds` Hamiltonian must be differentiable at the
point in question. -/
theorem exists_contDiff_floerOperator_add_const_mul_left (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    {U : Set ((ℝ × ℝ) × V)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      δK z (u z) = 0 ∧ ∀ r : ℝ,
        ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
          ω.floerOperator J Ks Kt u z + r • v := by
  obtain ⟨δK, hs, hc, hsub, hzero, hX⟩ :=
    ω.exists_contDiff_hamiltonianVectorField_eq z (u z) (-v) hU
  refine ⟨δK, hs, hc, hsub, hzero, fun r ↦ ?_⟩
  have hd : DifferentiableAt ℝ (δK z) (u z) :=
    (hs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (u z)
  rw [ω.floerOperator_add_const_mul_left J Ks Kt δK u z hKs hd, hX, smul_neg,
    sub_neg_eq_add]

/-- Localized smooth Hamiltonian variations give actual parameter derivatives of the Floer
operator in every prescribed direction, even along constant maps. The derivative is the same
at every parameter value. -/
theorem exists_contDiff_hasDerivAt_floerOperator (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    {U : Set ((ℝ × ℝ) × V)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      ∀ r : ℝ, HasDerivAt
        (fun t : ℝ ↦ ω.floerOperator J (fun w y ↦ Ks w y + t * δK w y) Kt u z) v r := by
  obtain ⟨δK, hs, hc, hsub, -, h⟩ :=
    ω.exists_contDiff_floerOperator_add_const_mul_left J Ks Kt u z v hKs hU
  refine ⟨δK, hs, hc, hsub, fun r ↦ ?_⟩
  simp_rw [h]
  simpa using ((hasDerivAt_id r).smul_const v).const_add (ω.floerOperator J Ks Kt u z)

/-- Adding a variation `r δK` supported over `Ω`, on which `Ks` is differentiable along `u`,
changes the Floer operator at every point by `-r X_{δK z}(u z)`. -/
private theorem floerOperator_add_const_mul_left_of_tsupport_subset (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {Ω : Set (ℝ × ℝ)} (hKs : ∀ z ∈ Ω, DifferentiableAt ℝ (Ks z) (u z))
    {δK : ℝ × ℝ → V → ℝ} (hδK : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK))
    (hδKΩ : tsupport (Function.uncurry δK) ⊆ Ω ×ˢ univ) (z : ℝ × ℝ) (r : ℝ) :
    ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
      ω.floerOperator J Ks Kt u z - r • ω.hamiltonianVectorField (δK z) (u z) := by
  by_cases hz : z ∈ Ω
  · exact ω.floerOperator_add_const_mul_left J Ks Kt δK u z (hKs z hz)
      ((hδK.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (u z)) r
  · -- Over a point outside `Ω` the variation vanishes identically.
    have h0 : δK z = fun _ ↦ 0 := funext fun y ↦
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry δK) (x := (z, y))
        fun h ↦ hz (hδKΩ h).1
    simp [floerOperator_def, h0]

/-- **Hamiltonian variations realize every field along a map.** Let `u` be continuous on an open
set `Ω` on which `Ks` is differentiable along `u`, and let `W` be a neighborhood of each point
`(z, u z)` with `z ∈ Ω`. For every smooth compactly supported field `ξ` with support in `Ω`, a
smooth Hamiltonian variation `δK` with compact support in `W` changes the Floer operator by
`r ξ`: `F(Ks + r δK) = F(Ks) + r ξ` at every point and for every real `r`. -/
theorem exists_contDiff_floerOperator_add_const_mul_left_eq_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hKs : ∀ z ∈ Ω, DifferentiableAt ℝ (Ks z) (u z))
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ Ω, W ∈ 𝓝 (z, u z))
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ)
    (hξΩ : tsupport ξ ⊆ Ω) :
    ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ W ∧
      ∀ z r, ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
        ω.floerOperator J Ks Kt u z + r • ξ z := by
  have hWΩ (z : ℝ × ℝ) (hz : z ∈ Ω) : W ∩ Ω ×ˢ univ ∈ 𝓝 (z, u z) :=
    inter_mem (hW z hz) ((hΩ.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
  obtain ⟨δK, hδK, hδKc, hδKW, hX⟩ := ω.exists_contDiff_hamiltonianVectorField_comp_eq hu hWΩ
    (ξ := -ξ) hξ.neg hξc.neg (by rwa [tsupport_neg])
  refine ⟨δK, hδK, hδKc, hδKW.trans inter_subset_left, fun z r ↦ ?_⟩
  rw [floerOperator_add_const_mul_left_of_tsupport_subset ω J Ks Kt u hKs hδK
    (hδKW.trans inter_subset_right), hX, Pi.neg_apply, smul_neg, sub_neg_eq_add]

variable {μ : Measure (ℝ × ℝ)}

/-- **Hamiltonian variations detect cokernel elements of the Floer operator.** Let `u` be
continuous on an open set `Ω` on which `Ks` is differentiable along `u`, let `W` be a neighborhood
of each point `(z, u z)` with `z ∈ Ω`, and let `η` be a locally integrable field of covectors on
`Ω`. If `η` annihilates the change `F(Ks + δK) - F(Ks)` of the Floer operator for every smooth
compactly supported Hamiltonian variation `δK` supported in `W`, then `η` vanishes almost
everywhere on `Ω`. No hypothesis is placed on `J`, on `Kt`, or on the derivative of `u`; in
particular `u` may be constant. -/
theorem ae_eq_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hKs : ∀ z ∈ Ω, DifferentiableAt ℝ (Ks z) (u z))
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ Ω, W ∈ 𝓝 (z, u z)) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : LocallyIntegrableOn η Ω μ)
    (h : ∀ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) →
      HasCompactSupport (Function.uncurry δK) → tsupport (Function.uncurry δK) ⊆ W →
        ∫ z, η z (ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
          ω.floerOperator J Ks Kt u z) ∂μ = 0) :
    ∀ᵐ z ∂μ, z ∈ Ω → η z = 0 := by
  have hWΩ (z : ℝ × ℝ) (hz : z ∈ Ω) : W ∩ Ω ×ˢ univ ∈ 𝓝 (z, u z) :=
    inter_mem (hW z hz) ((hΩ.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)
  refine ω.ae_eq_zero_of_forall_integral_apply_hamiltonianVectorField_eq_zero hΩ hu hWΩ hη
    fun δK hδK hδKc hδKW ↦ ?_
  have hF (z : ℝ × ℝ) : ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
      ω.floerOperator J Ks Kt u z = -ω.hamiltonianVectorField (δK z) (u z) := by
    have h₁ := floerOperator_add_const_mul_left_of_tsupport_subset ω J Ks Kt u hKs hδK
      (hδKW.trans inter_subset_right) z 1
    simp only [one_mul, one_smul] at h₁
    rw [h₁, sub_sub_cancel_left]
  have h' := h δK hδK hδKc (hδKW.trans inter_subset_left)
  simp_rw [hF, map_neg, integral_neg, neg_eq_zero] at h'
  exact h'

/-- **Hamiltonian variations detect continuous cokernel elements of the Floer operator.** For a
continuous field `η` of covectors on `Ω` and a locally finite measure that is positive on open
sets, such as Lebesgue measure, the conclusion of
`SymplecticForm.ae_eq_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero` holds at every
point of `Ω`. -/
theorem eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hKs : ∀ z ∈ Ω, DifferentiableAt ℝ (Ks z) (u z))
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ Ω, W ∈ 𝓝 (z, u z)) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContinuousOn η Ω)
    (h : ∀ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) →
      HasCompactSupport (Function.uncurry δK) → tsupport (Function.uncurry δK) ⊆ W →
        ∫ z, η z (ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
          ω.floerOperator J Ks Kt u z) ∂μ = 0) :
    EqOn η 0 Ω := by
  have hae := ω.ae_eq_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero J Ks Kt u hΩ
    hu hKs hW (hη.locallyIntegrableOn hΩ.measurableSet) h
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩ.measurableSet).mpr hae) hΩ hη
    continuousOn_const

end TauCeti.SymplecticForm
