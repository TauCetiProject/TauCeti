/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Analysis.Sobolev.Morrey.Basic

/-!
# The Sobolev form of the quadratic estimate for the Floer operator

Let `(V, ω)` be a finite-dimensional symplectic vector space and let
`F(u) = ∂s u - X_Ks(u) + J(u)(∂t u - X_Kt(u))` be the Floer operator
(`TauCeti.SymplecticForm.floerOperator`) with linearization `D_w` at a map `w`
(`TauCeti.SymplecticForm.floerLinearization`). Gluing and transversality solve `F(w + ξ) = 0`
near an approximate solution `w` by the Newton iteration of
`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`, in a Banach space of increments `ξ` with a
bounded right inverse of `D_w`. That theorem asks for the nonlinear part
`N_w(ξ) = F(w + ξ) - F(w) - D_w ξ` to be quadratically small in its norms,

`‖N_w(ξ₁) - N_w(ξ₂)‖ ≤ (L / 2) (‖ξ₁‖ + ‖ξ₂‖) ‖ξ₁ - ξ₂‖`.

The usual choice is `ξ ∈ W^{1,p}` and `N_w(ξ) ∈ Lᵖ` for `p > 2`, the dimension of the domain. This
file proves this estimate, starting from the pointwise quadratic estimate of
`TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate`
(`SymplecticForm.exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le`).
The norms are taken over an open set `Ω` of the domain `ℝ × ℝ`; as there, the coefficients `J`,
`Ks`, `Kt` are pulled back along a parameter map `φ : ℝ × ℝ → P`, and the graph of `(φ, w)` over
`Ω` lies in a compact set `K` on which they are `C²`, `C³` and `C³`.

* **The estimate with supremum norms.** If `‖ξ₁‖, ‖ξ₂‖ ≤ ε ≤ δ` and `‖ξ₁ - ξ₂‖ ≤ η` pointwise on
  `Ω`, and the slice defect `∂t w - X_Kt(w)` of the base map is bounded by `B` there, then
  `‖N_w(ξ₁) - N_w(ξ₂)‖_{Lᵖ(Ω)} ≤ C (ε (1 + B) ‖ξ₁ - ξ₂‖_{Lᵖ} + η ‖Dξ₁‖_{Lᵖ} + ε ‖D(ξ₁ - ξ₂)‖_{Lᵖ})`
  (`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le`).
  This holds for every `p ≥ 1` and every open set `Ω`, with `δ` and `C` depending only on `K` and
  the coefficients.
* **The estimate in `W^{1,p}`.** For `p > 2`, Morrey's supremum bound
  (`TauCeti.exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv`) controls the supremum norms on a
  convex open set by the `W^{1,p}` norm `‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)}`. Hence if
  `‖ξ₁‖_{1,p}, ‖ξ₂‖_{1,p} ≤ δ`, then
  `‖N_w(ξ₁) - N_w(ξ₂)‖_{Lᵖ(Ω)} ≤ C (1 + B) (‖ξ₁‖_{1,p} + ‖ξ₂‖_{1,p}) ‖ξ₁ - ξ₂‖_{1,p}`
  by
  `exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex`,
  which has the form of the quadratic hypothesis of the Newton iteration, once the increments are
  placed in a Banach completion. Its case `ξ₂ = 0`, the `floerOperator_add_sub` form of this
  theorem, is `‖F(w + ξ) - F(w) - D_w ξ‖_{Lᵖ(Ω)} ≤ C (1 + B) ‖ξ‖_{1,p}²`.

The constants of the `W^{1,p}` estimate do not depend on the size of `Ω`: they only depend on `p`
and on a radius `r` and a measure `m > 0` with `m ≤ |Ω ∩ B(z, r)|` for every `z ∈ Ω`. The
rectangles `(a, b) × (c, d)` with sides of length at least one satisfy this with `r = m = 1`
(`TauCeti.one_le_volume_Ioo_prod_Ioo_inter_ball`), so the estimate is uniform over the long necks
`(-R, R) × (0, 1)` of glued Floer solutions, with the coefficients `t`-dependent through
`φ z = z.2` as on cylindrical ends.

The increments are `C¹` on `Ω`. The almost everywhere strong measurability of the left-hand side
on `Ω`, without which its `Lᵖ` seminorm is `∞` by convention, is a hypothesis; it holds for instance
when the left-hand side is continuous on `Ω`. No Sobolev completion is constructed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.5, on the quadratic estimate in `W^{1,p}` and the implicit function theorem, and
  Chapter 10, on gluing.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

namespace TauCeti.SymplecticForm

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ω : SymplecticForm V)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ} {K : Set (P × V)}

/-- The pointwise quadratic estimate with the supremum bounds `ε`, `η`, `B` inserted and the slice
derivatives bounded by the full derivatives: the step integrated in
`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le`. -/
private theorem exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le_mul
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (φ : ℝ × ℝ → P) (w ξ₁ ξ₂ : ℝ × ℝ → V) (z : ℝ × ℝ)
      (ε η B : ℝ≥0), DifferentiableAt ℝ w z → DifferentiableAt ℝ ξ₁ z →
      DifferentiableAt ℝ ξ₂ z → (φ z, w z) ∈ K →
      ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ ≤ B →
      ‖ξ₁ z‖ ≤ ε → ‖ξ₂ z‖ ≤ ε → ε ≤ δ → ‖ξ₁ z - ξ₂ z‖ ≤ η →
      ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z‖ ≤
        C * (ε * (1 + B) * ‖(ξ₁ - ξ₂) z‖ + η * ‖fderiv ℝ ξ₁ z‖ +
          ε * ‖fderiv ℝ (ξ₁ - ξ₂) z‖) := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    ω.exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le hK hJ hKs hKt
  refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, C.toNNReal,
    fun φ w ξ₁ ξ₂ z ε η B hw hd₁ hd₂ hwK hB h₁ h₂ hεδ hη => ?_⟩
  have hεδ' : (ε : ℝ) ≤ δ := (NNReal.coe_le_coe.2 hεδ).trans_eq (Real.coe_toNNReal _ hδ.le)
  have hDi (L : ℝ × ℝ →L[ℝ] V) : ‖L stdComplexLineImag‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans_eq (by simp [stdComplexLineImag_eq])
  have hsub : fderiv ℝ ξ₁ z stdComplexLineImag - fderiv ℝ ξ₂ z stdComplexLineImag =
      fderiv ℝ (ξ₁ - ξ₂) z stdComplexLineImag := by
    rw [fderiv_sub hd₁ hd₂, sub_apply]
  refine (hC φ w ξ₁ ξ₂ z hw hd₁ hd₂ hwK (h₁.trans hεδ') (h₂.trans hεδ')).trans ?_
  rw [hsub, Pi.sub_apply]
  refine (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (by positivity)).trans ?_
  gcongr
  · exact max_le h₁ h₂
  · exact hDi _
  · exact hDi _

/-- **The quadratic estimate for the Floer operator in `Lᵖ`, with supremum norms.** Let `K` be a
compact set of pairs `(p, y)` of a parameter and a target point at which `J` is jointly `C²` and
the Hamiltonians `Ks`, `Kt` are jointly `C³`. There are `δ > 0` and `C` such that the following
holds for every `p ≥ 1`, every open set `Ω` of the domain and every parameter map `φ`. Let `w` be
differentiable on `Ω`, with graph `(φ z, w z) ∈ K` and slice defect
`‖∂t w - X_Kt(w)‖ ≤ B` over `Ω`, and let `ξ₁`, `ξ₂` be `C¹` on `Ω` with `‖ξ₁‖, ‖ξ₂‖ ≤ ε ≤ δ` and
`‖ξ₁ - ξ₂‖ ≤ η` on `Ω`. Then the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)`
satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_{Lᵖ(Ω)}
  ≤ C (ε (1 + B) ‖ξ₁ - ξ₂‖_{Lᵖ(Ω)} + η ‖Dξ₁‖_{Lᵖ(Ω)} + ε ‖D(ξ₁ - ξ₂)‖_{Lᵖ(Ω)})`,
provided its left-hand side is almost everywhere strongly measurable on `Ω`. -/
theorem exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (p : ℝ≥0∞) (Ω : Set (ℝ × ℝ)) (φ : ℝ × ℝ → P)
      (w ξ₁ ξ₂ : ℝ × ℝ → V) (ε η B : ℝ≥0), 1 ≤ p → IsOpen Ω → DifferentiableOn ℝ w Ω →
      ContDiffOn ℝ 1 ξ₁ Ω → ContDiffOn ℝ 1 ξ₂ Ω → (∀ z ∈ Ω, (φ z, w z) ∈ K) →
      (∀ z ∈ Ω,
        ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ₑ ≤ B) →
      (∀ z ∈ Ω, ‖ξ₁ z‖ₑ ≤ ε) → (∀ z ∈ Ω, ‖ξ₂ z‖ₑ ≤ ε) → ε ≤ δ →
      (∀ z ∈ Ω, ‖ξ₁ z - ξ₂ z‖ₑ ≤ η) →
      AEStronglyMeasurable (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z) (volume.restrict Ω) →
      eLpNorm (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z) p (volume.restrict Ω) ≤
        C * (ε * (1 + B) * eLpNorm (ξ₁ - ξ₂) p (volume.restrict Ω) +
          η * eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) +
          ε * eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p (volume.restrict Ω)) := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    ω.exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le_mul hK hJ
      hKs hKt
  refine ⟨δ, hδ, C, fun p Ω φ w ξ₁ ξ₂ ε η B hp hΩ hw hξ₁ hξ₂ hwK hB hε₁ hε₂ hεδ hη hN => ?_⟩
  have hξ : ContDiffOn ℝ 1 (ξ₁ - ξ₂) Ω := hξ₁.sub hξ₂
  -- The pointwise estimate at every point of `Ω`.
  have hpt : ∀ z ∈ Ω, ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z))
        (w + ξ₁) z -
      ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
      ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
        (ξ₁ - ξ₂) z‖ ≤
      (C : ℝ) * (((ε * (1 + B) : ℝ≥0) : ℝ) * ‖(ξ₁ - ξ₂) z‖ +
        (η : ℝ) * ‖fderiv ℝ ξ₁ z‖ + (ε : ℝ) * ‖fderiv ℝ (ξ₁ - ξ₂) z‖) := fun z hz => by
    have hzΩ : Ω ∈ nhds z := hΩ.mem_nhds hz
    push_cast
    exact hC φ w ξ₁ ξ₂ z ε η B (hw.differentiableAt hzΩ)
      ((hξ₁.differentiableOn one_ne_zero).differentiableAt hzΩ)
      ((hξ₂.differentiableOn one_ne_zero).differentiableAt hzΩ) (hwK z hz)
      (by exact_mod_cast eNorm_le_coe.1 (hB z hz)) (by exact_mod_cast eNorm_le_coe.1 (hε₁ z hz))
      (by exact_mod_cast eNorm_le_coe.1 (hε₂ z hz)) hεδ (by exact_mod_cast eNorm_le_coe.1 (hη z hz))
  -- Integrate the pointwise bound.
  have hm₁ : AEStronglyMeasurable (ξ₁ - ξ₂) (volume.restrict Ω) :=
    hξ.continuousOn.aestronglyMeasurable hΩ.measurableSet
  have hm₂ : AEStronglyMeasurable (fderiv ℝ ξ₁) (volume.restrict Ω) :=
    (hξ₁.continuousOn_fderiv_of_isOpen hΩ le_rfl).aestronglyMeasurable hΩ.measurableSet
  have hm₃ : AEStronglyMeasurable (fderiv ℝ (ξ₁ - ξ₂)) (volume.restrict Ω) :=
    (hξ.continuousOn_fderiv_of_isOpen hΩ le_rfl).aestronglyMeasurable hΩ.measurableSet
  refine (eLpNorm_mono_ae_real hN (ae_restrict_of_forall_mem hΩ.measurableSet hpt)).trans ?_
  have hsplit : (fun z ↦ (C : ℝ) * (((ε * (1 + B) : ℝ≥0) : ℝ) * ‖(ξ₁ - ξ₂) z‖ +
      (η : ℝ) * ‖fderiv ℝ ξ₁ z‖ + (ε : ℝ) * ‖fderiv ℝ (ξ₁ - ξ₂) z‖)) =
      (C : ℝ) • ((((ε * (1 + B) : ℝ≥0) : ℝ) • fun z ↦ ‖(ξ₁ - ξ₂) z‖) +
        ((η : ℝ) • fun z ↦ ‖fderiv ℝ ξ₁ z‖) + ((ε : ℝ) • fun z ↦ ‖fderiv ℝ (ξ₁ - ξ₂) z‖)) := by
    ext z
    simp [smul_eq_mul]
  rw [hsplit, eLpNorm_const_smul, NNReal.eNorm_eq]
  gcongr
  refine (eLpNorm_add_le hp).trans (add_le_add ((eLpNorm_add_le hp).trans (add_le_add ?_ ?_)) ?_)
  · rw [eLpNorm_const_smul, NNReal.eNorm_eq, eLpNorm_norm _ hm₁, ENNReal.coe_mul, ENNReal.coe_add,
      ENNReal.coe_one]
  · rw [eLpNorm_const_smul, NNReal.eNorm_eq, eLpNorm_norm _ hm₂]
  · rw [eLpNorm_const_smul, NNReal.eNorm_eq, eLpNorm_norm _ hm₃]

/-- The arithmetic combining the three terms of the supremum-norm estimate into the quadratic
`W^{1,p}` bound, with `a` the constant of Morrey's supremum bound. -/
private theorem quadratic_terms_le {a e d d' S S₁ S₂ B : ℝ≥0∞} (he : e ≤ S) (hd : d ≤ S₁ + S₂)
    (hd' : d' ≤ S) :
    a * (S₁ + S₂) * (1 + B) * e + a * S * d + a * (S₁ + S₂) * d' ≤
      3 * a * (1 + B) * (S₁ + S₂) * S := by
  have h₁ : a * (S₁ + S₂) * S ≤ a * (S₁ + S₂) * (1 + B) * S :=
    calc a * (S₁ + S₂) * S = a * (S₁ + S₂) * 1 * S := by ring
      _ ≤ a * (S₁ + S₂) * (1 + B) * S := by gcongr; exact le_self_add
  calc a * (S₁ + S₂) * (1 + B) * e + a * S * d + a * (S₁ + S₂) * d' ≤
        a * (S₁ + S₂) * (1 + B) * S + a * (S₁ + S₂) * S + a * (S₁ + S₂) * S :=
        add_le_add (add_le_add (mul_le_mul_right he _)
          ((mul_le_mul_right hd _).trans_eq (by ring))) (mul_le_mul_right hd' _)
    _ ≤ a * (S₁ + S₂) * (1 + B) * S + a * (S₁ + S₂) * (1 + B) * S +
        a * (S₁ + S₂) * (1 + B) * S := by gcongr
    _ = 3 * a * (1 + B) * (S₁ + S₂) * S := by ring

/-- The `W^{1,p}` seminorm `‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)}` of a difference of maps that are `C¹` on an
open set `Ω` is at most the sum of their seminorms. -/
private theorem eLpNorm_sub_add_eLpNorm_fderiv_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    {ξ₁ ξ₂ : ℝ × ℝ → E} (hξ₁ : ContDiffOn ℝ 1 ξ₁ Ω) (hξ₂ : ContDiffOn ℝ 1 ξ₂ Ω) :
    eLpNorm (ξ₁ - ξ₂) p (volume.restrict Ω) + eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p (volume.restrict Ω) ≤
      eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) +
        (eLpNorm ξ₂ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω)) := by
  have hfd : fderiv ℝ (ξ₁ - ξ₂) =ᵐ[volume.restrict Ω] fderiv ℝ ξ₁ - fderiv ℝ ξ₂ :=
    ae_restrict_of_forall_mem hΩ.measurableSet fun z hz => fderiv_sub
      ((hξ₁.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz))
      ((hξ₂.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz))
  calc _ ≤ eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm ξ₂ p (volume.restrict Ω) +
        (eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) +
          eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω)) := by
        gcongr
        · exact eLpNorm_sub_le hp
        · rw [eLpNorm_congr_ae hfd]
          exact eLpNorm_sub_le hp
    _ = _ := by ring

/-- The choice of the radius `δ₁ / (2 (a + 1))` in the `W^{1,p}` estimate makes `a` times the sum of
two such radii at most `δ₁`. -/
private theorem mul_add_div_two_mul_add_one_le (a δ₁ : ℝ≥0) :
    a * (δ₁ / (2 * (a + 1)) + δ₁ / (2 * (a + 1))) ≤ δ₁ := by
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [← add_div, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [a.coe_nonneg, δ₁.coe_nonneg]

/-- **The quadratic estimate for the Floer operator in `W^{1,p}`.** Let `K` be a compact set of
pairs `(p, y)` of a parameter and a target point at which `J` is jointly `C²` and the Hamiltonians
`Ks`, `Kt` are jointly `C³`, let `p > 2`, and let `r : ℝ` and `m ≠ 0`. There are `δ > 0` and `C`
such that the following holds for every convex open set `Ω` of the domain with
`m ≤ |Ω ∩ B(z, r)|` for all `z ∈ Ω`, and every parameter map `φ`. Write
`‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)}`. Let `w` be differentiable on `Ω`, with graph
`(φ z, w z) ∈ K` and slice defect `‖∂t w - X_Kt(w)‖ ≤ B` over `Ω`, and let `ξ₁`, `ξ₂` be `C¹` on
`Ω` with `‖ξ₁‖_{1,p}, ‖ξ₂‖_{1,p} ≤ δ`. Then the Floer operator with coefficients `J (φ z)`,
`Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_{Lᵖ(Ω)}
  ≤ C (1 + B) (‖ξ₁‖_{1,p} + ‖ξ₂‖_{1,p}) ‖ξ₁ - ξ₂‖_{1,p}`,
provided its left-hand side is almost everywhere strongly measurable on `Ω`. The constants do not
depend on the size of `Ω`. For the remainder `ξ ↦ F(w + ξ) - F(w) - D_w ξ` this has the form of
the quadratic hypothesis of `TauCeti.exists_mem_range_norm_le_add_add_eq_zero`; applying that
theorem still needs a Banach space of increments (a Sobolev completion) and the measurability side
condition. -/
theorem
    exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) {p : ℝ≥0} (hp : 2 < p) (r : ℝ)
    {m : ℝ≥0∞} (hm : m ≠ 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (Ω : Set (ℝ × ℝ)) (φ : ℝ × ℝ → P) (w ξ₁ ξ₂ : ℝ × ℝ → V)
      (B : ℝ≥0), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, m ≤ volume (Ω ∩ ball z r)) →
      DifferentiableOn ℝ w Ω → ContDiffOn ℝ 1 ξ₁ Ω → ContDiffOn ℝ 1 ξ₂ Ω →
      (∀ z ∈ Ω, (φ z, w z) ∈ K) →
      (∀ z ∈ Ω,
        ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ₑ ≤ B) →
      eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) ≤ δ →
      eLpNorm ξ₂ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω) ≤ δ →
      AEStronglyMeasurable (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z) (volume.restrict Ω) →
      eLpNorm (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z) p (volume.restrict Ω) ≤
        C * (1 + B) *
          (eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) +
            (eLpNorm ξ₂ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω))) *
          (eLpNorm (ξ₁ - ξ₂) p (volume.restrict Ω) +
            eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p (volume.restrict Ω)) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨CM, hCM⟩ := exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv (μ := volume)
    (E := ℝ × ℝ) (F := V) hp1 (by rw [finrank_prod, finrank_self]; norm_num; exact hp) r hm
  obtain ⟨δ₁, hδ₁, C₁, h₁⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le hK hJ
      hKs hKt
  refine ⟨δ₁ / (2 * (CM + 1)), by positivity, 3 * C₁ * CM, fun Ω φ w ξ₁ ξ₂ B hΩ hΩc hfat hw hξ₁
    hξ₂ hwK hB hS₁ hS₂ hN => ?_⟩
  set μ := volume.restrict Ω
  set S₁ := eLpNorm ξ₁ p μ + eLpNorm (fderiv ℝ ξ₁) p μ
  set S₂ := eLpNorm ξ₂ p μ + eLpNorm (fderiv ℝ ξ₂) p μ
  set S := eLpNorm (ξ₁ - ξ₂) p μ + eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p μ
  have hξ : ContDiffOn ℝ 1 (ξ₁ - ξ₂) Ω := hξ₁.sub hξ₂
  -- The `W^{1,p}` norm of the difference is finite.
  have hSle : S ≤ S₁ + S₂ :=
    eLpNorm_sub_add_eLpNorm_fderiv_sub_le (by exact_mod_cast hp1) hΩ hξ₁ hξ₂
  have hS₁₂ : S₁ + S₂ ≠ ∞ := ENNReal.add_ne_top.2
    ⟨ne_top_of_le_ne_top ENNReal.coe_ne_top hS₁, ne_top_of_le_ne_top ENNReal.coe_ne_top hS₂⟩
  have hS : S ≠ ∞ := (hSle.trans_lt hS₁₂.lt_top).ne
  -- The supremum bounds, by Morrey's inequality.
  have hsup (ξ : ℝ × ℝ → V) (hξ : ContDiffOn ℝ 1 ξ Ω) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      ‖ξ z‖ₑ ≤ CM * (eLpNorm ξ p μ + eLpNorm (fderiv ℝ ξ) p μ) :=
    hCM Ω ξ z hΩ hΩc hξ hz (hfat z hz)
  have hε : ((CM * (S₁ + S₂)).toNNReal : ℝ≥0∞) = CM * (S₁ + S₂) :=
    ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hS₁₂)
  have hη : ((CM * S).toNNReal : ℝ≥0∞) = CM * S :=
    ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hS)
  have hεδ : (CM * (S₁ + S₂)).toNNReal ≤ δ₁ := by
    rw [← ENNReal.coe_le_coe, hε]
    calc (CM : ℝ≥0∞) * (S₁ + S₂) ≤
          CM * ((δ₁ / (2 * (CM + 1)) : ℝ≥0) + (δ₁ / (2 * (CM + 1)) : ℝ≥0)) := by gcongr
      _ = ((CM * (δ₁ / (2 * (CM + 1)) + δ₁ / (2 * (CM + 1))) : ℝ≥0) : ℝ≥0∞) := by norm_cast
      _ ≤ δ₁ := ENNReal.coe_le_coe.2 (mul_add_div_two_mul_add_one_le CM δ₁)
  have h := h₁ p Ω φ w ξ₁ ξ₂ (CM * (S₁ + S₂)).toNNReal (CM * S).toNNReal B
    (by exact_mod_cast hp1) hΩ hw hξ₁ hξ₂ hwK hB
    (fun z hz => (hsup ξ₁ hξ₁ z hz).trans (by rw [hε]; exact mul_le_mul_right le_self_add _))
    (fun z hz => (hsup ξ₂ hξ₂ z hz).trans (by rw [hε]; exact mul_le_mul_right le_add_self _)) hεδ
    (fun z hz => (hsup (ξ₁ - ξ₂) hξ z hz).trans_eq hη.symm) hN
  rw [hε, hη] at h
  refine (h.trans (mul_le_mul_right (quadratic_terms_le le_self_add
    ((le_add_self : _ ≤ S₁).trans le_self_add) le_add_self) _)).trans_eq ?_
  push_cast
  ring

/-- **The quadratic estimate for the Floer operator at a map, in `W^{1,p}`.** Under the
hypotheses of
`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex`,
there are `δ > 0` and `C` such that every increment `ξ` which is `C¹` on `Ω` with
`‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)} ≤ δ` satisfies
`‖F(w + ξ) - F(w) - D_w ξ‖_{Lᵖ(Ω)} ≤ C (1 + B) ‖ξ‖_{1,p}²`,
provided its left-hand side is almost everywhere strongly measurable on `Ω`. -/
theorem
exists_pos_forall_eLpNorm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le_of_convex
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) {p : ℝ≥0} (hp : 2 < p) (r : ℝ)
    {m : ℝ≥0∞} (hm : m ≠ 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (Ω : Set (ℝ × ℝ)) (φ : ℝ × ℝ → P) (w ξ : ℝ × ℝ → V)
      (B : ℝ≥0), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, m ≤ volume (Ω ∩ ball z r)) →
      DifferentiableOn ℝ w Ω → ContDiffOn ℝ 1 ξ Ω → (∀ z ∈ Ω, (φ z, w z) ∈ K) →
      (∀ z ∈ Ω,
        ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ₑ ≤ B) →
      eLpNorm ξ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ) p (volume.restrict Ω) ≤ δ →
      AEStronglyMeasurable (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z)
        (volume.restrict Ω) →
      eLpNorm (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z)
        p (volume.restrict Ω) ≤
        C * (1 + B) *
          (eLpNorm ξ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ) p (volume.restrict Ω)) ^ 2 := by
  obtain ⟨δ, hδ, C, h⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex
      hK hJ hKs hKt hp r hm
  refine ⟨δ, hδ, C, fun Ω φ w ξ B hΩ hΩc hfat hw hξ hwK hB hS hN => ?_⟩
  have h0 : ContDiffOn ℝ 1 (0 : ℝ × ℝ → V) Ω := contDiffOn_const
  have hzero : eLpNorm (0 : ℝ × ℝ → V) p (volume.restrict Ω) +
      eLpNorm (fderiv ℝ (0 : ℝ × ℝ → V)) p (volume.restrict Ω) = 0 := by
    rw [fderiv_zero, eLpNorm_zero, eLpNorm_zero (ε := ℝ × ℝ →L[ℝ] V), add_zero]
  have := h Ω φ w ξ 0 B hΩ hΩc hfat hw hξ h0 hwK hB hS (by rw [hzero]; positivity)
    (by simpa only [add_zero, sub_zero] using hN)
  simp only [add_zero, sub_zero, hzero] at this
  rw [sq, ← mul_assoc]
  exact this

end TauCeti.SymplecticForm
