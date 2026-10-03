/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Coordinate
public import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Cusp meridians and their lifts

For a normalized cusp datum `D`, the horizontal path in scaling coordinates from `σ(z)`
to `σ(z) + n w` projects under the q-coordinate to the loop
`q(z) exp (2 π i n t)`. For `n = 1` this traverses its circle counterclockwise once.
Its unique lift starting at `z` ends at `D.generator • z`, not at its inverse. More generally,
the endpoint for `n` signed turns is `D.generator ^ n • z`.

These paths stay at constant scaled height, so they lie in every horodisc containing their
basepoint. Reversing a meridian negates the number of turns and inverts its endpoint
transformation. This fixes the orientation convention for cusp relations in quotient
presentations.

Uniqueness uses Mathlib's exponential covering map, rather than a chosen logarithm along
the loop. No discreteness or cofiniteness assumption is needed once the normalized datum
is supplied.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Function UpperHalfPlane
open scoped Complex.UnitDisc MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- The lift of `n` signed turns around a cusp: horizontal translation through `n` widths
in the scaling coordinate. -/
def meridianLift (n : ℤ) (z : ℍ) : Path z (D.generator ^ n • z) where
  toFun t := D.scaling⁻¹ • (((t : ℝ) * (n : ℝ) * D.width) +ᵥ (D.scaling • z))
  continuous_toFun := by
    apply (continuous_const_smul D.scaling⁻¹).comp
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    simp only [Function.comp_def, coe_vadd]
    fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, one_mul]
    rw [← scaling_smul_generator_zpow, inv_smul_smul]

/-- The horizontal lift, evaluated at a time in the unit interval. -/
theorem meridianLift_apply (n : ℤ) (z : ℍ) (t : unitInterval) :
    meridianLift D n z t =
      D.scaling⁻¹ • (((t : ℝ) * (n : ℝ) * D.width) +ᵥ (D.scaling • z)) := (rfl)

/-- In scaling coordinates, a meridian lift is horizontal translation at constant speed. -/
@[simp]
theorem scaling_smul_meridianLift (n : ℤ) (z : ℍ) (t : unitInterval) :
    D.scaling • meridianLift D n z t =
      ((t : ℝ) * (n : ℝ) * D.width) +ᵥ (D.scaling • z) := by
  rw [meridianLift_apply, smul_inv_smul]

/-- The cusp meridian with `n` signed turns, based at the q-coordinate of `z`. -/
def meridian (n : ℤ) (z : ℍ) : Path (qCoordinate D z) (qCoordinate D z) :=
  ((meridianLift D n z).map (isOpenQuotientMap_qCoordinate D).continuous).cast rfl
    (qCoordinate_smul_of_mem D (D.mem_stabilizer_iff.mpr ⟨n, rfl⟩) z).symm

/-- The meridian is the q-projection of its horizontal lift. -/
@[simp]
theorem meridian_apply (n : ℤ) (z : ℍ) (t : unitInterval) :
    meridian D n z t = qCoordinate D (meridianLift D n z t) := (rfl)

/-- The meridian makes exactly `n` signed turns about zero. Positive turns are
counterclockwise in the complex q-plane. -/
theorem coe_meridian (n : ℤ) (z : ℍ) (t : unitInterval) :
    ((meridian D n z t : 𝔻) : ℂ) =
      coordinate D z * Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I) * (t : ℝ)) := by
  rw [meridian_apply, coe_qCoordinate, coordinate_apply, scaling_smul_meridianLift,
    coe_vadd, coordinate_apply]
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [D.width_pos.ne']
  ring

/-- Continuous lifts with the same q-projection agree if they agree at one point of a
preconnected source. -/
theorem eq_of_coordinate_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {f g : A → ℍ} (hf : Continuous f) (hg : Continuous g)
    (hq : ∀ a, coordinate D (f a) = coordinate D (g a)) (a₀ : A) (h₀ : f a₀ = g a₀) :
    f = g := by
  let F (z : ℍ) : ℂ := 2 * Real.pi * Complex.I * (↑(D.scaling • z) : ℂ) / D.width
  have hF : Continuous F := by fun_prop
  have he : (fun w : ℂ ↦ (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {w : ℂ // w ≠ 0})) ∘
      (F ∘ f) = (fun w : ℂ ↦ (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {w : ℂ // w ≠ 0})) ∘
      (F ∘ g) := by
    funext a
    apply Subtype.ext
    simpa only [F, Function.comp_apply, coordinate_apply, Function.Periodic.qParam] using hq a
  have hfg := Complex.isCoveringMap_exp.eq_of_comp_eq (hF.comp hf) (hF.comp hg) he a₀
    (congrArg F h₀)
  funext a
  apply (MulAction.injective D.scaling)
  apply UpperHalfPlane.coe_injective
  have h := congrFun hfg a
  have hw : (D.width : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr D.width_pos.ne'
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  exact mul_left_cancel₀ hc ((div_left_inj' hw).mp h)

/-- The horizontal path is the unique continuous lift of the meridian starting at `z`.
In particular its endpoint is the `n`th power of the selected primitive generator. -/
theorem eq_meridianLift_of_qCoordinate_eq (n : ℤ) (z : ℍ) {f : unitInterval → ℍ}
    (hf : Continuous f) (h₀ : f 0 = z)
    (hq : ∀ t, qCoordinate D (f t) = meridian D n z t) :
    f = meridianLift D n z := by
  refine eq_of_coordinate_eq D hf (meridianLift D n z).continuous (fun t ↦ ?_) 0 ?_
  · simpa only [meridian_apply, coe_qCoordinate] using
      congrArg (fun q : {q : 𝔻 // q ≠ 0} ↦ ((q : 𝔻) : ℂ)) (hq t)
  · simpa using h₀

/-- A lift of an `n`-turn meridian starting at `z` ends at `generator ^ n • z`. -/
theorem meridian_lift_endpoint (n : ℤ) (z : ℍ) {f : unitInterval → ℍ}
    (hf : Continuous f) (h₀ : f 0 = z)
    (hq : ∀ t, qCoordinate D (f t) = meridian D n z t) :
    f 1 = D.generator ^ n • z := by
  rw [eq_meridianLift_of_qCoordinate_eq D n z hf h₀ hq]
  exact (meridianLift D n z).target

/-- Negating the turns reverses the lifted path and translates it back to its original
basepoint by the inverse endpoint transformation. -/
theorem meridianLift_neg_apply (n : ℤ) (z : ℍ) (t : unitInterval) :
    meridianLift D (-n) z t = D.generator ^ (-n) • (meridianLift D n z).symm t := by
  apply (MulAction.injective D.scaling)
  simp only [scaling_smul_meridianLift, scaling_smul_generator_zpow, Path.symm_apply,
    Function.comp_apply, vadd_vadd]
  congr 1
  simp only [Int.cast_neg, unitInterval.coe_symm_eq]
  ring

/-- Reversing the orientation of a cusp meridian negates its turns. Consequently the
positive primitive deck generator is replaced by its inverse. -/
@[simp]
theorem meridian_neg (n : ℤ) (z : ℍ) : meridian D (-n) z = (meridian D n z).symm := by
  apply Path.ext
  funext t
  rw [meridian_apply, meridianLift_neg_apply,
    qCoordinate_smul_of_mem D (D.mem_stabilizer_iff.mpr ⟨-n, rfl⟩)]
  simp only [Path.symm_apply, Function.comp_apply, meridian_apply]

/-- The zero-turn meridian is constant. -/
@[simp]
theorem meridian_zero (z : ℍ) : meridian D 0 z = Path.refl (qCoordinate D z) := by
  apply Path.ext
  funext t
  simp [meridianLift_apply]

end TauCeti.Subgroup.CuspDatum
