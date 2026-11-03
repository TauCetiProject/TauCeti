/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation
-- Private: the commuting of orthogonal bivectors, the square of a bivector and `w + w⁻¹ = 2 Re w`
-- on the circle are used only in proofs.
import TauCeti.Analysis.Complex.Circle
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# The torus characters of the half-spin representations of `Spin(4)` and `Spinᶜ(4)`

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let
`b = (b₀, b₁, b₂, b₃)` be a positively oriented orthonormal basis. The two coordinate planes
`⟨b₀, b₁⟩` and `⟨b₂, b₃⟩` give commuting circle subgroups of `Spin(4)`
(`CliffordAlgebra.spinCircle`), and hence a two-dimensional torus
`OrthonormalBasis.spinTorus : U(1) × U(1) → Spin(4)`,
`(w₁, w₂) ↦ (Re w₁ + Im w₁ b₀ b₁) (Re w₂ + Im w₂ b₂ b₃)`.
On `V`, `(w₁, w₂)` rotates the two planes by `w₁²` and `w₂²`. Writing `w_j = exp (i x_j / 2)`,
the rotation angles `x₁, x₂` are the weights of the tangent representation.

On a complex Clifford module `W`, the chirality element is `Γ = -J₁ J₂` with `J₁ = c(b₀) c(b₁)` and
`J₂ = c(b₂) c(b₃)` (`CliffordAlgebra.chirality_eq`). As `J₁² = -1`, `J₂ = ε J₁` on the
`ε`-eigenspace of `Γ`. Hence on the positive half-spinors `W⁺` the torus element `(w₁, w₂)` acts
as `(w₁ w₂, 1)`, and on `W⁻` as `(w₁ w₂⁻¹, 1)`. The element `(w, 1)` acts as `Re w + Im w J₁`,
by `w` on the line where `J₁ = i` and by `w⁻¹` on the line where `J₁ = -i`. So the weights of
`W⁺` are `±(x₁ + x₂) / 2` and those of `W⁻` are `±(x₁ - x₂) / 2`. In complex dimension two, the
`Spinᶜ(4)` element `[(w₁, w₂), z]` has the characters
`tr ρ⁺ = z (w₁ w₂ + w₁⁻¹ w₂⁻¹)` and `tr ρ⁻ = z (w₁ w₂⁻¹ + w₁⁻¹ w₂)`, so
`tr ρ⁺ - tr ρ⁻ = z (w₁ - w₁⁻¹) (w₂ - w₂⁻¹)`.
Under the formal substitution `z = exp ζ`, `w_j = exp (x_j / 2)` of Chern roots, this identity
reads `ch (W⁺ - W⁻) = exp ζ ∏_j 2 sinh (x_j / 2)`, the character input to the index formula of
the `Spinᶜ` Dirac operator. Since `[(w₁, w₂), z]` acts on `det W^±` by `z²`, the determinant line
has Chern root `l = 2ζ`.

## Main definitions

* `OrthonormalBasis.spinTorus b hQ`: the torus homomorphism `U(1) × U(1) → Spin(4)` of the
  coordinate planes `⟨b₀, b₁⟩` and `⟨b₂, b₃⟩`.

## Main results

* `OrthonormalBasis.spinTorus_apply`: `spinTorus` is the product of the two circle subgroups.
* `OrthonormalBasis.spinVectorAction_spinTorus_zero` (and `_one`, `_two`, `_three`): `(w₁, w₂)`
  rotates `⟨b₀, b₁⟩` by `w₁²` and `⟨b₂, b₃⟩` by `w₂²`.
* `CliffordAlgebra.halfSpinRep_one_spinTorus`, `CliffordAlgebra.halfSpinRep_neg_one_spinTorus`:
  on `W⁺`, `(w₁, w₂)` acts as `(w₁ w₂, 1)`, and on `W⁻` as `(w₁ w₂⁻¹, 1)`.
* `CliffordAlgebra.halfSpinRep_spinTorus_mk_one`: `(w, 1)` acts as `Re w + Im w c(b₀) c(b₁)`.
* `CliffordAlgebra.coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_I_smul`,
  `CliffordAlgebra.coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_neg_I_smul`: the weights `w`
  and `w⁻¹` on the eigenlines of `c(b₀) c(b₁)`.
* `CliffordAlgebra.trace_halfSpinRep_one_spinTorus`,
  `CliffordAlgebra.trace_halfSpinRep_neg_one_spinTorus`: the characters of the half-spin
  representations of `Spin(4)` on the torus.
* `CliffordAlgebra.trace_spinCGroupHalfSpinRep_one_mk_spinTorus`,
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_neg_one_mk_spinTorus` and
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_one_sub_neg_one_mk_spinTorus`: the characters of
  the half-spin representations of `Spinᶜ(4)` and their difference
  `z (w₁ - w₁⁻¹) (w₂ - w₂⁻¹)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §8, Chapter III, §11 and
  Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Module Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} (b : OrthonormalBasis (Fin 4) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

namespace OrthonormalBasis

include hQ

/-- The circle subgroups of the two coordinate planes commute. -/
private theorem commute_spinCircle (w₁ w₂ : Circle) :
    Commute
      (spinCircle Q (b 0) (b 1) (b.isOrtho_apply hQ (by decide))
        (b.map_apply_mul_map_apply hQ 0 1) w₁)
      (spinCircle Q (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
        (b.map_apply_mul_map_apply hQ 2 3) w₂) := by
  have hJ := (commute_ι_mul_ι_ι_of_isOrtho (b.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 2))
    (b.isOrtho_apply hQ (by decide : (1 : Fin 4) ≠ 2))).mul_right
      (commute_ι_mul_ι_ι_of_isOrtho (b.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 3))
        (b.isOrtho_apply hQ (by decide : (1 : Fin 4) ≠ 3)))
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, coe_spinCircle]
  exact ((Algebra.commute_algebraMap_right _ _).add_right
    ((Algebra.commute_algebraMap_left _ _).add_left ((hJ.smul_right _).smul_left _))).eq

/-- **The torus of `Spin(4)` attached to an orthonormal basis** `b` of a four-space with
`Q v = -‖v‖²`: `(w₁, w₂) ↦ (Re w₁ + Im w₁ b₀ b₁) (Re w₂ + Im w₂ b₂ b₃)`, the product of the
commuting circle subgroups of the coordinate planes `⟨b₀, b₁⟩` and `⟨b₂, b₃⟩`. -/
def spinTorus : Circle × Circle →* spinGroup Q :=
  (spinCircle Q (b 0) (b 1) (b.isOrtho_apply hQ (by decide))
    (b.map_apply_mul_map_apply hQ 0 1)).noncommCoprod
    (spinCircle Q (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
      (b.map_apply_mul_map_apply hQ 2 3)) (b.commute_spinCircle hQ)

/-- The underlying Clifford element of `spinTorus`. -/
@[simp]
theorem coe_spinTorus_apply (w : Circle × Circle) :
    (b.spinTorus hQ w : CliffordAlgebra Q) =
      (algebraMap ℝ _ (w.1 : ℂ).re + (w.1 : ℂ).im • (ι Q (b 0) * ι Q (b 1))) *
        (algebraMap ℝ _ (w.2 : ℂ).re + (w.2 : ℂ).im • (ι Q (b 2) * ι Q (b 3))) := by
  simp [spinTorus]

/-- `spinTorus` is the product of the circle subgroups of the planes `⟨b₀, b₁⟩` and `⟨b₂, b₃⟩`. -/
theorem spinTorus_apply (w : Circle × Circle) :
    b.spinTorus hQ w =
      spinCircle Q (b 0) (b 1) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 0 1) w.1 *
        spinCircle Q (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 2 3) w.2 :=
  MonoidHom.noncommCoprod_apply ..

/-- `(w₁, w₂)` rotates `b₀` towards `b₁` by `w₁²`. -/
theorem spinVectorAction_spinTorus_zero (w : Circle × Circle) :
    spinVectorAction Q (b.spinTorus hQ w) (b 0) =
      ((w.1 : ℂ) ^ 2).re • b 0 + ((w.1 : ℂ) ^ 2).im • b 1 := by
  rw [spinTorus_apply, spinVectorAction_mul, mul_apply_eq_comp,
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide)),
    spinVectorAction_spinCircle_left]
  simp [hQ, b.orthonormal.1 0, sub_eq_add_neg]

/-- `(w₁, w₂)` rotates `b₁` away from `b₀` by `w₁²`. -/
theorem spinVectorAction_spinTorus_one (w : Circle × Circle) :
    spinVectorAction Q (b.spinTorus hQ w) (b 1) =
      ((w.1 : ℂ) ^ 2).re • b 1 - ((w.1 : ℂ) ^ 2).im • b 0 := by
  rw [spinTorus_apply, spinVectorAction_mul, mul_apply_eq_comp,
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide)),
    spinVectorAction_spinCircle_right]
  simp [hQ, b.orthonormal.1 1, sub_eq_add_neg]

/-- `(w₁, w₂)` rotates `b₂` towards `b₃` by `w₂²`. -/
theorem spinVectorAction_spinTorus_two (w : Circle × Circle) :
    spinVectorAction Q (b.spinTorus hQ w) (b 2) =
      ((w.2 : ℂ) ^ 2).re • b 2 + ((w.2 : ℂ) ^ 2).im • b 3 := by
  rw [spinTorus_apply, spinVectorAction_mul, mul_apply_eq_comp,
    spinVectorAction_spinCircle_left, map_sub, map_smul, map_smul,
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide)),
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide))]
  simp [hQ, b.orthonormal.1 2, sub_eq_add_neg]

/-- `(w₁, w₂)` rotates `b₃` away from `b₂` by `w₂²`. -/
theorem spinVectorAction_spinTorus_three (w : Circle × Circle) :
    spinVectorAction Q (b.spinTorus hQ w) (b 3) =
      ((w.2 : ℂ) ^ 2).re • b 3 - ((w.2 : ℂ) ^ 2).im • b 2 := by
  rw [spinTorus_apply, spinVectorAction_mul, mul_apply_eq_comp,
    spinVectorAction_spinCircle_right, map_add, map_smul, map_smul,
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide)),
    spinVectorAction_spinCircle_of_isOrtho _ _ (b.isOrtho_apply hQ (by decide))
      (b.isOrtho_apply hQ (by decide))]
  simp [hQ, b.orthonormal.1 3, sub_eq_add_neg]

end OrthonormalBasis

namespace CliffordAlgebra

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4)) {W : Type*} [AddCommGroup W]
  [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

section Action

include hQ

omit [Fact (finrank ℝ V = 4)] in
/-- `(w, 1)` acts on `W` as `Re w + Im w c(b₀) c(b₁)`. -/
private theorem map_spinTorus_mk_one_apply (w : Circle) (ψ : W) :
    ρ (b.spinTorus hQ (w, 1)) ψ =
      ((w : ℂ).re : ℂ) • ψ + ((w : ℂ).im : ℂ) • ρ (ι Q (b 0) * ι Q (b 1)) ψ := by
  rw [OrthonormalBasis.coe_spinTorus_apply]
  simp only [Circle.coe_one, Complex.one_re, Complex.one_im, map_one, zero_smul, add_zero,
    mul_one, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Algebra.algebraMap_eq_smul_one, one_apply_eq_self, ← Complex.coe_smul]

variable {o} (hb : b.toBasis.orientation = o)
include hb

/-- On the `ε`-eigenspace of `Γ = -c(b₀) c(b₁) c(b₂) c(b₃)`, `c(b₂) c(b₃) = ε c(b₀) c(b₁)`. -/
private theorem map_ι_mul_ι_two_three_apply {ε : ℂ} {ψ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) :
    ρ (ι Q (b 2) * ι Q (b 3)) ψ = ε • ρ (ι Q (b 0) * ι Q (b 1)) ψ := by
  rw [mem_eigenspace_iff, chirality_eq o hQ b hb, mul_assoc (ι Q (b 0) * ι Q (b 1)), map_neg,
    map_mul] at hψ
  simp only [LinearMap.neg_apply, mul_apply_eq_comp] at hψ
  -- `J₁² = -1`, so `J₂ ψ = -J₁ (J₁ (J₂ ψ)) = J₁ (ε ψ)`.
  have h₁ (x : W) : ρ (ι Q (b 0) * ι Q (b 1)) (ρ (ι Q (b 0) * ι Q (b 1)) x) = -x := by
    rw [← mul_apply_eq_comp, ← map_mul,
      ι_mul_ι_mul_self_of_isOrtho (b.isOrtho_apply hQ (by decide)), b.map_apply_mul_map_apply hQ]
    simp
  calc ρ (ι Q (b 2) * ι Q (b 3)) ψ
      = ρ (ι Q (b 0) * ι Q (b 1)) (-ρ (ι Q (b 0) * ι Q (b 1)) (ρ (ι Q (b 2) * ι Q (b 3)) ψ)) := by
        rw [map_neg, h₁, neg_neg]
    _ = ε • ρ (ι Q (b 0) * ι Q (b 1)) ψ := by rw [hψ, map_smul]

/-- `(1, w)` acts on the `ε`-eigenspace of `Γ` as `Re w + ε Im w c(b₀) c(b₁)`. -/
private theorem map_spinTorus_one_mk_apply {ε : ℂ} {ψ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (w : Circle) :
    ρ (b.spinTorus hQ (1, w)) ψ =
      ((w : ℂ).re : ℂ) • ψ + (ε * (w : ℂ).im) • ρ (ι Q (b 0) * ι Q (b 1)) ψ := by
  rw [OrthonormalBasis.coe_spinTorus_apply]
  simp only [Circle.coe_one, Complex.one_re, Complex.one_im, map_one, zero_smul, add_zero,
    one_mul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Algebra.algebraMap_eq_smul_one, one_apply_eq_self, ← Complex.coe_smul]
  rw [map_ι_mul_ι_two_three_apply b hQ ρ hb hψ, smul_smul, mul_comm]

omit [Fact (finrank ℝ V = 4)] hb in
/-- If `(1, w₂)` acts on `ψ` as `(w, 1)`, then `(w₁, w₂)` acts on `ψ` as `(w₁ w, 1)`. -/
private theorem map_spinTorus_apply_eq {ψ : W} {w₁ w₂ w : Circle}
    (hw : ρ (b.spinTorus hQ (1, w₂)) ψ = ρ (b.spinTorus hQ (w, 1)) ψ) :
    ρ (b.spinTorus hQ (w₁, w₂)) ψ = ρ (b.spinTorus hQ (w₁ * w, 1)) ψ := by
  have h₁ : b.spinTorus hQ (w₁, w₂) = b.spinTorus hQ (w₁, 1) * b.spinTorus hQ (1, w₂) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have h₂ : b.spinTorus hQ (w₁ * w, 1) = b.spinTorus hQ (w₁, 1) * b.spinTorus hQ (w, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [h₁, h₂, Submonoid.coe_mul, Submonoid.coe_mul, map_mul, map_mul, mul_apply_eq_comp,
    mul_apply_eq_comp, hw]

/-- **The torus acts on `W⁺` through the product of its coordinates**: on the positive
half-spinors, `(w₁, w₂)` acts as `(w₁ w₂, 1)`. -/
theorem halfSpinRep_one_spinTorus (w₁ w₂ : Circle) :
    halfSpinRep o ρ 1 (b.spinTorus hQ (w₁, w₂)) =
      halfSpinRep o ρ 1 (b.spinTorus hQ (w₁ * w₂, 1)) := by
  ext ψ
  simp only [coe_halfSpinRep_apply]
  refine map_spinTorus_apply_eq b hQ ρ ?_
  rw [map_spinTorus_one_mk_apply b hQ ρ hb ψ.2, map_spinTorus_mk_one_apply, one_mul]

/-- **The torus acts on `W⁻` through the quotient of its coordinates**: on the negative
half-spinors, `(w₁, w₂)` acts as `(w₁ w₂⁻¹, 1)`. -/
theorem halfSpinRep_neg_one_spinTorus (w₁ w₂ : Circle) :
    halfSpinRep o ρ (-1) (b.spinTorus hQ (w₁, w₂)) =
      halfSpinRep o ρ (-1) (b.spinTorus hQ (w₁ * w₂⁻¹, 1)) := by
  ext ψ
  simp only [coe_halfSpinRep_apply]
  refine map_spinTorus_apply_eq b hQ ρ ?_
  rw [map_spinTorus_one_mk_apply b hQ ρ hb ψ.2, map_spinTorus_mk_one_apply,
    Circle.coe_inv_eq_conj, Complex.conj_re, Complex.conj_im, Complex.ofReal_neg, neg_one_mul]

end Action

include hQ

/-- `(w, 1)` acts on each eigenspace of `Γ` as `Re w + Im w c(b₀) c(b₁)`. -/
theorem halfSpinRep_spinTorus_mk_one (ε : ℂ) (w : Circle) :
    halfSpinRep o ρ ε (b.spinTorus hQ (w, 1)) =
      ((w : ℂ).re : ℂ) • 1 +
        ((w : ℂ).im : ℂ) • evenHalfSpinAction o ρ ε ((even.ι Q).bilin (b 0) (b 1)) := by
  ext ψ
  simp

/-- **The weight `w`**: `(w, 1)` acts by `w` on a half-spinor on which `c(b₀) c(b₁)` acts by
`i`. -/
theorem coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_I_smul {ε : ℂ} (w : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) ε}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = Complex.I • (ψ : W)) :
    (halfSpinRep o ρ ε (b.spinTorus hQ (w, 1)) ψ : W) = (w : ℂ) • (ψ : W) := by
  rw [coe_halfSpinRep_apply, map_spinTorus_mk_one_apply, hψ, smul_smul, ← add_smul,
    Complex.re_add_im]

/-- **The weight `w⁻¹`**: `(w, 1)` acts by `w⁻¹` on a half-spinor on which `c(b₀) c(b₁)` acts
by `-i`. -/
theorem coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_neg_I_smul {ε : ℂ} (w : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) ε}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = -Complex.I • (ψ : W)) :
    (halfSpinRep o ρ ε (b.spinTorus hQ (w, 1)) ψ : W) = ((w : ℂ))⁻¹ • (ψ : W) := by
  rw [coe_halfSpinRep_apply, map_spinTorus_mk_one_apply, hψ, smul_smul, ← add_smul]
  congr 1
  linear_combination -Circle.coe_add_inv_coe w - Complex.re_add_im (w : ℂ)

variable [FiniteDimensional ℂ W]

/-- The trace of `(w, 1)` on an eigenspace of `Γ` is `Re w` times its dimension. -/
theorem trace_halfSpinRep_spinTorus_mk_one (ε : ℂ) (w : Circle) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ ε (b.spinTorus hQ (w, 1))) =
      (w : ℂ).re * finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  rw [halfSpinRep_spinTorus_mk_one, map_add, map_smul, map_smul, LinearMap.trace_one,
    trace_evenHalfSpinAction_ι_bilin o ρ ε hQ, b.orthonormal.2 (by decide : (0 : Fin 4) ≠ 1)]
  simp

variable {o} (hb : b.toBasis.orientation = o)
include hb

/-- **The character of `W⁺` on the torus**: `(w₁, w₂)` has trace `Re (w₁ w₂) dim W⁺`. -/
theorem trace_halfSpinRep_one_spinTorus (w₁ w₂ : Circle) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ 1 (b.spinTorus hQ (w₁, w₂))) =
      ((w₁ : ℂ) * w₂).re * finrank ℂ (eigenspace (ρ (chirality Q o)) 1) := by
  rw [halfSpinRep_one_spinTorus b hQ ρ hb, trace_halfSpinRep_spinTorus_mk_one, Circle.coe_mul]

/-- **The character of `W⁻` on the torus**: `(w₁, w₂)` has trace `Re (w₁ w₂⁻¹) dim W⁻`. -/
theorem trace_halfSpinRep_neg_one_spinTorus (w₁ w₂ : Circle) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ (-1) (b.spinTorus hQ (w₁, w₂))) =
      ((w₁ : ℂ) * (w₂ : ℂ)⁻¹).re * finrank ℂ (eigenspace (ρ (chirality Q o)) (-1)) := by
  rw [halfSpinRep_neg_one_spinTorus b hQ ρ hb, trace_halfSpinRep_spinTorus_mk_one,
    Circle.coe_mul, Circle.coe_inv]

variable (hQ₀ : Q ≠ 0) (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
include h₂

/-- **The character of the positive half-spin representation of `Spinᶜ(4)`** on the torus:
`[(w₁, w₂), z]` has trace `z (w₁ w₂ + w₁⁻¹ w₂⁻¹)` on a two-dimensional `W⁺`. -/
theorem trace_spinCGroupHalfSpinRep_one_mk_spinTorus (w₁ w₂ z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ 1 hQ₀ (spinCGroup.mk Q hQ₀ (b.spinTorus hQ (w₁, w₂), z))) =
      (z : ℂ) * ((w₁ : ℂ) * w₂ + (w₁ : ℂ)⁻¹ * (w₂ : ℂ)⁻¹) := by
  rw [spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, map_smul,
    trace_halfSpinRep_one_spinTorus b hQ ρ hb, h₂, smul_eq_mul]
  have hw := Circle.coe_add_inv_coe (w₁ * w₂)
  simp only [Circle.coe_mul] at hw
  push_cast
  linear_combination -(z : ℂ) * hw

/-- **The character of the negative half-spin representation of `Spinᶜ(4)`** on the torus:
`[(w₁, w₂), z]` has trace `z (w₁ w₂⁻¹ + w₁⁻¹ w₂)` on `W⁻`, when `W⁺` is two-dimensional. -/
theorem trace_spinCGroupHalfSpinRep_neg_one_mk_spinTorus (w₁ w₂ z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ (-1) hQ₀ (spinCGroup.mk Q hQ₀ (b.spinTorus hQ (w₁, w₂), z))) =
      (z : ℂ) * ((w₁ : ℂ) * (w₂ : ℂ)⁻¹ + (w₁ : ℂ)⁻¹ * w₂) := by
  rw [spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, map_smul,
    trace_halfSpinRep_neg_one_spinTorus b hQ ρ hb, finrank_eigenspace_chirality_neg o hQ ρ, h₂,
    smul_eq_mul]
  have hw := Circle.coe_add_inv_coe (w₁ * w₂⁻¹)
  simp only [Circle.coe_mul, Circle.coe_inv, mul_inv, inv_inv] at hw
  push_cast
  linear_combination -(z : ℂ) * hw

/-- **The character of `W⁺ - W⁻` on the torus of `Spinᶜ(4)`**: on two-dimensional half-spinors,
`tr ρ⁺ - tr ρ⁻ = z (w₁ - w₁⁻¹) (w₂ - w₂⁻¹)` at `[(w₁, w₂), z]`. -/
theorem trace_spinCGroupHalfSpinRep_one_sub_neg_one_mk_spinTorus (w₁ w₂ z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ 1 hQ₀ (spinCGroup.mk Q hQ₀ (b.spinTorus hQ (w₁, w₂), z))) -
      LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ (-1) hQ₀ (spinCGroup.mk Q hQ₀ (b.spinTorus hQ (w₁, w₂), z))) =
      (z : ℂ) * ((w₁ : ℂ) - (w₁ : ℂ)⁻¹) * ((w₂ : ℂ) - (w₂ : ℂ)⁻¹) := by
  rw [trace_spinCGroupHalfSpinRep_one_mk_spinTorus b hQ ρ hb hQ₀ h₂,
    trace_spinCGroupHalfSpinRep_neg_one_mk_spinTorus b hQ ρ hb hQ₀ h₂]
  ring

end CliffordAlgebra
