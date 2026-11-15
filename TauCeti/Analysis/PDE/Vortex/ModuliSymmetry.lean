/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Translations and rotations of the framed plane vortex moduli space

The smooth framed degree-`m` plane vortices (`TauCeti.Vortex.framedVortexSubMulAction`) are the
smooth solutions of the vortex equations whose section `α` has the end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Their smooth framed gauge orbits are identified with `Sym ℂ m` by the zero
divisor (`TauCeti.Vortex.framedVortexModuliEquiv`). This file shows that the orientation-preserving
isometries of the plane act on the framed vortices and on their moduli space, and that the
identification with `Sym ℂ m` is equivariant: moving a vortex moves its zeros.

* **Translations.** `a +ᵥ x` is the pullback of `x` by `z ↦ z - a`. Translations preserve the
  end framing (`TauCeti.Vortex.tendsto_sectionValue_translateField`), so no gauge is needed. This
  is an action of the additive group `ℂ`, and the zeros of `a +ᵥ x` are those of `x` moved by `a`
  (`TauCeti.Vortex.framedVortexDivisor_vadd`).
* **Rotations.** For `u` on the unit circle, `u • x` is the pullback of `x` by `z ↦ u⁻¹ z`
  followed by the constant line-frame gauge `u ^ m`. The rotation alone multiplies the limit of
  the end framing by `u⁻ᵐ`, and the constant gauge restores it
  (`TauCeti.Vortex.tendsto_sectionValue_gaugeTransform_rotateField`). The constant gauge does not
  tend to one at infinity, so it is a change of the frame of the line at infinity, not an element
  of the framed gauge group. This is an action of `Circle`, and the zeros of `u • x` are those of
  `x` rotated by `u` (`TauCeti.Vortex.framedVortexDivisor_circle_smul`).
* The two actions satisfy the semidirect product law `u • (a +ᵥ x) = (u a) +ᵥ (u • x)`
  (`TauCeti.Vortex.circle_smul_vadd`) of the group of orientation-preserving isometries.

By Taubes's uniqueness theorem two framed vortices lie in one framed gauge orbit exactly when
their divisors agree (`TauCeti.Vortex.orbitRel_iff_framedVortexDivisor_eq`), so both actions
descend to the moduli space `M_m` of framed gauge orbits. There the divisor identification
`M_m ≃ Sym ℂ m` intertwines them with the actions on divisors,
`D ↦ D + a` and `D ↦ u D` (`TauCeti.Vortex.framedVortexModuliEquiv_vadd`,
`TauCeti.Vortex.framedVortexModuliEquiv_circle_smul`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open scoped ContDiff

namespace TauCeti.Vortex

variable {m : ℕ}

/-- **Uniqueness modulo framed gauge.** Two smooth framed degree-`m` vortices lie in one framed
gauge orbit exactly when their zero divisors agree. -/
theorem orbitRel_iff_framedVortexDivisor_eq {x y : framedVortexSubMulAction m} :
    MulAction.orbitRel framedGaugeGroup (framedVortexSubMulAction m) x y ↔
      framedVortexDivisor x = framedVortexDivisor y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    framedVortexDivisor_eq_framedVortexDivisor_iff]

/-! ### Translations -/

/-- Translations preserve smooth framed vortices: the pullback of a smooth framed degree-`m`
vortex by `z ↦ z + a` is again one, with the same end framing. -/
theorem translateField_mem_framedVortexSubMulAction (a : ℂ) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedVortexSubMulAction m) : translateField a x ∈ framedVortexSubMulAction m := by
  obtain ⟨hx, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  exact mem_framedVortexSubMulAction.2 ⟨contDiff_translateField a hx,
    fun z ↦ by rw [equation_translateField, hsol], tendsto_sectionValue_translateField hfr a⟩

/-- Translation of a smooth framed vortex by `a`: the pullback by `z ↦ z - a`. -/
instance : VAdd ℂ (framedVortexSubMulAction m) :=
  ⟨fun a x ↦ ⟨translateField (-a) x, translateField_mem_framedVortexSubMulAction (-a) x.2⟩⟩

@[simp]
theorem framedVortexSubMulAction.coe_vadd (a : ℂ) (x : framedVortexSubMulAction m) :
    ((a +ᵥ x : framedVortexSubMulAction m) : ℂ → EuclideanSpace ℝ (Fin 4)) =
      translateField (-a) x :=
  (rfl)

/-- **Translations act on the smooth framed vortices.** -/
instance : AddAction ℂ (framedVortexSubMulAction m) where
  zero_vadd x := Subtype.ext <| by simp
  add_vadd a b x := Subtype.ext <| by simp [add_comm]

/-- **Translation law for the divisor.** Translating a framed vortex by `a` moves its zeros by
`a`. -/
@[simp]
theorem framedVortexDivisor_vadd (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (a +ᵥ x) = (framedVortexDivisor x).map (· + a) := by
  rw [framedVortexDivisor_eq_iff, framedVortexSubMulAction.coe_vadd, Sym.coe_map]
  simpa only [sub_neg_eq_add] using isZeroMultiplicity_sectionValue_translateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) (-a)

/-! ### Rotations and the line frame -/

/-- Rotations preserve smooth framed vortices after a change of line frame: the pullback of a
smooth framed degree-`m` vortex by `z ↦ u z`, followed by the constant gauge `u⁻ᵐ`, is again one,
with the same end framing. -/
theorem gaugeTransform_rotateField_mem_framedVortexSubMulAction (u : Circle)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction m) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) ∈ framedVortexSubMulAction m := by
  obtain ⟨hx, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  have hr := contDiff_rotateField u hx
  refine mem_framedVortexSubMulAction.2 ⟨contDiff_gaugeTransform contDiff_const hr, fun z ↦ ?_,
    tendsto_sectionValue_gaugeTransform_rotateField hfr u⟩
  have hd {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ ∞ y) (i : Fin 4) (w : ℂ) :
      DifferentiableAt ℝ (fun w ↦ y w i) w :=
    (((contDiff_piLp 2).1 hy i).differentiable (by simp)).differentiableAt
  rw [equation_gaugeTransform_eq_zero_iff contDiffAt_const fun i ↦ hd hr i z,
    equation_rotateField_eq_zero_iff (hd hx 0 _) (hd hx 1 _), hsol]

/-- Rotation of a smooth framed vortex by `u`: the pullback by `z ↦ u⁻¹ z` followed by the
constant line-frame gauge `u ^ m`. -/
instance : SMul Circle (framedVortexSubMulAction m) :=
  ⟨fun u x ↦ ⟨gaugeTransform (fun _ ↦ u ^ m) (rotateField u⁻¹ x), by
    simpa only [inv_inv] using gaugeTransform_rotateField_mem_framedVortexSubMulAction u⁻¹ x.2⟩⟩

@[simp]
theorem framedVortexSubMulAction.coe_circle_smul (u : Circle) (x : framedVortexSubMulAction m) :
    ((u • x : framedVortexSubMulAction m) : ℂ → EuclideanSpace ℝ (Fin 4)) =
      gaugeTransform (fun _ ↦ u ^ m) (rotateField u⁻¹ x) :=
  (rfl)

/-- **Rotations act on the smooth framed vortices.** -/
instance : MulAction Circle (framedVortexSubMulAction m) where
  one_smul x := Subtype.ext <| by simp [← Pi.one_def]
  mul_smul u v x := Subtype.ext <| by
    simp only [framedVortexSubMulAction.coe_circle_smul, rotateField_gaugeTransform,
      rotateField_rotateField]
    rw [← gaugeTransform_mul (differentiable_const _) (differentiable_const _), mul_inv, mul_pow,
      Pi.mul_def]

/-- **Rotation law for the divisor.** Rotating a framed vortex by `u` rotates its zeros by `u`. -/
@[simp]
theorem framedVortexDivisor_circle_smul (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (u • x) = (framedVortexDivisor x).map ((u : ℂ) * ·) := by
  rw [framedVortexDivisor_eq_iff, framedVortexSubMulAction.coe_circle_smul, Sym.coe_map]
  have h := isZeroMultiplicity_sectionValue_rotateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) u⁻¹
  rw [Circle.coe_inv, inv_inv] at h
  exact isZeroMultiplicity_sectionValue_gaugeTransform continuous_const h

/-- **The semidirect product law.** Rotating a translated framed vortex is translating the
rotated vortex by the rotated vector. -/
theorem circle_smul_vadd (u : Circle) (a : ℂ) (x : framedVortexSubMulAction m) :
    u • (a +ᵥ x) = ((u : ℂ) * a) +ᵥ (u • x) := Subtype.ext <| by
  simp only [framedVortexSubMulAction.coe_circle_smul, framedVortexSubMulAction.coe_vadd,
    rotateField_translateField, translateField_gaugeTransform, Circle.coe_inv, inv_inv, mul_neg]

/-! ### The action on the moduli space -/

/-- Translation of framed gauge orbits of smooth framed vortices. -/
instance : VAdd ℂ (MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :=
  ⟨fun a ↦ Quotient.map' (a +ᵥ ·) fun x y h ↦ orbitRel_iff_framedVortexDivisor_eq.2 <| by
    rw [framedVortexDivisor_vadd, framedVortexDivisor_vadd,
      orbitRel_iff_framedVortexDivisor_eq.1 h]⟩

@[simp]
theorem vadd_mk_framedVortex (a : ℂ) (x : framedVortexSubMulAction m) :
    (a +ᵥ Quotient.mk'' x :
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) =
      Quotient.mk'' (a +ᵥ x) :=
  (rfl)

/-- **Translations act on the moduli space of framed vortices.** -/
instance : AddAction ℂ (MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m))
    where
  zero_vadd q := Quotient.inductionOn' q fun x ↦ by rw [vadd_mk_framedVortex, zero_vadd]
  add_vadd a b q := Quotient.inductionOn' q fun x ↦ by
    rw [vadd_mk_framedVortex, vadd_mk_framedVortex, vadd_mk_framedVortex, add_vadd]

/-- **Translation equivariance of the moduli.** The divisor identification of the framed vortex
moduli space with `Sym ℂ m` carries translation by `a` to the translation `D ↦ D + a` of
divisors. -/
@[simp]
theorem framedVortexModuliEquiv_vadd (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (a +ᵥ q) = (framedVortexModuliEquiv m q).map (· + a) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [vadd_mk_framedVortex, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_vadd]

/-- Rotation of framed gauge orbits of smooth framed vortices. -/
instance :
    SMul Circle (MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :=
  ⟨fun u ↦ Quotient.map' (u • ·) fun x y h ↦ orbitRel_iff_framedVortexDivisor_eq.2 <| by
    rw [framedVortexDivisor_circle_smul, framedVortexDivisor_circle_smul,
      orbitRel_iff_framedVortexDivisor_eq.1 h]⟩

@[simp]
theorem circle_smul_mk_framedVortex (u : Circle) (x : framedVortexSubMulAction m) :
    (u • Quotient.mk'' x :
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) =
      Quotient.mk'' (u • x) :=
  (rfl)

/-- **Rotations act on the moduli space of framed vortices.** -/
instance : MulAction Circle
    (MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) where
  one_smul q := Quotient.inductionOn' q fun x ↦ by rw [circle_smul_mk_framedVortex, one_smul]
  mul_smul u v q := Quotient.inductionOn' q fun x ↦ by
    rw [circle_smul_mk_framedVortex, circle_smul_mk_framedVortex, circle_smul_mk_framedVortex,
      mul_smul]

/-- **Rotation equivariance of the moduli.** The divisor identification of the framed vortex
moduli space with `Sym ℂ m` carries rotation by `u` to the rotation `D ↦ u D` of divisors. -/
@[simp]
theorem framedVortexModuliEquiv_circle_smul (u : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (u • q) = (framedVortexModuliEquiv m q).map ((u : ℂ) * ·) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [circle_smul_mk_framedVortex, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_circle_smul]

end TauCeti.Vortex
