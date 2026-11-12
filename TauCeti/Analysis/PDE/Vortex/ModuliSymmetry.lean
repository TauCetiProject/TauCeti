/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Translations and rotations of the moduli of framed plane vortices

The smooth framed degree-`m` vortices (`TauCeti.Vortex.framedVortexSubMulAction`) are the smooth
solutions of the vortex equations whose section has the end framing `α(z) (z / |z|)⁻ᵐ → 1`. Their
orbits under the smooth framed gauge group are identified with `Sym ℂ m` by the zero divisor
(`TauCeti.Vortex.framedVortexModuliEquiv`). This file shows that the orientation-preserving
isometries of the plane act on these vortices and on their moduli, and that the divisor is
equivariant.

* **Translations.** The pullback `translateField a x` by `z ↦ z + a` preserves the end framing, so
  it maps framed vortices to framed vortices (`TauCeti.Vortex.framedVortexTranslate`). It moves the
  divisor `D` to `D - a`.
* **Rotations.** The pullback `rotateField u x` by `z ↦ u z`, `u` on the unit circle, multiplies
  the limit of the end framing by `uᵐ`. The constant line-frame gauge `u⁻ᵐ` restores it, so
  `gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x)` is again a framed vortex
  (`TauCeti.Vortex.framedVortexRotate`). It rotates the divisor `D` to `u⁻¹ D`. The constant gauge
  does not tend to one at infinity, so it is not an element of the framed gauge group.

Both maps are actions (`framedVortexTranslate_framedVortexTranslate`,
`framedVortexRotate_framedVortexRotate`), they satisfy the semidirect product law of the isometry
group (`framedVortexRotate_framedVortexTranslate`), and they normalize the framed gauge group:
moving `g • x` is moving `x` and acting by the moved gauge (`framedVortexTranslate_smul`,
`framedVortexRotate_smul`, with `comp_add_mem_framedGaugeGroup` and
`comp_mul_mem_framedGaugeGroup`). Hence they descend to the quotient
(`framedVortexModuliTranslate`, `framedVortexModuliRotate`), where under `framedVortexModuliEquiv`
they become `Sym.map (· - a)` and `Sym.map (u⁻¹ * ·)` on `Sym ℂ m`.
Since `Sym ℂ m` consists of unordered tuples, relabelling the zeros of a vortex does not change
its point of the moduli.

## Main results

* `TauCeti.Vortex.framedVortexDivisor_framedVortexTranslate`,
  `TauCeti.Vortex.framedVortexDivisor_framedVortexRotate`: the divisor laws.
* `TauCeti.Vortex.framedVortexModuliEquiv_framedVortexModuliTranslate`,
  `TauCeti.Vortex.framedVortexModuliEquiv_framedVortexModuliRotate`: the identification of the
  moduli with `Sym ℂ m` is equivariant.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex Filter
open scoped ContDiff Topology

namespace TauCeti.Vortex

variable {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Smoothness of moved fields and gauges -/

/-- Translations preserve smooth fields. -/
theorem contDiff_translateField {n : WithTop ℕ∞} (a : ℂ) (hx : ContDiff ℝ n x) :
    ContDiff ℝ n (translateField a x) := by
  have h : translateField a x = fun z ↦ x (z + a) := funext (translateField_apply a x)
  rw [h]
  exact hx.comp (contDiff_id.add contDiff_const)

/-- Rotations preserve smooth fields. -/
theorem contDiff_rotateField {n : WithTop ℕ∞} (u : Circle) (hx : ContDiff ℝ n x) :
    ContDiff ℝ n (rotateField u x) := by
  have hc (i : Fin 4) : ContDiff ℝ n fun z ↦ x ((u : ℂ) * z) i :=
    ((contDiff_piLp 2).1 hx i).comp (contDiff_const.mul contDiff_id)
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, rotateField_apply_zero,
      rotateField_apply_one, rotateField_apply_two, rotateField_apply_three]
  · exact (contDiff_const.mul (hc 0)).add (contDiff_const.mul (hc 1))
  · exact (contDiff_const.mul (hc 1)).sub (contDiff_const.mul (hc 0))
  · exact hc 2
  · exact hc 3

/-- A framed gauge composed with a translation is a framed gauge. -/
theorem comp_add_mem_framedGaugeGroup {g : ℂ → Circle} (hg : g ∈ framedGaugeGroup) (a : ℂ) :
    (fun w ↦ g (w + a)) ∈ framedGaugeGroup := by
  obtain ⟨hs, ht⟩ := (mem_framedGaugeGroup g).1 hg
  exact (mem_framedGaugeGroup _).2 ⟨hs.comp (contDiff_id.add contDiff_const),
    ht.comp (Homeomorph.addRight a).map_cocompact.le⟩

/-- A framed gauge composed with a rotation is a framed gauge. -/
theorem comp_mul_mem_framedGaugeGroup {g : ℂ → Circle} (hg : g ∈ framedGaugeGroup) (u : Circle) :
    (fun w ↦ g (u * w)) ∈ framedGaugeGroup := by
  obtain ⟨hs, ht⟩ := (mem_framedGaugeGroup g).1 hg
  exact (mem_framedGaugeGroup _).2 ⟨hs.comp (contDiff_const.mul contDiff_id),
    ht.comp (tendsto_cocompact_mul_left₀ (Circle.coe_ne_zero u))⟩

/-! ### Translations of framed vortices -/

/-- Translations preserve the smooth framed degree-`m` vortices. -/
theorem translateField_mem_framedVortexSubMulAction (a : ℂ)
    (hx : x ∈ framedVortexSubMulAction m) : translateField a x ∈ framedVortexSubMulAction m := by
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  exact mem_framedVortexSubMulAction.2 ⟨contDiff_translateField a hs,
    fun z ↦ by rw [equation_translateField, hsol], tendsto_sectionValue_translateField hfr a⟩

/-- **Translation of a framed vortex** by `a`: the pullback by `z ↦ z + a`, again a smooth framed
degree-`m` vortex. -/
def framedVortexTranslate (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexSubMulAction m :=
  ⟨translateField a x, translateField_mem_framedVortexSubMulAction a x.2⟩

@[simp]
theorem coe_framedVortexTranslate (a : ℂ) (x : framedVortexSubMulAction m) :
    (framedVortexTranslate a x : ℂ → EuclideanSpace ℝ (Fin 4)) = translateField a x :=
  (rfl)

@[simp]
theorem framedVortexTranslate_zero (x : framedVortexSubMulAction m) :
    framedVortexTranslate 0 x = x :=
  Subtype.ext (translateField_zero x)

/-- Successive translations add. -/
@[simp]
theorem framedVortexTranslate_framedVortexTranslate (a b : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexTranslate a (framedVortexTranslate b x) = framedVortexTranslate (a + b) x :=
  Subtype.ext (translateField_translateField a b x)

/-- **Translations normalize the framed gauge group.** Translating `g • x` by `a` is translating
`x` and acting by the translated gauge `w ↦ g (w + a)`. -/
theorem framedVortexTranslate_smul (a : ℂ) (g : framedGaugeGroup)
    (x : framedVortexSubMulAction m) :
    framedVortexTranslate a (g • x) =
      (⟨fun w ↦ g.1 (w + a), comp_add_mem_framedGaugeGroup g.2 a⟩ : framedGaugeGroup) •
        framedVortexTranslate a x :=
  Subtype.ext (translateField_gaugeTransform a g.1 x)

/-- **Translation law for the divisor.** Translating a framed vortex by `a` moves its divisor `D`
to `D - a`. -/
theorem framedVortexDivisor_framedVortexTranslate (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (framedVortexTranslate a x) = (framedVortexDivisor x).map (· - a) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map]
  exact isZeroMultiplicity_sectionValue_translateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) a

/-! ### Rotations of framed vortices -/

/-- Rotations followed by the constant line-frame gauge `u⁻ᵐ` preserve the smooth framed
degree-`m` vortices. -/
theorem gaugeTransform_rotateField_mem_framedVortexSubMulAction (u : Circle)
    (hx : x ∈ framedVortexSubMulAction m) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) ∈ framedVortexSubMulAction m := by
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  have hr := contDiff_rotateField u hs
  refine mem_framedVortexSubMulAction.2 ⟨contDiff_gaugeTransform contDiff_const hr, fun z ↦ ?_,
    tendsto_sectionValue_gaugeTransform_rotateField hfr u⟩
  have hxi (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    ((contDiff_piLp 2).1 hs i).differentiable (by simp)
  have hri (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ rotateField u x w i) z :=
    ((contDiff_piLp 2).1 hr i).differentiable (by simp) z
  rw [equation_gaugeTransform_eq_zero_iff contDiffAt_const hri,
    equation_rotateField_eq_zero_iff (hxi 0 _) (hxi 1 _)]
  exact hsol _

/-- **Rotation of a framed vortex** by `u`: the pullback by `z ↦ u z` followed by the constant
line-frame gauge `u⁻ᵐ`, which restores the degree-`m` end framing. -/
def framedVortexRotate (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexSubMulAction m :=
  ⟨gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x),
    gaugeTransform_rotateField_mem_framedVortexSubMulAction u x.2⟩

@[simp]
theorem coe_framedVortexRotate (u : Circle) (x : framedVortexSubMulAction m) :
    (framedVortexRotate u x : ℂ → EuclideanSpace ℝ (Fin 4)) =
      gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) :=
  (rfl)

@[simp]
theorem framedVortexRotate_one (x : framedVortexSubMulAction m) : framedVortexRotate 1 x = x := by
  refine Subtype.ext ?_
  rw [coe_framedVortexRotate, inv_one, one_pow, rotateField_one]
  exact gaugeTransform_one x

/-- Successive rotations multiply. -/
@[simp]
theorem framedVortexRotate_framedVortexRotate (u v : Circle) (x : framedVortexSubMulAction m) :
    framedVortexRotate u (framedVortexRotate v x) = framedVortexRotate (u * v) x := by
  refine Subtype.ext ?_
  rw [coe_framedVortexRotate, coe_framedVortexRotate, coe_framedVortexRotate,
    rotateField_gaugeTransform, rotateField_rotateField,
    ← gaugeTransform_mul (u := fun _ ↦ u⁻¹ ^ m) (v := fun _ ↦ v⁻¹ ^ m) (differentiable_const _)
      (differentiable_const _)]
  congr 1
  funext
  simp only [Pi.mul_apply, mul_inv, mul_pow, mul_comm (u⁻¹ ^ m)]

/-- **Rotations normalize the framed gauge group.** Rotating `g • x` by `u` is rotating `x` and
acting by the rotated gauge `w ↦ g (u w)`. -/
theorem framedVortexRotate_smul (u : Circle) (g : framedGaugeGroup)
    (x : framedVortexSubMulAction m) :
    framedVortexRotate u (g • x) =
      (⟨fun w ↦ g.1 (u * w), comp_mul_mem_framedGaugeGroup g.2 u⟩ : framedGaugeGroup) •
        framedVortexRotate u x := by
  have hg : Differentiable ℝ fun w ↦ (g.1 (u * w) : ℂ) :=
    ((mem_framedGaugeGroup _).1 (comp_mul_mem_framedGaugeGroup g.2 u)).1.differentiable (by simp)
  refine Subtype.ext ?_
  simp only [coe_framedVortexRotate, SubMulAction.val_smul, framedGaugeGroup_smul]
  rw [rotateField_gaugeTransform,
    ← gaugeTransform_mul (u := fun _ ↦ u⁻¹ ^ m) (differentiable_const _) hg,
    ← gaugeTransform_mul (v := fun _ ↦ u⁻¹ ^ m) hg (differentiable_const _), mul_comm]

/-- **The semidirect product law.** Rotating by `u` a framed vortex translated by `a` is
translating by `u⁻¹ a` the rotated framed vortex. -/
theorem framedVortexRotate_framedVortexTranslate (u : Circle) (a : ℂ)
    (x : framedVortexSubMulAction m) :
    framedVortexRotate u (framedVortexTranslate a x) =
      framedVortexTranslate ((u : ℂ)⁻¹ * a) (framedVortexRotate u x) := by
  refine Subtype.ext ?_
  rw [coe_framedVortexRotate, coe_framedVortexTranslate, coe_framedVortexTranslate,
    coe_framedVortexRotate, rotateField_translateField, translateField_gaugeTransform]

/-- **Rotation law for the divisor.** Rotating a framed vortex by `u` rotates its divisor `D` to
`u⁻¹ D`. -/
theorem framedVortexDivisor_framedVortexRotate (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (framedVortexRotate u x) =
      (framedVortexDivisor x).map ((u : ℂ)⁻¹ * ·) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map, coe_framedVortexRotate]
  exact isZeroMultiplicity_sectionValue_gaugeTransform continuous_const
    (isZeroMultiplicity_sectionValue_rotateField
      (isZeroMultiplicity_sectionValue_framedVortexDivisor x) u)

/-! ### The induced maps on the moduli -/

/-- **Translation on the moduli of framed vortices**: the map induced on framed gauge orbits by
`framedVortexTranslate a`. -/
def framedVortexModuliTranslate (a : ℂ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) :=
  Quotient.map' (framedVortexTranslate a) fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨_, (framedVortexTranslate_smul a g y).symm⟩

@[simp]
theorem framedVortexModuliTranslate_mk (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexModuliTranslate a (Quotient.mk'' x) = Quotient.mk'' (framedVortexTranslate a x) :=
  (rfl)

/-- **Rotation on the moduli of framed vortices**: the map induced on framed gauge orbits by
`framedVortexRotate u`. -/
def framedVortexModuliRotate (u : Circle) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) :=
  Quotient.map' (framedVortexRotate u) fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨_, (framedVortexRotate_smul u g y).symm⟩

@[simp]
theorem framedVortexModuliRotate_mk (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexModuliRotate u (Quotient.mk'' x) = Quotient.mk'' (framedVortexRotate u x) :=
  (rfl)

/-- **Equivariance of the moduli under translations.** Under the identification of the moduli of
framed vortices with `Sym ℂ m`, translation by `a` is `D ↦ D - a`. -/
theorem framedVortexModuliEquiv_framedVortexModuliTranslate (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (framedVortexModuliTranslate a q) =
      (framedVortexModuliEquiv m q).map (· - a) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [framedVortexModuliTranslate_mk, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_framedVortexTranslate]

/-- **Equivariance of the moduli under rotations.** Under the identification of the moduli of
framed vortices with `Sym ℂ m`, rotation by `u` is `D ↦ u⁻¹ D`. -/
theorem framedVortexModuliEquiv_framedVortexModuliRotate (u : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (framedVortexModuliRotate u q) =
      (framedVortexModuliEquiv m q).map ((u : ℂ)⁻¹ * ·) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [framedVortexModuliRotate_mk, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_framedVortexRotate]

end TauCeti.Vortex
