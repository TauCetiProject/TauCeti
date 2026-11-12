/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.Symmetry
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Euclidean symmetries of the moduli space of framed plane vortices

A smooth framed degree-`m` vortex is a smooth solution `x` of the vortex equations on `ℂ` whose
section `α` satisfies `α(z) (z / |z|)⁻ᵐ → 1` at infinity
(`TauCeti.Vortex.framedVortexSubMulAction`). Taubes's theorem identifies the orbits of the smooth
framed gauge group on these vortices with the effective divisors of degree `m`, through the zero
divisor of the section (`TauCeti.Vortex.framedVortexModuliEquiv`). This file shows that this
identification is equivariant for the orientation-preserving isometries of the plane.

**Translations.** The pullback `z ↦ x (z + a)` (`TauCeti.Vortex.translateField`) of a framed
vortex is a framed vortex (`TauCeti.Vortex.framedVortexTranslate`), and its section vanishes at
the points of the divisor moved by `-a`:
`div (x (· + a)) = div x - a` (`TauCeti.Vortex.framedVortexDivisor_framedVortexTranslate`).

**Rotations and the line frame.** The pullback by `z ↦ u z`, for `u` on the unit circle
(`TauCeti.Vortex.rotateField`), multiplies the limit of the end framing by `u^m`. The constant
gauge `u^(-m)` restores it; this constant gauge is a change of frame of the line at infinity, not
an element of the framed gauge group. The composite is a framed vortex
(`TauCeti.Vortex.framedVortexRotate`), whose divisor is the divisor of `x` rotated by `u⁻¹`
(`TauCeti.Vortex.framedVortexDivisor_framedVortexRotate`).

Both operations satisfy the group laws of the orientation-preserving isometries of the plane,
including the semidirect product law
`rotate u ∘ translate a = translate (u⁻¹ a) ∘ rotate u`, and they carry the action of a framed
gauge `g` to the action of the moved gauge `g (· + a)`, respectively `g (u ·)`
(`TauCeti.Vortex.framedGaugeTranslate`, `TauCeti.Vortex.framedGaugeRotate`). They therefore
descend to the moduli space of framed gauge orbits
(`TauCeti.Vortex.framedVortexModuliTranslate`, `TauCeti.Vortex.framedVortexModuliRotate`), where
the divisor identification intertwines them with the maps `D ↦ D - a` and `D ↦ u⁻¹ D` of
`Sym ℂ m`.

Combined with Taubes's uniqueness theorem this gives the symmetries of individual vortices: two
framed vortices are related by a translation up to framed gauge exactly when their divisors are
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_framedVortexTranslate_eq_iff`), and similarly for
rotations (`TauCeti.Vortex.exists_framedGaugeGroup_smul_framedVortexRotate_eq_iff`). A vortex whose
zeros all sit at the origin, the radially symmetric vortex of Jaffe and Taubes, is invariant
under every rotation up to framed gauge
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_framedVortexRotate_eq`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

open Complex Filter Topology

namespace TauCeti.Vortex

variable {m : ℕ}

/-! ### Translations -/

/-- Translations preserve smooth framed degree-`m` vortices. -/
theorem translateField_mem_framedVortexSubMulAction (a : ℂ) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedVortexSubMulAction m) : translateField a x ∈ framedVortexSubMulAction m := by
  obtain ⟨hx, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  exact mem_framedVortexSubMulAction.2 ⟨contDiff_translateField a hx,
    fun z ↦ by rw [equation_translateField, hsol], tendsto_sectionValue_translateField hfr a⟩

/-- **Translation of a framed vortex**, the pullback `z ↦ x (z + a)`. -/
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

/-- **Translation of framed gauges**, `g ↦ g (· + a)`. -/
def framedGaugeTranslate (a : ℂ) : framedGaugeGroup →* framedGaugeGroup where
  toFun g := ⟨fun z ↦ g.1 (z + a), by
    obtain ⟨hg, hg1⟩ := (mem_framedGaugeGroup _).1 g.2
    exact (mem_framedGaugeGroup _).2 ⟨hg.comp (contDiff_id.add contDiff_const),
      hg1.comp (Homeomorph.addRight a).map_cocompact.le⟩⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)

@[simp]
theorem coe_framedGaugeTranslate_apply (a : ℂ) (g : framedGaugeGroup) (z : ℂ) :
    (framedGaugeTranslate a g : ℂ → Circle) z = (g : ℂ → Circle) (z + a) :=
  (rfl)

/-- Translations intertwine the actions of a framed gauge and of its translate. -/
theorem framedVortexTranslate_smul (a : ℂ) (g : framedGaugeGroup)
    (x : framedVortexSubMulAction m) :
    framedVortexTranslate a (g • x) = framedGaugeTranslate a g • framedVortexTranslate a x :=
  Subtype.ext (translateField_gaugeTransform a g x)

/-- **Translation law for the divisor.** The zeros of the translate `x (· + a)` are the zeros of
`x` moved by `-a`. -/
@[simp]
theorem framedVortexDivisor_framedVortexTranslate (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (framedVortexTranslate a x) = (framedVortexDivisor x).map (· - a) := by
  rw [framedVortexDivisor_eq_iff]
  have h := (isZeroMultiplicity_sectionValue_framedVortexDivisor x).comp_mul_add one_ne_zero a
  simp only [one_mul] at h
  convert h using 1
  · exact funext fun w ↦ sectionValue_translateField a x w
  · funext z
    have hc := Multiset.count_map_eq_count' (· - a) (framedVortexDivisor x : Multiset ℂ)
      (sub_left_injective (b := a)) (z + a)
    rwa [add_sub_cancel_right, ← Sym.coe_map] at hc

/-- Two framed vortices are related by a translation by `a`, up to framed gauge, exactly when
their divisors differ by `-a`. -/
theorem exists_framedGaugeGroup_smul_framedVortexTranslate_eq_iff (a : ℂ)
    {x y : framedVortexSubMulAction m} :
    (∃ g : framedGaugeGroup, g • framedVortexTranslate a y = x) ↔
      framedVortexDivisor x = (framedVortexDivisor y).map (· - a) := by
  simpa only [framedVortexDivisor_framedVortexTranslate] using
    (framedVortexDivisor_eq_framedVortexDivisor_iff (x := x) (y := framedVortexTranslate a y)).symm

/-! ### Rotations -/

/-- The constant line-frame gauge `u^(-m)` restores the end framing of a rotated framed
vortex. -/
theorem gaugeTransform_rotateField_mem_framedVortexSubMulAction (u : Circle)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction m) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) ∈ framedVortexSubMulAction m := by
  obtain ⟨hx, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  have hr := contDiff_rotateField u hx
  have hxi (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (((contDiff_piLp 2).1 hx i).differentiable (by simp)).differentiableAt
  have hri (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ rotateField u x w i) z :=
    (((contDiff_piLp 2).1 hr i).differentiable (by simp)).differentiableAt
  refine mem_framedVortexSubMulAction.2 ⟨contDiff_gaugeTransform contDiff_const hr, fun z ↦ ?_,
    tendsto_sectionValue_gaugeTransform_rotateField hfr u⟩
  rw [equation_gaugeTransform_eq_zero_iff contDiffAt_const (hri · z),
    equation_rotateField_eq_zero_iff (hxi 0 _) (hxi 1 _)]
  exact hsol _

/-- **Rotation of a framed vortex** by `u` on the unit circle: the pullback by `z ↦ u z`,
followed by the constant line-frame gauge `u^(-m)` restoring the end framing. -/
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
theorem framedVortexRotate_one (x : framedVortexSubMulAction m) : framedVortexRotate 1 x = x :=
  Subtype.ext <| by
    rw [coe_framedVortexRotate, inv_one, one_pow, rotateField_one, ← Pi.one_def,
      gaugeTransform_one]

/-- Successive rotations multiply. -/
@[simp]
theorem framedVortexRotate_framedVortexRotate (u v : Circle) (x : framedVortexSubMulAction m) :
    framedVortexRotate u (framedVortexRotate v x) = framedVortexRotate (u * v) x := by
  refine Subtype.ext ?_
  simp only [coe_framedVortexRotate, rotateField_gaugeTransform, rotateField_rotateField]
  rw [← gaugeTransform_mul (differentiable_const _) (differentiable_const _)]
  congr 1
  funext _
  simp only [Pi.mul_apply, mul_inv, mul_pow]

/-- **The semidirect product law.** Rotating by `u` a vortex translated by `a` is translating
the rotated vortex by `u⁻¹ a`. -/
theorem framedVortexRotate_framedVortexTranslate (u : Circle) (a : ℂ)
    (x : framedVortexSubMulAction m) :
    framedVortexRotate u (framedVortexTranslate a x) =
      framedVortexTranslate ((u : ℂ)⁻¹ * a) (framedVortexRotate u x) :=
  Subtype.ext <| by
    simp only [coe_framedVortexRotate, coe_framedVortexTranslate, rotateField_translateField,
      translateField_gaugeTransform]

/-- **Rotation of framed gauges**, `g ↦ g (u ·)`. -/
def framedGaugeRotate (u : Circle) : framedGaugeGroup →* framedGaugeGroup where
  toFun g := ⟨fun z ↦ g.1 (u * z), by
    obtain ⟨hg, hg1⟩ := (mem_framedGaugeGroup _).1 g.2
    exact (mem_framedGaugeGroup _).2 ⟨hg.comp (contDiff_const.mul contDiff_id),
      hg1.comp (tendsto_cocompact_mul_left₀ (Circle.coe_ne_zero u))⟩⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)

@[simp]
theorem coe_framedGaugeRotate_apply (u : Circle) (g : framedGaugeGroup) (z : ℂ) :
    (framedGaugeRotate u g : ℂ → Circle) z = (g : ℂ → Circle) (u * z) :=
  (rfl)

/-- Rotations intertwine the actions of a framed gauge and of its rotate. The constant line-frame
gauge commutes with every gauge. -/
theorem framedVortexRotate_smul (u : Circle) (g : framedGaugeGroup)
    (x : framedVortexSubMulAction m) :
    framedVortexRotate u (g • x) = framedGaugeRotate u g • framedVortexRotate u x := by
  refine Subtype.ext ?_
  have hG : (framedGaugeRotate u g : ℂ → Circle) = fun z ↦ (g : ℂ → Circle) (u * z) :=
    funext (coe_framedGaugeRotate_apply u g)
  have hg : Differentiable ℝ fun z ↦ ((g : ℂ → Circle) (u * z) : ℂ) := by
    simpa only [hG] using
      ((mem_framedGaugeGroup _).1 (framedGaugeRotate u g).2).1.differentiable (by simp)
  simp only [coe_framedVortexRotate, SubMulAction.val_smul, framedGaugeGroup_smul,
    rotateField_gaugeTransform, hG]
  rw [← gaugeTransform_mul (differentiable_const _) hg,
    ← gaugeTransform_mul hg (differentiable_const _)]
  congr 1
  funext w
  exact mul_comm _ _

/-- **Rotation law for the divisor.** The zeros of the rotated vortex are the zeros of `x`
rotated by `u⁻¹`; the line-frame gauge does not move them. -/
@[simp]
theorem framedVortexDivisor_framedVortexRotate (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (framedVortexRotate u x) =
      (framedVortexDivisor x).map ((u : ℂ)⁻¹ * ·) := by
  rw [framedVortexDivisor_eq_iff]
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  have h := ((isZeroMultiplicity_sectionValue_framedVortexDivisor x).comp_mul_add hu 0
    ).mul_left_of_continuous (g := fun _ ↦ ((u⁻¹ ^ m : Circle) : ℂ)) continuous_const
      fun _ ↦ Circle.coe_ne_zero _
  simp only [add_zero] at h
  convert h using 1
  · funext w
    rw [coe_framedVortexRotate, sectionValue_gaugeTransform, sectionValue_rotateField]
  · funext z
    have hc := Multiset.count_map_eq_count' ((u : ℂ)⁻¹ * ·) (framedVortexDivisor x : Multiset ℂ)
      (mul_right_injective₀ (inv_ne_zero hu)) ((u : ℂ) * z)
    rwa [inv_mul_cancel_left₀ hu, ← Sym.coe_map] at hc

/-- Two framed vortices are related by a rotation by `u`, followed by the line-frame gauge, up to
framed gauge, exactly when their divisors differ by the rotation `u⁻¹`. -/
theorem exists_framedGaugeGroup_smul_framedVortexRotate_eq_iff (u : Circle)
    {x y : framedVortexSubMulAction m} :
    (∃ g : framedGaugeGroup, g • framedVortexRotate u y = x) ↔
      framedVortexDivisor x = (framedVortexDivisor y).map ((u : ℂ)⁻¹ * ·) := by
  simpa only [framedVortexDivisor_framedVortexRotate] using
    (framedVortexDivisor_eq_framedVortexDivisor_iff (x := x) (y := framedVortexRotate u y)).symm

/-- **Rotational symmetry of the centred vortex** (Jaffe–Taubes). A framed vortex whose zeros all
sit at the origin is invariant, up to framed gauge, under every rotation followed by the
line-frame gauge. -/
theorem exists_framedGaugeGroup_smul_framedVortexRotate_eq (u : Circle)
    {x : framedVortexSubMulAction m} (hx : framedVortexDivisor x = Sym.replicate m 0) :
    ∃ g : framedGaugeGroup, g • framedVortexRotate u x = x := by
  refine (exists_framedGaugeGroup_smul_framedVortexRotate_eq_iff u).2 ?_
  rw [hx]
  refine Sym.coe_injective ?_
  simp [Sym.coe_map, Sym.coe_replicate]

/-! ### The moduli space -/

/-- Translation by `a` of the moduli space of framed degree-`m` vortices. -/
def framedVortexModuliTranslate (a : ℂ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) :=
  Quotient.map (framedVortexTranslate a) fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨framedGaugeTranslate a g, (framedVortexTranslate_smul a g y).symm⟩

@[simp]
theorem framedVortexModuliTranslate_mk (a : ℂ) (x : framedVortexSubMulAction m) :
    framedVortexModuliTranslate a (Quotient.mk'' x) = Quotient.mk'' (framedVortexTranslate a x) :=
  (rfl)

/-- Rotation by `u` of the moduli space of framed degree-`m` vortices. -/
def framedVortexModuliRotate (u : Circle) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) :=
  Quotient.map (framedVortexRotate u) fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨framedGaugeRotate u g, (framedVortexRotate_smul u g y).symm⟩

@[simp]
theorem framedVortexModuliRotate_mk (u : Circle) (x : framedVortexSubMulAction m) :
    framedVortexModuliRotate u (Quotient.mk'' x) = Quotient.mk'' (framedVortexRotate u x) :=
  (rfl)

/-- **Translation equivariance of the moduli space.** The divisor identification of the framed
gauge orbits with `Sym ℂ m` carries translation by `a` to the map `D ↦ D - a`. -/
theorem framedVortexModuliEquiv_framedVortexModuliTranslate (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (framedVortexModuliTranslate a q) =
      (framedVortexModuliEquiv m q).map (· - a) :=
  Quotient.inductionOn' q fun x ↦ by simp

/-- **Rotation equivariance of the moduli space.** The divisor identification of the framed gauge
orbits with `Sym ℂ m` carries rotation by `u` to the map `D ↦ u⁻¹ D`. -/
theorem framedVortexModuliEquiv_framedVortexModuliRotate (u : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m)) :
    framedVortexModuliEquiv m (framedVortexModuliRotate u q) =
      (framedVortexModuliEquiv m q).map ((u : ℂ)⁻¹ * ·) :=
  Quotient.inductionOn' q fun x ↦ by simp

end TauCeti.Vortex
