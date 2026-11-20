/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Coupling

/-!
# Translations and rotations of the moduli space of framed plane vortices

The smooth framed degree-`m` vortices of coupling one, the normalized vortex equation
(`TauCeti.Vortex.framedVortexSubMulAction 1 m`), modulo the smooth framed gauge group are
identified with `Sym ℂ m` by the zero divisor (`TauCeti.Vortex.framedVortexModuliEquiv`). This
file shows that this identification is equivariant for the orientation-preserving isometries of
the plane.

* A **translation** pulls a vortex back by `z ↦ z + a` (`TauCeti.Vortex.translateField`). It
  preserves the end framing, so it acts on the smooth framed vortices
  (`TauCeti.Vortex.translateFramedVortex`), and it moves the divisor `D` to `D - a`
  (`TauCeti.Vortex.framedVortexDivisor_translateFramedVortex`).
* A **rotation** by `u` on the unit circle pulls a vortex back by `z ↦ u z`
  (`TauCeti.Vortex.rotateField`). It multiplies the limit of the end framing by `u^m`, so it is
  followed by the constant line-frame gauge `u^(-m)`, which restores the framing
  (`TauCeti.Vortex.rotateFramedVortex`). The divisor `D` goes to `u⁻¹ D`
  (`TauCeti.Vortex.framedVortexDivisor_rotateFramedVortex`).
* Permutations of the zeros act trivially, since a divisor is an unordered multiset of points.

Both operations compose as the group of orientation-preserving isometries of the plane
(`translateFramedVortex_translateFramedVortex`, `rotateFramedVortex_rotateFramedVortex`,
`rotateFramedVortex_translateFramedVortex`)
and conjugate the smooth framed gauge group to itself (`translateFramedVortex_smul`,
`rotateFramedVortex_smul`), with the gauge composed with the isometry
(`TauCeti.Vortex.translateFramedGauge`, `TauCeti.Vortex.rotateFramedGauge`). They therefore descend
to the moduli space (`TauCeti.Vortex.translateFramedVortexModuli`,
`TauCeti.Vortex.rotateFramedVortexModuli`), where the divisor intertwines them with the maps
`D ↦ D - a` and `D ↦ u⁻¹ D` of `Sym ℂ m` (`framedVortexModuliEquiv_translateFramedVortexModuli`,
`framedVortexModuliEquiv_rotateFramedVortexModuli`) and the composition laws persist
(`translateFramedVortexModuli_translateFramedVortexModuli`,
`rotateFramedVortexModuli_rotateFramedVortexModuli`,
`rotateFramedVortexModuli_translateFramedVortexModuli`).

By Taubes's uniqueness theorem the gauge orbit of a vortex is fixed by an isometry exactly when its
divisor is. Hence for `m ≥ 1` a nonzero translation of a framed vortex is never gauge equivalent to
it (`exists_framedGaugeGroup_smul_eq_translateFramedVortex_iff`), so translations act freely on
the moduli space (`translateFramedVortexModuli_eq_self_iff`). A rotation fixes a point of the
moduli space exactly when it fixes its divisor (`rotateFramedVortexModuli_eq_self_iff`); in
particular a vortex whose zeros all lie at the origin is gauge equivalent to each of its rotations
(`exists_framedGaugeGroup_smul_eq_rotateFramedVortex_of_framedVortexDivisor_eq_replicate`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti.Vortex

variable {m : ℕ}

/-! ### Isometries acting on the smooth framed gauge group -/

/-- Composition with the translation `z ↦ z + a`, an endomorphism of the smooth framed gauge
group. -/
def translateFramedGauge (a : ℂ) : framedGaugeGroup →* framedGaugeGroup where
  toFun u := ⟨fun w ↦ u.val (w + a), comp_add_mem_framedGaugeGroup u.property a⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_translateFramedGauge (a : ℂ) (u : framedGaugeGroup) :
    (translateFramedGauge a u : ℂ → Circle) = fun w ↦ u.val (w + a) :=
  (rfl)

/-- Composition with the rotation `z ↦ u z`, an endomorphism of the smooth framed gauge group. -/
def rotateFramedGauge (u : Circle) : framedGaugeGroup →* framedGaugeGroup where
  toFun g := ⟨fun w ↦ g.val (u * w), comp_mul_mem_framedGaugeGroup g.property
      (Circle.coe_ne_zero u)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_rotateFramedGauge (u : Circle) (g : framedGaugeGroup) :
    (rotateFramedGauge u g : ℂ → Circle) = fun w ↦ g.val (u * w) :=
  (rfl)

/-! ### Translations of framed vortices -/

/-- Translating a smooth framed degree-`m` vortex gives a smooth framed degree-`m` vortex. -/
theorem translateField_mem_framedVortexSubMulAction {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedVortexSubMulAction 1 m) (a : ℂ) :
    translateField a x ∈ framedVortexSubMulAction 1 m := by
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  exact mem_framedVortexSubMulAction.2 ⟨contDiff_translateField a hs, fun z ↦ by simpa using hsol _,
    tendsto_sectionValue_translateField hfr a⟩

/-- **Translation of a framed vortex** by `a`: its pullback by `z ↦ z + a`. -/
def translateFramedVortex (a : ℂ) (x : framedVortexSubMulAction 1 m) :
    framedVortexSubMulAction 1 m :=
  ⟨translateField a x, translateField_mem_framedVortexSubMulAction x.property a⟩

@[simp]
theorem coe_translateFramedVortex (a : ℂ) (x : framedVortexSubMulAction 1 m) :
    (translateFramedVortex a x : ℂ → EuclideanSpace ℝ (Fin 4)) = translateField a x :=
  (rfl)

@[simp]
theorem translateFramedVortex_zero (x : framedVortexSubMulAction 1 m) :
    translateFramedVortex 0 x = x :=
  Subtype.ext (translateField_zero _)

/-- Successive translations of framed vortices add. -/
@[simp]
theorem translateFramedVortex_translateFramedVortex (a b : ℂ) (x : framedVortexSubMulAction 1 m) :
    translateFramedVortex a (translateFramedVortex b x) = translateFramedVortex (a + b) x :=
  Subtype.ext (translateField_translateField a b _)

/-- Translation conjugates a smooth framed gauge to its composition with the translation. -/
theorem translateFramedVortex_smul (a : ℂ) (u : framedGaugeGroup)
    (x : framedVortexSubMulAction 1 m) :
    translateFramedVortex a (u • x) = translateFramedGauge a u • translateFramedVortex a x :=
  Subtype.ext (translateField_gaugeTransform a u.val x)

/-- **Translation law for the divisor of a framed vortex.** Translating a framed vortex by `a`
moves its divisor `D` to `D - a`. -/
@[simp]
theorem framedVortexDivisor_translateFramedVortex (a : ℂ) (x : framedVortexSubMulAction 1 m) :
    framedVortexDivisor (translateFramedVortex a x) = (framedVortexDivisor x).map (· - a) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map]
  exact isZeroMultiplicity_sectionValue_translateField
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) a

/-! ### Rotations of framed vortices -/

/-- Rotating a smooth framed degree-`m` vortex by `u` and applying the constant line-frame gauge
`u^(-m)` gives a smooth framed degree-`m` vortex. -/
theorem gaugeTransform_rotateField_mem_framedVortexSubMulAction
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction 1 m) (u : Circle) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) ∈ framedVortexSubMulAction 1 m := by
  obtain ⟨hs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 hx
  simp only [coupledEquation_one] at hsol
  have hr := contDiff_rotateField u hs
  have hd {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ ∞ y) (i : Fin 4) (z : ℂ) :
      DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((contDiff_euclidean.1 hy i).differentiable (by simp)).differentiableAt
  refine mem_framedVortexSubMulAction.2
    ⟨contDiff_gaugeTransform contDiff_const hr, fun z ↦ ?_,
    tendsto_sectionValue_gaugeTransform_rotateField hfr u⟩
  rw [coupledEquation_one, equation_gaugeTransform_eq_zero_iff contDiffAt_const (hd hr · z),
    equation_rotateField_eq_zero_iff (hd hs 0 _) (hd hs 1 _)]
  exact hsol _

/-- **Rotation of a framed vortex** by `u`: its pullback by `z ↦ u z`, followed by the constant
line-frame gauge `u^(-m)` restoring the end framing. -/
def rotateFramedVortex (u : Circle) (x : framedVortexSubMulAction 1 m) :
    framedVortexSubMulAction 1 m :=
  ⟨gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x),
    gaugeTransform_rotateField_mem_framedVortexSubMulAction x.property u⟩

@[simp]
theorem coe_rotateFramedVortex (u : Circle) (x : framedVortexSubMulAction 1 m) :
    (rotateFramedVortex u x : ℂ → EuclideanSpace ℝ (Fin 4)) =
      gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) :=
  (rfl)

@[simp]
theorem rotateFramedVortex_one (x : framedVortexSubMulAction 1 m) : rotateFramedVortex 1 x = x := by
  refine Subtype.ext ?_
  rw [coe_rotateFramedVortex, inv_one, one_pow, rotateField_one, ← Pi.one_def, gaugeTransform_one]

/-- Successive rotations of framed vortices multiply. -/
@[simp]
theorem rotateFramedVortex_rotateFramedVortex (u v : Circle) (x : framedVortexSubMulAction 1 m) :
    rotateFramedVortex u (rotateFramedVortex v x) = rotateFramedVortex (u * v) x := by
  refine Subtype.ext ?_
  simp only [coe_rotateFramedVortex, rotateField_gaugeTransform, rotateField_rotateField]
  rw [← gaugeTransform_mul (differentiable_const _) (differentiable_const _)]
  congr 1
  funext
  simp only [Pi.mul_apply, mul_inv, mul_pow]

/-- **The semidirect product law.** Rotating by `u` a framed vortex translated by `a` is
translating by `u⁻¹ a` the rotated framed vortex. -/
theorem rotateFramedVortex_translateFramedVortex (u : Circle) (a : ℂ)
    (x : framedVortexSubMulAction 1 m) :
    rotateFramedVortex u (translateFramedVortex a x) =
      translateFramedVortex ((u : ℂ)⁻¹ * a) (rotateFramedVortex u x) := by
  refine Subtype.ext ?_
  simp only [coe_rotateFramedVortex, coe_translateFramedVortex, rotateField_translateField,
    translateField_gaugeTransform]

/-- Rotation conjugates a smooth framed gauge to its composition with the rotation. -/
theorem rotateFramedVortex_smul (u : Circle) (g : framedGaugeGroup)
    (x : framedVortexSubMulAction 1 m) :
    rotateFramedVortex u (g • x) = rotateFramedGauge u g • rotateFramedVortex u x := by
  have hg : Differentiable ℝ fun w ↦ (g.val (u * w) : ℂ) :=
    ((mem_framedGaugeGroup _).1 (rotateFramedGauge u g).property).1.differentiable (by simp)
  refine Subtype.ext ?_
  simp only [coe_rotateFramedVortex, SubMulAction.val_smul, framedGaugeGroup_smul,
    coe_rotateFramedGauge, rotateField_gaugeTransform]
  rw [← gaugeTransform_mul (differentiable_const _) hg,
    ← gaugeTransform_mul hg (differentiable_const _)]
  congr 1
  funext
  simp only [Pi.mul_apply, mul_comm]

/-- **Rotation law for the divisor of a framed vortex.** Rotating a framed vortex by `u` rotates
its divisor `D` to `u⁻¹ D`. -/
@[simp]
theorem framedVortexDivisor_rotateFramedVortex (u : Circle) (x : framedVortexSubMulAction 1 m) :
    framedVortexDivisor (rotateFramedVortex u x) =
      (framedVortexDivisor x).map ((u : ℂ)⁻¹ * ·) := by
  rw [framedVortexDivisor_eq_iff, Sym.coe_map, coe_rotateFramedVortex]
  exact isZeroMultiplicity_sectionValue_gaugeTransform continuous_const
    (isZeroMultiplicity_sectionValue_rotateField
      (isZeroMultiplicity_sectionValue_framedVortexDivisor x) u)

/-! ### Isometries fixing a gauge orbit -/

/-- **Translations move every framed vortex of positive degree.** For `m ≥ 1`, the translate by
`a` of a smooth framed degree-`m` vortex is gauge equivalent to it only for `a = 0`, since the
centre of mass of its divisor moves by `-a`. -/
theorem exists_framedGaugeGroup_smul_eq_translateFramedVortex_iff (hm : 0 < m) (a : ℂ)
    (x : framedVortexSubMulAction 1 m) :
    (∃ u : framedGaugeGroup, u • x = translateFramedVortex a x) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨1, by rw [h, one_smul, translateFramedVortex_zero]⟩⟩
  have hD := congrArg (fun D : Sym ℂ m ↦ (D : Multiset ℂ).sum)
    ((framedVortexDivisor_eq_framedVortexDivisor_iff one_pos).2 h)
  simp only [framedVortexDivisor_translateFramedVortex, Sym.coe_map, Multiset.sum_map_sub,
    Multiset.map_id', Multiset.map_const', Multiset.sum_replicate, Sym.card_coe, sub_eq_self,
    nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, hm.ne', false_or] at hD
  exact hD

/-- **Rotations fixing a gauge orbit.** The rotation by `u` of a smooth framed vortex is gauge
equivalent to it exactly when the rotation fixes its divisor. -/
theorem exists_framedGaugeGroup_smul_eq_rotateFramedVortex_iff (u : Circle)
    (x : framedVortexSubMulAction 1 m) :
    (∃ g : framedGaugeGroup, g • x = rotateFramedVortex u x) ↔
      (framedVortexDivisor x).map ((u : ℂ)⁻¹ * ·) = framedVortexDivisor x := by
  rw [← framedVortexDivisor_eq_framedVortexDivisor_iff one_pos,
    framedVortexDivisor_rotateFramedVortex, eq_comm]

/-- **Rotational symmetry of the vortex concentrated at the origin.** A smooth framed degree-`m`
vortex whose zeros all lie at the origin is gauge equivalent to each of its rotations. -/
theorem exists_framedGaugeGroup_smul_eq_rotateFramedVortex_of_framedVortexDivisor_eq_replicate
    {x : framedVortexSubMulAction 1 m} (hx : framedVortexDivisor x = Sym.replicate m 0)
    (u : Circle) : ∃ g : framedGaugeGroup, g • x = rotateFramedVortex u x := by
  refine (exists_framedGaugeGroup_smul_eq_rotateFramedVortex_iff u x).2 ?_
  rw [hx, Sym.eq_replicate_iff]
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Sym.mem_map.1 hb
  rw [(Sym.mem_replicate.1 ha).2, mul_zero]

/-! ### The induced maps of the moduli space -/

/-- Translation by `a` of the moduli space of smooth framed degree-`m` vortices. -/
def translateFramedVortexModuli (a : ℂ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m) :=
  Quotient.map' (translateFramedVortex a) fun x y h ↦ by
    obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨translateFramedGauge a u, (translateFramedVortex_smul a u y).symm⟩

@[simp]
theorem translateFramedVortexModuli_mk (a : ℂ) (x : framedVortexSubMulAction 1 m) :
    translateFramedVortexModuli a (Quotient.mk'' x) = Quotient.mk'' (translateFramedVortex a x) :=
  (rfl)

/-- Rotation by `u` of the moduli space of smooth framed degree-`m` vortices. -/
def rotateFramedVortexModuli (u : Circle) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m) →
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m) :=
  Quotient.map' (rotateFramedVortex u) fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2
      ⟨rotateFramedGauge u g, (rotateFramedVortex_smul u g y).symm⟩

@[simp]
theorem rotateFramedVortexModuli_mk (u : Circle) (x : framedVortexSubMulAction 1 m) :
    rotateFramedVortexModuli u (Quotient.mk'' x) = Quotient.mk'' (rotateFramedVortex u x) :=
  (rfl)

/-- **Equivariance of the moduli space under translations.** The divisor carries the
translation by `a` of the moduli space to the map `D ↦ D - a` of `Sym ℂ m`. -/
@[simp]
theorem framedVortexModuliEquiv_translateFramedVortexModuli (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    framedVortexModuliEquiv one_pos m (translateFramedVortexModuli a q) =
      (framedVortexModuliEquiv one_pos m q).map (· - a) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [translateFramedVortexModuli_mk, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_translateFramedVortex]

/-- **Equivariance of the moduli space under rotations.** The divisor carries the rotation by `u`
of the moduli space to the map `D ↦ u⁻¹ D` of `Sym ℂ m`. -/
@[simp]
theorem framedVortexModuliEquiv_rotateFramedVortexModuli (u : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    framedVortexModuliEquiv one_pos m (rotateFramedVortexModuli u q) =
      (framedVortexModuliEquiv one_pos m q).map ((u : ℂ)⁻¹ * ·) :=
  Quotient.inductionOn' q fun x ↦ by
    rw [rotateFramedVortexModuli_mk, framedVortexModuliEquiv_mk, framedVortexModuliEquiv_mk,
      framedVortexDivisor_rotateFramedVortex]

@[simp]
theorem translateFramedVortexModuli_zero
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    translateFramedVortexModuli 0 q = q :=
  Quotient.inductionOn' q fun x ↦ by simp

@[simp]
theorem translateFramedVortexModuli_translateFramedVortexModuli (a b : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    translateFramedVortexModuli a (translateFramedVortexModuli b q) =
      translateFramedVortexModuli (a + b) q :=
  Quotient.inductionOn' q fun x ↦ by simp

@[simp]
theorem rotateFramedVortexModuli_one
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    rotateFramedVortexModuli 1 q = q :=
  Quotient.inductionOn' q fun x ↦ by simp

@[simp]
theorem rotateFramedVortexModuli_rotateFramedVortexModuli (u v : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    rotateFramedVortexModuli u (rotateFramedVortexModuli v q) =
      rotateFramedVortexModuli (u * v) q :=
  Quotient.inductionOn' q fun x ↦ by simp

/-- The semidirect product law on the moduli space: rotating by `u` after translating by `a` is
translating by `u⁻¹ a` after rotating by `u`. -/
theorem rotateFramedVortexModuli_translateFramedVortexModuli (u : Circle) (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    rotateFramedVortexModuli u (translateFramedVortexModuli a q) =
      translateFramedVortexModuli ((u : ℂ)⁻¹ * a) (rotateFramedVortexModuli u q) :=
  Quotient.inductionOn' q fun x ↦ by
    simp only [translateFramedVortexModuli_mk, rotateFramedVortexModuli_mk,
      rotateFramedVortex_translateFramedVortex]

/-- **Translations act freely on the moduli space of positive degree.** For `m ≥ 1`, the
translation by `a` fixes a point of the moduli space only for `a = 0`. -/
theorem translateFramedVortexModuli_eq_self_iff (hm : 0 < m) (a : ℂ)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    translateFramedVortexModuli a q = q ↔ a = 0 :=
  Quotient.inductionOn' q fun x ↦ by
    rw [translateFramedVortexModuli_mk, ← exists_framedGaugeGroup_smul_eq_translateFramedVortex_iff
      hm a x]
    exact Quotient.eq''.trans (MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff)

/-- **Rotations fixing a point of the moduli space** are those fixing its divisor. -/
theorem rotateFramedVortexModuli_eq_self_iff (u : Circle)
    (q : MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m)) :
    rotateFramedVortexModuli u q = q ↔
      (framedVortexModuliEquiv one_pos m q).map ((u : ℂ)⁻¹ * ·) =
        framedVortexModuliEquiv one_pos m q := by
  rw [← framedVortexModuliEquiv_rotateFramedVortexModuli,
    (framedVortexModuliEquiv one_pos m).apply_eq_iff_eq]

end TauCeti.Vortex
