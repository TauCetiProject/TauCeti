/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.Heegaard.LensSpace.Splitting
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Unknot
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Lens spaces as surgeries on the unknot

For coprime integers `p > 0` and `q`, the `p / q`-surgery on the unknot in `S³` is a lens space
(Rolfsen, *Knots and Links*, Chapter 9): the exterior of the unknot is a solid torus, and gluing a
second solid torus to it so that the meridian of the second goes to the `(p, q)` curve gives the
union of two solid tori glued along their boundary tori by an element of `SL₂(ℤ)`. This file
realizes that filling inside the lens space `L(p; ℓ₀, ℓ₁)` with `ℓ₁ = -q ℓ₀` modulo `p`, as a
`TauCeti.DehnFilling` of the exterior of the unknot along the slope of value `p / q` for the
framing of the standard solid torus neighbourhood `TauCeti.unknotSolidTorus`, which is the
preferred framing (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). For `ℓ = ![1, q]`,
the lens space `L(p, q)` is thus the `-p / q`-surgery on the unknot, as in Rolfsen.

The two solid tori are the pieces `‖x 0‖ ≤ ‖x 1‖` and `‖x 1‖ ≤ ‖x 0‖` of the genus-one Heegaard
splitting of the lens space (`TauCeti.LensSpace.heegaardSplitting`). A point `(u, w)` of
`D² × S¹` gives the unit vector of `ℂ²` with coordinates proportional to `u w ^ e` and `w` (in the
two coordinates of the piece), and the rotations of the lens space act on these points through
`w ↦ ζ w`, `ζ ^ p = 1`, as soon as `e ℓⱼ = ℓᵢ` modulo `p`. So the image in the lens space depends
only on `(u, w ^ p)`, and this defines an embedding of the solid torus onto the piece. With
`s p + t q = 1`, the filling solid torus is the piece `‖x 0‖ ≤ ‖x 1‖` with `e = -t`, and the knot
exterior, through `TauCeti.unknotExteriorHomeomorph`, is the piece `‖x 1‖ ≤ ‖x 0‖` with `e = -q`.
On the common boundary torus these coordinates differ by the gluing
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`, of determinant `s p + t q = 1`, which carries the
meridian `(a, 1)` of the filling solid torus to the `(p, q)` curve of the boundary torus of the
exterior.

## Main definitions

* `TauCeti.unknotLensSpaceDehnFilling`: the lens space `L(p; ℓ₀, ℓ₁)`, with `ℓ₁ = -q ℓ₀`, as the
  Dehn filling of the exterior of the unknot along the slope `p / q`.

## Main results

* `TauCeti.unknotLensSpaceDehnFilling_gluing_apply`: the gluing of the boundary tori.
* `TauCeti.range_unknotLensSpaceDehnFilling_solidTorusEmbedding`,
  `TauCeti.range_unknotLensSpaceDehnFilling_exteriorEmbedding`: the filling solid torus and the
  knot exterior are the two handlebodies of the genus-one Heegaard splitting of the lens space.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9B and 9G
  (lens spaces as unions of two solid tori, and as surgeries on the unknot).
-/

public section

noncomputable section

open Metric Set Topology Function

namespace TauCeti

/-! ### The gluing of the boundary tori -/

/-- The homeomorphism `(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)` of the torus `S¹ × S¹` given by the
matrix `[[p, -t], [q, s]]` of determinant `s p + t q = 1`. -/
private def torusGluing (p q s t : ℤ) (h : s * p + t * q = 1) :
    Circle × Circle ≃ₜ Circle × Circle where
  toFun x := (x.1 ^ p * x.2 ^ (-t), x.1 ^ q * x.2 ^ s)
  invFun y := (y.1 ^ s * y.2 ^ t, y.1 ^ (-q) * y.2 ^ p)
  left_inv x := by
    ext1
    · simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, show p * s + q * t = 1 by linear_combination h,
        show -t * s + s * t = 0 by ring, zpow_one, zpow_zero, mul_one]
    · simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, show p * -q + q * p = 0 by ring,
        show -t * -q + s * p = 1 by linear_combination h, zpow_one, zpow_zero, one_mul]
  right_inv y := by
    ext1
    · simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add,
        show s * p + -q * -t = 1 by linear_combination h, show t * p + p * -t = 0 by ring, zpow_one,
        zpow_zero, mul_one]
    · simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, show s * q + -q * s = 0 by ring,
        show t * q + p * s = 1 by linear_combination h, zpow_one, zpow_zero, one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem torusGluing_apply (p q s t : ℤ) (h : s * p + t * q = 1) (x : Circle × Circle) :
    torusGluing p q s t h x = (x.1 ^ p * x.2 ^ (-t), x.1 ^ q * x.2 ^ s) :=
  (rfl)

/-- The gluing carries the meridian `(a, 1)` to the `(p, q)` curve. -/
private theorem torusGluing_torusCurve (p q s t : ℤ) (h : s * p + t * q = 1)
    (τ : unitInterval) : torusGluing p q s t h (torusCurve 1 0 τ) = torusCurve p q τ := by
  simp only [torusGluing_apply, torusCurve_apply, Int.cast_one, one_mul, Int.cast_zero, zero_mul,
    mul_zero, Circle.exp_zero, one_zpow, mul_one]
  refine Prod.ext ?_ ?_ <;>
    · simp only
      rw [← Circle.exp_intCast_mul]
      ring_nf

/-! ### Solid tori in a three-dimensional lens space -/

namespace LensSpace

variable {m : ℕ} [NeZero m] {ℓ : Fin 2 → (ZMod m)ˣ}

/-- The map `(u, w) ↦ (u, w ^ m)` of the solid torus. -/
private def powCore (m : ℕ) : C(SolidTorus, SolidTorus) :=
  ⟨fun x ↦ (x.1, x.2 ^ m), by fun_prop⟩

private theorem powCore_apply (m : ℕ) (x : SolidTorus) : powCore m x = (x.1, x.2 ^ m) :=
  (rfl)

private theorem powCore_surjective : Surjective (powCore m) := by
  rintro ⟨u, v⟩
  obtain ⟨w, rfl⟩ := Circle.exists_pow_nat_eq (NeZero.ne m) v
  exact ⟨(u, w), rfl⟩

private theorem isQuotientMap_powCore : IsQuotientMap (powCore m) :=
  .of_surjective_continuous powCore_surjective (powCore m).continuous

/-! #### Descending a cover of a solid torus to the lens space -/

section Descend

variable (ψ : C(SolidTorus, sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)) (j : Fin 2)

/-- The rotations of the lens space act on the image of `ψ` through the core circle: the rotation by
`a` multiplies the core coordinate `w` by `e^{2πi ℓⱼ a / m}`. -/
private def IsRotationCompatible : Prop :=
  ∀ (a : Multiplicative (ZMod m)) (x : SolidTorus),
    lensRotation m ℓ a (ψ x) = ψ (x.1, ZMod.toCircle ((ℓ j : ZMod m) * a.toAdd) * x.2)

variable {ψ j}

/-- The image of `ψ (u, w)` in the lens space depends only on `(u, w ^ m)`. -/
private theorem mk_eq_mk_of_powCore_eq (hψ : IsRotationCompatible (ℓ := ℓ) ψ j) {x y : SolidTorus}
    (hxy : powCore m x = powCore m y) : mk m ℓ (ψ x) = mk m ℓ (ψ y) := by
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hxy
  obtain ⟨b, hb⟩ := ZMod.exists_toCircle_eq_of_pow_eq_one (n := m) (ζ := y.2 * x.2⁻¹)
    (by rw [mul_pow, inv_pow, show x.2 ^ m = y.2 ^ m from h2, mul_inv_cancel])
  refine ((mk_eq_mk_iff m ℓ _ _).2 ⟨Multiplicative.ofAdd (((ℓ j)⁻¹ : (ZMod m)ˣ) * b), ?_⟩).symm
  rw [hψ, toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, hb,
    inv_mul_cancel_right]
  exact congrArg (fun x ↦ (ψ x : EuclideanSpace ℂ (Fin 2)))
    (Prod.ext (by simpa [powCore_apply] using h1) rfl)

/-- The map of the solid torus into the lens space sending `(u, w ^ m)` to the image of
`ψ (u, w)`. -/
private def descend (hψ : IsRotationCompatible (ℓ := ℓ) ψ j) : C(SolidTorus, LensSpace m ℓ) :=
  (isQuotientMap_powCore (m := m)).lift ⟨mk m ℓ ∘ ψ, (continuous_mk m ℓ).comp ψ.continuous⟩
    fun _ _ h ↦ mk_eq_mk_of_powCore_eq hψ h

private theorem descend_powCore (hψ : IsRotationCompatible (ℓ := ℓ) ψ j) (x : SolidTorus) :
    descend hψ (powCore m x) = mk m ℓ (ψ x) := by
  rw [descend]
  exact DFunLike.congr_fun ((isQuotientMap_powCore (m := m)).lift_comp
    ⟨mk m ℓ ∘ ψ, (continuous_mk m ℓ).comp ψ.continuous⟩
    fun _ _ h ↦ mk_eq_mk_of_powCore_eq hψ h) x

private theorem descend_injective (hψ : IsRotationCompatible (ℓ := ℓ) ψ j)
    (hinj : Injective ψ) : Injective (descend hψ) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := powCore_surjective (m := m) x
  obtain ⟨y, rfl⟩ := powCore_surjective (m := m) y
  rw [descend_powCore, descend_powCore, mk_eq_mk_iff] at hxy
  obtain ⟨a, ha⟩ := hxy
  rw [← hinj (Subtype.ext ((hψ a y).symm.trans ha)), powCore_apply, powCore_apply, mul_pow,
    ZMod.toCircle_pow_eq_one, one_mul]

private theorem isClosedEmbedding_descend (hψ : IsRotationCompatible (ℓ := ℓ) ψ j)
    (hinj : Injective ψ) : IsClosedEmbedding (descend hψ) :=
  (descend hψ).continuous.isClosedEmbedding (descend_injective hψ hinj)

private theorem range_descend (hψ : IsRotationCompatible (ℓ := ℓ) ψ j) :
    range (descend hψ) = mk m ℓ '' range ψ := by
  rw [← (powCore_surjective (m := m)).range_comp, ← range_comp]
  exact congrArg range (funext (descend_powCore hψ))

end Descend

/-! #### The two solid tori -/

/-- The twist `(u, w) ↦ (u w ^ e, w)` of the solid torus. -/
private def twist (e : ℤ) : SolidTorus ≃ₜ closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1 where
  toFun x := (⟨x.1 * (x.2 ^ e : Circle), by
      simpa [mem_closedBall_zero_iff] using mem_closedBall_zero_iff.1 x.1.2⟩,
    Circle.homeomorphSphere x.2)
  invFun y := (⟨y.1 * (Circle.homeomorphSphere.symm y.2 ^ (-e) : Circle), by
      simpa [mem_closedBall_zero_iff] using mem_closedBall_zero_iff.1 y.1.2⟩,
    Circle.homeomorphSphere.symm y.2)
  left_inv x := by
    refine Prod.ext (Subtype.ext ?_) (Circle.homeomorphSphere.symm_apply_apply x.2)
    simp only [Homeomorph.symm_apply_apply, mul_assoc, ← Circle.coe_mul, ← zpow_add,
      add_neg_cancel, zpow_zero, Circle.coe_one, mul_one]
  right_inv y := by
    refine Prod.ext (Subtype.ext ?_) (Circle.homeomorphSphere.apply_symm_apply y.2)
    simp only [mul_assoc, ← Circle.coe_mul, ← zpow_add, neg_add_cancel, zpow_zero, Circle.coe_one,
      mul_one]
  continuous_toFun := by
    refine .prodMk (.subtype_mk ?_ _) (Circle.homeomorphSphere.continuous.comp continuous_snd)
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp ((continuous_zpow (G := Circle) e).comp continuous_snd))
  continuous_invFun := by
    have h : Continuous fun y : closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1 ↦
        Circle.homeomorphSphere.symm y.2 := by fun_prop
    refine .prodMk (.subtype_mk ?_ _) h
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp ((continuous_zpow (G := Circle) (-e)).comp h))

/-- The solid torus `‖x 0‖ ≤ ‖x 1‖` of the unit sphere of `ℂ²`, parametrized so that `(u, w)` goes
to the unit vector proportional to `(u w ^ e, w)`. -/
private def leftCover (e : ℤ) : C(SolidTorus, sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  ⟨fun x ↦ (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv
      ((sphereProdFstLeHomeomorph ℂ ℂ).symm (twist e x)), by fun_prop⟩

/-- The solid torus `‖x 1‖ ≤ ‖x 0‖` of the unit sphere of `ℂ²`, parametrized so that `(u, w)` goes
to the unit vector proportional to `(w, u w ^ e)`. -/
private def rightCover (e : ℤ) : C(SolidTorus, sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  ⟨fun x ↦ (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv
      ((sphereProdSndLeHomeomorph ℂ ℂ).symm (twist e x).swap), by fun_prop⟩

private theorem leftCover_injective (e : ℤ) : Injective (leftCover e) :=
  (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv.injective.comp
    (Subtype.val_injective.comp ((sphereProdFstLeHomeomorph ℂ ℂ).symm.injective.comp
      (twist e).injective))

private theorem rightCover_injective (e : ℤ) : Injective (rightCover e) :=
  (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv.injective.comp
    (Subtype.val_injective.comp ((sphereProdSndLeHomeomorph ℂ ℂ).symm.injective.comp
      (Prod.swap_injective.comp (twist e).injective)))

private theorem coe_leftCover_apply_zero (e : ℤ) (x : SolidTorus) :
    (leftCover e x : EuclideanSpace ℂ (Fin 2)) 0 =
      (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • ((x.1 : ℂ) * (x.2 ^ e : Circle)) := by
  simp [leftCover, twist]

private theorem coe_leftCover_apply_one (e : ℤ) (x : SolidTorus) :
    (leftCover e x : EuclideanSpace ℂ (Fin 2)) 1 = (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • (x.2 : ℂ) := by
  simp [leftCover, twist]

private theorem coe_rightCover_apply_zero (e : ℤ) (x : SolidTorus) :
    (rightCover e x : EuclideanSpace ℂ (Fin 2)) 0 = (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • (x.2 : ℂ) := by
  simp [rightCover, twist]

private theorem coe_rightCover_apply_one (e : ℤ) (x : SolidTorus) :
    (rightCover e x : EuclideanSpace ℂ (Fin 2)) 1 =
      (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • ((x.1 : ℂ) * (x.2 ^ e : Circle)) := by
  simp [rightCover, twist]

private theorem range_leftCover (e : ℤ) :
    range (leftCover e) = {x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 |
      ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖} := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    simp only [mem_ofPred_eq, coe_leftCover_apply_zero, coe_leftCover_apply_one, norm_smul,
      norm_mul, Circle.norm_coe, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.1 y.1.2)
  · refine ⟨(twist e).symm (sphereProdFstLeHomeomorph ℂ ℂ
      ⟨(EuclideanSpace.finTwoEquivProd ℂ).unitSphereIsometryEquiv x, by simpa using hx⟩), ?_⟩
    ext1
    simp [leftCover]

private theorem range_rightCover (e : ℤ) :
    range (rightCover e) = {x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 |
      ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖} := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    simp only [mem_ofPred_eq, coe_rightCover_apply_zero, coe_rightCover_apply_one, norm_smul,
      norm_mul, Circle.norm_coe, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.1 y.1.2)
  · refine ⟨(twist e).symm (sphereProdSndLeHomeomorph ℂ ℂ
      ⟨(EuclideanSpace.finTwoEquivProd ℂ).unitSphereIsometryEquiv x, by simpa using hx⟩).swap, ?_⟩
    ext1
    simp [rightCover]

/-- `ζ ^ e = e^{2πi ℓᵢ a / m}` for `ζ = e^{2πi ℓⱼ a / m}` when `e ℓⱼ = ℓᵢ` modulo `m`. -/
private theorem toCircle_zpow {e : ℤ} {i j : Fin 2} (he : (e : ZMod m) * ℓ j = ℓ i)
    (a : Multiplicative (ZMod m)) :
    ZMod.toCircle ((ℓ j : ZMod m) * a.toAdd) ^ e = ZMod.toCircle ((ℓ i : ZMod m) * a.toAdd) := by
  rw [← AddChar.map_zsmul_eq_zpow, zsmul_eq_mul, ← mul_assoc, he]

private theorem isRotationCompatible_leftCover {e : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0) :
    IsRotationCompatible (ℓ := ℓ) (leftCover e) 1 := by
  intro a x
  have hζ := toCircle_zpow he a
  ext k
  fin_cases k <;>
    simp only [lensRotation_apply, coe_leftCover_apply_zero, coe_leftCover_apply_one,
      Complex.real_smul, Circle.coe_mul, mul_zpow, hζ, Fin.zero_eta, Fin.mk_one] <;> ring

private theorem isRotationCompatible_rightCover {e : ℤ} (he : (e : ZMod m) * ℓ 0 = ℓ 1) :
    IsRotationCompatible (ℓ := ℓ) (rightCover e) 0 := by
  intro a x
  have hζ := toCircle_zpow he a
  ext k
  fin_cases k <;>
    simp only [lensRotation_apply, coe_rightCover_apply_zero, coe_rightCover_apply_one,
      Complex.real_smul, Circle.coe_mul, mul_zpow, hζ, Fin.zero_eta, Fin.mk_one] <;> ring

/-- Points of the two pieces `‖x 0‖ ≤ ‖x 1‖` and `‖x 1‖ ≤ ‖x 0‖` lie on their common boundary
torus. -/
private theorem norm_eq_one_of_descend_eq {e e' : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0)
    (he' : (e' : ZMod m) * ℓ 0 = ℓ 1) {x y : SolidTorus}
    (hxy : descend (isRotationCompatible_leftCover he) x =
      descend (isRotationCompatible_rightCover he') y) :
    ‖(x.1 : ℂ)‖ = 1 := by
  obtain ⟨x, rfl⟩ := powCore_surjective (m := m) x
  obtain ⟨y, rfl⟩ := powCore_surjective (m := m) y
  rw [descend_powCore, descend_powCore, mk_eq_mk_iff] at hxy
  obtain ⟨a, ha⟩ := hxy
  have h0 := congrArg (fun z : EuclideanSpace ℂ (Fin 2) ↦ ‖z 0‖) ha
  have h1 := congrArg (fun z : EuclideanSpace ℂ (Fin 2) ↦ ‖z 1‖) ha
  simp only [norm_lensRotation_apply, coe_leftCover_apply_zero, coe_leftCover_apply_one,
    coe_rightCover_apply_zero, coe_rightCover_apply_one, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_mul, Circle.norm_coe, mul_one] at h0 h1
  have hx : ‖(x.1 : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.1.2
  have hsx : 0 < (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  -- With `c u` the scale of `u`, `c u' = c u ‖u‖` and `c u' ‖u'‖ = c u`, so `‖u‖ ‖u'‖ = 1`.
  have huv : ‖(x.1 : ℂ)‖ * ‖(y.1 : ℂ)‖ = 1 := by
    rw [h0, mul_assoc] at h1
    exact (mul_eq_left₀ hsx.ne').1 h1
  rw [powCore_apply]
  nlinarith [norm_nonneg (x.1 : ℂ), mem_closedBall_zero_iff.1 y.1.2]

end LensSpace

/-! ### `p / q`-surgery on the unknot -/

section Surgery

variable (p : ℕ) [NeZero p] (ℓ : Fin 2 → (ZMod p)ˣ) {q s t : ℤ}

omit [NeZero p] in
/-- The exponent `-t` for the filling solid torus `‖x 0‖ ≤ ‖x 1‖`: since `t q ≡ 1` modulo `p`,
`-t ℓ₁ = t q ℓ₀ = ℓ₀`. -/
private theorem exponent_left (hst : s * p + t * q = 1) (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    ((-t : ℤ) : ZMod p) * ℓ 1 = ℓ 0 := by
  have h := congrArg (Int.cast : ℤ → ZMod p) hst
  push_cast [ZMod.natCast_self] at h
  rw [hℓ]
  push_cast
  linear_combination (ℓ 0 : ZMod p) * h

omit [NeZero p] in
/-- The exponent `-q` for the knot exterior `‖x 1‖ ≤ ‖x 0‖`. -/
private theorem exponent_right (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    ((-q : ℤ) : ZMod p) * ℓ 0 = ℓ 1 := by
  rw [hℓ]
  push_cast
  ring

/-- The exterior of the unknot is carried onto `‖x 1‖ ≤ ‖x 0‖` by the identification
`TauCeti.unknotExteriorHomeomorph` of the exterior with `D² × S¹`. -/
private theorem unknotExteriorHomeomorph_exteriorBoundaryInclusion (r : Circle × Circle) :
    unknotExteriorHomeomorph
        (isSolidTorusNeighborhood_unknotSolidTorus.exteriorBoundaryInclusion r) =
      SolidTorus.boundaryInclusion r.swap := by
  rw [← unknotExteriorHomeomorph.apply_symm_apply (SolidTorus.boundaryInclusion r.swap)]
  refine congrArg _ (Subtype.ext ?_)
  rw [unknotExteriorHomeomorph_symm_boundaryInclusion, Prod.swap_swap,
    IsSolidTorusNeighborhood.coe_exteriorBoundaryInclusion_apply]

/-- **`p / q`-surgery on the unknot is a lens space.** For `s p + t q = 1` and `ℓ₁ = -q ℓ₀` modulo
`p`, the lens space `L(p; ℓ₀, ℓ₁)` is the Dehn filling of the exterior of the unknot along the slope
of value `p / q` in the framing of `TauCeti.unknotSolidTorus`, which is the preferred framing
(`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). The filling solid torus is the
handlebody `‖x 0‖ ≤ ‖x 1‖` of the genus-one Heegaard splitting of the lens space, the exterior is
the handlebody `‖x 1‖ ≤ ‖x 0‖`, and the boundary tori are glued by
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`. For `ℓ = ![1, q]` this exhibits `L(p, q)` as the
`-p / q`-surgery on the unknot. -/
def unknotLensSpaceDehnFilling (hst : s * p + t * q = 1) (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    DehnFilling isSolidTorusNeighborhood_unknotSolidTorus
      (isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.slopeEquiv.symm
        (slopeValue (p, q)))
      (LensSpace p ℓ) where
  exteriorEmbedding :=
    LensSpace.descend (LensSpace.isRotationCompatible_rightCover (exponent_right p ℓ hℓ)) ∘
      unknotExteriorHomeomorph
  isClosedEmbedding_exteriorEmbedding :=
    (LensSpace.isClosedEmbedding_descend _ (LensSpace.rightCover_injective _)).comp
      unknotExteriorHomeomorph.isClosedEmbedding
  solidTorusEmbedding :=
    LensSpace.descend (LensSpace.isRotationCompatible_leftCover (exponent_left p ℓ hst hℓ))
  isClosedEmbedding_solidTorusEmbedding :=
    LensSpace.isClosedEmbedding_descend _ (LensSpace.leftCover_injective _)
  gluing := torusGluing p q s t hst
  exteriorEmbedding_exteriorBoundaryInclusion r := by
    obtain ⟨w, hw⟩ := Circle.exists_pow_nat_eq (NeZero.ne p) r.2
    -- In the coordinates `(u, w)` of the two pieces over `(u, w ^ p)`, the point `(r.1, w)` of
    -- the filling solid torus is the point `(r.1 ^ q r.2 ^ s, r.1 w ^ (-t))` of the exterior.
    have hpow : (r.1 * w ^ (-t)) ^ p = r.1 ^ (p : ℤ) * r.2 ^ (-t) := by
      rw [mul_pow, ← hw, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        mul_comm (-t)]
    have hB : SolidTorus.boundaryInclusion (torusGluing p q s t hst r).swap =
        LensSpace.powCore p
          (SolidTorus.boundaryInclusion (r.1 ^ q * r.2 ^ s, r.1 * w ^ (-t))) := by
      refine Prod.ext (Subtype.ext (by simp [LensSpace.powCore_apply, torusGluing_apply])) ?_
      simp only [LensSpace.powCore_apply, SolidTorus.boundaryInclusion_snd, Prod.snd_swap,
        torusGluing_apply]
      exact hpow.symm
    have hA : SolidTorus.boundaryInclusion r =
        LensSpace.powCore p (SolidTorus.boundaryInclusion (r.1, w)) := by
      refine Prod.ext (Subtype.ext (by simp [LensSpace.powCore_apply])) ?_
      rw [LensSpace.powCore_apply, SolidTorus.boundaryInclusion_snd,
        SolidTorus.boundaryInclusion_snd, hw]
    -- `r.1 ^ q (w ^ p) ^ s (r.1 w ^ (-t)) ^ (-q) = w ^ (s p + t q) = w`.
    have hc : r.1 ^ q * r.2 ^ s * (r.1 * w ^ (-t)) ^ (-q) = w := by
      rw [← hw, ← zpow_natCast, ← zpow_mul, mul_zpow, ← zpow_mul, mul_mul_mul_comm,
        ← zpow_add, add_neg_cancel, zpow_zero, one_mul, ← zpow_add,
        show ((p : ℤ) * s + -t * -q) = 1 by linear_combination hst, zpow_one]
    rw [Function.comp_apply, unknotExteriorHomeomorph_exteriorBoundaryInclusion, hB, hA,
      LensSpace.descend_powCore, LensSpace.descend_powCore]
    refine congrArg _ (Subtype.ext ?_)
    ext k
    fin_cases k
    · simp [LensSpace.coe_rightCover_apply_zero, LensSpace.coe_leftCover_apply_zero]
    · simp only [Fin.mk_one, LensSpace.coe_rightCover_apply_one,
        LensSpace.coe_leftCover_apply_one, SolidTorus.coe_boundaryInclusion_fst,
        SolidTorus.boundaryInclusion_snd, Circle.norm_coe]
      rw [← Circle.coe_mul, hc]
  range_union_range := by
    rw [EquivLike.range_comp, LensSpace.range_descend, LensSpace.range_descend,
      LensSpace.range_rightCover, LensSpace.range_leftCover,
      ← LensSpace.heegaardSplitting_left, ← LensSpace.heegaardSplitting_right, union_comm,
      (LensSpace.heegaardSplitting p ℓ).union_eq_univ]
  range_inter_range_subset := by
    intro y hy
    obtain ⟨⟨x, hx⟩, z, hz⟩ := hy
    have hn := LensSpace.norm_eq_one_of_descend_eq (exponent_left p ℓ hst hℓ)
      (exponent_right p ℓ hℓ) (hz.trans hx.symm)
    refine ⟨(⟨z.1, mem_sphere_zero_iff_norm.2 hn⟩, z.2), ?_⟩
    rw [← hz, Function.comp_apply]
    exact congrArg _ (Prod.ext (Subtype.ext (SolidTorus.coe_boundaryInclusion_fst _))
      (SolidTorus.boundaryInclusion_snd _))
  fillingSlope_gluing := by
    have hpq : IsCoprime (p : ℤ) q := ⟨s, t, hst⟩
    rw [Equiv.eq_symm_apply, FramedBoundaryTorus.slopeEquiv_apply,
      IsSolidTorusNeighborhood.fillingSlope_eq_of_apply_torusCurve _ hpq
        (torusGluing_torusCurve p q s t hst),
      FramedBoundaryTorus.value_mk_torusCurveClass _ hpq]

variable {p ℓ}

/-- The `p / q`-surgery on the unknot glues the boundary tori by
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`. -/
@[simp]
theorem unknotLensSpaceDehnFilling_gluing_apply (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) (x : Circle × Circle) :
    (unknotLensSpaceDehnFilling p ℓ hst hℓ).gluing x =
      (x.1 ^ (p : ℤ) * x.2 ^ (-t), x.1 ^ q * x.2 ^ s) :=
  (rfl)

/-- The filling solid torus of the `p / q`-surgery on the unknot is the handlebody
`‖x 0‖ ≤ ‖x 1‖` of the genus-one Heegaard splitting of the lens space. -/
@[simp]
theorem range_unknotLensSpaceDehnFilling_solidTorusEmbedding (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    range (unknotLensSpaceDehnFilling p ℓ hst hℓ).solidTorusEmbedding =
      (LensSpace.heegaardSplitting p ℓ).left := by
  rw [LensSpace.heegaardSplitting_left, ← LensSpace.range_leftCover]
  exact LensSpace.range_descend _

/-- The exterior of the unknot in the `p / q`-surgery is the handlebody `‖x 1‖ ≤ ‖x 0‖` of the
genus-one Heegaard splitting of the lens space. -/
@[simp]
theorem range_unknotLensSpaceDehnFilling_exteriorEmbedding (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    range (unknotLensSpaceDehnFilling p ℓ hst hℓ).exteriorEmbedding =
      (LensSpace.heegaardSplitting p ℓ).right := by
  rw [LensSpace.heegaardSplitting_right, ← LensSpace.range_rightCover]
  exact (EquivLike.range_comp _ unknotExteriorHomeomorph).trans (LensSpace.range_descend _)

end Surgery

end TauCeti
