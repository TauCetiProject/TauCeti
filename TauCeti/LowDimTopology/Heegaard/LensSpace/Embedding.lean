/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.Analysis.Normed.Lp.ProdLp.Sphere
public import TauCeti.Geometry.Manifold.Instances.LensSpace
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Character
public import TauCeti.LowDimTopology.SeifertFibration
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Solid-torus parametrizations of lens-space handlebodies

The two pieces `‖x 0‖ ≤ ‖x 1‖` and `‖x 1‖ ≤ ‖x 0‖` in a three-dimensional lens space are
parametrized by `LensSpace.leftEmbedding` and `LensSpace.rightEmbedding`. For an integer twist
`e` satisfying `e ℓⱼ = ℓᵢ` modulo `m`, the cover sends `(u, w)` to the unit vector proportional
to `(u w ^ e, w)` in the corresponding coordinate order. Lens rotations act through the core
coordinate, so this descends along `(u, w) ↦ (u, w ^ m)` to a closed embedding of `D² × S¹`.

The range lemmas identify the two handlebodies; `leftEmbedding_apply` and `rightEmbedding_apply`
compute their values on the power-map cover. Their intersection lies on the boundary tori.
These parametrizations serve both the genus-one Heegaard splitting and surgery on the unknot.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 9B (lens spaces as unions
  of two solid tori).
-/

public section

noncomputable section

open Metric Set Topology Function

namespace TauCeti

namespace LensSpace

variable {m : ℕ} [NeZero m] {ℓ : Fin 2 → (ZMod m)ˣ}

/-- The map `(u, w) ↦ (u, w ^ m)` of the solid torus. -/
private def powCore (m : ℕ) : C(SolidTorus, SolidTorus) :=
  ⟨fun x ↦ (x.1, x.2 ^ m), by fun_prop⟩

private theorem powCore_apply (m : ℕ) (x : SolidTorus) : powCore m x = (x.1, x.2 ^ m) :=
  (rfl)

private theorem powCore_surjective : Surjective (powCore m) := by
  rintro ⟨u, v⟩
  obtain ⟨w, rfl⟩ := (Circle.isQuotientCoveringMap_npow m).surjective v
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
  simp only [powCore_apply, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  obtain ⟨b, hb⟩ := ZMod.exists_toCircle_eq_of_pow_eq_one (n := m) (ζ := y.2 * x.2⁻¹)
    (by rw [mul_pow, inv_pow, h2, mul_inv_cancel])
  refine ((mk_eq_mk_iff m ℓ _ _).2 ⟨Multiplicative.ofAdd (((ℓ j)⁻¹ : (ZMod m)ˣ) * b), ?_⟩).symm
  rw [hψ, toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, hb,
    inv_mul_cancel_right]
  exact congrArg (fun x ↦ (ψ x : EuclideanSpace ℂ (Fin 2)))
    (Prod.ext h1 rfl)

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
    AddChar.zmod_pow_eq_one, one_mul]

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
def leftCover (e : ℤ) : C(SolidTorus, sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  ⟨fun x ↦ (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv
      ((sphereProdFstLeHomeomorph ℂ ℂ).symm (twist e x)), by fun_prop⟩

/-- The solid torus `‖x 1‖ ≤ ‖x 0‖` of the unit sphere of `ℂ²`, parametrized so that `(u, w)` goes
to the unit vector proportional to `(w, u w ^ e)`. -/
def rightCover (e : ℤ) : C(SolidTorus, sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  ⟨fun x ↦ (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv
      ((sphereProdSndLeHomeomorph ℂ ℂ).symm (twist e x).swap), by fun_prop⟩

theorem leftCover_injective (e : ℤ) : Injective (leftCover e) :=
  (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv.injective.comp
    (Subtype.val_injective.comp ((sphereProdFstLeHomeomorph ℂ ℂ).symm.injective.comp
      (twist e).injective))

theorem rightCover_injective (e : ℤ) : Injective (rightCover e) :=
  (EuclideanSpace.finTwoEquivProd ℂ).symm.unitSphereIsometryEquiv.injective.comp
    (Subtype.val_injective.comp ((sphereProdSndLeHomeomorph ℂ ℂ).symm.injective.comp
      (Prod.swap_injective.comp (twist e).injective)))

/-- The disc coordinate of the left cover. -/
@[simp]
theorem coe_leftCover_apply_zero (e : ℤ) (x : SolidTorus) :
    (leftCover e x : EuclideanSpace ℂ (Fin 2)) 0 =
      (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • ((x.1 : ℂ) * (x.2 ^ e : Circle)) := by
  simp [leftCover, twist]

/-- The core coordinate of the left cover. -/
@[simp]
theorem coe_leftCover_apply_one (e : ℤ) (x : SolidTorus) :
    (leftCover e x : EuclideanSpace ℂ (Fin 2)) 1 = (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • (x.2 : ℂ) := by
  simp [leftCover, twist]

/-- The core coordinate of the right cover. -/
@[simp]
theorem coe_rightCover_apply_zero (e : ℤ) (x : SolidTorus) :
    (rightCover e x : EuclideanSpace ℂ (Fin 2)) 0 = (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • (x.2 : ℂ) := by
  simp [rightCover, twist]

/-- The disc coordinate of the right cover. -/
@[simp]
theorem coe_rightCover_apply_one (e : ℤ) (x : SolidTorus) :
    (rightCover e x : EuclideanSpace ℂ (Fin 2)) 1 =
      (√(1 + ‖(x.1 : ℂ)‖ ^ 2))⁻¹ • ((x.1 : ℂ) * (x.2 ^ e : Circle)) := by
  simp [rightCover, twist]

/-- The left cover has image the solid torus `‖x 0‖ ≤ ‖x 1‖` in the unit sphere of `ℂ²`. -/
@[simp]
theorem range_leftCover (e : ℤ) :
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

/-- The right cover has image the solid torus `‖x 1‖ ≤ ‖x 0‖` in the unit sphere of `ℂ²`. -/
@[simp]
theorem range_rightCover (e : ℤ) :
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

/-- The closed solid-torus parametrization of the left lens-space handlebody, with twist `e`.
The relation `e ℓ₁ = ℓ₀` makes its cover invariant under the lens rotations. -/
def leftEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0) :
    C(SolidTorus, LensSpace m ℓ) :=
  descend (isRotationCompatible_leftCover he)

/-- The closed solid-torus parametrization of the right lens-space handlebody, with twist `e`.
The relation `e ℓ₀ = ℓ₁` makes its cover invariant under the lens rotations. -/
def rightEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 0 = ℓ 1) :
    C(SolidTorus, LensSpace m ℓ) :=
  descend (isRotationCompatible_rightCover he)

/-- The left parametrization evaluated on the power-map cover of the solid torus. -/
@[simp]
theorem leftEmbedding_apply {e : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0)
    (u : closedBall (0 : ℂ) 1) (w : Circle) :
    leftEmbedding he (u, w ^ m) = mk m ℓ (leftCover e (u, w)) :=
  descend_powCore _ (u, w)

/-- The right parametrization evaluated on the power-map cover of the solid torus. -/
@[simp]
theorem rightEmbedding_apply {e : ℤ} (he : (e : ZMod m) * ℓ 0 = ℓ 1)
    (u : closedBall (0 : ℂ) 1) (w : Circle) :
    rightEmbedding he (u, w ^ m) = mk m ℓ (rightCover e (u, w)) :=
  descend_powCore _ (u, w)

/-- The left solid-torus parametrization is a closed embedding. -/
theorem isClosedEmbedding_leftEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0) :
    IsClosedEmbedding (leftEmbedding he) :=
  isClosedEmbedding_descend _ (leftCover_injective _)

/-- The right solid-torus parametrization is a closed embedding. -/
theorem isClosedEmbedding_rightEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 0 = ℓ 1) :
    IsClosedEmbedding (rightEmbedding he) :=
  isClosedEmbedding_descend _ (rightCover_injective _)

/-- The left solid-torus parametrization covers the image of `‖x 0‖ ≤ ‖x 1‖`. -/
@[simp]
theorem range_leftEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0) :
    range (leftEmbedding he) = mk m ℓ '' {x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 |
      ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖} := by
  rw [leftEmbedding, range_descend, range_leftCover]

/-- The right solid-torus parametrization covers the image of `‖x 1‖ ≤ ‖x 0‖`. -/
@[simp]
theorem range_rightEmbedding {e : ℤ} (he : (e : ZMod m) * ℓ 0 = ℓ 1) :
    range (rightEmbedding he) = mk m ℓ '' {x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 |
      ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖} := by
  rw [rightEmbedding, range_descend, range_rightCover]

/-- Points of the two pieces `‖x 0‖ ≤ ‖x 1‖` and `‖x 1‖ ≤ ‖x 0‖` lie on their common boundary
torus. -/
theorem norm_eq_one_of_leftEmbedding_eq_rightEmbedding {e e' : ℤ} (he : (e : ZMod m) * ℓ 1 = ℓ 0)
    (he' : (e' : ZMod m) * ℓ 0 = ℓ 1) {x y : SolidTorus}
    (hxy : leftEmbedding he x = rightEmbedding he' y) :
    ‖(x.1 : ℂ)‖ = 1 := by
  obtain ⟨x, rfl⟩ := powCore_surjective (m := m) x
  obtain ⟨y, rfl⟩ := powCore_surjective (m := m) y
  rw [leftEmbedding, rightEmbedding, descend_powCore, descend_powCore, mk_eq_mk_iff] at hxy
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

end TauCeti
