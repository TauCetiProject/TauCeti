/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Mirror
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Torus knots

For coprime integers `p` and `q`, the **`(p, q)` torus knot** is the curve
`z ↦ (zᵖ, z^q) / √2` in the unit sphere `S³` of `ℂ² = ℝ⁴`: as `z` runs once around the circle,
the first coordinate winds `p` times around the origin and the second `q` times. It lies on the
Clifford torus `|z| = |w| = 1 / √2`, along which the two solid tori `|z| ≤ |w|` and `|w| ≤ |z|` of
the genus-one Heegaard splitting of `S³` meet. The `(2, 3)` torus knot is the right-handed trefoil.

Torus knots are the first explicit family of knots in `S³` beyond the unknot, and this file gives
them as smooth circle presentations (`TauCeti.SmoothCircleEmbedding`), in the same ambient sphere
`S³ ⊆ ℝ⁴` as the unknot (`TauCeti.unknot`) and with the coordinates `(z, w) ↦ (Re z, Im z, Re w,
Im w)` of `TauCeti.complexProdToEuclideanFour`. The curve is smooth since the integer powers of the
circle are. It is injective since `zᵖ = wᵖ` and `z^q = w^q` force `z = w` when `p` and `q` are
coprime. It is an immersion since the lift `t ↦ (exp (p t i), exp (q t i)) / √2` of the curve to
`ℝ` has derivative `(p i exp (p t i), q i exp (q t i)) / √2`, which is nonzero because `p` and `q`
are not both zero. The circle being compact, an injective immersion of it is an embedding.

The three symmetries of the family are ambient isometries or reparametrizations, recorded here
exactly:

* reversing the orientation of the `(p, q)` torus knot gives the `(-p, -q)` torus knot;
* its mirror image (`TauCeti.SmoothCircleEmbedding.mirror`, which conjugates the second complex
  coordinate) is the `(p, -q)` torus knot;
* exchanging the two complex coordinates of `ℂ²`, an isometry of `S³` which permutes the real
  coordinates of `ℝ⁴` evenly and so preserves orientation, carries it to the `(q, p)` torus knot.

That a torus knot with `|p| ≤ 1` or `|q| ≤ 1` is unknotted, and that the others are knotted, is not
formalized here.

## Main definitions

* `TauCeti.torusKnot p q h`: the `(p, q)` torus knot in `S³`, for coprime integers `p` and `q`.
* `TauCeti.rightHandedTrefoil`: the right-handed trefoil, the `(2, 3)` torus knot.

## Main results

* `TauCeti.coe_torusKnot_apply`: the torus knot sends `z` to `(zᵖ, z^q) / √2`.
* `TauCeti.norm_fst_complexProdToEuclideanFour_symm_torusKnot`,
  `TauCeti.norm_snd_complexProdToEuclideanFour_symm_torusKnot`: it lies on the Clifford torus.
* `TauCeti.reverse_torusKnot`, `TauCeti.mirror_torusKnot`,
  `TauCeti.transDiffeomorph_torusKnot_withLpProdComm`: reversal, mirror image and the exchange of
  the complex coordinates act on the torus knots by `(p, q) ↦ (-p, -q)`, `(p, -q)` and `(q, p)`.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 3, Section C (torus knots).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (torus knots, the mirror image and the reverse of a knot).
-/

public section

noncomputable section

open Metric Function Set
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact finrank_real_complex_fact'

/-! ### The curve in `ℝ⁴` -/

/-- The real-linear map `(a, b) ↦ (Re a, Im a, Re b, Im b) / √2` from `ℂ × ℂ` to `ℝ⁴`, which
carries the product `S¹ × S¹` of unit circles onto the Clifford torus of the unit sphere. -/
private def cliffordScale : ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((√2)⁻¹ : ℝ) • ((complexProdToEuclideanFour.toContinuousLinearEquiv :
      WithLp 2 (ℂ × ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap)

private theorem cliffordScale_apply (x : ℂ × ℂ) :
    cliffordScale x = ((√2)⁻¹ : ℝ) • complexProdToEuclideanFour (WithLp.toLp 2 x) :=
  (rfl)

private theorem cliffordScale_injective : Injective cliffordScale := by
  intro x y hxy
  rw [cliffordScale_apply, cliffordScale_apply] at hxy
  exact WithLp.toLp_injective 2 <| complexProdToEuclideanFour.injective <|
    smul_right_injective _ (inv_ne_zero (Real.sqrt_ne_zero'.2 two_pos)) hxy

/-- The `(p, q)` torus curve `z ↦ (zᵖ, z^q) / √2` of the circle, read in `ℝ⁴`. -/
private def torusKnotMap (p q : ℤ) (z : Circle) : EuclideanSpace ℝ (Fin 4) :=
  cliffordScale (((z ^ p : Circle) : ℂ), ((z ^ q : Circle) : ℂ))

private theorem norm_torusKnotMap (p q : ℤ) (z : Circle) : ‖torusKnotMap p q z‖ = 1 := by
  have h2 : ‖WithLp.toLp 2 (((z ^ p : Circle) : ℂ), ((z ^ q : Circle) : ℂ))‖ = √2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
    norm_num
  simp [torusKnotMap, cliffordScale_apply, norm_smul, h2, -complexProdToEuclideanFour_apply,
    -Circle.coe_zpow, abs_of_nonneg]

private theorem contMDiff_torusKnotMap (p q : ℤ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ (torusKnotMap p q) := by
  have hpow (k : ℤ) : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ fun z : Circle ↦ ((z ^ k : Circle) : ℂ) :=
    contMDiff_coe_sphere.comp (contMDiff_zpow k)
  exact cliffordScale.contDiff.contMDiff.comp ((hpow p).prodMk_space (hpow q))

/-- Coprime exponents separate the points of the circle: `zᵖ = wᵖ` and `z^q = w^q` force
`z = w`. -/
private theorem torusKnotMap_injective {p q : ℤ} (h : IsCoprime p q) :
    Injective (torusKnotMap p q) := by
  intro z w hzw
  obtain ⟨hp, hq⟩ := Prod.mk.inj (cliffordScale_injective hzw)
  have hgcd : (z / w) ^ (p.gcd q) = 1 :=
    pow_intGCD_eq_one.2 ⟨by rw [div_zpow, Circle.coe_inj.1 hp, div_self'],
      by rw [div_zpow, Circle.coe_inj.1 hq, div_self']⟩
  rwa [Int.isCoprime_iff_gcd_eq_one.1 h, pow_one, div_eq_one] at hgcd

/-- The lift `t ↦ (exp (p t i), exp (q t i)) / √2` of the torus curve along `Circle.exp` has the
derivative `(p i exp (p t i), q i exp (q t i)) / √2`. -/
private theorem hasDerivAt_torusKnotMap_comp_circleExp (p q : ℤ) (t : ℝ) :
    HasDerivAt (torusKnotMap p q ∘ Circle.exp)
      (cliffordScale (Complex.exp (p * (t * Complex.I)) * (p * Complex.I),
        Complex.exp (q * (t * Complex.I)) * (q * Complex.I))) t := by
  have hexp (k : ℤ) : HasDerivAt (fun s : ℝ ↦ Complex.exp (k * (s * Complex.I)))
      (Complex.exp (k * (t * Complex.I)) * (k * Complex.I)) t := by
    simpa using
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_mul (k : ℂ)).cexp
  have hfun : torusKnotMap p q ∘ Circle.exp = fun s : ℝ ↦
      cliffordScale (Complex.exp (p * (s * Complex.I)), Complex.exp (q * (s * Complex.I))) := by
    ext1 s
    simp only [comp_apply, torusKnotMap, Circle.coe_zpow, Circle.coe_exp, Complex.exp_int_mul]
  rw [hfun]
  exact cliffordScale.hasFDerivAt.comp_hasDerivAt t ((hexp p).prodMk (hexp q))

/-- The torus curve has nonzero speed: its lift along `Circle.exp` has nonzero derivative, since
`p` and `q` are not both zero. -/
private theorem deriv_torusKnotMap_comp_circleExp_ne_zero {p q : ℤ} (h : IsCoprime p q)
    (t : ℝ) : deriv (torusKnotMap p q ∘ Circle.exp) t ≠ 0 := by
  rw [(hasDerivAt_torusKnotMap_comp_circleExp p q t).deriv, ← map_zero cliffordScale,
    cliffordScale_injective.ne_iff, Ne, Prod.mk_eq_zero]
  rintro ⟨hp, hq⟩
  refine not_isCoprime_zero_zero (?_ : IsCoprime (0 : ℤ) 0)
  simp only [mul_eq_zero, Complex.exp_ne_zero, Int.cast_eq_zero, Complex.I_ne_zero, false_or,
    or_false] at hp hq
  rwa [hp, hq] at h

/-- The torus curve, as a map into the unit sphere of `ℝ⁴`. -/
private def torusKnotSphereMap (p q : ℤ) (z : Circle) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨torusKnotMap p q z, mem_sphere_zero_iff_norm.2 (norm_torusKnotMap p q z)⟩

private theorem isSmoothEmbedding_torusKnotSphereMap {p q : ℤ} (h : IsCoprime p q) :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ (torusKnotSphereMap p q) := by
  have hsmooth : ContMDiff (𝓡 1) (𝓡 3) ∞ (torusKnotSphereMap p q) :=
    (contMDiff_torusKnotMap p q).codRestrict_sphere _
  have hinj : Injective (torusKnotSphereMap p q) := fun z w hzw ↦
    torusKnotMap_injective h (congrArg Subtype.val hzw)
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun z ↦ ?_,
    (hsmooth.continuous.isClosedEmbedding hinj).isEmbedding⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  refine (hsmooth.contMDiffOn (s := univ).isImmersionAt_iff_injective_mfderiv isOpen_univ
    (mem_univ _) (by simp)).2 ?_
  -- The derivative of the curve in `ℝ⁴` is that of the curve in the sphere followed by the
  -- injective derivative of the inclusion, so injectivity of the former suffices.
  have hcomp := mfderiv_comp (Circle.exp t)
    ((contMDiff_coe_sphere (m := 1) (n := 3) (E := EuclideanSpace ℝ (Fin 4))).mdifferentiableAt
      one_ne_zero)
    (hsmooth.mdifferentiableAt (by simp))
  have hcurve := injective_mfderiv_of_deriv_comp_circleExp_ne_zero
    ((contMDiff_torusKnotMap p q).mdifferentiableAt (by simp))
    (deriv_torusKnotMap_comp_circleExp_ne_zero h t)
  have hfun : torusKnotMap p q = Subtype.val ∘ torusKnotSphereMap p q := (rfl)
  rw [hfun, hcomp, ContinuousLinearMap.coe_comp] at hcurve
  exact hcurve.of_comp

/-! ### Torus knots -/

/-- The **`(p, q)` torus knot** in `S³`, for coprime integers `p` and `q`: the smooth embedding
`z ↦ (zᵖ, z^q) / √2` of the circle into the unit sphere of `ℂ² = ℝ⁴`, which lies on the Clifford
torus `|z| = |w| = 1 / √2`. -/
def torusKnot (p q : ℤ) (h : IsCoprime p q) :
    SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  SmoothEmbedding.ofIsSmoothEmbedding (torusKnotSphereMap p q)
    (isSmoothEmbedding_torusKnotSphereMap h)

variable {p q : ℤ} (h : IsCoprime p q)

/-- The `(p, q)` torus knot sends a point `z` of the circle to `(zᵖ, z^q) / √2`, in the real
coordinates `(Re z, Im z, Re w, Im w)` of `ℝ⁴`. -/
@[simp]
theorem coe_torusKnot_apply (z : Circle) :
    (torusKnot p q h z : EuclideanSpace ℝ (Fin 4)) =
      ((√2)⁻¹ : ℝ) • complexProdToEuclideanFour (WithLp.toLp 2 ((z : ℂ) ^ p, (z : ℂ) ^ q)) := by
  rw [torusKnot, SmoothEmbedding.ofIsSmoothEmbedding_apply]
  simp only [torusKnotSphereMap, torusKnotMap, cliffordScale_apply, Circle.coe_zpow]

/-- In the complex coordinates of `ℂ²`, the `(p, q)` torus knot sends `z` to `(zᵖ, z^q) / √2`. -/
theorem complexProdToEuclideanFour_symm_torusKnot (z : Circle) :
    complexProdToEuclideanFour.symm (torusKnot p q h z) =
      ((√2)⁻¹ : ℝ) • WithLp.toLp 2 ((z : ℂ) ^ p, (z : ℂ) ^ q) := by
  rw [coe_torusKnot_apply, map_smul, LinearIsometryEquiv.symm_apply_apply]

/-- The first complex coordinate of a point of a torus knot has absolute value `1 / √2`. -/
theorem norm_fst_complexProdToEuclideanFour_symm_torusKnot (z : Circle) :
    ‖(complexProdToEuclideanFour.symm (torusKnot p q h z)).fst‖ = (√2)⁻¹ := by
  simp

/-- The second complex coordinate of a point of a torus knot has absolute value `1 / √2`. Together
with `TauCeti.norm_fst_complexProdToEuclideanFour_symm_torusKnot`, this says that a torus knot lies
on the Clifford torus. -/
theorem norm_snd_complexProdToEuclideanFour_symm_torusKnot (z : Circle) :
    ‖(complexProdToEuclideanFour.symm (torusKnot p q h z)).snd‖ = (√2)⁻¹ := by
  simp

/-- Reversing the orientation of the `(p, q)` torus knot gives the `(-p, -q)` torus knot. -/
@[simp]
theorem reverse_torusKnot : (torusKnot p q h).reverse = torusKnot (-p) (-q) h.neg_neg :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by
    simp only [SmoothCircleEmbedding.reverse_apply, coe_torusKnot_apply, Circle.coe_inv,
      inv_zpow']

/-- The mirror image of the `(p, q)` torus knot is the `(p, -q)` torus knot: the reflection
defining the mirror image conjugates the second complex coordinate, and `conj (z^q) = z^(-q)` on
the circle. -/
@[simp]
theorem mirror_torusKnot : (torusKnot p q h).mirror = torusKnot p (-q) h.neg_right :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by
    simpa [map_smul, map_zpow₀, ← Circle.coe_inv_eq_conj] using
      congrArg (fun v ↦ ((√2)⁻¹ : ℝ) • v)
        (mirror_reflection_complexProdToEuclideanFour ((z : ℂ) ^ p) ((z : ℂ) ^ q))

/-- Exchanging the two complex coordinates of `ℂ² = ℝ⁴`, an isometry of `S³`, carries the
`(p, q)` torus knot to the `(q, p)` torus knot. -/
theorem transDiffeomorph_torusKnot_withLpProdComm :
    SmoothEmbedding.transDiffeomorph (torusKnot p q h)
        ((complexProdToEuclideanFour.symm.trans
          ((LinearIsometryEquiv.withLpProdComm 2 ℝ ℂ ℂ).trans
            complexProdToEuclideanFour)).unitSphereDiffeomorph ∞) =
      torusKnot q p h.symm :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by
    simp [map_smul]

/-! ### The right-handed trefoil -/

/-- The **right-handed trefoil**: the `(2, 3)` torus knot `z ↦ (z², z³) / √2` in `S³` with its
standard orientation from `ℂ²`. Its mirror image is the left-handed `(2, -3)` torus knot
(`TauCeti.mirror_torusKnot`). -/
def rightHandedTrefoil : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  torusKnot 2 3 (Int.isCoprime_iff_gcd_eq_one.2 rfl)

/-- The right-handed trefoil is the `(2, 3)` torus knot. -/
theorem rightHandedTrefoil_eq_torusKnot :
    rightHandedTrefoil = torusKnot 2 3 (Int.isCoprime_iff_gcd_eq_one.2 rfl) :=
  (rfl)

end TauCeti
