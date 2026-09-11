/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# The hyperbolic plane

The hyperbolic plane over a commutative ring in which two is invertible is the diagonal quadratic
form `⟨1, -1⟩`. It is nondegenerate, represents every scalar, and is isometric to the `xy`-form
`QuadraticForm.dualProd`. Over a field in which two is invertible (that is, of characteristic not
two), every plane `⟨a, -a⟩` with `a ≠ 0` is isometric to it.

The main result is the hyperbolic splitting theorem: over a field of characteristic not two, every
finite-dimensional nondegenerate isotropic quadratic form splits as the orthogonal sum of a
hyperbolic plane and another nondegenerate form. It is the inductive step of Witt decomposition:
iterating it splits off hyperbolic planes until the remaining part is anisotropic. The companion
statement that such a form is universal is
`QuadraticMap.represents_of_nondegenerate_of_not_anisotropic`, which needs no finiteness
hypothesis and is proved directly in `TauCeti/LinearAlgebra/QuadraticForm/Representation.lean`.

## Main definitions

* `TauCeti.hyperbolicPlane`: the diagonal form `⟨1, -1⟩`, over a commutative ring in which two is
  invertible.

## Main results

* `TauCeti.represents_hyperbolicPlane`: the hyperbolic plane represents every scalar.
* `TauCeti.equivalent_hyperbolicPlane_dualProd`: the hyperbolic plane is isometric to the
  `xy`-form `QuadraticForm.dualProd`.
* `TauCeti.equivalent_weightedSumSquares_self_neg`: in characteristic not two, every
  `⟨a, -a⟩`, for `a ≠ 0`, is hyperbolic.
* `TauCeti.exists_hyperbolicPlane_prod_equivalent`: in characteristic not two, every
  finite-dimensional nondegenerate isotropic form splits off a hyperbolic plane.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §3.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

section CommRing

variable {R : Type u} [CommRing R]

/-- The hyperbolic plane `⟨1, -1⟩` over a commutative ring in which two is invertible.

The invertibility hypothesis is not used by the formula; it confines the definition to the
setting where the diagonal form `⟨1, -1⟩` is the hyperbolic plane. In characteristic two it is
`⟨1, 1⟩`, whose polar form vanishes identically. -/
def hyperbolicPlane (R : Type u) [CommRing R] [_i2 : Invertible (2 : R)] :
    QuadraticForm R (Fin 2 → R) :=
  weightedSumSquares R ![(1 : R), -1]

/-- Evaluation of the hyperbolic plane in its diagonal coordinates. -/
@[simp]
theorem hyperbolicPlane_apply [Invertible (2 : R)] (x : Fin 2 → R) :
    hyperbolicPlane R x = x 0 ^ 2 - x 1 ^ 2 := by
  simp [hyperbolicPlane, weightedSumSquares_apply, Fin.sum_univ_two, pow_two]
  ring

/-- The hyperbolic plane is nondegenerate when two is invertible. -/
theorem nondegenerate_hyperbolicPlane [Invertible (2 : R)] :
    (hyperbolicPlane R).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [QuadraticMap.mem_radical_iff'] at hx
  have hxQ := hx.1
  rw [hyperbolicPlane_apply] at hxQ
  have h0 : x 0 = 0 := by
    have h := hx.2 ![1, 0]
    simp only [hyperbolicPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply] at h
    apply (isUnit_of_invertible (2 : R)).mul_right_eq_zero.mp
    linear_combination h - hxQ
  have h1 : x 1 = 0 := by
    have h := hx.2 ![0, 1]
    simp only [hyperbolicPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply] at h
    apply (isUnit_of_invertible (2 : R)).mul_right_eq_zero.mp
    linear_combination hxQ - h
  ext i
  fin_cases i <;> simp [h0, h1]

/-- When two is invertible, the hyperbolic plane represents every scalar. -/
theorem represents_hyperbolicPlane [Invertible (2 : R)] (a : R) :
    (hyperbolicPlane R).Represents a := by
  rw [represents_iff, Set.mem_range]
  refine ⟨![(a + 1) * ⅟(2 : R), (a - 1) * ⅟(2 : R)], ?_⟩
  rw [hyperbolicPlane_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    ((a + 1) * ⅟(2 : R)) ^ 2 - ((a - 1) * ⅟(2 : R)) ^ 2 =
        a * ((2 : R) * ⅟(2 : R)) ^ 2 := by ring
    _ = a := by rw [mul_invOf_self, one_pow, mul_one]

/-- When two is invertible, the hyperbolic plane is isometric to the `xy`-form
`QuadraticForm.dualProd R R`, whose value at `(f, z)` is `f z`. -/
theorem equivalent_hyperbolicPlane_dualProd [Invertible (2 : R)] :
    (hyperbolicPlane R).Equivalent (QuadraticForm.dualProd R R) := by
  -- The isometry is Mathlib's `QuadraticForm.toDualProd` for the square form `QuadraticMap.sq`,
  -- which is bijective in this rank-one case.
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  have hdual (f : Module.Dual R R) (y : R) : f y = y * f 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  -- `toDualProd` sends `(a, b)` to the dual vector `(a + b) * ·` paired with `a - b`.
  have happ (p : R × R) :
      QuadraticForm.toDualProd (QuadraticMap.sq : QuadraticForm R R) p =
        (LinearMap.mul R R (p.1 + p.2), p.1 - p.2) := by
    refine Prod.ext (LinearMap.ext fun y ↦ ?_) rfl
    simp only [QuadraticForm.toDualProd_apply, associated_sq, map_add, LinearMap.add_apply,
      LinearMap.mul_apply_apply]
  have hbij : Function.Bijective
      (QuadraticForm.toDualProd (QuadraticMap.sq : QuadraticForm R R)) := by
    refine ⟨fun p q hpq ↦ ?_, fun q ↦ ?_⟩
    · rw [happ, happ, Prod.mk.injEq] at hpq
      have hadd : p.1 + p.2 = q.1 + q.2 := by
        have h := congrArg (fun f : Module.Dual R R ↦ f 1) hpq.1
        simpa using h
      refine Prod.ext ?_ ?_
      · linear_combination ⅟(2 : R) * hadd + ⅟(2 : R) * hpq.2 - (p.1 - q.1) * h2
      · linear_combination ⅟(2 : R) * hadd - ⅟(2 : R) * hpq.2 - (p.2 - q.2) * h2
    · refine ⟨((q.1 1 + q.2) * ⅟(2 : R), (q.1 1 - q.2) * ⅟(2 : R)), ?_⟩
      rw [happ]
      refine Prod.ext (LinearMap.ext fun y ↦ ?_) (by linear_combination q.2 * h2)
      rw [LinearMap.mul_apply_apply, hdual q.1 y]
      linear_combination (y * q.1 1) * h2
  have hprod : (hyperbolicPlane R).Equivalent
      ((QuadraticMap.sq : QuadraticForm R R).prod (-QuadraticMap.sq)) :=
    ⟨{ toLinearEquiv := LinearEquiv.finTwoArrow R R
       map_app' x := by
         simp [hyperbolicPlane_apply, pow_two, sub_eq_add_neg] }⟩
  exact hprod.trans
    ⟨{ toLinearEquiv := LinearEquiv.ofBijective _ hbij
       map_app' p := (QuadraticForm.toDualProd (QuadraticMap.sq : QuadraticForm R R)).map_app p }⟩

end CommRing

variable {K : Type u} [Field K]

/-- Over a field in which two is invertible, every diagonal plane `⟨a, -a⟩` with `a` a unit is
isometric to the hyperbolic plane. -/
theorem equivalent_weightedSumSquares_self_neg [Invertible (2 : K)] (a : Kˣ) :
    (weightedSumSquares K ![(a : K), -(a : K)]).Equivalent (hyperbolicPlane K) := by
  have hdisc : IsSquare (a * (-a) * ((1 : Kˣ) * (-1))) := by
    refine ⟨a, ?_⟩
    simp
  have hsource : a ∈ unitValueSet
      (weightedSumSquares K ![(a : K), -(a : K)]) :=
    mem_unitValueSet_binary_left a (-(a : K))
  have htarget : a ∈ unitValueSet (hyperbolicPlane K) := by
    rw [mem_unitValueSet]
    exact represents_hyperbolicPlane (a : K)
  exact equivalent_binary_of_isSquare_of_mem_unitValueSet
    (a := a) (b := -a) (c := 1) (d := -1) (e := a) hdisc hsource htarget

variable {V : Type v} [AddCommGroup V] [Module K V]

private def hyperbolicPairMap (x y : V) : K × K →ₗ[K] V where
  toFun p := (p.1 + p.2) • x + (p.1 - p.2) • y
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    module

private theorem hyperbolicPairMap_injective [Invertible (2 : K)]
    (Q : QuadraticForm K V) {x y : V} (hxQ : Q x = 0) (hyQ : Q y = 0)
    (hxy : polar Q x y = 1) : Function.Injective (hyperbolicPairMap (K := K) x y) := by
  intro p q hpq
  have hpqzero : hyperbolicPairMap (K := K) x y (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hsub : (p - q).1 - (p - q).2 = 0 := by
    have := congrArg (polar Q x) hpqzero
    simpa [hyperbolicPairMap, polar_add_right, polar_smul_right, polar_self, hxQ, hxy] using this
  have hadd : (p - q).1 + (p - q).2 = 0 := by
    have := congrArg (fun z ↦ polar Q z y) hpqzero
    simpa [hyperbolicPairMap, polar_add_left, polar_smul_left, polar_self, hyQ, hxy,
      polar_comm] using this
  have hpq' : p - q = 0 := by
    apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero]
    · apply (mul_left_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero)
      linear_combination hadd + hsub
    · apply (mul_left_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero)
      linear_combination hadd - hsub
  exact sub_eq_zero.mp hpq'

private noncomputable def hyperbolicPairIsometryEquiv [Invertible (2 : K)]
    (Q : QuadraticForm K V) (x y : V) (hxQ : Q x = 0) (hyQ : Q y = 0)
    (hxy : polar Q x y = 1) :
    (hyperbolicPlane K).IsometryEquiv
      (Q.restrict (LinearMap.range (hyperbolicPairMap (K := K) x y))) where
  toLinearEquiv := (LinearEquiv.finTwoArrow K K).trans
    (LinearEquiv.ofInjective (hyperbolicPairMap (K := K) x y)
      (hyperbolicPairMap_injective Q hxQ hyQ hxy))
  map_app' v := by
    -- Expose the range equivalence so the quadratic-form calculation sees its underlying map.
    change Q ((v 0 + v 1) • x + (v 0 - v 1) • y) = hyperbolicPlane K v
    rw [QuadraticMap.map_add Q]
    simp only [hyperbolicPlane_apply, Q.map_smul, hxQ, hyQ, polar_smul_left,
      polar_smul_right, hxy, smul_eq_mul, mul_zero, add_zero, mul_one]
    ring

/-- Over a field in which two is invertible, every finite-dimensional nondegenerate isotropic
quadratic form splits as the orthogonal sum of a hyperbolic plane and a nondegenerate diagonal
form. -/
theorem exists_hyperbolicPlane_prod_equivalent [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) :
    ∃ p : RegularFormPresentation K,
      Q.Equivalent ((hyperbolicPlane K).prod (presentedForm p)) := by
  obtain ⟨x, y, hx, hxQ, hyQ, hxy⟩ := hQ.exists_isotropic_pair hiso
  let W := LinearMap.range (hyperbolicPairMap (K := K) x y)
  let eH := hyperbolicPairIsometryEquiv Q x y hxQ hyQ hxy
  have hWQ : (Q.restrict W).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    have hr := eH.map_radical
    rw [nondegenerate_hyperbolicPlane.radical_eq_bot, Submodule.map_bot] at hr
    exact hr.symm
  let B := QuadraticMap.associated Q
  have hBW : (LinearMap.BilinForm.restrict B W).Nondegenerate := by
    rw [← QuadraticMap.associated_restrict]
    exact QuadraticMap.nondegenerate_associated_iff.mpr hWQ
  have hcomp : IsCompl W (LinearMap.BilinForm.orthogonal B W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)).isRefl hBW
  have horth : (Q.restrict (LinearMap.BilinForm.orthogonal B W)).Nondegenerate := by
    have hB : B.Nondegenerate := QuadraticMap.nondegenerate_associated_iff.mpr hQ
    have hBsymm :=
      (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)).isRefl
    have hBorth :
        (LinearMap.BilinForm.restrict B (LinearMap.BilinForm.orthogonal B W)).Nondegenerate := by
      rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm,
        LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm]
      exact hcomp.symm
    rw [← QuadraticMap.nondegenerate_associated_iff]
    rw [QuadraticMap.associated_restrict]
    exact hBorth
  have hBpolar : LinearMap.BilinForm.orthogonal B W =
      LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    ext v
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, B, associated_isOrtho, isOrtho_polarBilin]
  rw [hBpolar] at hcomp horth
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)) horth
  have hdecomp : Q.Equivalent
      ((Q.restrict W).prod (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))) :=
    ⟨(QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q W hcomp).symm⟩
  have hreplace :
      ((Q.restrict W).prod (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))).Equivalent
        ((hyperbolicPlane K).prod (presentedForm p)) :=
    QuadraticMap.Equivalent.prod
      (⟨eH.symm⟩ : (Q.restrict W).Equivalent (hyperbolicPlane K)) hp
  exact ⟨p, hdecomp.trans hreplace⟩

end TauCeti
