/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LefschetzNumber.Torus
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Rank
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
import TauCeti.AlgebraicTopology.Singular.MappingTorus.Refl
import TauCeti.AlgebraicTopology.Singular.Torus.AddCircle
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner

/-!
# Examples: the product `S¹ × Y` and the symplectic suspension of a surface map

Taubes's comparison of the Seiberg–Witten and Gromov invariants of `X = (ℝ / ℤ)_s × Y` uses three
pieces of bookkeeping that can be tested on explicit data: the `Spinᶜ` lift of the rotations of an
oriented plane field on `Y`, the arithmetic of the line labels `e = a v + c t` of the suspension of
a surface map with `b₁(Y_φ) = 1`, and the homological Lefschetz series that replaces the orbit
product when the return map is degenerate. This file checks each of them on the examples that fix
their normalizations, and shows the value a competing convention would give.

* **The `Spinᶜ` lift of plane rotations.** In `Spinᶜ(3) = (Spin(3) × U(1)) / {1, (-1, -1)}` the
  rotations of an oriented plane `⟨u, w⟩` by `θ` lift to `[exp (θ J / 2), exp (i θ / 2)]`, with
  `J = ι u ι w` (`CliffordAlgebra.spinCCircle_exp`). At `θ = 2π` the first entry is
  `exp (π J) = -1` in `Spin(3)` (`spinCircle_circleExp_pi`) and the second is `exp (i π) = -1`, so
  the class is `[-1, -1] = 1` and the loop closes (`mk_spinCircle_circleExp_two_pi`): it closes
  only because both factors change sign. The lift `[exp (θ J / 2), exp (i θ)]` does not close up:
  at `θ = 2π` it is `[-1, 1] ≠ 1` (`mk_spinCircle_circleExp_two_pi_ne_one`).
* **Line labels of a suspension with `b₁ = 1`.** For a hyperbolic pair `v, t`
  (`v · v = t · t = 0`, `v · t = t · v = 1`), genus `g = 2`, so that `κ = 2 v` modulo torsion, and
  the label `e = 3 v + t` modulo torsion, `q = a + 1 - g = 2` and `c = 1`. Directly,
  `e · e = 2 a c = 6` (`apply_self_eq_six`) and `κ · e = (2 g - 2) c = 2`
  (`apply_canonical_eq_two`), so `d(e) = e · e - κ · e = 4 = 2 c q`
  (`apply_self_sub_apply_canonical_eq_four`). The pairing of `l = 2 e - κ` with
  `[Ω] = t + L v` is `2 (2 + L)` (`apply_two_smul_sub_add_mul_apply_eq`), positive for `L > 0`, the
  sign of `c` (`apply_two_smul_sub_add_mul_apply_pos`). The label `e = t` has `q = -1` and
  `d(e) = -2 < 0` (`apply_self_sub_apply_canonical_eq_neg_two`), so all its regular components
  vanish by dimension.
* **The identity of the two-torus.** Every point is fixed by the identity, so its return map is
  degenerate and an orbit product over its fixed points is undefined. The homological Lefschetz
  series `det (1 - t P) / (1 - t) ^ 2` with `P = 1` is `(1 - t) ^ 2 / (1 - t) ^ 2 = 1`
  (`lefschetzZeta_id_pi_addCircle`): every nonvacuum coefficient vanishes.
* **The three-torus.** The mapping torus `T³` of the identity of `T²` has
  `b₁ = dim ker (1 - 1) + 1 = 2 + 1 = 3` (`finrank_homology_one_mappingTorus_refl_pi_addCircle`),
  so `b₁ > 1` and the product `S¹ × T³ = T⁴` falls under the comparison for `b₂⁺ > 1`.

The normalizations for Arnold's cat map, `det (1 - P) = -1` and the series
`(1 - 3 t + t ^ 2) / (1 - t) ^ 2 = 1 - t - 2 t ^ 2 - 3 t ^ 3 - ⋯` with coarse coefficients
`det (1 - P) (a + 1 - g) = -a`, are `TauCeti.det_one_sub_catMap`,
`TauCeti.coe_charpolyRev_catMap_mul_mk_one_sq` and
`TauCeti.coeff_coe_charpolyRev_catMap_mul_mk_one_sq`, and its Lefschetz series is
`TauCeti.lefschetzZeta_smulVecHom_catMap`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158 (Lemma 3.1 for the Lefschetz series of a surface map).
* P. B. Kronheimer and T. S. Mrowka, *Monopoles and contact structures*, Invent. Math. 130 (1997),
  209–255 (the canonical `Spinᶜ` structure of an oriented plane field).
-/

public section

open Real CategoryTheory AlgebraicTopology HomologicalComplex Module
open _root_.LinearMap (BilinForm)

namespace TauCeti.Examples.Suspension

/-! ### The `Spinᶜ` lift of the rotations of an oriented plane -/

section SpinC

open CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M} (hQ : Q ≠ 0)
  {u w : M} (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)

/-- `exp (π J) = -1` in `Spin(Q)`, for `J = ι u ι w`: the `Spin` entry of the lift of the rotation
by `2π`. -/
theorem spinCircle_circleExp_pi :
    spinCircle Q u w huw h (Circle.exp π) = spinGroup.negOne Q hQ := by
  rw [Circle.exp_pi, spinCircle_neg_one]

/-- **The lift of the plane rotations closes up.** At `θ = 2π` the class
`[exp (θ J / 2), exp (i θ / 2)]` of `CliffordAlgebra.spinCCircle_exp` is `[-1, -1] = 1`. -/
theorem mk_spinCircle_circleExp_two_pi :
    spinCGroup.mk Q hQ (spinCircle Q u w huw h (Circle.exp (2 * π / 2)),
      Circle.exp (2 * π / 2)) = 1 := by
  rw [mul_div_cancel_left₀ π two_ne_zero, spinCircle_circleExp_pi hQ, Circle.exp_pi,
    spinCGroup.mk_negOne_neg_one]

/-- **The lift with `exp (i θ)` does not close up.** At `θ = 2π` the class
`[exp (θ J / 2), exp (i θ)]` is `[-1, 1]`, which is not the identity of `Spinᶜ(Q)`. -/
theorem mk_spinCircle_circleExp_two_pi_ne_one :
    spinCGroup.mk Q hQ (spinCircle Q u w huw h (Circle.exp (2 * π / 2)), Circle.exp (2 * π)) ≠
      1 := by
  rw [mul_div_cancel_left₀ π two_ne_zero, spinCircle_circleExp_pi hQ, Circle.exp_two_pi,
    ← spinCGroup.ofSpin_apply, spinCGroup.ofSpin_negOne, ← map_one (spinCGroup.ofCircle Q hQ)]
  exact (spinCGroup.ofCircle_injective Q hQ).ne (Circle.neg_ne_self 1)

end SpinC

/-! ### Line labels of a suspension of a genus-two surface map -/

section Chamber

variable {H : Type*} [AddCommGroup H] [Module ℤ H] {B : BilinForm ℤ H} {v t e κ : H}

/-- For `e = 3 v + t` modulo torsion, `e · e = 2 a c = 6`. -/
theorem apply_self_eq_six (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (he : IsOfFinAddOrder (e - ((3 : ℤ) • v + (1 : ℤ) • t))) :
    B e e = 6 :=
  B.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub hv ht hvt htv he

/-- For `κ = 2 v` (genus two) and `e = 3 v + t` modulo torsion, `κ · e = (2 g - 2) c = 2`. -/
theorem apply_canonical_eq_two (hv : B v v = 0) (hvt : B v t = 1)
    (he : IsOfFinAddOrder (e - ((3 : ℤ) • v + (1 : ℤ) • t)))
    (hκ : IsOfFinAddOrder (κ - (2 : ℤ) • v)) :
    B κ e = 2 := by
  rw [B.apply_eq_apply_of_isOfFinAddOrder_sub_left hκ,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_right he]
  simp [hv, hvt]

/-- **The dimension of the label `3 v + t` in genus two** is `d(e) = 2 c q = 4`, with `q = 2` and
`c = 1`. -/
theorem apply_self_sub_apply_canonical_eq_four (hv : B v v = 0) (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1) (he : IsOfFinAddOrder (e - ((3 : ℤ) • v + (1 : ℤ) • t)))
    (hκ : IsOfFinAddOrder (κ - (2 : ℤ) • v)) :
    B e e - B κ e = 4 := by
  rw [apply_self_eq_six hv ht hvt htv he, apply_canonical_eq_two hv hvt he hκ]
  norm_num

/-- For `e = 3 v + t` in genus two, the pairing of `l = 2 e - κ` with `[Ω] = t + L v` is
`2 (q + L c) = 2 (2 + L)`. -/
theorem apply_two_smul_sub_add_mul_apply_eq (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1)
    (htv : B t v = 1) (he : IsOfFinAddOrder (e - ((3 : ℤ) • v + (1 : ℤ) • t)))
    (hκ : IsOfFinAddOrder (κ - (2 : ℤ) • v)) (L : ℝ) :
    (B ((2 : ℤ) • e - κ) t : ℝ) + L * B ((2 : ℤ) • e - κ) v = 2 * (2 + L) := by
  rw [SmoothMappingTorus.apply_two_smul_sub_add_mul_apply_eq (g := 2) hv ht hvt htv he
    (by convert hκ using 3; norm_num)]
  norm_num

/-- For `e = 3 v + t` in genus two and `L > 0`, the pairing of `l = 2 e - κ` with
`[Ω] = t + L v` is positive, the sign of `c = 1`. -/
theorem apply_two_smul_sub_add_mul_apply_pos (hv : B v v = 0) (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1) (he : IsOfFinAddOrder (e - ((3 : ℤ) • v + (1 : ℤ) • t)))
    (hκ : IsOfFinAddOrder (κ - (2 : ℤ) • v)) {L : ℝ} (hL : 0 < L) :
    0 < (B ((2 : ℤ) • e - κ) t : ℝ) + L * B ((2 : ℤ) • e - κ) v := by
  rw [apply_two_smul_sub_add_mul_apply_eq hv ht hvt htv he hκ]
  positivity

/-- **The label `t` in genus two has negative dimension**: `q = -1`, `c = 1` and
`d(t) = 2 c q = -2`. -/
theorem apply_self_sub_apply_canonical_eq_neg_two (hv : B v v = 0) (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1) (he : IsOfFinAddOrder (e - t))
    (hκ : IsOfFinAddOrder (κ - (2 : ℤ) • v)) :
    B e e - B κ e = -2 := by
  rw [SmoothMappingTorus.apply_self_sub_apply_canonical_eq (a := 0) (c := 1) (g := 2) hv ht hvt
    htv (by simpa using he) (by convert hκ using 3; norm_num)]
  norm_num

end Chamber

/-! ### The identity of the two-torus and the three-torus -/

/-- **The Lefschetz series of the identity of the two-torus is `1`**: with `P = 1`,
`det (1 - t P) / (1 - t) ^ 2 = (1 - t) ^ 2 / (1 - t) ^ 2 = 1`, so every nonvacuum coefficient
vanishes. -/
theorem lefschetzZeta_id_pi_addCircle (p : ℝ) [NeZero p] (k : Type) [Field k] [Algebra ℚ k] :
    (ContinuousMap.id (Fin 2 → AddCircle p)).lefschetzZeta k = 1 := by
  have hid : ((1 : Matrix (Fin 2) (Fin 2) ℤ).smulVecHom (AddCircle p) :
      C(Fin 2 → AddCircle p, Fin 2 → AddCircle p)) = ContinuousMap.id _ := by
    ext x i
    simp [Matrix.smulVecHom_one]
  have hchar : ((1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom k)).charpolyRev =
      (1 - Polynomial.X) ^ 2 := by
    simp [Matrix.charpolyRev, Matrix.det_fin_two, sq]
  rw [← hid, Matrix.lefschetzZeta_smulVecHom_fin_two_of_det_eq_one (by simp) k (NeZero.ne p),
    hchar]
  push_cast
  rw [← mul_pow, mul_comm, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow]

/-- **The first Betti number of the three-torus is `3`.** Over any field, the mapping torus of the
identity of the two-torus `Fin 2 → AddCircle p` has `b₁ = dim ker (1 - 1) + 1 = 2 + 1 = 3`. -/
theorem finrank_homology_one_mappingTorus_refl_pi_addCircle (p : ℝ) [NeZero p] (k : Type)
    [Field k] :
    finrank k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus (Homeomorph.refl (Fin 2 → AddCircle p))))).homology 1) = 3 := by
  have h₂ := ModuleCat.finrank_singularHomology_pi_addCircle (ModuleCat.of k k)
    (fun _ : Fin 2 ↦ p) 1
  have h₃ : (Nat.card (Fin 2)).choose 1 * finrank k (ModuleCat.of k k) = 2 := by simp
  have : FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{0} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (Fin 2 → AddCircle p))).homology 1) :=
    ModuleCat.finite_singularHomology_pi_addCircle (ModuleCat.of k k) (fun _ : Fin 2 ↦ p) 1
  rw [MappingTorus.finrank_homology_one, MappingTorus.monodromyChainMap_refl, homologyMap_id,
    ModuleCat.hom_id, sub_self, LinearMap.ker_zero, finrank_top]
  -- `singularHomologyFunctor` is by definition the homology of `singularChainComplexFunctor`.
  exact congrArg (· + 1) (h₂.trans h₃)

end TauCeti.Examples.Suspension
