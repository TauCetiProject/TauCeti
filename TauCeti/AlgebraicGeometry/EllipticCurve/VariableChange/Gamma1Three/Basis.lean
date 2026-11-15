/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Gamma1Three.HopfAlgebroid

/-!
# Rank-eight basis and trace formulas for the `Γ₁(3)` arrow algebra

When `3` is invertible in a commutative ring `B`, the strict `Γ₁(3)` arrow algebra
`ArrowRingOf B a₁ a₃` is finitely generated and free of rank `8` over `B` on the ordered monomial
basis

`![1, s, s², s³, t, s * t, s² * t, s³ * t]`.

Eliminating `3r = s² + a₁s` from the three defining relations of `ArrowRingOf B a₁ a₃` yields
explicit reduction identities for `s⁴` and `27t²` over an arbitrary commutative ring `B`, and for
`r`, `t²` and `s⁴t` once `3` is invertible in `B`. Using these reductions, we construct a faithful
commutative subalgebra of `Module.End B (Fin 8 → B)` receiving `ArrowRingOf B a₁ a₃`, prove linear
independence and spanning of the monomial family (`ArrowRingOf.basis`), deduce `Module.Free`,
`Module.Finite` and `Module.finrank B (ArrowRingOf B a₁ a₃) = 8`, and compute
`Algebra.trace B (ArrowRingOf B a₁ a₃)` on all eight basis elements together with its base-change
compatibility (`ArrowRingOf.trace_map`) and Hopf-algebroid coproduct compatibility
(`trace_coproduct`).

## Main definitions

* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf.basisFamily B a₁ a₃`: the monomial tuple
  `![1, s, s², s³, t, s * t, s² * t, s³ * t]`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRingOf.basis B a₁ a₃`: the `Module.Basis (Fin 8) B`
  structure on `ArrowRingOf B a₁ a₃` when `[Invertible (3 : B)]`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.arrowRingBasis R`: the resulting `BaseRing R`-basis of
  `ArrowRing R` when `[Invertible (3 : R)]`.

## Main results

* `ArrowRingOf.s_pow_four`, `ArrowRingOf.twentySeven_mul_t_sq`: denominator-free polynomial
  reductions in `ArrowRingOf B a₁ a₃` over any commutative ring `B`.
* `ArrowRingOf.r_eq`, `ArrowRingOf.t_sq`, `ArrowRingOf.s_pow_four_mul_t`: reductions onto the
  eight-element monomial basis when `[Invertible (3 : B)]`.
* `ArrowRingOf.finrank_eq_eight` and `finrank_arrowRing_eq_eight`: rank-`8` freeness of
  `ArrowRingOf B a₁ a₃` and `ArrowRing R`.
* `ArrowRingOf.trace_one` through `ArrowRingOf.trace_s_cube_mul_t`, `ArrowRingOf.trace_mapOfEq`,
  `ArrowRingOf.trace_map`, and `trace_coproduct`: exact `Algebra.trace` formulas and functoriality.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* K. Carrick, J. Davies and S. van Nigtevecht, *Topological modular forms with level structure:
  deformations, transfers, and differentials*, §4.2, Lemma 4.8.
-/

public section

noncomputable section

namespace TauCeti.Gamma1ThreeHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve

namespace ArrowRingOf

/-! ### Polynomial reductions in `ArrowRingOf B a₁ a₃` -/

section Reductions

variable (B : Type*) [CommRing B] (a₁ a₃ : B)

/-- Scalar multiplication by `b : B` on `ArrowRingOf B a₁ a₃` agrees with multiplication by
`algebraMap B _ b` (specialized to the quotient `SMul` instance for syntactic rewriting). -/
theorem smul_eq_algebraMap_mul (b : B) (y : ArrowRingOf B a₁ a₃) :
    b • y = algebraMap B (ArrowRingOf B a₁ a₃) b * y :=
  Algebra.smul_def b y

/-- In `ArrowRingOf B a₁ a₃` (over any commutative ring `B`, with no invertibility assumption on
`3`), `s⁴ = 3a₃s - a₁s³ + 3a₁t + 6st`. -/
theorem s_pow_four :
    s B a₁ a₃ ^ 4 =
      3 * algebraMap B _ a₃ * s B a₁ a₃ -
        algebraMap B _ a₁ * s B a₁ a₃ ^ 3 +
        3 * algebraMap B _ a₁ * t B a₁ a₃ +
        6 * s B a₁ a₃ * t B a₁ a₃ := by
  have h₂ := three_mul_r_sub_s_sq_sub_a₁_mul_s B a₁ a₃
  have h₄ := relation_a₄ B a₁ a₃
  linear_combination -(s B a₁ a₃ ^ 2 + 3 * r B a₁ a₃) * h₂ + 3 * h₄

private theorem s_pow_five :
    s B a₁ a₃ ^ 5 =
      -3 * algebraMap B _ a₁ * algebraMap B _ a₃ * s B a₁ a₃ +
        3 * algebraMap B _ a₃ * s B a₁ a₃ ^ 2 +
        algebraMap B _ a₁ ^ 2 * s B a₁ a₃ ^ 3 -
        3 * algebraMap B _ a₁ ^ 2 * t B a₁ a₃ -
        3 * algebraMap B _ a₁ * s B a₁ a₃ * t B a₁ a₃ +
        6 * s B a₁ a₃ ^ 2 * t B a₁ a₃ := by
  linear_combination (s B a₁ a₃ - algebraMap B _ a₁) * s_pow_four B a₁ a₃

private theorem s_pow_six :
    s B a₁ a₃ ^ 6 =
      3 * algebraMap B _ a₁ ^ 2 * algebraMap B _ a₃ * s B a₁ a₃ -
        3 * algebraMap B _ a₁ * algebraMap B _ a₃ * s B a₁ a₃ ^ 2 +
        (-algebraMap B _ a₁ ^ 3 + 3 * algebraMap B _ a₃) * s B a₁ a₃ ^ 3 +
        3 * algebraMap B _ a₁ ^ 3 * t B a₁ a₃ +
        3 * algebraMap B _ a₁ ^ 2 * s B a₁ a₃ * t B a₁ a₃ -
        3 * algebraMap B _ a₁ * s B a₁ a₃ ^ 2 * t B a₁ a₃ +
        6 * s B a₁ a₃ ^ 3 * t B a₁ a₃ := by
  linear_combination
    (s B a₁ a₃ ^ 2 - algebraMap B _ a₁ * s B a₁ a₃ + algebraMap B _ a₁ ^ 2) * s_pow_four B a₁ a₃

/-- Denominator-cleared reduction of `27t²` in `ArrowRingOf B a₁ a₃` over any commutative ring
`B`. -/
theorem twentySeven_mul_t_sq :
    27 * t B a₁ a₃ ^ 2 =
      3 * (algebraMap B _ a₁ ^ 2 * algebraMap B _ a₃ * s B a₁ a₃ +
        2 * algebraMap B _ a₁ * algebraMap B _ a₃ * s B a₁ a₃ ^ 2 +
        algebraMap B _ a₃ * s B a₁ a₃ ^ 3 +
        (algebraMap B _ a₁ ^ 3 - 9 * algebraMap B _ a₃) * t B a₁ a₃ +
        algebraMap B _ a₁ ^ 2 * (s B a₁ a₃ * t B a₁ a₃) +
        2 * algebraMap B _ a₁ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) +
        2 * (s B a₁ a₃ ^ 3 * t B a₁ a₃)) := by
  have h3r : 3 * r B a₁ a₃ = s B a₁ a₃ ^ 2 + algebraMap B _ a₁ * s B a₁ a₃ := by
    linear_combination three_mul_r_sub_s_sq_sub_a₁_mul_s B a₁ a₃
  have h27 : 27 * t B a₁ a₃ ^ 2 =
      (3 * r B a₁ a₃) ^ 3 - 9 * algebraMap B _ a₁ * (3 * r B a₁ a₃) * t B a₁ a₃ -
        27 * algebraMap B _ a₃ * t B a₁ a₃ := by
    linear_combination -27 * relation_a₆ B a₁ a₃
  rw [h27, h3r]
  linear_combination
    s_pow_six B a₁ a₃ + 3 * algebraMap B _ a₁ * s_pow_five B a₁ a₃ +
      3 * algebraMap B _ a₁ ^ 2 * s_pow_four B a₁ a₃

/-- The ordered monomial family `![1, s, s², s³, t, s * t, s² * t, s³ * t]` in
`ArrowRingOf B a₁ a₃`. -/
def basisFamily : Fin 8 → ArrowRingOf B a₁ a₃ :=
  ![1, s B a₁ a₃, s B a₁ a₃ ^ 2, s B a₁ a₃ ^ 3, t B a₁ a₃,
    s B a₁ a₃ * t B a₁ a₃, s B a₁ a₃ ^ 2 * t B a₁ a₃, s B a₁ a₃ ^ 3 * t B a₁ a₃]

@[simp] private theorem basisFamily_zero : basisFamily B a₁ a₃ 0 = 1 := rfl
@[simp] private theorem basisFamily_one : basisFamily B a₁ a₃ 1 = s B a₁ a₃ := rfl
@[simp] private theorem basisFamily_two : basisFamily B a₁ a₃ 2 = s B a₁ a₃ ^ 2 := rfl
@[simp] private theorem basisFamily_three : basisFamily B a₁ a₃ 3 = s B a₁ a₃ ^ 3 := rfl
@[simp] private theorem basisFamily_four : basisFamily B a₁ a₃ 4 = t B a₁ a₃ := rfl
@[simp] private theorem basisFamily_five : basisFamily B a₁ a₃ 5 = s B a₁ a₃ * t B a₁ a₃ := rfl
@[simp] private theorem basisFamily_six :
    basisFamily B a₁ a₃ 6 = s B a₁ a₃ ^ 2 * t B a₁ a₃ := rfl
@[simp] private theorem basisFamily_seven :
    basisFamily B a₁ a₃ 7 = s B a₁ a₃ ^ 3 * t B a₁ a₃ := rfl

private theorem basisFamily_mem_span (i : Fin 8) :
    basisFamily B a₁ a₃ i ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃)) :=
  Submodule.subset_span ⟨i, rfl⟩

private def stdVec : Fin 8 → Fin 8 → B
  | 0 => ![1, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0, 0, 0]
  | 4 => ![0, 0, 0, 0, 1, 0, 0, 0]
  | 5 => ![0, 0, 0, 0, 0, 1, 0, 0]
  | 6 => ![0, 0, 0, 0, 0, 0, 1, 0]
  | 7 => ![0, 0, 0, 0, 0, 0, 0, 1]

private theorem pi_single_eq_stdVec (i : Fin 8) :
    Pi.single i (1 : B) = stdVec B i := by
  ext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem linearMap_trace_pi_eight (L : Module.End B (Fin 8 → B)) :
    LinearMap.trace B (Fin 8 → B) L =
      L (stdVec B 0) 0 + L (stdVec B 1) 1 + L (stdVec B 2) 2 + L (stdVec B 3) 3 +
        L (stdVec B 4) 4 + L (stdVec B 5) 5 + L (stdVec B 6) 6 + L (stdVec B 7) 7 := by
  rw [LinearMap.trace_eq_matrix_trace B (Pi.basisFun B (Fin 8)) L, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    pi_single_eq_stdVec, Fin.sum_univ_eight]

variable [Invertible (3 : B)]

private theorem algebraMap_invOf_three_mul :
    algebraMap B (ArrowRingOf B a₁ a₃) ⅟(3 : B) * 3 = 1 := by
  rw [← map_ofNat (algebraMap B (ArrowRingOf B a₁ a₃)) 3, ← map_mul, invOf_mul_self, map_one]

/-- When `3` is invertible in `B`, `r = ⅟3 * (s² + a₁s)` in `ArrowRingOf B a₁ a₃`. -/
theorem r_eq :
    r B a₁ a₃ =
      algebraMap B _ ⅟(3 : B) * (s B a₁ a₃ ^ 2 + algebraMap B _ a₁ * s B a₁ a₃) := by
  linear_combination
    algebraMap B _ ⅟(3 : B) * three_mul_r_sub_s_sq_sub_a₁_mul_s B a₁ a₃ -
      r B a₁ a₃ * algebraMap_invOf_three_mul B a₁ a₃

private theorem nine_mul_t_sq :
    9 * t B a₁ a₃ ^ 2 =
      algebraMap B _ a₁ ^ 2 * algebraMap B _ a₃ * s B a₁ a₃ +
        2 * algebraMap B _ a₁ * algebraMap B _ a₃ * s B a₁ a₃ ^ 2 +
        algebraMap B _ a₃ * s B a₁ a₃ ^ 3 +
        (algebraMap B _ a₁ ^ 3 - 9 * algebraMap B _ a₃) * t B a₁ a₃ +
        algebraMap B _ a₁ ^ 2 * (s B a₁ a₃ * t B a₁ a₃) +
        2 * algebraMap B _ a₁ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) +
        2 * (s B a₁ a₃ ^ 3 * t B a₁ a₃) := by
  linear_combination
    algebraMap B _ ⅟(3 : B) * twentySeven_mul_t_sq B a₁ a₃ -
      (9 * t B a₁ a₃ ^ 2 -
        (algebraMap B _ a₁ ^ 2 * algebraMap B _ a₃ * s B a₁ a₃ +
          2 * algebraMap B _ a₁ * algebraMap B _ a₃ * s B a₁ a₃ ^ 2 +
          algebraMap B _ a₃ * s B a₁ a₃ ^ 3 +
          (algebraMap B _ a₁ ^ 3 - 9 * algebraMap B _ a₃) * t B a₁ a₃ +
          algebraMap B _ a₁ ^ 2 * (s B a₁ a₃ * t B a₁ a₃) +
          2 * algebraMap B _ a₁ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) +
          2 * (s B a₁ a₃ ^ 3 * t B a₁ a₃))) * algebraMap_invOf_three_mul B a₁ a₃

/-- Explicit reduction of `t²` onto the basis `{1, s, s², s³, t, st, s²t, s³t}`. -/
theorem t_sq :
    t B a₁ a₃ ^ 2 =
      algebraMap B _ (⅟(3 : B) ^ 2 * a₁ ^ 2 * a₃) * s B a₁ a₃ +
        algebraMap B _ (2 * ⅟(3 : B) ^ 2 * a₁ * a₃) * s B a₁ a₃ ^ 2 +
        algebraMap B _ (⅟(3 : B) ^ 2 * a₃) * s B a₁ a₃ ^ 3 +
        algebraMap B _ (⅟(3 : B) ^ 2 * a₁ ^ 3 - a₃) * t B a₁ a₃ +
        algebraMap B _ (⅟(3 : B) ^ 2 * a₁ ^ 2) * (s B a₁ a₃ * t B a₁ a₃) +
        algebraMap B _ (2 * ⅟(3 : B) ^ 2 * a₁) * (s B a₁ a₃ ^ 2 * t B a₁ a₃) +
        algebraMap B _ (2 * ⅟(3 : B) ^ 2) * (s B a₁ a₃ ^ 3 * t B a₁ a₃) := by
  have h3 := algebraMap_invOf_three_mul B a₁ a₃
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination
    algebraMap B _ ⅟(3 : B) ^ 2 * nine_mul_t_sq B a₁ a₃ -
      (t B a₁ a₃ ^ 2 + algebraMap B _ a₃ * t B a₁ a₃) *
        (algebraMap B _ ⅟(3 : B) * 3 + 1) * h3

/-- Explicit reduction of `s⁴t` onto the basis `{1, s, s², s³, t, st, s²t, s³t}`. -/
theorem s_pow_four_mul_t :
    s B a₁ a₃ ^ 4 * t B a₁ a₃ =
      algebraMap B _ (-(a₁ ^ 3 * a₃ + 6 * a₃ ^ 2)) * s B a₁ a₃ -
        algebraMap B _ (4 * a₁ ^ 2 * a₃) * s B a₁ a₃ ^ 2 -
        algebraMap B _ (3 * a₁ * a₃) * s B a₁ a₃ ^ 3 +
        algebraMap B _ (3 * a₁ * a₃ - a₁ ^ 4) * t B a₁ a₃ -
        algebraMap B _ (3 * a₁ ^ 3 + 3 * a₃) * (s B a₁ a₃ * t B a₁ a₃) -
        algebraMap B _ (4 * a₁ ^ 2) * (s B a₁ a₃ ^ 2 * t B a₁ a₃) -
        algebraMap B _ (3 * a₁) * (s B a₁ a₃ ^ 3 * t B a₁ a₃) := by
  simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination
    -(3 * t B a₁ a₃ + 2 * algebraMap B _ a₃) * s_pow_four B a₁ a₃ -
      (algebraMap B _ a₁ + 2 * s B a₁ a₃) * nine_mul_t_sq B a₁ a₃

end Reductions

/-! ### Free rank-`8` basis and endomorphism representation -/

section Basis

variable (B : Type*) [CommRing B] [Invertible (3 : B)] (a₁ a₃ : B)

private theorem mul_s_mem_span {y : ArrowRingOf B a₁ a₃}
    (hy : y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃))) :
    s B a₁ a₃ * y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃)) := by
  refine Submodule.span_induction (fun _ ⟨i, hi⟩ ↦ ?_) (by simp)
    (fun x z _ _ hx hz ↦ by rw [mul_add]; exact add_mem hx hz)
    (fun b x _ hx ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx) hy
  subst hi
  have hmem := basisFamily_mem_span B a₁ a₃
  fin_cases i
  · change s B a₁ a₃ * 1 ∈ _
    rw [mul_one, ← basisFamily_one]
    exact hmem 1
  · change s B a₁ a₃ * s B a₁ a₃ ∈ _
    rw [← sq, ← basisFamily_two]
    exact hmem 2
  · change s B a₁ a₃ * s B a₁ a₃ ^ 2 ∈ _
    rw [show s B a₁ a₃ * s B a₁ a₃ ^ 2 = s B a₁ a₃ ^ 3 by ring, ← basisFamily_three]
    exact hmem 3
  · change s B a₁ a₃ * s B a₁ a₃ ^ 3 ∈ _
    rw [show s B a₁ a₃ * s B a₁ a₃ ^ 3 = s B a₁ a₃ ^ 4 by ring]
    have h1 := Submodule.smul_mem _ (3 * a₃) (hmem 1)
    have h3 := Submodule.smul_mem _ a₁ (hmem 3)
    have h4 := Submodule.smul_mem _ (3 * a₁) (hmem 4)
    have h5 := Submodule.smul_mem _ (6 : B) (hmem 5)
    rw [basisFamily_one, smul_eq_algebraMap_mul] at h1
    rw [basisFamily_three, smul_eq_algebraMap_mul] at h3
    rw [basisFamily_four, smul_eq_algebraMap_mul] at h4
    rw [basisFamily_five, smul_eq_algebraMap_mul] at h5
    have hsum := add_mem (add_mem (sub_mem h1 h3) h4) h5
    have heq : s B a₁ a₃ ^ 4 =
        algebraMap B _ (3 * a₃) * s B a₁ a₃ - algebraMap B _ a₁ * s B a₁ a₃ ^ 3 +
          algebraMap B _ (3 * a₁) * t B a₁ a₃ +
          algebraMap B _ 6 * (s B a₁ a₃ * t B a₁ a₃) := by
      rw [s_pow_four]
      simp only [map_mul, map_ofNat]
      ring
    rwa [heq]
  · change s B a₁ a₃ * t B a₁ a₃ ∈ _
    rw [← basisFamily_five]
    exact hmem 5
  · change s B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃) ∈ _
    rw [show s B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃) = s B a₁ a₃ ^ 2 * t B a₁ a₃ by ring,
      ← basisFamily_six]
    exact hmem 6
  · change s B a₁ a₃ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) ∈ _
    rw [show s B a₁ a₃ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) = s B a₁ a₃ ^ 3 * t B a₁ a₃ by ring,
      ← basisFamily_seven]
    exact hmem 7
  · change s B a₁ a₃ * (s B a₁ a₃ ^ 3 * t B a₁ a₃) ∈ _
    rw [show s B a₁ a₃ * (s B a₁ a₃ ^ 3 * t B a₁ a₃) = s B a₁ a₃ ^ 4 * t B a₁ a₃ by ring,
      s_pow_four_mul_t]
    have h1 := Submodule.smul_mem _ (-(a₁ ^ 3 * a₃ + 6 * a₃ ^ 2)) (hmem 1)
    have h2 := Submodule.smul_mem _ (4 * a₁ ^ 2 * a₃) (hmem 2)
    have h3 := Submodule.smul_mem _ (3 * a₁ * a₃) (hmem 3)
    have h4 := Submodule.smul_mem _ (3 * a₁ * a₃ - a₁ ^ 4) (hmem 4)
    have h5 := Submodule.smul_mem _ (3 * a₁ ^ 3 + 3 * a₃) (hmem 5)
    have h6 := Submodule.smul_mem _ (4 * a₁ ^ 2) (hmem 6)
    have h7 := Submodule.smul_mem _ (3 * a₁) (hmem 7)
    rw [basisFamily_one, smul_eq_algebraMap_mul] at h1
    rw [basisFamily_two, smul_eq_algebraMap_mul] at h2
    rw [basisFamily_three, smul_eq_algebraMap_mul] at h3
    rw [basisFamily_four, smul_eq_algebraMap_mul] at h4
    rw [basisFamily_five, smul_eq_algebraMap_mul] at h5
    rw [basisFamily_six, smul_eq_algebraMap_mul] at h6
    rw [basisFamily_seven, smul_eq_algebraMap_mul] at h7
    exact sub_mem (sub_mem (sub_mem (add_mem (sub_mem (sub_mem h1 h2) h3) h4) h5) h6) h7

private theorem mul_r_mem_span {y : ArrowRingOf B a₁ a₃}
    (hy : y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃))) :
    r B a₁ a₃ * y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃)) := by
  have hs1 := mul_s_mem_span B a₁ a₃ hy
  have hs2 := mul_s_mem_span B a₁ a₃ hs1
  have hc := Submodule.smul_mem _ ⅟(3 : B) (add_mem hs2 (Submodule.smul_mem _ a₁ hs1))
  simp only [smul_eq_algebraMap_mul] at hc
  have heq : r B a₁ a₃ * y =
      algebraMap B _ ⅟(3 : B) * (s B a₁ a₃ * (s B a₁ a₃ * y) +
        algebraMap B _ a₁ * (s B a₁ a₃ * y)) := by
    rw [r_eq]
    ring
  rwa [heq]

private theorem t_sq_mem_span :
    t B a₁ a₃ ^ 2 ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃)) := by
  have hmem := basisFamily_mem_span B a₁ a₃
  rw [t_sq]
  have h1 := Submodule.smul_mem _ (⅟(3 : B) ^ 2 * a₁ ^ 2 * a₃) (hmem 1)
  have h2 := Submodule.smul_mem _ (2 * ⅟(3 : B) ^ 2 * a₁ * a₃) (hmem 2)
  have h3 := Submodule.smul_mem _ (⅟(3 : B) ^ 2 * a₃) (hmem 3)
  have h4 := Submodule.smul_mem _ (⅟(3 : B) ^ 2 * a₁ ^ 3 - a₃) (hmem 4)
  have h5 := Submodule.smul_mem _ (⅟(3 : B) ^ 2 * a₁ ^ 2) (hmem 5)
  have h6 := Submodule.smul_mem _ (2 * ⅟(3 : B) ^ 2 * a₁) (hmem 6)
  have h7 := Submodule.smul_mem _ (2 * ⅟(3 : B) ^ 2) (hmem 7)
  rw [basisFamily_one, smul_eq_algebraMap_mul] at h1
  rw [basisFamily_two, smul_eq_algebraMap_mul] at h2
  rw [basisFamily_three, smul_eq_algebraMap_mul] at h3
  rw [basisFamily_four, smul_eq_algebraMap_mul] at h4
  rw [basisFamily_five, smul_eq_algebraMap_mul] at h5
  rw [basisFamily_six, smul_eq_algebraMap_mul] at h6
  rw [basisFamily_seven, smul_eq_algebraMap_mul] at h7
  exact add_mem (add_mem (add_mem (add_mem (add_mem (add_mem h1 h2) h3) h4) h5) h6) h7

private theorem mul_t_mem_span {y : ArrowRingOf B a₁ a₃}
    (hy : y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃))) :
    t B a₁ a₃ * y ∈ Submodule.span B (Set.range (basisFamily B a₁ a₃)) := by
  refine Submodule.span_induction (fun _ ⟨i, hi⟩ ↦ ?_) (by simp)
    (fun x z _ _ hx hz ↦ by rw [mul_add]; exact add_mem hx hz)
    (fun b x _ hx ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx) hy
  subst hi
  have hmem := basisFamily_mem_span B a₁ a₃
  have ht2 := t_sq_mem_span B a₁ a₃
  have hst2 := mul_s_mem_span B a₁ a₃ ht2
  have hs2t2 := mul_s_mem_span B a₁ a₃ hst2
  have hs3t2 := mul_s_mem_span B a₁ a₃ hs2t2
  fin_cases i
  · change t B a₁ a₃ * 1 ∈ _
    rw [mul_one, ← basisFamily_four]
    exact hmem 4
  · change t B a₁ a₃ * s B a₁ a₃ ∈ _
    rw [mul_comm, ← basisFamily_five]
    exact hmem 5
  · change t B a₁ a₃ * s B a₁ a₃ ^ 2 ∈ _
    rw [mul_comm, ← basisFamily_six]
    exact hmem 6
  · change t B a₁ a₃ * s B a₁ a₃ ^ 3 ∈ _
    rw [mul_comm, ← basisFamily_seven]
    exact hmem 7
  · change t B a₁ a₃ * t B a₁ a₃ ∈ _
    rw [← sq]
    exact ht2
  · change t B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃) ∈ _
    rw [show t B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃) = s B a₁ a₃ * t B a₁ a₃ ^ 2 by ring]
    exact hst2
  · change t B a₁ a₃ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) ∈ _
    rw [show t B a₁ a₃ * (s B a₁ a₃ ^ 2 * t B a₁ a₃) = s B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃ ^ 2) by
      ring]
    exact hs2t2
  · change t B a₁ a₃ * (s B a₁ a₃ ^ 3 * t B a₁ a₃) ∈ _
    rw [show t B a₁ a₃ * (s B a₁ a₃ ^ 3 * t B a₁ a₃) =
      s B a₁ a₃ * (s B a₁ a₃ * (s B a₁ a₃ * t B a₁ a₃ ^ 2)) by ring]
    exact hs3t2

private theorem top_le_span_basisFamily :
    (⊤ : Submodule B (ArrowRingOf B a₁ a₃)) ≤
      Submodule.span B (Set.range (basisFamily B a₁ a₃)) := by
  let M := Submodule.span B (Set.range (basisFamily B a₁ a₃))
  let S : Subalgebra B (ArrowRingOf B a₁ a₃) :=
    { carrier := {y | ∀ z ∈ M, y * z ∈ M}
      zero_mem' := fun _ _ ↦ by simp
      one_mem' := fun z hz ↦ by simpa using hz
      add_mem' := fun ha hb z hz ↦ by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
      mul_mem' := fun ha hb z hz ↦ by rw [mul_assoc]; exact ha _ (hb z hz)
      algebraMap_mem' := fun b z hz ↦ by rw [← smul_eq_algebraMap_mul]; exact M.smul_mem b hz }
  let rS : S := ⟨r B a₁ a₃, fun z hz ↦ mul_r_mem_span B a₁ a₃ hz⟩
  let sS : S := ⟨s B a₁ a₃, fun z hz ↦ mul_s_mem_span B a₁ a₃ hz⟩
  let tS : S := ⟨t B a₁ a₃, fun z hz ↦ mul_t_mem_span B a₁ a₃ hz⟩
  have hD : IsStrictGamma1ThreeChange (algebraMap B S a₁) (algebraMap B S a₃) ⟨1, rS, sS, tS⟩ :=
    isStrictGamma1ThreeChange_mk_iff.mpr
      ⟨Subtype.ext (three_mul_r_sub_s_sq_sub_a₁_mul_s B a₁ a₃),
        Subtype.ext (relation_a₄ B a₁ a₃), Subtype.ext (relation_a₆ B a₁ a₃)⟩
  let sec : ArrowRingOf B a₁ a₃ →+* S := lift ⟨(algebraMap B S, ⟨1, rS, sS, tS⟩), hD⟩
  have hsec : S.val.toRingHom.comp sec = RingHom.id (ArrowRingOf B a₁ a₃) := by
    refine ringHom_ext (RingHom.ext fun b ↦ by simp [sec]) ?_
    ext <;> simp [sec, rS, sS, tS]
  intro y _
  have hyS : y ∈ S := by
    have hy : S.val (sec y) = y := RingHom.congr_fun hsec y
    rw [← hy]
    exact (sec y).2
  have h1 : (1 : ArrowRingOf B a₁ a₃) ∈ M := Submodule.subset_span ⟨0, rfl⟩
  simpa using hyS 1 h1

/-! #### Endomorphism model on `Fin 8 → B` -/

private def opSVec (v : Fin 8 → B) : Fin 8 → B :=
  ![0,
    v 0 + 3 * a₃ * v 3 - (a₁ ^ 3 * a₃ + 6 * a₃ ^ 2) * v 7,
    v 1 - 4 * a₁ ^ 2 * a₃ * v 7,
    v 2 - a₁ * v 3 - 3 * a₁ * a₃ * v 7,
    3 * a₁ * v 3 + (3 * a₁ * a₃ - a₁ ^ 4) * v 7,
    6 * v 3 + v 4 - (3 * a₁ ^ 3 + 3 * a₃) * v 7,
    v 5 - 4 * a₁ ^ 2 * v 7,
    v 6 - 3 * a₁ * v 7]

private def opS : Module.End B (Fin 8 → B) where
  toFun := opSVec B a₁ a₃
  map_add' u v := funext fun i ↦ by fin_cases i <;> simp [opSVec] <;> ring
  map_smul' b v := funext fun i ↦ by fin_cases i <;> simp [opSVec] <;> ring

private def t9Col4 : Fin 8 → B :=
  ![0, a₁ ^ 2 * a₃, 2 * a₁ * a₃, a₃, a₁ ^ 3 - 9 * a₃, a₁ ^ 2, 2 * a₁, 2]

private def t9Col5 : Fin 8 → B := opSVec B a₁ a₃ (t9Col4 B a₁ a₃)

private def t9Col6 : Fin 8 → B := opSVec B a₁ a₃ (t9Col5 B a₁ a₃)

private def t9Col7 : Fin 8 → B := opSVec B a₁ a₃ (t9Col6 B a₁ a₃)

private def opT9Vec (v : Fin 8 → B) : Fin 8 → B :=
  ![v 4 * t9Col4 B a₁ a₃ 0 + v 5 * t9Col5 B a₁ a₃ 0 +
      v 6 * t9Col6 B a₁ a₃ 0 + v 7 * t9Col7 B a₁ a₃ 0,
    v 4 * t9Col4 B a₁ a₃ 1 + v 5 * t9Col5 B a₁ a₃ 1 +
      v 6 * t9Col6 B a₁ a₃ 1 + v 7 * t9Col7 B a₁ a₃ 1,
    v 4 * t9Col4 B a₁ a₃ 2 + v 5 * t9Col5 B a₁ a₃ 2 +
      v 6 * t9Col6 B a₁ a₃ 2 + v 7 * t9Col7 B a₁ a₃ 2,
    v 4 * t9Col4 B a₁ a₃ 3 + v 5 * t9Col5 B a₁ a₃ 3 +
      v 6 * t9Col6 B a₁ a₃ 3 + v 7 * t9Col7 B a₁ a₃ 3,
    9 * v 0 + v 4 * t9Col4 B a₁ a₃ 4 + v 5 * t9Col5 B a₁ a₃ 4 +
      v 6 * t9Col6 B a₁ a₃ 4 + v 7 * t9Col7 B a₁ a₃ 4,
    9 * v 1 + v 4 * t9Col4 B a₁ a₃ 5 + v 5 * t9Col5 B a₁ a₃ 5 +
      v 6 * t9Col6 B a₁ a₃ 5 + v 7 * t9Col7 B a₁ a₃ 5,
    9 * v 2 + v 4 * t9Col4 B a₁ a₃ 6 + v 5 * t9Col5 B a₁ a₃ 6 +
      v 6 * t9Col6 B a₁ a₃ 6 + v 7 * t9Col7 B a₁ a₃ 6,
    9 * v 3 + v 4 * t9Col4 B a₁ a₃ 7 + v 5 * t9Col5 B a₁ a₃ 7 +
      v 6 * t9Col6 B a₁ a₃ 7 + v 7 * t9Col7 B a₁ a₃ 7]

private def opT9 : Module.End B (Fin 8 → B) where
  toFun := opT9Vec B a₁ a₃
  map_add' u v := funext fun i ↦ by fin_cases i <;> simp [opT9Vec] <;> ring
  map_smul' b v := funext fun i ↦ by fin_cases i <;> simp [opT9Vec] <;> ring

omit [Invertible (3 : B)] in
private theorem commute_opS_opT9 : Commute (opS B a₁ a₃) (opT9 B a₁ a₃) := by
  refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
  change opSVec B a₁ a₃ (opT9Vec B a₁ a₃ v) i = opT9Vec B a₁ a₃ (opSVec B a₁ a₃ v) i
  fin_cases i <;>
    simp [opSVec, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4] <;>
    ring

private def opT : Module.End B (Fin 8 → B) :=
  (⅟(3 : B) ^ 2) • opT9 B a₁ a₃

private theorem commute_opS_opT : Commute (opS B a₁ a₃) (opT B a₁ a₃) :=
  (commute_opS_opT9 B a₁ a₃).smul_right _

private abbrev OpSubalg : Subalgebra B (Module.End B (Fin 8 → B)) :=
  Algebra.adjoin B {opS B a₁ a₃, opT B a₁ a₃}

private theorem mul_comm_opSubalg (x y : OpSubalg B a₁ a₃) : x * y = y * x := by
  apply Subtype.ext
  change Commute (x : Module.End B (Fin 8 → B)) (y : Module.End B (Fin 8 → B))
  refine Algebra.adjoin_induction (fun f hf ↦ ?_) (fun b ↦ Algebra.commute_algebraMap_left b _)
    (fun _ _ _ _ hf hg ↦ hf.add_left hg) (fun _ _ _ _ hf hg ↦ hf.mul_left hg) x.2
  refine Algebra.adjoin_induction (fun g hg ↦ ?_) (fun b ↦ Algebra.commute_algebraMap_right b _)
    (fun _ _ _ _ hf hg ↦ hf.add_right hg) (fun _ _ _ _ hf hg ↦ hf.mul_right hg) y.2
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact Commute.refl _
  · exact commute_opS_opT B a₁ a₃
  · exact (commute_opS_opT B a₁ a₃).symm
  · exact Commute.refl _

@[instance_reducible]
private def instCommRingOpSubalg : CommRing (OpSubalg B a₁ a₃) :=
  { (inferInstance : Ring (OpSubalg B a₁ a₃)) with mul_comm := mul_comm_opSubalg B a₁ a₃ }

attribute [local instance] instCommRingOpSubalg

private def elS : OpSubalg B a₁ a₃ :=
  ⟨opS B a₁ a₃, Algebra.subset_adjoin (by simp)⟩

private def elT : OpSubalg B a₁ a₃ :=
  ⟨opT B a₁ a₃, Algebra.subset_adjoin (by simp)⟩

private def elR : OpSubalg B a₁ a₃ :=
  ⅟(3 : B) • (elS B a₁ a₃ ^ 2 + a₁ • elS B a₁ a₃)

private def vec0 : Fin 8 → B :=
  ![1, 0, 0, 0, 0, 0, 0, 0]

private def vecToOp (v : Fin 8 → B) : OpSubalg B a₁ a₃ :=
  v 0 • 1 + v 1 • elS B a₁ a₃ + v 2 • elS B a₁ a₃ ^ 2 + v 3 • elS B a₁ a₃ ^ 3 +
    v 4 • elT B a₁ a₃ + v 5 • (elS B a₁ a₃ * elT B a₁ a₃) +
    v 6 • (elS B a₁ a₃ ^ 2 * elT B a₁ a₃) + v 7 • (elS B a₁ a₃ ^ 3 * elT B a₁ a₃)

private theorem invOf_three_sq_mul_nine : (⅟(3 : B)) ^ 2 * 9 = 1 := by
  linear_combination (⅟(3 : B) * 3 + 1) * invOf_mul_self (3 : B)

private theorem opT_vec0 :
    opT B a₁ a₃ (vec0 B) = ![0, 0, 0, 0, 1, 0, 0, 0] := by
  ext i
  fin_cases i
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]
    linear_combination invOf_three_sq_mul_nine B
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]
  · simp [opT, opT9, opT9Vec, vec0]

private theorem vecToOp_apply_vec0 (v : Fin 8 → B) :
    (vecToOp B a₁ a₃ v : Module.End B (Fin 8 → B)) (vec0 B) = v := by
  ext i
  change ((v 0 • (1 : Module.End B (Fin 8 → B)) + v 1 • opS B a₁ a₃ + v 2 • opS B a₁ a₃ ^ 2 +
    v 3 • opS B a₁ a₃ ^ 3 + v 4 • opT B a₁ a₃ + v 5 • (opS B a₁ a₃ * opT B a₁ a₃) +
    v 6 • (opS B a₁ a₃ ^ 2 * opT B a₁ a₃) + v 7 • (opS B a₁ a₃ ^ 3 * opT B a₁ a₃)) :
      Module.End B (Fin 8 → B)) (vec0 B) i = v i
  simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self, mul_apply_eq_comp,
    pow_succ, pow_zero, one_mul, opT_vec0]
  fin_cases i <;> simp [opS, opSVec, vec0]

private theorem opSubalg_eq_zero_of_apply_vec0 {x : OpSubalg B a₁ a₃}
    (hx : (x : Module.End B (Fin 8 → B)) (vec0 B) = 0) : x = 0 := by
  apply Subtype.ext
  refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
  have hv := vecToOp_apply_vec0 B a₁ a₃ v
  have hcomm : (x * vecToOp B a₁ a₃ v : OpSubalg B a₁ a₃) = vecToOp B a₁ a₃ v * x :=
    mul_comm x _
  have hval := congrArg (fun z : OpSubalg B a₁ a₃ ↦ (z : Module.End B _) (vec0 B) i) hcomm
  dsimp only [Subalgebra.coe_mul] at hval
  rw [mul_apply_eq_comp, mul_apply_eq_comp, hv, hx, map_zero, Pi.zero_apply] at hval
  simpa using hval

private def opR3 : Module.End B (Fin 8 → B) :=
  opS B a₁ a₃ ^ 2 + a₁ • opS B a₁ a₃

private def elR3 : OpSubalg B a₁ a₃ :=
  elS B a₁ a₃ ^ 2 + algebraMap B (OpSubalg B a₁ a₃) a₁ * elS B a₁ a₃

private def elT9 : OpSubalg B a₁ a₃ :=
  (9 : B) • elT B a₁ a₃

private theorem coe_elR3 : (elR3 B a₁ a₃ : Module.End B (Fin 8 → B)) = opR3 B a₁ a₃ := by
  simp [elR3, elS, opR3, Algebra.smul_def]

private theorem coe_elT9 : (elT9 B a₁ a₃ : Module.End B (Fin 8 → B)) = opT9 B a₁ a₃ := by
  have h9 := invOf_three_sq_mul_nine B
  rw [elT9, Subalgebra.coe_smul]
  change (9 : B) • ((⅟(3 : B) ^ 2) • opT9 B a₁ a₃) = opT9 B a₁ a₃
  rw [smul_smul, show (9 : B) * ⅟(3 : B) ^ 2 = 1 by linear_combination h9, one_smul]

private theorem elR_eq_invOf_three_mul_elR3 :
    elR B a₁ a₃ = algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) * elR3 B a₁ a₃ := by
  simp [elR, elR3, Algebra.smul_def]

private theorem elT_eq_invOf_three_sq_mul_elT9 :
    elT B a₁ a₃ = algebraMap B (OpSubalg B a₁ a₃) (⅟(3 : B) ^ 2) * elT9 B a₁ a₃ := by
  have h9 : algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) ^ 2 * 9 = 1 := by
    rw [← map_pow, ← map_ofNat (algebraMap B (OpSubalg B a₁ a₃)) 9, ← map_mul,
      invOf_three_sq_mul_nine, map_one]
  rw [elT9, Algebra.smul_def, map_ofNat, map_pow]
  linear_combination -elT B a₁ a₃ * h9

private theorem algebraMap_opSubalg_three_mul_invOf :
    (3 : OpSubalg B a₁ a₃) * algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) = 1 := by
  rw [← map_ofNat (algebraMap B (OpSubalg B a₁ a₃)) 3, ← map_mul, mul_invOf_self, map_one]

private theorem rel_g₂_opSubalg :
    3 * elR B a₁ a₃ - elS B a₁ a₃ ^ 2 - algebraMap B (OpSubalg B a₁ a₃) a₁ * elS B a₁ a₃ = 0 := by
  rw [elR_eq_invOf_three_mul_elR3, elR3]
  linear_combination
    (elS B a₁ a₃ ^ 2 + algebraMap B (OpSubalg B a₁ a₃) a₁ * elS B a₁ a₃) *
      algebraMap_opSubalg_three_mul_invOf B a₁ a₃

private theorem rel_g₄_opSubalg :
    3 * elR B a₁ a₃ ^ 2 -
      algebraMap B (OpSubalg B a₁ a₃) a₁ * elR B a₁ a₃ * elS B a₁ a₃ -
      algebraMap B (OpSubalg B a₁ a₃) a₃ * elS B a₁ a₃ -
      algebraMap B (OpSubalg B a₁ a₃) a₁ * elT B a₁ a₃ -
      2 * elS B a₁ a₃ * elT B a₁ a₃ = 0 := by
  have hcleared : (3 : B) • elR3 B a₁ a₃ ^ 2 -
      (3 * a₁) • (elR3 B a₁ a₃ * elS B a₁ a₃) -
      (9 * a₃) • elS B a₁ a₃ -
      a₁ • elT9 B a₁ a₃ -
      (2 : B) • (elS B a₁ a₃ * elT9 B a₁ a₃) = 0 := by
    apply opSubalg_eq_zero_of_apply_vec0
    simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Subalgebra.coe_mul, Subalgebra.coe_pow,
      coe_elR3, coe_elT9, elS]
    ext i
    fin_cases i <;>
      simp [opR3, opS, opT9, opSVec, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, vec0, sq] <;>
      ring
  simp only [Algebra.smul_def, map_mul, map_ofNat] at hcleared
  have h3 := algebraMap_opSubalg_three_mul_invOf B a₁ a₃
  rw [elR_eq_invOf_three_mul_elR3, elT_eq_invOf_three_sq_mul_elT9, map_pow]
  linear_combination
    algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) ^ 2 * hcleared +
      (algebraMap B (OpSubalg B a₁ a₃) a₁ * elR3 B a₁ a₃ * elS B a₁ a₃ *
          algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) +
        algebraMap B (OpSubalg B a₁ a₃) a₃ * elS B a₁ a₃ *
          (3 * algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) + 1)) * h3

private theorem rel_g₆_opSubalg :
    elR B a₁ a₃ ^ 3 -
      algebraMap B (OpSubalg B a₁ a₃) a₁ * elR B a₁ a₃ * elT B a₁ a₃ -
      algebraMap B (OpSubalg B a₁ a₃) a₃ * elT B a₁ a₃ -
      elT B a₁ a₃ ^ 2 = 0 := by
  have hcleared : (3 : B) • elR3 B a₁ a₃ ^ 3 -
      (3 * a₁) • (elR3 B a₁ a₃ * elT9 B a₁ a₃) -
      (9 * a₃) • elT9 B a₁ a₃ -
      elT9 B a₁ a₃ ^ 2 = 0 := by
    apply opSubalg_eq_zero_of_apply_vec0
    simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Subalgebra.coe_mul, Subalgebra.coe_pow,
      coe_elR3, coe_elT9]
    ext i
    fin_cases i <;>
      simp [opR3, opS, opT9, opSVec, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, vec0, pow_succ] <;>
      ring
  simp only [Algebra.smul_def, map_mul, map_ofNat] at hcleared
  have h3 := algebraMap_opSubalg_three_mul_invOf B a₁ a₃
  rw [elR_eq_invOf_three_mul_elR3, elT_eq_invOf_three_sq_mul_elT9, map_pow]
  linear_combination
    algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) ^ 4 * hcleared -
      (elR3 B a₁ a₃ ^ 3 -
          algebraMap B (OpSubalg B a₁ a₃) a₁ * elR3 B a₁ a₃ * elT9 B a₁ a₃) *
        algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) ^ 3 * h3 +
      algebraMap B (OpSubalg B a₁ a₃) a₃ * elT9 B a₁ a₃ *
        algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) ^ 2 *
        (3 * algebraMap B (OpSubalg B a₁ a₃) ⅟(3 : B) + 1) * h3

private def rep : ArrowRingOf B a₁ a₃ →ₐ[B] OpSubalg B a₁ a₃ :=
  let hD : IsStrictGamma1ThreeChange
      (algebraMap B (OpSubalg B a₁ a₃) a₁) (algebraMap B (OpSubalg B a₁ a₃) a₃)
      ⟨1, elR B a₁ a₃, elS B a₁ a₃, elT B a₁ a₃⟩ :=
    isStrictGamma1ThreeChange_mk_iff.mpr
      ⟨rel_g₂_opSubalg B a₁ a₃, rel_g₄_opSubalg B a₁ a₃, rel_g₆_opSubalg B a₁ a₃⟩
  AlgHom.mk (lift ⟨(algebraMap B (OpSubalg B a₁ a₃),
    ⟨1, elR B a₁ a₃, elS B a₁ a₃, elT B a₁ a₃⟩), hD⟩) fun b ↦ lift_algebraMap _ b

private theorem rep_s : rep B a₁ a₃ (s B a₁ a₃) = elS B a₁ a₃ :=
  lift_s _

private theorem rep_t : rep B a₁ a₃ (t B a₁ a₃) = elT B a₁ a₃ :=
  lift_t _

private def coordMap : ArrowRingOf B a₁ a₃ →ₗ[B] (Fin 8 → B) where
  toFun y := (rep B a₁ a₃ y : Module.End B (Fin 8 → B)) (vec0 B)
  map_add' x y := by simp [map_add]
  map_smul' b y := by simp [map_smul]

private theorem sum_basisFamily_rep (c : Fin 8 → B) :
    rep B a₁ a₃ (∑ i : Fin 8, c i • basisFamily B a₁ a₃ i) = vecToOp B a₁ a₃ c := by
  simp [Fin.sum_univ_eight, vecToOp, rep_s, rep_t]

private theorem coordMap_sum_basisFamily (c : Fin 8 → B) :
    coordMap B a₁ a₃ (∑ i : Fin 8, c i • basisFamily B a₁ a₃ i) = c := by
  change (rep B a₁ a₃ (∑ i : Fin 8, c i • basisFamily B a₁ a₃ i) : Module.End B _) (vec0 B) = c
  rw [sum_basisFamily_rep, vecToOp_apply_vec0]

private theorem linearIndependent_basisFamily :
    LinearIndependent B (basisFamily B a₁ a₃) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h := congrArg (coordMap B a₁ a₃) hc
  rw [coordMap_sum_basisFamily, map_zero] at h
  exact congrFun h

/-- **Rank-`8` basis of `ArrowRingOf B a₁ a₃`** over `[CommRing B] [Invertible (3 : B)]`:
`![1, s, s², s³, t, s * t, s² * t, s³ * t]`. -/
def basis : Module.Basis (Fin 8) B (ArrowRingOf B a₁ a₃) :=
  Module.Basis.mk (linearIndependent_basisFamily B a₁ a₃) (top_le_span_basisFamily B a₁ a₃)

/-- Coercion of `ArrowRingOf.basis` agrees with `basisFamily`. -/
@[simp]
theorem coe_basis : ⇑(basis B a₁ a₃) = basisFamily B a₁ a₃ :=
  Module.Basis.coe_mk _ _

omit [Invertible (3 : B)] in
/-- Base-change maps each element of `ArrowRingOf.basisFamily` to the corresponding element. -/
@[simp]
theorem mapOfEq_basisFamily {B' : Type*} [CommRing B'] {a₁' a₃' : B'}
    (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') (i : Fin 8) :
    mapOfEq f ha₁ ha₃ (basisFamily B a₁ a₃ i) = basisFamily B' a₁' a₃' i := by
  fin_cases i <;> simp

/-- Base-change maps each element of `ArrowRingOf.basis` to the corresponding basis element. -/
theorem mapOfEq_basis {B' : Type*} [CommRing B'] [Invertible (3 : B')] {a₁' a₃' : B'}
    (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') (i : Fin 8) :
    mapOfEq f ha₁ ha₃ (basis B a₁ a₃ i) = basis B' a₁' a₃' i := by
  simp

/-- `ArrowRingOf B a₁ a₃` is a free `B`-module when `3` is invertible in `B`. -/
instance : Module.Free B (ArrowRingOf B a₁ a₃) :=
  Module.Free.of_basis (basis B a₁ a₃)

/-- `ArrowRingOf B a₁ a₃` is a finitely generated `B`-module when `3` is invertible in `B`. -/
instance : Module.Finite B (ArrowRingOf B a₁ a₃) :=
  Module.Finite.of_basis (basis B a₁ a₃)

/-- Over any commutative ring `B` with `[Invertible (3 : B)]` and `[StrongRankCondition B]`
(in particular any nontrivial commutative ring in which `3` is invertible), `ArrowRingOf B a₁ a₃`
has rank `8` over `B`. -/
theorem finrank_eq_eight [StrongRankCondition B] :
    Module.finrank B (ArrowRingOf B a₁ a₃) = 8 := by
  rw [Module.finrank_eq_card_basis (basis B a₁ a₃), Fintype.card_fin]

/-! ### Exact trace formulas on `ArrowRingOf B a₁ a₃` -/

private theorem equivFun_basis_eq_coordMap :
    (basis B a₁ a₃).equivFun.toLinearMap = coordMap B a₁ a₃ := by
  refine (basis B a₁ a₃).ext fun i ↦ funext fun j ↦ ?_
  have h := congrFun (coordMap_sum_basisFamily B a₁ a₃ (Pi.single i 1)) j
  rw [Fintype.sum_eq_single i (fun k hk ↦ by simp [hk]), Pi.single_eq_same, one_smul,
    ← coe_basis] at h
  rw [LinearEquiv.coe_coe, Module.Basis.equivFun_self, h, Pi.single_apply]
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · simp [hij, hij.symm]

private theorem conj_lmul_eq_rep (y : ArrowRingOf B a₁ a₃) :
    (basis B a₁ a₃).equivFun.conj (Algebra.lmul B (ArrowRingOf B a₁ a₃) y) =
      (rep B a₁ a₃ y : Module.End B (Fin 8 → B)) := by
  refine LinearMap.ext fun v ↦ ?_
  rw [LinearEquiv.conj_apply_apply, ← LinearEquiv.coe_toLinearMap, equivFun_basis_eq_coordMap]
  change (rep B a₁ a₃ (y * (basis B a₁ a₃).equivFun.symm v) : Module.End B (Fin 8 → B)) (vec0 B) =
    (rep B a₁ a₃ y : Module.End B (Fin 8 → B)) v
  rw [map_mul, Subalgebra.coe_mul, mul_apply_eq_comp]
  change (rep B a₁ a₃ y : Module.End B (Fin 8 → B))
      (coordMap B a₁ a₃ ((basis B a₁ a₃).equivFun.symm v)) = _
  rw [← equivFun_basis_eq_coordMap, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

private theorem trace_eq_rep_trace (y : ArrowRingOf B a₁ a₃) :
    Algebra.trace B (ArrowRingOf B a₁ a₃) y =
      LinearMap.trace B (Fin 8 → B) (rep B a₁ a₃ y : Module.End B (Fin 8 → B)) := by
  rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ (basis B a₁ a₃).equivFun, conj_lmul_eq_rep]

/-- `Algebra.trace` of a scalar `algebraMap B _ b` in `ArrowRingOf B a₁ a₃` is `8 * b`. -/
@[simp]
theorem trace_algebraMap (b : B) :
    Algebra.trace B (ArrowRingOf B a₁ a₃) (algebraMap B _ b) = 8 * b := by
  rw [Algebra.trace_algebraMap_of_basis (basis B a₁ a₃), Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]

/-- `Algebra.trace` of `1` in `ArrowRingOf B a₁ a₃` is `8`. -/
@[simp]
theorem trace_one : Algebra.trace B (ArrowRingOf B a₁ a₃) 1 = 8 := by
  simpa using trace_algebraMap B a₁ a₃ 1

/-- `Algebra.trace` of `s` in `ArrowRingOf B a₁ a₃` is `-4a₁`. -/
@[simp]
theorem trace_s : Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃) = -4 * a₁ := by
  rw [trace_eq_rep_trace, rep_s, linearMap_trace_pi_eight]
  simp [elS, opS, opSVec, stdVec]
  ring

/-- `Algebra.trace` of `s²` in `ArrowRingOf B a₁ a₃` is `2a₁²`. -/
@[simp]
theorem trace_s_sq : Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃ ^ 2) = 2 * a₁ ^ 2 := by
  rw [trace_eq_rep_trace, map_pow, rep_s, linearMap_trace_pi_eight]
  simp [elS, opS, opSVec, stdVec, sq]
  ring

/-- `Algebra.trace` of `s³` in `ArrowRingOf B a₁ a₃` is `-a₁³`. -/
@[simp]
theorem trace_s_cube : Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃ ^ 3) = -a₁ ^ 3 := by
  rw [trace_eq_rep_trace, map_pow, rep_s, linearMap_trace_pi_eight]
  simp [elS, opS, opSVec, stdVec, pow_succ]
  ring

/-- `Algebra.trace` of `t` in `ArrowRingOf B a₁ a₃` is `⅟3 * a₁³ - 4a₃`. -/
@[simp]
theorem trace_t :
    Algebra.trace B (ArrowRingOf B a₁ a₃) (t B a₁ a₃) = ⅟(3 : B) * a₁ ^ 3 - 4 * a₃ := by
  rw [trace_eq_rep_trace, rep_t]
  change LinearMap.trace B (Fin 8 → B) ((⅟(3 : B) ^ 2) • opT9 B a₁ a₃) = _
  rw [map_smul, smul_eq_mul, linearMap_trace_pi_eight]
  have ht9 : (opT9 B a₁ a₃ (stdVec B 0) 0 + opT9 B a₁ a₃ (stdVec B 1) 1 +
      opT9 B a₁ a₃ (stdVec B 2) 2 + opT9 B a₁ a₃ (stdVec B 3) 3 +
      opT9 B a₁ a₃ (stdVec B 4) 4 + opT9 B a₁ a₃ (stdVec B 5) 5 +
      opT9 B a₁ a₃ (stdVec B 6) 6 + opT9 B a₁ a₃ (stdVec B 7) 7) = 3 * a₁ ^ 3 - 36 * a₃ := by
    simp [opT9, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, opSVec, stdVec]
    ring
  rw [ht9]
  linear_combination
    (⅟(3 : B) * a₁ ^ 3 - 4 * (⅟(3 : B) * 3 + 1) * a₃) * invOf_mul_self (3 : B)

/-- `Algebra.trace` of `s * t` in `ArrowRingOf B a₁ a₃` is `-2a₁a₃`. -/
@[simp]
theorem trace_s_mul_t :
    Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃ * t B a₁ a₃) = -2 * a₁ * a₃ := by
  rw [trace_eq_rep_trace, map_mul, rep_s, rep_t]
  change LinearMap.trace B (Fin 8 → B) (opS B a₁ a₃ * ((⅟(3 : B) ^ 2) • opT9 B a₁ a₃)) = _
  rw [mul_smul_comm, map_smul, smul_eq_mul, linearMap_trace_pi_eight]
  have htr : ((opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 0) 0 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 1) 1 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 2) 2 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 3) 3 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 4) 4 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 5) 5 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 6) 6 +
      (opS B a₁ a₃ * opT9 B a₁ a₃) (stdVec B 7) 7) = -18 * a₁ * a₃ := by
    simp [opS, opT9, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, opSVec, stdVec]
    ring
  rw [htr]
  linear_combination -2 * a₁ * a₃ * invOf_three_sq_mul_nine B

/-- `Algebra.trace` of `s² * t` in `ArrowRingOf B a₁ a₃` is `-⅟3 * a₁⁵ + 9a₁²a₃`. -/
@[simp]
theorem trace_s_sq_mul_t :
    Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃ ^ 2 * t B a₁ a₃) =
      -⅟(3 : B) * a₁ ^ 5 + 9 * a₁ ^ 2 * a₃ := by
  rw [trace_eq_rep_trace, map_mul, map_pow, rep_s, rep_t]
  change LinearMap.trace B (Fin 8 → B) (opS B a₁ a₃ ^ 2 * ((⅟(3 : B) ^ 2) • opT9 B a₁ a₃)) = _
  rw [mul_smul_comm, map_smul, smul_eq_mul, linearMap_trace_pi_eight]
  have htr : ((opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 0) 0 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 1) 1 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 2) 2 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 3) 3 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 4) 4 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 5) 5 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 6) 6 +
      (opS B a₁ a₃ ^ 2 * opT9 B a₁ a₃) (stdVec B 7) 7) = -3 * a₁ ^ 5 + 81 * a₁ ^ 2 * a₃ := by
    simp [opS, opT9, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, opSVec, stdVec, sq]
    ring
  rw [htr]
  linear_combination
    (-⅟(3 : B) * a₁ ^ 5 + 9 * (⅟(3 : B) * 3 + 1) * a₁ ^ 2 * a₃) * invOf_mul_self (3 : B)

/-- `Algebra.trace` of `s³ * t` in `ArrowRingOf B a₁ a₃` is `⅟3 * a₁⁶ - 7a₁³a₃ - 27a₃²`. -/
@[simp]
theorem trace_s_cube_mul_t :
    Algebra.trace B (ArrowRingOf B a₁ a₃) (s B a₁ a₃ ^ 3 * t B a₁ a₃) =
      ⅟(3 : B) * a₁ ^ 6 - 7 * a₁ ^ 3 * a₃ - 27 * a₃ ^ 2 := by
  rw [trace_eq_rep_trace, map_mul, map_pow, rep_s, rep_t]
  change LinearMap.trace B (Fin 8 → B) (opS B a₁ a₃ ^ 3 * ((⅟(3 : B) ^ 2) • opT9 B a₁ a₃)) = _
  rw [mul_smul_comm, map_smul, smul_eq_mul, linearMap_trace_pi_eight]
  have htr : ((opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 0) 0 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 1) 1 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 2) 2 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 3) 3 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 4) 4 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 5) 5 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 6) 6 +
      (opS B a₁ a₃ ^ 3 * opT9 B a₁ a₃) (stdVec B 7) 7) =
      3 * a₁ ^ 6 - 63 * a₁ ^ 3 * a₃ - 243 * a₃ ^ 2 := by
    simp [opS, opT9, opT9Vec, t9Col7, t9Col6, t9Col5, t9Col4, opSVec, stdVec, pow_succ]
    ring
  rw [htr]
  linear_combination
    (⅟(3 : B) * a₁ ^ 6 - (7 * a₁ ^ 3 * a₃ + 27 * a₃ ^ 2) * (⅟(3 : B) * 3 + 1)) *
      invOf_mul_self (3 : B)

/-- **Base-change compatibility of `Algebra.trace`** for `ArrowRingOf`. -/
theorem trace_mapOfEq {B' : Type*} [CommRing B'] [Invertible (3 : B')] {a₁' a₃' : B'}
    (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') (y : ArrowRingOf B a₁ a₃) :
    Algebra.trace B' (ArrowRingOf B' a₁' a₃') (mapOfEq f ha₁ ha₃ y) =
      f (Algebra.trace B (ArrowRingOf B a₁ a₃) y) := by
  have hf3 : f ⅟(3 : B) = ⅟(3 : B') := by
    have h1 : f ⅟(3 : B) * 3 = 1 := by
      rw [← map_ofNat f 3, ← map_mul, invOf_mul_self, map_one]
    linear_combination ⅟(3 : B') * h1 - f ⅟(3 : B) * invOf_mul_self (3 : B')
  rw [← (basis B a₁ a₃).sum_repr y]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_lhs =>
    rw [smul_eq_algebraMap_mul, map_mul, mapOfEq_algebraMap, mapOfEq_basis,
      ← smul_eq_algebraMap_mul]
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  fin_cases i <;>
    simp [hf3, ha₁, ha₃, map_ofNat]

/-- Base-change compatibility of `Algebra.trace` along `ArrowRingOf.map f`. -/
theorem trace_map {B' : Type*} [CommRing B'] [Invertible (3 : B')] (f : B →+* B')
    (y : ArrowRingOf B a₁ a₃) :
    Algebra.trace B' (ArrowRingOf B' (f a₁) (f a₃)) (map f y) =
      f (Algebra.trace B (ArrowRingOf B a₁ a₃) y) :=
  trace_mapOfEq B a₁ a₃ f rfl rfl y

end Basis

end ArrowRingOf

/-! ### Specialization to the universal `Γ₁(3)` Hopf algebroid `(BaseRing R, ArrowRing R)` -/

section UniversalBasis

private abbrev invertibleThreeOfRingHom {A B : Type*} [CommRing A] [CommRing B]
    [Invertible (3 : A)] (f : A →+* B) : Invertible (3 : B) :=
  (Invertible.map f (3 : A)).copy 3 (map_ofNat f 3).symm

variable (R : Type*) [CommRing R] [Invertible (3 : R)]

/-- When `3` is invertible in `R`, `ArrowRing R` has the explicit rank-`8` `BaseRing R`-basis
`![1, s, s², s³, t, s * t, s² * t, s³ * t]`. -/
def arrowRingBasis : Module.Basis (Fin 8) (BaseRing R) (ArrowRing R) :=
  letI := invertibleThreeOfRingHom (algebraMap R (BaseRing R))
  ArrowRingOf.basis (BaseRing R) (a₁ R) (a₃ R)

/-- `ArrowRing R` is a free `BaseRing R`-module when `3` is invertible in `R`. -/
instance : Module.Free (BaseRing R) (ArrowRing R) :=
  Module.Free.of_basis (arrowRingBasis R)

/-- `ArrowRing R` is a finitely generated `BaseRing R`-module when `3` is invertible in `R`. -/
instance : Module.Finite (BaseRing R) (ArrowRing R) :=
  Module.Finite.of_basis (arrowRingBasis R)

/-- Over any nontrivial commutative ring `R` in which `3` is invertible, `ArrowRing R` has rank
`8` over `BaseRing R`. -/
theorem finrank_arrowRing_eq_eight [Nontrivial R] :
    Module.finrank (BaseRing R) (ArrowRing R) = 8 := by
  rw [Module.finrank_eq_card_basis (arrowRingBasis R), Fintype.card_fin]

/-- **Hopf-algebroid trace identity**: tracing `coproduct R y` along the left `ArrowRing R`-algebra
structure of `TensorSquare R` equals `η_L (trace y)`. -/
theorem trace_coproduct (y : ArrowRing R) :
    Algebra.trace (ArrowRing R) (TensorSquare R) (coproduct R y) =
      algebraMap (BaseRing R) (ArrowRing R) (Algebra.trace (BaseRing R) (ArrowRing R) y) := by
  let _ := invertibleThreeOfRingHom (algebraMap R (BaseRing R))
  let _ := invertibleThreeOfRingHom (algebraMap (BaseRing R) (ArrowRing R))
  rw [coproduct_eq_shearEquiv_comp_map, RingHom.comp_apply]
  change Algebra.trace (ArrowRing R) (TensorSquare R)
      (ArrowRingOf.shearEquiv _ _ _ (ArrowRingOf.map (algebraMap (BaseRing R) (ArrowRing R)) y)) = _
  rw [Algebra.trace_eq_of_algEquiv, ArrowRingOf.trace_map]

end UniversalBasis

end TauCeti.Gamma1ThreeHopfAlgebroid
