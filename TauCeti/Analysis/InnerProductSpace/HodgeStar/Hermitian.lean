/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Hermitian part of a two-form and its extreme eigenvalues

Let `V` be an oriented real inner product space of dimension four and `J` an orthogonal almost
complex structure inducing the orientation, with Kähler two-vector `ω`
(`TauCeti.AlmostComplexStructure.kahlerForm`), so that `‖ω‖² = 2`. A two-vector `F ∈ ⋀² V`
represents the two-form `F(v, w) = ⟪F, v ∧ w⟫`. Its **Hermitian part** with respect to `J` is the
symmetric bilinear form

`B(v, w) = (F(v, J w) + F(w, J v)) / 2`,  `B(v, v) = F(v, J v)`.

For the Kähler form itself `B = ⟪·, ·⟫`, since `⟪v, w⟫ = ω(v, J w)`. Split `F` into its self-dual
part `F⁺`, a self-dual form with `⋆F⁺ = F⁺`, and its anti-self-dual part `F⁻`, with `⋆F⁻ = -F⁻`.
This file computes the Hermitian part of each summand:

* a self-dual form `η` has Hermitian part `(⟪ω, η⟫ / 2) ⟪·, ·⟫`. In particular the self-dual forms
  orthogonal to `ω`, the anti-`J`-invariant ones, have Hermitian part zero;
* an anti-self-dual form `μ` has Hermitian part with extreme eigenvalues `±‖μ‖ / √2`.

Consequently, with `c = ⟪ω, F⟫ / 2`, the smallest eigenvalue of the Hermitian part of `F` is
`c - ‖F⁻‖ / √2` and the largest is `c + ‖F⁻‖ / √2`: both are attained on unit vectors. In
particular a lower bound `B ≥ -C ⟪·, ·⟫` bounds the anti-self-dual part,
`‖F⁻‖ ≤ √2 (c + C)`.

For the curvature `F = iF_a` of a connection on a symplectic four-manifold, `c` is the component of
the curvature along `ω`, which the Seiberg–Witten curvature equation determines. A lower bound on
the Hermitian part of the curvature therefore controls the anti-self-dual curvature pointwise; this
is how Taubes bounds `|F_a⁻|` in his analysis of the Seiberg–Witten equations for large
perturbation parameter.

The bound for an anti-self-dual form uses only that it is orthogonal to `ω`, and needs only an
orthogonal `J`. The other statements take a positively oriented orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one, as in
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler`. That the bound for anti-self-dual forms
is attained is an explicit computation in the coordinates of such a frame.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`: `ω` is orthogonal to every anti-self-dual form.
* `inner_ιMulti_add_inner_ιMulti_of_hodgeStar_eq_self`: for self-dual `η`,
  `η(v, J w) + η(w, J v) = ⟪ω, η⟫ ⟪v, w⟫`.
* `inner_ιMulti_of_hodgeStar_eq_self`: for self-dual `η`, `η(v, J v) = ⟪ω, η⟫ / 2 · ‖v‖²`.
* `abs_inner_ιMulti_le_of_inner_kahlerForm_eq_zero`: if `⟪ω, μ⟫ = 0`, then
  `|μ(v, J v)| ≤ ‖μ‖ / √2 · ‖v‖²`.
* `exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg`: for anti-self-dual `μ` the lower bound
  `-‖μ‖ / √2` is attained on a unit vector.
* `inner_ιMulti_eq_mul_add_inner_ιMulti`: `F(v, J v) = ⟪ω, F⟫ / 2 · ‖v‖² + F⁻(v, J v)`.
* `abs_inner_ιMulti_sub_le`: `|F(v, J v) - ⟪ω, F⟫ / 2 · ‖v‖²| ≤ ‖F⁻‖ / √2 · ‖v‖²`.
* `isLeast_inner_ιMulti_image_sphere`, `isGreatest_inner_ιMulti_image_sphere`: the extreme
  eigenvalues `⟪ω, F⟫ / 2 ∓ ‖F⁻‖ / √2` of the Hermitian part of `F`.
* `norm_le_of_forall_le_inner_ιMulti`: a lower bound on the Hermitian part bounds `‖F⁻‖`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990),
  Chapter 1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fact (finrank ℝ V = 4)]

namespace TauCeti.AlmostComplexStructure

/-! ### Anti-self-dual forms orthogonal to the Kähler form -/

section Orthogonal

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

omit [Fact (finrank ℝ V = 4)] in
/-- `‖v ∧ J v‖ = ‖v‖²` for an orthogonal `J`, since `J v` is orthogonal to `v` and has the same
norm. -/
private theorem norm_ιMulti_sq (v : V) : ‖ιMulti ℝ 2 ![v, J v]‖ ^ 2 = ‖v‖ ^ 4 := by
  have h0 : ⟪v, J v⟫ = 0 := by
    have := inner_apply_left hJ v v
    rw [real_inner_comm] at this
    linarith
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_two, hJ, h0, real_inner_self_eq_norm_sq]
  ring

/-- **The Hermitian part of a form orthogonal to `ω` is bounded by `‖μ‖ / √2`**: if
`⟪ω, μ⟫ = 0`, then `|μ(v, J v)| ≤ ‖μ‖ / √2 · ‖v‖²`. This applies to every anti-self-dual `μ`
(`inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`), for which the bound is sharp
(`exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg`). -/
theorem abs_inner_ιMulti_le_of_inner_kahlerForm_eq_zero {μ : ⋀[ℝ]^2 V}
    (hμ : ⟪J.kahlerForm, μ⟫ = 0) (v : V) :
    |⟪μ, ιMulti ℝ 2 ![v, J v]⟫| ≤ ‖μ‖ / √2 * ‖v‖ ^ 2 := by
  -- Pair `μ` with `y = 2 (v ∧ J v) - ‖v‖² ω`, which has the same pairing as `2 (v ∧ J v)` and
  -- norm `√2 ‖v‖²`.
  set x := ιMulti ℝ 2 ![v, J v]
  set y := (2 : ℝ) • x - ‖v‖ ^ 2 • J.kahlerForm
  have hxω : ⟪x, J.kahlerForm⟫ = ‖v‖ ^ 2 := by
    rw [real_inner_comm, inner_kahlerForm_ιMulti hJ, hJ, real_inner_self_eq_norm_sq]
  have hω : ‖J.kahlerForm‖ ^ 2 = 2 := by
    rw [norm_kahlerForm_sq hJ, (Fact.out : finrank ℝ V = 4)]
    norm_num
  have hx : ‖x‖ ^ 2 = ‖v‖ ^ 4 := norm_ιMulti_sq hJ v
  have hy : ‖y‖ ^ 2 = (√2 * ‖v‖ ^ 2) ^ 2 := by
    simp only [y, norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, abs_two, abs_pow, sq_abs, mul_pow, hxω, hx, hω, Real.sq_sqrt zero_le_two]
    ring
  have hy' : ‖y‖ = √2 * ‖v‖ ^ 2 :=
    (pow_left_inj₀ (norm_nonneg y) (by positivity) two_ne_zero).1 hy
  have hμy : ⟪μ, y⟫ = 2 * ⟪μ, x⟫ := by
    have hμω : ⟪μ, J.kahlerForm⟫ = 0 := by rw [real_inner_comm]; exact hμ
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hμω]
    ring
  have hle := abs_real_inner_le_norm μ y
  rw [hμy, hy', abs_mul, abs_two] at hle
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  nlinarith [abs_nonneg ⟪μ, x⟫, norm_nonneg μ, sq_nonneg ‖v‖]

end Orthogonal

/-! ### Self-dual and anti-self-dual forms in a unitary frame -/

section Frame

variable {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {e : OrthonormalBasis (Fin 4) ℝ V} (he : e.toBasis.orientation = o)

include hkl he

variable {J : AlmostComplexStructure V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

include h₀ h₂ in
/-- **The Kähler form is orthogonal to the anti-self-dual forms**: `⟪ω, μ⟫ = 0` when
`⋆μ = -μ`, since `ω` is self-dual for the complex orientation. -/
theorem inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ) :
    ⟪J.kahlerForm, μ⟫ = 0 := by
  have h := o.inner_hodgeStar_right_of_hodgeStar_eq_neg even_two hkl hμ J.kahlerForm
  rw [hodgeStar_kahlerForm h₀ h₂ hkl he, real_inner_comm] at h
  linarith

include h₀ h₂ in
/-- **The Hermitian part of a self-dual form**: for self-dual `η`,
`η(v, J w) + η(w, J v) = ⟪ω, η⟫ ⟪v, w⟫`, so the Hermitian part of `η` is `⟪ω, η⟫ / 2` times the
inner product. In particular the self-dual forms orthogonal to `ω` have Hermitian part zero. -/
theorem inner_ιMulti_add_inner_ιMulti_of_hodgeStar_eq_self {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = η) (v w : V) :
    ⟪η, ιMulti ℝ 2 ![v, J w]⟫ + ⟪η, ιMulti ℝ 2 ![w, J v]⟫ = ⟪J.kahlerForm, η⟫ * ⟪v, w⟫ := by
  -- The self-dual part of `z = v ∧ J w - J v ∧ w` is `⟪v, w⟫ ω`, and `η` only sees that part.
  set z := ιMulti ℝ 2 ![v, J w] - ιMulti ℝ 2 ![J v, w]
  have hswap : ιMulti ℝ 2 ![J v, w] = -ιMulti ℝ 2 ![w, J v] := by
    rw [← (ιMulti ℝ 2).map_swap ![w, J v] zero_ne_one, Matrix.cons_cons_comp_swap_zero_one]
  have hstar := o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl hη z
  have h := congrArg (⟪η, ·⟫) (ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he v w)
  simp only [inner_add_right, real_inner_smul_right] at h
  have hz : ⟪η, z⟫ = ⟪η, ιMulti ℝ 2 ![v, J w]⟫ + ⟪η, ιMulti ℝ 2 ![w, J v]⟫ := by
    rw [inner_sub_right, hswap, inner_neg_right, sub_neg_eq_add]
  rw [← hz, real_inner_comm η J.kahlerForm]
  linarith

include h₀ h₂ in
/-- **The quadratic form of a self-dual form**: for self-dual `η`,
`η(v, J v) = ⟪ω, η⟫ / 2 · ‖v‖²`. -/
theorem inner_ιMulti_of_hodgeStar_eq_self {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η) (v : V) :
    ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = ⟪J.kahlerForm, η⟫ / 2 * ‖v‖ ^ 2 := by
  have h := inner_ιMulti_add_inner_ιMulti_of_hodgeStar_eq_self hkl he h₀ h₂ hη v v
  rw [real_inner_self_eq_norm_sq] at h
  linarith

/-! #### Anti-self-dual forms in a unitary frame -/

include h₀ h₂ in
/-- The quadratic form `μ(v, J v)` of an anti-self-dual form `μ` with coordinates `A, B, C` along
`e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃` is
`A (x₀² + x₁² - x₂² - x₃²) + 2 B (x₁ x₂ - x₀ x₃) + 2 C (x₀ x₂ + x₁ x₃)` in the coordinates `x`
of `v`. -/
private theorem inner_ιMulti_eq_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) (v : V) :
    ⟪μ, ιMulti ℝ 2 ![v, J v]⟫ =
      ⟪μ, ιMulti ℝ 2 ![e 0, e 1]⟫ *
          (e.repr v 0 ^ 2 + e.repr v 1 ^ 2 - e.repr v 2 ^ 2 - e.repr v 3 ^ 2) +
        2 * ⟪μ, ιMulti ℝ 2 ![e 0, e 2]⟫ * (e.repr v 1 * e.repr v 2 - e.repr v 0 * e.repr v 3) +
        2 * ⟪μ, ιMulti ℝ 2 ![e 0, e 3]⟫ * (e.repr v 0 * e.repr v 2 + e.repr v 1 * e.repr v 3) := by
  obtain ⟨h23, h13, h12⟩ := o.inner_ιMulti_two_of_hodgeStar_eq_neg hkl he hμ
  rw [e.inner_ιMulti_two_eq_sum, h23, h13, h12]
  simp only [repr_apply h₀ h₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

include h₀ h₂ in
/-- **The bound for anti-self-dual forms is attained**: for anti-self-dual `μ` there is a unit
vector `v` with `μ(v, J v) = -‖μ‖ / √2`. -/
theorem exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) :
    ∃ v : V, ‖v‖ = 1 ∧ ⟪μ, ιMulti ℝ 2 ![v, J v]⟫ = -(‖μ‖ / √2) := by
  -- In the frame, `μ(v, J v)` is a quadratic form in the coordinates of `v` whose smallest
  -- eigenvalue is `-s`, `s = √(A² + B² + C²)`, for the coordinates `A, B, C` of `μ`.
  have hval := inner_ιMulti_eq_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ
  have hnorm := o.norm_sq_of_hodgeStar_eq_neg hkl he hμ
  set A := ⟪μ, ιMulti ℝ 2 ![e 0, e 1]⟫
  set B := ⟪μ, ιMulti ℝ 2 ![e 0, e 2]⟫
  set C := ⟪μ, ιMulti ℝ 2 ![e 0, e 3]⟫
  set s := ‖μ‖ / √2
  have hs₀ : 0 ≤ s := by positivity
  have hs : s ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two, hnorm]
    ring
  have hAs : A ≤ s := by
    rw [← Real.sqrt_sq hs₀, hs]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg B, sq_nonneg C])
  clear_value s A B C
  rcases hAs.lt_or_eq with hlt | heq
  · -- The vector `w = (s - A) e₀ - C e₂ + B e₃`, normalized, attains `-s`.
    set w := (s - A) • e 0 - C • e 2 + B • e 3
    have hw (i : Fin 4) : e.repr w i = ![s - A, 0, -C, B] i := by
      fin_cases i <;> simp [w, OrthonormalBasis.repr_self]
    have hw₂ : ‖w‖ ^ 2 = 2 * s * (s - A) := by
      rw [← e.repr.norm_map, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
      simp only [hw, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination -hs
    have hspos : 0 < s := by
      rcases hs₀.lt_or_eq with h | h
      · exact h
      · nlinarith [sq_nonneg B, sq_nonneg C]
    have hwpos : 0 < ‖w‖ := by
      have h2 : 0 < ‖w‖ ^ 2 := by rw [hw₂]; nlinarith
      exact lt_of_le_of_ne (norm_nonneg w) fun h ↦ by rw [← h] at h2; simp at h2
    refine ⟨‖w‖⁻¹ • w, norm_smul_inv_norm (norm_ne_zero_iff.1 hwpos.ne'), ?_⟩
    rw [hval]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, hw, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    have hinv : ‖w‖⁻¹ ^ 2 * (2 * s * (s - A)) = 1 := by
      rw [← hw₂, inv_pow, inv_mul_cancel₀ (by positivity)]
    linear_combination (‖w‖⁻¹ ^ 2 * (2 * s - A)) * hs - s * hinv
  · -- If `A = s`, then `B = C = 0`, and `e₂` attains `-s`.
    refine ⟨e 2, e.orthonormal.1 2, ?_⟩
    rw [hval]
    simp [OrthonormalBasis.repr_self, heq]

/-! ### The extreme eigenvalues of the Hermitian part -/

include h₀ h₂ in
/-- **The Hermitian part of a two-form splits along `Λ⁺ ⊕ Λ⁻`**: with `F⁻ = μ` the
anti-self-dual part of `F`, `F(v, J v) = ⟪ω, F⟫ / 2 · ‖v‖² + F⁻(v, J v)`. -/
theorem inner_ιMulti_eq_mul_add_inner_ιMulti {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ = ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 + ⟪μ, ιMulti ℝ 2 ![v, J v]⟫ := by
  have h := inner_ιMulti_of_hodgeStar_eq_self hkl he h₀ h₂ hF v
  rw [inner_sub_left, inner_sub_right, inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ,
    sub_zero] at h
  linarith

include h₀ h₂ in
/-- **The Hermitian part of `F` is bounded by its extreme eigenvalues**: with `F⁻ = μ` the
anti-self-dual part of `F`, `|F(v, J v) - ⟪ω, F⟫ / 2 · ‖v‖²| ≤ ‖F⁻‖ / √2 · ‖v‖²`. -/
theorem abs_inner_ιMulti_sub_le {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) (v : V) :
    |⟪F, ιMulti ℝ 2 ![v, J v]⟫ - ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2| ≤ ‖μ‖ / √2 * ‖v‖ ^ 2 := by
  rw [inner_ιMulti_eq_mul_add_inner_ιMulti hkl he h₀ h₂ hμ hF, add_sub_cancel_left]
  exact abs_inner_ιMulti_le_of_inner_kahlerForm_eq_zero
    (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ) v

include h₀ h₂ in
/-- **The smallest eigenvalue of the Hermitian part of a two-form**: with `F⁻ = μ` the
anti-self-dual part of `F`, the least value of `F(v, J v)` on unit vectors is
`⟪ω, F⟫ / 2 - ‖F⁻‖ / √2`. -/
theorem isLeast_inner_ιMulti_image_sphere {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    IsLeast ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 - ‖μ‖ / √2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, hμv⟩ := exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    simp only [inner_ιMulti_eq_mul_add_inner_ιMulti hkl he h₀ h₂ hμ hF, hμv, hv]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    have h := abs_inner_ιMulti_sub_le hkl he h₀ h₂ hμ hF v
    rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, mul_one] at h
    linarith [neg_abs_le (⟪F, ιMulti ℝ 2 ![v, J v]⟫ - ⟪J.kahlerForm, F⟫ / 2)]

include h₀ h₂ in
/-- **The largest eigenvalue of the Hermitian part of a two-form**: with `F⁻ = μ` the
anti-self-dual part of `F`, the greatest value of `F(v, J v)` on unit vectors is
`⟪ω, F⟫ / 2 + ‖F⁻‖ / √2`. -/
theorem isGreatest_inner_ιMulti_image_sphere {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    IsGreatest ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 + ‖μ‖ / √2) := by
  refine ⟨?_, ?_⟩
  · -- The vector attaining the least value for `-μ` attains the greatest value for `μ`.
    have hμ' : o.hodgeStar hkl (-μ) = -(-μ) := by rw [map_neg, hμ]
    obtain ⟨v, hv, hμv⟩ := exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ'
    rw [inner_neg_left, norm_neg, neg_inj] at hμv
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    simp only [inner_ιMulti_eq_mul_add_inner_ιMulti hkl he h₀ h₂ hμ hF, hμv, hv]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    have h := abs_inner_ιMulti_sub_le hkl he h₀ h₂ hμ hF v
    rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, mul_one] at h
    linarith [le_abs_self (⟪F, ιMulti ℝ 2 ![v, J v]⟫ - ⟪J.kahlerForm, F⟫ / 2)]

include h₀ h₂ in
/-- **A lower bound on the Hermitian part bounds the anti-self-dual part**: if
`F(v, J v) ≥ -K ‖v‖²` for every `v`, then `‖F⁻‖ ≤ √2 (⟪ω, F⟫ / 2 + K)`, where `F⁻ = μ` is the
anti-self-dual part of `F`. -/
theorem norm_le_of_forall_le_inner_ιMulti {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) {K : ℝ}
    (hK : ∀ v, -K * ‖v‖ ^ 2 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) :
    ‖μ‖ ≤ √2 * (⟪J.kahlerForm, F⟫ / 2 + K) := by
  obtain ⟨v, hv, hμv⟩ := exists_inner_ιMulti_eq_neg_of_hodgeStar_eq_neg hkl he h₀ h₂ hμ
  have h := hK v
  rw [inner_ιMulti_eq_mul_add_inner_ιMulti hkl he h₀ h₂ hμ hF, hμv, hv] at h
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : ‖μ‖ = √2 * (‖μ‖ / √2) := by field_simp
  rw [hs]
  gcongr
  linarith

end Frame

end TauCeti.AlmostComplexStructure
