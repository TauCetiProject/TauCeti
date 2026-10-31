/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.PiLex
public import TauCeti.Algebra.BigOperators.Pi
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus

/-!
# The Veronese map of projective space

The monomials of degree `d` in `N` variables are indexed by the exponent vectors
`α : Fin N → ℕ` with `∑ i, α i = d`. Enumerating them in lexicographic order identifies them
with `Fin (veroneseDim N d)`, and the vector `veroneseMonomials d v` of all degree-`d`
monomials `∏ i, v i ^ α i` of a vector `v : Fin N → K` defines, over any field `K`, the
**Veronese map**

`Projectivization.veronese K d : ℙ K (Fin N → K) → ℙ K (Fin (veroneseDim N d) → K)`.

For `d ≠ 0` it is injective. Over `ℂ`, its image is the common zero locus of the quadratic
binomials `y_α y_β - y_γ y_δ` with `α + β = γ + δ`: the image is cut out by these equations as a
reduced zero set.

A homogeneous polynomial `p` of degree `d` is the linear form `veroneseLinearForm d p` in the
degree-`d` monomials, with the coefficients of `p` as coefficients. Hence the Veronese map pulls
the hyperplane cut out by this linear form back to the hypersurface `p = 0`, and the zero locus
of a family of degree-`d` equations is the preimage of a linear section of the image.

## Main definitions

* `TauCeti.veroneseDim N d`: the number of monomials of degree `d` in `N` variables.
* `TauCeti.veroneseExponent N d k`: the `k`-th exponent vector of degree `d`, in lexicographic
  order.
* `TauCeti.veroneseMonomials d v`: the vector of degree-`d` monomials of `v`.
* `Projectivization.veronese K d`: the degree-`d` Veronese map.
* `TauCeti.veroneseRelation R N d q`: the quadratic binomial `y_a y_b - y_c y_e` attached to a
  quadruple `q = ((a, b), (c, e))` of indices of exponent vectors with `α_a + α_b = α_c + α_e`.
* `TauCeti.veroneseLinearForm d p`: a polynomial of degree `d` as a linear form in the monomials.

## Main results

* `TauCeti.veroneseExponent_strictMono`: the exponent vectors are enumerated in lexicographic
  order.
* `Projectivization.veronese_mk`: the Veronese map in homogeneous coordinates.
* `TauCeti.eval_veroneseRelation`, `TauCeti.eval_veroneseLinearForm`,
  `TauCeti.coeff_single_veroneseLinearForm`: evaluating the quadratic binomials and the linear
  forms, and the coefficients of the linear forms.
* `Projectivization.veronese_injective`: the Veronese map of positive degree is injective.
* `Projectivization.range_veronese`: over `ℂ`, the image of the Veronese map of positive degree is
  the zero locus of the quadratic binomials.
* `Projectivization.preimage_veronese_complexProjectiveZeroLocus_veroneseLinearForm`: the
  Veronese map pulls back the linear sections `veroneseLinearForm d (p i) = 0` to the zero locus
  of the homogeneous degree-`d` equations `p i`.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4 (Veronese maps and the quadrics cutting out their images).
-/

public section

open MvPolynomial Finset
open scoped LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ}

/-! ### Exponent vectors of degree `d` -/

/-- The number of monomials of degree `d` in `N` variables, that is the number of exponent
vectors `α : Fin N → ℕ` with `∑ i, α i = d`. -/
def veroneseDim (N d : ℕ) : ℕ :=
  (Nat.antidiagonalTuple N d).card

/-- The exponent vectors of degree `d` in `N` variables, enumerated in increasing lexicographic
order. -/
noncomputable def veroneseExponentEquiv (N d : ℕ) :
    Fin (veroneseDim N d) ≃ {α : Fin N → ℕ // ∑ i, α i = d} :=
  (((Nat.antidiagonalTuple N d).map toLex.toEmbedding).orderIsoOfFin
      (card_map _)).toEquiv.trans
    { toFun α := ⟨ofLex α.1, by
        obtain ⟨β, hβ, h⟩ := mem_map.mp α.2
        simpa [← h] using Nat.mem_antidiagonalTuple.mp hβ⟩
      invFun α := ⟨toLex α.1, mem_map_of_mem _ (Nat.mem_antidiagonalTuple.mpr α.2)⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The `k`-th exponent vector of degree `d` in `N` variables, in lexicographic order. -/
noncomputable def veroneseExponent (N d : ℕ) (k : Fin (veroneseDim N d)) : Fin N → ℕ :=
  (veroneseExponentEquiv N d k).1

/-- The exponent vector enumerated by `veroneseExponentEquiv` is `veroneseExponent`. -/
@[simp]
theorem veroneseExponentEquiv_apply {d : ℕ} (k : Fin (veroneseDim N d)) :
    (veroneseExponentEquiv N d k : Fin N → ℕ) = veroneseExponent N d k :=
  (rfl)

/-- Every enumerated exponent vector has degree `d`. -/
@[simp]
theorem sum_veroneseExponent (d : ℕ) (k : Fin (veroneseDim N d)) :
    ∑ i, veroneseExponent N d k i = d :=
  (veroneseExponentEquiv N d k).2

/-- Distinct indices enumerate distinct exponent vectors. -/
theorem veroneseExponent_injective (d : ℕ) : Function.Injective (veroneseExponent N d) :=
  Subtype.val_injective.comp (veroneseExponentEquiv N d).injective

/-- The index of an exponent vector of degree `d` is recovered by `veroneseExponentEquiv`. -/
@[simp]
theorem veroneseExponent_veroneseExponentEquiv_symm {d : ℕ}
    (α : {α : Fin N → ℕ // ∑ i, α i = d}) :
    veroneseExponent N d ((veroneseExponentEquiv N d).symm α) = α := by
  rw [veroneseExponent, Equiv.apply_symm_apply]

/-- The enumeration of exponent vectors is increasing for the lexicographic order. -/
theorem veroneseExponent_strictMono (N d : ℕ) :
    StrictMono fun k ↦ toLex (veroneseExponent N d k) :=
  fun _ _ h ↦ ((Nat.antidiagonalTuple N d).map toLex.toEmbedding).orderIsoOfFin
    (card_map _) |>.strictMono h

/-! ### The vector of monomials -/

section Monomials

variable {K : Type*} [CommSemiring K]

/-- The vector of all monomials `∏ i, v i ^ α i` of degree `d` in the coordinates of `v`,
indexed by the exponent vectors in lexicographic order. -/
noncomputable def veroneseMonomials (d : ℕ) (v : Fin N → K) : Fin (veroneseDim N d) → K :=
  fun k ↦ ∏ i, v i ^ veroneseExponent N d k i

@[simp]
theorem veroneseMonomials_apply (d : ℕ) (v : Fin N → K) (k : Fin (veroneseDim N d)) :
    veroneseMonomials d v k = ∏ i, v i ^ veroneseExponent N d k i :=
  (rfl)

/-- The vector of monomials of degree `d` is homogeneous of degree `d`. -/
theorem veroneseMonomials_smul (d : ℕ) (c : K) (v : Fin N → K) :
    veroneseMonomials d (c • v) = c ^ d • veroneseMonomials d v := by
  ext k
  simp [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]

end Monomials

/-- The vector of monomials of degree `d` of a nonzero vector is nonzero: it contains the pure
powers `v i ^ d`. -/
theorem veroneseMonomials_ne_zero {K : Type*} [CommSemiring K] [NoZeroDivisors K] (d : ℕ)
    {v : Fin N → K} (hv : v ≠ 0) : veroneseMonomials d v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  refine Function.ne_iff.mpr
    ⟨(veroneseExponentEquiv N d).symm ⟨Pi.single i d, Fintype.sum_pi_single' i d⟩, ?_⟩
  simpa [Fintype.prod_pow_pi_single] using pow_ne_zero d hi

/-! ### Relations among monomials -/

/-- The quadruples `((a, b), (c, e))` of indices of exponent vectors of degree `d` with
`α_a + α_b = α_c + α_e`, indexing the quadratic relations among the monomials. -/
abbrev VeroneseRelationIndex (N d : ℕ) : Type :=
  {q : (Fin (veroneseDim N d) × Fin (veroneseDim N d)) ×
      (Fin (veroneseDim N d) × Fin (veroneseDim N d)) //
    veroneseExponent N d q.1.1 + veroneseExponent N d q.1.2 =
      veroneseExponent N d q.2.1 + veroneseExponent N d q.2.2}

/-- The quadratic binomial `y_a y_b - y_c y_e` for a quadruple `((a, b), (c, e))` of indices of
exponent vectors of degree `d` with `α_a + α_b = α_c + α_e`. These binomials vanish on the vector
of monomials of degree `d` of every vector. -/
noncomputable def veroneseRelation (R : Type*) [CommRing R] (N d : ℕ)
    (q : VeroneseRelationIndex N d) : MvPolynomial (Fin (veroneseDim N d)) R :=
  X q.1.1.1 * X q.1.1.2 - X q.1.2.1 * X q.1.2.2

/-- The relations among the monomials are homogeneous quadrics. -/
theorem isHomogeneous_veroneseRelation (R : Type*) [CommRing R] (N d : ℕ)
    (q : VeroneseRelationIndex N d) : (veroneseRelation R N d q).IsHomogeneous 2 :=
  ((isHomogeneous_X R _).mul (isHomogeneous_X R _)).sub
    ((isHomogeneous_X R _).mul (isHomogeneous_X R _))

/-- The value of the binomial `y_a y_b - y_c y_e` at a point `y`. -/
@[simp]
theorem eval_veroneseRelation {R : Type*} [CommRing R] {d : ℕ} (q : VeroneseRelationIndex N d)
    (y : Fin (veroneseDim N d) → R) :
    eval y (veroneseRelation R N d q) = y q.1.1.1 * y q.1.1.2 - y q.1.2.1 * y q.1.2.2 := by
  simp [veroneseRelation]

/-- The relations among the monomials vanish on the vector of monomials of degree `d`. -/
@[simp high]
theorem eval_veroneseMonomials_veroneseRelation {R : Type*} [CommRing R] {d : ℕ}
    (q : VeroneseRelationIndex N d) (v : Fin N → R) :
    eval (veroneseMonomials d v) (veroneseRelation R N d q) = 0 := by
  simp only [eval_veroneseRelation, veroneseMonomials_apply,
    ← prod_mul_distrib, ← pow_add, ← Pi.add_apply, q.2, sub_self]

/-- From a nonzero coordinate `Y α` with `0 < α i`, the binomial relations reach a nonzero
pure power `Y (d e_i)`. -/
private theorem apply_single_ne_zero {K : Type*} [Field K] {d : ℕ} {Y : (Fin N → ℕ) → K}
    (hY : ∀ α β γ δ : Fin N → ℕ, ∑ j, α j = d → ∑ j, β j = d → ∑ j, γ j = d →
      ∑ j, δ j = d → α + β = γ + δ → Y α * Y β = Y γ * Y δ)
    {α : Fin N → ℕ} (hα : ∑ j, α j = d) (hYα : Y α ≠ 0) {i : Fin N} (hi : 0 < α i) :
    Y (Pi.single i d) ≠ 0 := by
  revert hYα hi
  refine Pi.induction_on_single_of_sum_eq
    (P := fun α ↦ Y α ≠ 0 → 0 < α i → Y (Pi.single i d) ≠ 0) i
    (fun h _ ↦ h) (fun β j hji hβ ih hYβ hi ↦ ?_) hα
  have hβi : 0 < β i := by simpa [hji.symm] using hi
  obtain ⟨γ, rfl⟩ := Pi.exists_eq_add_single_one hβi
  simp only [Pi.add_apply, sum_add_distrib, Fintype.sum_pi_single'] at hβ
  -- `2 (γ + e_i + e_j) = (γ + 2 e_i) + (γ + 2 e_j)`
  have hrel := hY (γ + Pi.single i 1 + Pi.single j 1) (γ + Pi.single i 1 + Pi.single j 1)
    (γ + Pi.single i 1 + Pi.single i 1) (γ + Pi.single j 1 + Pi.single j 1)
    (by simp [sum_add_distrib]; omega) (by simp [sum_add_distrib]; omega)
    (by simp [sum_add_distrib]; omega) (by simp [sum_add_distrib]; omega) (by abel)
  refine ih (fun h ↦ hYβ ?_) (by simp)
  rw [← mul_self_eq_zero, hrel, h, zero_mul]

/-- For `d ≠ 0`, the binomial relations express every coordinate `Y α` through the coordinates
`m j = Y ((d - 1) e_i + e_j)`: `Y (d e_i) ^ (d - 1) * Y α = ∏ j, m j ^ α j`. -/
private theorem pow_mul_apply_eq_prod {K : Type*} [Field K] {d : ℕ} (hd : d ≠ 0)
    {Y : (Fin N → ℕ) → K}
    (hY : ∀ α β γ δ : Fin N → ℕ, ∑ j, α j = d → ∑ j, β j = d → ∑ j, γ j = d →
      ∑ j, δ j = d → α + β = γ + δ → Y α * Y β = Y γ * Y δ)
    {i : Fin N} (hYi : Y (Pi.single i d) ≠ 0) {α : Fin N → ℕ} (hα : ∑ j, α j = d) :
    Y (Pi.single i d) ^ (d - 1) * Y α =
      ∏ j, Y (Pi.single i (d - 1) + Pi.single j 1) ^ α j := by
  have hsingle : Pi.single i (d - 1) + Pi.single i 1 = Pi.single (M := fun _ ↦ ℕ) i d := by
    rw [← Pi.single_add, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
  refine Pi.induction_on_single_of_sum_eq (P := fun α ↦ Y (Pi.single i d) ^ (d - 1) * Y α =
    ∏ j, Y (Pi.single i (d - 1) + Pi.single j 1) ^ α j) i ?_ (fun β j hji hβ ih ↦ ?_) hα
  · rw [Fintype.prod_pow_pi_single, hsingle, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
  have hrel := hY (β + Pi.single j 1) (Pi.single i d) (β + Pi.single i 1)
    (Pi.single i (d - 1) + Pi.single j 1) (by simp [sum_add_distrib, hβ])
    (Fintype.sum_pi_single' i d) (by simp [sum_add_distrib, hβ])
    (by simp [sum_add_distrib]; omega) (by
      rw [← hsingle]
      abel)
  refine mul_right_cancel₀ hYi ?_
  calc Y (Pi.single i d) ^ (d - 1) * Y (β + Pi.single j 1) * Y (Pi.single i d)
      = Y (Pi.single i d) ^ (d - 1) * Y (β + Pi.single i 1) *
          Y (Pi.single i (d - 1) + Pi.single j 1) := by rw [mul_assoc, hrel, mul_assoc]
    _ = _ := by
      simp only [Pi.add_apply, pow_add, prod_mul_distrib] at ih ⊢
      rw [ih, Fintype.prod_pow_pi_single, Fintype.prod_pow_pi_single, hsingle]
      ring

/-! ### Linear forms in the monomials -/

section LinearForm

variable {R : Type*} [CommSemiring R]

/-- A polynomial `p` in `N` variables as a linear form in the monomials of degree `d`: the
coefficient of the `k`-th monomial is the coefficient of `p` at the `k`-th exponent vector.
For `p` homogeneous of degree `d`, its value on the vector of monomials of `v` is `p(v)`. -/
noncomputable def veroneseLinearForm (d : ℕ) (p : MvPolynomial (Fin N) R) :
    MvPolynomial (Fin (veroneseDim N d)) R :=
  ∑ k, C (p.coeff (Finsupp.equivFunOnFinite.symm (veroneseExponent N d k))) * X k

/-- The coefficient of the `k`-th monomial in the linear form of `p` is the coefficient of `p` at
the `k`-th exponent vector. -/
@[simp]
theorem coeff_single_veroneseLinearForm (d : ℕ) (p : MvPolynomial (Fin N) R)
    (k : Fin (veroneseDim N d)) :
    (veroneseLinearForm d p).coeff (Finsupp.single k 1) =
      p.coeff (Finsupp.equivFunOnFinite.symm (veroneseExponent N d k)) := by
  simp [veroneseLinearForm, coeff_X, Finsupp.single_left_inj]

/-- The value of the linear form of `p` at a point `y`. -/
@[simp]
theorem eval_veroneseLinearForm (d : ℕ) (p : MvPolynomial (Fin N) R)
    (y : Fin (veroneseDim N d) → R) :
    eval y (veroneseLinearForm d p) =
      ∑ k, p.coeff (Finsupp.equivFunOnFinite.symm (veroneseExponent N d k)) * y k := by
  simp [veroneseLinearForm]

/-- A linear form in the monomials is a homogeneous polynomial of degree one. -/
theorem isHomogeneous_veroneseLinearForm (d : ℕ) (p : MvPolynomial (Fin N) R) :
    (veroneseLinearForm d p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun k _ ↦ isHomogeneous_C_mul_X _ k

/-- A homogeneous polynomial of degree `d` evaluated at `v` is its linear form in the monomials
evaluated at the vector of monomials of `v`. -/
@[simp high]
theorem eval_veroneseMonomials_veroneseLinearForm {d : ℕ} {p : MvPolynomial (Fin N) R}
    (hp : p.IsHomogeneous d) (v : Fin N → R) :
    eval (veroneseMonomials d v) (veroneseLinearForm d p) = eval v p := by
  set g : (Fin N → ℕ) → R := fun α ↦
    p.coeff (Finsupp.equivFunOnFinite.symm α) * ∏ i, v i ^ α i
  have hsupp : p.support.map Finsupp.equivFunOnFinite.toEmbedding ⊆ Nat.antidiagonalTuple N d := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := mem_map.mp hα
    have h : β.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp (mem_support_iff.mp hβ)
    simpa [Nat.mem_antidiagonalTuple, Finsupp.degree_eq_sum] using h
  calc eval (veroneseMonomials d v) (veroneseLinearForm d p)
      = ∑ k, g (veroneseExponent N d k) := by simp [g]
    _ = ∑ α ∈ Nat.antidiagonalTuple N d, g α :=
      sum_bij (fun k _ ↦ veroneseExponent N d k)
        (fun k _ ↦ Nat.mem_antidiagonalTuple.mpr (sum_veroneseExponent d k))
        (fun _ _ _ _ h ↦ veroneseExponent_injective d h)
        (fun α hα ↦ ⟨(veroneseExponentEquiv N d).symm ⟨α, Nat.mem_antidiagonalTuple.mp hα⟩,
          mem_univ _, by simp⟩)
        fun _ _ ↦ rfl
    _ = ∑ α ∈ p.support.map Finsupp.equivFunOnFinite.toEmbedding, g α :=
      (sum_subset hsupp fun α _ hα ↦ by
        simp only [g, notMem_support_iff.mp fun h ↦
          hα (mem_map.mpr ⟨Finsupp.equivFunOnFinite.symm α, h, by simp⟩), zero_mul]).symm
    _ = eval v p := by simp [sum_map, g, eval_eq']

end LinearForm

end TauCeti

namespace Projectivization

open TauCeti

variable {N : ℕ}

section Field

variable (K : Type*) [Field K]

/-- The **Veronese map** of degree `d`, sending the point `[v]` of `ℙ K (Fin N → K)` to the point
`[(∏ i, v i ^ α i)_α]` whose homogeneous coordinates are the monomials of degree `d` in `v`. -/
noncomputable def veronese (d : ℕ) : ℙ K (Fin N → K) → ℙ K (Fin (veroneseDim N d) → K) :=
  Projectivization.lift
    (fun v ↦ mk K (veroneseMonomials d v.1) (veroneseMonomials_ne_zero d v.2))
    (by
      rintro ⟨-, ha⟩ ⟨w, hw⟩ t rfl
      exact (mk_eq_mk_iff' K _ _ _ _).mpr ⟨t ^ d, (veroneseMonomials_smul d t w).symm⟩)

/-- The Veronese map in homogeneous coordinates. -/
@[simp]
theorem veronese_mk (d : ℕ) (v : Fin N → K) (hv : v ≠ 0) :
    veronese K d (mk K v hv) = mk K (veroneseMonomials d v) (veroneseMonomials_ne_zero d hv) :=
  (rfl)

variable {K}

/-- The Veronese map of positive degree is injective. -/
theorem veronese_injective {d : ℕ} (hd : d ≠ 0) :
    Function.Injective (veronese (N := N) K d) := by
  intro x y hxy
  induction x using Projectivization.ind with | h v hv => ?_
  induction y using Projectivization.ind with | h w hw => ?_
  rw [veronese_mk, veronese_mk, mk_eq_mk_iff'] at hxy
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  -- the coordinate of the monomial `x_i ^ (d - 1) * x_j`
  have hcoord (j : Fin N) : a * (w i ^ (d - 1) * w j) = v i ^ (d - 1) * v j := by
    have hsum : ∑ k, (Pi.single i (d - 1) + Pi.single j 1 : Fin N → ℕ) k = d := by
      simp [sum_add_distrib]; omega
    simpa only [Pi.smul_apply, smul_eq_mul, veroneseMonomials_apply,
      veroneseExponent_veroneseExponentEquiv_symm, Pi.add_apply, pow_add, prod_mul_distrib,
      Fintype.prod_pow_pi_single, pow_one] using
      congrFun ha ((veroneseExponentEquiv N d).symm ⟨_, hsum⟩)
  have hd' : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
  have hii := hcoord i
  rw [← pow_succ, ← pow_succ, hd'] at hii
  have hwi : w i ≠ 0 := fun h ↦ pow_ne_zero d hi (by simp [← hii, h, hd])
  refine (mk_eq_mk_iff' K _ _ _ _).mpr ⟨v i / w i, funext fun j ↦ ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero (d - 1) hi) ?_
  rw [← hcoord j, Pi.smul_apply, smul_eq_mul]
  have : v i ^ (d - 1) * v i = a * (w i ^ (d - 1) * w i) := by
    rw [← pow_succ, ← pow_succ, hd', hii]
  field_simp
  linear_combination w j * this

end Field

/-- Over `ℂ`, the image of the Veronese map of positive degree is the common zero locus of the
quadratic binomials `y_α y_β - y_γ y_δ` with `α + β = γ + δ`. -/
theorem range_veronese {d : ℕ} (hd : d ≠ 0) :
    Set.range (veronese (N := N) ℂ d) = complexProjectiveZeroLocus (veroneseRelation ℂ N d) := by
  refine (Set.range_subset_iff.mpr fun x ↦ ?_).antisymm fun y hy ↦ ?_
  · induction x using Projectivization.ind with | h v hv => ?_
    rw [veronese_mk, complexProjectiveZeroLocus_mk_iff (isHomogeneous_veroneseRelation ℂ N d)]
    simp
  induction y using Projectivization.ind with | h y hy0 => ?_
  -- Moving along the relations from a nonzero coordinate reaches a nonzero pure power
  -- `y_(d e_i)`; the coordinates `y_((d - 1) e_i + e_j)` are then homogeneous coordinates of a
  -- preimage.
  rw [complexProjectiveZeroLocus_mk_iff (isHomogeneous_veroneseRelation ℂ N d)] at hy
  -- the coordinates of `y`, indexed by all exponent vectors and extended by zero
  set Y : (Fin N → ℕ) → ℂ := fun α ↦
    if h : ∑ i, α i = d then y ((veroneseExponentEquiv N d).symm ⟨α, h⟩) else 0 with hYdef
  have hYk (k : Fin (veroneseDim N d)) : Y (veroneseExponent N d k) = y k := by
    simp only [hYdef, sum_veroneseExponent, ↓reduceDIte]
    congr
    exact (veroneseExponentEquiv N d).symm_apply_eq.mpr rfl
  have hY : ∀ α β γ δ : Fin N → ℕ, ∑ j, α j = d → ∑ j, β j = d → ∑ j, γ j = d →
      ∑ j, δ j = d → α + β = γ + δ → Y α * Y β = Y γ * Y δ := by
    intro α β γ δ hα hβ hγ hδ h
    have := hy ⟨(((veroneseExponentEquiv N d).symm ⟨α, hα⟩,
      (veroneseExponentEquiv N d).symm ⟨β, hβ⟩), ((veroneseExponentEquiv N d).symm ⟨γ, hγ⟩,
      (veroneseExponentEquiv N d).symm ⟨δ, hδ⟩)), by simpa using h⟩
    simpa [hYdef, hα, hβ, hγ, hδ, sub_eq_zero] using this
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hy0
  obtain ⟨i, hi⟩ : ∃ i, 0 < veroneseExponent N d k i := by
    by_contra! h
    exact hd (by simpa [Nat.le_zero.mp (h _)] using (sum_veroneseExponent d k).symm)
  have hYi := apply_single_ne_zero hY (sum_veroneseExponent d k) (by rwa [hYk]) hi
  set m : Fin N → ℂ := fun j ↦ Y (Pi.single i (d - 1) + Pi.single j 1)
  have hm : m ≠ 0 := Function.ne_iff.mpr ⟨i, by
    simpa [m, ← Pi.single_add, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)] using hYi⟩
  refine ⟨mk ℂ m hm, ?_⟩
  rw [veronese_mk, mk_eq_mk_iff']
  refine ⟨Y (Pi.single i d) ^ (d - 1), funext fun k ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, ← hYk, veroneseMonomials_apply,
    pow_mul_apply_eq_prod hd hY hYi (sum_veroneseExponent d k)]

/-- The Veronese map pulls back the linear sections `veroneseLinearForm d (p i) = 0` of the
target projective space to the zero locus of the homogeneous degree-`d` equations `p i`. -/
theorem preimage_veronese_complexProjectiveZeroLocus_veroneseLinearForm {ι : Type*} {d : ℕ}
    {p : ι → MvPolynomial (Fin N) ℂ} (hp : ∀ i, (p i).IsHomogeneous d) :
    veronese ℂ d ⁻¹' complexProjectiveZeroLocus (fun i ↦ veroneseLinearForm d (p i)) =
      complexProjectiveZeroLocus p := by
  ext x
  induction x using Projectivization.ind with | h v hv => ?_
  rw [Set.mem_preimage, veronese_mk,
    complexProjectiveZeroLocus_mk_iff fun i ↦ isHomogeneous_veroneseLinearForm d (p i),
    complexProjectiveZeroLocus_mk_iff hp]
  simp only [eval_veroneseMonomials_veroneseLinearForm (hp _)]

end Projectivization
