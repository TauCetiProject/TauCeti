/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
public import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# The generator dictionary of the dimension-raising equivalence

Mathlib's `CliffordAlgebra.equivEven` identifies a Clifford algebra `Cℓ(M, Q)` with the even
subalgebra of `Cℓ(M × R, Q')`, where `Q' = CliffordAlgebra.EquivEven.Q' Q` sends `(m, r)` to
`Q m - r²`. The new direction is spanned by `e₀ = CliffordAlgebra.EquivEven.e0 Q`, with
`e₀² = -1`, and the vector `m` is sent to `e₀ v(m)`, where `v(m) = ι Q' (m, 0)`
(`CliffordAlgebra.toEven_ι`). For the negative-metric convention `Q = -g` of spin geometry the form
`Q'` is again negative definite, `Q' (m, r) = -(g(m, m) + r²)`, so this is the identification
`Cℓₙ ≅ Cℓ⁰ₙ₊₁` used to compare odd-dimensional Clifford modules with even-dimensional ones.

This file writes that identification in terms of the Clifford map
`CliffordAlgebra.map (QuadraticMap.Isometry.inl Q _) : Cℓ(M, Q) →ₐ Cℓ(M × R, Q')` induced by the
inclusion `M → M × R`, which sends `ι Q m` to `v(m)`. An even element `x⁰` is sent to its own
image `x⁰`, and an odd element `x¹` to `e₀ x¹`, so a general element `x⁰ + x¹` is sent to
`x⁰ + e₀ x¹`. The grade involution of `Cℓ(M, Q)` corresponds to conjugation by the unit `e₀`,
whose inverse is `-e₀`. In particular the volume element `e₁ ⋯ eₙ` of an odd number of vectors
is sent to `e₀ e₁ ⋯ eₙ = -(e₁ ⋯ eₙ e₀)`, minus the volume element of the list `e₁, …, eₙ, e₀`.
After complexification and the normalization `ω_ℂ = i^(ℓ+1) e₁ ⋯ eₙ` for `n = 2ℓ + 1`, this sign is
what makes the odd-dimensional volume element correspond to minus the chirality element of
`M × R` in that order; the complexified statement is not made here.

## Main results

* `CliffordAlgebra.EquivEven.e0_mul_map_inl`: `e₀` conjugates the image of `Cℓ(M, Q)` by the
  grade involution.
* `CliffordAlgebra.coe_toEven_of_mem_even`: an even element is sent to its image under the
  inclusion.
* `CliffordAlgebra.coe_toEven_of_mem_odd`: an odd element `x` is sent to `e₀ x`.
* `CliffordAlgebra.coe_toEven_involute`: the grade involution becomes conjugation by `e₀`.
* `CliffordAlgebra.coe_toEven_prod_map_ι_of_even_length` and
  `CliffordAlgebra.coe_toEven_prod_map_ι_of_odd_length`: an even ordered product of vectors is
  sent to the same product, and an odd one to minus the product with `e₀` appended.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3.
-/

public section

namespace CliffordAlgebra

open EquivEven
open QuadraticMap (Isometry)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

namespace EquivEven

/-- Left multiplication by `e₀` twice is negation, since `e₀² = -1`. -/
@[simp]
theorem e0_mul_e0_mul (y : CliffordAlgebra (Q' Q)) : e0 Q * (e0 Q * y) = -y := by
  rw [← mul_assoc, e0_mul_e0, neg_one_mul]

/-- The inclusion `M → M × R` sends the generator `ι Q m` to `v(m)`. -/
theorem map_inl_ι (m : M) : map (Isometry.inl Q (-QuadraticMap.sq)) (ι Q m) = v Q m := by
  rw [map_apply_ι, Isometry.inl_apply, v, LinearMap.comp_apply, LinearMap.inl_apply]

/-- **`e₀` conjugates the image of `Cℓ(M, Q)` by the grade involution**: for every `x`,
`e₀ x = x̂ e₀` in `Cℓ(M × R, Q')`, where `x̂ = involute x`. -/
theorem e0_mul_map_inl (x : CliffordAlgebra Q) :
    e0 Q * map (Isometry.inl Q (-QuadraticMap.sq)) x =
      map (Isometry.inl Q (-QuadraticMap.sq)) (involute x) * e0 Q := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι m => rw [involute_ι, map_neg, map_inl_ι, neg_mul, neg_v_mul_e0]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
  | mul x y hx hy =>
    simp only [map_mul, ← mul_assoc, hx]
    simp only [mul_assoc, hy]

end EquivEven

/-- **An even element is sent to its own image**: for `x` in the even part of `Cℓ(M, Q)`, the
dimension-raising equivalence sends `x` to its image under the inclusion `M → M × R`. -/
theorem coe_toEven_of_mem_even {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) :
    (toEven Q x : CliffordAlgebra (Q' Q)) = map (Isometry.inl Q (-QuadraticMap.sq)) x := by
  induction x, hx using even_induction with
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simp only [map_add, Subalgebra.coe_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, Subalgebra.coe_mul, toEven_ι, ih, map_inl_ι]
    rw [← mul_assoc (e0 Q * v Q m₁), e0_mul_v_mul_e0]

/-- **An odd element `x` is sent to `e₀ x`**: for `x` in the odd part of `Cℓ(M, Q)`, the
dimension-raising equivalence sends `x` to `e₀` times its image under the inclusion
`M → M × R`. -/
theorem coe_toEven_of_mem_odd {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 1) :
    (toEven Q x : CliffordAlgebra (Q' Q)) = e0 Q * map (Isometry.inl Q (-QuadraticMap.sq)) x := by
  induction x, hx using odd_induction with
  | ι m => rw [toEven_ι, map_inl_ι]
  | add x y hx hy ihx ihy => simp only [map_add, Subalgebra.coe_add, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h := e0_mul_map_inl (ι Q m₁ * ι Q m₂)
    simp only [map_mul, involute_ι, neg_mul_neg, map_inl_ι] at h
    simp only [map_mul, Subalgebra.coe_mul, toEven_ι, ih, map_inl_ι]
    rw [← mul_assoc (e0 Q * v Q m₁), e0_mul_v_mul_e0, ← mul_assoc (e0 Q), h]
    simp only [mul_assoc]

/-- **The grade involution becomes conjugation by `e₀`**: since `e₀⁻¹ = -e₀`, the
dimension-raising equivalence sends `x̂ = involute x` to `e₀ x e₀⁻¹ = -(e₀ x e₀)`. -/
theorem coe_toEven_involute (x : CliffordAlgebra Q) :
    (toEven Q (involute x) : CliffordAlgebra (Q' Q)) =
      -(e0 Q * toEven Q x * e0 Q) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes r (e0 Q), mul_assoc]
  | ι m => simp [toEven_ι, ← neg_e0_mul_v]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy, mul_add, add_mul, neg_add]
  | mul x y hx hy => simp [hx, hy, mul_assoc]

/-- **An even ordered product of vectors is sent to the same product in `Cℓ(M × R, Q')`.** -/
theorem coe_toEven_prod_map_ι_of_even_length {l : List M} (hl : Even l.length) :
    (toEven Q (l.map (ι Q)).prod : CliffordAlgebra (Q' Q)) = (l.map (v Q)).prod := by
  rw [coe_toEven_of_mem_even (prod_map_ι_mem_evenOdd_zero_of_even_length hl), map_list_prod,
    List.map_map]
  simp only [Function.comp_def, map_inl_ι]

/-- **An odd ordered product of vectors is sent to minus the product with `e₀` appended**: for
`l = [m₁, …, mₙ]` with `n` odd, the image of `ι m₁ ⋯ ι mₙ` is
`e₀ v(m₁) ⋯ v(mₙ) = -(v(m₁) ⋯ v(mₙ) e₀)`. For an orthogonal basis this is the volume element
of `M` going to minus the volume element of `M × R` in the order that puts `e₀` last. -/
theorem coe_toEven_prod_map_ι_of_odd_length {l : List M} (hl : Odd l.length) :
    (toEven Q (l.map (ι Q)).prod : CliffordAlgebra (Q' Q)) = -((l.map (v Q)).prod * e0 Q) := by
  have hodd := prod_map_ι_mem_evenOdd_one_of_odd_length (Q := Q) hl
  rw [coe_toEven_of_mem_odd hodd, e0_mul_map_inl, involute_eq_of_mem_odd hodd, map_neg,
    neg_mul, map_list_prod, List.map_map]
  simp only [Function.comp_def, map_inl_ι]

end CliffordAlgebra
