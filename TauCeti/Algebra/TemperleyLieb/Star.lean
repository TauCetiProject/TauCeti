/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import TauCeti.Algebra.TemperleyLieb.Basic

/-!
# The adjoint on the Temperley–Lieb algebra

Over a commutative star ring `R`, and for a self-adjoint loop value `δ` (for instance a real loop
value in `ℂ`), the Temperley–Lieb algebra `TemperleyLieb R δ n` carries the *analytic adjoint*:
the conjugate-linear, product-reversing involution fixing every generator `e i`. Geometrically it
reflects a planar tangle top to bottom and conjugates its coefficients. This is the star structure
with respect to which the Markov trace gives the Hermitian form `(x, y) ↦ tr (x⋆ * y)` whose
positivity is Jones's restriction on the loop value, and with respect to which `δ⁻¹ • e i` is a
self-adjoint idempotent, a Jones projection, whenever `δ` is invertible.

The defining relations are fixed by reversal of words, and the quadratic relation
`e i * e i = δ • e i` is fixed by conjugation of coefficients exactly when `δ` is self-adjoint.
So for self-adjoint `δ` the star structure exists (`TauCeti.TemperleyLieb.instStarRing`,
`TauCeti.TemperleyLieb.instStarModule`), it is the only one fixing the generators
(`TauCeti.TemperleyLieb.star_unique`), and an algebra map into a star algebra preserves it exactly
when it sends the generators to self-adjoint elements (`TauCeti.TemperleyLieb.map_star_iff`).
Conversely a conjugate-linear star structure fixing the generator on two strands forces `δ` to be
self-adjoint (`TauCeti.TemperleyLieb.isSelfAdjoint_of_star_e`): applying it to `e * e = δ • e`
gives `δ • e = star δ • e`, and distinct scalar multiples of the two-strand generator are
distinct (`TauCeti.TemperleyLieb.smul_left_injective_e_two`).

The hypothesis on `δ` is the instance argument `Fact (IsSelfAdjoint δ)`; for a real loop value
`δ : ℝ` in `ℂ` it is supplied by `Complex.conj_ofReal δ`.

## Main definitions

* `TauCeti.TemperleyLieb.instStarRing`: for self-adjoint `δ`, the star structure fixing every
  generator; it is conjugate-linear (`TauCeti.TemperleyLieb.instStarModule`).

## Main results

* `TauCeti.TemperleyLieb.star_e`: every generator is self-adjoint.
* `TauCeti.TemperleyLieb.star_unique`: the star structure is the unique additive,
  product-reversing, conjugate-linear unital map fixing the generators.
* `TauCeti.TemperleyLieb.map_star_iff`: the universal property as a star algebra.
* `TauCeti.TemperleyLieb.strandIncl_star`, `TauCeti.TemperleyLieb.aug_star`: the strand inclusion
  and the augmentation preserve the star structure.
* `TauCeti.TemperleyLieb.isSelfAdjoint_of_star_e`: a star structure fixing the generators exists
  only for self-adjoint `δ`.

## Implementation notes

A conjugate-linear antimultiplicative map out of `TemperleyLieb R δ n` is obtained from the
universal property `TauCeti.TemperleyLieb.lift`, as an `R`-algebra map into the opposite algebra
on which scalars act through `starRingEnd R`, built with `Algebra.compHom`. This follows the
construction of the star structures on `TauCeti.UqSl2` and `TauCeti.InfiniteTypeAHeckeAlgebra`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for the adjoint and the Hermitian
  form of the Temperley–Lieb algebras.
-/

public section

namespace TauCeti.TemperleyLieb

open MulOpposite

variable {R : Type*} [CommSemiring R] [StarRing R] {δ : R} {n : ℕ}

section Construction

variable [hδ : Fact (IsSelfAdjoint δ)]

/-- The conjugate-linear reversal map, bundled as a ring homomorphism into the opposite algebra.
The target algebra structure is twisted by conjugation of scalars only during construction. -/
private def conjugateReverse : TemperleyLieb R δ n →+* (TemperleyLieb R δ n)ᵐᵒᵖ := by
  letI : Algebra R (TemperleyLieb R δ n)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  exact (lift (fun i ↦ op (e δ i))
    (fun i ↦ unop_injective <| by
      simp only [unop_mul, unop_op, Algebra.smul_def, Algebra.compHom_algebraMap_apply,
        starRingEnd_apply, MulOpposite.algebraMap_apply, hδ.out.star_eq]
      rw [e_mul_self, Algebra.smul_def, Algebra.commutes])
    (fun h ↦ unop_injective <| by simpa [mul_assoc] using e_mul_e_mul_e h)
    (fun h ↦ unop_injective <| (commute_e h).eq.symm)).toRingHom

private theorem conjugateReverse_e (i : Fin (n - 1)) :
    conjugateReverse (e δ i) = op (e δ i) := by
  simp [conjugateReverse]

private theorem conjugateReverse_algebraMap (r : R) :
    conjugateReverse (algebraMap R (TemperleyLieb R δ n) r) =
      op (algebraMap R _ (star r)) := by
  simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateReverse_involutive (x : TemperleyLieb R δ n) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (e δ (n := n))) := by simp [adjoin_range_e]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [conjugateReverse_e]
  | algebraMap r => simp [conjugateReverse_algebraMap]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy => simp [map_mul, hx, hy]

/-- For a self-adjoint loop value, the analytic adjoint on the Temperley–Lieb algebra: the
conjugate-linear, product-reversing involution fixing every generator. -/
@[no_expose]
instance instStarRing : StarRing (TemperleyLieb R δ n) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- Every generator is self-adjoint. -/
@[simp]
theorem star_e (i : Fin (n - 1)) : star (e δ i) = e δ i :=
  congrArg unop (conjugateReverse_e i)

/-- Every generator is self-adjoint, stated with `IsSelfAdjoint`. -/
theorem isSelfAdjoint_e (i : Fin (n - 1)) : IsSelfAdjoint (e δ i) :=
  star_e i

private theorem star_algebraMap (r : R) :
    star (algebraMap R (TemperleyLieb R δ n) r) = algebraMap R _ (star r) :=
  congrArg unop (conjugateReverse_algebraMap r)

/-- The analytic adjoint is conjugate-linear. -/
instance instStarModule : StarModule R (TemperleyLieb R δ n) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

/-- The analytic adjoint is the unique additive, product-reversing, conjugate-linear unital map
fixing every generator. -/
theorem star_unique {f : TemperleyLieb R δ n → TemperleyLieb R δ n}
    (map_add : ∀ x y, f (x + y) = f x + f y) (map_mul : ∀ x y, f (x * y) = f y * f x)
    (map_smul : ∀ (r : R) x, f (r • x) = star r • f x) (map_one : f 1 = 1)
    (map_e : ∀ i, f (e δ i) = e δ i) : f = star := by
  funext x
  have hx : x ∈ Algebra.adjoin R (Set.range (e δ (n := n))) := by simp [adjoin_range_e]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [map_e, star_e]
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, star_smul, star_one]
  | add x y _ _ hx hy => rw [map_add, star_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, star_mul, hx, hy]

section UniversalProperty

variable {A : Type*} [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map out of the Temperley–Lieb algebra preserves the analytic adjoint exactly when
it sends every generator to a self-adjoint element. So the presentation is also a presentation
as a star algebra. -/
theorem map_star_iff {F : TemperleyLieb R δ n →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, IsSelfAdjoint (F (e δ i)) := by
  constructor
  · intro h i
    simpa only [IsSelfAdjoint, star_e] using (h (e δ i)).symm
  · intro h x
    have hx : x ∈ Algebra.adjoin R (Set.range (e δ (n := n))) := by simp [adjoin_range_e]
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [star_e, (h i).star_eq]
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y _ _ hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [star_mul, map_mul, hx, hy]

end UniversalProperty

/-- Adding a straight strand commutes with the analytic adjoint. -/
@[simp]
theorem strandIncl_star (x : TemperleyLieb R δ (n + 1)) :
    strandIncl (star x) = star (strandIncl x) :=
  map_star_iff.mpr (fun i ↦ by simpa using isSelfAdjoint_e (δ := δ) (n := n + 2) i.castSucc) x

/-- The augmentation conjugates: on at most one strand, where the algebra is the base ring, the
analytic adjoint is the star of `R`. -/
@[simp]
theorem aug_star (x : TemperleyLieb R δ n) : aug (star x) = star (aug x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint]) x

end Construction

/-- A conjugate-linear star structure on the two-strand Temperley–Lieb algebra fixing the
generator exists only for a self-adjoint loop value: applied to `e * e = δ • e` it gives
`δ • e = star δ • e`. In particular over `ℂ` the loop value must be real. -/
theorem isSelfAdjoint_of_star_e [StarMul (TemperleyLieb R δ 2)]
    [StarModule R (TemperleyLieb R δ 2)] (i : Fin (2 - 1)) (he : star (e δ i) = e δ i) :
    IsSelfAdjoint δ := by
  apply smul_left_injective_e_two (δ := δ) i
  have h := congrArg star (e_mul_self (δ := δ) i)
  rw [star_mul, star_smul, he, e_mul_self] at h
  exact h.symm

end TauCeti.TemperleyLieb
