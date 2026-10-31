/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Evaluations of elements of a symmetric algebra

Let `M` be a free module over an infinite integral domain `R`. Every linear form `f : M → R`
extends to the evaluation `SymmetricAlgebra.lift f : S(M) →ₐ[R] R`, and an element of `S(M)` is a
polynomial function on the dual of `M` through these evaluations. This file shows that the function
determines the element: two elements of `S(M)` with the same value at every linear form are equal.
In a basis of `M`, `S(M)` is a polynomial algebra (`SymmetricAlgebra.equivMvPolynomial`) and the
evaluations are the evaluations of polynomials at all points, which separate polynomials over an
infinite domain (`MvPolynomial.funext`).

Far fewer linear forms suffice. Over any integral domain, an element of `S(M)` vanishing at every
linear form whose values on a basis lie in prescribed infinite sets is zero, since a polynomial
vanishing on a box with infinite sides is zero (`MvPolynomial.funext_set`). For a semisimple Lie
algebra this is how polynomial functions on the weights are tested on the dominant integral
weights alone, whose values on the simple coroots are the natural numbers.

The function is polynomial in the usual sense along every affine line of linear forms, over any
commutative ring and without freeness: for `p : S(M)` and linear forms `f`, `g`, the values
`SymmetricAlgebra.lift (f + t • g) p` are the values at `t` of one polynomial in `R[X]`, namely the
image of `p` under the evaluation at the `R[X]`-valued linear form `f + X • g`. Over a domain, this
is how an identity between two such functions known at infinitely many points of a line is
extended to the whole line.

For a Cartan subalgebra `H` of a semisimple Lie algebra, `S(H)` is the algebra of polynomial
functions on the weights `H*`, and this is how an identity in `S(H)` is checked one weight at a
time.

## Main results

* `Module.Basis.lift_apply_eq_eval_equivMvPolynomial`: in the coordinates of a basis,
  the evaluation at a linear form is the evaluation of a polynomial at the values of the form on
  the basis.
* `SymmetricAlgebra.exists_polynomial_eval_eq_lift_add_smul`: along an affine line of
  linear forms, the evaluations of an element of `S(M)` are the values of a polynomial.
* `TauCeti.SymmetricAlgebra.eq_zero_of_forall_lift_eq_zero`: an element of `S(M)` vanishing at
  every linear form whose values on a basis lie in given infinite sets is zero.
* `TauCeti.SymmetricAlgebra.eq_of_forall_lift_apply_eq`: two elements of `S(M)` on which every
  evaluation `SymmetricAlgebra.lift f` agrees are equal.
-/

public section

namespace Module.Basis

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **Evaluation in coordinates.** Through the polynomial algebra structure induced by a basis `b`,
evaluating an element of the symmetric algebra at the linear form `f` is evaluating the
corresponding polynomial at the values of `f` on `b`. -/
theorem lift_apply_eq_eval_equivMvPolynomial (b : Module.Basis ι R M) (f : M →ₗ[R] R)
    (p : SymmetricAlgebra R M) :
    SymmetricAlgebra.lift f p =
      MvPolynomial.eval (fun i ↦ f (b i)) (SymmetricAlgebra.equivMvPolynomial b p) := by
  have h : SymmetricAlgebra.lift f = (MvPolynomial.aeval fun i ↦ f (b i)).comp
      (SymmetricAlgebra.equivMvPolynomial b : SymmetricAlgebra R M →ₐ[R] MvPolynomial ι R) :=
    SymmetricAlgebra.algHom_ext <| b.ext fun i ↦ by simp
  rw [h, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← MvPolynomial.aeval_eq_eval]

end Module.Basis

namespace SymmetricAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An element of the symmetric algebra is a polynomial function along every affine line** of
linear forms: for `p : S(M)` and linear forms `f`, `g` there is a polynomial `q` with
`q.eval t = SymmetricAlgebra.lift (f + t • g) p` for every `t : R`. -/
theorem exists_polynomial_eval_eq_lift_add_smul (p : SymmetricAlgebra R M) (f g : M →ₗ[R] R) :
    ∃ q : Polynomial R, ∀ t : R, q.eval t = SymmetricAlgebra.lift (f + t • g) p := by
  -- the evaluation at the `R[X]`-valued linear form `f + X • g`, followed by `X ↦ t`
  let φ : M →ₗ[R] Polynomial R := Polynomial.monomial 0 ∘ₗ f + Polynomial.monomial 1 ∘ₗ g
  refine ⟨SymmetricAlgebra.lift φ p, fun t ↦ ?_⟩
  have hcomp : (Polynomial.aeval t).comp (SymmetricAlgebra.lift φ) =
      SymmetricAlgebra.lift (f + t • g) := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_ofClass, AlgHom.coe_comp,
      SymmetricAlgebra.lift_ι_apply]
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
      Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
    ring
  rw [← Polynomial.coe_aeval_eq_eval, ← hcomp, AlgHom.comp_apply]

end SymmetricAlgebra

namespace TauCeti.SymmetricAlgebra

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- **An element of the symmetric algebra vanishing on a box of linear forms is zero.** Let `b` be
a basis of `M` over an integral domain and let `s i` be an infinite set of scalars for each basis
index `i`. If `SymmetricAlgebra.lift f p = 0` for every linear form `f` with `f (b i) ∈ s i` for
all `i`, then `p = 0`. -/
theorem eq_zero_of_forall_lift_eq_zero {ι : Type*} (b : Module.Basis ι R M) {s : ι → Set R}
    (hs : ∀ i, (s i).Infinite) {p : SymmetricAlgebra R M}
    (h : ∀ f : Module.Dual R M, (∀ i, f (b i) ∈ s i) → SymmetricAlgebra.lift f p = 0) :
    p = 0 := by
  refine (SymmetricAlgebra.equivMvPolynomial b).injective <|
    (MvPolynomial.funext_set s hs fun x hx ↦ ?_).trans (map_zero _).symm
  -- the point `x` is the coordinate vector of the linear form `b.constr R x`
  have hfx : ∀ i, b.constr R x (b i) ∈ s i := fun i ↦ by
    simpa only [Module.Basis.constr_basis] using hx i (Set.mem_univ i)
  have hcoord := b.lift_apply_eq_eval_equivMvPolynomial (b.constr R x) p
  simp only [Module.Basis.constr_basis] at hcoord
  rw [← hcoord, h _ hfx, map_zero]

/-- **An element of the symmetric algebra of a free module over an infinite domain is determined by
its values at all linear forms**: if `SymmetricAlgebra.lift f p = SymmetricAlgebra.lift f q` for
every `f : Module.Dual R M`, then `p = q`. -/
theorem eq_of_forall_lift_apply_eq [Infinite R] [Module.Free R M] {p q : SymmetricAlgebra R M}
    (h : ∀ f : Module.Dual R M, SymmetricAlgebra.lift f p = SymmetricAlgebra.lift f q) :
    p = q :=
  sub_eq_zero.mp <| eq_zero_of_forall_lift_eq_zero (Module.Free.chooseBasis R M)
    (s := fun _ ↦ Set.univ) (fun _ ↦ Set.infinite_univ) fun f _ ↦ by rw [map_sub, h f, sub_self]

end TauCeti.SymmetricAlgebra
