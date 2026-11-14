/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.PDeriv
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# The gradient of a symmetric tensor as a polynomial on the dual module

Let `M` be a module with a finite basis `b : Module.Basis ι R M` over a commutative semiring `R`.
Every element `p : SymmetricAlgebra R M` defines a polynomial function on the dual module
`Module.Dual R M` via `ξ ↦ SymmetricAlgebra.lift ξ p`. Expanding `p` as a polynomial `P` in the
basis coordinates (`SymmetricAlgebra.equivMvPolynomial b p`), its **gradient** at `ξ` is the
vector

`b.symmetricGradient p ξ = ∑ i, (∂ᵢ P)(ξ(b₁), …, ξ(bₙ)) • bᵢ`

in `M`. Pairing this vector with any linear form `η : Module.Dual R M` recovers the directional
derivative `SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv η p)`, which makes no reference to
`b`. Because a finite basis separates vectors by its coordinate forms, `b.symmetricGradient p ξ`
is independent of the chosen finite basis `b`. Under the finite-rank biduality equivalence
`M ≃ (M*)*`, it represents the differential at `ξ` of the polynomial evaluation `η ↦ p(η)`.

From the coordinate-free pairing formula follow `R`-linearity in `p`, vanishing on scalars,
`b.symmetricGradient (ι x) ξ = x` on generators, the Leibniz product rule, the power rule, and
contravariant naturality of evaluations together with covariant naturality of gradients along any
linear map between finite free modules.

## Main definitions

* `Module.Basis.symmetricGradient`: the gradient vector in `M` of `p : SymmetricAlgebra R M` at a
  linear form `ξ : Module.Dual R M`, computed in a finite basis `b`.
* `Module.Basis.symmetricGradientLinear`: `b.symmetricGradient · ξ` bundled as an `R`-linear map
  `SymmetricAlgebra R M →ₗ[R] M`.

## Main results

* `Module.Basis.apply_symmetricGradient`: for every `η : Module.Dual R M`,
  `η (b.symmetricGradient p ξ) = SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv η p)`.
* `Module.Basis.symmetricGradient_eq`: independence of the chosen finite basis.
* `Module.Basis.symmetricGradient_ι`, `Module.Basis.symmetricGradient_algebraMap`,
  `Module.Basis.symmetricGradient_mul`, `Module.Basis.symmetricGradient_pow`: generator, scalar,
  product, and power rules.
* `Module.Basis.symmetricGradient_map`: naturality of gradients along linear maps.

## References

* N. Bourbaki, *Algebra*, Chapters 1–3, Springer (1989), Chapter III, §6 (symmetric algebras and
  polynomial functions on the dual).
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (functional derivatives of polynomial functions on `𝔤*`).
-/

public section

namespace Module.Basis

section CommSemiring

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]

/-- The gradient at `ξ ∈ M*` of `p : SymmetricAlgebra R M` read as a polynomial function on `M*`:
the vector `∑ i, (∂ᵢ P)(ξ(b₁), …, ξ(bₙ)) • bᵢ` of `M`, where `P` is the polynomial of `p` in the
coordinates of the finite basis `b`. By `Module.Basis.symmetricGradient_eq`, this vector does not
depend on `b`. -/
noncomputable def symmetricGradient (b : Module.Basis ι R M) (p : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) : M :=
  ∑ i, MvPolynomial.eval (fun j ↦ ξ (b j))
      (MvPolynomial.pderiv i (SymmetricAlgebra.equivMvPolynomial b p)) • b i

/-- Defining coordinate sum for `Module.Basis.symmetricGradient`. -/
theorem symmetricGradient_def (b : Module.Basis ι R M) (p : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient p ξ =
      ∑ i, MvPolynomial.eval (fun j ↦ ξ (b j))
          (MvPolynomial.pderiv i (SymmetricAlgebra.equivMvPolynomial b p)) • b i :=
  (rfl)

/-- **Coordinate-free pairing formula.** Every linear form `η : Module.Dual R M` pairs with
`b.symmetricGradient p ξ` to give the directional derivative `SymmetricAlgebra.pderiv η p`
evaluated at `ξ`. -/
theorem apply_symmetricGradient (b : Module.Basis ι R M) (p : SymmetricAlgebra R M)
    (ξ η : Module.Dual R M) :
    η (b.symmetricGradient p ξ) = SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv η p) := by
  rw [symmetricGradient, map_sum, SymmetricAlgebra.pderiv_eq_sum b η p, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.map_smul, smul_eq_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, ← SymmetricAlgebra.equivMvPolynomial_pderiv_coord,
    ← b.lift_apply_eq_eval_equivMvPolynomial, mul_comm]

/-- The `i`-th coordinate of `b.symmetricGradient p ξ` is the partial derivative along `b.coord i`
evaluated at `ξ`. -/
@[simp]
theorem repr_symmetricGradient (b : Module.Basis ι R M) (p : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) (i : ι) :
    b.repr (b.symmetricGradient p ξ) i =
      SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv (b.coord i) p) :=
  b.apply_symmetricGradient p ξ (b.coord i)

/-- **Basis independence.** Any two finite bases of `M` compute the same gradient vector. -/
theorem symmetricGradient_eq {ι' : Type*} [Fintype ι'] (b : Module.Basis ι R M)
    (b' : Module.Basis ι' R M) (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    b.symmetricGradient p ξ = b'.symmetricGradient p ξ :=
  b.ext_elem fun i ↦ by rw [b.repr_symmetricGradient, ← b.coord_apply, b'.apply_symmetricGradient]

@[simp]
theorem symmetricGradient_zero (b : Module.Basis ι R M) (ξ : Module.Dual R M) :
    b.symmetricGradient 0 ξ = 0 :=
  b.ext_elem fun i ↦ by simp

@[simp]
theorem symmetricGradient_add (b : Module.Basis ι R M) (p q : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (p + q) ξ = b.symmetricGradient p ξ + b.symmetricGradient q ξ :=
  b.ext_elem fun i ↦ by simp

@[simp]
theorem symmetricGradient_smul (b : Module.Basis ι R M) (r : R) (p : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (r • p) ξ = r • b.symmetricGradient p ξ :=
  b.ext_elem fun i ↦ by simp

/-- The gradient at `ξ` bundled as an `R`-linear map `SymmetricAlgebra R M →ₗ[R] M`. -/
noncomputable def symmetricGradientLinear (b : Module.Basis ι R M) (ξ : Module.Dual R M) :
    SymmetricAlgebra R M →ₗ[R] M where
  toFun p := b.symmetricGradient p ξ
  map_add' p q := b.symmetricGradient_add p q ξ
  map_smul' r p := b.symmetricGradient_smul r p ξ

@[simp]
theorem symmetricGradientLinear_apply (b : Module.Basis ι R M) (ξ : Module.Dual R M)
    (p : SymmetricAlgebra R M) :
    b.symmetricGradientLinear ξ p = b.symmetricGradient p ξ :=
  (rfl)

theorem symmetricGradient_sum {α : Type*} (b : Module.Basis ι R M) (s : Finset α)
    (f : α → SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    b.symmetricGradient (∑ a ∈ s, f a) ξ = ∑ a ∈ s, b.symmetricGradient (f a) ξ :=
  map_sum (b.symmetricGradientLinear ξ) f s

/-- Every scalar in `SymmetricAlgebra R M` has zero gradient. -/
@[simp]
theorem symmetricGradient_algebraMap (b : Module.Basis ι R M) (r : R) (ξ : Module.Dual R M) :
    b.symmetricGradient (algebraMap R (SymmetricAlgebra R M) r) ξ = 0 :=
  b.ext_elem fun i ↦ by simp

@[simp]
theorem symmetricGradient_one (b : Module.Basis ι R M) (ξ : Module.Dual R M) :
    b.symmetricGradient 1 ξ = 0 := by
  simpa using b.symmetricGradient_algebraMap 1 ξ

@[simp]
theorem symmetricGradient_natCast (b : Module.Basis ι R M) (n : ℕ) (ξ : Module.Dual R M) :
    b.symmetricGradient (n : SymmetricAlgebra R M) ξ = 0 := by
  simpa using b.symmetricGradient_algebraMap (n : R) ξ

@[simp]
theorem symmetricGradient_ofNat (b : Module.Basis ι R M) (n : ℕ) [n.AtLeastTwo]
    (ξ : Module.Dual R M) :
    b.symmetricGradient (ofNat(n) : SymmetricAlgebra R M) ξ = 0 :=
  b.symmetricGradient_natCast n ξ

/-- The gradient of a symmetric generator `ι x` is `x` at every `ξ`. -/
@[simp]
theorem symmetricGradient_ι (b : Module.Basis ι R M) (x : M) (ξ : Module.Dual R M) :
    b.symmetricGradient (SymmetricAlgebra.ι R M x) ξ = x :=
  b.ext_elem fun i ↦ by simp

/-- **Product rule for `symmetricGradient`.** -/
theorem symmetricGradient_mul (b : Module.Basis ι R M) (p q : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (p * q) ξ =
      SymmetricAlgebra.lift ξ p • b.symmetricGradient q ξ +
        SymmetricAlgebra.lift ξ q • b.symmetricGradient p ξ :=
  b.ext_elem fun i ↦ by simp [Derivation.leibniz]

/-- **Power rule for `symmetricGradient`.** -/
theorem symmetricGradient_pow (b : Module.Basis ι R M) (p : SymmetricAlgebra R M) (n : ℕ)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (p ^ n) ξ =
      (n • SymmetricAlgebra.lift ξ p ^ (n - 1)) • b.symmetricGradient p ξ := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [pow_succ, b.symmetricGradient_mul, ih, map_pow, smul_smul, ← add_smul]
      congr 1
      rw [Nat.add_sub_cancel, nsmul_eq_mul, Nat.add_sub_cancel, nsmul_eq_mul]
      push_cast
      ring

/-- **Naturality (chain rule) of `symmetricGradient` along a linear map.** -/
theorem symmetricGradient_map {N ι' : Type*} [AddCommMonoid N] [Module R N] [Fintype ι']
    (b : Module.Basis ι R M) (b' : Module.Basis ι' R N) (g : M →ₗ[R] N)
    (p : SymmetricAlgebra R M) (ξ : Module.Dual R N) :
    b'.symmetricGradient (SymmetricAlgebra.map R g p) ξ =
      g (b.symmetricGradient p (ξ ∘ₗ g)) :=
  b'.ext_elem fun j ↦ by
    rw [b'.repr_symmetricGradient, SymmetricAlgebra.pderiv_map, SymmetricAlgebra.lift_map,
      ← b.apply_symmetricGradient, LinearMap.comp_apply, b'.coord_apply]

end CommSemiring

section CommRing

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

@[simp]
theorem symmetricGradient_neg (b : Module.Basis ι R M) (p : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (-p) ξ = -b.symmetricGradient p ξ :=
  map_neg (b.symmetricGradientLinear ξ) p

@[simp]
theorem symmetricGradient_sub (b : Module.Basis ι R M) (p q : SymmetricAlgebra R M)
    (ξ : Module.Dual R M) :
    b.symmetricGradient (p - q) ξ = b.symmetricGradient p ξ - b.symmetricGradient q ξ :=
  map_sub (b.symmetricGradientLinear ξ) p q

@[simp]
theorem symmetricGradient_intCast (b : Module.Basis ι R M) (z : ℤ) (ξ : Module.Dual R M) :
    b.symmetricGradient (z : SymmetricAlgebra R M) ξ = 0 := by
  simpa using b.symmetricGradient_algebraMap (z : R) ξ

end CommRing

end Module.Basis
