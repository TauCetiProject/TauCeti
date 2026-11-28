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

Let `M` be a module over a commutative semiring `R`. Every element `p : SymmetricAlgebra R M`
defines a polynomial function on the dual module `Module.Dual R M` via
`ξ ↦ SymmetricAlgebra.lift ξ p`. Pulling back the `R`-module structure on `M` along
`SymmetricAlgebra.lift ξ` equips `M` with a `SymmetricAlgebra R M`-module structure, and extending
`LinearMap.id : M →ₗ[R] M` via `SymmetricAlgebra.mkDerivation` produces a derivation
`SymmetricAlgebra R M → M`, giving the **gradient** `p.gradient ξ` (and bundled linear map
`SymmetricAlgebra.gradientLinear ξ`).

From the derivation structure follow `R`-linearity in `p`, vanishing on scalars,
`(ι R M x).gradient ξ = x` on generators, the Leibniz product rule, and the power rule. Pairing
`p.gradient ξ` with any linear form `η : Module.Dual R M` recovers the directional derivative
`SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv η p)`. In the coordinates of a finite basis `b`,
`p.gradient ξ` agrees with the partial-derivative coordinate sum
`∑ i, (∂ᵢ P)(ξ(b₁), …, ξ(bₙ)) • bᵢ` (`SymmetricAlgebra.gradient_eq_sum`).

## Main definitions

* `SymmetricAlgebra.gradientLinear`: the gradient at `ξ : Module.Dual R M`, bundled as an
  `R`-linear map `SymmetricAlgebra R M →ₗ[R] M`.
* `SymmetricAlgebra.gradient`: the gradient vector `p.gradient ξ` in `M` of
  `p : SymmetricAlgebra R M` at a linear form `ξ : Module.Dual R M`.

## Main results

* `SymmetricAlgebra.apply_gradient`: for every `η : Module.Dual R M`,
  `η (p.gradient ξ) = SymmetricAlgebra.lift ξ (SymmetricAlgebra.pderiv η p)`.
* `SymmetricAlgebra.apply_gradient_self_of_mem_homogeneousSubmodule`: Euler's identity
  `ξ (p.gradient ξ) = n • SymmetricAlgebra.lift ξ p` for homogeneous `p` of degree `n`.
* `SymmetricAlgebra.gradient_eq_sum`: coordinate expansion of `p.gradient ξ` in a finite basis.
* `SymmetricAlgebra.gradient_ι`, `SymmetricAlgebra.gradient_algebraMap`,
  `SymmetricAlgebra.gradient_mul`, `SymmetricAlgebra.gradient_pow`: generator, scalar, product,
  and power rules.
* `SymmetricAlgebra.gradient_map`: naturality of gradients along linear maps.

## References

* N. Bourbaki, *Algebra*, Chapters 1–3, Springer (1989), Chapter III, §6 (symmetric algebras and
  polynomial functions on the dual).
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (functional derivatives of polynomial functions on `𝔤*`).
-/

public section

namespace SymmetricAlgebra

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

private noncomputable abbrev gradientModule (ξ : Module.Dual R M) :
    Module (SymmetricAlgebra R M) M :=
  Module.compHom M (lift ξ).toRingHom

private theorem gradientScalarTower (ξ : Module.Dual R M) :
    letI := gradientModule ξ
    IsScalarTower R (SymmetricAlgebra R M) M :=
  letI := gradientModule ξ
  { smul_assoc := fun r p m ↦ by
      have h : (r • p) • m = lift ξ (r • p) • m := rfl
      have h' : r • (p • m) = r • (lift ξ p • m) := rfl
      rw [h, h', map_smul, smul_assoc] }

private noncomputable def gradientDerivation (ξ : Module.Dual R M) :
    letI := gradientModule ξ
    Derivation R (SymmetricAlgebra R M) M :=
  letI := gradientModule ξ
  letI := gradientScalarTower ξ
  mkDerivation (LinearMap.id : M →ₗ[R] M)

/-- The gradient at `ξ` bundled as an `R`-linear map `SymmetricAlgebra R M →ₗ[R] M`. -/
noncomputable def gradientLinear (ξ : Module.Dual R M) : SymmetricAlgebra R M →ₗ[R] M :=
  letI := gradientModule ξ
  (gradientDerivation ξ).toLinearMap

/-- The gradient at `ξ ∈ M*` of `p : SymmetricAlgebra R M` read as a polynomial function on `M*`:
the value at `p` of the unique `R`-derivation `SymmetricAlgebra R M → M` (with
`SymmetricAlgebra R M` acting on `M` via `SymmetricAlgebra.lift ξ`) sending each generator
`ι R M x` to `x`. -/
noncomputable def gradient (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) : M :=
  gradientLinear ξ p

@[simp]
theorem gradientLinear_apply (ξ : Module.Dual R M) (p : SymmetricAlgebra R M) :
    gradientLinear ξ p = p.gradient ξ :=
  (rfl)

@[simp]
theorem gradient_zero (ξ : Module.Dual R M) :
    (0 : SymmetricAlgebra R M).gradient ξ = 0 :=
  map_zero (gradientLinear ξ)

@[simp]
theorem gradient_add (p q : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (p + q).gradient ξ = p.gradient ξ + q.gradient ξ :=
  map_add (gradientLinear ξ) p q

@[simp]
theorem gradient_smul (r : R) (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (r • p).gradient ξ = r • p.gradient ξ :=
  map_smul (gradientLinear ξ) r p

theorem gradient_sum {α : Type*} (s : Finset α)
    (f : α → SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (∑ a ∈ s, f a).gradient ξ = ∑ a ∈ s, (f a).gradient ξ :=
  map_sum (gradientLinear ξ) f s

/-- Every scalar in `SymmetricAlgebra R M` has zero gradient. -/
@[simp]
theorem gradient_algebraMap (r : R) (ξ : Module.Dual R M) :
    (algebraMap R (SymmetricAlgebra R M) r).gradient ξ = 0 :=
  letI := gradientModule ξ
  Derivation.map_algebraMap (gradientDerivation ξ) r

@[simp]
theorem gradient_one (ξ : Module.Dual R M) :
    (1 : SymmetricAlgebra R M).gradient ξ = 0 :=
  letI := gradientModule ξ
  (gradientDerivation ξ).map_one_eq_zero

@[simp]
theorem gradient_natCast (n : ℕ) (ξ : Module.Dual R M) :
    (n : SymmetricAlgebra R M).gradient ξ = 0 := by
  simpa using gradient_algebraMap (R := R) (M := M) (n : R) ξ

@[simp]
theorem gradient_ofNat (n : ℕ) [n.AtLeastTwo] (ξ : Module.Dual R M) :
    (ofNat(n) : SymmetricAlgebra R M).gradient ξ = 0 :=
  gradient_natCast n ξ

/-- The gradient of a symmetric generator `ι x` is `x` at every `ξ`. -/
@[simp]
theorem gradient_ι (x : M) (ξ : Module.Dual R M) :
    (ι R M x).gradient ξ = x :=
  letI := gradientModule ξ
  letI := gradientScalarTower ξ
  mkDerivation_ι (LinearMap.id : M →ₗ[R] M) x

/-- **Product rule for `gradient`.** -/
@[simp]
theorem gradient_mul (p q : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (p * q).gradient ξ = lift ξ p • q.gradient ξ + lift ξ q • p.gradient ξ :=
  letI := gradientModule ξ
  (gradientDerivation ξ).leibniz p q

/-- **Power rule for `gradient`.** -/
@[simp]
theorem gradient_pow (p : SymmetricAlgebra R M) (n : ℕ) (ξ : Module.Dual R M) :
    (p ^ n).gradient ξ = (n • lift ξ p ^ (n - 1)) • p.gradient ξ := by
  let := gradientModule ξ
  have h : (p ^ n).gradient ξ = n • (lift ξ (p ^ (n - 1)) • p.gradient ξ) :=
    (gradientDerivation ξ).leibniz_pow p n
  rw [h, map_pow, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_eq_mul]

/-- **Coordinate-free pairing formula.** Every linear form `η : Module.Dual R M` pairs with
`p.gradient ξ` to give the directional derivative `SymmetricAlgebra.pderiv η p` evaluated at `ξ`. -/
theorem apply_gradient (p : SymmetricAlgebra R M) (ξ η : Module.Dual R M) :
    η (p.gradient ξ) = lift ξ (pderiv η p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul a b ha hb => simp [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- **Euler's homogeneous identity for `gradient`.** Pairing the gradient at `ξ` of a
homogeneous symmetric tensor of degree `n` with `ξ` itself recovers
`n • SymmetricAlgebra.lift ξ p`. -/
theorem apply_gradient_self_of_mem_homogeneousSubmodule
    {n : ℕ} {p : SymmetricAlgebra R M}
    (hp : p ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n) (ξ : Module.Dual R M) :
    ξ (p.gradient ξ) = n • lift ξ p := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y _ _ _ ihx ihy => simp [ihx, ihy, smul_add]
  | mem_mul m hm i x _ ih =>
    obtain ⟨y, rfl⟩ := hm
    simp only [gradient_mul, map_add, LinearMap.map_smul, gradient_ι, map_mul, lift_ι_apply,
      smul_eq_mul, ih, nsmul_eq_mul, Nat.cast_succ]
    ring

/-- **Naturality (chain rule) of `gradient` along a linear map.** -/
theorem gradient_map {N : Type*} [AddCommMonoid N] [Module R N] (g : M →ₗ[R] N)
    (p : SymmetricAlgebra R M) (ξ : Module.Dual R N) :
    (map R g p).gradient ξ = g (p.gradient (ξ ∘ₗ g)) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- The `i`-th coordinate of `p.gradient ξ` is the partial derivative along `b.coord i`
evaluated at `ξ`. -/
@[simp]
theorem _root_.Module.Basis.repr_gradient {ι : Type*} (b : Module.Basis ι R M)
    (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) (i : ι) :
    b.repr (p.gradient ξ) i = lift ξ (pderiv (b.coord i) p) :=
  apply_gradient p ξ (b.coord i)

/-- **Coordinate expansion of `gradient`.** In a finite basis `b`, `p.gradient ξ` is the
partial-derivative sum `∑ i, (∂ᵢ P)(ξ(b₁), …, ξ(bₙ)) • bᵢ`. -/
theorem gradient_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R M)
    (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    p.gradient ξ =
      ∑ i, MvPolynomial.eval (fun j ↦ ξ (b j))
          (MvPolynomial.pderiv i (equivMvPolynomial b p)) • b i := by
  classical
  refine b.ext_elem fun i ↦ ?_
  simp [← equivMvPolynomial_pderiv_coord, ← b.lift_apply_eq_eval_equivMvPolynomial,
    Finsupp.single_apply]

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[simp]
theorem gradient_neg (p : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (-p).gradient ξ = -(p.gradient ξ) :=
  map_neg (gradientLinear ξ) p

@[simp]
theorem gradient_sub (p q : SymmetricAlgebra R M) (ξ : Module.Dual R M) :
    (p - q).gradient ξ = p.gradient ξ - q.gradient ξ :=
  map_sub (gradientLinear ξ) p q

@[simp]
theorem gradient_intCast (z : ℤ) (ξ : Module.Dual R M) :
    (z : SymmetricAlgebra R M).gradient ξ = 0 := by
  simpa using gradient_algebraMap (R := R) (M := M) (z : R) ξ

end CommRing

end SymmetricAlgebra
