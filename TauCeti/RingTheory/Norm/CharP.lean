/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerBasis
public import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Norms of `p`-th roots in characteristic `p`

Let `R` be a reduced ring of exponential characteristic `p` and `S` a free `R`-algebra of rank
`p`. If `x ^ p = c` lies in `R`, then `Norm(x) ^ p = Norm(c) = c ^ p`, and since the Frobenius of
`R` is injective, `Norm(x) = c` (`TauCeti.Algebra.norm_eq_of_pow_eq_algebraMap`).

The basic example is a free algebra `B` over a field `k` of exponential characteristic `p` with a
power basis `1, α, …, α ^ (p - 1)` such that `α ^ p = a` lies in `k`, for instance the purely
inseparable extension `k(a ^ (1 / p))` when `a` is not a `p`-th power. Since the Frobenius of
`T ⊗[k] B` is additive for every `k`-algebra `T`,

```text
(∑ᵢ xᵢ ⊗ αⁱ) ^ p = ∑ᵢ aⁱ xᵢ ^ p ∈ T,
```

and the norm form of `B` in this basis is the diagonal form of degree `p`

```text
Norm(∑ᵢ Xᵢ ⊗ αⁱ) = ∑ᵢ aⁱ Xᵢ ^ p ∈ k[X₀, …, X_{p-1}].
```

It is computed in the reduced polynomial ring and specialized to every `T` along
`TauCeti.Algebra.norm_rTensor`, so the formula `Norm(∑ᵢ xᵢ ⊗ αⁱ) = ∑ᵢ aⁱ xᵢ ^ p` holds over every
commutative `k`-algebra `T`, reduced or not. Consequently every `y ∈ T ⊗[k] B` satisfies
`y ^ p = Norm(y)`: the `p`-th power map of `T ⊗[k] B` is its norm, followed by the inclusion of
`T`.

## Main results

* `TauCeti.Algebra.norm_eq_of_pow_eq_algebraMap`: in a free algebra of rank `p` over a reduced ring
  of exponential characteristic `p`, the norm of a `p`-th root of `c` is `c`.
* `PowerBasis.sum_tmul_gen_pow_pow_char`: `(∑ᵢ xᵢ ⊗ αⁱ) ^ p = ∑ᵢ aⁱ xᵢ ^ p`.
* `PowerBasis.norm_sum_X_tmul_gen_pow`: the norm form of `B` in the power basis is
  `∑ᵢ aⁱ Xᵢ ^ p`.
* `PowerBasis.norm_sum_tmul_gen_pow`: `Norm(∑ᵢ xᵢ ⊗ αⁱ) = ∑ᵢ aⁱ xᵢ ^ p` over every `k`-algebra.
* `PowerBasis.pow_char_eq_algebraMap_norm`: `y ^ p = Norm(y)` for every `y ∈ T ⊗[k] B`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
-/

public section

open MvPolynomial
open scoped TensorProduct

namespace TauCeti

/-- **The norm of a `p`-th root.** In a free algebra of rank `p` over a reduced ring of exponential
characteristic `p`, an element whose `p`-th power is the scalar `c` has norm `c`. Indeed
`Norm(x) ^ p = Norm(x ^ p) = c ^ p`, and the Frobenius of a reduced ring is injective. -/
theorem Algebra.norm_eq_of_pow_eq_algebraMap {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] (p : ℕ) [ExpChar R p] [IsReduced R] (hrank : Module.finrank R S = p)
    {x : S} {c : R} (h : x ^ p = algebraMap R S c) : Algebra.norm R x = c :=
  frobenius_inj R p <| by
    rw [frobenius_def, frobenius_def, ← map_pow, h, Algebra.norm_algebraMap, hrank]

end TauCeti

namespace PowerBasis

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B] (pb : PowerBasis k B)
variable {p : ℕ} [ExpChar k p] {a : k}

/-- **The `p`-th power of an element in coordinates.** If `α ^ p = a` for the generator `α` of a
power basis over a field of exponential characteristic `p`, then in `T ⊗[k] B` the `p`-th power of
`∑ᵢ xᵢ ⊗ αⁱ` is the scalar `∑ᵢ aⁱ xᵢ ^ p` of `T`. -/
theorem sum_tmul_gen_pow_pow_char (hgen : pb.gen ^ p = algebraMap k B a)
    {T : Type*} [CommRing T] [Algebra k T] (x : Fin pb.dim → T) :
    (∑ i, x i ⊗ₜ[k] (pb.gen ^ (i : ℕ))) ^ p =
      algebraMap T (T ⊗[k] B) (∑ i : Fin pb.dim, a ^ (i : ℕ) • x i ^ p) := by
  nontriviality T ⊗[k] B
  have : ExpChar (T ⊗[k] B) p := expChar_of_injective_algebraMap (algebraMap k _).injective p
  -- the Frobenius of `T ⊗[k] B` is additive, and `(αⁱ) ^ p = aⁱ` is a scalar
  rw [sum_pow_char, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.tmul_pow, ← pow_mul, mul_comm, pow_mul, hgen, ← map_pow,
    Algebra.algebraMap_eq_smul_one (a ^ (i : ℕ)), ← TensorProduct.smul_tmul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **The norm form of a `p`-th root extension.** Let `k` be a field of exponential characteristic
`p` and `α` the generator of a power basis of rank `p` with `α ^ p = a`. Then the norm form of `B`
in this basis is `Norm(∑ᵢ Xᵢ ⊗ αⁱ) = ∑ᵢ aⁱ Xᵢ ^ p`. -/
theorem norm_sum_X_tmul_gen_pow (hdim : pb.dim = p) (hgen : pb.gen ^ p = algebraMap k B a) :
    Algebra.norm (MvPolynomial (Fin pb.dim) k)
      (∑ i : Fin pb.dim, (X i : MvPolynomial (Fin pb.dim) k) ⊗ₜ[k] (pb.gen ^ (i : ℕ))) =
      ∑ i : Fin pb.dim, a ^ (i : ℕ) • X i ^ p := by
  have : Module.Free k B := .of_basis pb.basis
  refine TauCeti.Algebra.norm_eq_of_pow_eq_algebraMap p ?_ (pb.sum_tmul_gen_pow_pow_char hgen _)
  rw [Module.finrank_baseChange, pb.finrank, hdim]

/-- **The norm in coordinates.** Let `k` be a field of exponential characteristic `p` and `α` the
generator of a power basis of rank `p` with `α ^ p = a`. Then over every commutative `k`-algebra
`T`, reduced or not, `Norm(∑ᵢ xᵢ ⊗ αⁱ) = ∑ᵢ aⁱ xᵢ ^ p`. -/
theorem norm_sum_tmul_gen_pow (hdim : pb.dim = p) (hgen : pb.gen ^ p = algebraMap k B a)
    {T : Type*} [CommRing T] [Algebra k T] (x : Fin pb.dim → T) :
    Algebra.norm T (∑ i, x i ⊗ₜ[k] (pb.gen ^ (i : ℕ))) =
      ∑ i : Fin pb.dim, a ^ (i : ℕ) • x i ^ p := by
  have : Module.Free k B := .of_basis pb.basis
  have h := TauCeti.Algebra.norm_sum_tmul_eq_aeval pb.basis x
  simp only [pb.coe_basis] at h
  rw [h, pb.norm_sum_X_tmul_gen_pow hdim hgen]
  simp

/-- **The `p`-th power is the norm.** Let `k` be a field of exponential characteristic `p` and `α`
the generator of a power basis of rank `p` with `α ^ p = a`. Then for every commutative `k`-algebra
`T`, every `y ∈ T ⊗[k] B` satisfies `y ^ p = Norm(y)`, the norm being viewed in `T ⊗[k] B`. -/
theorem pow_char_eq_algebraMap_norm (hdim : pb.dim = p) (hgen : pb.gen ^ p = algebraMap k B a)
    {T : Type*} [CommRing T] [Algebra k T] (y : T ⊗[k] B) :
    y ^ p = algebraMap T (T ⊗[k] B) (Algebra.norm T y) := by
  -- write `y = ∑ᵢ yᵢ ⊗ αⁱ` in the basis of `T ⊗[k] B` induced by the power basis
  obtain ⟨x, rfl⟩ : ∃ x : Fin pb.dim → T, ∑ i, x i ⊗ₜ[k] (pb.gen ^ (i : ℕ)) = y :=
    ⟨(Algebra.TensorProduct.basis T pb.basis).repr y, by
      conv_rhs => rw [← (Algebra.TensorProduct.basis T pb.basis).sum_repr y]
      simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']⟩
  rw [pb.sum_tmul_gen_pow_pow_char hgen, pb.norm_sum_tmul_gen_pow hdim hgen]

end PowerBasis
