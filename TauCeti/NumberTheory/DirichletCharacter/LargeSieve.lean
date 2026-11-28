/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# Primitive character sums and exponential sums at one modulus

Let `χ` be a primitive Dirichlet character modulo `q`. Its values are recovered from the additive
characters of `ZMod q` through the Gauss sum of `χ⁻¹`:
`τ(χ⁻¹) χ(n) = ∑_{u ∈ (ZMod q)ˣ} χ⁻¹(u) e(u n / q)`. Hence a weighted character sum
`∑_j a_j χ(M + j)`, multiplied by `τ(χ⁻¹)`, is the `χ⁻¹`-transform of the values
`S(u / q)` of the exponential sum `S(t) = ∑_j a_j e((M + j) t)` at the reduced fractions with
denominator `q`. Orthogonality of the characters modulo `q` and `|τ(χ⁻¹)| ^ 2 = q` then give
`(q / φ(q)) ∑_{χ primitive mod q} |∑_j a_j χ(M + j)| ^ 2 ≤ ∑_{u ∈ (ZMod q)ˣ} |S(u / q)| ^ 2`,
the single-modulus step of the Bombieri–Davenport reduction of the large sieve for primitive
characters to the additive large sieve.

## Main results

* `DirichletCharacter.IsPrimitive.gaussSum_inv_mul_apply_eq_sum_units`:
  `τ(χ⁻¹) χ(a) = ∑_u χ⁻¹(u) ψ(u a)` for a primitive `χ` and any additive character `ψ`.
* `DirichletCharacter.IsPrimitive.gaussSum_inv_mul_sum_eq`: the weighted sum form with the
  standard additive character.
* `DirichletCharacter.sum_norm_sum_units_inv_mul_sq`: Parseval's identity
  `∑_χ |∑_u χ⁻¹(u) F(u)| ^ 2 = φ(q) ∑_u |F(u)| ^ 2` over all characters modulo `q`.
* `DirichletCharacter.div_totient_mul_sum_isPrimitive_norm_sum_sq_le`: the inequality displayed
  above.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 16, §16.2, proof of Theorem 16.2.
-/

public section

open Finset

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- **Gauss expansion of a primitive character.** For a primitive Dirichlet character `χ` modulo
`q`, any additive character `ψ` of `ZMod q` and any residue `a`,
`τ(χ⁻¹, ψ) χ(a) = ∑_u χ⁻¹(u) ψ(u a)`, the sum being over the units of `ZMod q`. The residue `a`
need not be a unit. -/
theorem IsPrimitive.gaussSum_inv_mul_apply_eq_sum_units {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (ψ : AddChar (ZMod q) R) (a : ZMod q) :
    gaussSum χ⁻¹ ψ * χ a = ∑ u : (ZMod q)ˣ, χ⁻¹ u * ψ (u * a) := by
  have h := gaussSum_mulShift_of_isPrimitive ψ hχ.inv a
  rw [inv_inv] at h
  have hmap : ∑ u : (ZMod q)ˣ, χ⁻¹ u * ψ (u * a) =
      ∑ x ∈ univ.map ⟨Units.val, Units.val_injective⟩, χ⁻¹ x * ψ (x * a) :=
    (sum_map univ ⟨Units.val, Units.val_injective⟩ fun x : ZMod q ↦ χ⁻¹ x * ψ (x * a)).symm
  rw [mul_comm, ← h, gaussSum, hmap]
  refine (sum_congr rfl fun x _ ↦ by rw [AddChar.mulShift_apply, mul_comm a]).trans
    (sum_subset (subset_univ _) fun x _ hx ↦ ?_).symm
  rw [MulChar.map_nonunit _ fun hx' ↦ hx (mem_map.2 ⟨hx'.unit, mem_univ _, hx'.unit_spec⟩),
    zero_mul]

/-- **Gauss expansion of a finite character sum.** For a primitive Dirichlet character `χ` modulo
`q`, an integer `M` and coefficients `a : Fin H → ℂ`,
`τ(χ⁻¹) ∑_j a_j χ(M + j) = ∑_u χ⁻¹(u) S(u.val / q)`, where `τ` is the Gauss sum for the standard
additive character and `S(t) = ∑_j a_j e((M + j) t)`. -/
theorem IsPrimitive.gaussSum_inv_mul_sum_eq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (M : ℤ) (H : ℕ) (a : Fin H → ℂ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * ∑ j : Fin H, a j * χ ((M + (j : ℕ) : ℤ) : ZMod q) =
      ∑ u : (ZMod q)ˣ, χ⁻¹ u * ∑ j : Fin H, a j *
        (Real.fourierChar (((M : ℝ) + (j : ℕ)) * (((u : ZMod q).val : ℝ) / q)) : ℂ) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm, hχ.gaussSum_inv_mul_apply_eq_sum_units, mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [ZMod.stdAddChar_mul_intCast, mul_left_comm]
  push_cast
  rfl

/-- **Parseval's identity over the Dirichlet characters modulo `q`.** For every function `F` on
the units of `ZMod q`, `∑_χ |∑_u χ⁻¹(u) F(u)| ^ 2 = φ(q) ∑_u |F(u)| ^ 2`, the outer sum being over
all Dirichlet characters modulo `q`. -/
theorem sum_norm_sum_units_inv_mul_sq (F : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * F u‖ ^ 2 =
      q.totient * ∑ u : (ZMod q)ˣ, ‖F u‖ ^ 2 := by
  have key : ∑ χ : DirichletCharacter ℂ q,
      (∑ u : (ZMod q)ˣ, χ⁻¹ u * F u) * (starRingEnd ℂ) (∑ v : (ZMod q)ˣ, χ⁻¹ v * F v) =
        q.totient * ∑ u : (ZMod q)ˣ, F u * (starRingEnd ℂ) (F u) := by
    have hterm (χ : DirichletCharacter ℂ q) :
        (∑ u : (ZMod q)ˣ, χ⁻¹ u * F u) * (starRingEnd ℂ) (∑ v : (ZMod q)ˣ, χ⁻¹ v * F v) =
          ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
            F u * (starRingEnd ℂ) (F v) * (χ ((u : ZMod q))⁻¹ * χ v) := by
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ ?_
      have hconj : (starRingEnd ℂ) (χ⁻¹ (v : ZMod q)) = χ v := by
        rw [starRingEnd_apply, MulChar.star_apply', inv_inv]
      have hinv : χ⁻¹ (u : ZMod q) = χ (u : ZMod q)⁻¹ := by
        rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
      rw [map_mul, hconj, hinv]
      ring
    simp_rw [hterm]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (DirichletCharacter ℂ q))), ← mul_sum,
      sum_char_inv_mul_char_eq ℂ (Units.isUnit _), Units.val_inj, mul_ite, mul_zero,
      sum_ite_eq, mem_univ, ite_true, mul_sum]
    exact sum_congr rfl fun u _ ↦ mul_comm _ _
  have hcast : ((∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * F u‖ ^ 2 : ℝ) : ℂ) =
      ((q.totient * ∑ u : (ZMod q)ˣ, ‖F u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj']
    exact key
  exact_mod_cast hcast

open Classical in
/-- **Primitive character energy at one modulus.** For every integer `M` and coefficients
`a : Fin H → ℂ`, `(q / φ(q)) ∑_χ |∑_j a_j χ(M + j)| ^ 2 ≤ ∑_u |S(u.val / q)| ^ 2`, where `χ` runs
over the primitive Dirichlet characters modulo `q`, `u` over the units of `ZMod q`, and
`S(t) = ∑_j a_j e((M + j) t)`. -/
theorem div_totient_mul_sum_isPrimitive_norm_sum_sq_le (M : ℤ) (H : ℕ) (a : Fin H → ℂ) :
    (q : ℝ) / q.totient * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
        ‖∑ j : Fin H, a j * χ ((M + (j : ℕ) : ℤ) : ZMod q)‖ ^ 2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j : Fin H, a j *
        (Real.fourierChar (((M : ℝ) + (j : ℕ)) * (((u : ZMod q).val : ℝ) / q)) : ℂ)‖ ^ 2 := by
  set S : (ZMod q)ˣ → ℂ := fun u ↦ ∑ j : Fin H, a j *
    (Real.fourierChar (((M : ℝ) + (j : ℕ)) * (((u : ZMod q).val : ℝ) / q)) : ℂ)
  have hφ : (0 : ℝ) < q.totient := Nat.cast_pos.2 (Nat.totient_pos.2 (NeZero.pos q))
  have hprim (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
      (q : ℝ) * ‖∑ j : Fin H, a j * χ ((M + (j : ℕ) : ℤ) : ZMod q)‖ ^ 2 =
        ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * S u‖ ^ 2 := by
    rw [← hχ.gaussSum_inv_mul_sum_eq, norm_mul, mul_pow,
      hχ.inv.norm_gaussSum (ZMod.isPrimitive_stdAddChar q), Real.sq_sqrt (Nat.cast_nonneg q)]
  calc (q : ℝ) / q.totient * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
        (·.IsPrimitive), ‖∑ j : Fin H, a j * χ ((M + (j : ℕ) : ℤ) : ZMod q)‖ ^ 2
      = (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
          ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * S u‖ ^ 2) / q.totient := by
        rw [div_mul_eq_mul_div, mul_sum]
        exact congrArg (· / (q.totient : ℝ))
          (sum_congr rfl fun χ hχ ↦ hprim χ (mem_filter.1 hχ).2)
    _ ≤ (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * S u‖ ^ 2) / q.totient :=
        div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun _ _ _ ↦ sq_nonneg _) hφ.le
    _ = ∑ u : (ZMod q)ˣ, ‖S u‖ ^ 2 := by
        rw [sum_norm_sum_units_inv_mul_sq, mul_div_cancel_left₀ _ hφ.ne']

end DirichletCharacter
