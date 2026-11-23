/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Hyper-Kloosterman sums

For a finite commutative ring `R`, an additive character `ψ : AddChar R K` with values in a
commutative semiring `K`, a natural number `k` and a unit `r` of `R`, the (raw, unnormalized)
hyper-Kloosterman sum of rank `k` is

  `Kl_k(ψ, r) = ∑_{x₁ ⋯ xₖ = r} ψ (x₁ + ⋯ + xₖ)`,

the sum running over the `k`-tuples of units of `R` with product `r`. For `k = 2` and
`R = ZMod p` this is the classical Kloosterman sum `∑_{x ≠ 0} ψ (x + r / x)`. The definition is
total in the rank: at `k = 0` the only tuple is empty, with product `1`. Over a finite field,
for a nontrivial `ψ` and `k ≥ 1`, Deligne's estimate bounds `‖Kl_k(ψ, r)‖` by
`k * q ^ ((k - 1) / 2)`; these sums are the finite-field input of the moment method of Luo,
Rudnick and Sarnak for the Selberg eigenvalue conjecture, where they arise from powers of Gauss
sums.

## Main definitions

* `TauCeti.hyperKloosterman R k ψ r`: the hyper-Kloosterman sum of rank `k`.

## Main statements

* `TauCeti.hyperKloosterman_eq_sum_prod_eq`: the same sum over all `k`-tuples of elements of `R`
  with product `r`, every such entry being a unit.
* `TauCeti.sum_add_mul_prod_inv_eq_hyperKloosterman`: eliminating the last variable,
  `∑_{x : Fin n → Rˣ} ψ (∑ xᵢ + r (∏ xᵢ)⁻¹)` is the sum of rank `n + 1`.
* `TauCeti.hyperKloosterman_zero`, `TauCeti.hyperKloosterman_one`: the ranks zero and one.
* `TauCeti.hyperKloosterman_mulShift`: replacing `ψ` by `x ↦ ψ (a x)` moves the argument from
  `r` to `a ^ k r`.
* `TauCeti.hyperKloosterman_ringEquiv`, `TauCeti.hyperKloosterman_ringHomComp`: transport along
  an isomorphism of the finite ring and along a ring homomorphism of the coefficients.
* `TauCeti.hyperKloosterman_one_addChar_succ`: for the trivial additive character the sum of rank
  `k + 1` counts the tuples, `#Rˣ ^ k`.

## References

* N. M. Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Annals of Mathematics
  Studies 116, Princeton University Press, 1988, §4.0 and Theorem 4.1.1.
* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equations (3.18)–(3.20).
-/

public section

open Finset

namespace TauCeti

variable (R : Type*) [CommRing R] [Finite R] {K : Type*} [CommSemiring K]

/-- The hyper-Kloosterman sum of rank `k`: the sum of `ψ (x₁ + ⋯ + xₖ)` over the `k`-tuples of
units of `R` with product `r`. -/
noncomputable def hyperKloosterman (k : ℕ) (ψ : AddChar R K) (r : Rˣ) : K := by
  classical
  letI := Fintype.ofFinite R
  exact ∑ x : Fin k → Rˣ with ∏ i, x i = r, ψ (∑ i, (x i : R))

variable {R}

/-- The defining sum of `hyperKloosterman`, for any choice of the `Fintype` and decidability
instances. -/
theorem hyperKloosterman_def [Fintype R] [DecidableEq R] (k : ℕ) (ψ : AddChar R K) (r : Rˣ) :
    hyperKloosterman R k ψ r = ∑ x : Fin k → Rˣ with ∏ i, x i = r, ψ (∑ i, (x i : R)) := by
  unfold hyperKloosterman
  congr!

/-- The hyper-Kloosterman sum, as a sum over all `k`-tuples of elements of `R` with product `r`:
since `r` is a unit, so is every entry of such a tuple. -/
theorem hyperKloosterman_eq_sum_prod_eq [Fintype R] [DecidableEq R] (k : ℕ) (ψ : AddChar R K)
    (r : Rˣ) :
    hyperKloosterman R k ψ r = ∑ x : Fin k → R with ∏ i, x i = (r : R), ψ (∑ i, x i) := by
  rw [hyperKloosterman_def]
  refine sum_nbij (fun x i ↦ (x i : R)) (fun x hx ↦ ?_) (fun x _ y _ hxy ↦ ?_) (fun y hy ↦ ?_)
    fun _ _ ↦ rfl
  · rw [mem_filter] at hx ⊢
    exact ⟨mem_univ _, by rw [← hx.2, Units.coe_prod]⟩
  · funext i
    exact Units.ext (congrFun hxy i)
  · rw [mem_coe, mem_filter] at hy
    have hu (i : Fin k) : IsUnit (y i) :=
      isUnit_of_dvd_unit (dvd_prod_of_mem y (mem_univ i)) (hy.2 ▸ r.isUnit)
    refine ⟨fun i ↦ (hu i).unit, ?_, funext fun i ↦ (hu i).unit_spec⟩
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, Units.ext (by simp [Units.coe_prod, hy.2])⟩

/-- **Elimination of the last variable.** The sum over all `n`-tuples of units of
`ψ (x₁ + ⋯ + xₙ + r (x₁ ⋯ xₙ)⁻¹)` is the hyper-Kloosterman sum of rank `n + 1`: appending the
unit `r (x₁ ⋯ xₙ)⁻¹` identifies the `n`-tuples with the `(n + 1)`-tuples of product `r`. -/
theorem sum_add_mul_prod_inv_eq_hyperKloosterman [Fintype R] [DecidableEq R] (n : ℕ)
    (ψ : AddChar R K) (r : Rˣ) :
    ∑ x : Fin n → Rˣ, ψ (∑ i, (x i : R) + ((r * (∏ i, x i)⁻¹ : Rˣ) : R)) =
      hyperKloosterman R (n + 1) ψ r := by
  rw [hyperKloosterman_def]
  refine sum_nbij' (fun x ↦ Fin.snoc x (r * (∏ i, x i)⁻¹)) Fin.init (fun x _ ↦ ?_)
    (fun _ _ ↦ mem_univ _) (fun x _ ↦ Fin.init_snoc _ _) (fun x hx ↦ ?_) fun x _ ↦ ?_
  · simp [Fin.prod_snoc]
  · rw [mem_filter] at hx
    conv_rhs => rw [← Fin.snoc_init_self x]
    congr 1
    rw [← hx.2, Fin.prod_univ_castSucc]
    simp [Fin.init]
  · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- At rank zero the only tuple is the empty one, whose product is `1`. -/
@[simp]
theorem hyperKloosterman_zero [DecidableEq R] (ψ : AddChar R K) (r : Rˣ) :
    hyperKloosterman R 0 ψ r = if r = 1 then 1 else 0 := by
  have := Fintype.ofFinite R
  simp only [hyperKloosterman_def, sum_filter, Fintype.sum_unique, univ_eq_empty, prod_empty,
    sum_empty, AddChar.map_zero_eq_one, eq_comm (a := r)]

/-- At rank one the only tuple is `(r)`. -/
@[simp]
theorem hyperKloosterman_one (ψ : AddChar R K) (r : Rˣ) : hyperKloosterman R 1 ψ r = ψ r := by
  classical
  have := Fintype.ofFinite R
  simp [← sum_add_mul_prod_inv_eq_hyperKloosterman]

/-- Replacing `ψ` by `x ↦ ψ (a x)` multiplies the argument by `a ^ k`: scaling every coordinate
by `a` multiplies the product by `a ^ k`. -/
theorem hyperKloosterman_mulShift (k : ℕ) (ψ : AddChar R K) (a r : Rˣ) :
    hyperKloosterman R k (ψ.mulShift a) r = hyperKloosterman R k ψ (a ^ k * r) := by
  classical
  have := Fintype.ofFinite R
  simp only [hyperKloosterman_def]
  refine sum_nbij' (fun x i ↦ a * x i) (fun x i ↦ a⁻¹ * x i) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    (fun x _ ↦ by simp) (fun x _ ↦ by simp) fun x _ ↦ ?_
  · rw [mem_filter] at hx ⊢
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, hx.2]
    exact ⟨mem_univ _, rfl⟩
  · rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, hx.2, inv_pow,
      inv_mul_cancel_left]
  · simp [mul_sum]

/-- A ring isomorphism `e : R ≃+* S` of finite rings transports hyper-Kloosterman sums: the sum
for a character `ψ` of `S` at `e r` is the sum for `ψ ∘ e` at `r`. -/
theorem hyperKloosterman_ringEquiv {S : Type*} [CommRing S] [Finite S] (e : R ≃+* S) (k : ℕ)
    (ψ : AddChar S K) (r : Rˣ) :
    hyperKloosterman S k ψ (Units.map e r) =
      hyperKloosterman R k (ψ.compAddMonoidHom e.toAddMonoidHom) r := by
  classical
  have := Fintype.ofFinite R
  have := Fintype.ofFinite S
  simp only [hyperKloosterman_def]
  symm
  refine sum_nbij' (fun x i ↦ Units.map e (x i)) (fun x i ↦ Units.map e.symm (x i))
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun x _ ↦ ?_) (fun x _ ↦ ?_) fun x _ ↦ ?_
  · rw [mem_filter] at hx ⊢
    exact ⟨mem_univ _, by rw [← map_prod, hx.2]⟩
  · rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [← map_prod, hx.2]
    ext
    simp
  · ext
    simp
  · ext
    simp
  · simp

/-- A ring homomorphism `f` of the coefficients carries the hyper-Kloosterman sum of `ψ` to that
of `f ∘ ψ`. -/
theorem hyperKloosterman_ringHomComp {K' : Type*} [CommSemiring K'] (f : K →+* K') (k : ℕ)
    (ψ : AddChar R K) (r : Rˣ) :
    hyperKloosterman R k (f.toMonoidHom.compAddChar ψ) r = f (hyperKloosterman R k ψ r) := by
  classical
  have := Fintype.ofFinite R
  simp [hyperKloosterman_def, map_sum, MonoidHom.coe_compAddChar]

/-- For the trivial additive character the hyper-Kloosterman sum of rank `k + 1` counts the
`(k + 1)`-tuples of units with product `r`: the first `k` units are free and determine the last.
Over a finite field `F` this is `(#F - 1) ^ k`. -/
@[simp]
theorem hyperKloosterman_one_addChar_succ (k : ℕ) (r : Rˣ) :
    hyperKloosterman R (k + 1) (1 : AddChar R K) r = Nat.card Rˣ ^ k := by
  classical
  have := Fintype.ofFinite R
  rw [← sum_add_mul_prod_inv_eq_hyperKloosterman]
  simp [Nat.card_eq_fintype_card]

end TauCeti
