/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.Algebra.MvPolynomial.Monomial
import TauCeti.GroupTheory.Perm.Partition

/-!
# Power sums over the cycle type of a permutation

Let `π` be a permutation of a finite set `α`, with cycle lengths `ρ₁, ρ₂, …` (fixed points
counted as cycles of length one), and let `p_ρ = ∏ᵢ p_{ρᵢ}` be the corresponding product of power
sums in the variables `x_i`, `i ∈ σ`.  Expanding the product chooses one variable for each cycle
of `π`, that is, a colouring `f : α → σ` constant on the cycles of `π`:

`p_ρ = ∑_{f : α → σ, f ∘ π = f} ∏_{a ∈ α} x_{f a}`.

So the coefficient of `x^d` in `p_ρ` is the number of `π`-invariant colourings of `α` using each
colour `i` exactly `d i` times.  This is the combinatorial half of the Frobenius formula for the
permutation characters of the symmetric group: an invariant colouring with prescribed colour
multiplicities is a tabloid fixed by `π`, so these coefficients are the values of the permutation
characters of the Young permutation modules.

## Main results

* `TauCeti.psumPart_isSymmetric` and `TauCeti.isHomogeneous_psumPart`: a product of power sums
  over a partition of `n` is symmetric and homogeneous of degree `n`.
* `TauCeti.psumPart_partition_eq_sum_prod_X`: **the power-sum product over the cycle type of `π`
  is the generating function of the `π`-invariant colourings.**
* `TauCeti.coeff_psumPart_partition`: its coefficient at `x^d` counts the `π`-invariant colourings
  with `d i` points of each colour `i`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Proposition 7.7.1 and Section 7.18.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset MvPolynomial

variable {σ : Type*} (R : Type*) [CommSemiring R]

/-- **A product of power sums is a symmetric polynomial**, each factor being symmetric. -/
theorem psumPart_isSymmetric [Fintype σ] {n : ℕ} (μ : n.Partition) :
    (psumPart σ R μ).IsSymmetric := by
  rw [psumPart]
  refine Multiset.prod_induction _ _ (fun _ _ => IsSymmetric.mul) IsSymmetric.one fun p hp => ?_
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hp
  exact psum_isSymmetric σ R k

/-- The power sum `p_k = ∑ᵢ xᵢ ^ k` is homogeneous of degree `k`. -/
theorem isHomogeneous_psum [Fintype σ] (k : ℕ) : (psum σ R k).IsHomogeneous k :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k

/-- **A product of power sums is homogeneous**, of degree the number its partition partitions. -/
theorem isHomogeneous_psumPart [Fintype σ] {n : ℕ} (μ : n.Partition) :
    (psumPart σ R μ).IsHomogeneous n := by
  have key : ∀ s : Multiset ℕ, ((s.map (psum σ R)).prod).IsHomogeneous s.sum := fun s => by
    induction s using Multiset.induction_on with
    | empty => exact isHomogeneous_one σ R
    | cons k s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      exact (isHomogeneous_psum R k).mul ih
  rw [psumPart]
  have h := key μ.parts
  rwa [μ.parts_sum] at h

variable {α : Type*}

/-- A colouring fixed by `π` is constant along the cycles of `π`. -/
private theorem apply_eq_of_sameCycle [Finite α] {π : Perm α} {f : α → σ} (hf : f ∘ π = f) {a b : α}
    (h : π.SameCycle a b) : f a = f b := by
  have hpow : ∀ i : ℕ, f ((π ^ i) a) = f a := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Perm.mul_apply, ← Function.comp_apply (f := f) (g := π), hf, ih]
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact (hpow i).symm

/-- The `π`-invariant colourings are the colourings of the cycles of `π`. -/
private def invariantColouringEquiv [Finite α] (π : Perm α) :
    (Quotient (SameCycle.setoid π) → σ) ≃ {f : α → σ // f ∘ π = f} where
  toFun g := ⟨fun a => g (Quotient.mk _ a), funext fun a =>
    congrArg g (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl π a)))⟩
  invFun f := Quotient.lift f.1 fun _ _ h => apply_eq_of_sameCycle f.2 h
  left_inv _ := funext fun c => Quotient.inductionOn c fun _ => rfl
  right_inv _ := rfl

private theorem invariantColouringEquiv_apply_coe [Finite α] (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) (a : α) :
    (invariantColouringEquiv π g : α → σ) a = g (Quotient.mk _ a) :=
  (rfl)

variable [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]

/-- **The power-sum product over the cycle type of `π` is the generating function of the
`π`-invariant colourings**: `p_ρ = ∑_{f ∘ π = f} ∏_a x_{f a}`, where `ρ` is the cycle type of `π`
with its fixed points counted as parts equal to one. -/
theorem psumPart_partition_eq_sum_prod_X (π : Perm α) :
    psumPart σ R π.partition =
      ∑ f ∈ univ.filter fun f : α → σ => f ∘ π = f, ∏ a, X (f a) := by
  let m : α → Quotient (SameCycle.setoid π) := Quotient.mk _
  -- `TauCeti.fullCycleType_eq_map_card_filter` is stated with classical decidability; working with
  -- the same instance on the cycles keeps its fibre cardinalities literally the ones below.
  let _ : DecidableEq (Quotient (SameCycle.setoid π)) := fun a b => Classical.propDecidable (a = b)
  let _ : Fintype (Quotient (SameCycle.setoid π)) := Fintype.ofFinite _
  -- The parts of the cycle type are the sizes of the cycles, that is, of the fibres of `m`.
  have hparts : π.partition.parts =
      (univ : Finset (Quotient (SameCycle.setoid π))).val.map
        fun c => Fintype.card {a // m a = c} := by
    rw [← fullCycleType_def, fullCycleType_eq_map_card_filter π m
        fun x y => (@Quotient.eq _ (SameCycle.setoid π) x y).symm,
      image_univ_of_surjective Quotient.mk_surjective]
    exact Multiset.map_congr rfl fun c _ => (Fintype.card_subtype _).symm
  -- Expanding the product of power sums chooses one colour for each cycle.
  rw [psumPart, hparts, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp only [Function.comp_apply, psum]
  rw [Fintype.prod_sum, Finset.sum_subtype (univ.filter fun f : α → σ => f ∘ π = f)
    (p := fun f => f ∘ π = f) fun f => by rw [mem_filter, and_iff_right (mem_univ f)]]
  refine Fintype.sum_equiv (invariantColouringEquiv π) _ _ fun g => ?_
  simp only [invariantColouringEquiv_apply_coe]
  rw [← Fintype.prod_fiberwise' m fun c => X (g c)]
  exact Finset.prod_congr rfl fun c _ => by rw [Finset.prod_const, Finset.card_univ]

/-- **The coefficients of the power-sum product over the cycle type of `π` count invariant
colourings**: the coefficient of `x^d` is the number of colourings `f : α → σ` fixed by `π` that
use each colour `i` exactly `d i` times. -/
theorem coeff_psumPart_partition (π : Perm α) (d : σ →₀ ℕ) :
    (psumPart σ R π.partition).coeff d =
      #{f : α → σ | f ∘ π = f ∧ ∀ i, #{a | f a = i} = d i} := by
  classical
  have hX : ∀ f : α → σ, ∏ a, (X (f a) : MvPolynomial σ R) =
      monomial (Multiset.toFinsupp (univ.val.map f)) 1 := fun f => by
    rw [← prod_map_X_eq_monomial, Multiset.map_map]
    rfl
  have hcontent : ∀ f : α → σ,
      Multiset.toFinsupp (univ.val.map f) = d ↔ ∀ i, #{a | f a = i} = d i := fun f => by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun i => ?_
    rw [Multiset.toFinsupp_apply, Multiset.count_map, Finset.card_def, Finset.filter_val]
    simp only [eq_comm]
  rw [psumPart_partition_eq_sum_prod_X, coeff_sum]
  simp only [hX, coeff_monomial, sum_boole, filter_filter, hcontent]

end TauCeti
