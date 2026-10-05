/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.GroupTheory.Perm.FiberSubgroup
import TauCeti.Algebra.MvPolynomial.Monomial
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete
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
* `TauCeti.sum_card_smul_psumPart_partition`: **averaged over `Equiv.Perm α` against the number of
  invariant colourings with fiber sizes `r`, the power-sum products give `(card α)! • ∏ᵢ h_{r i}`.**

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

variable [Fintype α] [DecidableEq α] [Fintype σ]

section InvariantColouring

/-- Local decidable equality for colourings in the power-sum expansion. -/
noncomputable local instance instDecidableEqPowerSumColour : DecidableEq σ := Classical.decEq σ

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

end InvariantColouring

/-! ### Averaging over the symmetric group -/

section Average

variable [DecidableEq σ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Averaging power sums against invariant colourings gives complete homogeneous polynomials**:
for `r : ι → ℕ` with total `card α`,

`∑_π #{c : α → ι | c ∘ π = c, c has fibers of sizes r} • p_{ρ(π)} = (card α)! • ∏ᵢ h_{r i}`.

The count on the left is the value at `π` of the permutation character on the colourings with
fiber sizes `r`, so this is the statement that the Frobenius characteristic of that permutation
representation is the product `∏ᵢ h_{r i}`.  Both sides expand over colourings of `α` by pairs
`ι × σ`: the left side counts each pair colouring once for every permutation preserving it, and
`TauCeti.sum_natCard_fiberSubgroup_smul` evaluates that count. -/
theorem sum_card_smul_psumPart_partition (r : ι → ℕ) (hr : ∑ i, r i = Fintype.card α) :
    ∑ π : Perm α, #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = r i} •
        psumPart σ R π.partition =
      (Fintype.card α).factorial • ∏ i, hsymm σ R (r i) := by
  -- a pair of colourings, one fixed by `π` with fibers of sizes `r` and one fixed by `π`, is a
  -- colouring by pairs fixed by `π` whose first coordinate has fibers of sizes `r`
  have h1 : ∀ π : Perm α,
      #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = r i} • psumPart σ R π.partition =
        ∑ h : α → ι × σ, if h ∘ π = h ∧ ∀ i, #{a | (h a).1 = i} = r i
          then ∏ a, (X (h a).2 : MvPolynomial σ R) else 0 := fun π => by
    rw [psumPart_partition_eq_sum_prod_X, ← sum_const, ← sum_product', ← sum_filter]
    refine sum_equiv (arrowProdEquivProdArrow α (fun _ => ι) (fun _ => σ)).symm (fun x => ?_)
      fun x _ => rfl
    simp only [mem_product, mem_filter, mem_univ, true_and, funext_iff, Function.comp_apply,
      arrowProdEquivProdArrow, coe_fn_symm_mk, Prod.ext_iff, forall_and]
    tauto
  -- the term of a colouring by pairs, read off its fiber sizes `A : ι × σ → ℕ`
  let F : (ι × σ → ℕ) → MvPolynomial σ R := fun A =>
    if ∀ i, ∑ s, A (i, s) = r i then ∏ s, X s ^ ∑ i, A (i, s) else 0
  have h2 : ∀ h : α → ι × σ,
      (∑ π : Perm α, if h ∘ π = h ∧ ∀ i, #{a | (h a).1 = i} = r i
        then ∏ a, (X (h a).2 : MvPolynomial σ R) else 0) =
        Nat.card (fiberSubgroup h) • F fun k => #{a | h a = k} := fun h => by
    have hcard : Nat.card (fiberSubgroup h) = #{π : Perm α | h ∘ π = h} := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun π => by
        rw [mem_fiberSubgroup, funext_iff]; rfl)
    -- the fibers of the two coordinates of `h` are unions of fibers of `h`
    have hfst : ∀ i, #{a | (h a).1 = i} = ∑ s, #{a | h a = (i, s)} := fun i => by
      rw [card_eq_sum_card_fiberwise (f := fun a => (h a).2) (t := univ) fun _ _ => mem_univ _]
      exact sum_congr rfl fun s _ => by
        rw [filter_filter]
        exact congrArg card (filter_congr fun a _ => by simp [Prod.ext_iff])
    have hsnd : ∀ s, #{a | (h a).2 = s} = ∑ i, #{a | h a = (i, s)} := fun s => by
      rw [card_eq_sum_card_fiberwise (f := fun a => (h a).1) (t := univ) fun _ _ => mem_univ _]
      exact sum_congr rfl fun i _ => by
        rw [filter_filter]
        exact congrArg card (filter_congr fun a _ => by simp [Prod.ext_iff, and_comm])
    have hX : ∏ a, (X (h a).2 : MvPolynomial σ R) = ∏ s, X s ^ #{a | (h a).2 = s} := by
      rw [← prod_fiberwise univ fun a => (h a).2]
      exact prod_congr rfl fun s _ => by
        rw [prod_congr rfl fun a ha => by rw [(mem_filter.1 ha).2], prod_const]
    simp only [F, ← hfst, ← hsnd, ← hX, hcard]
    split_ifs with hC
    · simp only [hC, implies_true, and_true]
      rw [← sum_filter, sum_const]
    · simp [hC]
  rw [sum_congr rfl fun π _ => h1 π, sum_comm, sum_congr rfl fun h _ => h2 h,
    sum_natCard_fiberSubgroup_smul]
  congr 1
  -- a fiber-size function with the right row sums is a family of exponent vectors, one per row
  simp only [F]
  rw [← sum_filter]
  simp_rw [hsymm_eq_sum_piAntidiag]
  rw [prod_univ_sum]
  refine sum_nbij' (fun A i s => A (i, s)) (fun D p => D p.1 p.2) (fun A hA => ?_)
    (fun D hD => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun A _ => ?_)
  · rw [mem_filter] at hA
    simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_univ, implies_true, and_true]
    exact hA.2
  · simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_univ, implies_true, and_true] at hD
    simp only [mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true, hD]
    rw [Fintype.sum_prod_type]
    simp only [hD, hr]
  · rw [prod_comm]
    exact prod_congr rfl fun s _ => (prod_pow_eq_pow_sum _ _ _).symm

end Average

end TauCeti
