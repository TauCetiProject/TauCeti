/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import TauCeti.LinearAlgebra.Graded.Multilinear
public import TauCeti.Topology.Algebra.Nonarchimedean.EnergyFiltration
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Inserting an element of positive energy into filtered operations

Let `μ = (μₙ)ₙ` be a family of multilinear operations `μₙ : Mⁿ → M` on a module `M`. Given an
element `b : M`, the *deformed operation* of arity `k` inserts `b` into all free slots:

`μᵇₖ(x₁, …, xₖ) = ∑_{ℓ₀, …, ℓₖ ≥ 0} μ_{k + ℓ₀ + ⋯ + ℓₖ}(b^{ℓ₀}, x₁, b^{ℓ₁}, …, xₖ, b^{ℓₖ})`.

Equivalently, a term is a word length `n ≥ k` together with the set `s` of `k` slots, out of `n`,
that hold the inputs, in increasing order; the remaining `n - k` slots hold `b`
(`TauCeti.insertionTerm`). This is the formula for the Taylor components of the operations of an
`A∞` structure twisted by a bounding cochain, in the bar (suspended) convention, where a bounding
cochain has degree zero and insertion carries no signs.

On a bare module the sum is infinite. It converges when `M` is complete for an energy filtration
`F` (`TauCeti.IsEnergyFiltration`), every operation satisfies the nonnegative energy bound
`ν(μₙ(a₁, …, aₙ)) ≥ ν(a₁) + ⋯ + ν(aₙ)` in every arity, including arity zero (this is
`TauCeti.MultilinearMap.IsHomogeneous` for the real grading by `F`, with shift `0`), and `b` has
strictly positive energy. A term with `n - k` copies of `b` then has energy at least
`ν(x₁) + ⋯ + ν(xₖ) + (n - k) ν(b)`, which tends to infinity. The deformed operation
`TauCeti.deformedOperation` is again multilinear and satisfies the same energy bound, so it can
be fed back into this construction. It agrees with `μₖ` up to terms of energy at least
`ν(x₁) + ⋯ + ν(xₖ) + ν(b)`, so it reduces to `μₖ` at energy zero; for `b = 0` it is `μₖ`. In
arity zero it is the sum `∑ₙ μₙ(b, …, b)`, whose vanishing is the Maurer–Cartan equation in the
bar convention.

## Main definitions

* `TauCeti.InsertionSlots k`: the words with `k` marked slots, indexing the terms of the series.
* `TauCeti.insertionTerm μ b i`: the multilinear map evaluating `μ` with the inputs at the marked
  slots of `i` and `b` at the others.
* `TauCeti.deformedOperation`: the operation `μᵇₖ`, the convergent sum of the insertion terms.

## Main results

* `TauCeti.InsertionSlots.le_fst`: a word with `k` marked slots has length at least `k`.
* `TauCeti.InsertionSlots.eq_univ_of_fst_eq`: a word of length `k` with `k` marked slots has every
  slot marked.
* `TauCeti.insertionTerm_mem`: an insertion term has energy at least the energy of its inputs plus
  `n - k` times the energy of `b`.
* `TauCeti.summable_insertionTerm`: the insertion series converges for `b` of positive energy.
* `TauCeti.isHomogeneous_deformedOperation`: the deformed operations satisfy the nonnegative
  energy bound.
* `TauCeti.deformedOperation_sub_mem`: `μᵇₖ - μₖ` has energy at least the energy of the inputs plus
  the energy of `b`.
* `TauCeti.deformedOperation_arity_zero_eq_tsum`: in arity zero the deformed operation is
  `∑ₙ μₙ(b, …, b)`.
* `TauCeti.deformedOperation_zero`: inserting `b = 0` returns the original operation.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Chapter 3.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]

/-! ### Insertion terms -/

/-- The terms of an insertion series of arity `k`: a word length `n` together with the set of `k`
slots, out of `n`, holding the inputs. The other `n - k` slots hold the inserted element. -/
abbrev InsertionSlots (k : ℕ) : Type := Σ n : ℕ, {s : Finset (Fin n) // #s = k}

/-- A word with `k` marked slots has length at least `k`. -/
theorem InsertionSlots.le_fst {k : ℕ} (i : InsertionSlots k) : k ≤ i.1 := by
  simpa [i.2.property] using card_le_univ i.2.val

/-- A word of length `k` with `k` marked slots has every slot marked. -/
theorem InsertionSlots.eq_univ_of_fst_eq {k : ℕ} {i : InsertionSlots k} (h : i.1 = k) :
    i = ⟨k, univ, by simp⟩ := by
  obtain ⟨n, s, hs⟩ := i
  obtain rfl : n = k := h
  obtain rfl : s = univ := eq_univ_of_card _ (by simpa using hs)
  rfl

/-- The insertion term of `μ` at `i = ⟨n, s⟩`: the multilinear map sending `x : Fin k → M` to
`μₙ` evaluated with the inputs `x` at the slots of `s`, in increasing order, and `b` at the
other slots. -/
noncomputable def insertionTerm (μ : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ M) M)
    (b : M) {k : ℕ} (i : InsertionSlots k) :
    MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ M) M where
  toFun x := MultilinearMap.curryFinFinset (RingHom.id R) M M i.2.property rfl (μ i.1) x fun _ ↦ b
  map_update_add' x j u v := by
    rw [MultilinearMap.map_update_add, add_apply]
  map_update_smul' x j r u := by
    rw [MultilinearMap.map_update_smul, smul_apply]

variable (μ : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ M) M) (b : M)

/-- The insertion term at `⟨n, s⟩` is `μₙ` evaluated on the word whose slots in `s` carry the
inputs, in increasing order, and whose other slots carry `b`. The word is written through Mathlib's
splitting `finSumEquivOfFinset` of `Fin n` into the slots of `s` and of its complement. -/
theorem insertionTerm_apply {k : ℕ} (i : InsertionSlots k) (x : Fin k → M) :
    insertionTerm μ b i x =
      μ i.1 fun p ↦ Sum.elim x (fun _ ↦ b) ((finSumEquivOfFinset i.2.property rfl).symm p) :=
  MultilinearMap.curryFinFinset_apply _ _ _ _ _

/-- With every input equal to `a`, the insertion term at `⟨n, s⟩` is `μₙ` on the word with `a` at
the slots of `s` and `b` elsewhere. -/
theorem insertionTerm_apply_const {k : ℕ} (i : InsertionSlots k) (a : M) :
    insertionTerm μ b i (fun _ ↦ a) = μ i.1 (i.2.val.piecewise (fun _ ↦ a) fun _ ↦ b) :=
  MultilinearMap.curryFinFinset_apply_const i.2.property rfl _ a b

/-- In arity zero the insertion term at `⟨n, ∅⟩` is `μₙ(b, …, b)`. -/
@[simp]
theorem insertionTerm_apply_of_arity_zero (i : InsertionSlots 0) (x : Fin 0 → M) :
    insertionTerm μ b i x = μ i.1 fun _ ↦ b := by
  rw [insertionTerm_apply]
  congr 1
  funext p
  rcases (finSumEquivOfFinset i.2.property rfl).symm p with j | j
  · exact j.elim0
  · rfl

/-- If `b = 0`, an insertion term with an inserted slot vanishes. -/
theorem insertionTerm_zero_of_ne {k : ℕ} (i : InsertionSlots k) (hi : i.1 ≠ k) :
    insertionTerm μ 0 i = 0 := by
  obtain ⟨n, s, hs⟩ := i
  have hk : k ≤ n := InsertionSlots.le_fst ⟨n, s, hs⟩
  have hi : n ≠ k := hi
  obtain ⟨p, hp⟩ : sᶜ.Nonempty :=
    card_pos.1 (by rw [card_compl, Fintype.card_fin, hs]; omega)
  ext x
  rw [insertionTerm_apply, zero_apply]
  refine MultilinearMap.map_coord_zero _ p ?_
  rw [← Equiv.apply_symm_apply (finSumEquivOfFinset hs rfl) p] at hp
  rcases h : (finSumEquivOfFinset hs rfl).symm p with j | j
  · rw [h, finSumEquivOfFinset_inl] at hp
    exact absurd (orderEmbOfFin_mem s hs j) (mem_compl.1 hp)
  · rfl

/-- The insertion term in which every slot holds an input is `μₖ` itself. -/
@[simp]
theorem insertionTerm_univ (k : ℕ) :
    insertionTerm μ b (⟨k, univ, by simp⟩ : InsertionSlots k) = μ k := by
  ext x
  rw [insertionTerm_apply]
  congr 1
  funext p
  have hp : (finSumEquivOfFinset (s := (univ : Finset (Fin k))) (by simp) rfl).symm p =
      Sum.inl p := by
    rw [Equiv.symm_apply_eq, finSumEquivOfFinset_inl]
    exact (DFunLike.congr_fun (orderEmbOfFin_unique' (s := univ) (by simp)
      (f := (OrderIso.refl (Fin k)).toOrderEmbedding) fun _ ↦ mem_univ _) p)
  rw [hp, Sum.elim_inl]

/-! ### Energy bounds -/

variable {F : ℝ → AddSubgroup M}

/-- **Energy of an insertion term.** If every operation satisfies the nonnegative energy bound,
`b` has energy at least `δ` and the inputs have energies at least `cⱼ`, then the insertion term at
`⟨n, s⟩` has energy at least `∑ cⱼ + (n - k) δ`. -/
theorem insertionTerm_mem (hμ : ∀ n, MultilinearMap.IsHomogeneous (μ n) (fun _ ↦ F) F 0)
    {δ : ℝ} (hb : b ∈ F δ) {k : ℕ} (i : InsertionSlots k) {c : Fin k → ℝ} {x : Fin k → M}
    (hx : ∀ j, x j ∈ F (c j)) :
    insertionTerm μ b i x ∈ F (∑ j, c j + ((i.1 - k : ℕ) : ℝ) * δ) := by
  set e := finSumEquivOfFinset i.2.property rfl
  have h := (hμ i.1).map_mem (fun p ↦ Sum.elim c (fun _ ↦ δ) (e.symm p))
    (fun p ↦ Sum.elim x (fun _ ↦ b) (e.symm p)) fun p ↦ by
      rcases e.symm p with j | _
      · exact hx j
      · exact hb
  rw [insertionTerm_apply]
  rw [add_zero, Equiv.sum_comp e.symm (Sum.elim c fun _ ↦ δ), Fintype.sum_sum_type] at h
  simpa [card_compl, i.2.property, nsmul_eq_mul] using h

/-- An insertion term of a word longer than its arity has energy at least the energy of its
inputs plus the energy of `b`, when `b` has nonnegative energy. -/
theorem insertionTerm_mem_of_ne (hF : Antitone F)
    (hμ : ∀ n, MultilinearMap.IsHomogeneous (μ n) (fun _ ↦ F) F 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : b ∈ F δ) {k : ℕ} (i : InsertionSlots k) (hi : i.1 ≠ k) {c : Fin k → ℝ} {x : Fin k → M}
    (hx : ∀ j, x j ∈ F (c j)) :
    insertionTerm μ b i x ∈ F (∑ j, c j + δ) := by
  refine hF ?_ (insertionTerm_mem μ b hμ hb i hx)
  have hk := i.le_fst
  have : (1 : ℝ) ≤ ((i.1 - k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ i.1 - k)
  nlinarith

/-- The words of bounded length with `k` marked slots are finite in number. -/
private theorem finite_setOf_insertionSlots_lt (k N : ℕ) :
    {i : InsertionSlots k | i.1 < N}.Finite :=
  ((Set.finite_lt_nat N).sigma fun _ _ ↦ Set.finite_univ).subset fun _ hi ↦ ⟨hi, trivial⟩

/-- The lower energy bounds `∑ cⱼ + (n - k) δ` of the insertion terms tend to infinity when
`δ > 0`. -/
private theorem tendsto_insertionEnergy {k : ℕ} (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i : InsertionSlots k ↦ C + ((i.1 - k : ℕ) : ℝ) * δ) cofinite atTop := by
  refine tendsto_atTop.2 fun D ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((D - C) / δ)
  refine (finite_setOf_insertionSlots_lt (k := k) (N + k)).subset fun i hi ↦ ?_
  have hi' : C + ((i.1 - k : ℕ) : ℝ) * δ < D := not_le.1 hi
  by_contra hle
  have hN' : (N : ℝ) ≤ ((i.1 - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_sub_of_add_le (not_lt.1 hle)
  have := (div_lt_iff₀ hδ).1 (hN.trans_le hN')
  linarith

variable [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  (hF : IsEnergyFiltration F) (hμ : ∀ n, MultilinearMap.IsHomogeneous (μ n) (fun _ ↦ F) F 0)
include hF hμ

/-- **The insertion series converges.** On a complete module with an energy filtration, if every
operation satisfies the nonnegative energy bound and `b` has positive energy, the insertion terms
at any inputs are summable. -/
theorem summable_insertionTerm {δ : ℝ} (hδ : 0 < δ) (hb : b ∈ F δ) {k : ℕ} (x : Fin k → M) :
    Summable fun i : InsertionSlots k ↦ insertionTerm μ b i x := by
  choose c hc using fun j ↦ hF.exists_mem (x j)
  exact hF.summable_of_mem (fun i ↦ insertionTerm_mem μ b hμ hb i hc)
    (tendsto_insertionEnergy _ hδ)

/-! ### The deformed operations -/

variable [T2Space M] [ContinuousConstSMul R M]

/-- The **deformed operation** `μᵇₖ` of arity `k`: the convergent sum of the insertion terms of
`μ`, inserting `b` of positive energy into all free slots. It is multilinear since the series
converges at every input. -/
noncomputable def deformedOperation (hb : ∃ δ, 0 < δ ∧ b ∈ F δ) (k : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ M) M where
  toFun x := ∑' i : InsertionSlots k, insertionTerm μ b i x
  map_update_add' x j u v := by
    obtain ⟨δ, hδ, hb⟩ := hb
    simp_rw [MultilinearMap.map_update_add]
    exact (summable_insertionTerm μ b hF hμ hδ hb _).tsum_add
      (summable_insertionTerm μ b hF hμ hδ hb _)
  map_update_smul' x j r u := by
    obtain ⟨δ, hδ, hb⟩ := hb
    simp_rw [MultilinearMap.map_update_smul, RingHom.id_apply]
    exact (summable_insertionTerm μ b hF hμ hδ hb _).tsum_const_smul r

variable (hb : ∃ δ, 0 < δ ∧ b ∈ F δ)

theorem deformedOperation_apply {k : ℕ} (x : Fin k → M) :
    deformedOperation μ b hF hμ hb k x = ∑' i : InsertionSlots k, insertionTerm μ b i x :=
  (rfl)

/-- The insertion series sums to the deformed operation. -/
theorem hasSum_deformedOperation {k : ℕ} (x : Fin k → M) :
    HasSum (fun i : InsertionSlots k ↦ insertionTerm μ b i x)
      (deformedOperation μ b hF hμ hb k x) := by
  obtain ⟨δ, hδ, hb'⟩ := hb
  exact (summable_insertionTerm μ b hF hμ hδ hb' x).hasSum

/-- **The deformed operations satisfy the nonnegative energy bound**: if the inputs have energies
at least `cⱼ`, then `μᵇₖ(x)` has energy at least `∑ cⱼ`. -/
theorem isHomogeneous_deformedOperation (k : ℕ) :
    MultilinearMap.IsHomogeneous (deformedOperation μ b hF hμ hb k) (fun _ ↦ F) F 0 := by
  refine MultilinearMap.isHomogeneous_def.2 fun c x hx ↦ ?_
  obtain ⟨δ, hδ, hb'⟩ := hb
  rw [add_zero, deformedOperation_apply]
  exact hF.tsum_mem fun i ↦ hF.antitone (le_add_of_nonneg_right (by positivity))
    (insertionTerm_mem μ b hμ hb' i hx)

/-- **The deformed operation reduces to the original one at energy zero**: `μᵇₖ(x) - μₖ(x)` has
energy at least `∑ cⱼ + δ` when the inputs have energies at least `cⱼ` and `b` has energy at
least `δ ≥ 0`. -/
theorem deformedOperation_sub_mem {δ : ℝ} (hδ : 0 ≤ δ) (hbδ : b ∈ F δ) {k : ℕ} {c : Fin k → ℝ}
    {x : Fin k → M} (hx : ∀ j, x j ∈ F (c j)) :
    deformedOperation μ b hF hμ hb k x - μ k x ∈ F (∑ j, c j + δ) := by
  set i₀ : InsertionSlots k := ⟨k, univ, by simp⟩
  have hsum := hasSum_deformedOperation μ b hF hμ hb x
  have hrest : HasSum (Function.update (fun i ↦ insertionTerm μ b i x) i₀ 0)
      (deformedOperation μ b hF hμ hb k x - μ k x) := by
    simpa [i₀, insertionTerm_univ, neg_add_eq_sub] using hsum.update i₀ 0
  rw [← hrest.tsum_eq]
  refine hF.tsum_mem fun i ↦ ?_
  rcases eq_or_ne i i₀ with rfl | hi
  · simp
  · rw [Function.update_of_ne hi]
    exact insertionTerm_mem_of_ne μ b hF.antitone hμ hδ hbδ i
      (fun h ↦ hi (InsertionSlots.eq_univ_of_fst_eq h)) hx

/-- The words with no marked slot are indexed by their length. -/
private def insertionSlotsZeroEquiv : InsertionSlots 0 ≃ ℕ where
  toFun i := i.1
  invFun n := ⟨n, ∅, card_empty⟩
  left_inv i := by
    obtain ⟨n, s, hs⟩ := i
    obtain rfl : s = ∅ := card_eq_zero.1 hs
    rfl
  right_inv _ := rfl

/-- **The nullary deformed operation** is `∑ₙ μₙ(b, …, b)`. In the bar convention its vanishing is
the Maurer–Cartan equation for `b`. -/
theorem deformedOperation_arity_zero_eq_tsum (x : Fin 0 → M) :
    deformedOperation μ b hF hμ hb 0 x = ∑' n, μ n fun _ ↦ b := by
  rw [deformedOperation_apply, ← insertionSlotsZeroEquiv.symm.tsum_eq]
  exact tsum_congr fun n ↦ insertionTerm_apply_of_arity_zero μ b _ x

/-- The nullary insertion series `∑ₙ μₙ(b, …, b)` converges to the nullary deformed operation. -/
theorem hasSum_deformedOperation_arity_zero (x : Fin 0 → M) :
    HasSum (fun n ↦ μ n fun _ ↦ b) (deformedOperation μ b hF hμ hb 0 x) := by
  rw [← insertionSlotsZeroEquiv.hasSum_iff]
  convert hasSum_deformedOperation μ b hF hμ hb x using 1
  funext i
  exact (insertionTerm_apply_of_arity_zero μ b i x).symm

/-- **Inserting zero changes nothing**: `μ⁰ₖ = μₖ`. -/
theorem deformedOperation_zero (h0 : ∃ δ, 0 < δ ∧ (0 : M) ∈ F δ) (k : ℕ) :
    deformedOperation μ 0 hF hμ h0 k = μ k := by
  ext x
  rw [deformedOperation_apply, tsum_eq_single (⟨k, univ, by simp⟩ : InsertionSlots k),
    insertionTerm_univ]
  intro i hi
  rw [DFunLike.congr_fun (insertionTerm_zero_of_ne μ i
    fun h ↦ hi (InsertionSlots.eq_univ_of_fst_eq h)) x, zero_apply]

end TauCeti
