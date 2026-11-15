/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
public import TauCeti.Algebra.Homology.AInfinity.Algebra.MaurerCartan
public import TauCeti.LinearAlgebra.TensorCoalgebra.Brace
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Insertion

/-!
# Twisting an `A∞` algebra by a Maurer--Cartan element

Let `α` be a Maurer--Cartan element of an `A∞` algebra `A`.  The **twisted** operations insert
copies of `α` in all possible ways: on the suspended bar construction, the twisted Taylor map is

`b^α (x₁ ⋯ xₙ) = ∑_{k₀, …, kₙ} b (α^{k₀} x₁ α^{k₁} ⋯ xₙ α^{kₙ})`,

where `b` is the Taylor map of `A`.  Since `α` has degree one, its suspension has degree zero, so
no Koszul signs arise in this suspended formula; unsuspended, the signs are those of
`TauCeti.AInfinityAlgebra.taylor_of_tprod`.  The arity-zero part of the same sum is the
Maurer--Cartan sum `∑ₖ b(α^k)`, which vanishes: this is what keeps the twisted structure uncurved.

On a bare graded module the sum over `k₀, …, kₙ` is infinite, so this file works in the
arity-nilpotent regime.  An **insertion bound** for `α` is a number `T` such that, for every
`t ≥ T`, `b` vanishes on the sum of all the insertions of `t` copies of `α` into any word
(`TauCeti.AInfinityAlgebra.IsInsertionBound`).  Then the twisted Taylor map is the finite sum of the
terms with fewer than `T` insertions, `TauCeti.AInfinityAlgebra.twistTaylor`.  Every algebra whose
operations vanish above some arity, in particular every DG algebra, admits an insertion bound for
every element (`TauCeti.AInfinityAlgebra.isInsertionBound_of_m_eq_zero`).

The twisted Taylor map satisfies the bar equation, so it defines an `A∞` algebra
`TauCeti.AInfinityAlgebra.twist`.  The proof does not expand the Stasheff identities.  Writing
`Insₜ` for the insertion of `t` copies of `α` into tensor words, the coderivation `Eᵥ` with Taylor
map `b ∘ Insᵥ` satisfies `b̂ ∘ Insₜ = ∑_{u + v = t} Insᵤ ∘ Eᵥ`, where `b̂` is the bar differential
(`TauCeti.TensorWords.IsGradedCoderivation.comp_insertions`).  The twisted bar differential is
`∑ᵥ Eᵥ` up to the curvature term inserting the Maurer--Cartan sum, which vanishes, so the twisted
Taylor map after the twisted bar differential is `∑ₜ b ∘ b̂ ∘ Insₜ`, which vanishes because `b̂`
squares to zero.

For a DG algebra the twist is the familiar one: the twisted differential is
`d^α x = d x - α x + (-1)^|x| x α`, that is `d - [α, -]`, and the product is unchanged.

## Main definitions

* `TauCeti.AInfinityAlgebra.insertionTaylor`: the Taylor map after inserting `t` copies of `α`,
  on all tensor words.
* `TauCeti.AInfinityAlgebra.IsInsertionBound`: the Taylor map vanishes after `T` insertions.
* `TauCeti.AInfinityAlgebra.twistTaylor`: the twisted Taylor map.
* `TauCeti.AInfinityAlgebra.twist`: the `A∞` algebra twisted by a Maurer--Cartan element.

## Main results

* `TauCeti.AInfinityAlgebra.twistTaylor_comp_gradedCoderiv_twistTaylor`: the twisted Taylor map
  satisfies the bar equation.
* `TauCeti.AInfinityAlgebra.twist_taylor`: the Taylor map of the twisted algebra.
* `TauCeti.AInfinityAlgebra.twist_zero`: twisting by zero gives back the algebra.
* `TauCeti.AInfinityAlgebra.isInsertionBound_of_m_eq_zero`: insertion bounds for algebras with
  bounded arity.
* `TauCeti.IsNonUnitalDGAlgebra.twist_m_one_apply` and
  `TauCeti.IsNonUnitalDGAlgebra.twist_m_two_apply`: the twisted differential and product of a DG
  algebra.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6 and 7.6.
-/

public section

open scoped TensorProduct

universe uR uA

namespace TauCeti

namespace AInfinityAlgebra

open TensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- The suspended Taylor map of `𝒜` after inserting `t` copies of `α`, on all tensor words:
`x₁ ⋯ xₙ ↦ ∑_{k₀ + ⋯ + kₙ = t} b (α^{k₀} x₁ α^{k₁} ⋯ xₙ α^{kₙ})`.  On the empty word it is
`b (α ⋯ α)`, the arity-`t` term of the suspended Maurer--Cartan sum. -/
noncomputable def insertionTaylor (α : A) (t : ℕ) : TensorWords R A →ₗ[R] A :=
  𝒜.taylor ∘ₗ reducedProjection R A ∘ₗ insertions R α t

theorem insertionTaylor_apply (α : A) (t : ℕ) (w : TensorWords R A) :
    𝒜.insertionTaylor α t w = 𝒜.taylor (reducedProjection R A (insertions R α t w)) :=
  (rfl)

/-- Inserting no copies of `α` gives back the Taylor map. -/
@[simp]
theorem insertionTaylor_zero (α : A) :
    𝒜.insertionTaylor α 0 = 𝒜.taylor ∘ₗ reducedProjection R A := by
  rw [insertionTaylor, insertions_zero, LinearMap.comp_id]

/-- An **insertion bound** for `α`: for every `t ≥ T`, the Taylor map vanishes on the sum of all the
insertions of `t` copies of `α` into any word, the empty word included, that is
`𝒜.insertionTaylor α t = 0`.  This makes the twisted operations, and the Maurer--Cartan sum,
finite sums. -/
def IsInsertionBound (α : A) (T : ℕ) : Prop :=
  ∀ t, T ≤ t → 𝒜.insertionTaylor α t = 0

theorem isInsertionBound_iff (α : A) (T : ℕ) :
    𝒜.IsInsertionBound α T ↔ ∀ t, T ≤ t → 𝒜.insertionTaylor α t = 0 :=
  Iff.rfl

/-- The **twisted Taylor map**: the suspended Taylor map with fewer than `T` copies of `α` inserted
in all possible ways. -/
noncomputable def twistTaylor (α : A) (T : ℕ) : ReducedTensorWords R A →ₗ[R] A :=
  ∑ t ∈ Finset.range T, 𝒜.insertionTaylor α t ∘ₗ reducedInclusion R A

theorem twistTaylor_apply (α : A) (T : ℕ) (w : ReducedTensorWords R A) :
    𝒜.twistTaylor α T w = ∑ t ∈ Finset.range T, 𝒜.insertionTaylor α t (reducedInclusion R A w) := by
  simp [twistTaylor, LinearMap.sum_apply]

variable {𝒜}

/-- A larger number is an insertion bound too. -/
theorem IsInsertionBound.mono {α : A} {T T' : ℕ} (hT : 𝒜.IsInsertionBound α T) (h : T ≤ T') :
    𝒜.IsInsertionBound α T' :=
  fun t ht ↦ hT t (h.trans ht)

/-- The twisted Taylor map does not depend on the insertion bound. -/
theorem IsInsertionBound.twistTaylor_eq {α : A} {T T' : ℕ} (hT : 𝒜.IsInsertionBound α T)
    (hTT' : T ≤ T') : 𝒜.twistTaylor α T' = 𝒜.twistTaylor α T := by
  rw [twistTaylor, twistTaylor]
  exact Finset.eventually_constant_sum (fun t ht ↦ by rw [hT t ht, LinearMap.zero_comp]) hTT'

/-- The twisted Taylor map has degree one for the suspended grading. -/
theorem isHomogeneous_twistTaylor {α : A} (hα : α ∈ 𝒜.grading.piece 1) (T : ℕ) :
    LinearMap.IsHomogeneous (𝒜.twistTaylor α T)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  rw [twistTaylor_apply]
  refine Submodule.sum_mem _ fun t _ ↦ ?_
  rw [insertionTaylor_apply]
  have h₁ := insertions_mem_gradedPiece
    (by rwa [InternalGrading.shift_piece, zero_add] : α ∈ (𝒜.grading.shift 1).piece 0) t
    (mem_gradedPiece_of_reducedInclusion hw)
  have h₂ := (isHomogeneous_reducedProjection (𝒜.grading.shift 1)).map_mem h₁
  rw [add_zero] at h₂
  exact (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).map_mem h₂

/-! ### Algebras of bounded arity -/

variable (𝒜) in
/-- Inserting `t` copies of `α` into a word of length `n` gives words of length `n + t`, which the
Taylor map kills when the operation of that arity vanishes. -/
theorem insertionTaylor_comp_of_eq_zero_of_m_eq_zero (α : A) {n t : ℕ} (h : 𝒜.m (n + t) = 0) :
    𝒜.insertionTaylor α t ∘ₗ of R A n = 0 := by
  rcases Nat.eq_zero_or_pos (n + t) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ t = 0 := by omega
    exact LinearMap.ext fun z ↦ by simp [reducedProjection_of_zero]
  · refine LinearMap.ext fun z ↦ ?_
    obtain ⟨y, hy⟩ := insertions_of_mem_range α t z
    rw [LinearMap.comp_apply, insertionTaylor_apply, ← hy, LinearMap.zero_apply,
      reducedProjection_of_of_pos R A hpos]
    exact LinearMap.congr_fun (𝒜.taylor_comp_of_eq_zero_of_m_eq_zero ⟨n + t, hpos⟩ h) y

variable (𝒜) in
/-- `TauCeti.AInfinityAlgebra.insertionTaylor_comp_of_eq_zero_of_m_eq_zero`, applied to a word. -/
theorem insertionTaylor_of_eq_zero_of_m_eq_zero (α : A) {n t : ℕ} (h : 𝒜.m (n + t) = 0)
    (z : TensorPower R n A) : 𝒜.insertionTaylor α t (of R A n z) = 0 :=
  LinearMap.congr_fun (𝒜.insertionTaylor_comp_of_eq_zero_of_m_eq_zero α h) z

variable (𝒜) in
/-- **Algebras of bounded arity admit insertion bounds.**  If the operations of `𝒜` vanish above
arity `N`, then `N + 1` is an insertion bound for every element.  This covers DG algebras, with
`N = 2`. -/
theorem isInsertionBound_of_m_eq_zero {N : ℕ} (hN : ∀ n, N < n → 𝒜.m n = 0) (α : A) :
    𝒜.IsInsertionBound α (N + 1) := fun t ht ↦
  DirectSum.linearMap_ext R fun n ↦ by
    rw [← of_def, LinearMap.zero_comp]
    exact 𝒜.insertionTaylor_comp_of_eq_zero_of_m_eq_zero α (hN (n + t) (by omega))

/-! ### The bar equation -/

/-- On the empty word, the Taylor map after inserting `n + 1` copies of `α` is the Taylor map on the
word `α ⋯ α`. -/
private theorem insertionTaylor_succ_one (α : A) (n : ℕ) :
    𝒜.insertionTaylor α (n + 1) 1 =
      𝒜.taylor (ReducedTensorWords.of R A ⟨n + 1, n.succ_pos⟩
        (PiTensorProduct.tprod R fun _ ↦ α)) := by
  rw [insertionTaylor_apply, insertions_apply_one, cons_pow_apply_one_eq_of,
    reducedProjection_of_of_pos]

/-- Under an insertion bound, the Maurer--Cartan equation says that the arity-zero part of the
twisted Taylor map vanishes. -/
private theorem IsInsertionBound.sum_insertionTaylor_one {α : A} {T : ℕ}
    (hT : 𝒜.IsInsertionBound α T) (hα : 𝒜.IsMaurerCartan α) :
    ∑ v ∈ Finset.range T, 𝒜.insertionTaylor α v 1 = 0 := by
  have hm (n : ℕ) (hn : T + 1 ≤ n) : 𝒜.m n (fun _ ↦ α) = 0 := by
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := LinearMap.congr_fun (hT (n + 1) (by omega)) 1
    rw [insertionTaylor_succ_one, 𝒜.taylor_of_tprod_const hα.mem_piece_one _ n.succ_pos,
      LinearMap.zero_apply, negOnePowCast_smul_eq_zero_iff] at h
    exact h
  have hsum := ((isMaurerCartan_iff_taylor (N := T) hm).1 hα).2
  rw [map_sum] at hsum
  rw [← Finset.eventually_constant_sum (fun v hv ↦ by rw [hT v hv, LinearMap.zero_apply])
    (Nat.le_succ T), Finset.sum_range_succ']
  simp only [insertionTaylor_succ_one, hsum, insertionTaylor_zero, LinearMap.comp_apply,
    reducedProjection_one, map_zero, add_zero]

variable (𝒜) in
/-- The coderivation of the coaugmented bar construction whose Taylor map is the Taylor map of `𝒜`
after inserting `v` copies of `α`.  It is the extension of the reduced coderivation of the
positive-arity part, together with the twisted insertion of the arity-zero part `b(α ⋯ α)`. -/
private noncomputable def insertionCoderiv (α : A) (v : ℕ) :
    TensorWords R A →ₗ[R] TensorWords R A :=
  extendReduced (ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1)
      (𝒜.insertionTaylor α v ∘ₗ reducedInclusion R A) 1) +
    twistedInsert R ((𝒜.grading.shift 1).koszulTwist 1) (𝒜.insertionTaylor α v 1)

private theorem isGradedCoderivation_insertionCoderiv (α : A) (v : ℕ) :
    IsGradedCoderivation (𝒜.grading.shift 1) 1 (𝒜.insertionCoderiv α v) :=
  (isGradedCoderivation_extendReduced
    (ReducedTensorWords.isGradedCoderivation_gradedCoderiv _ _ 1)).add
    (isGradedCoderivation_twistedInsert _ 1 _)

private theorem letter_reducedProjection_insertionCoderiv (α : A) (v : ℕ) (w : TensorWords R A) :
    ReducedTensorWords.letter R A (reducedProjection R A (𝒜.insertionCoderiv α v w)) =
      𝒜.insertionTaylor α v w := by
  conv_rhs => rw [← reducedInclusion_reducedProjection_add_algebraMap_counit R A w]
  rw [insertionCoderiv, LinearMap.add_apply, map_add, map_add, extendReduced_apply,
    reducedProjection_reducedInclusion, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_gradedCoderiv, letter_reducedProjection_twistedInsert,
    map_add, Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.comp_apply]

/-- The insertion coderivations vanish beyond an insertion bound. -/
private theorem IsInsertionBound.insertionCoderiv_eq_zero {α : A} {T : ℕ}
    (hT : 𝒜.IsInsertionBound α T) {v : ℕ} (hv : T ≤ v) : 𝒜.insertionCoderiv α v = 0 := by
  rw [insertionCoderiv, hT v hv, LinearMap.zero_comp, ReducedTensorWords.gradedCoderiv_zero_left,
    LinearMap.zero_apply, map_zero, add_zero]
  exact LinearMap.ext fun w ↦ by simp

/-- **The twisted Taylor map satisfies the bar equation**: for a Maurer--Cartan element `α` with an
insertion bound, the twisted Taylor map vanishes after its own graded Taylor expansion. -/
theorem twistTaylor_comp_gradedCoderiv_twistTaylor {α : A} (hα : 𝒜.IsMaurerCartan α) {T : ℕ}
    (hT : 𝒜.IsInsertionBound α T) :
    𝒜.twistTaylor α T ∘ₗ
        ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1) (𝒜.twistTaylor α T) 1 = 0 := by
  set E := 𝒜.insertionCoderiv α with hEdef
  have ha : (𝒜.grading.shift 1).koszulTwist 1 α = α :=
    (𝒜.grading.shift 1).koszulTwist_apply_of_mem_zero
      (by rw [InternalGrading.shift_piece, zero_add]; exact hα.mem_piece_one) 1
  -- The bar differential passes through the insertions.
  have key := 𝒜.isGradedCoderivation_coaugmentedBarDifferential.comp_insertions ha
    (isGradedCoderivation_insertionCoderiv α) fun v w ↦
      (letter_reducedProjection_insertionCoderiv α v w).trans
        (𝒜.letter_reducedProjection_coaugmentedBarDifferential _).symm
  -- The twisted bar differential is the sum of the insertion coderivations.
  have hcod (z : ReducedTensorWords R A) :
      reducedInclusion R A (ReducedTensorWords.gradedCoderiv (𝒜.grading.shift 1)
          (𝒜.twistTaylor α T) 1 z) =
        ∑ v ∈ Finset.range T, E v (reducedInclusion R A z) := by
    have hc := hT.sum_insertionTaylor_one hα
    simp only [twistTaylor, ReducedTensorWords.gradedCoderiv_sum, LinearMap.sum_apply, map_sum,
      hEdef, insertionCoderiv, LinearMap.add_apply, extendReduced_reducedInclusion,
      Finset.sum_add_distrib]
    rw [← LinearMap.sum_apply, ← map_sum (twistedInsert R ((𝒜.grading.shift 1).koszulTwist 1)), hc,
      map_zero, LinearMap.zero_apply, add_zero]
  refine LinearMap.ext fun z ↦ ?_
  rw [LinearMap.comp_apply, twistTaylor_apply, hcod, LinearMap.zero_apply]
  set x := reducedInclusion R A z
  set g : ℕ → ℕ → A := fun u v ↦ 𝒜.insertionTaylor α u (E v x) with hg
  have hgu (u v : ℕ) (hu : T ≤ u) : g u v = 0 := by rw [hg]; simp [hT u hu]
  have hgv (u v : ℕ) (hv : T ≤ v) : g u v = 0 := by
    rw [hg]; simp [hEdef, hT.insertionCoderiv_eq_zero hv]
  -- Reorganise the double sum by the total number of inserted letters.
  have hsum : ∑ u ∈ Finset.range T, 𝒜.insertionTaylor α u (∑ v ∈ Finset.range T, E v x) =
      ∑ k ∈ Finset.range (2 * T), ∑ p ∈ Finset.antidiagonal k, g p.1 p.2 := by
    rw [Finset.Nat.sum_range_sum_antidiagonal]
    simp only [map_sum]
    rw [← Finset.eventually_constant_sum (fun u hu ↦ Finset.sum_eq_zero fun v _ ↦ hgu u v hu)
      (show T ≤ 2 * T by omega)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : T ≤ u
    · rw [Finset.sum_eq_zero fun v _ ↦ hgu u v hu, Finset.sum_eq_zero fun v _ ↦ hgu u v hu]
    · exact (Finset.eventually_constant_sum (fun v hv ↦ hgv u v hv) (by omega)).symm
  rw [hsum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hk := LinearMap.congr_fun (key k) x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hk
  simp only [hg, insertionTaylor_apply, ← map_sum]
  rw [hEdef, ← hk, taylor_reducedProjection_coaugmentedBarDifferential]

/-! ### The twisted algebra -/

variable (𝒜) in
/-- **The `A∞` algebra twisted by a Maurer--Cartan element** `α` with insertion bound `T`: the same
graded module, with the twisted Taylor map `b^α (x₁ ⋯ xₙ) = ∑ b (α^{k₀} x₁ α^{k₁} ⋯ xₙ α^{kₙ})`. -/
noncomputable def twist (α : A) (hα : 𝒜.IsMaurerCartan α) (T : ℕ) (hT : 𝒜.IsInsertionBound α T) :
    AInfinityAlgebra R A :=
  ofTaylor 𝒜.grading (𝒜.twistTaylor α T) (isHomogeneous_twistTaylor hα.mem_piece_one T) <| by
    rw [ReducedTensorWords.gradedCoderiv_comp_self_eq_zero_iff
        (isHomogeneous_twistTaylor hα.mem_piece_one T) odd_one, ReducedTensorWords.brace_def]
    exact twistTaylor_comp_gradedCoderiv_twistTaylor hα hT

@[simp]
theorem twist_grading (α : A) (hα : 𝒜.IsMaurerCartan α) (T : ℕ) (hT : 𝒜.IsInsertionBound α T) :
    (𝒜.twist α hα T hT).grading = 𝒜.grading :=
  ofTaylor_grading _ _ _ _

/-- The Taylor map of the twisted algebra is the twisted Taylor map. -/
@[simp]
theorem twist_taylor (α : A) (hα : 𝒜.IsMaurerCartan α) (T : ℕ) (hT : 𝒜.IsInsertionBound α T) :
    (𝒜.twist α hα T hT).taylor = 𝒜.twistTaylor α T :=
  ofTaylor_taylor _ _ _ _

/-- The twisted algebra does not depend on the insertion bound. -/
theorem twist_eq_twist (α : A) (hα : 𝒜.IsMaurerCartan α) {T T' : ℕ}
    (hT : 𝒜.IsInsertionBound α T) (hT' : 𝒜.IsInsertionBound α T') :
    𝒜.twist α hα T' hT' = 𝒜.twist α hα T hT := by
  refine ext (by rw [twist_grading, twist_grading]) ?_
  rw [m_eq_desuspension, m_eq_desuspension, twist_taylor, twist_taylor, twist_grading,
    twist_grading, ← hT'.twistTaylor_eq (le_max_right T T'), hT.twistTaylor_eq (le_max_left T T')]

/-- Twisting by zero gives back the algebra. -/
@[simp]
theorem twist_zero {T : ℕ} (hT : 𝒜.IsInsertionBound 0 T) :
    𝒜.twist 0 𝒜.isMaurerCartan_zero T hT = 𝒜 := by
  have h : 𝒜.twistTaylor 0 T = 𝒜.taylor := by
    rw [← hT.twistTaylor_eq (Nat.le_succ T), twistTaylor, Finset.sum_range_succ']
    simp [insertionTaylor, zero_insertions, LinearMap.comp_assoc]
  refine ext (twist_grading ..) ?_
  rw [m_eq_desuspension, m_eq_desuspension, twist_taylor, twist_grading, h]

end AInfinityAlgebra

/-! ### Twisting a DG algebra -/

namespace IsNonUnitalDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜]
  [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}

open TensorWords AInfinityAlgebra

/-- In a DG algebra, the Taylor map vanishes once three copies of any element are inserted. -/
theorem isInsertionBound_toAInfinityAlgebra (h : IsNonUnitalDGAlgebra 𝒜 d) (α : A) :
    h.toAInfinityAlgebra.IsInsertionBound α 3 :=
  h.toAInfinityAlgebra.isInsertionBound_of_m_eq_zero (N := 2)
    (fun _ hn ↦ h.toAInfinityAlgebra_m_of_three_le hn) α

/-- **The twisted differential of a DG algebra** is `d - [α, -]`: on an element `x` of degree `p`,
`d^α x = d x - α x + (-1)^p x α`. -/
theorem twist_m_one_apply (h : IsNonUnitalDGAlgebra 𝒜 d) {α : A}
    (hα : h.toAInfinityAlgebra.IsMaurerCartan α) {p : ℤ} {x : A} (hx : x ∈ 𝒜 p) :
    (h.toAInfinityAlgebra.twist α hα 3 (h.isInsertionBound_toAInfinityAlgebra α)).m 1 ![x] =
      d x - α * x + ((p.negOnePow : ℤ) : R) • (x * α) := by
  have hα1 : α ∈ 𝒜 1 := by
    simpa using hα.mem_piece_one
  have hins : h.toAInfinityAlgebra.insertionTaylor α 2 (cons R A x 1) = 0 := by
    rw [cons_one_eq_of]
    exact h.toAInfinityAlgebra.insertionTaylor_of_eq_zero_of_m_eq_zero α
      (h.toAInfinityAlgebra_m_of_three_le le_rfl) _
  rw [← taylor_ofLetter, twist_taylor, twistTaylor_apply, ← cons_one, Finset.sum_range_succ, hins,
    add_zero]
  -- Split off the words with one inserted letter before evaluating the one-letter word.
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, insertionTaylor_apply,
    insertions_cons, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, pow_zero, pow_one, one_apply_eq_self, insertions_apply_one, map_add,
    reducedProjection_cons_cons_one, taylor_of_two]
  simp only [cons_one, reducedProjection_reducedInclusion, taylor_ofLetter,
    toAInfinityAlgebra_m_one_apply, toAInfinityAlgebra_m_two_apply, toAInfinityAlgebra_grading,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hx,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hα1, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one, neg_one_smul, neg_mul, smul_mul_assoc]
  abel

/-- **The twisted product of a DG algebra** is the product. -/
theorem twist_m_two_apply (h : IsNonUnitalDGAlgebra 𝒜 d) {α : A}
    (hα : h.toAInfinityAlgebra.IsMaurerCartan α) (x y : A) :
    (h.toAInfinityAlgebra.twist α hα 3 (h.isInsertionBound_toAInfinityAlgebra α)).m 2 ![x, y] =
      x * y := by
  set κ := (InternalGrading.ofDecomposition 𝒜).koszulTwist 1
  have h₂ := (h.toAInfinityAlgebra.twist α hα 3
    (h.isInsertionBound_toAInfinityAlgebra α)).taylor_of_two (κ x) y
  rw [twist_grading, toAInfinityAlgebra_grading, InternalGrading.koszulTwist_koszulTwist] at h₂
  have hins (t : ℕ) (ht : 1 ≤ t) :=
    h.toAInfinityAlgebra.insertionTaylor_of_eq_zero_of_m_eq_zero α (n := 2) (t := t)
      (h.toAInfinityAlgebra_m_of_three_le (by omega))
  have hi : reducedInclusion R A (ReducedTensorWords.of R A (2 : ℕ+)
      (PiTensorProduct.tprod R ![κ x, y])) = of R A 2 (PiTensorProduct.tprod R ![κ x, y]) :=
    reducedInclusion_of R A (2 : ℕ+) _
  have hp : reducedProjection R A (of R A 2 (PiTensorProduct.tprod R ![κ x, y])) =
      ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![κ x, y]) :=
    reducedProjection_of_of_pos R A two_pos _
  rw [← h₂, twist_taylor, twistTaylor_apply, hi, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hins 1 le_rfl, hins 2 (by omega), add_zero, add_zero,
    insertionTaylor_zero, LinearMap.comp_apply, hp, taylor_of_two]
  simp [κ, toAInfinityAlgebra_grading, InternalGrading.koszulTwist_koszulTwist]

end IsNonUnitalDGAlgebra

end TauCeti
