/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import TauCeti.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.LinearAlgebra.LinearIndependent.NonnegCombination

/-!
# The integral weights of the roots relative to a base

Let `b` be a base of a finite crystallographic root system `P`. A root `αⱼ` determines the integral
family `k ↦ ⟨αⱼ, αₖ∨⟩` indexed by the simple roots, its weight. The weight of a simple root `αᵢ` is
the `i`-th row of the Cartan matrix, and the simple reflection `sᵢ` acts on weights by
`χ ↦ χ - χ i • b.cartanMatrix.row i`. Since every root is obtained from a simple root by simple
reflections, a property of integral weights can be propagated from the rows of the Cartan matrix to
the weights of all roots. This is how the weight spaces of a Lie algebra presented by Serre's
relations are compared at all the roots, starting from the simple ones.

Conversely, the weights of the roots and their positive multiples are the only weights whose whole
orbit under the simple reflections consists of positive and negative weights, positive meaning a
nonzero sum of rows of the Cartan matrix. Starting from a positive weight, reflect at a simple root
`αₖ` with `χ k > 0`, which exists because the Cartan matrix is positive definite after rescaling
its columns. Either the height drops, or the reflected weight is negative, which forces `χ` to be
a multiple of the row of `αₖ`. This is the combinatorial half of Serre's theorem: it shows that a
Lie algebra presented by Serre's relations has no weights other than `0` and the roots.

Over a linearly ordered field the same facts are available for vectors of the root space, through
the canonical Weyl-invariant form: `TauCeti.eq_zero_of_mem_posRootCone_of_forall_coroot'_nonpos`
and `RootPairing.exists_weylGroup_repr_smul_pos_and_neg`. The statements here are in integral
weight coordinates and hold over any domain of characteristic zero, such as the field of
definition of a split Lie algebra, using only the rescaled positive definiteness of the Cartan
matrix (`RootPairing.Base.exists_cartanMatrix_mul_diagonal_posDef`).

## Main results

* `RootPairing.pairingIn_reflectionPerm_left_eq_sub`: the action of a reflection on the pairings of
  a root.
* `RootPairing.Base.cartanMatrix_row_eq_pairingIn`: the rows of the Cartan matrix are the weights
  of the simple roots.
* `RootPairing.Base.linearIndependent_cartanMatrix_row`: the rows of the Cartan matrix are linearly
  independent over `ℤ`.
* `RootPairing.Base.induction_pairingIn_reflection`: the induction principle on weights.
* `RootPairing.Base.exists_pos_of_mem_closure_range_cartanMatrix_row`: a nonzero sum of rows of
  the Cartan matrix has a positive coordinate.
* `RootPairing.Base.exists_eq_nsmul_pairingIn_of_reflection`: a property of weights that is stable
  under the simple reflections and holds only at positive and negative weights holds only at
  positive multiples of the weights of roots.

## References

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  §10.3 and §18.3
* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI, appendix
-/

public section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A reflection acts on the pairings of a root by
`⟨sᵢ αⱼ, αₖ∨⟩ = ⟨αⱼ, αₖ∨⟩ - ⟨αⱼ, αᵢ∨⟩ * ⟨αᵢ, αₖ∨⟩`. -/
theorem RootPairing.pairingIn_reflectionPerm_left_eq_sub (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S (P.reflectionPerm i j) k =
      P.pairingIn S j k - P.pairingIn S j i * P.pairingIn S i k := by
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_pairingIn, map_sub, map_mul]
  rw [← P.root_coroot_eq_pairing (P.reflectionPerm i j) k, P.root_reflectionPerm,
    P.reflection_apply_root]
  simp

namespace RootPairing.Base

/-- The `i`-th row of the Cartan matrix is the weight `k ↦ ⟨αᵢ, αₖ∨⟩` of the simple root `αᵢ`. -/
theorem cartanMatrix_row_eq_pairingIn [P.IsCrystallographic] (b : P.Base) (i : b.support) :
    b.cartanMatrix.row i = fun k : b.support ↦ P.pairingIn ℤ i k := by
  funext k
  simp [cartanMatrixIn_def]

/-- If a property of integral weights is stable under the simple reflections, then so is the
property of the negated weight. -/
private theorem neg_reflection_stable [P.IsCrystallographic] (b : P.Base)
    {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (ψ : b.support → ℤ) (i : b.support) (hψ : Q (-ψ)) :
    Q (-(ψ - ψ i • b.cartanMatrix.row i)) := by
  have hsub : -(ψ - ψ i • b.cartanMatrix.row i) = -ψ - (-ψ) i • b.cartanMatrix.row i := by
    rw [Pi.neg_apply, neg_smul, sub_neg_eq_add, neg_sub, sub_eq_neg_add]
  exact hsub ▸ hrefl _ i hψ

variable [P.IsCrystallographic] [CharZero R] [Finite ι] [IsDomain R]

/-- The rows of the Cartan matrix of a base of a finite crystallographic root system are linearly
independent over `ℤ`. -/
theorem linearIndependent_cartanMatrix_row [P.IsRootSystem] (b : P.Base) :
    LinearIndependent ℤ b.cartanMatrix.row := by
  classical
  refine b.cartanMatrix.linearIndependent_rows_of_det_ne_zero ?_
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

/-- **Induction on the weights of the roots.** For a base of a finite reduced crystallographic root
pairing, a property of integral weights that holds at the rows of the Cartan matrix (the weights of
the simple roots) and is stable under the simple reflections holds at the weight of every root. -/
theorem induction_pairingIn_reflection [P.IsReduced] (b : P.Base) {Q : (b.support → ℤ) → Prop}
    (hsimple : ∀ i : b.support, Q (b.cartanMatrix.row i))
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (j : ι) : Q fun k : b.support ↦ P.pairingIn ℤ j k := by
  let w (j : ι) : b.support → ℤ := fun k ↦ P.pairingIn ℤ j k
  have hrow (i : b.support) : w i = b.cartanMatrix.row i :=
    (b.cartanMatrix_row_eq_pairingIn i).symm
  have hreflect (i : b.support) (j : ι) :
      w (P.reflectionPerm i j) = w j - w j i • b.cartanMatrix.row i := by
    funext k
    rw [Pi.sub_apply, Pi.smul_apply, ← hrow, smul_eq_mul]
    exact P.pairingIn_reflectionPerm_left_eq_sub ℤ i j k
  have hneg (i : ι) : w (P.reflectionPerm i i) = -w i := by
    funext k
    simp [w]
  -- Negation is not a simple reflection in general, so both signs have to be carried along.
  suffices h : Q (w j) ∧ Q (-w j) from h.1
  refine b.induction_reflect j (p := fun j ↦ Q (w j) ∧ Q (-w j)) ?_ ?_ ?_
  · rintro i ⟨h₁, h₂⟩
    rw [hneg, neg_neg]
    exact ⟨h₂, h₁⟩
  · intro i hi
    have hsi := hrow ⟨i, hi⟩
    refine ⟨hsi ▸ hsimple _, ?_⟩
    rw [← hneg, hreflect ⟨i, hi⟩ i, hsi]
    exact hrefl _ _ (hsimple _)
  · rintro i l ⟨h₁, h₂⟩ hl
    rw [hreflect ⟨l, hl⟩ i]
    exact ⟨hrefl _ _ h₁, b.neg_reflection_stable hrefl _ _ h₂⟩

/-! ## Weights whose orbit is signed -/

/-- **A positive weight has a positive coordinate.** A nonzero sum `χ` of rows of the Cartan
matrix, that is, the weight `k ↦ ⟨μ, αₖ∨⟩` of a nonzero sum `μ` of simple roots, pairs positively
with some simple coroot. -/
theorem exists_pos_of_mem_closure_range_cartanMatrix_row [P.IsRootSystem] (b : P.Base)
    {χ : b.support → ℤ} (hχ : χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row)) :
    ∃ k, 0 < χ k := by
  classical
  obtain ⟨n, hn, rfl⟩ :=
    AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hχ
  have hn0 : (n : b.support → ℤ) ≠ 0 := fun h ↦
    b.linearIndependent_cartanMatrix_row.zero_notMem_closure_range <| by
      rwa [Finsupp.coe_eq_zero.1 h, map_zero] at hχ
  have hcoord (k : b.support) : Finsupp.linearCombination ℤ b.cartanMatrix.row n k =
      Matrix.vecMul (⇑n) b.cartanMatrix k := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [Finset.sum_apply, Matrix.vecMul, dotProduct]
  -- For a positive diagonal `D` making `A * D` positive definite,
  -- `0 < n ⬝ᵥ (A * D) n = ∑ₖ χₖ dₖ nₖ`, which is impossible if every `χₖ ≤ 0`.
  obtain ⟨d, hd, hpos⟩ := b.exists_cartanMatrix_mul_diagonal_posDef
  have key := hpos.dotProduct_mulVec_pos hn0
  rw [star_trivial, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at key
  by_contra! hle
  refine key.not_ge (Finset.sum_nonpos fun k _ ↦ ?_)
  rw [Matrix.mulVec_diagonal, ← hcoord]
  nlinarith [hle k, mul_nonneg (hd k).le (hn k)]

/-- A positive weight `χ` whose reflection at the simple root `αₖ` is negative is a positive
multiple of the `k`-th row of the Cartan matrix. -/
private theorem exists_eq_nsmul_cartanMatrix_row_of_neg_reflection [P.IsRootSystem] (b : P.Base)
    {χ : b.support → ℤ} (k : b.support)
    (hC : χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row))
    (hneg : -(χ - χ k • b.cartanMatrix.row k) ∈
      AddSubsemigroup.closure (Set.range b.cartanMatrix.row)) :
    ∃ m : ℕ, 0 < m ∧ χ = m • b.cartanMatrix.row k := by
  classical
  obtain ⟨n, hn, rfl⟩ :=
    AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hC
  set χ := Finsupp.linearCombination ℤ b.cartanMatrix.row n with hχ
  obtain ⟨n', hn', hn'eq⟩ :=
    AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hneg
  have hlc : Finsupp.linearCombination ℤ b.cartanMatrix.row (n - Finsupp.single k (χ k)) =
      χ - χ k • b.cartanMatrix.row k := by
    rw [map_sub, Finsupp.linearCombination_single]
  rw [← hlc, ← map_neg] at hn'eq
  obtain rfl := b.linearIndependent_cartanMatrix_row.finsuppLinearCombination_injective hn'eq
  -- Both `n` and `single k (χ k) - n` are nonnegative, so `n` is supported at `k`.
  have hsingle : n = Finsupp.single k (n k) := by
    ext j
    by_cases hj : j = k
    · simp [hj]
    · have h1 := hn' j
      have h2 := hn j
      simp only [Finsupp.coe_neg, Finsupp.coe_sub, Pi.neg_apply, Pi.sub_apply,
        Finsupp.single_apply, Ne.symm hj, ite_false, sub_zero] at h1 ⊢
      omega
  have hχk : χ = n k • b.cartanMatrix.row k := by
    rw [hχ]
    conv_lhs => rw [hsingle]
    rw [Finsupp.linearCombination_single]
  have hnk : 0 < n k := by
    refine (hn k).lt_of_ne fun h ↦ ?_
    rw [hχk, ← h, zero_smul] at hC
    exact b.linearIndependent_cartanMatrix_row.zero_notMem_closure_range hC
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnk.le
  exact ⟨m, by omega, by rw [hχk, hm, natCast_zsmul]⟩

/-- The positive case of `RootPairing.Base.exists_eq_nsmul_pairingIn_of_reflection`: writing the
weight as `∑ⱼ nⱼ αⱼ` with `nⱼ ≥ 0`, by strong induction on its height `∑ⱼ nⱼ`. -/
private theorem exists_eq_nsmul_pairingIn_of_mem_closure [P.IsRootSystem] (b : P.Base)
    {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (hsign : ∀ χ, Q χ → χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row) ∨
      -χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row))
    {χ : b.support → ℤ} (hχ : Q χ)
    (hC : χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row)) :
    ∃ (j : ι) (m : ℕ), 0 < m ∧ χ = m • fun k : b.support ↦ P.pairingIn ℤ j k := by
  classical
  obtain ⟨n, hn, rfl⟩ :=
    AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hC
  suffices ∀ (N : ℕ) (n : b.support →₀ ℤ), (∀ j, 0 ≤ n j) → ∑ j, n j = N →
      Q (Finsupp.linearCombination ℤ b.cartanMatrix.row n) →
      Finsupp.linearCombination ℤ b.cartanMatrix.row n ∈
        AddSubsemigroup.closure (Set.range b.cartanMatrix.row) →
      ∃ (j : ι) (m : ℕ), 0 < m ∧ Finsupp.linearCombination ℤ b.cartanMatrix.row n =
        m • fun k : b.support ↦ P.pairingIn ℤ j k from
    this _ n hn (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hn j)).symm hχ hC
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn hN hQ hC
  set χ := Finsupp.linearCombination ℤ b.cartanMatrix.row n
  have hinj := b.linearIndependent_cartanMatrix_row.finsuppLinearCombination_injective
  obtain ⟨k, hk⟩ := b.exists_pos_of_mem_closure_range_cartanMatrix_row hC
  have hlc : Finsupp.linearCombination ℤ b.cartanMatrix.row (n - Finsupp.single k (χ k)) =
      χ - χ k • b.cartanMatrix.row k := by
    rw [map_sub, Finsupp.linearCombination_single]
  rcases hsign _ (hrefl χ k hQ) with hpos | hneg
  · -- The reflected weight is again positive, of smaller height, and `χ` is its reflection.
    obtain ⟨n', hn', hn'eq⟩ :=
      AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hpos
    rw [← hlc] at hn'eq
    obtain rfl := hinj hn'eq
    have hsum : ∑ j, (n - Finsupp.single k (χ k)) j = N - χ k := by
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finset.sum_sub_distrib, hN, Finsupp.single_apply,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hnonneg := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hn' j
    obtain ⟨j, m, hm, hjm⟩ := ih (∑ j, (n - Finsupp.single k (χ k)) j).toNat (by omega) _ hn'
      (by omega) (hlc ▸ hrefl χ k hQ) (hlc ▸ hpos)
    rw [hlc] at hjm
    refine ⟨P.reflectionPerm k j, m, hm, funext fun l ↦ ?_⟩
    have hl := congrFun hjm l
    have hk' := congrFun hjm k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cartanMatrix_row_eq_pairingIn,
      nsmul_eq_mul, P.pairingIn_same] at hl hk' ⊢
    rw [P.pairingIn_reflectionPerm_left_eq_sub ℤ]
    linear_combination hl - P.pairingIn ℤ (k : ι) (l : ι) * hk'
  · -- The reflected weight is negative, so `χ` is a multiple of the row of `αₖ`.
    obtain ⟨m, hm, hχk⟩ := b.exists_eq_nsmul_cartanMatrix_row_of_neg_reflection k hC hneg
    exact ⟨k, m, hm, by rw [hχk, cartanMatrix_row_eq_pairingIn]⟩

/-- **The weights with a signed orbit are multiples of roots.** Let `Q` be a property of integral
weights `χ : b.support → ℤ` that is stable under the simple reflections
`χ ↦ χ - χ i • b.cartanMatrix.row i` and holds only at positive weights (nonzero sums of rows of
the Cartan matrix) and at negative ones. Then every weight with property `Q` is a positive
multiple of the weight `k ↦ ⟨α, αₖ∨⟩` of a root `α`. -/
theorem exists_eq_nsmul_pairingIn_of_reflection [P.IsRootSystem] (b : P.Base)
    {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (hsign : ∀ χ, Q χ → χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row) ∨
      -χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row))
    {χ : b.support → ℤ} (hχ : Q χ) :
    ∃ (j : ι) (m : ℕ), 0 < m ∧ χ = m • fun k : b.support ↦ P.pairingIn ℤ j k := by
  rcases hsign χ hχ with hC | hC
  · exact b.exists_eq_nsmul_pairingIn_of_mem_closure hrefl hsign hχ hC
  -- A negative weight is the negative of a positive one, for the negated property.
  obtain ⟨j, m, hm, hjm⟩ := b.exists_eq_nsmul_pairingIn_of_mem_closure (Q := fun ψ ↦ Q (-ψ))
    (b.neg_reflection_stable hrefl)
    (fun ψ hψ ↦ by simpa [or_comm] using hsign _ hψ) (by simpa using hχ) hC
  refine ⟨P.reflectionPerm j j, m, hm, ?_⟩
  rw [← neg_neg χ, hjm]
  funext k
  simp

end RootPairing.Base
