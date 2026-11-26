/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Defs
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Group.Pointwise.Set.Finite
import TauCeti.Combinatorics.Additive.ImageCard
import TauCeti.Data.Set.Card

/-!
# The residual subspace of Waldschmidt's rank argument

In the rank argument of Waldschmidt's proof of his lower bound for linear forms in logarithms
(W00 §9.2.3), the columns of the interpolation matrix are indexed by the elements of a finite set
`S ⊆ ℤᵐ`, or rather of its sums of differences, lying in a subspace `V ⊆ Kᵐ`. With
`c = (β₁, …, β_{m-1}, -1)` the coefficient vector of the normalized linear form and
`π_V : Kᵐ → Kᵐ / V` the quotient map, `V` is chosen to contain `c` and to have the smallest
dimension `d` among those with

`(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`.

The minimality is what the induction on proper subspaces `V' ⊊ V` uses: a subspace `V' ∋ c` of
smaller dimension `d'` violates the inequality, and comparing the two inequalities through the
fibres of `π_V` on `S` shows that the differences of elements of `S` lying in `V` fall into more
than `(d + 1) T₀^(d-d') / (d' + 1)` classes modulo `V'`. This lower bound is opposed to the
degree of an obstruction subgroup of codimension `d - d'` produced by the zero estimate. The
obstruction lives among the grid points `s · y`, in a subspace `W' = V' · y + K e₀` containing
the direction `e₀` of the derivatives; since `c · y = -β₀ e₀`, the grid points of two indices are
congruent modulo `W'` exactly when the indices are congruent modulo `V'`, so the count transfers.

Throughout, `m = n + 1`. The existence and counting statements hold for any vector `c`, nonzero
for the existence; the grid-point statements take `c = Fin.snoc (fun k ↦ b k.succ) (-1)` for the
coefficient vector `b = (β₀, β₁, …, β_{m-1})`, as in `TauCeti.waldschmidtPointMap_snoc`.

## Main results

* `TauCeti.IsWaldschmidtResidual`: `V` contains `c`, satisfies
  `(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`, and has the smallest dimension among such subspaces.
* `TauCeti.exists_isWaldschmidtResidual`: such a subspace `V` exists, and `d ≥ 1`.
* `TauCeti.mul_pow_lt_mul_ncard_image_mkQ_sub_inter_of_isWaldschmidtResidual`: for such a minimal
  `V` and every subspace `V' ∋ c` of dimension `d' < d`,
  `(d + 1) T₀^(d-d') < (d' + 1) #π_{V'}((S - S) ∩ V)`.
* `TauCeti.mul_pow_lt_mul_ncard_image_mkQ_nsmul_of_isWaldschmidtResidual`: the same bound for the
  `k`-fold sums `((S - S) ∩ V)[k]`, `k ≥ 1`, which index the columns of the rank argument for
  `k = m + 1`.
* `TauCeti.ncard_image_mkQ_waldschmidtPoint`: for `V' ∋ c`, a set of indices has as many grid
  points modulo `V' · y + K e₀` as classes modulo `V'`.
* `TauCeti.mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint`: for a minimal `V` and every proper
  subspace `W' ⊊ V · y + K e₀` containing `e₀`, of dimension `d'`, the grid points of
  `((S - S) ∩ V)[k]` satisfy `(d + 1) T₀^(d-d') < (d' + 1) #π_{W'}(((S - S) ∩ V)[k] · y)`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3, Proposition 9.16.
-/

public section

open Module
open scoped Pointwise

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- **The residual subspace of the rank argument.** For a set `S ⊆ ℤᵐ` and a vector `c ∈ Kᵐ`
(in the application, the coefficient vector `c = (β₁, …, β_{m-1}, -1)` of the normalized linear
form), a subspace `V ⊆ Kᵐ` of dimension `d` is *residual* if it contains `c`, satisfies
`(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`, where `π_V : Kᵐ → Kᵐ / V` is the quotient map, and has the
smallest dimension among all subspaces containing `c` that satisfy the corresponding
inequality. -/
structure IsWaldschmidtResidual (c : Fin (n + 1) → K) (S : Set (Fin (n + 1) → ℤ)) (T₀ : ℕ)
    (V : Submodule K (Fin (n + 1) → K)) : Prop where
  /-- The residual subspace contains `c`. -/
  mem : c ∈ V
  /-- The residual subspace satisfies `(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`. -/
  mul_ncard_image_mkQ_le : (finrank K V + 1) * ((fun s ↦ V.mkQ fun i ↦ (s i : K)) '' S).ncard ≤
    (n + 2) * T₀ ^ (n + 1 - finrank K V)
  /-- The residual subspace has the smallest dimension among the subspaces containing `c` that
  satisfy the inequality. -/
  finrank_le : ∀ V' : Submodule K (Fin (n + 1) → K), c ∈ V' →
    (finrank K V' + 1) * ((fun s ↦ V'.mkQ fun i ↦ (s i : K)) '' S).ncard ≤
      (n + 2) * T₀ ^ (n + 1 - finrank K V') → finrank K V ≤ finrank K V'

/-- **Existence of the residual subspace.** For a set `S ⊆ ℤᵐ` and a nonzero vector `c ∈ Kᵐ`
there is a residual subspace `V` in the sense of `TauCeti.IsWaldschmidtResidual`, and its
dimension is at least `1`. The whole space `Kᵐ` satisfies the inequality, and `d ≥ 1` because
`c ≠ 0`. -/
theorem exists_isWaldschmidtResidual {c : Fin (n + 1) → K} (hc : c ≠ 0)
    (S : Set (Fin (n + 1) → ℤ)) (T₀ : ℕ) :
    ∃ V : Submodule K (Fin (n + 1) → K), IsWaldschmidtResidual c S T₀ V ∧ 1 ≤ finrank K V := by
  classical
  let p : ℕ → Prop := fun d ↦ ∃ V : Submodule K (Fin (n + 1) → K), c ∈ V ∧
    finrank K V = d ∧
      (d + 1) * ((fun s ↦ V.mkQ fun i ↦ (s i : K)) '' S).ncard ≤ (n + 2) * T₀ ^ (n + 1 - d)
  -- The whole space qualifies: modulo `Kᵐ` the set `S` has at most one class.
  have hp : ∃ d, p d := by
    refine ⟨n + 1, ⊤, Submodule.mem_top, by simp, ?_⟩
    have : ((fun s ↦ (⊤ : Submodule K (Fin (n + 1) → K)).mkQ fun i ↦ (s i : K)) '' S).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.2 Set.subsingleton_of_subsingleton
    simpa using Nat.mul_le_mul_left (n + 2) this
  obtain ⟨V, hcV, hd, hcard⟩ := Nat.find_spec hp
  exact ⟨V, ⟨hcV, hd ▸ hcard, fun V' hcV' hcard' ↦
    hd ▸ Nat.find_min' hp ⟨V', hcV', rfl, hcard'⟩⟩,
    Submodule.one_le_finrank_iff.2 ((Submodule.ne_bot_iff _).2 ⟨c, hcV, hc⟩)⟩

/-- **Counting on a proper subspace.** Let `V` be a residual subspace of dimension `d` for a
vector `c` (`TauCeti.IsWaldschmidtResidual`):
`(d + 1) #π_V(S) ≤ (m + 1) T₀^(m-d)`, and no subspace containing `c` of smaller dimension satisfies
the corresponding inequality. Then for every subspace `V' ∋ c` of dimension `d' < d`,
the differences of elements of `S` lying in `V` fall into many classes modulo `V'`:

`(d + 1) T₀^(d-d') < (d' + 1) #π_{V'}((S - S) ∩ V)`.

This is the lower bound on the grid which the induction on proper subspaces `V' ⊊ V` opposes to
an obstruction subgroup of codimension `d - d'`. -/
theorem mul_pow_lt_mul_ncard_image_mkQ_sub_inter_of_isWaldschmidtResidual
    {c : Fin (n + 1) → K} {S : Set (Fin (n + 1) → ℤ)} (hS : S.Finite) {T₀ : ℕ}
    {V V' : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual c S T₀ V)
    (hcV' : c ∈ V') (hlt : finrank K V' < finrank K V) :
    (finrank K V + 1) * T₀ ^ (finrank K V - finrank K V') <
      (finrank K V' + 1) * ((fun s ↦ V'.mkQ fun i ↦ (s i : K)) ''
        ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V})).ncard := by
  set d := finrank K V
  set d' := finrank K V'
  let φ : (Fin (n + 1) → ℤ) →+ Fin (n + 1) → K := AddMonoidHom.compLeft (Int.castAddHom K) _
  have hφ (W : Submodule K (Fin (n + 1) → K)) :
      ⇑(W.mkQ.toAddMonoidHom.comp φ) = fun s ↦ W.mkQ fun i ↦ (s i : K) := by
    funext s
    exact congrArg W.mkQ (funext fun i ↦ by simp [φ])
  have hker : ((V.mkQ.toAddMonoidHom.comp φ).ker : Set (Fin (n + 1) → ℤ)) =
      {s | (fun i ↦ (s i : K)) ∈ V} := by
    ext s
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, hφ, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_ofPred_eq]
  have hcount := AddMonoidHom.ncard_image_le_mul_ncard_image_sub_inter_ker
    (V'.mkQ.toAddMonoidHom.comp φ) (V.mkQ.toAddMonoidHom.comp φ) hS
  rw [hker, hφ, hφ] at hcount
  -- By minimality of `V`, the subspace `V'` violates the defining inequality.
  have hV' : (n + 2) * T₀ ^ (n + 1 - d') <
      (d' + 1) * ((fun s ↦ V'.mkQ fun i ↦ (s i : K)) '' S).ncard :=
    lt_of_not_ge fun h ↦ (hV.finrank_le V' hcV' h).not_gt hlt
  have hd : d ≤ n + 1 := (Submodule.finrank_le V).trans_eq (by simp)
  have hpow : T₀ ^ (n + 1 - d') = T₀ ^ (n + 1 - d) * T₀ ^ (d - d') := by
    rw [← pow_add]
    congr 1
    lia
  rw [hpow] at hV'
  by_contra! h
  -- Combine `#π_{V'}(S) ≤ #π_V(S) · #π_{V'}((S - S) ∩ V)` with the two inequalities.
  have := Nat.mul_le_mul hV.mul_ncard_image_mkQ_le h
  have := Nat.mul_le_mul_left (d' + 1) hcount
  nlinarith

/-- **Counting on a proper subspace, for the columns of the rank argument.** The bound of
`TauCeti.mul_pow_lt_mul_ncard_image_mkQ_sub_inter_of_isWaldschmidtResidual` holds for the `k`-fold
sums `((S - S) ∩ V)[k]` with `k ≥ 1`, in particular for the set `((S - S) ∩ V)[m + 1]` indexing
the columns. (The hypotheses force `S` to be nonempty, so `(S - S) ∩ V` contains `0` and is
contained in its `k`-fold sums.) -/
theorem mul_pow_lt_mul_ncard_image_mkQ_nsmul_of_isWaldschmidtResidual
    {c : Fin (n + 1) → K} {S : Set (Fin (n + 1) → ℤ)} (hS : S.Finite) {T₀ : ℕ}
    {V V' : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual c S T₀ V)
    (hcV' : c ∈ V') (hlt : finrank K V' < finrank K V)
    {k : ℕ} (hk : k ≠ 0) :
    (finrank K V + 1) * T₀ ^ (finrank K V - finrank K V') <
      (finrank K V' + 1) * ((fun s ↦ V'.mkQ fun i ↦ (s i : K)) ''
        (k • ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}))).ncard := by
  set A := (S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}
  have hA : A.Finite := (hS.sub hS).inter_of_left _
  -- For empty `S` every subspace satisfies the inequality, against the minimality of `V`.
  have hSne : S.Nonempty := Set.ne_empty_iff_nonempty.1 fun h ↦
    (hV.finrank_le V' hcV' (by simp [h])).not_gt hlt
  have h0 : (0 : Fin (n + 1) → ℤ) ∈ A := ⟨hSne.zero_mem_sub, by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Int.cast_zero]
    exact V.zero_mem⟩
  refine (mul_pow_lt_mul_ncard_image_mkQ_sub_inter_of_isWaldschmidtResidual hS hV hcV' hlt).trans_le
    (Nat.mul_le_mul_left _ (Set.ncard_le_ncard (Set.image_mono (Set.subset_nsmul h0 hk))
      ((hA.nsmul k).image _)))

/-- **Counting grid points modulo `V' · y + K e₀`.** For a subspace `V'` containing the
coefficient vector `c = (β₁, …, β_{m-1}, -1)`, the grid points `s · y` of a set `A` of indices
fall into as many classes modulo `W' = V' · y + K e₀` as the indices do modulo `V'`: two grid
points are congruent modulo `W'` exactly when their indices are congruent modulo `V'`
(`TauCeti.comap_waldschmidtPointMap_map_sup`). -/
theorem ncard_image_mkQ_waldschmidtPoint (b : Fin (n + 1) → K) {V' : Submodule K (Fin (n + 1) → K)}
    (hV' : Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) ∈ V') (A : Set (Fin (n + 1) → ℤ)) :
    ((fun s ↦ (V'.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1).mkQ (waldschmidtPoint b s)) ''
      A).ncard = ((fun s ↦ V'.mkQ fun i ↦ (s i : K)) '' A).ncard := by
  rw [Set.ncard_def, Set.ncard_def, Set.encard_image_eq_encard_image_of_eq_iff fun s s' ↦ ?_]
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, ← waldschmidtPointMap_intCast, ← map_sub,
    ← Submodule.mem_comap, comap_waldschmidtPointMap_map_sup b hV']

/-- **Counting modulo a proper subspace of grid points.** Let `V` be a residual subspace of
dimension `d` for `c = (β₁, …, β_{m-1}, -1)` (`TauCeti.IsWaldschmidtResidual`), and let `W'` be
a proper subspace of `W = V · y + K e₀` containing the direction `e₀` of the derivatives, of
dimension `d'`. Then the grid points `s · y` of the column indices `s ∈ ((S - S) ∩ V)[k]`,
`k ≥ 1`, fall into many classes modulo `W'`:

`(d + 1) T₀^(d-d') < (d' + 1) #π_{W'}(((S - S) ∩ V)[k] · y)`.

This is the form in which the induction on proper subspaces meets an obstruction subgroup
`W' × 𝔾ₘ` of the zero estimate. -/
theorem mul_pow_lt_mul_ncard_image_mkQ_waldschmidtPoint (b : Fin (n + 1) → K)
    {S : Set (Fin (n + 1) → ℤ)} (hS : S.Finite) {T₀ : ℕ}
    {V : Submodule K (Fin (n + 1) → K)}
    (hV : IsWaldschmidtResidual (Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) S T₀ V)
    {W' : Submodule K (Fin (n + 1) → K)} (he₀ : Pi.single 0 1 ∈ W')
    (hW' : W' < V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1) {k : ℕ} (hk : k ≠ 0) :
    (finrank K V + 1) * T₀ ^ (finrank K V - finrank K W') <
      (finrank K W' + 1) * ((fun s ↦ W'.mkQ (waldschmidtPoint b s)) ''
        (k • ((S - S) ∩ {s | (fun i ↦ (s i : K)) ∈ V}))).ncard := by
  obtain ⟨V', hV'V, hcV', rfl⟩ := exists_eq_map_waldschmidtPointMap_sup b hV.mem he₀ hW'.le
  have hlt : finrank K V' < finrank K V := by
    refine (Submodule.finrank_mono hV'V).lt_of_ne fun h ↦ hW'.ne ?_
    rw [Submodule.eq_of_le_of_finrank_eq hV'V h]
  rw [finrank_map_waldschmidtPointMap_sup b hcV', ncard_image_mkQ_waldschmidtPoint b hcV']
  exact mul_pow_lt_mul_ncard_image_mkQ_nsmul_of_isWaldschmidtResidual hS hV hcV' hlt hk

end TauCeti
