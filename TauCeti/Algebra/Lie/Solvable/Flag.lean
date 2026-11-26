/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Solvable
public import TauCeti.Algebra.Lie.Subalgebra.Flag

/-!
# The flag of the radical through the nilradical

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero, with centre
`Z`, nilradical `N` and solvable radical `R`. This file proves the **flag lemma**: there are Lie
subalgebras

`Z = S₀ ≤ S₁ ≤ ⋯ ≤ S_a = N ≤ ⋯ ≤ S_b = R`

such that each `S i` is an ideal of codimension one in `S (i + 1)`, every `S i` with `i ≤ a` is
nilpotent, and every `S i` with `a ≤ i` is an ideal of `L` whose nilradical is `N`. Every step of
the flag is therefore a split extension by a line, and each step satisfies one of the two
hypotheses under which a nilrepresentation extends across such an extension: below `N` the larger
algebra is nilpotent, and above `N` the nilradicals of the two algebras agree. This is the chain
along which Ado's theorem in characteristic zero grows a representation of the centre into one of
the radical.

The two halves of the flag are built separately.

* Below `N` no assumption on the characteristic is needed: a Lie subalgebra of a nilpotent ideal
  `I` is joined to `I` by a flag of codimension-one steps (`LieIdeal.exists_flag_of_le`).
* Above `N`, `⁅L, R⁆ ≤ N` (`TauCeti.LieAlgebra.lie_radical_le_nilradical`) makes every subspace
  between `N` and `R` an ideal of `L`, so an ordinary flag of subspaces is a flag of ideals
  (`TauCeti.LieAlgebra.exists_flag_nilradical_radical`). The nilradical of each of these ideals is
  `N` (`LieIdeal.map_incl_nilradical_of_le`).

## Main results

* `TauCeti.LieAlgebra.exists_flag_nilradical_radical`: in characteristic zero, the nilradical is
  joined to the radical by a flag of ideals of `L`, each of codimension one in the next.
* `TauCeti.LieAlgebra.exists_flag_center_nilradical_radical`: **the flag lemma**.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2, the flag in
  the proof of Ado's theorem.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter VI, §2.
-/

public section

open LieAlgebra Module

namespace TauCeti

namespace LieAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

variable [CharZero K]

variable (K L) in
/-- **A flag of ideals from the nilradical to the radical.** In characteristic zero, the nilradical
of a finite-dimensional Lie algebra `L` is joined to its radical by a flag of Lie subalgebras
`nilradical K L = S 0 ≤ ⋯ ≤ S n = radical K L`, each an ideal of codimension one in the next, and
each an ideal of `L` containing the nilradical. -/
theorem exists_flag_nilradical_radical :
    ∃ (S : ℕ → LieSubalgebra K L) (n : ℕ), S 0 = nilradical K L ∧ S n = radical K L ∧
      (∀ i < n, S i ≤ S (i + 1) ∧ S (i + 1) ≤ (S i).normalizer ∧
        finrank K (S (i + 1)) = finrank K (S i) + 1) ∧
      ∀ i ≤ n, ∃ J : LieIdeal K L, (J : LieSubalgebra K L) = S i ∧ nilradical K L ≤ J := by
  -- Every subspace `T` between the nilradical and the radical is normalized by all of `L`,
  -- since `⁅L, radical K L⁆ ≤ nilradical K L`.
  have hlie (T : LieSubalgebra K L) (hNT : (nilradical K L : LieSubalgebra K L) ≤ T) (x : L)
      {r : L} (hr : r ∈ radical K L) : ⁅x, r⁆ ∈ T :=
    hNT (lie_radical_le_nilradical K L (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hr))
  have hNR : (nilradical K L : LieSubalgebra K L) ≤ radical K L := fun _ hz ↦
    nilradical_le_radical K L hz
  have hstep (T : LieSubalgebra K L)
      (hT : (nilradical K L : LieSubalgebra K L) ≤ T ∧ T ≤ radical K L) (hlt : T < radical K L) :
      ∃ x ∈ (radical K L : LieSubalgebra K L), x ∉ T ∧ x ∈ T.normalizer ∧
        (nilradical K L : LieSubalgebra K L) ≤ LieSubalgebra.lieSpan K L (insert x (T : Set L)) ∧
          LieSubalgebra.lieSpan K L (insert x (T : Set L)) ≤ radical K L := by
    obtain ⟨hNT, hTR⟩ := hT
    obtain ⟨x, hxR, hxT⟩ := IsConcreteLE.exists_of_lt hlt
    have hxnorm : x ∈ T.normalizer :=
      (T.mem_normalizer_iff x).mpr fun y hy ↦ hlie T hNT x (hTR hy)
    exact ⟨x, hxR, hxT, hxnorm, hNT.trans (T.lt_lieSpan_insert hxT).le,
      LieSubalgebra.lieSpan_le.mpr (Set.insert_subset hxR hTR)⟩
  obtain ⟨S, n, hS0, hSn, hP, hS⟩ := exists_flag_of_forall_lt
    (fun T ↦ (nilradical K L : LieSubalgebra K L) ≤ T ∧ T ≤ radical K L) hstep ⟨le_rfl, hNR⟩ hNR
  refine ⟨S, n, hS0, hSn, hS, fun i hi ↦ ?_⟩
  obtain ⟨hNS, hSR⟩ := hP i hi
  obtain ⟨J, hJ⟩ := (LieSubalgebra.exists_lieIdeal_coe_eq_iff (K := S i)).mpr
    fun x _ hy ↦ hlie _ hNS x (hSR hy)
  refine ⟨J, hJ, fun z hz ↦ ?_⟩
  rw [← LieIdeal.mem_toLieSubalgebra, hJ]
  exact hNS hz

variable (K L) in
/-- **The flag lemma.** Let `L` be a finite-dimensional Lie algebra over a field of characteristic
zero. There are Lie subalgebras

`center K L = S 0 ≤ S 1 ≤ ⋯ ≤ S a = nilradical K L ≤ ⋯ ≤ S b = radical K L`

such that each `S i` is an ideal of codimension one in `S (i + 1)`, every `S i` with `i ≤ a` is
nilpotent, and every `S i` with `a ≤ i ≤ b` is an ideal `J` of `L` whose nilradical, read inside
`L`, is the nilradical of `L`. -/
theorem exists_flag_center_nilradical_radical :
    ∃ (S : ℕ → LieSubalgebra K L) (a b : ℕ), a ≤ b ∧ S 0 = center K L ∧
      S a = nilradical K L ∧ S b = radical K L ∧
      (∀ i < b, S i ≤ S (i + 1) ∧ S (i + 1) ≤ (S i).normalizer ∧
        finrank K (S (i + 1)) = finrank K (S i) + 1) ∧
      (∀ i ≤ a, LieRing.IsNilpotent (S i)) ∧
      ∀ i, a ≤ i → i ≤ b → ∃ J : LieIdeal K L, (J : LieSubalgebra K L) = S i ∧
        (nilradical K J).map J.incl = nilradical K L := by
  obtain ⟨S₁, a, hS₁0, hS₁a, hS₁, hS₁N⟩ := (nilradical K L).exists_flag_of_le
    (T := (center K L : LieSubalgebra K L)) (center_le_nilradical K L)
  obtain ⟨S₂, c, hS₂0, hS₂c, hS₂, hJ⟩ := exists_flag_nilradical_radical K L
  -- Concatenate the flag from the centre to the nilradical with the one from the nilradical to
  -- the radical; the two agree at the nilradical, where the second flag starts.
  let S : ℕ → LieSubalgebra K L := fun i ↦ if i ≤ a then S₁ i else S₂ (i - a)
  have hS_le {i : ℕ} (hi : i ≤ a) : S i = S₁ i := ite_eq_left hi
  have hS_ge {i : ℕ} (hi : a ≤ i) : S i = S₂ (i - a) := by
    rcases hi.lt_or_eq with hi | rfl
    · exact ite_eq_right (by omega)
    · rw [hS_le le_rfl, hS₁a, Nat.sub_self, hS₂0]
  have : LieRing.IsNilpotent (nilradical K L : LieSubalgebra K L) :=
    inferInstanceAs (LieRing.IsNilpotent (nilradical K L))
  refine ⟨S, a, a + c, by omega, by rw [hS_le (Nat.zero_le a), hS₁0], by rw [hS_le le_rfl, hS₁a],
    by rw [hS_ge (by omega), Nat.add_sub_cancel_left, hS₂c], fun i hi ↦ ?_, fun i hi ↦ ?_,
    fun i hai hib ↦ ?_⟩
  · rcases lt_or_ge i a with hia | hia
    · rw [hS_le hia.le, hS_le hia]
      exact hS₁ i hia
    · rw [hS_ge hia, hS_ge (by omega), Nat.sub_add_comm hia]
      exact hS₂ (i - a) (by omega)
  · rw [hS_le hi]
    exact (LieSubalgebra.inclusion_injective (hS₁N i hi)).lieAlgebra_isNilpotent
  · obtain ⟨J, hJS, hNJ⟩ := hJ (i - a) (by omega)
    exact ⟨J, by rw [hJS, hS_ge hai], LieIdeal.map_incl_nilradical_of_le hNJ⟩

end LieAlgebra

end TauCeti
