/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
-- Private: the monomials of an orthogonal basis, their parity and their reversal signs are used
-- only inside the proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

/-!
# Reversal on odd elements in dimension five

Let `l` be an orthogonal basis of a five-dimensional quadratic module, listed, with volume element
`ω = ι Q v₁ * ⋯ * ι Q v₅`. The Clifford algebra is spanned by the monomials of `l`
(`TauCeti/LinearAlgebra/CliffordAlgebra/Monomials.lean`), and reversal multiplies the monomial of a
sublist of length `k` by `(-1) ^ (k.choose 2)`: it fixes the scalars, the vectors, the products of
four basis vectors and `ω`, and negates the products of two and of three. So for an odd element `y`
the sum `y + reverse y` lies in `V ⊕ R ω`, and an odd element fixed by reversal lies in `V ⊕ R ω`
as soon as `2` is invertible.

This is the dimension-five counterpart of
`TauCeti/LinearAlgebra/CliffordAlgebra/Reversal/Four.lean`, where in dimension at most four such
an element is a vector; the volume element is the one extra term, being odd and reverse-symmetric
exactly when the dimension is `≡ 1 (mod 4)`. Its use is the identification of the Spin group in
dimension five: an even unit `x` with `reverse x * x = 1` sends a vector `ι Q v` to the odd element
`x * ι Q v * reverse x`, which reversal fixes, so it is a vector plus a multiple of `ω`; that the
multiple vanishes is a separate argument, using that `ω` is central.

## Main results

* `CliffordAlgebra.add_reverse_mem_range_ι_sup_span_of_mem_evenOdd_one_of_length_eq_five`: for an
  orthogonal basis of length five, an odd element plus its reversal lies in `V ⊕ R ω`.
* `CliffordAlgebra.mem_range_ι_sup_span_of_mem_evenOdd_one_of_reverse_eq_of_length_eq_five`: for
  an orthogonal basis of length five, an odd element fixed by reversal lies in `V ⊕ R ω`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- **For an orthogonal basis of length five, an odd element plus its reversal is a vector plus a
multiple of the volume element.** Reversal multiplies the monomial of `k` basis vectors by
`(-1) ^ (k.choose 2)`, which is `1` for `k = 0, 1, 4, 5` and `-1` for `k = 2, 3`; the monomials of
length `0` and `4` are even and drop out of an odd element. -/
theorem add_reverse_mem_range_ι_sup_span_of_mem_evenOdd_one_of_length_eq_five {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤)
    (hlen : l.length = 5) {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q 1) :
    y + reverse y ∈ LinearMap.range (ι Q) ⊔ R ∙ (l.map (ι Q)).prod := by
  set T : Submodule R (CliffordAlgebra Q) := LinearMap.range (ι Q) ⊔ R ∙ (l.map (ι Q)).prod
  -- `P` is the submodule of elements whose sum with their reversal lies in `T` up to an even term.
  let P : Submodule R (CliffordAlgebra Q) := (T ⊔ evenOdd Q 0).comap (LinearMap.id + reverse)
  -- Every monomial of `l` lies in `P`, by the sign of reversal on a monomial of each length.
  have hP : Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l}) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    simp only [SetLike.mem_coe, P, Submodule.mem_comap, LinearMap.add_apply, LinearMap.id_apply]
    rw [reverse_prod_map_ι_of_pairwise_isOrtho (hl.sublist ht)]
    have hpow := prod_map_ι_mem_pow Q t
    have hk : t.length ≤ 5 := hlen ▸ ht.length_le
    have heq : t.length = l.length → t = l := ht.eq_of_length
    generalize hlt : t.length = k at hpow hk heq ⊢
    interval_cases k
    · have hev := prod_map_ι_mem_evenOdd_zero_of_even_length (Q := Q) (l := t) (by rw [hlt]; decide)
      rw [Nat.choose_zero_succ, pow_zero, one_smul]
      exact Submodule.mem_sup_right (add_mem hev hev)
    · rw [pow_one] at hpow
      rw [Nat.choose_eq_zero_of_lt Nat.one_lt_two, pow_zero, one_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (add_mem hpow hpow))
    · rw [Nat.choose_self, pow_one, neg_one_smul, add_neg_cancel]
      exact zero_mem _
    · rw [Odd.neg_one_pow (by decide), neg_one_smul, add_neg_cancel]
      exact zero_mem _
    · have hev := prod_map_ι_mem_evenOdd_zero_of_even_length (Q := Q) (l := t) (by rw [hlt]; decide)
      rw [Even.neg_one_pow (by decide), one_smul]
      exact Submodule.mem_sup_right (add_mem hev hev)
    · rw [Even.neg_one_pow (by decide), one_smul, heq hlen.symm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (add_mem (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)))
  have hyP : y ∈ P := hP (by rw [span_prod_map_ι_sublist_eq_top hspan]; exact Submodule.mem_top)
  simp only [P, Submodule.mem_comap, LinearMap.add_apply, LinearMap.id_apply] at hyP
  obtain ⟨o, ho, e, he, hoe⟩ := Submodule.mem_sup.mp hyP
  -- The even term vanishes, since `y + reverse y` and the term in `T` are both odd.
  have hodd : y + reverse y ∈ evenOdd Q 1 := add_mem hy ((reverse_mem_evenOdd_iff (Q := Q)).mpr hy)
  have hT : T ≤ evenOdd Q 1 := by
    refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (prod_map_ι_mem_evenOdd_one_of_odd_length (by rw [hlen]; decide)))
    rintro _ ⟨m, rfl⟩
    exact ι_mem_evenOdd_one Q m
  have he0 : e = 0 := by
    refine (Submodule.disjoint_def.mp (evenOdd_isCompl (Q := Q)).disjoint) e he ?_
    rw [← hoe] at hodd
    simpa using (evenOdd Q 1).sub_mem hodd (hT ho)
  rw [← hoe, he0, add_zero]
  exact ho

variable [Invertible (2 : R)]

/-- **For an orthogonal basis of length five, an odd element fixed by reversal is a vector plus a
multiple of the volume element.** -/
theorem mem_range_ι_sup_span_of_mem_evenOdd_one_of_reverse_eq_of_length_eq_five {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤)
    (hlen : l.length = 5) {y : CliffordAlgebra Q} (hy : y ∈ evenOdd Q 1) (hrev : reverse y = y) :
    y ∈ LinearMap.range (ι Q) ⊔ R ∙ (l.map (ι Q)).prod := by
  have h := add_reverse_mem_range_ι_sup_span_of_mem_evenOdd_one_of_length_eq_five hl hspan hlen hy
  rw [hrev, ← two_smul R y] at h
  simpa using Submodule.smul_mem _ (⅟(2 : R)) h

end CliffordAlgebra
