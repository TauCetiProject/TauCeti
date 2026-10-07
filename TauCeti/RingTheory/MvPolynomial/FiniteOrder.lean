/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder
public import TauCeti.RingTheory.MvPolynomial.Evaluation.Finite

/-!
# Finitely many directions detecting ambient order uniformly

For a fixed total degree bound, finitely many fixed affine directions detect the ambient
order of every polynomial at every center. The directions may be chosen in any box with
infinite sides. The ambient order is the minimum of the orders of the line restrictions.

Keeping one distinguished coordinate free gives a stronger geometric application: finitely
many transverse planes detect ambient order uniformly. Thus constancy of order in those
plane families implies constancy of full ambient order, rather than merely an inequality
or equality at one chosen center. Infinite orders are retained for zero polynomials.
Zero base directions and zero-dimensional bases are included.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3 (ambient order and transverse restrictions).
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ K : Type*} [Field K] [Finite σ]

/-- With a fixed degree bound, finitely many directions in any box with infinite sides
detect ambient order at every center, for every polynomial within that bound. -/
theorem exists_finset_orderAt_eq_iInf_trailingDegree (D : ℕ)
    (s : σ → Set K) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (σ → K), (↑T : Set (σ → K)) ⊆ Set.pi Set.univ s ∧
      ∀ p : MvPolynomial σ K, p.totalDegree ≤ D → ∀ a : σ → K,
        p.orderAt a = ⨅ v : T,
          (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v.1 i) * Polynomial.X)
            p).trailingDegree := by
  classical
  obtain ⟨T, hT, htest⟩ := exists_finset_eval_eq_zero_iff_of_totalDegree_le D s hs
  refine ⟨T, hT, fun p hp a ↦ le_antisymm ?_ ?_⟩
  · exact le_iInf fun v ↦ p.orderAt_le_trailingDegree_aeval_C_add_C_mul_X a v.1
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    obtain ⟨m, hm : (m : ℕ∞) = p.orderAt a⟩ :=
      ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hp0)
    obtain ⟨⟨d, hd, hdm⟩, -⟩ := orderAt_eq_coe_iff.1 hm.symm
    have hH : homogeneousComponent m (taylor a p) ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (fun q : MvPolynomial σ K ↦ q.coeff d) hzero
      simp [coeff_homogeneousComponent, hdm, hd] at hcoeff
    have hdegree : (homogeneousComponent m (taylor a p)).totalDegree ≤ D := by
      apply (totalDegree_le_of_support_subset ?_).trans
        ((totalDegree_taylor a p).trans_le hp)
      rw [support_homogeneousComponent]
      exact Finset.filter_subset _ _
    obtain ⟨v, hvT, hv⟩ : ∃ v ∈ T, eval v (homogeneousComponent m (taylor a p)) ≠ 0 := by
      simpa only [not_forall, exists_prop] using
        mt (htest _ hdegree).mpr hH
    refine (iInf_le_of_le ⟨v, hvT⟩ ?_).trans_eq hm
    apply Polynomial.trailingDegree_le_of_ne_zero
    simpa only [coeff_aeval_C_add_C_mul_X] using hv

/-- Finitely many fixed base directions detect ambient order on transverse planes at
all centers, uniformly for polynomials of bounded total degree. The plane coordinates are
the base-line parameter and the distinguished root coordinate, respectively. -/
theorem exists_finset_orderAt_eq_iInf_transverse [Infinite K] (n D : ℕ)
    (s : Fin n → Set K) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (Fin n → K), (↑T : Set (Fin n → K)) ⊆ Set.pi Set.univ s ∧
      ∀ p : MvPolynomial (Fin (n + 1)) K, p.totalDegree ≤ D →
        ∀ a : Fin (n + 1) → K,
          p.orderAt a = ⨅ v : T,
            (aeval (Fin.cons (C (a 0) + X (1 : Fin 2))
              (fun i ↦ C (a i.succ) + C (v.1 i) * X (0 : Fin 2))) p).orderAt (0 : Fin 2 → K) := by
  classical
  obtain ⟨t, ht, hline⟩ := exists_finset_orderAt_eq_iInf_trailingDegree D
    (Fin.cons Set.univ s) (fun i ↦ Fin.cases Set.infinite_univ hs i)
  refine ⟨t.image Fin.tail, ?_, fun p hp a ↦ ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact fun i _ ↦ ht hv i.succ (Set.mem_univ _)
  let G (w : Fin n → K) : Fin (n + 1) → MvPolynomial (Fin 2) K :=
    Fin.cons (C (a 0) + X (1 : Fin 2)) (fun i ↦ C (a i.succ) + C (w i) * X 0)
  let q (w : Fin n → K) := aeval (G w) p
  have hcenter (w : Fin n → K) : (fun i ↦ eval (0 : Fin 2 → K) (G w i)) = a := by
    funext i
    cases i using Fin.cases <;> simp [G]
  refine le_antisymm (le_iInf fun w ↦ ?_) ?_
  · simpa only [hcenter] using p.orderAt_le_orderAt_aeval (G w.1) (0 : Fin 2 → K)
  · rw [hline p hp a]
    apply le_iInf
    intro v
    have hcomp :
        aeval (fun j : Fin 2 ↦ Polynomial.C ((0 : Fin 2 → K) j) +
          Polynomial.C (![1, v.1 0] j) * Polynomial.X) (q (Fin.tail v.1)) =
        aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v.1 i) * Polynomial.X) p := by
      dsimp only [q]
      rw [← AlgHom.comp_apply]
      congr 1
      ext i
      cases i using Fin.cases <;> simp [G, Fin.tail]
    refine (iInf_le_of_le
      ⟨Fin.tail v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ ?_)
    simpa only [hcomp] using
      (q (Fin.tail v.1)).orderAt_le_trailingDegree_aeval_C_add_C_mul_X 0 ![1, v.1 0]

end TauCeti
