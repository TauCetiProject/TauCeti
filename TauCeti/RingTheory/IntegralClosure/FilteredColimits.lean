/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Integrality at a stage of a directed system

An integral equation over a directed colimit uses finitely many coefficients. If coefficients
have stage representatives and vanishing is detected eventually, that equation holds at a stage.
-/

public section

namespace TauCeti

/-- An integral element in a directed ring colimit is integral at a stage, provided
coefficients have stage representatives and vanishing is eventually detected. -/
theorem integral_at_stage
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (B C : J → Type*) [∀ j, CommRing (B j)] [∀ j, Ring (C j)]
    {Bcolim Ccolim : Type*} [CommRing Bcolim] [Ring Ccolim]
    (bmap : ∀ {i j : J}, i ≤ j → B i →+* B j)
    (cmap : ∀ {i j : J}, i ≤ j → C i →+* C j)
    (bι : ∀ j, B j →+* Bcolim) (cι : ∀ j, C j →+* Ccolim)
    (φ : ∀ j, B j →+* C j) (φcolim : Bcolim →+* Ccolim)
    (bcompat : ∀ {i j} (h : i ≤ j) b, bι j (bmap h b) = bι i b)
    (φcompat : ∀ j b, cι j (φ j b) = φcolim (bι j b))
    (φtrans : ∀ {i j} (h : i ≤ j) b, cmap h (φ i b) = φ j (bmap h b))
    (rep : ∀ b : Bcolim, ∃ j, ∃ t : B j, bι j t = b)
    (zero : ∀ j (z : C j), cι j z = 0 → ∃ k, ∃ h : j ≤ k, cmap h z = 0)
    (x : ∀ j, C j) (xcolim : Ccolim)
    (hx : ∀ j, cι j (x j) = xcolim)
    (htrans : ∀ {i j} (h : i ≤ j), cmap h (x i) = x j)
    (hi : φcolim.IsIntegralElem xcolim) : ∃ j, (φ j).IsIntegralElem (x j) := by
  classical
  obtain ⟨p, hp, heval⟩ := hi
  choose stage coeff hcoeff using fun k : Fin p.natDegree ↦ rep (p.coeff k)
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  have hstage (k : Fin p.natDegree) : stage k ≤ j :=
    hj _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  let q : Polynomial (B j) := Polynomial.X ^ p.natDegree +
    ∑ k : Fin p.natDegree, Polynomial.C (bmap (hstage k) (coeff k)) * Polynomial.X ^ (k : ℕ)
  have hq : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hqmap : q.map (bι j) = p := by
    rw [hp.as_sum]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, bcompat, hcoeff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ Polynomial.C (p.coeff k) * Polynomial.X ^ k) p.natDegree
  have hvanish : cι j (q.eval₂ (φ j) (x j)) = 0 := by
    have hcomm : (cι j).comp (φ j) = φcolim.comp (bι j) := by
      ext b
      exact φcompat j b
    rw [Polynomial.hom_eval₂, hcomm, ← Polynomial.eval₂_map, hx, hqmap]
    exact heval
  obtain ⟨k, hjk, hk⟩ := zero j (q.eval₂ (φ j) (x j)) hvanish
  refine ⟨k, q.map (bmap hjk), hq.map _, ?_⟩
  have hcomm : (cmap hjk).comp (φ j) = (φ k).comp (bmap hjk) := by
    ext b
    exact φtrans hjk b
  rw [Polynomial.eval₂_map, ← htrans hjk, ← hcomm, ← Polynomial.hom_eval₂]
  exact hk

end TauCeti
