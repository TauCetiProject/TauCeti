/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FiniteOrder
public import Mathlib.Topology.Perfect

/-!
# Choosing finite order detectors in an open set

Finitely many transverse planes with directions in any prescribed nonempty open set detect
ambient polynomial order uniformly at every center, for all polynomials of bounded degree.
This permits restricting to directions that are good for analytic preparation of a
discriminant, while retaining enough directions to recover the ambient order of the original
polynomial on its root sections.

The scalar field need only be a perfect T1 topological space; no compatibility between the
field operations and the topology is used. In particular the result applies over `ℝ` and `ℂ`.
-/

public section

open Set MvPolynomial

namespace TauCeti

variable {K : Type*} [Field K] [TopologicalSpace K] [T1Space K] [PerfectSpace K]

/-- A finite collection of transverse plane directions in any nonempty open set detects
ambient order at every point for every polynomial with a prescribed total degree bound. -/
theorem exists_finset_orderAt_eq_iInf_transverse_of_isOpen (n D : ℕ)
    {U : Set (Fin n → K)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ T : Finset (Fin n → K), (↑T : Set (Fin n → K)) ⊆ U ∧
      ∀ p : MvPolynomial (Fin (n + 1)) K, p.totalDegree ≤ D →
        ∀ a : Fin (n + 1) → K,
          p.orderAt a = ⨅ v : T,
            (aeval (Fin.cons (C (a 0) + X (1 : Fin 2))
              (fun i ↦ C (a i.succ) + C (v.1 i) * X (0 : Fin 2))) p).orderAt (0 : Fin 2 → K) := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨s, hs, hsU⟩ := isOpen_pi_iff'.1 hU a ha
  have hinfinite (i : Fin n) : (s i).Infinite :=
    infinite_of_mem_nhds (a i) ((hs i).1.mem_nhds (hs i).2)
  obtain ⟨T, hT, horder⟩ := exists_finset_orderAt_eq_iInf_transverse n D s hinfinite
  exact ⟨T, hT.trans hsU, horder⟩

end TauCeti
