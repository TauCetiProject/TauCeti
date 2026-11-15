/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FiniteOrder
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Choosing finite order detectors in an open set

Finitely many transverse planes with directions in any prescribed nonempty open set detect
ambient polynomial order uniformly at every center, for all polynomials of bounded degree.
This permits restricting to directions that are good for analytic preparation of a
discriminant, while retaining enough directions to recover the ambient order of the original
polynomial on its root sections.

As a consequence, if the order of every transverse restriction in such an open set is locally
constant along a family of points, then the ambient order is locally constant as well. Only
finitely many restrictions are needed on a neighborhood of each point, even though the
hypothesis is stated on the whole open set of analytically admissible directions.

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

namespace TauCeti

variable {K X : Type*} [Field K] [TopologicalSpace K] [T1Space K] [PerfectSpace K]
  [TopologicalSpace X]

/-- If every transverse-plane order in a nonempty open set of directions agrees with its
value at a fixed parameter throughout some neighborhood, then the ambient orders agree on
one common neighborhood. The neighborhoods for the individual directions may differ, and the
total-degree bound is needed only near the fixed parameter. -/
theorem eventually_orderAt_eq_of_transverse (n D : ℕ)
    {U : Set (Fin n → K)} (hU : IsOpen U) (hne : U.Nonempty)
    (p : X → MvPolynomial (Fin (n + 1)) K) (a : X → Fin (n + 1) → K)
    {x : X} (hp : ∀ᶠ y in nhds x, (p y).totalDegree ≤ D)
    (hlocal : ∀ v ∈ U, ∀ᶠ y in nhds x,
      (MvPolynomial.aeval
        (Fin.cons (MvPolynomial.C (a y 0) + MvPolynomial.X (1 : Fin 2))
          (fun i ↦ MvPolynomial.C (a y i.succ) +
            MvPolynomial.C (v i) * MvPolynomial.X (0 : Fin 2)))
        (p y)).orderAt (0 : Fin 2 → K) =
      (MvPolynomial.aeval
        (Fin.cons (MvPolynomial.C (a x 0) + MvPolynomial.X (1 : Fin 2))
          (fun i ↦ MvPolynomial.C (a x i.succ) +
            MvPolynomial.C (v i) * MvPolynomial.X (0 : Fin 2)))
        (p x)).orderAt (0 : Fin 2 → K)) :
    ∀ᶠ y in nhds x, (p y).orderAt (a y) = (p x).orderAt (a x) := by
  classical
  obtain ⟨T, hTU, horder⟩ :=
    exists_finset_orderAt_eq_iInf_transverse_of_isOpen n D hU hne
  have hslice : ∀ v : T, ∀ᶠ y in nhds x,
      (MvPolynomial.aeval
        (Fin.cons (MvPolynomial.C (a y 0) + MvPolynomial.X (1 : Fin 2))
          (fun i ↦ MvPolynomial.C (a y i.succ) +
            MvPolynomial.C (v.1 i) * MvPolynomial.X (0 : Fin 2)))
        (p y)).orderAt (0 : Fin 2 → K) =
      (MvPolynomial.aeval
        (Fin.cons (MvPolynomial.C (a x 0) + MvPolynomial.X (1 : Fin 2))
          (fun i ↦ MvPolynomial.C (a x i.succ) +
            MvPolynomial.C (v.1 i) * MvPolynomial.X (0 : Fin 2)))
        (p x)).orderAt (0 : Fin 2 → K) := fun v ↦ hlocal v (hTU v.property)
  filter_upwards [Filter.eventually_all.2 hslice, hp] with y hy hpy
  rw [horder (p y) hpy (a y), horder (p x) hp.self_of_nhds (a x)]
  exact iInf_congr fun v ↦ hy v

/-- Local constancy of all transverse-plane orders in a nonempty open set of directions
implies local constancy of ambient polynomial order. The polynomial and the point may both
vary with the parameter; only a uniform total-degree bound is required. -/
theorem isLocallyConstant_orderAt_of_transverse (n D : ℕ)
    {U : Set (Fin n → K)} (hU : IsOpen U) (hne : U.Nonempty)
    (p : X → MvPolynomial (Fin (n + 1)) K) (a : X → Fin (n + 1) → K)
    (hp : ∀ x, (p x).totalDegree ≤ D)
    (hlocal : ∀ v ∈ U, IsLocallyConstant fun x ↦
      (MvPolynomial.aeval
        (Fin.cons (MvPolynomial.C (a x 0) + MvPolynomial.X (1 : Fin 2))
          (fun i ↦ MvPolynomial.C (a x i.succ) +
            MvPolynomial.C (v i) * MvPolynomial.X (0 : Fin 2)))
        (p x)).orderAt (0 : Fin 2 → K)) :
    IsLocallyConstant fun x ↦ (p x).orderAt (a x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  exact eventually_orderAt_eq_of_transverse n D hU hne p a (.of_forall hp) fun v hv ↦
    (hlocal v hv).eventually_eq x

end TauCeti
