/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.DelineatingSet.Basic
public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.OrderInvariant
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
public import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Simultaneous delineating refinement over a point

The roots of the delineating sets of a finite polynomial family cut the line over a base point
into one common stack. Every input has constant ambient order on each cell, even when some or
all inputs are nullified over that point. The section list contains exactly those distinct roots;
its length is bounded by the sum of the degrees of the delineating polynomials.

Over the reals, this is a semialgebraic stack of analytic submanifolds: its sections have
dimension zero and its sectors have dimension one. Every input is also sign-invariant on each
cell. This supplies the simultaneous local refinement needed when lifting a polynomial family
over a zero-dimensional base cell. The cell version accepts any preconnected
zero-dimensional analytic submanifold: its chart condition forces it to be a singleton.
The empty family and zero polynomials are allowed.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), 242–268.
* C. W. Brown, *The McCallum projection, lifting, and order-invariance*, technical report
  USNA-CS-TR-2005-02, U.S. Naval Academy (2005).
-/

public section

open MvPolynomial Polynomial Set TauCeti

namespace Finset

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R] [IsAddTorsionFree R] {n : ℕ}

/-- The distinct roots of all delineating sets of a finite family give a common, strictly
ordered stack over a point, on whose cells every input has constant ambient order.
The number of sections is bounded by the sum of the delineating polynomials' degrees. -/
theorem exists_strictMono_orderAt_eq_of_mem_stackCells
    (F : Finset (MvPolynomial (Fin (n + 1)) R)) (α : Fin n → R) :
    ∃ (k : ℕ) (c : Fin k → R), StrictMono c ∧
      (∀ t, t ∈ Set.range c ↔ ∃ f ∈ F, ∃ q ∈ f.delineatingSet α, q.IsRoot t) ∧
      k ≤ ∑ f ∈ F, ∑ q ∈ f.delineatingSet α, q.natDegree ∧
      ∀ f ∈ F, ∀ E ∈ stackCells {α} (fun i _ ↦ c i),
        ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  classical
  let T := F.biUnion fun f ↦ (f.delineatingSet α).biUnion fun q ↦ q.roots.toFinset
  have hT (t : R) : t ∈ T ↔ ∃ f ∈ F, ∃ q ∈ f.delineatingSet α, q.IsRoot t := by
    simp only [T, mem_biUnion, Multiset.mem_toFinset]
    exact exists_congr fun f ↦ and_congr_right fun _ ↦
      exists_congr fun q ↦ and_congr_right fun hq ↦
        Polynomial.mem_roots (mem_delineatingSet.1 hq).1
  have hcard : T.card ≤ ∑ f ∈ F, ∑ q ∈ f.delineatingSet α, q.natDegree := by
    refine card_biUnion_le.trans (sum_le_sum fun f _ ↦ ?_)
    exact card_biUnion_le.trans (sum_le_sum fun q _ ↦
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q))
  refine ⟨T.card, T.orderEmbOfFin rfl, (T.orderEmbOfFin rfl).strictMono, ?_, hcard,
    fun f hf E hE y hy y' hy' ↦ ?_⟩
  · intro t
    rw [range_orderEmbOfFin]
    exact hT t
  · exact f.orderAt_eq_of_mem_stackCells (fun q hq t ht ↦ by
      rw [range_orderEmbOfFin]
      exact (hT t).2 ⟨f, hf, q, hq, ht⟩) hE hy hy'

end Finset

namespace Finset

variable {n : ℕ}

/-- Simultaneous refinement over a real base point gives a semialgebraic stack with a bounded
number of sections. Every cell is an analytic submanifold of dimension zero or one, and every
input polynomial has constant ambient order and sign on it. This includes nullified inputs. -/
theorem exists_isSemialgebraicStack_orderAt_eq
    (F : Finset (MvPolynomial (Fin (n + 1)) ℝ)) (α : Fin n → ℝ) :
    ∃ (k : ℕ) (c : Fin k → ℝ), IsSemialgebraicStack {α} (fun i _ ↦ c i) ∧
      (∀ t, t ∈ Set.range c ↔ ∃ f ∈ F, ∃ q ∈ f.delineatingSet α, q.IsRoot t) ∧
      k ≤ ∑ f ∈ F, ∑ q ∈ f.delineatingSet α, q.natDegree ∧
      ∀ E ∈ stackCells {α} (fun i _ ↦ c i),
        (∃ d ≤ 1, IsAnalyticSubmanifold d E) ∧
        ∀ f ∈ F, (∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y') ∧
          SignInvariant (fun y ↦ eval y f) E := by
  obtain ⟨k, c, hc, hroots, hbound, horder⟩ :=
    F.exists_strictMono_orderAt_eq_of_mem_stackCells α
  have hstack : IsSemialgebraicStack {α} (fun i _ ↦ c i) := by
    simpa using isSemialgebraicStack_eval (isSemialgebraic_singleton α)
      (fun i ↦ MvPolynomial.C (c i)) (fun _ _ ↦ by simpa using hc)
  refine ⟨k, c, hstack, hroots, hbound, fun E hE ↦ ⟨?_, ?_⟩⟩
  · rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨0, Nat.zero_le _, ?_⟩
      -- Over a singleton base, the section is the singleton with that fixed height.
      have hsection : cylinder {α} '' sectionSet (fun i _ ↦ c i) i =
          {Fin.cons (c i) α} := by
        ext y
        simp only [mem_image_cylinder, mem_sectionSet, mem_singleton_iff]
        exact ⟨fun ⟨hα, hi⟩ ↦ by rw [← Fin.cons_self_tail y, hα, ← hi],
          fun h ↦ by subst y; simp⟩
      rw [hsection]
      exact isAnalyticSubmanifold_singleton _
    · exact ⟨1, le_rfl, isAnalyticSubmanifold_image_cylinder_sectorSet
        (isAnalyticSubmanifold_singleton α) hstack.continuous hstack.strictMono j⟩
  · intro f hf
    have ho := horder f hf E hE
    refine ⟨ho, ?_⟩
    exact (isConnected_of_mem_stackCells isConnected_singleton hstack.continuous
      hstack.strictMono hE).isPreconnected.signInvariant_eval_of_orderAt_eq ho

/-- Simultaneous delineating refinement over a preconnected zero-dimensional analytic cell.
Every input has constant ambient order and sign on every part, including nullified inputs.
The resulting parts are analytic submanifolds of dimension zero or one, and the number of
sections is bounded by the degrees of the mixed-derivative specializations at any base point.
No singleton representation of the base cell is required. -/
theorem exists_isSemialgebraicStack_orderAt_eq_of_isAnalyticSubmanifold_zero
    (F : Finset (MvPolynomial (Fin (n + 1)) ℝ)) {S : Set (Fin n → ℝ)}
    (hS : IsAnalyticSubmanifold 0 S) (hconn : IsPreconnected S) :
    ∃ (k : ℕ) (c : Fin k → ℝ), IsSemialgebraicStack S (fun i _ ↦ c i) ∧
      (∀ α ∈ S, ∀ t, t ∈ Set.range c ↔ ∃ f ∈ F, ∃ q ∈ f.delineatingSet α, q.IsRoot t) ∧
      (∀ α ∈ S, k ≤ ∑ f ∈ F, ∑ q ∈ f.delineatingSet α, q.natDegree) ∧
      ∀ E ∈ stackCells S (fun i _ ↦ c i),
        (∃ d ≤ 1, IsAnalyticSubmanifold d E) ∧
        ∀ f ∈ F, (∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y') ∧
          SignInvariant (fun y ↦ eval y f) E := by
  obtain ⟨α, hα⟩ := hS.nonempty
  have hsingleton : S = {α} :=
    (hconn.isDiscrete_iff_subsingleton.mp hS.isDiscrete).eq_singleton_of_mem hα
  subst S
  obtain ⟨k, c, hstack, hroots, hbound, hcells⟩ :=
    F.exists_isSemialgebraicStack_orderAt_eq α
  exact ⟨k, c, hstack, by simpa only [mem_singleton_iff, forall_eq] using hroots,
    by simpa only [mem_singleton_iff, forall_eq] using hbound, hcells⟩

end Finset
