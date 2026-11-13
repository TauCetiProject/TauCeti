/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Rotate
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Commutators and cyclic classes of paths in a path algebra

In the path algebra `kQ` of a quiver `Q` over a ring `k`, every path between distinct vertices is
the commutator of itself with its target vertex idempotent, and two closed paths related by
rotating a factor from the front to the back differ by a commutator. Over a nontrivial commutative
ring `k`, no closed path lies in the commutator submodule `[kQ, kQ]`: the linear functional sending
basis paths in the rotation class of a fixed closed path to `1` and all other basis paths to `0`
vanishes on additive commutators and evaluates to `1` on that closed path.

No finiteness hypothesis on the vertex or arrow types of `Q` is needed, since `pathAlgebra k Q` is
already a non-unital ring and `k`-module for arbitrary quivers.

## Main results

* `TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_of_ne`: a basis path with distinct source and
  target lies in the commutator submodule.
* `TauCeti.PathAlgebra.ofPath_comp_sub_ofPath_comp_mem_commutatorSubmodule` and
  `TauCeti.PathAlgebra.ofPath_comp_mem_commutatorSubmodule_comm`: rotating composable paths
  changes a closed path by a commutator.
* `TauCeti.PathAlgebra.ofPath_notMem_commutatorSubmodule` and
  `TauCeti.PathAlgebra.vertexIdempotent_notMem_commutatorSubmodule`: over a nontrivial commutative
  ring, no closed basis path (in particular, no vertex idempotent) lies in the commutator
  submodule.
* `TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_iff`: over a nontrivial commutative ring, a
  basis path lies in `[kQ, kQ]` if and only if its endpoints are distinct.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1 and Theorem 3.1.6, for the cyclic quotient of a path
  algebra as the span of cyclic classes of closed paths.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w

section Ring

variable {k : Type w} [Ring k] {Q : Type u} [Quiver.{v} Q]

/-- A basis path between distinct vertices lies in the commutator submodule: it equals the
commutator `e_b * p - p * e_b` with its target vertex idempotent. -/
theorem ofPath_mem_commutatorSubmodule_of_ne {a b : Q} (p : Path a b) (hab : a ≠ b) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) ∈ commutatorSubmodule k (pathAlgebra k Q) := by
  have hcomm := mul_sub_mul_mem_commutatorSubmodule k (pathAlgebra k Q)
    (vertexIdempotent k b) (ofPath ⟨a, b, p⟩)
  rwa [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent_of_ne _ hab.symm,
    sub_zero] at hcomm

/-- Rotating two composable paths between `a` and `b` changes their closed concatenation by an
additive commutator. -/
theorem ofPath_comp_sub_ofPath_comp_mem_commutatorSubmodule {a b : Q} (p : Path a b)
    (q : Path b a) :
    (ofPath ⟨b, b, q.comp p⟩ - ofPath ⟨a, a, p.comp q⟩ : pathAlgebra k Q) ∈
      commutatorSubmodule k (pathAlgebra k Q) := by
  rw [← ofPath_mul_ofPath_of_comp, ← ofPath_mul_ofPath_of_comp]
  exact mul_sub_mul_mem_commutatorSubmodule k (pathAlgebra k Q)
    (ofPath ⟨a, b, p⟩) (ofPath ⟨b, a, q⟩)

/-- A closed concatenation of two composable paths lies in the commutator submodule if and only if
its rotation does. -/
theorem ofPath_comp_mem_commutatorSubmodule_comm {a b : Q} (p : Path a b) (q : Path b a) :
    (ofPath ⟨b, b, q.comp p⟩ : pathAlgebra k Q) ∈ commutatorSubmodule k (pathAlgebra k Q) ↔
      (ofPath ⟨a, a, p.comp q⟩ : pathAlgebra k Q) ∈ commutatorSubmodule k (pathAlgebra k Q) := by
  rw [← ofPath_mul_ofPath_of_comp, ← ofPath_mul_ofPath_of_comp, mul_mem_commutatorSubmodule_comm]

end Ring

section ClosedPath

variable {Q : Type u} [Quiver.{v} Q]

/-- The sequence of arrows of a path, recorded with their endpoints in latest-arrow-first order. -/
private def pathArrows : ∀ {a b : Q}, Path a b → List (Σ i j : Q, i ⟶ j)
  | _, _, .nil => []
  | _, _, .cons q e => ⟨_, _, e⟩ :: pathArrows q

private theorem pathArrows_comp {a b c : Q} (p : Path a b) (q : Path b c) :
    pathArrows (p.comp q) = pathArrows q ++ pathArrows p := by
  induction q with
  | nil => simp [pathArrows]
  | cons q e ih => simp only [Path.comp_cons, pathArrows, ih, List.cons_append]

open Classical in
/-- The linear functional on `pathAlgebra k Q` sending closed basis paths whose arrow sequence is a
cyclic rotation of `p` to `1` and all other basis paths to `0`. -/
private noncomputable def closedPathIndicator (k : Type w) [Semiring k] {a : Q} (p : Path a a) :
    pathAlgebra k Q →ₗ[k] k :=
  liftLinear k fun x =>
    if x.1 = x.2.1 ∧ (pathArrows x.2.2).IsRotated (pathArrows p) then 1 else 0

open Classical in
private theorem closedPathIndicator_ofPath (k : Type w) [Semiring k] {a : Q} (p : Path a a)
    (x : Quiver.TotalPath Q) :
    closedPathIndicator k p (ofPath x) =
      if x.1 = x.2.1 ∧ (pathArrows x.2.2).IsRotated (pathArrows p) then 1 else 0 :=
  liftLinear_ofPath k _ x

private theorem closedPathIndicator_mul_ofPath (k : Type w) [Semiring k] {a : Q} (p : Path a a)
    (x y : Quiver.TotalPath Q) :
    closedPathIndicator k p (ofPath x * ofPath y) =
      closedPathIndicator k p (ofPath y * ofPath x) := by
  classical
  obtain ⟨a₁, b₁, p₁⟩ := x
  obtain ⟨a₂, b₂, p₂⟩ := y
  by_cases hb₂ : b₂ = a₁
  · subst hb₂
    by_cases hb₁ : b₁ = a₂
    · subst hb₁
      simp only [ofPath_mul_ofPath_of_comp, closedPathIndicator_ofPath, true_and, pathArrows_comp]
      have hrot : (pathArrows p₁ ++ pathArrows p₂).IsRotated (pathArrows p) ↔
          (pathArrows p₂ ++ pathArrows p₁).IsRotated (pathArrows p) :=
        ⟨fun h => List.isRotated_append.symm.trans h, fun h => List.isRotated_append.trans h⟩
      simp only [hrot]
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hb₁,
        closedPathIndicator_ofPath, map_zero]
      simp only [Ne.symm hb₁, false_and, ite_false]
  · rw [ofPath_mul_ofPath_of_not_composable hb₂, map_zero]
    by_cases hb₁ : b₁ = a₂
    · subst hb₁
      rw [ofPath_mul_ofPath_of_comp, closedPathIndicator_ofPath]
      simp only [Ne.symm hb₂, false_and, ite_false]
    · rw [ofPath_mul_ofPath_of_not_composable hb₁, map_zero]

private theorem closedPathIndicator_mul_comm (k : Type w) [CommSemiring k] {a : Q}
    (p : Path a a) (f g : pathAlgebra k Q) :
    closedPathIndicator k p (f * g) = closedPathIndicator k p (g * f) := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp only [add_mul, mul_add, map_add, hf₁, hf₂]
  | single x c =>
    induction g using induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp only [add_mul, mul_add, map_add, hg₁, hg₂]
    | single y d =>
      simp only [single_eq_smul_ofPath, smul_mul_assoc, mul_smul_comm, map_smul,
        closedPathIndicator_mul_ofPath, smul_smul, mul_comm]

variable {k : Type w} [CommRing k] [Nontrivial k]

/-- Over a nontrivial commutative ring, no closed basis path lies in the commutator submodule of
the path algebra. -/
theorem ofPath_notMem_commutatorSubmodule {a : Q} (p : Path a a) :
    (ofPath ⟨a, a, p⟩ : pathAlgebra k Q) ∉ commutatorSubmodule k (pathAlgebra k Q) := by
  intro hp
  have hker := (commutatorSubmodule_le_ker_iff (closedPathIndicator k p)).2
    (closedPathIndicator_mul_comm k p)
  have hz := LinearMap.mem_ker.mp (hker hp)
  rw [closedPathIndicator_ofPath] at hz
  simp only [true_and, List.IsRotated.refl, ite_true] at hz
  exact one_ne_zero hz

/-- Over a nontrivial commutative ring, no vertex idempotent lies in the commutator submodule of
the path algebra. -/
theorem vertexIdempotent_notMem_commutatorSubmodule (v : Q) :
    vertexIdempotent k v ∉ commutatorSubmodule k (pathAlgebra k Q) := by
  rw [vertexIdempotent_eq_ofPath]
  exact ofPath_notMem_commutatorSubmodule Path.nil

/-- Over a nontrivial commutative ring, a basis path lies in the commutator submodule of the path
algebra if and only if its source and target are distinct. -/
@[simp]
theorem ofPath_mem_commutatorSubmodule_iff (x : Quiver.TotalPath Q) :
    (ofPath x : pathAlgebra k Q) ∈ commutatorSubmodule k (pathAlgebra k Q) ↔ x.1 ≠ x.2.1 := by
  obtain ⟨a, b, p⟩ := x
  refine ⟨fun h hab => ?_, fun hab => ofPath_mem_commutatorSubmodule_of_ne p hab⟩
  dsimp only at hab
  subst hab
  exact ofPath_notMem_commutatorSubmodule p h

end ClosedPath

end TauCeti.PathAlgebra
