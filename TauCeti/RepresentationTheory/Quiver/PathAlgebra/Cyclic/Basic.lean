/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The commutator submodule of a path algebra

In the path algebra `kQ` of an arbitrary quiver `Q`, open paths are commutators with vertex
idempotents, whereas closed paths survive in the cyclic quotient `kQ / [kQ, kQ]` over every
nontrivial commutative ring `k`.

The nonvanishing of closed paths is proved by evaluating linear functionals invariant under cyclic
permutation of arrow sequences, avoiding cyclic derivatives so that positive-characteristic root
powers of closed paths are handled uniformly alongside trivial paths.

## Main results

* `TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_of_ne`: any path with distinct endpoints lies
  in `commutatorSubmodule k (pathAlgebra k Q)`.
* `TauCeti.PathAlgebra.ofPath_notMem_commutatorSubmodule`: over a nontrivial commutative ring `k`,
  no closed path lies in `commutatorSubmodule k (pathAlgebra k Q)`.
* `TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_iff`: a basis path lies in the commutator
  submodule if and only if its source and target are distinct.
-/

public section

namespace TauCeti.PathAlgebra

universe u v w

section Ring

variable (k : Type w) [Ring k] {Q : Type u} [Quiver.{v} Q]

/-- Any path with distinct endpoints is a commutator with the target vertex idempotent, and hence
lies in the commutator submodule of the path algebra. -/
theorem ofPath_mem_commutatorSubmodule_of_ne {a b : Q} (p : _root_.Quiver.Path a b) (hab : a ≠ b) :
    ofPath (⟨a, b, p⟩ : Quiver.TotalPath Q) ∈ commutatorSubmodule k (pathAlgebra k Q) := by
  have h : vertexIdempotent k b * ofPath ⟨a, b, p⟩ - ofPath ⟨a, b, p⟩ * vertexIdempotent k b =
      ofPath ⟨a, b, p⟩ := by
    rw [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent_of_ne _ hab.symm, sub_zero]
  rw [← h]
  exact mul_sub_mul_mem_commutatorSubmodule k _ (vertexIdempotent k b) (ofPath ⟨a, b, p⟩)

end Ring

section CommRing

private def pathArrows {Q : Type u} [Quiver.{v} Q] :
    ∀ {a b : Q}, _root_.Quiver.Path a b → List (Σ i j : Q, i ⟶ j)
  | _, _, .nil => []
  | _, _, .cons p e => pathArrows p ++ [⟨_, _, e⟩]

private theorem pathArrows_comp {Q : Type u} [Quiver.{v} Q] {a b c : Q}
    (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path b c) :
    pathArrows (p.comp q) = pathArrows p ++ pathArrows q := by
  induction q with
  | nil => simp [pathArrows]
  | cons q e ih => simp [_root_.Quiver.Path.comp_cons, pathArrows, ih, List.append_assoc]

open Classical in
private noncomputable def arrowNecklaceFunctional {k : Type w} [CommRing k]
    {Q : Type u} [Quiver.{v} Q] (W : Cycle (Σ i j : Q, i ⟶ j) → k) :
    pathAlgebra k Q →ₗ[k] k :=
  liftLinear k fun x => if x.1 = x.2.1 then W (pathArrows x.2.2) else 0

open Classical in
private theorem arrowNecklaceFunctional_ofPath {k : Type w} [CommRing k]
    {Q : Type u} [Quiver.{v} Q] (W : Cycle (Σ i j : Q, i ⟶ j) → k) (x : Quiver.TotalPath Q) :
    arrowNecklaceFunctional W (ofPath x) =
      if x.1 = x.2.1 then W (pathArrows x.2.2) else 0 :=
  liftLinear_ofPath k _ x

private theorem arrowNecklaceFunctional_mul_ofPath {k : Type w} [CommRing k]
    {Q : Type u} [Quiver.{v} Q] (W : Cycle (Σ i j : Q, i ⟶ j) → k)
    (x y : Quiver.TotalPath Q) :
    arrowNecklaceFunctional W (ofPath x * ofPath y) =
      arrowNecklaceFunctional W (ofPath y * ofPath x) := by
  classical
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst d
    by_cases hbc : b = c
    · subst c
      simp only [ofPath_mul_ofPath_of_comp, arrowNecklaceFunctional_ofPath, ↓reduceIte,
        pathArrows_comp]
      exact congrArg W (Cycle.coe_eq_coe.mpr List.isRotated_append)
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hbc,
        arrowNecklaceFunctional_ofPath, map_zero]
      simp only [Ne.symm hbc, ↓reduceIte]
  · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]
    by_cases hbc : b = c
    · subst c
      rw [ofPath_mul_ofPath_of_comp, arrowNecklaceFunctional_ofPath]
      simp only [Ne.symm hda, ↓reduceIte]
    · rw [ofPath_mul_ofPath_of_not_composable hbc, map_zero]

private theorem arrowNecklaceFunctional_mul_comm {k : Type w} [CommRing k]
    {Q : Type u} [Quiver.{v} Q] (W : Cycle (Σ i j : Q, i ⟶ j) → k)
    (x y : pathAlgebra k Q) :
    arrowNecklaceFunctional W (x * y) = arrowNecklaceFunctional W (y * x) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add, hx, hx']
  | single p a =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [add_mul, mul_add, map_add, hy, hy']
    | single q b =>
      simp only [single_eq_smul_ofPath, smul_mul_assoc, mul_smul_comm, map_smul,
        arrowNecklaceFunctional_mul_ofPath, smul_smul, mul_comm]

variable (k : Type w) [CommRing k] [Nontrivial k] {Q : Type u} [Quiver.{v} Q]

/-- Over a nontrivial commutative ring, no closed path lies in the commutator submodule of the path
algebra. -/
theorem ofPath_notMem_commutatorSubmodule {a : Q} (p : _root_.Quiver.Path a a) :
    ofPath (⟨a, a, p⟩ : Quiver.TotalPath Q) ∉ commutatorSubmodule k (pathAlgebra k Q) := by
  classical
  let W : Cycle (Σ i j : Q, i ⟶ j) → k := fun s => if s = (pathArrows p : Cycle _) then 1 else 0
  have hker : commutatorSubmodule k (pathAlgebra k Q) ≤ LinearMap.ker (arrowNecklaceFunctional W) :=
    (commutatorSubmodule_le_ker_iff _).mpr (arrowNecklaceFunctional_mul_comm W)
  intro hmem
  have hz : arrowNecklaceFunctional W (ofPath ⟨a, a, p⟩) = 0 := LinearMap.mem_ker.mp (hker hmem)
  rw [arrowNecklaceFunctional_ofPath] at hz
  simp only [W, ↓reduceIte] at hz
  exact one_ne_zero hz

/-- A basis path lies in the commutator submodule of the path algebra if and only if its endpoints
are distinct. -/
@[simp]
theorem ofPath_mem_commutatorSubmodule_iff (x : Quiver.TotalPath Q) :
    ofPath x ∈ commutatorSubmodule k (pathAlgebra k Q) ↔ x.1 ≠ x.2.1 := by
  obtain ⟨a, b, p⟩ := x
  dsimp only
  constructor
  · rintro hmem rfl
    exact ofPath_notMem_commutatorSubmodule k p hmem
  · exact ofPath_mem_commutatorSubmodule_of_ne k p

/-- Every closed path represents a nonzero class in the cyclic quotient of the path algebra over a
nontrivial commutative ring. -/
theorem mkQ_ofPath_ne_zero {a : Q} (p : _root_.Quiver.Path a a) :
    (commutatorSubmodule k (pathAlgebra k Q)).mkQ (ofPath ⟨a, a, p⟩) ≠ 0 := by
  intro h
  exact ofPath_notMem_commutatorSubmodule k p ((Submodule.Quotient.mk_eq_zero _).mp h)

/-- Every vertex idempotent lies outside the commutator submodule of the path algebra over a
nontrivial commutative ring. -/
theorem vertexIdempotent_notMem_commutatorSubmodule (a : Q) :
    vertexIdempotent k a ∉ commutatorSubmodule k (pathAlgebra k Q) := by
  rw [vertexIdempotent_eq_ofPath]
  exact ofPath_notMem_commutatorSubmodule k (_root_.Quiver.Path.nil : _root_.Quiver.Path a a)

end CommRing

end TauCeti.PathAlgebra
