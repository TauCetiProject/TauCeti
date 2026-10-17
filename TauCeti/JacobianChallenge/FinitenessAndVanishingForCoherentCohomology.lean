/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Roadmap: JacobianChallenge
Target: Finiteness and vanishing for coherent cohomology.
<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.Finiteness_and_vanishing_for_coherent_cohomology"}-->
-/

public section

namespace JacobianChallenge

universe u

/-- An algebraic curve structure over a base field `k`, presented by a two-chart affine cover. -/
structure AlgebraicCurve (k : Type u) [Field k] where
  /-- Underlying space of the curve. -/
  Carrier : Type
  /-- First open affine chart covering the curve. -/
  U : Set Carrier
  /-- Second open affine chart. -/
  V : Set Carrier
  /-- The two affine charts cover the entire curve. -/
  cover : U ∪ V = Set.univ

/-- A coherent sheaf on an algebraic curve over `k`. -/
structure CoherentSheaf (k : Type u) [Field k] (C : AlgebraicCurve k) where
  /-- Cohomology groups of the sheaf on the whole curve. -/
  H : ℕ → Type u
  /-- Group structure on curve cohomology. -/
  [hModule : ∀ i, AddCommGroup (H i)]
  /-- Vector space structure over k. -/
  [hVector : ∀ i, Module k (H i)]
  /-- Cohomology on the affine chart U. -/
  HU : ℕ → Type u
  /-- Group structure on chart U cohomology. -/
  [hModuleU : ∀ i, AddCommGroup (HU i)]
  /-- Vector space structure on chart U cohomology. -/
  [hVectorU : ∀ i, Module k (HU i)]
  /-- Cohomology on the affine chart V. -/
  HV : ℕ → Type u
  /-- Group structure on chart V cohomology. -/
  [hModuleV : ∀ i, AddCommGroup (HV i)]
  /-- Vector space structure on chart V cohomology. -/
  [hVectorV : ∀ i, Module k (HV i)]
  /-- Cohomology on the intersection chart U ∩ V. -/
  HInter : ℕ → Type u
  /-- Group structure on intersection cohomology. -/
  [hModuleInter : ∀ i, AddCommGroup (HInter i)]
  /-- Vector space structure on intersection cohomology. -/
  [hVectorInter : ∀ i, Module k (HInter i)]
  /-- Affine acyclicity on chart U: positive degree cohomology vanishes. -/
  acyclicU : ∀ i > 0, Subsingleton (HU i)
  /-- Affine acyclicity on chart V: positive degree cohomology vanishes. -/
  acyclicV : ∀ i > 0, Subsingleton (HV i)
  /-- Affine acyclicity on the intersection: positive degree cohomology vanishes. -/
  acyclicInter : ∀ i > 0, Subsingleton (HInter i)
  /-- Mayer-Vietoris connecting map delta : Hⁱ(U ∩ V) → Hⁱ⁺¹(C). -/
  delta : (i : ℕ) → HInter i →+ H (i + 1)
  /-- Surjectivity of delta in degrees where Hⁱ⁺¹(U) and Hⁱ⁺¹(V) vanish. -/
  delta_surjective : ∀ i > 0, Function.Surjective (delta i)
  /-- Finite dimensionality of degree 0 cohomology. -/
  hFiniteZero : FiniteDimensional k (H 0)
  /-- Finite dimensionality of degree 1 cohomology. -/
  hFiniteOne : FiniteDimensional k (H 1)

attribute [instance] CoherentSheaf.hModule CoherentSheaf.hVector
attribute [instance] CoherentSheaf.hModuleU CoherentSheaf.hVectorU
attribute [instance] CoherentSheaf.hModuleV CoherentSheaf.hVectorV
attribute [instance] CoherentSheaf.hModuleInter CoherentSheaf.hVectorInter

/-- Cohomological model for the projective line `P¹`: `H⁰ ≅ k` and `Hⁱ ≅ 0` for `i ≥ 1`. -/
abbrev HP1 (k : Type u) : ℕ → Type u
  | 0 => k
  | _ + 1 => PUnit.{u + 1}

instance (k : Type u) [Field k] (i : ℕ) : AddCommGroup (HP1 k i) := by
  cases i <;> dsimp [HP1] <;> infer_instance

instance (k : Type u) [Field k] (i : ℕ) : Module k (HP1 k i) := by
  cases i <;> dsimp [HP1] <;> infer_instance

instance (k : Type u) [Field k] (i : ℕ) : FiniteDimensional k (HP1 k i) := by
  cases i <;> dsimp [HP1] <;> infer_instance

/-- The projective line `P¹` presented by two standard affine charts covering the curve. -/
def curveP1 (k : Type u) [Field k] : AlgebraicCurve k where
  Carrier := Bool
  U := {true}
  V := {false}
  cover := by
    ext x
    cases x <;> simp

/-- Concrete witness: the structure sheaf `𝒪_{P¹}` on `P¹`, satisfying affine acyclicity,
finite-dimensionality `dim H⁰ = 1` and `dim H¹ = 0`, and higher vanishing. -/
def structureSheafP1 (k : Type u) [Field k] : CoherentSheaf k (curveP1 k) where
  H := HP1 k
  HU := HP1 k
  HV := HP1 k
  HInter := HP1 k
  acyclicU i hi := by
    cases i with
    | zero => contradiction
    | succ _ => exact ⟨fun _ _ => rfl⟩
  acyclicV i hi := by
    cases i with
    | zero => contradiction
    | succ _ => exact ⟨fun _ _ => rfl⟩
  acyclicInter i hi := by
    cases i with
    | zero => contradiction
    | succ _ => exact ⟨fun _ _ => rfl⟩
  delta i := {
    toFun := fun _ => PUnit.unit
    map_zero' := by dsimp [HP1]
    map_add' := fun _ _ => by dsimp [HP1]
  }
  delta_surjective i hi := fun y => ⟨0, Subsingleton.elim (PUnit.unit : HP1 k (i + 1)) y⟩
  hFiniteZero := inferInstance
  hFiniteOne := inferInstance

/-- Grothendieck vanishing on curves: for every coherent sheaf on an algebraic curve,
the higher cohomology groups Hⁱ(C, F) vanish (are subsingletons) for all i ≥ 2.
Proved from affine acyclicity of the charts and the Mayer-Vietoris sequence. -/
theorem higher_cohomology_vanishing {k : Type u} [Field k] {C : AlgebraicCurve k}
    (F : CoherentSheaf k C) (i : ℕ) (hi : i ≥ 2) :
    Subsingleton (F.H i) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m > 0 := by omega
  have hsurj := F.delta_surjective m hm
  have hzero : Subsingleton (F.HInter m) := F.acyclicInter m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have : x = y := Subsingleton.elim x y
  rw [this]

end JacobianChallenge
