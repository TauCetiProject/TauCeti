/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Noetherian
public import TauCeti.RingTheory.AdicRing.Padic
public import TauCeti.RingTheory.TrivSqZeroExt

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Zero
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Examples and counterexamples for locally noetherian formal schemes

We exercise `TauCeti.FormalScheme.IsLocallyNoetherian` and `TauCeti.FormalScheme.IsNoetherian` on
positive examples and a key boundary counterexample:

1. **Formal spectrum of `ℤ_[p]` (`ofSpf ℤ_[p]`):** `ofSpf ℤ_[p]` is a noetherian formal scheme
   (with noetherian stalks, noetherian affine section rings, and a noetherian underlying space)
   that does not come from any ordinary scheme via `ofScheme`.
2. **Ordinary schemes (`Spec ℤ`, empty formal scheme `ofSpf (ZMod 1)`):** `ofScheme` preserves and
   reflects both `IsLocallyNoetherian` and `IsNoetherian`.
3. **Counterexample (`NoetherianSpace X` does not imply `X.IsLocallyNoetherian`):** for any field
   `k`, the discrete trivial square-zero extension `A = TrivSqZeroExt k (ℕ → k)` has a unique prime
   ideal, so `ofSpf A` is a one-point formal scheme (`Subsingleton (ofSpf A)` and
   `NoetherianSpace (ofSpf A)`), yet `A` has a strictly ascending chain of square-zero ideals so
   `¬ (ofSpf A).IsLocallyNoetherian` by EGA I, Ch. I, 10.6.5 (`isLocallyNoetherian_ofSpf_iff`).
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry TauCeti
open TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.Noetherian

section Padic

variable (p : ℕ) [Fact p.Prime]

-- `ofSpf ℤ_[p]` is a noetherian formal scheme with noetherian stalks and noetherian section rings,
-- yet is not in the essential image of `ofScheme`.
example :
    (ofSpf ℤ_[p]).IsNoetherian ∧ NoetherianSpace (ofSpf ℤ_[p]) ∧
      (∀ x : ofSpf ℤ_[p], IsNoetherianRing ((ofSpf ℤ_[p]).presheaf.stalk x)) ∧
      IsNoetherianRing (isAffineOpen_top_ofSpf ℤ_[p]).Sections ∧
      (∀ (U : Opens (ofSpf ℤ_[p])), (ofSpf ℤ_[p]).IsAffineOpen U →
        IsNoetherianRing ((ofSpf ℤ_[p]).presheaf.obj (op U))) ∧
      ¬ ∃ Y : Scheme.{0}, Nonempty (ofSpf ℤ_[p] ≅ ofScheme.obj Y) := by
  refine ⟨inferInstance, inferInstance, fun _ ↦ inferInstance, inferInstance,
    fun _ hU ↦ hU.isNoetherianRing, ?_⟩
  simp only [ofScheme_obj, exists_ofSpf_iso_toFormalScheme_iff]
  exact PadicInt.not_discreteTopology

end Padic

section SchemesAndEmpty

/-- The discrete topology on `ZMod 1` for the empty formal-scheme check. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
local instance zmodOneDiscrete : DiscreteTopology (ZMod 1) := ⟨rfl⟩

-- `Spec ℤ` viewed as a formal scheme is locally noetherian and noetherian, and `ofScheme`
-- preserves and reflects both `IsLocallyNoetherian` and `IsNoetherian`.
example : (Spec (CommRingCat.of ℤ)).toFormalScheme.IsLocallyNoetherian :=
  inferInstance

example : (Spec (CommRingCat.of ℤ)).toFormalScheme.IsNoetherian :=
  inferInstance

example (Y : Scheme.{u}) :
    (ofScheme.obj Y).IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian Y := by
  simp

example (Y : Scheme.{u}) :
    (ofScheme.obj Y).IsNoetherian ↔ AlgebraicGeometry.IsNoetherian Y := by
  simp

-- The empty formal scheme `ofSpf (ZMod 1)` is noetherian with no nontriviality assumption.
example : (ofSpf (ZMod 1)).IsNoetherian :=
  inferInstance

end SchemesAndEmpty

section Counterexample

variable (k : Type u) [Field k]

/-- The infinite-dimensional trivial square-zero extension `k ⊕ (ℕ → k)`. -/
private abbrev InfSqZero := TrivSqZeroExt k (ℕ → k)

/-- The discrete topology on `InfSqZero k` for the counterexample. -/
private instance infSqZeroTopology : TopologicalSpace (InfSqZero k) := ⊥
private instance infSqZeroDiscrete : DiscreteTopology (InfSqZero k) := ⟨rfl⟩

private theorem subsingleton_ofSpf_infSqZero : Subsingleton (ofSpf (InfSqZero k)) := by
  have : Ring.KrullDimLE 0 (InfSqZero k) :=
    Ring.krullDimLE_iff.mpr (by simp [TrivSqZeroExt.ringKrullDim_eq])
  have := Ring.KrullDimLE.subsingleton_primeSpectrum (InfSqZero k)
  exact inferInstanceAs (Subsingleton (Spf.carrier (InfSqZero k)))

/-- The `n`-th prefix square-zero ideal `{x | x.fst = 0 ∧ ∀ m ≥ n, x.snd m = 0}`. -/
private def prefixIdeal (n : ℕ) : Ideal (InfSqZero k) where
  carrier := {x | x.fst = 0 ∧ ∀ m ≥ n, x.snd m = 0}
  zero_mem' := ⟨rfl, fun _ _ ↦ rfl⟩
  add_mem' := fun ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ ↦
    ⟨by simp [ha₁, hb₁], fun m hm ↦ by simp [ha₂ m hm, hb₂ m hm]⟩
  smul_mem' := fun a x ⟨hx₁, hx₂⟩ ↦
    ⟨by simp [smul_eq_mul, hx₁],
      fun m hm ↦ by simp [smul_eq_mul, TrivSqZeroExt.snd_mul, hx₁, hx₂ m hm]⟩

private theorem not_isNoetherianRing_infSqZero : ¬ IsNoetherianRing (InfSqZero k) := by
  intro hnoeth
  have hmono : Monotone (prefixIdeal k) :=
    fun i j hij _ ⟨hx₁, hx₂⟩ ↦ ⟨hx₁, fun m hm ↦ hx₂ m (hij.trans hm)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hnoeth ⟨prefixIdeal k, hmono⟩
  let e : InfSqZero k := TrivSqZeroExt.inr fun m ↦ if m = n then (1 : k) else 0
  have he_succ : e ∈ prefixIdeal k (n + 1) := by
    refine ⟨rfl, fun m hm ↦ ?_⟩
    have hmn : m ≠ n := Nat.ne_of_gt (Nat.lt_of_succ_le hm)
    simp [e, hmn]
  have heq : prefixIdeal k n = prefixIdeal k (n + 1) := hn (n + 1) (Nat.le_succ n)
  have he_n : e ∈ prefixIdeal k n := heq ▸ he_succ
  have h := he_n.right n le_rfl
  simp [e] at h

-- Counterexample: `ofSpf (InfSqZero k)` has a noetherian (in fact subsingleton) underlying space,
-- yet is NOT locally noetherian! Thus the converse of `IsNoetherian.noetherianSpace` fails.
example :
    Subsingleton (ofSpf (InfSqZero k)) ∧ NoetherianSpace (ofSpf (InfSqZero k)) ∧
      ¬ (ofSpf (InfSqZero k)).IsLocallyNoetherian ∧ ¬ (ofSpf (InfSqZero k)).IsNoetherian := by
  have : Subsingleton (ofSpf (InfSqZero k)) := subsingleton_ofSpf_infSqZero k
  have : NoetherianSpace (ofSpf (InfSqZero k)) := inferInstance
  have hnotL : ¬ (ofSpf (InfSqZero k)).IsLocallyNoetherian := by
    rw [isLocallyNoetherian_ofSpf_iff]
    exact not_isNoetherianRing_infSqZero k
  exact ⟨inferInstance, inferInstance, hnotL, fun hN ↦ hnotL hN.toIsLocallyNoetherian⟩

end Counterexample

end TauCeti.Examples.FormalScheme.Noetherian
