/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Noetherian
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.TrivSqZeroExt

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Zero
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Checks for locally noetherian formal schemes

`Spf ℤ_[p]` is a noetherian formal scheme (with noetherian underlying space, stalks, and affine
section rings, yet not in the essential image of `ofScheme`), and so are its completed
localisations. Locally noetherian ordinary schemes are locally noetherian formal schemes, and the
affine formal opens of a locally noetherian formal scheme have noetherian rings of sections,
whatever chart exhibits them.

Non-noetherian adic rings — such as a discrete polynomial ring in infinitely many variables, or the
discrete infinite-dimensional trivial square-zero extension `TrivSqZeroExt k (ℕ → k)` whose formal
spectrum has a single point and hence a noetherian underlying space — have formal spectra that are
not locally noetherian.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TauCeti TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.Noetherian

section Padic

variable (p : ℕ) [Fact p.Prime]

-- The formal spectrum of the `p`-adic integers is a noetherian formal scheme.
example : (ofSpf ℤ_[p]).IsNoetherian := inferInstance

-- Its underlying topological space is noetherian, and its topologized section ring is noetherian,
-- yet `ofSpf ℤ_[p]` is not in the essential image of `ofScheme`.
example :
    NoetherianSpace (ofSpf ℤ_[p]) ∧
      IsNoetherianRing (isAffineOpen_top_ofSpf ℤ_[p]).Sections ∧
      ¬ ∃ Y : Scheme.{0}, Nonempty (ofSpf ℤ_[p] ≅ ofScheme.obj Y) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  simp only [ofScheme_obj, exists_ofSpf_iso_toFormalScheme_iff]
  exact PadicInt.not_discreteTopology

-- Its basic open subsets are noetherian formal schemes too.
example (f : ℤ_[p]) : (ofSpf (AdicRing.CompletedAway ℤ_[p] f)).IsNoetherian := inferInstance

-- Stalks of `Spf ℤ_[p]` are noetherian.
example (x : ofSpf ℤ_[p]) : IsNoetherianRing ((ofSpf ℤ_[p]).presheaf.stalk x) := inferInstance

-- Every affine formal open of a locally noetherian formal scheme has a noetherian ring of
-- sections, including those not given by the defining charts.
example (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X) (hU : X.IsAffineOpen U) :
    IsNoetherianRing (X.presheaf.obj (op U)) :=
  hU.isNoetherianRing

-- Open formal subschemes of `Spf ℤ_[p]` are locally noetherian.
example (U : Opens (ofSpf ℤ_[p])) : ((ofSpf ℤ_[p]).restrict U).IsLocallyNoetherian :=
  inferInstance

end Padic

section SchemesAndEmpty

/-- The discrete topology on `ZMod 1` for the empty formal-scheme check. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
local instance zmodOneDiscrete : DiscreteTopology (ZMod 1) := ⟨rfl⟩

-- A noetherian scheme, such as `Spec ℤ`, gives a noetherian formal scheme.
example : (Spec (CommRingCat.of ℤ)).toFormalScheme.IsNoetherian := inferInstance

-- `ofScheme` preserves and reflects both `IsLocallyNoetherian` and `IsNoetherian`.
example (Y : Scheme.{u}) :
    (ofScheme.obj Y).IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian Y := by
  simp

example (Y : Scheme.{u}) :
    (ofScheme.obj Y).IsNoetherian ↔ AlgebraicGeometry.IsNoetherian Y := by
  simp

-- The empty formal scheme `ofSpf (ZMod 1)` is noetherian with no nontriviality assumption.
example : (ofSpf (ZMod 1)).IsNoetherian := inferInstance

end SchemesAndEmpty

section NonNoetherian

/-- The discrete topology on a polynomial ring in countably many variables. -/
local instance mvPolynomialTopology : TopologicalSpace (MvPolynomial ℕ ℚ) := ⊥

/-- Discreteness of the topology on the polynomial ring. -/
local instance mvPolynomialDiscreteTopology : DiscreteTopology (MvPolynomial ℕ ℚ) := ⟨rfl⟩

-- A discrete ring that is not noetherian has a formal spectrum that is not locally noetherian.
example : ¬ (ofSpf (MvPolynomial ℕ ℚ)).IsLocallyNoetherian := by
  simpa using MvPolynomial.not_isNoetherianRing ℕ ℚ

end NonNoetherian

section NoetherianSpaceCounterexample

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

end NoetherianSpaceCounterexample

end TauCeti.Examples.FormalScheme.Noetherian
