/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.AlgebraicGeometry.FormalScheme.Noetherian
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Examples and counterexamples for locally noetherian formal schemes

We exercise `TauCeti.FormalScheme.IsLocallyNoetherian` and `TauCeti.FormalScheme.IsNoetherian` on
positive examples and a key boundary counterexample:

1. **`p`-adic formal disc (`ofSpf ℤ_[p]`):** `ofSpf ℤ_[p]` is a noetherian formal scheme (with
   noetherian stalks, noetherian affine section rings, and a noetherian underlying space) that does
   not come from any ordinary scheme via `ofScheme`.
2. **Ordinary schemes (`Spec ℤ`, empty formal scheme `ofSpf (ZMod 1)`):** `ofScheme` preserves and
   reflects both `IsLocallyNoetherian` and `IsNoetherian`.
3. **Counterexample (`NoetherianSpace X` does not imply `X.IsLocallyNoetherian`):** for any field
   `k`, the discrete trivial square-zero extension `A = TrivSqZeroExt k (ℕ → k)` has a unique prime
   ideal, so `ofSpf A` is a one-point formal scheme (`Subsingleton (ofSpf A)` and
   `NoetherianSpace (ofSpf A)`), yet `A` has a strictly ascending chain of square-zero ideals so
   `¬ (ofSpf A).IsLocallyNoetherian` by EGA I, Ch. I, 10.6.5 (`ofSpf_isLocallyNoetherian_iff`).
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry TauCeti
open TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.Noetherian

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance padicIntIsAdicRing : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

-- `ofSpf ℤ_[p]` is a noetherian formal scheme with noetherian stalks and noetherian section rings,
-- yet is not in the essential image of `ofScheme`.
example :
    (ofSpf ℤ_[p]).IsNoetherian ∧ NoetherianSpace (ofSpf ℤ_[p]) ∧
      (∀ x : ofSpf ℤ_[p], IsNoetherianRing ((ofSpf ℤ_[p]).presheaf.stalk x)) ∧
      ¬ ∃ Y : Scheme.{0}, Nonempty (ofSpf ℤ_[p] ≅ ofScheme.obj Y) := by
  refine ⟨inferInstance, inferInstance, fun x ↦ inferInstance, ?_⟩
  simp only [ofScheme_obj, exists_iso_toFormalScheme_iff]
  intro hdisc
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
  rw [nhds_discrete, Filter.tendsto_pure] at hnil
  obtain ⟨n, hn⟩ := hnil.exists
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

end Padic

section SchemesAndEmpty

/-- The discrete topology on `ZMod 1` for the empty formal-scheme check. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
local instance zmodOneDiscrete : DiscreteTopology (ZMod 1) := ⟨rfl⟩

-- `Spec ℤ` viewed as a formal scheme is noetherian, and `ofScheme` reflects `IsNoetherian`.
example : (Spec (CommRingCat.of ℤ)).toFormalScheme.IsNoetherian :=
  inferInstance

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
abbrev InfSqZero := TrivSqZeroExt k (ℕ → k)

/-- The discrete topology on `InfSqZero k` for the counterexample. -/
local instance infSqZeroTopology : TopologicalSpace (InfSqZero k) := ⊥
local instance infSqZeroDiscrete : DiscreteTopology (InfSqZero k) := ⟨rfl⟩

private theorem prime_eq_ker_fst (P : Ideal (InfSqZero k)) [hP : P.IsPrime] :
    P = RingHom.ker (TrivSqZeroExt.fstHom k k (ℕ → k)).toRingHom := by
  ext x
  rw [RingHom.mem_ker]
  -- Evaluate `(fstHom k k (ℕ → k)).toRingHom` as the first projection `x.fst`.
  change x ∈ P ↔ x.fst = 0
  constructor
  · intro hx
    by_contra hne
    have hunit : IsUnit x :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hne)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx hunit)
  · intro hx
    have hxeq : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [hx]) (by simp)
    have hsq : x * x ∈ P := by
      rw [hxeq, TrivSqZeroExt.inr_mul_inr]
      exact P.zero_mem
    exact (hP.mem_or_mem hsq).elim id id

private theorem subsingleton_ofSpf_infSqZero : Subsingleton (ofSpf (InfSqZero k)) := by
  refine ⟨fun p q ↦ Subtype.ext (PrimeSpectrum.ext ?_)⟩
  have hp := prime_eq_ker_fst k p.1.asIdeal
  have hq := prime_eq_ker_fst k q.1.asIdeal
  exact hp.trans hq.symm

/-- The `n`-th prefix square-zero ideal `{x | x.fst = 0 ∧ ∀ m ≥ n, x.snd m = 0}`. -/
private def prefixIdeal (n : ℕ) : Ideal (InfSqZero k) where
  carrier := {x | x.fst = 0 ∧ ∀ m ≥ n, x.snd m = 0}
  zero_mem' := ⟨rfl, fun _ _ ↦ rfl⟩
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], fun m hm ↦ by simp [ha.2 m hm, hb.2 m hm]⟩
  smul_mem' a x hx := by
    refine ⟨by simp [hx.1], fun m hm ↦ ?_⟩
    -- Unfold scalar multiplication on the ideal carrier as ring multiplication `a * x`.
    change (a * x).snd m = 0
    simp [TrivSqZeroExt.snd_mul, hx.1, hx.2 m hm]

private theorem not_isNoetherianRing_infSqZero : ¬ IsNoetherianRing (InfSqZero k) := by
  intro hnoeth
  have hmono : Monotone (prefixIdeal k) :=
    fun i j hij _ hx ↦ ⟨hx.1, fun m hm ↦ hx.2 m (hij.trans hm)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hnoeth ⟨prefixIdeal k, hmono⟩
  let e : InfSqZero k := TrivSqZeroExt.inr fun m ↦ if m = n then (1 : k) else 0
  have he_succ : e ∈ prefixIdeal k (n + 1) := by
    refine ⟨rfl, fun m hm ↦ ?_⟩
    have hmn : m ≠ n := Nat.ne_of_gt (Nat.lt_of_succ_le hm)
    simp [e, hmn]
  have heq : prefixIdeal k n = prefixIdeal k (n + 1) := hn (n + 1) (Nat.le_succ n)
  have he_n : e ∈ prefixIdeal k n := heq ▸ he_succ
  have h := he_n.2 n le_rfl
  simp [e] at h

-- Counterexample: `ofSpf (InfSqZero k)` has a noetherian (in fact subsingleton) underlying space,
-- yet is NOT locally noetherian! Thus the converse of `IsNoetherian.noetherianSpace` fails.
example :
    Subsingleton (ofSpf (InfSqZero k)) ∧ NoetherianSpace (ofSpf (InfSqZero k)) ∧
      ¬ (ofSpf (InfSqZero k)).IsLocallyNoetherian ∧ ¬ (ofSpf (InfSqZero k)).IsNoetherian := by
  have : Subsingleton (ofSpf (InfSqZero k)) := subsingleton_ofSpf_infSqZero k
  have : NoetherianSpace (ofSpf (InfSqZero k)) := inferInstance
  have hnotL : ¬ (ofSpf (InfSqZero k)).IsLocallyNoetherian := by
    rw [ofSpf_isLocallyNoetherian_iff]
    exact not_isNoetherianRing_infSqZero k
  exact ⟨inferInstance, inferInstance, hnotL, fun hN ↦ hnotL hN.toIsLocallyNoetherian⟩

end Counterexample

end TauCeti.Examples.FormalScheme.Noetherian
