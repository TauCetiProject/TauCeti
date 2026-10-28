/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Topology of relational configurations

The product topology on relational configurations is compact Hausdorff. Specifying an atom's
truth value gives a clopen, measurable cylinder. On countable carriers in countable relational
vocabularies the topology is Polish and its Borel σ-algebra is the existing product σ-algebra.
The same construction handles finite and empty carriers.

These are the usual spaces of structures used for the logic action; see Gao,
*Invariant Descriptive Set Theory*. The measurable coordinates and encoding of structures are
those of `TauCeti.RelationalConfiguration`; no second space of Boolean codes is introduced.
-/

public section

open TopologicalSpace

namespace TauCeti.RelationalConfiguration

variable {L : FirstOrder.Language} {V : Type*}

instance : TopologicalSpace (RelationalConfiguration L V) :=
  inferInstanceAs (TopologicalSpace (Atom L V → Bool))

instance : CompactSpace (RelationalConfiguration L V) :=
  inferInstanceAs (CompactSpace (Atom L V → Bool))

instance : T2Space (RelationalConfiguration L V) :=
  inferInstanceAs (T2Space (Atom L V → Bool))

/-- Reading one atom is continuous. -/
@[fun_prop]
theorem continuous_eval (a : Atom L V) :
    Continuous (fun c : RelationalConfiguration L V => c.eval a) := by
  simp only [eval_def]
  exact continuous_apply a

/-- Continuity into configurations is equivalent to continuity of every atom coordinate. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → RelationalConfiguration L V} :
    Continuous f ↔ ∀ a, Continuous (fun x => (f x).eval a) := by
  simp only [eval_def]
  exact continuous_pi_iff

/-- Building a configuration from its atom values is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk : (Atom L V → Bool) → RelationalConfiguration L V) :=
  continuous_iff.2 fun a => by simpa using (continuous_apply a (A := fun _ => Bool))

/-- Restricting along a vertex map is continuous. -/
@[fun_prop]
theorem continuous_restrict {W : Type*} (f : V → W) :
    Continuous (restrict (L := L) f) :=
  continuous_iff.2 fun a => by simpa using continuous_eval (a.map f)

/-- The configurations giving a fixed answer to one atom form a clopen cylinder. -/
theorem isClopen_setOf_eval (a : Atom L V) (b : Bool) :
    IsClopen {c : RelationalConfiguration L V | c.eval a = b} :=
  (isClopen_discrete {b}).preimage (continuous_eval a)

instance [∀ n, Countable (L.Relations n)] [Countable V] :
    SecondCountableTopology (RelationalConfiguration L V) :=
  inferInstanceAs (SecondCountableTopology (Atom L V → Bool))

instance [∀ n, Countable (L.Relations n)] [Countable V] :
    PolishSpace (RelationalConfiguration L V) := by
  have : IsCompletelyMetrizableSpace (Atom L V → Bool) :=
    IsCompletelyMetrizableSpace.pi_countable
  exact inferInstanceAs (PolishSpace (Atom L V → Bool))

instance [∀ n, Countable (L.Relations n)] [Countable V] :
    BorelSpace (RelationalConfiguration L V) :=
  inferInstanceAs (BorelSpace (Atom L V → Bool))

/-- There are at most continuum many configurations on a countable carrier in a countable
relational vocabulary. Function symbols play no role. -/
theorem mk_le_continuum (L : FirstOrder.Language) (V : Type*)
    [∀ n, Countable (L.Relations n)] [Countable V] :
    Cardinal.mk (RelationalConfiguration L V) ≤ Cardinal.continuum := by
  rw [RelationalConfiguration, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.lift_ofNat]
  exact (Cardinal.power_le_power_left (by norm_num) Cardinal.mk_le_aleph0).trans_eq
    Cardinal.two_power_aleph0

end TauCeti.RelationalConfiguration
