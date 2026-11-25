/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.Structure
import TauCeti.ModelTheory.RelationalConfiguration.Topology
import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.Infinitary.Infinite
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Graph
import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift
import TauCeti.Dynamics.SymbolicDynamics.Basic

/-!
# Spaces of structures on finite, infinite and empty carriers

The order on `ℕ` survives encoding and decoding, and its atom `0 ≤ 1` gives a clopen cylinder.
The finite and infinite coding spaces have the advertised standard Borel structures. Empty
carriers still retain nullary relations, and transport to a different universe preserves
infinitary sentences. The coding space of graphs on `ℕ` has continuum many points.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The order structure, rather than just its carrier, is recovered.
example : (@ofStructure Language.order ℕ (orderStructure ℕ)).toStructure = orderStructure ℕ := by
  simp

example :
    IsClopen {c : RelationalConfiguration Language.order ℕ |
      c.eval (atom (leSymb : Language.order.Relations 2) ![0, 1]) = true} :=
  isClopen_setOf_eval _ _

example {L : Language} [∀ n, Countable (L.Relations n)] (n : ℕ) :
    StandardBorelSpace (RelationalConfiguration L (Fin n)) := inferInstance

example {L : Language} [∀ n, Countable (L.Relations n)] :
    StandardBorelSpace (RelationalConfiguration L ℕ × RelationalConfiguration L ℕ) := inferInstance

-- The empty carrier imposes no constraint on the truth value of a nullary symbol.
example {L : Language} [L.IsRelational] (R : L.Relations 0) (b : Bool) :
    @Structure.RelMap L Empty (mk (fun _ => b)).toStructure 0 R Fin.elim0 ↔ b = true := by
  simp

example {L : Language} [L.IsRelational] {M : Type*} [L.Structure M] (φ : L.Sentenceω) :
    @SentenceInf.Realize L ℕ φ (ULift M)
      ((Equiv.ulift : ULift M ≃ M).symm.encodeVia (L := L)).toStructure ↔
        SentenceInf.Realize φ M :=
  Equiv.realize_encodeVia _ _

-- No configuration on a finite carrier models the infinitude sentence, and every one on `ℕ` does.
example {L : Language} [L.IsRelational] (n : ℕ) :
    (modelsOf L.infiniteSentence : Set (RelationalConfiguration L (Fin n))) = ∅ :=
  modelsOf_infiniteSentence_of_finite

example {L : Language} [L.IsRelational] :
    (modelsOf L.infiniteSentence : Set (RelationalConfiguration L ℕ)) = Set.univ :=
  modelsOf_infiniteSentence_of_infinite

-- Model classes of `L_{ω₁ω}` sentences on countable carriers are standard Borel spaces.
example {L : Language} [L.IsRelational] [∀ n, Countable (L.Relations n)] (φ : L.Sentenceω) :
    StandardBorelSpace (modelsOf φ : Set (RelationalConfiguration L ℕ)) := inferInstance

-- The coding space of graphs on `ℕ` has continuum many points.
example : Cardinal.mk (RelationalConfiguration Language.graph ℕ) = Cardinal.continuum :=
  mk_eq_continuum _ _ two_ne_zero Language.adj

-- Finite cylinders of configurations are measurable.
example {L : Language} {V : Type*} (s : Finset (Atom L V)) (f : Atom L V → Bool) :
    MeasurableSet
      (SymbolicDynamics.FullShift.cylinder s f : Set (RelationalConfiguration L V)) :=
  SymbolicDynamics.FullShift.measurableSet_cylinder s f

-- The finite cylinders form a basis of the topology of the coding space.
example {L : Language} {V : Type*} :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun p : Finset (Atom L V) × (Atom L V → Bool) =>
        (SymbolicDynamics.FullShift.cylinder p.1 p.2 : Set (RelationalConfiguration L V))) :=
  SymbolicDynamics.FullShift.isTopologicalBasis_cylinders
