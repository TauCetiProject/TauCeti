/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import TauCeti.Topology.Algebra.Group.Perm
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Perm
public import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift
public import TauCeti.Dynamics.SymbolicDynamics.Basic

/-!
# Topology of relational configurations

The product topology on relational configurations is compact Hausdorff, and relabelling by a
permutation of the carrier is continuous. Restriction along a vertex map is continuous, and
jointly continuous in the vertex map when the target carrier is discrete. Specifying an atom's
truth value gives a clopen, measurable cylinder, and so does specifying the truth values of a
finite set of atoms (`SymbolicDynamics.FullShift.cylinder`, clopen by
`SymbolicDynamics.FullShift.isOpen_cylinder` and `SymbolicDynamics.FullShift.isClosed_cylinder`,
measurable by `SymbolicDynamics.FullShift.measurableSet_cylinder`); these finite cylinders form a
basis of the topology (`SymbolicDynamics.FullShift.isTopologicalBasis_cylinder`). On
countable carriers in countable relational vocabularies the topology is Polish and its Borel
σ-algebra is the existing product σ-algebra. There are at most continuum many configurations, and
exactly continuum many on a countably infinite carrier when some relation symbol has positive
arity (`TauCeti.RelationalConfiguration.mk_eq_continuum`). The same construction handles finite
and empty carriers.

For a discrete carrier, the *logic action* of its permutation group, with the topology of
pointwise convergence, is jointly continuous, for every language, so stabilizers of
configurations are closed subgroups (`TauCeti.isClosed_stabilizer`). On a countable discrete
carrier in a countable relational vocabulary both spaces are second countable and carry their
Borel σ-algebras, so the action is jointly measurable (Mathlib's instance
`ContinuousSMul.measurableSMul₂`): the coding space on `ℕ` is a Borel `S∞`-space, whose orbit
relation is isomorphism (`TauCeti.RelationalConfiguration.isoSetoid_eq_orbitRel`).

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

/-- Convergence of configurations is convergence of every atom coordinate. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {f : ι → RelationalConfiguration L V}
    {c : RelationalConfiguration L V} :
    Filter.Tendsto f l (nhds c) ↔
      ∀ a, Filter.Tendsto (fun i => (f i).eval a) l (nhds (c.eval a)) := by
  simp only [eval_def]
  exact tendsto_pi_nhds

/-- Building a configuration from its atom values is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk : (Atom L V → Bool) → RelationalConfiguration L V) :=
  continuous_iff.2 fun a => by simpa using (continuous_apply a (A := fun _ => Bool))

/-- Restricting along a vertex map is continuous. -/
@[fun_prop]
theorem continuous_restrict {W : Type*} (f : V → W) :
    Continuous (restrict (L := L) f) :=
  continuous_iff.2 fun a => by simpa using continuous_eval (a.map f)

/-- Restriction is jointly continuous in the vertex map and the configuration when the target
carrier is discrete. -/
theorem continuous_uncurry_restrict {W : Type*} [TopologicalSpace W] [DiscreteTopology W] :
    Continuous (Function.uncurry (restrict (L := L) (V := V) (W := W))) := by
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with
  | h R x =>
    simp only [Function.uncurry_def, eval_restrict, Atom.map_atom]
    -- Reading the atom `R(y)` is continuous in the configuration and, trivially, in the tuple
    -- `y`, which ranges over a discrete space.
    have h : Continuous fun q : RelationalConfiguration L W × (Fin _ → W) =>
        q.1.eval (atom R q.2) :=
      continuous_prod_of_discrete_right.2 fun y => continuous_eval (atom R y)
    exact h.comp (continuous_snd.prodMk (continuous_pi fun i => (continuous_apply (x i)).comp
      continuous_fst))

/-- Each relabelling by a permutation of the carrier is continuous. -/
instance : ContinuousConstSMul (Equiv.Perm V) (RelationalConfiguration L V) :=
  ⟨fun _ => continuous_restrict _⟩

/-- **The logic action is jointly continuous**, for every language: relabelling by `σ` is
restriction along `σ⁻¹`, which is jointly continuous in the vertex map and the configuration,
and `σ⁻¹` depends continuously on `σ`. On `ℕ` this makes the coding space an `S∞`-space. -/
instance instContinuousSMulPerm [TopologicalSpace V] [DiscreteTopology V] :
    ContinuousSMul (Equiv.Perm V) (RelationalConfiguration L V) where
  continuous_smul := continuous_uncurry_restrict.comp
    (((continuous_pi Equiv.Perm.continuous_inv_apply).comp continuous_fst).prodMk continuous_snd)

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

/-- **There are continuum many configurations** on a countably infinite carrier in a language
with countably many relation symbols of each arity, one of them of positive arity. -/
theorem mk_eq_continuum (L : FirstOrder.Language) (V : Type*)
    [∀ n, Countable (L.Relations n)] [Countable V] [Infinite V] {n : ℕ} (hn : n ≠ 0)
    (R : L.Relations n) :
    Cardinal.mk (RelationalConfiguration L V) = Cardinal.continuum := by
  have := Atom.infinite_of_relations (V := V) hn R
  rw [RelationalConfiguration, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.lift_ofNat,
    Cardinal.mk_eq_aleph0 (Atom L V), Cardinal.lift_aleph0, Cardinal.two_power_aleph0]

end TauCeti.RelationalConfiguration
