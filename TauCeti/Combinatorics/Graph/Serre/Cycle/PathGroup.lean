/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree
public import TauCeti.Combinatorics.Graph.Serre.Path.SpanningTree
public import TauCeti.Combinatorics.Quiver.PathWeight
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Cycle classes of closed paths

A path in a Serre graph has a chain on any chosen set `O` of darts: each dart it crosses
contributes its unit chain, and minus the unit chain of its reverse, as far as these lie in `O`.
When `O` is an orientation, exactly one of the two is present, the boundary of the chain of a
path is its endpoint minus its starting point, and a closed path gives a cycle. Backtrack
homotopic paths have the same chain, so this defines the cycle class homomorphism from the
reduced path group to the kernel of the incidence boundary, over any coefficient ring.
Extension of scalars carries the integral cycle class to the cycle class over any ring, whose
coordinates are the casts of the integral ones; over `ZMod 2` the binary cycle class is the
reduction of the integral one.

For a connected graph the integral cycle class identifies the abelianization of the path group
with the integral cycle lattice. The inverse uses a spanning tree `T`: a chain `c` goes to the
product of the tree loops through its darts, whose cycle class is `c` minus the tree paths to
the vertices of the boundary of `c`, hence `c` itself when `c` is a cycle. The cycle class of
the tree loop through a positive dart outside `T` is a fundamental cycle: among the positive
darts outside `T` it has coordinate one at that dart and zero elsewhere. So it is the
fundamental cycle of that dart in the basis of the cycle module given by `T`, over every
coefficient ring: the chain of the dart followed by the tree path from its target back to its
source. The isomorphism matches the classes of the tree loops with the integral fundamental
cycles.

## Main definitions

* `TauCeti.SerreGraph.dartChain`: the signed chain of a dart.
* `TauCeti.SerreGraph.Path.chain`: the chain of a path.
* `TauCeti.SerreGraph.PathGroup.cycleClass`: the cycle class of a reduced closed path.
* `TauCeti.SerreGraph.SpanningTree.abelianizationEquivCycle`: the abelianized path group is the
  integral cycle lattice.

## Main results

* `TauCeti.SerreGraph.Path.incidenceBoundary_chain`: the boundary of the chain of a path.
* `TauCeti.SerreGraph.Path.Homotopic.chain_eq`: homotopic paths have the same chain.
* `TauCeti.SerreGraph.SpanningTree.cycleChordCoordinates_cycleClass_loop`: tree loops have unit
  coordinates outside the tree.
* `TauCeti.SerreGraph.SpanningTree.cycleClass_loop`: the cycle class of a tree loop is the
  fundamental cycle of its dart.
* `TauCeti.SerreGraph.SpanningTree.coe_cycleBasis`: the fundamental cycle of a dart outside the
  tree is that dart followed by the tree path back to its source.
* `TauCeti.SerreGraph.PathGroup.cycleBaseChangeEquiv_tmul_cycleClass`: extension of scalars
  carries integral cycle classes to cycle classes.

## References

* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2 (tree loops), §2.2 (cellular
  boundaries of one-dimensional complexes) and §2.A, Theorem 2A.1 (the first homology group is
  the abelianized fundamental group).
-/

public section

open scoped TensorProduct

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E) (R : Type*) [Ring R]

/-- The signed chain of a dart on the chosen darts `O`: the unit chain of the dart, minus the
unit chain of its reverse, keeping the coordinates in `O`. For an orientation it is the unit
chain of a positive dart and minus the unit chain of the reverse of a negative dart. -/
noncomputable def dartChain (e : Γ.E) : O →₀ R :=
  (Finsupp.single e (1 : R) - Finsupp.single (Γ.rev e) 1).subtypeDomain (· ∈ O)

variable {Γ O}

/-- A coordinate of the chain of a dart: one at the dart itself, minus one at its reverse. -/
theorem dartChain_apply (e : Γ.E) (f : O) :
    Γ.dartChain O R e f = Finsupp.single e (1 : R) f.1 - Finsupp.single (Γ.rev e) (1 : R) f.1 := by
  simp [dartChain]

variable (O) in
/-- Reversing a dart negates its chain. -/
@[simp] theorem dartChain_rev (e : Γ.E) : Γ.dartChain O R (Γ.rev e) = -Γ.dartChain O R e := by
  ext f
  simp [dartChain_apply]

/-- Casting the coefficients of the integral chain of a dart gives its chain over any ring. -/
@[simp] theorem mapRange_intCast_dartChain (e : Γ.E) :
    (Γ.dartChain O ℤ e).mapRange (Int.cast : ℤ → R) Int.cast_zero = Γ.dartChain O R e := by
  classical
  ext f
  simp only [Finsupp.mapRange_apply, dartChain_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- Casting a coordinate of the integral chain of a dart gives that coordinate over any ring. -/
@[simp] theorem intCast_dartChain_apply (e : Γ.E) (f : O) :
    ((Γ.dartChain O ℤ e f : ℤ) : R) = Γ.dartChain O R e f := by
  rw [← mapRange_intCast_dartChain (R := R), Finsupp.mapRange_apply]

/-- The chain of a positive dart of an orientation is its unit chain. -/
theorem dartChain_of_mem (hO : Γ.IsOrientation O) {e : Γ.E} (he : e ∈ O) :
    Γ.dartChain O R e = Finsupp.single ⟨e, he⟩ 1 := by
  classical
  ext f
  have hf : Γ.rev e ≠ f.1 := fun h => hO.rev_notMem_of_mem Γ e he (h ▸ f.2)
  simp [dartChain_apply, Finsupp.single_apply, hf, Subtype.ext_iff]

/-- The chain of a negative dart of an orientation is minus the unit chain of its reverse. -/
theorem dartChain_of_rev_mem (hO : Γ.IsOrientation O) {e : Γ.E} (he : Γ.rev e ∈ O) :
    Γ.dartChain O R e = -Finsupp.single ⟨Γ.rev e, he⟩ 1 := by
  rw [← dartChain_of_mem R hO he, dartChain_rev, neg_neg]

/-- For an orientation, the chain of a dart has boundary its target minus its source. -/
@[simp] theorem incidenceBoundary_dartChain (hO : Γ.IsOrientation O) (e : Γ.E) :
    Γ.incidenceBoundary O R (Γ.dartChain O R e) =
      Finsupp.single (Γ.tgt e) 1 - Finsupp.single (Γ.src e) 1 := by
  by_cases he : e ∈ O
  · simp [dartChain_of_mem R hO he]
  · simp [dartChain_of_rev_mem R hO ((hO.mem_rev_iff Γ e).mpr he)]

variable (Γ O)

/-- The chain of a path: the sum of the signed chains of its darts. -/
noncomputable def Path.chain {a b : Γ.V} (p : Γ.Path a b) : O →₀ R :=
  p.addWeight fun {x y : Γ.V} (e : x ⟶ y) => Γ.dartChain O R e.1

@[simp] theorem Path.chain_nil (a : Γ.V) : Path.chain Γ O R (Quiver.Path.nil : Γ.Path a a) = 0 := by
  simp [Path.chain]

@[simp] theorem Path.chain_cons {a b c : Γ.V} (p : Γ.Path a b) (e : b ⟶ c) :
    Path.chain Γ O R (p.cons e) = Path.chain Γ O R p + Γ.dartChain O R e.1 := by
  simp [Path.chain]

@[simp] theorem Path.chain_toPath {a b : Γ.V} (e : a ⟶ b) :
    Path.chain Γ O R e.toPath = Γ.dartChain O R e.1 := by
  simp [Quiver.Hom.toPath]

@[simp] theorem Path.chain_comp {a b c : Γ.V} (p : Γ.Path a b) (q : Γ.Path b c) :
    Path.chain Γ O R (p.comp q) = Path.chain Γ O R p + Path.chain Γ O R q := by
  simp [Path.chain]

/-- Reversing a path negates its chain. -/
@[simp] theorem Path.chain_reverse {a b : Γ.V} (p : Γ.Path a b) :
    Path.chain Γ O R p.reverse = -Path.chain Γ O R p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath]
    simp [ih, Γ.reverse_val, add_comm]

/-- Casting the coefficients of the integral chain of a path gives its chain over any ring. -/
@[simp] theorem Path.mapRange_intCast_chain {a b : Γ.V} (p : Γ.Path a b) :
    (Path.chain Γ O ℤ p).mapRange (Int.cast : ℤ → R) Int.cast_zero = Path.chain Γ O R p := by
  induction p with
  | nil => simp
  | cons p e ih => simp [Finsupp.mapRange_add, ih]

/-- Casting a coordinate of the integral chain of a path gives that coordinate over any ring. -/
@[simp] theorem Path.intCast_chain_apply {a b : Γ.V} (p : Γ.Path a b) (f : O) :
    ((Path.chain Γ O ℤ p f : ℤ) : R) = Path.chain Γ O R p f := by
  rw [← Path.mapRange_intCast_chain Γ O R, Finsupp.mapRange_apply]

variable {Γ O} in
/-- Backtrack homotopic paths have the same chain. -/
theorem Path.Homotopic.chain_eq {a b : Γ.V} {p q : Γ.Path a b} (h : Path.Homotopic Γ p q) :
    Path.chain Γ O R p = Path.chain Γ O R q := by
  apply Multiplicative.ofAdd.injective
  simpa only [Path.chain, Quiver.Path.weight_ofAdd] using
    h.weight_eq Γ (fun e => Multiplicative.ofAdd (Γ.dartChain O R e)) (by simp)

/-- Reducing a path does not change its chain. -/
@[simp] theorem Path.chain_reduce {a b : Γ.V} (p : Γ.Path a b) :
    Path.chain Γ O R (Path.reduce Γ p) = Path.chain Γ O R p :=
  ((Path.homotopic_reduce Γ p).chain_eq R).symm

variable {Γ O}

/-- For an orientation, the chain of a path has boundary its endpoint minus its starting point. -/
@[simp] theorem Path.incidenceBoundary_chain (hO : Γ.IsOrientation O) {a b : Γ.V}
    (p : Γ.Path a b) :
    Γ.incidenceBoundary O R (Path.chain Γ O R p) = Finsupp.single b 1 - Finsupp.single a 1 := by
  induction p with
  | nil => simp
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    simp [ih, hO]

/-- The chain of a path vanishes at a chosen dart that the path crosses in neither direction. -/
theorem Path.chain_apply_eq_zero {a b : Γ.V} {p : Γ.Path a b} {f : O}
    (h : ∀ e ∈ Path.darts Γ p, e ≠ f.1 ∧ Γ.rev e ≠ f.1) : Path.chain Γ O R p f = 0 := by
  induction p with
  | nil => simp
  | cons p e ih =>
    have he := h e.1 (by simp)
    simp [ih fun d hd => h d (by simp [hd]), dartChain_apply, he.1, he.2]

namespace PathGroup

variable {v : Γ.V}

/-- The cycle class of a reduced closed path with respect to an orientation: its signed dart
count, an element of the kernel of the incidence boundary. It is a homomorphism to the additive
group of cycles. -/
noncomputable def cycleClass (hO : Γ.IsOrientation O) (R : Type*) [Ring R] :
    PathGroup Γ v →* Multiplicative (Γ.incidenceBoundary O R).ker where
  toFun g := .ofAdd ⟨Path.chain Γ O R g.toPath, by simp [hO]⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext : 1
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext : 1
    simp

/-- The cycle class of a reduced closed path is the chain of that path. -/
theorem coe_cycleClass (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    ((cycleClass hO R g).toAdd : O →₀ R) = Path.chain Γ O R g.toPath := (rfl)

/-- The cycle class of a closed path can be computed before reducing it. -/
@[simp] theorem coe_cycleClass_ofPath (hO : Γ.IsOrientation O) (p : Γ.Path v v) :
    ((cycleClass hO R (ofPath p)).toAdd : O →₀ R) = Path.chain Γ O R p := by
  simp [coe_cycleClass]

/-- Casting coefficients carries the integral cycle class to the cycle class over any ring. -/
theorem mapRange_intCast_coe_cycleClass (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    ((cycleClass hO ℤ g).toAdd : O →₀ ℤ).mapRange (Int.cast : ℤ → R) Int.cast_zero =
      (cycleClass hO R g).toAdd := by
  simp [coe_cycleClass]

/-- Casting a coordinate of the integral cycle class of a closed path gives that coordinate of its
cycle class over any ring. -/
@[simp] theorem intCast_coe_cycleClass_apply (hO : Γ.IsOrientation O) (g : PathGroup Γ v) (f : O) :
    (((cycleClass hO ℤ g).toAdd : O →₀ ℤ) f : R) = ((cycleClass hO R g).toAdd : O →₀ R) f := by
  rw [← mapRange_intCast_coe_cycleClass R hO, Finsupp.mapRange_apply]

/-- Extension of scalars sends `r ⊗` the integral cycle class of a closed path to `r` times its
cycle class over `R`. For `r = 1` and `R = ZMod 2`: the binary cycle class is the reduction of the
integral one. -/
@[simp] theorem cycleBaseChangeEquiv_tmul_cycleClass (hO : Γ.IsOrientation O) (r : R)
    (g : PathGroup Γ v) : Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] (cycleClass hO ℤ g).toAdd) =
      r • (cycleClass hO R g).toAdd := by
  rw [cycleBaseChangeEquiv_tmul_eq]
  exact congrArg (r • ·) (Subtype.ext (mapRange_intCast_coe_cycleClass R hO g))

/-- The cycle class of a positive loop dart is its unit chain. Together with `map_inv`, such a
loop and its reverse have opposite classes, nonzero over a nontrivial ring; this applies to every
petal of a rose. -/
theorem coe_cycleClass_ofPath_toPath (hO : Γ.IsOrientation O) (e : v ⟶ v) (he : e.1 ∈ O) :
    ((cycleClass hO R (ofPath e.toPath)).toAdd : O →₀ R) = Finsupp.single ⟨e.1, he⟩ 1 := by
  rw [coe_cycleClass_ofPath, Path.chain_toPath, dartChain_of_mem R hO he]

end PathGroup

namespace SpanningTree

variable (T : Γ.SpanningTree) (v : Γ.V)

/-- The chain of a tree path vanishes at every chosen dart outside the tree. -/
theorem chain_path_apply_of_notMem (a b : Γ.V) {f : O} (hf : f.1 ∉ T.darts) :
    Path.chain Γ O R (T.path a b) f = 0 :=
  Path.chain_apply_eq_zero R fun e he => by
    have he := T.mem_of_mem_darts_path he
    exact ⟨fun h => hf (h ▸ he), fun h => hf (h ▸ T.rev_mem e he)⟩

/-- Outside the tree, the cycle class of a tree loop has the coordinates of the chain of its
dart: the two tree paths contribute nothing. -/
theorem coe_cycleClass_loop_apply_of_notMem (hO : Γ.IsOrientation O) (e : Γ.E) {f : O}
    (hf : f.1 ∉ T.darts) :
    (PathGroup.cycleClass hO R (T.loop v e)).toAdd.1 f = Γ.dartChain O R e f := by
  simp [loop_def, T.chain_path_apply_of_notMem R _ _ hf]

/-- The cycle class of the tree loop through a positive dart outside the tree is a fundamental
cycle: its coordinates at the positive darts outside the tree form the unit vector of that
dart. -/
theorem cycleChordCoordinates_cycleClass_loop (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    Γ.cycleChordCoordinates O T.darts R (PathGroup.cycleClass hO R (T.loop v e.1)).toAdd =
      Finsupp.single e 1 := by
  classical
  ext f
  rw [cycleChordCoordinates_apply, T.coe_cycleClass_loop_apply_of_notMem R v hO _ f.2.2,
    dartChain_of_mem R hO e.2.1]
  simp [Finsupp.single_apply, Subtype.ext_iff]

/-- The cycle class of the tree loop through a positive dart outside the tree is the fundamental
cycle of that dart. -/
@[simp] theorem cycleClass_loop (hO : Γ.IsOrientation O) (e : ↥(O \ T.darts)) :
    PathGroup.cycleClass hO R (T.loop v e.1) = .ofAdd (T.cycleBasis hO R e) := by
  apply Multiplicative.toAdd.injective
  apply (T.cycleBasis hO R).repr.injective
  ext f
  simpa using DFunLike.congr_fun (T.cycleChordCoordinates_cycleClass_loop R v hO e) f

/-- The fundamental cycle of a positive dart outside the tree is the chain of the cycle that
crosses that dart and returns along the tree path from its target to its source. -/
theorem coe_cycleBasis (hO : Γ.IsOrientation O) (e : ↥(O \ T.darts)) :
    ((T.cycleBasis hO R e : (Γ.incidenceBoundary O R).ker) : O →₀ R) =
      Finsupp.single ⟨e.1, e.2.1⟩ 1 + Path.chain Γ O R (T.path (Γ.tgt e.1) (Γ.src e.1)) := by
  rw [← toAdd_ofAdd (T.cycleBasis hO R e), ← T.cycleClass_loop R (Γ.tgt e.1) hO e, loop_def,
    PathGroup.coe_cycleClass_ofPath]
  simp [dartChain_of_mem R hO e.2.1, add_comm]

/-- The class in the abelianized path group of the product of tree loops prescribed by an
integral chain. -/
private noncomputable def loopClass : (O →₀ ℤ) →+ Additive (Group.Abelianization (PathGroup Γ v)) :=
  Finsupp.liftAddHom fun e =>
    zmultiplesHom _ (Additive.ofMul (Group.Abelianization.of (T.loop v e.1)))

private theorem loopClass_single (e : O) (n : ℤ) :
    T.loopClass v (Finsupp.single e n) =
      n • Additive.ofMul (Group.Abelianization.of (T.loop v e.1)) := by
  simp [loopClass]

private theorem loopClass_dartChain (hO : Γ.IsOrientation O) (e : Γ.E) :
    T.loopClass v (Γ.dartChain O ℤ e) = Additive.ofMul (Group.Abelianization.of (T.loop v e)) := by
  by_cases he : e ∈ O
  · simp [dartChain_of_mem ℤ hO he, loopClass_single]
  · simp [dartChain_of_rev_mem ℤ hO ((hO.mem_rev_iff Γ e).mpr he), loopClass_single]

private theorem loopClass_chain (hO : Γ.IsOrientation O) {a b : Γ.V} (p : Γ.Path a b) :
    T.loopClass v (Path.chain Γ O ℤ p) =
      Additive.ofMul (Group.Abelianization.of (T.basedPath v p)) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, basedPath_comp, basedPath_toPath, Path.chain_comp,
      map_add, ih, Path.chain_toPath, T.loopClass_dartChain v hO]
    simp

/-- The cycle class on the abelianized path group. -/
private noncomputable def abCycleClass (hO : Γ.IsOrientation O) :
    Additive (Group.Abelianization (PathGroup Γ v)) →+ (Γ.incidenceBoundary O ℤ).ker :=
  (Group.Abelianization.lift (PathGroup.cycleClass hO ℤ)).toAdditiveLeft

private theorem abCycleClass_of (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    abCycleClass v hO (Additive.ofMul (Group.Abelianization.of g)) =
      (PathGroup.cycleClass hO ℤ g).toAdd := by
  simp [abCycleClass]

/-- The cycle class of the product of tree loops prescribed by a chain `c` is `c` corrected by
the tree paths to the vertices of its boundary. -/
private theorem coe_abCycleClass_loopClass (hO : Γ.IsOrientation O) (c : O →₀ ℤ) :
    (abCycleClass v hO (T.loopClass v c) : O →₀ ℤ) =
      c - Finsupp.linearCombination ℤ (fun a => Path.chain Γ O ℤ (T.path v a))
        (Γ.incidenceBoundary O ℤ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Submodule.coe_add, hc, hd]; abel
  | single e n =>
    have h := Path.chain_reverse Γ O ℤ (T.path v (Γ.tgt e.1))
    rw [T.reverse_path] at h
    simp [loopClass_single, abCycleClass_of, PathGroup.coe_cycleClass, loop_def,
      dartChain_of_mem ℤ hO e.2, h, sub_eq_add_neg]
    abel

/-- The abelianization of the path group of a connected graph is its integral cycle lattice:
the cycle class of closed paths induces an isomorphism from the abelianized path group onto the
kernel of the integral incidence boundary of an orientation. The spanning tree enters only
through the inverse, which sends a cycle to the product of the tree loops through its darts. -/
noncomputable def abelianizationEquivCycle (hO : Γ.IsOrientation O) :
    Additive (Group.Abelianization (PathGroup Γ v)) ≃+ (Γ.incidenceBoundary O ℤ).ker :=
  AddMonoidHom.toAddEquiv (abCycleClass v hO)
    ((T.loopClass v).comp (Γ.incidenceBoundary O ℤ).ker.subtype.toAddMonoidHom)
    (by
      ext g
      induction g using PathGroup.induction_on with
      | h p => simp [abCycleClass_of, T.loopClass_chain v hO])
    (by
      ext c : 2
      simp [T.coe_abCycleClass_loopClass v hO, LinearMap.mem_ker.mp c.2])

/-- The isomorphism sends the class of a closed path to its cycle class; in particular it does
not depend on the spanning tree. -/
@[simp] theorem abelianizationEquivCycle_of (hO : Γ.IsOrientation O) (g : PathGroup Γ v) :
    T.abelianizationEquivCycle v hO (Additive.ofMul (Group.Abelianization.of g)) =
      (PathGroup.cycleClass hO ℤ g).toAdd :=
  abCycleClass_of v hO g

/-- The inverse isomorphism sends the cycle class of a closed path back to its class. -/
@[simp] theorem abelianizationEquivCycle_symm_cycleClass (hO : Γ.IsOrientation O)
    (g : PathGroup Γ v) :
    (T.abelianizationEquivCycle v hO).symm (PathGroup.cycleClass hO ℤ g).toAdd =
      Additive.ofMul (Group.Abelianization.of g) := by
  rw [← T.abelianizationEquivCycle_of v hO, AddEquiv.symm_apply_apply]

/-- The inverse isomorphism sends the integral fundamental cycle of a positive dart outside the
tree to the class of its tree loop. -/
@[simp] theorem abelianizationEquivCycle_symm_cycleBasis (hO : Γ.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    (T.abelianizationEquivCycle v hO).symm (T.cycleBasis hO ℤ e) =
      Additive.ofMul (Group.Abelianization.of (T.loop v e.1)) := by
  simpa using T.abelianizationEquivCycle_symm_cycleClass v hO (T.loop v e.1)

end SpanningTree

end TauCeti.SerreGraph
