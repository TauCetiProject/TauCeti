/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
public import TauCeti.Combinatorics.Network.Ear.StronglyConnected

/-!
# Directed ear decompositions of digraphs

This file views a digraph `D : Digraph V` as a `Unit`-capacitated directed network `D.toNetwork`
whose arrow family is `D.AdjHom`, and specializes the directed ear characterization of strong
connectivity to digraphs.

Loops in `D` are retained as arrows in `D.AdjHom v v` (closed ears of length one), and every
`D.AdjHom v w = PLift (D.Adj v w)` is a subsingleton and therefore automatically `Finite`, so the
finite-network ear characterization requires only `[Finite V]` (no decidability assumptions on `V`
or `D.Adj`).

## Main definitions

* `Digraph.toNetwork`: `D` viewed as a `Unit`-capacitated `Network Unit V` with arrow family
  `D.AdjHom`.

## Main results

* `Digraph.forall_reflTransGen_iff_nonempty_earDecomposition`: a finite digraph on a nonempty
  vertex type is strongly connected if and only if `D.toNetwork` admits a directed ear
  decomposition of `⊤`.
* `Digraph.forall_reflTransGen_iff_exists_earDecomposition_initialVertex`: strong connectivity is
  equivalent to an ear decomposition starting at any prescribed vertex `v₀`.
* `Digraph.forall_reflTransGen_iff_exists_cycle_earDecomposition`: on a finite nontrivial vertex
  type, strong connectivity is equivalent to an ear decomposition whose `stage 1` is a directed
  cycle of length at least `2`.
* `Digraph.earDecomposition_length_eq_zero_iff`: an ear decomposition of `⊤` has zero ears exactly
  when `V` is a subsingleton and `D = ⊥`.
* `Digraph.existsUnique_ear_of_adj`: every directed edge (including any loop) belongs to a unique
  ear of any ear decomposition of `⊤`.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Section 5.3.
-/

public section

open TauCeti Relation

universe u

namespace Digraph

variable {V : Type u} (D : Digraph V)

/-- A digraph viewed as a `Unit`-capacitated directed network whose arrow family is `D.AdjHom`.

This definition is exposed because its dependent arrow family must reduce to `D.AdjHom` when walks,
cycles, and ears on `D.toNetwork` are elaborated. -/
@[expose]
def toNetwork : Network Unit V where
  Hom := D.AdjHom
  lower := fun {_ _} _ ↦ ()
  upper := fun {_ _} _ ↦ ()
  lower_le_upper := fun _ ↦ le_rfl

@[simp]
theorem toNetwork_hom (v w : V) : D.toNetwork.Hom v w = D.AdjHom v w :=
  rfl

@[simp]
theorem toNetwork_lower {v w : V} (e : D.AdjHom v w) : D.toNetwork.lower e = () :=
  rfl

@[simp]
theorem toNetwork_upper {v w : V} (e : D.AdjHom v w) : D.toNetwork.upper e = () :=
  rfl

/-- Between any two vertices, `D.toNetwork` has at most one arrow. -/
instance (v w : V) : Subsingleton (D.toNetwork.Hom v w) :=
  inferInstanceAs (Subsingleton (D.AdjHom v w))

/-- `D.toNetwork` is strongly connected exactly when every vertex reaches every other vertex along
`D.Adj`. -/
@[simp]
theorem toNetwork_isStronglyConnected_iff :
    D.toNetwork.IsStronglyConnected ↔ ∀ v w, ReflTransGen D.Adj v w :=
  D.toNetwork.isStronglyConnected_iff.trans D.isStronglyConnected_iff

variable {D}

/-- In a strongly connected digraph (without finiteness assumptions), every nonempty proper
subnetwork of `D.toNetwork` admits an open or closed directed ear. -/
theorem nonempty_ear {S : D.toNetwork.Subnetwork} (hD : ∀ v w, ReflTransGen D.Adj v w)
    (hS_ne : S.vertexSet.Nonempty) (hS_top : S ≠ ⊤) : Nonempty (D.toNetwork.Ear S) :=
  (D.toNetwork_isStronglyConnected_iff.2 hD).nonempty_ear hS_ne hS_top

/-- In a finite strongly connected digraph, every partial ear decomposition extends to a full ear
decomposition of `⊤` preserving its initial vertex, prefix stages, ear kinds, and ear
subnetworks. -/
theorem exists_earDecomposition_top_of_earDecomposition [Finite V]
    (hD : ∀ v w, ReflTransGen D.Adj v w) {S : D.toNetwork.Subnetwork}
    (E : D.toNetwork.EarDecomposition S) :
    ∃ (E' : D.toNetwork.EarDecomposition ⊤) (h : E.length ≤ E'.length),
      E'.initialVertex = E.initialVertex ∧
      (∀ j : Fin (E.length + 1), E'.stage (Fin.castLE (Nat.succ_le_succ h) j) = E.stage j) ∧
      (∀ i : Fin E.length, E'.kindAt (Fin.castLE h i) = E.kindAt i) ∧
      (∀ i : Fin E.length,
        (E'.ear (Fin.castLE h i)).toSubnetwork = (E.ear i).toSubnetwork) :=
  (D.toNetwork_isStronglyConnected_iff.2 hD).exists_earDecomposition_top_of_earDecomposition E

/-- A finite digraph is strongly connected if and only if `D.toNetwork` admits a directed ear
decomposition of `⊤` starting at a prescribed vertex `v₀`. -/
theorem forall_reflTransGen_iff_exists_earDecomposition_initialVertex [Finite V] (v₀ : V) :
    (∀ v w, ReflTransGen D.Adj v w) ↔
      ∃ E : D.toNetwork.EarDecomposition ⊤, E.initialVertex = v₀ := by
  rw [← D.toNetwork_isStronglyConnected_iff,
    D.toNetwork.isStronglyConnected_iff_exists_earDecomposition_initialVertex v₀]

/-- **Directed ear characterization of strongly connected digraphs.** A finite digraph on a
nonempty vertex type is strongly connected if and only if `D.toNetwork` admits a directed ear
decomposition of `⊤`. -/
theorem forall_reflTransGen_iff_nonempty_earDecomposition [Nonempty V] [Finite V] :
    (∀ v w, ReflTransGen D.Adj v w) ↔ Nonempty (D.toNetwork.EarDecomposition ⊤) := by
  rw [← D.toNetwork_isStronglyConnected_iff,
    D.toNetwork.isStronglyConnected_iff_nonempty_earDecomposition]

/-- On any finite digraph, `D.toNetwork` admits a directed ear decomposition of `⊤` if and only if
`V` is nonempty and every vertex reaches every other vertex along `D.Adj`. -/
theorem nonempty_earDecomposition_top_iff [Finite V] :
    Nonempty (D.toNetwork.EarDecomposition ⊤) ↔
      Nonempty V ∧ ∀ v w, ReflTransGen D.Adj v w := by
  rw [D.toNetwork.nonempty_earDecomposition_top_iff, D.toNetwork_isStronglyConnected_iff]

/-- An ear decomposition of `⊤` in `D.toNetwork` has zero ears if and only if `V` has at most one
vertex and `D` has no directed edges (not even a loop). -/
theorem earDecomposition_length_eq_zero_iff (E : D.toNetwork.EarDecomposition ⊤) :
    E.length = 0 ↔ Subsingleton V ∧ D = ⊥ := by
  rw [E.length_eq_zero_iff]
  refine and_congr_right' ⟨fun hE ↦ ?_, fun hbot ↦ ⟨fun ⟨x, y, ⟨hadj⟩⟩ ↦ ?_⟩⟩
  · ext x y
    exact ⟨fun hadj ↦ hE.false ⟨x, y, ⟨hadj⟩⟩, False.elim⟩
  · subst hbot
    exact hadj

/-- In a finite strongly connected digraph, every directed cycle along `D.AdjHom` appears as
`stage 1` of a directed ear decomposition of `⊤`. -/
theorem exists_earDecomposition_of_isCycle [Finite V] (hD : ∀ v w, ReflTransGen D.Adj v w)
    {v₀ : V} {c : ArrowWalk D.AdjHom v₀ v₀} (hc : c.IsCycle) :
    ∃ (E : D.toNetwork.EarDecomposition ⊤) (h : 0 < E.length),
      E.initialVertex = v₀ ∧ E.kindAt ⟨0, h⟩ = .closed ∧
        E.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork :=
  (D.toNetwork_isStronglyConnected_iff.2 hD).exists_earDecomposition_of_isCycle hc

/-- **Cycle-starting directed ear characterization for digraphs.** On a finite nontrivial vertex
type, `D` is strongly connected if and only if some directed cycle of length at least `2` along
`D.AdjHom` forms `stage 1` of a directed ear decomposition of `⊤` in `D.toNetwork`. -/
theorem forall_reflTransGen_iff_exists_cycle_earDecomposition [Nontrivial V] [Finite V] :
    (∀ v w, ReflTransGen D.Adj v w) ↔
      ∃ (v₀ : V) (c : ArrowWalk D.AdjHom v₀ v₀) (E : D.toNetwork.EarDecomposition ⊤)
        (h : 0 < E.length),
        c.IsCycle ∧ 2 ≤ c.length ∧ E.initialVertex = v₀ ∧
          E.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  rw [← D.toNetwork_isStronglyConnected_iff,
    D.toNetwork.isStronglyConnected_iff_exists_cycle_earDecomposition]
  exact Iff.rfl

/-- Every directed edge of `D` (including any loop) belongs to the arrow set of a unique ear of any
ear decomposition of `⊤` in `D.toNetwork`. -/
theorem existsUnique_ear_of_adj (E : D.toNetwork.EarDecomposition ⊤) {v w : V} (h : D.Adj v w) :
    ∃! i : Fin E.length, (⟨v, w, ⟨h⟩⟩ : Σ x y, D.AdjHom x y) ∈ (E.ear i).toSubnetwork.arrowSet :=
  E.existsUnique_ear ⟨v, w, ⟨h⟩⟩

end Digraph
