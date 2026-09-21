/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import TauCeti.Combinatorics.RibbonGraph.Basic
import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# The permutation triple of a bipartite ribbon graph

Numbering the edges of a finite bipartite ribbon graph by `Fin n` turns its black and white
rotations into two permutations of `Fin n`.  Their product determines the third component of a
permutation triple.  The third component is the transported face permutation, so the construction
retains all three kinds of cells of the graph.

Changing the edge numbering simultaneously conjugates the three components.  Consequently the
isomorphism class of the resulting triple is independent of the numbering.  Graph isomorphisms
also give equivalent triples, and connected ribbon graphs give connected triples.  These facts
are the reverse half of the correspondence between permutation triples and dessins.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

open Equiv

public section

namespace TauCeti

namespace BipartiteRibbonGraph

variable {n : ℕ} (Γ : BipartiteRibbonGraph)

/-- The permutation triple obtained by numbering the edges of a bipartite ribbon graph.  Its first
two components are the transported black and white rotations. -/
def toPermutationTriple (ν : Γ.E ≃ Fin n) : PermutationTriple n :=
  PermutationTriple.ofTwo (ν.permCongr Γ.rotB) (ν.permCongr Γ.rotW)

/-- The first component of the triple is the black rotation in the chosen numbering. -/
@[simp]
theorem toPermutationTriple_σ0 (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).σ0 = ν.permCongr Γ.rotB := by
  rw [toPermutationTriple, PermutationTriple.ofTwo_σ0]

/-- The second component of the triple is the white rotation in the chosen numbering. -/
@[simp]
theorem toPermutationTriple_σ1 (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).σ1 = ν.permCongr Γ.rotW := by
  rw [toPermutationTriple, PermutationTriple.ofTwo_σ1]

/-- The third component of the triple is the face permutation in the chosen numbering. -/
@[simp]
theorem toPermutationTriple_σinf (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).σinf = ν.permCongr Γ.facePerm := by
  rw [toPermutationTriple, PermutationTriple.ofTwo_σinf,
    BipartiteRibbonGraph.facePerm_def]
  -- `permCongr` and `permCongrHom` are definitionally the same map, but the homomorphism
  -- spelling is needed for the generic `map_mul` and `map_inv` lemmas.
  change (ν.permCongrHom Γ.rotW * ν.permCongrHom Γ.rotB)⁻¹ =
    ν.permCongrHom ((Γ.rotW * Γ.rotB)⁻¹)
  rw [map_inv, map_mul]

/-- The monodromy group of the triple is the transported rotation group of the graph. -/
@[simp]
theorem monodromyGroup_toPermutationTriple (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).monodromyGroup = Γ.rotationGroup.map ν.permCongrHom := by
  rw [← PermutationTriple.closure_pair_eq_monodromyGroup,
    ← BipartiteRibbonGraph.closure_pair_eq_rotationGroup, MonoidHom.map_closure]
  simp only [toPermutationTriple_σ0, toPermutationTriple_σ1, Set.image_pair]
  -- The mapped subgroup uses `permCongrHom`, whereas the component lemmas expose the
  -- definitionally equal `permCongr`; putting both sides in one spelling closes the goal.
  change Subgroup.closure {ν.permCongr Γ.rotB, ν.permCongr Γ.rotW} =
    Subgroup.closure {ν.permCongr Γ.rotB, ν.permCongr Γ.rotW}
  rfl

/-- The rotation group of the graph is isomorphic to the monodromy group of its triple. -/
noncomputable def rotationGroupEquivMonodromyGroup (ν : Γ.E ≃ Fin n) :
    Γ.rotationGroup ≃* (Γ.toPermutationTriple ν).monodromyGroup :=
  (Subgroup.equivMapOfInjective Γ.rotationGroup ν.permCongrHom ν.permCongrHom.injective).trans
    (MulEquiv.subgroupCongr (Γ.monodromyGroup_toPermutationTriple ν).symm)

/-- The rotation-group isomorphism acts by conjugating an edge permutation through the chosen
numbering. -/
@[simp]
theorem coe_rotationGroupEquivMonodromyGroup (ν : Γ.E ≃ Fin n) (g : Γ.rotationGroup) :
    ((Γ.rotationGroupEquivMonodromyGroup ν g :
      (Γ.toPermutationTriple ν).monodromyGroup) : Perm (Fin n)) =
      ν.permCongr (g : Perm Γ.E) := (rfl)

/-- The edge numbering intertwines the rotation action with the monodromy action. -/
private def edgeEquivMonodromyGroup (ν : Γ.E ≃ Fin n) :
    Γ.E →ₑ[Γ.rotationGroupEquivMonodromyGroup ν] Fin n where
  toFun := ν
  map_smul' g e := by
    -- The two subgroup actions hide their ambient permutations behind subtype coercions;
    -- expose those permutations before applying the characteristic lemma above.
    change ν ((g : Perm Γ.E) e) =
      ((Γ.rotationGroupEquivMonodromyGroup ν g :
        (Γ.toPermutationTriple ν).monodromyGroup) : Perm (Fin n)) (ν e)
    rw [coe_rotationGroupEquivMonodromyGroup, Equiv.permCongr_apply, ν.symm_apply_apply]

/-- The triple obtained from a ribbon graph is connected exactly when the graph is connected. -/
theorem isConnected_toPermutationTriple (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).IsConnected ↔ Γ.IsConnected := by
  rw [PermutationTriple.isConnected_iff, BipartiteRibbonGraph.isConnected_def]
  have hnonempty : n ≠ 0 ↔ Nonempty Γ.E := by
    rw [← Nat.pos_iff_ne_zero, Fin.pos_iff_nonempty]
    exact ν.nonempty_congr.symm
  exact and_congr hnonempty
    (MulAction.isPretransitive_congr (f := Γ.edgeEquivMonodromyGroup ν)
      (Γ.rotationGroupEquivMonodromyGroup ν).surjective ν.bijective).symm

/-- Postcomposing an edge numbering by a relabeling simultaneously relabels the resulting
permutation triple. -/
@[simp]
theorem toPermutationTriple_trans (ν : Γ.E ≃ Fin n) (τ : Perm (Fin n)) :
    Γ.toPermutationTriple (ν.trans τ) = τ • Γ.toPermutationTriple ν := by
  apply PermutationTriple.ext_of_two
  · ext i
    simp [Equiv.permCongr_apply]
  · ext i
    simp [Equiv.permCongr_apply]

/-- Triples obtained from two numberings of the same graph differ by simultaneous relabeling. -/
theorem equivalent_toPermutationTriple (ν μ : Γ.E ≃ Fin n) :
    PermutationTriple.Equivalent (Γ.toPermutationTriple ν) (Γ.toPermutationTriple μ) := by
  rw [PermutationTriple.equivalent_iff_exists_smul_eq]
  refine ⟨ν.symm.trans μ, ?_⟩
  rw [← toPermutationTriple_trans]
  congr
  ext e
  simp

variable {Γ : BipartiteRibbonGraph} {Δ : BipartiteRibbonGraph}

/-- Numbering the target of a ribbon-graph isomorphism gives the same triple as pulling that
numbering back to the source. -/
@[simp]
theorem toPermutationTriple_iso (f : Γ.Iso Δ) (ν : Δ.E ≃ Fin n) :
    Γ.toPermutationTriple (f.edge.trans ν) = Δ.toPermutationTriple ν := by
  apply PermutationTriple.ext_of_two
  · rw [toPermutationTriple_σ0, toPermutationTriple_σ0]
    ext i
    simp only [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply]
    rw [f.map_rotB, f.edge.apply_symm_apply]
  · rw [toPermutationTriple_σ1, toPermutationTriple_σ1]
    ext i
    simp only [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply]
    rw [f.map_rotW, f.edge.apply_symm_apply]

/-- Isomorphic ribbon graphs give equivalent triples under arbitrary edge numberings. -/
theorem equivalent_toPermutationTriple_of_iso (f : Γ.Iso Δ) (ν : Γ.E ≃ Fin n)
    (μ : Δ.E ≃ Fin n) :
    PermutationTriple.Equivalent (Γ.toPermutationTriple ν) (Δ.toPermutationTriple μ) := by
  rw [← toPermutationTriple_iso f μ]
  exact Γ.equivalent_toPermutationTriple ν (f.edge.trans μ)

end BipartiteRibbonGraph

end TauCeti
