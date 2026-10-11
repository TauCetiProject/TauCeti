/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.MonodromyTriple
public import TauCeti.Combinatorics.PermutationTriple.IsoClass
import all TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic

/-!
# Associated covers of connected permutation triples

A connected permutation triple determines a transitive action of the fundamental group of the
thrice-punctured sphere. Its associated cover has the finite action set as its numbered fiber, and
its monodromy triple recovers the given triple. This is the finite action-cover construction used
to pass from combinatorial data to covering spaces.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

/-- The associated covering space of a connected permutation triple, built from its fundamental
group action on `Fin n`. -/
@[expose] def ConnectedTriple.actionCover (t : ConnectedTriple n) :
    CoveringSpace (TopCat.of ThricePuncturedSphere) := by
  let ρ := Classical.choose (permutationTriple_surjective t.1)
  letI : MulAction (FundamentalGroup ThricePuncturedSphere basePt) (Fin n) :=
    MulAction.compHom _ ρ.rangeRestrict
  exact UniversalCover.actionCoveringSpace basePt (Fin n)

/-- The natural numbering of the fiber of the associated cover by the action set `Fin n`. -/
def ConnectedTriple.actionCoverNumbering (t : ConnectedTriple n) :
    ⇑t.actionCover.proj ⁻¹' {basePt} ≃ Fin n := by
  let ρ := Classical.choose (permutationTriple_surjective t.1)
  letI : MulAction (FundamentalGroup ThricePuncturedSphere basePt) (Fin n) :=
    MulAction.compHom _ ρ.rangeRestrict
  exact UniversalCover.actionCoveringSpaceFiberEquiv basePt (Fin n)

/-- The numbered monodromy triple of the associated cover is the original connected triple. -/
theorem ConnectedTriple.monodromyTriple_actionCover (t : ConnectedTriple n) :
    t.actionCover.isCoveringMap_proj.monodromyTriple t.actionCoverNumbering = t.1 := by
  let ρ := Classical.choose (permutationTriple_surjective t.1)
  let _ := MulAction.compHom (Fin n) ρ.rangeRestrict
  let _ := t.actionCover.isCoveringMap_proj.fundamentalGroupMulAction basePt
  have hρ : t.actionCoverNumbering.permCongrHom.toMonoidHom.comp
      (t.actionCover.isCoveringMap_proj.monodromyPerm basePt) = ρ := by
    rw [← t.actionCover.isCoveringMap_proj.toPermHom_eq_monodromyPerm,
      ← Equiv.permutationRepresentation.eq_def]
    apply Equiv.permutationRepresentation_eq_of_map_smul t.actionCoverNumbering (ρ := ρ)
    intro γ i
    exact UniversalCover.actionCoveringSpaceFiberEquiv_apply_monodromy basePt (Fin n) γ i
  rw [IsCoveringMap.monodromyTriple_def, hρ,
    ← Classical.choose_spec (permutationTriple_surjective t.1)]

end TauCeti
