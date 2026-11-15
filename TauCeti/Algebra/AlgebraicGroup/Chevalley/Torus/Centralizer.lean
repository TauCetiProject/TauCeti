/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# The torus centralizer inside the Chevalley Borel subgroup

Over an infinite field, the actual character-lattice torus of a Chevalley datum is
self-centralizing inside its Borel-type subgroup. Its centralizer in the positive subgroup
is trivial. These are local inputs to the torus-centralizer calculation in the whole
generated group. `ChevalleyDatum.mem_centralizer_range_torusPoints_iff` characterizes
centralizing elements of the whole point group by weight-space preservation, but containment
of that centralizer in the Borel subgroup or torus is not proved here.

Commuting with every torus point forces a matrix to preserve each weight space. Positive
points have identity diagonal blocks on these spaces, by
`ChevalleyDatum.coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq`, so a positive
point that also preserves every weight space equals `1`. This proves the trivial intersection
without root coordinates. The Borel calculation then uses its existing positive-times-torus
factorization and `Subgroup.inf_sup_assoc_of_le`. The diagonal-family criterion
`mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL` supplies the matrix argument.
The infinite-field hypothesis lets `exists_torusCharacter_ne` separate arbitrary distinct
weights without root coordinates. Some hypothesis on the field is needed: over the field
with two elements the torus has only one point.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28.
* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K] [Infinite K]

/-- Over an infinite field, centralizing the actual torus means preserving every weight space.
This allows arbitrary weight multiplicities and arbitrary character lattices. -/
theorem mem_centralizer_range_torusPoints_iff (g : D.points K) :
    g ∈ Subgroup.centralizer (Set.range (D.torusPoints K)) ↔
      ∀ i j, D.weight i ≠ D.weight j →
        ((g : Matrix.GeneralLinearGroup (Fin D.dim) K) : Matrix (Fin D.dim) (Fin D.dim) K)
          i j = 0 := by
  rw [mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL
      (fun s => (D.coe_torusPoints K s).trans
        (kostantTorusMatrix_apply D.lattice D.basis D.coordinateWeight s))]
  constructor
  · intro hg i j hij
    have hcoord : D.coordinateWeight i ≠ D.coordinateWeight j := by
      intro heq
      apply hij
      simpa only [D.weightLatticeEmbedding_coordinateWeight] using
        congrArg D.weightLatticeEmbedding heq
    exact hg i j (exists_torusCharacter_ne hcoord)
  · rintro hg i j ⟨s, hs⟩
    apply hg i j
    intro heq
    have hcoord : D.coordinateWeight i = D.coordinateWeight j :=
      D.weightLatticeEmbedding_injective (by simpa only
        [D.weightLatticeEmbedding_coordinateWeight] using heq)
    exact hs (congrArg (torusCharacter s) hcoord)

/-- No nonidentity positive point centralizes the actual torus over an infinite field. -/
@[simp]
theorem positivePoints_inf_centralizer_range_torusPoints :
    D.positivePoints K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      ⊥ := by
  apply eq_bot_iff.mpr
  rintro g ⟨hg, hc⟩
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : D.weight i = D.weight j
  · simpa using D.coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq K hg hij
  · have hne : i ≠ j := fun heq => hij (congrArg D.weight heq)
    simpa [Matrix.one_apply, hne] using
      (D.mem_centralizer_range_torusPoints_iff K g).mp hc i j hij

/-- Inside the Borel-type subgroup, the actual torus is its own centralizer over an infinite
field. This is not a statement about the centralizer in the whole point group. -/
@[simp]
theorem borelSubgroup_inf_centralizer_range_torusPoints :
    D.borelSubgroup K ⊓ Subgroup.centralizer (Set.range (D.torusPoints K)) =
      (D.torusPoints K).range := by
  have hT : (D.torusPoints K).range ≤
      Subgroup.centralizer (Set.range (D.torusPoints K)) := by
    simpa only [MonoidHom.coe_range] using Subgroup.le_centralizer (D.torusPoints K).range
  rw [D.borelSubgroup_def, inf_comm,
    ← Subgroup.inf_sup_assoc_of_le
      (Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (D.range_torusPoints_le_normalizer_positivePoints K))
      hT,
    inf_comm, D.positivePoints_inf_centralizer_range_torusPoints K, bot_sup_eq]

end TauCeti.DynkinType.ChevalleyDatum
