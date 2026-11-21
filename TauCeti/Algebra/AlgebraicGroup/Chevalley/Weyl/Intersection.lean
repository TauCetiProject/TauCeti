/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient

/-!
# Intersections of the Borel and positive subgroups with the Weyl subgroup

For a Chevalley datum `D` over an arbitrary commutative ring `A` (including nonreduced rings,
finite fields, `𝔽₂`, and the zero ring), the intersection of `D.borelSubgroup A` with
`D.weylSubgroup A` is the actual weight-lattice torus `(D.torusPoints A).range`, and the positive
subgroup `D.positivePoints A` meets `D.weylSubgroup A` trivially.

When `A` is nontrivial, passing to a residue field `A ⧸ M` sends any `g ∈ B(A) ∩ N(A)` into
`B(A ⧸ M) ∩ N(A ⧸ M)`, where `D.weylProjection (A ⧸ M)` vanishes by
`D.weylProjection_eq_one_of_mem_borelSubgroup`. Base-change invariance of the canonical Weyl
quotient isomorphism (`D.weylQuotientMulEquiv_map`) then forces `g` to represent the identity in
`N(A) ⧸ T(A)`, so `g ∈ T(A)`. Combining `B(A) ∩ N(A) = T(A)` with `U(A) ∩ T(A) = ⊥` from
`Chevalley.Borel` immediately gives `U(A) ∩ N(A) = ⊥`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints`:
  `D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.positivePoints_inf_weylSubgroup_eq_bot`:
  `D.positivePoints A ⊓ D.weylSubgroup A = ⊥` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_subgroupOf_weylSubgroup`:
  `(D.borelSubgroup A).subgroupOf (D.weylSubgroup A) =`
  `((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

/-- Over any commutative ring, the intersection of the Borel subgroup with the Weyl subgroup is
the actual weight-lattice torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range := by
  rcases subsingleton_or_nontrivial A with hsub | hnontriv
  · apply le_antisymm
    · rintro g -
      exact ⟨1, Subtype.ext (Subsingleton.elim _ _)⟩
    · exact le_inf (D.range_torusPoints_le_borelSubgroup A) (D.range_torusPoints_le_weylSubgroup A)
  · apply le_antisymm
    · rintro g ⟨hgB, hgW⟩
      obtain ⟨M, hM⟩ := Ideal.exists_maximal A
      let _ : M.IsMaximal := hM
      let _ : Field (A ⧸ M) := Ideal.Quotient.field M
      let ψ := Ideal.Quotient.mk M
      have hproj : D.weylProjection (A ⧸ M) (D.weylSubgroupMap A ψ ⟨g, hgW⟩) = 1 :=
        D.weylProjection_eq_one_of_mem_borelSubgroup (A ⧸ M)
          (by
            rw [D.coe_weylSubgroupMap]
            exact D.map_borelSubgroup_le A ψ ⟨g, hgB, rfl⟩)
      have hq : D.weylQuotientMulEquiv A (QuotientGroup.mk ⟨g, hgW⟩) = 1 := by
        rw [← D.weylQuotientMulEquiv_map ψ ⟨g, hgW⟩, D.weylQuotientMulEquiv_mk]
        exact hproj
      have hmk : (QuotientGroup.mk ⟨g, hgW⟩ :
          D.weylSubgroup A ⧸ ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)) = 1 :=
        (D.weylQuotientMulEquiv A).injective (hq.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff (⟨g, hgW⟩ : D.weylSubgroup A)).mp hmk
    · exact le_inf (D.range_torusPoints_le_borelSubgroup A) (D.range_torusPoints_le_weylSubgroup A)

/-- Over any commutative ring, the intersection of the Weyl subgroup with the Borel subgroup is
the actual weight-lattice torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints :
    D.weylSubgroup A ⊓ D.borelSubgroup A = (D.torusPoints A).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A]

/-- Over any commutative ring, the positive subgroup meets the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints A ⊓ D.weylSubgroup A = ⊥ := by
  rw [eq_bot_iff, ← D.positivePoints_inf_range_torusPoints_eq_bot A,
    ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A]
  exact le_inf inf_le_left
    (le_inf (inf_le_left.trans (D.positivePoints_le_borelSubgroup A)) inf_le_right)

/-- Over any commutative ring, the Weyl subgroup meets the positive subgroup trivially. -/
@[simp]
theorem weylSubgroup_inf_positivePoints_eq_bot :
    D.weylSubgroup A ⊓ D.positivePoints A = ⊥ := by
  rw [inf_comm, D.positivePoints_inf_weylSubgroup_eq_bot A]

/-- Read inside `D.weylSubgroup A`, the Borel subgroup cuts out the actual weight-lattice torus,
over every commutative ring. -/
@[simp]
theorem borelSubgroup_subgroupOf_weylSubgroup :
    (D.borelSubgroup A).subgroupOf (D.weylSubgroup A) =
      ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A) := by
  rw [Subgroup.subgroupOf_inj, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints,
    inf_eq_left.mpr (D.range_torusPoints_le_weylSubgroup A)]

end TauCeti.DynkinType.ChevalleyDatum
