/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc

/-!
# High horodiscs in a Fuchsian quotient

For a normalized cusp datum `D` and a height at least its width, the horodisc at that height is
precisely invariant under the cusp stabilizer. This file packages the horodisc as an invariant
subspace for that stabilizer and proves that its orbit space maps by an open embedding into the
coarse quotient `Γ \\ ℍ`. Thus the q-coordinate on the stabilizer quotient supplies a genuine
punctured neighbourhood of the corresponding cusp in the coarse quotient, rather than merely a
coordinate on an abstract stabilizer quotient.

The next compactification step fills this puncture by the cusp point and extends the q-coordinate
across it.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
-/

public section

noncomputable section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- The horodisc at `D`'s cusp, as an invariant subspace for its full stabilizer. -/
abbrev horodiscSubMulAction (A : ℝ) : SubMulAction (stabilizer Γ D.cusp) ℍ where
  carrier := horodisc D A
  smul_mem' g z hz := by
    rw [← smul_horodisc_of_mem_stabilizer D g.2 A]
    exact Set.smul_mem_smul_set hz

@[simp]
theorem coe_horodiscSubMulAction (A : ℝ) :
    (horodiscSubMulAction D A : Set ℍ) = horodisc D A :=
  rfl

@[simp]
theorem mem_horodiscSubMulAction {A : ℝ} {z : ℍ} :
    z ∈ horodiscSubMulAction D A ↔ z ∈ horodisc D A :=
  Iff.rfl

/-- The map from the cusp-stabilizer quotient of a horodisc to the full coarse quotient. -/
abbrev horodiscQuotientToQuotient (A : ℝ) :
    orbitRel.Quotient (stabilizer Γ D.cusp) (horodiscSubMulAction D A) →
      orbitRel.Quotient Γ ℍ :=
  Quotient.map' (↑) fun _ _ h ↦ by
    rw [orbitRel_apply, SubMulAction.mem_orbit_subMul_iff] at h
    exact orbitRel_apply.mpr (orbit_subgroup_subset _ _ h)

@[simp]
theorem horodiscQuotientToQuotient_mk {A : ℝ} (z : horodiscSubMulAction D A) :
    horodiscQuotientToQuotient D A (Quotient.mk _ z) = Quotient.mk _ (z : ℍ) :=
  rfl

/-- The local quotient map of a horodisc is continuous. -/
theorem continuous_horodiscQuotientToQuotient (A : ℝ) :
    Continuous (horodiscQuotientToQuotient D A) :=
  continuous_subtype_val.quotient_map' _

/-- The local quotient map of a horodisc is open onto its image in the coarse quotient. -/
theorem isOpenMap_horodiscQuotientToQuotient (A : ℝ) :
    IsOpenMap (horodiscQuotientToQuotient D A) := by
  intro V hV
  have himage : horodiscQuotientToQuotient D A '' V =
      Quotient.mk _ '' ((↑) '' (Quotient.mk _ ⁻¹' V : Set (horodiscSubMulAction D A))) := by
    conv_lhs => rw [← image_preimage_eq V Quotient.mk_surjective]
    simp only [image_image, horodiscQuotientToQuotient_mk]
  rw [himage]
  have hopen : IsOpen (horodiscSubMulAction D A : Set ℍ) := by
    rw [coe_horodiscSubMulAction]
    exact isOpen_horodisc D A
  exact isOpenMap_quotient_mk'_mul _
    (hopen.isOpenMap_subtype_val _ (hV.preimage continuous_quotient_mk'))

/-- The range of the local quotient map is the image of the horodisc in the coarse quotient. -/
theorem range_horodiscQuotientToQuotient (A : ℝ) :
    range (horodiscQuotientToQuotient D A) = Quotient.mk (orbitRel Γ ℍ) '' horodisc D A := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Quotient.inductionOn with
    | h z => exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Quotient.mk _ ⟨z, hz⟩, rfl⟩

/-- On a high horodisc, two points have the same image in the coarse quotient exactly when their
q-coordinates agree. Thus the q-coordinate distinguishes the points of the punctured cusp
neighbourhood in the coarse quotient. -/
theorem quotientMk_eq_iff_qCoordinate_eq [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A)
    {z z' : ℍ} (hz : z ∈ horodisc D A) (hz' : z' ∈ horodisc D A) :
    Quotient.mk (orbitRel Γ ℍ) z = Quotient.mk (orbitRel Γ ℍ) z' ↔
      qCoordinate D z = qCoordinate D z' := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact h)
    change g • z' = z at hg
    have hgmem : g ∈ stabilizer Γ D.cusp :=
      mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc D hA hz' (by rw [hg]; exact hz)
    rw [← hg]
    exact qCoordinate_smul_of_mem D hgmem z'
  · intro h
    obtain ⟨n, hn⟩ := (qCoordinate_eq_iff D z z').mp h
    exact Quotient.sound (orbitRel_apply.mpr ⟨D.generator ^ n, hn.symm⟩)

/-- Above the cusp width, the local horodisc quotient embeds openly into the coarse quotient. -/
theorem isOpenEmbedding_horodiscQuotientToQuotient [DiscreteTopology Γ] {A : ℝ}
    (hA : D.width ≤ A) :
    IsOpenEmbedding (horodiscQuotientToQuotient D A) := by
  refine .of_continuous_injective_isOpenMap (continuous_horodiscQuotientToQuotient D A) ?_
    (isOpenMap_horodiscQuotientToQuotient D A)
  rintro ⟨z⟩ ⟨z'⟩ h
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact h)
  change g • (z' : ℍ) = (z : ℍ) at hg
  have hgmem : g ∈ stabilizer Γ D.cusp :=
    mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc D hA z'.2 (by rw [hg]; exact z.2)
  exact Quotient.sound <| orbitRel_apply.mpr <|
    SubMulAction.mem_orbit_subMul_iff.mpr ⟨⟨g, hgmem⟩, hg⟩

/-- A high horodisc has open image in the coarse quotient. -/
theorem isOpen_image_quotientMk_horodisc [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A) :
    IsOpen (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A) := by
  rw [← range_horodiscQuotientToQuotient]
  exact (isOpenEmbedding_horodiscQuotientToQuotient D hA).isOpen_range

end TauCeti.Subgroup.CuspDatum
