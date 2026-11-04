/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# High horodiscs in a Fuchsian quotient

For a normalized cusp datum `D` and a height at least its width, the horodisc at that height is
precisely invariant under the cusp stabilizer. This file packages the horodisc as an invariant
subspace for that stabilizer and proves that its orbit space maps by an open embedding into the
coarse quotient `Γ \\ ℍ`. The image is an open subset that can serve as a punctured cusp chart
domain after compactification, with the q-coordinate supplied by the stabilizer quotient.

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

/-- On a high horodisc, two points have the same image in the coarse quotient exactly when their
q-coordinates agree. Thus the q-coordinate distinguishes the points of the punctured cusp
neighbourhood in the coarse quotient. -/
theorem quotientMk_eq_iff_qCoordinate_eq [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A)
    {z z' : ℍ} (hz : z ∈ horodisc D A) (hz' : z' ∈ horodisc D A) :
    Quotient.mk (orbitRel Γ ℍ) z = Quotient.mk (orbitRel Γ ℍ) z' ↔
      qCoordinate D z = qCoordinate D z' := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h))
    have hgmem : g ∈ stabilizer Γ D.cusp :=
      mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc D hA hz' (by rw [hg]; exact hz)
    rw [← hg]
    exact qCoordinate_smul_of_mem D hgmem z'
  · intro h
    obtain ⟨n, hn⟩ := (qCoordinate_eq_iff D z z').mp h
    exact Quotient.sound (orbitRel_apply.mpr ⟨D.generator ^ n, hn.symm⟩)

/-- Above the cusp width, the local horodisc quotient embeds openly into the coarse quotient. -/
theorem isOpenEmbedding_orbitRelQuotientMap_horodiscSubMulAction [DiscreteTopology Γ] {A : ℝ}
    (hA : D.width ≤ A) :
    IsOpenEmbedding (horodiscSubMulAction D A).orbitRelQuotientMap :=
  (horodiscSubMulAction D A).isOpenEmbedding_orbitRelQuotientMap (isOpen_horodisc D A)
    fun _ _ hy hgy ↦ mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc D hA hy hgy

/-- A horodisc has open image in the coarse quotient. -/
theorem isOpen_image_quotientMk_horodisc (A : ℝ) :
    IsOpen (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A) :=
  isOpenMap_quotient_mk'_mul _ (isOpen_horodisc D A)

end TauCeti.Subgroup.CuspDatum
