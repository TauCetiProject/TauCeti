/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer

/-!
# Finiteness of elliptic orbits

For a discrete subgroup of `PSL(2, ℝ)`, points with nontrivial stabilizer are locally isolated:
proper discontinuity reduces nearby stabilizers to the stabilizer of the centre, and a nonidentity
projective Möbius transformation fixes at most one point of the upper half-plane. Their orbits are
therefore locally isolated in the coarse quotient. High cusp horodiscs contain no such points,
so a compact cusp compactification has only finitely many elliptic orbits.

This finiteness is needed to form the elliptic-order list in an orbifold signature. It applies
whenever the compactification is compact, independently of how compactness was established.

## References

Svetlana Katok, *Fuchsian Groups*, §2.4 and Chapter 4.
-/

public section

open Filter MulAction Set Topology UpperHalfPlane TauCeti
open scoped MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ))

section Local

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- Every point has a neighbourhood containing no elliptic point other than itself. -/
theorem exists_nhds_inter_ellipticPoints_subset_singleton (z : ℍ) :
    ∃ U ∈ 𝓝 z, U ∩ (freeLocus Γ ℍ : Set ℍ)ᶜ ⊆ {z} := by
  obtain ⟨U, hU, hsep⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Γ z
  refine ⟨U, hU, ?_⟩
  intro w hw
  have hwE : stabilizer Γ w ≠ ⊥ := (mem_freeLocus Γ ℍ).not.mp hw.2
  have hex : ∃ g : Γ, g ∈ stabilizer Γ w ∧ g ≠ 1 := by
    by_contra h
    apply hwE
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    by_contra hg1
    exact h ⟨g, hg, hg1⟩
  obtain ⟨g, hg, hg1⟩ := hex
  have hgw : g • w = w := mem_stabilizer_iff.mp hg
  have hgz : g • z = z := hsep g ⟨w, ⟨w, hw.1, hgw⟩, hw.1⟩
  have hneq : (g : PSL(2, ℝ)) ≠ 1 := by
    intro h
    exact hg1 (Subtype.ext h)
  by_contra hwz
  exact hneq (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self
    (by simpa only [Subgroup.smul_def] using hgz)
    (by simpa only [Subgroup.smul_def] using hgw) hwz)

end Local

variable [DiscreteTopology Γ]

/-- An elliptic orbit is an orbit containing a point with nontrivial stabilizer. -/
def ellipticOrbits : Set (orbitRel.Quotient Γ ℍ) :=
  Quotient.mk (orbitRel Γ ℍ) '' (freeLocus Γ ℍ : Set ℍ)ᶜ

omit [DiscreteTopology Γ] in
/-- An orbit is elliptic exactly when a representative has nontrivial stabilizer. -/
@[simp]
theorem quotientMk_mem_ellipticOrbits_iff (z : ℍ) :
    (Quotient.mk (orbitRel Γ ℍ) z : orbitRel.Quotient Γ ℍ) ∈ Γ.ellipticOrbits ↔
      z ∉ freeLocus Γ ℍ := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (mem_freeLocus_iff_of_quotientMk_eq Γ ℍ heq).not.mp hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The elliptic points of the compactification are precisely the coarse orbits with
nontrivial stabilizer. -/
private def ellipticCompactified : Set Γ.CompactifiedQuotient :=
  CompactifiedQuotient.ofQuotient '' Γ.ellipticOrbits

/-- Near an interior point, there is at most one elliptic orbit. -/
private theorem exists_isOpen_ellipticCompactified_inter_subset_singleton (z : ℍ) :
    ∃ U : Set Γ.CompactifiedQuotient, IsOpen U ∧
      CompactifiedQuotient.ofQuotient (Quotient.mk (orbitRel Γ ℍ) z) ∈ U ∧
      Γ.ellipticCompactified ∩ U ⊆
        {CompactifiedQuotient.ofQuotient (Quotient.mk (orbitRel Γ ℍ) z)} := by
  obtain ⟨V, hV, hVell⟩ := Γ.exists_nhds_inter_ellipticPoints_subset_singleton z
  let W := interior V
  let Q : Set (orbitRel.Quotient Γ ℍ) := Quotient.mk (orbitRel Γ ℍ) '' W
  let U : Set Γ.CompactifiedQuotient := CompactifiedQuotient.ofQuotient '' Q
  have hQ : IsOpen Q := by
    exact isOpenMap_quotient_mk'_mul W isOpen_interior
  refine ⟨U, CompactifiedQuotient.isOpenMap_ofQuotient Q hQ, ?_, ?_⟩
  · exact ⟨_, ⟨z, mem_interior_iff_mem_nhds.mpr hV, rfl⟩, rfl⟩
  · rintro x ⟨⟨q, hqell, rfl⟩, ⟨q', hq', hqq'⟩⟩
    obtain ⟨e, he, rfl⟩ := hqell
    obtain ⟨w, hw, hwq⟩ := hq'
    have hew : w ∈ (freeLocus Γ ℍ : Set ℍ)ᶜ :=
      (mem_freeLocus_iff_of_quotientMk_eq Γ ℍ
        ((CompactifiedQuotient.ofQuotient_injective hqq').symm.trans hwq.symm)).not.mp he
    have hwz : w = z := hVell ⟨interior_subset hw, hew⟩
    subst w
    exact mem_singleton_iff.mpr (by simpa only [hwq] using hqq'.symm)

/-- High cusp neighbourhoods contain no elliptic orbits. -/
private theorem disjoint_ellipticCompactified_cuspNhd (D : Γ.CuspDatum) {A : ℝ}
    (hA : D.width ≤ A) :
    Disjoint Γ.ellipticCompactified (CompactifiedQuotient.cuspNhd D A) := by
  rw [disjoint_left]
  rintro x ⟨q, ⟨z, hz, rfl⟩, rfl⟩ hx
  have hq := (CompactifiedQuotient.ofQuotient_mem_cuspNhd_iff D A).mp hx
  obtain ⟨w, hw, heq⟩ := hq
  have hwE := (mem_freeLocus_iff_of_quotientMk_eq Γ ℍ heq.symm).not.mp hz
  exact hwE ((mem_freeLocus Γ ℍ).mpr (D.stabilizer_eq_bot_of_mem_horodisc hA hw))

/-- A compactified Fuchsian quotient has finitely many elliptic orbits. -/
private theorem finite_ellipticCompactified [CompactSpace Γ.CompactifiedQuotient] :
    Γ.ellipticCompactified.Finite := by
  classical
  have hlocal (x : Γ.CompactifiedQuotient) :
      ∃ U : Set Γ.CompactifiedQuotient, IsOpen U ∧ x ∈ U ∧
        (Γ.ellipticCompactified ∩ U).Finite := by
    cases x with
    | ofQuotient q =>
        obtain ⟨U, hU, hx, hsub⟩ :=
          Γ.exists_isOpen_ellipticCompactified_inter_subset_singleton q.out
        refine ⟨U, hU, ?_, (finite_singleton _).subset hsub⟩
        simpa only [Quotient.out_eq] using hx
    | ofCusp C =>
        obtain ⟨D, hD⟩ := CuspDatum.cuspOrbit_surjective C
        refine ⟨CompactifiedQuotient.cuspNhd D D.width,
          CompactifiedQuotient.isOpen_cuspNhd D D.width, ?_, ?_⟩
        · rw [← hD]
          exact CompactifiedQuotient.ofCusp_mem_cuspNhd D D.width
        · exact (Set.finite_empty).subset fun x hx ↦
            False.elim ((disjoint_left.mp
              (Γ.disjoint_ellipticCompactified_cuspNhd D le_rfl)) hx.1 hx.2)
  choose U hU hmem hfin using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hmem x⟩)
  have hfinite : (⋃ x ∈ t, Γ.ellipticCompactified ∩ U x).Finite :=
    (Finset.finite_toSet t).biUnion fun x _ ↦ hfin x
  exact hfinite.subset fun x hx ↦ by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact mem_iUnion₂.mpr ⟨i, hi, ⟨hx, hxi⟩⟩

/-- The elliptic orbits in the coarse quotient are finite whenever its cusp
compactification is compact. -/
theorem finite_ellipticOrbits [CompactSpace Γ.CompactifiedQuotient] :
    Γ.ellipticOrbits.Finite := by
  exact (Γ.finite_ellipticCompactified).preimage
    CompactifiedQuotient.ofQuotient_injective.injOn |>.subset (by
      intro q hq
      exact ⟨q, hq, rfl⟩)

end Subgroup
