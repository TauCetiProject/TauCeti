/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusp points and cusp orbits of a projective subgroup

A cusp point of a subgroup `Γ ≤ PSL(2, ℝ)` is a point of the projective boundary fixed by a
parabolic element of `Γ`. Parabolicity is invariant under conjugation, so the cusp points form an
invariant subspace of `OnePoint ℝ`. A cusp orbit is an orbit in the full projective boundary whose
representatives are cusp points.

The cusp-orbit carrier is deliberately a subtype of the boundary orbit space. This makes it the
literal collection of boundary orbits that will be adjoined to a Fuchsian quotient during cusp
compactification. It is canonically equivalent to the quotient of the invariant subspace of cusp
points, and `Subgroup.cuspOrbitEquivQuotientCuspPoints` records that comparison.

This construction is the effective-projective analogue of Mathlib's `IsCusp`,
`cuspsSubMulAction`, and `CuspOrbits` for subgroups of `GL(2, ℝ)`.

## Main declarations

* `Subgroup.IsCuspPoint`: a projective boundary point fixed by a parabolic element of `Γ`.
* `Subgroup.cuspPoints`: the invariant subspace of cusp points.
* `Subgroup.BoundaryOrbit`: the orbit space of `Γ` on the full projective boundary.
* `Subgroup.CuspOrbit`: the subtype of boundary orbits represented by cusp points.
* `Subgroup.cuspOrbitEquivQuotientCuspPoints`: the identification with the quotient of
  `Subgroup.cuspPoints`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 10.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.4 and 4.2.
-/

public noncomputable section

open Matrix MulAction
open scoped MatrixGroups

namespace Subgroup

/-- A point of the projective boundary is a cusp point of `Γ ≤ PSL(2, ℝ)` when it is fixed by a
parabolic element of `Γ`. -/
def IsCuspPoint (Γ : Subgroup PSL(2, ℝ)) (c : OnePoint ℝ) : Prop :=
  ∃ g : Γ, ProjectiveSpecialLinearGroup.IsParabolic (g : PSL(2, ℝ)) ∧ g • c = c

/-- A point is a cusp point exactly when it is the unique fixed point of a parabolic element of
`Γ`. -/
theorem isCuspPoint_iff_exists_parabolicFixedPoint_eq {Γ : Subgroup PSL(2, ℝ)}
    {c : OnePoint ℝ} :
    Γ.IsCuspPoint c ↔ ∃ g : Γ, ProjectiveSpecialLinearGroup.IsParabolic (g : PSL(2, ℝ)) ∧
      ProjectiveSpecialLinearGroup.parabolicFixedPoint (g : PSL(2, ℝ)) = c := by
  simp only [IsCuspPoint]
  refine exists_congr fun g ↦ and_congr_right fun hg ↦ ?_
  exact hg.smul_eq_self_iff.trans eq_comm

/-- A point is a cusp point exactly when its stabilizer in `Γ` contains a parabolic element. -/
theorem isCuspPoint_iff_exists_mem_stabilizer_isParabolic {Γ : Subgroup PSL(2, ℝ)}
    {c : OnePoint ℝ} :
    Γ.IsCuspPoint c ↔ ∃ g : Γ, g ∈ stabilizer Γ c ∧
      ProjectiveSpecialLinearGroup.IsParabolic (g : PSL(2, ℝ)) := by
  simp only [IsCuspPoint, mem_stabilizer_iff]
  exact exists_congr fun _ ↦ and_comm

/-- Every cusp stabilizer contains a nonidentity parabolic element. -/
theorem IsCuspPoint.exists_ne_one_mem_stabilizer {Γ : Subgroup PSL(2, ℝ)}
    {c : OnePoint ℝ} (hc : Γ.IsCuspPoint c) :
    ∃ g : Γ, g ≠ 1 ∧ g ∈ stabilizer Γ c ∧
      ProjectiveSpecialLinearGroup.IsParabolic (g : PSL(2, ℝ)) := by
  obtain ⟨g, hgpar, hgc⟩ := hc
  exact ⟨g, fun hg ↦ hgpar.ne_one (congrArg Subtype.val hg), hgc, hgpar⟩

/-- A cusp point for a subgroup remains a cusp point after enlarging the subgroup. -/
theorem IsCuspPoint.mono {Γ Δ : Subgroup PSL(2, ℝ)} {c : OnePoint ℝ}
    (hΓΔ : Γ ≤ Δ) (hc : Γ.IsCuspPoint c) : Δ.IsCuspPoint c := by
  obtain ⟨g, hgpar, hgc⟩ := hc
  exact ⟨⟨g, hΓΔ g.property⟩, hgpar, hgc⟩

/-- The image of a cusp point under an element of `Γ` is again a cusp point. -/
theorem IsCuspPoint.smul {Γ : Subgroup PSL(2, ℝ)} {c : OnePoint ℝ}
    (hc : Γ.IsCuspPoint c) (g : Γ) : Γ.IsCuspPoint (g • c) := by
  obtain ⟨p, hppar, hpc⟩ := hc
  refine ⟨g * p * g⁻¹, ?_, ?_⟩
  · simpa using
      (ProjectiveSpecialLinearGroup.isParabolic_conj_iff (g : PSL(2, ℝ))
        (p : PSL(2, ℝ))).mpr hppar
  · simp [mul_smul, hpc]

/-- Cusp-point membership is invariant under the action of `Γ`. -/
@[simp]
theorem isCuspPoint_smul_iff {Γ : Subgroup PSL(2, ℝ)} (g : Γ) (c : OnePoint ℝ) :
    Γ.IsCuspPoint (g • c) ↔ Γ.IsCuspPoint c := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ hc.smul g⟩
  simpa using hc.smul g⁻¹

/-- The cusp points of `Γ`, as an invariant subspace of the projective boundary. -/
def cuspPoints (Γ : Subgroup PSL(2, ℝ)) : SubMulAction Γ (OnePoint ℝ) where
  carrier := {c | Γ.IsCuspPoint c}
  smul_mem' g _ hc := hc.smul g

@[simp]
theorem mem_cuspPoints {Γ : Subgroup PSL(2, ℝ)} {c : OnePoint ℝ} :
    c ∈ Γ.cuspPoints ↔ Γ.IsCuspPoint c :=
  Iff.rfl

/-- The orbit space of `Γ` on the full projective boundary. -/
abbrev BoundaryOrbit (Γ : Subgroup PSL(2, ℝ)) :=
  orbitRel.Quotient Γ (OnePoint ℝ)

/-- A boundary orbit is a cusp orbit when one, equivalently every, representative is a cusp
point. -/
def IsCuspOrbit (Γ : Subgroup PSL(2, ℝ)) (C : Γ.BoundaryOrbit) : Prop :=
  ∃ c : OnePoint ℝ, Γ.IsCuspPoint c ∧ Quotient.mk'' c = C

/-- The orbit of a boundary point is a cusp orbit exactly when that point is a cusp point. -/
@[simp]
theorem isCuspOrbit_mk_iff {Γ : Subgroup PSL(2, ℝ)} (c : OnePoint ℝ) :
    Γ.IsCuspOrbit (Quotient.mk'' c) ↔ Γ.IsCuspPoint c := by
  constructor
  · rintro ⟨d, hd, hdc⟩
    rw [Quotient.eq'', orbitRel_apply, mem_orbit_iff] at hdc
    obtain ⟨g, rfl⟩ := hdc
    exact (isCuspPoint_smul_iff g c).mp hd
  · exact fun hc ↦ ⟨c, hc, rfl⟩

/-- The cusp orbits of `Γ`, as the subtype of its boundary orbits represented by cusp points. -/
abbrev CuspOrbit (Γ : Subgroup PSL(2, ℝ)) :=
  {C : Γ.BoundaryOrbit // Γ.IsCuspOrbit C}

/-- The cusp orbit represented by a cusp point. -/
def cuspOrbitMk {Γ : Subgroup PSL(2, ℝ)} (c : Γ.cuspPoints) : Γ.CuspOrbit :=
  ⟨Quotient.mk'' (c : OnePoint ℝ), (isCuspOrbit_mk_iff c).mpr c.property⟩

@[simp]
theorem cuspOrbitMk_val {Γ : Subgroup PSL(2, ℝ)} (c : Γ.cuspPoints) :
    (Γ.cuspOrbitMk c : Γ.BoundaryOrbit) = Quotient.mk'' (c : OnePoint ℝ) :=
  (rfl)

/-- Two cusp points represent the same cusp orbit exactly when they lie in the same `Γ`-orbit. -/
theorem cuspOrbitMk_eq_iff {Γ : Subgroup PSL(2, ℝ)} (c d : Γ.cuspPoints) :
    Γ.cuspOrbitMk c = Γ.cuspOrbitMk d ↔ (c : OnePoint ℝ) ∈ orbit Γ (d : OnePoint ℝ) := by
  rw [Subtype.ext_iff, cuspOrbitMk_val, cuspOrbitMk_val, Quotient.eq'', orbitRel_apply]

/-- The subtype of cusp orbits in the full boundary quotient is canonically equivalent to the
orbit quotient of the invariant subspace of cusp points. -/
def cuspOrbitEquivQuotientCuspPoints (Γ : Subgroup PSL(2, ℝ)) :
    Γ.CuspOrbit ≃ orbitRel.Quotient Γ Γ.cuspPoints :=
  Equiv.subtypeQuotientEquivQuotientSubtype (Γ.IsCuspPoint ·) (Γ.IsCuspOrbit ·)
    (fun c ↦ (isCuspOrbit_mk_iff c).symm) fun c d ↦ by
      rw [SubMulAction.orbitRel_of_subMul]
      exact Iff.rfl

@[simp]
theorem cuspOrbitEquivQuotientCuspPoints_cuspOrbitMk {Γ : Subgroup PSL(2, ℝ)}
    (c : Γ.cuspPoints) :
    Γ.cuspOrbitEquivQuotientCuspPoints (Γ.cuspOrbitMk c) = Quotient.mk'' c :=
  (rfl)

/-- Every cusp orbit has a cusp-point representative. -/
theorem cuspOrbitMk_surjective {Γ : Subgroup PSL(2, ℝ)} :
    Function.Surjective (@cuspOrbitMk Γ) := by
  intro C
  obtain ⟨c, hc, hC⟩ := C.property
  exact ⟨⟨c, hc⟩, Subtype.ext hC⟩

end Subgroup
