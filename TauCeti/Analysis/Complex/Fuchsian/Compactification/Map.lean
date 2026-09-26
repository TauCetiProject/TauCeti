/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic

/-!
# Maps between compactified Fuchsian quotients

An inclusion of discrete subgroups `Δ ≤ Γ ≤ PSL(2, ℝ)` induces a map from the compactified
quotient of `Δ` to that of `Γ`. On the coarse quotient it sends the orbit of `z` to its larger
orbit; at a cusp it sends the orbit of a parabolic fixed point to its larger orbit. The map is
continuous also at the adjoined cusp points. The construction applies to arbitrary subgroup
inclusions; finite index is needed only for subsequent finiteness and ramification results.

The continuity argument compares horodiscs with the same representative and scaling. Their
geometric sets are identical even when their groups have different primitive cusp widths.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ Θ : Subgroup PSL(2, ℝ)}

/-- An inclusion of projective subgroups sends an orbit in the upper half-plane to the
corresponding orbit of the larger group. -/
def coarseQuotientMap (h : Δ ≤ Γ) : orbitRel.Quotient Δ ℍ → orbitRel.Quotient Γ ℍ :=
  Quotient.map' id fun _ _ hab ↦ by
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hab)
    exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨g, h g.property⟩, hg⟩)

@[simp]
theorem coarseQuotientMap_mk (h : Δ ≤ Γ) (z : ℍ) :
    coarseQuotientMap h (Quotient.mk _ z) = Quotient.mk _ z :=
  Quotient.map'_mk _ _ _

/-- The orbit map induced by a subgroup inclusion is continuous. -/
theorem continuous_coarseQuotientMap (h : Δ ≤ Γ) : Continuous (coarseQuotientMap h) :=
  continuous_id.quotient_map' _

/-- An inclusion of projective subgroups sends a boundary orbit to the corresponding orbit
of the larger group. -/
def boundaryOrbitMap (h : Δ ≤ Γ) : Δ.BoundaryOrbit → Γ.BoundaryOrbit :=
  Quotient.map' id fun _ _ hab ↦ by
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hab)
    exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨g, h g.property⟩, hg⟩)

@[simp]
theorem boundaryOrbitMap_mk (h : Δ ≤ Γ) (c : OnePoint ℝ) :
    boundaryOrbitMap h (Quotient.mk'' c) = Quotient.mk'' c :=
  Quotient.map'_mk _ _ _

/-- The map on boundary orbits is continuous. -/
theorem continuous_boundaryOrbitMap (h : Δ ≤ Γ) : Continuous (boundaryOrbitMap h) :=
  continuous_id.quotient_map' _

@[simp]
theorem boundaryOrbitMap_id : boundaryOrbitMap (le_refl Δ) = id := by
  funext C
  induction C using Quotient.inductionOn with
  | h c => simp

theorem boundaryOrbitMap_comp (h : Δ ≤ Γ) (k : Γ ≤ Θ) :
    boundaryOrbitMap k ∘ boundaryOrbitMap h = boundaryOrbitMap (h.trans k) := by
  funext C
  induction C using Quotient.inductionOn with
  | h c => simp

/-- The map on boundary orbits restricts to cusp orbits, since a parabolic element of `Δ`
is also an element of `Γ`. -/
def cuspOrbitMap (h : Δ ≤ Γ) : Δ.CuspOrbit → Γ.CuspOrbit :=
  fun C ↦ ⟨boundaryOrbitMap h C, by
    have hc : Δ.IsCuspPoint C.val.out :=
      (isCuspOrbit_mk_iff _).mp (by simpa only [Quotient.out_eq] using C.property)
    have hcΓ : Γ.IsCuspOrbit (Quotient.mk'' C.val.out) :=
      (isCuspOrbit_mk_iff _).mpr (hc.mono h)
    have heq : Quotient.mk'' C.val.out = C.val := Quotient.out_eq _
    rw [← heq, boundaryOrbitMap_mk]
    exact hcΓ⟩

@[simp]
theorem cuspOrbitMap_cuspOrbitMk (h : Δ ≤ Γ) (c : Δ.cuspPoints) :
    cuspOrbitMap h (Δ.cuspOrbitMk c) =
      Γ.cuspOrbitMk ⟨c, mem_cuspPoints.mpr ((mem_cuspPoints.mp c.property).mono h)⟩ :=
  Subtype.ext (by simp only [cuspOrbitMap, cuspOrbitMk_val, boundaryOrbitMap_mk])

/-- A normalized cusp datum maps to the cusp orbit of the same boundary point in the larger
group. -/
theorem cuspOrbitMap_cuspOrbit (h : Δ ≤ Γ) (D : Δ.CuspDatum) :
    cuspOrbitMap h D.cuspOrbit =
      Γ.cuspOrbitMk ⟨D.cusp, mem_cuspPoints.mpr (D.isCuspPoint.mono h)⟩ := by
  apply Subtype.ext
  simp only [cuspOrbitMap, D.cuspOrbit_val, cuspOrbitMk_val, boundaryOrbitMap_mk]

/-- An inclusion of projective subgroups induces a map on their compactified
quotients, agreeing with the ordinary orbit map away from the cusps. -/
def compactifiedQuotientMap (h : Δ ≤ Γ) :
    Δ.CompactifiedQuotient → Γ.CompactifiedQuotient
  | .ofQuotient p => .ofQuotient (coarseQuotientMap h p)
  | .ofCusp C => .ofCusp (cuspOrbitMap h C)

@[simp]
theorem compactifiedQuotientMap_ofQuotient (h : Δ ≤ Γ) (p : orbitRel.Quotient Δ ℍ) :
    compactifiedQuotientMap h (.ofQuotient p) =
      .ofQuotient (coarseQuotientMap h p) :=
  (rfl)

@[simp]
theorem compactifiedQuotientMap_ofCusp (h : Δ ≤ Γ) (C : Δ.CuspOrbit) :
    compactifiedQuotientMap h (.ofCusp C) = .ofCusp (cuspOrbitMap h C) :=
  (rfl)

@[simp]
theorem coarseQuotientMap_id :
    coarseQuotientMap (le_refl Δ) = id := by
  funext p
  induction p using Quotient.inductionOn with
  | h z => simp

@[simp]
theorem cuspOrbitMap_id : cuspOrbitMap (le_refl Δ) = id := by
  funext C
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  simp

@[simp]
theorem compactifiedQuotientMap_id :
    compactifiedQuotientMap (le_refl Δ) = id := by
  funext x
  cases x <;> simp

theorem coarseQuotientMap_comp (h : Δ ≤ Γ) (k : Γ ≤ Θ) :
    coarseQuotientMap k ∘ coarseQuotientMap h = coarseQuotientMap (h.trans k) := by
  funext p
  induction p using Quotient.inductionOn with
  | h z => simp

theorem cuspOrbitMap_comp (h : Δ ≤ Γ) (k : Γ ≤ Θ) :
    cuspOrbitMap k ∘ cuspOrbitMap h = cuspOrbitMap (h.trans k) := by
  funext C
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  simp

/-- Compactified quotient maps compose along a tower of subgroup inclusions. -/
theorem compactifiedQuotientMap_comp (h : Δ ≤ Γ) (k : Γ ≤ Θ) :
    compactifiedQuotientMap k ∘ compactifiedQuotientMap h =
      compactifiedQuotientMap (h.trans k) := by
  funext x
  cases x <;> simp [← congrFun (coarseQuotientMap_comp h k),
    ← congrFun (cuspOrbitMap_comp h k)]

namespace CompactifiedQuotient

/-- The map induced by `Δ ≤ Γ` sends a cusp neighbourhood into the neighbourhood at the
same boundary point and height, when the cusp data use the same scaling. -/
theorem map_cuspNhd_subset (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : E.cusp = D.cusp) (hσ : E.scaling = D.scaling) (A : ℝ) :
    compactifiedQuotientMap h '' cuspNhd D A ⊆ cuspNhd E A := by
  rintro _ ⟨x, hx, rfl⟩
  cases x with
  | ofQuotient p =>
      rw [ofQuotient_mem_cuspNhd_iff] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [compactifiedQuotientMap_ofQuotient, coarseQuotientMap_mk,
        ofQuotient_mem_cuspNhd_iff]
      exact ⟨z, by simpa only [TauCeti.Subgroup.CuspDatum.mem_horodisc, hσ] using hz, rfl⟩
  | ofCusp C =>
      rw [ofCusp_mem_cuspNhd_iff] at hx
      subst C
      rw [compactifiedQuotientMap_ofCusp, ofCusp_mem_cuspNhd_iff]
      rw [cuspOrbitMap_cuspOrbit]
      apply Subtype.ext
      simpa only [cuspOrbitMk_val, E.cuspOrbit_val] using congrArg Quotient.mk'' hc.symm

/-- The map of compactified quotients is continuous at each cusp point. -/
theorem continuousAt_compactifiedQuotientMap_ofCusp [DiscreteTopology Δ]
    [DiscreteTopology Γ] (h : Δ ≤ Γ) (D : Δ.CuspDatum) :
    ContinuousAt (compactifiedQuotientMap h) (.ofCusp D.cuspOrbit) := by
  obtain ⟨E, hc, hσ⟩ := (D.isCuspPoint.mono h).exists_cuspDatum D.scaling_smul_cusp
  have hC : cuspOrbitMap h D.cuspOrbit = E.cuspOrbit := by
    rw [cuspOrbitMap_cuspOrbit]
    apply Subtype.ext
    simpa only [cuspOrbitMk_val, E.cuspOrbit_val] using congrArg Quotient.mk'' hc.symm
  rw [ContinuousAt, compactifiedQuotientMap_ofCusp, hC]
  intro U hU
  obtain ⟨A, hA⟩ := (mem_nhds_ofCusp_iff E).mp hU
  apply (mem_nhds_ofCusp_iff D).mpr
  refine ⟨A, ?_⟩
  intro x hx
  exact hA (map_cuspNhd_subset h D E hc hσ A ⟨x, hx, rfl⟩)

/-- The compactified orbit map induced by an inclusion of discrete projective subgroups is
continuous, including at the added cusp points. -/
theorem continuous_compactifiedQuotientMap [DiscreteTopology Δ] [DiscreteTopology Γ]
    (h : Δ ≤ Γ) :
    Continuous (compactifiedQuotientMap h) := by
  rw [continuous_iff_continuousAt]
  intro x
  cases x with
  | ofQuotient p =>
      have hcomp : ContinuousAt
          (compactifiedQuotientMap h ∘ (ofQuotient (Γ := Δ))) p := by
        have heq : compactifiedQuotientMap h ∘ (ofQuotient (Γ := Δ)) =
            (ofQuotient (Γ := Γ)) ∘ coarseQuotientMap h := by
          funext q
          simp
        rw [heq]
        exact (continuous_ofQuotient.comp (continuous_coarseQuotientMap h)).continuousAt
      exact ((isOpenEmbedding_ofQuotient (Γ := Δ)).isInducing.continuousAt_iff'
        ((isOpen_range_ofQuotient (Γ := Δ)).mem_nhds ⟨p, rfl⟩)).mp hcomp
  | ofCusp C =>
      obtain ⟨D, hD⟩ := CuspDatum.cuspOrbit_surjective C
      rw [← hD]
      exact continuousAt_compactifiedQuotientMap_ofCusp h D

end CompactifiedQuotient

end Subgroup
