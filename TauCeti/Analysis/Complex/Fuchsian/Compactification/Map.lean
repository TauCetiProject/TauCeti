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

Cusp data with the same representative and scaling define the same horodiscs, even when their
groups have different primitive cusp widths.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ Θ : Subgroup PSL(2, ℝ)}

/-- An inclusion of projective subgroups induces a map on their compactified
quotients, agreeing with the ordinary orbit map away from the cusps. -/
def compactifiedQuotientMap (h : Δ ≤ Γ) :
    Δ.CompactifiedQuotient → Γ.CompactifiedQuotient
  | .ofQuotient p => .ofQuotient (Setoid.map_of_le
      (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) p)
  | .ofCusp C => .ofCusp (cuspOrbitMap h C)

@[simp]
theorem compactifiedQuotientMap_ofQuotient (h : Δ ≤ Γ) (p : orbitRel.Quotient Δ ℍ) :
    compactifiedQuotientMap h (.ofQuotient p) =
      .ofQuotient (Setoid.map_of_le
        (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) p) :=
  (rfl)

@[simp]
theorem compactifiedQuotientMap_ofCusp (h : Δ ≤ Γ) (C : Δ.CuspOrbit) :
    compactifiedQuotientMap h (.ofCusp C) = .ofCusp (cuspOrbitMap h C) :=
  (rfl)

/-- The compactified quotient map for a reflexive inclusion is the identity. -/
@[simp]
theorem compactifiedQuotientMap_self :
    compactifiedQuotientMap (le_refl Δ) = id := by
  funext x
  cases x with
  | ofQuotient p =>
      induction p using Quotient.inductionOn' with
      | h z => simp
  | ofCusp C => simp

/-- Two subgroup inclusions induce the map for their composite on each compactified point. -/
@[simp]
theorem compactifiedQuotientMap_compactifiedQuotientMap (h : Δ ≤ Γ) (k : Γ ≤ Θ)
    (x : Δ.CompactifiedQuotient) :
    compactifiedQuotientMap k (compactifiedQuotientMap h x) =
      compactifiedQuotientMap (h.trans k) x := by
  cases x with
  | ofQuotient p =>
      induction p using Quotient.inductionOn' with
      | h z => simp
  | ofCusp C => simp

/-- Compactified quotient maps compose along a tower of subgroup inclusions. -/
theorem compactifiedQuotientMap_comp (h : Δ ≤ Γ) (k : Γ ≤ Θ) :
    compactifiedQuotientMap k ∘ compactifiedQuotientMap h =
      compactifiedQuotientMap (h.trans k) := by
  funext x
  exact compactifiedQuotientMap_compactifiedQuotientMap h k x

/-- The compactified map commutes with the coarse-quotient constructors. -/
theorem compactifiedQuotientMap_comp_ofQuotient (h : Δ ≤ Γ) :
    compactifiedQuotientMap h ∘ (CompactifiedQuotient.ofQuotient (Γ := Δ)) =
      (CompactifiedQuotient.ofQuotient (Γ := Γ)) ∘ Setoid.map_of_le
        (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) := by
  funext p
  simp

namespace CompactifiedQuotient

/-- The map induced by `Δ ≤ Γ` sends a cusp neighbourhood into the neighbourhood at the
same boundary point and height, when the cusp data use the same scaling. -/
theorem image_compactifiedQuotientMap_cuspNhd_subset_cuspNhd
    (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : E.scaling = D.scaling) (A : ℝ) :
    compactifiedQuotientMap h '' cuspNhd D A ⊆ cuspNhd E A := by
  have hc : E.cusp = D.cusp := (MulAction.injective D.scaling)
    ((hσ ▸ E.scaling_smul_cusp).trans D.scaling_smul_cusp.symm)
  rintro _ ⟨x, hx, rfl⟩
  cases x with
  | ofQuotient p =>
      rw [ofQuotient_mem_cuspNhd_iff] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [compactifiedQuotientMap_ofQuotient, TauCeti.Setoid.map_of_le_mk,
        ofQuotient_mem_cuspNhd_iff]
      exact ⟨z, by simpa only [TauCeti.Subgroup.CuspDatum.mem_horodisc, hσ] using hz, rfl⟩
  | ofCusp C =>
      rw [ofCusp_mem_cuspNhd_iff] at hx
      subst C
      rw [compactifiedQuotientMap_ofCusp, ofCusp_mem_cuspNhd_iff]
      exact cuspOrbitMap_cuspOrbit_eq_of_cusp_eq h hc

/-- The map of compactified quotients is continuous at each cusp point. -/
theorem continuousAt_compactifiedQuotientMap_ofCusp [DiscreteTopology Γ]
    (h : Δ ≤ Γ) (D : Δ.CuspDatum) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ContinuousAt (compactifiedQuotientMap h) (.ofCusp D.cuspOrbit) := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  obtain ⟨E, hc, hσ⟩ := (D.isCuspPoint.mono h).exists_cuspDatum D.scaling_smul_cusp
  have hC := cuspOrbitMap_cuspOrbit_eq_of_cusp_eq h hc
  rw [ContinuousAt, compactifiedQuotientMap_ofCusp, hC]
  refine (nhds_basis_cuspNhd E 0).tendsto_right_iff.mpr fun A _ ↦ ?_
  exact Filter.mem_of_superset (cuspNhd_mem_nhds D A)
    (image_subset_iff.mp (image_compactifiedQuotientMap_cuspNhd_subset_cuspNhd
      h D E hσ A))

/-- The compactified orbit map induced by an inclusion of discrete projective subgroups is
continuous, including at the added cusp points. -/
theorem continuous_compactifiedQuotientMap [DiscreteTopology Γ] (h : Δ ≤ Γ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    Continuous (compactifiedQuotientMap h) := by
  have : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [continuous_iff_continuousAt]
  intro x
  cases x with
  | ofQuotient p =>
      have hcomp : ContinuousAt
          (compactifiedQuotientMap h ∘ (ofQuotient (Γ := Δ))) p := by
        rw [compactifiedQuotientMap_comp_ofQuotient]
        exact (continuous_ofQuotient.comp
          (continuous_map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le
            (X := ℍ) h))).continuousAt
      exact (isOpenEmbedding_ofQuotient (Γ := Δ)).continuousAt_iff.mp hcomp
  | ofCusp C =>
      obtain ⟨D, hD⟩ := CuspDatum.cuspOrbit_surjective C
      rw [← hD]
      exact continuousAt_compactifiedQuotientMap_ofCusp h D

end CompactifiedQuotient

end Subgroup
