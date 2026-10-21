/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Meridian
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Relations
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Ideal

/-!
# Positive cusp generators from polygon cycles

At an ideal vertex of a side-paired convex hyperbolic polygon, a parabolic cycle transformation
is the positive primitive generator of the full vertex stabilizer, provided the ambient group
contains the side pairings and distinct translated interiors are disjoint. In every scaling
sending that vertex to infinity, the cycle transformation is translation by the cusp width.
Thus a counterclockwise cusp meridian lifts to a path ending at the cycle transformation of
its starting point; reversing the turns gives the inverse transformation.

This identifies the order of side generators in polygon cycle words with the orientation of the
q-coordinate. Primitivity uses the ideal-vertex stabilizer theorem, while positivity uses the
ordered strips of the cycle. Neither discreteness nor local finiteness is assumed in addition
to parabolicity of the cycle transformation.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9 (parabolic vertex cycles).
* Svetlana Katok, *Fuchsian Groups*, Chapters 3–4 (cycles and cusp stabilizers).
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4 (cusp coordinates).

The construction combines `SidePairing.map_stabilizer_eq_zpowers_cycleMap_of_vertex_eq_inr`
with `SidePairing.exists_pos_conj_cycleMap_eq_upperRightHom` and the normalized cusp datum
and meridian APIs.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Complex.UnitDisc

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

/-- The parabolic cycle at an ideal vertex supplies normalized cusp data with exactly that
cycle transformation as generator, in every scaling sending the vertex to infinity. -/
theorem exists_cuspDatum_generator_eq_cycleMap {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) (hmap : ∀ i, σ.map i ∈ Γ)
    (hpar : IsParabolic (σ.cycleMap j))
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g : PSL(2, ℝ)} (hg : g • ξ = ∞) :
    ∃ D : Γ.CuspDatum, D.cusp = ξ ∧ D.scaling = g ∧
      (D.generator : PSL(2, ℝ)) = σ.cycleMap j := by
  obtain ⟨w, hw, hconj⟩ := σ.exists_pos_conj_cycleMap_eq_upperRightHom hj hpar hg
  let γ : Γ := ⟨σ.cycleMap j, σ.cycleMap_mem hmap j⟩
  have hgen : Subgroup.zpowers γ = stabilizer Γ ξ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [MonoidHom.map_zpowers,
      σ.map_stabilizer_eq_zpowers_cycleMap_of_vertex_eq_inr hj hmap hpar hdisj]
    rfl
  exact ⟨⟨ξ, g, γ, w, hw, hgen, hconj⟩, rfl, rfl, rfl⟩

/-- The positive generator of any normalized datum at an ideal polygon vertex is the cycle
transformation itself. In particular it is neither its inverse nor a proper power. -/
theorem cuspDatum_generator_eq_cycleMap {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (D : Γ.CuspDatum) (hc : D.cusp = ξ) :
    (D.generator : PSL(2, ℝ)) = σ.cycleMap j := by
  -- The datum already forces every nonidentity stabilizer element to be parabolic.
  let γ : Γ := ⟨σ.cycleMap j, σ.cycleMap_mem hmap j⟩
  have hfix : γ ∈ stabilizer Γ D.cusp := by
    rw [hc, mem_stabilizer_iff, Subgroup.mk_smul]
    exact σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj
  have hpar : IsParabolic (σ.cycleMap j) :=
    D.isParabolic_of_mem_stabilizer_of_ne_one hfix fun h ↦
      σ.cycleMap_ne_one_of_vertex_eq_inr hj (congrArg Subtype.val h)
  obtain ⟨E, hEc, hEs, hEg⟩ := σ.exists_cuspDatum_generator_eq_cycleMap hj hmap hpar hdisj
    (hc ▸ D.scaling_smul_cusp)
  have hED : E = D := Subgroup.CuspDatum.ext (hEc.trans hc.symm) hEs
  exact hED ▸ hEg

/-- A lift of a cusp meridian with `k` signed turns at an ideal polygon vertex ends at the
evaluation of the `k`th power of its cycle word. Positive turns are counterclockwise in the
q-plane, so one positive turn evaluates the cycle word rather than its inverse. -/
theorem meridian_lift_endpoint_eq_pairingHom_cycleWord_zpow_smul {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (D : Γ.CuspDatum) (hc : D.cusp = ξ) (k : ℤ) (z : ℍ) {f : unitInterval → ℍ}
    (hf : Continuous f) (h₀ : f 0 = z)
    (hq : ∀ t, TauCeti.Subgroup.CuspDatum.qCoordinate D (f t) =
      TauCeti.Subgroup.CuspDatum.meridian D k z t) :
    f 1 = σ.pairingHom (σ.cycleWord j ^ k) • z := by
  rw [map_zpow, σ.pairingHom_cycleWord,
    TauCeti.Subgroup.CuspDatum.meridian_lift_endpoint D k z hf h₀ hq,
    Subgroup.smul_def, Subgroup.coe_zpow, σ.cuspDatum_generator_eq_cycleMap hj hmap hdisj D hc]

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
