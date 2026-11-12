/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import TauCeti.Analysis.Convex.Recession.Basic
public import TauCeti.Geometry.Toric.Algebraic.Cone.RationalDuality
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap

/-!
# Rational-normal polyhedral cones

A pointed cone has a rational-normal affine inequality presentation exactly when it is generated
by finitely many lattice vectors (`TauCeti.isRationalNormalPolyhedron_coe_iff`; the
integral-character form of rational Minkowski–Weyl is
`TauCeti.Toric.IsIntegralLattice.isLatticeRational_iff_exists_dual_image`). The offsets of a
presentation need not be rational. A cone is stable under nonnegative scaling and contains `0`,
which forces the offset of each inequality of a presentation to be nonpositive; the linear parts
alone then cut out the cone, even though individual offsets may be nonzero
(`TauCeti.IsRationalNormalPolyhedron.isLatticeRational`). Conversely a lattice-rational cone is
cut out by integral characters, a presentation with zero offsets
(`TauCeti.Toric.IsLatticeRational.exists_rationalAffinePolyhedron_offset_zero`), and every
presentation with zero offsets cuts out a lattice-rational cone
(`TauCeti.RationalAffinePolyhedron.exists_isLatticeRational_of_offset_zero`). Hence for cones
rational-normal and rational polyhedrality coincide with lattice rationality
(`TauCeti.isRationalNormalPolyhedron_coe_iff`, `TauCeti.isRationalPolyhedron_coe_iff`).

The comparison allows lineality and bridges affine polyhedral cells and toric cones.

## Attribution

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Cone.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Convex/Polyhedron/Rational/Cone.lean
-/

public section

namespace TauCeti

open Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {i : N →+ V} {h : IsIntegralLattice i} {C : PointedCone ℝ V}

/-- The cone cut out by the linear parts of a rational-normal presentation is lattice rational. -/
theorem RationalAffinePolyhedron.exists_isLatticeRational_mem_iff_linear
    (P : RationalAffinePolyhedron h) :
    ∃ C : PointedCone ℝ V, IsLatticeRational i C ∧
      ∀ x, x ∈ C ↔ ∀ j, (P.inequality j).toAffineMap.linear x ≤ 0 := by
  classical
  let ℓ (j) : Module.Dual ℝ V := (P.inequality j).toAffineMap.linear
  refine ⟨PointedCone.dual
      (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
      ((Finset.univ.image fun j => -ℓ j : Finset (Module.Dual ℝ V)) : Set (Module.Dual ℝ V)),
    ?_, fun x => by simp [PointedCone.mem_dual, ℓ]⟩
  refine h.isLatticeRational_dual_of_isRationalFunctional _ fun f hf => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hf
  exact (P.rational_linear j).neg

/-- A rational-normal presentation with zero offsets cuts out a lattice-rational cone. -/
theorem RationalAffinePolyhedron.exists_isLatticeRational_of_offset_zero
    (P : RationalAffinePolyhedron h) (h0 : ∀ j, P.inequality j 0 = 0) :
    ∃ C : PointedCone ℝ V, (C : Set V) = P.carrier ∧ IsLatticeRational i C := by
  obtain ⟨C, hC, hmem⟩ := P.exists_isLatticeRational_mem_iff_linear
  refine ⟨C, ?_, hC⟩
  ext x
  rw [SetLike.mem_coe, hmem, RationalAffinePolyhedron.mem_carrier]
  refine forall_congr' fun j => ?_
  have hdec : P.inequality j x = (P.inequality j).toAffineMap.linear x + P.inequality j 0 :=
    (P.inequality j).toAffineMap.apply_eq_linear_add_apply_zero x
  rw [hdec, h0 j, add_zero]

/-- A rational-normal polyhedral cone is lattice rational. The affine offsets of the given
presentation may be arbitrary real numbers. -/
theorem IsRationalNormalPolyhedron.isLatticeRational
    (hC : IsRationalNormalPolyhedron h (C : Set V)) : IsLatticeRational i C := by
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp hC
  obtain ⟨C', hC', hmem⟩ := P.exists_isLatticeRational_mem_iff_linear
  have hlin := PointedCone.mem_iff_forall_linear_nonpos
    (fun j => (P.inequality j).toAffineMap) (C := C) (by
      rw [← hP]
      ext x
      exact RationalAffinePolyhedron.mem_carrier)
  convert hC' using 1
  ext x
  rw [hlin, hmem]

section Continuous

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

/-- A lattice-rational cone is presented by finitely many integral characters, with all offsets
zero. -/
theorem Toric.IsLatticeRational.exists_rationalAffinePolyhedron_offset_zero
    (hC : IsLatticeRational i C) (h : IsIntegralLattice i) :
    ∃ P : RationalAffinePolyhedron h, P.carrier = C ∧ ∀ j, P.inequality j 0 = 0 := by
  classical
  let _ := h.finiteDimensional
  obtain ⟨s, rfl⟩ := h.isLatticeRational_iff_exists_dual_image.mp hC
  let g (m : s) : V →ᴬ[ℝ] ℝ :=
    -(ContinuousLinearMap.toContinuousAffineMap
      ⟨h.realCharacter m.val, (h.realCharacter m.val).continuous_of_finiteDimensional⟩)
  have hg (m : s) : IsRationalFunctional h (g m).toAffineMap.linear :=
    (IsRationalFunctional.realCharacter h m.val.toIntLinearMap).neg
  refine ⟨RationalAffinePolyhedron.ofFinite g hg, ?_, fun j => ?_⟩
  · ext x
    rw [RationalAffinePolyhedron.mem_carrier_ofFinite]
    simp [PointedCone.mem_dual, g]
  · obtain ⟨m, hm⟩ := RationalAffinePolyhedron.exists_inequality_ofFinite hg j
    simp [hm, g]

/-- A lattice-rational cone is a rational polyhedron. -/
theorem Toric.IsLatticeRational.isRationalPolyhedron (hC : IsLatticeRational i C)
    (h : IsIntegralLattice i) : IsRationalPolyhedron h (C : Set V) := by
  obtain ⟨P, hP, h0⟩ := hC.exists_rationalAffinePolyhedron_offset_zero h
  refine isRationalPolyhedron_iff.mpr ⟨P, hP, ?_⟩
  exact RationalAffinePolyhedron.hasRationalOffsets_iff.mpr fun j => ⟨0, by simp [h0]⟩

end Continuous

section Continuous

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

/-- On pointed cones, rational-normal polyhedrality and lattice rationality agree. -/
theorem isRationalNormalPolyhedron_coe_iff :
    IsRationalNormalPolyhedron h (C : Set V) ↔ IsLatticeRational i C := by
  refine ⟨fun hC => hC.isLatticeRational, fun hC => ?_⟩
  exact (hC.isRationalPolyhedron h).isRationalNormalPolyhedron

/-- On pointed cones, rational polyhedrality, with rational offsets, and lattice rationality
agree. -/
theorem isRationalPolyhedron_coe_iff :
    IsRationalPolyhedron h (C : Set V) ↔ IsLatticeRational i C :=
  ⟨fun hC => hC.isRationalNormalPolyhedron.isLatticeRational,
    fun hC => hC.isRationalPolyhedron h⟩

end Continuous

end TauCeti
