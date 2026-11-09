/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import TauCeti.Geometry.Toric.Algebraic.Cone.RationalDuality

/-!
# Rational-normal polyhedral cones

A pointed cone has a rational-normal affine inequality presentation exactly when it is generated
by finitely many lattice vectors (rational Minkowski–Weyl,
`TauCeti.Toric.IsIntegralLattice.isLatticeRational_iff_exists_dual_image`). The offsets of a
presentation need not be rational: a cone is stable under nonnegative scaling, which forces every
inequality of a presentation to be homogeneous, so the linear parts alone cut out the cone
(`TauCeti.IsRationalNormalPolyhedron.isLatticeRational`). Conversely a lattice-rational cone is
cut out by integral characters, a presentation with rational (indeed zero) offsets. Hence for
cones rational-normal and rational polyhedrality coincide with lattice rationality.

The comparison allows lineality and bridges affine polyhedral cells and toric cones.

## Attribution

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Cone.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Convex/Polyhedron/Rational/Cone.lean
-/

public section

namespace TauCeti

open Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i} {C : PointedCone ℝ V}

/-- A lattice-rational cone is a rational polyhedron: it is cut out by finitely many integral
characters, whose offsets all vanish. -/
theorem Toric.IsLatticeRational.isRationalPolyhedron (hC : IsLatticeRational i C)
    (h : IsIntegralLattice i) : IsRationalPolyhedron h (C : Set V) := by
  classical
  let _ := h.finiteDimensional
  obtain ⟨s, rfl⟩ := h.isLatticeRational_iff_exists_dual_image.mp hC
  let g (m : s) : V →ᴬ[ℝ] ℝ :=
    -(ContinuousLinearMap.toContinuousAffineMap
      ⟨h.realCharacter m.val, (h.realCharacter m.val).continuous_of_finiteDimensional⟩)
  have hg (m : s) : IsRationalFunctional h (g m).toAffineMap.linear :=
    (IsRationalFunctional.realCharacter h m.val.toIntLinearMap).neg
  refine isRationalPolyhedron_iff.mpr ⟨RationalAffinePolyhedron.ofFinite g hg, ?_,
    (RationalAffinePolyhedron.hasRationalOffsets_ofFinite_iff hg).mpr fun m => ⟨0, by simp [g]⟩⟩
  ext x
  rw [RationalAffinePolyhedron.mem_carrier_ofFinite]
  simp [PointedCone.mem_dual, g]

/-- A rational-normal polyhedral cone is lattice rational. The affine offsets of the given
presentation may be arbitrary real numbers: since the cone is stable under nonnegative scaling,
its inequalities are cut out by their linear parts alone. -/
theorem IsRationalNormalPolyhedron.isLatticeRational
    (hC : IsRationalNormalPolyhedron h (C : Set V)) : IsLatticeRational i C := by
  classical
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp hC
  -- The inequalities are `ℓ j x + c j ≤ 0` with `c j ≤ 0` because `0 ∈ C`.
  let ℓ (j) : Module.Dual ℝ V := (P.inequality j).toAffineMap.linear
  have hdec (j) (x : V) : P.inequality j x = ℓ j x + P.inequality j 0 := by
    simpa [ℓ] using congrFun (P.inequality j).toAffineMap.decomp x
  have hc (j) : P.inequality j 0 ≤ 0 := by
    have : (0 : V) ∈ P.carrier := hP ▸ C.zero_mem
    exact RationalAffinePolyhedron.mem_carrier.mp this j
  have hlin (x : V) : x ∈ C ↔ ∀ j, ℓ j x ≤ 0 := by
    refine ⟨fun hx j => ?_, fun hx => ?_⟩
    · -- Otherwise the inequality fails on a large multiple of `x`.
      by_contra hle
      have hpos := not_le.mp hle
      have hmem : ((1 - P.inequality j 0) / ℓ j x) • x ∈ P.carrier :=
        hP ▸ C.smul_mem (div_nonneg (by linarith [hc j]) hpos.le) hx
      have := RationalAffinePolyhedron.mem_carrier.mp hmem j
      rw [hdec, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    · rw [← SetLike.mem_coe, ← hP, RationalAffinePolyhedron.mem_carrier]
      intro j
      linarith [hdec j x, hx j, hc j]
  have heq : C = PointedCone.dual
      (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
      ((Finset.univ.image fun j => -ℓ j : Finset (Module.Dual ℝ V)) : Set (Module.Dual ℝ V)) := by
    ext x
    simp [PointedCone.mem_dual, hlin]
  rw [heq]
  refine h.isLatticeRational_dual_of_isRationalFunctional _ fun f hf => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hf
  exact (P.rational_linear j).neg

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

end TauCeti
