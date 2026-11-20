/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Skeleton
import TauCeti.Analysis.Convex.Polyhedron.Rational.Direction
import TauCeti.LinearAlgebra.Dual.Kernel
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Transverse slices and integral normals at joints

At an intrinsic interior point of a cell of codimension `k`, the
codimension-at-least-`k` skeleton meets a suitable ball and a complementary
affine slice only at that point. The slice has dimension `k`. The same ball
misses the relative boundary and the other cells of the skeleton.

For a codimension-two cell, its direction is the common kernel of two
integral characters extended to the real ambient space. Contracting these
equations against a transverse lattice direction gives a nonzero integral
normal to the sum of the cell direction and that direction's line.
Neither construction requires the cell to contain a lattice point.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Joint.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

open Set Module

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A transverse lattice direction and a codimension-two cell determine a nonzero
integral normal whose real kernel is the sum of the cell direction and the lattice
direction's line. The two input characters can be chosen with independent real extensions. -/
theorem exists_joint_transverse_normal (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.cellsOfCodimension 2) (v : N) (hv : i v ∉ (affineSpan ℝ J).direction) :
    ∃ f g : N →+ ℤ, LinearIndependent ℝ ![h.realCharacter f, h.realCharacter g] ∧
      (affineSpan ℝ J).direction = (h.realCharacter f).ker ⊓ (h.realCharacter g).ker ∧
      f v • g - g v • f ≠ 0 ∧
      (h.realCharacter (f v • g - g v • f)).ker =
        (affineSpan ℝ J).direction ⊔ ℝ ∙ i v := by
  let := h.finiteDimensional
  obtain ⟨hcell, hdim⟩ := mem_cellsOfCodimension.mp hJ
  obtain ⟨f, g, hind, hfg⟩ :=
    (C.rational J hcell).exists_direction_eq_inf_ker (C.nonempty J hcell) hdim
  have hreal : h.realCharacter (f v • g - g v • f) =
      h.realCharacter f (i v) • h.realCharacter g -
        h.realCharacter g (i v) • h.realCharacter f := by
    ext w
    simp
  have hker : (h.realCharacter (f v • g - g v • f)).ker =
      (affineSpan ℝ J).direction ⊔ ℝ ∙ i v := by
    rw [hreal, LinearMap.ker_apply_smul_sub_apply_smul _ _ (hfg ▸ hv), ← hfg]
  refine ⟨f, g, hind, hfg, ?_, hker⟩
  intro he
  have htop : (affineSpan ℝ J).direction ⊔ ℝ ∙ i v = ⊤ := by
    simpa only [he, map_zero, LinearMap.ker_zero] using hker.symm
  have hsup := Submodule.finrank_sup_span_singleton hv
  rw [htop, finrank_top] at hsup
  omega

/-- At a relative interior point of a codimension-`k` cell there are a ball and a
`k`-dimensional complementary slice in which the whole skeleton of codimension at least
`k` consists of the center alone. The ball avoids the cell's relative boundary and the
other skeleton cells, and meets only cells containing the chosen cell. -/
theorem exists_ball_transverse_slice (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∃ (r : ℝ) (W : Submodule ℝ V), 0 < r ∧
      IsCompl (affineSpan ℝ P).direction W ∧ finrank ℝ W = k ∧
      (Metric.ball x r ∩ (AffineSubspace.mk' x W : Set V)) ∩
        (C.codimensionGE k).support = {x} ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ P) ∧
      (∀ Q ∈ (C.codimensionGE k).cells, Q ≠ P → Disjoint (Metric.ball x r) Q) ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hskeleton, hfrontier, hother, hcells⟩ :=
    C.exists_ball_inter_support_codimensionGE_eq hP hx
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (affineSpan ℝ P).direction
  have hdimP := (mem_cellsOfCodimension.mp hP).2
  have hdimW := Submodule.finrank_add_eq_of_isCompl hW
  have hxP := intrinsicInterior_subset hx
  have hxA := subset_affineSpan ℝ P hxP
  have hxW : x ∈ (AffineSubspace.mk' x W : Set V) := AffineSubspace.self_mem_mk' x W
  obtain ⟨p, hp⟩ := AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl
    (s₁ := affineSpan ℝ P) (s₂ := AffineSubspace.mk' x W) ⟨x, hxA⟩ ⟨x, hxW⟩
    (by simpa only [AffineSubspace.direction_mk'] using hW)
  have hxp : x = p := Set.mem_singleton_iff.mp (hp ▸ ⟨hxA, hxW⟩)
  subst p
  refine ⟨r, W, hr, hW, by omega, ?_, hfrontier, hother, hcells⟩
  ext y
  constructor
  · rintro ⟨⟨hyball, hyW⟩, hys⟩
    have hyP : y ∈ Metric.ball x r ∩ P := hskeleton ▸ ⟨hyball, hys⟩
    exact hp ▸ ⟨subset_affineSpan ℝ P hyP.2, hyW⟩
  · intro hy
    have hyx := Set.mem_singleton_iff.mp hy
    subst y
    have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    have hxs : x ∈ Metric.ball x r ∩ (C.codimensionGE k).support :=
      hskeleton.symm ▸ ⟨hxball, hxP⟩
    exact ⟨⟨hxball, hxW⟩, hxs.2⟩

end TauCeti.FinitePolyhedralComplex
