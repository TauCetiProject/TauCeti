/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Geometry.Convex.Cone.FiniteGeneration
public import TauCeti.Geometry.Convex.Cone.Homogenization

/-!
# Homogenization of convex polyhedra

Homogenizing an affine inequality `g x ≤ 0` replaces `g` by the linear functional
`(x, t) ↦ g.contLinear x + t * g 0`, which equals `t * g (t⁻¹ • x)` for `t ≠ 0`. The
homogenization (`Set.homogenization`) of a nonempty solution set of finitely many affine
inequalities is the cone of all `(x, t)` with `t ≥ 0` satisfying the homogenized inequalities. This
holds for every presentation of the set, whether or not it is bounded and whether or not it has
lineality. In a finite-dimensional space it follows that the homogenization of a convex polyhedron
is a finitely generated cone, and that its height-zero slice, the asymptotic cone of the
polyhedron, is cut out by the linear parts of the inequalities.

Nonemptiness is essential for the description by inequalities: two presentations of the empty set
can have different homogeneous inequality cones, whereas the homogenization of the empty set is
always the zero cone.

## Main declarations

* `ContinuousAffineMap.homogenize`: the homogenized linear functional of an affine functional.
* `TauCeti.homogeneousInequalityCone`: the cone of `(x, t)` with `t ≥ 0` satisfying the
  homogenized inequalities of a finite family.
* `Set.homogenization_setOf_forall_eq`: the homogenization of a nonempty solution set is the
  homogeneous inequality cone of any presentation.
* `Set.asymptoticCone_setOf_forall`: the asymptotic cone of a nonempty solution set consists of
  the directions on which the linear parts of the inequalities are nonpositive.
* `TauCeti.IsConvexPolyhedron.fg_homogenization`: the homogenization of a convex polyhedron in a
  finite-dimensional space is a finitely generated cone.

## Provenance

Adapted from `Mei/Geometry/Convex/Homogenization/Inequalities.lean` and
`Mei/Geometry/Convex/Polyhedron/Homogenization/Inequalities.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, licensed under Apache 2.0.
-/

public section

open Set

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V]

namespace ContinuousAffineMap

/-- The linear functional on `V × ℝ` homogenizing an affine functional `g`: it sends `(x, t)` to
`g.contLinear x + t * g 0`. -/
def homogenize (g : V →ᴬ[ℝ] ℝ) : (V × ℝ) →L[ℝ] ℝ :=
  g.contLinear.comp (ContinuousLinearMap.fst ℝ V ℝ) + g 0 • ContinuousLinearMap.snd ℝ V ℝ

/-- At height `t`, homogenization adds `t` times the value of the affine functional at zero. -/
@[simp]
theorem homogenize_apply (g : V →ᴬ[ℝ] ℝ) (x : V) (t : ℝ) :
    g.homogenize (x, t) = g.contLinear x + t * g 0 := by
  simp [homogenize, mul_comm]

/-- At height one, the homogenized functional recovers the affine functional. -/
@[simp high] -- Apply before `homogenize_apply` expands the value into linear part and offset.
theorem homogenize_one (g : V →ᴬ[ℝ] ℝ) (x : V) : g.homogenize (x, (1 : ℝ)) = g x := by
  have h := g.map_vadd (0 : V) x
  simpa [homogenize_apply] using h.symm

/-- At a nonzero height `t`, the homogenized functional is `t` times the affine functional at
`t⁻¹ • x`. -/
theorem homogenize_apply_of_ne_zero (g : V →ᴬ[ℝ] ℝ) (x : V) {t : ℝ} (ht : t ≠ 0) :
    g.homogenize (x, t) = t * g (t⁻¹ • x) := by
  have heval : g (t⁻¹ • x) = t⁻¹ * g.contLinear x + g 0 := by
    simpa only [vadd_eq_add, add_zero, map_smul, smul_eq_mul,
      ContinuousAffineMap.coe_contLinear] using g.map_vadd 0 (t⁻¹ • x)
  rw [heval, homogenize_apply, mul_add, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

end ContinuousAffineMap

namespace TauCeti

/-- The cone of `(x, t)` with `t ≥ 0` satisfying the homogenized inequalities of the family `g`.
For a nonempty solution set of `g`, this is its homogenization
(`Set.homogenization_setOf_forall_eq`). -/
def homogeneousInequalityCone (g : ι → (V →ᴬ[ℝ] ℝ)) : PointedCone ℝ (V × ℝ) :=
  (PointedCone.positive ℝ ℝ).comap (LinearMap.snd ℝ V ℝ) ⊓
    ⨅ i, (PointedCone.positive ℝ ℝ).comap (-(g i).homogenize.toLinearMap)

/-- Membership in the homogeneous inequality cone records the height and every homogenized row. -/
@[simp]
theorem mem_homogeneousInequalityCone {g : ι → (V →ᴬ[ℝ] ℝ)} {z : V × ℝ} :
    z ∈ homogeneousInequalityCone g ↔ 0 ≤ z.2 ∧ ∀ i, (g i).homogenize z ≤ 0 := by
  simp [homogeneousInequalityCone]

/-- The homogeneous inequality cone is closed, being cut out by continuous functionals. -/
theorem isClosed_homogeneousInequalityCone (g : ι → (V →ᴬ[ℝ] ℝ)) :
    IsClosed (homogeneousInequalityCone g : Set (V × ℝ)) := by
  have : (homogeneousInequalityCone g : Set (V × ℝ)) =
      {z | 0 ≤ z.2} ∩ ⋂ i, {z | (g i).homogenize z ≤ 0} := by
    ext z
    simp
  rw [this]
  exact (isClosed_le continuous_const continuous_snd).inter
    (isClosed_iInter fun i => isClosed_le (g i).homogenize.continuous continuous_const)

end TauCeti

namespace Set

variable [ContinuousSMul ℝ V] [Finite ι]

/-- **Homogenization by inequalities.** The homogenization of a nonempty solution set of finitely
many affine inequalities is the homogeneous inequality cone of the family. -/
theorem homogenization_setOf_forall_eq (g : ι → (V →ᴬ[ℝ] ℝ))
    (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    homogenization {x : V | ∀ i, g i x ≤ 0} = TauCeti.homogeneousInequalityCone g := by
  have hpoly := TauCeti.isConvexPolyhedron_setOf_forall g
  obtain ⟨p, hp⟩ := hne
  refine le_antisymm ((homogenization_le_iff (TauCeti.isClosed_homogeneousInequalityCone g)).mpr
    fun x hx => ?_) fun ⟨x, t⟩ hz => ?_
  · simpa using hx
  · obtain ⟨ht, hrows⟩ := TauCeti.mem_homogeneousInequalityCone.mp hz
    rcases ht.eq_or_lt with rfl | ht
    · -- At height zero, every ray based at `p` stays in the polyhedron.
      refine mem_homogenization_zero_of_mem_asymptoticCone hpoly.convex hpoly.isClosed hp
        (mem_asymptoticCone_of_forall_add_smul_mem (p := p) fun s hs i => ?_)
      have hlin : (g i).contLinear x ≤ 0 := by simpa using hrows i
      have hval := (g i).map_vadd p (s • x)
      simp only [vadd_eq_add, map_smul, smul_eq_mul, ContinuousAffineMap.coe_contLinear] at hval
      rw [add_comm p, hval]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs hlin) (hp i)
    · refine (hpoly.convex.mem_homogenization_pos_iff hpoly.isClosed ht).mpr fun i => ?_
      have := hrows i
      rw [(g i).homogenize_apply_of_ne_zero x ht.ne'] at this
      exact nonpos_of_mul_nonpos_right this ht

/-- The membership criterion for the homogenization of a nonempty solution set: nonnegative height
and the homogenized inequalities. -/
theorem mem_homogenization_setOf_forall_iff {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty) {x : V} {t : ℝ} :
    (x, t) ∈ homogenization {x : V | ∀ i, g i x ≤ 0} ↔
      0 ≤ t ∧ ∀ i, (g i).homogenize (x, t) ≤ 0 := by
  rw [homogenization_setOf_forall_eq g hne, TauCeti.mem_homogeneousInequalityCone]

/-- **The asymptotic cone of a polyhedron.** For a nonempty solution set of finitely many affine
inequalities, a direction lies in the asymptotic cone iff the linear part of every inequality is
nonpositive on it. -/
theorem asymptoticCone_setOf_forall (g : ι → (V →ᴬ[ℝ] ℝ))
    (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    asymptoticCone ℝ {x : V | ∀ i, g i x ≤ 0} = {v | ∀ i, (g i).contLinear v ≤ 0} := by
  have hpoly := TauCeti.isConvexPolyhedron_setOf_forall g
  ext v
  rw [← hpoly.convex.mem_homogenization_zero_iff hne hpoly.isClosed,
    mem_homogenization_setOf_forall_iff hne]
  simp

end Set

namespace TauCeti

/-- **Homogenization of a convex polyhedron.** In a finite-dimensional Hausdorff space, the
homogenization of a convex polyhedron is a finitely generated cone. -/
theorem IsConvexPolyhedron.fg_homogenization [ContinuousSMul ℝ V] [T2Space V] [Module.Finite ℝ V]
    {P : Set V} (hP : IsConvexPolyhedron P) : P.homogenization.FG := by
  classical
  obtain ⟨n, g, rfl⟩ := isConvexPolyhedron_iff.mp hP
  rcases Set.eq_empty_or_nonempty {x : V | ∀ i, g i x ≤ 0} with h | hne
  · rw [h, homogenization_empty]
    exact Submodule.fg_bot
  · rw [homogenization_setOf_forall_eq g hne]
    -- The cone is cut out by the finitely many functionals `snd` and `-homogenize (g i)`.
    refine PointedCone.DualFG.fg (p := LinearMap.id)
      ⟨insert (LinearMap.snd ℝ V ℝ) (Finset.univ.image fun i => -(g i).homogenize.toLinearMap),
        ?_⟩
    ext z
    simp [PointedCone.mem_dual]

end TauCeti
