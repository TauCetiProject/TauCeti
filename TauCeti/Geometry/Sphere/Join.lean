/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.Topology.Join
import TauCeti.Analysis.Normed.Module.Ball

/-!
# The join of two spheres is a sphere

For real normed spaces `E` and `F`, the join of the unit spheres `S_E` and `S_F` maps to the unit
sphere of `E ⊕₂ F = WithLp 2 (E × F)` by

`[x, y, t] ↦ (√(1 - t) x, √t y)`

(`TauCeti.sphereJoinMap`): the segment of the join from `x` to `y` is sent to the quarter of a
great circle from `(x, 0)` to `(0, y)`. This map is always injective, and it is surjective when
`E` and `F` are nontrivial, since a unit vector `(a, b)` is `(√(1 - t) x, √t y)` for `t = ‖b‖²`
and unit vectors `x`, `y` in the directions of `a` and `b`. When `E` and `F` are moreover
finite-dimensional the join is compact, so the map is a homeomorphism
(`TauCeti.sphereJoinHomeomorph`). For Euclidean spaces this is `Sⁿ * Sᵐ ≃ₜ Sⁿ⁺ᵐ⁺¹`
(`TauCeti.euclideanSphereJoinHomeomorph`).

This identification is what turns a multiplication `μ : Sⁿ × Sⁿ → Sⁿ` into a map
`S²ⁿ⁺¹ ≃ₜ Sⁿ * Sⁿ → ΣSⁿ ≃ₜ Sⁿ⁺¹` by the Hopf construction `[x, y, t] ↦ [μ (x, y), t]`; for
the complex, quaternionic and octonionic multiplications this gives the Hopf maps.

Nontriviality is needed: if `F` is trivial its unit sphere is empty, so the join is empty, while
the unit sphere of `E ⊕₂ F` is that of `E`. Finite dimension makes the spheres, and hence the
join, compact, which is what makes the continuous bijection a homeomorphism.

## Main definitions

* `TauCeti.sphereJoinMap`: the map `[x, y, t] ↦ (√(1 - t) x, √t y)` from the join of the unit
  spheres of `E` and `F` to the unit sphere of `E ⊕₂ F`.
* `TauCeti.sphereJoinHomeomorph`: this map as a homeomorphism, for nontrivial finite-dimensional
  `E` and `F`.
* `TauCeti.euclideanSphereJoinHomeomorph`: `Sⁿ * Sᵐ ≃ₜ Sⁿ⁺ᵐ⁺¹` for the unit spheres of
  Euclidean spaces.

## Main results

* `TauCeti.injective_sphereJoinMap`, `TauCeti.surjective_sphereJoinMap`: the map is injective,
  and surjective when `E` and `F` are nontrivial.
* `TauCeti.coe_euclideanSphereJoinHomeomorph_mk_castAdd`,
  `TauCeti.coe_euclideanSphereJoinHomeomorph_mk_natAdd`: the coordinates of the image of
  `[x, y, t]` in `Sⁿ⁺ᵐ⁺¹` are those of `√(1 - t) x` followed by those of `√t y`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, where joins
  are introduced and the join of spheres is identified with a sphere.
* A. Hatcher, *Vector Bundles and K-Theory*, §2.3, on the Hopf construction from the join.
-/

public section

noncomputable section

open Metric WithLp unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- For unit vectors `x`, `y` and `t ∈ [0, 1]`, the vector `(√(1 - t) x, √t y)` of `E ⊕₂ F` is a
unit vector. -/
private theorem mem_sphere_toLp_sqrt_smul (x : sphere (0 : E) 1) (y : sphere (0 : F) 1)
    (t : I) : toLp 2 (√(1 - (t : ℝ)) • (x : E), √(t : ℝ) • (y : F)) ∈
      sphere (0 : WithLp 2 (E × F)) 1 := by
  have h := prod_norm_sq_eq_of_L2 (toLp 2 (√(1 - (t : ℝ)) • (x : E), √(t : ℝ) • (y : F)))
  simp only [toLp_fst, toLp_snd, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    norm_eq_of_mem_sphere, mul_one, Real.sq_sqrt (sub_nonneg.2 t.2.2), Real.sq_sqrt t.2.1,
    sub_add_cancel] at h
  rw [mem_sphere_zero_iff_norm]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- The map `[x, y, t] ↦ (√(1 - t) x, √t y)` from the join of the unit spheres of `E` and `F` to
the unit sphere of `E ⊕₂ F`. It is injective (`TauCeti.injective_sphereJoinMap`), surjective for
nontrivial `E` and `F` (`TauCeti.surjective_sphereJoinMap`), and a homeomorphism when they are
moreover finite-dimensional (`TauCeti.sphereJoinHomeomorph`). -/
def sphereJoinMap :
    C(Join (sphere (0 : E) 1) (sphere (0 : F) 1), sphere (0 : WithLp 2 (E × F)) 1) :=
  Join.lift
    { toFun p := ⟨toLp 2 (√(1 - (p.2.2 : ℝ)) • (p.1 : E), √(p.2.2 : ℝ) • (p.2.1 : F)),
        mem_sphere_toLp_sqrt_smul p.1 p.2.1 p.2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ((prod_continuous_toLp 2 E F).comp ?_) _
        fun_prop }
    (fun x y y' ↦ Subtype.ext <| by simp) (fun x x' y ↦ Subtype.ext <| by simp)

/-- The map `TauCeti.sphereJoinMap` sends `[x, y, t]` to `(√(1 - t) x, √t y)`. -/
@[simp]
theorem coe_sphereJoinMap_mk (x : sphere (0 : E) 1) (y : sphere (0 : F) 1) (t : I) :
    (sphereJoinMap (Join.mk x y t) : WithLp 2 (E × F)) =
      toLp 2 (√(1 - (t : ℝ)) • (x : E), √(t : ℝ) • (y : F)) := by
  simp [sphereJoinMap]

/-- The map from the join of the unit spheres to the unit sphere of `E ⊕₂ F` is injective. -/
theorem injective_sphereJoinMap : Function.Injective (sphereJoinMap (E := E) (F := F)) := by
  intro z z' h
  induction z using Join.ind with | h x y t => ?_
  induction z' using Join.ind with | h x' y' t' => ?_
  have hxy := congrArg (fun p : sphere (0 : WithLp 2 (E × F)) 1 ↦ ofLp (p : WithLp 2 (E × F))) h
  simp only [coe_sphereJoinMap_mk, ofLp_toLp, Prod.mk.injEq] at hxy
  obtain ⟨hx, hy⟩ := hxy
  have htt' : t = t' := by
    have h' := congrArg norm hy
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_eq_of_mem_sphere, mul_one] at h'
    exact Subtype.ext ((Real.sqrt_inj t.2.1 t'.2.1).1 h')
  subst htt'
  refine Join.mk_eq_mk_iff.2 ⟨rfl, fun ht ↦ Subtype.ext ?_, fun ht ↦ Subtype.ext ?_⟩
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h ↦ ht (Subtype.ext h)
    exact smul_right_injective E (Real.sqrt_ne_zero'.2 (sub_pos.2 hlt)) hx
  · have hlt : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 fun h ↦ ht (Subtype.ext h.symm)
    exact smul_right_injective F (Real.sqrt_ne_zero'.2 hlt) hy

/-- For nontrivial `E` and `F`, the map from the join of the unit spheres to the unit sphere of
`E ⊕₂ F` is surjective: a unit vector `(a, b)` is the image of `[x, y, ‖b‖²]` for unit vectors `x`
and `y` with `‖a‖ x = a` and `‖b‖ y = b`. -/
theorem surjective_sphereJoinMap [Nontrivial E] [Nontrivial F] :
    Function.Surjective (sphereJoinMap (E := E) (F := F)) := by
  rintro ⟨p, hp⟩
  have hnorm : ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 = 1 := by
    rw [← prod_norm_sq_eq_of_L2, mem_sphere_zero_iff_norm.1 hp, one_pow]
  obtain ⟨x, hx⟩ := exists_mem_sphere_norm_smul_eq p.fst
  obtain ⟨y, hy⟩ := exists_mem_sphere_norm_smul_eq p.snd
  have ht : ‖p.snd‖ ^ 2 ∈ I := ⟨by positivity, by nlinarith [sq_nonneg ‖p.fst‖]⟩
  have h1 : √(1 - ‖p.snd‖ ^ 2) = ‖p.fst‖ := by
    rw [← hnorm, add_sub_cancel_right, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨Join.mk x y ⟨_, ht⟩, Subtype.ext ?_⟩
  rw [coe_sphereJoinMap_mk]
  dsimp only
  rw [h1, Real.sqrt_sq (norm_nonneg _), hx, hy]
  -- `(p.fst, p.snd)` is `ofLp p` by eta for pairs, and `toLp 2 (ofLp p) = p`
  rfl

/-- For nontrivial finite-dimensional real normed spaces `E` and `F`, the join of their unit
spheres is homeomorphic to the unit sphere of `E ⊕₂ F` by `[x, y, t] ↦ (√(1 - t) x, √t y)`. -/
def sphereJoinHomeomorph [Nontrivial E] [Nontrivial F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] :
    Join (sphere (0 : E) 1) (sphere (0 : F) 1) ≃ₜ sphere (0 : WithLp 2 (E × F)) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨injective_sphereJoinMap, surjective_sphereJoinMap⟩)
    sphereJoinMap.continuous

/-- The homeomorphism `TauCeti.sphereJoinHomeomorph` is the map `TauCeti.sphereJoinMap`. -/
@[simp]
theorem coe_sphereJoinHomeomorph [Nontrivial E] [Nontrivial F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] : ⇑(sphereJoinHomeomorph (E := E) (F := F)) = sphereJoinMap :=
  (rfl)

/-- The join of the unit spheres `Sⁿ` and `Sᵐ` of Euclidean spaces is homeomorphic to the unit
sphere `Sⁿ⁺ᵐ⁺¹`: the point `[x, y, t]` goes to the vector whose first `n + 1` coordinates are those
of `√(1 - t) x` and whose last `m + 1` coordinates are those of `√t y`
(`TauCeti.coe_euclideanSphereJoinHomeomorph_mk_castAdd`,
`TauCeti.coe_euclideanSphereJoinHomeomorph_mk_natAdd`). It is `TauCeti.sphereJoinHomeomorph`
followed by the linear isometry `ℝⁿ⁺¹ ⊕₂ ℝᵐ⁺¹ ≃ ℝⁿ⁺ᵐ⁺²` concatenating coordinates. -/
def euclideanSphereJoinHomeomorph (n m : ℕ) :
    Join (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + m + 2))) 1 :=
  sphereJoinHomeomorph.trans
    ((PiLp.sumPiLpEquivProdLpPiLp 2 fun _ ↦ ℝ).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (finSumFinEquiv.trans (finCongr (by omega))))).unitSphereIsometryEquiv.toHomeomorph

variable {n m : ℕ}

/-- The first `n + 1` coordinates of the image of `[x, y, t]` under
`TauCeti.euclideanSphereJoinHomeomorph` are those of `√(1 - t) x`. -/
theorem coe_euclideanSphereJoinHomeomorph_mk_castAdd
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : I) (i : Fin (n + 1)) :
    (euclideanSphereJoinHomeomorph n m (Join.mk x y t) : EuclideanSpace ℝ (Fin (n + m + 2)))
        (Fin.cast (by omega) (Fin.castAdd (m + 1) i)) =
      √(1 - (t : ℝ)) * (x : EuclideanSpace ℝ (Fin (n + 1))) i := by
  simp [euclideanSphereJoinHomeomorph]

/-- The last `m + 1` coordinates of the image of `[x, y, t]` under
`TauCeti.euclideanSphereJoinHomeomorph` are those of `√t y`. -/
theorem coe_euclideanSphereJoinHomeomorph_mk_natAdd
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : I) (i : Fin (m + 1)) :
    (euclideanSphereJoinHomeomorph n m (Join.mk x y t) : EuclideanSpace ℝ (Fin (n + m + 2)))
        (Fin.cast (by omega) (Fin.natAdd (n + 1) i)) =
      √(t : ℝ) * (y : EuclideanSpace ℝ (Fin (m + 1))) i := by
  simp [euclideanSphereJoinHomeomorph]

end TauCeti
