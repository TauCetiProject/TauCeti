/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Topology.Join

import TauCeti.Analysis.Normed.Module.Normalize

/-!
# The join of two spheres is a sphere

For real normed spaces `E` and `F`, the map `[x, y, t] ↦ (√(1 - t) • x, √t • y)` sends the join of
the unit spheres of `E` and `F` into the unit sphere of the `L²` product `WithLp 2 (E × F)`, since
`(1 - t) + t = 1`. It is always injective, and surjective when both spheres are nonempty, that is
when `E` and `F` are nontrivial. When `E` and `F` are finite dimensional the join is compact and
the sphere is Hausdorff, so this bijection is a homeomorphism. For Euclidean spheres this is
`Sⁿ * Sᵐ ≅ Sⁿ⁺ᵐ⁺¹`, the identification through which the Hopf construction of a map
`Sⁿ × Sⁿ → Sⁿ` lands on `S²ⁿ⁺¹`.

## Main declarations

* `TauCeti.sphereJoinMap`: the continuous map
  `Join (sphere (0 : E) 1) (sphere (0 : F) 1) → sphere (0 : WithLp 2 (E × F)) 1`.
* `TauCeti.sphereJoinMap_injective`, `TauCeti.sphereJoinMap_surjective`: it is bijective.
* `TauCeti.sphereJoinHomeomorph`: for finite-dimensional `E` and `F`, the homeomorphism of the
  join of the unit spheres with the unit sphere of `WithLp 2 (E × F)`.
* `TauCeti.euclideanSphereJoinHomeomorph`: the homeomorphism `Sⁿ * Sᵐ ≃ₜ Sⁿ⁺ᵐ⁺¹` of unit spheres
  in Euclidean spaces, splitting the coordinates of `ℝⁿ⁺ᵐ⁺²` as `ℝⁿ⁺¹ × ℝᵐ⁺¹`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, *Operations on Spaces*, the join `X * Y`.
* A. Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf),
  §2.3, the Hopf construction.
-/

public section

noncomputable section

namespace TauCeti

open Metric unitInterval WithLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The map `(x, y, t) ↦ (√(1 - t) • x, √t • y)` from `Sᴱ × Sᶠ × I` to the unit sphere of the `L²`
product, before passing to the join. -/
private def sphereJoinMapAux :
    C(sphere (0 : E) 1 × sphere (0 : F) 1 × I, sphere (0 : WithLp 2 (E × F)) 1) where
  toFun p := ⟨toLp 2 (√(1 - (p.2.2 : ℝ)) • (p.1 : E), √(p.2.2 : ℝ) • (p.2.1 : F)), by
    -- The squared norms of the two components are `1 - t` and `t`.
    have h1 : 0 ≤ 1 - (p.2.2 : ℝ) := sub_nonneg.2 (le_one p.2.2)
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      prod_norm_sq_eq_of_L2]
    simp only [toLp_fst, toLp_snd, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_eq_of_mem_sphere, mul_one, Real.sq_sqrt h1,
      Real.sq_sqrt (nonneg p.2.2)]
    ring⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((prod_continuous_toLp 2 E F).comp ?_) _
    fun_prop

/-- The map `[x, y, t] ↦ (√(1 - t) • x, √t • y)` from the join of the unit spheres of `E` and `F`
to the unit sphere of `WithLp 2 (E × F)`. It is a homeomorphism when `E` and `F` are nontrivial and
finite dimensional (`TauCeti.sphereJoinHomeomorph`). -/
def sphereJoinMap :
    C(Join (sphere (0 : E) 1) (sphere (0 : F) 1), sphere (0 : WithLp 2 (E × F)) 1) :=
  Join.lift sphereJoinMapAux
    (fun x y y' => Subtype.ext <| by simp [sphereJoinMapAux])
    (fun x x' y => Subtype.ext <| by simp [sphereJoinMapAux])

@[simp]
theorem coe_sphereJoinMap_mk (x : sphere (0 : E) 1) (y : sphere (0 : F) 1) (t : I) :
    (sphereJoinMap (Join.mk _ _ (x, y, t)) : WithLp 2 (E × F)) =
      toLp 2 (√(1 - (t : ℝ)) • (x : E), √(t : ℝ) • (y : F)) := by
  simp [sphereJoinMap, sphereJoinMapAux]

/-- The map from the join of two spheres to the sphere of the `L²` product is injective. -/
theorem sphereJoinMap_injective :
    Function.Injective (sphereJoinMap (E := E) (F := F)) := by
  intro a b hab
  induction a using Join.ind with | h p => ?_
  induction b using Join.ind with | h q => ?_
  obtain ⟨x, y, s⟩ := p
  obtain ⟨x', y', t⟩ := q
  have h := congrArg (fun z : sphere (0 : WithLp 2 (E × F)) 1 => ofLp (z : WithLp 2 (E × F))) hab
  simp only [coe_sphereJoinMap_mk, ofLp_toLp, Prod.mk.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hst : s = t := by
    have := congrArg norm hy
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_eq_of_mem_sphere, mul_one] at this
    exact Subtype.ext ((Real.sqrt_inj (nonneg s) (nonneg t)).1 this)
  subst hst
  refine Join.mk_eq_mk_iff.2 ⟨rfl, fun hs => Subtype.ext ?_, fun hs => Subtype.ext ?_⟩
  · refine smul_right_injective E (Real.sqrt_ne_zero'.2 ?_) hx
    exact sub_pos.2 (lt_of_le_of_ne (le_one s) fun h => hs (Subtype.ext h))
  · refine smul_right_injective F (Real.sqrt_ne_zero'.2 ?_) hy
    exact lt_of_le_of_ne (nonneg s) fun h => hs (Subtype.ext h.symm)

/-- The map from the join of the unit spheres of nontrivial spaces to the sphere of the `L²`
product is surjective. -/
theorem sphereJoinMap_surjective [Nontrivial E] [Nontrivial F] :
    Function.Surjective (sphereJoinMap (E := E) (F := F)) := by
  rintro ⟨p, hp⟩
  have hn : ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 = 1 := by
    rw [← prod_norm_sq_eq_of_L2, mem_sphere_zero_iff_norm.1 hp, one_pow]
  obtain ⟨e⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one |>.coe_sort
  obtain ⟨e'⟩ := (NormedSpace.sphere_nonempty (x := (0 : F)) (r := 1)).2 zero_le_one |>.coe_sort
  have ht : ‖p.snd‖ ^ 2 ∈ I := ⟨by positivity, by nlinarith [sq_nonneg ‖p.fst‖]⟩
  refine ⟨Join.mk _ _ (sphereDirection e p.fst, sphereDirection e' p.snd, ⟨_, ht⟩), Subtype.ext ?_⟩
  rw [coe_sphereJoinMap_mk]
  have h1 : 1 - ‖p.snd‖ ^ 2 = ‖p.fst‖ ^ 2 := by linarith
  simp only [h1, Real.sqrt_sq (norm_nonneg _), norm_smul_sphereDirection]
  -- `toLp 2 (p.fst, p.snd) = p` is the eta law of the product and of `WithLp`.
  rfl

theorem sphereJoinMap_bijective [Nontrivial E] [Nontrivial F] :
    Function.Bijective (sphereJoinMap (E := E) (F := F)) :=
  ⟨sphereJoinMap_injective, sphereJoinMap_surjective⟩

variable [Nontrivial E] [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

variable (E F) in
/-- **The join of two spheres is a sphere.** For nontrivial finite-dimensional real normed spaces
`E` and `F`, the map `[x, y, t] ↦ (√(1 - t) • x, √t • y)` is a homeomorphism from the join of the
unit spheres of `E` and `F` to the unit sphere of `WithLp 2 (E × F)`. -/
def sphereJoinHomeomorph :
    Join (sphere (0 : E) 1) (sphere (0 : F) 1) ≃ₜ sphere (0 : WithLp 2 (E × F)) 1 :=
  sphereJoinMap.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ sphereJoinMap_bijective)

@[simp]
theorem coe_sphereJoinHomeomorph : ⇑(sphereJoinHomeomorph E F) = sphereJoinMap := (rfl)

/-- **The join `Sⁿ * Sᵐ` is `Sⁿ⁺ᵐ⁺¹`.** The homeomorphism sends `[x, y, t]` to the unit vector of
`ℝⁿ⁺ᵐ⁺²` whose first `n + 1` coordinates are those of `√(1 - t) • x` and whose last `m + 1`
coordinates are those of `√t • y`. -/
def euclideanSphereJoinHomeomorph (n m : ℕ) :
    Join (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + m + 1 + 1))) 1 :=
  -- Split `ℝⁿ⁺ᵐ⁺²` isometrically as the `L²` product of its first `n + 1` and last `m + 1`
  -- coordinates, and restrict the inverse splitting to the unit spheres.
  (sphereJoinHomeomorph _ _).trans <|
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((finCongr (by omega)).trans finSumFinEquiv.symm)).trans
        (PiLp.sumPiLpEquivProdLpPiLp 2 fun _ => ℝ)).symm.toHomeomorph.subtype fun z => by simp

/-- The first `n + 1` coordinates of the image of `[x, y, t]` in `Sⁿ⁺ᵐ⁺¹` are those of
`√(1 - t) • x`. -/
@[simp]
theorem euclideanSphereJoinHomeomorph_apply_castAdd (n m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : I) (i : Fin (n + 1)) :
    (euclideanSphereJoinHomeomorph n m (Join.mk _ _ (x, y, t)) :
        EuclideanSpace ℝ (Fin (n + m + 1 + 1))) (Fin.cast (by omega) (Fin.castAdd (m + 1) i)) =
      √(1 - (t : ℝ)) * (x : EuclideanSpace ℝ (Fin (n + 1))) i := by
  simp [euclideanSphereJoinHomeomorph]

/-- The last `m + 1` coordinates of the image of `[x, y, t]` in `Sⁿ⁺ᵐ⁺¹` are those of `√t • y`. -/
@[simp]
theorem euclideanSphereJoinHomeomorph_apply_natAdd (n m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : I) (i : Fin (m + 1)) :
    (euclideanSphereJoinHomeomorph n m (Join.mk _ _ (x, y, t)) :
        EuclideanSpace ℝ (Fin (n + m + 1 + 1))) (Fin.cast (by omega) (Fin.natAdd (n + 1) i)) =
      √(t : ℝ) * (y : EuclideanSpace ℝ (Fin (m + 1))) i := by
  simp [euclideanSphereJoinHomeomorph]

end TauCeti
