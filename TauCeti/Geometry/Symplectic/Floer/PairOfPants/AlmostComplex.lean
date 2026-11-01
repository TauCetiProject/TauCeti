/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Cayley
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Domain-dependent almost complex structures on the pair of pants

The pair-of-pants product counts solutions of `(du - X_K)^{0,1} = 0` for an almost complex
structure `J_z` depending on the point `z` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`. On the
cylindrical end `q`, far out, `J_z` must be the time-dependent structure `J_q(t)` already chosen
for the Floer complex of that end, just as the perturbation must be `H_q(t) dt` there
(`TauCeti.Floer.pairOfPantsPerturbation`). This file constructs such a structure, tame or
compatible, from any three period-one families of structures on the ends.

The structures act on a fixed symplectic vector space `(V, ω)` and may also depend on a point `x`
of a manifold `M` (for a vector space target, `M = V`). Fix an `ω`-compatible base structure
`J₀`. The Cayley transform `J ↦ -(1 + J₀ J)(1 - J₀ J)⁻¹` identifies the `ω`-tame structures with
the Cayley ball, a convex set containing `0 = cayley J₀`, and the `ω`-compatible ones with the
convex compatible Cayley ball (`TauCeti.SymplecticForm.Compatible.cayleyEquiv`,
`TauCeti.SymplecticForm.Compatible.cayley_mem_compatibleCayleyBall_iff`). The structure
`TauCeti.Floer.pairOfPantsAlmostComplex` is the inverse Cayley transform of

`∑ q, β(±s_q(w) - 1) • cayley (J_q(t_q(w), x))`,

where `(s_q, t_q)` are the coordinates of the end `q`, the sign is that of the end, and `β` is the
smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. The cutoffs of distinct ends have
disjoint supports, so at each point at most one term is nonzero, and it is a point of the segment
from `0` to the Cayley transform of a tame (or compatible) structure. The results are:

* `TauCeti.Floer.tames_pairOfPantsAlmostComplex` and
  `TauCeti.Floer.compatible_pairOfPantsAlmostComplex`: the structure is `ω`-tame, and it is
  `ω`-compatible when the end structures are.
* `TauCeti.Floer.cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos`: on the part `±s > 0`
  of the end `q`, its Cayley transform is `β(±s - 1) • cayley (J_q(t, x))`.
* `TauCeti.Floer.pairOfPantsAlmostComplex_cylindricalEndLift`: on the part `±s ≥ 2` of the end
  `q`, it is `J_q(t, x)`.
* `TauCeti.Floer.exists_cylindricalEndLift_of_pairOfPantsAlmostComplex_ne`: it is `J₀` off the
  parts `±s > 1` of the three ends.
* `TauCeti.Floer.contMDiffAt_pairOfPantsAlmostComplex`: for `C^n` families of period one, it is
  `C^n` on `S × M`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the contractibility of the spaces of tame and compatible structures.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data on punctured surfaces that agree with the Floer data on the ends.
-/

public noncomputable section

open Set Real Manifold Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {M : Type*}

omit [FiniteDimensional ℝ V] in
/-- If the Cayley transforms of all the end structures lie in a convex set containing `0`, so does
the cutoff-weighted sum of the Cayley transforms: at most one cutoff is nonzero at each point. -/
private theorem sum_smul_cayley_mem {s : Set (Module.End ℝ V)} (hs : Convex ℝ s)
    (h0 : (0 : Module.End ℝ V) ∈ s) {J : Puncture → ℝ → M → AlmostComplexStructure V}
    (hJ : ∀ q t x, J₀.cayley (J q t x) ∈ s) (w : ℂ) (x : M) :
    ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
      J₀.cayley (J q (q.endCoord w).im x) ∈ s := by
  by_cases h : ∃ q : Puncture, smoothTransition (q.endSign * (q.endCoord w).re - 1) ≠ 0
  · obtain ⟨q, hq⟩ := h
    obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hq
    rw [Finset.sum_eq_single q]
    · exact hs.smul_mem_of_zero_mem h0 (hJ _ _ _)
        ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
    · intro r _ hr
      have hr' := smoothTransition_endCoord_cylindricalEndLift_eq_zero hr
        (z := q.endCoord w) (by linarith)
      rw [q.cylindricalEndLift_endCoord hw] at hr'
      simp [hr']
    · simp
  · push Not at h
    simpa [h] using h0

/-- The domain-dependent almost complex structure on the pair of pants given by families
`J q t x` of `ω`-tame structures on its three ends, relative to an `ω`-compatible base structure
`J₀`. At `w ∈ ℂ` and `x ∈ M` it is the inverse Cayley transform, relative to `J₀`, of
`∑ q, β(±s_q(w) - 1) • cayley (J q (t_q(w)) x)`, where `(s_q, t_q)` are the coordinates of the end
`q` and `β` is the smooth transition function. It is `J q t x` far out on the end `q` and `J₀` off
the ends. -/
def pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (w : ℂ) (x : M) : AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        J₀.cayley (J q (q.endCoord w).im x),
      sum_smul_cayley_mem h₀.tames.convex_cayleyBall h₀.tames.zero_mem_cayleyBall
        (fun q t x => h₀.cayley_mem_cayleyBall (hJ q t x)) w x⟩

variable {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}

/-- The pair-of-pants structure is tamed by `ω`. -/
theorem tames_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (pairOfPantsAlmostComplex h₀ J hJ w x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the pair-of-pants structure, relative to `J₀`, is the cutoff-weighted
sum `∑ q, β(±s_q(w) - 1) • cayley (J q (t_q(w)) x)`. This characterizes the structure, since the
Cayley transform is injective on tame structures. -/
theorem cayley_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (pairOfPantsAlmostComplex h₀ J hJ w x) =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        J₀.cayley (J q (q.endCoord w).im x) := by
  rw [pairOfPantsAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The pair-of-pants structure is `ω`-compatible when the structures on the ends are. -/
theorem compatible_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (w : ℂ) (x : M) :
    ω.Compatible (pairOfPantsAlmostComplex h₀ J hJ w x) := by
  refine (h₀.cayley_mem_compatibleCayleyBall_iff (tames_pairOfPantsAlmostComplex h₀ w x)).mp ?_
  rw [cayley_pairOfPantsAlmostComplex]
  exact sum_smul_cayley_mem h₀.tames.convex_compatibleCayleyBall
    h₀.tames.zero_mem_compatibleCayleyBall
    (fun q t x => (h₀.cayley_mem_compatibleCayleyBall_iff (hJ q t x)).mpr (hJc q t x)) w x

variable {q : Puncture}

/-- **The structure on an end.** On the part `±s > 0` of the end `q`, the Cayley transform of the
pair-of-pants structure at the point with end coordinates `z = s + i t` is
`β(±s - 1) • cayley (J q t x)`: the structure moves along the segment of the Cayley ball from
`J₀` to `J q t x`. -/
theorem cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : M) :
    J₀.cayley (pairOfPantsAlmostComplex h₀ J hJ (q.cylindricalEndLift z) x) =
      smoothTransition (q.endSign * z.re - 1) • J₀.cayley (J q z.im x) := by
  rw [cayley_pairOfPantsAlmostComplex, Finset.sum_eq_single q]
  · obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
    have hre : (q.endCoord (q.cylindricalEndLift z)).re = z.re := by simp [hk]
    have him : (q.endCoord (q.cylindricalEndLift z)).im = z.im + k := by simp [hk]
    have hp : J q (z.im + k) = J q z.im := by simpa using hJp.int_mul k z.im
    rw [hre, him, hp]
  · intro r _ hr
    simp [smoothTransition_endCoord_cylindricalEndLift_eq_zero hr hz]
  · simp

/-- **The structure is `J q t` far out on each end.** On the part `±s ≥ 2` of the end `q`, the
pair-of-pants structure at the point with end coordinates `z = s + i t` is `J q t x`. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) (x : M) :
    pairOfPantsAlmostComplex h₀ J hJ (q.cylindricalEndLift z) x = J q z.im x := by
  rw [← h₀.cayley_inj (tames_pairOfPantsAlmostComplex h₀ _ x) (hJ q z.im x),
    cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos h₀ hJp (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_smul]

/-- The pair-of-pants structure differs from `J₀` only on the parts `±s > 1` of the three ends. -/
theorem exists_cylindricalEndLift_of_pairOfPantsAlmostComplex_ne (h₀ : ω.Compatible J₀)
    {w : ℂ} {x : M} (h : pairOfPantsAlmostComplex h₀ J hJ w x ≠ J₀) :
    ∃ (q : Puncture) (z : ℂ), 1 < q.endSign * z.re ∧ q.cylindricalEndLift z = w := by
  by_contra! hne
  refine h ((h₀.cayley_inj (tames_pairOfPantsAlmostComplex h₀ w x) h₀.tames).mp ?_)
  rw [cayley_pairOfPantsAlmostComplex, AlmostComplexStructure.cayley_self]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hc : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0
  · simp [hc]
  · obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hc
    exact absurd (q.cylindricalEndLift_endCoord hw) (hne q _ h₁)

section Smooth

/-! ### Smoothness -/

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- The Cayley transforms `-(1 + J₀ J)(1 - J₀ J)⁻¹` of a `C^n` family of `ω`-tame structures on
an end form a `C^n` family of continuous linear maps, since `1 - J₀ J` is invertible. -/
private theorem contMDiff_cayley (h₀ : ω.Compatible J₀) (q : Puncture) {n : ℕ∞}
    (hJq : ∀ t x, ω.Tames (J q t x))
    (hJs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => Module.End.toContinuousLinearMap V (J q p.1 p.2).toLinearMap)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => Module.End.toContinuousLinearMap V (J₀.cayley (J q p.1 p.2))) := by
  set e := Module.End.toContinuousLinearMap (𝕜 := ℝ) V
  set j : ℝ × M → V →L[ℝ] V := fun p => e (J q p.1 p.2).toLinearMap
  have hC : (fun p : ℝ × M => e (J₀.cayley (J q p.1 p.2))) =
      fun p => -(1 + e J₀.toLinearMap * j p) * Ring.inverse (1 - e J₀.toLinearMap * j p) := by
    funext p
    rw [AlmostComplexStructure.cayley_def, map_neg, map_mul, map_ringInverse, map_add, map_sub,
      map_one, map_mul, neg_mul]
  intro p
  have hu : IsUnit (1 - e J₀.toLinearMap * j p) := by
    have := (h₀.tames.isUnit_one_sub_mul (hJq p.1 p.2)).map e
    rwa [map_sub, map_one, map_mul] at this
  rw [hC]
  exact ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).neg.mul
    ((contDiffAt_ringInverse ℝ hu.unit).comp (j p)
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)))).comp_contMDiffAt
    (f := j) (hJs p)

/-- **The structure is smooth.** For families `J q t x` of `ω`-tame structures which have period
one in `t` and are `C^n` on `ℝ × M`, the pair-of-pants structure is `C^n` on `S × M`, where
`S = ℂ ∖ {0, 1}` is the thrice-punctured sphere. -/
theorem contMDiffAt_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap))
    (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × M =>
        (pairOfPantsAlmostComplex h₀ J hJ p.1 p.2).toLinearMap.toContinuousLinearMap)
      ((w : ℂ), x) := by
  -- Pass to the algebra equivalence `Module.End.toContinuousLinearMap`, which is
  -- `LinearMap.toContinuousLinearMap` as a function, to move products and inverses across.
  have he (f : V →ₗ[ℝ] V) :
      LinearMap.toContinuousLinearMap f = Module.End.toContinuousLinearMap V f := rfl
  simp_rw [he] at hJs ⊢
  set e := Module.End.toContinuousLinearMap (𝕜 := ℝ) V
  -- The cutoff-weighted sum of the Cayley transforms of the end structures is the Cayley
  -- transform `C` of the pair-of-pants structure.
  set C : ℂ × M → V →L[ℝ] V := fun p =>
    ∑ q, smoothTransition (q.endSign * (q.endCoord p.1).re - 1) •
      e (J₀.cayley (J q (q.endCoord p.1).im p.2)) with hC_def
  have hC (p : ℂ × M) : C p = e (J₀.cayley (pairOfPantsAlmostComplex h₀ J hJ p.1 p.2)) := by
    simp only [hC_def, cayley_pairOfPantsAlmostComplex, map_sum, map_smul]
  -- The structure is the inverse Cayley transform `J₀ (1 + C)(1 - C)⁻¹` of `C`.
  have hJC : (fun p : ℂ × M => e (pairOfPantsAlmostComplex h₀ J hJ p.1 p.2).toLinearMap) =
      fun p => e J₀.toLinearMap * (1 + C p) * Ring.inverse (1 - C p) := by
    funext p
    rw [hC, h₀.toLinearMap_eq_mul_ringInverse (tames_pairOfPantsAlmostComplex h₀ p.1 p.2),
      map_mul, map_mul, map_add, map_one, map_ringInverse, map_sub, map_one]
  -- `C` is smooth: the cutoffs are smooth, and periodicity makes the Cayley transforms of the
  -- end structures smooth functions of the angular coordinate.
  have hCs : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, V →L[ℝ] V) n C ((w : ℂ), x) := by
    refine contMDiffAt_finsetSum fun q _ => ?_
    have hw : (w : ℂ) ≠ q.endCenter := ne_endCenter w.2 q
    have hc : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℝ) n
        (fun p : ℂ × M => smoothTransition (q.endSign * (q.endCoord p.1).re - 1)) ((w : ℂ), x) :=
      (smoothTransition.contDiff.contDiffAt.comp (w : ℂ)
        ((contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).sub
          contDiffAt_const)).contMDiffAt.comp ((w : ℂ), x) contMDiffAt_fst
    have hFp : Function.Periodic (fun t y => e (J₀.cayley (J q t y))) 1 := fun t => by
      simp only [hJp q t]
    exact hc.smul (q.contMDiffAt_comp_im_endCoord hFp (contMDiff_cayley h₀ q (hJ q) (hJs q)) hw x)
  -- The inverse Cayley transform is smooth at `C (w, x)`, which lies in the Cayley ball.
  have hu : IsUnit (1 - C ((w : ℂ), x)) := by
    have := (SymplecticForm.isUnit_one_sub_of_mem_cayleyBall
      (h₀.cayley_mem_cayleyBall (tames_pairOfPantsAlmostComplex (hJ := hJ) h₀ w x))).map e
    rwa [map_sub, map_one, ← hC ((w : ℂ), x)] at this
  rw [hJC]
  exact ((contDiffAt_const.mul (contDiffAt_const.add contDiffAt_id)).mul
    ((contDiffAt_ringInverse ℝ hu.unit).comp (C ((w : ℂ), x))
      (contDiffAt_const.sub contDiffAt_id))).comp_contMDiffAt hCs

end Smooth

end TauCeti.Floer
