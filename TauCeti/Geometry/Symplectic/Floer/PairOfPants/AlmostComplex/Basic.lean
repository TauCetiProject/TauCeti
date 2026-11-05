/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
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
* `TauCeti.Floer.cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos`: if `J_q` has period
  one in `t`, then on the part `±s > 0` of the end `q` its Cayley transform is
  `β(±s - 1) • cayley (J_q(t, x))`.
* `TauCeti.Floer.pairOfPantsAlmostComplex_cylindricalEndLift`: if `J_q` has period one in `t`,
  then on the part `±s ≥ 2` of the end `q` it is `J_q(t, x)`.
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

variable {M : Type*}

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

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
`q` and `β` is the smooth transition function. It is `J₀` off the ends, and, when `J q` has period
one in `t`, it is `J q t x` far out on the end `q`. -/
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
@[simp]
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

/-- **The structure on an end.** If `J q` has period one in `t`, then on the part `±s > 0` of the
end `q`, the Cayley transform of the pair-of-pants structure at the point with end coordinates
`z = s + i t` is
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

/-- **The structure is `J q t` far out on each end.** If `J q` has period one in `t`, then on the
part `±s ≥ 2` of the end `q`, the pair-of-pants structure at the point with end coordinates
`z = s + i t` is `J q t x`. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) (x : M) :
    pairOfPantsAlmostComplex h₀ J hJ (q.cylindricalEndLift z) x = J q z.im x := by
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ _ x) (hJ q z.im x) ?_
  rw [cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos h₀ hJp (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_smul]

/-- At a point far out on an end, the structure is the prescribed end structure evaluated at
its angular coordinate. -/
theorem pairOfPantsAlmostComplex_eq_endStructure (h₀ : ω.Compatible J₀)
    {w : ℂ} (hw : 2 ≤ q.endSign * (q.endCoord w).re) (x : M) :
    pairOfPantsAlmostComplex h₀ J hJ w x = J q (q.endCoord w).im x := by
  have hne : w ≠ q.endCenter :=
    q.ne_endCenter_of_re_endCoord_ne_zero (by
      intro h
      simp only [h, mul_zero] at hw
      norm_num at hw)
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ w x)
    (hJ q (q.endCoord w).im x) ?_
  rw [cayley_pairOfPantsAlmostComplex, Finset.sum_eq_single q]
  · rw [smoothTransition.one_of_one_le (by linarith), one_smul]
  · intro r _ hr
    have hr' := smoothTransition_endCoord_cylindricalEndLift_eq_zero hr
      (z := q.endCoord w) (by linarith)
    rw [q.cylindricalEndLift_endCoord hne] at hr'
    simp [hr']
  · simp

/-- The pair-of-pants structure differs from `J₀` only on the parts `±s > 1` of the three ends. -/
theorem exists_cylindricalEndLift_of_pairOfPantsAlmostComplex_ne (h₀ : ω.Compatible J₀)
    {w : ℂ} {x : M} (h : pairOfPantsAlmostComplex h₀ J hJ w x ≠ J₀) :
    ∃ (q : Puncture) (z : ℂ), 1 < q.endSign * z.re ∧ q.cylindricalEndLift z = w := by
  by_contra! hne
  refine h (h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ w x) h₀.tames ?_)
  rw [cayley_pairOfPantsAlmostComplex, AlmostComplexStructure.cayley_self]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hc : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0
  · simp [hc]
  · obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hc
    exact absurd (q.cylindricalEndLift_endCoord hw) (hne q _ h₁)

end Algebraic

section Smooth

/-! ### Smoothness -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

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
  -- The cutoff-weighted sum of the Cayley transforms of the end structures is the Cayley
  -- transform `C` of the pair-of-pants structure, which therefore is the inverse Cayley chart
  -- applied to `C`.
  set C : ℂ × M → V →L[ℝ] V := fun p =>
    ∑ q, smoothTransition (q.endSign * (q.endCoord p.1).re - 1) •
      LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.1).im p.2)) with hC_def
  have hC (p : ℂ × M) : (C p).toLinearMap =
      ∑ q, smoothTransition (q.endSign * (q.endCoord p.1).re - 1) •
        J₀.cayley (J q (q.endCoord p.1).im p.2) := by
    simp [hC_def]
  have hCb (p : ℂ × M) : (C p).toLinearMap ∈ ω.cayleyBall J₀ := by
    rw [hC, ← cayley_pairOfPantsAlmostComplex (hJ := hJ) h₀]
    exact h₀.cayley_mem_cayleyBall (tames_pairOfPantsAlmostComplex h₀ p.1 p.2)
  have hJC : (fun p : ℂ × M =>
      (pairOfPantsAlmostComplex h₀ J hJ p.1 p.2).toLinearMap.toContinuousLinearMap) =
      fun p => LinearMap.toContinuousLinearMap
        (h₀.cayleyEquiv.symm ⟨(C p).toLinearMap, hCb p⟩).val.toLinearMap := by
    simp only [pairOfPantsAlmostComplex, hC]
  -- `C` is smooth: the cutoffs are smooth, and periodicity makes the Cayley transforms of the
  -- end structures smooth functions of the angular coordinate.
  have hCs : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, V →L[ℝ] V) n C ((w : ℂ), x) := by
    refine contMDiffAt_finsetSum fun q _ => ?_
    have hw : (w : ℂ) ≠ q.endCenter := ne_endCenter w.2 q
    have hFp : Function.Periodic
        (fun t y => LinearMap.toContinuousLinearMap (J₀.cayley (J q t y))) 1 := fun t => by
      simp only [hJp q t]
    exact (contMDiffAt_smoothTransition_endCoord q hw x).smul (q.contMDiffAt_comp_im_endCoord hFp
      (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J q p.1 p.2) (fun p => hJ q p.1 p.2)
        (hJs q)) hw x)
  rw [hJC]
  exact h₀.contMDiffAt_cayleyEquiv_symm hCb hCs

end Smooth

end TauCeti.Floer
