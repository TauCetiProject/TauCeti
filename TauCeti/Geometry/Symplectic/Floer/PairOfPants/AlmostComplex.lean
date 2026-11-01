/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Cayley.Smooth

/-!
# Domain-dependent compatible almost complex structures on the pair of pants

Besides the Hamiltonian perturbation `K`, the perturbed Cauchy–Riemann equation
`(du - X_K)^{0,1} = 0` on the pair of pants `S = ℂ ∖ {0, 1}` uses an almost complex structure
`J_z` on the target that depends on the point `z ∈ S`. On the cylindrical end `q`, far out, it must
be the time-dependent structure `J_q(t)` already chosen for the Floer complex attached to that
end, so that the ends of a pair of pants are asymptotic to Floer cylinders.

This file constructs such a family on a symplectic vector space `(V, ω)` from any compatible base
structure `J₀` and any three families `J_q(t, x)` of `ω`-compatible structures on `V`, of period
one in `t` and depending on a parameter `x`, which is the point of the target (`x ∈ V`) in Floer
theory. It uses the Cayley chart at `J₀`
(`TauCeti.SymplecticForm.Compatible.compatibleCayleyEquiv`), in which the compatible structures
form a convex set containing `0`, the coordinate of `J₀`. The Cayley coordinate of the family is
`∑ q, β(±s_q(z) - 1) C_q(t_q(z), x)`, where `C_q` is the Cayley coordinate of `J_q`, `(s_q, t_q)`
are the coordinates of the end `q` and `β` is the smooth transition from `0` on `(-∞, 0]` to `1`
on `[1, ∞)`; this is the cutoff of `TauCeti.Floer.pairOfPantsPerturbation`. The cutoffs of
distinct ends have disjoint supports, so at most one term is nonzero and the coordinate stays in
the compatible Cayley ball.

## Main definitions

* `TauCeti.Floer.pairOfPantsCayley J₀ J z x`: the Cayley coordinate of the family at `z ∈ ℂ` and
  the parameter `x`.
* `TauCeti.Floer.pairOfPantsAlmostComplex h₀ hJ z x`: the compatible structure `J_z(x)`.

## Main results

* `TauCeti.Floer.compatible_pairOfPantsAlmostComplex`: every `J_z(x)` is `ω`-compatible.
* `TauCeti.Floer.pairOfPantsAlmostComplex_cylindricalEndLift_of_pos`: on the part `±s > 0` of the
  end `q`, in end coordinates `(s, t)`, the family is the Cayley path from `J₀` to `J_q(t, x)` at
  the parameter `±s - 1` (`TauCeti.SymplecticForm.Compatible.cayleyPath`).
* `TauCeti.Floer.pairOfPantsAlmostComplex_cylindricalEndLift`: on the part `±s ≥ 2` of the end
  `q` it is `J_q(t, x)`.
* `TauCeti.Floer.pairOfPantsAlmostComplex_eq_of_two_le`: the same statement at points of `S`,
  in terms of the end coordinates of the point.
* `TauCeti.Floer.pairOfPantsAlmostComplex_eq_of_forall_le_one`: off the parts `±s > 1` of the
  three ends it is `J₀`.
* `TauCeti.Floer.contDiffAt_pairOfPantsAlmostComplex`: for `C^n` families `J_q` with parameters
  `x` in a normed space `E`, the family is `C^n` on `S × E`, as a map to the continuous
  endomorphisms of `V`.

The end structures are arbitrary compatible structures depending on the point of the target and
on time, so they include those of regular Floer data. Choosing the domain-dependent structures
generically, and the corresponding families on a symplectic manifold, are not addressed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 8, on
  Hamiltonian perturbations and domain-dependent almost complex structures.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), on perturbation data on
  surfaces with strip-like and cylindrical ends.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Section 2.5,
  on the Cayley chart of compatible complex structures.
-/

public noncomputable section

open Set Real Topology Manifold
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ω : SymplecticForm V}
  {J₀ : AlmostComplexStructure V}

section Pointwise

variable {X : Type*} {J : Puncture → ℝ → X → AlmostComplexStructure V}

variable (J₀ J) in
/-- The Cayley coordinate at `J₀` of the pair-of-pants almost complex structure with end
structures `J q`. At `w ∈ ℂ` and `x ∈ X` it is `∑ q, β(±s_q(w) - 1) C_q(t_q(w), x)`, where
`C_q(t, x)` is the Cayley transform of `J q t x` at `J₀`, `(s_q, t_q)` are the coordinates of the
end `q`, the sign is that of the end, and `β` is the smooth transition function. -/
def pairOfPantsCayley (w : ℂ) (x : X) : Module.End ℝ V :=
  ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) • J₀.cayley (J q (q.endCoord w).im x)

/-- The defining equation of the Cayley coordinate: the cutoff-weighted sum over the three ends of
the Cayley transforms of the end structures. -/
theorem pairOfPantsCayley_def (w : ℂ) (x : X) :
    pairOfPantsCayley J₀ J w x =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        J₀.cayley (J q (q.endCoord w).im x) :=
  (rfl)

/-- Where the cutoff of the end `r` is nonzero, the Cayley coordinate is the cutoff-scaled Cayley
transform of the structure of that end. -/
theorem pairOfPantsCayley_eq_smul {r : Puncture} {w : ℂ}
    (hr : smoothTransition (r.endSign * (r.endCoord w).re - 1) ≠ 0) (x : X) :
    pairOfPantsCayley J₀ J w x =
      smoothTransition (r.endSign * (r.endCoord w).re - 1) •
        J₀.cayley (J r (r.endCoord w).im x) := by
  obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hr
  rw [pairOfPantsCayley_def, Finset.sum_eq_single r]
  · intro s _ hs
    have hc := smoothTransition_endCoord_cylindricalEndLift_eq_zero (r := s) hs.symm
      (z := r.endCoord w) (by linarith)
    rw [r.cylindricalEndLift_endCoord hw] at hc
    simp [hc]
  · simp

/-- Where every cutoff vanishes, the Cayley coordinate is `0`, the coordinate of `J₀`. -/
theorem pairOfPantsCayley_eq_zero {w : ℂ}
    (h : ∀ q : Puncture, smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0) (x : X) :
    pairOfPantsCayley J₀ J w x = 0 := by
  simp [pairOfPantsCayley_def, h]

/-- On the part `±s > 0` of the end `q`, in end coordinates, the Cayley coordinate is
`β(±s - 1) C_q(t, x)`. -/
theorem pairOfPantsCayley_cylindricalEndLift_of_pos {q : Puncture}
    (hJ : Function.Periodic (J q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : X) :
    pairOfPantsCayley J₀ J (q.cylindricalEndLift z) x =
      smoothTransition (q.endSign * z.re - 1) • J₀.cayley (J q z.im x) := by
  rw [pairOfPantsCayley_def, Finset.sum_eq_single q]
  · obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
    have hre : (q.endCoord (q.cylindricalEndLift z)).re = z.re := by simp [hk]
    have him : (q.endCoord (q.cylindricalEndLift z)).im = z.im + k := by simp [hk]
    have hp : J q (z.im + k) x = J q z.im x := by
      simpa using congrFun (hJ.int_mul k z.im) x
    rw [hre, him, hp]
  · intro r _ hr
    simp [smoothTransition_endCoord_cylindricalEndLift_eq_zero hr.symm hz]
  · simp

variable [FiniteDimensional ℝ V] (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Compatible (J q t x))
include h₀ hJ

/-- The Cayley coordinate lies in the compatible Cayley ball of `J₀`: at most one of its terms is
nonzero, and that term is the Cayley coordinate of a compatible structure scaled into `[0, 1]`. -/
theorem pairOfPantsCayley_mem_compatibleCayleyBall (w : ℂ) (x : X) :
    pairOfPantsCayley J₀ J w x ∈ ω.compatibleCayleyBall J₀ := by
  by_cases h : ∃ r : Puncture, smoothTransition (r.endSign * (r.endCoord w).re - 1) ≠ 0
  · obtain ⟨r, hr⟩ := h
    rw [pairOfPantsCayley_eq_smul hr]
    exact h₀.smul_cayley_mem_compatibleCayleyBall (hJ _ _ _)
      ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · simp only [not_exists, not_not] at h
    rw [pairOfPantsCayley_eq_zero h]
    exact h₀.tames.zero_mem_compatibleCayleyBall

/-- The **pair-of-pants almost complex structure** with base structure `J₀` and end structures
`J q`: the compatible structure at `w ∈ ℂ` and `x ∈ X` whose Cayley coordinate at `J₀` is
`TauCeti.Floer.pairOfPantsCayley J₀ J w x`. Far out on the end `q` it is `J q t x`, and off the
ends it is `J₀`. -/
def pairOfPantsAlmostComplex (w : ℂ) (x : X) : AlmostComplexStructure V :=
  (h₀.compatibleCayleyEquiv.symm
    ⟨pairOfPantsCayley J₀ J w x, pairOfPantsCayley_mem_compatibleCayleyBall h₀ hJ w x⟩).val

/-- The pair-of-pants almost complex structure is the inverse compatible Cayley chart at its
Cayley coordinate. -/
theorem pairOfPantsAlmostComplex_def (w : ℂ) (x : X) :
    pairOfPantsAlmostComplex h₀ hJ w x =
      (h₀.compatibleCayleyEquiv.symm
        ⟨pairOfPantsCayley J₀ J w x, pairOfPantsCayley_mem_compatibleCayleyBall h₀ hJ w x⟩).val :=
  (rfl)

/-- The pair-of-pants almost complex structure is `ω`-compatible at every point. -/
theorem compatible_pairOfPantsAlmostComplex (w : ℂ) (x : X) :
    ω.Compatible (pairOfPantsAlmostComplex h₀ hJ w x) :=
  (h₀.compatibleCayleyEquiv.symm _).property

/-- The Cayley coordinate at `J₀` of the pair-of-pants almost complex structure is
`TauCeti.Floer.pairOfPantsCayley`. -/
@[simp]
theorem cayley_pairOfPantsAlmostComplex (w : ℂ) (x : X) :
    J₀.cayley (pairOfPantsAlmostComplex h₀ hJ w x) = pairOfPantsCayley J₀ J w x := by
  simpa only [pairOfPantsAlmostComplex_def,
    SymplecticForm.Compatible.compatibleCayleyEquiv_apply_coe] using
    congrArg Subtype.val (h₀.compatibleCayleyEquiv.apply_symm_apply _)

/-- A structure tamed by `ω` is the pair-of-pants almost complex structure at `w` and `x` exactly
when its Cayley coordinate at `J₀` is `TauCeti.Floer.pairOfPantsCayley J₀ J w x`. -/
theorem pairOfPantsAlmostComplex_eq_iff {w : ℂ} {x : X} {J' : AlmostComplexStructure V}
    (h' : ω.Tames J') :
    pairOfPantsAlmostComplex h₀ hJ w x = J' ↔ J₀.cayley J' = pairOfPantsCayley J₀ J w x := by
  refine ⟨fun h => by rw [← h, cayley_pairOfPantsAlmostComplex], fun h => ?_⟩
  exact h₀.eq_of_cayley_eq (compatible_pairOfPantsAlmostComplex h₀ hJ w x).tames h'
    (by rw [cayley_pairOfPantsAlmostComplex, h])

/-- **The structure on an end.** On the part `±s > 0` of the end `q`, in end coordinates
`(s, t)`, the pair-of-pants almost complex structure is the Cayley path from `J₀` to `J q t x` at
the parameter `±s - 1`. In particular it is `J₀` for `±s ≤ 1`. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift_of_pos {q : Puncture}
    (hJq : Function.Periodic (J q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : X) :
    pairOfPantsAlmostComplex h₀ hJ (q.cylindricalEndLift z) x =
      h₀.cayleyPath (hJ q z.im x) (q.endSign * z.re - 1) := by
  rw [pairOfPantsAlmostComplex_eq_iff h₀ hJ (h₀.compatible_cayleyPath _ _).tames,
    SymplecticForm.Compatible.cayley_cayleyPath, pairOfPantsCayley_cylindricalEndLift_of_pos hJq hz]

/-- **The structure is `J_q(t)` far out on each end.** On the part `±s ≥ 2` of the end `q`, in end
coordinates `(s, t)`, the pair-of-pants almost complex structure is `J q t x`. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift {q : Puncture}
    (hJq : Function.Periodic (J q) 1) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) (x : X) :
    pairOfPantsAlmostComplex h₀ hJ (q.cylindricalEndLift z) x = J q z.im x := by
  rw [pairOfPantsAlmostComplex_cylindricalEndLift_of_pos h₀ hJ hJq (by linarith),
    SymplecticForm.Compatible.cayleyPath_of_one_le _ _ (by linarith)]

/-- **The structure is `J_r(t_r)` far out on each end.** At a point `w` of the part `±s ≥ 2` of the
end `r`, the pair-of-pants almost complex structure is the structure of that end at the angular
coordinate of `w`. -/
theorem pairOfPantsAlmostComplex_eq_of_two_le {r : Puncture} {w : ℂ}
    (hw : 2 ≤ r.endSign * (r.endCoord w).re) (x : X) :
    pairOfPantsAlmostComplex h₀ hJ w x = J r (r.endCoord w).im x := by
  have hc : smoothTransition (r.endSign * (r.endCoord w).re - 1) = 1 :=
    smoothTransition.one_of_one_le (by linarith)
  rw [pairOfPantsAlmostComplex_eq_iff h₀ hJ (hJ _ _ _).tames,
    pairOfPantsCayley_eq_smul (by rw [hc]; exact one_ne_zero), hc, one_smul]

/-- **The structure is `J₀` off the ends.** At a point which lies on none of the parts `±s > 1`
of the three ends, the pair-of-pants almost complex structure is the base structure `J₀`. -/
theorem pairOfPantsAlmostComplex_eq_of_forall_le_one {w : ℂ}
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) (x : X) :
    pairOfPantsAlmostComplex h₀ hJ w x = J₀ := by
  rw [pairOfPantsAlmostComplex_eq_iff h₀ hJ h₀.tames, AlmostComplexStructure.cayley_self,
    pairOfPantsCayley_eq_zero fun q => smoothTransition.zero_of_nonpos (by linarith [hw q])]

end Pointwise

section Smooth

variable [FiniteDimensional ℝ V] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {J : Puncture → ℝ → E → AlmostComplexStructure V}

/-- **The structure is smooth.** For end structures `J q` of period one which are `C^n` on
`ℝ × E` as maps to the continuous endomorphisms of `V`, the pair-of-pants almost complex structure
is `C^n` on `S × E`, where `S = ℂ ∖ {0, 1}` is the thrice-punctured sphere. -/
theorem contDiffAt_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Compatible (J q t x)) {n : ℕ∞} (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ n
      (fun p : ℝ × E => LinearMap.toContinuousLinearMap (J q p.1 p.2).toLinearMap))
    (w : ThricePuncturedSphere) (x : E) :
    ContDiffAt ℝ n
      (fun p : ℂ × E => LinearMap.toContinuousLinearMap
        (pairOfPantsAlmostComplex h₀ hJ p.1 p.2).toLinearMap) ((w : ℂ), x) := by
  -- The Cayley coordinate, as a map to continuous endomorphisms.
  let C : ℂ × E → V →L[ℝ] V := fun p => ∑ q,
    smoothTransition (q.endSign * (q.endCoord p.1).re - 1) •
      LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.1).im p.2))
  have hCeq (p : ℂ × E) : (C p).toLinearMap = pairOfPantsCayley J₀ J p.1 p.2 := by
    simp [C, pairOfPantsCayley_def, ContinuousLinearMap.toLinearMap_sum]
  have hC (p : ℂ × E) : (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀ := by
    rw [hCeq]
    exact pairOfPantsCayley_mem_compatibleCayleyBall h₀ hJ p.1 p.2
  have hCs : ContDiffAt ℝ n C ((w : ℂ), x) := by
    refine ContDiffAt.sum fun q _ => ?_
    have hw : (w : ℂ) ≠ q.endCenter := ne_endCenter w.2 q
    have hc : ContDiffAt ℝ n
        (fun p : ℂ × E => smoothTransition (q.endSign * (q.endCoord p.1).re - 1)) ((w : ℂ), x) :=
      (smoothTransition.contDiffAt.comp (w : ℂ)
        ((contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).sub contDiffAt_const)).comp
        ((w : ℂ), x) contDiffAt_fst
    -- The Cayley transforms of the end structures, evaluated at the angular coordinate.
    have hK : ContDiff ℝ n (fun p : ℝ × E =>
        LinearMap.toContinuousLinearMap (J₀.cayley (J q p.1 p.2))) :=
      h₀.tames.contDiff_cayley (fun p : ℝ × E => (hJ q p.1 p.2).tames) (hJs q)
    have hKp : Function.Periodic
        (fun t x => LinearMap.toContinuousLinearMap (J₀.cayley (J q t x))) 1 :=
      fun t => by simp only [hJp q t]
    -- `contMDiffAt_comp_im_endCoord` is stated on the product manifold `ℂ × E`; pass to and from
    -- the normed space `ℂ × E` through the identity maps.
    have hk := (q.contMDiffAt_comp_im_endCoord (I := 𝓘(ℝ, E)) (n := n) hKp
      (hK.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)) hw x).comp ((w : ℂ), x)
      (contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt)
    exact hc.smul (contMDiffAt_iff_contDiffAt.1 hk)
  convert h₀.contDiffAt_compatibleCayleyEquiv_symm hC hCs using 1
  funext p
  rw [pairOfPantsAlmostComplex_def]
  simp only [hCeq]

end Smooth

end TauCeti.Floer
