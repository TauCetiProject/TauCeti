/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath
import TauCeti.Analysis.Complex.ThricePuncturedSphere.MovingEnds
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Almost complex structures on spheres with moving input ends

The associativity of the pair-of-pants product compares the two broken products through a family
of four-punctured spheres whose inputs sit at moving punctures of `ℂ` and whose output sits at
`∞`. Its Hamiltonian perturbations are the data `TauCeti.Floer.puncturedSpherePerturbation c a H
Hout` of input ends with centers `c i`, scales `a i` and Hamiltonians `H i`, and of an output end
with Hamiltonian `Hout`. This file constructs the matching domain-dependent almost complex
structures, which far out on each end are the structures already chosen for the Floer complex of
that end.

Fix an `ω`-compatible base structure `J₀`. An input end with center `c` and scale `a` has the end
lift `z ↦ c + a φ₀(z)`, where `φ₀` is the end lift of the input `0` of the pair of pants
`ℂ ∖ {0, 1}`. Its structure `TauCeti.Floer.inputEndAlmostComplex h₀ c a J hJ` is the inverse Cayley
transform, relative to `J₀`, of

`β(s(w') - 1) • cayley (J (t(w')) x)`,  where  `w' = (w - c) / a`,

`(s, t)` are the coordinates of the end at `0` of the pair of pants and `β` is the smooth
transition. So it is the pair-of-pants structure whose only end structure other than `J₀` is `J` at
the input `0`, composed with the affine map `w ↦ (w - c) / a`
(`TauCeti.Floer.pairOfPantsAlmostComplex_update_zero`); it is `J₀` off the disc
`‖w - c‖ < ‖a‖ exp (-2π) / 2`. For finitely many input ends and an output end structure `Jout`, the
structure `TauCeti.Floer.puncturedSphereAlmostComplex` is the inverse Cayley transform of the sum of
the Cayley transforms of the input end structures and of the negative plane structure of `Jout`
(`TauCeti.Floer.negativePlaneAlmostComplex`). The definition assumes the configuration hypotheses
under which the perturbation datum is the end datum on each end: the discs `‖w - c i‖ < ‖a i‖ / 2`
are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)` on which the negative plane structure
is `J₀`. Then at most one term of the sum is nonzero at each point, so the sum lies in the Cayley
ball.

## Main definitions

* `TauCeti.Floer.inputEndAlmostComplex`: the structure of one input end.
* `TauCeti.Floer.puncturedSphereAlmostComplex`: the structure on a sphere with moving input ends.

## Main results

* `TauCeti.Floer.tames_puncturedSphereAlmostComplex`,
  `TauCeti.Floer.compatible_puncturedSphereAlmostComplex`: the structure is `ω`-tame, and
  `ω`-compatible when the end structures are.
* `TauCeti.Floer.puncturedSphereAlmostComplex_eq_inputEndAlmostComplex`: on the disc
  `‖w - c i‖ < ‖a i‖ / 2` it is the structure of the input end `i`;
  `TauCeti.Floer.puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex`: off the supports of
  the input end structures it is the negative plane structure; and
  `TauCeti.Floer.puncturedSphereAlmostComplex_eq_of_le_norm_sub_of_norm_le`: off all the ends it
  is `J₀`.
* `TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift` and
  `TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift_inf`: far out on the input end `i`
  it is `J i (t) x` in the end lift `z ↦ c i + a i φ₀(z)`, and far out on the output end it is
  `Jout (t) x`. These are the end coordinates in which the perturbation datum is `H i(t) dt` and
  `Hout(t) dt` (`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift`,
  `TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift_inf`).
* `TauCeti.Floer.puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex`: the pair-of-pants
  structure is the case of the inputs `0` and `1` with scales `1` and `-1`.
* `TauCeti.Floer.contMDiffAt_puncturedSphereAlmostComplex_comp`: along a family of configurations,
  domain points and target points over a manifold `N`, the structures form a `C^n` family wherever
  the scales are nonzero and the domain point is not a center;
  `TauCeti.Floer.contMDiffAt_puncturedSphereAlmostComplex` is the case of a fixed configuration.
* `TauCeti.Floer.contMDiffAt_puncturedSphereAlmostComplex_associativity`: along the path of
  configurations between the two associativity compositions
  (`TauCeti.Floer.associativityCenter`, `TauCeti.Floer.associativityScale`), the structures are
  `C^n` jointly in the path parameter, the domain point and the target point.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through a family of
  four-punctured spheres.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured surfaces with cylindrical ends and consistent Floer data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V : Type*}

section Algebraic

variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-! ### One input end -/

section InputEnd

/-- The almost complex structure of an input end with center `c` and scale `a` and end structures
`J (t) x`, relative to an `ω`-compatible base structure `J₀`. At `w ∈ ℂ` and `x ∈ M` it is the
inverse Cayley transform, relative to `J₀`, of `β(s(w') - 1) • cayley (J (t(w')) x)` for
`w' = (w - c) / a`, where `(s, t)` are the coordinates of the end at `0` of the pair of pants and
`β` is the smooth transition function. Its end lift is `z ↦ c + a φ₀(z)`, where `φ₀` is the end lift
of the input `0`. -/
def inputEndAlmostComplex (h₀ : ω.Compatible J₀) (c a : ℂ) (J : ℝ → M → AlmostComplexStructure V)
    (hJ : ∀ t x, ω.Tames (J t x)) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨smoothTransition ((zero.endCoord ((w - c) / a)).re - 1) •
        J₀.cayley (J (zero.endCoord ((w - c) / a)).im x),
      h₀.tames.convex_cayleyBall.smul_mem_of_zero_mem h₀.tames.zero_mem_cayleyBall
        (h₀.cayley_mem_cayleyBall (hJ _ x))
        ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩⟩

variable {c a : ℂ} {J : ℝ → M → AlmostComplexStructure V} {hJ : ∀ t x, ω.Tames (J t x)}

/-- The input end structure is tamed by `ω`. -/
theorem tames_inputEndAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (inputEndAlmostComplex h₀ c a J hJ w x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the input end structure, relative to `J₀`, is
`β(s(w') - 1) • cayley (J (t(w')) x)` for `w' = (w - c) / a`. This characterizes the structure,
since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_inputEndAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (inputEndAlmostComplex h₀ c a J hJ w x) =
      smoothTransition ((zero.endCoord ((w - c) / a)).re - 1) •
        J₀.cayley (J (zero.endCoord ((w - c) / a)).im x) := by
  rw [inputEndAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

omit [FiniteDimensional ℝ V] in
/-- The end structures of an input end, `J` at the input `0` and `J₀` at the other ends of the
pair of pants, are tame when `J₀` and `J` are. -/
theorem tames_update_zero (h₀ : ω.Tames J₀) (hJ : ∀ t x, ω.Tames (J t x)) (q : Puncture)
    (t : ℝ) (x : M) : ω.Tames (update (fun _ _ _ => J₀) zero J q t x) :=
  (forall_update_iff _ fun _ (f : ℝ → M → _) => ∀ t x, ω.Tames (f t x)).2
    ⟨hJ, fun _ _ _ _ => h₀⟩ q t x

/-- **An input end is a pair of pants with one non-base end.** The pair-of-pants structure whose
end structure at the input `0` is `J` and whose other end structures are the base structure `J₀`,
at the point `(w - c) / a`, is the input end structure with center `c` and scale `a` at `w`. -/
theorem pairOfPantsAlmostComplex_update_zero (h₀ : ω.Compatible J₀)
    (hJ' : ∀ q t x, ω.Tames (update (fun _ _ _ => J₀) zero J q t x)) (w : ℂ) (x : M) :
    pairOfPantsAlmostComplex h₀ (update (fun _ _ _ => J₀) zero J) hJ' ((w - c) / a) x =
      inputEndAlmostComplex h₀ c a J hJ w x := by
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ _ x)
    (tames_inputEndAlmostComplex h₀ w x) ?_
  rw [cayley_pairOfPantsAlmostComplex, cayley_inputEndAlmostComplex,
    Fintype.sum_eq_single zero fun q hq => by
      simp [update_of_ne hq, AlmostComplexStructure.cayley_self]]
  simp

/-- The input end structure is `ω`-compatible when the end structures are. -/
theorem compatible_inputEndAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ t x, ω.Compatible (J t x)) (w : ℂ) (x : M) :
    ω.Compatible (inputEndAlmostComplex h₀ c a J hJ w x) := by
  rw [← pairOfPantsAlmostComplex_update_zero h₀ (tames_update_zero h₀.tames hJ)]
  exact compatible_pairOfPantsAlmostComplex h₀
    ((forall_update_iff _ fun _ (f : ℝ → M → _) => ∀ t x, ω.Compatible (f t x)).2
      ⟨hJc, fun _ _ _ _ => h₀⟩) _ x

/-- **The support of an input end structure.** It is the base structure `J₀` off the disc
`‖w - c‖ < ‖a‖ exp (-2π) / 2`. -/
theorem inputEndAlmostComplex_eq_of_le_norm_sub (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : ‖a‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c‖) (x : M) :
    inputEndAlmostComplex h₀ c a J hJ w x = J₀ := by
  refine h₀.eq_of_cayley_eq (tames_inputEndAlmostComplex h₀ w x) h₀.tames ?_
  rw [cayley_inputEndAlmostComplex, AlmostComplexStructure.cayley_self]
  -- The longitudinal coordinate of the end at `0` is at most `1` at `w' = (w - c) / a`.
  have hre : (zero.endCoord ((w - c) / a)).re ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simpa using (re_endCoord_endCenter zero).le.trans zero_le_one
    · refine re_endCoord_zero_le_one ?_
      rw [norm_div, le_div_iff₀ (norm_pos_iff.2 ha)]
      linarith
  rw [smoothTransition.zero_of_nonpos (by linarith), zero_smul]

/-- **The input end structure on its end.** If `J` has period one in `t` and `a ≠ 0`, then at the
point `c + a φ₀(z)` of the end lift with `Re z > 0` its Cayley transform is
`β(Re z - 1) • cayley (J (Im z) x)`. -/
theorem cayley_inputEndAlmostComplex_cylindricalEndLift_of_pos (h₀ : ω.Compatible J₀)
    (hJp : Periodic J 1) (ha : a ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) :
    J₀.cayley (inputEndAlmostComplex h₀ c a J hJ (c + a * zero.cylindricalEndLift z) x) =
      smoothTransition (z.re - 1) • J₀.cayley (J z.im x) := by
  rw [← pairOfPantsAlmostComplex_update_zero h₀ (tames_update_zero h₀.tames hJ),
    add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
  simpa using cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos (q := zero)
    (hJ := tames_update_zero h₀.tames hJ) h₀ (by simpa using hJp) (z := z) (by simpa using hz) x

/-- **The input end structure is `J (t)` far out on its end.** If `J` has period one in `t` and
`a ≠ 0`, then at the point `c + a φ₀(z)` of the end lift with `Re z ≥ 2` the input end structure is
`J (Im z) x`. -/
theorem inputEndAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hJp : Periodic J 1) (ha : a ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) :
    inputEndAlmostComplex h₀ c a J hJ (c + a * zero.cylindricalEndLift z) x = J z.im x := by
  rw [← pairOfPantsAlmostComplex_update_zero h₀ (tames_update_zero h₀.tames hJ),
    add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
  simpa using pairOfPantsAlmostComplex_cylindricalEndLift (q := zero)
    (hJ := tames_update_zero h₀.tames hJ) h₀ (by simpa using hJp) (z := z) (by simpa using hz) x

end InputEnd

/-! ### The sphere with moving input ends -/

section Sphere

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {J : ι → ℝ → M → AlmostComplexStructure V}
  {hJ : ∀ i t x, ω.Tames (J i t x)} {Jout : ℝ → M → AlmostComplexStructure V}
  {hJout : ∀ t x, ω.Tames (Jout t x)}

/-- On the disc of the input `i`, the sum of the Cayley transforms of the input end structures and
of the negative plane structure is the Cayley transform of the input end structure of `i`. -/
private theorem sum_cayley_eq_of_norm_sub_lt (h₀ : ω.Compatible J₀)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι} {w : ℂ}
    (hw : ‖w - c i‖ < ‖a i‖ / 2) (x : M) :
    ∑ j, J₀.cayley (inputEndAlmostComplex h₀ (c j) (a j) (J j) (hJ j) w x) +
        J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) =
      J₀.cayley (inputEndAlmostComplex h₀ (c i) (a i) (J i) (hJ i) w x) := by
  rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [inputEndAlmostComplex_eq_of_le_norm_sub h₀
          ((norm_mul_exp_neg_two_pi_div_two_le (a j)).trans
            (le_norm_sub_of_norm_sub_le hsep hj hw.le)),
        AlmostComplexStructure.cayley_self]) (by simp),
    negativePlaneAlmostComplex_eq_of_norm_le h₀ (norm_le_of_norm_sub_le hout hw.le),
    AlmostComplexStructure.cayley_self, add_zero]

/-- Off the supports of all the input end structures, the sum of the Cayley transforms is the
Cayley transform of the negative plane structure. -/
private theorem sum_cayley_eq_of_forall_le_norm_sub (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) (x : M) :
    ∑ j, J₀.cayley (inputEndAlmostComplex h₀ (c j) (a j) (J j) (hJ j) w x) +
        J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) =
      J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) := by
  rw [Finset.sum_eq_zero fun j _ => by
    rw [inputEndAlmostComplex_eq_of_le_norm_sub h₀ (hw j), AlmostComplexStructure.cayley_self],
    zero_add]

/-- If the Cayley transforms of all the input end structures and of the negative plane structure
lie in a set `s`, so does their sum: at each point it is one of them. -/
private theorem sum_cayley_mem (h₀ : ω.Compatible J₀)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {s : Set (Module.End ℝ V)}
    (hin : ∀ i w x, J₀.cayley (inputEndAlmostComplex h₀ (c i) (a i) (J i) (hJ i) w x) ∈ s)
    (hpl : ∀ w x, J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) ∈ s) (w : ℂ) (x : M) :
    ∑ j, J₀.cayley (inputEndAlmostComplex h₀ (c j) (a j) (J j) (hJ j) w x) +
      J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) ∈ s := by
  by_cases h : ∃ i, ‖w - c i‖ < ‖a i‖ * Real.exp (-(2 * π)) / 2
  · obtain ⟨i, hi⟩ := h
    rw [sum_cayley_eq_of_norm_sub_lt h₀ hsep hout
      (hi.trans_le (norm_mul_exp_neg_two_pi_div_two_le (a i))) x]
    exact hin i w x
  · push Not at h
    rw [sum_cayley_eq_of_forall_le_norm_sub h₀ h x]
    exact hpl w x

/-- The domain-dependent almost complex structure on the sphere with input ends of centers `c i`,
scales `a i` and end structures `J i (t) x`, and with an output end at `∞` with end structure
`Jout (t) x`, relative to an `ω`-compatible base structure `J₀`. At `w ∈ ℂ` and `x ∈ M` it is the
inverse Cayley transform, relative to `J₀`, of the sum of the Cayley transforms of the input end
structures `inputEndAlmostComplex h₀ (c i) (a i) (J i)` and of the negative plane structure of
`Jout`. The configuration is required to satisfy the hypotheses under which the perturbation datum
`TauCeti.Floer.puncturedSpherePerturbation` is the end datum on each end: the discs
`‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`. Then at most
one term of the sum is nonzero at each point. -/
def puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (c a : ι → ℂ)
    (J : ι → ℝ → M → AlmostComplexStructure V) (hJ : ∀ i t x, ω.Tames (J i t x))
    (Jout : ℝ → M → AlmostComplexStructure V) (hJout : ∀ t x, ω.Tames (Jout t x))
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (w : ℂ) (x : M) :
    AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨∑ i, J₀.cayley (inputEndAlmostComplex h₀ (c i) (a i) (J i) (hJ i) w x) +
        J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x),
      sum_cayley_mem h₀ hsep hout
        (fun _ _ _ => h₀.cayley_mem_cayleyBall (tames_inputEndAlmostComplex h₀ _ _))
        (fun _ _ => h₀.cayley_mem_cayleyBall (tames_negativePlaneAlmostComplex h₀ _ _)) w x⟩

variable {hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖}
  {hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)}

/-- The structure on the sphere with moving input ends is tamed by `ω`. -/
theorem tames_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the structure on the sphere with moving input ends, relative to `J₀`,
is the sum of the Cayley transforms of the input end structures and of the negative plane
structure. This characterizes the structure, since the Cayley transform is injective on tame
structures. -/
@[simp]
theorem cayley_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x) =
      ∑ i, J₀.cayley (inputEndAlmostComplex h₀ (c i) (a i) (J i) (hJ i) w x) +
        J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout w x) := by
  rw [puncturedSphereAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- **Near an input end the structure is that end's structure.** On the disc
`‖w - c i‖ < ‖a i‖ / 2` of the input `i`, the structure is the input end structure of `i`. -/
theorem puncturedSphereAlmostComplex_eq_inputEndAlmostComplex (h₀ : ω.Compatible J₀) {i : ι}
    {w : ℂ} (hw : ‖w - c i‖ < ‖a i‖ / 2) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x =
      inputEndAlmostComplex h₀ (c i) (a i) (J i) (hJ i) w x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ w x)
    (tames_inputEndAlmostComplex h₀ w x) ?_
  rw [cayley_puncturedSphereAlmostComplex, sum_cayley_eq_of_norm_sub_lt h₀ hsep hout hw]

/-- **Off the input ends the structure is the output structure.** At a point outside the supports
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of all the input end structures, the structure is the negative
plane structure of the output end structure. -/
theorem puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀)
    {w : ℂ} (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x =
      negativePlaneAlmostComplex h₀ Jout hJout w x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ w x)
    (tames_negativePlaneAlmostComplex h₀ w x) ?_
  rw [cayley_puncturedSphereAlmostComplex, sum_cayley_eq_of_forall_le_norm_sub h₀ hw]

/-- **Off all the ends the structure is `J₀`.** At a point outside the supports
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of all the input end structures, in the disc
`‖w‖ ≤ 2 exp (2π)` where the negative plane structure is `J₀`, the structure is `J₀`. -/
theorem puncturedSphereAlmostComplex_eq_of_le_norm_sub_of_norm_le (h₀ : ω.Compatible J₀)
    {w : ℂ} (hc : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖)
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x = J₀ := by
  rw [puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex h₀ hc,
    negativePlaneAlmostComplex_eq_of_norm_le h₀ hw]

/-- The structure on the sphere with moving input ends is `ω`-compatible when the end structures
are. -/
theorem compatible_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ i t x, ω.Compatible (J i t x)) (hJoutc : ∀ t x, ω.Compatible (Jout t x)) (w : ℂ)
    (x : M) : ω.Compatible (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout w x) := by
  refine (h₀.cayley_mem_compatibleCayleyBall_iff (tames_puncturedSphereAlmostComplex h₀ w x)).mp ?_
  rw [cayley_puncturedSphereAlmostComplex]
  exact sum_cayley_mem h₀ hsep hout
    (fun i w x => (h₀.cayley_mem_compatibleCayleyBall_iff (tames_inputEndAlmostComplex h₀ w x)).mpr
      (compatible_inputEndAlmostComplex h₀ (hJc i) w x))
    (fun w x => (h₀.cayley_mem_compatibleCayleyBall_iff
      (tames_negativePlaneAlmostComplex h₀ w x)).mpr
      (compatible_negativePlaneAlmostComplex h₀ hJoutc w x)) w x

/-- **The structure on an input end.** If `J i` has period one in `t` and `a i ≠ 0`, then on the
part `s > 0` of the input end `i`, the Cayley transform of the structure at the point
`c i + a i φ₀(z)` of the end lift is `β(s - 1) • cayley (J i t x)` for `z = s + i t`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos (h₀ : ω.Compatible J₀)
    {i : ι} (hJp : Periodic (J i) 1) (ha : a i ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout
        (c i + a i * zero.cylindricalEndLift z) x) =
      smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
  -- The point lies in the disc `‖w - c i‖ < ‖a i‖ / 2` of the input `i`.
  rw [puncturedSphereAlmostComplex_eq_inputEndAlmostComplex h₀
      (norm_add_mul_cylindricalEndLift_sub_lt (c i) ha hz),
    cayley_inputEndAlmostComplex_cylindricalEndLift_of_pos h₀ hJp ha hz]

/-- **The structure is `J i (t)` far out on each input end.** If `J i` has period one in `t` and
`a i ≠ 0`, then on the part `s ≥ 2` of the input end `i` the structure at the point
`c i + a i φ₀(z)` of the end lift is `J i (Im z) x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀) {i : ι}
    (hJp : Periodic (J i) 1) (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout
        (c i + a i * zero.cylindricalEndLift z) x = J i z.im x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJ i z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos h₀ hJp ha (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_smul]

/-- **The structure on the output end.** If `Jout` has period one in `t`, then on the part
`s ≤ -1` of the output end, the Cayley transform of the structure at the point `φ_∞(z)` is
`β(-s - 1) • cayley (Jout t x)` for `z = s + i t`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le (h₀ : ω.Compatible J₀)
    (hJp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -1) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout
        (inf.cylindricalEndLift z) x) =
      smoothTransition (-z.re - 1) • J₀.cayley (Jout z.im x) := by
  rw [puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex h₀
      (fun i => le_norm_cylindricalEndLift_inf_sub (hout i) hz),
    cayley_negativePlaneAlmostComplex_cylindricalEndLift_of_neg h₀ hJp (by linarith)]

/-- **The structure is `Jout (t)` far out on the output end.** If `Jout` has period one in `t`,
then on the part `s ≤ -2` of the output end the structure at the point `φ_∞(z)` is
`Jout (Im z) x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout (inf.cylindricalEndLift z) x =
      Jout z.im x := by
  rw [puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex h₀
      (fun i => le_norm_cylindricalEndLift_inf_sub (hout i) (by linarith)),
    negativePlaneAlmostComplex_cylindricalEndLift h₀ hJp hz]

end Sphere

/-! ### The pair of pants -/

section PairOfPants

variable {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {hJ' : ∀ i t x, ω.Tames ((![J zero, J one] : Fin 2 → ℝ → M → AlmostComplexStructure V) i t x)}
  {hsep : Pairwise fun i j => ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 + ‖(![1, -1] : Fin 2 → ℂ) j‖ / 2 ≤
    ‖(![0, 1] : Fin 2 → ℂ) i - (![0, 1] : Fin 2 → ℂ) j‖}
  {hout : ∀ i, ‖(![0, 1] : Fin 2 → ℂ) i‖ + ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 ≤
    2 * Real.exp (2 * π)}

/-- **The pair of pants has two input ends.** The pair-of-pants structure of the end structures
`J q` is the structure of the sphere with the input ends of centers `0` and `1`, scales `1` and
`-1` and end structures `J 0` and `J 1`, and with output end structure `J ∞`. -/
theorem puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀) :
    puncturedSphereAlmostComplex h₀ ![0, 1] ![1, -1] ![J zero, J one] hJ' (J inf) (hJ inf) hsep
      hout = pairOfPantsAlmostComplex h₀ J hJ := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  -- The input end at `1` is the image of the input end at `0` under `w ↦ 1 - w`.
  have hc : zero.endCoord ((w - 1) / -1) = one.endCoord w := by
    rw [endCoord_def, endCoord_def, endCenter_zero, endCenter_one, endScale_zero, endScale_one]
    congr 3
    ring
  rw [cayley_puncturedSphereAlmostComplex, cayley_pairOfPantsAlmostComplex, Fin.sum_univ_two,
    Puncture.sum_univ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    cayley_inputEndAlmostComplex, cayley_negativePlaneAlmostComplex, sub_zero, div_one, hc,
    endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul]

end PairOfPants

end Algebraic

section Smooth

/-! ### Smoothness -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The input end structure is smooth in its center and scale.** For a family `J (t) x` of
`ω`-tame structures which has period one in `t` and is `C^n` on `ℝ × M`, the input end structure is
`C^n` jointly in the center `c`, the scale `a`, the domain point `w` and the target point, at every
point with `a ≠ 0` and `w ≠ c`. -/
theorem contMDiffAt_inputEndAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    {J : ℝ → M → AlmostComplexStructure V} {hJ : ∀ t x, ω.Tames (J t x)} (hJp : Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c a w : ℂ} (ha : a ≠ 0) (hw : w ≠ c) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => LinearMap.toContinuousLinearMap
        (inputEndAlmostComplex h₀ p.1.1 p.1.2 J hJ p.2.1 p.2.2).toLinearMap)
      ((c, a), (w, x)) := by
  refine h₀.contMDiffAt_of_contMDiffAt_cayley (fun _ => tames_inputEndAlmostComplex h₀ _ _) ?_
  simp only [cayley_inputEndAlmostComplex, map_smul]
  -- The point `w' = (w - c) / a` of the end at `0` depends smoothly on `(c, a, w)` for `a ≠ 0`.
  have hcoordM := contMDiffAt_sub_div (𝕜 := ℝ) (I' := I) (n := n) (c := c) (w := w) ha x
  have hw' : (w - c) / a ≠ zero.endCenter := by
    rw [endCenter_zero]
    exact div_ne_zero (sub_ne_zero.2 hw) ha
  have hβ := contMDiffAt_smoothTransition_endCoord_comp zero 1 hcoordM hw'
  simp only [endSign_zero, one_mul] at hβ
  -- Periodicity makes the Cayley transforms of `J` a smooth function of the angular coordinate.
  have hFp : Periodic (fun t y => LinearMap.toContinuousLinearMap (J₀.cayley (J t y))) 1 :=
    fun t => by simp only [hJp t]
  have hC := (zero.contMDiffAt_comp_im_endCoord hFp
    (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J p.1 p.2) (fun p => hJ p.1 p.2) hJs)
    hw' x).comp ((c, a), (w, x)) (hcoordM.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))
  exact hβ.smul hC

variable {ι : Type*} [Fintype ι] {J : ι → ℝ → M → AlmostComplexStructure V}
  {hJ : ∀ i t x, ω.Tames (J i t x)} {Jout : ℝ → M → AlmostComplexStructure V}
  {hJout : ∀ t x, ω.Tames (Jout t x)}

/-- **The structures along a family of configurations are smooth.** Let the end structures be
`ω`-tame, of period one in `t` and `C^n` on `ℝ × M`. Over a manifold `N`, let the centers `c y`,
the scales `a y`, the domain point `w y` and the target point `x y` be `C^n` at `y₀`, with every
configuration satisfying the hypotheses of `TauCeti.Floer.puncturedSphereAlmostComplex`. If the
scales `a y₀ i` are nonzero and `w y₀` is none of the centers `c y₀ i`, the structures
`puncturedSphereAlmostComplex h₀ (c y) (a y) J hJ Jout hJout _ _ (w y) (x y)` are `C^n` at
`y₀`. -/
theorem contMDiffAt_puncturedSphereAlmostComplex_comp (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J i p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jout p.1 p.2).toLinearMap.toContinuousLinearMap))
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {IN : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N] {c a : N → ι → ℂ}
    {hsep : ∀ y, Pairwise fun i j => ‖a y i‖ / 2 + ‖a y j‖ / 2 ≤ ‖c y i - c y j‖}
    {hout : ∀ y i, ‖c y i‖ + ‖a y i‖ / 2 ≤ 2 * Real.exp (2 * π)} {w : N → ℂ} {x : N → M}
    {y₀ : N} (hc : ContMDiffAt IN 𝓘(ℝ, ι → ℂ) n c y₀) (ha : ContMDiffAt IN 𝓘(ℝ, ι → ℂ) n a y₀)
    (hw : ContMDiffAt IN 𝓘(ℝ, ℂ) n w y₀) (hx : ContMDiffAt IN I n x y₀)
    (ha₀ : ∀ i, a y₀ i ≠ 0) (hwc : ∀ i, w y₀ ≠ c y₀ i) :
    ContMDiffAt IN 𝓘(ℝ, V →L[ℝ] V) n (fun y => LinearMap.toContinuousLinearMap
      (puncturedSphereAlmostComplex h₀ (c y) (a y) J hJ Jout hJout (hsep y) (hout y) (w y)
        (x y)).toLinearMap) y₀ := by
  refine h₀.contMDiffAt_of_contMDiffAt_cayley
    (fun _ => tames_puncturedSphereAlmostComplex h₀ _ _) ?_
  simp only [cayley_puncturedSphereAlmostComplex, map_add, map_sum]
  refine (contMDiffAt_finsetSum fun i _ => ?_).add ?_
  · -- Each input end structure is smooth in its center, scale, domain point and target point.
    have hev : ContMDiffAt IN (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) n
        (fun y => ((c y i, a y i), (w y, x y))) y₀ :=
      ((contMDiffAt_pi_module_iff.1 hc i).prodMk_space (contMDiffAt_pi_module_iff.1 ha i)).prodMk
        (hw.prodMk hx)
    have h := (contMDiffAt_inputEndAlmostComplex h₀ (hJp i) (hJs i) (hJ := hJ i) (ha₀ i) (hwc i)
      (x y₀)).comp y₀ hev
    exact h₀.tames.contMDiffAt_cayley (tames_inputEndAlmostComplex h₀ _ _) h
  · -- The negative plane structure is smooth on the whole plane.
    have h := (contMDiff_negativePlaneAlmostComplex h₀ (hJ := hJout) hJoutp hJouts).contMDiffAt.comp
      y₀ (hw.prodMk hx)
    exact h₀.tames.contMDiffAt_cayley (tames_negativePlaneAlmostComplex h₀ _ _) h

/-- **The structure is smooth.** For end structures which are `ω`-tame, of period one in `t` and
`C^n` on `ℝ × M`, and a configuration with nonzero scales satisfying the hypotheses of
`TauCeti.Floer.puncturedSphereAlmostComplex`, the structure is `C^n` on `ℂ × M` at every domain
point other than the centers. -/
theorem contMDiffAt_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J i p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jout p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c a : ι → ℂ} {hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖}
    {hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)} (ha : ∀ i, a i ≠ 0) {w : ℂ}
    (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × M => LinearMap.toContinuousLinearMap
        (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout hsep hout p.1 p.2).toLinearMap)
      (w, x) :=
  contMDiffAt_puncturedSphereAlmostComplex_comp (c := fun _ => c) (a := fun _ => a)
    (hsep := fun _ => hsep) (hout := fun _ => hout) (w := Prod.fst) (x := Prod.snd) h₀ hJp hJs
    hJoutp hJouts contMDiffAt_const contMDiffAt_const contMDiffAt_fst contMDiffAt_snd ha hw

/-- **The structures along the associativity path form a smooth family.** For end structures which
are `ω`-tame, of period one in `t` and `C^n` on `ℝ × M`, and a plumbing factor `0 < f` with
`3 f ≤ 1`, the structure of the sphere with the input ends of the associativity path is `C^n`
jointly in the parameter `τ`, the domain point and the target point, at every domain point other
than the three centers. Together with
`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation_associativity`, this gives a smooth family of
Floer data along the path. -/
theorem contMDiffAt_puncturedSphereAlmostComplex_associativity (h₀ : ω.Compatible J₀) {n : ℕ∞}
    {J : Fin 3 → ℝ → M → AlmostComplexStructure V} {hJ : ∀ i t x, ω.Tames (J i t x)}
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J i p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jout p.1 p.2).toLinearMap.toContinuousLinearMap))
    {f : ℝ} (hf : 0 < f) (hf₃ : 3 * f ≤ 1) {τ : ℝ} {w : ℂ}
    (hw : ∀ i, w ≠ associativityCenter f τ i) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℂ × M) => LinearMap.toContinuousLinearMap
        (puncturedSphereAlmostComplex h₀ (associativityCenter f p.1) (associativityScale f p.1) J
          hJ Jout hJout (pairwise_add_le_norm_associativityCenter_sub hf.le hf₃ p.1)
          (norm_associativityCenter_add_le hf.le (by linarith) p.1) p.2.1 p.2.2).toLinearMap)
      (τ, (w, x)) :=
  contMDiffAt_puncturedSphereAlmostComplex_comp h₀ hJp hJs hJoutp hJouts
    ((contDiff_associativityCenter f).contMDiff.contMDiffAt.comp _ contMDiffAt_fst)
    ((contDiff_associativityScale f).contMDiff.contMDiffAt.comp _ contMDiffAt_fst)
    (contMDiffAt_fst.comp _ contMDiffAt_snd) (contMDiffAt_snd.comp _ contMDiffAt_snd)
    (associativityScale_ne_zero hf τ) hw

end Smooth

end TauCeti.Floer
