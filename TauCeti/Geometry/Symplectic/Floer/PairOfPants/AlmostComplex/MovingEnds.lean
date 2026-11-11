/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds

/-!
# Almost complex structures on spheres with moving input ends

The associativity of the pair-of-pants product compares the two ways of composing two products
through a family of four-punctured spheres whose input punctures move in `ℂ` while the output
stays at `∞`. Its Hamiltonian perturbations are `TauCeti.Floer.puncturedSpherePerturbation c a H
Hout`: an input end with center `c i` and nonzero scale `a i` has the end lift
`z ↦ c i + a i φ₀(z)`, where `φ₀(z) = exp (-2πz) / 2` is the end lift of the input end at `0` of
`ℂ ∖ {0, 1}`, and the output end is the end at `∞` of `ℂ ∖ {0, 1}`. This file constructs the
matching domain-dependent almost complex structures.

The structures act on a fixed symplectic vector space `(V, ω)` and may depend on a point `x` of a
manifold `M`. Fix an `ω`-compatible base structure `J₀`, families `J i (t, x)` of `ω`-tame
structures on the input ends and a family `Jout (t, x)` on the output end. The Cayley coordinate
`TauCeti.Floer.puncturedSphereCayley J₀ c a J Jout w x` is

`∑ i, β(s_i(w) - 1) • cayley (J i (t_i(w), x)) + β(-s_∞(w) - 1) • cayley (Jout (t_∞(w), x))`,

where `s_i + i t_i` is the end coordinate of the end at `0` at `(w - c i) / a i`, `s_∞ + i t_∞` is
the end coordinate of the end at `∞` at `w`, and `β` is the smooth transition. The weight of the
input `i` vanishes off the disc `‖w - c i‖ < ‖a i‖ exp (-2π) / 2`, and the weight of the output
vanishes on the disc `‖w‖ ≤ 2 exp (2π)`. So when these input discs are pairwise disjoint and lie in
the output disc, at most one weight is nonzero at each point and the Cayley coordinate lies in the
Cayley ball (`TauCeti.Floer.puncturedSphereCayley_mem`). The structure
`TauCeti.Floer.puncturedSphereAlmostComplex h₀ c a J Jout` is its inverse Cayley transform there,
and `J₀` at configurations where the Cayley coordinate leaves the ball. The results are:

* `TauCeti.Floer.tames_puncturedSphereAlmostComplex` and
  `TauCeti.Floer.compatible_puncturedSphereAlmostComplex`: the structure is `ω`-tame, and it is
  `ω`-compatible when the end structures are.
* `TauCeti.Floer.cayley_puncturedSphereAlmostComplex`: for separated input discs its Cayley
  transform is `puncturedSphereCayley J₀ c a J Jout`.
* `TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift` and
  `TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift_inf`: if the end structures have
  period one, it is `J i (t, x)` far out on the input end `i`, in its end lift
  `z ↦ c i + a i φ₀(z)`, and `Jout (t, x)` far out on the output end. These are the end coordinates
  in which `puncturedSpherePerturbation c a H Hout` is `H i (t) dt` and `Hout (t) dt`.
* `TauCeti.Floer.puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex`: off the input discs
  it is the negative plane structure of `Jout`, in particular `J₀` between the ends.
* `TauCeti.Floer.puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex`: the pair-of-pants
  structure is the case of the inputs `0` and `1` with scales `1` and `-1`, and
  `TauCeti.Floer.pairOfPantsAlmostComplex_update_base_eq_puncturedSphereAlmostComplex`: with one
  input structure replaced by `J₀`, it is the case of the single other input.
* `TauCeti.Floer.plumbedAlmostComplex_update_base_eq_puncturedSphereAlmostComplex`: the plumbed
  structure of a composition of two pairs of pants (`TauCeti.Floer.plumbedAlmostComplex`), with the
  structures of the two glued ends replaced by `J₀`, is the case of three input ends, just as the
  plumbed perturbation with the neck Hamiltonian switched off is
  `puncturedSpherePerturbation` of three input ends
  (`TauCeti.Floer.plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`). This places the
  two compositions of the associativity family in the moving-ends family of Floer data.
* `TauCeti.Floer.contMDiffAt_puncturedSphereAlmostComplex`: for period-one `C^n` end families, the
  structure is `C^n` jointly in the centers, the scales, the domain point and the point `x`, on the
  open set of configurations with nonzero scales whose input discs are strictly separated, away from
  the centers. So it is a smooth family over any smooth path of such configurations.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured surfaces with ends and consistent Floer data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the contractibility of the spaces of tame and compatible structures.
-/

public noncomputable section

open Set Real Manifold Topology Function Filter
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V ι : Type*} [Fintype ι]

section Algebraic

variable [AddCommGroup V] [Module ℝ V] {J₀ : AlmostComplexStructure V} {c a : ι → ℂ}
  {J : ι → ℝ → M → AlmostComplexStructure V} {Jout : ℝ → M → AlmostComplexStructure V}

variable (J₀ c a J Jout) in
/-- The Cayley coordinate, relative to `J₀`, of the almost complex structure on the sphere with
input ends of centers `c i`, scales `a i` and structures `J i`, and output end at `∞` with
structure `Jout`: the sum over the ends of the end weight times the Cayley transform of the end
structure at the angular coordinate of that end,

`∑ i, β(s_i(w) - 1) • cayley (J i (t_i(w), x)) + β(-s_∞(w) - 1) • cayley (Jout (t_∞(w), x))`,

where `s_i + i t_i` is the end coordinate of the end at `0` at `(w - c i) / a i` and `s_∞ + i t_∞`
the end coordinate of the end at `∞` at `w`. -/
def puncturedSphereCayley (w : ℂ) (x : M) : Module.End ℝ V :=
  ∑ i, smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
      J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) +
    smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x)

theorem puncturedSphereCayley_def (w : ℂ) (x : M) :
    puncturedSphereCayley J₀ c a J Jout w x =
      ∑ i, smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
          J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) +
        smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) :=
  (rfl)

/-- **Off the input discs only the output end contributes.** At a point outside the discs
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2`, the Cayley coordinate is the output term. -/
theorem puncturedSphereCayley_of_forall_le_norm_sub {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) (x : M) :
    puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) := by
  rw [puncturedSphereCayley_def, Finset.sum_eq_zero fun i _ => ?_, zero_add]
  rw [smoothTransition_eq_zero_of_le_norm_sub (hw i), zero_smul]

/-- **At most one end contributes.** If discs `‖w - c j‖ < r j` containing the discs
`‖w - c j‖ < ‖a j‖ exp (-2π) / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`,
then at a point of the disc of the input `i` the Cayley coordinate is the term of that input
alone. -/
theorem puncturedSphereCayley_of_norm_sub_lt {r : ι → ℝ}
    (hr : ∀ j, ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ r j)
    (hsep : Pairwise fun i j => r i + r j ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + r i ≤ 2 * Real.exp (2 * π)) {i : ι} {w : ℂ} (hw : ‖w - c i‖ < r i)
    (x : M) :
    puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
        J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) := by
  -- The other input discs and the output end are disjoint from the disc of the input `i`.
  have hj (j : ι) (hji : j ≠ i) :
      smoothTransition ((zero.endCoord ((w - c j) / a j)).re - 1) = 0 := by
    refine smoothTransition_eq_zero_of_le_norm_sub ?_
    have h₂ : ‖c j - c i‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
      simpa using norm_sub_le (w - c i) (w - c j)
    linarith [hsep hji, hr j]
  have hinf : smoothTransition (-(inf.endCoord w).re - 1) = 0 := by
    refine smoothTransition_eq_zero_of_norm_le ?_
    have h₂ : ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by simpa using norm_add_le (c i) (w - c i)
    linarith [hout i]
  rw [puncturedSphereCayley_def, Finset.sum_eq_single i (fun j _ hji => by rw [hj j hji, zero_smul])
    (by simp), hinf, zero_smul, add_zero]

/-- **The Cayley coordinate lies in every convex set containing the end coordinates.** If the
discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, at most one end weight is nonzero at each point, so the Cayley coordinate lies
in every convex set containing `0` and the Cayley transforms of all the end structures, such as the
Cayley ball and the compatible Cayley ball. -/
theorem puncturedSphereCayley_mem {s : Set (Module.End ℝ V)} (hs : Convex ℝ s)
    (h0 : (0 : Module.End ℝ V) ∈ s) (hJ : ∀ i t x, J₀.cayley (J i t x) ∈ s)
    (hJout : ∀ t x, J₀.cayley (Jout t x) ∈ s)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) (w : ℂ)
    (x : M) : puncturedSphereCayley J₀ c a J Jout w x ∈ s := by
  have hmem {b : ℝ} {K : Module.End ℝ V} (hK : K ∈ s) : smoothTransition b • K ∈ s :=
    hs.smul_mem_of_zero_mem h0 hK ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  by_cases h : ∃ i, ‖w - c i‖ < ‖a i‖ * Real.exp (-(2 * π)) / 2
  · obtain ⟨i, hi⟩ := h
    rw [puncturedSphereCayley_of_norm_sub_lt (fun _ => le_rfl) hsep hout hi]
    exact hmem (hJ _ _ _)
  · push Not at h
    rw [puncturedSphereCayley_of_forall_le_norm_sub h]
    exact hmem (hJout _ _)

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V}

open Classical in
/-- **The almost complex structure on a sphere with moving input ends.** For input ends with
centers `c i`, scales `a i` and families `J i` of `ω`-tame structures, and the output end at `∞`
with the family `Jout`, relative to an `ω`-compatible base structure `J₀`: the inverse Cayley
transform of `puncturedSphereCayley J₀ c a J Jout w x` where it lies in the Cayley ball, as it does
everywhere when the discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` are pairwise disjoint and lie in the
disc `‖w‖ ≤ 2 exp (2π)` (`TauCeti.Floer.cayley_puncturedSphereAlmostComplex`), and `J₀` where it
does not. -/
def puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (c a : ι → ℂ)
    (J : ι → ℝ → M → AlmostComplexStructure V) (Jout : ℝ → M → AlmostComplexStructure V)
    (w : ℂ) (x : M) : AlmostComplexStructure V :=
  if h : puncturedSphereCayley J₀ c a J Jout w x ∈ ω.cayleyBall J₀ then
    h₀.cayleyEquiv.symm ⟨_, h⟩
  else J₀

/-- The structure on a sphere with moving input ends is tamed by `ω`. -/
theorem tames_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (puncturedSphereAlmostComplex h₀ c a J Jout w x) := by
  unfold puncturedSphereAlmostComplex
  split_ifs
  exacts [(h₀.cayleyEquiv.symm _).2, h₀.tames]

/-- Where the Cayley coordinate lies in the Cayley ball, it is the Cayley transform of the
structure. -/
theorem cayley_puncturedSphereAlmostComplex_of_mem (h₀ : ω.Compatible J₀) {w : ℂ} {x : M}
    (h : puncturedSphereCayley J₀ c a J Jout w x ∈ ω.cayleyBall J₀) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout w x) =
      puncturedSphereCayley J₀ c a J Jout w x := by
  simp only [puncturedSphereAlmostComplex, h, ↓reduceDIte]
  rw [← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- **The structure is determined by its Cayley transform.** A tame structure whose Cayley
transform, relative to `J₀`, is the Cayley coordinate is the structure on the sphere with moving
input ends. -/
theorem eq_puncturedSphereAlmostComplex_of_cayley_eq (h₀ : ω.Compatible J₀)
    {K : AlmostComplexStructure V} (hK : ω.Tames K) {w : ℂ} {x : M}
    (h : J₀.cayley K = puncturedSphereCayley J₀ c a J Jout w x) :
    K = puncturedSphereAlmostComplex h₀ c a J Jout w x := by
  refine h₀.eq_of_cayley_eq hK (tames_puncturedSphereAlmostComplex h₀ w x) ?_
  rw [cayley_puncturedSphereAlmostComplex_of_mem h₀ (h ▸ h₀.cayley_mem_cayleyBall hK), h]

/-- **The Cayley transform of the structure.** If the end structures are `ω`-tame and the discs
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`,
the Cayley transform of the structure, relative to `J₀`, is `puncturedSphereCayley J₀ c a J Jout`.
This characterizes the structure, since the Cayley transform is injective on tame structures. -/
theorem cayley_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ : ∀ i t x, ω.Tames (J i t x)) (hJout : ∀ t x, ω.Tames (Jout t x))
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) (w : ℂ)
    (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout w x) =
      puncturedSphereCayley J₀ c a J Jout w x :=
  cayley_puncturedSphereAlmostComplex_of_mem h₀ (puncturedSphereCayley_mem
    h₀.tames.convex_cayleyBall h₀.tames.zero_mem_cayleyBall
    (fun i t x => h₀.cayley_mem_cayleyBall (hJ i t x))
    (fun t x => h₀.cayley_mem_cayleyBall (hJout t x)) hsep hout w x)

/-- The structure on a sphere with moving input ends is `ω`-compatible when the structures on the
ends are. -/
theorem compatible_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ i t x, ω.Compatible (J i t x)) (hJoutc : ∀ t x, ω.Compatible (Jout t x)) (w : ℂ)
    (x : M) : ω.Compatible (puncturedSphereAlmostComplex h₀ c a J Jout w x) := by
  by_cases h : puncturedSphereCayley J₀ c a J Jout w x ∈ ω.cayleyBall J₀
  · refine (h₀.cayley_mem_compatibleCayleyBall_iff
      (tames_puncturedSphereAlmostComplex h₀ w x)).mp ?_
    rw [cayley_puncturedSphereAlmostComplex_of_mem h₀ h]
    -- The Cayley transforms of compatible structures are self-adjoint for `ω(·, J₀ ·)`, and so is
    -- their weighted sum.
    have hsa {K : AlmostComplexStructure V} (hK : ω.Compatible K) (v v' : V) :
        ω (J₀.cayley K v) (J₀ v') = ω v (J₀ (J₀.cayley K v')) :=
      (SymplecticForm.mem_compatibleCayleyBall.1
        ((h₀.cayley_mem_compatibleCayleyBall_iff hK.tames).2 hK)).2 v v'
    have hJsa (i : ι) (t : ℝ) (y : M) := hsa (hJc i t y)
    have hJoutsa (t : ℝ) (y : M) := hsa (hJoutc t y)
    refine SymplecticForm.mem_compatibleCayleyBall.2 ⟨h, fun v v' => ?_⟩
    simp [puncturedSphereCayley_def, map_sum, hJsa, hJoutsa]
  · simp only [puncturedSphereAlmostComplex, h, ↓reduceDIte]
    exact h₀

/-- **Off the input discs the structure is the negative plane structure.** At a point outside the
discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2`, the structure is the negative plane structure of the
output structure. In particular it is `J₀` there if moreover `‖w‖ ≤ 2 exp (2π)`
(`TauCeti.Floer.negativePlaneAlmostComplex_eq_of_norm_le`). -/
theorem puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀)
    (hJout : ∀ t x, ω.Tames (Jout t x)) {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J Jout w x =
      negativePlaneAlmostComplex h₀ Jout hJout w x := by
  refine (eq_puncturedSphereAlmostComplex_of_cayley_eq h₀
    (tames_negativePlaneAlmostComplex h₀ w x) ?_).symm
  rw [puncturedSphereCayley_of_forall_le_norm_sub hw, cayley_negativePlaneAlmostComplex]

/-- **The structure on an input end.** If the discs `‖w - c j‖ < ‖a j‖ / 2` are pairwise disjoint
and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and `J i` has period one in `t`, then on the part `s > 0`
of the input end `i`, the Cayley transform of the structure at the point `c i + a i φ₀(z)` with end
coordinates `z = s + i t` is `β(s - 1) • cayley (J i t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos
    (h₀ : ω.Compatible J₀) (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι}
    (hJ : ∀ t x, ω.Tames (J i t x)) (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout (c i + a i * zero.cylindricalEndLift z)
      x) = smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
  set w := c i + a i * zero.cylindricalEndLift z
  have hlt : ‖w - c i‖ < ‖a i‖ / 2 := by
    rw [add_sub_cancel_left]
    exact norm_mul_cylindricalEndLift_zero_lt ha hz
  have hφ : (w - c i) / a i = zero.cylindricalEndLift z := by
    simp only [w, add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
  -- Only the input `i` contributes at `w`.
  have hC : puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
    obtain ⟨k, hk⟩ := zero.exists_endCoord_cylindricalEndLift z
    have him : (zero.endCoord (zero.cylindricalEndLift z)).im = z.im + k := by
      rw [hk]
      simp
    have hp : J i (z.im + k) = J i z.im := by simpa using hJp.int_mul k z.im
    rw [puncturedSphereCayley_of_norm_sub_lt (r := fun j => ‖a j‖ / 2) (fun j => ?_) hsep hout hlt,
      hφ, re_endCoord_cylindricalEndLift, him, hp]
    have he : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Real.pi_pos])
    nlinarith [norm_nonneg (a j)]
  rw [cayley_puncturedSphereAlmostComplex_of_mem h₀ (hC ▸ h₀.smul_cayley_mem_cayleyBall (hJ _ x)
    (abs_le.2 ⟨by linarith [smoothTransition.nonneg (z.re - 1)], smoothTransition.le_one _⟩)), hC]

/-- **The structure is `J i t` far out on each input end.** Under the hypotheses of
`TauCeti.Floer.cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos`, on the part
`s ≥ 2` of the input end `i` the structure at the point `c i + a i φ₀(z)` with end coordinates
`z = s + i t` is `J i t x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {i : ι}
    (hJ : ∀ t x, ω.Tames (J i t x)) (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J Jout (c i + a i * zero.cylindricalEndLift z) x =
      J i z.im x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJ z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos h₀ hsep hout hJ hJp ha
    (by linarith), smoothTransition.one_of_one_le (by linarith), one_smul]

/-- **The structure on the output end.** If the discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` lie in the
disc `‖w‖ ≤ 2 exp (2π)` and `Jout` has period one in `t`, then on the part `s ≤ -1` of the output
end the Cayley transform of the structure at the point with end coordinates `z = s + i t` is
`β(-s - 1) • cayley (Jout t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le (h₀ : ω.Compatible J₀)
    (hJout : ∀ t x, ω.Tames (Jout t x))
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    (hJoutp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -1) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout (inf.cylindricalEndLift z) x) =
      smoothTransition (-z.re - 1) • J₀.cayley (Jout z.im x) := by
  have hnorm : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    gcongr
    nlinarith [Real.pi_pos]
  have hw (i : ι) : ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖inf.cylindricalEndLift z - c i‖ := by
    have h := norm_sub_norm_le (inf.cylindricalEndLift z) (c i)
    linarith [hout i]
  rw [puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex h₀ hJout hw,
    cayley_negativePlaneAlmostComplex_cylindricalEndLift_of_neg h₀ hJoutp (by linarith)]

/-- **The structure is `Jout t` far out on the output end.** Under the hypotheses of
`TauCeti.Floer.cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le`, on the part
`s ≤ -2` of the output end the structure at the point with end coordinates `z = s + i t` is
`Jout t x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJout : ∀ t x, ω.Tames (Jout t x))
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    (hJoutp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J Jout (inf.cylindricalEndLift z) x = Jout z.im x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJout z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le h₀ hJout hout hJoutp
    (by linarith), smoothTransition.one_of_one_le (by linarith), one_smul]

end Algebraic

/-! ### The pair of pants as a sphere with moving input ends -/

section PairOfPants

variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {J₀ : AlmostComplexStructure V} {J : Puncture → ℝ → M → AlmostComplexStructure V}

/-- **The pair of pants has two input ends.** The pair-of-pants structure is the structure on the
sphere with the input ends of centers `0` and `1` and scales `1` and `-1`, with the structures of
the two inputs, and with its output structure. -/
theorem puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Tames (J q t x)) :
    puncturedSphereAlmostComplex h₀ ![0, 1] ![1, -1] ![J zero, J one] (J inf) =
      pairOfPantsAlmostComplex h₀ J hJ := by
  funext w x
  refine (eq_puncturedSphereAlmostComplex_of_cayley_eq h₀
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_).symm
  have h₁ : zero.endCoord ((w - 1) / -1) = one.endCoord w := by
    simpa using endCoord_zero_sub_endCenter_div one w
  rw [cayley_pairOfPantsAlmostComplex, Puncture.sum_univ, puncturedSphereCayley_def,
    Fin.sum_univ_two]
  simp [h₁, add_assoc]

/-- **A pair of pants with one input structure switched off has one input end.** With the
structure of the input `q` replaced by the base structure `J₀`, the pair-of-pants structure is the
structure on the sphere with the single input end of the other input `r`, of center `c_r` and scale
`2 b_r`, and with the output structure. -/
theorem pairOfPantsAlmostComplex_update_base_eq_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    {q r : Puncture} (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf)
    (hJ' : ∀ p t x, ω.Tames (update J q (fun _ _ => J₀) p t x)) :
    pairOfPantsAlmostComplex h₀ (update J q fun _ _ => J₀) hJ' =
      puncturedSphereAlmostComplex h₀ ![r.endCenter] ![2 * r.endScale] ![J r] (J inf) := by
  funext w x
  refine eq_puncturedSphereAlmostComplex_of_cayley_eq h₀
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_pairOfPantsAlmostComplex, Puncture.sum_univ, puncturedSphereCayley_def,
    Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, endCoord_zero_sub_endCenter_div]
  cases q <;> cases r <;> simp_all [AlmostComplexStructure.cayley_self]

/-- **With the neck structure switched off, the plumbed sphere has moving input ends.** Plumb the
output end of a pair of pants with end structures `Ja` into the input end `q ≠ ∞` of one with end
structures `Jb`, along a neck of length `L ≥ 0`, over the same base structure `J₀`, with the
structures of the two glued ends replaced by `J₀`. The plumbed structure
(`TauCeti.Floer.plumbedAlmostComplex`) is the structure on the sphere with the three input ends of
centers `c_q`, `ψ(1)` and `c_r`, scales `f`, `-f` and `2 b_r`, and structures `Ja 0`, `Ja 1` and
`Jb r`, and with output structure `Jb ∞`. Here `r` is the other input, `ψ` the plumbing map, `f` the
plumbing factor and `b_r` the scale of the end `r`. This is the counterpart for almost complex
structures of `TauCeti.Floer.plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`. -/
theorem plumbedAlmostComplex_update_base_eq_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    {Ja Jb : Puncture → ℝ → M → AlmostComplexStructure V} {q r : Puncture} (hq : q ≠ inf)
    (hrq : r ≠ q) (hr : r ≠ inf) {L : ℝ} (hL : 0 ≤ L)
    (hJa : ∀ p t x, ω.Tames (update Ja inf (fun _ _ => J₀) p t x))
    (hJb : ∀ p t x, ω.Tames (update Jb q (fun _ _ => J₀) p t x)) :
    plumbedAlmostComplex h₀ h₀ (update Ja inf fun _ _ => J₀) (update Jb q fun _ _ => J₀) hJa hJb
        q L =
      puncturedSphereAlmostComplex h₀ ![q.endCenter, q.plumbingMap L 1, r.endCenter]
        ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] ![Ja zero, Ja one, Jb r]
        (Jb inf) := by
  funext w x
  rw [plumbedAlmostComplex_def]
  split_ifs with h
  · -- On the inserted half only the two inputs of the inserted pair of pants contribute.
    refine eq_puncturedSphereAlmostComplex_of_cayley_eq h₀
      (tames_pairOfPantsAlmostComplex h₀ _ x) ?_
    obtain ⟨h₁, h₂⟩ := exp_neg_two_pi_div_two_le_norm_sub_endCenter_and_norm_le hq hrq hr hL h
    have hr₀ : smoothTransition ((zero.endCoord ((w - r.endCenter) / (2 * r.endScale))).re - 1) =
        0 := smoothTransition_eq_zero_of_le_norm_sub (by rwa [norm_two_mul_endScale hr, one_mul])
    set v := (w - q.endCenter) / q.plumbingFactor L
    have hf := q.plumbingFactor_ne_zero L
    have hv₁ : zero.endCoord ((w - q.plumbingMap L 1) / -q.plumbingFactor L) = one.endCoord v := by
      have h' := endCoord_zero_sub_endCenter_div one v
      simp only [endCenter_one, endScale_one] at h'
      rw [← h', plumbingMap_apply]
      congr 1
      simp only [v]
      field_simp
      ring
    rw [cayley_pairOfPantsAlmostComplex, Puncture.sum_univ, puncturedSphereCayley_def,
      Fin.sum_univ_three]
    simp [hr₀, smoothTransition_eq_zero_of_norm_le h₂, hv₁, v,
      AlmostComplexStructure.cayley_self]
  · -- On the receiving part the two inputs of the inserted pair of pants do not contribute.
    refine eq_puncturedSphereAlmostComplex_of_cayley_eq h₀
      (tames_pairOfPantsAlmostComplex h₀ _ x) ?_
    have hle : (q.endCoord w).re ≤ L / 2 := not_lt.1 h
    have hψ := smoothTransition_eq_zero_of_le_norm_sub (c := q.plumbingMap L 1)
      (a := -q.plumbingFactor L) (by
        rw [norm_neg]
        exact norm_plumbingFactor_mul_exp_div_two_le_norm_sub_plumbingMap_one hq hL hle)
    have hc : smoothTransition ((zero.endCoord ((w - q.endCenter) / q.plumbingFactor L)).re - 1) =
        0 := by
      rcases eq_or_ne w q.endCenter with rfl | hc
      · exact smoothTransition_eq_zero_of_sub_div_eq_zero (by rw [sub_self, zero_div])
      · exact smoothTransition_eq_zero_of_le_norm_sub
          (norm_plumbingFactor_mul_exp_div_two_le_norm_sub_endCenter hq hL hc hle)
    rw [cayley_pairOfPantsAlmostComplex, Puncture.sum_univ, puncturedSphereCayley_def,
      Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hψ, hc, zero_smul, zero_add, endCoord_zero_sub_endCenter_div]
    cases q <;> cases r <;> simp_all [AlmostComplexStructure.cayley_self]

end PairOfPants

/-! ### Smoothness -/

section Smooth

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : ι → ℝ → M → AlmostComplexStructure V} {Jout : ℝ → M → AlmostComplexStructure V}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- The term `β(s_i - 1) • cayley (K (t_i, x))` of the input `i` of the Cayley coordinate, for a
period-one `C^n` family `K`, is `C^n` jointly in the configuration, the domain point and `x`, at
configurations with `a i ≠ 0` and domain points `w ≠ c i`. Here `s_i + i t_i` is the end
coordinate of the end at `0` at `(w - c i) / a i`. -/
private theorem contMDiffAt_inputCayley (h₀ : ω.Compatible J₀) {n : ℕ∞}
    {K : ℝ → M → AlmostComplexStructure V} (hK : ∀ t x, ω.Tames (K t x)) (hKp : Periodic K 1)
    (hKs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (K p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c a : ι → ℂ} (i : ι) (ha : a i ≠ 0) {w : ℂ} (hw : w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        smoothTransition ((zero.endCoord ((p.2.1 - p.1.1 i) / p.1.2 i)).re - 1) •
          LinearMap.toContinuousLinearMap
            (J₀.cayley (K (zero.endCoord ((p.2.1 - p.1.1 i) / p.1.2 i)).im p.2.2)))
      ((c, a), (w, x)) := by
  -- In the end coordinate `v` of the end at `0` the term is smooth away from `v = 0`.
  have hv : (w - c i) / a i ≠ zero.endCenter := by
    simpa using div_ne_zero (sub_ne_zero.2 hw) ha
  have hFp : Periodic (fun t y => LinearMap.toContinuousLinearMap (J₀.cayley (K t y))) 1 :=
    fun t => by simp only [hKp t]
  have hterm := (contMDiffAt_smoothTransition_endCoord (n := n) zero 1 hv x).smul
    (zero.contMDiffAt_comp_im_endCoord hFp
      (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => K p.1 p.2) (fun p => hK p.1 p.2) hKs)
      hv x)
  simp only [endSign_zero, one_mul] at hterm
  -- The end coordinate `v = (w - c i) / a i` is a smooth function of the configuration and `w`.
  exact hterm.comp ((c, a), (w, x)) ((contMDiffAt_sub_div_prodMk ha w x).comp ((c, a), (w, x))
    (contMDiff_prodMap_apply i).contMDiffAt)

omit [Fintype ι] in
/-- Strict separation of the input discs, and of the input discs from the circle
`‖w‖ = 2 exp (2π)`, persists on a neighbourhood of a configuration, in its weak form. -/
private theorem eventually_separated [Finite ι] {c a : ι → ℂ}
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 < ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 < 2 * Real.exp (2 * π)) :
    ∀ᶠ ca : (ι → ℂ) × (ι → ℂ) in 𝓝 (c, a),
      (Pairwise fun i j => ‖ca.2 i‖ * Real.exp (-(2 * π)) / 2 +
        ‖ca.2 j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖ca.1 i - ca.1 j‖) ∧
      ∀ i, ‖ca.1 i‖ + ‖ca.2 i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π) := by
  have hcont {f : (ι → ℂ) × (ι → ℂ) → ℝ} (hf : Continuous f) (h : 0 < f (c, a)) :
      ∀ᶠ ca in 𝓝 (c, a), 0 < f ca := hf.continuousAt.eventually (lt_mem_nhds h)
  refine (eventually_all.2 fun i => eventually_all.2 fun j => ?_).and
    (eventually_all.2 fun i => ?_)
  · by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · filter_upwards [hcont (f := fun ca => ‖ca.1 i - ca.1 j‖ -
          (‖ca.2 i‖ * Real.exp (-(2 * π)) / 2 + ‖ca.2 j‖ * Real.exp (-(2 * π)) / 2))
          (by fun_prop) (by simpa using hsep hij)] with ca hca _
      linarith
  · filter_upwards [hcont (f := fun ca => 2 * Real.exp (2 * π) -
        (‖ca.1 i‖ + ‖ca.2 i‖ * Real.exp (-(2 * π)) / 2)) (by fun_prop)
        (by simpa using hout i)] with ca hca
    linarith

/-- **The structure is smooth in the configuration.** For families `J i` and `Jout` of `ω`-tame
structures which have period one in `t` and are `C^n` on `ℝ × M`, the structure on a sphere with
moving input ends is `C^n` jointly in the centers, the scales, the domain point and the point `x`,
at every configuration with nonzero scales whose discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` have
strictly separated closures inside the open disc `‖w‖ < 2 exp (2π)`, and every domain point other
than the centers. These configurations form an open set, so composing with a smooth path of
configurations gives a smooth family of structures. -/
theorem contMDiffAt_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJ : ∀ i t x, ω.Tames (J i t x)) (hJout : ∀ t x, ω.Tames (Jout t x))
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J i p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jout p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c a : ι → ℂ} (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 < ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 < 2 * Real.exp (2 * π)) {w : ℂ}
    (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => LinearMap.toContinuousLinearMap
        (puncturedSphereAlmostComplex h₀ p.1.1 p.1.2 J Jout p.2.1 p.2.2).toLinearMap)
      ((c, a), (w, x)) := by
  -- The Cayley coordinate, as a family of continuous endomorphisms; the output term is the Cayley
  -- transform of the negative plane structure, which is smooth on the whole plane.
  set C : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) → V →L[ℝ] V := fun p =>
    ∑ i, smoothTransition ((zero.endCoord ((p.2.1 - p.1.1 i) / p.1.2 i)).re - 1) •
        LinearMap.toContinuousLinearMap
          (J₀.cayley (J i (zero.endCoord ((p.2.1 - p.1.1 i) / p.1.2 i)).im p.2.2)) +
      LinearMap.toContinuousLinearMap
        (J₀.cayley (negativePlaneAlmostComplex h₀ Jout hJout p.2.1 p.2.2)) with hC_def
  have hC (p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M)) :
      (C p).toLinearMap = puncturedSphereCayley J₀ p.1.1 p.1.2 J Jout p.2.1 p.2.2 := by
    simp [hC_def, puncturedSphereCayley_def, cayley_negativePlaneAlmostComplex]
  refine h₀.contMDiffAt_of_eventually_cayley_eq (C := C)
    (Eventually.of_forall fun p => tames_puncturedSphereAlmostComplex h₀ _ _)
    ((contMDiffAt_finsetSum fun i _ =>
      contMDiffAt_inputCayley h₀ (hJ i) (hJp i) (hJs i) i (ha i) (hw i) x).add
      (((h₀.tames.contMDiff_cayley
        (fun p : ℂ × M => tames_negativePlaneAlmostComplex h₀ p.1 p.2)
        (contMDiff_negativePlaneAlmostComplex h₀ hJoutp hJouts)).contMDiffAt).comp
        ((c, a), (w, x)) contMDiffAt_snd)) ?_
  -- Near the configuration the input discs stay separated, so the Cayley coordinate stays in the
  -- Cayley ball and is the Cayley transform of the structure.
  filter_upwards [((continuous_fst (X := (ι → ℂ) × (ι → ℂ)) (Y := ℂ × M)).tendsto
    ((c, a), (w, x))).eventually (eventually_separated hsep hout)] with p hp
  rw [hC, cayley_puncturedSphereAlmostComplex h₀ hJ hJout hp.1 hp.2]

end Smooth

end TauCeti.Floer
