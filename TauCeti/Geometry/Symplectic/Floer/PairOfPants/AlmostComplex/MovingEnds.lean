/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
import Mathlib.Geometry.Manifold.Algebra.SMul

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
the disc `‖w‖ ≤ 2 exp (2π)`, at most one weight is nonzero at each point and the Cayley coordinate
lies in the Cayley ball (`TauCeti.Floer.puncturedSphereCayley_mem`). The structure
`TauCeti.Floer.puncturedSphereAlmostComplex h₀ c a J Jout w x` is the inverse Cayley transform of
`puncturedSphereCayley J₀ c a J Jout w x` at the points `(w, x)` where this lies in the Cayley ball,
and `J₀` at the points where it does not (`TauCeti.Floer.puncturedSphereAlmostComplex_of_notMem`).
The results are:

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
  rw [smoothTransition_endCoord_zero_eq_zero_of_le_norm_sub (hw i), zero_smul]

/-- **Only the input `i` contributes away from the other input discs.** At a point outside the
discs `‖w - c j‖ < ‖a j‖ exp (-2π) / 2` of the inputs `j ≠ i` and in the disc `‖w‖ ≤ 2 exp (2π)`,
the Cayley coordinate is the term of the input `i` alone. -/
theorem puncturedSphereCayley_of_forall_ne {i : ι} {w : ℂ}
    (hne : ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c j‖)
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
        J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) := by
  rw [puncturedSphereCayley_def, Finset.sum_eq_single i (fun j _ hji => by
      rw [smoothTransition_endCoord_zero_eq_zero_of_le_norm_sub (hne j hji), zero_smul]) (by simp),
    smoothTransition_neg_endCoord_inf_eq_zero_of_norm_le hw, zero_smul, add_zero]

/-- **At most one end contributes.** If the disc `‖w - c i‖ < r i` is disjoint from discs
`‖w - c j‖ < r j` containing the discs `‖w - c j‖ < ‖a j‖ exp (-2π) / 2` of the other inputs, and
lies in the disc `‖w‖ ≤ 2 exp (2π)`, then at a point of the disc of the input `i` the Cayley
coordinate is the term of that input alone. -/
theorem puncturedSphereCayley_of_norm_sub_lt {r : ι → ℝ} {i : ι}
    (hr : ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ r j)
    (hsep : ∀ j, j ≠ i → r i + r j ≤ ‖c i - c j‖) (hout : ‖c i‖ + r i ≤ 2 * Real.exp (2 * π))
    {w : ℂ} (hw : ‖w - c i‖ < r i) (x : M) :
    puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
        J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) :=
  puncturedSphereCayley_of_forall_ne (le_norm_sub_of_norm_sub_lt hr hsep hw)
    (norm_le_two_mul_exp_of_norm_sub_lt hout hw) x

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
    rw [puncturedSphereCayley_of_norm_sub_lt (fun _ _ => le_rfl) (fun _ hji => hsep hji.symm)
      (hout i) hi]
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

open Classical in
theorem puncturedSphereAlmostComplex_def (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J Jout w x =
      if h : puncturedSphereCayley J₀ c a J Jout w x ∈ ω.cayleyBall J₀ then
        (h₀.cayleyEquiv.symm ⟨_, h⟩ : AlmostComplexStructure V)
      else J₀ :=
  (rfl)

/-- **The fallback to the base structure.** Where the Cayley coordinate leaves the Cayley ball,
the structure is `J₀`. -/
@[simp]
theorem puncturedSphereAlmostComplex_of_notMem (h₀ : ω.Compatible J₀) {w : ℂ} {x : M}
    (h : puncturedSphereCayley J₀ c a J Jout w x ∉ ω.cayleyBall J₀) :
    puncturedSphereAlmostComplex h₀ c a J Jout w x = J₀ := by
  simp only [puncturedSphereAlmostComplex_def, h, ↓reduceDIte]

/-- The structure on a sphere with moving input ends is tamed by `ω`. -/
theorem tames_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (puncturedSphereAlmostComplex h₀ c a J Jout w x) := by
  rw [puncturedSphereAlmostComplex_def]
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

/-- **The structure depends only on the Cayley coordinate.** Two configurations of input ends
whose Cayley coordinates agree at the points `(w, x)` and `(w', x')` carry the same structure
there. -/
theorem puncturedSphereAlmostComplex_congr (h₀ : ω.Compatible J₀) {κ : Type*} [Fintype κ]
    {c' a' : κ → ℂ} {J' : κ → ℝ → M → AlmostComplexStructure V}
    {Jout' : ℝ → M → AlmostComplexStructure V} {w w' : ℂ} {x x' : M}
    (h : puncturedSphereCayley J₀ c a J Jout w x = puncturedSphereCayley J₀ c' a' J' Jout' w' x') :
    puncturedSphereAlmostComplex h₀ c a J Jout w x =
      puncturedSphereAlmostComplex h₀ c' a' J' Jout' w' x' := by
  rw [puncturedSphereAlmostComplex_def, puncturedSphereAlmostComplex_def]
  generalize puncturedSphereCayley J₀ c' a' J' Jout' w' x' = C at h ⊢
  subst h
  rfl

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
    have hsa {K : AlmostComplexStructure V} (hK : ω.Compatible K) :
        J₀.cayley K ∈ (ω.associatedBilinForm J₀).selfAdjointSubmodule :=
      (SymplecticForm.mem_compatibleCayleyBall.1
        ((h₀.cayley_mem_compatibleCayleyBall_iff hK.tames).2 hK)).2
    have hmem : puncturedSphereCayley J₀ c a J Jout w x ∈
        (ω.associatedBilinForm J₀).selfAdjointSubmodule := by
      rw [puncturedSphereCayley_def]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsa (hJc i _ x)))
        (Submodule.smul_mem _ _ (hsa (hJoutc _ x)))
    exact SymplecticForm.mem_compatibleCayleyBall.2 ⟨h, hmem⟩
  · rw [puncturedSphereAlmostComplex_of_notMem h₀ h]
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

/-- **The structure on an input end, pointwise.** If `J i` has period one in `t`, then at a point
`c i + a i φ₀(z)` of the input end `i`, with end coordinates `z = s + i t`, which lies outside the
discs `‖w - c j‖ < ‖a j‖ exp (-2π) / 2` of the other inputs and in the disc `‖w‖ ≤ 2 exp (2π)`, the
Cayley transform of the structure is `β(s - 1) • cayley (J i t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_forall_ne
    (h₀ : ω.Compatible J₀) {i : ι} (hJ : ∀ t x, ω.Tames (J i t x)) (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ}
    (hne : ∀ j, j ≠ i →
      ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i + a i * zero.cylindricalEndLift z - c j‖)
    (hz : ‖c i + a i * zero.cylindricalEndLift z‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout (c i + a i * zero.cylindricalEndLift z)
      x) = smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
  set w := c i + a i * zero.cylindricalEndLift z
  have hφ : (w - c i) / a i = zero.cylindricalEndLift z := by
    simp only [w, add_sub_cancel_left, mul_div_cancel_left₀ _ ha]
  -- Only the input `i` contributes at `w`.
  have hC : puncturedSphereCayley J₀ c a J Jout w x =
      smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
    rw [puncturedSphereCayley_of_forall_ne hne hz, hφ, re_endCoord_cylindricalEndLift,
      apply_im_endCoord_cylindricalEndLift hJp]
  rw [cayley_puncturedSphereAlmostComplex_of_mem h₀ (hC ▸ h₀.smul_cayley_mem_cayleyBall (hJ _ x)
    (smoothTransition.abs_le_one (z.re - 1))), hC]

/-- **The structure on an input end, for discs of any radii.** If the disc `‖w - c i‖ < r i` is
disjoint from discs `‖w - c j‖ < r j` containing the discs `‖w - c j‖ < ‖a j‖ exp (-2π) / 2` of
the other inputs, and lies in the disc `‖w‖ ≤ 2 exp (2π)`, and `J i` has period one in `t`, then at
a point `c i + a i φ₀(z)` of the disc of the input `i`, with end coordinates `z = s + i t`, the
Cayley transform of the structure is `β(s - 1) • cayley (J i t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_norm_lt
    (h₀ : ω.Compatible J₀) {r : ι → ℝ} {i : ι}
    (hr : ∀ j, j ≠ i → ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ r j)
    (hsep : ∀ j, j ≠ i → r i + r j ≤ ‖c i - c j‖) (hout : ‖c i‖ + r i ≤ 2 * Real.exp (2 * π))
    (hJ : ∀ t x, ω.Tames (J i t x)) (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : ‖a i * zero.cylindricalEndLift z‖ < r i) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J Jout (c i + a i * zero.cylindricalEndLift z)
      x) = smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
  have hlt : ‖c i + a i * zero.cylindricalEndLift z - c i‖ < r i := by rwa [add_sub_cancel_left]
  exact cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_forall_ne h₀ hJ hJp ha
    (le_norm_sub_of_norm_sub_lt hr hsep hlt) (norm_le_two_mul_exp_of_norm_sub_lt hout hlt) x

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
      x) = smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) :=
  cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_norm_lt h₀ (r := fun j => ‖a j‖ / 2)
    (fun j _ => by nlinarith [norm_nonneg (a j), exp_neg_two_pi_lt_one])
    (fun _ hji => hsep hji.symm) (hout i) hJ hJp ha
    (by simpa using norm_mul_cylindricalEndLift_zero_lt ha hz) x

/-- **The structure is `J i t` far out on each input end.** If the discs
`‖w - c j‖ < ‖a j‖ exp (-2π) / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and
`J i` has period one in `t`, then on the part `s ≥ 2` of the input end `i` the structure at the
point `c i + a i φ₀(z)` with end coordinates `z = s + i t` is `J i t x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) {i : ι}
    (hJ : ∀ t x, ω.Tames (J i t x)) (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J Jout (c i + a i * zero.cylindricalEndLift z) x =
      J i z.im x := by
  -- On the part `s ≥ 2` the point lies in the support disc of the input `i`.
  have hlt : ‖a i * zero.cylindricalEndLift z‖ < ‖a i‖ * Real.exp (-(2 * π)) / 2 := by
    simpa using norm_mul_cylindricalEndLift_zero_lt (R := 1) ha (by linarith)
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJ z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_norm_lt h₀ (fun _ _ => le_rfl)
    (fun _ hji => hsep hji.symm) (hout i) hJ hJp ha hlt, smoothTransition.one_of_one_le
    (by linarith), one_smul]

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
    simpa only [mul_one] using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1) hz
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
    rw [← puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex h₀ hJa]
    refine puncturedSphereAlmostComplex_congr h₀ ?_
    have hpos : 0 < (q.endCoord w).re := by linarith [(by positivity : 0 ≤ L / 2)]
    have h₁ := exp_neg_two_pi_div_two_le_norm_sub_endCenter hq hr hrq hpos
    have h₂ := norm_le_two_mul_exp_of_re_endCoord_pos hq hpos
    have hr₀ : smoothTransition ((zero.endCoord ((w - r.endCenter) / (2 * r.endScale))).re - 1) =
        0 :=
      smoothTransition_endCoord_zero_eq_zero_of_le_norm_sub
        (by rwa [norm_two_mul_endScale hr, one_mul])
    rw [puncturedSphereCayley_def, puncturedSphereCayley_def, Fin.sum_univ_two,
      Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    -- The second inserted input is the input `1` of the inserted pair of pants.
    have hf := q.plumbingFactor_ne_zero L
    have hv₁ : (w - q.plumbingMap L 1) / -q.plumbingFactor L =
        ((w - q.endCenter) / q.plumbingFactor L - 1) / -1 := by
      rw [plumbingMap_apply]
      field_simp
      ring
    rw [hv₁]
    simp [hr₀, smoothTransition_neg_endCoord_inf_eq_zero_of_norm_le h₂,
      AlmostComplexStructure.cayley_self]
  · -- On the receiving part the two inputs of the inserted pair of pants do not contribute.
    rw [pairOfPantsAlmostComplex_update_base_eq_puncturedSphereAlmostComplex h₀ hq hrq hr hJb]
    refine puncturedSphereAlmostComplex_congr h₀ ?_
    have hle : (q.endCoord w).re ≤ L / 2 := not_lt.1 h
    have hψ := smoothTransition_endCoord_zero_eq_zero_of_le_norm_sub (c := q.plumbingMap L 1)
      (a := -q.plumbingFactor L) (by
        rw [norm_neg]
        exact norm_plumbingFactor_mul_exp_div_two_le_norm_sub_plumbingMap_one hq hL hle)
    have hc : smoothTransition ((zero.endCoord ((w - q.endCenter) / q.plumbingFactor L)).re - 1) =
        0 := by
      rcases eq_or_ne w q.endCenter with rfl | hc
      · rw [sub_self, zero_div, smoothTransition_endCoord_zero_zero]
      · exact smoothTransition_endCoord_zero_eq_zero_of_le_norm_sub
          (norm_plumbingFactor_mul_exp_div_two_le_norm_sub_endCenter hq hL hc hle)
    rw [puncturedSphereCayley_def, puncturedSphereCayley_def, Fin.sum_univ_one,
      Fin.sum_univ_three]
    simp [hψ, hc]

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
    (contMDiff_apply_prodMk i).contMDiffAt)

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
  refine h₀.tames.contMDiffAt_of_eventually_cayley_eq (C := C)
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
    ((c, a), (w, x))).eventually
    (eventually_pairwise_add_lt_norm_sub_and_norm_add_lt hsep hout)] with p hp
  rw [hC, cayley_puncturedSphereAlmostComplex h₀ hJ hJout (fun _ _ hij => (hp.1 hij).le)
    fun i => (hp.2 i).le]

end Smooth

end TauCeti.Floer
