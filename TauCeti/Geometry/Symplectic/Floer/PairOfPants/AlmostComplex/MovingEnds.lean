/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
import TauCeti.Analysis.Convex.Combination
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Domain-dependent almost complex structures on spheres with moving input ends

The associativity of the pair-of-pants product is proved over a family of four-punctured spheres
whose input punctures move in `ℂ`, the output sitting at `∞`. The Floer equation on each member
needs a Hamiltonian perturbation, `TauCeti.Floer.puncturedSpherePerturbation`, and an almost
complex structure `J_w` depending on the domain point which, far out on each end, is the
time-dependent structure already chosen for the Floer complex of that end. This file constructs
such structures for any finite set of input ends, as a family which is smooth in the positions of
the ends.

An input end is given by a center `c` and a nonzero scale `a`: its end lift is
`z ↦ c + a φ₀(z)`, where `φ₀(z) = exp (-2πz) / 2` is the end lift of the input end at `0` of the
pair of pants `ℂ ∖ {0, 1}`. Its longitudinal and angular coordinates at `w` are those of the end at
`0` at `(w - c) / a`, and `TauCeti.Floer.inputEndCutoff c a w` is the cutoff `β(s - 1)` in this
longitudinal coordinate, `β` being the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`.
It vanishes off the disc `‖w - c‖ < ‖a‖ exp (-2π) / 2`
(`TauCeti.Floer.inputEndCutoff_eq_zero_of_le_norm_sub`), the support of the input end datum
`TauCeti.Floer.inputEndPerturbation c a`.

Fix an `ω`-compatible base structure `J₀`, input ends indexed by a finite linearly ordered type
`ι`, with centers `c i`, scales `a i` and families `J i t x` of `ω`-tame structures, and a family
`Jout t x` for the output end. Write `bᵢ(w)` for the cutoff of the input end `i`, `b_∞(w)` for the
cutoff `β(-s - 1)` of the output end and `Cᵢ`, `C_∞` for the Cayley transforms, relative to `J₀`,
of the end structures at the angular coordinates of `w`. The structure
`TauCeti.Floer.puncturedSphereAlmostComplex` is the inverse Cayley transform of

`b_∞ C_∞ + (1 - b_∞) ∑ i, bᵢ ∏_{j < i} (1 - bⱼ) Cᵢ`.

The weights `bᵢ ∏_{j < i} (1 - bⱼ)` are those of the partition of unity built from bump functions:
they are nonnegative with sum `1 - ∏ i, (1 - bᵢ) ≤ 1`, so the sum is a point of the convex Cayley
ball (`Convex.sum_mul_prod_one_sub_smul_mem`) for every configuration of the ends, colliding or
not. The structure is therefore tame for every configuration, and compatible when the end
structures are.

When the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, at most one of the cutoffs is nonzero at each point, every product is `1`
where its cutoff is nonzero, and the Cayley transform is the plain cutoff-weighted sum
`∑ i, bᵢ Cᵢ + b_∞ C_∞` (`TauCeti.Floer.cayley_puncturedSphereAlmostComplex_eq_sum`). Then:

* far out on the input end `i`, where `s ≥ 2`, the structure is `J i t x`
  (`TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift`), and far out on the output end,
  where `s ≤ -2`, it is `Jout t x`
  (`TauCeti.Floer.puncturedSphereAlmostComplex_cylindricalEndLift_inf`);
* off the supports of all the cutoffs it is `J₀`
  (`TauCeti.Floer.puncturedSphereAlmostComplex_eq_of_le_norm_sub_of_norm_le`; this needs no
  separation);
* with inputs `0` and `1` of scales `1` and `-1` it is the pair-of-pants structure
  (`TauCeti.Floer.puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex`).

For end families of period one in `t` which are `C^n` on `ℝ × M`, the structure is `C^n` jointly in
the centers, the scales, the domain point and the parameter `x`, at every configuration with
nonzero scales and every domain point other than the centers
(`TauCeti.Floer.contMDiffAt_puncturedSphereAlmostComplex`). Composed with a smooth path of
configurations it is a smooth family of almost complex data, as the moduli problem over a family of
domains requires.

The structures act on a fixed symplectic vector space `(V, ω)`, and the parameter `x` ranges over
an arbitrary type `M`, a manifold for the smoothness statement (for a vector space target,
`M = V`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured discs with strip-like ends and consistent perturbation data over them.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

/-! ### The cutoff of an input end -/

section Cutoff

variable {c a w : ℂ}

/-- The cutoff `β(s - 1)` of the input end with center `c` and scale `a` at `w`, where `s` is the
longitudinal coordinate of the end at `0` of the pair of pants at `(w - c) / a`. It is the
coefficient of the end Hamiltonian in the input end datum `TauCeti.Floer.inputEndPerturbation`. -/
def inputEndCutoff (c a w : ℂ) : ℝ :=
  smoothTransition ((zero.endCoord ((w - c) / a)).re - 1)

theorem inputEndCutoff_def (c a w : ℂ) :
    inputEndCutoff c a w = smoothTransition ((zero.endCoord ((w - c) / a)).re - 1) :=
  (rfl)

theorem inputEndCutoff_mem_Icc (c a w : ℂ) : inputEndCutoff c a w ∈ Icc 0 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

/-- **The support of the cutoff.** The cutoff of an input end vanishes off the disc
`‖w - c‖ < ‖a‖ exp (-2π) / 2`, as does the input end datum. -/
theorem inputEndCutoff_eq_zero_of_le_norm_sub (hw : ‖a‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c‖) :
    inputEndCutoff c a w = 0 := by
  refine smoothTransition.zero_of_nonpos (sub_nonpos.2 ?_)
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using (re_endCoord_endCenter zero).le.trans zero_le_one
  · refine re_endCoord_zero_le_one ?_
    rw [norm_div, le_div_iff₀ (norm_pos_iff.2 ha)]
    linarith

/-- **The cutoff on its end.** At the point `c + a φ₀(z)` of the input end, the cutoff is
`β(Re z - 1)`. -/
theorem inputEndCutoff_add_mul_cylindricalEndLift (ha : a ≠ 0) (z : ℂ) :
    inputEndCutoff c a (c + a * zero.cylindricalEndLift z) = smoothTransition (z.re - 1) := by
  rw [inputEndCutoff_def, add_sub_cancel_left, mul_div_cancel_left₀ _ ha,
    re_endCoord_cylindricalEndLift]

/-- On the input end at `1` of the pair of pants, with center `1` and scale `-1`, the end
coordinate of the end at `0` read through `w ↦ (w - 1) / (-1)` is that of the end at `1`. -/
private theorem endCoord_zero_sub_one_div_neg_one (w : ℂ) :
    zero.endCoord ((w - 1) / -1) = one.endCoord w := by
  rw [endCoord_def, endCoord_def, endCenter_zero, endCenter_one, endScale_zero, endScale_one]
  congr 3
  ring

end Cutoff

/-! ### The structure -/

section Algebraic

variable {M V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  [Fintype ι] [LinearOrder ι]

/-- The almost complex structure on a sphere with moving input ends. For input ends with centers
`c i`, scales `a i` and families `J i t x` of `ω`-tame structures, an output end at `∞` with
family `Jout t x`, and an `ω`-compatible base structure `J₀`, at `w ∈ ℂ` and `x ∈ M` it is the
inverse Cayley transform, relative to `J₀`, of `b_∞ C_∞ + (1 - b_∞) ∑ i, bᵢ ∏_{j < i} (1 - bⱼ) Cᵢ`.
Here `bᵢ = inputEndCutoff (c i) (a i) w` and `b_∞ = β(-s_∞(w) - 1)` are the cutoffs of the ends,
and `Cᵢ`, `C_∞` are the Cayley transforms of `J i` and `Jout` at the angular coordinates of `w` on
the ends. When the ends are separated the products are `1` where they matter, and the Cayley
transform is `∑ i, bᵢ Cᵢ + b_∞ C_∞` (`cayley_puncturedSphereAlmostComplex_eq_sum`). -/
def puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (c a : ι → ℂ)
    (J : ι → ℝ → M → AlmostComplexStructure V) (hJ : ∀ i t x, ω.Tames (J i t x))
    (Jout : ℝ → M → AlmostComplexStructure V) (hJout : ∀ t x, ω.Tames (Jout t x)) (w : ℂ)
    (x : M) : AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) +
        (1 - smoothTransition (-(inf.endCoord w).re - 1)) •
          ∑ i, (inputEndCutoff (c i) (a i) w *
            ∏ j ∈ Finset.univ with j < i, (1 - inputEndCutoff (c j) (a j) w)) •
            J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x),
      h₀.tames.convex_cayleyBall (h₀.cayley_mem_cayleyBall (hJout _ x))
        (h₀.tames.convex_cayleyBall.sum_mul_prod_one_sub_smul_mem h₀.tames.zero_mem_cayleyBall
          (fun _ _ => inputEndCutoff_mem_Icc _ _ w) fun i _ => h₀.cayley_mem_cayleyBall (hJ i _ x))
        (smoothTransition.nonneg _) (sub_nonneg.2 (smoothTransition.le_one _))
        (add_sub_cancel _ _)⟩

variable {c a : ι → ℂ} {J : ι → ℝ → M → AlmostComplexStructure V}
  {hJ : ∀ i t x, ω.Tames (J i t x)} {Jout : ℝ → M → AlmostComplexStructure V}
  {hJout : ∀ t x, ω.Tames (Jout t x)}

/-- The structure on a sphere with moving input ends is tamed by `ω`. -/
theorem tames_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the structure, relative to `J₀`, is
`b_∞ C_∞ + (1 - b_∞) ∑ i, bᵢ ∏_{j < i} (1 - bⱼ) Cᵢ`. This characterizes the structure, since the
Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) =
      smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) +
        (1 - smoothTransition (-(inf.endCoord w).re - 1)) •
          ∑ i, (inputEndCutoff (c i) (a i) w *
            ∏ j ∈ Finset.univ with j < i, (1 - inputEndCutoff (c j) (a j) w)) •
            J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) := by
  rw [puncturedSphereAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The structure is `ω`-compatible when the end structures are, for every configuration of the
ends. -/
theorem compatible_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ i t x, ω.Compatible (J i t x)) (hJoutc : ∀ t x, ω.Compatible (Jout t x)) (w : ℂ)
    (x : M) : ω.Compatible (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) := by
  have hmem (J' : AlmostComplexStructure V) (h : ω.Compatible J') :
      J₀.cayley J' ∈ ω.compatibleCayleyBall J₀ :=
    (h₀.cayley_mem_compatibleCayleyBall_iff h.tames).mpr h
  refine (h₀.cayley_mem_compatibleCayleyBall_iff
    (tames_puncturedSphereAlmostComplex h₀ w x)).mp ?_
  rw [cayley_puncturedSphereAlmostComplex]
  exact h₀.tames.convex_compatibleCayleyBall (hmem _ (hJoutc _ x))
    (h₀.tames.convex_compatibleCayleyBall.sum_mul_prod_one_sub_smul_mem
      h₀.tames.zero_mem_compatibleCayleyBall (fun _ _ => inputEndCutoff_mem_Icc _ _ w)
      fun i _ => hmem _ (hJc i _ x))
    (smoothTransition.nonneg _) (sub_nonneg.2 (smoothTransition.le_one _)) (add_sub_cancel _ _)

/-- Where the cutoffs of all the input ends other than `i` and of the output end vanish, the
Cayley transform is `bᵢ Cᵢ`. -/
private theorem cayley_puncturedSphereAlmostComplex_of_forall_ne (h₀ : ω.Compatible J₀)
    {i : ι} {w : ℂ} (hne : ∀ j, j ≠ i → inputEndCutoff (c j) (a j) w = 0)
    (hinf : smoothTransition (-(inf.endCoord w).re - 1) = 0) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) =
      inputEndCutoff (c i) (a i) w • J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) := by
  have hprod : ∏ j ∈ Finset.univ with j < i, (1 - inputEndCutoff (c j) (a j) w) = 1 :=
    Finset.prod_eq_one fun j hj => by
      rw [hne j (Finset.mem_filter.1 hj).2.ne, sub_zero]
  rw [cayley_puncturedSphereAlmostComplex, hinf, zero_smul, zero_add, sub_zero, one_smul,
    Finset.sum_eq_single i (fun j _ hj => by rw [hne j hj, zero_mul, zero_smul]) (by simp),
    hprod, mul_one]

/-- Where the cutoffs of all the input ends vanish, the Cayley transform is `b_∞ C_∞`. -/
private theorem cayley_puncturedSphereAlmostComplex_of_forall (h₀ : ω.Compatible J₀) {w : ℂ}
    (h : ∀ j, inputEndCutoff (c j) (a j) w = 0) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) =
      smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) := by
  rw [cayley_puncturedSphereAlmostComplex, Finset.sum_eq_zero fun j _ => by
    rw [h j, zero_mul, zero_smul], smul_zero, add_zero]

/-- The cutoff of the output end vanishes on the disc `‖w‖ ≤ 2 exp (2π)`. -/
private theorem smoothTransition_neg_re_endCoord_inf_eq_zero {w : ℂ}
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) : smoothTransition (-(inf.endCoord w).re - 1) = 0 :=
  smoothTransition.zero_of_nonpos (by
    linarith [neg_re_endCoord_inf_le zero_le_one (w := w) (by simpa using hw)])

/-- **Off all the ends the structure is `J₀`.** At a point outside the supports
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of all the input cutoffs, in the disc `‖w‖ ≤ 2 exp (2π)` where
the output cutoff vanishes, the structure is the base structure, whatever the configuration. -/
theorem puncturedSphereAlmostComplex_eq_of_le_norm_sub_of_norm_le (h₀ : ω.Compatible J₀)
    {w : ℂ} (hc : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖)
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x = J₀ := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ w x) h₀.tames ?_
  rw [cayley_puncturedSphereAlmostComplex_of_forall h₀
      (fun i => inputEndCutoff_eq_zero_of_le_norm_sub (hc i)),
    smoothTransition_neg_re_endCoord_inf_eq_zero hw, zero_smul, AlmostComplexStructure.cayley_self]

/-! ### Separated configurations -/

section Separated

variable (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
  (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π))
include hsep hout

omit [Fintype ι] [LinearOrder ι] in
/-- On the disc `‖w - c i‖ < ‖a i‖ / 2` of a separated configuration, the cutoffs of the other
input ends and of the output end vanish. -/
private theorem inputEndCutoff_eq_zero_and_eq_zero {i : ι} {w : ℂ} (hw : ‖w - c i‖ < ‖a i‖ / 2) :
    (∀ j, j ≠ i → inputEndCutoff (c j) (a j) w = 0) ∧
      smoothTransition (-(inf.endCoord w).re - 1) = 0 := by
  have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  refine ⟨fun j hj => inputEndCutoff_eq_zero_of_le_norm_sub ?_,
    smoothTransition_neg_re_endCoord_inf_eq_zero ?_⟩
  · have h₁ : ‖a j‖ / 2 + ‖a i‖ / 2 ≤ ‖c j - c i‖ := hsep hj
    have h₂ : ‖c j - c i‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
      simpa using norm_sub_le (w - c i) (w - c j)
    nlinarith [norm_nonneg (a j)]
  · calc ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by simpa using norm_add_le (c i) (w - c i)
      _ ≤ 2 * Real.exp (2 * π) := by linarith [hout i]

/-- **The structure of a separated configuration.** If the discs `‖w - c i‖ < ‖a i‖ / 2` are
pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, the Cayley transform of the structure is
the cutoff-weighted sum `∑ i, bᵢ Cᵢ + b_∞ C_∞`: at most one of its terms is nonzero at each
point. -/
theorem cayley_puncturedSphereAlmostComplex_eq_sum (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) =
      ∑ i, inputEndCutoff (c i) (a i) w • J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) +
        smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (Jout (inf.endCoord w).im x) := by
  by_cases h : ∃ i, inputEndCutoff (c i) (a i) w ≠ 0
  · obtain ⟨i, hi⟩ := h
    -- The point lies in the support of the cutoff of `i`, inside the disc of the end `i`.
    have hw : ‖w - c i‖ < ‖a i‖ / 2 := by
      have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
      by_contra! hle
      exact hi (inputEndCutoff_eq_zero_of_le_norm_sub (by nlinarith [norm_nonneg (a i)]))
    obtain ⟨hne, hinf⟩ := inputEndCutoff_eq_zero_and_eq_zero hsep hout hw
    rw [cayley_puncturedSphereAlmostComplex_of_forall_ne h₀ hne hinf, hinf, zero_smul, add_zero,
      Finset.sum_eq_single i (fun j _ hj => by rw [hne j hj, zero_smul]) (by simp)]
  · push Not at h
    rw [cayley_puncturedSphereAlmostComplex_of_forall h₀ h,
      Finset.sum_eq_zero fun j _ => by rw [h j, zero_smul], zero_add]

/-- **The structure near an input end.** If the discs `‖w - c j‖ < ‖a j‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, then on the disc of the input `i` the Cayley
transform of the structure is `bᵢ Cᵢ`. -/
theorem cayley_puncturedSphereAlmostComplex_of_norm_sub_lt (h₀ : ω.Compatible J₀) {i : ι}
    {w : ℂ} (hw : ‖w - c i‖ < ‖a i‖ / 2) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout w x) =
      inputEndCutoff (c i) (a i) w • J₀.cayley (J i (zero.endCoord ((w - c i) / a i)).im x) :=
  have h := inputEndCutoff_eq_zero_and_eq_zero hsep hout hw
  cayley_puncturedSphereAlmostComplex_of_forall_ne h₀ h.1 h.2 x

/-- **The structure on an input end.** For a separated configuration, if `J i` has period one in
`t`, then on the part `s > 0` of the input end `i`, the Cayley transform of the structure at the
point `c i + a i φ₀(z)` with end coordinates `z = s + i t` is `β(s - 1) • cayley (J i t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos (h₀ : ω.Compatible J₀)
    {i : ι} (hJp : Periodic (J i) 1) (ha : a i ≠ 0) {z : ℂ} (hz : 0 < z.re) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout
        (c i + a i * zero.cylindricalEndLift z) x) =
      smoothTransition (z.re - 1) • J₀.cayley (J i z.im x) := by
  have hlt : ‖c i + a i * zero.cylindricalEndLift z - c i‖ < ‖a i‖ / 2 := by
    have h := norm_cylindricalEndLift_sub_endCenter zero z
    rw [endCenter_zero, sub_zero, endScale_zero] at h
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [add_sub_cancel_left, norm_mul, h, h2]
    have : Real.exp (-(2 * π * z.re)) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    nlinarith [norm_pos_iff.2 ha]
  obtain ⟨k, hk⟩ := zero.exists_endCoord_cylindricalEndLift z
  rw [cayley_puncturedSphereAlmostComplex_of_norm_sub_lt hsep hout h₀ hlt,
    inputEndCutoff_add_mul_cylindricalEndLift ha, add_sub_cancel_left,
    mul_div_cancel_left₀ _ ha, hk]
  have hper : J i (z.im + k) = J i z.im := by simpa using hJp.int_mul k z.im
  simp [hper]

/-- **The structure is `J i t` far out on each input end.** Under the hypotheses of
`cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos`, on the part `s ≥ 2` of the input
end `i` the structure at the point with end coordinates `z = s + i t` is `J i t x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀) {i : ι}
    (hJp : Periodic (J i) 1) (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout (c i + a i * zero.cylindricalEndLift z)
      x = J i z.im x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJ i z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_of_pos hsep hout h₀ hJp ha
      (by linarith), smoothTransition.one_of_one_le (by linarith), one_smul]

omit hsep in
/-- **The structure on the output end.** If the discs `‖w - c i‖ < ‖a i‖ / 2` lie in the disc
`‖w‖ ≤ 2 exp (2π)` and `Jout` has period one in `t`, then on the part `s ≤ -1` of the output end
the Cayley transform of the structure at the point `φ_∞(z)` with end coordinates `z = s + i t` is
`β(-s - 1) • cayley (Jout t x)`. -/
theorem cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le (h₀ : ω.Compatible J₀)
    (hJp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -1) (x : M) :
    J₀.cayley (puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout (inf.cylindricalEndLift z) x) =
      smoothTransition (-z.re - 1) • J₀.cayley (Jout z.im x) := by
  have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have hnorm : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ := by
    simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1) (z := z) (by linarith)
  rw [cayley_puncturedSphereAlmostComplex_of_forall h₀ fun i =>
      inputEndCutoff_eq_zero_of_le_norm_sub ?_,
    ← cayley_negativePlaneAlmostComplex h₀ (hJ := hJout),
    cayley_negativePlaneAlmostComplex_cylindricalEndLift_of_neg h₀ hJp (by linarith)]
  have h := norm_sub_norm_le (inf.cylindricalEndLift z) (c i)
  nlinarith [hout i, norm_nonneg (a i)]

omit hsep in
/-- **The structure is `Jout t` far out on the output end.** Under the hypotheses of
`cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le`, on the part `s ≤ -2` of the
output end the structure at the point with end coordinates `z = s + i t` is `Jout t x`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJp : Periodic Jout 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    puncturedSphereAlmostComplex h₀ c a J hJ Jout hJout (inf.cylindricalEndLift z) x =
      Jout z.im x := by
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ _ x) (hJout z.im x) ?_
  rw [cayley_puncturedSphereAlmostComplex_cylindricalEndLift_inf_of_le hout h₀ hJp
      (by linarith), smoothTransition.one_of_one_le (by linarith), one_smul]

end Separated

omit [LinearOrder ι] [Fintype ι] in
/-- **The pair of pants has two input ends.** The pair-of-pants structure is the structure of the
input ends with centers `0` and `1` and scales `1` and `-1`, and of its output end. -/
theorem puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀)
    {J : Puncture → ℝ → M → AlmostComplexStructure V} (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJ' : ∀ i t x, ω.Tames (![J zero, J one] i t x)) :
    puncturedSphereAlmostComplex h₀ ![0, 1] ![1, -1] ![J zero, J one] hJ' (J inf) (hJ inf) =
      pairOfPantsAlmostComplex h₀ J hJ := by
  funext w x
  have hsep : Pairwise fun i j : Fin 2 =>
      ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 + ‖(![1, -1] : Fin 2 → ℂ) j‖ / 2 ≤
        ‖(![0, 1] : Fin 2 → ℂ) i - (![0, 1] : Fin 2 → ℂ) j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  have h1 : (1 : ℝ) ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  have hout (i : Fin 2) : ‖(![0, 1] : Fin 2 → ℂ) i‖ + ‖(![1, -1] : Fin 2 → ℂ) i‖ / 2 ≤
      2 * Real.exp (2 * π) := by
    fin_cases i <;> simp <;> linarith
  refine h₀.eq_of_cayley_eq (tames_puncturedSphereAlmostComplex h₀ w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_puncturedSphereAlmostComplex_eq_sum hsep hout, cayley_pairOfPantsAlmostComplex,
    Fin.sum_univ_two, Puncture.sum_univ]
  simp [inputEndCutoff_def, endCoord_zero_sub_one_div_neg_one]

end Algebraic

/-! ### Smoothness -/

section Smooth

variable {M V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  [Fintype ι] [LinearOrder ι]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {J : ι → ℝ → M → AlmostComplexStructure V} {hJ : ∀ i t x, ω.Tames (J i t x)}
  {Jout : ℝ → M → AlmostComplexStructure V} {hJout : ∀ t x, ω.Tames (Jout t x)}

omit [LinearOrder ι] in
/-- The point `(w - c) / a` of the end at `0` read off a configuration is `C^n` in the
configuration and the domain point, where the scale is nonzero. -/
private theorem contMDiffAt_sub_div {n : ℕ∞} (i : ι) {c a : ι → ℂ} (ha : a i ≠ 0) (w : ℂ)
    (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => (p.2.1 - p.1.1 i) / p.1.2 i)
      ((c, a), (w, x)) := by
  have h : ContDiffAt ℂ n (fun q : ((ι → ℂ) × (ι → ℂ)) × ℂ => (q.2 - q.1.1 i) / q.1.2 i)
      ((c, a), w) := by
    refine ContDiffAt.div (f := fun q : ((ι → ℂ) × (ι → ℂ)) × ℂ => q.2 - q.1.1 i)
      (g := fun q : ((ι → ℂ) × (ι → ℂ)) × ℂ => q.1.2 i) ?_ ?_ ha <;> fun_prop
  exact (h.restrict_scalars ℝ).contMDiffAt.comp
    (f := fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => (p.1, p.2.1)) ((c, a), (w, x))
    (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))

omit [LinearOrder ι] in
/-- The cutoff of the input end `i` is `C^n` in the configuration and the domain point, at a
configuration with `a i ≠ 0` and a domain point other than `c i`. -/
private theorem contMDiffAt_inputEndCutoff {n : ℕ∞} (i : ι) {c a : ι → ℂ} (ha : a i ≠ 0)
    {w : ℂ} (hw : w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => inputEndCutoff (p.1.1 i) (p.1.2 i) p.2.1)
      ((c, a), (w, x)) := by
  have h := contMDiffAt_smoothTransition_endCoord_comp zero 1
    (contMDiffAt_sub_div (I := I) (n := n) i ha w x)
    (by rw [endCenter_zero]; exact div_ne_zero (sub_ne_zero.2 hw) ha)
  simpa only [endSign_zero, one_mul, inputEndCutoff_def] using h

/-- The cutoff `β(-s_∞ - 1)` of the output end is `C^n` on all of `ℂ`: it vanishes on the open
disc `‖w‖ < 2 exp (2π)`, which contains the center `0` of the end. -/
private theorem contDiffAt_smoothTransition_neg_re_endCoord_inf {n : ℕ∞} (w : ℂ) :
    ContDiffAt ℝ n (fun w => smoothTransition (-(inf.endCoord w).re - 1)) w := by
  rcases lt_or_ge ‖w‖ (2 * Real.exp (2 * π)) with hlt | hge
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hlt)] with v hv
    exact smoothTransition_neg_re_endCoord_inf_eq_zero hv.le
  · have hw : w ≠ inf.endCenter := by
      rintro rfl
      simp only [endCenter_inf, norm_zero] at hge
      linarith [Real.exp_pos (2 * π)]
    exact smoothTransition.contDiff.contDiffAt.comp w
      ((inf.contDiffAt_re_endCoord hw).neg.sub contDiffAt_const)

/-- **The structure is smooth in the configuration.** For families `J i t x` and `Jout t x` of
`ω`-tame structures which have period one in `t` and are `C^n` on `ℝ × M`, the structure on a
sphere with moving input ends is `C^n` jointly in the centers, the scales, the domain point and the
parameter `x`, at every configuration with nonzero scales and every domain point other than the
centers. No separation of the ends is needed. Composing with a smooth path of configurations gives
a smooth family of structures. -/
theorem contMDiffAt_puncturedSphereAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J i p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jout p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c a : ι → ℂ} (ha : ∀ i, a i ≠ 0) {w : ℂ} (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => (puncturedSphereAlmostComplex h₀ p.1.1 p.1.2 J
        hJ Jout hJout p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) ((c, a), (w, x)) := by
  refine h₀.contMDiffAt_of_contMDiffAt_cayley (fun _ => tames_puncturedSphereAlmostComplex h₀ _ _)
    ?_
  simp only [cayley_puncturedSphereAlmostComplex, map_add, map_smul, map_sum]
  -- The output cutoff, and the output term, which is the Cayley transform of the negative plane
  -- structure, are smooth everywhere.
  have hb : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        smoothTransition (-(inf.endCoord p.2.1).re - 1)) ((c, a), (w, x)) :=
    ContMDiffAt.comp (g := fun w : ℂ => smoothTransition (-(inf.endCoord w).re - 1))
      (f := fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => p.2.1) ((c, a), (w, x))
      (contDiffAt_smoothTransition_neg_re_endCoord_inf w).contMDiffAt
      (contMDiffAt_fst.comp _ contMDiffAt_snd)
  have hN : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        smoothTransition (-(inf.endCoord p.2.1).re - 1) •
          LinearMap.toContinuousLinearMap (J₀.cayley (Jout (inf.endCoord p.2.1).im p.2.2)))
      ((c, a), (w, x)) := by
    have h := (h₀.tames.contMDiff_cayley (fun p => tames_negativePlaneAlmostComplex h₀ _ _)
      (contMDiff_negativePlaneAlmostComplex (hJ := hJout) h₀ hJoutp hJouts)) (w, x)
    simp only [cayley_negativePlaneAlmostComplex, map_smul] at h
    exact ContMDiffAt.comp (f := fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => p.2) ((c, a), (w, x)) h
      contMDiffAt_snd
  refine hN.add ((contMDiffAt_const.sub hb).smul (contMDiffAt_finsetSum fun i _ => ?_))
  -- Each input term is a product of cutoffs times the Cayley transform of `J i` at the angular
  -- coordinate of the end `i`, which periodicity makes smooth.
  have hFp : Periodic (fun t y => LinearMap.toContinuousLinearMap (J₀.cayley (J i t y))) 1 :=
    fun t => by simp only [hJp i t]
  have hC := (zero.contMDiffAt_comp_im_endCoord hFp
    (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J i p.1 p.2) (fun p => hJ i p.1 p.2)
      (hJs i)) (w := (w - c i) / a i)
      (by rw [endCenter_zero]; exact div_ne_zero (sub_ne_zero.2 (hw i)) (ha i)) x).comp
    ((c, a), (w, x))
    ((contMDiffAt_sub_div i (ha i) w x).prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))
  exact ((contMDiffAt_inputEndCutoff (n := n) i (ha i) (hw i) x).mul
    (contMDiffAt_finsetProd fun j _ =>
      contMDiffAt_const.sub (contMDiffAt_inputEndCutoff (n := n) j (ha j) (hw j) x))).smul hC

end Smooth

end TauCeti.Floer
