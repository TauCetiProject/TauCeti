/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Sobolev spaces on finite unions of circles

A function on a finite disjoint union of boundary circles is a finite family of functions on
its components. The ℓ² norm is the square root of the sum of their squared Sobolev norms.
`CircleSobolev.piLpEquiv` identifies this family with a single Fourier sequence taking values
in the finite ℓ² product. The coefficient equations retain the component labels and the
continuous-representative equation identifies the actual boundary values. The latter can be
used separately with each component's positive period.

The caller's `Fintype` instance is retained explicitly: it determines the finite ℓ²
products and sums. The empty family is allowed.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§9–12.
-/

public section

noncomputable section

namespace TauCeti.CircleSobolev

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] {s t : ℝ}

private def component (a : CircleSobolev s (PiLp 2 E)) (i : ι) : CircleSobolev s (E i) :=
  ⟨fun n ↦ a.coeff n i, a.memℓp_weight_smul_coeff.mono' fun n ↦ by
    simpa only [PiLp.smul_apply] using PiLp.norm_apply_le (weight s n • a.coeff n) i⟩

private def assemble (a : PiLp 2 (fun i ↦ CircleSobolev s (E i))) :
    CircleSobolev s (PiLp 2 E) where
  coeff n := WithLp.toLp 2 (fun i ↦ (a i).coeff n)
  memℓp_weight_smul_coeff := by
    apply (memℓp_weight_smul_iff _).2
    have h := hasSum_sum (s := Finset.univ) (fun i _ ↦ hasSum_norm_sq (a i))
    have hn (n : ℤ) :
        (weight s n * ‖WithLp.toLp 2 (fun i ↦ (a i).coeff n)‖) ^ 2 =
          ∑ i, weight (2 * s) n * ‖(a i).coeff n‖ ^ 2 := by
      rw [mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum, two_mul, weight_add]
      congr 1
      ext i
      ring
    convert h.summable using 1
    exact funext hn

private theorem norm_sq_assemble (a : PiLp 2 (fun i ↦ CircleSobolev s (E i))) :
    ‖assemble a‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ ↦ hasSum_norm_sq (a i))
  refine (hasSum_norm_sq (assemble a)).unique ?_
  convert h using 1
  ext n
  simp [assemble, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]

/-- Fourier coefficients on a finite union of circles, identified with a finite ℓ²
product of the component Sobolev spaces. This is valid at every real Sobolev order. -/
def piLpEquiv :
    CircleSobolev s (PiLp 2 E) ≃ₗᵢ[ℂ] PiLp 2 (fun i ↦ CircleSobolev s (E i)) where
  toFun a := WithLp.toLp 2 (component a)
  invFun := assemble
  left_inv a := by
    apply CircleSobolev.ext
    funext n
    exact PiLp.ext fun i ↦ rfl
  right_inv a := by
    apply PiLp.ext
    intro i
    exact CircleSobolev.ext (by rfl)
  map_add' a b := by
    apply PiLp.ext
    intro i
    exact CircleSobolev.ext (by rfl)
  map_smul' c a := by
    apply PiLp.ext
    intro i
    exact CircleSobolev.ext (by rfl)
  norm_map' a := by
    have ha : assemble (WithLp.toLp 2 (component a)) = a := by
      apply CircleSobolev.ext
      funext n
      exact PiLp.ext fun i ↦ rfl
    have h := norm_sq_assemble (WithLp.toLp 2 (component a))
    rw [ha, ← PiLp.norm_sq_eq_of_L2] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.symm

/-- Projection to a boundary component keeps its Fourier coefficients. -/
@[simp]
theorem coeff_piLpEquiv (a : CircleSobolev s (PiLp 2 E)) (i : ι) (n : ℤ) :
    (piLpEquiv a i).coeff n = a.coeff n i :=
  (rfl)

/-- Assembly of the boundary components keeps their Fourier coefficients. -/
@[simp]
theorem coeff_piLpEquiv_symm (a : PiLp 2 (fun i ↦ CircleSobolev s (E i))) (n : ℤ) (i : ι) :
    ((piLpEquiv.symm a).coeff n) i = (a i).coeff n :=
  (rfl)

/-- The squared Sobolev norm on a finite union is the sum of the component squared norms. -/
theorem norm_sq_eq_sum_piLpEquiv (a : CircleSobolev s (PiLp 2 E)) :
    ‖a‖ ^ 2 = ∑ i, ‖piLpEquiv a i‖ ^ 2 := by
  rw [← piLpEquiv.norm_map a]
  exact PiLp.norm_sq_eq_of_L2 _ _

/-- A Fourier monomial restricts to the monomial with the corresponding component value. -/
@[simp]
theorem piLpEquiv_single (n : ℤ) (v : PiLp 2 E) (i : ι) :
    piLpEquiv (single (s := s) n v) i = single n (v i) := by
  apply CircleSobolev.ext
  funext m
  by_cases h : m = n <;> simp [h]

/-- Component restriction commutes with lowering the Sobolev order. -/
@[simp]
theorem piLpEquiv_inclusion (h : t ≤ s) (a : CircleSobolev s (PiLp 2 E)) (i : ι) :
    piLpEquiv (inclusion h a) i = inclusion h (piLpEquiv a i) := by
  apply CircleSobolev.ext
  funext n
  simp

variable [∀ i, CompleteSpace (E i)] (T : ℝ) [Fact (0 < T)]

/-- The family decomposition agrees with evaluation of the continuous boundary functions.
The period can be chosen independently on each boundary component. -/
@[simp]
theorem toContinuousMap_piLpEquiv (hs : 1 / 2 < s)
    (a : CircleSobolev s (PiLp 2 E)) (i : ι) (x : AddCircle T) :
    toContinuousMap T hs (piLpEquiv a i) x = toContinuousMap T hs a x i := by
  have h := ((hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)).mapL
    (PiLp.proj (𝕜 := ℂ) 2 E i)
  apply HasSum.unique _ h
  simpa using (hasSum_toContinuousMap T hs (piLpEquiv a i)).mapL
    (ContinuousMap.evalCLM ℂ x)

/-- Assembly of the component functions agrees with their continuous boundary values. -/
@[simp]
theorem toContinuousMap_piLpEquiv_symm (hs : 1 / 2 < s)
    (a : PiLp 2 (fun i ↦ CircleSobolev s (E i))) (i : ι) (x : AddCircle T) :
    toContinuousMap T hs (piLpEquiv.symm a) x i = toContinuousMap T hs (a i) x := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (toContinuousMap_piLpEquiv T hs (piLpEquiv.symm a) i x).symm

end TauCeti.CircleSobolev
