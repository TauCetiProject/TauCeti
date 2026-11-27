/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import TauCeti.Algebra.Module.ZLattice.BilinFormDual
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Periodic

/-!
# Means over the torus `V ⧸ L` of a full lattice

Let `L` be a full lattice in a finite-dimensional real normed space `V`
(`[DiscreteTopology L] [IsZLattice ℝ L]`). An `L`-periodic function `G : V → ℂ` is a function on
the torus `V ⧸ L`. This file defines its mean `TauCeti.ZLattice.torusMean L G` as the integral of
`G` over the unit cube in the coordinates of the real basis `TauCeti.ZLattice.realBasis L` given by
a `ℤ`-basis of `L`, and proves:

* the mean of a periodic function is translation invariant
  (`TauCeti.ZLattice.torusMean_comp_add_right`);
* the mean is additive on continuous functions and homogeneous
  (`TauCeti.ZLattice.torusMean_add`, `TauCeti.ZLattice.torusMean_sum`,
  `TauCeti.ZLattice.torusMean_const_mul`);
* **Fourier uniqueness**: for a nondegenerate real bilinear form `B` on `V`, a continuous
  `L`-periodic function whose Fourier coefficients `torusMean L (x ↦ exp (2πi B (a, x)) G (x))`,
  `a ∈ L^⊥ = B.dualSubmodule L`, all vanish is zero
  (`TauCeti.ZLattice.eq_zero_of_forall_torusMean_exp_mul_eq_zero`).

These are the coordinate-free forms of the facts about periodic functions on `ℝᵈ` in
`TauCeti.Analysis.Fourier.Torus.Periodic`.
-/

public section

open Complex MeasureTheory Set Module
open scoped Real

namespace TauCeti.ZLattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The real basis of `V` given by a `ℤ`-basis of the full lattice `L`. -/
noncomputable def realBasis : Basis (Free.ChooseBasisIndex ℤ L) ℝ V :=
  (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

@[simp]
theorem realBasis_apply (i : Free.ChooseBasisIndex ℤ L) :
    realBasis L i = (Free.chooseBasis ℤ L i : V) := by
  rw [realBasis, Basis.ofZLatticeBasis_apply]

/-- The mean of a function `G` on `V` over the torus `V ⧸ L`, as the integral over the unit cube in
the coordinates of `realBasis L`. -/
noncomputable def torusMean (G : V → ℂ) : ℂ :=
  ∫ φ in univ.pi fun _ : Free.ChooseBasisIndex ℤ L ↦ Icc (0 : ℝ) 1,
    G ((realBasis L).equivFun.symm φ)

theorem torusMean_def (G : V → ℂ) :
    torusMean L G = ∫ φ in univ.pi fun _ : Free.ChooseBasisIndex ℤ L ↦ Icc (0 : ℝ) 1,
      G ((realBasis L).equivFun.symm φ) :=
  (rfl)

variable {L}

theorem continuous_realBasis_equivFun_symm : Continuous (realBasis L).equivFun.symm :=
  LinearMap.continuous_of_finiteDimensional (realBasis L).equivFun.symm.toLinearMap

/-- A continuous function is integrable over the unit cube in lattice coordinates. -/
theorem integrable_comp_realBasis_equivFun_symm {G : V → ℂ} (hG : Continuous G) :
    Integrable (fun φ ↦ G ((realBasis L).equivFun.symm φ))
      ((volume : Measure (Free.ChooseBasisIndex ℤ L → ℝ)).restrict
        (univ.pi fun _ ↦ Icc (0 : ℝ) 1)) :=
  (hG.comp continuous_realBasis_equivFun_symm).continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

/-- An `L`-periodic function, read in lattice coordinates, is periodic under `ℤ^ι`. -/
theorem comp_realBasis_equivFun_symm_add_intCast {G : V → ℂ}
    (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (φ : Free.ChooseBasisIndex ℤ L → ℝ) (n : Free.ChooseBasisIndex ℤ L → ℤ) :
    G ((realBasis L).equivFun.symm (φ + fun i ↦ (n i : ℝ))) =
      G ((realBasis L).equivFun.symm φ) := by
  have h : (realBasis L).equivFun.symm (fun i ↦ (n i : ℝ)) =
      ((∑ i, n i • Free.chooseBasis ℤ L i : L) : V) := by
    simp [Basis.equivFun_symm_apply, Int.cast_smul_eq_zsmul]
  rw [map_add, h, hG]

/-- **Translation invariance** of the mean of an `L`-periodic function. -/
theorem torusMean_comp_add_right {G : V → ℂ} (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (v : V) : torusMean L (fun x ↦ G (x + v)) = torusMean L G := by
  have h (φ : Free.ChooseBasisIndex ℤ L → ℝ) : (realBasis L).equivFun.symm φ + v =
      (realBasis L).equivFun.symm (φ + (realBasis L).equivFun v) := by
    rw [map_add, LinearEquiv.symm_apply_apply]
  simp only [torusMean, h]
  exact UnitAddTorus.setIntegral_unitCube_comp_add_right
    (g := fun φ ↦ G ((realBasis L).equivFun.symm φ))
    (comp_realBasis_equivFun_symm_add_intCast hG) _

/-- The mean is additive on continuous functions. -/
theorem torusMean_add {G G' : V → ℂ} (hG : Continuous G) (hG' : Continuous G') :
    torusMean L (fun x ↦ G x + G' x) = torusMean L G + torusMean L G' :=
  integral_add (integrable_comp_realBasis_equivFun_symm hG)
    (integrable_comp_realBasis_equivFun_symm hG')

/-- The mean of a finite sum of continuous functions is the sum of the means. -/
theorem torusMean_sum {κ : Type*} {s : Finset κ} {G : κ → V → ℂ}
    (hG : ∀ i, Continuous (G i)) :
    torusMean L (fun x ↦ ∑ i ∈ s, G i x) = ∑ i ∈ s, torusMean L (G i) :=
  integral_finsetSum s fun i _ ↦ integrable_comp_realBasis_equivFun_symm (hG i)

/-- The mean is homogeneous. -/
theorem torusMean_const_mul (c : ℂ) (G : V → ℂ) :
    torusMean L (fun x ↦ c * G x) = c * torusMean L G :=
  integral_const_mul c _

/-- **Fourier uniqueness on the torus `V ⧸ L`.** For a nondegenerate real bilinear form `B`, a
continuous `L`-periodic function all of whose Fourier coefficients
`torusMean L (x ↦ exp (2πi B (a, x)) G (x))`, `a ∈ L^⊥ = B.dualSubmodule L`, vanish is zero. -/
theorem eq_zero_of_forall_torusMean_exp_mul_eq_zero {B : LinearMap.BilinForm ℝ V}
    (hB : B.Nondegenerate) {G : V → ℂ} (hc : Continuous G)
    (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (h : ∀ a ∈ B.dualSubmodule L, torusMean L (fun x ↦ exp (2 * π * I * B a x) * G x) = 0) :
    G = 0 := by
  classical
  set e := B.dualBasis hB (realBasis L)
  have h_zero : (fun φ ↦ G ((realBasis L).equivFun.symm φ)) = 0 := by
    refine UnitAddTorus.eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero
      (hc.comp continuous_realBasis_equivFun_symm)
      (comp_realBasis_equivFun_symm_add_intCast hG) fun n ↦ ?_
    -- The character of `a = -∑ⱼ nⱼ eⱼ` is the monomial `mFourier (-n)`.
    set a : V := ∑ j, ((-n j : ℤ) : ℝ) • e j
    have ha : a ∈ B.dualSubmodule L := by
      rw [B.dualSubmodule_eq_span_dualBasis_ofZLatticeBasis hB L (Free.chooseBasis ℤ L)]
      exact Submodule.sum_mem _ fun j _ ↦ by
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (Submodule.subset_span (mem_range_self j)) _
    have hE (j i : Free.ChooseBasisIndex ℤ L) :
        B (e j) (realBasis L i) = if i = j then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left _ _ _ _
    have hn (i : Free.ChooseBasisIndex ℤ L) : B a (realBasis L i) = (-n) i := by
      simp only [a, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hE,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.neg_apply]
    have h_char (φ : Free.ChooseBasisIndex ℤ L → ℝ) :=
      UnitAddTorus.exp_two_pi_I_mul_equivFun_symm_eq_mFourier (realBasis L) (B a) hn φ
    have := h a ha
    simp only [torusMean, h_char] at this
    exact this
  funext x
  have := congrFun h_zero ((realBasis L).equivFun x)
  rwa [LinearEquiv.symm_apply_apply] at this

end TauCeti.ZLattice
