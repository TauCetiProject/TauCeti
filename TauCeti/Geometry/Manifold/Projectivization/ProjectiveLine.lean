/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine coordinates of the complex projective line

The complex projective line `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` is covered by the two affine coordinates
`t ↦ [t : 1]` and `s ↦ [1 : s]` (`TauCeti.ProjectiveLine.affineParam`), related on their overlap
by `s = 1 / t` (`TauCeti.ProjectiveLine.affineParam_inv`). Each coordinate is a holomorphic
inverse of the corresponding affine chart and misses exactly one point
(`TauCeti.ProjectiveLine.affineParam_zero_notMem_affineOpen`). Its derivative is bijective
(`TauCeti.ProjectiveLine.injective_mfderiv_affineParam` and
`TauCeti.ProjectiveLine.surjective_mfderiv_affineParam`), and together the two coordinates detect
smoothness of functions (`TauCeti.ProjectiveLine.contMDiff_of_contDiff_comp_affineParam`).
A `C^n` function `u` on `ℂ` with `s ↦ u (1 / s)` of class `C^n` across `s = 0` after setting it
to `0` there, read in one affine chart and extended by `0` at the remaining point, is `C^n` on the
projective line (`TauCeti.ProjectiveLine.contMDiff_indicator_affineOpen`).

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 1 (projective space and its affine charts).
-/

public section

open Set Function Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace TauCeti

namespace ProjectiveLine

/-- The affine coordinate of the projective line on the open set where the `i`-th homogeneous
coordinate does not vanish: `t ↦ [t : 1]` for `i = 1` and `s ↦ [1 : s]` for `i = 0`. -/
noncomputable def affineParam (i : Fin 2) (t : ℂ) : ℙ ℂ (Fin 2 → ℂ) :=
  (affineChart (K := ℂ) (n := 1) i).symm fun _ ↦ t

/-- The affine coordinate `i` in homogeneous coordinates: `[t : 1]` for `i = 1` and `[1 : t]` for
`i = 0`. -/
theorem affineParam_eq (i : Fin 2) (t : ℂ) :
    affineParam i t = mk ℂ (Fin.insertNth (α := fun _ ↦ ℂ) i 1 fun _ ↦ t)
      (Fin.insertNth_one_ne_zero i _) :=
  affineChart_symm_apply i _

/-- The two affine coordinates are related by `s = 1 / t` on their overlap. -/
theorem affineParam_inv {i j : Fin 2} (hij : i ≠ j) {t : ℂ} (ht : t ≠ 0) :
    affineParam i t = affineParam j t⁻¹ := by
  rw [affineParam_eq, affineParam_eq, mk_eq_mk_iff]
  refine ⟨Units.mk0 t ht, ?_⟩
  ext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- The affine coordinate `i` takes values in the affine open where the `i`-th homogeneous
coordinate does not vanish. -/
@[simp]
theorem affineParam_mem_affineOpen (i : Fin 2) (t : ℂ) :
    affineParam i t ∈ affineOpen (K := ℂ) i := by
  rw [← affineChart_source]
  exact (affineChart i).map_target (by simp [affineChart_target])

/-- The affine chart is a left inverse of the affine coordinate. -/
@[simp]
theorem affineChart_affineParam (i : Fin 2) (t : ℂ) :
    affineChart (K := ℂ) (n := 1) i (affineParam i t) = fun _ ↦ t :=
  (affineChart i).right_inv (by simp [affineChart_target])

/-- On its affine open, the affine coordinate is a left inverse of the affine chart. -/
@[simp]
theorem affineParam_affineChart {i : Fin 2} {x : ℙ ℂ (Fin 2 → ℂ)}
    (hx : x ∈ affineOpen (K := ℂ) i) :
    affineParam i (affineChart (K := ℂ) (n := 1) i x 0) = x := by
  have h' : (fun _ : Fin 1 ↦ affineChart (K := ℂ) (n := 1) i x 0) =
      affineChart (K := ℂ) (n := 1) i x :=
    funext fun k ↦ by fin_cases k; rfl
  rw [affineParam, h']
  exact (affineChart i).left_inv (by rwa [affineChart_source])

/-- The affine coordinates of the projective line are holomorphic, hence `C^n` for every `n`. -/
theorem contMDiff_affineParam {n : WithTop ℕ∞} (i : Fin 2) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) n (affineParam i) :=
  (contMDiff_affineChart_symm i n).comp (contDiff_pi.2 fun _ ↦ contDiff_id).contMDiff

/-- The affine coordinates of the projective line are `C^n` maps of the underlying real
manifolds, for every `n`. -/
theorem contMDiff_affineParam_real {n : WithTop ℕ∞} (i : Fin 2) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) n (affineParam i) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_affineParam i).restrictScalars ℝ

/-- The derivative of an affine coordinate of the projective line is injective: the affine chart
is a left inverse of the coordinate. -/
theorem injective_mfderiv_affineParam (i : Fin 2) (t : ℂ) :
    Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t) := by
  let e : ℂ →L[ℝ] Fin 1 → ℂ := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℝ ℂ
  have he : Injective e := fun a b hab ↦ by simpa [e] using congrFun hab 0
  have hcomp : affineChart (K := ℂ) (n := 1) i ∘ affineParam i = e :=
    funext (affineChart_affineParam i)
  have hchart : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
      (affineChart (K := ℂ) (n := 1) i) (affineParam i t) := by
    have := (((contMDiffOn_affineChart (𝕜 := ℂ) (n := 1) i ∞).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds (affineParam_mem_affineOpen i t))).restrictScalars ℝ)
    simpa only [modelWithCornersSelf_restrictScalars] using this.mdifferentiableAt (by simp)
  have key := mfderiv_comp t hchart
    ((contMDiff_affineParam_real (n := 1) i t).mdifferentiableAt one_ne_zero)
  rw [hcomp, mfderiv_eq_fderiv, e.fderiv] at key
  refine Injective.of_comp (f := mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
    (affineChart (K := ℂ) (n := 1) i) (affineParam i t)) ?_
  rw [← ContinuousLinearMap.coe_comp, ← key]
  -- The derivative of `e` read through the model spaces is `e` itself.
  exact (NormedSpace.fromTangentSpace _).symm.injective.comp
    (he.comp (NormedSpace.fromTangentSpace t).injective)

/-- For `i ≠ j`, the point `0` of the affine coordinate `j` lies outside the affine open `i`: it is
the one point of the projective line that the affine coordinate `i` misses. -/
theorem affineParam_zero_notMem_affineOpen {i j : Fin 2} (hij : i ≠ j) :
    affineParam j 0 ∉ affineOpen (K := ℂ) i := by
  rw [affineParam_eq, mk_mem_affineOpen_iff, not_not]
  fin_cases i <;> fin_cases j <;> simp_all

/-- A function on the projective line whose compositions with both affine coordinates are `C^n`
is `C^n`. -/
theorem contMDiff_of_contDiff_comp_affineParam {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : WithTop ℕ∞} {f : ℙ ℂ (Fin 2 → ℂ) → G}
    (hf : ∀ i, ContDiff ℝ n (f ∘ affineParam i)) :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, G) n f := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hchart : ContMDiffAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) n
      (affineChart (K := ℂ) (n := 1) i) x := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiffOn_affineChart (𝕜 := ℂ) (n := 1) i n).contMDiffAt
        ((isOpen_affineOpen i).mem_nhds hi)).restrictScalars ℝ
  have hG : ContDiff ℝ n fun z : Fin 1 → ℂ ↦ (f ∘ affineParam i) (z 0) :=
    (hf i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contDiff
  refine (hG.contMDiff.contMDiffAt.comp x hchart).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_affineOpen i).mem_nhds hi] with y hy
  simp [affineParam_affineChart hy]

/-- Every derivative of an affine coordinate of the projective line is surjective. -/
theorem surjective_mfderiv_affineParam (i : Fin 2) (t : ℂ) :
    Surjective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t) := by
  have h : Module.finrank ℝ ℂ = Module.finrank ℝ (Fin 1 → ℂ) := by
    simp [Module.finrank_pi_fintype]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t).toLinearMap)).1
    (injective_mfderiv_affineParam i t)

/-! ### Extension by zero from an affine chart -/

section ExtendByZero

variable {G : Type*}

/-- A function `u` on `ℂ`, read in the affine chart `i` and extended by `0` off the affine open
`i`, is `u` again in the affine coordinate `i`. -/
theorem indicator_affineOpen_comp_affineParam [Zero G] (i : Fin 2) (u : ℂ → G) :
    (affineOpen (K := ℂ) i).indicator (fun x ↦ u (affineChart (K := ℂ) (n := 1) i x 0)) ∘
      affineParam i = u :=
  funext fun t ↦ by simp

/-- For `i ≠ j`, a function `u` on `ℂ`, read in the affine chart `i` and extended by `0` off the
affine open `i`, is `s ↦ u (1 / s)` in the affine coordinate `j`, with value `0` at the point
`s = 0` that the affine coordinate `i` misses. -/
theorem indicator_affineOpen_comp_affineParam_of_ne [Zero G] {i j : Fin 2} (hij : i ≠ j)
    (u : ℂ → G) :
    (affineOpen (K := ℂ) i).indicator (fun x ↦ u (affineChart (K := ℂ) (n := 1) i x 0)) ∘
      affineParam j = update (fun s ↦ u s⁻¹) 0 0 :=
  funext fun s ↦ by
    rcases eq_or_ne s 0 with rfl | hs
    · simp [indicator_of_notMem (affineParam_zero_notMem_affineOpen hij)]
    · rw [comp_apply, affineParam_inv hij.symm hs, update_of_ne hs]
      simp

/-- **Extension by zero from an affine chart.** If `u` is `C^n` on `ℂ` and `s ↦ u (1 / s)`,
extended by `0` at `s = 0`, is `C^n`, then `u` read in the affine chart `i` and extended by `0`
off the affine open `i` is a `C^n` function on the projective line. -/
theorem contMDiff_indicator_affineOpen [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} (i : Fin 2) {u : ℂ → G} (hu : ContDiff ℝ n u)
    (hinv : ContDiff ℝ n (update (fun s ↦ u s⁻¹) 0 0)) :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, G) n
      ((affineOpen (K := ℂ) i).indicator fun x ↦ u (affineChart (K := ℂ) (n := 1) i x 0)) := by
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by fin_cases i <;> simp
  refine contMDiff_of_contDiff_comp_affineParam fun l ↦ ?_
  obtain rfl | rfl : l = i ∨ l = j := by omega
  · rwa [indicator_affineOpen_comp_affineParam]
  · rwa [indicator_affineOpen_comp_affineParam_of_ne hij]

end ExtendByZero

end ProjectiveLine

end TauCeti
