/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Derivative

/-!
# Potentials of closed overconvergent one-forms

Over an ultrametric normed field of characteristic zero, a finite family of overconvergent
series `f i` is the gradient of an overconvergent series exactly when
`∂ᵢ fⱼ = ∂ⱼ fᵢ`. The potential is unique after prescribing its constant coefficient.
These are the coordinate statements of exactness in degree one and of the constant kernel
in degree zero for the de Rham complex of a dagger polydisc.

Termwise integration preserves overconvergence after shrinking the convergence radius.
Successively correcting a potential by a primitive in one variable therefore stays inside the
Monsky–Washnitzer algebra. The finite-coordinate statement also permits additional variables
as parameters. No completeness or nontriviality assumption on the norm is needed.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*,
  Duke Math. J. 113 (2002), §2, Lemma 2.1, the polydisc calculation.

The analytic input is `TauCeti.Dagger.primitive_mem_washnitzerAlgebra`; uniqueness uses
Mathlib's `MvPowerSeries.pderiv.ext`.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- A closed family in finitely many coordinate directions has an overconvergent potential
in those directions. Other variables may occur as parameters. -/
theorem exists_pderiv_eq_on (s : Finset σ) (f : σ → washnitzerAlgebra σ K)
    (hf : ∀ i ∈ s, ∀ j ∈ s, pderiv σ K i (f j) = pderiv σ K j (f i)) :
    ∃ g : washnitzerAlgebra σ K, ∀ i ∈ s, pderiv σ K i g = f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g, hg⟩ := ih (fun j hj k hk ↦ hf j (by simp [hj]) k (by simp [hk]))
    let h := f i - pderiv σ K i g
    have hzero (j : σ) (hj : j ∈ s) : pderiv σ K j h = 0 := by
      simp only [h, map_sub, pderiv_comm j i, hg j hj]
      exact sub_eq_zero.mpr (hf j (by simp [hj]) i (by simp))
    refine ⟨g + primitive σ K i h, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp [h]
    · have hji : i ≠ j := fun hij ↦ hi (hij ▸ hj)
      have hcomm : pderiv σ K j (primitive σ K i h) =
          primitive σ K i (pderiv σ K j h) := by
        apply Subtype.ext
        simpa only [coe_pderiv, coe_primitive] using
          MvPowerSeries.pderiv_primitive_of_ne hji h.1
      simp [hcomm, hzero j hj, hg j hj]

/-- A finite overconvergent one-form is exact if and only if its mixed partial derivatives
agree. This is the coordinate Poincaré lemma in degree one. -/
theorem exists_pderiv_eq_iff [Finite σ] (f : σ → washnitzerAlgebra σ K) :
    (∃ g : washnitzerAlgebra σ K, ∀ i, pderiv σ K i g = f i) ↔
      ∀ i j, pderiv σ K i (f j) = pderiv σ K j (f i) := by
  constructor
  · rintro ⟨g, hg⟩ i j
    rw [← hg i, ← hg j]
    exact pderiv_comm i j g
  · intro hf
    classical
    let := Fintype.ofFinite σ
    simpa using exists_pderiv_eq_on Finset.univ f (fun i _ j _ ↦ hf i j)

/-- In characteristic zero, an overconvergent function has all partial derivatives zero
exactly when it is a scalar. This also holds for an infinite variable type. -/
theorem forall_pderiv_eq_zero_iff (g : washnitzerAlgebra σ K) :
    (∀ i, pderiv σ K i g = 0) ↔ ∃ c : K, algebraMap K (washnitzerAlgebra σ K) c = g := by
  constructor
  · intro hg
    refine ⟨constantCoeff g.1, Subtype.ext ?_⟩
    apply MvPowerSeries.pderiv.ext
    · intro i
      simpa [MvPowerSeries.algebraMap_apply] using
        (congrArg Subtype.val (hg i)).symm
    · simp [MvPowerSeries.algebraMap_apply]
  · rintro ⟨c, rfl⟩ i
    exact (pderiv σ K i).map_algebraMap c

/-- A closed overconvergent one-form has a unique potential with any prescribed constant
coefficient. In zero variables this says that the prescribed scalar is the unique function. -/
theorem existsUnique_pderiv_eq [Finite σ] (f : σ → washnitzerAlgebra σ K)
    (hf : ∀ i j, pderiv σ K i (f j) = pderiv σ K j (f i)) (c : K) :
    ∃! g : washnitzerAlgebra σ K,
      (∀ i, pderiv σ K i g = f i) ∧ constantCoeff g.1 = c := by
  obtain ⟨g, hg⟩ := (exists_pderiv_eq_iff f).mpr hf
  let g₀ := g + algebraMap K (washnitzerAlgebra σ K) (c - constantCoeff g.1)
  have hD (i : σ) : pderiv σ K i g₀ = f i := by
    simp [g₀, hg i]
  have hconst : constantCoeff g₀.1 = c := by
    simp [g₀, MvPowerSeries.algebraMap_apply]
  refine ⟨g₀, ⟨hD, hconst⟩, ?_⟩
  rintro g' ⟨hg', hc⟩
  apply Subtype.ext
  apply MvPowerSeries.pderiv.ext
  · intro i
    simpa only [coe_pderiv] using
      congrArg Subtype.val ((hg' i).trans (hD i).symm)
  · exact hc.trans hconst.symm

end TauCeti.Dagger.washnitzerAlgebra
