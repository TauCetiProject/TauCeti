/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Finite observations and normalized increments

A finite real observation vector carries exactly the information in its initial value and
its successive increments divided by nonzero deterministic scales. If the initial value is
deterministic only almost surely, the observation and increment sigma algebras agree after
adjoining ambient null sets, not necessarily before augmentation.

Every standard Borel-valued measurable claim on the observations then has an almost-sure
representation as a Borel function of the normalized increments. This transfers finite-grid Gaussian
expansions from increment-dependent claims to observation-dependent claims. No independence,
Gaussian law, path regularity, or moment hypothesis is needed for this information dictionary.
In a Brownian grid starting at zero the scales are square roots of the positive time steps;
a grid starting at a positive date must retain its initial observation instead.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4 (finite-dimensional Gaussian claims).
-/

public section

open MeasureTheory MeasurableSpace

namespace TauCeti

variable {Ω : Type*} {n : ℕ}

/-- A finite real observation vector is measurable exactly when its initial value and all
successive normalized increments are measurable. Nonzero, not positive, scales suffice. -/
theorem measurable_fin_succ_iff_initial_increments [MeasurableSpace Ω]
    (X : Ω → Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    Measurable X ↔ Measurable (fun ω => X ω 0) ∧
      Measurable (fun ω (i : Fin n) => (X ω i.succ - X ω i.castSucc) / a i) := by
  constructor
  · intro hX
    exact ⟨(measurable_pi_apply 0).comp hX, Measurable.of_eval fun i =>
      (((measurable_pi_apply i.succ).comp hX).sub
        ((measurable_pi_apply i.castSucc).comp hX)).div_const (a i)⟩
  · rintro ⟨h0, hd⟩
    apply Measurable.of_eval
    intro j
    induction j using Fin.induction with
    | zero => exact h0
    | succ i hi =>
      have hd' := ((measurable_pi_apply i).comp hd).mul_const (a i)
      have he : (fun ω => X ω i.succ) =
          (fun ω => X ω i.castSucc +
            (X ω i.succ - X ω i.castSucc) / a i * a i) := by
        funext ω
        simp [ha i]
      rw [he]
      exact hi.add hd'

/-- Finite observations generate the same sigma algebra as the pair consisting of their
initial value and normalized increments. In particular, a random initial observation cannot
in general be discarded. -/
theorem comap_fin_succ_eq_initial_increments
    (X : Ω → Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    MeasurableSpace.comap X inferInstance = MeasurableSpace.comap (fun ω => (X ω 0,
      fun i : Fin n => (X ω i.succ - X ω i.castSucc) / a i)) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (X ω 0,
      fun i : Fin n => (X ω i.succ - X ω i.castSucc) / a i)) inferInstance
    apply measurable_iff_comap_le.mp
    apply (measurable_fin_succ_iff_initial_increments X a ha).mpr
    exact ⟨measurable_fst.comp (comap_measurable _),
      measurable_snd.comp (comap_measurable _)⟩
  · let : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    apply measurable_iff_comap_le.mp
    have hX : Measurable[MeasurableSpace.comap X inferInstance] X := comap_measurable _
    obtain ⟨h0, hd⟩ := (measurable_fin_succ_iff_initial_increments X a ha).mp hX
    exact h0.prodMk hd

/-- With a deterministic initial observation, normalized increments alone generate the
observation sigma algebra, including for an empty increment vector. -/
theorem comap_fin_succ_eq_increments_of_initial_const
    (X : Ω → Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (c : ℝ) (h0 : ∀ ω, X ω 0 = c) :
    MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap (fun ω (i : Fin n) =>
        (X ω i.succ - X ω i.castSucc) / a i) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (i : Fin n) =>
        (X ω i.succ - X ω i.castSucc) / a i) inferInstance
    apply measurable_iff_comap_le.mp
    apply (measurable_fin_succ_iff_initial_increments X a ha).mpr
    exact ⟨by simpa only [h0] using (measurable_const : Measurable (fun _ : Ω => c)),
      comap_measurable _⟩
  · let : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    exact measurable_iff_comap_le.mp
      ((measurable_fin_succ_iff_initial_increments X a ha).mp (comap_measurable _)).2

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- If the initial observation is constant almost surely, adjoining ambient null sets makes
the observation and normalized-increment sigma algebras equal. This uses the ambient a.e.
filter even when neither generated sigma algebra contains all ambient null sets. -/
theorem eventuallyMeasurableSpace_comap_fin_succ_eq_increments
    (X : Ω → Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (c : ℝ) (h0 : ∀ᵐ ω ∂P, X ω 0 = c) :
    eventuallyMeasurableSpace (MeasurableSpace.comap X inferInstance) (ae P) =
      eventuallyMeasurableSpace
        (MeasurableSpace.comap (fun ω (i : Fin n) => (X ω i.succ - X ω i.castSucc) / a i)
          inferInstance) (ae P) := by
  let Y : Ω → Fin (n + 1) → ℝ := fun ω j => X ω j - X ω 0 + c
  have hY : MeasurableSpace.comap Y inferInstance =
      MeasurableSpace.comap (fun ω (i : Fin n) => (X ω i.succ - X ω i.castSucc) / a i)
        inferInstance := by
    convert comap_fin_succ_eq_increments_of_initial_const Y a ha c
      (fun ω => by simp [Y]) using 1
    simp [Y]
  have hXY : X =ᵐ[P] Y := by
    filter_upwards [h0] with ω hω
    funext j
    simp [Y, hω]
  rw [← hY]
  apply le_antisymm <;> rintro s ⟨t, ⟨u, hu, rfl⟩, hst⟩
  · exact ⟨Y ⁻¹' u, ⟨u, hu, rfl⟩, hst.trans (hXY.preimage u)⟩
  · exact ⟨X ⁻¹' u, ⟨u, hu, rfl⟩, hst.trans (hXY.symm.preimage u)⟩

/-- A standard Borel-valued claim measurable in a finite observation vector with almost-surely
deterministic initial value is almost surely a Borel function of its normalized increments.
The equality is almost sure even when the claim or observations have exceptional values. -/
theorem exists_measurable_comp_increments_ae {E : Type*} [Nonempty E]
    [MeasurableSpace E] [StandardBorelSpace E]
    (X : Ω → Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (c : ℝ) (h0 : ∀ᵐ ω ∂P, X ω 0 = c) {H : Ω → E}
    (hH : Measurable[MeasurableSpace.comap X inferInstance] H) :
    ∃ g : (Fin n → ℝ) → E, Measurable g ∧
      H =ᵐ[P] fun ω => g (fun i => (X ω i.succ - X ω i.castSucc) / a i) := by
  obtain ⟨f, hf, hfact⟩ := hH.exists_eq_measurable_comp
  let Y : Ω → Fin (n + 1) → ℝ := fun ω j => X ω j - X ω 0 + c
  have hY : MeasurableSpace.comap Y inferInstance =
      MeasurableSpace.comap (fun ω (i : Fin n) =>
        (X ω i.succ - X ω i.castSucc) / a i) inferInstance := by
    convert comap_fin_succ_eq_increments_of_initial_const Y a ha c
      (fun ω => by simp [Y]) using 1
    simp [Y]
  have hm : Measurable[MeasurableSpace.comap (fun ω (i : Fin n) =>
      (X ω i.succ - X ω i.castSucc) / a i) inferInstance] (fun ω => f (Y ω)) := by
    rw [← hY]
    exact hf.comp (comap_measurable Y)
  obtain ⟨g, hg, hgfact⟩ := hm.exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  filter_upwards [h0] with ω hω
  calc
    H ω = f (X ω) := congrFun hfact ω
    _ = f (Y ω) := by
      congr 1
      funext j
      simp [Y, hω]
    _ = g (fun i => (X ω i.succ - X ω i.castSucc) / a i) := congrFun hgfact ω

end TauCeti
