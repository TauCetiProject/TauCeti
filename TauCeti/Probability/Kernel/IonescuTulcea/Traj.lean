/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.Probability.Kernel.IonescuTulcea.Maps

/-!
# Trajectory measures with s-finite initial laws, and their uniqueness

The Ionescu--Tulcea trajectory measure can start from an s-finite measure. Its joint law of a
finite prefix and the following coordinate is the composition-product of the prefix law and the
next transition kernel. This identity lets finite transport plans be glued without normalization.

This generalizes Mathlib's
`ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, which assumes
a probability initial law.

Conversely, `ProbabilityTheory.Kernel.eq_trajMeasure` shows that these identities characterize the
trajectory measure: a measure with initial law `μ₀` whose prefix laws follow the kernels `κ` is
`trajMeasure μ₀ κ`, for a σ-finite initial law. Since a composition-product sees a kernel only
almost everywhere, the trajectory measure is unchanged when each kernel is modified on a null set
of prefixes (`ProbabilityTheory.Kernel.trajMeasure_congr`), for any initial law: this follows by
uniqueness from almost every starting point. The splitting of a prefix through time `n + 1`
into its prefix through time `n` and its last coordinate is `MeasurableEquiv.IicProdSucc`.
-/

public section

open Finset MeasureTheory Preorder
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)}

/-- An s-finite initial law gives an s-finite trajectory measure. -/
instance trajMeasure.instSFinite [SFinite μ₀] : SFinite (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  infer_instance

/-- A finite initial law gives a finite trajectory measure. -/
instance trajMeasure.instIsFiniteMeasure [IsFiniteMeasure μ₀] :
    IsFiniteMeasure (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  infer_instance

/-- The time-zero marginal of a trajectory measure is its initial law. -/
@[simp]
theorem trajMeasure_map_eval_zero : (trajMeasure μ₀ κ).map (fun x ↦ x 0) = μ₀ := by
  let e : ((i : Iic 0) → X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
  have heval : (fun x : (k : ℕ) → X k ↦ x 0) = e ∘ frestrictLe 0 := (rfl)
  have hprefix : (trajMeasure μ₀ κ).map (frestrictLe 0) = μ₀.map e.symm := by
    rw [trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      traj_map_frestrictLe, partialTraj_self, Measure.id_comp]
  rw [heval, ← Measure.map_map e.measurable (measurable_frestrictLe 0), hprefix]
  simp

/-- For an s-finite initial law, the joint law of the prefix through time `n` and the next
coordinate is the composition-product of the prefix law and the transition kernel at `n`. -/
theorem map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite [SFinite μ₀] (n : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe n) ⊗ₘ κ n =
      (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
  have hproj : Measurable (fun x : (k : ℕ) → X k ↦ (frestrictLe n x, x (n + 1))) := by
    fun_prop
  -- The prefix identity for a fixed starting point.
  have hstep : (Kernel.id ×ₖ κ n) ∘ₖ partialTraj κ 0 n =
      (traj κ 0).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
    ext x₀ : 1
    simpa [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply _ hproj] using
      partialTraj_compProd_eq_map_traj (κ := κ) (x₀ := x₀) zero_le
  simp [trajMeasure, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hproj,
    Measure.map_comp _ _ (measurable_frestrictLe n), traj_map_frestrictLe, Measure.comp_assoc,
    hstep]

/-- **Uniqueness of the trajectory measure.** A measure on trajectories whose time-zero marginal is
the σ-finite measure `μ₀`, and whose law of each prefix and the following coordinate is the
composition-product of the prefix law with the transition kernel, is the trajectory measure
`trajMeasure μ₀ κ`. -/
theorem eq_trajMeasure [SigmaFinite μ₀] {P : Measure ((n : ℕ) → X n)}
    (h₀ : P.map (fun x ↦ x 0) = μ₀)
    (hsucc : ∀ n, P.map (fun x ↦ (frestrictLe n x, x (n + 1))) = P.map (frestrictLe n) ⊗ₘ κ n) :
    P = trajMeasure μ₀ κ := by
  -- The laws of the prefixes agree, by induction on their length.
  have hprefix : ∀ n, P.map (frestrictLe n) = (trajMeasure μ₀ κ).map (frestrictLe n) := by
    intro n
    induction n with
    | zero =>
      let e : ((i : Iic 0) → X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
      have heval : (fun x : (k : ℕ) → X k ↦ x 0) = e ∘ frestrictLe 0 := (rfl)
      apply e.map_measurableEquiv_injective
      rw [Measure.map_map e.measurable (measurable_frestrictLe 0),
        Measure.map_map e.measurable (measurable_frestrictLe 0), ← heval, h₀,
        trajMeasure_map_eval_zero]
    | succ n ih =>
      apply (MeasurableEquiv.IicProdSucc n).symm.map_measurableEquiv_injective
      rw [Measure.map_map (by fun_prop) (measurable_frestrictLe _),
        Measure.map_map (by fun_prop) (measurable_frestrictLe _),
        MeasurableEquiv.IicProdSucc_symm_comp_frestrictLe, hsucc, ih,
        map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite]
  -- It suffices to compare the measures on the trajectories starting in a set of finite mass.
  let E (k : ℕ) : Set ((n : ℕ) → X n) := (fun x ↦ x 0) ⁻¹' spanningSets μ₀ k
  refine (Measure.ext_iff_of_iUnion_eq_univ (s := E) ?_).2 fun k ↦ ?_
  · simp only [E, ← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  have hfin (Q : Measure ((n : ℕ) → X n)) (hQ : Q.map (fun x ↦ x 0) = μ₀) :
      IsFiniteMeasure (Q.restrict (E k)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ,
      ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_spanningSets μ₀ k), hQ]
    exact measure_spanningSets_lt_top μ₀ k
  have := hfin P h₀
  have := hfin _ (trajMeasure_map_eval_zero (κ := κ))
  -- Restricted measures on trajectories are determined by the laws of their prefixes.
  have hproj : IsProjectiveMeasureFamily
      fun I : Finset ℕ ↦ ((trajMeasure μ₀ κ).restrict (E k)).map I.restrict :=
    fun I J hJI ↦ by
      rw [Measure.map_map (measurable_restrict₂ hJI) (measurable_restrict _),
        restrict₂_comp_restrict]
  refine IsProjectiveLimit.unique ((isProjectiveLimit_nat_iff hproj _).2 fun n ↦ ?_) fun _ ↦ rfl
  -- The set `E k` is an event of the prefix through time `n`.
  let S : Set ((i : Iic n) → X i) :=
    (fun y ↦ y ⟨0, mem_Iic.2 (Nat.zero_le n)⟩) ⁻¹' spanningSets μ₀ k
  have hs : MeasurableSet S := measurable_pi_apply _ (measurableSet_spanningSets μ₀ k)
  change (P.restrict (frestrictLe n ⁻¹' S)).map (frestrictLe n) =
    ((trajMeasure μ₀ κ).restrict (frestrictLe n ⁻¹' S)).map (frestrictLe n)
  rw [← Measure.restrict_map (measurable_frestrictLe n) hs,
    ← Measure.restrict_map (measurable_frestrictLe n) hs, hprefix n]

/-- The trajectory measure is unchanged when each transition kernel is modified on a null set of
prefixes of the trajectory measure. -/
theorem trajMeasure_congr
    {η : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))} [∀ n, IsMarkovKernel (η n)]
    (h : ∀ n, κ n =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe n)] η n) :
    trajMeasure μ₀ κ = trajMeasure μ₀ η := by
  let e : ((i : Iic 0) → X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
  -- The trajectory measure started from a point.
  have hdirac (ξ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))) [∀ n, IsMarkovKernel (ξ n)]
      (x : (i : Iic 0) → X i) : trajMeasure (Measure.dirac (e x)) ξ = traj ξ 0 x := by
    rw [trajMeasure, Measure.map_dirac' e.symm.measurable, e.symm_apply_apply,
      Measure.dirac_bind (traj ξ 0).measurable]
  -- Almost every starting prefix has the kernels agreeing almost everywhere along its trajectory.
  have hae : ∀ᵐ x ∂(μ₀.map e.symm), ∀ n, κ n =ᵐ[(traj κ 0 x).map (frestrictLe n)] η n := by
    rw [ae_all_iff]
    intro n
    have hn := h n
    rw [trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe n)] at hn
    filter_upwards [Measure.ae_ae_of_ae_comp hn] with x hx
    rwa [Kernel.map_apply _ (measurable_frestrictLe n)] at hx
  -- From such a prefix, the two trajectory laws agree by uniqueness.
  have htraj : ∀ᵐ x ∂(μ₀.map e.symm), traj κ 0 x = traj η 0 x := by
    filter_upwards [hae] with x hx
    rw [← hdirac κ x, ← hdirac η x]
    refine eq_trajMeasure trajMeasure_map_eval_zero fun n ↦ ?_
    have hn : κ n =ᵐ[(trajMeasure (Measure.dirac (e x)) κ).map (frestrictLe n)] η n := by
      rw [hdirac]
      exact hx n
    rw [← Measure.compProd_congr hn,
      map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite]
  exact Measure.comp_congr htraj

end ProbabilityTheory.Kernel
