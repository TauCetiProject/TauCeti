/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

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
`trajMeasure μ₀ κ`, for a finite initial law. Since a composition-product sees a kernel only
almost everywhere, the trajectory measure is unchanged when each kernel is modified on a null set
of prefixes (`ProbabilityTheory.Kernel.trajMeasure_congr`); for an s-finite initial law this
follows from the finite case, the trajectory measure being additive in its initial law
(`ProbabilityTheory.Kernel.trajMeasure_sum`). The splitting of a prefix through time `n + 1`
into its prefix through time `n` and its last coordinate is `MeasurableEquiv.IicProdSucc`.
-/

public section

open Finset MeasureTheory Preorder
open scoped ProbabilityTheory

namespace MeasurableEquiv

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- A prefix through time `n + 1` is a prefix through time `n` together with its last
coordinate. -/
def IicProdSucc (n : ℕ) : ((i : Iic n) → X i) × X (n + 1) ≃ᵐ ((i : Iic (n + 1)) → X i) :=
  (prodCongr (refl _) (piSingleton n)).trans (IicProdIoc n.le_succ)

/-- The inverse of `MeasurableEquiv.IicProdSucc` splits off the last coordinate. -/
theorem coe_IicProdSucc_symm (n : ℕ) :
    ⇑(IicProdSucc (X := X) n).symm =
      fun x ↦ (frestrictLe₂ n.le_succ x, x ⟨n + 1, mem_Iic.2 le_rfl⟩) := (rfl)

/-- Splitting the prefix through time `n + 1` of a trajectory gives its prefix through time `n`
and its coordinate at time `n + 1`. -/
theorem IicProdSucc_symm_comp_frestrictLe (n : ℕ) :
    (IicProdSucc (X := X) n).symm ∘ frestrictLe (n + 1) =
      fun x ↦ (frestrictLe n x, x (n + 1)) := (rfl)

end MeasurableEquiv

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
`μ₀`, and whose law of each prefix and the following coordinate is the composition-product of the
prefix law with the transition kernel, is the trajectory measure `trajMeasure μ₀ κ`. -/
theorem eq_trajMeasure [IsFiniteMeasure μ₀] {P : Measure ((n : ℕ) → X n)}
    (h₀ : P.map (fun x ↦ x 0) = μ₀)
    (hsucc : ∀ n, P.map (fun x ↦ (frestrictLe n x, x (n + 1))) = P.map (frestrictLe n) ⊗ₘ κ n) :
    P = trajMeasure μ₀ κ := by
  have : IsFiniteMeasure (P.map fun x ↦ x 0) := h₀ ▸ inferInstance
  have : IsFiniteMeasure P := Measure.isFiniteMeasure_of_map (measurable_pi_apply 0).aemeasurable
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
  -- A measure on trajectories is determined by the laws of its prefixes.
  have hproj : IsProjectiveMeasureFamily fun I : Finset ℕ ↦ (trajMeasure μ₀ κ).map I.restrict :=
    fun I J hJI ↦ by
      rw [Measure.map_map (measurable_restrict₂ hJI) (measurable_restrict _),
        restrict₂_comp_restrict]
  exact IsProjectiveLimit.unique ((isProjectiveLimit_nat_iff hproj P).2 hprefix) fun _ ↦ rfl

/-- The trajectory measure of a sum of initial laws is the sum of their trajectory measures. -/
theorem trajMeasure_sum {ι : Type*} (μ : ι → Measure (X 0)) :
    trajMeasure (Measure.sum μ) κ = Measure.sum fun i ↦ trajMeasure (μ i) κ := by
  simp only [trajMeasure]
  rw [Measure.map_sum (MeasurableEquiv.measurable _).aemeasurable,
    Measure.bind_sum _ _ (traj κ 0).measurable.aemeasurable]

/-- The trajectory measure is unchanged when each transition kernel is modified on a null set of
prefixes of the trajectory measure. -/
theorem trajMeasure_congr [SFinite μ₀]
    {η : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))} [∀ n, IsMarkovKernel (η n)]
    (h : ∀ n, κ n =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe n)] η n) :
    trajMeasure μ₀ κ = trajMeasure μ₀ η := by
  -- For a finite initial law, the trajectory measure of `κ` satisfies the characterization of
  -- the trajectory measure of `η`.
  have hfin (ν : Measure (X 0)) [IsFiniteMeasure ν]
      (hν : ∀ n, κ n =ᵐ[(trajMeasure ν κ).map (frestrictLe n)] η n) :
      trajMeasure ν κ = trajMeasure ν η :=
    eq_trajMeasure trajMeasure_map_eval_zero fun n ↦ by
      rw [← Measure.compProd_congr (hν n),
        map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure_of_sFinite]
  -- An s-finite initial law is a countable sum of finite ones.
  rw [← sum_sfiniteSeq μ₀, trajMeasure_sum] at h ⊢
  rw [trajMeasure_sum]
  refine congrArg Measure.sum (funext fun i ↦ hfin _ fun n ↦ ?_)
  have hn := h n
  rw [Measure.map_sum (measurable_frestrictLe n).aemeasurable] at hn
  exact Measure.ae_sum_iff.1 hn i

end ProbabilityTheory.Kernel
