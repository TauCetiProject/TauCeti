/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
import TauCeti.MeasureTheory.Constructions.Cylinder.Events

/-!
# Checks for specifications and Gibbs measures

Configurations `ℤ → Bool`, with `ℤ` acting on itself by translation (written multiplicatively,
`Multiplicative ℤ`).

* On the closed shift-invariant subshift `X₀` of the two constant configurations, any coordinate
  outside a finite set `Λ` determines the configuration, so the exterior σ-algebra of `Λ` is the
  full trace σ-algebra. The identity kernels `γ_Λ(· | ω) = δ_ω` are then a specification, and every
  measure on `X₀` is Gibbs for it.
* On the full shift, the event `{ω(0) = 1}` is not measurable for the exterior σ-algebra of `{0}`,
  since two configurations differing only at `0` have the same exterior. (The site `0` of `ℤ` is
  `1 = ofAdd 0` in `Multiplicative ℤ`.) Informally, this is why the identity kernels are not a
  specification there: `ω ↦ δ_ω({ω(0) = 1})` is not measurable for that exterior σ-algebra.
-/

open MeasureTheory ProbabilityTheory Set

public noncomputable section

namespace TauCeti.Examples.GibbsSpecification

/-- The subshift of the two constant configurations `ℤ → Bool`. -/
def X₀ : Subshift (Multiplicative ℤ) (Multiplicative ℤ) Bool where
  carrier := {ω | ∀ i j, ω i = ω j}
  isClosed := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_apply i) (continuous_apply j)
  smul_mem' _ _ hω _ _ := hω _ _

/-- A configuration lies in `X₀` exactly when it is constant. -/
@[simp]
theorem mem_X₀_iff (ω : Multiplicative ℤ → Bool) : ω ∈ X₀ ↔ ∀ i j, ω i = ω j :=
  Iff.rfl

/-- A configuration of `X₀` is constant. -/
theorem X₀_val_apply_eq (ω : X₀) (i j : Multiplicative ℤ) : ω.val i = ω.val j :=
  ω.property i j

/-- On `X₀`, the exterior σ-algebra of every finite set is the full trace σ-algebra: a single
coordinate outside the set determines the configuration. -/
theorem exterior_X₀ (Λ : Finset (Multiplicative ℤ)) :
    X₀.exterior (Λ : Set (Multiplicative ℤ)) = Subtype.instMeasurableSpace := by
  refine le_antisymm (X₀.exterior_le _) fun s hs => ?_
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset Λ
  have h (j : Multiplicative ℤ) : (fun ω : X₀ => ω.val j) = fun ω => ω.val i :=
    funext fun ω => X₀_val_apply_eq ω j i
  have hval : Measurable[X₀.exterior Λ] fun ω : X₀ => (ω : Multiplicative ℤ → Bool) := by
    let : MeasurableSpace X₀ := X₀.exterior Λ
    exact measurable_pi_iff.2 fun j => by
      rw [h j]
      exact X₀.measurable_apply_exterior (by simpa using hi)
  exact measurable_iff_comap_le.1 hval s hs

/-- The identity map of `X₀` is measurable from every exterior σ-algebra. -/
private theorem measurable_id_exterior (Λ : Finset (Multiplicative ℤ)) :
    Measurable[X₀.exterior (Λ : Set (Multiplicative ℤ)), Subtype.instMeasurableSpace]
      (id : X₀ → X₀) := by
  rw [exterior_X₀]
  exact measurable_id

/-- **The identity specification on `X₀`**: `γ_Λ(· | ω) = δ_ω`. -/
def idSpec : Specification X₀ where
  kernel Λ := Kernel.deterministic id (measurable_id_exterior Λ)
  isMarkovKernel Λ := Kernel.isMarkovKernel_deterministic _
  isProper Λ := by
    refine (Kernel.isProper_iff_inter_eq_indicator_mul (X₀.exterior_le _)).2
      fun A hA B hB ω => ?_
    simp [Kernel.deterministic_apply, Measure.dirac_apply' _ hA,
      Measure.dirac_apply' _ (hA.inter (X₀.exterior_le _ B hB)), inter_indicator_one, mul_comm]
  comp_eq Λ Δ _ := by
    ext1 ω
    simp [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, Kernel.deterministic_apply]

/-- The kernels of the identity specification are the Dirac measures. -/
@[simp]
theorem idSpec_kernel_apply (Λ : Finset (Multiplicative ℤ)) (ω : X₀) :
    idSpec.kernel Λ ω = Measure.dirac ω :=
  Kernel.deterministic_apply (measurable_id_exterior Λ) ω

/-- Every measure on `X₀` is Gibbs for the identity specification. -/
theorem isGibbs_idSpec (μ : Measure X₀) : idSpec.IsGibbs μ := by
  refine Specification.isGibbs_iff.2 fun Λ => ?_
  have h : ⇑(idSpec.kernel Λ) = Measure.dirac := funext (idSpec_kernel_apply Λ)
  rw [h, Measure.bind_dirac]

/-- On the full shift, `{ω(0) = 1}` is not measurable for the exterior σ-algebra of `{0}`; here the
site `0` of `ℤ` is `1 = ofAdd 0` in `Multiplicative ℤ`. Informally, the identity kernels are
therefore not kernels for the exterior σ-algebras. -/
example : ¬ MeasurableSet[(⊤ : Subshift (Multiplicative ℤ) (Multiplicative ℤ) Bool).exterior
    ({1} : Set (Multiplicative ℤ))] {ω | ω.val 1 = true} := by
  intro h
  rw [Subshift.exterior_def] at h
  obtain ⟨A, hA, hpre⟩ := MeasurableSpace.measurableSet_comap.1 h
  have hdep := hA.dependsOn_of_cylinderEvents
  set ω₁ : Multiplicative ℤ → Bool := fun _ => false
  set ω₂ : Multiplicative ℤ → Bool := Function.update ω₁ 1 true
  have h₁ : ω₁ ∉ A := fun h => by
    have : (⟨ω₁, Subshift.mem_top _⟩ :
        (⊤ : Subshift (Multiplicative ℤ) (Multiplicative ℤ) Bool)) ∈ Subtype.val ⁻¹' A := h
    rw [hpre] at this
    simp [ω₁] at this
  have h₂ : ω₂ ∈ A := by
    have : (⟨ω₂, Subshift.mem_top _⟩ : (⊤ : Subshift (Multiplicative ℤ) (Multiplicative ℤ) Bool))
        ∈ {ω | ω.val 1 = true} := by
      simp [ω₂]
    rw [← hpre] at this
    exact this
  have : (ω₁ ∈ A) = (ω₂ ∈ A) := hdep fun i hi => by
    simp only [ω₂, ω₁]
    rw [Function.update_of_ne (by simpa using hi)]
  exact h₁ (this ▸ h₂)

end TauCeti.Examples.GibbsSpecification
