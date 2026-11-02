/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing

/-!
# The dense analytic criterion for KMS states

The analytic KMS identity can be checked on a norm-dense invariant set of entire analytic
elements. In particular, a norm-dense invariant star subalgebra of entire elements suffices;
no continuity of imaginary-time evolution in the ambient norm is assumed.

The extension to arbitrary elements uses uniform convergence on the closed KMS strip.
Differences of KMS functions satisfy the strip norm bound, so norm approximation of the
second coefficient gives uniformly Cauchy KMS functions. Their limit retains continuity,
holomorphy, boundedness, and both boundary values. This argument works for either sign of
the inverse temperature, including zero, and for nonunital algebras.

The criterion follows Bratteli--Robinson, *Operator Algebras and Quantum Statistical
Mechanics 2*, second edition, Section 5.3.
-/

public section

open Complex Set Filter
open scoped ComplexOrder Topology

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {φ : A →L[ℂ] ℂ}
  {a b : A}

private theorem exists_isKMSFunction_of_tendsto {u : ℕ → A} {F : ℕ → ℂ → ℂ}
    (hu : Tendsto u atTop (𝓝 b)) (hF : ∀ n, α.IsKMSFunction β φ a (u n) (F n)) :
    ∃ G, α.IsKMSFunction β φ a b G := by
  classical
  -- The strip estimate converts norm convergence of coefficients to uniform Cauchy convergence.
  have hC : UniformCauchySeqOn F atTop (im ⁻¹' uIcc 0 β) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq
      (ε / (‖φ‖ * ‖a‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hnorm := ((hF m).sub_right (hF n)).norm_le hz
    have hdist := hN m hm n hn
    rw [dist_eq_norm] at hdist ⊢
    calc
      ‖F m z - F n z‖ ≤ ‖φ‖ * ‖a‖ * ‖u m - u n‖ := hnorm
      _ ≤ (‖φ‖ * ‖a‖ + 1) * ‖u m - u n‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
      _ < ε := by
        rw [lt_div_iff₀ (by positivity : 0 < ‖φ‖ * ‖a‖ + 1)] at hdist
        simpa only [mul_comm] using hdist
  let G : ℂ → ℂ := fun z => limUnder atTop (fun n => F n z)
  have hlim (z : ℂ) (hz : z ∈ im ⁻¹' uIcc 0 β) :
      Tendsto (fun n => F n z) atTop (𝓝 (G z)) :=
    (hC.cauchySeq hz).tendsto_limUnder
  have hU : TendstoUniformlyOn F G atTop (im ⁻¹' uIcc 0 β) :=
    hC.tendstoUniformlyOn_of_tendsto hlim
  refine ⟨G, hU.continuousOn (Frequently.of_forall fun n => (hF n).continuousOn),
    ?_, ?_, ?_, ?_⟩
  · exact ((hU.mono (preimage_mono Ioo_subset_Icc_self)).tendstoLocallyUniformlyOn).differentiableOn
      (.of_forall fun n => (hF n).differentiableOn) (isOpen_Ioo.preimage continuous_im)
  · refine isBounded_iff_forall_norm_le.mpr ⟨‖φ‖ * ‖a‖ * ‖b‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact le_of_tendsto_of_tendsto (hlim z hz |>.norm)
      (tendsto_const_nhds.mul hu.norm) (.of_forall fun n => (hF n).norm_le hz)
  · intro t
    exact tendsto_nhds_unique (hlim t (by simp))
      (((φ.continuous.comp (continuous_const.mul
        (StarAlgEquiv.isometry (α (Multiplicative.ofAdd t))).continuous)).tendsto b).comp hu
        |>.congr fun n => (hF n).apply_ofReal t |>.symm)
  · intro t
    exact tendsto_nhds_unique (hlim (t + β * I) (by simp))
      (((φ.continuous.comp
        ((StarAlgEquiv.isometry (α (Multiplicative.ofAdd t))).continuous.mul
          continuous_const)).tendsto b).comp hu
        |>.congr fun n => (hF n).apply_ofReal_add_mul_I t |>.symm)

/-- For a fixed first coefficient, the second coefficients admitting a KMS function form a
norm-closed set. -/
theorem isClosed_setOf_exists_isKMSFunction (α : CStarAction (Multiplicative ℝ) A)
    (β : ℝ) (φ : A →L[ℂ] ℂ) (a : A) :
    IsClosed {b | ∃ F, α.IsKMSFunction β φ a b F} := by
  classical
  refine isSeqClosed_iff_isClosed.mp fun u b hu hb => ?_
  choose F hF using hu
  exact exists_isKMSFunction_of_tendsto hb hF

/-- It suffices to construct KMS functions for second coefficients in a dense set. The
first coefficient is allowed to be arbitrary. -/
theorem exists_isKMSFunction_of_dense {s : Set A} (hs : Dense s)
    (h : ∀ b ∈ s, ∃ F, α.IsKMSFunction β φ a b F) (b : A) :
    ∃ F, α.IsKMSFunction β φ a b F :=
  (isClosed_setOf_exists_isKMSFunction α β φ a).closure_subset_iff.mpr h (hs b)

variable [PartialOrder A] [StarOrderedRing A] {ω : A →P[ℂ] ℂ}

/-- **Dense analytic KMS criterion.** A state is β-KMS if and only if the analytic KMS
identity holds for pairs in a norm-dense invariant set of entire analytic elements.
In particular, the set can be a norm-dense invariant star subalgebra. -/
theorem isKMSState_iff_of_dense {s : Set A} (hs : Dense s)
    (hinv : IsInvariant (fun t a => α t a) s)
    (hentire : ∀ b ∈ s, α.IsEntireAnalytic b) :
    α.IsKMSState β ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧
      ∀ a ∈ s, ∀ b ∈ s, ω (a * α.entireExtension b (β * I)) = ω (b * a) := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, fun a _ b hb =>
    hω.apply_mul_entireExtension_mul_I a (hentire b hb)⟩, fun ⟨hnorm, hid⟩ => ?_⟩
  -- First extend the untwisted coefficient by continuity; imaginary time is fixed here.
  have hid' (a : A) {b : A} (hb : b ∈ s) :
      ω (a * α.entireExtension b (β * I)) = ω (b * a) := by
    exact congrFun (Continuous.ext_on hs
      ((map_continuous ω).comp (continuous_id.mul continuous_const))
      ((map_continuous ω).comp (continuous_const.mul continuous_id))
      (fun a ha => hid a ha b hb)) a
  refine ⟨hnorm, fun a b => exists_isKMSFunction_of_dense hs (fun c hc => ?_) b⟩
  refine ⟨fun z => ω (a * α.entireExtension c z),
    (isKMSFunction_apply_mul_entireExtension_iff (hentire c hc)).mpr fun t => ?_⟩
  rw [← (hentire c hc).entireExtension_action]
  exact hid' a (hinv (Multiplicative.ofAdd t) hc)

/-- A state is β-KMS exactly when it satisfies the analytic KMS identity for every pair of
entire analytic elements. No assumption that all elements of the algebra are entire is needed. -/
theorem isKMSState_iff_forall_isEntireAnalytic :
    α.IsKMSState β ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧
      ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
        ω (a * α.entireExtension b (β * I)) = ω (b * a) := by
  simpa only [SetLike.mem_coe, mem_entireAnalytic] using
    isKMSState_iff_of_dense (β := β) (ω := ω)
    α.dense_entireAnalytic
    (fun t b hb => mem_entireAnalytic.mpr (by
      simpa only [ofAdd_toAdd] using
        (mem_entireAnalytic.mp hb).apply (Multiplicative.toAdd t)))
    (fun b hb => mem_entireAnalytic.mp hb)

/-- For the trivial action the β-KMS states are the tracial states, for every `β`. -/
theorem isKMSState_trivial_iff :
    (trivial : CStarAction _ A).IsKMSState β ω ↔
      ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b, ω (a * b) = ω (b * a) := by
  simp [isKMSState_iff_forall_isEntireAnalytic, isEntireAnalytic_trivial]

end TauCeti.CStarAction
