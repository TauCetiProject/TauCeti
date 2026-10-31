/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.PhragmenLindelof

/-!
# Ground states of C⋆-algebra dynamics

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`. For a
continuous linear functional `φ` and `a b : A`, a *ground-state function* is a bounded
continuous function `F` on the closed upper half-plane, holomorphic on the open upper
half-plane, with boundary values `F t = φ (a α_t(b))` on the real axis. A *ground state* is a
state, a positive continuous functional of norm one, admitting a ground-state function for
every pair `a, b`. This is the zero-temperature limit of the KMS condition: the strip
`0 ≤ im z ≤ β` becomes the upper half-plane and the second boundary condition disappears.
Bratteli and Robinson define ground states instead by the generator inequality
`-i ω (a⋆ δ(a)) ≥ 0`; the analytic condition used here is equivalent to it.

The ground-state function of a pair is unique, `IsGroundStateFunction.eqOn`, by Schwarz
reflection across the real axis, and it is bounded on the upper half-plane by `‖φ‖ ‖a‖ ‖b‖`,
`IsGroundStateFunction.norm_le`, by the Phragmén–Lindelöf principle. When `b` is entire
analytic the ground-state function is `z ↦ φ (a α_z(b))`. Since the pairs admitting
ground-state functions are closed in the second coefficient, a state is a ground state exactly
when `‖ω (a α_z(b))‖ ≤ ‖a‖ ‖b‖` for all `a`, all entire analytic `b` and `im z ≥ 0`,
`isGroundState_iff_norm_apply_mul_entireExtension_le`.

Ground states are invariant, `IsGroundState.apply_action`: for entire analytic `b`, letting
`a` run through an approximate unit bounds `z ↦ ω (α_z(b))` on the upper half-plane, and the
star relation `α_z(b)⋆ = α_{conj z}(b⋆)` bounds it on the lower half-plane, so it is constant
by Liouville's theorem. Every state is a ground state of the trivial dynamics,
`isGroundState_trivial_iff`.

Weak-* limits of β-KMS states as `β → +∞` are ground states whenever the limit is a state,
`IsGroundState.of_tendsto_isKMSState`; on a unital algebra the limit is automatically a state,
`IsGroundState.of_tendsto_isKMSState_of_unital`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, from Definition 5.3.18 on, for ground states, their analytic characterization,
their invariance, and the zero-temperature limit of KMS states.
-/

public section

open Complex Set Filter
open scoped ComplexOrder Topology

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `F` is a ground-state function for the functional `φ` and the pair `a, b`: it is bounded
and continuous on the closed upper half-plane, holomorphic on the open upper half-plane, and
has the boundary values `F t = φ (a α_t(b))` on the real axis. -/
structure IsGroundStateFunction (α : CStarAction (Multiplicative ℝ) A) (φ : A →L[ℂ] ℂ)
    (a b : A) (F : ℂ → ℂ) : Prop where
  continuousOn : ContinuousOn F {z | 0 ≤ z.im}
  differentiableOn : DifferentiableOn ℂ F {z | 0 < z.im}
  isBounded_image : Bornology.IsBounded (F '' {z | 0 ≤ z.im})
  apply_ofReal (t : ℝ) : F t = φ (a * α (Multiplicative.ofAdd t) b)

variable {α : CStarAction (Multiplicative ℝ) A} {φ : A →L[ℂ] ℂ} {a b : A} {F G : ℂ → ℂ}
  {z : ℂ}

namespace IsGroundStateFunction

/-- A ground-state function agrees on the closed upper half-plane with any function that is
continuous there, holomorphic on the open upper half-plane and has the same values on the
real axis. -/
theorem eqOn_of_apply_ofReal (hF : α.IsGroundStateFunction φ a b F)
    (hGc : ContinuousOn G {z | 0 ≤ z.im}) (hGd : DifferentiableOn ℂ G {z | 0 < z.im})
    (hG : ∀ t : ℝ, G t = φ (a * α (Multiplicative.ofAdd t) b)) :
    EqOn F G {z | 0 ≤ z.im} := fun z hz => by
  refine sub_eq_zero.mp <| eqOn_zero_of_zero_on_real_axis (f := fun z => F z - G z) isOpen_univ
    isPreconnected_univ (mapsTo_univ _ _) (x := 0) (mem_univ _)
    ((hF.continuousOn.sub hGc).mono inter_subset_right)
    ((hF.differentiableOn.sub hGd).mono inter_subset_right)
    (fun w _ hw => ?_) ⟨mem_univ z, hz⟩
  rw [← re_add_im w, hw, ofReal_zero, zero_mul, add_zero, hF.apply_ofReal, hG, sub_self]

/-- **Uniqueness of ground-state functions.** Two ground-state functions of the same pair
agree on the closed upper half-plane. -/
theorem eqOn (hF : α.IsGroundStateFunction φ a b F) (hG : α.IsGroundStateFunction φ a b G) :
    EqOn F G {z | 0 ≤ z.im} :=
  hF.eqOn_of_apply_ofReal hG.continuousOn hG.differentiableOn hG.apply_ofReal

/-- Subtracting ground-state functions with the same first coefficient subtracts the second
coefficients. -/
theorem sub_right {c : A} (hF : α.IsGroundStateFunction φ a b F)
    (hG : α.IsGroundStateFunction φ a c G) :
    α.IsGroundStateFunction φ a (b - c) (fun z => F z - G z) where
  continuousOn := hF.continuousOn.sub hG.continuousOn
  differentiableOn := hF.differentiableOn.sub hG.differentiableOn
  isBounded_image := (hF.isBounded_image.sub hG.isBounded_image).subset
    (image_subset_iff.mpr fun z hz => ⟨F z, mem_image_of_mem F hz,
      G z, mem_image_of_mem G hz, rfl⟩)
  apply_ofReal t := by simp [hF.apply_ofReal, hG.apply_ofReal, mul_sub]

/-- **Norm bound.** A ground-state function is bounded on the closed upper half-plane by
`‖φ‖ ‖a‖ ‖b‖`. -/
theorem norm_le (hF : α.IsGroundStateFunction φ a b F) (hz : 0 ≤ z.im) :
    ‖F z‖ ≤ ‖φ‖ * ‖a‖ * ‖b‖ := by
  refine PhragmenLindelof.upper_half_plane_of_isBounded
    ⟨hF.differentiableOn, by simpa using hF.continuousOn⟩
    (hF.isBounded_image.subset (image_mono (ofPred_subset_ofPred.mpr fun _ => le_of_lt)))
    (fun t => ?_) hz
  rw [hF.apply_ofReal, mul_assoc]
  refine (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg φ))
  exact (norm_mul_le _ _).trans_eq (by rw [StarAlgEquiv.norm_map])

/-- For an entire analytic `b`, the ground-state function of the pair `a, b` is
`z ↦ φ (a α_z(b))`. -/
theorem apply_eq_apply_mul_entireExtension (hF : α.IsGroundStateFunction φ a b F)
    (hb : α.IsEntireAnalytic b) (hz : 0 ≤ z.im) : F z = φ (a * α.entireExtension b z) :=
  hF.eqOn_of_apply_ofReal hb.differentiable_apply_mul_entireExtension.continuous.continuousOn
    hb.differentiable_apply_mul_entireExtension.differentiableOn
    (fun t => by rw [hb.entireExtension_ofReal]) hz

end IsGroundStateFunction

/-- For an entire analytic `b`, the function `z ↦ φ (a α_z(b))` is a ground-state function of
the pair `a, b` exactly when it is bounded on the closed upper half-plane. -/
theorem isGroundStateFunction_apply_mul_entireExtension_iff (hb : α.IsEntireAnalytic b) :
    α.IsGroundStateFunction φ a b (fun z => φ (a * α.entireExtension b z)) ↔
      Bornology.IsBounded ((fun z => φ (a * α.entireExtension b z)) '' {z | 0 ≤ z.im}) :=
  ⟨fun h => h.isBounded_image, fun h =>
    ⟨hb.differentiable_apply_mul_entireExtension.continuous.continuousOn,
      hb.differentiable_apply_mul_entireExtension.differentiableOn, h,
      fun t => by rw [hb.entireExtension_ofReal]⟩⟩

/-! ### Closedness in the second coefficient -/

private theorem exists_isGroundStateFunction_of_tendsto {u : ℕ → A} {F : ℕ → ℂ → ℂ}
    (hu : Tendsto u atTop (𝓝 b)) (hF : ∀ n, α.IsGroundStateFunction φ a (u n) (F n)) :
    ∃ G, α.IsGroundStateFunction φ a b G := by
  classical
  -- The half-plane estimate converts norm convergence of coefficients to uniform convergence.
  have hC : UniformCauchySeqOn F atTop {z | 0 ≤ z.im} := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq
      (ε / (‖φ‖ * ‖a‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hdist := hN m hm n hn
    rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hdist
    rw [dist_eq_norm]
    calc
      ‖F m z - F n z‖ ≤ ‖φ‖ * ‖a‖ * ‖u m - u n‖ := ((hF m).sub_right (hF n)).norm_le hz
      _ ≤ (‖φ‖ * ‖a‖ + 1) * ‖u m - u n‖ := by gcongr; linarith
      _ < ε := by linarith
  let G : ℂ → ℂ := fun z => limUnder atTop (fun n => F n z)
  have hlim (z : ℂ) (hz : 0 ≤ z.im) : Tendsto (fun n => F n z) atTop (𝓝 (G z)) :=
    (hC.cauchySeq hz).tendsto_limUnder
  have hU : TendstoUniformlyOn F G atTop {z | 0 ≤ z.im} :=
    hC.tendstoUniformlyOn_of_tendsto hlim
  refine ⟨G, hU.continuousOn (.of_forall fun n => (hF n).continuousOn), ?_, ?_, fun t => ?_⟩
  · exact (hU.mono (ofPred_subset_ofPred.mpr fun _ => le_of_lt)).tendstoLocallyUniformlyOn
      |>.differentiableOn (.of_forall fun n => (hF n).differentiableOn)
        (isOpen_lt continuous_const continuous_im)
  · refine isBounded_iff_forall_norm_le.mpr ⟨‖φ‖ * ‖a‖ * ‖b‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact le_of_tendsto_of_tendsto (hlim z hz).norm (tendsto_const_nhds.mul hu.norm)
      (.of_forall fun n => (hF n).norm_le hz)
  · refine tendsto_nhds_unique (hlim t (by simp)) ?_
    exact (((φ.continuous.comp (continuous_const.mul
      (StarAlgEquiv.isometry (α (Multiplicative.ofAdd t))).continuous)).tendsto b).comp hu).congr
      fun n => ((hF n).apply_ofReal t).symm

/-- For a fixed first coefficient, the second coefficients admitting a ground-state function
form a norm-closed set. -/
theorem isClosed_setOf_exists_isGroundStateFunction (α : CStarAction (Multiplicative ℝ) A)
    (φ : A →L[ℂ] ℂ) (a : A) : IsClosed {b | ∃ F, α.IsGroundStateFunction φ a b F} := by
  refine isSeqClosed_iff_isClosed.mp fun u b hu hb => ?_
  choose F hF using hu
  exact exists_isGroundStateFunction_of_tendsto hb hF

/-- It suffices to construct ground-state functions for second coefficients in a dense set. -/
theorem exists_isGroundStateFunction_of_dense {s : Set A} (hs : Dense s)
    (h : ∀ b ∈ s, ∃ F, α.IsGroundStateFunction φ a b F) (b : A) :
    ∃ F, α.IsGroundStateFunction φ a b F :=
  (isClosed_setOf_exists_isGroundStateFunction α φ a).closure_subset_iff.mpr h (hs b)

/-! ### Ground states -/

variable [PartialOrder A]

/-- A *ground state* of the real action `α` is a state `ω`, a positive continuous functional of
norm one, such that every pair `a, b` has a ground-state function: a bounded continuous function
on the closed upper half-plane, holomorphic on the open upper half-plane, with boundary values
`ω (a α_t(b))` on the real axis. Positivity is for the C⋆-algebra order; it makes `ω`
hermitian, which the invariance of ground states uses. -/
structure IsGroundState [StarOrderedRing A] (α : CStarAction (Multiplicative ℝ) A)
    (ω : A →P[ℂ] ℂ) : Prop where
  norm_eq_one : ‖(ω : A →L[ℂ] ℂ)‖ = 1
  exists_isGroundStateFunction (a b : A) : ∃ F, α.IsGroundStateFunction ω a b F

variable [StarOrderedRing A] {ω : A →P[ℂ] ℂ}

/-- For a ground state `ω` and an entire analytic `b`, `‖ω (a α_z(b))‖ ≤ ‖a‖ ‖b‖` on the closed
upper half-plane. -/
theorem IsGroundState.norm_apply_mul_entireExtension_le (hω : α.IsGroundState ω) (a : A)
    (hb : α.IsEntireAnalytic b) (hz : 0 ≤ z.im) :
    ‖ω (a * α.entireExtension b z)‖ ≤ ‖a‖ * ‖b‖ := by
  obtain ⟨F, hF⟩ := hω.exists_isGroundStateFunction a b
  have := hF.norm_le hz
  rwa [hω.norm_eq_one, one_mul, hF.apply_eq_apply_mul_entireExtension hb hz] at this

/-- **Analytic characterization of ground states.** A positive functional `ω` is a ground state
exactly when it has norm one and `‖ω (a α_z(b))‖ ≤ ‖a‖ ‖b‖` for every `a`, every entire analytic
`b` and every `z` in the closed upper half-plane. -/
theorem isGroundState_iff_norm_apply_mul_entireExtension_le :
    α.IsGroundState ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b, α.IsEntireAnalytic b →
      ∀ z : ℂ, 0 ≤ z.im → ‖ω (a * α.entireExtension b z)‖ ≤ ‖a‖ * ‖b‖ := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, fun a _ hb _ hz =>
    hω.norm_apply_mul_entireExtension_le a hb hz⟩, fun ⟨hnorm, hle⟩ => ⟨hnorm, fun a b => ?_⟩⟩
  refine exists_isGroundStateFunction_of_dense α.dense_entireAnalytic (fun c hc => ?_) b
  have hc := mem_entireAnalytic.mp hc
  refine ⟨_, (isGroundStateFunction_apply_mul_entireExtension_iff hc).mpr ?_⟩
  refine isBounded_iff_forall_norm_le.mpr ⟨‖a‖ * ‖c‖, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hle a c hc z hz

/-- Every state is a ground state of the trivial dynamics. -/
@[simp]
theorem isGroundState_trivial_iff :
    (trivial : CStarAction _ A).IsGroundState ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 := by
  refine ⟨IsGroundState.norm_eq_one, fun hnorm =>
    isGroundState_iff_norm_apply_mul_entireExtension_le.mpr ⟨hnorm, fun a b _ z _ => ?_⟩⟩
  rw [entireExtension_trivial]
  exact ((ω : A →L[ℂ] ℂ).le_opNorm _).trans (by rw [hnorm, one_mul]; exact norm_mul_le a b)

/-! ### Invariance of ground states -/

/-- For a ground state `ω` and an entire analytic `b`, `‖ω (α_z(b))‖ ≤ ‖b‖` on the closed upper
half-plane: the bound of `IsGroundState.norm_apply_mul_entireExtension_le` with the first factor
running through an approximate unit. -/
private theorem IsGroundState.norm_apply_entireExtension_le (hω : α.IsGroundState ω)
    (hb : α.IsEntireAnalytic b) (hz : 0 ≤ z.im) : ‖ω (α.entireExtension b z)‖ ≤ ‖b‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine le_of_tendsto (((map_continuous ω).tendsto _).comp
    (hl.toIsApproximateUnit.tendsto_mul_right _)).norm (hl.eventually_norm.mono fun e he => ?_)
  exact (hω.norm_apply_mul_entireExtension_le e hb hz).trans
    (mul_le_of_le_one_left (norm_nonneg b) he)

/-- **Ground states are invariant on entire analytic elements.** A ground state `ω` satisfies
`ω (α_z(b)) = ω b` for every entire analytic `b` and every complex time `z`. -/
@[simp]
theorem IsGroundState.apply_entireExtension (hω : α.IsGroundState ω)
    (hb : α.IsEntireAnalytic b) (z : ℂ) : ω (α.entireExtension b z) = ω b := by
  set g : ℂ → ℂ := fun z => ω (α.entireExtension b z) with hg_def
  have hg : Differentiable ℂ g :=
    (ω : A →L[ℂ] ℂ).differentiable.comp hb.differentiable_entireExtension
  -- on the lower half-plane, `ω (α_z(b)) = conj (ω (α_{conj z}(b⋆)))`
  have hrange : Bornology.IsBounded (range g) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨‖b‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    rcases le_total 0 w.im with hw | hw
    · exact hω.norm_apply_entireExtension_le hb hw
    · have h := hω.norm_apply_entireExtension_le hb.star (z := (starRingEnd ℂ) w)
        (by simpa using hw)
      rwa [hb.entireExtension_star, Complex.conj_conj, map_star, norm_star, norm_star] at h
  simpa [hg_def, hb.entireExtension_apply_zero] using hg.apply_eq_apply_of_bounded hrange z 0

/-- **Ground states are invariant.** Every ground state `ω` is invariant under the dynamics:
`ω (α_t(a)) = ω a`. -/
@[simp]
theorem IsGroundState.apply_action (hω : α.IsGroundState ω) (t : Multiplicative ℝ) (a : A) :
    ω (α t a) = ω a := by
  refine congrFun (Continuous.ext_on α.dense_entireAnalytic (f := fun a => ω (α t a))
    ((map_continuous ω).comp (α.continuous_apply continuous_const continuous_id))
    (map_continuous ω) fun b hb => ?_) a
  have hb := mem_entireAnalytic.mp hb
  have := hω.apply_entireExtension hb (Multiplicative.toAdd t : ℝ)
  rwa [hb.entireExtension_ofReal, ofAdd_toAdd] at this

/-! ### Zero-temperature limits of KMS states -/

/-- **Zero-temperature limits of KMS states are ground states.** If `β i → +∞`, the states
`ω' i` are eventually `β i`-KMS states, and they converge pointwise to a positive functional `ω`
of norm one, then `ω` is a ground state. The norm condition cannot be dropped for nonunital
`A`, where states may converge weak-* to `0`. -/
theorem IsGroundState.of_tendsto_isKMSState {ι : Type*} {l : Filter ι} [l.NeBot] {β : ι → ℝ}
    (hβ : Tendsto β l atTop) {ω' : ι → A →P[ℂ] ℂ}
    (hω' : ∀ᶠ i in l, α.IsKMSState (β i) (ω' i))
    (hlim : ∀ a, Tendsto (fun i => ω' i a) l (𝓝 (ω a))) (hnorm : ‖(ω : A →L[ℂ] ℂ)‖ = 1) :
    α.IsGroundState ω := by
  refine isGroundState_iff_norm_apply_mul_entireExtension_le.mpr ⟨hnorm, fun a b hb z hz => ?_⟩
  refine le_of_tendsto (hlim _).norm ((hω'.and (hβ.eventually_ge_atTop z.im)).mono ?_)
  rintro i ⟨hi, hβi⟩
  -- for `im z ≤ β i`, the point `z` lies in the KMS strip of `ω' i`
  obtain ⟨F, hF⟩ := hi.exists_isKMSFunction a b
  have hzs : z ∈ im ⁻¹' uIcc 0 (β i) := mem_uIcc_of_le hz hβi
  have := hF.norm_le hzs
  rwa [hi.norm_eq_one, one_mul, hF.apply_eq_apply_mul_entireExtension hb hzs] at this

/-- **Zero-temperature limits of KMS states on unital algebras.** On a unital C⋆-algebra, a
pointwise limit of `β i`-KMS states with `β i → +∞` is a ground state as soon as it is positive:
it is automatically of norm one. -/
theorem IsGroundState.of_tendsto_isKMSState_of_unital {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {γ : CStarAction (Multiplicative ℝ) B} {ω : B →P[ℂ] ℂ}
    {ι : Type*} {l : Filter ι} [l.NeBot] {β : ι → ℝ} (hβ : Tendsto β l atTop)
    {ω' : ι → B →P[ℂ] ℂ} (hω' : ∀ᶠ i in l, γ.IsKMSState (β i) (ω' i))
    (hlim : ∀ a, Tendsto (fun i => ω' i a) l (𝓝 (ω a))) : γ.IsGroundState ω := by
  refine of_tendsto_isKMSState hβ hω' hlim ?_
  -- the norm of a positive functional on a unital algebra is its value at `1`
  have h1 : ω 1 = 1 := tendsto_nhds_unique (hlim 1) (tendsto_const_nhds.congr' <| hω'.mono
    fun i hi => by
      beta_reduce
      rw [← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one, hi.norm_eq_one, ofReal_one])
  exact_mod_cast (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω).trans h1

end TauCeti.CStarAction
