/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.Action.Hom
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# KMS states of C⋆-algebra dynamics

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`, and let
`β` be a real number, the inverse temperature. For a continuous linear functional `φ` and
`a b : A`, a *KMS function* is a bounded continuous function `F` on the closed strip between
the real axis and the line `im z = β`, holomorphic on the open strip, with boundary values

`F t = φ (a α_t(b))` and `F (t + iβ) = φ (α_t(b) a)`.

A *β-KMS state* is a state, that is a positive continuous functional of norm one, admitting a
KMS function for every pair `a, b`. Positivity refers to the C⋆-algebra order on `A`, the
order making it a `StarOrderedRing`. The positivity of a state is used only for pullback along
surjective equivariant homomorphisms, where it guarantees that the norm is preserved.

The strip lies above the real axis for `β > 0` and below it for `β < 0`. For `β = 0` it is the
real axis itself, and the `0`-KMS states are exactly the tracial states, `isKMSState_zero_iff`;
at `β = 0` the definition does not force invariance under `α`.

The KMS function of a pair is unique, `IsKMSFunction.eqOn`, by Schwarz reflection across the
real axis, and it is bounded on the strip by `‖φ‖ ‖a‖ ‖b‖`, `IsKMSFunction.norm_le`, by the
Phragmén–Lindelöf principle. When `b` is entire analytic, the KMS function is
`z ↦ φ (a α_z(b))`; this gives the analytic form of the KMS condition,
`ω (a α_{iβ}(b)) = ω (b a)`, `IsKMSState.apply_mul_entireExtension_mul_I`. The converse
analytic criterion and its specialization to the trivial action are proved in
`TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense`.

For `β ≠ 0` every β-KMS state is invariant under the dynamics, `IsKMSState.apply_action`.
Replacing `a` by an approximate unit in the analytic KMS identity gives `ω (α_{iβ}(b)) = ω b`
for entire analytic `b`, so `z ↦ ω (α_z(b))` is an entire function with period `iβ`. It is
bounded on a strip, hence on `ℂ`, and therefore constant by Liouville's theorem,
`IsKMSState.apply_entireExtension`. Invariance on all of `A` follows by density of the entire
analytic elements. No identity element is needed.

KMS functions and KMS states pull back along an equivariant homomorphism `π`: a KMS function of
the pair `π a, π b` for `φ` is one of the pair `a, b` for `φ ∘ π`, `Hom.isKMSFunction_iff`, so
`ω ∘ π` is a β-KMS state whenever `ω` is and `ω ∘ π` has norm one, `IsKMSState.comp`. Along a
surjective `π`, for instance a quotient map by an invariant ideal, the norm condition is automatic,
and a positive functional `ω` of the quotient dynamics is a β-KMS state exactly when `ω ∘ π` is,
`isKMSState_comp_iff_of_surjective`. For the inclusion of a closed invariant star subalgebra this
gives restriction of KMS states, `IsKMSState.restrict`, which needs the norm condition: the
restriction of a state need not be a state.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Definition 5.3.1 and Proposition 5.3.7, for the strip and analytic forms of the KMS condition,
and Proposition 5.3.3 for the invariance of KMS states.
-/

public section

open Complex Set
open scoped ComplexOrder

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `F` is a KMS function at inverse temperature `β` for the functional `φ` and the pair `a, b`:
it is bounded and continuous on the closed strip between the real axis and the line
`im z = β`, holomorphic on the open strip, and has the boundary values
`F t = φ (a α_t(b))` and `F (t + iβ) = φ (α_t(b) a)`. -/
structure IsKMSFunction (α : CStarAction (Multiplicative ℝ) A) (β : ℝ) (φ : A →L[ℂ] ℂ)
    (a b : A) (F : ℂ → ℂ) : Prop where
  continuousOn : ContinuousOn F (im ⁻¹' uIcc 0 β)
  differentiableOn : DifferentiableOn ℂ F (im ⁻¹' uIoo 0 β)
  isBounded_image : Bornology.IsBounded (F '' (im ⁻¹' uIcc 0 β))
  apply_ofReal (t : ℝ) : F t = φ (a * α (Multiplicative.ofAdd t) b)
  apply_ofReal_add_mul_I (t : ℝ) : F (t + β * I) = φ (α (Multiplicative.ofAdd t) b * a)

variable {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {φ : A →L[ℂ] ℂ} {a b : A}
  {F G : ℂ → ℂ}

namespace IsKMSFunction

/-- A KMS function agrees on the strip with any function that is continuous on the closed
strip, holomorphic on the open strip and has the same values on the real axis. -/
theorem eqOn_of_apply_ofReal (hF : α.IsKMSFunction β φ a b F)
    (hGc : ContinuousOn G (im ⁻¹' uIcc 0 β)) (hGd : DifferentiableOn ℂ G (im ⁻¹' uIoo 0 β))
    (hG : ∀ t : ℝ, G t = φ (a * α (Multiplicative.ofAdd t) b)) :
    EqOn F G (im ⁻¹' uIcc 0 β) := fun _ hz =>
  sub_eq_zero.mp <| eqOn_zero_im_preimage_uIcc_of_zero_on_real_axis (hF.continuousOn.sub hGc)
    (hF.differentiableOn.sub hGd) (fun t => by simp [hF.apply_ofReal, hG]) hz

/-- **Uniqueness of KMS functions.** Two KMS functions of the same pair agree on the strip. -/
theorem eqOn (hF : α.IsKMSFunction β φ a b F) (hG : α.IsKMSFunction β φ a b G) :
    EqOn F G (im ⁻¹' uIcc 0 β) :=
  hF.eqOn_of_apply_ofReal hG.continuousOn hG.differentiableOn hG.apply_ofReal

/-- Subtracting KMS functions with the same first coefficient subtracts the second
coefficients. -/
theorem sub_right {c : A} (hF : α.IsKMSFunction β φ a b F)
    (hG : α.IsKMSFunction β φ a c G) :
    α.IsKMSFunction β φ a (b - c) (fun z => F z - G z) where
  continuousOn := hF.continuousOn.sub hG.continuousOn
  differentiableOn := hF.differentiableOn.sub hG.differentiableOn
  isBounded_image := (hF.isBounded_image.sub hG.isBounded_image).subset
    (image_subset_iff.mpr fun z hz => ⟨F z, mem_image_of_mem F hz,
      G z, mem_image_of_mem G hz, rfl⟩)
  apply_ofReal t := by simp [hF.apply_ofReal, hG.apply_ofReal, mul_sub]
  apply_ofReal_add_mul_I t := by
    simp [hF.apply_ofReal_add_mul_I, hG.apply_ofReal_add_mul_I, sub_mul]

/-- On the two boundary lines a KMS function is bounded by `‖φ‖ ‖a‖ ‖b‖`. -/
private theorem norm_le_of_im_eq (hF : α.IsKMSFunction β φ a b F) {z : ℂ}
    (hz : z.im = 0 ∨ z.im = β) : ‖F z‖ ≤ ‖φ‖ * ‖a‖ * ‖b‖ := by
  have hnorm (x : A) (hx : ‖x‖ ≤ ‖a‖ * ‖b‖) : ‖φ x‖ ≤ ‖φ‖ * ‖a‖ * ‖b‖ :=
    (φ.le_opNorm x).trans <| by rw [mul_assoc]; gcongr
  rcases hz with hz | hz <;> rw [← re_add_im z, hz]
  · rw [ofReal_zero, zero_mul, add_zero, hF.apply_ofReal]
    exact hnorm _ ((norm_mul_le _ _).trans_eq <| by rw [StarAlgEquiv.norm_map])
  · rw [hF.apply_ofReal_add_mul_I]
    exact hnorm _ ((norm_mul_le _ _).trans_eq <| by rw [StarAlgEquiv.norm_map, mul_comm])

/-- **Norm bound.** A KMS function is bounded on the strip by `‖φ‖ ‖a‖ ‖b‖`. -/
theorem norm_le (hF : α.IsKMSFunction β φ a b F) {z : ℂ} (hz : z ∈ im ⁻¹' uIcc 0 β) :
    ‖F z‖ ≤ ‖φ‖ * ‖a‖ * ‖b‖ := by
  rcases eq_or_ne β 0 with rfl | hβ
  · exact hF.norm_le_of_im_eq (Or.inl (by simpa using hz))
  -- apply the Phragmén–Lindelöf principle on the strip `0 ⊓ β < im z < 0 ⊔ β`
  have hlt : 0 ⊓ β < 0 ⊔ β := inf_lt_sup.mpr hβ.symm
  have hedge {z : ℂ} (hz : z.im = 0 ⊓ β ∨ z.im = 0 ⊔ β) : z.im = 0 ∨ z.im = β := by
    rcases hz with hz | hz
    · rcases min_choice 0 β with h | h <;> simp_all
    · rcases max_choice 0 β with h | h <;> simp_all
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hF.isBounded_image
  refine PhragmenLindelof.horizontal_strip
    ⟨hF.differentiableOn, hF.continuousOn.mono ?_⟩
    ⟨0, div_pos Real.pi_pos (sub_pos.mpr hlt), 0, ?_⟩
    (fun z hz => hF.norm_le_of_im_eq (hedge (Or.inl hz)))
    (fun z hz => hF.norm_le_of_im_eq (hedge (Or.inr hz))) hz.1 hz.2
  · rw [closure_preimage_im, closure_Ioo hlt.ne]
    rfl
  · simp only [zero_mul, Real.exp_zero]
    refine Asymptotics.IsBigO.of_bound C (Filter.eventually_inf_principal.mpr <|
      .of_forall fun z hz => ?_)
    simpa using hC _ (mem_image_of_mem F (preimage_mono Ioo_subset_Icc_self hz))

end IsKMSFunction

/-- For an entire analytic `b`, the function `z ↦ φ (a α_z(b))` is entire. -/
private theorem differentiable_apply_mul_entireExtension (hb : α.IsEntireAnalytic b) :
    Differentiable ℂ fun z => φ (a * α.entireExtension b z) :=
  φ.differentiable.comp
    ((ContinuousLinearMap.mul ℂ A a).differentiable.comp hb.differentiable_entireExtension)

namespace IsKMSFunction

/-- For an entire analytic `b`, the KMS function of the pair `a, b` is `z ↦ φ (a α_z(b))`. -/
theorem apply_eq_apply_mul_entireExtension (hF : α.IsKMSFunction β φ a b F)
    (hb : α.IsEntireAnalytic b) {z : ℂ} (hz : z ∈ im ⁻¹' uIcc 0 β) :
    F z = φ (a * α.entireExtension b z) :=
  hF.eqOn_of_apply_ofReal (differentiable_apply_mul_entireExtension hb).continuous.continuousOn
    (differentiable_apply_mul_entireExtension hb).differentiableOn
    (fun t => by rw [hb.entireExtension_ofReal]) hz

/-- **Analytic KMS identity.** If the pair `a, b` has a KMS function and `b` is entire analytic,
then `φ (a α_{t + iβ}(b)) = φ (α_t(b) a)` for every real `t`. -/
theorem apply_mul_entireExtension_ofReal_add_mul_I (hF : α.IsKMSFunction β φ a b F)
    (hb : α.IsEntireAnalytic b) (t : ℝ) :
    φ (a * α.entireExtension b (t + β * I)) = φ (α (Multiplicative.ofAdd t) b * a) := by
  rw [← hF.apply_eq_apply_mul_entireExtension hb (by simp), hF.apply_ofReal_add_mul_I]

end IsKMSFunction

/-- For an entire analytic `b`, the function `z ↦ φ (a α_z(b))` is a KMS function of the pair
`a, b` exactly when it satisfies the analytic KMS identity on the line `im z = β`. -/
theorem isKMSFunction_apply_mul_entireExtension_iff (hb : α.IsEntireAnalytic b) :
    α.IsKMSFunction β φ a b (fun z => φ (a * α.entireExtension b z)) ↔
      ∀ t : ℝ, φ (a * α.entireExtension b (t + β * I)) =
        φ (α (Multiplicative.ofAdd t) b * a) := by
  refine ⟨fun h => h.apply_ofReal_add_mul_I, fun h => ⟨?_, ?_, ?_, ?_, h⟩⟩
  · exact (differentiable_apply_mul_entireExtension hb).continuous.continuousOn
  · exact (differentiable_apply_mul_entireExtension hb).differentiableOn
  · simpa [image_image] using (φ.comp (ContinuousLinearMap.mul ℂ A a)).lipschitzWith.isBounded_image
      (hb.isBounded_image_im_preimage (s := uIcc 0 β) (Metric.isBounded_Icc _ _))
  · exact fun t => by rw [hb.entireExtension_ofReal]

section Pullback

variable {B : Type*} [NonUnitalCStarAlgebra B] {γ : CStarAction (Multiplicative ℝ) B}

/-- **Pullback of KMS functions.** Let `π` be an equivariant homomorphism and let `ψ` be the
pullback `φ ∘ π` of a functional `φ`. Then `F` is a KMS function of the pair `a, b` for `ψ`
exactly when it is a KMS function of the pair `π a, π b` for `φ`. -/
theorem Hom.isKMSFunction_iff (π : Hom α γ) {φ : B →L[ℂ] ℂ} {ψ : A →L[ℂ] ℂ}
    (hψ : ∀ x, ψ x = φ (π x)) :
    α.IsKMSFunction β ψ a b F ↔ γ.IsKMSFunction β φ (π a) (π b) F := by
  have h₁ (t : ℝ) : ψ (a * α (.ofAdd t) b) = φ (π a * γ (.ofAdd t) (π b)) := by simp [hψ]
  have h₂ (t : ℝ) : ψ (α (.ofAdd t) b * a) = φ (γ (.ofAdd t) (π b) * π a) := by simp [hψ]
  exact ⟨fun hF => ⟨hF.continuousOn, hF.differentiableOn, hF.isBounded_image,
      fun t => (hF.apply_ofReal t).trans (h₁ t),
      fun t => (hF.apply_ofReal_add_mul_I t).trans (h₂ t)⟩,
    fun hF => ⟨hF.continuousOn, hF.differentiableOn, hF.isBounded_image,
      fun t => (hF.apply_ofReal t).trans (h₁ t).symm,
      fun t => (hF.apply_ofReal_add_mul_I t).trans (h₂ t).symm⟩⟩

end Pullback

variable [PartialOrder A]

/-- A *β-KMS state* of the real action `α` is a state `ω`, a positive continuous functional of
norm one, such that every pair `a, b` has a KMS function at inverse temperature `β`: a bounded
continuous function on the closed strip between the real axis and the line `im z = β`,
holomorphic on the open strip, with boundary values `ω (a α_t(b))` and `ω (α_t(b) a)`.
Positivity is for the C⋆-algebra order, so `StarOrderedRing A` is assumed although no field
uses it. -/
structure IsKMSState [StarOrderedRing A] (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (ω : A →P[ℂ] ℂ) : Prop where
  norm_eq_one : ‖(ω : A →L[ℂ] ℂ)‖ = 1
  exists_isKMSFunction (a b : A) : ∃ F, α.IsKMSFunction β ω a b F

variable [StarOrderedRing A] {ω : A →P[ℂ] ℂ}

/-- **Analytic form of the KMS condition.** For a β-KMS state `ω` and an entire analytic `b`,
`ω (a α_{iβ}(b)) = ω (b a)`. -/
theorem IsKMSState.apply_mul_entireExtension_mul_I (hω : α.IsKMSState β ω) (a : A)
    (hb : α.IsEntireAnalytic b) : ω (a * α.entireExtension b (β * I)) = ω (b * a) := by
  obtain ⟨F, hF⟩ := hω.exists_isKMSFunction a b
  simpa using hF.apply_mul_entireExtension_ofReal_add_mul_I hb 0

/-- The `0`-KMS states are exactly the tracial states. -/
theorem isKMSState_zero_iff :
    α.IsKMSState 0 ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b, ω (a * b) = ω (b * a) := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, fun a b => ?_⟩, fun ⟨hnorm, htr⟩ => ⟨hnorm, fun a b => ?_⟩⟩
  · obtain ⟨F, hF⟩ := hω.exists_isKMSFunction a b
    simpa [ofReal_zero ▸ hF.apply_ofReal 0] using hF.apply_ofReal_add_mul_I 0
  -- on the real axis the KMS function is `z ↦ ω (a α_{re z}(b))`
  refine ⟨fun z => ω (a * α (Multiplicative.ofAdd z.re) b), ?_, ?_, ?_, fun t => by simp,
    fun t => by simp [htr]⟩
  · exact ((map_continuous ω).comp (continuous_const.mul (α.continuous_apply
      (continuous_ofAdd.comp continuous_re) continuous_const))).continuousOn
  · rw [uIoo_self, preimage_empty]
    exact differentiableOn_empty
  · refine isBounded_iff_forall_norm_le.mpr ⟨‖(ω : A →L[ℂ] ℂ)‖ * (‖a‖ * ‖b‖), ?_⟩
    rintro _ ⟨z, -, rfl⟩
    refine ((ω : A →L[ℂ] ℂ).le_opNorm _).trans ?_
    gcongr
    exact (norm_mul_le _ _).trans_eq (by rw [StarAlgEquiv.norm_map])

/-! ### Invariance of KMS states -/

/-- For a β-KMS state `ω` and an entire analytic `b`, `ω (α_{iβ}(b)) = ω b`: the analytic KMS
identity with the first factor running through an approximate unit. -/
private theorem IsKMSState.apply_entireExtension_mul_I (hω : α.IsKMSState β ω)
    (hb : α.IsEntireAnalytic b) : ω (α.entireExtension b (β * I)) = ω b := by
  have hl := (CStarAlgebra.increasingApproximateUnit A).toIsApproximateUnit
  have hω' := map_continuous ω
  refine tendsto_nhds_unique (hω'.continuousAt.tendsto.comp (hl.tendsto_mul_right _))
    ((hω'.continuousAt.tendsto.comp (hl.tendsto_mul_left b)).congr fun e => ?_)
  exact (hω.apply_mul_entireExtension_mul_I e hb).symm

/-- **KMS states are invariant on entire analytic elements.** For `β ≠ 0`, a β-KMS state `ω`
satisfies `ω (α_z(b)) = ω b` for every entire analytic `b` and every complex time `z`. -/
theorem IsKMSState.apply_entireExtension (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    (hb : α.IsEntireAnalytic b) (z : ℂ) : ω (α.entireExtension b z) = ω b := by
  set g : ℂ → ℂ := fun z => ω (α.entireExtension b z) with hg_def
  have hg : Differentiable ℂ g := (ω : A →L[ℂ] ℂ).differentiable.comp
    hb.differentiable_entireExtension
  -- `g` has period `iβ`, so along each vertical line it has the real period `|β|`
  have hper : Function.Periodic g (β * I) := fun z => by
    simp only [hg_def, ← hb.entireExtension_entireExtension]
    exact hω.apply_entireExtension_mul_I (hb.isEntireAnalytic_entireExtension z)
  have hvert (x : ℝ) : Function.Periodic (fun y : ℝ => g (x + y * I)) |β| := by
    have hβper : Function.Periodic (fun y : ℝ => g (x + y * I)) β := fun y => by
      simpa [add_mul, add_assoc] using hper (x + y * I)
    rcases abs_choice β with h | h <;> rw [h]
    exacts [hβper, hβper.neg]
  -- hence the range of `g` is its image of the strip `0 ≤ im z ≤ |β|`, which is bounded
  have hrange : Bornology.IsBounded (Set.range g) := by
    refine ((ω : A →L[ℂ] ℂ).lipschitzWith.isBounded_image (hb.isBounded_image_im_preimage
      (Metric.isBounded_Icc 0 |β|))).subset ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy, hzy⟩ := (hvert z.re).exists_mem_Ico₀ (abs_pos.mpr hβ) z.im
    refine ⟨α.entireExtension b (z.re + y * I), ⟨_, by simpa using Ico_subset_Icc_self hy, rfl⟩,
      ?_⟩
    simpa [hg_def, re_add_im] using hzy.symm
  simpa [hg_def, hb.entireExtension_apply_zero] using hg.apply_eq_apply_of_bounded hrange z 0

/-- **KMS states are invariant.** For `β ≠ 0`, every β-KMS state `ω` is invariant under the
dynamics: `ω (α_t(a)) = ω a`. At `β = 0` the KMS states are the tracial states, which need not
be invariant. -/
theorem IsKMSState.apply_action (hω : α.IsKMSState β ω) (hβ : β ≠ 0) (t : Multiplicative ℝ)
    (a : A) : ω (α t a) = ω a := by
  refine congrFun (Continuous.ext_on α.dense_entireAnalytic (f := fun a => ω (α t a))
    ((map_continuous ω).comp (α.continuous_apply continuous_const continuous_id))
    (map_continuous ω) fun b hb => ?_) a
  have hb := mem_entireAnalytic.mp hb
  have := hω.apply_entireExtension hβ hb (Multiplicative.toAdd t : ℝ)
  rwa [hb.entireExtension_ofReal, ofAdd_toAdd] at this

/-! ### Pullback along equivariant homomorphisms -/

section Pullback

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {γ : CStarAction (Multiplicative ℝ) B}

/-- **Pullback of KMS states.** If `π` is an equivariant homomorphism and `ω` is a β-KMS state,
then `ω ∘ π` is a β-KMS state as soon as it has norm one. -/
theorem IsKMSState.comp {ω : B →P[ℂ] ℂ} (hω : γ.IsKMSState β ω) (π : Hom α γ)
    (hnorm : ‖((ω.comp (.ofClass π) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1) :
    α.IsKMSState β (ω.comp (.ofClass π)) where
  norm_eq_one := hnorm
  exists_isKMSFunction a b :=
    (hω.exists_isKMSFunction (π a) (π b)).imp fun _ => (π.isKMSFunction_iff fun _ => rfl).mpr

/-- **Pullback of KMS states along quotients.** If `π` is a surjective equivariant homomorphism and
`ω` is a β-KMS state, then `ω ∘ π` is a β-KMS state. -/
theorem IsKMSState.comp_of_surjective {ω : B →P[ℂ] ℂ} (hω : γ.IsKMSState β ω) (π : Hom α γ)
    (hπ : Function.Surjective π) : α.IsKMSState β (ω.comp (.ofClass π)) :=
  hω.comp π <| (PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective ω π hπ).trans
    hω.norm_eq_one

/-- Along a surjective equivariant homomorphism `π`, the β-KMS states of the quotient dynamics
are exactly the positive functionals `ω` whose pullback `ω ∘ π` is a β-KMS state. -/
theorem isKMSState_comp_iff_of_surjective {ω : B →P[ℂ] ℂ} (π : Hom α γ)
    (hπ : Function.Surjective π) :
    α.IsKMSState β (ω.comp (.ofClass π)) ↔ γ.IsKMSState β ω := by
  refine ⟨fun hω => ⟨?_, fun x y => ?_⟩, fun hω => hω.comp_of_surjective π hπ⟩
  · rw [← PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective ω π hπ]
    exact hω.norm_eq_one
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  exact (hω.exists_isKMSFunction a b).imp fun _ => (π.isKMSFunction_iff fun _ => rfl).mp

/-- **Restriction of KMS states.** The restriction of a β-KMS state to a closed invariant star
subalgebra `S` is a β-KMS state of the restricted dynamics as soon as it has norm one. -/
theorem IsKMSState.restrict (hω : α.IsKMSState β ω) {S : NonUnitalStarSubalgebra ℂ A}
    (hS : _root_.IsInvariant (fun t a => α t a) (S : Set A)) [IsClosed (S : Set A)]
    (hωS : ‖((ω.comp (.ofClass hS.subtypeHom) : S →P[ℂ] ℂ) : S →L[ℂ] ℂ)‖ = 1) :
    hS.restrict.IsKMSState β (ω.comp (.ofClass hS.subtypeHom)) :=
  hω.comp hS.subtypeHom hωS

end Pullback

end TauCeti.CStarAction
