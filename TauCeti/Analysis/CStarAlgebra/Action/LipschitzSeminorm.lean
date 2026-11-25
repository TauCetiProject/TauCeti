/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Basic
import TauCeti.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The Lipschitz seminorm of an action on a C⋆-algebra

For a group `G` with a length function `ℓ`, given as a Mathlib `GroupNorm`, and an action `α`
of `G` on a C⋆-algebra `A` by star automorphisms, the *action seminorm* of an element `a` is

`α.actionLip ℓ a = ⨆ g, ‖α g a - a‖ₑ / ℓ g`,

the least `C ∈ ℝ≥0∞` with `‖α g a - a‖ ≤ C ℓ g` for every `g`. The term at `g = 1` vanishes,
so this is the supremum over `g ≠ 1` of Rieffel's definition. Elements whose orbits are not
Lipschitz have value `∞`, so `actionLip` is an extended seminorm on the whole algebra rather
than a Mathlib `Seminorm`.

This file proves the algebraic and topological laws of the action seminorm:

* the evaluation estimate `‖α g a - a‖ₑ ≤ α.actionLip ℓ a * ℓ g` and the description of its
  sublevel sets, `CStarAction.actionLip_le_iff`, with the real forms
  `norm_apply_sub_le_toReal_actionLip_mul` and `actionLip_le_ofReal`;
* the seminorm laws: `actionLip_zero`, `actionLip_neg`, `actionLip_add_le`, homogeneity for
  complex and real scalars `actionLip_smul` and `actionLip_real_smul`, and invariance under the
  star operation, `actionLip_star`;
* the Leibniz inequality `actionLip_mul_le` and, for a unital algebra, the inverse estimate
  `actionLip_inv_le` for units;
* the zero set: `actionLip_eq_zero_iff` identifies it with the fixed points of the action, and
  `actionLip_add_of_forall_apply_eq` shows invariance under translation by fixed points;
* lower semicontinuity, `lowerSemicontinuous_actionLip`, so every sublevel set is norm closed;
* the unital star subalgebra `CStarAction.lipStarSubalgebra` of elements of finite action
  seminorm, and its density `dense_lipStarSubalgebra` for a compact group with a continuous
  length function.

For the density theorem, averaging an orbit against a continuous weight `f` on `G` gives an
element of finite action seminorm when the left translates of `f` move by at most a multiple
of `ℓ` (`actionLip_integral_smul_le`), and the average is close to `a` when `f` is a
probability density concentrated near `1` (`norm_integral_smul_sub_le`). The weights used are
the normalized bumps `g ↦ max (δ - ℓ g) 0`.

These are the properties of `actionLip` used, together with a compactness argument for ergodic
actions of compact groups with a continuous length function, to show that its restriction to the
self-adjoint part is a closed Lip-norm in Rieffel's sense. That compactness argument is not part
of this file.

## References

* M. A. Rieffel, *Metrics on states from actions of compact groups*, Doc. Math. 3 (1998),
  215–229, §2 (the definition, its seminorm and Leibniz laws, and Proposition 2.2 on density).
-/

public section

open scoped ENNReal

namespace TauCeti

namespace CStarAction

variable {G : Type*} [Group G] [TopologicalSpace G]

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The action seminorm `⨆ g, ‖α g a - a‖ₑ / ℓ g` of an element `a` for a length function `ℓ`
on `G`: by `actionLip_le_iff`, the least `C ∈ ℝ≥0∞` with `‖α g a - a‖ₑ ≤ C * ℓ g` for every
`g`. -/
noncomputable def actionLip (α : CStarAction G A) (ℓ : GroupNorm G) (a : A) : ℝ≥0∞ :=
  ⨆ g, ‖α g a - a‖ₑ / ENNReal.ofReal (ℓ g)

variable (α : CStarAction G A) (ℓ : GroupNorm G)

/-- Unfolding lemma for `actionLip`. -/
theorem actionLip_def (a : A) :
    α.actionLip ℓ a = ⨆ g, ‖α g a - a‖ₑ / ENNReal.ofReal (ℓ g) :=
  (rfl)

/-- Each quotient `‖α g a - a‖ₑ / ℓ g` is bounded by the action seminorm. -/
theorem eNorm_apply_sub_div_le_actionLip (g : G) (a : A) :
    ‖α g a - a‖ₑ / ENNReal.ofReal (ℓ g) ≤ α.actionLip ℓ a :=
  le_iSup (fun g ↦ ‖α g a - a‖ₑ / ENNReal.ofReal (ℓ g)) g

/-- The sublevel sets of the action seminorm: `L(a) ≤ r` exactly when `‖α g a - a‖ ≤ r ℓ g`
for every `g`. This holds for every `r`, including `r = ∞`. -/
theorem actionLip_le_iff {a : A} {r : ℝ≥0∞} :
    α.actionLip ℓ a ≤ r ↔ ∀ g, ‖α g a - a‖ₑ ≤ r * ENNReal.ofReal (ℓ g) := by
  refine iSup_le_iff.trans (forall_congr' fun g ↦ ?_)
  rcases eq_or_ne g 1 with rfl | hg
  · simp
  · exact ENNReal.div_le_iff (ENNReal.ofReal_pos.2 (map_pos_of_ne_one ℓ hg)).ne'
      ENNReal.ofReal_ne_top

/-- The evaluation estimate: the displacement of `a` by `g` is at most the action seminorm of
`a` times the length of `g`. -/
theorem eNorm_apply_sub_le_actionLip_mul (g : G) (a : A) :
    ‖α g a - a‖ₑ ≤ α.actionLip ℓ a * ENNReal.ofReal (ℓ g) :=
  (α.actionLip_le_iff ℓ).1 le_rfl g

/-- The real form of the evaluation estimate, for an element of finite action seminorm. -/
theorem norm_apply_sub_le_toReal_actionLip_mul {a : A} (ha : α.actionLip ℓ a ≠ ∞) (g : G) :
    ‖α g a - a‖ ≤ (α.actionLip ℓ a).toReal * ℓ g := by
  have h := α.eNorm_apply_sub_le_actionLip_mul ℓ g a
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (apply_nonneg ℓ g))] at h
  exact h

/-- A real Lipschitz bound `‖α g a - a‖ ≤ K ℓ g` for every `g` bounds the action seminorm. -/
theorem actionLip_le_ofReal {a : A} {K : ℝ} (h : ∀ g, ‖α g a - a‖ ≤ K * ℓ g) :
    α.actionLip ℓ a ≤ ENNReal.ofReal K :=
  (α.actionLip_le_iff ℓ).2 fun g ↦ by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul' (apply_nonneg ℓ g)]
    exact ENNReal.ofReal_le_ofReal (h g)

/-- The action seminorm vanishes exactly on the fixed points of the action. -/
theorem actionLip_eq_zero_iff {a : A} : α.actionLip ℓ a = 0 ↔ ∀ g, α g a = a := by
  simp [actionLip, ENNReal.div_eq_zero_iff, sub_eq_zero]

/-- The action seminorm vanishes at zero. -/
@[simp]
theorem actionLip_zero : α.actionLip ℓ 0 = 0 :=
  (α.actionLip_eq_zero_iff ℓ).2 fun g ↦ map_zero (α g)

/-- The action seminorm is invariant under negation. -/
@[simp]
theorem actionLip_neg (a : A) : α.actionLip ℓ (-a) = α.actionLip ℓ a := by
  simp only [actionLip, map_neg, ← neg_sub', eNorm_neg]

/-- The action seminorm is subadditive. -/
theorem actionLip_add_le (a b : A) :
    α.actionLip ℓ (a + b) ≤ α.actionLip ℓ a + α.actionLip ℓ b := by
  refine (α.actionLip_le_iff ℓ).2 fun g ↦ ?_
  calc ‖α g (a + b) - (a + b)‖ₑ = ‖(α g a - a) + (α g b - b)‖ₑ := by
        rw [map_add, add_sub_add_comm]
    _ ≤ ‖α g a - a‖ₑ + ‖α g b - b‖ₑ := eNorm_add_le _ _
    _ ≤ α.actionLip ℓ a * ENNReal.ofReal (ℓ g) + α.actionLip ℓ b * ENNReal.ofReal (ℓ g) :=
        add_le_add (α.eNorm_apply_sub_le_actionLip_mul ℓ g a)
          (α.eNorm_apply_sub_le_actionLip_mul ℓ g b)
    _ = (α.actionLip ℓ a + α.actionLip ℓ b) * ENNReal.ofReal (ℓ g) := (add_mul _ _ _).symm

/-- The action seminorm of a difference is at most the sum of the action seminorms. -/
theorem actionLip_sub_le (a b : A) :
    α.actionLip ℓ (a - b) ≤ α.actionLip ℓ a + α.actionLip ℓ b := by
  simpa [sub_eq_add_neg] using α.actionLip_add_le ℓ a (-b)

/-- The action seminorm is absolutely homogeneous for complex scalars. -/
theorem actionLip_smul (c : ℂ) (a : A) :
    α.actionLip ℓ (c • a) = ‖c‖ₑ * α.actionLip ℓ a := by
  simp only [actionLip, map_smul, ← smul_sub, eNorm_smul, mul_div_assoc, ENNReal.mul_iSup]

/-- The action seminorm is absolutely homogeneous for real scalars. -/
theorem actionLip_real_smul (r : ℝ) (a : A) :
    α.actionLip ℓ (r • a) = ‖r‖ₑ * α.actionLip ℓ a := by
  rw [← Complex.coe_smul, actionLip_smul, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- The action seminorm is invariant under the star operation. -/
@[simp]
theorem actionLip_star (a : A) : α.actionLip ℓ (star a) = α.actionLip ℓ a := by
  simp only [actionLip, map_star, ← star_sub, eNorm_eq_nnNorm, nnNorm_star]

/-- Translation by a fixed point of the action does not change the action seminorm. -/
theorem actionLip_add_of_forall_apply_eq {b : A} (hb : ∀ g, α g b = b) (a : A) :
    α.actionLip ℓ (a + b) = α.actionLip ℓ a := by
  simp only [actionLip, map_add, hb, add_sub_add_right_eq_sub]

/-- The Leibniz inequality `L(ab) ≤ L(a) ‖b‖ + ‖a‖ L(b)` for the action seminorm `L`. -/
theorem actionLip_mul_le (a b : A) :
    α.actionLip ℓ (a * b) ≤ α.actionLip ℓ a * ‖b‖ₑ + ‖a‖ₑ * α.actionLip ℓ b := by
  refine (α.actionLip_le_iff ℓ).2 fun g ↦ ?_
  calc ‖α g (a * b) - a * b‖ₑ = ‖(α g a - a) * α g b + a * (α g b - b)‖ₑ := by
        rw [map_mul, sub_mul, mul_sub, sub_add_sub_cancel]
    _ ≤ ‖α g a - a‖ₑ * ‖b‖ₑ + ‖a‖ₑ * ‖α g b - b‖ₑ := by
        refine (eNorm_add_le _ _).trans (add_le_add ?_ (eNorm_mul_le _ _))
        simpa only [StarAlgEquiv.eNorm_map] using eNorm_mul_le (α g a - a) (α g b)
    _ ≤ α.actionLip ℓ a * ENNReal.ofReal (ℓ g) * ‖b‖ₑ +
          ‖a‖ₑ * (α.actionLip ℓ b * ENNReal.ofReal (ℓ g)) := by
        gcongr <;> exact α.eNorm_apply_sub_le_actionLip_mul ℓ g _
    _ = (α.actionLip ℓ a * ‖b‖ₑ + ‖a‖ₑ * α.actionLip ℓ b) * ENNReal.ofReal (ℓ g) := by
        ring

/-- The trivial action has action seminorm zero. -/
@[simp]
theorem actionLip_trivial (a : A) : (trivial : CStarAction G A).actionLip ℓ a = 0 :=
  ((trivial : CStarAction G A).actionLip_eq_zero_iff ℓ).2 fun g ↦ trivial_apply g a

/-- Transporting an action along a star-algebra equivalence transports its action seminorm. -/
@[simp]
theorem actionLip_conjugate {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) (b : B) :
    (α.conjugate e).actionLip ℓ b = α.actionLip ℓ (e.symm b) := by
  simp only [actionLip, conjugate_apply]
  congr! 3 with g
  rw [← StarAlgEquiv.eNorm_map e, map_sub, e.apply_symm_apply]

/-- Every sublevel set of the action seminorm is norm closed. -/
theorem isClosed_setOf_actionLip_le (r : ℝ≥0∞) : IsClosed {a : A | α.actionLip ℓ a ≤ r} := by
  simp only [actionLip_le_iff, Set.ofPred_forall]
  exact isClosed_iInter fun g ↦ isClosed_le (by fun_prop) continuous_const

/-- The action seminorm is lower semicontinuous for the norm topology. -/
theorem lowerSemicontinuous_actionLip : LowerSemicontinuous (α.actionLip ℓ) :=
  lowerSemicontinuous_iff_isClosed_preimage.2 (α.isClosed_setOf_actionLip_le ℓ)

section Averaging

open MeasureTheory

variable [CompactSpace G]

section Measure

variable [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]

/-- Averaging the orbit of `a` against a continuous weight `f` whose left translates satisfy
`|f (h⁻¹ * g) - f g| ≤ C ℓ h` gives an element of action seminorm at most `C ‖a‖ μ(G)`. -/
theorem actionLip_integral_smul_le [BorelSpace G] [ContinuousMul G] [μ.IsMulLeftInvariant]
    {f : G → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ h g, |f (h⁻¹ * g) - f g| ≤ C * ℓ h) (a : A) :
    α.actionLip ℓ (∫ g, f g • α g a ∂μ) ≤ ENNReal.ofReal (C * ‖a‖ * μ.real Set.univ) := by
  have hint {k : G → ℝ} (hk : Continuous k) : Integrable (fun g ↦ k g • α g a) μ :=
    (hk.smul (α.continuous_orbit a)).integrable_of_hasCompactSupport (.of_compactSpace _)
  refine α.actionLip_le_ofReal ℓ fun h ↦ ?_
  -- Left invariance of `μ` moves the translation from the orbit onto the weight.
  have htrans : α h (∫ g, f g • α g a ∂μ) = ∫ g, f (h⁻¹ * g) • α g a ∂μ := by
    rw [← α.integral_comp_comm]
    refine Eq.trans ?_ (integral_mul_left_eq_self (fun g ↦ f (h⁻¹ * g) • α g a) h)
    congr! 2 with g
    rw [inv_mul_cancel_left, ← Complex.coe_smul, map_smul, Complex.coe_smul, mul_apply]
  rw [htrans, ← integral_sub (hint (k := fun g ↦ f (h⁻¹ * g)) (by fun_prop)) (hint hf)]
  simp_rw [← sub_smul]
  calc ‖∫ g, (f (h⁻¹ * g) - f g) • α g a ∂μ‖ ≤ C * ℓ h * ‖a‖ * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const <| .of_forall fun g ↦ by
          rw [norm_smul, Real.norm_eq_abs, StarAlgEquiv.norm_map]
          exact mul_le_mul_of_nonneg_right (hC h g) (norm_nonneg a)
    _ = C * ‖a‖ * μ.real Set.univ * ℓ h := by ring

/-- For a weight `f ≥ 0` of total mass one, the average of the orbit of `a` against `f`
differs from `a` by at most the `f`-average of the displacements `‖α g a - a‖`. -/
theorem norm_integral_smul_sub_le [OpensMeasurableSpace G] {f : G → ℝ} (hf : Continuous f)
    (hf₀ : 0 ≤ f) (hf₁ : ∫ g, f g ∂μ = 1) (a : A) :
    ‖(∫ g, f g • α g a ∂μ) - a‖ ≤ ∫ g, f g * ‖α g a - a‖ ∂μ := by
  have hint {F : G → A} (hF : Continuous F) : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (.of_compactSpace _)
  nth_rw 2 [← one_smul ℝ a]
  rw [← hf₁, ← integral_smul_const,
    ← integral_sub (hint (F := fun g ↦ f g • α g a) (by fun_prop))
      (hint (F := fun g ↦ f g • a) (by fun_prop))]
  simp_rw [← smul_sub]
  refine norm_integral_le_of_norm_le ((hf.mul ((α.continuous_orbit a).sub
    continuous_const).norm).integrable_of_hasCompactSupport (.of_compactSpace _))
    (.of_forall fun g ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg (hf₀ g)]

end Measure

/-- For a compact group with a continuous length function, the elements of finite action
seminorm are norm dense. -/
theorem dense_setOf_actionLip_ne_top [IsTopologicalGroup G] (hℓ : Continuous ℓ) :
    Dense {a : A | α.actionLip ℓ a ≠ ∞} := by
  borelize G
  refine fun a ↦ Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  -- Small values of `ℓ` force small displacements of `a`: the closed set where the
  -- displacement is at least `ε / 2` is compact and avoids `1`, so `ℓ` is bounded below on it.
  obtain ⟨δ, hδ, hδa⟩ : ∃ δ > 0, ∀ g, ℓ g < δ → ‖α g a - a‖ < ε / 2 := by
    set K := {g : G | ε / 2 ≤ ‖α g a - a‖}
    have hK : IsCompact K := (isClosed_le continuous_const (by fun_prop)).isCompact
    rcases K.eq_empty_or_nonempty with hK₀ | hK₀
    · exact ⟨1, one_pos, fun g _ ↦ not_le.1 fun hg ↦ hK₀.subset hg⟩
    obtain ⟨g₀, hg₀, hmin⟩ := hK.exists_isMinOn hK₀ hℓ.continuousOn
    refine ⟨ℓ g₀, map_pos_of_ne_one ℓ ?_, fun g hg ↦ not_le.1 fun hgK ↦ (hmin hgK).not_gt hg⟩
    rintro rfl
    simp [K, (half_pos hε).not_ge] at hg₀
  -- The normalized bump `f = φ / ∫ φ` with `φ g = max (δ - ℓ g) 0`.
  set μ : Measure G := Measure.haar
  set φ : G → ℝ := fun g ↦ max (δ - ℓ g) 0
  have hφc : Continuous φ := (continuous_const.sub hℓ).max continuous_const
  have hφ₀ : 0 ≤ φ := fun g ↦ le_max_right _ _
  have hI : 0 < ∫ g, φ g ∂μ := hφc.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (.of_compactSpace _) hφ₀ (x := 1) (by simp [φ, hδ])
  set f : G → ℝ := fun g ↦ φ g / ∫ g, φ g ∂μ
  have hfc : Continuous f := hφc.div_const _
  have hf₀ : 0 ≤ f := fun g ↦ div_nonneg (hφ₀ g) hI.le
  have hf₁ : ∫ g, f g ∂μ = 1 := by rw [integral_div, div_self hI.ne']
  refine ⟨∫ g, f g • α g a ∂μ, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (α.actionLip_integral_smul_le ℓ μ hfc (C := (∫ g, φ g ∂μ)⁻¹) (fun h g ↦ ?_) a), ?_⟩
  · -- The bump moves under left translation by at most `ℓ h`, since `ℓ` is a group norm.
    rw [← sub_div, abs_div, abs_of_pos hI, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ((abs_max_sub_max_le_abs _ _ _).trans ?_) (inv_pos.2 hI).le
    rw [sub_sub_sub_cancel_left, abs_sub_comm]
    simpa [div_eq_mul_inv] using abs_sub_map_le_div ℓ (h⁻¹ * g) g
  · rw [dist_comm, dist_eq_norm]
    refine (α.norm_integral_smul_sub_le μ hfc hf₀ hf₁ a).trans_lt ?_
    calc ∫ g, f g * ‖α g a - a‖ ∂μ ≤ ∫ g, f g * (ε / 2) ∂μ := by
          refine integral_mono_of_nonneg (.of_forall fun g ↦ by positivity)
            ((hfc.mul continuous_const).integrable_of_hasCompactSupport (.of_compactSpace _))
            (.of_forall fun g ↦ ?_)
          rcases (hf₀ g).eq_or_lt with hg | hg
          · simp [← hg]
          refine mul_le_mul_of_nonneg_left (hδa g ?_).le hg.le
          simpa [φ, sub_pos] using (div_pos_iff_of_pos_right hI).1 hg
      _ < ε := by rw [integral_mul_const, hf₁]; linarith

end Averaging

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] (α : CStarAction G A) (ℓ : GroupNorm G)

/-- Scalar multiples of the identity have action seminorm zero. -/
@[simp]
theorem actionLip_algebraMap (c : ℂ) : α.actionLip ℓ (algebraMap ℂ A c) = 0 :=
  (α.actionLip_eq_zero_iff ℓ).2 fun g ↦ AlgHomClass.commutes (α g) c

/-- The identity has action seminorm zero. -/
@[simp]
theorem actionLip_one : α.actionLip ℓ 1 = 0 :=
  (α.actionLip_eq_zero_iff ℓ).2 fun g ↦ map_one (α g)

/-- The inverse estimate `L(u⁻¹) ≤ ‖u⁻¹‖² L(u)` for a unit `u` of the algebra. -/
theorem actionLip_inv_le (u : Aˣ) :
    α.actionLip ℓ ↑u⁻¹ ≤ ‖(↑u⁻¹ : A)‖ₑ ^ 2 * α.actionLip ℓ u := by
  refine (α.actionLip_le_iff ℓ).2 fun g ↦ ?_
  have key : α g ↑u⁻¹ - ↑u⁻¹ = α g ↑u⁻¹ * (u - α g u) * ↑u⁻¹ := by
    simp [mul_sub, sub_mul, mul_assoc, ← map_mul]
  calc ‖α g ↑u⁻¹ - ↑u⁻¹‖ₑ = ‖α g ↑u⁻¹ * (u - α g u) * ↑u⁻¹‖ₑ := by rw [key]
    _ ≤ ‖α g ↑u⁻¹‖ₑ * ‖(u - α g u : A)‖ₑ * ‖(↑u⁻¹ : A)‖ₑ :=
        (eNorm_mul_le _ _).trans (by gcongr; exact eNorm_mul_le _ _)
    _ = ‖(↑u⁻¹ : A)‖ₑ * ‖α g u - u‖ₑ * ‖(↑u⁻¹ : A)‖ₑ := by
        rw [← eNorm_neg (u - α g u : A), neg_sub, StarAlgEquiv.eNorm_map]
    _ ≤ ‖(↑u⁻¹ : A)‖ₑ * (α.actionLip ℓ u * ENNReal.ofReal (ℓ g)) * ‖(↑u⁻¹ : A)‖ₑ := by
        gcongr
        exact α.eNorm_apply_sub_le_actionLip_mul ℓ g _
    _ = ‖(↑u⁻¹ : A)‖ₑ ^ 2 * α.actionLip ℓ u * ENNReal.ofReal (ℓ g) := by ring

/-- The elements of finite action seminorm form a unital star subalgebra. -/
noncomputable def lipStarSubalgebra : StarSubalgebra ℂ A where
  carrier := {a | α.actionLip ℓ a ≠ ∞}
  mul_mem' {a b} ha hb := by
    refine ne_top_of_le_ne_top ?_ (α.actionLip_mul_le ℓ a b)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ha eNorm_ne_top,
      ENNReal.mul_ne_top eNorm_ne_top hb⟩
  add_mem' {a b} ha hb :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ha, hb⟩) (α.actionLip_add_le ℓ a b)
  algebraMap_mem' c := by simp
  star_mem' {a} ha := by simpa using ha

@[simp]
theorem mem_lipStarSubalgebra {a : A} : a ∈ α.lipStarSubalgebra ℓ ↔ α.actionLip ℓ a ≠ ∞ :=
  Iff.rfl

/-- The carrier of `lipStarSubalgebra` is the finite domain of the action seminorm. -/
theorem coe_lipStarSubalgebra :
    (α.lipStarSubalgebra ℓ : Set A) = {a | α.actionLip ℓ a ≠ ∞} :=
  (rfl)

/-- For a compact group with a continuous length function, the star subalgebra of elements of
finite action seminorm is norm dense. -/
theorem dense_lipStarSubalgebra [CompactSpace G] [IsTopologicalGroup G] (hℓ : Continuous ℓ) :
    Dense (α.lipStarSubalgebra ℓ : Set A) := by
  rw [coe_lipStarSubalgebra]
  exact α.dense_setOf_actionLip_ne_top ℓ hℓ

end Unital

end CStarAction

end TauCeti
