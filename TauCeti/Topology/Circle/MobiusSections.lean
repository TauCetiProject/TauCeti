/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Topology.Instances.AddCircle.MobiusModule
import TauCeti.Topology.Instances.AddCircle.Coe

/-!
# Antiperiodic sections of the real Möbius line

Write the circle as `ℝ / ℤ`. An antiperiodic function `v` on `ℝ` determines a section of the
fixed line of the Möbius reflection by multiplying `v(t)` by `(cos (πt), sin (πt))`.
The inverse takes the coefficient along that unit vector. Via this comparison the doubled
trivialization is rotation by the half-angle, and the stabilization obstruction for the
reflection model gives exact order two for the reduced class in `K₀`.

For the bundle interpretation, see Charles A. Weibel, *The K-book*, Chapter I, §4.9.1.
-/

public section

namespace TauCeti

open ContinuousMap Module Real

local notation "T" => AddCircle (1 : ℝ)
local notation "R" => C(T, ℝ)

/-- The module of real functions on the covering line, with scalars pulled back from the circle. -/
@[expose] noncomputable def mobiusCoverModule : ModuleCat.{0} R :=
  letI := Module.compHom C(ℝ, ℝ)
    (compRightAlgHom ℝ ℝ ⟨((↑) : ℝ → T), continuous_quotient_mk'⟩).toRingHom
  ModuleCat.of R C(ℝ, ℝ)

/-- Read a vector in the restricted-scalar module as a continuous map on the covering line. -/
def mobiusCoverToContinuousMap (v : mobiusCoverModule) : C(ℝ, ℝ) := v

/-- The real section module of the Möbius line, expressed by antiperiodic functions. -/
def mobiusAntiperiodicSections : Submodule R mobiusCoverModule where
  carrier := {v | Function.Antiperiodic (mobiusCoverToContinuousMap v) 1}
  zero_mem' := fun _ ↦ neg_zero.symm
  add_mem' {v w} hv hw := fun t ↦ by
    -- The restricted module retains pointwise addition on the covering line.
    change mobiusCoverToContinuousMap v (t + 1) + mobiusCoverToContinuousMap w (t + 1) =
      -(mobiusCoverToContinuousMap v t + mobiusCoverToContinuousMap w t)
    rw [hv t, hw t, neg_add]
  smul_mem' f v hv := fun t ↦ by
    -- Restriction of scalars evaluates `f` at the quotient class before multiplying.
    change f ((t + 1 : ℝ) : T) * mobiusCoverToContinuousMap v (t + 1) =
      -(f (t : T) * mobiusCoverToContinuousMap v t)
    rw [AddCircle.coe_add_period, hv t, mul_neg]

/-- Membership in the section submodule is the sign-change condition over one turn. -/
@[simp] theorem mem_mobiusAntiperiodicSections (v : mobiusCoverModule) :
    v ∈ mobiusAntiperiodicSections ↔ Function.Antiperiodic (mobiusCoverToContinuousMap v) 1 :=
  (Iff.rfl)

/-- The type of continuous antiperiodic sections of the real Möbius line. -/
abbrev MobiusSections := ↥mobiusAntiperiodicSections

namespace MobiusSections

/-- Regard a continuous antiperiodic function on the covering line as a Möbius section. -/
def ofContinuousMap (v : C(ℝ, ℝ)) (hv : Function.Antiperiodic v 1) : MobiusSections :=
  ⟨v, (mem_mobiusAntiperiodicSections v).mpr hv⟩

/-- The underlying continuous map of a section on the covering line. -/
def toContinuousMap (v : MobiusSections) : C(ℝ, ℝ) := mobiusCoverToContinuousMap v.val

/-- Evaluate a section in the standard frame of the covering line. -/
def eval (v : MobiusSections) (t : ℝ) : ℝ := v.toContinuousMap t

/-- Evaluating the underlying continuous map is evaluation in the covering frame. -/
@[simp] theorem toContinuousMap_apply (v : MobiusSections) (t : ℝ) :
    v.toContinuousMap t = v.eval t := (rfl)

/-- The underlying map of a section constructed from an antiperiodic map is that map. -/
@[simp] theorem toContinuousMap_ofContinuousMap (v : C(ℝ, ℝ)) (hv : Function.Antiperiodic v 1) :
    (ofContinuousMap v hv).toContinuousMap = v := (rfl)

/-- The section constructed from an antiperiodic function has the same covering coordinates. -/
@[simp] theorem eval_ofContinuousMap (v : C(ℝ, ℝ)) (hv : Function.Antiperiodic v 1) (t : ℝ) :
    (ofContinuousMap v hv).eval t = v t := (rfl)

/-- Evaluation in the covering frame determines a section. -/
@[ext] theorem ext {v w : MobiusSections} (h : ∀ t, v.eval t = w.eval t) : v = w :=
  Subtype.ext (ContinuousMap.ext (f := v.toContinuousMap) (g := w.toContinuousMap) h)

/-- The covering coordinate of a section is continuous. -/
@[fun_prop] theorem continuous_eval (v : MobiusSections) : Continuous v.eval :=
  v.toContinuousMap.continuous

/-- The covering coordinate of a section is antiperiodic. -/
theorem antiperiodic_eval (v : MobiusSections) : Function.Antiperiodic v.eval 1 :=
  (mem_mobiusAntiperiodicSections _).mp v.property

/-- Addition of sections in the covering frame is pointwise. -/
@[simp] theorem add_eval (v w : MobiusSections) (t : ℝ) : (v + w).eval t = v.eval t + w.eval t :=
  (rfl)

/-- Negation of sections in the covering frame is pointwise. -/
@[simp] theorem neg_eval (v : MobiusSections) (t : ℝ) : (-v).eval t = -v.eval t := (rfl)

/-- Subtraction of sections in the covering frame is pointwise. -/
@[simp] theorem sub_eval (v w : MobiusSections) (t : ℝ) : (v - w).eval t = v.eval t - w.eval t :=
  (rfl)

/-- Scalar multiplication uses the value of the scalar at the corresponding circle point. -/
@[simp] theorem smul_eval (f : R) (v : MobiusSections) (t : ℝ) :
    (f • v).eval t = f (t : T) * v.eval t := (rfl)

/-- The zero section vanishes at every point. -/
@[simp] theorem zero_eval (t : ℝ) : (0 : MobiusSections).eval t = 0 := (rfl)

private theorem antiperiodic_cosHalf : Function.Antiperiodic (fun t ↦ cos (π * t)) 1 := by
  intro t
  simp [mul_add, cos_add_pi]

private theorem antiperiodic_sinHalf : Function.Antiperiodic (fun t ↦ sin (π * t)) 1 := by
  intro t
  simp [mul_add, sin_add_pi]

/-- Evaluation in the covering frame hits every real number at each point. -/
theorem eval_surjective (t : ℝ) : Function.Surjective (fun v : MobiusSections ↦ v.eval t) := by
  intro a
  let f : C(ℝ, ℝ) := ⟨fun s ↦ a * cos (π * (s - t)), by fun_prop⟩
  have h : Function.Antiperiodic f 1 := (antiperiodic_cosHalf.sub_const t).smul a
  exact ⟨ofContinuousMap f h, by simp [f]⟩

private noncomputable def reflectionCoords (v : MobiusSections) : Fin 2 → R :=
  have hc := v.antiperiodic_eval.mul antiperiodic_cosHalf
  have hs := v.antiperiodic_eval.mul antiperiodic_sinHalf
  ![⟨hc.lift, hc.continuous_lift (by fun_prop)⟩, ⟨hs.lift, hs.continuous_lift (by fun_prop)⟩]

private theorem reflectionCoords_zero (v : MobiusSections) (t : ℝ) :
    reflectionCoords v 0 (t : T) = v.eval t * cos (π * t) := by
  simp [reflectionCoords, Function.Periodic.lift_coe]

private theorem reflectionCoords_one (v : MobiusSections) (t : ℝ) :
    reflectionCoords v 1 (t : T) = v.eval t * sin (π * t) := by
  simp [reflectionCoords, Function.Periodic.lift_coe]

private theorem reflectionCoords_mem (v : MobiusSections) :
    reflectionCoords v ∈ mobiusSections := by
  refine mem_mobiusSections_iff.mpr fun t ↦ ?_
  rw [reflectionCoords_zero, reflectionCoords_one, mul_assoc, cos_two_mul, sin_two_mul]
  constructor
  · linear_combination 2 * v.eval t * cos (π * t) * cos_sq_add_sin_sq (π * t)
  · ring

/-- The antiperiodic section model is linearly equivalent to the reflection's fixed module.
The forward map multiplies by the unit vector `(cos (πt), sin (πt))`, and the inverse takes
its coefficient along that vector. -/
noncomputable def reflectionLinearEquiv : MobiusSections ≃ₗ[R] mobiusSections where
  toFun v := ⟨reflectionCoords v, reflectionCoords_mem v⟩
  invFun w := ofContinuousMap ⟨mobiusSectionCoeff w, continuous_mobiusSectionCoeff w⟩
    (antiperiodic_mobiusSectionCoeff w)
  left_inv v := by
    apply MobiusSections.ext
    intro t
    simp only [eval_ofContinuousMap, coe_mk, mobiusSectionCoeff_apply, reflectionCoords_zero,
      reflectionCoords_one]
    linear_combination v.eval t * cos_sq_add_sin_sq (π * t)
  right_inv w := by
    apply Subtype.ext
    funext i
    apply AddCircle.continuousMap_ext_coe
    intro t
    obtain ⟨h₀, h₁⟩ := apply_eq_mobiusSectionCoeff_mul w.property t
    let v := ofContinuousMap ⟨mobiusSectionCoeff w, continuous_mobiusSectionCoeff w⟩
      (antiperiodic_mobiusSectionCoeff w)
    have hzero : reflectionCoords v 0 (t : T) = (w : Fin 2 → R) 0 (t : T) := by
      rw [reflectionCoords_zero]
      exact h₀.symm
    have hone : reflectionCoords v 1 (t : T) = (w : Fin 2 → R) 1 (t : T) := by
      rw [reflectionCoords_one]
      exact h₁.symm
    fin_cases i
    · exact hzero
    · exact hone
  map_add' v w := by
    apply Subtype.ext
    funext i
    apply AddCircle.continuousMap_ext_coe
    intro t
    fin_cases i <;>
      simp [reflectionCoords_zero, reflectionCoords_one, add_mul]
  map_smul' f v := by
    apply Subtype.ext
    funext i
    apply AddCircle.continuousMap_ext_coe
    intro t
    fin_cases i <;>
      simp [reflectionCoords_zero, reflectionCoords_one, smul_eq_mul, mul_assoc]

/-- The first coordinate after multiplying by the unit vector on the fixed line. -/
@[simp] theorem reflectionLinearEquiv_apply_zero (v : MobiusSections) (t : ℝ) :
    (reflectionLinearEquiv v : Fin 2 → R) 0 (t : T) = v.eval t * cos (π * t) :=
  reflectionCoords_zero v t

/-- The second coordinate after multiplying by the unit vector on the fixed line. -/
@[simp] theorem reflectionLinearEquiv_apply_one (v : MobiusSections) (t : ℝ) :
    (reflectionLinearEquiv v : Fin 2 → R) 1 (t : T) = v.eval t * sin (π * t) :=
  reflectionCoords_one v t

/-- In the inverse comparison, the covering coordinate is the coefficient along the unit vector. -/
@[simp] theorem reflectionLinearEquiv_symm_eval (w : mobiusSections) (t : ℝ) :
    (reflectionLinearEquiv.symm w).eval t = mobiusSectionCoeff w t := (rfl)

/-- The antiperiodic section module is finite, by comparison with the reflection model. -/
instance : Module.Finite R MobiusSections :=
  Module.Finite.of_surjective reflectionLinearEquiv.symm.toLinearMap
    reflectionLinearEquiv.symm.surjective

/-- The antiperiodic section module is projective, by comparison with the reflection model. -/
instance : Module.Projective R MobiusSections :=
  Module.Projective.of_equiv reflectionLinearEquiv.symm

/-- Rotation by `πt` sends a pair of antiperiodic coordinates to periodic coordinates. -/
noncomputable def prodLinearEquiv : (MobiusSections × MobiusSections) ≃ₗ[R] (R × R) :=
  (reflectionLinearEquiv.prodCongr reflectionLinearEquiv).trans
    (mobiusSectionsProdEquiv.trans (LinearEquiv.finTwoArrow R R))

/-- The first coordinate of the doubled trivialization in the covering frame. -/
@[simp] theorem prodLinearEquiv_fst_apply (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (prodLinearEquiv vw).1 (t : T) = cos (π * t) * vw.1.eval t - sin (π * t) * vw.2.eval t := by
  simp [prodLinearEquiv, Matrix.vecHead, sub_eq_add_neg, mul_comm]

/-- The second coordinate of the doubled trivialization in the covering frame. -/
@[simp] theorem prodLinearEquiv_snd_apply (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (prodLinearEquiv vw).2 (t : T) = sin (π * t) * vw.1.eval t + cos (π * t) * vw.2.eval t := by
  simp [prodLinearEquiv, Matrix.vecHead, Matrix.vecTail, mul_comm]

/-- The first covering coordinate of the inverse doubled trivialization. -/
@[simp] theorem prodLinearEquiv_symm_fst_eval (ab : R × R) (t : ℝ) :
    (prodLinearEquiv.symm ab).1.eval t =
      cos (π * t) * ab.1 (t : T) + sin (π * t) * ab.2 (t : T) := by
  have hfst := prodLinearEquiv_fst_apply (prodLinearEquiv.symm ab) t
  have hsnd := prodLinearEquiv_snd_apply (prodLinearEquiv.symm ab) t
  rw [prodLinearEquiv.apply_symm_apply] at hfst hsnd
  rw [hfst, hsnd]
  linear_combination -(prodLinearEquiv.symm ab).1.eval t * cos_sq_add_sin_sq (π * t)

/-- The second covering coordinate of the inverse doubled trivialization. -/
@[simp] theorem prodLinearEquiv_symm_snd_eval (ab : R × R) (t : ℝ) :
    (prodLinearEquiv.symm ab).2.eval t = -(sin (π * t) * ab.1 (t : T)) +
      cos (π * t) * ab.2 (t : T) := by
  have hfst := prodLinearEquiv_fst_apply (prodLinearEquiv.symm ab) t
  have hsnd := prodLinearEquiv_snd_apply (prodLinearEquiv.symm ab) t
  rw [prodLinearEquiv.apply_symm_apply] at hfst hsnd
  rw [hfst, hsnd]
  linear_combination -(prodLinearEquiv.symm ab).2.eval t * cos_sq_add_sin_sq (π * t)

/-- A single Möbius line cannot be made free of rank `n + 1` by adding `n` free generators. -/
theorem not_nonempty_stabilizedLinearEquiv (n : ℕ) :
    ¬ Nonempty ((MobiusSections × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) := by
  rintro ⟨e⟩
  exact (isEmpty_mobiusSections_prod_linearEquiv n).false
    ((reflectionLinearEquiv.symm.prodCongr (LinearEquiv.refl R _)).trans e)

-- Right modules over a commutative ring are obtained by restriction along `unop`.
private noncomputable def toRightKZero :
    SplitK0.{0} (finiteProjectiveModules R).FullSubcategory ≃+ KZero R :=
  SplitK0.mapEquiv.{0, 0} ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.toOpposite R).symm).finiteProjectiveModulesEquivalence)

/-- The class of the Möbius module minus the class of the free line. -/
noncomputable def reducedClass : KZero R :=
  toRightKZero (FiniteProjectiveModules.classOf R MobiusSections 1)

/-- The reduced class is the left-module class transported by restriction along `unop`. -/
theorem reducedClass_def : reducedClass =
    SplitK0.mapEquiv.{0, 0} ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.toOpposite R).symm).finiteProjectiveModulesEquivalence)
      (FiniteProjectiveModules.classOf R MobiusSections 1) := (rfl)

/-- The reduced class of the real Möbius line has exact additive order two. -/
theorem addOrderOf_reducedClass : addOrderOf reducedClass = 2 := by
  let x := FiniteProjectiveModules.classOf R MobiusSections 1
  have hne : x ≠ 0 := by
    intro hx
    obtain ⟨n, hn⟩ := (FiniteProjectiveModules.classOf_eq_zero_iff 1).mp hx
    exact not_nonempty_stabilizedLinearEquiv n (hn.map fun e ↦ e.trans
      (LinearEquiv.piCongrLeft R (fun _ ↦ R) (finCongr (Nat.add_comm 1 n))))
  have htwo : 2 • x = 0 := by
    rw [two_nsmul, ← FiniteProjectiveModules.classOf_prod 1 1]
    exact (FiniteProjectiveModules.classOf_congr
      (prodLinearEquiv.trans (LinearEquiv.finTwoArrow R R).symm) 2).trans
        (FiniteProjectiveModules.classOf_free R 2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply addOrderOf_eq_prime_iff.mpr
  exact ⟨by rw [reducedClass, ← map_nsmul, htwo, map_zero],
    fun h ↦ hne (toRightKZero.injective (h.trans (map_zero toRightKZero).symm))⟩

end MobiusSections

end TauCeti
