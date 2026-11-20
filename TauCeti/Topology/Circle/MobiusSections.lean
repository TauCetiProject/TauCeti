/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Topology.Instances.AddCircle.Coe
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.Instances.Matrix

/-!
# Real sections of the Möbius line

Write the circle as `ℝ / ℤ`. A section of the Möbius line is an antiperiodic real function on
`ℝ`, with scalars acting by pullback from the circle. Two copies become free of rank two via
rotation by the half-angle. In contrast, adjoining any finite free module to a single copy does
not give a free module of the corresponding rank: the determinant of a putative frame would be
continuous, nowhere zero and antiperiodic. The resulting class `[M] - [R]` in projective `K₀`
has exact order two, where `R = C(ℝ / ℤ, ℝ)`.

For the bundle interpretation, see Charles A. Weibel, *The K-book*, Chapter I, §4.9.1.
-/

public section

namespace TauCeti

open ContinuousMap Module

local notation "T" => AddCircle (1 : ℝ)
local notation "R" => C(T, ℝ)

/-- The module of real functions on the covering line, with scalars pulled back from the circle. -/
@[expose] noncomputable def mobiusCoverModule : ModuleCat.{0} R :=
  letI := Module.compHom C(ℝ, ℝ)
    (compRightAlgHom ℝ ℝ ⟨((↑) : ℝ → T), continuous_quotient_mk'⟩).toRingHom
  ModuleCat.of R C(ℝ, ℝ)

/-- The real section module of the Möbius line, expressed by antiperiodic functions. -/
def mobiusSections : Submodule R mobiusCoverModule where
  carrier := {v | Function.Antiperiodic (show C(ℝ, ℝ) from v) (1 : ℝ)}
  zero_mem' := fun _ ↦ neg_zero.symm
  add_mem' {v w} hv hw := fun t ↦ by
    let a : C(ℝ, ℝ) := v
    let b : C(ℝ, ℝ) := w
    -- The ambient addition is that of continuous maps, evaluated at `t + 1` and `t`.
    change a (t + 1) + b (t + 1) = -(a t + b t)
    have ha : a (t + 1) = -a t := hv t
    have hb : b (t + 1) = -b t := hw t
    rw [ha, hb, neg_add]
  smul_mem' f v hv := fun t ↦ by
    let a : C(ℝ, ℝ) := v
    -- Expose the pointwise values of the restricted scalar action.
    change f ((t + 1 : ℝ) : T) * a (t + 1) = -(f (t : T) * a t)
    have ha : a (t + 1) = -a t := hv t
    rw [AddCircle.coe_add_period, ha, mul_neg]

/-- A function lies in the Möbius section module exactly when it changes sign on translation
by one. -/
@[simp] theorem mem_mobiusSections (v : mobiusCoverModule) :
    v ∈ mobiusSections ↔ Function.Antiperiodic (show C(ℝ, ℝ) from v) (1 : ℝ) := (Iff.rfl)

/-- The type of continuous antiperiodic sections of the real Möbius line. -/
abbrev MobiusSections := ↥mobiusSections

namespace MobiusSections

/-- Regard a continuous antiperiodic function on the covering line as a Möbius section. -/
def ofContinuousMap (v : C(ℝ, ℝ)) (hv : Function.Antiperiodic v (1 : ℝ)) : MobiusSections :=
  ⟨v, (mem_mobiusSections _).mpr hv⟩

/-- Evaluate a section in the standard frame of the covering line. -/
def eval (v : MobiusSections) (t : ℝ) : ℝ := (show C(ℝ, ℝ) from v.val) t

/-- The section constructed from an antiperiodic function has the same covering coordinates. -/
@[simp] theorem eval_ofContinuousMap (v : C(ℝ, ℝ)) (hv : Function.Antiperiodic v (1 : ℝ))
    (t : ℝ) : (ofContinuousMap v hv).eval t = v t := (rfl)

/-- Evaluation in the covering frame determines a section. -/
@[ext] theorem ext {v w : MobiusSections} (h : ∀ t, v.eval t = w.eval t) : v = w :=
  Subtype.ext (ContinuousMap.ext (f := (show C(ℝ, ℝ) from v.val))
    (g := (show C(ℝ, ℝ) from w.val)) h)

/-- The covering coordinate of a section is continuous. -/
@[fun_prop] theorem continuous_eval (v : MobiusSections) : Continuous v.eval :=
  (show C(ℝ, ℝ) from v.val).continuous

/-- The covering coordinate of a section is antiperiodic. -/
theorem antiperiodic_eval (v : MobiusSections) : Function.Antiperiodic v.eval 1 :=
  (mem_mobiusSections _).mp v.property

/-- Addition of sections in the covering frame is pointwise. -/
@[simp] theorem add_eval (v w : MobiusSections) (t : ℝ) : (v + w).eval t = v.eval t + w.eval t :=
  (rfl)

/-- Scalar multiplication uses the value of the scalar at the corresponding circle point. -/
@[simp] theorem smul_eval (f : R) (v : MobiusSections) (t : ℝ) :
    (f • v).eval t = f (t : T) * v.eval t := (rfl)

/-- The zero section vanishes at every point. -/
@[simp] theorem zero_eval (t : ℝ) : (0 : MobiusSections).eval t = 0 := (rfl)

private noncomputable abbrev cosHalf (t : ℝ) := Real.cos (Real.pi * t)
private noncomputable abbrev sinHalf (t : ℝ) := Real.sin (Real.pi * t)

private theorem cosHalf_anti : Function.Antiperiodic cosHalf 1 := by
  intro t
  simp [cosHalf, mul_add, Real.cos_add_pi]

private theorem sinHalf_anti : Function.Antiperiodic sinHalf 1 := by
  intro t
  simp [sinHalf, mul_add, Real.sin_add_pi]

private noncomputable def rotate (vw : MobiusSections × MobiusSections) : R × R :=
  have hc : Continuous cosHalf := by fun_prop
  have hs : Continuous sinHalf := by fun_prop
  ⟨((cosHalf_anti.mul vw.1.antiperiodic_eval).sub
      (sinHalf_anti.mul vw.2.antiperiodic_eval)).liftContinuousMap
        ((hc.mul vw.1.continuous_eval).sub (hs.mul vw.2.continuous_eval)),
    ((sinHalf_anti.mul vw.1.antiperiodic_eval).add
      (cosHalf_anti.mul vw.2.antiperiodic_eval)).liftContinuousMap
        ((hs.mul vw.1.continuous_eval).add (hc.mul vw.2.continuous_eval))⟩

private noncomputable def unrotate (ab : R × R) : MobiusSections × MobiusSections :=
  ⟨ofContinuousMap ⟨fun t ↦ cosHalf t * ab.1 (t : T) + sinHalf t * ab.2 (t : T), by fun_prop⟩
      (fun t ↦ by simp only [coe_mk, cosHalf_anti t, sinHalf_anti t, AddCircle.coe_add_period,
        neg_mul, neg_add]),
    ofContinuousMap ⟨fun t ↦ -(sinHalf t * ab.1 (t : T)) + cosHalf t * ab.2 (t : T), by fun_prop⟩
      (fun t ↦ by simp only [coe_mk, cosHalf_anti t, sinHalf_anti t, AddCircle.coe_add_period,
        neg_mul, neg_add])⟩

private theorem rotate_fst (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (rotate vw).1 (t : T) = cosHalf t * vw.1.eval t - sinHalf t * vw.2.eval t := by
  simp [rotate]

private theorem rotate_snd (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (rotate vw).2 (t : T) = sinHalf t * vw.1.eval t + cosHalf t * vw.2.eval t := by
  simp [rotate]

private theorem unrotate_fst (ab : R × R) (t : ℝ) :
    (unrotate ab).1.eval t = cosHalf t * ab.1 (t : T) + sinHalf t * ab.2 (t : T) := (rfl)

private theorem unrotate_snd (ab : R × R) (t : ℝ) :
    (unrotate ab).2.eval t = -(sinHalf t * ab.1 (t : T)) + cosHalf t * ab.2 (t : T) := (rfl)

/-- Two copies of the Möbius line have a free section module: rotation by `πt` sends the two
antiperiodic coordinates at `t` to a periodic pair. -/
noncomputable def prodLinearEquiv :
    (MobiusSections × MobiusSections) ≃ₗ[R] (R × R) where
  toFun := rotate
  invFun := unrotate
  left_inv vw := by
    apply Prod.ext <;> apply MobiusSections.ext <;> intro t
    · rw [unrotate_fst, rotate_fst, rotate_snd]
      linear_combination vw.1.eval t * Real.cos_sq_add_sin_sq (Real.pi * t)
    · rw [unrotate_snd, rotate_fst, rotate_snd]
      linear_combination vw.2.eval t * Real.cos_sq_add_sin_sq (Real.pi * t)
  right_inv ab := by
    apply Prod.ext <;> apply AddCircle.continuousMap_ext_coe <;> intro t
    · rw [rotate_fst, unrotate_fst, unrotate_snd]
      linear_combination ab.1 (t : T) * Real.cos_sq_add_sin_sq (Real.pi * t)
    · rw [rotate_snd, unrotate_fst, unrotate_snd]
      linear_combination ab.2 (t : T) * Real.cos_sq_add_sin_sq (Real.pi * t)
  map_add' v w := by
    apply Prod.ext <;> apply AddCircle.continuousMap_ext_coe <;> intro t <;>
      simp only [Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply, rotate_fst, rotate_snd,
        add_eval] <;> ring
  map_smul' f v := by
    apply Prod.ext <;> apply AddCircle.continuousMap_ext_coe <;> intro t <;>
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        ContinuousMap.mul_apply, rotate_fst, rotate_snd, smul_eval] <;> ring

/-- The first coordinate of the doubled trivialization in the covering frame. -/
@[simp] theorem prodLinearEquiv_fst_apply (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (prodLinearEquiv vw).1 (t : T) =
      Real.cos (Real.pi * t) * vw.1.eval t - Real.sin (Real.pi * t) * vw.2.eval t :=
  rotate_fst vw t

/-- The second coordinate of the doubled trivialization in the covering frame. -/
@[simp] theorem prodLinearEquiv_snd_apply (vw : MobiusSections × MobiusSections) (t : ℝ) :
    (prodLinearEquiv vw).2 (t : T) =
      Real.sin (Real.pi * t) * vw.1.eval t + Real.cos (Real.pi * t) * vw.2.eval t :=
  rotate_snd vw t

/-- The first covering coordinate of the inverse doubled trivialization. -/
@[simp] theorem prodLinearEquiv_symm_fst_eval (ab : R × R) (t : ℝ) :
    (prodLinearEquiv.symm ab).1.eval t =
      Real.cos (Real.pi * t) * ab.1 (t : T) + Real.sin (Real.pi * t) * ab.2 (t : T) :=
  unrotate_fst ab t

/-- The second covering coordinate of the inverse doubled trivialization. -/
@[simp] theorem prodLinearEquiv_symm_snd_eval (ab : R × R) (t : ℝ) :
    (prodLinearEquiv.symm ab).2.eval t =
      -(Real.sin (Real.pi * t) * ab.1 (t : T)) + Real.cos (Real.pi * t) * ab.2 (t : T) :=
  unrotate_snd ab t

/-- Evaluation in the covering frame hits every real number at each point. -/
theorem eval_surjective (t : ℝ) : Function.Surjective (fun v : MobiusSections ↦ v.eval t) := by
  intro a
  let f : C(ℝ, ℝ) := ⟨fun s ↦ a * cosHalf (s - t), by fun_prop⟩
  have h : Function.Antiperiodic f 1 := (cosHalf_anti.sub_const t).smul a
  exact ⟨ofContinuousMap f h, by simp [f, cosHalf]⟩

instance : Module.Finite R MobiusSections :=
  letI : Module.Finite R (MobiusSections × MobiusSections) :=
    Module.Finite.of_surjective prodLinearEquiv.symm.toLinearMap prodLinearEquiv.symm.surjective
  Module.Finite.of_surjective (LinearMap.fst R MobiusSections MobiusSections)
    (fun v ↦ ⟨(v, 0), rfl⟩)

instance : Module.Projective R MobiusSections :=
  letI : Module.Projective R (MobiusSections × MobiusSections) :=
    Module.Projective.of_equiv prodLinearEquiv.symm
  Module.Projective.of_split (LinearMap.inl R MobiusSections MobiusSections)
    (LinearMap.fst R MobiusSections MobiusSections) (by ext; rfl)

private def stabilizedEval {n : ℕ} (t : ℝ) :
    (MobiusSections × (Fin n → R)) →+ (Fin (n + 1) → ℝ) where
  toFun v := Fin.cons (v.1.eval t) (fun i ↦ v.2 i (t : T))
  map_zero' := by ext i; cases i using Fin.cases <;> simp
  map_add' v w := by ext i; cases i using Fin.cases <;> simp

private theorem stabilizedEval_smul {n : ℕ} (t : ℝ) (f : R)
    (v : MobiusSections × (Fin n → R)) (i : Fin (n + 1)) :
    stabilizedEval t (f • v) i = f (t : T) * stabilizedEval t v i := by
  cases i using Fin.cases <;>
    simp [stabilizedEval, smul_eq_mul, ContinuousMap.mul_apply]

private theorem stabilizedEval_surjective {n : ℕ} (t : ℝ) :
    Function.Surjective (stabilizedEval (n := n) t) := by
  intro y
  obtain ⟨v, hv⟩ := eval_surjective t (y 0)
  refine ⟨(v, fun i ↦ ContinuousMap.const T (y i.succ)), ?_⟩
  ext i
  cases i using Fin.cases <;> simp [stabilizedEval, hv]

private noncomputable def frameMatrix {n : ℕ}
    (b : Basis (Fin (n + 1)) R (MobiusSections × (Fin n → R))) (t : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j ↦ stabilizedEval t (b j) i

private theorem continuous_frameMatrix {n : ℕ}
    (b : Basis (Fin (n + 1)) R (MobiusSections × (Fin n → R))) :
    Continuous (frameMatrix b) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  cases i using Fin.cases
  · exact (b j).1.continuous_eval
  · exact ((b j).2 _).continuous.comp continuous_quotient_mk'

private theorem det_frameMatrix_ne_zero {n : ℕ}
    (b : Basis (Fin (n + 1)) R (MobiusSections × (Fin n → R))) (t : ℝ) :
    (frameMatrix b t).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨v, rfl⟩ := stabilizedEval_surjective t y
  refine ⟨fun j ↦ b.repr v j (t : T), ?_⟩
  funext i
  conv_rhs => rw [← b.sum_repr v, map_sum, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, frameMatrix, Matrix.of_apply, stabilizedEval_smul, mul_comm]

private theorem antiperiodic_det_frameMatrix {n : ℕ}
    (b : Basis (Fin (n + 1)) R (MobiusSections × (Fin n → R))) :
    Function.Antiperiodic (fun t ↦ (frameMatrix b t).det) 1 := by
  intro t
  have h : frameMatrix b (t + 1) =
      (frameMatrix b t).updateRow 0 ((-1 : ℝ) • frameMatrix b t 0) := by
    ext i j
    cases i using Fin.cases
    · simp [frameMatrix, stabilizedEval, (b j).1.antiperiodic_eval t]
    · simp [frameMatrix, stabilizedEval]
  -- Translation by one negates the determinant because it negates exactly the first row.
  have hdet := Matrix.det_updateRow_smul (frameMatrix b t) 0 (-1 : ℝ) (frameMatrix b t 0)
  simpa [h] using hdet

/-- A single Möbius line cannot be made free of rank `n + 1` by adding `n` free generators. -/
theorem not_nonempty_stabilizedLinearEquiv (n : ℕ) :
    ¬ Nonempty ((MobiusSections × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) := by
  rintro ⟨e⟩
  let b := (Pi.basisFun R (Fin (n + 1))).map e.symm
  let f : ℝ → ℝ := fun t ↦ (frameMatrix b t).det
  have hc : Continuous f := (continuous_frameMatrix b).matrix_det
  have h : f 1 = -f 0 := (antiperiodic_det_frameMatrix b).eq
  obtain ⟨t, -, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
    rcases le_total (f 0) 0 with h₀ | h₀
    · exact intermediate_value_Icc zero_le_one hc.continuousOn ⟨h₀, by linarith⟩
    · exact intermediate_value_Icc' zero_le_one hc.continuousOn ⟨by linarith, h₀⟩
  exact det_frameMatrix_ne_zero b t ht

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
