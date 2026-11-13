/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugate

/-!
# Topology and norm on the complex conjugate of a complex vector space

The conjugate `TauCeti.Conjugate V` of a complex module `V`
(`TauCeti.LinearAlgebra.Complex.Conjugate`) carries the topology and (semi)norm of `V`; with the
conjugated complex action it is again a topological vector space and a normed space. The identity
`V → Conjugate V` is a continuous conjugate-linear equivalence (`TauCeti.Conjugate.toConjL`),
conjugating twice gives back `V`, and conjugation commutes with products.

## Main declarations

* `TauCeti.Conjugate.toConjL`: the identity as a continuous conjugate-linear equivalence;
  `TauCeti.Conjugate.toConjL'` is the identity as a continuous real-linear one.
* `ContinuousLinearMap.conjugate`: the conjugate of a continuous complex-linear map, an isometry.
* `ContinuousLinearMap.toConjugate`: continuous conjugate-linear maps `V → W` are equivalent to
  continuous complex-linear maps `V → Conjugate W`.
* `TauCeti.Conjugate.doubleConjugateL`: `Conjugate (Conjugate V) ≃L[ℂ] V`.
* `TauCeti.Conjugate.prodL`: `Conjugate (V × W) ≃L[ℂ] Conjugate V × Conjugate W`.
* `TauCeti.Conjugate.complexConjL`: complex conjugation is a complex-linear isomorphism
  `ℂ ≃L[ℂ] Conjugate ℂ`; it agrees with the identity exactly on the real line.
-/

public section

noncomputable section

open ComplexConjugate

namespace TauCeti

namespace Conjugate

variable {V W : Type*}

/-! ### Topological and normed structure -/

instance instTopologicalSpace [TopologicalSpace V] : TopologicalSpace (Conjugate V) :=
  ‹TopologicalSpace V›

/-- The identity map `V → Conjugate V` as a homeomorphism. -/
def toConjHomeomorph [TopologicalSpace V] : V ≃ₜ Conjugate V where
  __ := toConj
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem coe_toConjHomeomorph [TopologicalSpace V] :
    ⇑(toConjHomeomorph : V ≃ₜ Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjHomeomorph_symm [TopologicalSpace V] :
    ⇑(toConjHomeomorph : V ≃ₜ Conjugate V).symm = ofConj := (rfl)

theorem continuous_toConj [TopologicalSpace V] : Continuous (toConj : V → Conjugate V) :=
  continuous_id

theorem continuous_ofConj [TopologicalSpace V] : Continuous (ofConj : Conjugate V → V) :=
  continuous_id

instance instContinuousAdd [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V] :
    ContinuousAdd (Conjugate V) :=
  ‹ContinuousAdd V›

instance instIsTopologicalAddGroup [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] : IsTopologicalAddGroup (Conjugate V) :=
  ‹IsTopologicalAddGroup V›

instance instContinuousSMulReal [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [ContinuousSMul ℝ V] : ContinuousSMul ℝ (Conjugate V) :=
  ‹ContinuousSMul ℝ V›

instance instContinuousSMulComplex [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [ContinuousSMul ℂ V] : ContinuousSMul ℂ (Conjugate V) where
  continuous_smul := (continuous_smul (M := ℂ) (X := V)).comp
    (Complex.continuous_conj.prodMap continuous_id)

instance instContinuousConstSMulComplex [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [ContinuousConstSMul ℂ V] : ContinuousConstSMul ℂ (Conjugate V) where
  continuous_const_smul c := continuous_const_smul (conj c : ℂ) (T := V)

instance instT2Space [TopologicalSpace V] [T2Space V] : T2Space (Conjugate V) := ‹T2Space V›

/-- The seminorm of the conjugate is that of `V`. It is built field by field, rather than as the
instance of `V` itself, so that `instNormedAddCommGroup` restricts to it up to instance
reducibility and the normed-space instances below apply to normed `V`. -/
instance instSeminormedAddCommGroup [h : SeminormedAddCommGroup V] :
    SeminormedAddCommGroup (Conjugate V) where
  toNorm := h.toNorm
  toAddCommGroup := h.toAddCommGroup
  toPseudoMetricSpace := h.toPseudoMetricSpace
  dist_eq := h.dist_eq

/-- The norm of the conjugate is that of `V`, extending `instSeminormedAddCommGroup`. -/
instance instNormedAddCommGroup [NormedAddCommGroup V] : NormedAddCommGroup (Conjugate V) where
  __ := instSeminormedAddCommGroup
  eq_of_dist_eq_zero := eq_of_dist_eq_zero (γ := V)

@[simp] theorem norm_toConj [SeminormedAddCommGroup V] (v : V) : ‖toConj v‖ = ‖v‖ := rfl
@[simp] theorem norm_ofConj [SeminormedAddCommGroup V] (v : Conjugate V) :
    ‖ofConj v‖ = ‖v‖ := rfl

instance instNormedSpaceReal [SeminormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (Conjugate V) :=
  ‹NormedSpace ℝ V›

instance instNormedSpaceComplex [SeminormedAddCommGroup V] [NormedSpace ℂ V] :
    NormedSpace ℂ (Conjugate V) where
  norm_smul_le c v := by
    rw [← norm_ofConj, ofConj_smul, norm_smul, Complex.norm_conj, norm_ofConj]

instance instCompleteSpace [SeminormedAddCommGroup V] [CompleteSpace V] :
    CompleteSpace (Conjugate V) :=
  ‹CompleteSpace V›

section TopologicalModule

variable [AddCommGroup V] [TopologicalSpace V]

/-- The identity map `V → Conjugate V` as a continuous conjugate-linear equivalence. -/
def toConjL [Module ℂ V] : V ≃L⋆[ℂ] Conjugate V where
  __ := toConj
  map_add' _ _ := rfl
  map_smul' := toConj_smul
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem coe_toConjL [Module ℂ V] : ⇑(toConjL : V ≃L⋆[ℂ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjL_symm [Module ℂ V] :
    ⇑(toConjL : V ≃L⋆[ℂ] Conjugate V).symm = ofConj := (rfl)

/-- The identity map `V → Conjugate V` as a continuous real-linear equivalence. -/
def toConjL' [Module ℝ V] : V ≃L[ℝ] Conjugate V where
  __ := toConj
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem coe_toConjL' [Module ℝ V] : ⇑(toConjL' : V ≃L[ℝ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjL'_symm [Module ℝ V] :
    ⇑(toConjL' : V ≃L[ℝ] Conjugate V).symm = ofConj := (rfl)

end TopologicalModule

end Conjugate

end TauCeti

open TauCeti TauCeti.Conjugate

namespace ContinuousLinearMap

section TopologicalModule

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

/-- The conjugate of a continuous complex-linear map: the same map, read between the conjugate
spaces. -/
def conjugate (f : V →L[ℂ] W) : Conjugate V →L[ℂ] Conjugate W where
  toFun v := toConj (f (ofConj v))
  map_add' v w := by simp
  map_smul' c v := by simp
  cont := f.continuous

@[simp] theorem conjugate_apply (f : V →L[ℂ] W) (v : Conjugate V) :
    f.conjugate v = toConj (f (ofConj v)) := (rfl)

@[simp] theorem conjugate_add [ContinuousAdd W] (f g : V →L[ℂ] W) :
    (f + g).conjugate = f.conjugate + g.conjugate :=
  (rfl)

@[simp] theorem conjugate_sub [IsTopologicalAddGroup W] (f g : V →L[ℂ] W) :
    (f - g).conjugate = f.conjugate - g.conjugate :=
  (rfl)

@[simp] theorem conjugate_id : (ContinuousLinearMap.id ℂ V).conjugate = .id ℂ _ := (rfl)

theorem conjugate_comp {U : Type*} [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    (g : W →L[ℂ] U) (f : V →L[ℂ] W) : (g.comp f).conjugate = g.conjugate.comp f.conjugate :=
  (rfl)

@[simp] theorem conjugate_zero : (0 : V →L[ℂ] W).conjugate = 0 := (rfl)

@[simp] theorem conjugate_neg [IsTopologicalAddGroup W] (f : V →L[ℂ] W) :
    (-f).conjugate = -f.conjugate :=
  (rfl)

/-- A scalar picks up a complex conjugate when the map is conjugated. -/
@[simp] theorem conjugate_smul [ContinuousConstSMul ℂ W] (c : ℂ) (f : V →L[ℂ] W) :
    (c • f).conjugate = conj c • f.conjugate := by
  ext v
  simp

theorem conjugate_injective :
    Function.Injective (conjugate : (V →L[ℂ] W) → Conjugate V →L[ℂ] Conjugate W) :=
  fun f g h ↦ ext fun v ↦ by simpa using congr($h (toConj v))

/-- Continuous conjugate-linear maps `V → W` are the continuous complex-linear maps
`V → Conjugate W`. -/
def toConjugate : (V →L⋆[ℂ] W) ≃ (V →L[ℂ] Conjugate W) where
  toFun f :=
    { toFun v := toConj (f v)
      map_add' v w := by simp
      map_smul' c v := by simp
      cont := continuous_toConj.comp f.continuous }
  invFun g :=
    { toFun v := ofConj (g v)
      map_add' v w := by simp
      map_smul' c v := by simp
      cont := continuous_ofConj.comp g.continuous }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toConjugate_apply (f : V →L⋆[ℂ] W) (v : V) : toConjugate f v = toConj (f v) :=
  (rfl)

@[simp] theorem toConjugate_symm_apply (g : V →L[ℂ] Conjugate W) (v : V) :
    toConjugate.symm g v = ofConj (g v) :=
  (rfl)

@[simp] theorem coe_toConjugate (f : V →L⋆[ℂ] W) :
    (toConjugate f : V →ₗ[ℂ] Conjugate W) = LinearMap.toConjugate (f : V →ₗ⋆[ℂ] W) :=
  LinearMap.ext fun v ↦ by simp

end TopologicalModule

section Normed

variable {V W : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]
  [SeminormedAddCommGroup W] [NormedSpace ℂ W]

/-- Conjugation preserves operator norms. -/
@[simp] theorem norm_conjugate (f : V →L[ℂ] W) : ‖f.conjugate‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun v ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
  · simpa using f.le_opNorm (ofConj v)
  · simpa using f.conjugate.le_opNorm (toConj v)

/-- Conjugation of continuous complex-linear maps is an isometry for the operator norms. -/
theorem isometry_conjugate : Isometry (conjugate : (V →L[ℂ] W) → Conjugate V →L[ℂ] Conjugate W) :=
  Isometry.of_dist_eq fun f g ↦ by rw [dist_eq_norm, dist_eq_norm, ← conjugate_sub,
    norm_conjugate]

theorem continuous_conjugate :
    Continuous (conjugate : (V →L[ℂ] W) → Conjugate V →L[ℂ] Conjugate W) :=
  isometry_conjugate.continuous

end Normed

end ContinuousLinearMap

namespace TauCeti.Conjugate

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

/-! ### Double conjugates and products -/

/-- Conjugating twice gives back the original space. -/
def doubleConjugateL : Conjugate (Conjugate V) ≃L[ℂ] V where
  toFun v := ofConj (ofConj v)
  invFun v := toConj (toConj v)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by simp
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem doubleConjugateL_apply (v : Conjugate (Conjugate V)) :
    doubleConjugateL v = ofConj (ofConj v) := (rfl)

@[simp] theorem doubleConjugateL_symm_apply (v : V) :
    (doubleConjugateL : Conjugate (Conjugate V) ≃L[ℂ] V).symm v = toConj (toConj v) := (rfl)

/-- Conjugating a map twice gives back the map, up to `doubleConjugateL`. -/
theorem _root_.ContinuousLinearMap.conjugate_conjugate (f : V →L[ℂ] W) :
    f.conjugate.conjugate = ((doubleConjugateL : Conjugate (Conjugate W) ≃L[ℂ] W).symm :
      W →L[ℂ] Conjugate (Conjugate W)) ∘L f ∘L
        (doubleConjugateL : Conjugate (Conjugate V) ≃L[ℂ] V) :=
  (rfl)

/-- The conjugate of a product is the product of the conjugates. -/
def prodL : Conjugate (V × W) ≃L[ℂ] Conjugate V × Conjugate W where
  toFun v := (toConj (ofConj v).1, toConj (ofConj v).2)
  invFun v := toConj (ofConj v.1, ofConj v.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by ext <;> simp
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem prodL_apply (v : Conjugate (V × W)) :
    prodL v = (toConj (ofConj v).1, toConj (ofConj v).2) := (rfl)

@[simp] theorem prodL_symm_apply (v : Conjugate V × Conjugate W) :
    (prodL : Conjugate (V × W) ≃L[ℂ] _).symm v = toConj (ofConj v.1, ofConj v.2) := (rfl)

end TauCeti.Conjugate

/-! ### Check: the conjugate of `ℂ` -/

namespace TauCeti.Conjugate

/-- Complex conjugation `ℂ → Conjugate ℂ` is complex-linear for the conjugated action. -/
def complexConjL : ℂ ≃L[ℂ] Conjugate ℂ where
  toFun z := toConj (conj z)
  invFun z := conj (ofConj z)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp
  map_smul' c z := by simp [smul_toConj]
  continuous_toFun := Complex.continuous_conj
  continuous_invFun := Complex.continuous_conj

@[simp] theorem complexConjL_apply (z : ℂ) : complexConjL z = toConj (conj z) := (rfl)

/-- The complex-linear isomorphism `complexConjL` agrees with the identity `ℂ → Conjugate ℂ`
exactly on the real line, the fixed set of complex conjugation. -/
theorem complexConjL_eq_toConj_iff (z : ℂ) : complexConjL z = toConj z ↔ ∃ r : ℝ, z = r := by
  rw [complexConjL_apply, toConj_inj, Complex.conj_eq_iff_real]

end TauCeti.Conjugate
