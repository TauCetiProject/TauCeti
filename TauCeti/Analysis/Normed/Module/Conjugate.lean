/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The complex conjugate of a complex vector space

For a complex module `V`, `TauCeti.Conjugate V` is a type synonym for `V` carrying the same
additive group, real module structure, topology and norm, and the conjugated complex action
`c • v = conj c • v` (`Module.compHom V (starRingEnd ℂ)`). The identity `V → Conjugate V` is then
a conjugate-linear equivalence (`TauCeti.Conjugate.toConjₗ`, `TauCeti.Conjugate.toConjL`), a
conjugate-linear map `V → W` becomes a complex-linear map `V → Conjugate W`
(`LinearMap.toConjugate`), conjugating twice gives back `V`, and conjugation commutes with
products.

A real subspace of `V` is read as a real subspace of `Conjugate V` (`Submodule.conjugate`); the
totally real subspaces of `V` and `Conjugate V` correspond under it
(`TauCeti.Analysis.Normed.Module.Conjugate.TotallyReal`).

## Design

Mathlib has no conjugate-module construction, only the semilinear-map conventions
(`V →ₗ⋆[ℂ] W`, `starRingEnd ℂ`). There are two natural carriers for the conjugate: a type synonym
with conjugated action, or keeping `V` as a real module and negating its complex structure
(as `SmoothAlmostComplexStructure.neg` does for almost complex structures). We use the type
synonym. It is a genuine `Module ℂ`, so every complex-linear construction (complex vector
bundles, direct sums, characteristic classes of complex bundles) applies to it unchanged, while
the negated-structure carrier would have to be re-equipped as a complex module before any of them
can be used. The real-module structure is copied from `V` rather than restricted from the
conjugated action, so that the real structures of `V` and `Conjugate V` agree definitionally; in
particular a complex vector bundle and its conjugate share their real trivializations.

The construction is specific to `ℂ`: a version over a general star ring would put two
non-definitionally-equal real module structures on `Conjugate V` when the scalars are `ℝ`.

## Main declarations

* `TauCeti.Conjugate`: the conjugate complex vector space, with `TauCeti.Conjugate.toConj` and
  `TauCeti.Conjugate.ofConj`.
* `TauCeti.Conjugate.toConjₗ`, `TauCeti.Conjugate.toConjL`: the identity as a conjugate-linear
  (continuous) equivalence; `TauCeti.Conjugate.toConjL'` is the identity as a real-linear one.
* `LinearMap.toConjugate`: a conjugate-linear map as a complex-linear map into the conjugate.
* `ContinuousLinearMap.conjugate`: the conjugate of a continuous complex-linear map, an isometry.
* `TauCeti.Conjugate.conjugateConjugateL`: `Conjugate (Conjugate V) ≃L[ℂ] V`.
* `TauCeti.Conjugate.prodL`: `Conjugate (V × W) ≃L[ℂ] Conjugate V × Conjugate W`.
* `Submodule.conjugate`: a real subspace of `V`, read as a real subspace of `Conjugate V`.
* `TauCeti.Conjugate.complexConjL`: complex conjugation is a complex-linear isomorphism
  `ℂ ≃L[ℂ] Conjugate ℂ`; it agrees with the identity exactly on the real line.
-/

public section

noncomputable section

open ComplexConjugate

namespace TauCeti

/-- The complex conjugate of a complex module `V`: the same additive group, real structure,
topology and norm, with complex scalars acting through complex conjugation. -/
@[expose] def Conjugate (V : Type*) : Type _ := V

namespace Conjugate

variable {V W : Type*}

/-- The identity map from `V` to its conjugate. -/
@[expose] def toConj : V ≃ Conjugate V := Equiv.refl _

/-- The identity map from the conjugate of `V` to `V`. -/
@[expose] def ofConj : Conjugate V ≃ V := Equiv.refl _

@[simp] theorem toConj_symm : (toConj : V ≃ Conjugate V).symm = ofConj := rfl
@[simp] theorem ofConj_symm : (ofConj : Conjugate V ≃ V).symm = toConj := rfl
@[simp] theorem toConj_ofConj (v : Conjugate V) : toConj (ofConj v) = v := rfl
@[simp] theorem ofConj_toConj (v : V) : ofConj (toConj v) = v := rfl
theorem toConj_inj {v w : V} : toConj v = toConj w ↔ v = w := Iff.rfl
theorem ofConj_inj {v w : Conjugate V} : ofConj v = ofConj w ↔ v = w := Iff.rfl

/-! ### Algebraic structure -/

instance instAddCommGroup [AddCommGroup V] : AddCommGroup (Conjugate V) := ‹AddCommGroup V›

section AddCommGroup

variable [AddCommGroup V]

@[simp] theorem toConj_zero : toConj (0 : V) = 0 := rfl
@[simp] theorem ofConj_zero : ofConj (0 : Conjugate V) = 0 := rfl
@[simp] theorem toConj_add (v w : V) : toConj (v + w) = toConj v + toConj w := rfl
@[simp] theorem ofConj_add (v w : Conjugate V) : ofConj (v + w) = ofConj v + ofConj w := rfl
@[simp] theorem toConj_neg (v : V) : toConj (-v) = -toConj v := rfl
@[simp] theorem ofConj_neg (v : Conjugate V) : ofConj (-v) = -ofConj v := rfl
@[simp] theorem toConj_sub (v w : V) : toConj (v - w) = toConj v - toConj w := rfl
@[simp] theorem ofConj_sub (v w : Conjugate V) : ofConj (v - w) = ofConj v - ofConj w := rfl

/-- The real structure of the conjugate is that of `V`. -/
instance instModuleReal [Module ℝ V] : Module ℝ (Conjugate V) := ‹Module ℝ V›

/-- Complex scalars act on the conjugate through complex conjugation. -/
instance instModuleComplex [Module ℂ V] : Module ℂ (Conjugate V) :=
  Module.compHom V (starRingEnd ℂ)

@[simp] theorem toConj_smul_real [Module ℝ V] (r : ℝ) (v : V) :
    toConj (r • v) = r • toConj v := rfl

@[simp] theorem ofConj_smul_real [Module ℝ V] (r : ℝ) (v : Conjugate V) :
    ofConj (r • v) = r • ofConj v := rfl

/-- The identity map `V → Conjugate V` as a real-linear equivalence. -/
def toConjₗ' [Module ℝ V] : V ≃ₗ[ℝ] Conjugate V where
  __ := toConj
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_toConjₗ' [Module ℝ V] : ⇑(toConjₗ' : V ≃ₗ[ℝ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjₗ'_symm [Module ℝ V] :
    ⇑(toConjₗ' : V ≃ₗ[ℝ] Conjugate V).symm = ofConj := (rfl)

variable [Module ℂ V]

theorem smul_toConj (c : ℂ) (v : V) : c • toConj v = toConj (conj c • v) := rfl

@[simp] theorem ofConj_smul (c : ℂ) (v : Conjugate V) : ofConj (c • v) = conj c • ofConj v := rfl

@[simp] theorem toConj_smul (c : ℂ) (v : V) : toConj (c • v) = conj c • toConj v := by
  simp [smul_toConj]

instance instIsScalarTower [Module ℝ V] [IsScalarTower ℝ ℂ V] :
    IsScalarTower ℝ ℂ (Conjugate V) where
  smul_assoc r c v := by
    apply ofConj.injective
    rw [ofConj_smul, ofConj_smul_real, ofConj_smul, ← smul_assoc]
    congr 1
    simp [Complex.real_smul]

/-- The identity map `V → Conjugate V` as a conjugate-linear equivalence. -/
def toConjₗ : V ≃ₗ⋆[ℂ] Conjugate V where
  __ := toConj
  map_add' _ _ := rfl
  map_smul' := toConj_smul

@[simp] theorem coe_toConjₗ : ⇑(toConjₗ : V ≃ₗ⋆[ℂ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjₗ_symm :
    ⇑(toConjₗ : V ≃ₗ⋆[ℂ] Conjugate V).symm = ofConj := (rfl)

end AddCommGroup

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

instance instNormedAddCommGroup [NormedAddCommGroup V] : NormedAddCommGroup (Conjugate V) :=
  ‹NormedAddCommGroup V›

@[simp] theorem norm_toConj [NormedAddCommGroup V] (v : V) : ‖toConj v‖ = ‖v‖ := rfl
@[simp] theorem norm_ofConj [NormedAddCommGroup V] (v : Conjugate V) : ‖ofConj v‖ = ‖v‖ := rfl

instance instNormedSpaceReal [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (Conjugate V) :=
  ‹NormedSpace ℝ V›

instance instNormedSpaceComplex [NormedAddCommGroup V] [NormedSpace ℂ V] :
    NormedSpace ℂ (Conjugate V) where
  norm_smul_le c v := by
    rw [← norm_ofConj, ofConj_smul, norm_smul, Complex.norm_conj, norm_ofConj]

instance instCompleteSpace [NormedAddCommGroup V] [CompleteSpace V] :
    CompleteSpace (Conjugate V) :=
  ‹CompleteSpace V›

instance instFiniteReal [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] :
    Module.Finite ℝ (Conjugate V) :=
  ‹Module.Finite ℝ V›

instance instFiniteComplex [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] :
    Module.Finite ℂ (Conjugate V) :=
  .of_surjective toConjₗ.toLinearMap toConjₗ.surjective

section TopologicalModule

variable [AddCommGroup V] [TopologicalSpace V]

/-- The identity map `V → Conjugate V` as a continuous conjugate-linear equivalence. -/
def toConjL [Module ℂ V] : V ≃L⋆[ℂ] Conjugate V where
  __ := toConjₗ
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem coe_toConjL [Module ℂ V] : ⇑(toConjL : V ≃L⋆[ℂ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjL_symm [Module ℂ V] :
    ⇑(toConjL : V ≃L⋆[ℂ] Conjugate V).symm = ofConj := (rfl)

/-- The identity map `V → Conjugate V` as a continuous real-linear equivalence. -/
def toConjL' [Module ℝ V] : V ≃L[ℝ] Conjugate V where
  __ := toConjₗ'
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem coe_toConjL' [Module ℝ V] : ⇑(toConjL' : V ≃L[ℝ] Conjugate V) = toConj := (rfl)
@[simp] theorem coe_toConjL'_symm [Module ℝ V] :
    ⇑(toConjL' : V ≃L[ℝ] Conjugate V).symm = ofConj := (rfl)

end TopologicalModule

end Conjugate

end TauCeti

open TauCeti TauCeti.Conjugate

/-! ### Conjugate-linear maps as complex-linear maps into the conjugate -/

namespace LinearMap

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A conjugate-linear map `V → W` as a complex-linear map `V → Conjugate W`. -/
def toConjugate (f : V →ₗ⋆[ℂ] W) : V →ₗ[ℂ] Conjugate W where
  toFun v := toConj (f v)
  map_add' v w := by simp
  map_smul' c v := by simp

@[simp] theorem toConjugate_apply (f : V →ₗ⋆[ℂ] W) (v : V) : f.toConjugate v = toConj (f v) :=
  (rfl)

end LinearMap

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

end TopologicalModule

section Normed

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

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
def conjugateConjugateL : Conjugate (Conjugate V) ≃L[ℂ] V where
  toFun v := ofConj (ofConj v)
  invFun v := toConj (toConj v)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by simp
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp] theorem conjugateConjugateL_apply (v : Conjugate (Conjugate V)) :
    conjugateConjugateL v = ofConj (ofConj v) := (rfl)

@[simp] theorem conjugateConjugateL_symm_apply (v : V) :
    (conjugateConjugateL : Conjugate (Conjugate V) ≃L[ℂ] V).symm v = toConj (toConj v) := (rfl)

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

/-! ### Real subspaces -/

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real subspace of `V`, read as a real subspace of `Conjugate V`. -/
@[expose] def conjugate (L : Submodule ℝ V) : Submodule ℝ (Conjugate V) :=
  L.map (toConjₗ' : V ≃ₗ[ℝ] Conjugate V).toLinearMap

@[simp] theorem mem_conjugate {L : Submodule ℝ V} {v : Conjugate V} :
    v ∈ L.conjugate ↔ ofConj v ∈ L := by
  simp [conjugate, Submodule.mem_map_equiv]

theorem toConj_mem_conjugate {L : Submodule ℝ V} {v : V} : toConj v ∈ L.conjugate ↔ v ∈ L :=
  mem_conjugate

end Submodule

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
