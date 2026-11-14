/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The complex conjugate of a complex vector space

For a complex module `V`, `TauCeti.Conjugate V` is a type synonym for `V` carrying the same
additive group and real module structure, and the conjugated complex action
`c • v = conj c • v` (`Module.compHom V (starRingEnd ℂ)`). The identity `V → Conjugate V` is then
a conjugate-linear equivalence (`TauCeti.Conjugate.toConjₗ`), and the conjugate-linear maps `V → W`
are the complex-linear maps `V → Conjugate W` (`LinearMap.toConjugate`).

A real subspace of `V` is read as a real subspace of `Conjugate V` (`Submodule.conjugate`); the
totally real subspaces of `V` and `Conjugate V` correspond under it
(`TauCeti.LinearAlgebra.TotallyReal.Conjugate`). The topology and norm of the conjugate are in
`TauCeti.Analysis.Normed.Module.Conjugate`.

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
* `TauCeti.Conjugate.toConjₗ`: the identity as a conjugate-linear equivalence;
  `TauCeti.Conjugate.toConjₗ'` is the identity as a real-linear one.
* `LinearMap.toConjugate`: conjugate-linear maps `V → W` are equivalent to complex-linear maps
  `V → Conjugate W`.
* `Submodule.conjugate`: a real subspace of `V`, read as a real subspace of `Conjugate V`.
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

instance instFiniteReal [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] :
    Module.Finite ℝ (Conjugate V) :=
  ‹Module.Finite ℝ V›

instance instFiniteComplex [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] :
    Module.Finite ℂ (Conjugate V) :=
  .of_surjective toConjₗ.toLinearMap toConjₗ.surjective

end Conjugate

end TauCeti

open TauCeti TauCeti.Conjugate

/-! ### Conjugate-linear maps as complex-linear maps into the conjugate -/

namespace LinearMap

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Conjugate-linear maps `V → W` are the complex-linear maps `V → Conjugate W`. -/
def toConjugate : (V →ₗ⋆[ℂ] W) ≃ (V →ₗ[ℂ] Conjugate W) where
  toFun f :=
    { toFun v := toConj (f v)
      map_add' v w := by simp
      map_smul' c v := by simp }
  invFun g :=
    { toFun v := ofConj (g v)
      map_add' v w := by simp
      map_smul' c v := by simp }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toConjugate_apply (f : V →ₗ⋆[ℂ] W) (v : V) : toConjugate f v = toConj (f v) :=
  (rfl)

@[simp] theorem toConjugate_symm_apply (g : V →ₗ[ℂ] Conjugate W) (v : V) :
    toConjugate.symm g v = ofConj (g v) :=
  (rfl)

end LinearMap

/-! ### Real subspaces -/

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real subspace of `V`, read as a real subspace of `Conjugate V`. -/
def conjugate (L : Submodule ℝ V) : Submodule ℝ (Conjugate V) :=
  L.map (toConjₗ' : V ≃ₗ[ℝ] Conjugate V).toLinearMap

@[simp] theorem mem_conjugate {L : Submodule ℝ V} {v : Conjugate V} :
    v ∈ L.conjugate ↔ ofConj v ∈ L := by
  simp [conjugate, Submodule.mem_map_equiv]

theorem toConj_mem_conjugate {L : Submodule ℝ V} {v : V} : toConj v ∈ L.conjugate ↔ v ∈ L :=
  mem_conjugate

/-- The conjugate of a real subspace is its image under the real-linear identity
`V ≃ₗ[ℝ] Conjugate V`. -/
theorem map_toConjₗ' (L : Submodule ℝ V) :
    L.map (toConjₗ' : V ≃ₗ[ℝ] Conjugate V).toLinearMap = L.conjugate :=
  (rfl)

end Submodule
