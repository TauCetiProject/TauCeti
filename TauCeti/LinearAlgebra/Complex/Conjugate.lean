/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
* `LinearMap.conjugateMap` and `LinearEquiv.conjugate`: functorial conjugation of complex-linear
  maps and equivalences. The map version is not called `LinearMap.conjugate`, which Mathlib uses
  for the conjugate of a projection by a group element (`Mathlib.RepresentationTheory.Maschke`).
* `TauCeti.Conjugate.doubleConjugateLinearEquiv`: the complex-linear identification of the
  double conjugate with the original module.
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

/-- The conjugate of a real vector space has the same real rank: its real structure is that of
`V`. -/
@[simp] theorem rank_real [AddCommGroup V] [Module ℝ V] :
    Module.rank ℝ (Conjugate V) = Module.rank ℝ V :=
  (rfl)

/-- The conjugate of a real vector space has the same real dimension. -/
@[simp] theorem finrank_real [AddCommGroup V] [Module ℝ V] :
    Module.finrank ℝ (Conjugate V) = Module.finrank ℝ V :=
  (rfl)

/-- The conjugate of a complex vector space has the same complex rank. -/
@[simp] theorem rank_complex [AddCommGroup V] [Module ℂ V] :
    Module.rank ℂ (Conjugate V) = Module.rank ℂ V :=
  (rank_eq_of_equiv_equiv (starRingEnd ℂ) (toConjₗ : V ≃ₗ⋆[ℂ] Conjugate V).toAddEquiv
    (Function.Involutive.bijective Complex.conj_conj) fun c v ↦ toConj_smul c v).symm

/-- The conjugate of a complex vector space has the same complex dimension. -/
@[simp] theorem finrank_complex [AddCommGroup V] [Module ℂ V] :
    Module.finrank ℂ (Conjugate V) = Module.finrank ℂ V :=
  congrArg Cardinal.toNat rank_complex

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

/-! ### Functoriality and double conjugation -/

namespace LinearMap

universe u v w

variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- A complex-linear map, read between conjugate modules. -/
def conjugateMap (f : V →ₗ[ℂ] W) : Conjugate V →ₗ[ℂ] Conjugate W where
  toFun v := toConj (f (ofConj v))
  map_add' v w := by simp
  map_smul' c v := by simp

@[simp] theorem conjugateMap_apply (f : V →ₗ[ℂ] W) (v : Conjugate V) :
    f.conjugateMap v = toConj (f (ofConj v)) := by rfl

@[simp] theorem conjugateMap_id : (LinearMap.id : V →ₗ[ℂ] V).conjugateMap = .id := by rfl

theorem conjugateMap_comp (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    (g.comp f).conjugateMap = g.conjugateMap.comp f.conjugateMap := by rfl

@[simp] theorem conjugateMap_zero : (0 : V →ₗ[ℂ] W).conjugateMap = 0 := by ext; rfl

@[simp] theorem conjugateMap_add (f g : V →ₗ[ℂ] W) :
    (f + g).conjugateMap = f.conjugateMap + g.conjugateMap := by ext; rfl

@[simp] theorem conjugateMap_neg (f : V →ₗ[ℂ] W) :
    (-f).conjugateMap = -f.conjugateMap := by ext; rfl

@[simp] theorem conjugateMap_sub (f g : V →ₗ[ℂ] W) :
    (f - g).conjugateMap = f.conjugateMap - g.conjugateMap := by ext; rfl

/-- Conjugating a scalar multiple of a map conjugates its scalar. -/
@[simp] theorem conjugateMap_smul (c : ℂ) (f : V →ₗ[ℂ] W) :
    (c • f).conjugateMap = starRingEnd ℂ c • f.conjugateMap := by
  ext v
  simp

theorem conjugateMap_injective :
    Function.Injective (conjugateMap : (V →ₗ[ℂ] W) → Conjugate V →ₗ[ℂ] Conjugate W) := by
  intro f g h
  ext v
  exact toConj.injective (congrArg (fun k => k (toConj v)) h)

end LinearMap

namespace LinearEquiv

universe u v

variable {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An equivalence of complex modules induces an equivalence of their conjugates. -/
def conjugate (e : V ≃ₗ[ℂ] W) : Conjugate V ≃ₗ[ℂ] Conjugate W where
  __ := e.toLinearMap.conjugateMap
  invFun w := toConj (e.symm (ofConj w))
  left_inv v := congrArg toConj (e.symm_apply_apply (ofConj v))
  right_inv w := congrArg toConj (e.apply_symm_apply (ofConj w))

@[simp] theorem conjugate_apply (e : V ≃ₗ[ℂ] W) (v : Conjugate V) :
    e.conjugate v = toConj (e (ofConj v)) := by rfl

@[simp] theorem conjugate_symm (e : V ≃ₗ[ℂ] W) : e.conjugate.symm = e.symm.conjugate := by rfl

@[simp] theorem conjugate_toLinearMap (e : V ≃ₗ[ℂ] W) :
    e.conjugate.toLinearMap = e.toLinearMap.conjugateMap := by rfl

@[simp] theorem conjugate_refl : (LinearEquiv.refl ℂ V).conjugate = .refl ℂ _ := by
  ext v
  rfl

@[simp] theorem conjugate_trans {U : Type*} [AddCommGroup U] [Module ℂ U]
    (e : V ≃ₗ[ℂ] W) (e' : W ≃ₗ[ℂ] U) :
    (e.trans e').conjugate = e.conjugate.trans e'.conjugate := by
  ext v
  rfl

end LinearEquiv

namespace TauCeti.Conjugate

universe u v

variable {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Conjugating a complex module twice gives back the original module. -/
def doubleConjugateLinearEquiv : Conjugate (Conjugate V) ≃ₗ[ℂ] V where
  toFun v := ofConj (ofConj v)
  invFun v := toConj (toConj v)
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := by rfl
  map_smul' c v := by simp

@[simp] theorem doubleConjugateLinearEquiv_apply (v : Conjugate (Conjugate V)) :
    doubleConjugateLinearEquiv v = ofConj (ofConj v) := by rfl

@[simp] theorem doubleConjugateLinearEquiv_symm_apply (v : V) :
    (doubleConjugateLinearEquiv : Conjugate (Conjugate V) ≃ₗ[ℂ] V).symm v =
      toConj (toConj v) := by rfl

/-- Double conjugation is natural in arbitrary complex-linear maps. -/
theorem doubleConjugateLinearEquiv_naturality (f : V →ₗ[ℂ] W) :
    doubleConjugateLinearEquiv.toLinearMap.comp f.conjugateMap.conjugateMap =
      f.comp doubleConjugateLinearEquiv.toLinearMap := by rfl

end TauCeti.Conjugate
