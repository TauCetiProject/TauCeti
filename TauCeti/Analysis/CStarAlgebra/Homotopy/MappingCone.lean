/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.Homotopy.Cone

/-!
# Mapping cones of C⋆-algebra `⋆`-homomorphisms

For a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` between non-unital complex C⋆-algebras, the mapping cone
`MappingCone φ` is the closed `⋆`-subalgebra `{(a, f) ∈ A × CStarCone B | φ a = f 1}` equipped with
the supremum product norm `‖(a, f)‖ = max ‖a‖ ‖f‖` (Blackadar, *Operator Algebras*, II.5.5.10).

## Main declarations

* `TauCeti.MappingCone`: the pullback C⋆-algebra `{(a, f) ∈ A × CStarCone B | φ a = evalOne f}`,
  with projections `TauCeti.MappingCone.fstHom` and `TauCeti.MappingCone.sndHom`.
* `TauCeti.MappingCone.lift` and `TauCeti.MappingCone.map`: pullback universal property and
  functoriality for commuting squares of `⋆`-homomorphisms.
* `TauCeti.MappingCone.inr`, `TauCeti.MappingCone.equivKerFstHom`,
  `TauCeti.MappingCone.fstHom_surjective`, and `TauCeti.MappingCone.quotientKerFstHomEquiv`:
  the mapping cone exact sequence `0 → CStarSuspension B → MappingCone φ → A → 0`.
* `TauCeti.MappingCone.sectionCLM` and `TauCeti.MappingCone.sectionCP`: the isometric completely
  positive linear section `a ↦ (a, t ↦ t • φ a)` of `fstHom φ`, together with
  `TauCeti.MappingCone.sectionCLM_map_mul_eq_iff` showing that it preserves multiplication on a pair
  `(a, b)` if and only if `φ (a * b) = 0`.
* `TauCeti.MappingCone.idEquivCone`, `TauCeti.MappingCone.isContractible_id`,
  `TauCeti.MappingCone.zeroEquivProd`, `TauCeti.MappingCone.not_isContractible_zero_of_nontrivial`,
  and `TauCeti.MappingCone.isEmpty_starHomotopyEquiv_id_zero_complex`: special cases `φ = id` and
  `φ = 0`.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.5.5.10–II.5.5.11.
-/

public section

noncomputable section

open Filter Set Topology unitInterval
open scoped CStarAlgebra ZeroAtInfty

namespace TauCeti

section Carrier

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Closed `⋆`-subalgebra `{(a, f) ∈ A × CStarCone B | φ a = evalOne f}` defining the mapping cone
of `φ : A →⋆ₙₐ[ℂ] B`. -/
def mappingConeSubalgebra (φ : A →⋆ₙₐ[ℂ] B) : NonUnitalStarSubalgebra ℂ (A × CStarCone B) where
  carrier := {p : A × CStarCone B | φ p.1 = CStarCone.evalOne p.2}
  mul_mem' {p q} (hp : φ p.1 = CStarCone.evalOne p.2) (hq : φ q.1 = CStarCone.evalOne q.2) := by
    rw [mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, hp, hq]
  zero_mem' := by simp
  add_mem' {p q} (hp : φ p.1 = CStarCone.evalOne p.2) (hq : φ q.1 = CStarCone.evalOne q.2) := by
    rw [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add, map_add, hp, hq]
  smul_mem' c {p} (hp : φ p.1 = CStarCone.evalOne p.2) := by
    rw [mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, hp]
  star_mem' {p} (hp : φ p.1 = CStarCone.evalOne p.2) := by
    rw [mem_ofPred_eq, Prod.fst_star, Prod.snd_star, map_star, map_star, hp]

@[simp]
theorem mem_mappingConeSubalgebra_iff (φ : A →⋆ₙₐ[ℂ] B) (p : A × CStarCone B) :
    p ∈ mappingConeSubalgebra φ ↔ φ p.1 = CStarCone.evalOne p.2 :=
  Iff.rfl

instance isClosed_mappingConeSubalgebra (φ : A →⋆ₙₐ[ℂ] B) :
    IsClosed (mappingConeSubalgebra φ : Set (A × CStarCone B)) :=
  isClosed_eq ((map_continuous φ).comp continuous_fst)
    ((map_continuous CStarCone.evalOne).comp continuous_snd)

/-- The mapping cone C⋆-algebra `{(a, f) ∈ A × CStarCone B | φ a = f 1}` of `φ : A →⋆ₙₐ[ℂ] B`. -/
def MappingCone (φ : A →⋆ₙₐ[ℂ] B) : Type _ :=
  mappingConeSubalgebra φ

instance (φ : A →⋆ₙₐ[ℂ] B) : NonUnitalCStarAlgebra (MappingCone φ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (mappingConeSubalgebra φ))

/-- Equip `MappingCone φ` with the spectral (C⋆-) partial order so that `A →CP MappingCone φ`
(`MappingCone.sectionCP`) typechecks. -/
instance (φ : A →⋆ₙₐ[ℂ] B) : PartialOrder (MappingCone φ) :=
  CStarAlgebra.spectralOrder _

/-- Equip `MappingCone φ` with the spectral `StarOrderedRing` structure matching its
`PartialOrder` so that `A →CP MappingCone φ` (`MappingCone.sectionCP`) typechecks. -/
instance (φ : A →⋆ₙₐ[ℂ] B) : StarOrderedRing (MappingCone φ) :=
  CStarAlgebra.spectralOrderedRing _

end Carrier

namespace MappingCone

section Basic

variable {A B C D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- First coordinate `x.fst : A` of an element `x : MappingCone φ`. -/
def fst {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : A := x.val.1

/-- Cone coordinate `x.snd : CStarCone B` of an element `x : MappingCone φ`. -/
def snd {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : CStarCone B := x.val.2

theorem eq_evalOne {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) :
    φ x.fst = CStarCone.evalOne x.snd := x.property

@[ext]
theorem ext {φ : A →⋆ₙₐ[ℂ] B} {x y : MappingCone φ} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) :
    x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- Construct an element of `MappingCone φ` from `(a, f)` satisfying `φ a = CStarCone.evalOne f`. -/
def mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B) (h : φ a = CStarCone.evalOne f) :
    MappingCone φ :=
  ⟨(a, f), h⟩

@[simp] theorem fst_mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B)
    (h : φ a = CStarCone.evalOne f) : (mk φ a f h).fst = a := (rfl)

@[simp] theorem snd_mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B)
    (h : φ a = CStarCone.evalOne f) : (mk φ a f h).snd = f := (rfl)

@[simp] theorem mk_fst_snd {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) :
    mk φ x.fst x.snd x.eq_evalOne = x := (rfl)

@[simp] theorem fst_zero {φ : A →⋆ₙₐ[ℂ] B} : (0 : MappingCone φ).fst = 0 := (rfl)
@[simp] theorem snd_zero {φ : A →⋆ₙₐ[ℂ] B} : (0 : MappingCone φ).snd = 0 := (rfl)
@[simp] theorem fst_add {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x + y).fst = x.fst + y.fst := (rfl)
@[simp] theorem snd_add {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x + y).snd = x.snd + y.snd := (rfl)
@[simp] theorem fst_neg {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (-x).fst = -x.fst := (rfl)
@[simp] theorem snd_neg {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (-x).snd = -x.snd := (rfl)
@[simp] theorem fst_sub {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x - y).fst = x.fst - y.fst := (rfl)
@[simp] theorem snd_sub {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x - y).snd = x.snd - y.snd := (rfl)
@[simp] theorem fst_mul {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x * y).fst = x.fst * y.fst := (rfl)
@[simp] theorem snd_mul {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) :
    (x * y).snd = x.snd * y.snd := (rfl)
@[simp] theorem fst_smul {φ : A →⋆ₙₐ[ℂ] B} (c : ℂ) (x : MappingCone φ) :
    (c • x).fst = c • x.fst := (rfl)
@[simp] theorem snd_smul {φ : A →⋆ₙₐ[ℂ] B} (c : ℂ) (x : MappingCone φ) :
    (c • x).snd = c • x.snd := (rfl)
@[simp] theorem fst_star {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (star x).fst = star x.fst := (rfl)
@[simp] theorem snd_star {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (star x).snd = star x.snd := (rfl)

instance {A B : Type*} [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) : NonUnitalCommCStarAlgebra (MappingCone φ) where
  mul_comm x y := ext (by rw [fst_mul, fst_mul, mul_comm]) (by rw [snd_mul, snd_mul, mul_comm])

theorem norm_eq {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : ‖x‖ = max ‖x.fst‖ ‖x.snd‖ :=
  Prod.norm_def x.val

theorem continuous_fst {φ : A →⋆ₙₐ[ℂ] B} : Continuous (fst (φ := φ)) :=
  _root_.continuous_fst.comp continuous_subtypeVal

theorem continuous_snd {φ : A →⋆ₙₐ[ℂ] B} : Continuous (snd (φ := φ)) :=
  _root_.continuous_snd.comp continuous_subtypeVal

/-- A map into `MappingCone φ` is continuous if and only if its two coordinate projections are
continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : A →⋆ₙₐ[ℂ] B}
    {g : X → MappingCone φ} :
    Continuous g ↔ Continuous (fun x => (g x).fst) ∧ Continuous (fun x => (g x).snd) :=
  (IsInducing.subtypeVal : IsInducing
    (fun y : MappingCone φ => ((y.fst, y.snd) : A × CStarCone B))).continuous_iff.trans
      continuous_prodMk

/-- First projection `MappingCone φ →⋆ₙₐ[ℂ] A` sending `(a, f)` to `a`. -/
def fstHom (φ : A →⋆ₙₐ[ℂ] B) : MappingCone φ →⋆ₙₐ[ℂ] A where
  toFun := fst
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem fstHom_apply (φ : A →⋆ₙₐ[ℂ] B) (x : MappingCone φ) : fstHom φ x = x.fst := (rfl)

/-- Second projection `MappingCone φ →⋆ₙₐ[ℂ] CStarCone B` sending `(a, f)` to `f`. -/
def sndHom (φ : A →⋆ₙₐ[ℂ] B) : MappingCone φ →⋆ₙₐ[ℂ] CStarCone B where
  toFun := snd
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem sndHom_apply (φ : A →⋆ₙₐ[ℂ] B) (x : MappingCone φ) : sndHom φ x = x.snd := (rfl)

@[simp]
theorem fst_sum {ι : Type*} {φ : A →⋆ₙₐ[ℂ] B} (s : Finset ι) (f : ι → MappingCone φ) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst :=
  map_sum (fstHom φ) f s

@[simp]
theorem snd_sum {ι : Type*} {φ : A →⋆ₙₐ[ℂ] B} (s : Finset ι) (f : ι → MappingCone φ) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd :=
  map_sum (sndHom φ) f s

theorem comp_fstHom_eq (φ : A →⋆ₙₐ[ℂ] B) :
    φ.comp (fstHom φ) = CStarCone.evalOne.comp (sndHom φ) :=
  NonUnitalStarAlgHom.ext eq_evalOne

/-- Pullback universal property of `MappingCone φ`: any pair of `⋆`-homomorphisms
`α : C →⋆ₙₐ[ℂ] A` and `β : C →⋆ₙₐ[ℂ] CStarCone B` satisfying `φ.comp α = evalOne.comp β` factors
uniquely through `MappingCone φ`. -/
def lift (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) : C →⋆ₙₐ[ℂ] MappingCone φ where
  toFun c := mk φ (α c) (β c) (DFunLike.congr_fun h c)
  map_smul' r c := ext (map_smul α r c) (map_smul β r c)
  map_zero' := ext (map_zero α) (map_zero β)
  map_add' c₁ c₂ := ext (map_add α c₁ c₂) (map_add β c₁ c₂)
  map_mul' c₁ c₂ := ext (map_mul α c₁ c₂) (map_mul β c₁ c₂)
  map_star' c := ext (map_star α c) (map_star β c)

@[simp]
theorem fst_lift_apply (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) (c : C) : (lift φ α β h c).fst = α c := (rfl)

@[simp]
theorem snd_lift_apply (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) (c : C) : (lift φ α β h c).snd = β c := (rfl)

@[simp]
theorem fstHom_comp_lift (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) : (fstHom φ).comp (lift φ α β h) = α := (rfl)

@[simp]
theorem sndHom_comp_lift (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) : (sndHom φ).comp (lift φ α β h) = β := (rfl)

theorem lift_unique {φ : A →⋆ₙₐ[ℂ] B} {α : C →⋆ₙₐ[ℂ] A} {β : C →⋆ₙₐ[ℂ] CStarCone B}
    (h : φ.comp α = CStarCone.evalOne.comp β) {ψ : C →⋆ₙₐ[ℂ] MappingCone φ}
    (h₁ : (fstHom φ).comp ψ = α) (h₂ : (sndHom φ).comp ψ = β) : ψ = lift φ α β h :=
  NonUnitalStarAlgHom.ext fun c => ext (DFunLike.congr_fun h₁ c) (DFunLike.congr_fun h₂ c)

/-- Functorial action on mapping cones induced by a commuting square `ψ.comp α = β.comp φ`. -/
def map (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ :=
  lift ψ (α.comp (fstHom φ)) ((CStarCone.map β).comp (sndHom φ)) <| by
    ext x
    have hx := DFunLike.congr_fun hsq x.fst
    simp only [NonUnitalStarAlgHom.comp_apply] at hx
    simpa [x.eq_evalOne] using hx

@[simp]
theorem fst_map_apply (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) (x : MappingCone φ) : (map φ ψ α β hsq x).fst = α x.fst := (rfl)

@[simp]
theorem snd_map_apply (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) (x : MappingCone φ) :
    (map φ ψ α β hsq x).snd = CStarCone.map β x.snd := (rfl)

@[simp]
theorem fstHom_comp_map (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) : (fstHom ψ).comp (map φ ψ α β hsq) = α.comp (fstHom φ) := (rfl)

@[simp]
theorem sndHom_comp_map (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) :
    (sndHom ψ).comp (map φ ψ α β hsq) = (CStarCone.map β).comp (sndHom φ) := (rfl)

@[simp]
theorem map_id (φ : A →⋆ₙₐ[ℂ] B)
    (hsq : φ.comp (.id ℂ A) = (NonUnitalStarAlgHom.id ℂ B).comp φ := by ext; rfl) :
    map φ φ (.id ℂ A) (.id ℂ B) hsq = .id ℂ (MappingCone φ) := by
  ext x : 1; refine ext rfl ?_; ext t; simp [NonUnitalStarAlgHom.coe_id]

theorem map_comp {E F : Type*} [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]
    {φ : A →⋆ₙₐ[ℂ] B} {ψ : C →⋆ₙₐ[ℂ] D} {χ : E →⋆ₙₐ[ℂ] F}
    {α₁ : A →⋆ₙₐ[ℂ] C} {β₁ : B →⋆ₙₐ[ℂ] D} {α₂ : C →⋆ₙₐ[ℂ] E} {β₂ : D →⋆ₙₐ[ℂ] F}
    (h₁ : ψ.comp α₁ = β₁.comp φ) (h₂ : χ.comp α₂ = β₂.comp ψ) :
    (map ψ χ α₂ β₂ h₂).comp (map φ ψ α₁ β₁ h₁) =
      map φ χ (α₂.comp α₁) (β₂.comp β₁) (by
        ext a
        have h₂a : χ (α₂ (α₁ a)) = β₂ (ψ (α₁ a)) := DFunLike.congr_fun h₂ (α₁ a)
        have h₁a : ψ (α₁ a) = β₁ (φ a) := DFunLike.congr_fun h₁ a
        simp [h₂a, h₁a]) := by
  ext x : 1; refine ext rfl ?_; ext t; simp

end Basic

section ExactSequence

variable {A B C D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- Isometric `⋆`-homomorphism `CStarSuspension B →⋆ₙₐ[ℂ] MappingCone φ` sending `g` to `(0, g)`. -/
def inr (φ : A →⋆ₙₐ[ℂ] B) : CStarSuspension B →⋆ₙₐ[ℂ] MappingCone φ :=
  lift φ 0 CStarSuspension.toCone (by ext g; simp)

@[simp] theorem fst_inr_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) : (inr φ g).fst = 0 := (rfl)

@[simp] theorem snd_inr_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) :
    (inr φ g).snd = CStarSuspension.toCone g := (rfl)

@[simp] theorem fstHom_comp_inr (φ : A →⋆ₙₐ[ℂ] B) : (fstHom φ).comp (inr φ) = 0 := (rfl)

theorem map_comp_inr {φ : A →⋆ₙₐ[ℂ] B} {ψ : C →⋆ₙₐ[ℂ] D} {α : A →⋆ₙₐ[ℂ] C} {β : B →⋆ₙₐ[ℂ] D}
    (hsq : ψ.comp α = β.comp φ) :
    (map φ ψ α β hsq).comp (inr φ) = (inr ψ).comp (CStarSuspension.map β) := by
  ext g : 1
  refine ext (by simp) ?_
  ext t
  by_cases ht1 : t = iocOne
  · subst ht1; simp
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      ht1 ((notMem_range_inclusion_Ioo_Ioc_iff t).mp hx)
    simp

theorem inr_injective (φ : A →⋆ₙₐ[ℂ] B) : Function.Injective (inr φ) := fun _ _ h =>
  CStarSuspension.toCone_injective (congrArg snd h)

theorem isometry_inr (φ : A →⋆ₙₐ[ℂ] B) : Isometry (inr φ) :=
  NonUnitalStarAlgHom.isometry (inr φ) (inr_injective φ)

theorem mem_range_inr_iff (φ : A →⋆ₙₐ[ℂ] B) {x : MappingCone φ} :
    x ∈ range (inr φ) ↔ fstHom φ x = 0 :=
  ⟨fun ⟨g, hg⟩ => hg ▸ fst_inr_apply φ g,
    fun hx =>
      ⟨CStarSuspension.ofConeEqZero x.snd
          (by rw [← x.eq_evalOne, ← fstHom_apply φ x, hx, map_zero]),
        ext (fstHom_apply φ x ▸ hx.symm) (CStarSuspension.toCone_ofConeEqZero _ _)⟩⟩

/-- `CStarSuspension B` is `⋆`-isomorphic to the kernel ideal of
`fstHom φ : MappingCone φ →⋆ₙₐ[ℂ] A`. -/
def equivKerFstHom (φ : A →⋆ₙₐ[ℂ] B) :
    CStarSuspension B ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (fstHom φ) where
  toFun g := ⟨inr φ g, by simp [TwoSidedIdeal.mem_ker]⟩
  invFun x := CStarSuspension.ofConeEqZero x.val.snd <| by
    have hx : x.val.fst = 0 := (TwoSidedIdeal.mem_ker (fstHom φ)).mp x.property
    rw [← x.val.eq_evalOne, hx, map_zero]
  left_inv g := CStarSuspension.ofConeEqZero_toCone g
  right_inv x := by
    have hx : x.val.fst = 0 := (TwoSidedIdeal.mem_ker (fstHom φ)).mp x.property
    exact Subtype.ext (ext hx.symm (CStarSuspension.toCone_ofConeEqZero _ _))
  map_mul' g₁ g₂ := Subtype.ext (map_mul (inr φ) g₁ g₂)
  map_add' g₁ g₂ := Subtype.ext (map_add (inr φ) g₁ g₂)
  map_smul' c g := Subtype.ext (map_smul (inr φ) c g)
  map_star' g := Subtype.ext (map_star (inr φ) g)

@[simp]
theorem coe_equivKerFstHom_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) :
    ((equivKerFstHom φ g : TwoSidedIdeal.ker (fstHom φ)) : MappingCone φ) = inr φ g := (rfl)

@[simp]
theorem equivKerFstHom_symm_apply (φ : A →⋆ₙₐ[ℂ] B) (x : TwoSidedIdeal.ker (fstHom φ))
    (t : Ioo (0 : ℝ) 1) :
    (equivKerFstHom φ).symm x t = (x : MappingCone φ).snd (Set.inclusion Ioo_subset_Ioc_self t) :=
  CStarSuspension.ofConeEqZero_apply x.val.snd _ t

/-- Linear section `a ↦ (a, t ↦ t • φ a)` of `fstHom φ`, bundled as a `ℂ`-linear map. -/
private def sectionLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →ₗ[ℂ] MappingCone φ where
  toFun a := mk φ a (CStarCone.linearPath (φ a)) (CStarCone.evalOne_linearPath (φ a)).symm
  map_add' a₁ a₂ := by refine ext rfl ?_; ext t; simp [map_add, smul_add]
  map_smul' c a := by
    refine ext rfl ?_; ext t
    simp only [RingHom.id_apply, snd_mk, snd_smul, smul_apply, CStarCone.linearPath_apply, map_smul,
      ← Complex.coe_smul]
    exact (smul_comm c ((t : ℝ) : ℂ) (φ a)).symm

@[simp] private theorem fst_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionLinearMap φ a).fst = a := (rfl)

@[simp] private theorem snd_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionLinearMap φ a).snd = CStarCone.linearPath (φ a) := (rfl)

@[simp]
private theorem norm_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    ‖sectionLinearMap φ a‖ = ‖a‖ := by
  rw [norm_eq, fst_sectionLinearMap_apply, snd_sectionLinearMap_apply, CStarCone.norm_linearPath]
  exact max_eq_left (NonUnitalStarAlgHom.norm_apply_le φ a)

private theorem isometry_sectionLinearMap (φ : A →⋆ₙₐ[ℂ] B) : Isometry (sectionLinearMap φ) :=
  AddMonoidHomClass.isometry_of_norm (sectionLinearMap φ) (norm_sectionLinearMap_apply φ)

/-- Isometric continuous linear section `a ↦ (a, t ↦ t • φ a)` of `fstHom φ`. -/
def sectionCLM (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] MappingCone φ :=
  { sectionLinearMap φ with cont := (isometry_sectionLinearMap φ).continuous }

@[simp] theorem fst_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) : (sectionCLM φ a).fst = a := (rfl)

@[simp] theorem snd_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionCLM φ a).snd = CStarCone.linearPath (φ a) := (rfl)

@[simp]
theorem norm_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) : ‖sectionCLM φ a‖ = ‖a‖ :=
  norm_sectionLinearMap_apply φ a

theorem isometry_sectionCLM (φ : A →⋆ₙₐ[ℂ] B) : Isometry (sectionCLM φ) :=
  isometry_sectionLinearMap φ

theorem norm_sectionCLM_le (φ : A →⋆ₙₐ[ℂ] B) : ‖sectionCLM φ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by simp

theorem fstHom_surjective (φ : A →⋆ₙₐ[ℂ] B) : Function.Surjective (fstHom φ) :=
  fun a => ⟨sectionCLM φ a, rfl⟩

/-- The quotient of `MappingCone φ` by `ker (fstHom φ)` is `⋆`-isomorphic to `A`. -/
def quotientKerFstHomEquiv (φ : A →⋆ₙₐ[ℂ] B) :
    MappingCone φ ⧸ TwoSidedIdeal.ker (fstHom φ) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective (fstHom_surjective φ)

@[simp]
theorem quotientKerFstHomEquiv_mk (φ : A →⋆ₙₐ[ℂ] B) (x : MappingCone φ) :
    quotientKerFstHomEquiv φ (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (fstHom φ)) x) =
      x.fst :=
  (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk (fstHom_surjective φ) x).trans
    (fstHom_apply φ x)

/-- Square-root cone element `t ↦ √t • b` in `CStarCone B`, used to factor `sectionLinearMap` on
positive matrices `star R * R`. -/
private def sqrtConePath (b : B) : CStarCone B :=
  CStarCone.ofPathEqZero
    ⟨fun t : I => Real.sqrt (t : ℝ) • b,
      (Real.continuous_sqrt.comp continuous_subtypeVal).smul continuous_const⟩
    (by simp)

@[simp]
private theorem sqrtConePath_apply (b : B) (t : Ioc (0 : ℝ) 1) :
    sqrtConePath b t = Real.sqrt (t : ℝ) • b := by simp [sqrtConePath]

private theorem evalOne_sqrtConePath (b : B) : CStarCone.evalOne (sqrtConePath b) = b := by simp

private theorem map_star_mul_self_sectionLinearMap (φ : A →⋆ₙₐ[ℂ] B) {k : ℕ}
    (R : CStarMatrix (Fin k) (Fin k) A) :
    (star R * R).map (sectionLinearMap φ) =
      star (CStarMatrix.ofMatrix fun l j =>
        mk φ (R l j) (sqrtConePath (φ (R l j))) (evalOne_sqrtConePath _).symm) *
      (CStarMatrix.ofMatrix fun l j =>
        mk φ (R l j) (sqrtConePath (φ (R l j))) (evalOne_sqrtConePath _).symm) := by
  set S : CStarMatrix (Fin k) (Fin k) (MappingCone φ) :=
    CStarMatrix.ofMatrix fun l j =>
      mk φ (R l j) (sqrtConePath (φ (R l j))) (evalOne_sqrtConePath _).symm
  have hS (l j : Fin k) :
      S l j = mk φ (R l j) (sqrtConePath (φ (R l j))) (evalOne_sqrtConePath _).symm := rfl
  ext i j : 1
  refine ext ?_ ?_
  · simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, hS]
  · ext t
    simp only [CStarMatrix.map_apply, snd_sectionLinearMap_apply, CStarCone.linearPath_apply,
      CStarMatrix.mul_apply, CStarMatrix.star_apply, hS, map_sum, map_mul, map_star, snd_sum,
      snd_mul, snd_star, snd_mk, ZeroAtInftyContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_apply, ZeroAtInftyContinuousMap.star_apply, sqrtConePath_apply,
      ← Complex.coe_smul, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
      ← Complex.ofReal_mul, Real.mul_self_sqrt t.property.1.le]

/-- Completely positive contractive (in fact, isometric) linear section
`a ↦ (a, t ↦ t • φ a)` of `fstHom φ : MappingCone φ →⋆ₙₐ[ℂ] A`. -/
def sectionCP [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) :
    A →CP MappingCone φ where
  toLinearMap := (sectionCLM φ).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have hmem := StarOrderedRing.nonneg_iff.mp hM
    have hmapₗ (X : CStarMatrix (Fin k) (Fin k) A) :
        X.map (sectionCLM φ).toLinearMap = CStarMatrix.mapₗ (sectionCLM φ).toLinearMap X := rfl
    rw [hmapₗ]
    refine AddSubmonoid.closure_induction (hx := hmem) ?_ ?_ ?_
    · rintro _ ⟨R, rfl⟩
      rw [← hmapₗ]
      exact (map_star_mul_self_sectionLinearMap φ R).symm ▸ star_mul_self_nonneg _
    · rw [map_zero]
    · intro X Y _ _ hX hY; rw [map_add]; exact add_nonneg hX hY

@[simp]
theorem toLinearMap_sectionCP [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) :
    (sectionCP φ).toLinearMap = (sectionCLM φ).toLinearMap := (rfl)

@[simp]
theorem sectionCP_apply [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    sectionCP φ a = sectionCLM φ a := (rfl)

/-- The linear section `a ↦ (a, t ↦ t • φ a)` preserves the product of `a` and `b` if and only if
`φ (a * b) = 0` (since `(t • φ a) * (t • φ b) = t² • φ (a * b)` differs from `t • φ (a * b)` at
`t = 1/2` whenever `φ (a * b) ≠ 0`). -/
theorem sectionCLM_map_mul_eq_iff (φ : A →⋆ₙₐ[ℂ] B) (a b : A) :
    sectionCLM φ (a * b) = sectionCLM φ a * sectionCLM φ b ↔ φ (a * b) = 0 := by
  constructor
  · intro h
    let half : Ioc (0 : ℝ) 1 := ⟨2⁻¹, by norm_num, by norm_num⟩
    have hhalf := DFunLike.congr_fun (congrArg snd h) half
    simp only [snd_sectionCLM_apply, snd_mul, mul_apply,
      CStarCone.linearPath_apply, half, ← Complex.coe_smul, smul_mul_smul_comm, ← map_mul] at hhalf
    have hsub : (((2⁻¹ : ℝ) : ℂ) - ((2⁻¹ : ℝ) : ℂ) * ((2⁻¹ : ℝ) : ℂ)) • φ (a * b) = 0 := by
      rw [sub_smul, hhalf, sub_self]
    have hquarter := congrArg ((4 : ℂ) • ·) hsub
    rw [smul_zero, smul_smul] at hquarter
    have h4 : (4 : ℂ) * (((2⁻¹ : ℝ) : ℂ) - ((2⁻¹ : ℝ) : ℂ) * ((2⁻¹ : ℝ) : ℂ)) = 1 := by
      push_cast; ring
    rwa [h4, one_smul] at hquarter
  · intro hab
    refine ext rfl ?_; ext t
    simp [hab, ← Complex.coe_smul, smul_mul_smul_comm, ← map_mul]

end ExactSequence

section SpecialCases

/-- The mapping cone of the identity `⋆`-homomorphism `.id ℂ A` is `⋆`-isomorphic to `CStarCone A`.
-/
def idEquivCone (A : Type*) [NonUnitalCStarAlgebra A] :
    MappingCone (.id ℂ A) ≃⋆ₐ[ℂ] CStarCone A where
  toFun := snd
  invFun f := mk (.id ℂ A) (CStarCone.evalOne f) f rfl
  left_inv x := ext x.eq_evalOne.symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem idEquivCone_apply {A : Type*} [NonUnitalCStarAlgebra A] (x : MappingCone (.id ℂ A)) :
    idEquivCone A x = x.snd := (rfl)

@[simp]
theorem fst_idEquivCone_symm_apply {A : Type*} [NonUnitalCStarAlgebra A] (f : CStarCone A) :
    ((idEquivCone A).symm f).fst = f iocOne :=
  CStarCone.evalOne_apply f

@[simp]
theorem snd_idEquivCone_symm_apply {A : Type*} [NonUnitalCStarAlgebra A] (f : CStarCone A) :
    ((idEquivCone A).symm f).snd = f := (rfl)

/-- `MappingCone (.id ℂ A)` is contractible. -/
theorem isContractible_id (A : Type*) [NonUnitalCStarAlgebra A] :
    IsContractibleCStarAlgebra (MappingCone (.id ℂ A)) :=
  (IsContractibleCStarAlgebra.iff_of_starAlgEquiv (idEquivCone A)).mpr (CStarCone.isContractible A)

/-- The mapping cone of `0 : A →⋆ₙₐ[ℂ] B` splits as `A × CStarSuspension B`. -/
def zeroEquivProd (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    MappingCone (0 : A →⋆ₙₐ[ℂ] B) ≃⋆ₐ[ℂ] A × CStarSuspension B where
  toFun x := (x.fst, CStarSuspension.ofConeEqZero x.snd x.eq_evalOne.symm)
  invFun p := mk 0 p.1 (CStarSuspension.toCone p.2) (by simp)
  left_inv x := ext rfl (CStarSuspension.toCone_ofConeEqZero _ _)
  right_inv p := Prod.ext rfl (CStarSuspension.ofConeEqZero_toCone p.2)
  map_mul' _ _ := Prod.ext rfl (by ext t; simp)
  map_add' _ _ := Prod.ext rfl (by ext t; simp)
  map_smul' _ _ := Prod.ext rfl (by ext t; simp)
  map_star' _ := Prod.ext rfl (by ext t; simp)

@[simp]
theorem zeroEquivProd_apply (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (x : MappingCone (0 : A →⋆ₙₐ[ℂ] B)) :
    zeroEquivProd A B x = (x.fst, CStarSuspension.ofConeEqZero x.snd x.eq_evalOne.symm) := (rfl)

@[simp]
theorem fst_zeroEquivProd_symm_apply (A B : Type*) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (p : A × CStarSuspension B) :
    ((zeroEquivProd A B).symm p).fst = p.1 := (rfl)

@[simp]
theorem snd_zeroEquivProd_symm_apply (A B : Type*) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (p : A × CStarSuspension B) :
    ((zeroEquivProd A B).symm p).snd = CStarSuspension.toCone p.2 := (rfl)

/-- When `A` is a nontrivial unital C⋆-algebra, `MappingCone (0 : A →⋆ₙₐ[ℂ] B)` contains the
nonzero projection `(1, 0)` and is therefore not contractible. -/
theorem not_isContractible_zero_of_nontrivial (A B : Type*) [CStarAlgebra A] [Nontrivial A]
    [NonUnitalCStarAlgebra B] :
    ¬IsContractibleCStarAlgebra (MappingCone (0 : A →⋆ₙₐ[ℂ] B)) := by
  intro h
  have hprod : IsContractibleCStarAlgebra (A × CStarSuspension B) :=
    (IsContractibleCStarAlgebra.iff_of_starAlgEquiv (zeroEquivProd A B)).mp h
  have hidem : IsIdempotentElem ((1 : A), (0 : CStarSuspension B)) := by
    rw [IsIdempotentElem]; ext <;> simp
  exact one_ne_zero (congrArg Prod.fst (hprod.eq_zero_of_isIdempotentElem hidem))

theorem not_isContractible_zero_complex :
    ¬IsContractibleCStarAlgebra (MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ)) :=
  not_isContractible_zero_of_nontrivial ℂ ℂ

/-- `MappingCone (.id ℂ ℂ)` and `MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ)` are not `⋆`-homotopy equivalent. -/
theorem isEmpty_starHomotopyEquiv_id_zero_complex :
    IsEmpty (StarHomotopyEquiv (MappingCone (.id ℂ ℂ)) (MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ))) :=
  ⟨fun e => not_isContractible_zero_complex
    ((IsContractibleCStarAlgebra.iff_of_starHomotopyEquiv e).mp (isContractible_id ℂ))⟩

end SpecialCases

end MappingCone

end TauCeti

end
