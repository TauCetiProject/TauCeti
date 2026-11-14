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
* `TauCeti.MappingCone.inl`, `TauCeti.MappingCone.equivKerFstHom`,
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
* `TauCeti.MappingCone.evalZeroMap`, `TauCeti.MappingCone.evalOneMap`,
  `TauCeti.MappingCone.evalZeroHomotopyEquiv`, `TauCeti.MappingCone.evalOneHomotopyEquiv`, and
  `TauCeti.MappingCone.homotopyEquiv`: for a homotopy `Φ` from `φ₀` to `φ₁`, the endpoint
  evaluations out of `MappingCone Φ.toHom` are `⋆`-homotopy equivalences, so homotopic
  `⋆`-homomorphisms have `⋆`-homotopy-equivalent mapping cones.

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

instance isClosed_mappingConeSubalgebra (φ : A →⋆ₙₐ[ℂ] B) :
    IsClosed (mappingConeSubalgebra φ : Set (A × CStarCone B)) :=
  isClosed_eq ((map_continuous φ).comp continuous_fst)
    ((map_continuous CStarCone.evalOne).comp continuous_snd)

/-- The mapping cone C⋆-algebra `{(a, f) ∈ A × CStarCone B | φ a = f 1}` of `φ : A →⋆ₙₐ[ℂ] B`. -/
def MappingCone (φ : A →⋆ₙₐ[ℂ] B) : Type _ :=
  mappingConeSubalgebra φ

instance (φ : A →⋆ₙₐ[ℂ] B) : NonUnitalCStarAlgebra (MappingCone φ) :=
  inferInstanceAs (NonUnitalCStarAlgebra (mappingConeSubalgebra φ))

instance (φ : A →⋆ₙₐ[ℂ] B) : PartialOrder (MappingCone φ) :=
  CStarAlgebra.spectralOrder _

instance (φ : A →⋆ₙₐ[ℂ] B) : StarOrderedRing (MappingCone φ) :=
  CStarAlgebra.spectralOrderedRing _

end Carrier

namespace MappingCone

section Basic

variable {A B C D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- First coordinate `x.fst : A` of an element `x : MappingCone φ`. -/
def fst {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : A :=
  x.1.1

/-- Cone coordinate `x.snd : CStarCone B` of an element `x : MappingCone φ`. -/
def snd {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : CStarCone B :=
  x.1.2

theorem eq_evalOne {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) :
    φ x.fst = CStarCone.evalOne x.snd :=
  x.2

@[ext]
theorem ext {φ : A →⋆ₙₐ[ℂ] B} {x y : MappingCone φ} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) :
    x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- Construct an element of `MappingCone φ` from `(a, f)` satisfying `φ a = CStarCone.evalOne f`. -/
def mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B) (h : φ a = CStarCone.evalOne f) :
    MappingCone φ :=
  ⟨(a, f), h⟩

@[simp]
theorem fst_mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B) (h : φ a = CStarCone.evalOne f) :
    (mk φ a f h).fst = a :=
  (rfl)

@[simp]
theorem snd_mk (φ : A →⋆ₙₐ[ℂ] B) (a : A) (f : CStarCone B) (h : φ a = CStarCone.evalOne f) :
    (mk φ a f h).snd = f :=
  (rfl)

@[simp]
theorem mk_fst_snd {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) :
    mk φ x.fst x.snd x.eq_evalOne = x :=
  (rfl)

@[simp] theorem fst_zero {φ : A →⋆ₙₐ[ℂ] B} : (0 : MappingCone φ).fst = 0 := (rfl)
@[simp] theorem snd_zero {φ : A →⋆ₙₐ[ℂ] B} : (0 : MappingCone φ).snd = 0 := (rfl)

@[simp]
theorem fst_add {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x + y).fst = x.fst + y.fst :=
  (rfl)

@[simp]
theorem snd_add {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x + y).snd = x.snd + y.snd :=
  (rfl)

@[simp]
theorem fst_neg {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (-x).fst = -x.fst :=
  (rfl)

@[simp]
theorem snd_neg {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (-x).snd = -x.snd :=
  (rfl)

@[simp]
theorem fst_sub {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x - y).fst = x.fst - y.fst :=
  (rfl)

@[simp]
theorem snd_sub {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x - y).snd = x.snd - y.snd :=
  (rfl)

@[simp]
theorem fst_mul {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x * y).fst = x.fst * y.fst :=
  (rfl)

@[simp]
theorem snd_mul {φ : A →⋆ₙₐ[ℂ] B} (x y : MappingCone φ) : (x * y).snd = x.snd * y.snd :=
  (rfl)

@[simp]
theorem fst_smul {φ : A →⋆ₙₐ[ℂ] B} (c : ℂ) (x : MappingCone φ) : (c • x).fst = c • x.fst :=
  (rfl)

@[simp]
theorem snd_smul {φ : A →⋆ₙₐ[ℂ] B} (c : ℂ) (x : MappingCone φ) : (c • x).snd = c • x.snd :=
  (rfl)

@[simp]
theorem fst_star {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (star x).fst = star x.fst :=
  (rfl)

@[simp]
theorem snd_star {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : (star x).snd = star x.snd :=
  (rfl)

instance {A B : Type*} [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) : NonUnitalCommCStarAlgebra (MappingCone φ) where
  mul_comm x y := ext (by rw [fst_mul, fst_mul, mul_comm]) (by rw [snd_mul, snd_mul, mul_comm])

theorem norm_eq {φ : A →⋆ₙₐ[ℂ] B} (x : MappingCone φ) : ‖x‖ = max ‖x.fst‖ ‖x.snd‖ :=
  (rfl)

theorem continuous_fst {φ : A →⋆ₙₐ[ℂ] B} : Continuous (fst (φ := φ)) :=
  _root_.continuous_fst.comp continuous_subtype_val

theorem continuous_snd {φ : A →⋆ₙₐ[ℂ] B} : Continuous (snd (φ := φ)) :=
  _root_.continuous_snd.comp continuous_subtype_val

/-- A map into `MappingCone φ` is continuous if and only if its two coordinate projections are
continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : A →⋆ₙₐ[ℂ] B}
    {g : X → MappingCone φ} :
    Continuous g ↔ Continuous (fun x => (g x).fst) ∧ Continuous (fun x => (g x).snd) := by
  have hind : IsInducing (fun y : MappingCone φ => ((y.fst, y.snd) : A × CStarCone B)) :=
    IsInducing.subtypeVal
  exact hind.continuous_iff.trans continuous_prodMk

/-- First projection `MappingCone φ →⋆ₙₐ[ℂ] A` sending `(a, f)` to `a`. -/
def fstHom (φ : A →⋆ₙₐ[ℂ] B) : MappingCone φ →⋆ₙₐ[ℂ] A where
  toFun := fst
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem fstHom_apply (φ : A →⋆ₙₐ[ℂ] B) (x : MappingCone φ) : fstHom φ x = x.fst :=
  (rfl)

/-- Second projection `MappingCone φ →⋆ₙₐ[ℂ] CStarCone B` sending `(a, f)` to `f`. -/
def sndHom (φ : A →⋆ₙₐ[ℂ] B) : MappingCone φ →⋆ₙₐ[ℂ] CStarCone B where
  toFun := snd
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem sndHom_apply (φ : A →⋆ₙₐ[ℂ] B) (x : MappingCone φ) : sndHom φ x = x.snd :=
  (rfl)

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
    (h : φ.comp α = CStarCone.evalOne.comp β) (c : C) :
    (lift φ α β h c).fst = α c :=
  (rfl)

@[simp]
theorem snd_lift_apply (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) (c : C) :
    (lift φ α β h c).snd = β c :=
  (rfl)

@[simp]
theorem fstHom_comp_lift (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) :
    (fstHom φ).comp (lift φ α β h) = α :=
  (rfl)

@[simp]
theorem sndHom_comp_lift (φ : A →⋆ₙₐ[ℂ] B) (α : C →⋆ₙₐ[ℂ] A) (β : C →⋆ₙₐ[ℂ] CStarCone B)
    (h : φ.comp α = CStarCone.evalOne.comp β) :
    (sndHom φ).comp (lift φ α β h) = β :=
  (rfl)

theorem lift_unique {φ : A →⋆ₙₐ[ℂ] B} {α : C →⋆ₙₐ[ℂ] A} {β : C →⋆ₙₐ[ℂ] CStarCone B}
    (h : φ.comp α = CStarCone.evalOne.comp β) {ψ : C →⋆ₙₐ[ℂ] MappingCone φ}
    (h₁ : (fstHom φ).comp ψ = α) (h₂ : (sndHom φ).comp ψ = β) :
    ψ = lift φ α β h :=
  NonUnitalStarAlgHom.ext fun c =>
    ext (DFunLike.congr_fun h₁ c) (DFunLike.congr_fun h₂ c)

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
    (hsq : ψ.comp α = β.comp φ) (x : MappingCone φ) :
    (map φ ψ α β hsq x).fst = α x.fst :=
  (rfl)

@[simp]
theorem snd_map_apply (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) (α : A →⋆ₙₐ[ℂ] C) (β : B →⋆ₙₐ[ℂ] D)
    (hsq : ψ.comp α = β.comp φ) (x : MappingCone φ) :
    (map φ ψ α β hsq x).snd = CStarCone.map β x.snd :=
  (rfl)

@[simp]
theorem map_id (φ : A →⋆ₙₐ[ℂ] B)
    (hsq : φ.comp (.id ℂ A) = (NonUnitalStarAlgHom.id ℂ B).comp φ := by ext; rfl) :
    map φ φ (.id ℂ A) (.id ℂ B) hsq = .id ℂ (MappingCone φ) := by
  ext x : 1
  refine ext rfl ?_
  ext t
  simp [NonUnitalStarAlgHom.coe_id]

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
  ext x : 1
  refine ext rfl ?_
  ext t
  simp

end Basic

section ExactSequence

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Isometric `⋆`-homomorphism `CStarSuspension B →⋆ₙₐ[ℂ] MappingCone φ` sending `g` to `(0, g)`. -/
def inl (φ : A →⋆ₙₐ[ℂ] B) : CStarSuspension B →⋆ₙₐ[ℂ] MappingCone φ :=
  lift φ 0 CStarSuspension.toCone (by ext g; simp)

@[simp]
theorem fst_inl_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) : (inl φ g).fst = 0 :=
  (rfl)

@[simp]
theorem snd_inl_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) :
    (inl φ g).snd = CStarSuspension.toCone g :=
  (rfl)

@[simp]
theorem fstHom_comp_inl (φ : A →⋆ₙₐ[ℂ] B) : (fstHom φ).comp (inl φ) = 0 :=
  (rfl)

theorem inl_injective (φ : A →⋆ₙₐ[ℂ] B) : Function.Injective (inl φ) := fun _ _ h =>
  CStarSuspension.toCone_injective (congrArg snd h)

theorem isometry_inl (φ : A →⋆ₙₐ[ℂ] B) : Isometry (inl φ) :=
  NonUnitalStarAlgHom.isometry (inl φ) (inl_injective φ)

/-- `CStarSuspension B` is `⋆`-isomorphic to the kernel ideal of
`fstHom φ : MappingCone φ →⋆ₙₐ[ℂ] A`. -/
def equivKerFstHom (φ : A →⋆ₙₐ[ℂ] B) :
    CStarSuspension B ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (fstHom φ) where
  toFun g := ⟨inl φ g, by simp [TwoSidedIdeal.mem_ker]⟩
  invFun x := CStarSuspension.ofConeEqZero x.1.snd <| by
    have hx : x.1.fst = 0 := (TwoSidedIdeal.mem_ker (fstHom φ)).mp x.2
    rw [← x.1.eq_evalOne, hx, map_zero]
  left_inv g := CStarSuspension.ofConeEqZero_toCone g
  right_inv x := by
    have hx : x.1.fst = 0 := (TwoSidedIdeal.mem_ker (fstHom φ)).mp x.2
    exact Subtype.ext (ext hx.symm (CStarSuspension.toCone_ofConeEqZero _ _))
  map_mul' g₁ g₂ := Subtype.ext (map_mul (inl φ) g₁ g₂)
  map_add' g₁ g₂ := Subtype.ext (map_add (inl φ) g₁ g₂)
  map_smul' c g := Subtype.ext (map_smul (inl φ) c g)
  map_star' g := Subtype.ext (map_star (inl φ) g)

@[simp]
theorem coe_equivKerFstHom_apply (φ : A →⋆ₙₐ[ℂ] B) (g : CStarSuspension B) :
    ((equivKerFstHom φ g : TwoSidedIdeal.ker (fstHom φ)) : MappingCone φ) = inl φ g :=
  (rfl)

/-- Linear section `a ↦ (a, t ↦ t • φ a)` of `fstHom φ`, bundled as a `ℂ`-linear map. -/
def sectionLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →ₗ[ℂ] MappingCone φ where
  toFun a := mk φ a (CStarCone.linearPath (φ a)) (CStarCone.evalOne_linearPath (φ a)).symm
  map_add' a₁ a₂ := by
    refine ext rfl ?_
    ext t
    simp [map_add, smul_add]
  map_smul' c a := by
    refine ext rfl ?_
    ext t
    simp only [RingHom.id_apply, snd_mk, snd_smul, smul_apply, CStarCone.linearPath_apply, map_smul,
      ← Complex.coe_smul]
    exact (smul_comm c ((t : ℝ) : ℂ) (φ a)).symm

@[simp]
theorem fst_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionLinearMap φ a).fst = a :=
  (rfl)

@[simp]
theorem snd_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionLinearMap φ a).snd = CStarCone.linearPath (φ a) :=
  (rfl)

@[simp]
theorem norm_sectionLinearMap_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    ‖sectionLinearMap φ a‖ = ‖a‖ := by
  rw [norm_eq, fst_sectionLinearMap_apply, snd_sectionLinearMap_apply, CStarCone.norm_linearPath]
  exact max_eq_left (NonUnitalStarAlgHom.norm_apply_le φ a)

theorem isometry_sectionLinearMap (φ : A →⋆ₙₐ[ℂ] B) : Isometry (sectionLinearMap φ) :=
  AddMonoidHomClass.isometry_of_norm (sectionLinearMap φ) (norm_sectionLinearMap_apply φ)

/-- Isometric continuous linear section `a ↦ (a, t ↦ t • φ a)` of `fstHom φ`. -/
def sectionCLM (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] MappingCone φ :=
  { sectionLinearMap φ with
    cont := (isometry_sectionLinearMap φ).continuous }

@[simp]
theorem fst_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) : (sectionCLM φ a).fst = a :=
  (rfl)

@[simp]
theorem snd_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sectionCLM φ a).snd = CStarCone.linearPath (φ a) :=
  (rfl)

theorem fstHom_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) : fstHom φ (sectionCLM φ a) = a :=
  (rfl)

@[simp]
theorem norm_sectionCLM_apply (φ : A →⋆ₙₐ[ℂ] B) (a : A) : ‖sectionCLM φ a‖ = ‖a‖ :=
  norm_sectionLinearMap_apply φ a

theorem isometry_sectionCLM (φ : A →⋆ₙₐ[ℂ] B) : Isometry (sectionCLM φ) :=
  isometry_sectionLinearMap φ

theorem fstHom_surjective (φ : A →⋆ₙₐ[ℂ] B) : Function.Surjective (fstHom φ) :=
  fun a => ⟨sectionCLM φ a, rfl⟩

/-- The quotient of `MappingCone φ` by `ker (fstHom φ)` is `⋆`-isomorphic to `A`. -/
def quotientKerFstHomEquiv (φ : A →⋆ₙₐ[ℂ] B) :
    MappingCone φ ⧸ TwoSidedIdeal.ker (fstHom φ) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective (fstHom_surjective φ)

/-- Square-root cone element `t ↦ √t • b` in `CStarCone B`, used to factor `sectionLinearMap` on
positive matrices `star R * R`. -/
private def sqrtConePath (b : B) : CStarCone B :=
  CStarCone.ofPathEqZero
    ⟨fun t : I => Real.sqrt (t : ℝ) • b,
      (Real.continuous_sqrt.comp continuous_subtype_val).smul continuous_const⟩
    (by simp)

@[simp]
private theorem sqrtConePath_apply (b : B) (t : Ioc (0 : ℝ) 1) :
    sqrtConePath b t = Real.sqrt (t : ℝ) • b := by
  simp [sqrtConePath]

private theorem evalOne_sqrtConePath (b : B) : CStarCone.evalOne (sqrtConePath b) = b := by
  simp

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
      ← Complex.ofReal_mul, Real.mul_self_sqrt t.2.1.le]

/-- Completely positive contractive (in fact, isometric) linear section
`a ↦ (a, t ↦ t • φ a)` of `fstHom φ : MappingCone φ →⋆ₙₐ[ℂ] A`. -/
def sectionCP [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) :
    A →CP MappingCone φ where
  toLinearMap := sectionLinearMap φ
  map_cstarMatrix_nonneg' k M hM := by
    have hmem := StarOrderedRing.nonneg_iff.mp hM
    have hmapₗ (X : CStarMatrix (Fin k) (Fin k) A) :
        X.map (sectionLinearMap φ) = CStarMatrix.mapₗ (sectionLinearMap φ) X := rfl
    rw [hmapₗ]
    refine AddSubmonoid.closure_induction (hx := hmem) ?_ ?_ ?_
    · rintro _ ⟨R, rfl⟩
      rw [← hmapₗ, map_star_mul_self_sectionLinearMap φ R]
      exact star_mul_self_nonneg _
    · rw [map_zero]
    · intro X Y _ _ hX hY
      rw [map_add]
      exact add_nonneg hX hY

@[simp]
theorem sectionCP_apply [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    sectionCP φ a = sectionCLM φ a :=
  (rfl)

theorem fstHom_sectionCP_apply [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    fstHom φ (sectionCP φ a) = a :=
  (rfl)

theorem norm_sectionCP_apply [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    ‖sectionCP φ a‖ = ‖a‖ :=
  norm_sectionCLM_apply φ a

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
      push_cast
      ring
    rwa [h4, one_smul] at hquarter
  · intro hab
    refine ext rfl ?_
    ext t
    simp [hab, ← Complex.coe_smul, smul_mul_smul_comm, ← map_mul]

theorem sectionCP_map_mul_eq_iff [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₙₐ[ℂ] B)
    (a b : A) :
    sectionCP φ (a * b) = sectionCP φ a * sectionCP φ b ↔ φ (a * b) = 0 :=
  sectionCLM_map_mul_eq_iff φ a b

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
    idEquivCone A x = x.snd :=
  (rfl)

/-- `MappingCone (.id ℂ A)` is contractible. -/
theorem isContractible_id (A : Type*) [NonUnitalCStarAlgebra A] :
    IsContractibleCStarAlgebra (MappingCone (.id ℂ A)) :=
  (IsContractibleCStarAlgebra.iff_of_starAlgEquiv (idEquivCone A)).mpr (CStarCone.isContractible A)

/-- The mapping cone of `0 : A →⋆ₙₐ[ℂ] B` splits as `A × CStarSuspension B`. -/
def zeroEquivProd (A B : Type*) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] :
    MappingCone (0 : A →⋆ₙₐ[ℂ] B) ≃⋆ₐ[ℂ] A × CStarSuspension B where
  toFun x := (x.fst, CStarSuspension.ofConeEqZero x.snd x.eq_evalOne.symm)
  invFun p := mk 0 p.1 (CStarSuspension.toCone p.2) (by simp)
  left_inv x := ext rfl (CStarSuspension.toCone_ofConeEqZero _ _)
  right_inv p := Prod.ext rfl (CStarSuspension.ofConeEqZero_toCone p.2)
  map_mul' x y := Prod.ext rfl (by ext t; simp)
  map_add' x y := Prod.ext rfl (by ext t; simp)
  map_smul' c x := Prod.ext rfl (by ext t; simp)
  map_star' x := Prod.ext rfl (by ext t; simp)

/-- When `A` is a nontrivial unital C⋆-algebra, `MappingCone (0 : A →⋆ₙₐ[ℂ] B)` contains the
nonzero projection `(1, 0)` and is therefore not contractible. -/
theorem not_isContractible_zero_of_nontrivial (A B : Type*) [CStarAlgebra A] [Nontrivial A]
    [NonUnitalCStarAlgebra B] :
    ¬IsContractibleCStarAlgebra (MappingCone (0 : A →⋆ₙₐ[ℂ] B)) := by
  intro h
  have hprod : IsContractibleCStarAlgebra (A × CStarSuspension B) :=
    (IsContractibleCStarAlgebra.iff_of_starAlgEquiv (zeroEquivProd A B)).mp h
  have hidem : IsIdempotentElem ((1 : A), (0 : CStarSuspension B)) := by
    rw [IsIdempotentElem]
    ext <;> simp
  have hzero := hprod.eq_zero_of_isIdempotentElem hidem
  exact one_ne_zero (congrArg Prod.fst hzero)

theorem not_isContractible_zero_complex :
    ¬IsContractibleCStarAlgebra (MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ)) :=
  not_isContractible_zero_of_nontrivial ℂ ℂ

/-- `MappingCone (.id ℂ ℂ)` and `MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ)` are not `⋆`-homotopy equivalent. -/
theorem isEmpty_starHomotopyEquiv_id_zero_complex :
    IsEmpty (StarHomotopyEquiv (MappingCone (.id ℂ ℂ)) (MappingCone (0 : ℂ →⋆ₙₐ[ℂ] ℂ))) :=
  ⟨fun e =>
    not_isContractible_zero_complex
      ((IsContractibleCStarAlgebra.iff_of_starHomotopyEquiv e).mp (isContractible_id ℂ))⟩

end SpecialCases

section HomotopyInvariance

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {φ₀ φ₁ : A →⋆ₙₐ[ℂ] B}

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀` at `t = 0`. -/
def evalZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀ :=
  map Φ.toHom φ₀ (.id ℂ A) (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 0) <| by
    ext a
    simp

@[simp]
theorem fst_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalZeroMap Φ x).fst = x.fst :=
  (rfl)

@[simp]
theorem snd_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) :
    (evalZeroMap Φ x).snd s = x.snd s 0 := by
  simp [evalZeroMap]

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁` at `t = 1`. -/
def evalOneMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁ :=
  map Φ.toHom φ₁ (.id ℂ A) (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 1) <| by
    ext a
    simp

@[simp]
theorem fst_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalOneMap Φ x).fst = x.fst :=
  (rfl)

@[simp]
theorem snd_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) :
    (evalOneMap Φ x).snd s = x.snd s 1 := by
  simp [evalOneMap]

/-- Clamped rescaling `(s, t) ↦ min(s(1 + t), 1)` on `unitInterval × unitInterval`. -/
private def scaleClamp : C(I × I, I) where
  toFun p := ⟨min ((p.1 : ℝ) * (1 + (p.2 : ℝ))) 1,
    le_min (mul_nonneg p.1.2.1 (by linarith [p.2.2.1])) zero_le_one,
    min_le_right _ _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (((continuous_subtype_val.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp _root_.continuous_snd))).min
        continuous_const)

/-- Clamped shift `(s, t) ↦ max(s(1 + t) - 1, 0)` on `unitInterval × unitInterval`. -/
private def shiftClamp : C(I × I, I) where
  toFun p := ⟨max ((p.1 : ℝ) * (1 + (p.2 : ℝ)) - 1) 0,
    le_max_right _ _,
    max_le (by nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2]) zero_le_one⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((((continuous_subtype_val.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp _root_.continuous_snd))).sub
        continuous_const).max continuous_const)

private theorem scaleClamp_zero_left (t : I) : scaleClamp (0, t) = 0 := by
  ext
  simp [scaleClamp]

private theorem scaleClamp_one_left (t : I) : scaleClamp (1, t) = 1 := by
  ext
  have ht : (1 : ℝ) ≤ 1 + (t : ℝ) := le_add_of_nonneg_right t.2.1
  simp [scaleClamp, min_eq_right ht]

private theorem shiftClamp_one_left (t : I) : shiftClamp (1, t) = t := by
  ext
  simp [shiftClamp, t.2.1]

private theorem scaleClamp_zero_right (s : I) : scaleClamp (s, 0) = s := by
  ext
  simp [scaleClamp, min_eq_left s.2.2]

private theorem shiftClamp_of_le_one {p : I × I} (hp : (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1) :
    shiftClamp p = 0 := by
  ext
  simp [shiftClamp, max_eq_right (sub_nonpos.mpr hp)]

private theorem scaleClamp_of_ge_one {p : I × I} (hp : 1 ≤ (p.1 : ℝ) * (1 + (p.2 : ℝ))) :
    scaleClamp p = 1 := by
  ext
  simp [scaleClamp, min_eq_right hp]

/-- Two-parameter continuous family `(s, t) ↦ f(s(1 + t))` for `s(1 + t) ≤ 1` and
`Φ_a(s(1 + t) - 1)` for `s(1 + t) ≥ 1`, defining the homotopy inverse to `evalZeroMap`. -/
private def inclZeroSquare (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] C(I × I, B) where
  toFun x :=
    { toFun p :=
        if (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1 then
          CStarCone.toPath x.snd (scaleClamp p)
        else
          Φ.toHom x.fst (shiftClamp p)
      continuous_toFun := by
        refine Continuous.if_le
          ((CStarCone.toPath x.snd).comp scaleClamp).continuous
          ((Φ.toHom x.fst).comp shiftClamp).continuous
          ((continuous_subtype_val.comp _root_.continuous_fst).mul
            (continuous_const.add (continuous_subtype_val.comp _root_.continuous_snd)))
          continuous_const fun p hp => ?_
        have hs1 : scaleClamp p = 1 := by
          ext
          simp [scaleClamp, hp]
        have hs0 : shiftClamp p = 0 := by
          ext
          simp [shiftClamp, hp]
        rw [hs1, hs0, CStarCone.toPath_apply_one, ← x.eq_evalOne, Φ.eval_zero] }
  map_smul' c x := by
    ext p
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply]
    split_ifs <;> simp [map_smul]
  map_zero' := by
    ext p
    simp only [ContinuousMap.coe_mk, ContinuousMap.zero_apply]
    split_ifs <;> simp
  map_add' x y := by
    ext p
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
    split_ifs <;> simp [map_add]
  map_mul' x y := by
    ext p
    simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply]
    split_ifs <;> simp [map_mul]
  map_star' x := by
    ext p
    simp only [ContinuousMap.coe_mk, ContinuousMap.star_apply]
    split_ifs <;> simp [map_star]

private theorem inclZeroSquare_zero_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 0 = 0 := by
  ext t
  rw [ContinuousMap.curry_apply, ContinuousMap.zero_apply]
  simp [inclZeroSquare, scaleClamp_zero_left]

private theorem inclZeroSquare_one_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 1 = Φ.toHom x.fst := by
  ext t
  rw [ContinuousMap.curry_apply]
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  simp only [inclZeroSquare, NonUnitalStarAlgHom.coe_mk',
    NonUnitalAlgHom.coe_mk, ContinuousMap.coe_mk, h1, one_mul]
  split_ifs with ht
  · have ht_le : (t : ℝ) ≤ 0 := by linarith
    have ht0 : t = 0 := Subtype.ext (le_antisymm ht_le t.2.1)
    subst ht0
    rw [scaleClamp_one_left, CStarCone.toPath_apply_one, ← x.eq_evalOne, Φ.eval_zero]
  · rw [shiftClamp_one_left]

/-- Rescaling-and-concatenation `⋆`-homomorphism `MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom`
forming a `⋆`-homotopy inverse to `evalZeroMap Φ`. -/
def inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom :=
  lift Φ.toHom (fstHom φ₀)
    { toFun x := CStarCone.ofPathEqZero ((inclZeroSquare Φ x).curry) (inclZeroSquare_zero_left Φ x)
      map_smul' c x := by ext s t; simp [map_smul]
      map_zero' := by ext s t; simp
      map_add' x y := by ext s t; simp [map_add]
      map_mul' x y := by ext s t; simp [map_mul]
      map_star' x := by ext s t; simp [map_star] }
    (by
      ext x t
      simpa using DFunLike.congr_fun (inclZeroSquare_one_left Φ x).symm t)

@[simp]
theorem evalZeroMap_comp_inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroMap Φ).comp (inclZeroMap Φ) = .id ℂ (MappingCone φ₀) := by
  ext x : 1
  refine ext rfl ?_
  ext s
  have h0 : ((0 : I) : ℝ) = 0 := rfl
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq,
    snd_evalZeroMap_apply, inclZeroMap, snd_lift_apply, NonUnitalStarAlgHom.coe_mk',
    NonUnitalAlgHom.coe_mk, CStarCone.ofPathEqZero_apply, ContinuousMap.curry_apply,
    inclZeroSquare, ContinuousMap.coe_mk, coe_iocToUnitInterval, h0, add_zero, mul_one]
  split_ifs with hs
  · rw [scaleClamp_zero_right, CStarCone.toPath_apply_ioc]
  · exact False.elim (hs s.2.2)

/-- Linear homotopy `((r, s), t) ↦ ((1 - r) * scaleClamp (s, t) + r * s, ...)` from
`(scaleClamp (s, t), shiftClamp (s, t))` at `r = 0` to `(s, t)` at `r = 1`. -/
private def warpHomotopy : C((I × I) × I, I × I) where
  toFun q :=
    let p : I × I := (q.1.2, q.2)
    (⟨(1 - (q.1.1 : ℝ)) * (scaleClamp p : ℝ) + (q.1.1 : ℝ) * (p.1 : ℝ),
        add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.1.2.2) (scaleClamp p).2.1)
          (mul_nonneg q.1.1.2.1 p.1.2.1),
        by nlinarith [q.1.1.2.1, q.1.1.2.2, (scaleClamp p).2.2, p.1.2.2]⟩,
     ⟨(1 - (q.1.1 : ℝ)) * (shiftClamp p : ℝ) + (q.1.1 : ℝ) * (p.2 : ℝ),
        add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.1.2.2) (shiftClamp p).2.1)
          (mul_nonneg q.1.1.2.1 p.2.2.1),
        by nlinarith [q.1.1.2.1, q.1.1.2.2, (shiftClamp p).2.2, p.2.2.2]⟩)
  continuous_toFun := by
    have hr : Continuous fun q : (I × I) × I => (q.1.1 : ℝ) :=
      continuous_subtype_val.comp (_root_.continuous_fst.comp _root_.continuous_fst)
    have hp : Continuous fun q : (I × I) × I => ((q.1.2, q.2) : I × I) :=
      (_root_.continuous_snd.comp _root_.continuous_fst).prodMk _root_.continuous_snd
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact ((continuous_const.sub hr).mul
        (continuous_subtype_val.comp (scaleClamp.continuous.comp hp))).add
        (hr.mul (continuous_subtype_val.comp (_root_.continuous_fst.comp hp)))
    · exact ((continuous_const.sub hr).mul
        (continuous_subtype_val.comp (shiftClamp.continuous.comp hp))).add
        (hr.mul (continuous_subtype_val.comp (_root_.continuous_snd.comp hp)))

private theorem warpHomotopy_zero_left (s t : I) :
    warpHomotopy ((0, s), t) = (scaleClamp (s, t), shiftClamp (s, t)) := by
  ext <;> simp [warpHomotopy]

private theorem warpHomotopy_one_left (s t : I) : warpHomotopy ((1, s), t) = (s, t) := by
  ext <;> simp [warpHomotopy]

private theorem warpHomotopy_fst_zero (r t : I) : (warpHomotopy ((r, 0), t)).1 = 0 := by
  ext
  simp [warpHomotopy, scaleClamp_zero_left]

private theorem warpHomotopy_one_mid (r t : I) : warpHomotopy ((r, 1), t) = (1, t) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp [warpHomotopy, scaleClamp_one_left]
  · simp [warpHomotopy, shiftClamp_one_left]
    ring

/-- Continuous path `r ↦ G_r` in `CStarCone C(I, B)` deforming `(s, t) ↦ F(scaleClamp, shiftClamp)`
to `G`. -/
private def warpConePath (G : CStarCone C(I, B)) : C(I, CStarCone C(I, B)) where
  toFun r := CStarCone.ofPathEqZero
    (((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry) r)
    (by
      ext t
      simp [ContinuousMap.curry_apply, Function.uncurry, warpHomotopy_fst_zero])
  continuous_toFun := by
    rw [(CStarCone.isometry_toPath (A := C(I, B))).isUniformInducing.isInducing.continuous_iff]
    have hcomp : (CStarCone.toPath (A := C(I, B)) ∘ fun r => CStarCone.ofPathEqZero
        (((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry) r)
        (by
          ext t
          simp [ContinuousMap.curry_apply, Function.uncurry, warpHomotopy_fst_zero])) =
        (((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry := by
      ext r s t
      simp
    rw [hcomp]
    exact ((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry).continuous

private theorem evalOne_warpConePath (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (r : I) :
    CStarCone.evalOne (warpConePath y.snd r) = Φ.toHom y.fst := by
  ext t
  simp [warpConePath, Function.uncurry, warpHomotopy_one_mid, ← y.eq_evalOne]

private theorem inclZeroSquare_evalZeroMap_eq (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (p : I × I) :
    inclZeroSquare Φ (evalZeroMap Φ y) p =
      (CStarCone.toPath y.snd).uncurry (scaleClamp p, shiftClamp p) := by
  have hpath0 (u : I) : CStarCone.toPath (evalZeroMap Φ y).snd u = CStarCone.toPath y.snd u 0 := by
    by_cases hu0 : u = 0
    · subst hu0
      simp
    · obtain ⟨w, rfl⟩ := notMem_compl_iff.mp fun hw =>
        hu0 ((notMem_range_iocToUnitInterval_iff u).mp hw)
      simp
  simp only [inclZeroSquare, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk,
    ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
  split_ifs with hp
  · rw [shiftClamp_of_le_one hp, hpath0]
  · rw [scaleClamp_of_ge_one (not_le.mp hp).le, fst_evalZeroMap_apply, CStarCone.toPath_apply_one,
      ← y.eq_evalOne]

/-- Homotopy from `(inclZeroMap Φ).comp (evalZeroMap Φ)` to `.id ℂ (MappingCone Φ.toHom)`. -/
private def inclZeroCompEvalZeroHomotopy (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    NonUnitalStarAlgHom.Homotopy ((inclZeroMap Φ).comp (evalZeroMap Φ))
      (.id ℂ (MappingCone Φ.toHom)) where
  toHom :=
    { toFun y :=
        { toFun r := mk Φ.toHom y.fst (warpConePath y.snd r) (evalOne_warpConePath Φ y r).symm
          continuous_toFun :=
            continuous_iff.mpr ⟨continuous_const, (warpConePath y.snd).continuous⟩ }
      map_smul' c y := by
        ext r : 1
        refine ext rfl ?_
        ext s t
        simp [warpConePath, Function.uncurry, map_smul]
      map_zero' := by
        ext r : 1
        refine ext rfl ?_
        ext s t
        simp [warpConePath, Function.uncurry]
      map_add' x y := by
        ext r : 1
        refine ext rfl ?_
        ext s t
        simp [warpConePath, Function.uncurry, map_add]
      map_mul' x y := by
        ext r : 1
        refine ext rfl ?_
        ext s t
        simp [warpConePath, Function.uncurry, map_mul]
      map_star' y := by
        ext r : 1
        refine ext rfl ?_
        ext s t
        simp [warpConePath, Function.uncurry, map_star] }
  eval_zero y := by
    refine ext rfl ?_
    ext s t
    have heq := inclZeroSquare_evalZeroMap_eq Φ y (iocToUnitInterval s, t)
    simp only [ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] at heq
    simp [warpConePath, Function.uncurry, warpHomotopy_zero_left, inclZeroMap, heq]
  eval_one y := by
    refine ext rfl ?_
    ext s t
    simp [warpConePath, Function.uncurry, warpHomotopy_one_left]

/-- Endpoint evaluation at `0` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₀`. -/
def evalZeroHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₀) where
  toFun := evalZeroMap Φ
  invFun := inclZeroMap Φ
  left_inv := ⟨inclZeroCompEvalZeroHomotopy Φ⟩
  right_inv := by
    rw [evalZeroMap_comp_inclZeroMap]
    exact ⟨.refl _⟩

@[simp]
theorem evalZeroHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).toFun = evalZeroMap Φ :=
  (rfl)

@[simp]
theorem evalZeroHomotopyEquiv_invFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).invFun = inclZeroMap Φ :=
  (rfl)

/-- Time-reversal `⋆`-isomorphism `MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom` intertwining
`evalOneMap Φ` with `evalZeroMap Φ.symm`. -/
def symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (map Φ.toHom Φ.symm.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compNonUnitalStarAlgEquiv' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (map Φ.symm.toHom Φ.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compNonUnitalStarAlgEquiv' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (by
      ext x : 1
      refine ext rfl ?_
      ext s t
      simp)
    (by
      ext x : 1
      refine ext rfl ?_
      ext s t
      simp)

theorem evalOneMap_eq_evalZeroMap_comp_symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    evalOneMap Φ = (evalZeroMap Φ.symm).comp (symmEquiv Φ).toNonUnitalStarAlgHom := by
  ext x : 1
  refine ext rfl ?_
  ext s
  simp [symmEquiv]

/-- Endpoint evaluation at `1` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₁`. -/
def evalOneHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₁) := by
  let e := (StarHomotopyEquiv.ofStarAlgEquiv (symmEquiv Φ)).trans (evalZeroHomotopyEquiv Φ.symm)
  have htoFun : e.toFun = evalOneMap Φ := by
    simpa [e] using (evalOneMap_eq_evalZeroMap_comp_symmEquiv Φ).symm
  exact
    { toFun := evalOneMap Φ
      invFun := e.invFun
      left_inv := by rw [← htoFun]; exact e.left_inv
      right_inv := by rw [← htoFun]; exact e.right_inv }

@[simp]
theorem evalOneHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalOneHomotopyEquiv Φ).toFun = evalOneMap Φ :=
  (rfl)

/-- A homotopy `Φ` between `φ₀` and `φ₁` induces a `⋆`-homotopy equivalence between `MappingCone φ₀`
and `MappingCone φ₁`. -/
def homotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone φ₀) (MappingCone φ₁) :=
  (evalZeroHomotopyEquiv Φ).symm.trans (evalOneHomotopyEquiv Φ)

end HomotopyInvariance

end MappingCone

end TauCeti

namespace NonUnitalStarAlgHom.Homotopic

/-- Homotopic `⋆`-homomorphisms between C⋆-algebras have `⋆`-homotopy-equivalent mapping cones. -/
theorem nonempty_mappingCone_starHomotopyEquiv {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] {φ₀ φ₁ : A →⋆ₙₐ[ℂ] B} (h : φ₀.Homotopic φ₁) :
    Nonempty (TauCeti.StarHomotopyEquiv (TauCeti.MappingCone φ₀) (TauCeti.MappingCone φ₁)) :=
  h.elim fun Φ => ⟨TauCeti.MappingCone.homotopyEquiv Φ⟩

end NonUnitalStarAlgHom.Homotopic

end
