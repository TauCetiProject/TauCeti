/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom

/-!
# Morphisms of A-infinity algebras

A morphism of uncurved nonunital `A∞` algebras `A ⟶ B` is a degree-zero coalgebra morphism
`F : Tᶜ(sA) ⟶ Tᶜ(sB)` of reduced bar constructions which intertwines the bar differentials,
`b_B ∘ F = F ∘ b_A`.  A coalgebra morphism of reduced tensor coalgebras is determined by its
suspended Taylor components `Tᶜ(sA) ⟶ sB`, and every family of such components arises from
exactly one coalgebra morphism
(`TauCeti.ReducedTensorWords.coalgHomEquivTaylor`).  This coalgebra morphism is therefore the
stored datum, and the Taylor components are derived from it.

With this definition identities and composites are those of linear maps, so the category laws
hold on the nose.  The arity-one Taylor component is the linear part `f₁ : A ⟶ B`: it has degree
zero and is a chain map for the unary operations.  A strict morphism, whose components above
arity one vanish, induces the letterwise map of bar constructions; conversely an `A∞` morphism
whose Taylor components above arity one vanish comes from a unique strict morphism, since the
bar-differential equation then unsuspends to `f₁ ∘ mₙ = mₙ ∘ f₁^{⊗n}`.

## Main definitions

* `TauCeti.AInfinityHom`: a morphism of nonunital `A∞` algebras.
* `TauCeti.AInfinityHom.taylor`: its suspended Taylor components.
* `TauCeti.AInfinityHom.linearPart`: its arity-one component `f₁`.
* `TauCeti.AInfinityHom.id` and `TauCeti.AInfinityHom.comp`: identities and composition.
* `TauCeti.AInfinityStrictHom.toAInfinityHom`: a strict morphism as an `A∞` morphism.
* `TauCeti.AInfinityHom.IsStrict`: the Taylor components above arity one vanish.

## Main results

* `TauCeti.AInfinityHom.ext`: an `A∞` morphism is determined by its Taylor components.
* `TauCeti.AInfinityHom.comp_assoc`, `TauCeti.AInfinityHom.comp_id`, and
  `TauCeti.AInfinityHom.id_comp`: the category laws.
* `TauCeti.AInfinityHom.linearPart_m_one`: the linear part is a chain map.
* `TauCeti.AInfinityHom.linearPart_mem`: the linear part preserves degrees.
* `TauCeti.AInfinityHom.isStrict_iff_exists_eq_toAInfinityHom`: the strict `A∞` morphisms are
  exactly the images of strict morphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC uD

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- A morphism of uncurved nonunital `A∞` algebras, stored as the induced morphism of reduced
bar constructions: a coalgebra morphism of degree zero for the suspended gradings which
intertwines the bar differentials.  Its suspended Taylor components are `AInfinityHom.taylor`. -/
structure AInfinityHom (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The induced morphism of reduced bar constructions. -/
  barMap : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B
  /-- The bar map commutes with reduced deconcatenation. -/
  isCoalgHom_barMap : ReducedTensorWords.IsCoalgHom R barMap
  /-- The bar map has degree zero for the suspended gradings. -/
  isHomogeneous_barMap : LinearMap.IsHomogeneous barMap
    (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
    (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0
  /-- The bar map intertwines the bar differentials. -/
  barDifferential_comp_barMap : BB.barDifferential ∘ₗ barMap = barMap ∘ₗ AA.barDifferential

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The intertwining of the bar differentials, applied to an element. -/
@[simp]
theorem barDifferential_barMap (f : AInfinityHom AA BB) (z : ReducedTensorWords R A) :
    BB.barDifferential (f.barMap z) = f.barMap (AA.barDifferential z) :=
  LinearMap.congr_fun f.barDifferential_comp_barMap z

/-! ### Taylor components -/

/-- The suspended Taylor components of an `A∞` morphism: its bar map followed by the projection
onto single letters.  On words of length `n` this is the suspension of the component `fₙ`. -/
noncomputable def taylor (f : AInfinityHom AA BB) : ReducedTensorWords R A →ₗ[R] B :=
  ReducedTensorWords.letter R B ∘ₗ f.barMap

theorem taylor_def (f : AInfinityHom AA BB) :
    f.taylor = ReducedTensorWords.letter R B ∘ₗ f.barMap := (rfl)

/-- The bar map of an `A∞` morphism is the Taylor expansion of its Taylor components. -/
theorem barMap_eq_coalgHom (f : AInfinityHom AA BB) :
    f.barMap = ReducedTensorWords.coalgHom R f.taylor :=
  f.isCoalgHom_barMap.eq_coalgHom

/-- The Taylor components have degree zero for the suspended gradings. -/
theorem isHomogeneous_taylor (f : AInfinityHom AA BB) :
    LinearMap.IsHomogeneous f.taylor (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
  rw [taylor_def]
  simpa only [add_zero] using
    (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp f.isHomogeneous_barMap

/-- `A∞` morphisms are determined by their bar maps. -/
theorem barMap_injective :
    Function.Injective (barMap : AInfinityHom AA BB → _) := by
  rintro ⟨F, _, _, _⟩ ⟨G, _, _, _⟩ h
  cases h
  rfl

/-- `A∞` morphisms are determined by their Taylor components. -/
theorem taylor_injective : Function.Injective (taylor : AInfinityHom AA BB → _) := by
  intro f g h
  apply barMap_injective
  rw [f.barMap_eq_coalgHom, g.barMap_eq_coalgHom, h]

/-- Two `A∞` morphisms with the same Taylor components are equal. -/
@[ext]
theorem ext {f g : AInfinityHom AA BB} (h : f.taylor = g.taylor) : f = g :=
  taylor_injective h

/-! ### Identities and composition -/

/-- The identity `A∞` morphism, whose bar map is the identity. -/
protected def id (AA : AInfinityAlgebra R A) : AInfinityHom AA AA where
  barMap := LinearMap.id
  isCoalgHom_barMap := ReducedTensorWords.isCoalgHom_id A
  isHomogeneous_barMap := LinearMap.isHomogeneous_id _
  barDifferential_comp_barMap := by rw [LinearMap.comp_id, LinearMap.id_comp]

@[simp]
theorem id_barMap (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).barMap = LinearMap.id := (rfl)

/-- The Taylor components of the identity are the projection onto single letters. -/
@[simp]
theorem taylor_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).taylor = ReducedTensorWords.letter R A := by
  rw [taylor_def, id_barMap, LinearMap.comp_id]

/-- The composite of `A∞` morphisms, whose bar map is the composite of the bar maps. -/
def comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) : AInfinityHom AA CC where
  barMap := g.barMap ∘ₗ f.barMap
  isCoalgHom_barMap := g.isCoalgHom_barMap.comp f.isCoalgHom_barMap
  isHomogeneous_barMap := by
    simpa only [add_zero] using g.isHomogeneous_barMap.comp f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    rw [← LinearMap.comp_assoc, g.barDifferential_comp_barMap, LinearMap.comp_assoc,
      f.barDifferential_comp_barMap, LinearMap.comp_assoc]

@[simp]
theorem comp_barMap (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).barMap = g.barMap ∘ₗ f.barMap := (rfl)

/-- The Taylor components of a composite are those of the second morphism applied to the bar map
of the first. -/
@[simp]
theorem taylor_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).taylor = g.taylor ∘ₗ f.barMap := by
  rw [taylor_def, taylor_def, comp_barMap, LinearMap.comp_assoc]

/-- Composing an `A∞` morphism on the right with the identity leaves it unchanged. -/
@[simp]
theorem comp_id (f : AInfinityHom AA BB) : f.comp (AInfinityHom.id AA) = f :=
  barMap_injective <| by rw [comp_barMap, id_barMap, LinearMap.comp_id]

/-- Composing an `A∞` morphism on the left with the identity leaves it unchanged. -/
@[simp]
theorem id_comp (f : AInfinityHom AA BB) : (AInfinityHom.id BB).comp f = f :=
  barMap_injective <| by rw [comp_barMap, id_barMap, LinearMap.id_comp]

/-- Composition of `A∞` morphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type uD} [AddCommGroup D] [Module R D] {DD : AInfinityAlgebra R D}
    (h : AInfinityHom CC DD) (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  barMap_injective <| by simp only [comp_barMap, LinearMap.comp_assoc]

/-! ### The linear part -/

/-- The linear part `f₁` of an `A∞` morphism: its Taylor component on single letters. -/
noncomputable def linearPart (f : AInfinityHom AA BB) : A →ₗ[R] B :=
  f.taylor ∘ₗ ReducedTensorWords.ofLetter R A

@[simp]
theorem linearPart_apply (f : AInfinityHom AA BB) (a : A) :
    f.linearPart a = f.taylor (ReducedTensorWords.ofLetter R A a) := (rfl)

/-- The bar map sends a single letter to the single letter given by the linear part. -/
@[simp]
theorem barMap_ofLetter (f : AInfinityHom AA BB) (a : A) :
    f.barMap (ReducedTensorWords.ofLetter R A a) =
      ReducedTensorWords.ofLetter R B (f.linearPart a) := by
  rw [f.barMap_eq_coalgHom, ReducedTensorWords.coalgHom_ofLetter, linearPart_apply]

/-- The linear part of an `A∞` morphism preserves the internal degree. -/
theorem linearPart_mem (f : AInfinityHom AA BB) {p : ℤ} {a : A}
    (ha : a ∈ AA.grading.piece p) : f.linearPart a ∈ BB.grading.piece p := by
  have ha' : a ∈ (AA.grading.shift 1).piece (p - 1) := by
    rwa [InternalGrading.shift_piece, sub_add_cancel]
  have h := f.isHomogeneous_taylor.map_mem
    (ReducedTensorWords.ofLetter_mem_gradedPiece (AA.grading.shift 1) ha')
  rwa [add_zero, InternalGrading.shift_piece, sub_add_cancel] at h

/-- The linear part of an `A∞` morphism is homogeneous of degree zero. -/
theorem isHomogeneous_linearPart (f : AInfinityHom AA BB) :
    LinearMap.IsHomogeneous f.linearPart AA.grading.piece BB.grading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  rw [add_zero]
  exact f.linearPart_mem ha

/-- The linear part of an `A∞` morphism is a chain map for the unary operations: this is the
arity-one component of the bar-differential equation. -/
theorem linearPart_m_one (f : AInfinityHom AA BB) (a : A) :
    f.linearPart (AA.m 1 ![a]) = BB.m 1 ![f.linearPart a] := by
  have h := congrArg (ReducedTensorWords.letter R B)
    (f.barDifferential_barMap (ReducedTensorWords.ofLetter R A a))
  rw [barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, barMap_ofLetter,
    ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter] at h
  exact h.symm

@[simp]
theorem linearPart_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).linearPart = LinearMap.id := by
  ext a
  rw [linearPart_apply, taylor_id, ReducedTensorWords.letter_ofLetter, LinearMap.id_apply]

@[simp]
theorem linearPart_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).linearPart = g.linearPart ∘ₗ f.linearPart := by
  ext a
  rw [LinearMap.comp_apply, linearPart_apply, taylor_comp, LinearMap.comp_apply,
    barMap_ofLetter, linearPart_apply g]

end AInfinityHom

/-! ### Strict morphisms -/

namespace AInfinityStrictHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- A strict morphism as an `A∞` morphism: its bar map applies the morphism to every letter. -/
noncomputable def toAInfinityHom (f : AInfinityStrictHom AA BB) : AInfinityHom AA BB where
  barMap := f.barMap
  isCoalgHom_barMap := by
    rw [barMap_def]
    exact ReducedTensorWords.isCoalgHom_map f.toLinearMap
  isHomogeneous_barMap := f.isHomogeneous_barMap
  barDifferential_comp_barMap := f.barDifferential_comp_barMap

@[simp]
theorem toAInfinityHom_barMap (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.barMap = f.barMap := (rfl)

/-- The Taylor components of a strict morphism vanish above arity one. -/
@[simp]
theorem taylor_toAInfinityHom (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.taylor = f.toLinearMap ∘ₗ ReducedTensorWords.letter R A := by
  rw [AInfinityHom.taylor_def, toAInfinityHom_barMap, barMap_def,
    ReducedTensorWords.letter_comp_map]

/-- The linear part of a strict morphism is its underlying linear map. -/
@[simp]
theorem linearPart_toAInfinityHom (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.linearPart = f.toLinearMap := by
  ext a
  rw [AInfinityHom.linearPart_apply, taylor_toAInfinityHom, LinearMap.comp_apply,
    ReducedTensorWords.letter_ofLetter]

/-- Passing from strict morphisms to `A∞` morphisms is injective. -/
theorem toAInfinityHom_injective :
    Function.Injective (toAInfinityHom : AInfinityStrictHom AA BB → AInfinityHom AA BB) := by
  intro f g h
  apply toLinearMap_injective
  rw [← linearPart_toAInfinityHom, h, linearPart_toAInfinityHom]

/-- The identity strict morphism induces the identity `A∞` morphism. -/
@[simp]
theorem toAInfinityHom_id (AA : AInfinityAlgebra R A) :
    (AInfinityStrictHom.id AA).toAInfinityHom = AInfinityHom.id AA :=
  AInfinityHom.barMap_injective (barMap_id AA)

/-- Passing from strict morphisms to `A∞` morphisms preserves composition. -/
@[simp]
theorem toAInfinityHom_comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (g.comp f).toAInfinityHom = g.toAInfinityHom.comp f.toAInfinityHom :=
  AInfinityHom.barMap_injective (barMap_comp g f)

end AInfinityStrictHom

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- An `A∞` morphism is *strict* when its Taylor components above arity one vanish, that is,
when its Taylor map only reads the letter component through the linear part. -/
def IsStrict (f : AInfinityHom AA BB) : Prop :=
  f.taylor = f.linearPart ∘ₗ ReducedTensorWords.letter R A

/-- The strict morphism determined by the linear part of a strict `A∞` morphism. -/
noncomputable def IsStrict.toStrictHom {f : AInfinityHom AA BB} (hf : f.IsStrict) :
    AInfinityStrictHom AA BB where
  toLinearMap := f.linearPart
  map_mem' ha := f.linearPart_mem ha
  map_m' n := by
    -- Unsuspension cancels the common suspension sign on the two sides of the
    -- bar-differential equation because the linear part preserves degrees.
    have hbar : f.barMap = ReducedTensorWords.map (R := R) f.linearPart := by
      rw [f.barMap_eq_coalgHom, hf, ReducedTensorWords.coalgHom_comp_letter]
    -- Comparing letter components of the bar-differential equation.
    have htaylor : BB.taylor ∘ₗ ReducedTensorWords.map (R := R) f.linearPart =
        f.linearPart ∘ₗ AA.taylor := by
      have h := congrArg (ReducedTensorWords.letter R B ∘ₗ ·) f.barDifferential_comp_barMap
      simp only [← LinearMap.comp_assoc, AInfinityAlgebra.letter_comp_barDifferential] at h
      rw [hbar, ReducedTensorWords.letter_comp_map, LinearMap.comp_assoc,
        AInfinityAlgebra.letter_comp_barDifferential] at h
      exact h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [AA.m_zero, BB.m_zero, LinearMap.compMultilinearMap_zero,
        MultilinearMap.zero_compLinearMap]
    apply AA.grading.multilinearMap_ext
    intro d x hx
    let e : ℕ → ℤ := fun i ↦ if h : i < n then d ⟨i, h⟩ else 0
    let y : ℕ → A := fun i ↦ if h : i < n then x ⟨i, h⟩ else 0
    have hy : ∀ i < n, y i ∈ AA.grading.piece (e i) := by
      intro i hi
      simp only [y, e, hi, dite_true]
      exact hx ⟨i, hi⟩
    have hfy : ∀ i < n, f.linearPart (y i) ∈ BB.grading.piece (e i) :=
      fun i hi ↦ f.linearPart_mem (hy i hi)
    have hA := (AInfinity.isSuspension_def _ _ _).1 AA.taylor_isSuspension n hn e y hy
    have hB := (AInfinity.isSuspension_def _ _ _).1 BB.taylor_isSuspension n hn e
      (fun i ↦ f.linearPart (y i)) hfy
    have hxy : (fun i : Fin n ↦ y i) = x := by
      funext i
      simp only [y, i.isLt, dite_true]
    have h := LinearMap.congr_fun htaylor
      (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ y i))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ReducedTensorWords.map_of_tprod, hB, hA,
      AInfinity.evalNat_suspend, AInfinity.evalNat_suspend, map_smul] at h
    simp only [MultilinearMap.evalNat_def, hxy] at h
    have h' := congrArg (negOnePowCast R (MultilinearMap.suspExp n e) • ·) h
    simp only [smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul, one_smul] at h'
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, h'.symm]
    congr 1
    funext i
    simp only [y, i.isLt, dite_true]

@[simp]
theorem IsStrict.toStrictHom_toLinearMap {f : AInfinityHom AA BB} (hf : f.IsStrict) :
    hf.toStrictHom.toLinearMap = f.linearPart := (rfl)

@[simp]
theorem IsStrict.toAInfinityHom_toStrictHom {f : AInfinityHom AA BB} (hf : f.IsStrict) :
    hf.toStrictHom.toAInfinityHom = f := by
  ext1
  rw [AInfinityStrictHom.taylor_toAInfinityHom, IsStrict.toStrictHom_toLinearMap, hf]

/-- The `A∞` morphism induced by a strict morphism is strict. -/
@[simp]
theorem isStrict_toAInfinityHom (f : AInfinityStrictHom AA BB) : f.toAInfinityHom.IsStrict := by
  rw [IsStrict, AInfinityStrictHom.taylor_toAInfinityHom,
    AInfinityStrictHom.linearPart_toAInfinityHom]

/-- The strict `A∞` morphisms are exactly those induced by strict morphisms. -/
theorem isStrict_iff_exists_eq_toAInfinityHom (f : AInfinityHom AA BB) :
    f.IsStrict ↔ ∃ g : AInfinityStrictHom AA BB, g.toAInfinityHom = f := by
  refine ⟨fun hf ↦ ⟨hf.toStrictHom, hf.toAInfinityHom_toStrictHom⟩, ?_⟩
  rintro ⟨g, rfl⟩
  exact isStrict_toAInfinityHom g

end AInfinityHom

end TauCeti
