/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit

/-!
# Strict morphisms of A-infinity algebras

A strict morphism of uncurved nonunital `A∞` algebras is a degree-zero linear map that commutes
with every unsuspended operation.  It is the special case of an `A∞` morphism whose components
above arity one vanish.  Applying the map letterwise gives the corresponding morphism between
reduced tensor coalgebras; the deconcatenation naturality theorem records its coalgebra equation.

This file bundles strict morphisms and supplies their extensionality, identity, composition, and
strict-unit-preservation API.  The operation equations are stated both as multilinear-map
equalities and pointwise, so later constructions can use them without unfolding the structure.

## Main definitions

* `TauCeti.AInfinityStrictHom`: a strict morphism of nonunital `A∞` algebras.
* `TauCeti.AInfinityStrictHom.barMap`: its letterwise map on reduced tensor words.
* `TauCeti.AInfinityStrictUnitalHom`: a strict morphism preserving chosen strict units.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.4.
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
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {CC : AInfinityAlgebra R C}

/-- A strict morphism of uncurved nonunital `A∞` algebras.

The underlying linear map has degree zero and intertwines every operation `m n`.  In particular,
the arity-one equation says that it is a chain map, while the arity-two equation says that it
preserves the binary product. -/
structure AInfinityStrictHom (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    extends A →ₗ[R] B where
  /-- A strict morphism preserves the internal degree. -/
  map_mem' : ∀ {p : ℤ} {a : A}, a ∈ AA.grading.piece p →
    toLinearMap a ∈ BB.grading.piece p
  /-- A strict morphism commutes with every `A∞` operation. -/
  map_m' : ∀ n : ℕ,
    toLinearMap.compMultilinearMap (AA.m n) =
      (BB.m n).compLinearMap fun _ ↦ toLinearMap

namespace AInfinityStrictHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {CC : AInfinityAlgebra R C}

/-- Strict morphisms are determined by their underlying linear maps. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : AInfinityStrictHom AA BB → A →ₗ[R] B) := by
  rintro ⟨f, hf, hm⟩ ⟨g, hg, hn⟩ h
  cases h
  rfl

instance : FunLike (AInfinityStrictHom AA BB) A B where
  coe f := f.toLinearMap
  coe_injective _ _ h := toLinearMap_injective <| LinearMap.ext fun a ↦ congrFun h a

instance : LinearMapClass (AInfinityStrictHom AA BB) R A B where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : CoeOut (AInfinityStrictHom AA BB) (A →ₗ[R] B) := ⟨toLinearMap⟩

@[simp]
theorem coe_toLinearMap (f : AInfinityStrictHom AA BB) : ⇑f.toLinearMap = f := rfl

@[simp]
theorem coe_mk (f : A →ₗ[R] B) (hf hm) :
    ⇑(AInfinityStrictHom.mk f hf hm : AInfinityStrictHom AA BB) = f := rfl

/-- Two strict `A∞` morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : AInfinityStrictHom AA BB} (h : ∀ a, f a = g a) : f = g :=
  toLinearMap_injective <| LinearMap.ext h

/-- A strict morphism sends a homogeneous element to the piece of the same degree. -/
@[grind =>]
theorem map_mem (f : AInfinityStrictHom AA BB) {p : ℤ} {a : A}
    (ha : a ∈ AA.grading.piece p) : f a ∈ BB.grading.piece p :=
  f.map_mem' ha

/-- The underlying linear map of a strict morphism is homogeneous of degree zero. -/
theorem isHomogeneous (f : AInfinityStrictHom AA BB) :
    LinearMap.IsHomogeneous f.toLinearMap AA.grading.piece BB.grading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  simpa only [add_zero] using f.map_mem' ha

/-- A strict morphism commutes with the arity-`n` operation, as a multilinear-map equality. -/
theorem map_m_map (f : AInfinityStrictHom AA BB) (n : ℕ) :
    f.toLinearMap.compMultilinearMap (AA.m n) =
      (BB.m n).compLinearMap fun _ ↦ f.toLinearMap :=
  f.map_m' n

/-- A strict morphism commutes pointwise with the arity-`n` operation. -/
@[simp]
theorem map_m (f : AInfinityStrictHom AA BB) (n : ℕ) (x : Fin n → A) :
    f (AA.m n x) = BB.m n (fun i ↦ f (x i)) := by
  exact MultilinearMap.congr_fun (f.map_m_map n) x

/-- A strict morphism commutes with the unary differential. -/
theorem map_m_one (f : AInfinityStrictHom AA BB) (a : A) :
    f (AA.m 1 ![a]) = BB.m 1 ![f a] := by
  rw [f.map_m]
  congr 1
  funext i
  fin_cases i
  rfl

/-- A strict morphism preserves the binary product. -/
theorem map_m_two (f : AInfinityStrictHom AA BB) (a b : A) :
    f (AA.m 2 ![a, b]) = BB.m 2 ![f a, f b] := by
  rw [f.map_m]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The identity strict morphism of an `A∞` algebra. -/
protected def id (AA : AInfinityAlgebra R A) : AInfinityStrictHom AA AA where
  toLinearMap := LinearMap.id
  map_mem' ha := by simpa using ha
  map_m' n := by
    rw [LinearMap.id_compMultilinearMap, MultilinearMap.compLinearMap_id]

@[simp]
theorem id_toLinearMap (AA : AInfinityAlgebra R A) :
    (AInfinityStrictHom.id AA).toLinearMap = LinearMap.id := (rfl)

@[simp]
theorem coe_id (AA : AInfinityAlgebra R A) : ⇑(AInfinityStrictHom.id AA) = _root_.id :=
  (rfl)

@[simp]
theorem id_apply (AA : AInfinityAlgebra R A) (a : A) : AInfinityStrictHom.id AA a = a :=
  (rfl)

/-- Composition of strict morphisms of `A∞` algebras. -/
def comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    AInfinityStrictHom AA CC where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_m' n := by
    rw [LinearMap.comp_compMultilinearMap, f.map_m_map,
      LinearMap.compMultilinearMap_compLinearMap, g.map_m_map,
      MultilinearMap.compLinearMap_assoc]

@[simp]
theorem comp_toLinearMap (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := (rfl)

@[simp]
theorem coe_comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) (a : A) :
    g.comp f a = g (f a) := (rfl)

@[simp]
theorem comp_id (f : AInfinityStrictHom AA BB) :
    f.comp (AInfinityStrictHom.id AA) = f := by
  ext a
  simp only [comp_apply, id_apply]

@[simp]
theorem id_comp (f : AInfinityStrictHom AA BB) :
    (AInfinityStrictHom.id BB).comp f = f := by
  ext a
  simp only [comp_apply, id_apply]

/-- Composition of strict `A∞` morphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type uD} [AddCommGroup D] [Module R D]
    {DD : AInfinityAlgebra R D} (h : AInfinityStrictHom CC DD)
    (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext a
  simp only [comp_apply]

/-! ### The induced reduced-bar map -/

/-- The map on reduced bar constructions induced by applying a strict morphism to every letter. -/
noncomputable def barMap (f : AInfinityStrictHom AA BB) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  ReducedTensorWords.map (R := R) f.toLinearMap

/-- The defining equation for the reduced-bar map. -/
theorem barMap_def (f : AInfinityStrictHom AA BB) :
    f.barMap = ReducedTensorWords.map (R := R) f.toLinearMap := (rfl)

/-- On a pure tensor word, the reduced-bar map applies the strict morphism to every letter. -/
theorem barMap_of_tprod (f : AInfinityStrictHom AA BB) (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → A) :
    f.barMap (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) =
      ReducedTensorWords.of R B n (PiTensorProduct.tprod R fun i ↦ f (x i)) := by
  rw [barMap_def, ReducedTensorWords.map_of_tprod]
  congr 2

/-- The reduced-bar map preserves deconcatenation. -/
theorem deconcatenation_comp_barMap (f : AInfinityStrictHom AA BB) :
    ReducedTensorWords.deconcatenation R B ∘ₗ f.barMap =
      TensorProduct.map f.barMap f.barMap ∘ₗ ReducedTensorWords.deconcatenation R A := by
  simpa only [barMap_def] using
    ReducedTensorWords.deconcatenation_natural (R := R) f.toLinearMap

@[simp]
theorem barMap_id (AA : AInfinityAlgebra R A) :
    (AInfinityStrictHom.id AA).barMap = LinearMap.id := by
  rw [barMap_def, id_toLinearMap, ReducedTensorWords.map_id]

@[simp]
theorem barMap_comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (g.comp f).barMap = g.barMap ∘ₗ f.barMap := by
  rw [barMap_def, comp_toLinearMap, ReducedTensorWords.map_comp, barMap_def, barMap_def]

end AInfinityStrictHom

/-! ### Strictly unital strict morphisms -/

/-- A strictly unital strict morphism between `A∞` algebras with chosen strict units. -/
structure AInfinityStrictUnitalHom {eA : A} {eB : B}
    (hA : AA.StrictUnit eA) (hB : BB.StrictUnit eB)
    extends AInfinityStrictHom AA BB where
  /-- A strictly unital morphism preserves the chosen strict unit. -/
  map_unit' : toAInfinityStrictHom eA = eB

namespace AInfinityStrictUnitalHom

variable {eA : A} {eB : B} {eC : C}
  {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB} {hC : CC.StrictUnit eC}

/-- Strictly unital strict morphisms are determined by their underlying strict morphisms. -/
theorem toAInfinityStrictHom_injective : Function.Injective
    (toAInfinityStrictHom : AInfinityStrictUnitalHom hA hB → AInfinityStrictHom AA BB) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  cases h
  rfl

instance : FunLike (AInfinityStrictUnitalHom hA hB) A B where
  coe f := f.toAInfinityStrictHom
  coe_injective _f _g h := toAInfinityStrictHom_injective <|
    AInfinityStrictHom.ext fun a ↦ congrFun h a

instance : LinearMapClass (AInfinityStrictUnitalHom hA hB) R A B where
  map_add f := f.toAInfinityStrictHom.map_add
  map_smulₛₗ f := f.toAInfinityStrictHom.map_smul

instance : CoeOut (AInfinityStrictUnitalHom hA hB) (AInfinityStrictHom AA BB) :=
  ⟨toAInfinityStrictHom⟩

/-- Two strictly unital strict morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : AInfinityStrictUnitalHom hA hB} (h : ∀ a, f a = g a) : f = g := by
  exact toAInfinityStrictHom_injective (AInfinityStrictHom.ext h)

/-- A strictly unital strict morphism preserves the chosen unit. -/
@[simp]
theorem map_unit (f : AInfinityStrictUnitalHom hA hB) : f eA = eB :=
  f.map_unit'

/-- The identity strictly unital strict morphism. -/
protected def id (hA : AA.StrictUnit eA) : AInfinityStrictUnitalHom hA hA where
  toAInfinityStrictHom := AInfinityStrictHom.id AA
  map_unit' := rfl

@[simp]
theorem id_apply (hA : AA.StrictUnit eA) (a : A) : AInfinityStrictUnitalHom.id hA a = a :=
  (rfl)

/-- Composition of strictly unital strict morphisms. -/
def comp (g : AInfinityStrictUnitalHom hB hC) (f : AInfinityStrictUnitalHom hA hB) :
    AInfinityStrictUnitalHom hA hC where
  toAInfinityStrictHom := g.toAInfinityStrictHom.comp f.toAInfinityStrictHom
  map_unit' := by
    rw [AInfinityStrictHom.comp_apply, f.map_unit', g.map_unit']

@[simp]
theorem comp_apply (g : AInfinityStrictUnitalHom hB hC)
    (f : AInfinityStrictUnitalHom hA hB) (a : A) : g.comp f a = g (f a) :=
  (rfl)

@[simp]
theorem comp_id (f : AInfinityStrictUnitalHom hA hB) :
    f.comp (AInfinityStrictUnitalHom.id hA) = f := by
  ext a
  simp only [comp_apply, id_apply]

@[simp]
theorem id_comp (f : AInfinityStrictUnitalHom hA hB) :
    (AInfinityStrictUnitalHom.id hB).comp f = f := by
  ext a
  simp only [comp_apply, id_apply]

/-- Composition of strictly unital strict morphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type uD} [AddCommGroup D] [Module R D]
    {DD : AInfinityAlgebra R D} {eD : D} {hD : DD.StrictUnit eD}
    (k : AInfinityStrictUnitalHom hC hD) (g : AInfinityStrictUnitalHom hB hC)
    (f : AInfinityStrictUnitalHom hA hB) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext a
  simp only [comp_apply]

end AInfinityStrictUnitalHom

end TauCeti
