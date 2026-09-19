/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit

/-!
# Strict morphisms of A-infinity algebras

A strict morphism of uncurved nonunital `A∞` algebras is a degree-zero linear map that commutes
with every unsuspended operation.  It is the special case of an `A∞` morphism whose components
above arity one vanish.  Applying the map letterwise gives the corresponding morphism between
reduced tensor coalgebras; the deconcatenation naturality theorem records its coalgebra equation.

This file bundles strict morphisms and supplies their extensionality, identity, composition, and
strict-unit-preservation API.  It also identifies strict morphisms with general `A∞` morphisms
whose Taylor components above arity one vanish.  The operation equations are stated both as
multilinear-map equalities and pointwise, so later constructions can use them without unfolding
the structure.

## Main definitions

* `TauCeti.AInfinityStrictHom`: a strict morphism of nonunital `A∞` algebras.
* `TauCeti.AInfinityStrictHom.barMap`: its letterwise map on reduced tensor words.
* `TauCeti.AInfinityStrictHom.toAInfinityHom`: a strict morphism as an `A∞` morphism.
* `TauCeti.AInfinityHom.IsStrict`: the Taylor components above arity one vanish.
* `TauCeti.AInfinityStrictUnitalHom`: a strict morphism preserving chosen strict units.

## Main results

* `TauCeti.AInfinityHom.isStrict_iff_exists_eq_toAInfinityHom`: the strict `A∞` morphisms are
  exactly the images of strict morphisms.

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

/-- The underlying linear map of a strict morphism is homogeneous of degree zero for the gradings
shifted by `c`; the case `c = 1` is the suspended grading of the bar construction. -/
theorem isHomogeneous_shift (f : AInfinityStrictHom AA BB) (c : ℤ) :
    LinearMap.IsHomogeneous f.toLinearMap (AA.grading.shift c).piece
      (BB.grading.shift c).piece 0 := by
  have hA : (AA.grading.shift c).piece = Graded.shift AA.grading.piece c := by
    funext p
    rw [InternalGrading.shift_piece, Graded.shift_apply]
  have hB : (BB.grading.shift c).piece = Graded.shift BB.grading.piece c := by
    funext p
    rw [InternalGrading.shift_piece, Graded.shift_apply]
  rw [hA, hB]
  exact LinearMap.isHomogeneous_shift_iff.2 f.isHomogeneous

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

/-! ### The induced map on the reduced tensor coalgebra -/

/-- Apply a strict morphism to every letter of the reduced tensor coalgebra.  With the shifted
gradings and bar differentials, this is the induced map of reduced bar constructions. -/
noncomputable def barMap (f : AInfinityStrictHom AA BB) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  ReducedTensorWords.map (R := R) f.toLinearMap

/-- The defining equation for the reduced-bar map. -/
theorem barMap_def (f : AInfinityStrictHom AA BB) :
    f.barMap = ReducedTensorWords.map (R := R) f.toLinearMap := (rfl)

/-- On a pure tensor word, the induced map applies the strict morphism to every letter. -/
@[simp]
theorem barMap_of_tprod (f : AInfinityStrictHom AA BB) (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → A) :
    f.barMap (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) =
      ReducedTensorWords.of R B n (PiTensorProduct.tprod R fun i ↦ f (x i)) := by
  rw [barMap_def, ReducedTensorWords.map_of_tprod]
  congr 2

/-- The induced map of reduced bar constructions has degree zero for the shifted gradings. -/
theorem isHomogeneous_barMap (f : AInfinityStrictHom AA BB) :
    LinearMap.IsHomogeneous f.barMap
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
  rw [barMap_def]
  exact ReducedTensorWords.isHomogeneous_map _ _ (f.isHomogeneous_shift 1)

private theorem taylor_comp_barMap (f : AInfinityStrictHom AA BB) :
    BB.taylor ∘ₗ f.barMap = f.toLinearMap ∘ₗ AA.taylor := by
  apply ReducedTensorWords.linearMap_ext
  intro n x
  have hmaps :
      (BB.taylor ∘ₗ f.barMap) ∘ₗ ReducedTensorWords.of R A n =
        (f.toLinearMap ∘ₗ AA.taylor) ∘ₗ ReducedTensorWords.of R A n := by
    apply AA.grading.piTensorProduct_ext
    intro q
    let d : ℕ → ℤ := fun i ↦ if h : i < n.1 then (q ⟨i, h⟩).1 else 0
    let y : ℕ → A := fun i ↦ if h : i < n.1 then (q ⟨i, h⟩).2 else 0
    have hy : ∀ i < n.1, y i ∈ AA.grading.piece (d i) := by
      intro i hi
      simp only [y, d, hi, dite_true]
      exact (q ⟨i, hi⟩).2.property
    have hfy : ∀ i < n.1, f (y i) ∈ BB.grading.piece (d i) :=
      fun i hi ↦ f.map_mem (hy i hi)
    have hBB := (AInfinity.isSuspension_def _ _ _).1 BB.taylor_isSuspension n.1 n.2 d
      (fun i ↦ f (y i)) hfy
    have hAA := (AInfinity.isSuspension_def _ _ _).1 AA.taylor_isSuspension n.1 n.2 d y hy
    simp only [y, Fin.isLt, dite_true] at hBB hAA
    simp only [LinearMap.comp_apply, barMap_of_tprod]
    rw [hBB, hAA]
    rw [AInfinity.evalNat_suspend, AInfinity.evalNat_suspend, map_smul]
    simp only [MultilinearMap.evalNat_def]
    congr 1
    exact (f.map_m n.1 fun i ↦ y i).symm
  exact LinearMap.congr_fun hmaps (PiTensorProduct.tprod R x)

/-- The induced map of reduced bar constructions intertwines their bar differentials. -/
theorem barDifferential_comp_barMap (f : AInfinityStrictHom AA BB) :
    BB.barDifferential ∘ₗ f.barMap = f.barMap ∘ₗ AA.barDifferential := by
  rw [AA.barDifferential_def, BB.barDifferential_def]
  apply ReducedTensorWords.linearMap_ext
  intro n x
  simp only [LinearMap.comp_apply, barMap_of_tprod]
  rw [ReducedTensorWords.gradedCoderiv_of_tprod,
    ReducedTensorWords.gradedCoderiv_of_tprod, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [barMap_def, ReducedTensorWords.map_splice]
  have htwist := (f.isHomogeneous_shift 1).twistedTuple_map 1 x 0 p
  rw [← htwist]
  have htaylor := LinearMap.congr_fun f.taylor_comp_barMap
    (ReducedTensorWords.subword R x p d)
  simp only [LinearMap.comp_apply] at htaylor
  rw [barMap_def, ReducedTensorWords.map_subword] at htaylor
  simpa only [← coe_toLinearMap] using congrArg
    (ReducedTensorWords.splice R
      (InternalGrading.twistedTuple (BB.grading.shift 1) 1 (fun i ↦ f (x i)) 0 p)
      0 n.1 p d) htaylor

/-- The reduced-bar map preserves deconcatenation. -/
theorem deconcatenation_comp_barMap (f : AInfinityStrictHom AA BB) :
    ReducedTensorWords.deconcatenation R B ∘ₗ f.barMap =
      TensorProduct.map f.barMap f.barMap ∘ₗ ReducedTensorWords.deconcatenation R A := by
  simpa only [barMap_def] using
    ReducedTensorWords.deconcatenation_natural (R := R) f.toLinearMap

/-- The induced tensor-word map preserves identities. -/
@[simp]
theorem barMap_id (AA : AInfinityAlgebra R A) :
    (AInfinityStrictHom.id AA).barMap = LinearMap.id := by
  rw [barMap_def, id_toLinearMap, ReducedTensorWords.map_id]

/-- The induced tensor-word map preserves composition. -/
@[simp]
theorem barMap_comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (g.comp f).barMap = g.barMap ∘ₗ f.barMap := by
  rw [barMap_def, comp_toLinearMap, ReducedTensorWords.map_comp, barMap_def, barMap_def]

end AInfinityStrictHom

/-! ### Comparison with general `A∞` morphisms -/

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
theorem barMap_toAInfinityHom (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.barMap = f.barMap := (rfl)

/-- The Taylor components of a strict morphism vanish above arity one. -/
@[simp]
theorem taylor_toAInfinityHom (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.taylor = f.toLinearMap ∘ₗ ReducedTensorWords.letter R A := by
  rw [AInfinityHom.taylor_def, barMap_toAInfinityHom, barMap_def,
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
    (AInfinityStrictHom.id AA).toAInfinityHom = AInfinityHom.id AA := by
  apply AInfinityHom.barMap_injective
  rw [barMap_toAInfinityHom, AInfinityHom.barMap_id, barMap_id]

/-- Passing from strict morphisms to `A∞` morphisms preserves composition. -/
@[simp]
theorem toAInfinityHom_comp (g : AInfinityStrictHom BB CC) (f : AInfinityStrictHom AA BB) :
    (g.comp f).toAInfinityHom = g.toAInfinityHom.comp f.toAInfinityHom := by
  apply AInfinityHom.barMap_injective
  rw [barMap_toAInfinityHom, AInfinityHom.barMap_comp, barMap_toAInfinityHom,
    barMap_toAInfinityHom, barMap_comp]

end AInfinityStrictHom

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- An `A∞` morphism is *strict* when its Taylor components above arity one vanish, that is,
when its Taylor map only reads the letter component through the linear part. -/
def IsStrict (f : AInfinityHom AA BB) : Prop :=
  f.taylor = f.linearPart ∘ₗ ReducedTensorWords.letter R A

/-- The identity `A∞` morphism is strict. -/
@[simp]
theorem isStrict_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsStrict := by
  rw [IsStrict, taylor_id, linearPart_id, LinearMap.id_comp]

/-- A composite of strict `A∞` morphisms is strict. -/
@[simp]
theorem IsStrict.comp {CC : AInfinityAlgebra R C} {g : AInfinityHom BB CC}
    {f : AInfinityHom AA BB} (hg : g.IsStrict) (hf : f.IsStrict) : (g.comp f).IsStrict := by
  rw [IsStrict, taylor_comp, hg, LinearMap.comp_assoc, ← f.taylor_def, hf,
    linearPart_comp, LinearMap.comp_assoc]

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
theorem id_toAInfinityStrictHom (hA : AA.StrictUnit eA) :
    (AInfinityStrictUnitalHom.id hA).toAInfinityStrictHom = AInfinityStrictHom.id AA :=
  (rfl)

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
theorem comp_toAInfinityStrictHom (g : AInfinityStrictUnitalHom hB hC)
    (f : AInfinityStrictUnitalHom hA hB) :
    (g.comp f).toAInfinityStrictHom = g.toAInfinityStrictHom.comp f.toAInfinityStrictHom :=
  (rfl)

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
