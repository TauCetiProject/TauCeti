/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

/-!
# Morphisms of nonunital differential graded algebras

A morphism of nonunital differential graded algebras is an `R`-linear multiplicative map which
preserves the internal degree and commutes with the differentials. This file bundles those maps
as `TauCeti.NonUnitalDGAlgHom` and supplies their identity and composition operations.

For unital DG algebras, forgetting preservation of the unit gives such a morphism between the
underlying nonunital DG algebras. The forgetful operation preserves identities and composition,
so constructions formulated at the nonunital level apply directly to unital DG algebras.

## Main definitions

* `TauCeti.NonUnitalDGAlgHom`: a morphism of nonunital DG algebras.
* `TauCeti.NonUnitalDGAlgHom.id` and `TauCeti.NonUnitalDGAlgHom.comp`: identity and composition.
* `TauCeti.DGAlgHom.toNonUnital`: forget that a DG algebra morphism preserves units.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA uB uC uD

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

/-- A morphism of nonunital differential graded algebras: an `R`-linear multiplicative map which
preserves the internal degree and commutes with the differentials. -/
structure NonUnitalDGAlgHom (hA : IsNonUnitalDGAlgebra 𝒜 dA)
    (hB : IsNonUnitalDGAlgebra ℬ dB) extends A →ₙₐ[R] B where
  /-- A nonunital DG algebra morphism preserves the internal degree. -/
  map_mem' : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → toNonUnitalAlgHom a ∈ ℬ p
  /-- A nonunital DG algebra morphism commutes with the differentials. -/
  map_d' (a : A) : dB (toNonUnitalAlgHom a) = toNonUnitalAlgHom (dA a)

namespace NonUnitalDGAlgHom

variable {hA : IsNonUnitalDGAlgebra 𝒜 dA} {hB : IsNonUnitalDGAlgebra ℬ dB}
  {hC : IsNonUnitalDGAlgebra 𝒞 dC}

/-- Two nonunital DG algebra morphisms are equal if their underlying nonunital algebra
homomorphisms are equal. -/
theorem toNonUnitalAlgHom_injective :
    Function.Injective
      (toNonUnitalAlgHom : NonUnitalDGAlgHom hA hB → A →ₙₐ[R] B) := by
  rintro ⟨f, hf, hd⟩ ⟨g, hg, he⟩ h
  cases h
  rfl

instance : FunLike (NonUnitalDGAlgHom hA hB) A B where
  coe f := f.toNonUnitalAlgHom
  coe_injective _ _ h :=
    toNonUnitalAlgHom_injective <| NonUnitalAlgHom.ext fun a ↦ congrFun h a

instance : GradedFunLike (NonUnitalDGAlgHom hA hB) 𝒜 ℬ where
  map_mem f := f.map_mem'

instance : NonUnitalAlgHomClass (NonUnitalDGAlgHom hA hB) R A B where
  map_add f := f.toNonUnitalAlgHom.map_add
  map_zero f := f.toNonUnitalAlgHom.map_zero
  map_mul f := f.toNonUnitalAlgHom.map_mul
  map_smulₛₗ f := f.toNonUnitalAlgHom.map_smul

instance : CoeOut (NonUnitalDGAlgHom hA hB) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

@[simp]
theorem coe_toNonUnitalAlgHom (f : NonUnitalDGAlgHom hA hB) :
    ⇑f.toNonUnitalAlgHom = f := rfl

@[simp]
theorem coe_mk (f : A →ₙₐ[R] B) (hf hd) :
    ⇑(NonUnitalDGAlgHom.mk f hf hd : NonUnitalDGAlgHom hA hB) = f := rfl

/-- Two nonunital DG algebra morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : NonUnitalDGAlgHom hA hB} (h : ∀ a, f a = g a) : f = g :=
  toNonUnitalAlgHom_injective <| NonUnitalAlgHom.ext h

/-- A nonunital DG algebra morphism sends a homogeneous element to the piece of the same degree. -/
theorem map_mem (f : NonUnitalDGAlgHom hA hB) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    f a ∈ ℬ p :=
  f.map_mem' ha

/-- A nonunital DG algebra morphism commutes with the differentials. -/
@[simp]
theorem map_d (f : NonUnitalDGAlgHom hA hB) (a : A) : dB (f a) = f (dA a) :=
  f.map_d' a

/-- The identity morphism of a nonunital differential graded algebra. -/
protected def id (hA : IsNonUnitalDGAlgebra 𝒜 dA) : NonUnitalDGAlgHom hA hA where
  toNonUnitalAlgHom := NonUnitalAlgHom.id R A
  map_mem' ha := by simpa using ha
  map_d' _ := rfl

@[simp]
theorem id_toNonUnitalAlgHom (hA : IsNonUnitalDGAlgebra 𝒜 dA) :
    (NonUnitalDGAlgHom.id hA).toNonUnitalAlgHom = NonUnitalAlgHom.id R A := (rfl)

@[simp]
theorem coe_id (hA : IsNonUnitalDGAlgebra 𝒜 dA) :
    ⇑(NonUnitalDGAlgHom.id hA) = _root_.id := (rfl)

@[simp]
theorem id_apply (hA : IsNonUnitalDGAlgebra 𝒜 dA) (a : A) :
    NonUnitalDGAlgHom.id hA a = a :=
  congrFun (coe_id hA) a

/-- Composition of morphisms of nonunital differential graded algebras. -/
def comp (g : NonUnitalDGAlgHom hB hC) (f : NonUnitalDGAlgHom hA hB) :
    NonUnitalDGAlgHom hA hC where
  toNonUnitalAlgHom := g.toNonUnitalAlgHom.comp f.toNonUnitalAlgHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_d' a :=
    (g.map_d' (f.toNonUnitalAlgHom a)).trans
      (congrArg g.toNonUnitalAlgHom (f.map_d' a))

@[simp]
theorem comp_toNonUnitalAlgHom (g : NonUnitalDGAlgHom hB hC)
    (f : NonUnitalDGAlgHom hA hB) :
    (g.comp f).toNonUnitalAlgHom =
      g.toNonUnitalAlgHom.comp f.toNonUnitalAlgHom := (rfl)

@[simp]
theorem coe_comp (g : NonUnitalDGAlgHom hB hC) (f : NonUnitalDGAlgHom hA hB) :
    ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : NonUnitalDGAlgHom hB hC) (f : NonUnitalDGAlgHom hA hB) (a : A) :
    g.comp f a = g (f a) :=
  congrFun (coe_comp g f) a

@[simp]
theorem comp_id (f : NonUnitalDGAlgHom hA hB) :
    f.comp (NonUnitalDGAlgHom.id hA) = f := by
  ext a
  simp only [comp_apply, id_apply]

@[simp]
theorem id_comp (f : NonUnitalDGAlgHom hA hB) :
    (NonUnitalDGAlgHom.id hB).comp f = f := by
  ext a
  simp only [comp_apply, id_apply]

/-- Composition of nonunital DG algebra morphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type uD}
    [NonUnitalRing D] [Module R D] [IsScalarTower R D D] [SMulCommClass R D D]
    {𝒟 : ℤ → Submodule R D} [SetLike.GradedMul 𝒟] [DirectSum.Decomposition 𝒟]
    {dD : D →ₗ[R] D} {hD : IsNonUnitalDGAlgebra 𝒟 dD}
    (k : NonUnitalDGAlgHom hC hD) (g : NonUnitalDGAlgHom hB hC)
    (f : NonUnitalDGAlgHom hA hB) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext a
  simp only [comp_apply]

end NonUnitalDGAlgHom

/-! ### Forgetting units -/

namespace DGAlgHom

variable {A' : Type uA} {B' : Type uB}
  [Ring A'] [Algebra R A'] [Ring B'] [Algebra R B']
  {𝒜' : ℤ → Submodule R A'} {ℬ' : ℤ → Submodule R B'}
  [GradedAlgebra 𝒜'] [GradedAlgebra ℬ']
  {dA' : A' →ₗ[R] A'} {dB' : B' →ₗ[R] B'}
  {hA' : IsDGAlgebra 𝒜' dA'} {hB' : IsDGAlgebra ℬ' dB'}

/-- Forget that a morphism of unital DG algebras preserves units. -/
def toNonUnital (f : DGAlgHom hA' hB') :
    NonUnitalDGAlgHom hA'.toIsNonUnitalDGAlgebra hB'.toIsNonUnitalDGAlgebra where
  toNonUnitalAlgHom := f.toGradedAlgHom.toAlgHom.toNonUnitalAlgHom
  map_mem' := f.map_mem
  map_d' := f.map_d

/-- Forgetting units does not change the value of a DG algebra morphism. -/
@[simp]
theorem toNonUnital_apply (f : DGAlgHom hA' hB') (a : A') :
    f.toNonUnital a = f a := (rfl)

@[simp]
theorem coe_toNonUnital (f : DGAlgHom hA' hB') : ⇑f.toNonUnital = f :=
  funext f.toNonUnital_apply

/-- Forgetting units sends the identity unital DG algebra morphism to the nonunital identity. -/
@[simp]
theorem toNonUnital_id (hA' : IsDGAlgebra 𝒜' dA') :
    (DGAlgHom.id hA').toNonUnital =
      NonUnitalDGAlgHom.id hA'.toIsNonUnitalDGAlgebra := by
  ext a
  simp only [toNonUnital_apply, DGAlgHom.id_apply, NonUnitalDGAlgHom.id_apply]

/-- Forgetting units preserves composition of DG algebra morphisms. -/
@[simp]
theorem toNonUnital_comp {C' : Type uC} [Ring C'] [Algebra R C']
    {𝒞' : ℤ → Submodule R C'} [GradedAlgebra 𝒞']
    {dC' : C' →ₗ[R] C'} {hC' : IsDGAlgebra 𝒞' dC'}
    (g : DGAlgHom hB' hC') (f : DGAlgHom hA' hB') :
    (g.comp f).toNonUnital = g.toNonUnital.comp f.toNonUnital := by
  ext a
  simp only [toNonUnital_apply, DGAlgHom.comp_apply, NonUnitalDGAlgHom.comp_apply]

end DGAlgHom

end TauCeti
