/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.HomComplex
public import Mathlib.LinearAlgebra.Prod

/-!
# Composition in curved duplex Hom complexes

The even and odd cochains between curved duplexes compose by the usual componentwise
composition, with parity added modulo two. Composition is bilinear, associative, and unital.
The Hom differential satisfies the graded Leibniz rule
`δ(g ∘ f) = δ(g) ∘ f + (-1)^|g| g ∘ δ(f)`.

We give all four parity cases explicitly. In particular, the sign depends on the parity of
the second map in Mathlib's diagrammatic composition order. On closed even cochains,
composition agrees with composition of duplex morphisms. These operations apply in particular
to the Hom complexes of finite-projective matrix factorizations.

## References

* I. Frenkel, M. Khovanov and O. Schiffmann, *Homological realization of Nakajima varieties
  and Weyl group actions*, Compositio Mathematica **141** (2005), Sections 2–3.
-/

public section

universe w v u

namespace TauCeti.CurvedDuplex

open CategoryTheory Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [CommRing R] [Linear R C] {w₀ : R}
  {W X Y Z : CurvedDuplex C w₀}

/-- Bilinear composition of two parity-preserving cochains, first `f`, then `g`. -/
def compEvenEven : EvenCochain X Y →ₗ[R] EvenCochain Y Z →ₗ[R] EvenCochain X Z where
  toFun f := (Linear.leftComp R _ f.1).prodMap (Linear.leftComp R _ f.2)
  map_add' f g := by ext h <;> simp [add_comp]
  map_smul' r f := by ext h <;> simp [Linear.smul_comp]

/-- Bilinear composition of an even cochain followed by an odd cochain. -/
def compEvenOdd : EvenCochain X Y →ₗ[R] OddCochain Y Z →ₗ[R] OddCochain X Z where
  toFun f := (Linear.leftComp R _ f.1).prodMap (Linear.leftComp R _ f.2)
  map_add' f g := by ext h <;> simp [add_comp]
  map_smul' r f := by ext h <;> simp [Linear.smul_comp]

/-- Bilinear composition of an odd cochain followed by an even cochain. -/
def compOddEven : OddCochain X Y →ₗ[R] EvenCochain Y Z →ₗ[R] OddCochain X Z where
  toFun f := ((Linear.leftComp R _ f.1).prodMap (Linear.leftComp R _ f.2)).comp
    (LinearEquiv.prodComm R _ _).toLinearMap
  map_add' f g := by ext h <;> simp [add_comp]
  map_smul' r f := by ext h <;> simp [Linear.smul_comp]

/-- Bilinear composition of two parity-reversing cochains. -/
def compOddOdd : OddCochain X Y →ₗ[R] OddCochain Y Z →ₗ[R] EvenCochain X Z where
  toFun f := ((Linear.leftComp R _ f.1).prodMap (Linear.leftComp R _ f.2)).comp
    (LinearEquiv.prodComm R _ _).toLinearMap
  map_add' f g := by ext h <;> simp [add_comp]
  map_smul' r f := by ext h <;> simp [Linear.smul_comp]

@[simp] theorem compEvenEven_fst (f : EvenCochain X Y) (g : EvenCochain Y Z) :
    (compEvenEven f g).1 = f.1 ≫ g.1 := (rfl)

@[simp] theorem compEvenEven_snd (f : EvenCochain X Y) (g : EvenCochain Y Z) :
    (compEvenEven f g).2 = f.2 ≫ g.2 := (rfl)

@[simp] theorem compEvenOdd_fst (f : EvenCochain X Y) (g : OddCochain Y Z) :
    (compEvenOdd f g).1 = f.1 ≫ g.1 := (rfl)

@[simp] theorem compEvenOdd_snd (f : EvenCochain X Y) (g : OddCochain Y Z) :
    (compEvenOdd f g).2 = f.2 ≫ g.2 := (rfl)

@[simp] theorem compOddEven_fst (f : OddCochain X Y) (g : EvenCochain Y Z) :
    (compOddEven f g).1 = f.1 ≫ g.2 := (rfl)

@[simp] theorem compOddEven_snd (f : OddCochain X Y) (g : EvenCochain Y Z) :
    (compOddEven f g).2 = f.2 ≫ g.1 := (rfl)

@[simp] theorem compOddOdd_fst (f : OddCochain X Y) (g : OddCochain Y Z) :
    (compOddOdd f g).1 = f.1 ≫ g.2 := (rfl)

@[simp] theorem compOddOdd_snd (f : OddCochain X Y) (g : OddCochain Y Z) :
    (compOddOdd f g).2 = f.2 ≫ g.1 := (rfl)

/-! ## Units and associativity -/

/-- The identity even cochain. -/
def idEven (X : CurvedDuplex C w₀) : EvenCochain X X := (𝟙 X.X₀, 𝟙 X.X₁)

@[simp] theorem idEven_fst : (idEven X).1 = 𝟙 X.X₀ := (rfl)

@[simp] theorem idEven_snd : (idEven X).2 = 𝟙 X.X₁ := (rfl)

@[simp] theorem compEvenEven_idEven (f : EvenCochain X Y) :
    compEvenEven f (idEven Y) = f := by ext <;> simp

@[simp] theorem idEven_compEvenEven (f : EvenCochain X Y) :
    compEvenEven (idEven X) f = f := by ext <;> simp

@[simp] theorem compOddEven_idEven (f : OddCochain X Y) :
    compOddEven f (idEven Y) = f := by ext <;> simp

@[simp] theorem idEven_compEvenOdd (f : OddCochain X Y) :
    compEvenOdd (idEven X) f = f := by ext <;> simp

/-- Associativity for three even cochains. -/
@[simp] theorem compEvenEven_compEvenEven (f : EvenCochain W X) (g : EvenCochain X Y)
    (h : EvenCochain Y Z) :
    compEvenEven (compEvenEven f g) h = compEvenEven f (compEvenEven g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities even, even, odd. -/
@[simp] theorem compEvenEven_compEvenOdd (f : EvenCochain W X) (g : EvenCochain X Y)
    (h : OddCochain Y Z) :
    compEvenOdd (compEvenEven f g) h = compEvenOdd f (compEvenOdd g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities even, odd, even. -/
@[simp] theorem compEvenOdd_compOddEven (f : EvenCochain W X) (g : OddCochain X Y)
    (h : EvenCochain Y Z) :
    compOddEven (compEvenOdd f g) h = compEvenOdd f (compOddEven g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities even, odd, odd. -/
@[simp] theorem compEvenOdd_compOddOdd (f : EvenCochain W X) (g : OddCochain X Y)
    (h : OddCochain Y Z) :
    compOddOdd (compEvenOdd f g) h = compEvenEven f (compOddOdd g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities odd, even, even. -/
@[simp] theorem compOddEven_compOddEven (f : OddCochain W X) (g : EvenCochain X Y)
    (h : EvenCochain Y Z) :
    compOddEven (compOddEven f g) h = compOddEven f (compEvenEven g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities odd, even, odd. -/
@[simp] theorem compOddEven_compOddOdd (f : OddCochain W X) (g : EvenCochain X Y)
    (h : OddCochain Y Z) :
    compOddOdd (compOddEven f g) h = compOddOdd f (compEvenOdd g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for cochains of parities odd, odd, even. -/
@[simp] theorem compOddOdd_compEvenEven (f : OddCochain W X) (g : OddCochain X Y)
    (h : EvenCochain Y Z) :
    compEvenEven (compOddOdd f g) h = compOddOdd f (compOddEven g h) := by
  ext <;> simp [Category.assoc]

/-- Associativity for three odd cochains. -/
@[simp] theorem compOddOdd_compEvenOdd (f : OddCochain W X) (g : OddCochain X Y)
    (h : OddCochain Y Z) :
    compEvenOdd (compOddOdd f g) h = compOddEven f (compOddOdd g h) := by
  ext <;> simp [Category.assoc]

/-! ## Graded Leibniz laws -/

/-- The differential of an even-even composite satisfies the unsigned Leibniz law. -/
theorem evenDifferential_compEvenEven (f : EvenCochain X Y) (g : EvenCochain Y Z) :
    evenDifferential X Z (compEvenEven f g) =
      compEvenOdd f (evenDifferential Y Z g) +
        compOddEven (evenDifferential X Y f) g := by
  ext <;> simp [sub_comp, comp_sub, Category.assoc]

/-- An odd second factor contributes a minus sign in the even-odd Leibniz law. -/
theorem oddDifferential_compEvenOdd (f : EvenCochain X Y) (g : OddCochain Y Z) :
    oddDifferential X Z (compEvenOdd f g) =
      compEvenEven f (oddDifferential Y Z g) -
        compOddOdd (evenDifferential X Y f) g := by
  ext <;> simp [comp_add, sub_comp, Category.assoc] <;> abel

/-- An even second factor contributes a plus sign in the odd-even Leibniz law. -/
theorem oddDifferential_compOddEven (f : OddCochain X Y) (g : EvenCochain Y Z) :
    oddDifferential X Z (compOddEven f g) =
      compOddOdd f (evenDifferential Y Z g) +
        compEvenEven (oddDifferential X Y f) g := by
  ext <;> simp [add_comp, comp_sub, Category.assoc] <;> abel

/-- The odd-odd Leibniz law has a minus sign and takes values in odd cochains. -/
theorem evenDifferential_compOddOdd (f : OddCochain X Y) (g : OddCochain Y Z) :
    evenDifferential X Z (compOddOdd f g) =
      compOddEven f (oddDifferential Y Z g) -
        compEvenOdd (oddDifferential X Y f) g := by
  ext <;> simp [add_comp, comp_add, Category.assoc] <;> abel

/-- Composition of closed duplex maps is the even-even composition of their cycles. -/
theorem homEquivCycles_comp_val (f : X ⟶ Y) (g : Y ⟶ Z) :
    (homEquivCycles X Z (f ≫ g)).val =
      compEvenEven (homEquivCycles X Y f).val (homEquivCycles Y Z g).val := by
  ext <;> simp

end TauCeti.CurvedDuplex
