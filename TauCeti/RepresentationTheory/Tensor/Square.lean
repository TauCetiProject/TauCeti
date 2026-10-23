/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.RepresentationTheory.ExteriorPower
public import TauCeti.RepresentationTheory.SymmetricPower
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Tensor-square decompositions of representations

When `2` is invertible, the tensor square of a representation splits into its symmetric and
exterior squares. This file lifts the natural linear decomposition to representations. It also
proves the two trace identities that this splitting is measured by, over every field, including
characteristic two where the decomposition does not split.

The two identities read the same exact sequence `⋀²M → M ⊗ M → Sym²M` twice. Reading it against
`g` acting diagonally gives the sum `χ(g)² = χ_{Sym²}(g) + χ_{Λ²}(g)`. Reading it against that
same diagonal action *composed with the swap of the two tensor factors* gives the difference:
the swap is `-1` on the exterior square and `+1` on the symmetric square, while its composite
with the diagonal action has trace `χ(g²)`. So `χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)`, and adding and
subtracting the two identities gives the doubled formulas `2·χ_{Sym²}(g) = χ(g)² + χ(g²)` and
`2·χ_{Λ²}(g) = χ(g)² - χ(g²)`. These hold over every field, but they pin down the two characters
individually only away from characteristic two: in characteristic two their left sides vanish and
the sum and difference identities coincide, so neither character is determined by them.

## Main definitions

* `Representation.tensorSquareEquivSymmetricExterior` is the natural representation equivalence.

## Main results

* `Representation.char_tensorSquare` is the tensor-square character identity, the sum
  `χ(g)² = χ_{Sym²}(g) + χ_{Λ²}(g)`.
* `Representation.char_symmetricSquare_sub_char_exteriorSquare` is the companion difference
  `χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)`.
* `Representation.two_mul_char_symmetricSquare` and
  `Representation.two_mul_char_exteriorSquare` are the doubled formulas, over every field, and
  `Representation.char_symmetricSquare` and `Representation.char_exteriorSquare` are the
  familiar halved forms that determine each character, away from characteristic two.

## Implementation notes

The trace identities specialize `LinearMap.trace_piTensorProduct_map_two` and
`LinearMap.trace_symmetricPower_sub_trace_exteriorPower` from the linear tensor-square API to
the action of a representation. Both hold in characteristic two: the linear trace identities
use exactness and freeness, with no assumption on `2`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6 and Exercise 2.2.
* J.-P. Serre, *Linear Representations of Finite Groups*, §2.1 and §13.2.
* Mathlib's exterior-power universal-property, pairing, and basis APIs, by Sophie Morel,
  Joël Riou, and Daniel Morrison.
-/

public section

open scoped TensorProduct

universe v w

variable {R : Type} {G : Type v} {M : Type w}

namespace Representation

section CommRing

variable [CommRing R] [Invertible (2 : R)] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The tensor square of a representation is equivalent to the product of its symmetric and
exterior squares when `2` is invertible. -/
noncomputable def tensorSquareEquivSymmetricExterior (ρ : Representation R G M) :
    (ρ.tensorPower 2).Equiv ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) :=
  .mk (TauCeti.tensorSquareEquivSymmetricExterior R M) fun g ↦ by
    apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
    rintro _ ⟨f, rfl⟩
    simp only [LinearMap.comp_apply, tensorPower_apply, PiTensorProduct.map_tprod]
    -- Unfold the representation action and product wrappers to compare their pure-tensor values.
    change TauCeti.tensorSquareEquivSymmetricExterior R M
        (PiTensorProduct.tprod R fun i ↦ ρ g (f i)) =
      ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) g
        (TauCeti.tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f))
    have h₁ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M
      (fun i ↦ ρ g (f i))
    have h₂ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M f
    rw [h₁, h₂]
    simp only [prod_apply_apply, symmetricPower_apply, SymmetricPower.map_tprod,
      exteriorPower_apply, exteriorPower.map_apply_ιMulti, Prod.mk.injEq, true_and]
    apply congrArg (exteriorPower.ιMulti R 2)
    funext i
    rfl

/-- The underlying linear equivalence of the tensor-square decomposition is the natural
linear-algebraic decomposition. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_toLinearEquiv (ρ : Representation R G M) :
    ρ.tensorSquareEquivSymmetricExterior.toLinearEquiv =
      TauCeti.tensorSquareEquivSymmetricExterior R M :=
  (rfl)

end CommRing

section Field

variable [Field R] [Monoid G]
variable [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- Over any field, the tensor-square character is the sum of the symmetric-square and
exterior-square characters. -/
theorem char_tensorSquare (ρ : Representation R G M) (g : G) : (ρ.character g) ^ 2 =
      (ρ.symmetricPower 2).character g + (ρ.exteriorPower 2).character g := by
  classical
  rw [← char_tensorPower ρ 2 g]
  simp only [Representation.character, tensorPower_apply, symmetricPower_apply,
    exteriorPower_apply]
  exact (ρ g).trace_piTensorProduct_map_two

/-- **The difference of the two square characters is the character at the square.** Over any
field, including in characteristic two, `χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)`; this is the identity
that, together with `Representation.char_tensorSquare`, gives the doubled formulas for the two
characters, which determine them individually away from characteristic two. -/
theorem char_symmetricSquare_sub_char_exteriorSquare (ρ : Representation R G M) (g : G) :
    (ρ.symmetricPower 2).character g - (ρ.exteriorPower 2).character g
      = ρ.character (g * g) := by
  simpa only [Representation.character, symmetricPower_apply, exteriorPower_apply, map_mul,
    Module.End.mul_eq_comp] using
    LinearMap.trace_symmetricPower_sub_trace_exteriorPower (ρ g)

/-- **The symmetric-square character, without dividing**: `2·χ_{Sym²}(g) = χ(g)² + χ(g²)`. -/
theorem two_mul_char_symmetricSquare (ρ : Representation R G M) (g : G) :
    2 * (ρ.symmetricPower 2).character g = ρ.character g ^ 2 + ρ.character (g * g) := by
  rw [char_tensorSquare ρ g, ← char_symmetricSquare_sub_char_exteriorSquare ρ g]
  ring

/-- **The exterior-square character, without dividing**: `2·χ_{Λ²}(g) = χ(g)² - χ(g²)`. -/
theorem two_mul_char_exteriorSquare (ρ : Representation R G M) (g : G) :
    2 * (ρ.exteriorPower 2).character g = ρ.character g ^ 2 - ρ.character (g * g) := by
  rw [char_tensorSquare ρ g, ← char_symmetricSquare_sub_char_exteriorSquare ρ g]
  ring

/-- **The character of the symmetric square**, `χ_{Sym²}(g) = ½(χ(g)² + χ(g²))`, away from
characteristic two. -/
theorem char_symmetricSquare (ρ : Representation R G M) (g : G) (h2 : (2 : R) ≠ 0) :
    (ρ.symmetricPower 2).character g = (ρ.character g ^ 2 + ρ.character (g * g)) / 2 :=
  eq_div_of_mul_eq h2 (by rw [mul_comm]; exact two_mul_char_symmetricSquare ρ g)

/-- **The character of the exterior square**, `χ_{Λ²}(g) = ½(χ(g)² - χ(g²))`, away from
characteristic two. -/
theorem char_exteriorSquare (ρ : Representation R G M) (g : G) (h2 : (2 : R) ≠ 0) :
    (ρ.exteriorPower 2).character g = (ρ.character g ^ 2 - ρ.character (g * g)) / 2 :=
  eq_div_of_mul_eq h2 (by rw [mul_comm]; exact two_mul_char_exteriorSquare ρ g)

end Field

end Representation
