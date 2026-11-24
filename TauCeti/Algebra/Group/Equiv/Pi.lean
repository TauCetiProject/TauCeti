/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Equiv.Basic
public import TauCeti.Logic.Equiv.Pi

/-!
# Multiplicative and additive equivalences of Pi types

Functions into products are multiplicatively (additively) equivalent to products of function
spaces: a family of pairs regroups into a pair of families. In the torsion decomposition of an
elliptic curve, each primary component of `E[N]` is a product of two cyclic groups; regrouping
lets the Chinese remainder theorem reassemble the first and second cyclic factors separately into
`ZMod N`.

Coordinate transport by `MulEquiv.arrowCongr` (`AddEquiv.arrowCongr`) inverts by reversing both
the coordinate and alphabet equivalences.

Transporting a product `∀ i, M i` of monoids along an equivalence `e : ι' ≃ ι` of the index types,
`MulEquiv.piCongrLeft M e : (∀ i', M (e i')) ≃* ∀ i, M i`, is `Equiv.piCongrLeft` as a
multiplicative equivalence; it relabels the factors of a product of groups. Relabelling along two
equivalences in turn is relabelling along their composite (`MulEquiv.piCongrLeft_trans`).

A product indexed by `Option α` splits off its factor at `none`:
`MulEquiv.piOptionEquivProd : (∀ a, N a) ≃* N none × ∀ a, N (some a)` is
`Equiv.piOptionEquivProd` as a multiplicative equivalence.

## Main declarations

* `TauCeti.MulEquiv.arrowProdEquivProdArrow`:
  `(∀ i, M i × N i) ≃* (∀ i, M i) × (∀ i, N i)`, with additive version
  `TauCeti.AddEquiv.arrowProdEquivProdArrow`.
* `MulEquiv.arrowCongr_symm`, `AddEquiv.arrowCongr_symm`: inversion reverses both equivalences
  in function transport.
* `MulEquiv.piCongrLeft`, `AddEquiv.piCongrLeft`: transport of dependent functions along an
  equivalence of the index types.
* `MulEquiv.piOptionEquivProd`, `AddEquiv.piOptionEquivProd`: splitting off the factor at `none`
  of a product indexed by `Option α`.
-/

public section

/-- Inverting multiplicative function transport reverses the equivalences of both the domain and
the codomain. -/
@[to_additive (attr := simp) /-- Inverting additive function transport reverses the equivalences
of both the domain and the codomain. -/]
theorem MulEquiv.arrowCongr_symm {ι κ M N : Type*} [Mul M] [Mul N] (e : ι ≃ κ) (f : M ≃* N) :
    (MulEquiv.arrowCongr e f).symm = MulEquiv.arrowCongr e.symm f.symm := (rfl)

namespace MulEquiv

variable {ι ι' ι'' : Type*} (M : ι → Type*) [∀ i, Mul (M i)]

/-- Transport dependent functions through an equivalence of the index types. This is
`Equiv.piCongrLeft` as a `MulEquiv`. -/
@[to_additive /-- Transport dependent functions through an equivalence of the index types. This is
`Equiv.piCongrLeft` as an `AddEquiv`. -/]
def piCongrLeft (e : ι' ≃ ι) : (∀ i', M (e i')) ≃* ∀ i, M i :=
  (MulEquiv.mk (Equiv.piCongrLeft M e).symm fun _ _ ↦ (rfl)).symm

@[to_additive (attr := simp)]
theorem coe_piCongrLeft (e : ι' ≃ ι) : ⇑(piCongrLeft M e) = Equiv.piCongrLeft M e :=
  (rfl)

/-- The inverse of relabelling along `e` reads the coordinate at `i'` from `e i'`. -/
@[to_additive (attr := simp) /-- The inverse of relabelling along `e` reads the coordinate at `i'`
from `e i'`. -/]
theorem piCongrLeft_symm_apply (e : ι' ≃ ι) (f : ∀ i, M i) (i' : ι') :
    (piCongrLeft M e).symm f i' = f (e i') :=
  (rfl)

@[to_additive (attr := simp)]
theorem piCongrLeft_refl : piCongrLeft M (.refl ι) = .refl (∀ i, M i) :=
  (rfl)

/-- Relabelling the factors along `e₁` and then along `e₂` is relabelling them along
`e₁.trans e₂`. -/
@[to_additive /-- Relabelling the summands along `e₁` and then along `e₂` is relabelling them along
`e₁.trans e₂`. -/]
theorem piCongrLeft_trans (e₁ : ι'' ≃ ι') (e₂ : ι' ≃ ι) :
    (piCongrLeft (fun i' ↦ M (e₂ i')) e₁).trans (piCongrLeft M e₂) =
      piCongrLeft M (e₁.trans e₂) :=
  toEquiv_injective (Equiv.piCongrLeft_trans M e₁ e₂)

variable {α : Type*} {N : Option α → Type*} [∀ a, Mul (N a)]

/-- A product indexed by `Option α` splits off the factor at `none`. This is
`Equiv.piOptionEquivProd` as a `MulEquiv`. -/
@[to_additive /-- A product indexed by `Option α` splits off the summand at `none`. This is
`Equiv.piOptionEquivProd` as an `AddEquiv`. -/]
def piOptionEquivProd : (∀ a, N a) ≃* N none × ∀ a, N (some a) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }

@[to_additive (attr := simp)]
theorem piOptionEquivProd_apply (g : ∀ a, N a) :
    piOptionEquivProd g = (g none, fun a ↦ g (some a)) :=
  (rfl)

@[to_additive (attr := simp)]
theorem piOptionEquivProd_symm_apply_none (x : N none × ∀ a, N (some a)) :
    piOptionEquivProd.symm x none = x.1 :=
  (rfl)

@[to_additive (attr := simp)]
theorem piOptionEquivProd_symm_apply_some (x : N none × ∀ a, N (some a)) (a : α) :
    piOptionEquivProd.symm x (some a) = x.2 a :=
  (rfl)

end MulEquiv

namespace TauCeti.MulEquiv

variable {ι : Type*} (M N : ι → Type*) [∀ i, Mul (M i)] [∀ i, Mul (N i)]

/-- Functions into products are multiplicatively equivalent to products of function spaces. -/
@[to_additive _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow
/-- Functions into products are additively equivalent to products of function spaces. -/]
def arrowProdEquivProdArrow : (∀ i, M i × N i) ≃* (∀ i, M i) × (∀ i, N i) :=
  { Equiv.arrowProdEquivProdArrow ι M N with map_mul' := fun _ _ ↦ rfl }

/-- `arrowProdEquivProdArrow` maps a function to its two component functions. -/
@[to_additive (attr := simp) _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow_apply
/-- `arrowProdEquivProdArrow` maps a function to its two component functions. -/]
theorem arrowProdEquivProdArrow_apply (f : ∀ i, M i × N i) :
    arrowProdEquivProdArrow M N f = (fun i ↦ (f i).1, fun i ↦ (f i).2) := (rfl)

/-- The inverse of `arrowProdEquivProdArrow` pairs component functions pointwise. -/
@[to_additive (attr := simp) _root_.TauCeti.AddEquiv.arrowProdEquivProdArrow_symm_apply
/-- The inverse of `arrowProdEquivProdArrow` pairs component functions pointwise. -/]
theorem arrowProdEquivProdArrow_symm_apply (f : (∀ i, M i) × (∀ i, N i)) :
    (arrowProdEquivProdArrow M N).symm f = fun i ↦ (f.1 i, f.2 i) := (rfl)

end TauCeti.MulEquiv
