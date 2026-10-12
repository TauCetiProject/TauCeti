/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Tensor
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Irreducible

/-!
# The determinant twist of a Weyl module, indexed by a dominant weight

The Weyl modules `TauCeti.weylModuleOfShape` are indexed by Young diagrams, so they only reach the
*polynomial* representations of `GL n k`.  A general dominant weight `λ` is not a Young diagram: its
entries may be negative.  It is however a Young diagram shifted by an integer, namely its
polynomial part `TauCeti.DominantWeight.detShiftShape` shifted by its last entry
`TauCeti.DominantWeight.detShift` (`TauCeti.DominantWeight.shift_weightOfShape_detShiftShape`), and
shifting a weight by `m·(1, …, 1)` is tensoring a representation with `det ^ m`.  That presentation
is unique once the diagram is required to have at most `n - 1` rows, which the polynomial part
always does (`TauCeti.DominantWeight.colLen_zero_detShiftShape_le_pred` and
`TauCeti.DominantWeight.eq_detShift_and_eq_detShiftShape`); without the row bound the diagram and
the shift can trade a constant against each other.

This file performs that twist.  For `λ : DominantWeight n`,

`rationalWeylRep k n λ := det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)`, `μ = λ.detShiftShape`,

realized on the Weyl module of `μ` itself rather than on `k ⊗ 𝕊^{μ}(kⁿ)`, the line being absorbed
by `Representation.charTwist` (and `TauCeti.tprodEquivRationalWeylRep` identifies the two).  Over
a field of characteristic zero it is **irreducible for every dominant weight, with no row
condition**: the polynomial part of a weight for `GL n` automatically has at most `n` rows
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le`), which is exactly the hypothesis the
irreducibility of a Weyl module needs, and a determinant twist does not change the lattice of
subrepresentations.  So the dominant weights index a family of irreducible rational
representations without a side condition, each of them a twist of the Weyl module of a shape with
at most `n - 1` rows.

What is *not* done here is to identify `rationalWeylRep k n λ` as the irreducible representation of
highest weight `λ`, nor to show that these exhaust the irreducible rational representations, nor
that distinct weights give non-isomorphic representations: all three belong to the highest-weight
classification, which is not proved here.  The construction and its irreducibility are what that
classification will be stated about.

## Main definitions

* `TauCeti.rationalWeylRep`: the determinant twist `det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)` of the Weyl module of the
  polynomial part of `λ`, on the carrier of that Weyl module.
* `TauCeti.rationalWeylFDRep`: the same representation bundled as an object of `FDRep`.
* `TauCeti.tprodEquivRationalWeylRep`: the identification of the literal tensor product
  `TauCeti.detPowerRep ⊗ 𝕊^{μ}(kⁿ)` with `TauCeti.rationalWeylRep`.

## Main results

* `TauCeti.isIrreducible_rationalWeylRep` and `TauCeti.simple_rationalWeylFDRep`: over a field of
  characteristic zero, **the rational Weyl module of a dominant weight is irreducible**, for every
  dominant weight.
* `TauCeti.rationalWeylRep_eq_weylRepOfShape_of_detShift_eq_zero`: a weight with vanishing last
  entry is untwisted, so the Weyl modules of shapes with at most `n - 1` rows occur as the
  untwisted case of the construction.
* `TauCeti.weightSpace_rationalWeylRep`: the twist translates the weights of the Weyl module of
  the polynomial part by the constant sequence `λₙ`.
* `TauCeti.char_rationalWeylRep`: over a field of characteristic zero, its character is `det ^ λₙ`
  times the character of the Weyl module of the polynomial part.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
-/

public section

namespace TauCeti

universe u

open Matrix

section CommRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ)

/-! ## The twisted Weyl module -/

/-- **The rational Weyl module of a dominant weight** `λ`: the Weyl module of the polynomial part
`μ = λ.detShiftShape`, with its `GL n k`-action twisted by the linear character `det ^ λₙ`.

The carrier is that of the Weyl module of `μ`; the usual tensor-product form
`det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)` is `TauCeti.tprodEquivRationalWeylRep`. -/
noncomputable def rationalWeylRep (l : DominantWeight n) :
    Representation k (GL (Fin n) k) (weylModuleOfShape k n l.detShiftShape).toSubmodule :=
  Representation.charTwist
    ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ l.detShift)
    (weylRepOfShape k n l.detShiftShape)

/-- The defining equation of `TauCeti.rationalWeylRep`, as a character twist.  The body is not
exposed, so this is how the theory of `Representation.charTwist` is applied to it downstream. -/
theorem rationalWeylRep_def (l : DominantWeight n) :
    rationalWeylRep k n l =
      Representation.charTwist
        ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ l.detShift)
        (weylRepOfShape k n l.detShiftShape) :=
  (rfl)

@[simp]
theorem rationalWeylRep_apply (l : DominantWeight n) (g : GL (Fin n) k)
    (x : (weylModuleOfShape k n l.detShiftShape).toSubmodule) :
    rationalWeylRep k n l g x =
      (↑(Matrix.GeneralLinearGroup.det g ^ l.detShift) : k) •
        weylRepOfShape k n l.detShiftShape g x :=
  Representation.charTwist_apply_apply _ _ g x

/-- A dominant weight whose last entry vanishes carries no twist: its rational Weyl module is the
Weyl module of its polynomial part.  Since a polynomial part has at most `n - 1` rows, the Weyl
modules occurring in the case `λₙ = 0` are those of shapes with at most `n - 1` rows. -/
theorem rationalWeylRep_eq_weylRepOfShape_of_detShift_eq_zero {l : DominantWeight n}
    (hl : l.detShift = 0) :
    rationalWeylRep k n l = weylRepOfShape k n l.detShiftShape := by
  have h : (Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ l.detShift = 1 := by
    rw [hl]
    exact MonoidHom.ext fun g => by simp
  rw [rationalWeylRep_def, h, Representation.charTwist_one]

/-- **The tensor product of `det ^ λₙ` with the Weyl module of the polynomial part of `λ` is the
rational Weyl module**, the form in which the determinant twist is usually written.  The
equivalence is `TensorProduct.lid`: the tensor product with the line is the twist with the line
absorbed, which is `Representation.tprodEquivCharTwist` at the character `det ^ λₙ`. -/
noncomputable def tprodEquivRationalWeylRep (l : DominantWeight n) :
    ((detPowerRep k n l.detShift).tprod (weylRepOfShape k n l.detShiftShape)).Equiv
      (rationalWeylRep k n l) :=
  .mk (_root_.TensorProduct.lid k _) fun g => LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, detPowerRep_def, rationalWeylRep_apply]
    exact Representation.lid_ofLinearCharacter_tprod_apply _ _ g x

@[simp]
theorem toLinearMap_tprodEquivRationalWeylRep (l : DominantWeight n) :
    (tprodEquivRationalWeylRep k n l).toLinearMap =
      (_root_.TensorProduct.lid k
        ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule).toLinearMap :=
  (rfl)

@[simp]
theorem tprodEquivRationalWeylRep_tmul (l : DominantWeight n) (x : k)
    (v : (weylModuleOfShape k n l.detShiftShape).toSubmodule) :
    tprodEquivRationalWeylRep k n l (x ⊗ₜ[k] v) = x • v :=
  (rfl)

/-- **The twist translates the weights**: the weight-`a` space of the rational Weyl module of `λ`
is the weight-`(a - λₙ)` space of the Weyl module of the polynomial part of `λ`.  Both are
submodules of the same carrier, no identification intervening. -/
@[simp]
theorem weightSpace_rationalWeylRep (l : DominantWeight n) (a : Fin n → ℤ) :
    weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) a
      = weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (weylRepOfShape k n l.detShiftShape) (a - fun _ ↦ l.detShift) := by
  rw [rationalWeylRep_def, weightSpace_charTwist_detPow]

end CommRing

section Bundled

variable (k : Type u) [CommRing k] [Algebra ℚ k] [IsNoetherianRing k] (n : ℕ)

/-- The rational Weyl module of a dominant weight, bundled as an object of `FDRep`, in parallel with
`TauCeti.weylFDRepOfShape`: the Noetherian hypothesis is all the bundling asks, a submodule of the
tensor power being finitely generated as soon as the base ring is Noetherian. -/
noncomputable abbrev rationalWeylFDRep (l : DominantWeight n) : FDRep k (GL (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule) (rationalWeylRep k n l)

end Bundled

section Field

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-! ## Irreducibility -/

/-- **The rational Weyl module of a dominant weight is irreducible**, for *every* dominant weight
and with no condition on the number of rows: the polynomial part of a weight for `GL n` has at most
`n` rows, so its Weyl module is irreducible, and twisting by a linear character preserves
irreducibility. -/
instance isIrreducible_rationalWeylRep (l : DominantWeight n) :
    Representation.IsIrreducible (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) :=
  (Representation.isIrreducible_charTwist_iff _ _).mpr
    ((isIrreducible_weylRepOfShape_iff _).mpr l.colLen_zero_detShiftShape_le)

/-! ## The bundled form and the character -/

/-- The bundled rational Weyl module is a simple object of `FDRep k (GL (Fin n) k)`, for every
dominant weight. -/
instance simple_rationalWeylFDRep (l : DominantWeight n) :
    CategoryTheory.Simple (rationalWeylFDRep k n l) :=
  (FDRep.simple_iff_isIrreducible _).mpr (isIrreducible_rationalWeylRep k n l)

/-- **The character of the rational Weyl module is `det ^ λₙ` times the character of the Weyl
module of the polynomial part of `λ`.** -/
@[simp]
theorem char_rationalWeylRep (l : DominantWeight n) (g : GL (Fin n) k) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) g =
      (↑(Matrix.GeneralLinearGroup.det g ^ l.detShift) : k) *
        Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
          (weylRepOfShape k n l.detShiftShape) g :=
  Representation.char_charTwist _ _ g

/-- The character of the bundled rational Weyl module, the same identity read in `FDRep`. -/
@[simp]
theorem char_rationalWeylFDRep (l : DominantWeight n) (g : GL (Fin n) k) :
    (rationalWeylFDRep k n l).character g =
      (↑(Matrix.GeneralLinearGroup.det g ^ l.detShift) : k) *
        (weylFDRepOfShape k n l.detShiftShape).character g :=
  char_rationalWeylRep k n l g

end Field

end TauCeti
