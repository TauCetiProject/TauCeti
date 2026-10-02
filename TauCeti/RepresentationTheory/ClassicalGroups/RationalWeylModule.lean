/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Irreducible

/-!
# The determinant twist of a Weyl module, indexed by a dominant weight

The Weyl modules `TauCeti.weylModuleOfShape` are indexed by Young diagrams, so they only reach the
*polynomial* representations of `GL n k`.  A general dominant weight `λ` is not a Young diagram: its
entries may be negative.  What it is, uniquely, is a Young diagram shifted by an integer, namely its
polynomial part `TauCeti.DominantWeight.detShiftShape` shifted by its last entry
`TauCeti.DominantWeight.detShift` (`TauCeti.DominantWeight.shift_weightOfShape_detShiftShape`), and
shifting a weight by `m·(1, …, 1)` is tensoring a representation with `det ^ m`.

This file performs that twist.  For `λ : DominantWeight n`,

`rationalWeylRep k n λ := det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)`, `μ = λ.detShiftShape`,

realized on the Weyl module of `μ` itself rather than on `k ⊗ 𝕊^{μ}(kⁿ)`, the line being absorbed
by `Representation.charTwist` (and `TauCeti.rationalWeylRepTprodEquiv` identifies the two).  It is
**irreducible for every dominant weight, with no row condition**: the polynomial part of a weight
for `GL n` automatically has at most `n` rows
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le`), which is exactly the hypothesis the
irreducibility of a Weyl module needs, and a determinant twist does not change the lattice of
subrepresentations.  So the dominant weights index a family of pairwise distinct irreducible
rational representations without a side condition, the shapes they are twists of being the ones
with at most `n - 1` rows.

What is *not* done here is to identify `rationalWeylRep k n λ` as the irreducible representation of
highest weight `λ`, nor to show that these exhaust the irreducible rational representations: both
belong to the highest-weight classification, which is not proved here.  The construction and its
irreducibility are what that classification will be stated about.

## Main definitions

* `TauCeti.rationalWeylRep`: the determinant twist `det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)` of the Weyl module of the
  polynomial part of `λ`, on the carrier of that Weyl module.
* `TauCeti.rationalWeylFDRep`: the same representation bundled as an object of `FDRep`.
* `TauCeti.rationalWeylRepTprodEquiv`: the identification of `TauCeti.rationalWeylRep` with the
  literal tensor product `TauCeti.detPowerRep ⊗ 𝕊^{μ}(kⁿ)`.

## Main results

* `TauCeti.isIrreducible_rationalWeylRep` and `TauCeti.simple_rationalWeylFDRep`: **the rational
  Weyl module of a dominant weight is irreducible**, for every dominant weight.
* `TauCeti.rationalWeylRep_of_detShift_eq_zero`: a weight with vanishing last entry is untwisted,
  so the polynomial Weyl modules are the special case `λₙ = 0` of the construction.
* `TauCeti.char_rationalWeylRep`: its character is `det ^ λₙ` times the character of the Weyl
  module — the Laurent form of the character of a rational representation.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "Highest weight and the classification", whose closing sentence "the rational `V_λ` are
  then the `det`-twists `det^{λₙ} ⊗ V_μ`" is what this file builds, and Layer 4, "The rational
  character is Laurent".
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

The carrier is that of the Weyl module of `μ`; the tensor-product form `det ^ λₙ ⊗ 𝕊^{μ}(kⁿ)` that
the roadmap writes is `TauCeti.rationalWeylRepTprodEquiv`. -/
noncomputable def rationalWeylRep (l : DominantWeight n) :
    Representation k (GL (Fin n) k) (weylModuleOfShape k n l.detShiftShape).toSubmodule :=
  Representation.charTwist
    ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ l.detShift)
    (weylRepOfShape k n l.detShiftShape)

@[simp]
theorem rationalWeylRep_apply (l : DominantWeight n) (g : GL (Fin n) k)
    (x : (weylModuleOfShape k n l.detShiftShape).toSubmodule) :
    rationalWeylRep k n l g x =
      (↑(Matrix.GeneralLinearGroup.det g ^ l.detShift) : k) •
        weylRepOfShape k n l.detShiftShape g x :=
  Representation.charTwist_apply_apply _ _ g x

/-- A dominant weight whose last entry vanishes carries no twist: its rational Weyl module is the
Weyl module of its polynomial part.  So the polynomial Weyl modules are the case `λₙ = 0`. -/
theorem rationalWeylRep_of_detShift_eq_zero {l : DominantWeight n} (hl : l.detShift = 0) :
    rationalWeylRep k n l = weylRepOfShape k n l.detShiftShape := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [rationalWeylRep_apply, hl, zpow_zero, Units.val_one, one_smul]

/-- **The rational Weyl module is the tensor product of `det ^ λₙ` with the Weyl module of the
polynomial part of `λ`**, the form in which the determinant twist is usually written.  The
equivalence is `TensorProduct.lid`: the twist is the tensor product with the line absorbed. -/
noncomputable def rationalWeylRepTprodEquiv (l : DominantWeight n) :
    ((detPowerRep k n l.detShift).tprod (weylRepOfShape k n l.detShiftShape)).Equiv
      (rationalWeylRep k n l) :=
  .mk (_root_.TensorProduct.lid k _) fun g => by
    ext
    simp

end CommRing

section Field

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-! ## Irreducibility -/

/-- **The rational Weyl module of a dominant weight is irreducible**, for *every* dominant weight
and with no condition on the number of rows: the polynomial part of a weight for `GL n` has at most
`n` rows, so its Weyl module is irreducible, and twisting by a linear character preserves
irreducibility. -/
theorem isIrreducible_rationalWeylRep (l : DominantWeight n) :
    Representation.IsIrreducible (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) :=
  (Representation.isIrreducible_charTwist_iff _ _).mpr
    ((isIrreducible_weylRepOfShape_iff _).mpr l.colLen_zero_detShiftShape_le)

/-! ## The bundled form and the character -/

/-- The rational Weyl module of a dominant weight, bundled as an object of `FDRep`, in parallel with
`TauCeti.weylFDRepOfShape`. -/
noncomputable abbrev rationalWeylFDRep (l : DominantWeight n) : FDRep k (GL (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule) (rationalWeylRep k n l)

/-- The bundled rational Weyl module is a simple object of `FDRep k (GL (Fin n) k)`, for every
dominant weight. -/
theorem simple_rationalWeylFDRep (l : DominantWeight n) :
    CategoryTheory.Simple (rationalWeylFDRep k n l) :=
  (FDRep.simple_iff_isIrreducible _).mpr (isIrreducible_rationalWeylRep k n l)

/-- **The character of the rational Weyl module is Laurent**: it is `det ^ λₙ` times the character
of the Weyl module of the polynomial part of `λ`, a polynomial character divided by a power of the
determinant. -/
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
