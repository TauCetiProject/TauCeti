/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# Weyl modules restricted to the special linear group

The rational representations of `GL n k` are the determinant twists `det^m ⊗ 𝕊^μ(kⁿ)` of the
polynomial ones, and the twist is exactly what the special linear subgroup cannot see: `det` is
constantly `1` on `SL n k`.  This file restricts the Weyl modules along the inclusion
`SL n k ↪ GL n k` and records that invisibility.

Two forms of it are proved.  The tensor form, `TauCeti.tprodDetPowerSLEquiv`, says that for *any*
representation `ρ` of `GL n k` the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of
`ρ`, along `TensorProduct.lid`; the carrier-level form,
`TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`, says that the rational Weyl module of a dominant
weight `λ` restricts to the Weyl module of its polynomial part
`TauCeti.DominantWeight.detShiftShape`, and here it is an equality of representations, not merely
an isomorphism, because `TauCeti.rationalWeylRep` is built on the carrier of that Weyl module.

Combining the second form with `TauCeti.DominantWeight.detShiftShape_shift` gives the statement
the classical-groups roadmap pins for `SL n`: the restriction depends on `λ` only through its
class modulo the constant weights `m·(1, …, 1)`, and by
`TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` it depends on nothing less.  Those
classes are indexed by the Young diagrams of at most `n - 1` rows
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le_pred`), so the Weyl modules of such diagrams
already exhaust the restrictions.  On characters the invariance needs no rewriting of shapes and is
stated outright as `TauCeti.char_rationalWeylSLRep_shift`.

That these restrictions are *irreducible*, and that they exhaust the irreducible rational
representations of `SL n k`, is the highest-weight classification for `SL n` and is not proved
here; it needs more than the determinant twist, since recovering `GL n k` from `SL n k` and the
scalars asks every unit of `k` to be an `n`-th power.

## Main definitions

* `TauCeti.weylSLRepOfShape`: the Weyl module of a Young diagram, as a representation of
  `SL n k`, with `TauCeti.weylSLFDRepOfShape` its bundled form.
* `TauCeti.rationalWeylSLRep`: the rational Weyl module of a dominant weight, as a representation
  of `SL n k`, with `TauCeti.rationalWeylSLFDRep` its bundled form.
* `TauCeti.tprodDetPowerSLEquiv`: the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of
  `ρ`, along `TensorProduct.lid`.

## Main results

* `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`: **the determinant twist disappears on
  `SL n k`** -- the rational Weyl module of `λ` restricts to the Weyl module of the polynomial
  part of `λ`.
* `TauCeti.char_rationalWeylSLRep_shift`: **the restricted character only depends on `λ` modulo
  the constant weights**.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, “`SLₙ`”.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones and the
  representations of `SL n` are indexed by dominant weights modulo `(1, …, 1)`.
-/

public section

open Matrix
open scoped TensorProduct

universe u v

namespace TauCeti

section Determinant

variable (k : Type u) [CommRing k] (n : ℕ)

/-! ## The determinant twist on the special linear group -/

/-- **`TensorProduct.lid` carries the restricted action of `det^m ⊗ ρ` to the restricted action of
`ρ`**: the determinant is `1` on `SL n k`, so the twisting factor is `1`.  This is the
equivariance datum behind `TauCeti.tprodDetPowerSLEquiv`, recorded on elements so that it can be
used without unfolding that equivalence. -/
theorem lid_detPowerRep_tprod_toGL_apply {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) (g : Matrix.SpecialLinearGroup (Fin n) k)
    (x : k ⊗[k] V) :
    _root_.TensorProduct.lid k V
        (((detPowerRep k n m).tprod ρ) (Matrix.SpecialLinearGroup.toGL g) x)
      = ρ (Matrix.SpecialLinearGroup.toGL g) (_root_.TensorProduct.lid k V x) := by
  have hdet : (((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m)
      (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [detPowerRep_def, Representation.lid_ofLinearCharacter_tprod_apply, hdet, Units.val_one,
    one_smul]

/-- **The determinant twist is invisible to the special linear group**: for every representation
`ρ` of `GL n k`, the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of `ρ`, along
`TensorProduct.lid`.  This is the twist-by-twist form of
`TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`. -/
noncomputable def tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    Representation.Equiv
      (((detPowerRep k n m).tprod ρ).comp Matrix.SpecialLinearGroup.toGL)
      (ρ.comp Matrix.SpecialLinearGroup.toGL) :=
  .mk (_root_.TensorProduct.lid k V) fun g =>
    LinearMap.ext fun x => lid_detPowerRep_tprod_toGL_apply k n m ρ g x

@[simp]
theorem toLinearMap_tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    (tprodDetPowerSLEquiv k n m ρ).toLinearMap =
      (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

end Determinant

section CommRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ)

/-! ## The Weyl module of a shape -/

/-- **The Weyl module of a Young diagram as a representation of `SL n k`**, restricting
`TauCeti.weylRepOfShape` along the inclusion of the special linear group. -/
noncomputable def weylSLRepOfShape (μ : YoungDiagram) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k)
      ↥(weylModuleOfShape k n μ).toSubmodule :=
  (weylRepOfShape k n μ).comp Matrix.SpecialLinearGroup.toGL

@[simp]
theorem weylSLRepOfShape_apply (μ : YoungDiagram) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    weylSLRepOfShape k n μ g = weylRepOfShape k n μ (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

/-! ## The rational Weyl module of a dominant weight -/

/-- **The rational Weyl module of a dominant weight as a representation of `SL n k`**, restricting
`TauCeti.rationalWeylRep` along the inclusion of the special linear group. -/
noncomputable def rationalWeylSLRep (l : DominantWeight n) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k)
      ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule :=
  (rationalWeylRep k n l).comp Matrix.SpecialLinearGroup.toGL

@[simp]
theorem rationalWeylSLRep_apply (l : DominantWeight n)
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    rationalWeylSLRep k n l g = rationalWeylRep k n l (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

/-- **The determinant twist disappears on the special linear group**: the rational Weyl module of
a dominant weight `λ` restricts to the Weyl module of the polynomial part of `λ`.  The two are
equal, not merely isomorphic, because `TauCeti.rationalWeylRep` twists the action on the carrier
of that very Weyl module.

Rewriting the shape with `TauCeti.DominantWeight.detShiftShape_shift` turns this into the
statement that the restriction depends on `λ` only through its class modulo the constant weights
`m·(1, …, 1)`, and `TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` says that it
depends on nothing coarser. -/
theorem rationalWeylSLRep_eq_weylSLRepOfShape (l : DominantWeight n) :
    rationalWeylSLRep k n l = weylSLRepOfShape k n l.detShiftShape := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  have hdet : (Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [rationalWeylSLRep_apply, weylSLRepOfShape_apply, rationalWeylRep_apply, hdet, one_zpow,
    Units.val_one, one_smul]

/-- The rational Weyl module of `λ`, restricted to `SL n k`, is the restriction of
`det^{λₙ} ⊗ 𝕊^μ(kⁿ)` with `μ` the polynomial part of `λ`: the tensor form of
`TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`, obtained from
`TauCeti.tprodDetPowerSLEquiv`. -/
noncomputable def tprodEquivRationalWeylSLRep (l : DominantWeight n) :
    Representation.Equiv
      (((detPowerRep k n l.detShift).tprod
        (weylRepOfShape k n l.detShiftShape)).comp Matrix.SpecialLinearGroup.toGL)
      (weylSLRepOfShape k n l.detShiftShape) :=
  tprodDetPowerSLEquiv k n l.detShift (weylRepOfShape k n l.detShiftShape)

end CommRing

section Bundled

variable (k : Type u) [CommRing k] [Algebra ℚ k] [IsNoetherianRing k] (n : ℕ)

/-- The Weyl module of a shape over `SL n k`, bundled as an object of `FDRep`, in parallel with
`TauCeti.weylFDRepOfShape`: the Noetherian hypothesis is all the bundling asks, a submodule of the
tensor power being finitely generated as soon as the base ring is Noetherian. -/
noncomputable abbrev weylSLFDRepOfShape (μ : YoungDiagram) :
    FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n μ).toSubmodule) (weylSLRepOfShape k n μ)

/-- The rational Weyl module of a dominant weight over `SL n k`, bundled as an object of `FDRep`,
in parallel with `TauCeti.rationalWeylFDRep`. -/
noncomputable abbrev rationalWeylSLFDRep (l : DominantWeight n) :
    FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule) (rationalWeylSLRep k n l)

/-- The bundled form of `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`. -/
theorem rationalWeylSLFDRep_eq_weylSLFDRepOfShape (l : DominantWeight n) :
    rationalWeylSLFDRep k n l = weylSLFDRepOfShape k n l.detShiftShape := by
  rw [rationalWeylSLFDRep, rationalWeylSLRep_eq_weylSLRepOfShape]

end Bundled

section Field

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-! ## Characters -/

/-- The character of the Weyl module of a shape over `SL n k` is the character of the Weyl module
over `GL n k`, read at the image of the matrix. -/
@[simp]
theorem char_weylSLRepOfShape (μ : YoungDiagram) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylSLRepOfShape k n μ) g
      = Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

/-- **The restricted character of a rational Weyl module is the character of the Weyl module of
its polynomial part**: the determinant factor of `TauCeti.char_rationalWeylRep` is `1` on
`SL n k`. -/
@[simp]
theorem char_rationalWeylSLRep (l : DominantWeight n)
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylSLRep k n l) g
      = Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (weylSLRepOfShape k n l.detShiftShape) g := by
  rw [rationalWeylSLRep_eq_weylSLRepOfShape]

/-- **The restricted character depends on the weight only modulo the constant weights**: `λ` and
`λ + m·(1, …, 1)` have the same character on `SL n k`.  Unlike
`TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`, this needs no rewriting of carriers, the
character being a scalar. -/
theorem char_rationalWeylSLRep_shift (l : DominantWeight n) (m : ℤ)
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Representation.character (V := ↥(weylModuleOfShape k n (l.shift m).detShiftShape).toSubmodule)
        (rationalWeylSLRep k n (l.shift m)) g
      = Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylSLRep k n l) g := by
  rw [char_rationalWeylSLRep, char_rationalWeylSLRep, DominantWeight.detShiftShape_shift]

end Field

end TauCeti
