/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# Weyl modules restricted to the special linear group

The rational Weyl module `TauCeti.rationalWeylRep` of a dominant weight `λ` is the determinant
twist `det^{λₙ} ⊗ 𝕊^μ(kⁿ)` of the Weyl module of the polynomial part `μ` of `λ`, and that twist is
exactly what the special linear subgroup cannot see: `det` is constantly `1` on `SL n k`.  This
file restricts the Weyl modules along the inclusion `SL n k ↪ GL n k` and records that
invisibility.

The carrier-level form is `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`: the rational Weyl
module of `λ` restricts to the Weyl module of its polynomial part
`TauCeti.DominantWeight.detShiftShape`, and here it is an equality of representations, not merely
an isomorphism, because `TauCeti.rationalWeylRep` is built on the carrier of that Weyl module.
The twist-by-twist form, which says the same thing for an arbitrary representation of `GL n k`, is
`TauCeti.tprodDetPowerSLEquiv`, beside the determinant powers themselves.

Rewriting the shape with `TauCeti.DominantWeight.detShiftShape_shift` turns the carrier-level form
into the statement that the restriction depends on `λ` only through its class modulo the constant
weights `m·(1, …, 1)`, and `TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` says that
the polynomial part is a complete invariant of that class.  Those classes are indexed by the Young
diagrams of at most `n - 1` rows
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le_pred` and
`TauCeti.DominantWeight.detShiftShape_weightOfShape`), so the Weyl modules of such diagrams
already exhaust the restrictions.  On the bundled representations, where there is no carrier to
rewrite, that invariance is stated outright as `TauCeti.rationalWeylSLFDRep_shift`.

That these restrictions are *irreducible*, and that they exhaust the irreducible rational
representations of `SL n k`, is the highest-weight classification for `SL n` and is not proved
here; it needs more than the determinant twist, since recovering `GL n k` from `SL n k` and the
scalars asks every unit of `k` to be an `n`-th power.

## Main definitions

* `TauCeti.weylSLRepOfShape`: the Weyl module of a Young diagram, as a representation of
  `SL n k`, with `TauCeti.weylSLFDRepOfShape` its bundled form.
* `TauCeti.rationalWeylSLRep`: the rational Weyl module of a dominant weight, as a representation
  of `SL n k`, with `TauCeti.rationalWeylSLFDRep` its bundled form.

## Main results

* `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`: **the determinant twist disappears on
  `SL n k`** -- the rational Weyl module of `λ` restricts to the Weyl module of the polynomial
  part of `λ`.
* `TauCeti.rationalWeylSLFDRep_shift`: **the restriction only depends on `λ` modulo the constant
  weights**.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` over an algebraically closed field of characteristic zero are
  the determinant twists of the polynomial ones and the irreducible representations of `SL n` are
  indexed by the dominant weights modulo `(1, …, 1)`.
-/

public section

universe u

namespace TauCeti

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

/-- The restricted action of a rational Weyl module, read at the image of the matrix.

This is deliberately not a `simp` lemma: `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape` is the
normal form, and it already rewrites the left-hand side here. -/
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
`m·(1, …, 1)`, and `TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` says that the
polynomial part is a complete invariant of that class. -/
@[simp]
theorem rationalWeylSLRep_eq_weylSLRepOfShape (l : DominantWeight n) :
    rationalWeylSLRep k n l = weylSLRepOfShape k n l.detShiftShape := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  have hdet : (Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [rationalWeylSLRep_apply, weylSLRepOfShape_apply, rationalWeylRep_apply, hdet, one_zpow,
    Units.val_one, one_smul]

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

/-- **The restriction depends on the weight only modulo the constant weights**: `λ` and
`λ + m·(1, …, 1)` restrict to the same representation of `SL n k`.  Bundled as an equality of
`FDRep` objects this says so outright, with no carrier to rewrite by hand: the two sides are built
on the Weyl modules of the polynomial parts of `λ + m·(1, …, 1)` and of `λ`, which
`TauCeti.DominantWeight.detShiftShape_shift` identifies.  Together with
`TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff`, which says that the polynomial part
is a complete invariant of the class of `λ`, this is the sense in which the restricted rational
Weyl modules are indexed by the dominant weights modulo the constant weights. -/
@[simp]
theorem rationalWeylSLFDRep_shift (l : DominantWeight n) (m : ℤ) :
    rationalWeylSLFDRep k n (l.shift m) = rationalWeylSLFDRep k n l := by
  have key : ∀ l' : DominantWeight n,
      rationalWeylSLFDRep k n l' = weylSLFDRepOfShape k n l'.detShiftShape := fun l' => by
    rw [rationalWeylSLFDRep, rationalWeylSLRep_eq_weylSLRepOfShape]
  rw [key, key, DominantWeight.detShiftShape_shift]

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

end Field

end TauCeti
