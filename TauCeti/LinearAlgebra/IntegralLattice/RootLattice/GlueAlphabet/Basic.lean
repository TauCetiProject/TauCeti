/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Dynkin

/-!
# The glue alphabet of a simply-laced Dynkin type

Gluing root lattices into overlattices (Conway--Sloane, Chapter 4 §3 and Chapter 16 §1) records a
glue vector by one label per component: the label of its class in the discriminant group
`A_Q = Q^∨ / Q` of that component's root lattice `Q`.  This file fixes, uniformly in the
simply-laced Dynkin type `t`, the finite quadratic module `t.glueAlphabet ht` in which these labels
live, and identifies it with the discriminant quadratic module of the root lattice
`t.rootLattice ht`:

| type | alphabet | generator values |
| --- | --- | --- |
| `Aₙ` | `ℤ/(n+1)` | `q(1) = n / (2(n+1))` |
| `Dₙ`, `n` even | `ℤ/2 × ℤ/2` | `q(1,0) = 1/2`, `q(0,1) = n/8`, `q(1,1) = n/8` |
| `Dₙ`, `n` odd | `ℤ/4` | `q(1) = n/8` |
| `E₆` | `ℤ/3` | `q(1) = 2/3` |
| `E₇` | `ℤ/2` | `q(1) = 3/4` |
| `E₈` | `ℤ/1` | none |

The values are half-norms `q(x + Q) = ⟨x, x⟩ / 2 mod ℤ`.  The alphabets are the presented models
already identified with the discriminant forms of the family-specific lattices:
`typeAStandardQuadraticModule`, `checkerboardStandardQuadraticModule`,
`checkerboardCyclicQuadraticModule`, `typeE₆StandardQuadraticModule` and
`typeE₇StandardQuadraticModule`.  The point of this file is the case split *once*: an ordered
list of ADE components is a list of Dynkin types, and products of alphabets, glue words and their
transport into the discriminant group of an orthogonal sum of root lattices are formed without a
further case split on each component.

The two parities of `Dₙ` give non-isomorphic groups, so the type-`D` alphabet is a dependent
`if` on `Even n`; `glueAlphabet_D_of_even` and `glueAlphabet_D_of_odd` identify it with the
corresponding model for a given parity.  Treating both as one cyclic `ℤ/4` would give the wrong
group for even `n`.

## Main declarations

* `TauCeti.DynkinType.glueAlphabet`: the glue alphabet of a simply-laced Dynkin type.
* `TauCeti.DynkinType.glueAlphabetIsometry`: for a valid simply-laced type, its isometry with the
  discriminant quadratic module of the root lattice.
* `TauCeti.DynkinType.glueAlphabetIsometry_A_apply`, `glueAlphabetIsometry_D_apply_of_even`,
  `glueAlphabetIsometry_D_apply_of_odd`, `glueAlphabetIsometry_E6_apply`,
  `glueAlphabetIsometry_E7_apply`: the isometry agrees with the family-specific identifications.
* `TauCeti.DynkinType.isNondegenerate_glueAlphabet`, `natCard_glueAlphabet`: the alphabet is
  nondegenerate, of order `|det t.cartanMatrix|`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  and Chapter 16, §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

/-- **The glue alphabet of a simply-laced Dynkin type**: the finite quadratic module of glue
labels for one component, namely `ℤ/(n+1)` for `Aₙ`, `ℤ/2 × ℤ/2` for `Dₙ` with `n` even, `ℤ/4` for
`Dₙ` with `n` odd, `ℤ/3` for `E₆`, `ℤ/2` for `E₇` and the trivial group for `E₈`, each with the
half-norm form of the discriminant of the root lattice
(`TauCeti.DynkinType.glueAlphabetIsometry`). -/
-- Exposing the body makes the carrier of `(A n).glueAlphabet ht` definitionally `ZMod (n + 1)`
-- (and similarly for the other types and for a concrete rank of `Dₙ`), as required to write and
-- evaluate glue labels as elements of these groups.
@[expose] noncomputable def glueAlphabet :
    (t : DynkinType) → t.IsSimplyLaced → FiniteQuadraticModule
  | A n, _ => typeAStandardQuadraticModule n
  | D n, _ =>
    if hn : Even n then checkerboardStandardQuadraticModule n hn
    else checkerboardCyclicQuadraticModule n
  | E6, _ => typeE₆StandardQuadraticModule
  | E7, _ => typeE₇StandardQuadraticModule
  | E8, _ => FiniteQuadraticModule.cyclic 1 0 (smul_zero _) (smul_zero _)
  | B n, h => absurd h (not_isSimplyLaced_B n)
  | C n, h => absurd h (not_isSimplyLaced_C n)
  | F4, h => absurd h not_isSimplyLaced_F4
  | G2, h => absurd h not_isSimplyLaced_G2

/-- The glue alphabet of `Aₙ` is the cyclic model `ℤ/(n+1)`. -/
@[simp]
theorem glueAlphabet_A (n : ℕ) (ht : (A n).IsSimplyLaced) :
    (A n).glueAlphabet ht = typeAStandardQuadraticModule n :=
  (rfl)

/-- For even `n`, the glue alphabet of `Dₙ` is the Klein four model `ℤ/2 × ℤ/2`. -/
@[simp]
theorem glueAlphabet_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Even n) :
    (D n).glueAlphabet ht = checkerboardStandardQuadraticModule n hn :=
  dite_eq_left hn

/-- For odd `n`, the glue alphabet of `Dₙ` is the cyclic model `ℤ/4`. -/
@[simp]
theorem glueAlphabet_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Odd n) :
    (D n).glueAlphabet ht = checkerboardCyclicQuadraticModule n :=
  dite_eq_right (Nat.not_even_iff_odd.mpr hn)

/-- The glue alphabet of `E₆` is the cyclic model `ℤ/3`. -/
@[simp]
theorem glueAlphabet_E6 (ht : E6.IsSimplyLaced) :
    E6.glueAlphabet ht = typeE₆StandardQuadraticModule :=
  (rfl)

/-- The glue alphabet of `E₇` is the cyclic model `ℤ/2`. -/
@[simp]
theorem glueAlphabet_E7 (ht : E7.IsSimplyLaced) :
    E7.glueAlphabet ht = typeE₇StandardQuadraticModule :=
  (rfl)

/-- The glue alphabet of `E₈` has a single element. -/
instance (ht : E8.IsSimplyLaced) : Subsingleton (E8.glueAlphabet ht) :=
  inferInstanceAs (Subsingleton (ZMod 1))

/-! The root lattices of `Aₙ`, `E₆`, `E₇` and `E₈` are equal to the family-specific simple-root
lattices on `Fin n → ℚ`, `Fin 6 → ℚ`, `Fin 7 → ℚ` and `Fin 8 → ℚ` (`rootLattice_A` and its
analogues), whereas `t.rootLattice ht` lives on `Fin t.rank → ℚ`.  Instance search does not unfold
`t.rank`, so the nondegeneracy instance is restated on the family-specific ambient spaces, for use
with `IntegralLattice.Isometry.ofEq` in this file. -/

private theorem isNondegenerate_rootLattice_A (n : ℕ) (ht : (A n).IsSimplyLaced) :
    @IsNondegenerate (Fin n → ℚ) _ (Pi.Function.module _ _ _) ((A n).rootLattice ht) :=
  inferInstanceAs ((A n).rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E6 (ht : E6.IsSimplyLaced) :
    @IsNondegenerate (Fin 6 → ℚ) _ (Pi.Function.module _ _ _) (E6.rootLattice ht) :=
  inferInstanceAs (E6.rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E7 (ht : E7.IsSimplyLaced) :
    @IsNondegenerate (Fin 7 → ℚ) _ (Pi.Function.module _ _ _) (E7.rootLattice ht) :=
  inferInstanceAs (E7.rootLattice ht).IsNondegenerate

private theorem isNondegenerate_rootLattice_E8 (ht : E8.IsSimplyLaced) :
    @IsNondegenerate (Fin 8 → ℚ) _ (Pi.Function.module _ _ _) (E8.rootLattice ht) :=
  inferInstanceAs (E8.rootLattice ht).IsNondegenerate

attribute [local instance] isNondegenerate_rootLattice_A isNondegenerate_rootLattice_E6
  isNondegenerate_rootLattice_E7 isNondegenerate_rootLattice_E8

/-- **The glue alphabet is the discriminant quadratic module of the root lattice.**  For a valid
simply-laced Dynkin type `t`, this is the isometry from `t.glueAlphabet ht` to the discriminant
form of `t.rootLattice ht` that carries the generator of `ℤ/(n+1)` for `Aₙ` to the class of the
first fundamental weight, the generators of `ℤ/2 × ℤ/2` (even `n`) or `ℤ/4` (odd `n`) for `Dₙ` to
the vector and spinor classes, respectively to the spinor class, and the generators for `E₆` and
`E₇` to the classes of the minuscule weights `ϖ₁` and `ϖ₇`. -/
noncomputable def glueAlphabetIsometry :
    (t : DynkinType) → t.Valid → (ht : t.IsSimplyLaced) →
      FiniteQuadraticModule.Isometry (t.glueAlphabet ht)
        ((t.rootLattice ht).discriminantQuadraticModule (t.isEven_rootLattice ht))
  | A n, _, ht => (typeADiscriminantQuadraticIsometry n).trans
      ((Isometry.ofEq (rootLattice_A n ht).symm).discriminantQuadraticIsometry
        (isEven_typeARootLattice n))
  | D n, hv, ht =>
    haveI : NeZero n := ⟨by have := valid_D.mp hv; omega⟩
    if hn : Even n then
      (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn)).trans <|
        (checkerboardDiscriminantQuadraticIsometry n hn).trans
          ((rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm.discriminantQuadraticIsometry
            (isEven_checkerboardLattice n))
    else
      (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn))).trans <|
        (checkerboardCyclicQuadraticIsometry n (Nat.not_even_iff_odd.mp hn)).trans
          ((rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm.discriminantQuadraticIsometry
            (isEven_checkerboardLattice n))
  | E6, _, ht => typeE₆DiscriminantQuadraticIsometry.trans
      ((Isometry.ofEq (rootLattice_E6 ht).symm).discriminantQuadraticIsometry
        isEven_typeE₆RootLattice)
  | E7, _, ht => typeE₇DiscriminantQuadraticIsometry.trans
      ((Isometry.ofEq (rootLattice_E7 ht).symm).discriminantQuadraticIsometry
        isEven_typeE₇RootLattice)
  | E8, _, ht =>
    haveI : Subsingleton
        (typeE₈RootLattice.discriminantQuadraticModule isEven_typeE₈RootLattice) :=
      inferInstanceAs (Subsingleton typeE₈RootLattice.DiscriminantGroup)
    FiniteQuadraticModule.Isometry.ofSubsingleton.trans
      ((Isometry.ofEq (rootLattice_E8 ht).symm).discriminantQuadraticIsometry
        isEven_typeE₈RootLattice)
  | B n, _, h => absurd h (not_isSimplyLaced_B n)
  | C n, _, h => absurd h (not_isSimplyLaced_C n)
  | F4, _, h => absurd h not_isSimplyLaced_F4
  | G2, _, h => absurd h not_isSimplyLaced_G2

/-- On `Aₙ`, the glue isometry is the cyclic identification `typeADiscriminantGroupEquiv`,
transported along `rootLattice_A`. -/
@[simp]
theorem glueAlphabetIsometry_A_apply (n : ℕ) (hv : (A n).Valid) (ht : (A n).IsSimplyLaced)
    (x : ZMod (n + 1)) :
    (A n).glueAlphabetIsometry hv ht x =
      (Isometry.ofEq (rootLattice_A n ht).symm).discriminantGroupEquiv
        (typeADiscriminantGroupEquiv n x) :=
  (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
    (congrArg _ (typeADiscriminantQuadraticIsometry_apply n x))

/-- On `Dₙ` with `n` even, the glue isometry is the Klein four identification
`zmodTwoProdAddEquivCheckerboardDiscriminantGroup`, transported along
`rootLatticeIsometryCheckerboard`. -/
@[simp]
theorem glueAlphabetIsometry_D_apply_of_even (n : ℕ) (hv : (D n).Valid)
    (ht : (D n).IsSimplyLaced) (hn : Even n) (x : (D n).glueAlphabet ht) :
    haveI : NeZero n := ⟨by have := valid_D.mp hv; omega⟩
    (D n).glueAlphabetIsometry hv ht x =
      (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm.discriminantGroupEquiv
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup n hn
          (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn) x)) := by
  have : NeZero n := ⟨by have := valid_D.mp hv; omega⟩
  simp only [glueAlphabetIsometry, dite_eq_left hn, FiniteQuadraticModule.Isometry.trans_apply]
  exact (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
    (congrArg _ (checkerboardDiscriminantQuadraticIsometry_apply n hn _))

/-- On `Dₙ` with `n` odd, the glue isometry is the cyclic identification
`zmodFourAddEquivCheckerboardDiscriminantGroup`, transported along
`rootLatticeIsometryCheckerboard`. -/
@[simp]
theorem glueAlphabetIsometry_D_apply_of_odd (n : ℕ) (hv : (D n).Valid)
    (ht : (D n).IsSimplyLaced) (hn : Odd n) (x : (D n).glueAlphabet ht) :
    (D n).glueAlphabetIsometry hv ht x =
      (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm.discriminantGroupEquiv
        (zmodFourAddEquivCheckerboardDiscriminantGroup n hn
          (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn) x)) := by
  have : NeZero n := ⟨by have := valid_D.mp hv; omega⟩
  simp only [glueAlphabetIsometry, dite_eq_right (Nat.not_even_iff_odd.mpr hn),
    FiniteQuadraticModule.Isometry.trans_apply]
  exact (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
    (congrArg _ (checkerboardCyclicQuadraticIsometry_apply n hn _))

/-- On `E₆`, the glue isometry is the cyclic identification `typeE₆DiscriminantGroupEquiv`,
transported along `rootLattice_E6`. -/
@[simp]
theorem glueAlphabetIsometry_E6_apply (hv : E6.Valid) (ht : E6.IsSimplyLaced) (x : ZMod 3) :
    E6.glueAlphabetIsometry hv ht x =
      (Isometry.ofEq (rootLattice_E6 ht).symm).discriminantGroupEquiv
        (typeE₆DiscriminantGroupEquiv x) :=
  (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
    (congrArg _ (typeE₆DiscriminantQuadraticIsometry_apply x))

/-- On `E₇`, the glue isometry is the cyclic identification `typeE₇DiscriminantGroupEquiv`,
transported along `rootLattice_E7`. -/
@[simp]
theorem glueAlphabetIsometry_E7_apply (hv : E7.Valid) (ht : E7.IsSimplyLaced) (x : ZMod 2) :
    E7.glueAlphabetIsometry hv ht x =
      (Isometry.ofEq (rootLattice_E7 ht).symm).discriminantGroupEquiv
        (typeE₇DiscriminantGroupEquiv x) :=
  (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
    (congrArg _ (typeE₇DiscriminantQuadraticIsometry_apply x))

/-- **The glue alphabet of a valid simply-laced type is nondegenerate**, being isometric to the
discriminant form of a nondegenerate lattice. -/
theorem isNondegenerate_glueAlphabet (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    (t.glueAlphabet ht).IsNondegenerate :=
  (t.glueAlphabetIsometry hv ht).isNondegenerate_iff.mpr
    (isNondegenerate_discriminantQuadraticModule _ _)

/-- **The glue alphabet has order `|det t.cartanMatrix|`**, the discriminant of the root
lattice. -/
theorem natCard_glueAlphabet (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Nat.card (t.glueAlphabet ht) = t.cartanMatrix.det.natAbs := by
  rw [Nat.card_congr (t.glueAlphabetIsometry hv ht).toLinearEquiv.toEquiv]
  exact (natCard_discriminantGroup _).trans
    ((discriminant_def _).trans (congrArg _ (t.determinant_rootLattice ht)))

end TauCeti.DynkinType
