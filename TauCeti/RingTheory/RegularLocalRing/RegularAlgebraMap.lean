/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.RegularLocalRing.GeometricallyRegular

/-!
# Regular ring maps

A ring map `R → B` is *regular* if `B` is flat over `R` and, for every prime `p` of `R`, the
fibre `κ(p) ⊗[R] B` is a geometrically regular `κ(p)`-algebra (Stacks, Definition 15.42.1). This
is the condition imposed on the formal fibres of G-rings, and hence of quasi-excellent and
excellent rings.

## Main definitions and results

* `TauCeti.Excellence.RegularAlgebraMap R B`: the structure map `R → B` is a regular ring map.
* `TauCeti.Excellence.regularAlgebraMap_iff_geometricallyRegular`: over a field `k`, a regular
  `k`-algebra is the same as a geometrically regular one.
* `TauCeti.Excellence.RegularAlgebraMap.of_smooth`: smooth algebras are regular, since their
  fibres are smooth over the residue fields.
* `TauCeti.Excellence.RegularAlgebraMap.of_isLocalization`: localizations are regular, for
  instance `R → R_p` and `ℤ → ℚ`.
* `AlgEquiv.regularAlgebraMap`: regularity is invariant under isomorphisms of `R`-algebras.

## References

* The Stacks Project, Section 15.42 (Regular ring maps), Definition 15.42.1.
-/

public section

universe u v w

open TensorProduct

namespace TauCeti.Excellence

/-- An `R`-algebra `B` is a *regular algebra*, or `R → B` is a *regular ring map*, if `B` is flat
over `R` and for every prime `p` of `R` the fibre `κ(p) ⊗[R] B` is geometrically regular over the
residue field `κ(p)` (Stacks, Definition 15.42.1). -/
class RegularAlgebraMap (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] :
    Prop where
  /-- A regular algebra is flat. -/
  flat : Module.Flat R B
  /-- The fibre of a regular algebra over a prime of the base is geometrically regular over the
  residue field. -/
  geometricallyRegular_fiber (p : Ideal R) [p.IsPrime] :
    GeometricallyRegular p.ResidueField (p.Fiber B)

attribute [instance] RegularAlgebraMap.flat RegularAlgebraMap.geometricallyRegular_fiber

/-- Over a field `k`, a regular `k`-algebra is the same as a geometrically regular one: flatness
is automatic and the only fibre is over the zero ideal, whose residue field is `k`. -/
theorem regularAlgebraMap_iff_geometricallyRegular (k : Type u) (B : Type v) [Field k]
    [CommRing B] [Algebra k B] : RegularAlgebraMap k B ↔ GeometricallyRegular k B := by
  have h (p : Ideal k) [p.IsPrime] : Function.Bijective (algebraMap k p.ResidueField) := by
    obtain rfl := Ideal.eq_bot_of_prime p
    exact ⟨(algebraMap k _).injective, Ideal.algebraMap_residueField_surjective ⊥⟩
  refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨inferInstance, fun p _ ↦ ?_⟩⟩
  · exact (geometricallyRegular_tensorProduct_iff_of_bijective (h ⊥) B).mp inferInstance
  · exact (geometricallyRegular_tensorProduct_iff_of_bijective (h p) B).mpr inferInstance

namespace RegularAlgebraMap

variable {R : Type u} {B : Type v} {B' : Type w} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing B'] [Algebra R B']

/-- A smooth algebra is regular: it is flat, and its fibres are smooth over the residue fields,
hence geometrically regular. -/
instance (priority := 100) of_smooth [Algebra.Smooth R B] : RegularAlgebraMap R B where
  flat := inferInstance
  geometricallyRegular_fiber _ _ := inferInstance

/-- A localization of `R` is a regular `R`-algebra: it is flat, and its fibres are localizations
of the residue fields. -/
theorem of_isLocalization (M : Submonoid R) [IsLocalization M B] : RegularAlgebraMap R B where
  flat := IsLocalization.flat B M
  geometricallyRegular_fiber p _ :=
    .of_isLocalization (Algebra.algebraMapSubmonoid p.ResidueField M) (p.Fiber B)

/-- The localization `Localization M` is a regular `R`-algebra. -/
instance localization (M : Submonoid R) : RegularAlgebraMap R (Localization M) :=
  of_isLocalization M

/-- Regularity of an algebra is invariant under isomorphisms of `R`-algebras. -/
theorem _root_.AlgEquiv.regularAlgebraMap (e : B ≃ₐ[R] B') [RegularAlgebraMap R B] :
    RegularAlgebraMap R B' where
  flat := .of_linearEquiv e.symm.toLinearEquiv
  geometricallyRegular_fiber p _ :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] _)
      e).geometricallyRegular

end RegularAlgebraMap

/-! ### Checks -/

/-- A ring is regular over itself. -/
example (R : Type u) [CommRing R] : RegularAlgebraMap R R := inferInstance

/-- The zero algebra is regular. -/
example (R : Type u) [CommRing R] : RegularAlgebraMap R (R ⧸ (⊤ : Ideal R)) := inferInstance

/-- The rationals are a regular `ℤ`-algebra, although they are not of finite type over `ℤ`. -/
example : RegularAlgebraMap ℤ ℚ := .of_isLocalization (nonZeroDivisors ℤ)

/-- Polynomial rings in finitely many variables are regular. -/
example (R : Type u) [CommRing R] (n : ℕ) : RegularAlgebraMap R (MvPolynomial (Fin n) R) :=
  inferInstance

/-- The dual numbers `k[ε]/(ε²)` are flat over the field `k`, but their fibre is not
geometrically regular, so they are not a regular `k`-algebra. -/
example (k : Type u) [Field k] : ¬ RegularAlgebraMap k (TrivSqZeroExt k k) :=
  (regularAlgebraMap_iff_geometricallyRegular k _).not.mpr
    (not_geometricallyRegular_trivSqZeroExt k)

end TauCeti.Excellence
