/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.RegularLocalRing.GeometricallyRegular

import TauCeti.RingTheory.Flat.Tower
import TauCeti.RingTheory.RegularLocalRing.Descent

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
* `TauCeti.Excellence.RegularAlgebraMap.localization_base`: an algebra regular over `R` is regular
  over any localization of `R` through which its structure map factors, for instance over a ring
  isomorphic to `R`.
* `TauCeti.Excellence.RegularAlgebraMap.isRegularRing`: a Noetherian regular algebra over a regular
  ring is a regular ring.
* `TauCeti.Excellence.RegularAlgebraMap.of_faithfullyFlat`: if `R → C` is regular and `C` is
  faithfully flat over an intermediate `R`-algebra `B`, then `R → B` is regular.
* `RingEquiv.regularAlgebraMap_adicCompletion`: regularity of the completion map `A → Â` along an
  ideal is transported along a ring isomorphism matching the ideals.
* `Ideal.regularAlgebraMap_adicCompletion_of_isAdicComplete`: the completion map of a ring along an
  ideal it is complete for is regular.

## References

* The Stacks Project, Section 15.42 (Regular ring maps), Definition 15.42.1 and Lemma 15.42.7
  (Tag 07NT).
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

/-- Regularity of an algebra passes to a localization of the base: if `R'` is a localization of
`R` at `M` and `B` is an `R'`-algebra that is regular over `R`, then `B` is regular over `R'`.
Taking `M = IsUnit.submonoid R`, this covers a ring `R'` isomorphic to `R`. -/
theorem localization_base {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' B]
    [IsScalarTower R R' B] (M : Submonoid R) [IsLocalization M R'] [RegularAlgebraMap R B] :
    RegularAlgebraMap R' B where
  flat := (Module.flat_iff_of_isLocalization R' M B).mpr inferInstance
  geometricallyRegular_fiber p' _ := by
    let p := p'.comap (algebraMap R R')
    let : Algebra p.ResidueField p'.ResidueField :=
      (Ideal.ResidueField.map p p' (algebraMap R R') rfl).toAlgebra
    have : IsScalarTower R p.ResidueField p'.ResidueField := .of_algebraMap_eq fun r ↦
      (IsScalarTower.algebraMap_apply R R' _ r).trans
        (Ideal.ResidueField.map_algebraMap p p' _ rfl r).symm
    have hκ : Function.Bijective (algebraMap p.ResidueField p'.ResidueField) :=
      (RingHom.surjectiveOnStalks_of_isLocalization M R').residueFieldMap_bijective p p' rfl
    have := (geometricallyRegular_tensorProduct_iff_of_bijective hκ (p.Fiber B)).mpr inferInstance
    have : TensorProduct.CompatibleSMul R R' p'.ResidueField B :=
      IsLocalization.tensorProduct_compatibleSMul M R' _ _
    -- `κ(p') ⊗[κ(p)] (κ(p) ⊗[R] B) ≃ κ(p') ⊗[R] B ≃ κ(p') ⊗[R'] B` as `κ(p')`-algebras.
    exact ((Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
      p'.ResidueField B).trans (Algebra.TensorProduct.equivOfCompatibleSMul R R'
        p'.ResidueField p'.ResidueField B).symm).geometricallyRegular

/-- A Noetherian regular algebra over a regular ring is a regular ring: its fibres are
geometrically regular, hence regular. -/
theorem isRegularRing [IsRegularRing R] [IsNoetherianRing B] [RegularAlgebraMap R B] :
    IsRegularRing B :=
  IsRegularRing.of_flat_of_isRegularRing_fiber (R := R) fun p _ ↦
    GeometricallyRegular.isRegularRing p.ResidueField

/-- **Regularity descends along faithfully flat maps.** If `R → B → C` are ring maps such that
`R → C` is regular and `C` is faithfully flat over `B`, then `R → B` is regular
(Stacks, Tag 07NT). Faithful flatness cannot be weakened to flatness: the punctured cusp
`k[t, t⁻¹]` is smooth over `k` and flat over the cusp `k[x, y] ⧸ (y² - x³)`. -/
theorem of_faithfullyFlat (C : Type w) [CommRing C] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [Module.FaithfullyFlat B C] [RegularAlgebraMap R C] :
    RegularAlgebraMap R B := by
  have := Module.Flat.of_faithfullyFlat_of_flat R B C
  refine ⟨inferInstance, fun p _ ↦ ?_⟩
  -- `L ⊗[κ(p)] (κ(p) ⊗[R] B) ≃ L ⊗[R] B` is regular for every finite purely inseparable `L`.
  have key (L : Type u) [Field L] [Algebra p.ResidueField L] [Module.Finite p.ResidueField L]
      [IsPurelyInseparable p.ResidueField L] : IsRegularRing (L ⊗[p.ResidueField] p.Fiber B) := by
    let : Algebra R L := ((algebraMap p.ResidueField L).comp (algebraMap R _)).toAlgebra
    have : IsScalarTower R p.ResidueField L := .of_algebraMap_eq fun _ ↦ rfl
    have : IsRegularRing (L ⊗[R] C) := .of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField L L C).toRingEquiv
    have : IsRegularRing (L ⊗[R] B) := TauCeti.IsRegularRing.tensorProduct_of_faithfullyFlat L C
    exact .of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField L L B).symm.toRingEquiv
  -- Taking `L = κ(p)` shows that the fibre itself is regular, in particular Noetherian.
  have := (key p.ResidueField).toIsNoetherian
  exact ⟨isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.lid p.ResidueField (p.Fiber B)).toRingEquiv, key⟩

end RegularAlgebraMap

/-! ### Completion maps -/

/-- Regularity of the completion map `A → Â` along an ideal `I` is transported along a ring
isomorphism `e : A ≃+* A'` carrying `I` onto `I'`: then `A' → Â'` along `I'` is regular. For local
rings and their maximal ideals, `IsLocalRing.map_ringEquiv_maximalIdeal e` supplies the
hypothesis. -/
theorem _root_.RingEquiv.regularAlgebraMap_adicCompletion {A : Type u} {A' : Type v}
    [CommRing A] [CommRing A'] (e : A ≃+* A') {I : Ideal A} {I' : Ideal A'} (he : I.map e = I')
    [RegularAlgebraMap A (AdicCompletion I A)] :
    RegularAlgebraMap A' (AdicCompletion I' A') := by
  let : Algebra A A' := e.toRingHom.toAlgebra
  let e' : A ≃ₐ[A] A' := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have := (AdicCompletion.congrₐ e' he).regularAlgebraMap
  have : IsLocalization (IsUnit.submonoid A) A' :=
    .of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le e.bijective
  exact .localization_base (IsUnit.submonoid A)

/-- The completion map `A → Â` of a ring along an ideal `I` for which `A` is `I`-adically complete
is regular, being an isomorphism. -/
theorem _root_.Ideal.regularAlgebraMap_adicCompletion_of_isAdicComplete {A : Type u} [CommRing A]
    (I : Ideal A) [IsAdicComplete I A] : RegularAlgebraMap A (AdicCompletion I A) :=
  (AdicCompletion.ofAlgEquiv I).regularAlgebraMap

/-! ### Checks -/

/-- A ring is regular over itself. -/
example (R : Type u) [CommRing R] : RegularAlgebraMap R R := inferInstance

/-- The zero algebra is regular. -/
example (R : Type u) [CommRing R] : RegularAlgebraMap R (R ⧸ (⊤ : Ideal R)) := inferInstance

/-- The rationals are a regular `ℤ`-algebra, although they are not of finite type over `ℤ`. -/
example : RegularAlgebraMap ℤ ℚ := .of_isLocalization (nonZeroDivisors ℤ)

/-- Polynomial rings in finitely many variables over `R` are regular `R`-algebras. -/
example (R : Type u) [CommRing R] (n : ℕ) : RegularAlgebraMap R (MvPolynomial (Fin n) R) :=
  inferInstance

/-- Regularity of `R → B` descends from the polynomial ring `B[X]`, which is free, hence faithfully
flat, over a nontrivial ring `B`. -/
example (R B : Type u) [CommRing R] [CommRing B] [Nontrivial B] [Algebra R B]
    [RegularAlgebraMap R (Polynomial B)] : RegularAlgebraMap R B :=
  .of_faithfullyFlat (Polynomial B)

/-- The dual numbers `k[ε]/(ε²)` are flat over the field `k`, but their fibre is not
geometrically regular, so they are not a regular `k`-algebra. -/
example (k : Type u) [Field k] : ¬ RegularAlgebraMap k (TrivSqZeroExt k k) :=
  (regularAlgebraMap_iff_geometricallyRegular k _).not.mpr
    (not_geometricallyRegular_trivSqZeroExt k)

end TauCeti.Excellence
