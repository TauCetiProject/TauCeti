/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Etale.Field
public import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Smooth.Regular

/-!
# Geometrically regular algebras over a field

An algebra `B` over a field `k` is *geometrically regular* if `B` is Noetherian and the base
change `L ⊗[k] B` is a regular ring for every finite purely inseparable extension `L / k`
(Stacks, Definition 10.166.2, in the form of Lemma 10.166.1). Stacks, Lemma 10.166.1, shows that
this is equivalent to regularity of `L ⊗[k] B` for every finitely generated field extension
`L / k`; that equivalence is not proved here. Geometric regularity of the fibres is the condition
defining regular ring maps, G-rings and excellent rings.

Regularity of `B` itself does not suffice: a nontrivial finite purely inseparable extension `L / k`
is a field, hence regular, but `L ⊗[k] L` is not reduced, so `L` is not geometrically regular over
`k`.

## Main definitions and results

* `TauCeti.Excellence.GeometricallyRegular k B`: `B` is a geometrically regular `k`-algebra.
* `TauCeti.Excellence.GeometricallyRegular.isRegularRing`: a geometrically regular algebra is a
  regular ring.
* `AlgEquiv.geometricallyRegular`: geometric regularity is invariant under isomorphisms of
  `k`-algebras.
* `TauCeti.Excellence.GeometricallyRegular.of_smooth`: a smooth `k`-algebra is geometrically
  regular; this covers `k` itself, the zero algebra and polynomial rings in finitely many
  variables.
* `TauCeti.Excellence.GeometricallyRegular.of_isSeparable`: a finite separable field extension is
  geometrically regular.
* `TauCeti.Excellence.GeometricallyRegular.surjective_algebraMap_of_algHom`: a nonzero
  geometrically regular `k`-algebra receives no `k`-algebra map from a nontrivial finite purely
  inseparable extension of `k`.
* `TauCeti.Excellence.geometricallyRegular_iff_isSeparable`: a finite purely inseparable extension
  is geometrically regular exactly when it is separable, that is, trivial.
* `TauCeti.Excellence.geometricallyRegular_tensorProduct_iff_of_bijective`: geometric regularity
  is unchanged by base change along an isomorphism of fields `k → K`.
* `TauCeti.Excellence.GeometricallyRegular.of_isLocalization`: a localization of a field is
  geometrically regular.
* `TauCeti.Excellence.not_geometricallyRegular_trivSqZeroExt`: the dual numbers `k[ε]/(ε²)` are
  not geometrically regular.

## References

* The Stacks Project, Section 10.166 (Geometrically regular algebras), Lemma 10.166.1 and
  Definition 10.166.2.
-/

public section

universe u v w

open TensorProduct

namespace TauCeti.Excellence

/-- An algebra `B` over a field `k` is *geometrically regular* if `B` is Noetherian and
`L ⊗[k] B` is a regular ring for every finite purely inseparable field extension `L / k`
(Stacks, Definition 10.166.2, in the form of Lemma 10.166.1). The extensions `L` range over the
universe of `k`. -/
class GeometricallyRegular (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B] :
    Prop where
  /-- A geometrically regular algebra is Noetherian. -/
  isNoetherianRing : IsNoetherianRing B
  /-- The base change of a geometrically regular algebra to a finite purely inseparable extension
  of the base field is a regular ring. -/
  isRegularRing_tensorProduct (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
    [IsPurelyInseparable k L] : IsRegularRing (L ⊗[k] B)

attribute [instance] GeometricallyRegular.isRegularRing_tensorProduct

namespace GeometricallyRegular

variable {k : Type u} {B : Type v} {B' : Type w} [Field k] [CommRing B] [Algebra k B]
  [CommRing B'] [Algebra k B']

variable (k) in
/-- A geometrically regular algebra is a regular ring: take `L = k`. -/
theorem isRegularRing [GeometricallyRegular k B] : IsRegularRing B :=
  .of_ringEquiv (Algebra.TensorProduct.lid k B).toRingEquiv

/-- Geometric regularity is invariant under isomorphisms of `k`-algebras. -/
theorem _root_.AlgEquiv.geometricallyRegular (e : B ≃ₐ[k] B') [GeometricallyRegular k B] :
    GeometricallyRegular k B' where
  isNoetherianRing :=
    have := ‹GeometricallyRegular k B›.isNoetherianRing
    isNoetherianRing_of_ringEquiv B e.toRingEquiv
  isRegularRing_tensorProduct L _ _ _ _ :=
    .of_ringEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) e).toRingEquiv

/-- A smooth algebra over a field is geometrically regular: its base change to any field is smooth
over that field, hence regular. -/
instance (priority := 100) of_smooth [Algebra.Smooth k B] : GeometricallyRegular k B where
  isNoetherianRing := Algebra.FiniteType.isNoetherianRing k B
  isRegularRing_tensorProduct L _ _ _ _ := IsRegularRing.of_smooth (R := L)

/-- A finite separable field extension is geometrically regular, being étale over the base. -/
instance (priority := 100) of_isSeparable (K : Type v) [Field K] [Algebra k K] [Module.Finite k K]
    [Algebra.IsSeparable k K] : GeometricallyRegular k K :=
  have : Algebra.FormallyEtale k K := .of_isSeparable k K
  have : Algebra.Etale k K :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  inferInstance

/-- A nonzero geometrically regular `k`-algebra `B` receives no `k`-algebra map from a nontrivial
finite purely inseparable extension `L / k`: if `f : L →ₐ[k] B` exists, then `L = k`. Indeed
`L ⊗[k] L` embeds into the regular, hence reduced, ring `L ⊗[k] B`. -/
theorem surjective_algebraMap_of_algHom [GeometricallyRegular k B] [Nontrivial B] (L : Type u)
    [Field L] [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L] (f : L →ₐ[k] B) :
    Function.Surjective (algebraMap k L) :=
  have : IsReduced (L ⊗[k] L) :=
    isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k L) f)
      (TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id f.toRingHom.injective)
  IsPurelyInseparable.surjective_algebraMap_of_isReduced_tensorProduct k L

end GeometricallyRegular

/-- A finite purely inseparable extension `L / k` is geometrically regular if and only if it is
separable, that is, if and only if `L = k`. -/
theorem geometricallyRegular_iff_isSeparable {k : Type u} [Field k] (L : Type u) [Field L]
    [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L] :
    GeometricallyRegular k L ↔ Algebra.IsSeparable k L := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ .of_isSeparable L⟩
  have hs := GeometricallyRegular.surjective_algebraMap_of_algHom L (AlgHom.id k L)
  exact AlgEquiv.Algebra.isSeparable
    (AlgEquiv.ofBijective (Algebra.ofId k L) ⟨(algebraMap k L).injective, hs⟩)

/-- The dual numbers `k[ε]/(ε²)` over a field `k` are not geometrically regular: they are not even
reduced. -/
theorem not_geometricallyRegular_trivSqZeroExt (k : Type u) [Field k] :
    ¬ GeometricallyRegular k (TrivSqZeroExt k k) := by
  intro h
  have := h.isRegularRing k
  have hε : IsNilpotent (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) :=
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  simpa using congrArg TrivSqZeroExt.snd hε.eq_zero

/-- Geometric regularity does not see an isomorphism of base fields: if `algebraMap k K` is
bijective, then `K ⊗[k] B` is geometrically regular over `K` if and only if `B` is geometrically
regular over `k`. -/
theorem geometricallyRegular_tensorProduct_iff_of_bijective {k K : Type u} [Field k] [Field K]
    [Algebra k K] (h : Function.Bijective (algebraMap k K)) (B : Type v) [CommRing B]
    [Algebra k B] : GeometricallyRegular K (K ⊗[k] B) ↔ GeometricallyRegular k B := by
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) h
  let φ : K ⊗[k] B ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k B)
  refine ⟨fun hK ↦ ⟨?_, fun L _ _ _ _ ↦ ?_⟩, fun hk ↦ ⟨?_, fun L _ _ _ _ ↦ ?_⟩⟩
  · have := hK.isNoetherianRing
    exact isNoetherianRing_of_ringEquiv _ φ.toRingEquiv
  · -- Make `L` a `K`-algebra through `K ≃ k`, and cancel the base change along `k → K`.
    let : Algebra K L := ((algebraMap k L).comp e.symm.toRingHom).toAlgebra
    have : IsScalarTower k K L := .of_algebraMap_eq fun x ↦
      congrArg (algebraMap k L) (e.symm_apply_apply x).symm
    have : Module.Finite K L := .of_restrictScalars_finite k K L
    have : IsPurelyInseparable K L := .tower_top k K L
    exact .of_ringEquiv (Algebra.TensorProduct.cancelBaseChange k K K L B).toRingEquiv
  · have := hk.isNoetherianRing
    exact isNoetherianRing_of_ringEquiv _ φ.symm.toRingEquiv
  · let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    have : IsScalarTower k K L := .of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite k K := .of_surjective (Algebra.linearMap k K) h.2
    have : Module.Finite k L := .trans K L
    have : IsPurelyInseparable k K := e.isPurelyInseparable
    have : IsPurelyInseparable k L := .trans k K L
    exact .of_ringEquiv (Algebra.TensorProduct.cancelBaseChange k K K L B).symm.toRingEquiv

/-- A localization of a field `k` is geometrically regular over `k`: it is either zero or `k`
itself, and in both cases smooth over `k`. -/
theorem GeometricallyRegular.of_isLocalization {k : Type u} [Field k] (M : Submonoid k)
    (B : Type v) [CommRing B] [Algebra k B] [IsLocalization M B] : GeometricallyRegular k B := by
  by_cases h0 : (0 : k) ∈ M
  · have := IsLocalization.subsingleton (S := B) h0
    infer_instance
  · have : Algebra.Smooth k B := .of_equiv <| IsLocalization.atUnits k M (S := B) fun x hx ↦
      (isUnit_iff_ne_zero.mpr fun h ↦ h0 (h ▸ hx))
    infer_instance

/-! ### Checks -/

/-- A field is geometrically regular over itself. -/
example (k : Type u) [Field k] : GeometricallyRegular k k := inferInstance

/-- The zero algebra is geometrically regular. -/
example (k : Type u) [Field k] : GeometricallyRegular k (k ⧸ (⊤ : Ideal k)) := inferInstance

/-- Polynomial rings in finitely many variables are geometrically regular. -/
example (k : Type u) [Field k] (n : ℕ) : GeometricallyRegular k (MvPolynomial (Fin n) k) :=
  inferInstance

/-- A finite purely inseparable extension that is not separable is regular, being a field, but is
not geometrically regular. -/
example (k L : Type u) [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    [IsPurelyInseparable k L] (h : ¬ Algebra.IsSeparable k L) : ¬ GeometricallyRegular k L :=
  (geometricallyRegular_iff_isSeparable L).not.mpr h

end TauCeti.Excellence
