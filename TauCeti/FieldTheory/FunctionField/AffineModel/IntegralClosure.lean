/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
-- Proof-only: Dedekind integral closures without separability.
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
-- Proof-only: finiteness of the normalization of `k[x]` without separability.
import TauCeti.RingTheory.IntegralClosure.MvPolynomial

/-!
# The affine model `R_x`: the integral closure of `k[x]`

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The integral
closure

`R_x = integralClosure k[x] F`

of the polynomial ring `k[x] = Algebra.adjoin k {x}` in `F` is the standard **affine model** of
`F / k` attached to `x`: the coordinate ring of the part of the curve where `x` has no pole. This
file shows that `R_x` has every property the affine-model API of
`TauCeti/FieldTheory/FunctionField/AffineModel/` asks of a model, with no separability hypothesis
on `F / k(x)`:

* `R_x` is a Dedekind domain with fraction field `F`, and a finitely generated `k`-algebra;
* its functions are exactly those whose poles are among the poles of `x`, that is, `R_x` is the
  holomorphy ring of the places at which `x` is regular;
* hence its finite chart consists of the places at which `x` has no pole, and those places are in
  bijection with the height one primes of `R_x`.

The places missing from the finite chart are the poles of `x`, of which there are finitely many
(`TauCeti.Place.finite_setOf_ord_neg`).

## Main results

* `TauCeti.isDedekindDomain_integralClosure_adjoin` and
  `TauCeti.isFractionRing_integralClosure_adjoin`: `R_x` is a Dedekind domain with fraction field
  `F`.
* `TauCeti.finiteType_integralClosure_adjoin`: `R_x` is a finitely generated `k`-algebra.
* `TauCeti.isDedekindDomain_holomorphyRing_setOf_mem` and
  `TauCeti.finiteType_holomorphyRing_setOf_mem`: the same two properties for `R_x` presented as
  the holomorphy ring of the places at which `x` is regular, the form in which it is a chart of
  the scheme of `F` in `TauCeti/AlgebraicGeometry/Curves/TwoChartModel/`.
* `TauCeti.restrictScalars_integralClosure_adjoin_eq_holomorphyRing` and
  `TauCeti.mem_integralClosure_adjoin_iff`: a function lies in `R_x` exactly when it is regular at
  every place at which `x` is regular.
* `TauCeti.isIntegral_map_holomorphyRing_setOf_mem`: a ring map out of `R_x` that sends the
  constants and `x` to integral elements sends all of `R_x` to integral elements.
* `TauCeti.Place.forall_algebraMap_mem_integers_integralClosure_adjoin_iff`: a place is finite on
  `R_x` exactly when `x` has no pole there.
* `TauCeti.integralClosureAdjoinHeightOneSpectrumEquiv`: the places at which `x` has no pole are in
  bijection with the height one primes of `R_x`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2.
-/

public section

open IsDedekindDomain

open scoped _root_.IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### The finite chart of `R_x` -/

namespace Place

/-- **The finite chart of `R_x`**: a place `P` is finite on the integral closure of `k[x]` in `F`
exactly when `x` has no pole at `P`. -/
@[simp]
theorem forall_algebraMap_mem_integers_integralClosure_adjoin_iff (P : Place k F) {x : F} :
    (∀ a ∈ integralClosure (Algebra.adjoin k {x}) F, P.valuation a ≤ 1) ↔
      x ∈ P.integers :=
  ⟨fun h ↦ by
      rw [P.mem_integers_iff]
      exact h x ((integralClosure (Algebra.adjoin k {x}) F).algebraMap_mem
        ⟨x, Algebra.self_mem_adjoin_singleton k x⟩),
    fun hx a ha ↦ by
      rw [← P.mem_integers_iff]
      exact P.mem_integers_of_isIntegral_adjoin hx ha⟩

end Place

/-! ### `R_x` as a holomorphy ring -/

/-- **`R_x` is the holomorphy ring of the places at which `x` is regular** (Stichtenoth,
Section III.2): the integral closure of `k[x]` in `F` consists of the functions of `F` that are
regular wherever `x` is. This is Stichtenoth's Theorem 3.2.6 for `k[x]`, whose functions are all
regular at a place exactly when `x` is. -/
theorem restrictScalars_integralClosure_adjoin_eq_holomorphyRing (hF : IsFunctionField k F)
    (x : F) :
    (integralClosure (Algebra.adjoin k {x}) F).restrictScalars k =
      holomorphyRing {P : Place k F | x ∈ P.integers} := by
  rw [restrictScalars_integralClosure_eq_holomorphyRing hF]
  congr 1
  ext P
  exact P.adjoin_le_integers_iff

/-- **A function is integral over `k[x]` exactly when its poles are among the poles of `x`**: it
lies in `R_x` exactly when it is regular at every place at which `x` is regular. -/
theorem mem_integralClosure_adjoin_iff (hF : IsFunctionField k F) {x z : F} :
    z ∈ integralClosure (Algebra.adjoin k {x}) F ↔
      ∀ P : Place k F, x ∈ P.integers → z ∈ P.integers := by
  rw [← Subalgebra.mem_restrictScalars k,
    restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF, mem_holomorphyRing_iff]
  rfl

/-- **A ring map out of `R_x` is integral wherever it is integral on `k[x]`**: if a ring
homomorphism from the functions regular wherever `x` is sends the constants and `x` to elements
integral over `R`, then it sends every such function to an element integral over `R`. These
functions form the integral closure of `k[x]` in `F`. -/
theorem isIntegral_map_holomorphyRing_setOf_mem (hF : IsFunctionField k F) {x : F}
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (φ : holomorphyRing {P : Place k F | x ∈ P.integers} →+* S)
    (hk : ∀ c : k, IsIntegral R (φ (algebraMap k _ c)))
    (hx : IsIntegral R (φ ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩))
    (z : holomorphyRing {P : Place k F | x ∈ P.integers}) : IsIntegral R (φ z) := by
  let A := holomorphyRing {P : Place k F | x ∈ P.integers}
  have hBA : Algebra.adjoin k {x} ≤ A :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (mem_holomorphyRing_iff.mpr fun _ hP ↦ hP))
  let ι := Subalgebra.inclusion hBA
  let _ : Algebra (Algebra.adjoin k {x}) A := ι.toRingHom.toAlgebra
  -- `z` is integral over `k[x]` inside `F`, hence inside `A`.
  have hzF : IsIntegral (Algebra.adjoin k {x}) (z : F) := (mem_integralClosure_iff _ _).mp <|
    (Subalgebra.ext_iff.mp (restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF x) z).mpr
      z.2
  let val : A →ₐ[Algebra.adjoin k {x}] F := { A.val.toRingHom with commutes' := fun _ ↦ rfl }
  have hz : IsIntegral (Algebra.adjoin k {x}) z :=
    (isIntegral_algHom_iff val Subtype.val_injective).mp hzF
  -- `φ` sends `k[x]`, generated by the constants and `x`, to elements integral over `R`.
  have hB (b : Algebra.adjoin k {x}) : φ (ι b) ∈ integralClosure R S := by
    obtain ⟨b, hb⟩ := b
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hx
    | algebraMap c => exact hk c
    | add y w hy hw hy' hw' =>
      rw [← AddMemClass.mk_add_mk (hx := hy) (hy := hw), map_add, map_add]
      exact add_mem hy' hw'
    | mul y w hy hw hy' hw' =>
      rw [← MulMemClass.mk_mul_mk (hx := hy) (hy := hw), map_mul, map_mul]
      exact mul_mem hy' hw'
  exact isIntegral_trans _ (hz.map_of_comp_eq ((φ.comp ι.toRingHom).codRestrict _ hB) φ rfl)

/-! ### `R_x` is an affine model -/

section Model

variable {x : F}

open _root_.IntermediateField.algebraAdjoinAdjoin

/-- **`R_x` is a Dedekind domain**: the integral closure of `k[x]` in an algebraic function field
`F`, for `x` transcendental over `k`. No separability of `F / k(x)` is assumed. -/
theorem isDedekindDomain_integralClosure_adjoin (hF : IsFunctionField k F)
    (hx : Transcendental k x) : IsDedekindDomain (integralClosure (Algebra.adjoin k {x}) F) := by
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  -- `k[x] ≅ k[X]` is a principal ideal domain, hence Dedekind.
  have : IsPrincipalIdealRing (Algebra.adjoin k {x}) :=
    .of_surjective _ (Polynomial.algEquivOfTranscendental k x hx).surjective
  exact integralClosure.isDedekindDomain _ k⟮x⟯ F

/-- **`F` is the field of fractions of `R_x`**, for `x ∈ F` transcendental over `k` in an
algebraic function field `F`. -/
theorem isFractionRing_integralClosure_adjoin (hF : IsFunctionField k F)
    (hx : Transcendental k x) : IsFractionRing (integralClosure (Algebra.adjoin k {x}) F) F := by
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  exact integralClosure.isFractionRing_of_finite_extension k⟮x⟯ F

/-- **`R_x` is a finitely generated `k`-algebra**: for `x` transcendental over `k` and `F` finite
over `k(x)`, for instance an algebraic function field, the integral closure of `k[x]` in `F` is a
finite `k[x]`-module. No separability of `F / k(x)` is assumed. -/
theorem finiteType_integralClosure_adjoin [FiniteDimensional k⟮x⟯ F] (hx : Transcendental k x) :
    Algebra.FiniteType k (integralClosure (Algebra.adjoin k {x}) F) := by
  have : Module.Finite (Algebra.adjoin k {x}) (integralClosure (Algebra.adjoin k {x}) F) :=
    IsIntegralClosure.finite_adjoin_of_transcendental k hx F _
  have : Algebra.FiniteType k (Algebra.adjoin k {x}) :=
    .adjoin_of_finite (Set.finite_singleton x)
  exact .trans (S := Algebra.adjoin k {x}) inferInstance inferInstance

/-- **The functions regular wherever `x` is form a Dedekind domain**, for `x` transcendental over
`k`: this holomorphy ring is `R_x`. -/
theorem isDedekindDomain_holomorphyRing_setOf_mem (hF : IsFunctionField k F)
    (hx : Transcendental k x) :
    IsDedekindDomain (holomorphyRing {P : Place k F | x ∈ P.integers}) := by
  rw [← restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF x]
  exact isDedekindDomain_integralClosure_adjoin hF hx

/-- **The functions regular wherever `x` is form a finitely generated `k`-algebra**, for `x`
transcendental over `k`: this holomorphy ring is `R_x`. -/
theorem finiteType_holomorphyRing_setOf_mem (hF : IsFunctionField k F)
    (hx : Transcendental k x) :
    Algebra.FiniteType k (holomorphyRing {P : Place k F | x ∈ P.integers}) := by
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  rw [← restrictScalars_integralClosure_adjoin_eq_holomorphyRing hF x]
  exact finiteType_integralClosure_adjoin hx

end Model

/-! ### Places and height one primes of `R_x` -/

section HeightOneSpectrum

variable (x : F) [IsDedekindDomain (integralClosure (Algebra.adjoin k {x}) F)]
  [IsFractionRing (integralClosure (Algebra.adjoin k {x}) F) F]

/-- **The places at which `x` has no pole are the height one primes of `R_x`** (Stichtenoth,
Section III.2). -/
noncomputable def integralClosureAdjoinHeightOneSpectrumEquiv :
    {P : Place k F // x ∈ P.integers} ≃
      HeightOneSpectrum (integralClosure (Algebra.adjoin k {x}) F) :=
  (Equiv.subtypeEquivRight fun P ↦
      (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff).symm.trans (by
        simp only [Subalgebra.algebraMap_apply, Place.mem_integers_iff, Subtype.forall])).trans
    (Place.heightOneSpectrumEquiv k F _)

@[simp]
theorem integralClosureAdjoinHeightOneSpectrumEquiv_apply
    (P : {P : Place k F // x ∈ P.integers}) :
    integralClosureAdjoinHeightOneSpectrumEquiv x P =
      (P : Place k F).center
        (fun r : integralClosure (Algebra.adjoin k {x}) F ↦ (P : Place k F).mem_integers_iff.mpr
          ((P : Place k F).forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr P.2
            (r : F) r.2)) :=
  Place.heightOneSpectrumEquiv_apply k F _

@[simp]
theorem coe_integralClosureAdjoinHeightOneSpectrumEquiv_symm_apply
    (𝔭 : HeightOneSpectrum (integralClosure (Algebra.adjoin k {x}) F)) :
    ((integralClosureAdjoinHeightOneSpectrumEquiv x).symm 𝔭 : Place k F) =
      Place.ofPrime k F 𝔭 :=
  Place.coe_heightOneSpectrumEquiv_symm_apply k F 𝔭

end HeightOneSpectrum

end TauCeti
