/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Smooth
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Tame fixed-point closed subgroups of affine group schemes

Let `H` be a commutative Hopf algebra over a commutative ring `R` and
`ρ : Θ →* CategoryTheory.Aut H` an action of a monoid `Θ` by Hopf algebra automorphisms.
Contravariantly, `Θ` acts on the affine group scheme `Spec H` by group-scheme automorphisms. This
file constructs the closed fixed-point subgroup scheme `(Spec H)^Θ` and proves Edixhoven's tame
smoothness theorem for it.

On coordinate algebras, each `θ : Θ` defines the equalizer Hopf ideal
`equalizerHopfIdeal (ρ θ).asIso.hom (𝟙 H)`. Taking the supremum over `Θ` gives a single Hopf ideal
`TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal ρ`, whose underlying ring ideal coincides with the
coinvariant displacement ideal
`Algebra.fixedPointIdeal ((CommHopfAlgCat.autToAlgEquivHom H).comp ρ)`
(`fixedPointsHopfIdeal_toIdeal`, `sub_mem_fixedPointsHopfIdeal`, `fixedPointsHopfIdeal_le_iff`).
When `ρ` is trivial, this Hopf ideal vanishes and the quotient is canonically isomorphic to `H`
(`fixedPointsHopfIdeal_eq_bot_iff`, `fixedPointsHopfIdeal_one`, `fixedPointsTrivialIso`). On
`A`-points, the subgroup cut out by `fixedPointsHopfIdeal ρ` is the subgroup of points fixed by
every `θ : Θ` (`mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff`,
`range_mapDomain_mkQuotient_fixedPointsHopfIdeal`). When `Θ` is a group whose order `Nat.card Θ` is
invertible in `R` and `H` is smooth over `R`, the fixed-point quotient Hopf algebra is smooth over
`R` (`smooth_quotient_fixedPointsHopfIdeal`).

For a finite-type commutative Hopf algebra `H : FiniteTypeCommHopfAlgCat R`, forgetting the
finite-type witness on automorphisms via `autObjHom` produces the quotient
`FiniteTypeCommHopfAlgCat.fixedPoints ρ` with quotient morphism `mkFixedPoints ρ`, packaging
`(Spec H)^Θ` as a finite-type closed subgroup (`fixedPointsHopfIdeal`, `mkFixedPoints_surjective`,
`range_mapDomain_mkFixedPoints`, `fixedPointsTrivialIso`). Then
`smoothCommHopfAlgProperty_fixedPoints` and `smooth_fixedPoints` establish Edixhoven's group-scheme
theorem: when `Nat.card Θ` is invertible in `k` and `H` is smooth, `H^Θ` is represented by a smooth
closed subgroup.

Two concrete involutions illustrate both connected and disconnected fixed-point subgroups:
* For any commutative Hopf `R`-algebra `H`, swapping the tensor factors of `H ⊗[R] H` via
  `CommHopfAlgCat.tensorSwapAut H` cuts out the kernel of multiplication, so the fixed-point
  quotient is canonically isomorphic to the diagonal `H` (`CommHopfAlgCat.fixedPointsTensorSwapIso`)
  and inherits connectedness of `PrimeSpectrum H`
  (`CommHopfAlgCat.connectedSpace_primeSpectrum_fixedPoints_tensorSwapAut`).
* On the multiplicative group `R[T;T⁻¹]`, inversion `T n ↦ T (-n)`
  (`MultiplicativeGroup.inversionAut`) cuts out `{u : Aˣ | u⁻¹ = u}` on `A`-points
  (`mem_fixedPoints_inversionAut_iff`). Over any commutative ring `R` with `2` invertible, this
  fixed-point subgroup is smooth (`smooth_fixedPoints_inversionAut`) and has disconnected prime
  spectrum (`not_connectedSpace_primeSpectrum_fixedPoints_inversionAut`); when `R` is nontrivial, it
  contains the distinct `R`-points `1` and `-1` (`exists_ne_mem_fixedPoints_inversionAut`).

## Main definitions

* `CommHopfAlgCat.autToAlgEquivHom`: forgetful group homomorphism
  `CategoryTheory.Aut H →* (H ≃ₐ[R] H)`.
* `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal` and
  `TauCeti.CommHopfAlgCat.fixedPointsTrivialIso`: the Hopf ideal cutting out `Θ`-fixed points of
  `Spec H`, and the canonical isomorphism `H ⧸ fixedPointsHopfIdeal ρ ≅ H` for `ρ = 1`.
* `TauCeti.FiniteTypeCommHopfAlgCat.autObjHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointsHopfIdeal`,
  `TauCeti.FiniteTypeCommHopfAlgCat.fixedPoints`,
  `TauCeti.FiniteTypeCommHopfAlgCat.mkFixedPoints`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointsTrivialIso`: the forgetful automorphism homomorphism,
  finite-type fixed-point quotient, quotient morphism, and trivial-action isomorphism.
* `CommHopfAlgCat.tensorSwapAut` and `CommHopfAlgCat.fixedPointsTensorSwapIso`: the factor-swapping
  `ℤ/2ℤ`-action on `H ⊗[R] H` and the isomorphism of its fixed-point quotient with `H`.
* `TauCeti.MultiplicativeGroup.inversionAut`: the inversion `ℤ/2ℤ`-action on `R[T;T⁻¹]`.

## Main results

* `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_toIdeal`,
  `TauCeti.CommHopfAlgCat.sub_mem_fixedPointsHopfIdeal`,
  `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_le_iff`,
  `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_eq_bot_iff`, and
  `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal_one`: algebraic characterization of
  `fixedPointsHopfIdeal`.
* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff` and
  `TauCeti.CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointsHopfIdeal`: point-level
  identification of the fixed-point closed subgroup.
* `TauCeti.CommHopfAlgCat.smooth_quotient_fixedPointsHopfIdeal`,
  `TauCeti.FiniteTypeCommHopfAlgCat.mkFixedPoints_surjective`,
  `TauCeti.FiniteTypeCommHopfAlgCat.range_mapDomain_mkFixedPoints`,
  `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: Edixhoven's tame fixed-point smoothness
  theorem for affine group schemes.
* `CommHopfAlgCat.connectedSpace_primeSpectrum_fixedPoints_tensorSwapAut`: the fixed-point subgroup
  of the factor swap on `H ⊗[R] H` has connected prime spectrum whenever `H` does.
* `TauCeti.MultiplicativeGroup.mem_fixedPoints_inversionAut_iff`,
  `TauCeti.MultiplicativeGroup.smooth_fixedPoints_inversionAut`,
  `TauCeti.MultiplicativeGroup.exists_ne_mem_fixedPoints_inversionAut`, and
  `TauCeti.MultiplicativeGroup.not_connectedSpace_primeSpectrum_fixedPoints_inversionAut`: points,
  smoothness, two `R`-points, and disconnectedness for inversion on `𝔾ₘ`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Prop. 3.1
  (p. 293) and Prop. 3.4 (pp. 294–295).
-/

public noncomputable section

open CategoryTheory TensorProduct WithConv
open scoped LaurentPolynomial

universe u v w w'

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Forget the coalgebra structure on an automorphism of `H : CommHopfAlgCat R` to obtain an
`R`-algebra automorphism of `H`. -/
def autToAlgEquivHom (H : CommHopfAlgCat.{v} R) :
    CategoryTheory.Aut H →* (H ≃ₐ[R] H) where
  toFun e := (CommHopfAlgCat.ofIso e.asIso).toAlgEquiv
  map_one' := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl

/-- `autToAlgEquivHom H e` evaluates via `e.asIso.hom.hom`. -/
@[simp]
theorem autToAlgEquivHom_apply (H : CommHopfAlgCat.{v} R) (e : CategoryTheory.Aut H) (a : H) :
    autToAlgEquivHom H e a = e.asIso.hom.hom a :=
  (rfl)

end CommHopfAlgCat

namespace TauCeti

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R} {Θ : Type w} [Monoid Θ]

/-- The **fixed-point Hopf ideal** of an action `ρ : Θ →* CategoryTheory.Aut H`: the supremum of the
equalizer Hopf ideals `equalizerHopfIdeal (ρ θ).asIso.hom (𝟙 H)` over all `θ : Θ`. Contravariantly,
its quotient represents the closed fixed-point subgroup `(Spec H)^Θ`. -/
def fixedPointsHopfIdeal (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal R H :=
  ⨆ θ : Θ, equalizerHopfIdeal (ρ θ).asIso.hom (𝟙 H)

/-- The ideal underlying `fixedPointsHopfIdeal ρ` coincides with the coinvariant displacement ideal
`Algebra.fixedPointIdeal ((autToAlgEquivHom H).comp ρ)`. -/
@[simp]
theorem fixedPointsHopfIdeal_toIdeal (ρ : Θ →* CategoryTheory.Aut H) :
    (fixedPointsHopfIdeal ρ).toIdeal = Algebra.fixedPointIdeal ((autToAlgEquivHom H).comp ρ) := by
  rw [fixedPointsHopfIdeal, HopfIdeal.iSup_toIdeal, Algebra.fixedPointIdeal_def]
  refine iSup_congr fun θ ↦ ?_
  rw [equalizerHopfIdeal_toIdeal, HopfIdeal.equalizerIdeal_eq_span]
  rfl

/-- Every displacement `(ρ θ).asIso.hom.hom a - a` belongs to `fixedPointsHopfIdeal ρ`. -/
theorem sub_mem_fixedPointsHopfIdeal (ρ : Θ →* CategoryTheory.Aut H) (θ : Θ) (a : H) :
    (ρ θ).asIso.hom.hom a - a ∈ fixedPointsHopfIdeal ρ := by
  rw [← HopfIdeal.mem_toIdeal, fixedPointsHopfIdeal_toIdeal]
  exact Algebra.sub_mem_fixedPointIdeal ((autToAlgEquivHom H).comp ρ) θ a

/-- `fixedPointsHopfIdeal ρ` is contained in a Hopf ideal `J` if and only if every displacement
`(ρ θ).asIso.hom.hom a - a` lies in `J`. -/
theorem fixedPointsHopfIdeal_le_iff {ρ : Θ →* CategoryTheory.Aut H} {J : HopfIdeal R H} :
    fixedPointsHopfIdeal ρ ≤ J ↔ ∀ (θ : Θ) (a : H), (ρ θ).asIso.hom.hom a - a ∈ J := by
  rw [← HopfIdeal.toIdeal_le_toIdeal, fixedPointsHopfIdeal_toIdeal, Algebra.fixedPointIdeal_le_iff]
  rfl

/-- `fixedPointsHopfIdeal ρ` vanishes if and only if the action `ρ` is trivial. -/
@[simp]
theorem fixedPointsHopfIdeal_eq_bot_iff (ρ : Θ →* CategoryTheory.Aut H) :
    fixedPointsHopfIdeal ρ = ⊥ ↔ ρ = 1 := by
  rw [eq_bot_iff, fixedPointsHopfIdeal_le_iff]
  constructor
  · intro h
    ext θ : 1
    apply CategoryTheory.Aut.isoEquiv.injective
    apply CategoryTheory.Iso.ext
    apply _root_.CommHopfAlgCat.hom_ext
    ext a
    exact sub_eq_zero.1 (HopfIdeal.mem_bot.1 (h θ a))
  · rintro rfl θ a
    simp

/-- The trivial action cuts out the zero Hopf ideal. -/
@[simp]
theorem fixedPointsHopfIdeal_one :
    fixedPointsHopfIdeal (1 : Θ →* CategoryTheory.Aut H) = ⊥ :=
  (fixedPointsHopfIdeal_eq_bot_iff _).2 rfl

/-- When `ρ = 1`, the fixed-point quotient `quotient H (fixedPointsHopfIdeal ρ)` is canonically
isomorphic to `H`. -/
def fixedPointsTrivialIso {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    quotient H (fixedPointsHopfIdeal ρ) ≅ H :=
  eqToIso (congrArg (quotient H) ((fixedPointsHopfIdeal_eq_bot_iff ρ).2 hρ)) ≪≫ quotientBotIso H

/-- On `A`-points, the closed subgroup cut out by `fixedPointsHopfIdeal ρ` consists of the points
fixed by every `θ : Θ`. -/
@[simp]
theorem mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff (ρ : Θ →* CategoryTheory.Aut H)
    (A : CommAlgCat.{w'} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    x ∈ quotientPointsSubgroup H (fixedPointsHopfIdeal ρ) A ↔
      ∀ θ : Θ, BialgHom.mapDomain (ρ θ).asIso.hom.hom x = x := by
  rw [mem_quotientPointsSubgroup_iff]
  have hker : (∀ h : H, h ∈ fixedPointsHopfIdeal ρ → x.ofConv h = 0) ↔
      (fixedPointsHopfIdeal ρ).toIdeal ≤ RingHom.ker (x.ofConv : H →ₐ[R] A).toRingHom :=
    ⟨fun h y hy ↦ RingHom.mem_ker.2 (h y (HopfIdeal.mem_toIdeal.1 hy)),
      fun h y hy ↦ RingHom.mem_ker.1 (h (HopfIdeal.mem_toIdeal.2 hy))⟩
  rw [hker, fixedPointsHopfIdeal_toIdeal, Algebra.fixedPointIdeal_le_ker_iff]
  refine forall_congr' fun θ ↦ ?_
  constructor
  · intro h
    apply ofConv_injective
    ext a
    simpa only [BialgHom.mapDomain_apply_apply, MonoidHom.comp_apply, autToAlgEquivHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h a
  · intro h a
    simpa only [BialgHom.mapDomain_apply_apply, MonoidHom.comp_apply, autToAlgEquivHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv a) h

/-- The image of `BialgHom.mapDomain (mkQuotient H (fixedPointsHopfIdeal ρ)).hom` on `A`-points is
the set of `Θ`-fixed points of `H(A)`. -/
theorem range_mapDomain_mkQuotient_fixedPointsHopfIdeal (ρ : Θ →* CategoryTheory.Aut H)
    (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointsHopfIdeal ρ)).hom) =
      {g | ∀ θ : Θ, BialgHom.mapDomain (A := A) (ρ θ).asIso.hom.hom g = g} := by
  ext g
  exact (mem_range_quotientPointsHom_iff H (fixedPointsHopfIdeal ρ) (CommAlgCat.of R A) g).trans <|
    (mem_quotientPointsSubgroup_iff H (fixedPointsHopfIdeal ρ) (CommAlgCat.of R A) g).symm.trans
      (mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff ρ (CommAlgCat.of R A) g)

/-- **Edixhoven's tame fixed-point smoothness theorem for commutative Hopf algebras.** If `Θ` is a
group with `IsUnit (Nat.card Θ : R)` acting on a smooth commutative Hopf `R`-algebra `H`, then the
fixed-point quotient `quotient H (fixedPointsHopfIdeal ρ)` is smooth over `R` (Edixhoven,
Props. 3.1 and 3.4, pp. 293–295). -/
theorem smooth_quotient_fixedPointsHopfIdeal {Θ : Type w} [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) [Algebra.Smooth R H] (hΘ : IsUnit (Nat.card Θ : R)) :
    Algebra.Smooth R (quotient H (fixedPointsHopfIdeal ρ)) := by
  have _ : Algebra.Smooth R (H ⧸ Algebra.fixedPointIdeal ((autToAlgEquivHom H).comp ρ)) :=
    TauCeti.Algebra.smooth_quotient_fixedPointIdeal ((autToAlgEquivHom H).comp ρ) hΘ
  exact Algebra.Smooth.of_equiv
    (Ideal.quotientEquivAlgOfEq R (fixedPointsHopfIdeal_toIdeal ρ)).symm

end CommHopfAlgCat

end TauCeti

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The involutive `ℤ/2ℤ`-action on `H ⊗[R] H` exchanging the two tensor factors via
`Bialgebra.TensorProduct.comm`. Contravariantly, `ℤ/2ℤ` swaps the two factors of
`Spec H × Spec H`. -/
def tensorSwapAut (H : CommHopfAlgCat.{v} R) :
    Multiplicative (ZMod 2) →* CategoryTheory.Aut (CommHopfAlgCat.of R (H ⊗[R] H)) :=
  (zmodMonoidHomEquiv 2
    (CategoryTheory.Aut (CommHopfAlgCat.of R (H ⊗[R] H)))).symm
    ⟨CategoryTheory.Aut.of (CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.comm R H H)), by
      rw [sq]
      apply CategoryTheory.Aut.isoEquiv.injective
      apply CategoryTheory.Iso.ext
      apply CommHopfAlgCat.hom_ext
      apply BialgHom.coe_toAlgHom_injective
      exact Algebra.TensorProduct.ext' fun _ _ ↦ rfl⟩

private theorem kerOfSurjective_mulBialgHom_eq_fixedPointsHopfIdeal_tensorSwapAut
    (H : CommHopfAlgCat.{v} R)
    (hsurj : Function.Surjective (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H)).hom) :
    HopfIdeal.kerOfSurjective (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H)).hom hsurj =
      fixedPointsHopfIdeal (tensorSwapAut H) := by
  have hact : (autToAlgEquivHom (CommHopfAlgCat.of R (H ⊗[R] H))).comp (tensorSwapAut H) =
      TauCeti.Algebra.tensorSwapAction R H := by
    apply (zmodMonoidHomEquiv 2 ((H ⊗[R] H) ≃ₐ[R] (H ⊗[R] H))).injective
    apply Subtype.ext
    rw [coe_zmodMonoidHomEquiv_apply, coe_zmodMonoidHomEquiv_apply, MonoidHom.comp_apply,
      TauCeti.Algebra.tensorSwapAction_ofAdd_one, tensorSwapAut,
      zmodMonoidHomEquiv_symm_apply_ofAdd_one]
    apply AlgEquiv.coe_toAlgHom_injective
    exact Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  have hI : (HopfIdeal.kerOfSurjective
      (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H)).hom hsurj).toIdeal =
      (fixedPointsHopfIdeal (tensorSwapAut H)).toIdeal := by
    rw [HopfIdeal.kerOfSurjective_toIdeal, fixedPointsHopfIdeal_toIdeal, hact,
      TauCeti.Algebra.fixedPointIdeal_tensorSwapAction]
    rfl
  ext z
  exact HopfIdeal.mem_toIdeal.symm.trans (by rw [hI]; exact HopfIdeal.mem_toIdeal)

/-- **Fixed points of the factor swap on `H ⊗[R] H`.** Exchanging the two factors of
`Spec H × Spec H` cuts out the diagonal closed subgroup, so the fixed-point quotient of `H ⊗[R] H`
is canonically isomorphic as a commutative Hopf algebra to `H`. -/
def fixedPointsTensorSwapIso (H : CommHopfAlgCat.{v} R) :
    quotient (CommHopfAlgCat.of R (H ⊗[R] H)) (fixedPointsHopfIdeal (tensorSwapAut H)) ≅ H :=
  have hsurj : Function.Surjective (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H)).hom :=
    fun a ↦ ⟨a ⊗ₜ[R] (1 : H), mul_one a⟩
  Hom.quotientIsoOfKerOfSurjectiveEq (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H)) hsurj
    (kerOfSurjective_mulBialgHom_eq_fixedPointsHopfIdeal_tensorSwapAut H hsurj)

/-- Whenever `PrimeSpectrum H` is connected, the fixed-point quotient of `H ⊗[R] H` under the
factor swap also has connected prime spectrum. -/
theorem connectedSpace_primeSpectrum_fixedPoints_tensorSwapAut
    (H : CommHopfAlgCat.{v} R) [ConnectedSpace (PrimeSpectrum H)] :
    ConnectedSpace (PrimeSpectrum
      (quotient (CommHopfAlgCat.of R (H ⊗[R] H)) (fixedPointsHopfIdeal (tensorSwapAut H)))) :=
  (Homeomorph.connectedSpace_iff (PrimeSpectrum.homeomorphOfRingEquiv
    (CommHopfAlgCat.ofIso (fixedPointsTensorSwapIso H)).toAlgEquiv.toRingEquiv)).2 ‹_›

end CommHopfAlgCat

namespace TauCeti

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Forget the finite-type witness on an automorphism of `H : FiniteTypeCommHopfAlgCat R` to obtain
an automorphism of the underlying `H.obj : CommHopfAlgCat R`. -/
def autObjHom (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    CategoryTheory.Aut H →* CategoryTheory.Aut H.obj where
  toFun e := .of
    { hom := e.asIso.hom.hom
      inv := e.asIso.inv.hom
      hom_inv_id := congrArg (fun q ↦ q.hom) e.asIso.hom_inv_id
      inv_hom_id := congrArg (fun q ↦ q.hom) e.asIso.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The fixed-point Hopf ideal of `H.obj` associated to an action `ρ : Θ →* CategoryTheory.Aut H` on
a finite-type commutative Hopf algebra `H`. -/
def fixedPointsHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal R H.obj :=
  CommHopfAlgCat.fixedPointsHopfIdeal ((autObjHom H).comp ρ)

/-- The fixed-point quotient of `H : FiniteTypeCommHopfAlgCat R` under
`ρ : Θ →* CategoryTheory.Aut H`, representing the closed fixed-point subgroup `(Spec H)^Θ`. -/
abbrev fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : FiniteTypeCommHopfAlgCat.{u, v} R :=
  quotient H (fixedPointsHopfIdeal ρ)

/-- The quotient morphism `H ⟶ fixedPoints ρ` in `FiniteTypeCommHopfAlgCat R`. -/
abbrev mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : H ⟶ fixedPoints ρ :=
  mkQuotient H (fixedPointsHopfIdeal ρ)

/-- The coordinate morphism `mkFixedPoints ρ` onto the fixed-point quotient is surjective. -/
theorem mkFixedPoints_surjective {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : Function.Surjective (mkFixedPoints ρ).hom.hom :=
  _root_.CommHopfAlgCat.mkQuotient_surjective H.obj (fixedPointsHopfIdeal ρ)

/-- On `A`-points, the image of `mkFixedPoints ρ` is the set of `Θ`-fixed points of `H(A)`. -/
theorem range_mapDomain_mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w}
    [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) ((mkFixedPoints ρ).hom.hom : (H : Type v) →ₐc[R] _)) =
      {g | ∀ θ : Θ,
        BialgHom.mapDomain (A := A) ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[R] H) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointsHopfIdeal ((autObjHom H).comp ρ) A

/-- For a trivial action `ρ = 1`, `fixedPoints ρ` is canonically isomorphic to `H`. -/
def fixedPointsTrivialIso {H : FiniteTypeCommHopfAlgCat.{u, v} R} {Θ : Type w} [Monoid Θ]
    {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) : fixedPoints ρ ≅ H :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.fixedPointsTrivialIso (by rw [hρ, MonoidHom.comp_one])

/-- If `Θ` is a group with `IsUnit (Nat.card Θ : R)` acting on a smooth finite-type commutative
Hopf algebra `H`, then `(fixedPoints ρ).obj` satisfies `smoothCommHopfAlgProperty R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Group Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hH : smoothCommHopfAlgProperty R H.obj) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (fixedPoints ρ).obj := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  exact CommHopfAlgCat.smooth_quotient_fixedPointsHopfIdeal ((autObjHom H).comp ρ) hΘ

/-- **Edixhoven's tame fixed-point theorem for affine group schemes.** Fixed points of a group `Θ`
with `IsUnit (Nat.card Θ : k)` acting on a smooth affine group scheme of finite type over `k` are
represented by a smooth closed subgroup (Edixhoven, Props. 3.1 and 3.4, pp. 293–295). -/
theorem smooth_fixedPoints {k : Type u} [CommRing k]
    (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) (Θ : Type w) [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (R : Type w') [CommRing R] [Algebra k R],
        Set.range (BialgHom.mapDomain (A := R) (f.hom.hom : (H : Type v) →ₐc[k] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := R)
              ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[k] H) g = g} :=
  ⟨fixedPoints ρ, mkFixedPoints ρ, smoothCommHopfAlgProperty_fixedPoints ρ hH hΘ,
    mkFixedPoints_surjective ρ, range_mapDomain_mkFixedPoints ρ⟩

end FiniteTypeCommHopfAlgCat

namespace MultiplicativeGroup

section Inversion

/-- The involutive `ℤ/2ℤ`-action on `R[T;T⁻¹]` given on Laurent monomials by `T n ↦ T (-n)`,
corresponding contravariantly to group-scheme inversion `g ↦ g⁻¹` on `𝔾ₘ`. -/
def inversionAut (R : Type u) [CommRing R] :
    Multiplicative (ZMod 2) →* CategoryTheory.Aut (_root_.CommHopfAlgCat.of R R[T;T⁻¹]) :=
  (zmodMonoidHomEquiv 2
    (CategoryTheory.Aut (_root_.CommHopfAlgCat.of R R[T;T⁻¹]))).symm
    ⟨CategoryTheory.Aut.of
        (_root_.CommHopfAlgCat.isoMk (AddMonoidAlgebra.domCongrBialgEquiv R R (AddEquiv.neg ℤ))),
      by
        rw [sq]
        apply CategoryTheory.Aut.isoEquiv.injective
        apply CategoryTheory.Iso.ext
        apply _root_.CommHopfAlgCat.hom_ext
        apply BialgHom.coe_toAlgHom_injective
        exact congrArg AlgEquiv.toAlgHom
          ((AddMonoidAlgebra.trans_domCongr_domCongr (AddEquiv.neg ℤ) (AddEquiv.neg ℤ)).trans <|
            (congrArg (AddMonoidAlgebra.domCongr R R) (AddEquiv.ext neg_neg)).trans
              AddMonoidAlgebra.domCongr_refl)⟩

private theorem mapDomain_domCongr_neg_eq_inv {R : Type u} [CommRing R] {A : Type v}
    [CommRing A] [Algebra R A] (x : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A)
        (BialgHom.mapDomain (AddMonoidAlgebra.domCongrBialgEquiv R R (AddEquiv.neg ℤ)).toBialgHom
          x) = (pointsMulEquiv (R := R) (A := A) x)⁻¹ := by
  apply Units.ext
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply, laurentEvalEquiv_symm_apply,
    laurentEvalEquiv_symm_apply_inv, BialgHom.mapDomain_apply_apply]
  exact congrArg x.ofConv (AddMonoidAlgebra.domCongr_single (R := R) (AddEquiv.neg ℤ) (1 : ℤ) 1)

/-- On `A`-points, the fixed-point subgroup of `𝔾ₘ` under `inversionAut R` consists of the units
`u : Aˣ` satisfying `u⁻¹ = u` (that is, `μ₂(A)`). -/
theorem mem_fixedPoints_inversionAut_iff {R : Type u} [CommRing R] (A : CommAlgCat.{v} R)
    (x : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.of R R[T;T⁻¹]) A) :
    x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
          (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)) A ↔
      (pointsMulEquiv (R := R) (A := A) x)⁻¹ = pointsMulEquiv (R := R) (A := A) x := by
  constructor
  · intro hx
    have hgen := (CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff
      (inversionAut R) A x).1 hx (.ofAdd 1)
    rw [inversionAut, zmodMonoidHomEquiv_symm_apply_ofAdd_one] at hgen
    exact (mapDomain_domCongr_neg_eq_inv x).symm.trans
      (congrArg (pointsMulEquiv (R := R) (A := A)) hgen)
  · intro h
    have h1 : BialgHom.mapDomain (inversionAut R (.ofAdd 1)).asIso.hom.hom x = x := by
      rw [inversionAut, zmodMonoidHomEquiv_symm_apply_ofAdd_one]
      exact (pointsMulEquiv (R := R) (A := A)).injective
        ((mapDomain_domCongr_neg_eq_inv x).trans h)
    have hker : (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)).toIdeal ≤
        RingHom.ker (x.ofConv : R[T;T⁻¹] →ₐ[R] A).toRingHom := by
      rw [CommHopfAlgCat.fixedPointsHopfIdeal_toIdeal,
        TauCeti.Algebra.fixedPointIdeal_eq_span_of_mem_zpowers _ (.ofAdd 1)
          Multiplicative.mem_zpowers_ofAdd_one, Ideal.span_le, Set.range_subset_iff]
      intro p
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MonoidHom.comp_apply,
        _root_.CommHopfAlgCat.autToAlgEquivHom_apply (_root_.CommHopfAlgCat.of R R[T;T⁻¹])]
      simpa only [BialgHom.mapDomain_apply_apply] using
        congrArg (fun m : WithConv (R[T;T⁻¹] →ₐ[R] A) ↦ m.ofConv p) h1
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    exact fun p hp ↦ RingHom.mem_ker.1 (hker (HopfIdeal.mem_toIdeal.2 hp))

/-- When `2` is invertible in `R`, the fixed-point quotient of `R[T;T⁻¹]` under inversion (`μ₂`) is
smooth over `R`. -/
theorem smooth_fixedPoints_inversionAut {R : Type u} [CommRing R] (h2 : IsUnit (2 : R)) :
    Algebra.Smooth R
      (_root_.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R))) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  exact CommHopfAlgCat.smooth_quotient_fixedPointsHopfIdeal (inversionAut R) (by rwa [hcard])

/-- Over a nontrivial commutative ring `R` in which `2` is invertible, the fixed-point subgroup of
`𝔾ₘ` under inversion contains two distinct `R`-points corresponding to `1` and `-1`. -/
theorem exists_ne_mem_fixedPoints_inversionAut {R : Type u} [CommRing R] [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ∃ x y : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (CommAlgCat.of R R),
      x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
            (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)) (CommAlgCat.of R R) ∧
      y ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
            (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)) (CommAlgCat.of R R) ∧
      x ≠ y := by
  refine ⟨(pointsMulEquiv (R := R) (A := R)).symm 1,
    (pointsMulEquiv (R := R) (A := R)).symm (-1), ?_, ?_, ?_⟩
  · rw [mem_fixedPoints_inversionAut_iff, MulEquiv.apply_symm_apply, inv_one]
  · rw [mem_fixedPoints_inversionAut_iff, MulEquiv.apply_symm_apply]
    exact Units.ext (by simp)
  · intro heq
    have hval : (1 : R) = -1 :=
      congrArg Units.val ((pointsMulEquiv (R := R) (A := R)).symm.injective heq)
    have h2zero : (2 : R) = 0 := by
      calc (2 : R) = 1 + 1 := one_add_one_eq_two.symm
        _ = 1 + (-1) := by rw [← hval]
        _ = 0 := add_neg_cancel 1
    exact h2.ne_zero h2zero

private theorem laurentEval_eq_zero_of_mem_fixedPointsHopfIdeal_inversionAut
    {R : Type u} [CommRing R] (u : Rˣ) (hu : u⁻¹ = u) {q : R[T;T⁻¹]}
    (hq : q ∈ (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)).toIdeal) :
    laurentEval (R := R) u q = 0 := by
  have hpt : (pointsMulEquiv (R := R) (A := R)).symm u ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)) (CommAlgCat.of R R) := by
    rw [mem_fixedPoints_inversionAut_iff, MulEquiv.apply_symm_apply, hu]
  simpa [pointsMulEquiv_symm_apply] using
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 hpt q
      (HopfIdeal.mem_toIdeal.1 hq)

private theorem isIdempotentElem_inversionAut_projector {R : Type u} [CommRing R]
    (h2 : IsUnit (2 : R)) :
    IsIdempotentElem (Ideal.Quotient.mk
      (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)).toIdeal
      (LaurentPolynomial.C (↑h2.unit⁻¹ : R) * (1 + LaurentPolynomial.T 1))) := by
  let I := (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)).toIdeal
  have hT : (inversionAut R (.ofAdd 1)).asIso.hom.hom (LaurentPolynomial.T 1) =
      LaurentPolynomial.T (-1) := by
    rw [inversionAut, zmodMonoidHomEquiv_symm_apply_ofAdd_one]
    exact AddMonoidAlgebra.domCongr_single (R := R) (AddEquiv.neg ℤ) (1 : ℤ) 1
  let t : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mk I (LaurentPolynomial.T 1)
  have ht_sq : t * t = 1 := by
    have ht_inv : Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) = t := by
      rw [← hT, Ideal.Quotient.eq]
      exact HopfIdeal.mem_toIdeal.2
        (CommHopfAlgCat.sub_mem_fixedPointsHopfIdeal (inversionAut R) (.ofAdd 1) _)
    calc t * t = Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) * t := by rw [ht_inv]
      _ = Ideal.Quotient.mk I (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) :=
          (map_mul _ _ _).symm
      _ = 1 := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, map_one]
  let c : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mk I (LaurentPolynomial.C (↑h2.unit⁻¹ : R))
  have hc2 : 2 * c = 1 := by
    have h2mk : (2 : R[T;T⁻¹] ⧸ I) = Ideal.Quotient.mk I (LaurentPolynomial.C 2) :=
      (map_ofNat (Ideal.Quotient.mk I) 2).symm.trans
        (congrArg (Ideal.Quotient.mk I) (map_ofNat LaurentPolynomial.C 2).symm)
    rw [h2mk, ← map_mul, ← map_mul, IsUnit.mul_val_inv h2, map_one, map_one]
  have he_eq : Ideal.Quotient.mk I
      (LaurentPolynomial.C (↑h2.unit⁻¹ : R) * (1 + LaurentPolynomial.T 1)) = c * (1 + t) := by
    simp [c, t]
  rw [IsIdempotentElem, he_eq]
  calc (c * (1 + t)) * (c * (1 + t)) = c * c * (1 + 2 * t + t * t) := by ring
    _ = c * (2 * c) * (1 + t) := by rw [ht_sq]; ring
    _ = c * (1 + t) := by rw [hc2, mul_one]

/-- **Disconnectedness of the fixed-point subgroup of `𝔾ₘ` under inversion.** Over any commutative
ring `R` with `2` invertible, the prime spectrum of the fixed-point quotient of `R[T;T⁻¹]` under
inversion is not connected. -/
theorem not_connectedSpace_primeSpectrum_fixedPoints_inversionAut {R : Type u} [CommRing R]
    (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace (PrimeSpectrum
      (_root_.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)))) := by
  intro hconn
  let I := (CommHopfAlgCat.fixedPointsHopfIdeal (inversionAut R)).toIdeal
  let _ : ConnectedSpace (PrimeSpectrum (R[T;T⁻¹] ⧸ I)) := hconn
  have _ : Nontrivial (R[T;T⁻¹] ⧸ I) := PrimeSpectrum.nonempty_iff_nontrivial.1 hconn.toNonempty
  have _ : Nontrivial R := (algebraMap R (R[T;T⁻¹] ⧸ I)).domain_nontrivial
  -- Evaluate on `I` at `1` and `-1` to rule out `mk I p = 0` and `mk I p = 1`.
  rcases (isIdempotentElem_inversionAut_projector h2).eq_zero_or_eq_one_of_preconnectedSpace with
    he0 | he1
  · have h0 := laurentEval_eq_zero_of_mem_fixedPointsHopfIdeal_inversionAut 1 inv_one
      (Ideal.Quotient.eq_zero_iff_mem.1 he0)
    simp only [map_mul, map_add, map_one, AlgHom.apply_laurentPolynomial_C_self,
      laurentEval_T_one, Units.val_one, one_add_one_eq_two] at h0
    rw [mul_comm, IsUnit.mul_val_inv h2] at h0
    exact one_ne_zero h0
  · have h1 := laurentEval_eq_zero_of_mem_fixedPointsHopfIdeal_inversionAut (-1)
      (Units.ext (by simp)) (Ideal.Quotient.eq.1 he1)
    simp only [map_sub, map_mul, map_add, map_one, AlgHom.apply_laurentPolynomial_C_self,
      laurentEval_T_one, Units.val_neg, Units.val_one, add_neg_cancel, mul_zero, zero_sub,
      neg_eq_zero] at h1
    exact one_ne_zero h1

end Inversion

end MultiplicativeGroup

end TauCeti
