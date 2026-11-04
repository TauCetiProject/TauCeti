/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DedekindDomain.Basic

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Stalks at a generization

Let `X` be a scheme and `x ⤳ y` a specialization, so that `x` is a generization of `y`. The
specialization map `𝒪_{X,y} ⟶ 𝒪_{X,x}` identifies `𝒪_{X,x}` with the localization of `𝒪_{X,y}`
at the prime `𝔮` lying under the maximal ideal of `𝒪_{X,x}`, and `𝔮` is the maximal ideal of
`𝒪_{X,y}` only when `x = y`. On an affine open `Spec R` containing `y` these are the facts that
`R_q` is the localization of `R_p` at `q R_p` for primes `q ⊆ p`, and that `q R_p` determines `q`.

When every nonzero prime of `𝒪_{X,y}` is maximal (`Ring.DimensionLEOne`) and `x ≠ y`, the prime
`𝔮` is therefore zero: the residue field `κ(x)` is the fraction field of `𝒪_{X,y}`. Without a
domain assumption this is stronger than Krull dimension at most one. For a point `y` of
codimension one with `𝒪_{X,y}` a discrete valuation ring this identifies the field `K_y` of
Stacks, Section 58.31, with the residue field at the generic point of `Spec 𝒪_{X,y}`, which is
how ramification along `y` of a cover defined over a neighbourhood of that generic point is read
off.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isLocalization_stalkSpecializes`: `𝒪_{X,x}` is the
  localization of `𝒪_{X,y}` at the prime under its maximal ideal.
* `TauCeti.AlgebraicGeometry.Scheme.comap_stalkSpecializes_maximalIdeal_eq_iff`: that prime is
  the maximal ideal of `𝒪_{X,y}` iff `x = y`.
* `TauCeti.AlgebraicGeometry.Scheme.comap_germ_comap_stalkSpecializes_maximalIdeal`: on an affine
  open containing `y`, that prime pulls back to the prime ideal of `x`.
* `TauCeti.AlgebraicGeometry.Scheme.specializes_of_comap_stalkSpecializes_maximalIdeal_le`: the
  primes of `𝒪_{X,y}` of two generizations of `y` are ordered as the generizations are.
* `TauCeti.AlgebraicGeometry.Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq_span_singleton`:
  on a locally Noetherian integral scheme, every prime element of `𝒪_{X,y}` generates the prime of
  a codimension-one generization of `y`, by Krull's principal ideal theorem.
* `TauCeti.AlgebraicGeometry.Scheme.isFractionRing_residueField_of_specializes`: if every
  nonzero prime of `𝒪_{X,y}` is maximal and `x ≠ y`, then `κ(x)` is a fraction field of
  `𝒪_{X,y}`.
* `TauCeti.AlgebraicGeometry.Scheme.algebraMap_stalkSpecializes` and
  `TauCeti.AlgebraicGeometry.Scheme.stalkSpecializes_injective`: on an irreducible scheme the
  specialization map is compatible with the maps to the function field, and on an integral scheme
  it is injective.

## References

* [Stacks Project, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE), the field `K_ξ`
  attached to a codimension-one point `ξ` with discrete valuation ring stalk.
-/

public section

open AlgebraicGeometry IsLocalRing CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

namespace Scheme

universe u

variable {X : Scheme.{u}} {x y : X}

/-- For a specialization `x ⤳ y`, the stalk `𝒪_{X,x}` is the localization of `𝒪_{X,y}` at the
prime lying under the maximal ideal of `𝒪_{X,x}`, via the specialization map. -/
theorem isLocalization_stalkSpecializes (h : x ⤳ y) :
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x)
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom) := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  -- Both stalks are localizations of the sections `R` over an affine open containing `y`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  let := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  set p := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  set q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : IsLocalization.AtPrime (X.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hyU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    .of_algebraMap_eq fun r ↦ by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
        TopCat.Presheaf.germ_stalkSpecializes]
  have hle : p.primeCompl ≤ q.primeCompl := fun r hr ↦
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) q r).mp <| by
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk y)]
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ p r).mpr hr).map _
  -- `R_q` is the localization of `R_p` at the image of `R ∖ q`, which generates the prime.
  have := IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk y)
    (X.presheaf.stalk x) p.primeCompl q.primeCompl hle
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (X.presheaf.stalk x)
    (q.primeCompl.map (algebraMap Γ(X, U) (X.presheaf.stalk y))) _ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not]
    rw [← RingHom.algebraMap_toAlgebra (X.presheaf.stalkSpecializes h).hom,
      ← IsScalarTower.algebraMap_apply]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ q r).mpr hr
  · rintro ⟨s, hs⟩
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj p.primeCompl s
    refine ⟨algebraMap _ _ (m : Γ(X, U)), r, ?_, by rw [← hrm, mul_comm]⟩
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) q r).mp ?_
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk y), ← hrm, map_mul]
    refine IsUnit.mul ?_ (((IsLocalization.AtPrime.isUnit_to_map_iff _ p m).mpr m.2).map _)
    simpa [Ideal.primeCompl, mem_maximalIdeal, mem_nonunits_iff, RingHom.algebraMap_toAlgebra]
      using hs

/-- For a specialization `x ⤳ y`, the prime of `𝒪_{X,y}` lying under the maximal ideal of
`𝒪_{X,x}` is the maximal ideal of `𝒪_{X,y}` exactly when `x = y`. -/
@[simp]
theorem comap_stalkSpecializes_maximalIdeal_eq_iff (h : x ⤳ y) :
    (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom =
      maximalIdeal (X.presheaf.stalk y) ↔ x = y := by
  refine ⟨fun hxy ↦ ?_, fun hxy ↦ by subst hxy; simp⟩
  -- On an affine open `Spec R` containing `y`, both ideals lie over the primes of `x` and `y`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  let := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hcomp : (X.presheaf.stalkSpecializes h).hom.comp (algebraMap Γ(X, U) (X.presheaf.stalk y)) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) := by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hprime : hU.primeIdealOf ⟨x, hxU⟩ = hU.primeIdealOf ⟨y, hyU⟩ := by
    ext1
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal,
      ← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y)
        (hU.primeIdealOf ⟨y, hyU⟩).asIdeal, Ideal.under, Ideal.under,
      ← hxy, ← hcomp, Ideal.comap_comap]
  simpa using (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm.trans
    (hprime ▸ hU.fromSpec_primeIdealOf ⟨y, hyU⟩)

/-- For a specialization `x ⤳ y` and an affine open `U` containing `y`, the prime of `𝒪_{X,y}`
lying under the maximal ideal of `𝒪_{X,x}` pulls back along the germ map to the prime ideal of
`Γ(X, U)` corresponding to `x`. -/
theorem comap_germ_comap_stalkSpecializes_maximalIdeal {U : X.Opens} (hU : IsAffineOpen U)
    (hyU : y ∈ U) (h : x ⤳ y) :
    ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom).comap
        (X.presheaf.germ U y hyU).hom =
      (hU.primeIdealOf ⟨x, h.mem_open U.isOpen hyU⟩).asIdeal := by
  let := X.presheaf.algebra_section_stalk ⟨x, h.mem_open U.isOpen hyU⟩
  have := hU.isLocalization_stalk ⟨x, h.mem_open U.isOpen hyU⟩
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  exact IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) _

/-- For generizations `x` and `x'` of `y`, if the prime of `𝒪_{X,y}` corresponding to `x` is
contained in the one corresponding to `x'`, then `x` is a generization of `x'`. -/
theorem specializes_of_comap_stalkSpecializes_maximalIdeal_le {x' : X} (h : x ⤳ y)
    (h' : x' ⤳ y)
    (hle : (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom ≤
      (maximalIdeal (X.presheaf.stalk x')).comap (X.presheaf.stalkSpecializes h').hom) :
    x ⤳ x' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hle' := Ideal.comap_mono (f := (X.presheaf.germ U y hyU).hom) hle
  rw [comap_germ_comap_stalkSpecializes_maximalIdeal hU hyU h,
    comap_germ_comap_stalkSpecializes_maximalIdeal hU hyU h'] at hle'
  have hsp := ((PrimeSpectrum.le_iff_specializes _ _).mp hle').map hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at hsp

/-- **Prime elements of a local ring and codimension-one generizations.** On a locally Noetherian
integral scheme, every prime element `p` of the local ring `𝒪_{X,y}` generates the prime of
`𝒪_{X,y}` lying under the maximal ideal of `𝒪_{X,x}` for some codimension-one generization `x`
of `y`. The point `x` has codimension one by Krull's principal ideal theorem. -/
theorem exists_comap_stalkSpecializes_maximalIdeal_eq_span_singleton [IsIntegral X]
    [IsLocallyNoetherian X] {p : X.presheaf.stalk y} (hp : Prime p) :
    ∃ x : X, Order.coheight x = 1 ∧ ∃ h : x ⤳ y,
      (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom =
        Ideal.span {p} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  replace hU : IsAffineOpen U := hU
  let := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  set P := hU.primeIdealOf ⟨y, hyU⟩
  have hspan : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  -- The prime `q` of `Γ(X, U)` under `(p)`, contained in the prime `P` of `y`.
  let q : Spec Γ(X, U) := ⟨(Ideal.span {p}).comap (algebraMap Γ(X, U) _), inferInstance⟩
  have hqP : q.asIdeal ≤ P.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) P.asIdeal]
    refine Ideal.comap_mono ?_
    rw [Ideal.span_singleton_le_iff_mem, mem_maximalIdeal]
    exact hp.not_isUnit
  have hxy : hU.fromSpec q ⤳ y :=
    (((PrimeSpectrum.le_iff_specializes q P).mp hqP).map hU.fromSpec.continuous).trans
      (specializes_of_eq (hU.fromSpec_primeIdealOf ⟨y, hyU⟩))
  have hprime : hU.primeIdealOf ⟨_, hxy.mem_open U.isOpen hyU⟩ = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hdisj : Disjoint (P.asIdeal.primeCompl : Set Γ(X, U)) q.asIdeal :=
    Set.disjoint_left.mpr fun a ha haq ↦ ha (hqP haq)
  have hmap : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk y)) = Ideal.span {p} :=
    IsLocalization.map_under P.asIdeal.primeCompl _ _
  -- `fromSpec q` has codimension one, as `(p)` has height one by Krull's principal ideal theorem.
  have hcoh : Order.coheight (hU.fromSpec q) = 1 := by
    rw [coheight_eq_of_isOpenImmersion hU.fromSpec, ← idealHeight_eq_coheight,
      ← IsLocalization.height_map_of_disjoint (S := X.presheaf.stalk y) P.asIdeal.primeCompl
        q.asIdeal hdisj, hmap]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  refine ⟨_, hcoh, hxy, ?_⟩
  -- Both ideals of the localization `𝒪_{X,y}` pull back to `q` on `Γ(X, U)`.
  rw [← IsLocalization.map_under P.asIdeal.primeCompl (X.presheaf.stalk y)
      ((maximalIdeal _).comap (X.presheaf.stalkSpecializes hxy).hom), ← hmap]
  congr 1
  exact (comap_germ_comap_stalkSpecializes_maximalIdeal hU hyU hxy).trans (congrArg _ hprime)

/-- On an irreducible scheme, the image in the function field of a germ at `y` is the image of its
germ at a generization `x` of `y`. -/
@[simp]
theorem algebraMap_stalkSpecializes [IrreducibleSpace X] (h : x ⤳ y) (b : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom b) =
      algebraMap (X.presheaf.stalk y) X.functionField b := by
  simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]

/-- On an integral scheme the specialization map `𝒪_{X,y} ⟶ 𝒪_{X,x}` is injective, both local
rings being subrings of the function field. -/
theorem stalkSpecializes_injective [IsIntegral X] (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := fun a b hab ↦
  IsFractionRing.injective (X.presheaf.stalk y) X.functionField <| by
    rw [← algebraMap_stalkSpecializes h, hab, algebraMap_stalkSpecializes h]

/-- If `x` is a proper generization of `y` and every nonzero prime of `𝒪_{X,y}` is maximal
(`Ring.DimensionLEOne`, which without a domain assumption is stronger than Krull dimension at
most one), then the residue field `κ(x)` is a fraction field of `𝒪_{X,y}`, via the
specialization map. In particular `𝒪_{X,y}` is a domain. -/
theorem isFractionRing_residueField_of_specializes [Ring.DimensionLEOne (X.presheaf.stalk y)]
    (h : x ⤳ y) (hxy : x ≠ y) :
    letI := (X.presheaf.stalkSpecializes h ≫ X.residue x).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk y) (X.residueField x) := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  set 𝔮 := (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) 𝔮 := isLocalization_stalkSpecializes h
  -- The prime `𝔮` is not maximal, so it is zero.
  have h𝔮 : 𝔮 = ⊥ := by
    by_contra hne
    have : 𝔮.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    exact hxy ((comap_stalkSpecializes_maximalIdeal_eq_iff h).mp (eq_maximalIdeal this))
  have : (⊥ : Ideal (X.presheaf.stalk y)).IsPrime := h𝔮 ▸ inferInstance
  have : IsDomain (X.presheaf.stalk y) := .of_bot_isPrime _
  have hfrac : IsFractionRing (X.presheaf.stalk y) (X.presheaf.stalk x) := by
    have : 𝔮.primeCompl = nonZeroDivisors (X.presheaf.stalk y) := by
      ext; simp [h𝔮, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    unfold IsLocalization.AtPrime at hloc
    rwa [this] at hloc
  -- Nonzero elements of `𝒪_{X,y}` become units in `𝒪_{X,x}`, hence nonzero in `κ(x)`.
  have hres (a : X.presheaf.stalk y) (ha : a ≠ 0) :
      X.residue x (X.presheaf.stalkSpecializes h a) ≠ 0 :=
    ((IsLocalization.map_units (M := nonZeroDivisors (X.presheaf.stalk y))
      (X.presheaf.stalk x) ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩).map (X.residue x).hom).ne_zero
  let := (X.presheaf.stalkSpecializes h ≫ X.residue x).hom.toAlgebra
  have : FaithfulSMul (X.presheaf.stalk y) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr <| (injective_iff_map_eq_zero _).mpr
      fun a ha ↦ not_not.mp fun ha' ↦ hres a ha' ha
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk y)) s
  refine ⟨a, b, eq_div_of_mul_eq (hres b (nonZeroDivisors.ne_zero b.2)) ?_⟩
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
    ← map_mul]
  exact congrArg _ (IsLocalization.mk'_spec _ a b)

end Scheme

end AlgebraicGeometry

end TauCeti
