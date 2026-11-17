/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.FixedPoints
public import TauCeti.RingTheory.Smooth.FixedPoints

/-!
# Tame fixed-point subgroups of smooth affine group schemes

Given a commutative Hopf algebra `H` over a commutative ring `R` and a family `f : ι → (H →ₐc[R] H)`
of bialgebra endomorphisms, the quotient by `TauCeti.HopfIdeal.fixedPoints f` represents the closed
subgroup scheme of `Spec H` fixed by every `f i`: over every commutative `R`-algebra `A`, its
`A`-points are the elements `g` of `WithConv (H →ₐ[R] A)` satisfying
`BialgHom.mapDomain (f i) g = g` for all `i`.

When `H` is smooth over `R` and a group `Γ` of invertible order `Nat.card Γ ∈ Rˣ` acts on `H` by
Hopf-algebra automorphisms, Edixhoven's tame fixed-point theorem implies that the fixed-point
quotient is again smooth over `R`. As an application, for every smooth commutative affine group
scheme `G` over a ring `R` with `2 ∈ Rˣ`, the 2-torsion closed subgroup `G[2]` cut out by the
inversion involution (the antipode) is smooth over `R`.

## Main definitions

* `TauCeti.CommHopfAlgCat.inversionAction`: the action of `ℤˣ` by inversion (the antipode) on a
  cocommutative object of `CommHopfAlgCat R`.

## Main results

* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPoints_iff` and
  `TauCeti.CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPoints`: characterization of the
  `A`-points of a fixed-point Hopf-ideal quotient.
* `TauCeti.CommHopfAlgCat.smooth_quotient_fixedPoints`: smoothness of the fixed-point quotient
  of a smooth commutative Hopf algebra under a tame group action.
* `TauCeti.FiniteTypeCommHopfAlgCat.smooth_quotient_fixedPoints` and
  `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: Edixhoven's tame fixed-point theorem in
  `FiniteTypeCommHopfAlgCat`.
* `TauCeti.CommHopfAlgCat.smooth_twoTorsion`: smoothness of the 2-torsion closed subgroup of a
  smooth commutative affine group scheme when `IsUnit (2 : R)`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions
  3.1 and 3.4, pp. 293–295.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w z

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

section Points

variable {ι : Sort*}

/-- An `A`-point of `H` lies in the closed subgroup cut out by `HopfIdeal.fixedPoints f` if and
only if it is fixed by every `f i`. -/
theorem mem_quotientPointsSubgroup_fixedPoints_iff (H : _root_.CommHopfAlgCat.{v} R)
    (f : ι → H →ₐc[R] H) (A : CommAlgCat.{w} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (HopfIdeal.fixedPoints f) A ↔
      ∀ i, BialgHom.mapDomain (A := A) (f i) g = g := by
  rw [mem_quotientPointsSubgroup_iff]
  constructor
  · intro hg i
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    have hzero := hg (f i a - a) (HopfIdeal.sub_mem_fixedPoints f i a)
    rw [map_sub, sub_eq_zero] at hzero
    rw [BialgHom.mapDomain_apply_apply]
    exact hzero
  · intro hg h hh
    have hle : (HopfIdeal.fixedPoints f).toIdeal ≤ RingHom.ker g.ofConv.toRingHom := by
      rw [HopfIdeal.fixedPoints_le_ker_iff]
      intro i a
      simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using congrArg (fun p : WithConv (H →ₐ[R] A) ↦ p.ofConv a) (hg i)
    exact RingHom.mem_ker.mp (hle (HopfIdeal.mem_toIdeal.mpr hh))

/-- The image of `BialgHom.mapDomain` along the quotient morphism for `HopfIdeal.fixedPoints f` is
the set of `A`-points fixed by every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPoints (H : _root_.CommHopfAlgCat.{v} R)
    (f : ι → H →ₐc[R] H) (A : Type w) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A)
        (_root_.CommHopfAlgCat.mkQuotient H (HopfIdeal.fixedPoints f)).hom) =
      {g : WithConv (H →ₐ[R] A) | ∀ i, BialgHom.mapDomain (A := A) (f i) g = g} := by
  ext g
  simpa only [Set.mem_range, Set.mem_ofPred_eq, quotientPointsSubgroup, MonoidHom.mem_range,
    quotientPointsHom, _root_.CommHopfAlgCat.Hom.mapPointsFunctor, GrpCat.hom_ofHom] using
    mem_quotientPointsSubgroup_fixedPoints_iff H f (CommAlgCat.of R A) g

end Points

section Smoothness

/-- **Edixhoven's tame fixed-point theorem for commutative Hopf algebras.** If `H` is smooth over
`R` and a group `Γ` acts on `H` by bialgebra endomorphisms with `IsUnit (Nat.card Γ : R)`, then
the fixed-point Hopf-ideal quotient of `H` is smooth over `R`. -/
theorem smooth_quotient_fixedPoints_of_action (H : _root_.CommHopfAlgCat.{v} R)
    (hH : smoothCommHopfAlgProperty R H) {Γ : Type w} [Group Γ] (ρ : Γ → H →ₐc[R] H)
    (hρ : ∀ γ τ a, ρ (γ * τ) a = ρ γ (ρ τ a)) (hΓ : IsUnit (Nat.card Γ : R)) :
    smoothCommHopfAlgProperty R (_root_.CommHopfAlgCat.quotient H (HopfIdeal.fixedPoints ρ)) := by
  have : Algebra.Smooth R H := (smoothCommHopfAlgProperty_iff H).mp hH
  rw [smoothCommHopfAlgProperty_iff]
  -- Unfold `CommHopfAlgCat.quotient` to the quotient algebra `H ⧸ (fixedPoints ρ).toIdeal`.
  change Algebra.Smooth R (H ⧸ (HopfIdeal.fixedPoints ρ).toIdeal)
  rw [HopfIdeal.fixedPoints_toIdeal]
  exact Algebra.Smooth.quotient_fixedPointsIdeal ρ hρ hΓ

/-- **Edixhoven's tame fixed-point theorem in `CommHopfAlgCat`.** For a smooth commutative Hopf
algebra `H` and a group action `ρ : Γ →* Aut H` with `IsUnit (Nat.card Γ : R)`, the fixed-point
quotient is smooth over `R`. -/
theorem smooth_quotient_fixedPoints (H : _root_.CommHopfAlgCat.{v} R)
    (hH : smoothCommHopfAlgProperty R H) {Γ : Type w} [Group Γ] (ρ : Γ →* CategoryTheory.Aut H)
    (hΓ : IsUnit (Nat.card Γ : R)) :
    smoothCommHopfAlgProperty R
      (_root_.CommHopfAlgCat.quotient H (HopfIdeal.fixedPoints fun γ ↦ (ρ γ).asIso.hom.hom)) :=
  smooth_quotient_fixedPoints_of_action H hH (fun γ ↦ (ρ γ).asIso.hom.hom)
    (fun γ τ a ↦ by
      rw [map_mul, Aut.mul_asIso, Iso.trans_hom, _root_.CommHopfAlgCat.hom_comp,
        BialgHom.comp_apply])
    hΓ

end Smoothness

section Inversion

/-- The inversion involution on a cocommutative object `H` of `CommHopfAlgCat R`, as an action of
the two-element group `ℤˣ` sending `-1` to the antipode. -/
noncomputable def inversionAction (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    ℤˣ →* CategoryTheory.Aut H :=
  let s : H ⟶ H := _root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := H))
  have hss : s ≫ s = 𝟙 H := by
    apply _root_.CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro a
    simp only [s, _root_.CommHopfAlgCat.hom_comp, _root_.CommHopfAlgCat.hom_ofHom,
      BialgHom.comp_apply, HopfAlgebra.antipodeBialgHom_apply, HopfAlgebra.antipode_antipode]
    rfl
  let iso : H ≅ H := ⟨s, s, hss, hss⟩
  { toFun := fun u ↦ if u = 1 then 1 else Aut.of iso
    map_one' := by simp
    map_mul' := fun u v ↦ by
      rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl
      · simp
      · simp
      · simp
      · have hneg : (-1 : ℤˣ) ≠ 1 := by decide
        have hmul : (-1 : ℤˣ) * (-1) = 1 := by decide
        simp only [hmul, ↓reduceIte, hneg]
        apply Aut.ext
        apply Iso.ext
        simpa [iso, Aut.mul_asIso, Aut.one_asIso] using hss.symm }

/-- Evaluating `inversionAction H (-1)` yields the antipode bialgebra endomorphism. -/
@[simp]
theorem inversionAction_neg_one (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    (inversionAction H (-1)).asIso.hom.hom = HopfAlgebra.antipodeBialgHom (R := R) (A := H) := by
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  simp [inversionAction, hneg]

/-- The fixed-point Hopf ideal of `inversionAction H` is the equalizer of the antipode with the
identity. -/
theorem fixedPoints_inversionAction (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    HopfIdeal.fixedPoints (fun u : ℤˣ ↦ (inversionAction H u).asIso.hom.hom) =
      HopfIdeal.equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := H)) (BialgHom.id R H) := by
  refine le_antisymm ?_ ?_
  · rw [HopfIdeal.fixedPoints_le_iff]
    intro u a
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp [zero_mem]
    · rw [inversionAction_neg_one]
      exact HopfIdeal.sub_mem_equalizer a
  · rw [HopfIdeal.equalizer_le_iff]
    intro a
    have h := HopfIdeal.sub_mem_fixedPoints
      (fun u : ℤˣ ↦ (inversionAction H u).asIso.hom.hom) (-1) a
    rwa [inversionAction_neg_one] at h

/-- An `A`-point of a cocommutative Hopf algebra `H` lies in the 2-torsion closed subgroup cut out
by `equalizer antipode id` if and only if `g ^ 2 = 1`. -/
theorem mem_quotientPointsSubgroup_twoTorsion_iff (H : _root_.CommHopfAlgCat.{v} R)
    [Coalgebra.IsCocomm R H] (A : CommAlgCat.{w} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H
        (HopfIdeal.equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := H)) (BialgHom.id R H))
        A ↔ g ^ 2 = 1 := by
  rw [← fixedPoints_inversionAction H, mem_quotientPointsSubgroup_fixedPoints_iff]
  have hinv : BialgHom.mapDomain (A := A) (HopfAlgebra.antipodeBialgHom (R := R) (A := H)) g =
      g⁻¹ := by
    apply WithConv.ofConv_injective
    ext a
    rw [BialgHom.mapDomain_apply_apply, HopfAlgebra.antipodeBialgHom_apply,
      WithConv.algHom_inv_def, WithConv.ofConv_toConv, AlgHom.antipodeComp_apply]
  constructor
  · intro hg
    have hneg := hg (-1)
    rw [inversionAction_neg_one, hinv] at hneg
    rw [sq, ← inv_eq_iff_mul_eq_one]
    exact hneg
  · intro hsq u
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · rw [inversionAction_neg_one, hinv, inv_eq_iff_mul_eq_one, ← sq]
      exact hsq

/-- **Smoothness of 2-torsion.** For any smooth commutative affine group scheme over a ring `R` in
which `2` is a unit, the 2-torsion closed subgroup (fixed points of inversion) is smooth over
`R`. -/
theorem smooth_twoTorsion (H : _root_.CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H]
    (hH : smoothCommHopfAlgProperty R H) (h2 : IsUnit (2 : R)) :
    smoothCommHopfAlgProperty R
      (_root_.CommHopfAlgCat.quotient H
        (HopfIdeal.equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := H))
          (BialgHom.id R H))) := by
  rw [← fixedPoints_inversionAction H]
  have hcard : (Nat.card ℤˣ : R) = 2 := by
    have h2' : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [h2', Nat.cast_ofNat]
  exact smooth_quotient_fixedPoints H hH (inversionAction H) (hcard.symm ▸ h2)

end Inversion

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- **Edixhoven's tame fixed-point theorem for finite-type commutative Hopf algebras (explicit
quotient form).** -/
theorem smooth_quotient_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (hH : smoothCommHopfAlgProperty R H.obj) {Γ : Type w} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut H) (hΓ : IsUnit (Nat.card Γ : R)) :
    smoothCommHopfAlgProperty R
      (quotient H (HopfIdeal.fixedPoints fun γ ↦ toBialgHom (ρ γ).asIso.hom)).obj :=
  CommHopfAlgCat.smooth_quotient_fixedPoints_of_action H.obj hH
    (fun γ ↦ toBialgHom (ρ γ).asIso.hom)
    (fun γ τ a ↦ by
      rw [map_mul, Aut.mul_asIso, Iso.trans_hom, toBialgHom_comp, BialgHom.comp_apply])
    hΓ

/-- **Edixhoven's tame fixed-point theorem.** The fixed points of a group of invertible order
acting on a smooth finite-type affine group scheme are represented by a smooth closed subgroup
scheme. -/
theorem smooth_fixedPoints {k : Type u} [CommRing k] (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) {Θ : Type w} [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective (toBialgHom f) ∧
      ∀ (A : Type z) [CommRing A] [Algebra k A],
        Set.range (BialgHom.mapDomain (A := A) (toBialgHom f)) =
          {g | ∀ θ : Θ, BialgHom.mapDomain (A := A) (toBialgHom (ρ θ).asIso.hom) g = g} := by
  let I : HopfIdeal k H := HopfIdeal.fixedPoints fun θ ↦ toBialgHom (ρ θ).asIso.hom
  refine ⟨quotient H I, mkQuotient H I, smooth_quotient_fixedPoints H hH ρ hΘ,
    CommHopfAlgCat.mkQuotient_surjective H.obj I, fun A _ _ ↦ ?_⟩
  exact CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPoints H.obj
    (fun θ ↦ toBialgHom (ρ θ).asIso.hom) A

end FiniteTypeCommHopfAlgCat

end TauCeti
