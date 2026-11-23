/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.SInteger
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
import TauCeti.GroupTheory.Subgroup.AdditiveRank
import TauCeti.FieldTheory.FunctionField.RiemannRoch.AffineClassNumber
import TauCeti.RingTheory.DedekindDomain.SInteger.Rank

/-!
# Units of holomorphy rings and the `S`-unit theorem for function fields

For a set `S` of places of an algebraic function field `F / k`, a nonzero function of the
holomorphy ring `𝒪_S` is a unit of `𝒪_S` exactly when it has no zero on `S`. For a finite set `T`
of places, the units of `𝒪_{Tᶜ}` are therefore the **`T`-units** of `F`: the functions with
neither zeros nor poles outside `T`.

This file proves **Dirichlet's `S`-unit theorem for function fields with a finite constant field**
(Rosen, Proposition 14.2): for every finite set `T` of places, the group of `T`-units is finitely
generated of rank `|T| - 1`. For `T` empty the `T`-units are the nonzero constants, a finite group,
so the formula holds there too with truncated subtraction.

The proof reduces to the `S`-unit theorem of a Dedekind domain with finite class group,
`TauCeti.finrank_sUnits`. Fix a place `P₀ ∈ T` and let `R₀ = 𝒪_{{P₀}ᶜ}` be the ring of functions
regular away from `P₀`. It is a Dedekind domain with fraction field `F` whose height one primes are
the places other than `P₀`, its class group is finite over a finite constant field, and its units
are the nonzero constants: by the product formula a function whose zeros and poles all lie at
`P₀` has none at all (`TauCeti.Place.ord_eq_zero_of_forall_ne_ord_eq_zero`). The `T`-units of `F`
are then the `S`-units of `R₀` for the set `S` of the `|T| - 1` primes coming from `T \ {P₀}`.

## Main results

* `TauCeti.isUnit_holomorphyRing_iff`: a nonzero function of `𝒪_S` is a unit exactly when it has
  order zero at every place of `S`.
* `TauCeti.mem_range_unitsMap_holomorphyRing_iff`: the same statement for the units of `𝒪_S`
  viewed in `Fˣ`.
* `TauCeti.isUnit_holomorphyRing_compl_singleton_iff`: the units of `𝒪_{{P}ᶜ}` are the nonzero
  constants.
* `TauCeti.fg_units_holomorphyRing_compl`: over a finite constant field, the units of `𝒪_{Tᶜ}`
  form a finitely generated group for every finite `T`.
* `TauCeti.finrank_units_holomorphyRing_compl`: **Dirichlet's `S`-unit theorem for function
  fields** — their rank is `|T| - 1`.

## References

* M. Rosen, *Number Theory in Function Fields*, GTM 210, Springer, 2002, Chapter 14,
  Proposition 14.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Proposition 5.1.3.
-/

public section

open IsDedekindDomain

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### Units of a holomorphy ring -/

/-- **A nonzero function of `𝒪_S` is a unit of `𝒪_S` exactly when it has no zero on `S`**: its
inverse then has no pole on `S` either. -/
theorem isUnit_holomorphyRing_iff {S : Set (Place k F)} {x : holomorphyRing S}
    (hx : (x : F) ≠ 0) : IsUnit x ↔ ∀ P ∈ S, P.ord (x : F) = 0 := by
  refine ⟨fun ⟨u, hu⟩ P hP ↦ ?_, fun h ↦ ?_⟩
  · subst hu
    have hinv : ((u⁻¹ : (holomorphyRing S)ˣ) : F) ≠ 0 := by simp
    have hmul := congrArg (fun y : holomorphyRing S ↦ P.ord (y : F)) u.mul_inv
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one, P.ord_one, P.ord_mul hx hinv] at hmul
    have h₁ := mem_holomorphyRing_iff_forall_ord_nonneg.mp (u : holomorphyRing S).property P hP
    have h₂ := mem_holomorphyRing_iff_forall_ord_nonneg.mp (u⁻¹ : (holomorphyRing S)ˣ).val.property
        P hP
    omega
  · have hmem : (x : F)⁻¹ ∈ holomorphyRing S := mem_holomorphyRing_iff_forall_ord_nonneg.mpr
      fun P hP ↦ by rw [P.ord_inv, h P hP, neg_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx)⟩

/-- **The units of `𝒪_S`, viewed in `Fˣ`, are the functions with neither zeros nor poles on
`S`.** -/
theorem mem_range_unitsMap_holomorphyRing_iff {S : Set (Place k F)} {u : Fˣ} :
    u ∈ (Units.map ((holomorphyRing S).val : holomorphyRing S →* F)).range ↔
      ∀ P ∈ S, P.ord (u : F) = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    have hw : ((w : holomorphyRing S) : F) ≠ 0 := by simp
    exact (isUnit_holomorphyRing_iff hw).mp w.isUnit
  · have hmem : (u : F) ∈ holomorphyRing S := mem_holomorphyRing_iff_forall_ord_nonneg.mpr
      fun P hP ↦ (h P hP).ge
    obtain ⟨w, hw⟩ := (isUnit_holomorphyRing_iff (x := ⟨(u : F), hmem⟩) u.ne_zero).mpr h
    exact ⟨w, Units.ext (congrArg Subtype.val hw)⟩

/-! ### Units of the ring of functions regular away from one place -/

/-- **The units of `𝒪_{{P}ᶜ}` are the nonzero constants**: a function regular away from `P`
whose inverse is too has neither zeros nor poles anywhere. -/
theorem isUnit_holomorphyRing_compl_singleton_iff (hF : IsFunctionField k F) {P : Place k F}
    {x : holomorphyRing ({P}ᶜ : Set (Place k F))} (hx : (x : F) ≠ 0) :
    IsUnit x ↔ (x : F) ∈ algebraicClosure k F := by
  rw [isUnit_holomorphyRing_iff hx]
  refine ⟨fun h ↦ ?_, fun h Q _ ↦ Q.ord_eq_zero_of_isAlgebraic (mem_algebraicClosure_iff.mp h)⟩
  have hne (Q : Place k F) (hQ : Q ≠ P) : Q.ord ((Units.mk0 _ hx : Fˣ) : F) = 0 := h Q hQ
  have hP := Place.ord_eq_zero_of_forall_ne_ord_eq_zero hF hne
  refine (Place.mem_algebraicClosure_iff_forall_mem_integers hF).mpr fun Q ↦
    Q.mem_integers_iff_ord_nonneg.mpr ?_
  by_cases hQ : Q = P
  · subst hQ
    exact hP.ge
  · exact (hne Q hQ).ge

/-- Over a finite constant field, `𝒪_{{P}ᶜ}` has only finitely many units: they are nonzero
constants. -/
theorem finite_units_holomorphyRing_compl_singleton (hF : IsFunctionField k F) [Finite k]
    (P : Place k F) : Finite (holomorphyRing ({P}ᶜ : Set (Place k F)))ˣ := by
  have := hF.finiteDimensional_algebraicClosure
  have : Finite (algebraicClosure k F) := Module.finite_of_finite k
  have hw (w : (holomorphyRing ({P}ᶜ : Set (Place k F)))ˣ) :
      ((w : holomorphyRing ({P}ᶜ : Set (Place k F))) : F) ∈ algebraicClosure k F :=
    (isUnit_holomorphyRing_compl_singleton_iff hF (by simp)).mp w.isUnit
  refine Finite.of_injective (β := algebraicClosure k F) (fun w ↦ ⟨_, hw w⟩) fun w₁ w₂ h ↦ ?_
  exact Units.ext (Subtype.ext (Subtype.mk.inj h))

/-! ### `T`-units as `S`-units of an affine model -/

section AffineModel

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra k R] [Algebra R F]
  [IsFractionRing R F] [IsScalarTower k R F]

/-- **The `T`-units of `F` are `S`-units of any affine model `R` all of whose places at infinity
lie in `T`**: they are the `S`-units of `R` for `S` the height one primes of `R` whose places lie
in `T`. -/
theorem range_unitsMap_holomorphyRing_compl_eq_unit {T : Set (Place k F)}
    (hT : ∀ P ∉ T, ∀ r : R, algebraMap R F r ∈ P.integers) :
    (Units.map ((holomorphyRing Tᶜ).val : holomorphyRing Tᶜ →* F)).range =
      (Place.ofPrime (R := R) k F ⁻¹' T).unit F := by
  ext u
  rw [mem_range_unitsMap_holomorphyRing_iff, Set.mem_unit_iff_forall_ord_eq_zero k]
  refine ⟨fun h p hp ↦ h _ hp, fun h P hP ↦ ?_⟩
  rw [← Place.ofPrime_center k F P (hT P hP)]
  exact h _ (by rwa [Set.mem_preimage, Place.ofPrime_center])

end AffineModel

/-! ### The `S`-unit theorem -/

/-- Both halves of the `S`-unit theorem at once, so that they share the reduction to the
`S`-units of the Dedekind domain `R₀ = 𝒪_{{P₀}ᶜ}` for a place `P₀ ∈ T`. -/
private theorem fg_and_finrank_units_holomorphyRing_compl (hF : IsFunctionField k F) [Finite k]
    {T : Set (Place k F)} (hT : T.Finite) :
    Monoid.FG (holomorphyRing Tᶜ)ˣ ∧
      Module.finrank ℤ (Additive (holomorphyRing Tᶜ)ˣ) = T.ncard - 1 := by
  -- A finite abelian group has rank zero.
  have finrank_zero (G : Type v) [CommGroup G] [Finite G] : Module.finrank ℤ (Additive G) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr
      (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)
  rcases T.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · -- The `∅`-units are regular at every place, so they are units of `𝒪_{{P}ᶜ}`, which are
    -- finitely many constants.
    obtain ⟨P⟩ := Place.nonempty hF
    have := finite_units_holomorphyRing_compl_singleton hF P
    have hle := holomorphyRing_antitone (show ({P}ᶜ : Set (Place k F)) ⊆ (∅ : Set _)ᶜ by simp)
    have : Finite (holomorphyRing (∅ : Set (Place k F))ᶜ)ˣ :=
      Finite.of_injective (Units.map (Subalgebra.inclusion hle).toMonoidHom)
        (Units.map_injective (Subalgebra.inclusion_injective hle))
    exact ⟨Monoid.fg_of_finite, by rw [Set.ncard_empty, finrank_zero]⟩
  -- `R₀` is a Dedekind domain with fraction field `F`, finite class group and finitely many units.
  let R₀ := holomorphyRing ({P₀}ᶜ : Set (Place k F))
  have := isDedekindDomain_holomorphyRing_compl hF (Set.finite_singleton P₀)
  have : IsFractionRing R₀ F := isFractionRing_holomorphyRing hF ⟨P₀, by simp⟩
  have := Divisor.finite_classGroup_of_finite R₀ hF
  have := finite_units_holomorphyRing_compl_singleton hF P₀
  have : Monoid.FG R₀ˣ := Monoid.fg_of_finite
  -- The places finite on `R₀` are exactly the places other than `P₀`.
  have hfin (P : Place k F) : (∀ r : R₀, algebraMap R₀ F r ∈ P.integers) ↔ P ≠ P₀ :=
    forall_algebraMap_mem_integers_holomorphyRing_iff hF
  have hrange : Set.range (Place.ofPrime (R := R₀) k F) = {P₀}ᶜ := by
    rw [Place.range_ofPrime]
    ext P
    exact hfin P
  -- The `T`-units are the `S`-units of `R₀` for the primes `S` of the places of `T \ {P₀}`.
  let S := Place.ofPrime (R := R₀) k F ⁻¹' T
  have hinj := Place.ofPrime_injective (R := R₀) k F
  have : Finite S := (hT.preimage hinj.injOn).to_subtype
  have hS : Nat.card S = T.ncard - 1 := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ hinj,
      Set.image_preimage_eq_inter_range, hrange, ← Set.sdiff_eq,
      Set.ncard_sdiff_singleton_of_mem hP₀]
  let e : (holomorphyRing Tᶜ)ˣ ≃* S.unit F :=
    (MonoidHom.ofInjective (Units.map_injective
      (f := ((holomorphyRing Tᶜ).val : holomorphyRing Tᶜ →* F)) Subtype.val_injective)).trans
      (MulEquiv.subgroupCongr (range_unitsMap_holomorphyRing_compl_eq_unit
        fun P hP ↦ (hfin P).mpr (by rintro rfl; exact hP hP₀)))
  refine ⟨Group.fg_iff_monoid_fg.mp (Group.fg_of_surjective (f := e.symm.toMonoidHom)
    e.symm.surjective), ?_⟩
  rw [(MulEquiv.toAdditive e).toIntLinearEquiv.finrank_eq, finrank_sUnits R₀ F S, hS,
    finrank_zero, zero_add]

/-- **The `T`-units of a function field with a finite constant field are finitely generated**:
for every finite set `T` of places, the unit group of the ring `𝒪_{Tᶜ}` of functions regular
outside `T` is a finitely generated group. -/
theorem fg_units_holomorphyRing_compl (hF : IsFunctionField k F) [Finite k]
    {T : Set (Place k F)} (hT : T.Finite) : Monoid.FG (holomorphyRing Tᶜ)ˣ :=
  (fg_and_finrank_units_holomorphyRing_compl hF hT).1

/-- **Dirichlet's `S`-unit theorem for function fields** (Rosen, Proposition 14.2): over a finite
constant field, for every finite set `T` of places the group of `T`-units — the unit group of the
ring `𝒪_{Tᶜ}` of functions regular outside `T` — has rank `|T| - 1`. For `T` empty both sides
are `0`: the `∅`-units are the nonzero constants. For `T` infinite both sides are `0` as well: the
rank is then infinite, and `Module.finrank` and `Set.ncard` both return `0`. -/
theorem finrank_units_holomorphyRing_compl (hF : IsFunctionField k F) [Finite k]
    (T : Set (Place k F)) :
    Module.finrank ℤ (Additive (holomorphyRing Tᶜ)ˣ) = T.ncard - 1 := by
  by_cases hT : T.Finite
  · exact (fg_and_finrank_units_holomorphyRing_compl hF hT).2
  -- An infinite `T` contains finite sets `T'` of every size, whose `T'`-units are `T`-units of
  -- rank `|T'| - 1`; so the rank is infinite.
  rw [Set.Infinite.ncard hT]
  refine Cardinal.toNat_eq_zero.mpr (.inr (Cardinal.aleph0_le.mpr fun n ↦ ?_))
  obtain ⟨T', hT'T, hT'fin, hT'card⟩ := Set.Infinite.exists_subset_ncard_eq hT (n + 1)
  obtain ⟨hfg, hrank⟩ := fg_and_finrank_units_holomorphyRing_compl hF hT'fin
  have : Module.Finite ℤ (Additive (holomorphyRing T'ᶜ)ˣ) :=
    Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr (Group.fg_iff_monoid_fg.mpr hfg))
  have hle := holomorphyRing_antitone (Set.compl_subset_compl.mpr hT'T)
  calc (n : Cardinal) = Module.finrank ℤ (Additive (holomorphyRing T'ᶜ)ˣ) := by
        rw [hrank, hT'card, Nat.add_sub_cancel]
    _ = Module.rank ℤ (Additive (holomorphyRing T'ᶜ)ˣ) := Module.finrank_eq_rank _ _
    _ ≤ Module.rank ℤ (Additive (holomorphyRing Tᶜ)ˣ) :=
        (Units.map (Subalgebra.inclusion hle).toMonoidHom).rank_additive_le_of_injective
          (Units.map_injective (Subalgebra.inclusion_injective hle))

end TauCeti
