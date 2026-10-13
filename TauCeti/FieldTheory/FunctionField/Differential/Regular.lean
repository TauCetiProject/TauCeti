/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence

/-!
# Regular Kähler differentials at places

At a place `P`, a separating prime element `t` identifies the image of `Ω[𝒪_P⁄k] → Ω[F⁄k]`
with `𝒪_P dt`, as soon as differentiation by `t` preserves `𝒪_P`. This holds at rational places
over any constant field, and at every place over a perfect exact constant field. In particular,
regularity can be checked on the coefficient in the basis `dt`, without assuming that the map from
local differentials is injective.

At rational places, when the Kähler–Weil comparison is independent of the separating element,
this lattice is exactly the annihilator of `𝒪_P` under the local residue pairing.

Over a perfect exact constant field the comparison needs no rational place at all. The Weil
differential `dt` of a prime element has order zero at `P`
(`TauCeti.weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero`), so a nonzero Weil
differential `z dt` has order `ord_P z`. The chain rule for Weil differentials, together with the
divisor `-2 (z)_∞ + Diff(F / k(z))` of `dz`, shows that `dz/dt` is regular at `P` whenever `z` is.
Hence at every place, of any degree, the image of local Kähler differentials is exactly the
nonnegative-order lattice of Weil differentials, and equivalently the annihilator of `𝒪_P` for the
local component. This is the local comparison needed to identify the differential sheaf on a
smooth curve with a canonical divisor sheaf.

## Main results

* `TauCeti.Place.mem_range_map_iff_coord_mem_integers`: at a rational place, a differential is
  regular exactly when its coefficient in `dt` is.
* `TauCeti.Place.derivativeOfSeparating_mem_integers_of_perfectField`: over a perfect exact
  constant field, differentiation by a prime element preserves the valuation ring of any place.
* `TauCeti.Place.mem_range_map_iff_coord_mem_integers_of_perfectField`: the coefficient criterion
  at every place over a perfect exact constant field.
* `TauCeti.Place.mem_range_map_iff_weilDifferentialOrder_nonneg`: over a perfect exact constant
  field, a Kähler differential is regular at a place exactly when the corresponding Weil
  differential has nonnegative order there.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.7 and IV.2–3.
* R. Hartshorne, *Algebraic Geometry*, II, Section 8, and IV, Section 1.

The Kähler–Weil comparison and its residue formula are those of
`kaehlerDifferentialEquivWeilDifferentialOfSeparating` and
`repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`.
-/

public section

open scoped IntermediateField
open KaehlerDifferential

namespace TauCeti.Place

section WithUniformizer

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

include ht in
/-- If differentiation by a separating prime element `t` preserves the valuation ring of `P`,
then a Kähler differential comes from that valuation ring exactly when its coefficient in the
basis `dt` is integral there. -/
private theorem mem_range_map_iff_coord_mem_integers_of_forall
    (hD : ∀ z ∈ P.integers, derivativeOfSeparating htr z ∈ P.integers) (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers := by
  constructor
  · rintro ⟨η, rfl⟩
    have hη : η ∈ Submodule.span P.integers (Set.range (D k P.integers)) := by
      rw [span_range_derivation]
      trivial
    induction hη using Submodule.span_induction with
    | mem η hη =>
      obtain ⟨z, rfl⟩ := hη
      rw [KaehlerDifferential.map_D]
      simpa only [Module.Basis.coord_apply, kaehlerBasisOfSeparating_repr_D,
        ValuationSubring.algebraMap_apply] using hD z z.2
    | zero => simp
    | add a b _ _ ha hb => simpa using P.integers.add_mem _ _ ha hb
    | smul a b _ hb =>
      simpa [← IsScalarTower.algebraMap_smul F a, Algebra.smul_def] using
        P.integers.mul_mem _ _ a.2 hb
  · intro hω
    have ht' : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
    refine ⟨(⟨(kaehlerBasisOfSeparating htr).coord () ω, hω⟩ : P.integers) •
      D k P.integers ⟨t, ht'⟩, ?_⟩
    rw [map_smul, KaehlerDifferential.map_D]
    -- The local-ring action on rational differentials is restriction along its inclusion in F.
    rw [← IsScalarTower.algebraMap_smul F]
    simpa [kaehlerBasisOfSeparating_apply] using
      (kaehlerBasisOfSeparating htr).sum_repr ω

include hP ht in
/-- A rational Kähler differential comes from the valuation ring of a rational place exactly
when its coefficient in the basis given by a separating uniformizer is integral there. -/
theorem mem_range_map_iff_coord_mem_integers (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers :=
  P.mem_range_map_iff_coord_mem_integers_of_forall ht htr
    (fun _ ↦ P.derivativeOfSeparating_mem_integers hP ht htr) ω

/-- The residue pairing against integral functions detects whether the coefficient of a
rational differential in a separating-uniformizer basis is integral. -/
theorem coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero (ω : Ω[F⁄k]) :
    (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers ↔
      ∀ u ∈ P.integers, P.kaehlerResidue hP ht htr (u • ω) = 0 := by
  let a := (kaehlerBasisOfSeparating htr).coord () ω
  have hω : a • D k F t = ω := by
    simpa [a, kaehlerBasisOfSeparating_apply] using
      (kaehlerBasisOfSeparating htr).sum_repr ω
  constructor
  · intro ha u hu
    rw [← hω, smul_smul, kaehlerResidue_smul_D]
    exact P.residue_eq_zero_of_mem_integers hP ht (P.integers.mul_mem _ _ hu ha)
  · intro h
    by_contra ha
    have ha0 : a ≠ 0 := by
      intro ha0
      have haz : a ∈ P.integers := ha0 ▸ P.integers.zero_mem
      exact ha haz
    have ht0 : t ≠ 0 := htr.ne_zero
    have hord : P.ord a < 0 := lt_of_not_ge (P.mem_integers_iff_ord_nonneg.not.mp ha)
    have hu : (a * t)⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv, P.ord_mul ha0 ht0, ht]
      omega
    have hzero := h (a * t)⁻¹ hu
    rw [← hω, smul_smul, kaehlerResidue_smul_D] at hzero
    have hmul : (a * t)⁻¹ * a = t⁻¹ := by
      field_simp
    rw [hmul, residue_inv_uniformizer] at hzero
    exact one_ne_zero hzero

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (hinf : {Q : Place k F | Q.degree = 1}.Infinite)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]

include hP ht htr hinf in
/-- Under the Kähler–Weil comparison, the image of local Kähler differentials at a rational
place is precisely the annihilator of its valuation ring for the local component. -/
theorem mem_range_map_iff_forall_repartitionDualComponent_eq_zero_of_uniformizer (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
            Module.Dual k ↥(repartitionSpace k F)) P u = 0 := by
  rw [P.mem_range_map_iff_coord_mem_integers hP ht htr,
    P.coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero hP ht htr]
  simp_rw [repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    hF hex hinf hx hP ht htr]

include hP ht htr hinf in
/-- Given a separating uniformizer at a rational place, a nonzero Weil differential has
nonnegative order exactly when its corresponding Kähler differential comes from the valuation
ring. The constant field need not be perfect. -/
theorem mem_range_map_iff_weilDifferentialOrder_nonneg_of_uniformizer
    (ω : weilDifferentialSpace k F)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm ω ∈
        (KaehlerDifferential.map k k P.integers F).range ↔
      0 ≤ weilDifferentialOrder hF hex ω.2 hω P := by
  rw [P.mem_range_map_iff_forall_repartitionDualComponent_eq_zero_of_uniformizer
      hP ht htr hF hex hinf hx,
    LinearEquiv.apply_symm_apply, le_weilDifferentialOrder_iff hF hex ω.2 hω P 0]
  simp only [WithZero.exp_zero, ← P.mem_integers_iff]

end WithUniformizer

section PerfectField

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k]
  (P : Place k F) (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)

/-- Over a perfect field, a Kähler differential comes from the valuation ring of a rational
place exactly when its residue pairing with every integral function vanishes. No uniformizer
is part of the statement. -/
theorem mem_range_map_iff_forall_kaehlerResidueOfPerfectField_smul_eq_zero (hP : P.degree = 1)
    (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers, P.kaehlerResidueOfPerfectField hP hF (u • ω) = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  rw [P.mem_range_map_iff_coord_mem_integers hP ht htr,
    P.coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero hP ht htr,
    P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF htr]

include hF hex in
/-- **Differentiation by a prime element preserves the valuation ring**, at a place of any degree
of a function field over a perfect exact constant field: if `t` is a prime element at `P` and `z`
is regular at `P`, then so is `dz/dt`. -/
theorem derivativeOfSeparating_mem_integers_of_perfectField {t : F} (ht : P.ord t = 1)
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] {z : F} (hz : z ∈ P.integers) :
    derivativeOfSeparating htr z ∈ P.integers := by
  -- A function with vanishing differential has derivative zero.
  by_cases hDz : D k F z = 0
  · have h := derivativeOfSeparating_smul_D htr z
    rw [hDz, smul_eq_zero] at h
    rw [h.resolve_right (D_ne_zero_of_separating htr)]
    exact P.integers.zero_mem
  -- Otherwise `z` is separating, and the chain rule gives `dz = (dz/dt) dt` for the Weil
  -- differentials, so `ord_P (dz/dt) = v_P(dz) - v_P(dt) = v_P(dz)`.
  have hzsep : Algebra.IsSeparable k⟮z⟯ F := (hF.isSeparable_adjoin_iff_D_ne_zero).mpr hDz
  have hztr : Transcendental k z := fun halg ↦ hDz (D_eq_zero_of_isSeparable
    (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)))
  have hd0 := derivativeOfSeparating_ne_zero htr hztr
  have hchain : (weilDifferentialOfSeparating hF hztr : Module.Dual k ↥(repartitionSpace k F)) =
      repartitionDualMul hF (Units.mk0 _ hd0 : F) (weilDifferentialOfSeparating hF htr) := by
    rw [weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_perfectField hF hex htr
      hztr, coe_weilDifferentialSpaceModule_smul, Units.val_mk0]
  have hdz := weilDifferentialDivisor_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF htr).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF htr) (Units.mk0 _ hd0)
  rw [← weilDifferentialDivisor_congr hF hex hchain (weilDifferentialOfSeparating hF hztr).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hztr)] at hdz
  have hord := congrArg (fun D : Divisor k F ↦ D.coeff P) hdz
  have := P.finiteDimensional_residueField hF
  simp only [coeff_weilDifferentialDivisor,
    weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero hF hex htr ht,
    AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_principal, Units.val_mk0,
    add_zero] at hord
  -- The divisor `-2 (z)_∞ + Diff(F / k(z))` of `dz` has nonnegative coefficient at `P`.
  let _ := ratFuncAlgebraOfTranscendental hztr
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hztr
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hztr
  rw [← coeff_weilDifferentialDivisor, weilDifferentialDivisor_weilDifferentialOfSeparating,
    AlgebraicGeometry.WeilDivisor.coeff_add, AlgebraicGeometry.WeilDivisor.coeff_zsmul,
    Divisor.coeff_poles, Units.val_mk0, Divisor.coeff_different] at hord
  rw [P.mem_integers_iff_ord_nonneg] at hz ⊢
  omega

include hF hex in
/-- At a place of any degree of a function field over a perfect exact constant field, a Kähler
differential comes from the valuation ring exactly when its coefficient in the basis given by a
prime element is integral there. -/
theorem mem_range_map_iff_coord_mem_integers_of_perfectField {t : F} (ht : P.ord t = 1)
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers :=
  P.mem_range_map_iff_coord_mem_integers_of_forall ht htr
    (fun _ ↦ P.derivativeOfSeparating_mem_integers_of_perfectField hF hex ht htr) ω

variable {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]

include hF hex in
/-- Over a perfect exact constant field, a nonzero Weil differential has nonnegative order at a
place of any degree exactly when its corresponding Kähler differential comes from that place's
valuation ring. No uniformizer is part of the statement. -/
theorem mem_range_map_iff_weilDifferentialOrder_nonneg
    (ω : weilDifferentialSpace k F)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm ω ∈
        (KaehlerDifferential.map k k P.integers F).range ↔
      0 ≤ weilDifferentialOrder hF hex ω.2 hω P := by
  let := weilDifferentialSpaceModule hF
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.finiteDimensional_residueField hF
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField hF hex hx htr,
    P.mem_range_map_iff_coord_mem_integers_of_perfectField hF hex ht htr]
  -- Write `ω = a dt`; then `v_P(ω) = ord_P a + v_P(dt) = ord_P a`.
  obtain ⟨η, rfl⟩ := (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex htr).surjective ω
  rw [LinearEquiv.symm_apply_apply]
  let a := (kaehlerBasisOfSeparating htr).coord () η
  have hη : a • D k F t = η := by
    simpa [a, kaehlerBasisOfSeparating_apply] using (kaehlerBasisOfSeparating htr).sum_repr η
  have hωa : (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex htr η :
      Module.Dual k ↥(repartitionSpace k F)) =
      repartitionDualMul hF a (weilDifferentialOfSeparating hF htr) := by
    rw [← hη, map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
      coe_weilDifferentialSpaceModule_smul]
  have ha : a ≠ 0 := fun ha ↦ hω (by simp [hωa, ha])
  have hdt : (weilDifferentialOfSeparating hF htr : Module.Dual k ↥(repartitionSpace k F)) ≠ 0 :=
    by simpa using weilDifferentialOfSeparating_ne_zero hF htr
  have hord := weilDifferentialOrder_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF htr).2 hdt (Units.mk0 a ha) P
  have hcongr := congrArg (fun D : Divisor k F ↦ D.coeff P)
    (weilDifferentialDivisor_congr hF hex hωa (Submodule.coe_mem _) hω
      (repartitionDualMul_mem_weilDifferentialSpace hF a (weilDifferentialOfSeparating hF htr).2)
      (repartitionDualMul_ne_zero hF ha hdt))
  simp only [coeff_weilDifferentialDivisor] at hcongr
  rw [hcongr.trans hord, weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero hF hex htr ht,
    add_zero, Units.val_mk0, P.mem_integers_iff_ord_nonneg]

include hF hex in
/-- Over a perfect exact constant field, the image of local Kähler differentials at a place of
any degree is the annihilator of its valuation ring for the local component of the Kähler–Weil
comparison. No uniformizer is part of the statement. -/
theorem mem_range_map_iff_forall_repartitionDualComponent_eq_zero (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
            Module.Dual k ↥(repartitionSpace k F)) P u = 0 := by
  by_cases hω : (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
      Module.Dual k ↥(repartitionSpace k F)) = 0
  · have h0 : ω = 0 :=
      (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).map_eq_zero_iff.mp
        (Subtype.ext hω)
    simp [h0]
  have h := P.mem_range_map_iff_weilDifferentialOrder_nonneg hF hex hx _ hω
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, le_weilDifferentialOrder_iff hF hex _ hω P 0]
  simp only [WithZero.exp_zero, ← P.mem_integers_iff]

end PerfectField

end TauCeti.Place
