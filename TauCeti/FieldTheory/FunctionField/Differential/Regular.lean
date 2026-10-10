/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence

/-!
# Regular Kähler differentials at rational places

At a rational place `P`, a separating uniformizer `t` identifies the image of
`Ω[𝒪_P⁄k] → Ω[F⁄k]` with `𝒪_P dt`. In particular, regularity can be checked on the
coefficient in the basis `dt`, without assuming that the map from local differentials is
injective.

When the Kähler–Weil comparison is independent of the separating element, this lattice
is exactly the annihilator of `𝒪_P` under the local residue pairing. For nonzero
differentials it is therefore exactly the nonnegative-order lattice of Weil differentials.
This is the local comparison needed to identify the differential sheaf on a smooth curve
with a canonical divisor sheaf. The results concern rational places; over an algebraically
closed constant field every place of a function field is rational.

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

include hP ht in
/-- A rational Kähler differential comes from the valuation ring of a rational place exactly
when its coefficient in the basis given by a separating uniformizer is integral there. -/
theorem mem_range_map_iff_coord_mem_integers (ω : Ω[F⁄k]) :
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
        ValuationSubring.algebraMap_apply] using
          P.derivativeOfSeparating_mem_integers hP ht htr z.2
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
theorem mem_range_map_iff_forall_repartitionDualComponent_eq_zero (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
            Module.Dual k ↥(repartitionSpace k F)) P u = 0 := by
  rw [P.mem_range_map_iff_coord_mem_integers hP ht htr,
    P.coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero hP ht htr]
  simp_rw [repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    hF hex hinf hx hP ht htr]

end WithUniformizer

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k]
  (P : Place k F) (hP : P.degree = 1) (hF : IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F) (hinf : {Q : Place k F | Q.degree = 1}.Infinite)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]

include hP hinf in
/-- Over a perfect exact constant field with infinitely many rational places, a nonzero Weil
differential has nonnegative order at a rational place exactly when its corresponding Kähler
differential comes from that place's valuation ring. No uniformizer is part of the statement. -/
theorem mem_range_map_iff_nonneg_weilDifferentialOrder
    (ω : weilDifferentialSpace k F)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm ω ∈
        (KaehlerDifferential.map k k P.integers F).range ↔
      0 ≤ weilDifferentialOrder hF hex ω.2 hω P := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  rw [P.mem_range_map_iff_forall_repartitionDualComponent_eq_zero hP ht htr hF hex hinf hx,
    LinearEquiv.apply_symm_apply, le_weilDifferentialOrder_iff hF hex ω.2 hω P 0]
  simp only [WithZero.exp_zero, ← P.mem_integers_iff]

end TauCeti.Place
