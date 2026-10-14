/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence

/-!
# Regular Kähler differentials at places

At a place `P` whose residue field is separable over `k`, a separating uniformizer `t` identifies
the image of `Ω[𝒪_P⁄k] → Ω[F⁄k]` with `𝒪_P dt`, because differentiation with respect to `t`
preserves `𝒪_P`. In particular, regularity can be checked on the coefficient in the basis `dt`,
without assuming that the map from local differentials is injective.

The trace residue pairing against `𝒪_P` detects integrality of that coefficient. When the
Kähler–Weil comparison is independent of the separating element, as it is over a perfect constant
field, local components of Weil differentials are trace residues, so this lattice is exactly the
annihilator of `𝒪_P` under the local component. For nonzero differentials it is therefore exactly
the nonnegative-order lattice of Weil differentials. Over a perfect constant field every residue
field is separable and every prime element is separating, so this holds at places of every
degree. This is the local comparison needed to identify the differential sheaf on a smooth curve
with a canonical divisor sheaf.

At rational places the trace residue is the residue, and the comparison is also stated through
the residue of Kähler differentials.

## Main results

* `TauCeti.Place.mem_range_map_iff_coord_mem_integers`: a differential comes from `𝒪_P` exactly
  when its coefficient in `dt` is integral.
* `TauCeti.Place.coord_mem_integers_iff_forall_traceResidue_coord_smul_eq_zero`: that coefficient
  is integral exactly when the trace residues of `u ω / dt` vanish for all integral `u`.
* `TauCeti.Place.mem_range_map_iff_weilDifferentialOrder_nonneg`: over a perfect exact constant
  field, a nonzero Weil differential has nonnegative order at a place of any degree exactly when
  the corresponding Kähler differential comes from the valuation ring.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.7 and IV.2–3, and
  Remark 4.3.7(d).
* R. Hartshorne, *Algebraic Geometry*, II, Section 8, and IV, Section 1.

The Kähler–Weil comparison and its residue formula are those of
`kaehlerDifferentialEquivWeilDifferentialOfSeparating`,
`repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating` and, over a
perfect constant field, `Place.traceResidue_coord_smul_eq_repartitionDualComponent_of_perfectField`.
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
/-- A Kähler differential of `F` comes from the valuation ring of a place with separable residue
field exactly when its coefficient in the basis given by a separating uniformizer is integral
there. -/
theorem mem_range_map_iff_coord_mem_integers [Algebra.IsSeparable k P.ResidueField]
    (ω : Ω[F⁄k]) :
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
          P.derivativeOfSeparating_mem_integers ht htr z.2
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

include ht in
/-- At a place with separable residue field, the trace residue pairing against integral functions
detects whether the coefficient of a Kähler differential in a separating-uniformizer basis is
integral. -/
theorem coord_mem_integers_iff_forall_traceResidue_coord_smul_eq_zero
    [FiniteDimensional k P.ResidueField] [Algebra.IsSeparable k P.ResidueField] (ω : Ω[F⁄k]) :
    (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers ↔
      ∀ u ∈ P.integers,
        P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () (u • ω)) = 0 := by
  set a := (kaehlerBasisOfSeparating htr).coord () ω
  simp_rw [map_smul, smul_eq_mul]
  constructor
  · intro ha u hu
    rw [traceResidue_apply,
      P.residueResidueField_eq_zero_of_mem_integers ht (P.integers.mul_mem _ _ hu ha), map_zero]
  · intro h
    by_contra ha
    -- Pair `a` against `c / (a t)` for a unit `c` whose value at `P` has trace one.
    obtain ⟨c, hc⟩ := Algebra.trace_surjective k P.ResidueField 1
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective c
    have ha0 : a ≠ 0 := fun ha0 ↦ ha (ha0 ▸ P.integers.zero_mem)
    have ht0 : t ≠ 0 := htr.ne_zero
    have hord : P.ord a < 0 := lt_of_not_ge (P.mem_integers_iff_ord_nonneg.not.mp ha)
    have hu : (a * t)⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv, P.ord_mul ha0 ht0, ht]
      omega
    have hzero := h (c * (a * t)⁻¹) (P.integers.mul_mem _ _ c.2 hu)
    have hmul : c * (a * t)⁻¹ * a = c * t⁻¹ := by
      field_simp
    rw [hmul, traceResidue_mul_inv_uniformizer, hc] at hzero
    exact one_ne_zero hzero

/-- The residue pairing against integral functions detects whether the coefficient of a
rational differential in a separating-uniformizer basis is integral. -/
theorem coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero (ω : Ω[F⁄k]) :
    (kaehlerBasisOfSeparating htr).coord () ω ∈ P.integers ↔
      ∀ u ∈ P.integers, P.kaehlerResidue hP ht htr (u • ω) = 0 := by
  let _ : FiniteDimensional k P.ResidueField :=
    .of_finrank_eq_succ (P.degree_eq_finrank.symm.trans hP)
  let _ := P.isSeparable_residueField_of_degree_eq_one hP
  rw [P.coord_mem_integers_iff_forall_traceResidue_coord_smul_eq_zero ht htr]
  simp_rw [← P.kaehlerResidue_eq_traceResidue_coord hP ht htr]

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
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [P.mem_range_map_iff_coord_mem_integers ht htr,
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

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k]
  (P : Place k F) (hP : P.degree = 1) (hF : IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]

/-- Over a perfect field, a Kähler differential comes from the valuation ring of a rational
place exactly when its residue pairing with every integral function vanishes. No uniformizer
is part of the statement. -/
theorem mem_range_map_iff_forall_kaehlerResidueOfPerfectField_smul_eq_zero (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers, P.kaehlerResidueOfPerfectField hP hF (u • ω) = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [P.mem_range_map_iff_coord_mem_integers ht htr,
    P.coord_mem_integers_iff_forall_kaehlerResidue_smul_eq_zero hP ht htr,
    P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF htr]

/-- Over a perfect exact constant field, the image of local Kähler differentials at a place of any
degree is the annihilator of its valuation ring for the local component of the Kähler–Weil
comparison, without choosing a uniformizer. -/
theorem mem_range_map_iff_forall_repartitionDualComponent_eq_zero (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
            Module.Dual k ↥(repartitionSpace k F)) P u = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.finiteDimensional_residueField hF
  have := P.isSeparable_residueField_of_perfectField hF
  rw [P.mem_range_map_iff_coord_mem_integers ht htr,
    P.coord_mem_integers_iff_forall_traceResidue_coord_smul_eq_zero ht htr]
  simp_rw [P.traceResidue_coord_smul_eq_repartitionDualComponent_of_perfectField hF hex hx ht htr]

/-- Over a perfect exact constant field, a nonzero Weil differential has nonnegative order at a
place of any degree exactly when its corresponding Kähler differential comes from that place's
valuation ring. No uniformizer is part of the statement. -/
theorem mem_range_map_iff_weilDifferentialOrder_nonneg
    (ω : weilDifferentialSpace k F)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm ω ∈
        (KaehlerDifferential.map k k P.integers F).range ↔
      0 ≤ weilDifferentialOrder hF hex ω.2 hω P := by
  rw [P.mem_range_map_iff_forall_repartitionDualComponent_eq_zero hF hex hx,
    LinearEquiv.apply_symm_apply, le_weilDifferentialOrder_iff hF hex ω.2 hω P 0]
  simp only [WithZero.exp_zero, ← P.mem_integers_iff]

end TauCeti.Place
