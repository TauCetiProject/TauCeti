/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.FixedPoints

/-!
# Fixed-point subrings and subalgebras of discrete valuation rings

Let a group `G` act by ring automorphisms on an integral domain `B`. Because multiplication by a
nonzero `G`-fixed element in `B` is cancellative, the quotient in `B` of two `G`-fixed elements is
itself `G`-fixed: inclusion from `FixedPoints.subring B G` or `FixedPoints.subalgebra A B G` into
`B` reflects divisibility without any finiteness assumption on `G`.

When `B` is a discrete valuation ring, choosing a nonzero element of minimal additive valuation in
any nonzero ideal shows that `FixedPoints.subring B G` and `FixedPoints.subalgebra A B G` are
principal ideal domains for arbitrary `G` (for infinite `G` the fixed ring may be a field). When `G`
is finite (or when `B` lies locally and faithfully over a discrete valuation ring `A`), the fixed
ring cannot be a field and is therefore a discrete valuation ring. Moreover, when a finite group `G`
acts faithfully on an integral domain `B` and `H ≤ G` is normal, the induced quotient action of
`G ⧸ H` on `FixedPoints.subring B H` and `FixedPoints.subalgebra A B H` is faithful.

## Main definitions and results

* `TauCeti.fixedPointsSubringEquivSubalgebra`: the canonical ring isomorphism
  `FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G`.
* `TauCeti.coe_quotient_smul_subalgebra`: coercion to `B` of the quotient action of `G ⧸ H` on
  `FixedPoints.subalgebra A B H`.
* `TauCeti.dvd_coe_fixedPoints_subring_iff`, `TauCeti.dvd_coe_fixedPoints_subalgebra_iff`:
  inclusion into an integral domain `B` reflects and preserves divisibility on `G`-fixed elements.
* `TauCeti.instIsPrincipalIdealRingFixedPointsSubring`,
  `TauCeti.instIsPrincipalIdealRingFixedPointsSubalgebra`: fixed-point subrings and subalgebras of a
  discrete valuation ring are principal ideal rings.
* `TauCeti.instIsDiscreteValuationRingFixedPointsSubring`,
  `TauCeti.instIsDiscreteValuationRingFixedPointsSubalgebra`: under a finite group action on a
  discrete valuation ring, the fixed-point subring and subalgebra are discrete valuation rings.
* `TauCeti.instFaithfulSMulQuotientFixedPointsSubring`,
  `TauCeti.instFaithfulSMulQuotientFixedPointsSubalgebra`: for a faithful action of a finite group
  `G` on a domain `B` and normal `H ≤ G`, `G ⧸ H` acts faithfully on `B^H`.
-/

public section

open IsLocalRing

namespace TauCeti

section CommRing

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]
  [SMulCommClass G A B]

/-- The canonical ring isomorphism between `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G`. -/
def fixedPointsSubringEquivSubalgebra :
    FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Coercion to `B` of the quotient action of `G ⧸ H` on `FixedPoints.subalgebra A B H`. -/
@[simp]
theorem coe_quotient_smul_subalgebra (H : Subgroup G) [H.Normal] (g : G)
    (y : FixedPoints.subalgebra A B H) :
    (((QuotientGroup.mk g : G ⧸ H) • y : FixedPoints.subalgebra A B H) : B) = g • (y : B) :=
  rfl

/-- `QuotientGroup.mk'` form of `coe_quotient_smul_subalgebra`. -/
theorem coe_quotient_mk'_smul_subalgebra (H : Subgroup G) [H.Normal] (g : G)
    (y : FixedPoints.subalgebra A B H) :
    (((QuotientGroup.mk' H g) • y : FixedPoints.subalgebra A B H) : B) = g • (y : B) :=
  rfl

end CommRing

section Domain

variable {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- Inclusion `FixedPoints.subring B G →+* B` into an integral domain reflects and preserves
divisibility. -/
@[simp]
theorem dvd_coe_fixedPoints_subring_iff {x y : FixedPoints.subring B G} :
    (x : B) ∣ (y : B) ↔ x ∣ y := by
  refine ⟨?_, (FixedPoints.subring B G).subtype.map_dvd⟩
  rintro ⟨q, hq⟩
  by_cases hx : x = 0
  · subst hx
    have hy : y = 0 := Subtype.ext (by simpa using hq)
    simp [hy]
  · have hxB : (x : B) ≠ 0 := Subtype.coe_ne_coe.2 hx
    refine ⟨⟨q, fun g ↦ mul_left_cancel₀ hxB ?_⟩, Subtype.ext hq⟩
    calc
      (x : B) * (g • q) = g • (x : B) * (g • q) := by rw [x.2 g]
      _ = g • ((x : B) * q) := (smul_mul' g (x : B) q).symm
      _ = (x : B) * q := by rw [← hq, y.2 g]

/-- Inclusion `FixedPoints.subalgebra A B G →+* B` into an integral domain reflects and preserves
divisibility. -/
@[simp]
theorem dvd_coe_fixedPoints_subalgebra_iff [SMulCommClass G A B]
    {x y : FixedPoints.subalgebra A B G} :
    (x : B) ∣ (y : B) ↔ x ∣ y :=
  ⟨fun h ↦ (fixedPointsSubringEquivSubalgebra (A := A)).toRingHom.map_dvd
    (dvd_coe_fixedPoints_subring_iff (x := ⟨x.1, x.2⟩) (y := ⟨y.1, y.2⟩) |>.1 h),
    (algebraMap (FixedPoints.subalgebra A B G) B).map_dvd⟩

/-- If a finite group `G` acts faithfully on an integral domain `B` and `H ≤ G` is normal, then the
quotient `G ⧸ H` acts faithfully on `FixedPoints.subalgebra A B H`. -/
instance instFaithfulSMulQuotientFixedPointsSubalgebra [Finite G] [FaithfulSMul G B]
    [SMulCommClass G A B] (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subalgebra A B H) where
  eq_of_smul_eq_smul {q₁ q₂} hq := by
    let _ := Fintype.ofFinite H
    refine Quotient.inductionOn₂' q₁ q₂ (fun g₁ g₂ ↦ ?_) hq
    intro h
    have hcomp : (MulSemiringAction.toRingHom G B g₁).comp
        (algebraMap (FixedPoints.subalgebra A B H) B) =
        (MulSemiringAction.toRingHom G B g₂).comp
          (algebraMap (FixedPoints.subalgebra A B H) B) := by
      ext c
      exact congrArg Subtype.val (h c)
    obtain ⟨k, hk⟩ := Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq
      (FixedPoints.subalgebra A B H) H _ _ hcomp
    have hgk : g₁ * (k : G) = g₂ := eq_of_smul_eq_smul fun b : B ↦ by
      simpa [mul_smul, Subgroup.smul_def] using RingHom.congr_fun hk b
    exact QuotientGroup.eq.2 (by rw [← hgk, inv_mul_cancel_left]; exact k.2)

/-- If a finite group `G` acts faithfully on an integral domain `B` and `H ≤ G` is normal, then the
quotient `G ⧸ H` acts faithfully on `FixedPoints.subring B H`. -/
instance instFaithfulSMulQuotientFixedPointsSubring [Finite G] [FaithfulSMul G B]
    (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subring B H) :=
  inferInstanceAs (FaithfulSMul (G ⧸ H) (FixedPoints.subalgebra ℤ B H))

end Domain

section IsDiscreteValuationRing

variable {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

/-- The fixed-point subring of a discrete valuation ring under any group action is a principal ideal
ring. -/
instance instIsPrincipalIdealRingFixedPointsSubring :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    by_cases hI : I = ⊥
    · exact ⟨0, by simp [hI]⟩
    obtain ⟨x₀, hx₀I, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : {x : FixedPoints.subring B G // x ∈ I ∧ x ≠ 0} → ℕ :=
      fun z ↦ (_root_.IsDiscreteValuationRing.addVal B (z.1 : B)).toNat
    obtain ⟨⟨a, haI, ha0⟩, -, hmin⟩ :=
      (InvImage.wf f Nat.lt_wfRel.wf).has_min Set.univ ⟨⟨x₀, hx₀I, hx₀0⟩, trivial⟩
    refine ⟨a, le_antisymm (fun y hyI ↦ ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 haI))⟩
    by_cases hy0 : y = 0
    · simp [hy0]
    have hle_nat : f ⟨a, haI, ha0⟩ ≤ f ⟨y, hyI, hy0⟩ :=
      not_lt.1 (hmin ⟨y, hyI, hy0⟩ trivial)
    have ha_top : _root_.IsDiscreteValuationRing.addVal B (a : B) ≠ ⊤ :=
      _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 ha0)
    have hy_top : _root_.IsDiscreteValuationRing.addVal B (y : B) ≠ ⊤ :=
      _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 hy0)
    have hle : _root_.IsDiscreteValuationRing.addVal B (a : B) ≤
        _root_.IsDiscreteValuationRing.addVal B (y : B) := by
      rw [← ENat.natCast_toNat ha_top, ← ENat.natCast_toNat hy_top]
      exact_mod_cast hle_nat
    exact Ideal.mem_span_singleton.2
      (dvd_coe_fixedPoints_subring_iff.1 (_root_.IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle))

/-- The fixed-point subalgebra of a discrete valuation ring under any group action is a principal
ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubalgebra [SMulCommClass G A B] :
    IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  IsPrincipalIdealRing.of_surjective
    (fixedPointsSubringEquivSubalgebra (A := A) (B := B) (G := G)).toRingHom
    (fixedPointsSubringEquivSubalgebra (A := A) (B := B) (G := G)).surjective

/-- The fixed-point subalgebra of a discrete valuation ring under a finite group action is a
discrete valuation ring. -/
instance instIsDiscreteValuationRingFixedPointsSubalgebra [Finite G] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := by
    have hint : Algebra.IsIntegral (FixedPoints.subalgebra A B G) B :=
      Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B G) B G
    exact _root_.IsDiscreteValuationRing.not_isField B
      ((hint.isField_iff_isField
        (FaithfulSMul.algebraMap_injective (FixedPoints.subalgebra A B G) B)).mp
        (isField_iff_maximalIdeal_eq.2 hbot))

/-- The fixed-point subring of a discrete valuation ring under a finite group action is a discrete
valuation ring. -/
instance instIsDiscreteValuationRingFixedPointsSubring [Finite G] :
    _root_.IsDiscreteValuationRing (FixedPoints.subring B G) where
  not_a_field' hbot :=
    _root_.IsDiscreteValuationRing.not_isField (FixedPoints.subalgebra ℤ B G)
      ((fixedPointsSubringEquivSubalgebra (A := ℤ) (B := B) (G := G)).symm.toMulEquiv.isField
        (isField_iff_maximalIdeal_eq.2 hbot))

/-- When `B` lies locally and faithfully over a discrete valuation ring `A`, the fixed-point
subalgebra `FixedPoints.subalgebra A B G` is a discrete valuation ring for any (possibly infinite)
group `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isLocalHom
    [IsDomain A] [_root_.IsDiscreteValuationRing A] [IsLocalHom (algebraMap A B)]
    [FaithfulSMul A B] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := by
    obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
    have hmem : algebraMap A (FixedPoints.subalgebra A B G) ϖ ∈
        maximalIdeal (FixedPoints.subalgebra A B G) :=
      map_nonunit (algebraMap A (FixedPoints.subalgebra A B G)) ϖ
        ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit))
    rw [hbot, Ideal.mem_bot] at hmem
    have h0 : algebraMap A B ϖ = 0 := by
      rw [IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B G) B, hmem, map_zero]
    exact hϖ.ne_zero (FaithfulSMul.algebraMap_injective A B (h0.trans (map_zero _).symm))

end IsDiscreteValuationRing

end TauCeti
