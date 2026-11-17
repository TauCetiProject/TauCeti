/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.Invariant.DiscreteValuationRing
public import TauCeti.RingTheory.LocalRing.Herbrand
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import TauCeti.NumberTheory.RamificationInertia.Galois
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Invariant.Galois
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Herbrand's lemma in the lower numbering for discrete valuation rings

Let a finite group `G` act on a discrete valuation ring `B` by ring automorphisms, and let `H ⊴ G`
be a normal subgroup. Assuming the residue field extension `𝓀(B) / 𝓀(B^G)` is separable — with
neither completeness nor finiteness of the residue field, nor faithfulness of the `G`-action — this
file establishes Serre's quotient formula for the lower index and proves Herbrand's lemma in the
lower numbering: `(G ⧸ H)_{φ_H(u)} = G_u H / H` and `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for all
`u : ℝ`.

## Main results

* `TauCeti.IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul`: `v_S(a) = e · v_R(a)`
  for a faithful local homomorphism of DVRs.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_eq_ramificationIdx`: `#G_0 = e` for a
  faithful finite group action on a DVR with separable residue extension.
* `TauCeti.IsLocalRing.isSeparable_residueField_subring_of_isInvariant`: transferring residue
  separability from an invariant local base ring `A` to `FixedPoints.subring B G`.
* `TauCeti.IsLocalRing.ramificationGroupReal_quotient_subring_herbrandFun_eq_map`:
  `(G ⧸ H)_{φ_H(u)} = G_u H / H` for all `u : ℝ`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_quotient_subring_mul`:
  `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for all `u : ℝ`.

## References

* [J.-P. Serre, *Local Fields*][serre1979], Chapter IV, §§1, 3, Propositions 3 and 14.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 3.
* Adapts `TauCeti/NumberTheory/LocalField/LowerIndex.lean` and
  `TauCeti/NumberTheory/LocalField/Herbrand/Quotient.lean` to arbitrary DVRs via
  `TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top` and
  `TauCeti.MulSemiringAction.charpoly_dvd`.
-/

public section
noncomputable section

open Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.IsDiscreteValuationRing

/-- For a faithful local homomorphism of discrete valuation rings `R → S`, the additive valuation
scales by the ramification index: `v_S(a) = e · v_R(a)`. -/
theorem addVal_algebraMap_eq_ramificationIdx_mul {R S : Type*}
    [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [FaithfulSMul R S] (x : R) :
    _root_.IsDiscreteValuationRing.addVal S (algebraMap R S x) =
      ((_root_.IsLocalRing.maximalIdeal S).ramificationIdx R : ℕ∞) *
        _root_.IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  have hϖ_ne : algebraMap R S ϖ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).2 hϖ.ne_zero
  have hmap_ne : (_root_.IsLocalRing.maximalIdeal R).map (algebraMap R S) ≠ ⊥ := fun hbot ↦
    hϖ_ne <| Ideal.mem_bot.1 <| hbot ▸ Ideal.mem_map_of_mem _
      ((_root_.IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hmap := TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap_ne
  set e := (_root_.IsLocalRing.maximalIdeal S).ramificationIdx R
  have he_ne : e ≠ 0 := fun he0 ↦
    (_root_.IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
      (by simpa [he0, Ideal.one_eq_top] using hmap)
  have hϖ_assoc : Associated (algebraMap R S ϖ) (π ^ e) := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
      ← hmap, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ_val : _root_.IsDiscreteValuationRing.addVal S (algebraMap R S ϖ) = e := by
    rw [(_root_.IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 hϖ_assoc, hπ.addVal_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, AddValuation.map_zero, AddValuation.map_zero,
      ENat.mul_top (Nat.cast_ne_zero.2 he_ne)]
  · obtain ⟨n, u, rfl⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    have hu : _root_.IsDiscreteValuationRing.addVal S (algebraMap R S u) = 0 :=
      _root_.IsDiscreteValuationRing.addVal_eq_zero_of_unit (u.map (algebraMap R S : R →* S))
    rw [_root_.IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow,
      AddValuation.map_mul, AddValuation.map_pow, hu, zero_add, hϖ_val, nsmul_eq_mul, mul_comm]

end TauCeti.IsDiscreteValuationRing

namespace TauCeti.IsLocalRing

section Setup

/-- For a faithful group action on a commutative ring `B`, `G` is a Galois group for `B` over
`B^G`. -/
private theorem isGaloisGroup_fixedPoints_subring (B G : Type*) [CommRing B]
    [Group G] [MulSemiringAction G B] [FaithfulSMul G B] :
    IsGaloisGroup G (FixedPoints.subring B G) B where
  faithful := inferInstance
  commutes := ⟨fun g r b ↦ by
    change g • ((r : B) * b) = (r : B) * (g • b)
    rw [smul_mul', r.2 g]⟩
  isInvariant := inferInstance

/-- If `A` and `B` are DVRs and `B` is integral over `A`, then `A → B` is faithful. -/
private theorem faithfulSMul_of_isIntegral_dvr (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra.IsIntegral A B] : FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero (algebraMap A B) hϖ fun h0 ↦ ?_
  have hker : RingHom.ker (algebraMap A B) = _root_.IsLocalRing.maximalIdeal A :=
    le_antisymm (_root_.IsLocalRing.le_maximalIdeal (by
      rw [ne_eq, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]; exact one_ne_zero))
      (by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]; exact h0)
  have : (RingHom.ker (algebraMap A B)).IsMaximal := hker ▸ inferInstance
  have hfield : IsField (algebraMap A B).range :=
    (RingHom.quotientKerEquivRange (algebraMap A B)).symm.toMulEquiv.isField
      (Ideal.Quotient.field _).toIsField
  let : Algebra A (algebraMap A B).range := (algebraMap A B).rangeRestrict.toAlgebra
  have : IsScalarTower A (algebraMap A B).range B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral (algebraMap A B).range B := Algebra.IsIntegral.tower_top (R := A)
  exact IsDiscreteValuationRing.not_isField B <|
    (Algebra.IsIntegral.isField_iff_isField Subtype.val_injective).1 hfield

/-- For a faithful local homomorphism of DVRs with separable residue extension,
`Algebra.HasSeparableResidueFieldsAt` holds at the prime under the maximal ideal. -/
private theorem hasSeparableResidueFieldsAt_under_maximalIdeal (R S : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [FaithfulSMul R S]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField R) (_root_.IsLocalRing.ResidueField S)] :
    Algebra.HasSeparableResidueFieldsAt R S ((_root_.IsLocalRing.maximalIdeal S).under R) where
  isSeparable' q hq hq_over := by
    have hunder : (_root_.IsLocalRing.maximalIdeal S).under R = _root_.IsLocalRing.maximalIdeal R :=
      _root_.IsLocalRing.maximalIdeal_comap (algebraMap R S)
    have hq_ne : q ≠ ⊥ := by
      rintro rfl
      exact IsDiscreteValuationRing.not_a_field R <| hunder.symm.trans <| hq_over.over.trans <|
        Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R S)
    have hq_eq : q = _root_.IsLocalRing.maximalIdeal S :=
      _root_.IsLocalRing.eq_maximalIdeal (hq.isMaximal hq_ne)
    subst hq_eq
    have : ((_root_.IsLocalRing.maximalIdeal S).under R).IsMaximal := hunder ▸ inferInstance
    let p := (_root_.IsLocalRing.maximalIdeal S).under R
    let q' := _root_.IsLocalRing.maximalIdeal S
    let := Localization.AtPrime.algebraOfLiesOver p q'
    let eR : _root_.IsLocalRing.ResidueField R ≃+* p.ResidueField :=
      (Ideal.quotEquivOfEq hunder.symm).trans
        (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    let eS : _root_.IsLocalRing.ResidueField S ≃+* q'.ResidueField :=
      RingEquiv.ofBijective _ q'.bijective_algebraMap_quotient_residueField
    refine Algebra.IsSeparable.of_equiv_equiv eR eS ?_
    ext x
    obtain ⟨r, rfl⟩ := _root_.IsLocalRing.residue_surjective x
    change algebraMap p.ResidueField q'.ResidueField
        (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)) =
      algebraMap (S ⧸ q') q'.ResidueField
        (_root_.IsLocalRing.ResidueField.map (algebraMap R S) (_root_.IsLocalRing.residue R r))
    rw [_root_.IsLocalRing.ResidueField.map_residue]
    change algebraMap p.ResidueField q'.ResidueField
        (algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p r)) =
      algebraMap (S ⧸ q') q'.ResidueField (Ideal.Quotient.mk q' (algebraMap R S r))
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← IsScalarTower.algebraMap_apply R p.ResidueField q'.ResidueField,
      ← IsScalarTower.algebraMap_apply R S q'.ResidueField]

/-- For a faithful finite group action on a DVR `B` with invariant DVR `A` and separable residue
extension, `#G_0` equals the ramification index of `B / A`. -/
theorem natCard_ramificationGroup_zero_eq_ramificationIdx (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [FaithfulSMul G B] :
    Nat.card (ramificationGroup G B 0) = (_root_.IsLocalRing.maximalIdeal B).ramificationIdx A := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := faithfulSMul_of_isIntegral_dvr A B
  let : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have := IsGaloisGroup.isGalois G (FractionRing A) (FractionRing B)
  have := IsGaloisGroup.finiteDimensional G (FractionRing A) (FractionRing B)
  have : Module.Finite A B := IsIntegralClosure.finite A (FractionRing A) (FractionRing B) B
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have : Module.Flat A B := inferInstance
  have : Algebra.HasSeparableResidueFieldsAt A B ((_root_.IsLocalRing.maximalIdeal B).under A) :=
    hasSeparableResidueFieldsAt_under_maximalIdeal A B
  rw [ramificationGroup_zero_eq_inertia,
    Ideal.card_inertia_eq_ramificationIdx A G (_root_.IsLocalRing.maximalIdeal B)]

/-- A DVR `B` is module-finite over `B^G` for a faithful finite group action. -/
private theorem module_finite_fixedPoints_subring (B G : Type*) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] :
    Module.Finite (FixedPoints.subring B G) B := by
  let := isGaloisGroup_fixedPoints_subring B G
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have := IsGaloisGroup.isGalois G (FractionRing (FixedPoints.subring B G)) (FractionRing B)
  have := IsGaloisGroup.finiteDimensional G (FractionRing (FixedPoints.subring B G))
    (FractionRing B)
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subring B G) B G
  exact IsIntegralClosure.finite (FixedPoints.subring B G)
    (FractionRing (FixedPoints.subring B G)) (FractionRing B) B

/-- If `A → B` is an invariant local homomorphism with separable residue extension, then
`𝓀(B) / 𝓀(B^G)` is also separable: `𝓀(A) → 𝓀(B^G)` is surjective, hence an isomorphism. -/
theorem isSeparable_residueField_subring_of_isInvariant
    (A B : Type*) [CommRing A] [_root_.IsLocalRing A]
    [CommRing B] [_root_.IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField A) (_root_.IsLocalRing.ResidueField B)]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B) := by
  let f : A →+* FixedPoints.subring B G :=
    (algebraMap A B).codRestrict (FixedPoints.subring B G) fun a g ↦ smul_algebraMap g a
  have hf_surj : Function.Surjective f := fun ⟨b, hb⟩ ↦ by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b hb
    exact ⟨a, Subtype.ext ha⟩
  have : IsLocalHom f := ⟨fun a ha ↦
    isUnit_of_map_unit (algebraMap A B) a (TauCeti.FixedPoints.isUnit_subring_iff.1 ha)⟩
  let fRes := _root_.IsLocalRing.ResidueField.map f
  have hfRes_surj : Function.Surjective fRes := fun y ↦ by
    obtain ⟨x, rfl⟩ := _root_.IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := hf_surj x
    exact ⟨_root_.IsLocalRing.residue A a, _root_.IsLocalRing.ResidueField.map_residue f a⟩
  refine Algebra.IsSeparable.of_equiv_equiv
    (RingEquiv.ofBijective fRes ⟨fRes.injective, hfRes_surj⟩) (RingEquiv.refl _) ?_
  ext x
  obtain ⟨a, rfl⟩ := _root_.IsLocalRing.residue_surjective x
  change _root_.IsLocalRing.ResidueField.map (algebraMap (FixedPoints.subring B G) B)
      (fRes (_root_.IsLocalRing.residue A a)) =
    _root_.IsLocalRing.ResidueField.map (algebraMap A B) (_root_.IsLocalRing.residue A a)
  rw [_root_.IsLocalRing.ResidueField.map_residue, _root_.IsLocalRing.ResidueField.map_residue,
    _root_.IsLocalRing.ResidueField.map_residue]
  rfl

end Setup

section Faithful

variable (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal]

/-- `FixedPoints.subring B G` embeds into `FixedPoints.subring B H` as a subring. -/
private def fixedSubringBotToMid : FixedPoints.subring B G →+* FixedPoints.subring B H where
  toFun x := ⟨x.1, fun h ↦ x.2 h.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsDiscreteValuationRing B] [Finite G] [FaithfulSMul G B] in
/-- Lower-index divisibility in one direction: `σ y - y` divides `(σ • charpoly H x)(x)`. -/
private theorem smul_sub_dvd_eval_smul_charpoly [Fintype H]
    [Algebra (FixedPoints.subring B G) (FixedPoints.subring B H)]
    [IsScalarTower (FixedPoints.subring B G) (FixedPoints.subring B H) B]
    {y : FixedPoints.subring B H} (hy : Algebra.adjoin (FixedPoints.subring B G) {y} = ⊤)
    (σ : G) (x : B) :
    σ • (y : B) - (y : B) ∣ (σ • MulSemiringAction.charpoly H x).eval x := by
  have hcomm : SMulCommClass (G ⧸ H) (FixedPoints.subring B G) (FixedPoints.subring B H) :=
    ⟨fun q r z ↦ Quotient.inductionOn' q fun g ↦ Subtype.ext <| by
      have hr : (algebraMap (FixedPoints.subring B G) (FixedPoints.subring B H) r : B) = r.1 :=
        congrArg (fun f : FixedPoints.subring B G →+* B ↦ f r)
          (IsScalarTower.algebraMap_eq (FixedPoints.subring B G) (FixedPoints.subring B H) B).symm
      rw [Algebra.smul_def, Algebra.smul_def]
      change g • ((algebraMap (FixedPoints.subring B G) (FixedPoints.subring B H) r * z :
          FixedPoints.subring B H) : B) =
        ((algebraMap (FixedPoints.subring B G) (FixedPoints.subring B H) r *
          ((QuotientGroup.mk g : G ⧸ H) • z) : FixedPoints.subring B H) : B)
      simp only [Subring.coe_mul, hr, smul_mul', r.2 g]
      rfl⟩
  set P := MulSemiringAction.charpoly H x
  rw [← sub_zero ((σ • P).eval x), ← MulSemiringAction.eval_charpoly H x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  have hw_mem : P.coeff n ∈ FixedPoints.subring B H := MulSemiringAction.smul_coeff_charpoly x n
  set w : FixedPoints.subring B H := ⟨P.coeff n, hw_mem⟩
  have hquot : ((QuotientGroup.mk σ : G ⧸ H) • w - w : FixedPoints.subring B H) =
      ⟨σ • P.coeff n - P.coeff n, sub_mem ((QuotientGroup.mk σ : G ⧸ H) • w).2 hw_mem⟩ := rfl
  have hdvd := smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (QuotientGroup.mk σ : G ⧸ H) w
  rw [coeff_sub, AddMonoidAlgebra.coeff_smul_apply]
  exact TauCeti.FixedPoints.dvd_subring_iff.1 (hquot ▸ hdvd)

omit [IsDiscreteValuationRing B] [Finite G] [H.Normal] in
/-- Lower-index divisibility in the reverse direction: `(σ • charpoly H x)(x)` divides `y - σ y`.
-/
private theorem eval_smul_charpoly_dvd_sub_smul [Fintype H]
    {x : B} (hx : Algebra.adjoin (FixedPoints.subring B G) {x} = ⊤)
    (y : FixedPoints.subring B H) (σ : G) :
    (σ • MulSemiringAction.charpoly H x).eval x ∣ (y : B) - σ • (y : B) := by
  have : SMulCommClass G (FixedPoints.subring B G) B :=
    (isGaloisGroup_fixedPoints_subring B G).commutes
  obtain ⟨q, hq⟩ : ∃ q : (FixedPoints.subring B G)[X], aeval x q = (y : B) := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
  set g := q.map (algebraMap (FixedPoints.subring B G) B) - C (y : B)
  have hg : ∀ τ : H, g.eval (τ • x) = 0 := fun τ ↦ by
    rw [eval_sub, eval_C, eval_map_algebraMap, Subgroup.smul_def, Polynomial.aeval_smul, hq,
      ← Subgroup.smul_def, y.2 τ, sub_self]
  have hinj : Function.Injective fun τ : H ↦ τ • x :=
    (smul_left_injective_of_adjoin_singleton_eq_top (G := G) hx).comp Subtype.val_injective
  obtain ⟨h, hh⟩ := TauCeti.MulSemiringAction.charpoly_dvd hinj hg
  have hσg : σ • g = q.map (algebraMap (FixedPoints.subring B G) B) - C (σ • (y : B)) := by
    have hmap : (MulSemiringAction.toRingHom G B σ).comp
        (algebraMap (FixedPoints.subring B G) B) = algebraMap (FixedPoints.subring B G) B :=
      RingHom.ext fun r ↦ smul_algebraMap σ r
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map, hmap]
  refine ⟨(σ • h).eval x, ?_⟩
  rw [← eval_mul, ← smul_mul', ← hh, hσg, eval_sub, eval_C, eval_map_algebraMap, hq]

omit [H.Normal] in
/-- Monogenic generators exist for `B` and `B^H` over `B^G`, and `𝓀(B)/𝓀(B^H)` is separable. -/
private theorem exists_adjoin_eq_top_and_separable_mid
    [Algebra (FixedPoints.subring B G) (FixedPoints.subring B H)]
    [IsScalarTower (FixedPoints.subring B G) (FixedPoints.subring B H) B]
    [IsLocalHom (algebraMap (FixedPoints.subring B G) (FixedPoints.subring B H))]
    [FaithfulSMul (FixedPoints.subring B G) (FixedPoints.subring B H)]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] :
    (∃ x : B, Algebra.adjoin (FixedPoints.subring B G) {x} = ⊤) ∧
      (∃ y : FixedPoints.subring B H, Algebra.adjoin (FixedPoints.subring B G) {y} = ⊤) ∧
      Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B H))
        (_root_.IsLocalRing.ResidueField B) := by
  have : Module.Finite (FixedPoints.subring B G) B := module_finite_fixedPoints_subring B G
  have : Module.Finite (FixedPoints.subring B G) (FixedPoints.subring B H) :=
    Module.Finite.of_injective
      (IsScalarTower.toAlgHom (FixedPoints.subring B G) (FixedPoints.subring B H) B).toLinearMap
      Subtype.val_injective
  have : Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField (FixedPoints.subring B H)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ (_root_.IsLocalRing.ResidueField B)
  exact ⟨TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top,
    TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top,
    Algebra.isSeparable_tower_top_of_isSeparable
      (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G)) _ _⟩

/-- **Serre's quotient formula for the lower index** on a DVR:
`#H_0 · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`. -/
private theorem natCard_ramificationGroup_zero_mul_lowerIndex_quotient_eq_sum [Fintype H]
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] (σ : G) :
    (Nat.card (ramificationGroup H B 0) : ℕ∞) *
        lowerIndex (FixedPoints.subring B H) (QuotientGroup.mk σ : G ⧸ H) =
      ∑ τ : H, lowerIndex B (σ * (τ : G)) := by
  let : Algebra (FixedPoints.subring B G) (FixedPoints.subring B H) :=
    (fixedSubringBotToMid B G H).toAlgebra
  have : IsScalarTower (FixedPoints.subring B G) (FixedPoints.subring B H) B :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FaithfulSMul (FixedPoints.subring B G) (FixedPoints.subring B H) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun _ _ h ↦
      Subtype.ext (congrArg (Subtype.val : FixedPoints.subring B H → B) h)
  have : IsLocalHom (algebraMap (FixedPoints.subring B G) (FixedPoints.subring B H)) :=
    ⟨fun _ h ↦ TauCeti.FixedPoints.isUnit_subring_iff.2
      (TauCeti.FixedPoints.isUnit_subring_iff (G := H).1 h)⟩
  have : SMulCommClass G (FixedPoints.subring B G) B :=
    (isGaloisGroup_fixedPoints_subring B G).commutes
  have : SMulCommClass H (FixedPoints.subring B H) B :=
    (isGaloisGroup_fixedPoints_subring B H).commutes
  have : SMulCommClass (G ⧸ H) (FixedPoints.subring B G) (FixedPoints.subring B H) :=
    ⟨fun q r z ↦ Quotient.inductionOn' q fun g ↦ Subtype.ext <| by
      change g • (r.1 * z.1) = r.1 * (g • z.1); rw [smul_mul', r.2 g]⟩
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hsep⟩ := exists_adjoin_eq_top_and_separable_mid B G H
  have key : IsDiscreteValuationRing.addVal B (σ • (y : B) - (y : B)) =
      IsDiscreteValuationRing.addVal B ((σ • MulSemiringAction.charpoly H x).eval x) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <| associated_of_dvd_dvd
      (smul_sub_dvd_eval_smul_charpoly B G H hy σ x)
      (dvd_sub_comm.1 (eval_smul_charpoly_dvd_sub_smul B G H hx y σ))
  have hprod : ∀ (s : Finset H) (f : H → B),
      IsDiscreteValuationRing.addVal B (∏ τ ∈ s, f τ) =
        ∑ τ ∈ s, IsDiscreteValuationRing.addVal B (f τ) := fun s f ↦ by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, AddValuation.map_mul, ih]
  rw [natCard_ramificationGroup_zero_eq_ramificationIdx (FixedPoints.subring B H) B H,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul]
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, AddValuation.map_sub_swap _ _ x,
    ← hprod, mul_smul, ← Subgroup.smul_def, ← TauCeti.MulSemiringAction.eval_smul_charpoly]
  exact key

omit [Finite G] [FaithfulSMul G B] [H.Normal] in
/-- If `σ` has largest lower index in `σ H`, then `i_G(σ τ) = min (i_H(τ), i_G(σ))`. -/
private theorem lowerIndex_mul_of_forall_le (σ : G)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) (τ : H) :
    lowerIndex B (σ * (τ : G)) = min (lowerIndex B τ) (lowerIndex B σ) := by
  have hτ : lowerIndex B τ = lowerIndex B (τ : G) := by rw [lowerIndex_def, lowerIndex_def]; rfl
  rw [hτ]
  have h₁ := min_le_lowerIndex_mul (S := B) σ (τ : G)
  have h₂ := min_le_lowerIndex_mul (S := B) σ⁻¹ (σ * (τ : G))
  rw [inv_mul_cancel_left, lowerIndex_inv, min_eq_right (hσ τ)] at h₂
  exact le_antisymm (le_min h₂ (hσ τ)) (by rw [min_comm]; exact h₁)

omit [FaithfulSMul G B] [H.Normal] in
/-- Every coset `σ H` contains an element of largest lower index. -/
private theorem exists_forall_lowerIndex_mul_le (σ : G) :
    ∃ τ₀ : H, ∀ τ : H,
      lowerIndex B (σ * (τ₀ : G) * (τ : G)) ≤ lowerIndex B (σ * (τ₀ : G)) := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨τ₀, -, hτ₀⟩ := Finset.exists_max_image (Finset.univ : Finset H)
    (fun τ ↦ lowerIndex B (σ * (τ : G))) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ ?_⟩
  simpa only [Subgroup.coe_mul, mul_assoc] using hτ₀ (τ₀ * τ) (Finset.mem_univ _)

/-- **Serre's lemma**: if `σ` has largest lower index `j` in `σ H`, then `i_{G/H}(σ H)` is finite
and `φ_H(j - 1) = i_{G/H}(σ H) - 1`. -/
private theorem herbrandFun_lowerIndex_sub_one
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)]
    (σ : G) {j : ℕ} (hj : lowerIndex B σ = j)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    lowerIndex (FixedPoints.subring B H) (QuotientGroup.mk σ : G ⧸ H) ≠ ⊤ ∧
      herbrandFun H B ((j : ℝ) - 1) =
        ((lowerIndex (FixedPoints.subring B H) (QuotientGroup.mk σ : G ⧸ H)).toNat : ℝ) - 1 := by
  classical
  let := Fintype.ofFinite H
  have hsum : (Nat.card (ramificationGroup H B 0) : ℕ∞) *
      lowerIndex (FixedPoints.subring B H) (QuotientGroup.mk σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
    rw [natCard_ramificationGroup_zero_mul_lowerIndex_quotient_eq_sum B G H σ]
    simp_rw [lowerIndex_mul_of_forall_le B G H σ hσ, hj]
    exact sum_min_lowerIndex_natCast (G := H) (S := B) j
  have hne : lowerIndex (FixedPoints.subring B H) (QuotientGroup.mk σ : G ⧸ H) ≠ ⊤ := fun htop ↦ by
    rw [htop, ENat.mul_top (by exact_mod_cast Nat.card_pos.ne'), ← Nat.cast_sum] at hsum
    exact ENat.natCast_ne_top _ hsum.symm
  refine ⟨hne, ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [← hn, ENat.toNat_natCast]
  rcases j with _ | m
  · rw [Nat.cast_zero, zero_sub, herbrandFun_neg_one]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast,
      div_eq_iff (by exact_mod_cast Nat.card_pos.ne')]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
        Nat.card (ramificationGroup H B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by exact_mod_cast hsum
    linear_combination -hsumR

/-- **Herbrand's lemma in the lower numbering** (faithful case). -/
private theorem ramificationGroupReal_quotient_herbrandFun_eq_map_faithful
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have hmax_iff (σ : G) (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
      (QuotientGroup.mk σ : G ⧸ H) ∈
          ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) ↔
        σ ∈ ramificationGroupReal G B u := by
    rcases eq_or_ne (lowerIndex B σ) ⊤ with htop | htop
    · rw [lowerIndex_eq_top_iff] at htop; subst htop; exact iff_of_true (one_mem _) (one_mem _)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
    obtain ⟨hne, hφ⟩ := herbrandFun_lowerIndex_sub_one B G H σ hj.symm hσ
    rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq (ENat.natCast_toNat hne).symm, ← hφ,
      mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm]
    exact (herbrandFun_strictMono H B).le_iff_le
  have hmk (σ : G) (τ₀ : H) :
      (QuotientGroup.mk (σ * (τ₀ : G)) : G ⧸ H) = QuotientGroup.mk σ := by
    rw [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]; exact H.inv_mem τ₀.2
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_le B G H σ
    exact ⟨σ * (τ₀ : G), (hmax_iff _ hτ₀).1 (hmk σ τ₀ ▸ hq), hmk σ τ₀⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_le B G H σ
    rw [QuotientGroup.mk'_apply, ← hmk σ τ₀, hmax_iff _ hτ₀]
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans (by simpa [mul_assoc] using hτ₀ τ₀⁻¹)

end Faithful

section GeneralSubring

variable (B G : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [Finite G] [MulSemiringAction G B]
  (H : Subgroup G) [H.Normal]

/-- The kernel of the action of `G` on `B`. -/
private abbrev actionKer : Subgroup G :=
  (MulSemiringAction.toRingAut G B).ker

/-- The faithful quotient `G ⧸ ker(G → Aut(B))` acts on `B`. -/
@[instance_reducible]
private def faithfulQuotientAction : MulSemiringAction (G ⧸ actionKer B G) B :=
  MulSemiringAction.compHom B
    (QuotientGroup.lift (actionKer B G) (MulSemiringAction.toRingAut G B) fun _ hx ↦ hx)

omit [IsDomain B] [IsDiscreteValuationRing B] [Finite G] in
private theorem faithfulSMul_faithfulQuotient :
    let := faithfulQuotientAction B G
    FaithfulSMul (G ⧸ actionKer B G) B := by
  let := faithfulQuotientAction B G
  refine ⟨fun {q₁ q₂} h ↦ QuotientGroup.induction_on q₁ (fun g₁ ↦
    QuotientGroup.induction_on q₂ (fun g₂ h ↦ ?_)) h⟩
  rw [QuotientGroup.eq]
  change MulSemiringAction.toRingAut G B (g₁⁻¹ * g₂) = 1
  ext x
  have h' : g₁ • x = g₂ • x := h x
  change (g₁⁻¹ * g₂) • x = x
  rw [mul_smul, ← h', inv_smul_smul]

/-- Passing to the faithful quotient does not change the fixed-point subring of `L ≤ G`. -/
private def fixedPointsSubringEquivFaithful (L : Subgroup G) :
    let := faithfulQuotientAction B G
    FixedPoints.subring B L ≃+* FixedPoints.subring B (L.map (QuotientGroup.mk' (actionKer B G)))
    where
  toFun x := ⟨x.1, fun ⟨_, g, hg, rfl⟩ ↦ x.2 ⟨g, hg⟩⟩
  invFun x := ⟨x.1, fun g ↦ x.2 ⟨QuotientGroup.mk g.1, g.1, g.2, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The quotient homomorphism `G ⧸ H →* (G ⧸ K) ⧸ (H K / K)`. -/
private def quotientToFaithfulQuotient :
    G ⧸ H →* (G ⧸ actionKer B G) ⧸ (H.map (QuotientGroup.mk' (actionKer B G))) :=
  QuotientGroup.map H (H.map (QuotientGroup.mk' (actionKer B G)))
    (QuotientGroup.mk' (actionKer B G)) (fun _ hh ↦ Subgroup.mem_map_of_mem _ hh)

omit [IsDomain B] [IsDiscreteValuationRing B] [Finite G] in
/-- Pulling back a subgroup image along the faithful-quotient square commutes with taking images. -/
private theorem map_mk'_comap_eq_comap_map_mk' (L : Subgroup (G ⧸ actionKer B G)) :
    (L.comap (QuotientGroup.mk' (actionKer B G))).map (QuotientGroup.mk' H) =
      (L.map (QuotientGroup.mk' (H.map (QuotientGroup.mk' (actionKer B G))))).comap
        (quotientToFaithfulQuotient B G H) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_map]
  refine ⟨fun ⟨g, hg, hgx⟩ ↦ ⟨QuotientGroup.mk g, hg, hgx ▸ rfl⟩, fun ⟨q, hq, hqx⟩ ↦ ?_⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective x
  have hmem : QuotientGroup.mk (g₀⁻¹ * g₁) ∈ H.map (QuotientGroup.mk' (actionKer B G)) := by
    have h' : (QuotientGroup.mk (QuotientGroup.mk g₀ : G ⧸ actionKer B G) :
        (G ⧸ actionKer B G) ⧸ H.map (QuotientGroup.mk' (actionKer B G))) =
        QuotientGroup.mk (QuotientGroup.mk g₁) := hqx
    rwa [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h'
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.1 hmem
  have hk : h⁻¹ * (g₀⁻¹ * g₁) ∈ actionKer B G := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq] at hgh
  set k := h⁻¹ * (g₀⁻¹ * g₁)
  refine ⟨g₀ * k, ?_, ?_⟩
  · rw [Subgroup.mem_comap, map_mul]
    simp only [QuotientGroup.mk'_apply]
    rwa [(QuotientGroup.eq_one_iff k).2 hk, mul_one]
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hconj : (g₀ * k)⁻¹ * g₁ = g₁⁻¹ * (g₀ * h * g₀⁻¹) * g₁ := by simp [k, mul_assoc]
    exact hconj ▸ by simpa [mul_assoc] using ‹H.Normal›.conj_mem' _ (‹H.Normal›.conj_mem h hh g₀) g₁

omit [Finite G] in
/-- Passing to the faithful quotient preserves residue separability over the fixed subring. -/
private theorem isSeparable_residueField_faithfulQuotient
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] :
    let := faithfulQuotientAction B G
    Algebra.IsSeparable
      (_root_.IsLocalRing.ResidueField (FixedPoints.subring B (G ⧸ actionKer B G)))
      (_root_.IsLocalRing.ResidueField B) := by
  let := faithfulQuotientAction B G
  have : SMulCommClass (G ⧸ actionKer B G) (FixedPoints.subring B G) B :=
    ⟨fun q r b ↦ QuotientGroup.induction_on q fun g ↦ by
      change g • (r.1 * b) = r.1 * (g • b); rw [smul_mul', r.2 g]⟩
  have : Algebra.IsInvariant (FixedPoints.subring B G) B (G ⧸ actionKer B G) :=
    ⟨fun b hb ↦ ⟨⟨b, fun g ↦ hb (QuotientGroup.mk g)⟩, rfl⟩⟩
  exact isSeparable_residueField_subring_of_isInvariant (FixedPoints.subring B G) B
    (G ⧸ actionKer B G)

/-- **Herbrand's lemma in the lower numbering** for `B^H`:
`(G ⧸ H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`. Neither completeness of `B`, finiteness of the
residue field, nor faithfulness of the `G`-action is required. -/
theorem ramificationGroupReal_quotient_subring_herbrandFun_eq_map
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  let := faithfulQuotientAction B G
  have := faithfulSMul_faithfulQuotient B G
  have := isSeparable_residueField_faithfulQuotient B G
  set q := QuotientGroup.mk' (actionKer B G)
  set H' := H.map q
  have hH_surj : Function.Surjective (q.subgroupMap H) := by
    rintro ⟨_, g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
  have hφH : herbrandFun H B u = herbrandFun H' B u :=
    herbrandFun_eq_of_surjective_ringEquiv (q.subgroupMap H) hH_surj (RingEquiv.refl B)
      (fun _ _ ↦ rfl) u
  have hQ : ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u) =
      (ramificationGroupReal ((G ⧸ actionKer B G) ⧸ H') (FixedPoints.subring B H')
        (herbrandFun H' B u)).comap (quotientToFaithfulQuotient B G H) := by
    rw [hφH]
    exact ramificationGroupReal_eq_comap_of_ringEquiv (quotientToFaithfulQuotient B G H)
      (fixedPointsSubringEquivFaithful B G H) (fun r _ ↦ QuotientGroup.induction_on r fun _ ↦ rfl) _
  have hG : ramificationGroupReal G B u =
      (ramificationGroupReal (G ⧸ actionKer B G) B u).comap q :=
    ramificationGroupReal_eq_comap_of_ringEquiv q (RingEquiv.refl B) (fun _ _ ↦ rfl) u
  rw [hQ, hG, ramificationGroupReal_quotient_herbrandFun_eq_map_faithful B _ H' u,
    map_mk'_comap_eq_comap_map_mk']

/-- **Counting form of Herbrand's lemma** for `B^H`:
`#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for every `u : ℝ`. -/
theorem natCard_ramificationGroupReal_quotient_subring_mul
    [Algebra.IsSeparable (_root_.IsLocalRing.ResidueField (FixedPoints.subring B G))
      (_root_.IsLocalRing.ResidueField B)] (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subring B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  rw [ramificationGroupReal_quotient_subring_herbrandFun_eq_map B G H u,
    ← MonoidHom.domRestrict_range, ← subgroupOf_ramificationGroupReal G B H u]
  have hker_card : Nat.card ((QuotientGroup.mk' H).domRestrict (ramificationGroupReal G B u)).ker =
      Nat.card ((ramificationGroupReal G B u).subgroupOf H) :=
    Nat.card_congr
      { toFun := fun x ↦ ⟨⟨x.1.1, by
          simpa [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] using x.2⟩, x.1.2⟩
        invFun := fun y ↦ ⟨⟨y.1.1, y.2⟩, by simp [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  rw [← hker_card, mul_comm, Subgroup.card_ker_mul_card_range]

end GeneralSubring

end TauCeti.IsLocalRing
