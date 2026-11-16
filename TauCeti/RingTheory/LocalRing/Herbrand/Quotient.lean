/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.RingTheory.Invariant.LocalRing
public import TauCeti.RingTheory.LocalRing.Herbrand.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Herbrand's theorem, transitivity, and quotient compatibility of the upper numbering

Let a finite group `G` act faithfully by `A`-algebra automorphisms on a discrete valuation ring `B`
with invariant ring a discrete valuation ring `A` and separable residue extension
`ResidueField A → ResidueField B`. For any normal subgroup `H` of `G`, the fixed subalgebra
`C = FixedPoints.subalgebra A B H` is automatically a discrete valuation ring
(`TauCeti.FixedPoints.instIsDiscreteValuationRingSubalgebra`) on which `G ⧸ H` acts faithfully with
invariant ring `A`.

Under these hypotheses — without assuming completeness of `A` or finiteness of the residue field —
this file proves Serre's quotient formula for the lower index, **Herbrand's theorem** on the lower
and upper filtrations, and **transitivity of the Herbrand functions**:

* `e(B/C) · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` (first in monogenic generality without residue
  separability, then with `e(B/C) = #H_0`);
* `(G/H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`;
* `φ_G(u) = φ_{G/H}(φ_H(u))` and `ψ_G(v) = ψ_H(ψ_{G/H}(v))` for every `u, v : ℝ`;
* `(G/H)^v = G^v H / H` and `H ∩ G^v = H^{ψ_{G/H}(v)}` for every `v : ℝ`;
* `v` is an upper jump of `G` if and only if `v` is an upper jump of `G ⧸ H` or `ψ_{G/H}(v)` is an
  upper jump of `H`.

We also deduce the field-theoretic form for a finite Galois extension `L/K` of fraction fields of
discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field `E = L^H`, identifying
the quotient action on `FixedPoints.subalgebra A (integralClosure A L) H` with the action of
`Gal(E/K)` on `integralClosure A E` along `IsGalois.normalAutEquivQuotient H`.

These results generalize the nonarchimedean local-field development in
`TauCeti/NumberTheory/LocalField/LowerIndex.lean` and
`TauCeti/NumberTheory/LocalField/Herbrand/{Quotient,Tower,UpperQuotient}.lean` to arbitrary
discrete valuation rings with separable residue extensions.

## Main results

* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_of_adjoin_eq_top`: Serre's quotient
  lower-index formula in the monogenic setting.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_eq_ramificationIdx`: `#G_0 = e(B/A)` for a
  separable residue extension.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum`:
  `#H_0 · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`.
* `TauCeti.IsLocalRing.herbrandFun_lowerIndex_sub_one`: Serre's lemma
  `φ_H(i_G(σ) - 1) = i_{G/H}(σ H) - 1` for `σ` maximizing the lower index in its coset.
* `TauCeti.IsLocalRing.map_quotientMk'_ramificationGroupReal`: Herbrand's theorem on the lower
  filtration, `(G_u).map (QuotientGroup.mk' H) = (G ⧸ H)_{φ_H(u)}`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_quotient_herbrandFun_mul`: counting form
  `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`.
* `TauCeti.IsLocalRing.herbrandFun_tower`: transitivity `φ_G = φ_{G ⧸ H} ∘ φ_H` on `ℝ`.
* `TauCeti.IsLocalRing.inverseHerbrandFun_tower`, `TauCeti.IsLocalRing.herbrandOrderIso_tower`,
  `TauCeti.IsLocalRing.psiNat_tower`: transitivity of `ψ`, `herbrandOrderIso`, and `ψℕ`.
* `TauCeti.IsLocalRing.upperRamificationGroup_quotient_eq_map`: Herbrand's theorem in the upper
  numbering, `(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)`.
* `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_of_normal`:
  `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}`.
* `TauCeti.IsLocalRing.upperJump_iff_quotient_or_subgroup`: characterization of upper jumps in a
  quotient.
* `TauCeti.IsLocalRing.fixedPointsIntegralClosureEquiv`,
  `TauCeti.IsLocalRing.isDiscreteValuationRing_integralClosure_fixedField`,
  `TauCeti.IsLocalRing.herbrandFun_fixedField_tower`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_fixedField_tower`,
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_fixedField`,
  `TauCeti.IsLocalRing.upperRamificationGroup_fixedField_eq_map`,
  `TauCeti.IsLocalRing.map_restrictNormalHom_upperRamificationGroup`: field-theoretic form through
  `IsGalois.normalAutEquivQuotient`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1 Proposition 3 and §3 Lemmas 4–5,
  Propositions 14–15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, Propositions 3–4.
-/

public section
noncomputable section

open IsLocalRing Polynomial

namespace TauCeti.IsLocalRing

/-! ### Serre's quotient formula for the lower index in the monogenic setting -/

section Monogenic

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  (H : Subgroup G) [H.Normal]

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- The displacement `σ • y - y` of an algebra generator `y` of `B^H` over `A` divides
`(σ • charpoly H x).eval x`: every coefficient of `charpoly H x` lies in `B^H`, and
`(charpoly H x).eval x = 0`. -/
private theorem smul_sub_dvd_eval_smul_charpoly [Fintype H]
    {y : FixedPoints.subalgebra A B H} (hy : Algebra.adjoin A {y} = ⊤) (σ : G) (x : B) :
    σ • (y : B) - (y : B) ∣ (σ • MulSemiringAction.charpoly H x).eval x := by
  set P := MulSemiringAction.charpoly H x
  rw [← sub_zero ((σ • P).eval x), ← MulSemiringAction.eval_charpoly H x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  let w : FixedPoints.subalgebra A B H := ⟨P.coeff n, MulSemiringAction.smul_coeff_charpoly x n⟩
  have hmem : ((QuotientGroup.mk σ : G ⧸ H) • y - y : FixedPoints.subalgebra A B H) ∣
      ((QuotientGroup.mk σ : G ⧸ H) • w - w) :=
    TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (QuotientGroup.mk σ : G ⧸ H) w
  have hsmul : ∀ z : FixedPoints.subalgebra A B H,
      (((QuotientGroup.mk σ : G ⧸ H) • z : FixedPoints.subalgebra A B H) : B) = σ • (z : B) :=
    fun _ ↦ rfl
  have hdvd : σ • (y : B) - (y : B) ∣ σ • P.coeff n - P.coeff n := by
    simpa [w, hsmul] using map_dvd (FixedPoints.subalgebra A B H).val hmem
  simpa [P, coeff_sub, AddMonoidAlgebra.coeff_smul_apply] using hdvd

omit [IsDiscreteValuationRing B] [H.Normal] in
/-- Conversely, `(σ • charpoly H x).eval x` divides `y - σ • y` for every `y ∈ B^H` when `x`
generates `B` over `A` and `G` acts faithfully on `B`. -/
private theorem eval_smul_charpoly_dvd_sub_smul [Fintype H] [FaithfulSMul G B]
    {x : B} (hx : Algebra.adjoin A {x} = ⊤) (y : FixedPoints.subalgebra A B H) (σ : G) :
    (σ • MulSemiringAction.charpoly H x).eval x ∣ (y : B) - σ • (y : B) := by
  obtain ⟨q, hq⟩ : ∃ q : A[X], aeval x q = (y : B) := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
  set g := q.map (algebraMap A B) - C (y : B)
  have hg : ∀ τ : H, g.eval (τ • x) = 0 := fun τ ↦ by
    rw [eval_sub, eval_C, eval_map_algebraMap, Subgroup.smul_def, Polynomial.aeval_smul, hq,
      ← Subgroup.smul_def, y.2 τ, sub_self]
  have hinj : Function.Injective fun τ : H ↦ τ • x := by
    simpa [Function.comp_def, Subgroup.smul_def] using
      (TauCeti.smul_left_injective_of_adjoin_singleton_eq_top (G := G) hx).comp
        Subtype.val_injective
  obtain ⟨h, hh⟩ := TauCeti.MulSemiringAction.charpoly_dvd hinj hg
  have hσg : σ • g = q.map (algebraMap A B) - C (σ • (y : B)) := by
    have hmap : (MulSemiringAction.toRingHom G B σ).comp (algebraMap A B) = algebraMap A B :=
      RingHom.ext fun r ↦ smul_algebraMap σ r
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map, hmap]
  refine ⟨(σ • h).eval x, ?_⟩
  rw [← eval_mul, ← smul_mul', ← hh, hσg, eval_sub, eval_C, eval_map_algebraMap, hq]

/-- **Serre's quotient formula for the lower index in the monogenic setting.** Let a group `G`
act faithfully on a discrete valuation ring `B` commuting with a base ring `A`, and let `H` be a
finite normal subgroup of `G`. If `B` and `B^H` are each monogenic over `A`, then
`e(B / B^H) · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` in `ℕ∞`. Neither residue separability nor a
discrete valuation ring structure on `A` is needed. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_sum_of_adjoin_eq_top [Fintype H] [FaithfulSMul G B]
    {x : B} (hx : Algebra.adjoin A {x} = ⊤)
    {y : FixedPoints.subalgebra A B H} (hy : Algebra.adjoin A {y} = ⊤) (σ : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ τ : H, lowerIndex B (σ * (τ : G)) := by
  have key : _root_.IsDiscreteValuationRing.addVal B (σ • (y : B) - (y : B)) =
      _root_.IsDiscreteValuationRing.addVal B ((σ • MulSemiringAction.charpoly H x).eval x) :=
    (_root_.IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <|
      associated_of_dvd_dvd (smul_sub_dvd_eval_smul_charpoly H hy σ x)
        (dvd_sub_comm.1 (eval_smul_charpoly_dvd_sub_smul H hx y σ))
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, ← nsmul_eq_mul,
    ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap, AddValuation.map_sub_swap _ _ x,
    ← AddValuation.map_prod, mul_smul, ← Subgroup.smul_def,
    ← TauCeti.MulSemiringAction.eval_smul_charpoly]
  exact key

end Monogenic

/-! ### Coset maxima of the lower index -/

section CosetMax

variable {G B : Type*} [Group G] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [MulSemiringAction G B]

/-- If `σ` maximizes `lowerIndex B` in its coset `σ H`, then
`i_G(σ τ) = min (i_H(τ), i_G(σ))` for every `τ ∈ H`. -/
theorem lowerIndex_mul_of_forall_le {H : Subgroup G} (σ : G)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) (τ : H) :
    lowerIndex B (σ * (τ : G)) = min (lowerIndex B τ) (lowerIndex B σ) := by
  have hτ : lowerIndex B τ = lowerIndex B (τ : G) := by
    simp only [lowerIndex_def, Subgroup.smul_def]
  rw [hτ]
  have h₁ := min_le_lowerIndex_mul (S := B) σ (τ : G)
  have h₂ := min_le_lowerIndex_mul (S := B) σ⁻¹ (σ * (τ : G))
  rw [inv_mul_cancel_left, lowerIndex_inv, min_eq_right (hσ τ)] at h₂
  exact le_antisymm (le_min h₂ (hσ τ)) (by rw [min_comm]; exact h₁)

/-- For a finite subgroup `H ≤ G`, every coset `σ H` contains an element maximizing
`lowerIndex B`. -/
theorem exists_forall_lowerIndex_mul_le (H : Subgroup G) [Finite H] (σ : G) :
    ∃ τ₀ : H, ∀ τ : H,
      lowerIndex B (σ * (τ₀ : G) * (τ : G)) ≤ lowerIndex B (σ * (τ₀ : G)) := by
  cases nonempty_fintype H
  obtain ⟨τ₀, -, hτ₀⟩ := Finset.exists_max_image (Finset.univ : Finset H)
    (fun τ ↦ lowerIndex B (σ * (τ : G))) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ ?_⟩
  have h := hτ₀ (τ₀ * τ) (Finset.mem_univ _)
  simpa only [Subgroup.coe_mul, mul_assoc] using h

end CosetMax

/-! ### Auxiliary structural facts for DVR invariant extensions -/

section Helpers

/-- An integral ring homomorphism between discrete valuation rings is injective. -/
private theorem faithfulSMul_of_isDiscreteValuationRing_of_isIntegral
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hprime : (RingHom.ker (algebraMap A B)).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap A B)).IsMaximal := hprime.isMaximal hne
  let : Field (A ⧸ RingHom.ker (algebraMap A B)) := Ideal.Quotient.field _
  let : Algebra (A ⧸ RingHom.ker (algebraMap A B)) B := (RingHom.kerLift (algebraMap A B)).toAlgebra
  have hint : Algebra.IsIntegral (A ⧸ RingHom.ker (algebraMap A B)) B :=
    Algebra.isIntegral_def.2 ((algebraMap_isIntegral_iff.2 inferInstance).kerLift)
  have hfield : IsField B :=
    (Algebra.IsIntegral.isField_iff_isField (R := A ⧸ RingHom.ker (algebraMap A B)) (S := B)
      (RingHom.kerLift_injective _)).1 (Field.toIsField _)
  exact _root_.IsDiscreteValuationRing.not_isField B hfield

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- A discrete valuation ring with a faithful finite group action whose invariant ring is a
discrete valuation ring `A` is module-finite over `A`. -/
private theorem module_finite_of_isInvariant_dvr
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [FaithfulSMul G B] : Module.Finite A B := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have : FaithfulSMul A B := faithfulSMul_of_isDiscreteValuationRing_of_isIntegral A B
  let : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have := IsGaloisGroup.isGalois G (FractionRing A) (FractionRing B)
  have := IsGaloisGroup.finiteDimensional G (FractionRing A) (FractionRing B)
  exact IsIntegralClosure.finite A (FractionRing A) (FractionRing B) B

end Helpers

/-! ### Herbrand's theorem, transitivity, and upper numbering on quotients -/

section Quotient

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

/-- For a faithful finite group action on discrete valuation rings with separable residue
extension, the zeroth ramification group has order equal to the ramification index. -/
theorem natCard_ramificationGroup_zero_eq_ramificationIdx :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have : FaithfulSMul A B := faithfulSMul_of_isDiscreteValuationRing_of_isIntegral A B
  have : Module.Finite A B := module_finite_of_isInvariant_dvr A B G
  have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) :=
    ‹Algebra.IsSeparable (ResidueField A) (ResidueField B)›
  let : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  rw [ramificationGroup_zero_eq_inertia,
    Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
      (maximalIdeal A) (maximalIdeal B),
    Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]

variable (H : Subgroup G) [H.Normal]

/-- **Serre's quotient formula for the lower index** under a separable residue extension:
`#H_0 · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)` in `ℕ∞`. -/
theorem natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum [Fintype H] (σ : G) :
    (Nat.card (ramificationGroup H B 0) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ τ : H, lowerIndex B (σ * (τ : G)) := by
  set C := FixedPoints.subalgebra A B H
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have : FaithfulSMul A B := faithfulSMul_of_isDiscreteValuationRing_of_isIntegral A B
  have : FaithfulSMul A C :=
    faithfulSMul_of_isDiscreteValuationRing_of_isIntegral A C
  have : Module.Finite A B := module_finite_of_isInvariant_dvr A B G
  have : Module.Finite A C := by
    have : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B
    exact Module.Finite.iff_fg.2 (IsNoetherian.noetherian C.toSubmodule)
  have : Algebra.IsSeparable (ResidueField A) (ResidueField C) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (ResidueField A) (ResidueField C) (ResidueField B)
  have : Algebra.IsSeparable (ResidueField C) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField C) (ResidueField B)
  obtain ⟨x, hx⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := B)
  obtain ⟨y, hy⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := C)
  rw [natCard_ramificationGroup_zero_eq_ramificationIdx C B H]
  exact ramificationIdx_mul_lowerIndex_mk_eq_sum_of_adjoin_eq_top H hx hy σ

/-- **Serre's lemma** in counting form: if `σ` maximizes `lowerIndex B` in its coset `σ H` and
`i_G(σ) = j` is finite, then `#H_0 · i_{G/H}(σ H) = ∑_{k < j} #H_k`. -/
theorem natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card (σ : G) {j : ℕ}
    (hj : lowerIndex B σ = j)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    (Nat.card (ramificationGroup H B 0) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  cases nonempty_fintype H
  rw [natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum A B G H σ]
  simp_rw [lowerIndex_mul_of_forall_le σ hσ, hj]
  exact sum_min_lowerIndex_natCast (G := H) (S := B) j

private theorem lowerIndex_mk_ne_top (σ : G) (hj : lowerIndex B σ ≠ ⊤)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj
  intro htop
  have hsum := natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card A B G H σ hj.symm hσ
  have h0 : (Nat.card (ramificationGroup H B 0) : ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup H B 0)).ne'
  rw [htop, ENat.mul_top h0, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

/-- **Serre's lemma on the lower index of a quotient.** If `σ` maximizes `lowerIndex B` in its
coset `σ H` and `i_G(σ) = j` is finite, then `φ_H(j - 1) = i_{G/H}(σ H) - 1`. -/
theorem herbrandFun_lowerIndex_sub_one (σ : G) {j : ℕ}
    (hj : lowerIndex B σ = j)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H)).toNat : ℝ) - 1 := by
  have hsum := natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card A B G H σ hj hσ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_mk_ne_top A B G H σ (hj ▸ ENat.natCast_ne_top j) hσ)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (ramificationGroup H B 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup H B 0)).ne'
  rcases j with _ | m
  · rw [Nat.cast_zero, zero_sub, herbrandFun_neg_one]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero,
      (Nat.card_pos (α := ramificationGroup H B 0)).ne', false_or] at hsum
    simp [hsum]
  · have hjm : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
    rw [hjm, herbrandFun_natCast, div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
        Nat.card (ramificationGroup H B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

private theorem mk_mem_ramificationGroupReal_herbrandFun_iff (σ : G)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) (u : ℝ) :
    (σ : G ⧸ H) ∈ ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
        (herbrandFun H B u) ↔
      σ ∈ ramificationGroupReal G B u := by
  rcases eq_or_ne (lowerIndex B σ) ⊤ with htop | htop
  · rw [lowerIndex_eq_top_iff] at htop
    subst htop
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_mk_ne_top A B G H σ htop hσ)).symm,
    ← herbrandFun_lowerIndex_sub_one A B G H σ hj.symm hσ,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm]
  exact (herbrandFun_strictMono H B).le_iff_le

/-- **Herbrand's theorem on the lower filtration.** For a faithful finite group action on discrete
valuation rings with separable residue extension and normal subgroup `H ≤ G`, the image of `G_u`
in `G ⧸ H` is `(G ⧸ H)_{φ_H(u)}` for every real `u`. -/
theorem map_quotientMk'_ramificationGroupReal (u : ℝ) :
    (ramificationGroupReal G B u).map (QuotientGroup.mk' H) =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_le (B := B) H σ
    have hmk : QuotientGroup.mk' H σ = ((σ * (τ₀ : G) : G) : G ⧸ H) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      simp [τ₀.2]
    rw [hmk, mk_mem_ramificationGroupReal_herbrandFun_iff A B G H _ hτ₀]
    have hle : lowerIndex B σ ≤ lowerIndex B (σ * (τ₀ : G)) := by
      have := hτ₀ τ₀⁻¹
      simpa [mul_assoc] using this
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans hle
  · intro h
    induction q using QuotientGroup.induction_on with | _ σ =>
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_le (B := B) H σ
    have hmk : ((σ * (τ₀ : G) : G) : G ⧸ H) = (σ : G ⧸ H) := by
      rw [QuotientGroup.eq]
      simp [inv_mem τ₀.2]
    refine ⟨σ * (τ₀ : G), ?_, by rw [QuotientGroup.mk'_apply, hmk]⟩
    rw [← mk_mem_ramificationGroupReal_herbrandFun_iff A B G H _ hτ₀, hmk]
    exact h

/-- **Herbrand's theorem in counting form:** `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for every `u : ℝ`. -/
theorem natCard_ramificationGroupReal_quotient_herbrandFun_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  set f := (QuotientGroup.mk' H).domRestrict (ramificationGroupReal G B u)
  have hrange : Nat.card f.range =
      Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
        (herbrandFun H B u)) := by
    rw [MonoidHom.domRestrict_range, map_quotientMk'_ramificationGroupReal A B G H u]
  have hker : Nat.card f.ker = Nat.card (ramificationGroupReal H B u) := by
    rw [← subgroupOf_ramificationGroupReal]
    refine Nat.card_congr
      { toFun := fun ⟨⟨σ, hσ⟩, hker⟩ ↦ ⟨⟨σ, by
          rwa [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, ← MonoidHom.mem_ker,
            QuotientGroup.ker_mk'] at hker⟩, hσ⟩
        invFun := fun ⟨⟨σ, hσH⟩, hσ⟩ ↦ ⟨⟨σ, hσ⟩, by
          rwa [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, ← MonoidHom.mem_ker,
            QuotientGroup.ker_mk']⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }
  rw [← hrange, ← hker, mul_comm]
  exact Subgroup.card_ker_mul_card_range f

private theorem ramificationGroupReal_quotient_eq_of_forall_eq {a b t : ℝ}
    (ht₁ : herbrandFun H B a < t) (ht₂ : t ≤ herbrandFun H B b)
    (h : ∀ s : ℝ, a < s → s ≤ b → ramificationGroupReal G B s = ramificationGroupReal G B b) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) t =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B b) := by
  have hs₁ : a < inverseHerbrandFun H B t := by
    rw [← inverseHerbrandFun_herbrandFun H B a]
    exact inverseHerbrandFun_strictMono H B ht₁
  have hs₂ : inverseHerbrandFun H B t ≤ b := by
    rw [← inverseHerbrandFun_herbrandFun H B b]
    exact (inverseHerbrandFun_strictMono H B).monotone ht₂
  have ht : t = herbrandFun H B (inverseHerbrandFun H B t) :=
    (herbrandFun_inverseHerbrandFun H B t).symm
  rw [ht, ← map_quotientMk'_ramificationGroupReal A B G H,
    ← map_quotientMk'_ramificationGroupReal A B G H, h _ hs₁ hs₂]

private theorem herbrandFun_tower_of_mem_Icc_of_eq (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u)
    (h₂ : u ≤ m + 1)
    (hm : herbrandFun G B m =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B m)) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  have hG : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal G B t = ramificationGroupReal G B u := fun t ht₁ ht₂ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le G B (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  have hH : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal H B t = ramificationGroupReal H B u := fun t ht₁ ht₂ ↦ by
    rw [ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      ramificationGroupReal_eq_of_sub_one_lt_of_le H B (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  have hGsub := herbrandFun_sub_of_forall_eq G B h₁ hG
  have hHsub := herbrandFun_sub_of_forall_eq H B h₁ hH
  have hQsub := herbrandFun_sub_of_forall_eq (G ⧸ H) C ((herbrandFun_strictMono H B).monotone h₁)
    fun _ ht₁ ht₂ ↦ ramificationGroupReal_quotient_eq_of_forall_eq A B G H ht₁ ht₂ hG
  have hcard : (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) : ℝ) *
      Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
    exact_mod_cast natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H u
  have hcard₀ : (Nat.card (ramificationGroup (G ⧸ H) C 0) : ℝ) *
      Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
    have h0 := natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H 0
    rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
      ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
    exact_mod_cast h0
  have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) /
      Nat.card (ramificationGroup G B 0) =
        (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) /
            Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
      mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
  rw [hslope] at hGsub
  rw [hHsub] at hQsub
  linear_combination hGsub - hQsub + hm

private theorem herbrandFun_tower_of_mem_Icc (m : ℕ) :
    ∀ u : ℝ, (m : ℝ) ≤ u → u ≤ m + 1 →
      herbrandFun G B u =
        herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  induction m with
  | zero =>
    intro u h₁ h₂
    refine herbrandFun_tower_of_mem_Icc_of_eq A B G H 0 h₁ h₂ ?_
    simp
  | succ m ih =>
    intro u h₁ h₂
    exact herbrandFun_tower_of_mem_Icc_of_eq A B G H (m + 1) h₁ h₂
      (ih _ (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function:** `φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every real `u`.
Completeness of `A` is not required; separability of the residue extension is essential. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  rcases le_or_gt u (-1) with hu | hu
  · -- Below `-1`, both sides are affine with value `-1` at `-1` and slope `#G / #G_0`.
    have hφH_le : herbrandFun H B u ≤ -1 := by
      rw [← herbrandFun_neg_one H B]
      exact (herbrandFun_strictMono H B).monotone hu
    rw [herbrandFun_of_le_neg_one G B hu, herbrandFun_of_le_neg_one (G ⧸ H) C hφH_le,
      herbrandFun_of_le_neg_one H B hu]
    have hcardG : (Nat.card (G ⧸ H) : ℝ) * Nat.card H = Nat.card G := by
      have hlag : Nat.card H * Nat.card (G ⧸ H) = Nat.card G := by
        rw [← Subgroup.index_eq_card]
        exact H.card_mul_index
      exact_mod_cast (mul_comm _ _).trans hlag
    have hcard₀ : (Nat.card (ramificationGroup (G ⧸ H) C 0) : ℝ) *
        Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
      have h0 := natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H 0
      rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
        ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
      exact_mod_cast h0
    have hslope : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
        ((Nat.card H : ℝ) / Nat.card (ramificationGroup H B 0)) *
          ((Nat.card (G ⧸ H) : ℝ) / Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
      rw [div_mul_div_comm, ← hcardG, ← hcard₀, mul_comm (Nat.card H : ℝ),
        mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
    rw [hslope]
    ring
  · rcases le_or_gt u 0 with h0 | h0
    · rw [herbrandFun_of_le_zero H B hu.le h0, herbrandFun_of_le_zero (G ⧸ H) C hu.le h0,
        herbrandFun_of_le_zero G B hu.le h0]
    · exact herbrandFun_tower_of_mem_Icc A B G H ⌊u⌋₊ u (Nat.floor_le h0.le)
        (Nat.lt_floor_add_one u).le

/-- **Transitivity of the inverse Herbrand function:** `ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every
real `v`. -/
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  apply (herbrandFun_strictMono G B).injective
  rw [herbrandFun_inverseHerbrandFun, herbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Transitivity of the Herbrand order isomorphism:**
`herbrandOrderIso G B = (herbrandOrderIso H B).trans (herbrandOrderIso (G ⧸ H) B^H)`. -/
theorem herbrandOrderIso_tower :
    herbrandOrderIso G B =
      (herbrandOrderIso H B).trans
        (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) := by
  refine OrderIso.ext (funext fun u ↦ Subtype.ext ?_)
  rw [OrderIso.trans_apply, coe_herbrandOrderIso_apply, coe_herbrandOrderIso_apply,
    coe_herbrandOrderIso_apply]
  exact herbrandFun_tower A B G H u

/-- **Transitivity of the integral inverse Herbrand function:**
`ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) n) := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower A B G H]

/-- **Herbrand's theorem in the upper numbering:** for every real `v`,
`(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)`. Completeness of `A` is not required; separability
of the residue extension is essential. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    map_quotientMk'_ramificationGroupReal A B G H,
    inverseHerbrandFun_tower A B G H, herbrandFun_inverseHerbrandFun]

/-- **Normal subgroup trace in the upper numbering:** `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every
real `v`. -/
theorem subgroupOf_upperRamificationGroup_of_normal (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, inverseHerbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun]

/-- Every upper jump of the quotient `G ⧸ H` is an upper jump of `G`. -/
theorem upperJump_of_quotient {v : ℝ}
    (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) : UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢
  intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ (hv w hvw).ne ?_
  rw [upperRamificationGroup_quotient_eq_map A B G H,
    upperRamificationGroup_quotient_eq_map A B G H, heq]

/-- **Upper jumps in a quotient:** `v` is an upper jump of `G` if and only if `v` is an upper jump
of `G ⧸ H` or `ψ_{G ⧸ H}(v)` is an upper jump of `H`. -/
theorem upperJump_iff_quotient_or_subgroup (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  set C := FixedPoints.subalgebra A B H
  constructor
  · intro hv
    rw [upperJump_iff] at hv
    refine or_iff_not_imp_left.2 fun hQ ↦ (upperJump_iff H B _).2 fun x hx ↦ ?_
    obtain ⟨w₀, hvw₀, hw₀⟩ : ∃ w₀, v < w₀ ∧
        upperRamificationGroup (G ⧸ H) C w₀ = upperRamificationGroup (G ⧸ H) C v := by
      simp only [upperJump_iff, not_forall] at hQ
      obtain ⟨w₀, hvw₀, hlt⟩ := hQ
      exact ⟨w₀, hvw₀, (upperRamificationGroup_antitone (G ⧸ H) C hvw₀.le).eq_of_not_lt hlt⟩
    set w := min w₀ (herbrandFun (G ⧸ H) C x)
    have hvw : v < w := lt_min hvw₀ <| by
      have hx' : inverseHerbrandFun (G ⧸ H) C v < x := hx
      simpa only [herbrandFun_inverseHerbrandFun] using herbrandFun_strictMono (G ⧸ H) C hx'
    have hw : upperRamificationGroup (G ⧸ H) C w = upperRamificationGroup (G ⧸ H) C v :=
      le_antisymm (upperRamificationGroup_antitone (G ⧸ H) C hvw.le)
        (hw₀ ▸ upperRamificationGroup_antitone (G ⧸ H) C (min_le_left _ _))
    have hxw : inverseHerbrandFun (G ⧸ H) C w ≤ x := by
      simpa only [inverseHerbrandFun_herbrandFun] using
        (inverseHerbrandFun_strictMono (G ⧸ H) C).monotone
          (min_le_right w₀ (herbrandFun (G ⧸ H) C x))
    refine (upperRamificationGroup_antitone H B hxw).trans_lt ?_
    rw [← subgroupOf_upperRamificationGroup_of_normal A B G H,
      ← subgroupOf_upperRamificationGroup_of_normal A B G H]
    refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
      fun heq ↦ (hv w hvw).not_ge fun σ hσ ↦ ?_
    obtain ⟨τ, hτ, hτσ⟩ : QuotientGroup.mk' H σ ∈
        (upperRamificationGroup G B w).map (QuotientGroup.mk' H) := by
      rw [← upperRamificationGroup_quotient_eq_map A B G H, hw,
        upperRamificationGroup_quotient_eq_map A B G H]
      exact Subgroup.mem_map_of_mem _ hσ
    have hρH : τ⁻¹ * σ ∈ H := by
      rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
    have hρw : (⟨τ⁻¹ * σ, hρH⟩ : H) ∈ (upperRamificationGroup G B w).subgroupOf H := by
      rw [heq, Subgroup.mem_subgroupOf]
      exact mul_mem (inv_mem (upperRamificationGroup_antitone G B hvw.le hτ)) hσ
    rw [Subgroup.mem_subgroupOf] at hρw
    simpa only [mul_inv_cancel_left] using mul_mem hτ hρw
  · rintro (hQ | hH)
    · exact upperJump_of_quotient A B G H hQ
    · rw [upperJump_iff] at hH ⊢
      intro w hvw
      refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ ?_
      have hlt := hH _ (inverseHerbrandFun_strictMono (G ⧸ H) C hvw)
      rw [← subgroupOf_upperRamificationGroup_of_normal A B G H,
        ← subgroupOf_upperRamificationGroup_of_normal A B G H, heq] at hlt
      exact hlt.ne rfl

end Quotient

/-! ### Field form through `IsGalois.normalAutEquivQuotient` -/

section FieldForm

variable (A K L : Type*) [CommRing A] [Field K] [Algebra A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- For a field extension `L/K` and a subgroup `H ≤ Gal(L/K)`, the `H`-fixed subalgebra of
`integralClosure A L` is canonically `A`-isomorphic to the integral closure of `A` in the fixed
field `L^H`. -/
def fixedPointsIntegralClosureEquiv (H : Subgroup (L ≃ₐ[K] L)) :
    FixedPoints.subalgebra A (integralClosure A L) H ≃ₐ[A]
      integralClosure A (IntermediateField.fixedField H) where
  toFun x :=
    ⟨⟨((x : integralClosure A L) : L), fun σ ↦ congrArg Subtype.val (x.2 σ)⟩, by
      rw [mem_integralClosure_iff,
        ← isIntegral_algHom_iff
          ((IntermediateField.fixedField H).val.restrictScalars A) Subtype.val_injective]
      exact (x : integralClosure A L).2⟩
  invFun y :=
    ⟨⟨((y : IntermediateField.fixedField H) : L), by
      rw [mem_integralClosure_iff]
      exact y.2.map ((IntermediateField.fixedField H).val.restrictScalars A)⟩,
      fun σ ↦ Subtype.ext ((y : IntermediateField.fixedField H).2 σ)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- If `integralClosure A L` is a discrete valuation ring and `H ≤ Gal(L/K)` is finite, then
`integralClosure A (IntermediateField.fixedField H)` is also a discrete valuation ring. -/
theorem isDiscreteValuationRing_integralClosure_fixedField
    (H : Subgroup (L ≃ₐ[K] L)) [Finite H] [IsDiscreteValuationRing (integralClosure A L)] :
    _root_.IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsIntegralClosureEquiv A K L H)

variable [FiniteDimensional K L] [IsGalois K L]

/-- `fixedPointsIntegralClosureEquiv` is equivariant along `IsGalois.normalAutEquivQuotient H`. -/
theorem fixedPointsIntegralClosureEquiv_smul (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (q : (L ≃ₐ[K] L) ⧸ H) (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    fixedPointsIntegralClosureEquiv A K L H (q • x) =
      IsGalois.normalAutEquivQuotient H q • fixedPointsIntegralClosureEquiv A K L H x := by
  induction q using QuotientGroup.induction_on with | _ σ =>
  refine Subtype.ext (Subtype.ext ?_)
  change σ ((x : integralClosure A L) : L) =
    (IsGalois.normalAutEquivQuotient H (σ : (L ≃ₐ[K] L) ⧸ H)
      (fixedPointsIntegralClosureEquiv A K L H x : IntermediateField.fixedField H) : L)
  rw [IsGalois.normalAutEquivQuotient_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]

private theorem algebra_isInvariant_integralClosure :
    Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) where
  isInvariant x hx := by
    have hfixed : (x : L) ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
      intro σ
      exact congrArg Subtype.val (hx σ.1)
    rw [IsGalois.fixedField_top] at hfixed
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hfixed
    have hint : IsIntegral A k := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective]
      change IsIntegral A (algebraMap K L k)
      rw [hk]
      exact (mem_integralClosure_iff A L).1 x.2
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨a, Subtype.ext ?_⟩
    change algebraMap A L a = (x : L)
    rw [IsScalarTower.algebraMap_apply A K L, ha, hk]

omit [IsGalois K L] [IsDiscreteValuationRing A] in
private theorem faithfulSMul_integralClosure :
    FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) where
  eq_of_smul_eq_smul {σ₁ σ₂} h := by
    have : IsFractionRing (integralClosure A L) L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
    ext x
    obtain ⟨⟨y, z⟩, hyz⟩ := IsLocalization.surj (nonZeroDivisors (integralClosure A L)) x
    rcases z with ⟨z, hz⟩
    dsimp only at hyz
    have hy : σ₁ (y : L) = σ₂ (y : L) := congrArg Subtype.val (h y)
    have hz' : σ₁ (z : L) = σ₂ (z : L) := congrArg Subtype.val (h z)
    have hmul : σ₁ (x * (z : L)) = σ₂ (x * (z : L)) := by
      change σ₁ (x * algebraMap (integralClosure A L) L z) =
        σ₂ (x * algebraMap (integralClosure A L) L z)
      rw [hyz]
      exact hy
    rw [map_mul, map_mul, hz'] at hmul
    have hz0 : (z : L) ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hz (Subtype.ext h0)
    exact mul_right_cancel₀ ((map_ne_zero_iff σ₂ σ₂.injective).2 hz0) hmul

variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
  [IsDiscreteValuationRing (integralClosure A L)]
  [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
  [_root_.IsLocalRing (integralClosure A (IntermediateField.fixedField H))]

/-- **Transitivity of the Herbrand function** in a finite Galois extension `L/K` of fraction fields
of discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field `E = L^H`. -/
theorem herbrandFun_fixedField_tower (u : ℝ) :
    herbrandFun (L ≃ₐ[K] L) (integralClosure A L) u =
      herbrandFun
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H))
        (herbrandFun H (integralClosure A L) u) := by
  have : Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) :=
    algebra_isInvariant_integralClosure A K L
  have : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
    faithfulSMul_integralClosure A K L
  rw [herbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) H u]
  exact herbrandFun_eq_of_equiv (IsGalois.normalAutEquivQuotient H)
    (fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
    (fixedPointsIntegralClosureEquiv_smul A K L H) _

/-- **Transitivity of the inverse Herbrand function** in a finite Galois extension `L/K` of
fraction fields of discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field
`E = L^H`. -/
theorem inverseHerbrandFun_fixedField_tower (v : ℝ) :
    inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure A L) v =
      inverseHerbrandFun H (integralClosure A L)
        (inverseHerbrandFun
          ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
          (integralClosure A (IntermediateField.fixedField H)) v) := by
  have : Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) :=
    algebra_isInvariant_integralClosure A K L
  have : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
    faithfulSMul_integralClosure A K L
  rw [inverseHerbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) H v,
    inverseHerbrandFun_eq_of_equiv (IsGalois.normalAutEquivQuotient H)
      (fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
      (fixedPointsIntegralClosureEquiv_smul A K L H)]

/-- **Normal subgroup trace in the upper numbering, field form:** for a finite Galois extension
`L/K` of fraction fields of discrete valuation rings with separable residue extension and normal
subgroup `H ≤ Gal(L/K)`, `H ∩ Gal(L/K)^v = H^{ψ_{L^H / K}(v)}`. -/
theorem subgroupOf_upperRamificationGroup_fixedField (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).subgroupOf H =
      upperRamificationGroup H (integralClosure A L)
        (inverseHerbrandFun
          ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
          (integralClosure A (IntermediateField.fixedField H)) v) := by
  have : Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) :=
    algebra_isInvariant_integralClosure A K L
  have : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
    faithfulSMul_integralClosure A K L
  rw [subgroupOf_upperRamificationGroup_of_normal A (integralClosure A L) (L ≃ₐ[K] L) H v,
    inverseHerbrandFun_eq_of_equiv (IsGalois.normalAutEquivQuotient H)
      (fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
      (fixedPointsIntegralClosureEquiv_smul A K L H)]

/-- **Herbrand's theorem in the upper numbering, field form through
`IsGalois.normalAutEquivQuotient`:** for a finite Galois extension `L/K` of fraction fields of
discrete valuation rings with separable residue extension and normal subgroup `H ≤ Gal(L/K)`,
`IsGalois.normalAutEquivQuotient H` identifies the quotient upper group `(G^v).map mk'` with
`Gal(L^H / K)^v` acting on `integralClosure A (L^H)`. -/
theorem upperRamificationGroup_fixedField_eq_map (v : ℝ) :
    upperRamificationGroup
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H)) v =
      ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
          (QuotientGroup.mk' H)).map
        (IsGalois.normalAutEquivQuotient H).toMonoidHom := by
  have : Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) :=
    algebra_isInvariant_integralClosure A K L
  have : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
    faithfulSMul_integralClosure A K L
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v]
  exact (map_upperRamificationGroup_of_equiv (IsGalois.normalAutEquivQuotient H)
    (fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
    (fixedPointsIntegralClosureEquiv_smul A K L H) v).symm

/-- **Herbrand's theorem in the upper numbering, restriction form:** restriction to the fixed
field `L^H` maps `Gal(L/K)^v` onto `Gal(L^H/K)^v`. -/
theorem map_restrictNormalHom_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      upperRamificationGroup
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H)) v := by
  have hcomp : (IsGalois.normalAutEquivQuotient H).toMonoidHom.comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [upperRamificationGroup_fixedField_eq_map A K L H v, Subgroup.map_map, hcomp]

end FieldForm

end TauCeti.IsLocalRing
