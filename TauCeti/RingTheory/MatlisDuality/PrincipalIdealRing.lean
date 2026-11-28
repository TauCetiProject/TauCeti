/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Module.Injective.Cogenerator
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.Algebra.Module.Submodule.LinearMap

/-!
# Matlis duality over a principal ideal domain

Let `O` be a commutative ring with fraction field `K`. For `a ≠ 0`, division by `a` identifies
`O/a` with the elements of `K/O` killed by `a`, and so identifies `Hom_O(Q, O/a)` with
`Hom_O(Q, K/O)` for every `O`-module `Q` killed by `a`.

Let `O` moreover be a principal ideal domain that is not a field. The module `K/O` is injective
over `O`, and `Hom_O(O/𝔪, K/O)` is simple for every maximal ideal `𝔪`, so `Hom_O(-, K/O)`
preserves lengths (`TauCeti.length_linearMap_of_forall_isMaximal`). Through the identification
above, for `a ≠ 0` the duality `Hom_O(-, O/a)` preserves the lengths of modules killed by `a`,
`O/a` separates their points, and linear maps to `O/a` extend along injections into them. Over a
field these hold trivially, since `a` is a unit and every module killed by `a` is zero.

## Main definitions

* `TauCeti.divQuotient`: division by `a`, the map `O/a → K/O`, `t ↦ t/a`.
* `TauCeti.quotientEquivTorsionBySet`: for `a ≠ 0`, the identification of `O/a` with the
  elements of `K/O` killed by `a`.
* `TauCeti.linearMapQuotientSpanEquivFractionRingQuotient`: for `a ≠ 0` and an `O`-module `Q`
  killed by `a`, the identification `Hom_O(Q, O/a) ≃ₗ[O] Hom_O(Q, K/O)`.

## Main results

* `TauCeti.divQuotient_injective`, `TauCeti.range_divQuotient`: for `a ≠ 0`, division by `a` is
  injective with image the `a`-torsion of `K/O`.
* `TauCeti.length_linearMap_quotient_of_isMaximal`: over a principal ideal domain that is not a
  field, `Hom_O(O/𝔪, K/O)` has length one for every maximal ideal `𝔪`.
* `TauCeti.length_linearMap_fractionRing_quotient`: over a principal ideal domain that is not a
  field, `Hom_O(M, K/O)` has the length of `M`, for every `O`-module `M` (Matlis duality).
* `TauCeti.length_linearMap_quotient_span_singleton_right`: over a principal ideal domain, for
  `a ≠ 0` and an `O`-module `Q` killed by `a`, `Hom_O(Q, O/a)` has the length of `Q`.
* `TauCeti.exists_linearMap_quotient_span_singleton_apply_ne_zero`,
  `TauCeti.exists_linearMap_quotient_span_singleton_comp_eq`: over a principal ideal domain, for
  `a ≠ 0`, `O/a` separates the points of modules killed by `a`, and linear maps to `O/a` extend
  along injections into such modules.

## References

* E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958).
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

public section

open LinearMap

namespace TauCeti

universe u v

variable {O : Type u} {K : Type v} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]

/-- Division by `a`, the functional `O/a → K/O` sending the class of `t` to the class of `t/a`.
For `a ≠ 0` it identifies `O/a` with the elements of `K/O` killed by `a`
(`TauCeti.quotientEquivTorsionBySet`). -/
noncomputable def divQuotient (a : O) :
    O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K) :=
  (Ideal.span {a}).liftQ
    ((range (Algebra.linearMap O K)).mkQ ∘ₗ toSpanSingleton O K (algebraMap O K a)⁻¹)
    (by
      rw [Ideal.span_singleton_le_iff_mem, mem_ker, comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · exact ⟨1, by simp [Algebra.smul_def, IsFractionRing.to_map_eq_zero_iff.not.2 ha]⟩)

omit [IsDomain O] in
@[simp]
theorem divQuotient_mk (a t : O) :
    divQuotient (K := K) a (Ideal.Quotient.mk (Ideal.span {a}) t) =
      Submodule.Quotient.mk (t • (algebraMap O K a)⁻¹) := by
  rw [← Ideal.Quotient.mk_eq_mk, divQuotient, Submodule.liftQ_apply, comp_apply,
    toSpanSingleton_apply, Submodule.mkQ_apply]

/-- For `a ≠ 0`, `divQuotient a` identifies `O/a` with the elements of `K/O` killed by `a`. -/
noncomputable def quotientEquivTorsionBySet {a : O} (ha : a ≠ 0) :
    (O ⧸ Ideal.span {a}) ≃ₗ[O]
      Submodule.torsionBySet O (K ⧸ range (Algebra.linearMap O K)) (Ideal.span {a}) := by
  have ha' : algebraMap O K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.2 ha
  -- The field identity behind all three steps: `a * (t / a) = t` in `K`.
  have hdiv (t : O) : algebraMap O K a * (t • (algebraMap O K a)⁻¹) = algebraMap O K t := by
    rw [Algebra.smul_def]
    field_simp
  have htors : Submodule.torsionBySet O (K ⧸ range (Algebra.linearMap O K)) (Ideal.span {a}) =
      Submodule.torsionBy O _ a :=
    Submodule.torsionBySet_span_singleton_eq a
  refine LinearEquiv.ofBijective ((divQuotient a).codRestrict _ fun x ↦ ?_) ⟨?_, ?_⟩
  · rw [htors, Submodule.mem_torsionBy_iff]
    induction x using Submodule.Quotient.induction_on with | _ t =>
    rw [Ideal.Quotient.mk_eq_mk, divQuotient_mk, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, by rw [Algebra.linearMap_apply, Algebra.smul_def a, hdiv]⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict, eq_bot_iff]
    intro r hr
    induction r using Submodule.Quotient.induction_on with | _ r =>
    rw [mem_ker, Ideal.Quotient.mk_eq_mk, divQuotient_mk, Submodule.Quotient.mk_eq_zero] at hr
    obtain ⟨s, hs⟩ := hr
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
    refine ⟨s, IsFractionRing.injective O K ?_⟩
    rw [Algebra.linearMap_apply] at hs
    rw [map_mul, hs, hdiv]
  · rintro ⟨x, hx⟩
    rw [htors, Submodule.mem_torsionBy_iff] at hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨r, hr⟩ := hx
    rw [Algebra.linearMap_apply] at hr
    refine ⟨Submodule.Quotient.mk r, Subtype.ext ?_⟩
    rw [LinearMap.codRestrict_apply, Ideal.Quotient.mk_eq_mk, divQuotient_mk]
    refine congrArg Submodule.Quotient.mk (mul_left_cancel₀ ha' ?_)
    rw [hdiv, hr, Algebra.smul_def]

omit [IsDomain O] in
@[simp]
theorem coe_quotientEquivTorsionBySet_apply_mk {a : O} (ha : a ≠ 0) (t : O) :
    (quotientEquivTorsionBySet (K := K) ha (Ideal.Quotient.mk (Ideal.span {a}) t) :
      K ⧸ range (Algebra.linearMap O K)) =
      Submodule.Quotient.mk (t • (algebraMap O K a)⁻¹) :=
  divQuotient_mk a t

/-- For `a ≠ 0` and an `O`-module `Q` killed by `a`, `divQuotient a` induces an equivalence
`Hom_O(Q, O ⧸ Ideal.span {a}) ≃ₗ[O] Hom_O(Q, K ⧸ O)`. -/
noncomputable def linearMapQuotientSpanEquivFractionRingQuotient
    {Q : Type*} [AddCommMonoid Q] [Module O Q] {a : O} (ha : a ≠ 0) (h : ∀ x : Q, a • x = 0) :
    (Q →ₗ[O] O ⧸ Ideal.span {a}) ≃ₗ[O] (Q →ₗ[O] K ⧸ range (Algebra.linearMap O K)) :=
  (LinearEquiv.congrRight (quotientEquivTorsionBySet (K := K) ha)).trans
    (Submodule.linearMapSubtypeEquiv O _ fun ψ x ↦ by
      rw [Submodule.torsionBySet_span_singleton_eq, Submodule.mem_torsionBy_iff,
        ← map_smul, h, map_zero])

omit [IsDomain O] in
@[simp]
theorem linearMapQuotientSpanEquivFractionRingQuotient_apply
    {Q : Type*} [AddCommMonoid Q] [Module O Q] {a : O} (ha : a ≠ 0) (h : ∀ x : Q, a • x = 0)
    (φ : Q →ₗ[O] O ⧸ Ideal.span {a}) (x : Q) :
    linearMapQuotientSpanEquivFractionRingQuotient (K := K) ha h φ x =
      divQuotient (K := K) a (φ x) := by
  simp [linearMapQuotientSpanEquivFractionRingQuotient]
  rfl

omit [IsDomain O] in
/-- `quotientEquivTorsionBySet` is division by `a`. -/
theorem coe_quotientEquivTorsionBySet_apply {a : O} (ha : a ≠ 0) (x : O ⧸ Ideal.span {a}) :
    (quotientEquivTorsionBySet (K := K) ha x : K ⧸ range (Algebra.linearMap O K)) =
      divQuotient a x :=
  (rfl)

omit [IsDomain O] in
/-- For `a ≠ 0`, division by `a`, `O/a → K/O`, is injective. -/
theorem divQuotient_injective {a : O} (ha : a ≠ 0) :
    Function.Injective (divQuotient (K := K) a) := fun x y h ↦
  (quotientEquivTorsionBySet (K := K) ha).injective <| Subtype.ext <| by
    rwa [coe_quotientEquivTorsionBySet_apply, coe_quotientEquivTorsionBySet_apply]

omit [IsDomain O] in
/-- For `a ≠ 0`, the image of division by `a`, `O/a → K/O`, is the `a`-torsion of `K/O`. -/
theorem range_divQuotient {a : O} (ha : a ≠ 0) :
    range (divQuotient (K := K) a) =
      Submodule.torsionBy O (K ⧸ range (Algebra.linearMap O K)) a := by
  rw [← Submodule.torsionBySet_span_singleton_eq]
  ext y
  refine ⟨?_, fun hy ↦ ⟨(quotientEquivTorsionBySet ha).symm ⟨y, hy⟩, ?_⟩⟩
  · rintro ⟨x, rfl⟩
    rw [← coe_quotientEquivTorsionBySet_apply ha]
    exact (quotientEquivTorsionBySet ha x).property
  · rw [← coe_quotientEquivTorsionBySet_apply ha, LinearEquiv.apply_symm_apply]

omit [IsDomain O] in
/-- Over a principal ideal domain that is not a field, `Hom_O(O/𝔪, K/O)` is simple for every
maximal ideal `𝔪 = (π)`: it is the `π`-torsion of `K/O`, a copy of `O/𝔪`. -/
theorem length_linearMap_quotient_of_isMaximal [IsPrincipalIdealRing O] (hO : ¬IsField O)
    {𝔪 : Ideal O} (h𝔪 : 𝔪.IsMaximal) :
    Module.length O (O ⧸ 𝔪 →ₗ[O] K ⧸ range (Algebra.linearMap O K)) = 1 := by
  have : IsDomain O := IsDomain.of_faithfulSMul O K
  obtain ⟨π, rfl⟩ : ∃ π, 𝔪 = Ideal.span {π} := ⟨_, (Ideal.span_singleton_generator 𝔪).symm⟩
  have hπ : π ≠ 0 := fun h ↦ Ring.ne_bot_of_isMaximal_of_not_isField h𝔪 hO (by simp [h])
  rw [((Ideal.span {π}).quotientLinearMapEquivTorsionBySet _).length_eq,
    ← (quotientEquivTorsionBySet hπ).length_eq, Ideal.length_quotient_eq_one]

omit [IsDomain O] in
/-- **Matlis duality over a principal ideal domain.** For a principal ideal domain `O` that is not
a field, `Hom_O(M, K/O)` has the length of `M`, for every `O`-module `M`: `K/O` is injective, and
`Hom_O(O/𝔪, K/O)` has length one for every maximal ideal `𝔪`. Over a field `K/O` is zero. -/
theorem length_linearMap_fractionRing_quotient [IsPrincipalIdealRing O] (hO : ¬IsField O)
    (M : Type*) [AddCommGroup M] [Module O M] :
    Module.length O (M →ₗ[O] K ⧸ range (Algebra.linearMap O K)) = Module.length O M := by
  have : Small.{v} O := small_of_injective (IsFractionRing.injective O K)
  exact TauCeti.length_linearMap_of_forall_isMaximal
    (fun _ h𝔪 ↦ length_linearMap_quotient_of_isMaximal hO h𝔪) M

omit [Field K] [Algebra O K] [IsFractionRing O K] in
/-- For an `O`-module `Q` killed by `a ≠ 0` over a principal ideal domain,
`Hom_O(Q, O ⧸ Ideal.span {a})` has the same length as `Q`. -/
theorem length_linearMap_quotient_span_singleton_right [IsPrincipalIdealRing O]
    {Q : Type*} [AddCommGroup Q] [Module O Q] {a : O} (ha : a ≠ 0) (h : ∀ x : Q, a • x = 0) :
    Module.length O (Q →ₗ[O] O ⧸ Ideal.span {a}) = Module.length O Q := by
  by_cases hO : IsField O
  · -- over a field, `a` is a unit, so `Q` is zero
    obtain ⟨b, hb⟩ := hO.mul_inv_cancel ha
    have : Subsingleton Q :=
      subsingleton_of_forall_eq 0 fun x ↦ (IsUnit.of_mul_eq_one b hb).smul_eq_zero.1 (h x)
    rw [Module.length_eq_zero, Module.length_eq_zero]
  rw [(linearMapQuotientSpanEquivFractionRingQuotient (K := FractionRing O) ha h).length_eq,
    length_linearMap_fractionRing_quotient hO]

omit [Field K] [Algebra O K] [IsFractionRing O K] in
/-- **`O ⧸ (a)` separates the points of a module killed by `a`.** Over a principal ideal domain,
for `a ≠ 0`, a nonzero element of an `O`-module killed by `a` has a nonzero image under some
linear map to `O ⧸ (a)`. -/
theorem exists_linearMap_quotient_span_singleton_apply_ne_zero [IsPrincipalIdealRing O]
    {Q : Type*} [AddCommGroup Q] [Module O Q] {a : O} (ha : a ≠ 0) (h : ∀ x : Q, a • x = 0)
    {x : Q} (hx : x ≠ 0) : ∃ Ψ : Q →ₗ[O] O ⧸ Ideal.span {a}, Ψ x ≠ 0 := by
  by_cases hO : IsField O
  · -- over a field, `a` is a unit, so `x = 0`
    obtain ⟨b, hb⟩ := hO.mul_inv_cancel ha
    exact absurd ((IsUnit.of_mul_eq_one b hb).smul_eq_zero.1 (h x)) hx
  let e := linearMapQuotientSpanEquivFractionRingQuotient (K := FractionRing O) ha h
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_apply_ne_zero_of_forall_isMaximal
    (TauCeti.nontrivial_linearMap_of_isMaximal
      fun _ h𝔪 ↦ length_linearMap_quotient_of_isMaximal (K := FractionRing O) hO h𝔪) hx
  refine ⟨e.symm ψ, fun h0 ↦ hψ ?_⟩
  rw [← e.apply_symm_apply ψ, linearMapQuotientSpanEquivFractionRingQuotient_apply, h0, map_zero]

omit [Field K] [Algebra O K] [IsFractionRing O K] in
/-- **`O ⧸ (a)` is injective for modules killed by `a`.** Over a principal ideal domain, for
`a ≠ 0`, every linear map to `O ⧸ (a)` extends along an injective linear map `f : Q₁ → Q₂` into a
module killed by `a`. -/
theorem exists_linearMap_quotient_span_singleton_comp_eq [IsPrincipalIdealRing O]
    {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [Module O Q₁] [AddCommGroup Q₂] [Module O Q₂] {a : O}
    (ha : a ≠ 0) (h : ∀ x : Q₂, a • x = 0) {f : Q₁ →ₗ[O] Q₂} (hf : Function.Injective f)
    (θ : Q₁ →ₗ[O] O ⧸ Ideal.span {a}) : ∃ Ψ : Q₂ →ₗ[O] O ⧸ Ideal.span {a}, Ψ ∘ₗ f = θ := by
  have h₁ (x : Q₁) : a • x = 0 := hf (by rw [map_smul, h, map_zero])
  let e₁ := linearMapQuotientSpanEquivFractionRingQuotient (K := FractionRing O) ha h₁
  let e₂ := linearMapQuotientSpanEquivFractionRingQuotient (K := FractionRing O) ha h
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property O _ Q₁ Q₂ f hf (e₁ θ)
  refine ⟨e₂.symm ψ, e₁.injective (LinearMap.ext fun x ↦ ?_)⟩
  have h₂ : e₂ (e₂.symm ψ) (f x) = ψ (f x) := by rw [LinearEquiv.apply_symm_apply]
  rw [linearMapQuotientSpanEquivFractionRingQuotient_apply] at h₂
  rw [linearMapQuotientSpanEquivFractionRingQuotient_apply, LinearMap.comp_apply, h₂, ← hψ,
    LinearMap.comp_apply]

end TauCeti
