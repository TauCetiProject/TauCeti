/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.PowerBasis
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.FieldTheory.FunctionField.Place.Extension.PurelyInseparable
import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.RingTheory.Length.Determinant
import TauCeti.RingTheory.LocalRing.Monogenic
import TauCeti.RingTheory.Polynomial.Truncated.Determinant

/-!
# Tate's genus-change theorem in positive characteristic

In characteristic `p > 0`, the genus of an algebraic function field `F / k` with exact constant
field `k` can drop under an inseparable algebraic constant field extension `F' = F · k'`, and new
constants `k'' ⊇ k'` may appear in `F'`. Tate proved in 1952 that the genus drop is constrained by
a congruence modulo `p - 1`:

`(p - 1) ∣ 2 (g(F / k) - g(F' / k''))`,

and hence `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')` for every odd prime `p`. In particular, whenever
`2 g(F / k) < p - 1` (or `g(F / k) < (p - 1) / 2` for `p ≠ 2`), the genus is conserved across
every algebraic constant field extension. Both bounds are sharp: for an odd prime `p` and a
transcendental `a`, the hyperelliptic-like curve `y ^ 2 = x ^ p - a` over `𝔽_p(a)` has genus
`(p - 1) / 2` and drops to genus `0` over `𝔽_p(a ^ (1 / p))`, while for `p = 2` the curve
`y ^ 2 = x ^ 3 + a` over `𝔽_2(a)` has genus `1` and drops to genus `0` over `𝔽_2(a ^ (1 / 2))`.

Following Schröer (2009), we prove Tate's theorem without differentials by combining the global
genus-change formula `g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P` from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change` with a local determinant
computation at a purely inseparable constant step `k' / k` of prime degree `p`:

1. **Local monogenicity.** At the unique place `P'` of `F' / k'` above `P`, the fundamental
   identity reads `e(P' ∣ P) · f(P' ∣ P) = p`. Whether `(e, f) = (p, 1)` or `(1, p)`, Nakayama's
   criterion (`TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal`) produces a single
   generator `β` of `𝒪_{P'}` over `𝒪_P`, hence an `𝒪_P`-power basis `1, β, …, β ^ (p - 1)` with
   `β ^ p ∈ 𝒪_P`.
2. **Local singularity degree.** Writing a primitive element `α` of `k' / k` as `f(β)` for a
   polynomial `f ∈ 𝒪_P[X]` of degree `< p`, the transition matrix `A` from `1, β, …, β ^ (p - 1)`
   to `1, α, …, α ^ (p - 1)` reduces `f(X) ^ i` modulo `X ^ p - β ^ p`. Over `𝒪_{P'}`, this modulus
   factors as `(X - β) ^ p`, so `Matrix.det_of_X_sub_C_pow_dvd_pow_sub_sum` evaluates `det A` as
   `f'(β) ^ (p (p - 1) / 2)`. Comparing `𝒪_P`-lengths and `k`-dimensions yields
   `2 δ_P = (p - 1) · ord_{P'}(f'(β)) · deg P'`.
3. **Tower and stabilization.** In the degree-`p` step, `k'' / k'` is purely inseparable of
   `p`-power degree, so `(p - 1) ∣ [k'' : k'] - 1` and `(p - 1) ∣ 2 (g(F / k) - g(F' / k''))`.
   General algebraic constant extensions reduce to finite ones by
   `TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`, split at the separable closure
   of `k`, and induct along prime-degree purely inseparable steps inside the exact constant field
   upstairs.

## Main results

* `TauCeti.Place.exists_powerBasis_integers_of_finrank_eq_prime`: local monogenicity of `𝒪_{P'}`
  over `𝒪_P` for a purely inseparable constant extension of prime degree `p`.
* `TauCeti.Place.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime` and
  `TauCeti.Place.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime`: the local
  Tate–Schröer formula `2 δ_P = (p - 1) · m · deg P'` and divisibility `(p - 1) ∣ 2 δ_P` for a
  purely inseparable constant extension of prime degree `p`.
* `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn`,
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top`, and
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top`:
  Tate's genus-change divisibility `(p - 1) ∣ 2 (g(F / k) - g(F' / k''))` for arbitrary algebraic
  constant extensions in characteristic `p`, with or without constant growth.
* `TauCeti.half_sub_one_dvd_genus_sub_genus_of_constantCompositum_eq_top`: for `p ≠ 2`,
  `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')`.
* `TauCeti.genus_eq_genus_of_two_mul_genus_lt_sub_one`,
  `TauCeti.genus_eq_genus_of_genus_lt_half_sub_one`, and
  `TauCeti.isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one`: genus conservation
  and preservation of exact constants when `2 g(F / k) < p - 1`.

## References

* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
-/

public section

open IntermediateField IsLocalRing Module Polynomial

namespace TauCeti

universe u u' v v'

/-! ### Order of vanishing in the valuation ring of a place -/

section PlaceOrd

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- For a nonzero element `x` of the valuation ring `𝒪_P` of a place `P`, the module-length order
of vanishing `Ring.ord 𝒪_P x` agrees with the normalized valuation `(P.ord x).toNat`. -/
theorem Place.ringOrd_integers_eq_toNat_ord (P : Place k F) {x : P.integers} (hx : (x : F) ≠ 0) :
    Ring.ord P.integers x = ((P.ord (x : F)).toNat : ℕ∞) := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have ht_ord : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.1 ht
  let π : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.2 (by omega)⟩
  have hπ : Irreducible π := P.irreducible_of_isUniformizer ht
  have hx0 : x ≠ 0 := fun h0 ↦ hx (congrArg Subtype.val h0)
  obtain ⟨n, u, rfl⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  rw [Ring.ord_eq_addVal, _root_.IsDiscreteValuationRing.addVal_def' u hπ n]
  have hu0 : ((u : P.integers) : F) ≠ 0 := fun h0 ↦ u.ne_zero (Subtype.ext h0)
  have hπ0 : (π : F) ≠ 0 := by
    intro h0
    rw [show t = (π : F) from rfl, h0, P.ord_zero] at ht_ord
    omega
  have hord : P.ord (((u : P.integers) * π ^ n : P.integers) : F) = n := by
    change P.ord ((u : P.integers) * (π : F) ^ n) = n
    rw [P.ord_mul hu0 (pow_ne_zero n hπ0), (P.isUnit_iff_ord_eq_zero hu0).1 u.isUnit,
      P.ord_pow (π : F) n, show (π : F) = t from rfl, ht_ord]
    omega
  rw [hord, Int.toNat_natCast]

end PlaceOrd

/-! ### Prime-degree purely inseparable field extensions -/

section PurelyInseparable

/-- Any field extension of prime degree is generated by a single element. -/
private theorem exists_adjoin_simple_eq_top_of_finrank_prime {K L : Type*} [Field K] [Field L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) (hdeg : finrank K L = p) :
    ∃ α : L, K⟮α⟯ = ⊤ := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hdeg ▸ hp.pos)
  have hne : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro hbot
    have := congrArg (fun E : IntermediateField K L ↦ finrank K E) hbot
    rw [IntermediateField.finrank_bot, IntermediateField.finrank_top', hdeg] at this
    exact hp.ne_one this.symm
  obtain ⟨α, -, hα⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hne.symm)
  have h1 : 1 < finrank K K⟮α⟯ := by
    by_contra! hle
    have heq : finrank K K⟮α⟯ = 1 := le_antisymm hle finrank_pos
    exact hα ((IntermediateField.finrank_eq_one_iff.1 heq).le (mem_adjoin_simple_self K α))
  have hdvd : finrank K K⟮α⟯ ∣ p := hdeg ▸ ⟨finrank K⟮α⟯ L, (finrank_mul_finrank K K⟮α⟯ L).symm⟩
  have hαdeg : finrank K K⟮α⟯ = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left h1.ne'
  exact ⟨α, eq_of_le_of_finrank_eq le_top (by rw [IntermediateField.finrank_top', hαdeg, hdeg])⟩

/-- Every purely inseparable extension in prime characteristic `p` with `1 < finrank K M` contains
an intermediate field of degree `p` over the base. -/
private theorem exists_intermediateField_finrank_eq_prime {K M : Type*} [Field K] [Field M]
    [Algebra K M] (p : ℕ) [Fact p.Prime] [CharP K p] [IsPurelyInseparable K M]
    (hgt : 1 < finrank K M) :
    ∃ L : IntermediateField K M, finrank K L = p := by
  have hp : p.Prime := Fact.out
  have : ExpChar K p := .prime hp
  have hne : (⊥ : IntermediateField K M) ≠ ⊤ := fun hbot ↦ by
    have := congrArg (fun E : IntermediateField K M ↦ finrank K E) hbot
    rw [IntermediateField.finrank_bot, IntermediateField.finrank_top'] at this
    omega
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hne.symm)
  obtain ⟨m, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p x
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hdegx : finrank K K⟮x⟯ = 1 := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral x), hmin, pow_zero, natDegree_X_pow_sub_C]
    exact hx ((IntermediateField.finrank_eq_one_iff.1 hdegx).le (mem_adjoin_simple_self K x))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  let z : M := x ^ p ^ d
  have hz_not_bot : z ∉ (⊥ : IntermediateField K M) := by
    rintro ⟨c, hc⟩
    have hroot : aeval x (X ^ p ^ d - C c : K[X]) = 0 := by simp [z, ← hc]
    have hle := minpoly.min K x (monic_X_pow_sub_C c (pow_ne_zero d hp.ne_zero)) hroot
    rw [hmin, degree_X_pow_sub_C (pow_pos hp.pos _) y, degree_X_pow_sub_C (pow_pos hp.pos _) c,
      Nat.cast_le] at hle
    exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self d)).not_ge hle
  have hzp : aeval z (X ^ p - C y : K[X]) = 0 := by
    have hxroot := minpoly.aeval K x
    rw [hmin, map_sub, map_pow, aeval_X, aeval_C, pow_succ, pow_mul] at hxroot
    simpa [z] using hxroot
  have hz_le : finrank K K⟮z⟯ ≤ p := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral z)]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K z hzp)
      (X_pow_sub_C_ne_zero hp.pos y)).trans (by rw [natDegree_X_pow_sub_C])
  have hz_ne1 : finrank K K⟮z⟯ ≠ 1 := fun heq ↦
    hz_not_bot ((IntermediateField.finrank_eq_one_iff.1 heq).le (mem_adjoin_simple_self K z))
  have : IsPurelyInseparable K K⟮z⟯ := IsPurelyInseparable.tower_bot K K⟮z⟯ M
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow K K⟮z⟯ p
  have hr0 : r ≠ 0 := fun h0 ↦ hz_ne1 (by rw [hr, h0, pow_zero])
  have hr1 : r = 1 := le_antisymm
    ((Nat.pow_le_pow_iff_right hp.one_lt).1 (by simpa [hr] using hz_le)) (Nat.pos_of_ne_zero hr0)
  exact ⟨K⟮z⟯, by rw [hr, hr1, pow_one]⟩

/-- When `k` is exact in `F` and `k' / k` has prime degree `p`, the constant compositum
`F' = F · k'` also has degree `p` over `F`. -/
private theorem finrank_eq_of_isIntegrallyClosedIn_of_finrank_prime {k : Type u} {k' : Type u'}
    {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k']
    [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F']
    [IsScalarTower k F F'] {p : ℕ} (hp : p.Prime) (hk' : finrank k k' = p)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    finrank F F' = p := by
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  obtain ⟨α, hα⟩ := exists_adjoin_simple_eq_top_of_finrank_prime hp hk'
  have hα_int : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hFα : F⟮algebraMap k' F' α⟯ = ⊤ := by
    rw [← h, constantCompositum_eq_adjoin_of_adjoin_eq_top F k' F' ({α} : Set k') hα,
      Set.image_singleton]
  have hkα : k⟮algebraMap k' F' α⟯ = (IsScalarTower.toAlgHom k k' F').fieldRange := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro _ ⟨rfl⟩
      exact ⟨α, rfl⟩
    · rintro _ ⟨c, rfl⟩
      have hc : c ∈ k⟮α⟯ := hα ▸ IntermediateField.mem_top
      have hmap := IntermediateField.adjoin_map k ({α} : Set k') (IsScalarTower.toAlgHom k k' F')
      rw [Set.image_singleton] at hmap
      exact hmap.le ⟨c, hc, rfl⟩
  calc finrank F F'
      = finrank F F⟮algebraMap k' F' α⟯ := by rw [hFα, IntermediateField.finrank_top']
    _ = finrank k k⟮algebraMap k' F' α⟯ :=
        IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn
          hex (hα_int.map (IsScalarTower.toAlgHom k k' F'))
    _ = finrank k k' := by
        rw [hkα]
        exact
          (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k k' F')).symm.toLinearEquiv.finrank_eq
    _ = p := hk'

end PurelyInseparable

/-! ### Local monogenicity at a prime purely inseparable constant step -/

section LocalMonogenic

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

variable (k F) in
/-- At a place `P'` over `P = P'|_F`, the `(P'.restrict k F).integers`-submodule of `P'.integers`
cut out by `P.constantSpanIntegers k' F'`. -/
private noncomputable def Place.constantSpanSubmodule [Algebra.IsIntegral F F']
    (P' : Place k' F') : Submodule (P'.restrict k F).integers P'.integers where
  carrier := {x | (x : F') ∈ (P'.restrict k F).constantSpanIntegers k' F'}
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    rw [Set.mem_ofPred_eq, Algebra.smul_def, Subring.coe_mul, Place.coe_algebraMap_integers]
    exact Place.mul_mem_constantSpanIntegers k' F'
      (Place.algebraMap_mem_constantSpanIntegers k' F' r.2) hx

/-- In coordinates with respect to a `k`-basis `b` of `k'`, `P'.constantSpanSubmodule k F` is
spanned over `𝒪_P` by the images of `b`. -/
private theorem Place.constantSpanSubmodule_eq_span [FiniteDimensional k k']
    [Algebra.IsIntegral F F'] (h : constantCompositum F k' F' = ⊤)
    (hn : finrank F F' = finrank k k') (P' : Place k' F') {ι : Type*} [Finite ι]
    (b : Basis ι k k') :
    P'.constantSpanSubmodule k F = Submodule.span (P'.restrict k F).integers
      (Set.range fun i ↦ (⟨algebraMap k' F' (b i), P'.algebraMap_mem_integers (b i)⟩ :
        P'.integers)) := by
  classical
  cases nonempty_fintype ι
  set P := P'.restrict k F
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.2 ?_)
  · have hcoord := (P.mem_constantSpanIntegers_iff h hn b).1 hx
    let cF := constantBasisOfFinrankEq h hn b
    have hx_eq : x = ∑ i, (⟨cF.repr (x : F') i, hcoord i⟩ : P.integers) •
        (⟨algebraMap k' F' (b i), P'.algebraMap_mem_integers (b i)⟩ : P'.integers) := by
      refine Subtype.ext ?_
      conv_lhs => rw [← cF.sum_repr (x : F')]
      change _ = P'.integers.subtype (∑ i, _)
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change _ = ((⟨cF.repr (x : F') i, hcoord i⟩ : P.integers) •
        (⟨algebraMap k' F' (b i), P'.algebraMap_mem_integers (b i)⟩ : P'.integers) :
          P'.integers).1
      simp_rw [Algebra.smul_def]
      rw [Subring.coe_mul, Place.coe_algebraMap_integers, constantBasisOfFinrankEq_apply]
    rw [hx_eq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    change algebraMap k' F' (b i) ∈ P.constantSpanIntegers k' F'
    rw [← mul_one (algebraMap k' F' (b i)), ← map_one (algebraMap F F'), ← Algebra.smul_def]
    exact Submodule.smul_mem _ (b i) (Place.algebraMap_mem_constantSpanIntegers k' F' (one_mem _))

variable (k F) in
/-- When `F' / F` is purely inseparable, `P'` is the unique place over `P = P'|_F`, so `𝒪'_P`
coincides with `𝒪_{P'}` and `P'.integers ⧸ P'.constantSpanSubmodule k F` is `k`-linearly isomorphic
to `P.singularityQuotient k' F'`. -/
private noncomputable def Place.singularityQuotientLinearEquiv [Algebra.IsIntegral k k']
    [IsPurelyInseparable F F'] (hF' : IsFunctionField k' F') (P' : Place k' F') :
    letI := Place.integersAlgebraBase k P'
    haveI := Place.isScalarTower_integersAlgebraBase k P'
    haveI := Place.isScalarTower_integers_restrict k F P'
    (P'.integers ⧸ P'.constantSpanSubmodule k F) ≃ₗ[k]
      (P'.restrict k F).singularityQuotient k' F' :=
  letI := Place.integersAlgebraBase k P'
  haveI := Place.isScalarTower_integersAlgebraBase k P'
  haveI := Place.isScalarTower_integers_restrict k F P'
  let P := P'.restrict k F
  have hmem : ∀ z : F', z ∈ P.integralClosureSubmodule k' F' ↔ z ∈ P'.integers := fun z ↦ by
    rw [P.mem_integralClosureSubmodule_iff_forall_restrict_eq k' F' hF']
    exact ⟨fun hz ↦ hz P' rfl,
      fun hz Q' hQ' ↦ Place.restrict_injective_of_isPurelyInseparable k F hQ' ▸ hz⟩
  let eTop : P'.integers ≃ₗ[k] ↥(P.integralClosureSubmodule k' F') :=
    { toFun := fun x ↦ ⟨x.1, (hmem x.1).2 x.2⟩
      invFun := fun x ↦ ⟨x.1, (hmem x.1).1 x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ Subtype.ext <| by
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, Algebra.smul_def, Algebra.smul_def,
          Subring.coe_mul, IsScalarTower.algebraMap_apply k k' P'.integers,
          Place.coe_algebraMap_constants, ← IsScalarTower.algebraMap_apply k k' F'] }
  ((Submodule.Quotient.restrictScalarsEquiv k (P'.constantSpanSubmodule k F)).symm.trans
    (Submodule.Quotient.equiv ((P'.constantSpanSubmodule k F).restrictScalars k)
      (((P.constantSpanIntegers k' F').submoduleOf
        (P.integralClosureSubmodule k' F')).restrictScalars k) eTop (by
        ext ⟨z, hz⟩
        simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
        exact ⟨fun ⟨x, hx, hxz⟩ ↦ by cases hxz; exact hx,
          fun hz' ↦ ⟨⟨z, (hmem z).1 hz⟩, hz', rfl⟩⟩))).trans
    (Submodule.Quotient.restrictScalarsEquiv k _)

/-- At any place `P'` of a purely inseparable constant field extension `F' = F · k'` with
`[F' : F] = [k' : k]`, the valuation ring `𝒪_{P'}` is module-finite over `𝒪_P` (`P = P'|_F`). -/
private theorem Place.moduleFinite_integers_of_isPurelyInseparable [FiniteDimensional k k']
    [IsPurelyInseparable F F'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hn : finrank F F' = finrank k k') (P' : Place k' F') :
    Module.Finite (P'.restrict k F).integers P'.integers := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  let _ := Place.integersAlgebraBase k P'
  have := Place.isScalarTower_integersAlgebraBase k P'
  have := Place.isScalarTower_integers_restrict k F P'
  have : Module.Finite (P'.restrict k F).integers (P'.constantSpanSubmodule k F) := by
    rw [P'.constantSpanSubmodule_eq_span h hn (finBasis k k')]
    exact Module.Finite.span_of_finite _ (Set.finite_range _)
  have := (P'.restrict k F).finiteDimensional_singularityQuotient hF hex h hn
  have : FiniteDimensional k ((P'.restrict k F).singularityQuotient k' F') :=
    Module.Finite.trans k' _
  have : Module.Finite k (P'.integers ⧸ P'.constantSpanSubmodule k F) :=
    Module.Finite.equiv (P'.singularityQuotientLinearEquiv k F hF').symm
  have : Module.Finite (P'.restrict k F).integers (P'.integers ⧸ P'.constantSpanSubmodule k F) :=
    Module.Finite.of_restrictScalars_finite k (P'.restrict k F).integers _
  exact Module.Finite.of_submodule_quotient (P'.constantSpanSubmodule k F)

/-- Nakayama monogenicity of `𝒪_{P'}` over `𝒪_P` when `e(P' ∣ P) · f(P' ∣ P) = p` is prime. -/
private theorem Place.exists_adjoin_integers_eq_top_of_finrank_eq_prime {p : ℕ} (hp : p.Prime)
    [FiniteDimensional k k'] [IsPurelyInseparable F F'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hFF' : finrank F F' = p) (hn : finrank F F' = finrank k k') (P' : Place k' F') :
    ∃ β : P'.integers, Algebra.adjoin (P'.restrict k F).integers {β} = ⊤ := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : Module.Finite (P'.restrict k F).integers P'.integers :=
    P'.moduleFinite_integers_of_isPurelyInseparable hF hex h hn
  have hef : Place.ramificationIdx F P' * Place.relativeDegree k F P' = p :=
    (Place.ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable k F hF P').trans
      hFF'
  rw [Place.relativeDegree_def] at hef
  rcases hp.eq_one_or_self_of_dvd _ ⟨_, ((mul_comm _ _).trans hef).symm⟩ with hf1 | hfp
  · obtain ⟨_, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible P'.integers
    have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf1).2
    exact ⟨_,
      IsLocalRing.adjoin_eq_top_of_algebraMap_residueField_surjective_of_span_eq_maximalIdeal
        hsurj hπ.maximalIdeal_eq.symm⟩
  · have he1 : Place.ramificationIdx F P' = 1 := by
      rw [hfp] at hef
      nlinarith [hp.pos]
    obtain ⟨bar_b, hbar⟩ := exists_adjoin_simple_eq_top_of_finrank_prime hp hfp
    obtain ⟨β, hβ⟩ := residue_surjective (R := P'.integers) bar_b
    obtain ⟨t₀, ht₀⟩ := (P'.restrict k F).exists_isUniformizer
    have ht₀_ord : (P'.restrict k F).ord t₀ = 1 :=
      (P'.restrict k F).isUniformizer_iff_ord_eq_one.1 ht₀
    let π₀ : (P'.restrict k F).integers :=
      ⟨t₀, (P'.restrict k F).mem_integers_iff_ord_nonneg.2 (by omega)⟩
    have hπ₀_unif : P'.valuation.IsUniformizer
        ((algebraMap (P'.restrict k F).integers P'.integers π₀ : P'.integers) : F') := by
      rw [P'.isUniformizer_iff_ord_eq_one, Place.coe_algebraMap_integers,
        Place.ord_algebraMap_restrict k F P', he1, Nat.cast_one, one_mul, ht₀_ord]
    have hspan : Ideal.span {aeval β (C π₀)} = maximalIdeal P'.integers := by
      rw [aeval_C]
      exact (P'.irreducible_of_isUniformizer hπ₀_unif).maximalIdeal_eq.symm
    refine ⟨β, TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := C π₀) ?_ hspan⟩
    rw [hβ, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic bar_b), hbar]
    rfl

/-- **Local monogenicity at a prime purely inseparable step**: when `[k' : k] = p` is prime and
`k' / k` is purely inseparable, `𝒪_{P'}` admits a power basis of dimension `p` over `𝒪_P`. -/
theorem Place.exists_powerBasis_integers_of_finrank_eq_prime {p : ℕ} [Fact p.Prime]
    [IsPurelyInseparable k k'] [Algebra.IsIntegral F F'] (hk' : finrank k k' = p)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ∃ pb : PowerBasis (P'.restrict k F).integers P'.integers, pb.dim = p := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have hFF' : finrank F F' = p := finrank_eq_of_isIntegrallyClosedIn_of_finrank_prime hp hk' hex h
  have hn : finrank F F' = finrank k k' := hFF'.trans hk'.symm
  have : Module.Finite (P'.restrict k F).integers P'.integers :=
    P'.moduleFinite_integers_of_isPurelyInseparable hF hex h hn
  obtain ⟨β, hβ⟩ := P'.exists_adjoin_integers_eq_top_of_finrank_eq_prime hp hF hex h hFF' hn
  have : FaithfulSMul (P'.restrict k F).integers P'.integers :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y hxy ↦ Subtype.ext <|
      (algebraMap F F').injective
        (by simpa [Place.coe_algebraMap_integers] using congrArg Subtype.val hxy)
  have : IsScalarTower (P'.restrict k F).integers P'.integers F' :=
    .of_algebraMap_eq fun x ↦ by
      change algebraMap F F' (x : F) =
        ((algebraMap (P'.restrict k F).integers P'.integers x : P'.integers) : F')
      rw [Place.coe_algebraMap_integers]
  refine ⟨PowerBasis.ofAdjoinEqTop' (IsIntegral.of_finite _ β) hβ, ?_⟩
  rw [← PowerBasis.finrank, ← IsFractionRing.finrank_eq (P'.restrict k F).integers F P'.integers F',
    hFF']

end LocalMonogenic

/-! ### The local Tate–Schröer formula -/

section LocalFormula

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

/-- Given a power basis `pb` of `S` over `R` of prime dimension `p` in characteristic `p` with
`pb.gen ^ p ∈ R`, the transition matrix from `pb.basis` to the powers `1, α, …, α ^ (p - 1)` of any
`α ∈ S` has determinant `f'(pb.gen) ^ (p (p - 1) / 2)` in `S`. -/
private theorem det_toMatrix_pow_eq_derivative_eval_pow {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] {p : ℕ} [Fact p.Prime] [CharP S p] (pb : PowerBasis R S)
    (hdim : pb.dim = p) {b : R} (hb : algebraMap R S b = pb.gen ^ p) (α : S) :
    let w : Basis (Fin p) R S := pb.basis.reindex (finCongr hdim)
    let ψ : S →ₗ[R] S := w.constr R fun i : Fin p ↦ α ^ (i : ℕ)
    let A : Matrix (Fin p) (Fin p) R := LinearMap.toMatrix w w ψ
    ∃ f : R[X], algebraMap R S A.det = (aeval pb.gen f.derivative) ^ (p * (p - 1) / 2) := by
  classical
  have hp : p.Prime := Fact.out
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R S)
  set w : Basis (Fin p) R S := pb.basis.reindex (finCongr hdim)
  have hw (j : Fin p) : w j = pb.gen ^ (j : ℕ) := by simp [w]
  set ψ : S →ₗ[R] S := w.constr R fun i : Fin p ↦ α ^ (i : ℕ)
  set A : Matrix (Fin p) (Fin p) R := LinearMap.toMatrix w w ψ
  have hcol (i : Fin p) : α ^ (i : ℕ) = ∑ j : Fin p, algebraMap R S (A j i) * pb.gen ^ (j : ℕ) := by
    rw [← w.constr_basis R (fun m : Fin p ↦ α ^ (m : ℕ)) i, ← w.sum_repr (ψ (w i))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← LinearMap.toMatrix_apply w w ψ j i, Algebra.smul_def, hw]
  let i₁ : Fin p := ⟨1, hp.one_lt⟩
  let f : R[X] := ∑ j : Fin p, C (A j i₁) * X ^ (j : ℕ)
  have hf_eval : aeval pb.gen f = α := by simpa [f, i₁, map_sum] using (hcol i₁).symm
  have hdvd_R (i : Fin p) :
      (X ^ p - C b) ∣ f ^ (i : ℕ) - ∑ j : Fin p, C (A j i) * X ^ (j : ℕ) := by
    set q : R[X] := f ^ (i : ℕ) - ∑ j : Fin p, C (A j i) * X ^ (j : ℕ)
    have hm : (X ^ p - C b).Monic := monic_X_pow_sub_C b hp.ne_zero
    have hne1 : (X ^ p - C b : R[X]) ≠ 1 := fun h1 ↦
      hp.ne_zero (by simpa [natDegree_X_pow_sub_C] using congrArg natDegree h1)
    rw [← modByMonic_eq_zero_iff_dvd hm]
    have hdeg : (q %ₘ (X ^ p - C b)).natDegree < p :=
      (natDegree_modByMonic_lt q hm hne1).trans_eq (by rw [natDegree_X_pow_sub_C])
    have haeval_mod : aeval pb.gen (q %ₘ (X ^ p - C b)) = 0 := by
      have := congrArg (aeval pb.gen) (modByMonic_add_div q (X ^ p - C b))
      have hq0 : aeval pb.gen q = 0 := by
        simpa [q, hf_eval, map_sum] using sub_eq_zero.2 (hcol i)
      simpa [hb, hq0] using this
    have hsum : ∑ j : Fin p, C ((q %ₘ (X ^ p - C b)).coeff j) * X ^ (j : ℕ) =
        q %ₘ (X ^ p - C b) := by
      rw [Fin.sum_univ_eq_sum_range (fun m ↦ C ((q %ₘ (X ^ p - C b)).coeff m) * X ^ m) p]
      exact ((q %ₘ (X ^ p - C b)).as_sum_range_C_mul_X_pow' hdeg).symm
    rw [← hsum] at haeval_mod ⊢
    simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, ← hw, ← Algebra.smul_def] at haeval_mod
    have hcoeff := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ haeval_mod
    simp [hcoeff]
  refine ⟨f, ?_⟩
  have hdvd_S (i : Fin p) : (X - C pb.gen) ^ p ∣
      (f.map (algebraMap R S)) ^ (i : ℕ) -
        ∑ j : Fin p, C (((algebraMap R S).mapMatrix A) j i) * X ^ (j : ℕ) := by
    have hmap := Polynomial.map_dvd (algebraMap R S) (hdvd_R i)
    have hfac : (X ^ p - C b).map (algebraMap R S) = (X - C pb.gen) ^ p := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hb,
        sub_pow_char, ← C_pow]
    simpa [hfac, Polynomial.map_sum] using hmap
  rw [RingHom.map_det (algebraMap R S), Matrix.det_of_X_sub_C_pow_dvd_pow_sub_sum hdvd_S,
    Polynomial.derivative_map, Polynomial.eval_map, aeval_def]

/-- When `cF` is an `F`-basis of `F'` whose `i`-th vector is `ψ (w i)`, the matrix of `ψ` in an
`𝒪_P`-basis `w` of `𝒪_{P'}` has nonzero determinant. -/
private theorem Place.det_toMatrix_ne_zero_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Algebra.IsIntegral F F'] (P' : Place k' F')
    (w : Basis ι (P'.restrict k F).integers P'.integers)
    (ψ : P'.integers →ₗ[(P'.restrict k F).integers] P'.integers) (cF : Basis ι F F')
    (hcF : ∀ i, cF i = (ψ (w i) : F')) :
    (LinearMap.toMatrix w w ψ).det ≠ 0 := by
  set P := P'.restrict k F
  set A := LinearMap.toMatrix w w ψ
  intro h0
  have h0F : ((algebraMap P.integers F).mapMatrix A).det = 0 := by
    rw [← RingHom.map_det, h0, map_zero]
  obtain ⟨u, hu0, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0F
  refine hu0 (funext <| (Fintype.linearIndependent_iff.1 cF.linearIndependent) u ?_)
  have hψi (i : ι) : cF i = ∑ j, (A j i : F) • (w j : F') := by
    rw [hcF i]
    conv_lhs => rw [← w.sum_repr (ψ (w i))]
    change P'.integers.subtype (∑ j, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change ((w.repr (ψ (w i)) j • w j : P'.integers) : F') = _
    rw [← LinearMap.toMatrix_apply w w ψ j i]
    simp_rw [Algebra.smul_def]
    rw [Subring.coe_mul, Place.coe_algebraMap_integers]
  calc ∑ i, u i • cF i
      = ∑ j, (∑ i, (A j i : F) * u i) • (w j : F') := by
        simp_rw [hψi, Finset.smul_sum, smul_smul, mul_comm (u _)]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        have hj : ∑ i, (A j i : F) * u i = 0 := by
          simpa [Matrix.mulVec, dotProduct] using congrFun hmul j
        rw [hj, zero_smul]

/-- Comparing `𝒪_P`-length and `k'`-dimension identifies `p · δ_P` with `ord_P(det A) · deg P`. -/
private theorem Place.mul_singularityDegree_eq_toNat_ord_det_mul_degree {p : ℕ} (hp : p.Prime)
    [FiniteDimensional k k'] [IsPurelyInseparable F F'] (hk' : finrank k k' = p)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    (w : Basis (Fin p) (P'.restrict k F).integers P'.integers) {α : k'} (hα : k⟮α⟯ = ⊤) :
    let αS : P'.integers := ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
    let ψ := w.constr (P'.restrict k F).integers fun i : Fin p ↦ αS ^ (i : ℕ)
    let A := LinearMap.toMatrix w w ψ
    (A.det : F) ≠ 0 ∧
      p * (P'.restrict k F).singularityDegree k' F' =
        ((P'.restrict k F).ord (A.det : F)).toNat * (P'.restrict k F).degree := by
  classical
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  have hn : finrank F F' = finrank k k' :=
    (finrank_eq_of_isIntegrallyClosedIn_of_finrank_prime hp hk' hex h).trans hk'.symm
  set P := P'.restrict k F
  let αS : P'.integers := ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
  let ψ := w.constr P.integers fun i : Fin p ↦ αS ^ (i : ℕ)
  let A := LinearMap.toMatrix w w ψ
  let pbk : PowerBasis k k' :=
    PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hα
  have hpbk_dim : pbk.dim = p := pbk.finrank.symm.trans hk'
  let bk : Basis (Fin p) k k' := pbk.basis.reindex (finCongr hpbk_dim)
  have hbk (i : Fin p) : bk i = α ^ (i : ℕ) := by simp [bk, pbk]
  let cF : Basis (Fin p) F F' := constantBasisOfFinrankEq h hn bk
  have hcF (i : Fin p) : cF i = (ψ (w i) : F') := by
    rw [constantBasisOfFinrankEq_apply, hbk, map_pow, w.constr_basis]
    rfl
  have hAdet : A.det ≠ 0 := P'.det_toMatrix_ne_zero_of_basis w ψ cF hcF
  have hAdetF : (A.det : F) ≠ 0 := fun h0 ↦ hAdet (Subtype.ext h0)
  have hrange : LinearMap.range ψ = P'.constantSpanSubmodule k F := by
    rw [LinearMap.range_eq_map, ← w.span_eq, Submodule.map_span, ← Set.range_comp,
      P'.constantSpanSubmodule_eq_span h hn bk]
    refine congrArg (Submodule.span P.integers) (congrArg Set.range (funext fun i ↦ ?_))
    rw [Function.comp_apply, w.constr_basis]
    exact Subtype.ext (by simp [αS, hbk])
  let _ := Place.integersAlgebraBase k P'
  have := Place.isScalarTower_integersAlgebraBase k P'
  have := Place.isScalarTower_integers_restrict k F P'
  have hlen : (Module.length P.integers (P'.integers ⧸ P'.constantSpanSubmodule k F)).toNat =
      (P.ord (A.det : F)).toNat := by
    rw [← hrange, w.length_quotient_range_eq_length_quotient_range_toMatrix ψ,
      Matrix.length_quotient_range_mulVecLin_eq_ord_det A hAdet,
      P.ringOrd_integers_eq_toNat_ord hAdetF, ENat.toNat_natCast]
  have hfinrank_k : p * P.singularityDegree k' F' = finrank k (P.singularityQuotient k' F') := by
    rw [← hk', Place.singularityDegree_def k' F' P,
      Module.finrank_mul_finrank k k' (P.singularityQuotient k' F')]
  refine ⟨hAdetF, ?_⟩
  rw [hfinrank_k, ← (P'.singularityQuotientLinearEquiv k F hF').finrank_eq,
    TauCeti.finrank_eq_length_mul_finrank_residueField k P.integers
      (P'.integers ⧸ P'.constantSpanSubmodule k F), hlen, P.degree_eq_finrank]

/-- Valuation arithmetic translating `det A = dS ^ (p (p - 1) / 2)` into
`2 e(P' ∣ P) ord_P(det A) = p (p - 1) ord_{P'}(dS)`. -/
private theorem Place.two_mul_ramificationIdx_mul_toNat_ord_eq {p : ℕ} (hp : p.Prime)
    [Algebra.IsIntegral F F'] (P' : Place k' F') {x : (P'.restrict k F).integers}
    {d : P'.integers} (hxd : algebraMap (P'.restrict k F).integers P'.integers x =
      d ^ (p * (p - 1) / 2)) :
    2 * Place.ramificationIdx F P' * ((P'.restrict k F).ord (x : F)).toNat =
      p * (p - 1) * (P'.ord (d : F')).toNat := by
  have hval := congrArg (fun y : P'.integers ↦ P'.ord (y : F')) hxd
  rw [Place.coe_algebraMap_integers, Place.ord_algebraMap_restrict k F P', Subring.coe_pow,
    P'.ord_pow (d : F')] at hval
  have hx_nn : 0 ≤ (P'.restrict k F).ord (x : F) :=
    (P'.restrict k F).mem_integers_iff_ord_nonneg.1 x.2
  have hd_nn : 0 ≤ P'.ord (d : F') := P'.mem_integers_iff_ord_nonneg.1 d.2
  have h2 : 2 * (p * (p - 1) / 2) = p * (p - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self p).two_dvd
  have h2z : (2 : ℤ) * ↑(p * (p - 1) / 2) = ↑p * (↑p - 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h2
    have hp1 : 1 ≤ p := hp.pos
    push_cast [hp1] at this ⊢
    exact this
  refine Nat.cast_injective (R := ℤ) ?_
  have hp1 : 1 ≤ p := hp.pos
  push_cast [hp1]
  rw [Int.toNat_of_nonneg hx_nn, Int.toNat_of_nonneg hd_nn]
  linear_combination 2 * hval + P'.ord (d : F') * h2z

/-- **Local Tate–Schröer formula**: for a purely inseparable constant field extension `F' = F · k'`
of prime degree `p` over a function field `F / k` with exact constants, at the unique place `P'`
above `P = P'|_F` there is a natural number `m` such that `2 δ_P = (p - 1) · m · deg P'`. -/
theorem Place.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime {p : ℕ}
    [Fact p.Prime] [CharP k p] [IsPurelyInseparable k k'] [Algebra.IsIntegral F F']
    (hk' : finrank k k' = p) (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ∃ m : ℕ, 2 * (P'.restrict k F).singularityDegree k' F' = (p - 1) * m * P'.degree := by
  classical
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have hFF' : finrank F F' = p := finrank_eq_of_isIntegrallyClosedIn_of_finrank_prime hp hk' hex h
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have : ExpChar F p := .prime hp
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : CharP P'.integers p :=
    charP_of_injective_algebraMap (algebraMap k' P'.integers).injective p
  obtain ⟨pb, hdim⟩ := P'.exists_powerBasis_integers_of_finrank_eq_prime hk' hF hex h
  obtain ⟨b₀, hb₀⟩ := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow F F' p (n := 1)
    (by simp [hFF']) (pb.gen : F')
  rw [pow_one] at hb₀
  let b : (P'.restrict k F).integers :=
    ⟨b₀, (Place.mem_integers_iff_of_algebraMap_eq_pow k F P' hp.ne_zero hb₀).1 pb.gen.2⟩
  obtain ⟨α, hα⟩ := exists_adjoin_simple_eq_top_of_finrank_prime hp hk'
  let αS : P'.integers := ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
  obtain ⟨f, hfdet⟩ := det_toMatrix_pow_eq_derivative_eval_pow pb hdim (Subtype.ext hb₀ :
    algebraMap (P'.restrict k F).integers P'.integers b = pb.gen ^ p) αS
  let w : Basis (Fin p) (P'.restrict k F).integers P'.integers := pb.basis.reindex (finCongr hdim)
  obtain ⟨-, hlen⟩ := P'.mul_singularityDegree_eq_toNat_ord_det_mul_degree hp hk' hF hex h w hα
  have hord_eq := P'.two_mul_ramificationIdx_mul_toNat_ord_eq hp hfdet
  have hef : Place.ramificationIdx F P' * Place.relativeDegree k F P' = p :=
    (Place.ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable k F hF P').trans
      hFF'
  have hfdeg : Place.relativeDegree k F P' * (P'.restrict k F).degree = p * P'.degree := by
    simpa [hk'] using (Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P').symm
  refine ⟨(P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat,
    Nat.mul_left_cancel (Nat.mul_pos hp.pos hp.pos) ?_⟩
  calc p * p * (2 * (P'.restrict k F).singularityDegree k' F')
      = 2 * (Place.ramificationIdx F P' * Place.relativeDegree k F P') *
          (p * (P'.restrict k F).singularityDegree k' F') := by rw [hef]; ring
    _ = (2 * Place.ramificationIdx F P' * ((P'.restrict k F).ord _).toNat) *
          (Place.relativeDegree k F P' * (P'.restrict k F).degree) := by rw [hlen]; ring
    _ = (p * (p - 1) * (P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat) *
          (p * P'.degree) := by rw [hord_eq, hfdeg]
    _ = p * p * ((p - 1) * (P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat *
          P'.degree) := by ring

/-- **Local Tate divisibility**: in a purely inseparable constant field extension `F' = F · k'` of
prime degree `p` over a function field `F / k` with exact constants, `p - 1` divides `2 δ_P` at
every place `P` of `F / k`. -/
theorem Place.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime {p : ℕ} [Fact p.Prime]
    [CharP k p] [IsPurelyInseparable k k'] (hk' : finrank k k' = p) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    (p - 1) ∣ 2 * P.singularityDegree k' F' := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  obtain ⟨P', rfl⟩ := Place.restrict_surjective (hF.of_constantCompositum_eq_top h) P
  obtain ⟨m, hm⟩ := P'.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime hk' hF hex h
  exact ⟨m * P'.degree, by rw [hm, mul_assoc]⟩

/-- For an odd prime `p`, `(p - 1) / 2` divides the local singularity degree `δ_P` at every place
`P` of a degree-`p` purely inseparable constant extension. -/
theorem Place.half_sub_one_dvd_singularityDegree_of_finrank_eq_prime {p : ℕ} [Fact p.Prime]
    [CharP k p] [IsPurelyInseparable k k'] (hp2 : p ≠ 2) (hk' : finrank k k' = p)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    ((p - 1) / 2) ∣ P.singularityDegree k' F' := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  refine (Nat.mul_dvd_mul_iff_left two_pos).1 ?_
  rw [h2]
  exact P.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime hk' hF hex h

end LocalFormula

/-! ### Tate's genus-change theorem -/

section Tate

/-- In a degree-`p` purely inseparable constant extension over an exact base constant field `k`,
any algebraic constant enlargement `k'' / k'` inside `F'` is purely inseparable over `k'`. -/
private theorem isPurelyInseparable_enlargement_of_finrank_eq_prime {k : Type u} {k' : Type u'}
    {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k']
    [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F']
    [IsScalarTower k F F'] {p : ℕ} (hp : p.Prime) [CharP k p] [FiniteDimensional k k']
    [IsPurelyInseparable F F'] (hex : IsIntegrallyClosedIn k F) (hFF' : finrank F F' = p)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] :
    IsPurelyInseparable k' k'' := by
  have : FiniteDimensional F F' := Module.finite_of_finrank_pos (hFF' ▸ hp.pos)
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have : ExpChar F p := .prime hp
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime hp
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  rw [isPurelyInseparable_iff_pow_mem k' p]
  intro c
  obtain ⟨y, hy⟩ := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow F F' p (n := 1)
    (by simp [hFF']) (algebraMap k'' F' c)
  rw [pow_one] at hy
  have hy_int : IsIntegral k y := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom k F F') (algebraMap F F').injective).1 ?_
    change IsIntegral k (algebraMap F F' y)
    rw [hy, ← map_pow]
    exact (Algebra.IsIntegral.isIntegral (R := k) (c ^ p)).map (IsScalarTower.toAlgHom k k'' F')
  obtain ⟨c₀, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hy_int
  refine ⟨1, algebraMap k k' c₀, (algebraMap k'' F').injective ?_⟩
  rw [pow_one, map_pow, ← hy, ← IsScalarTower.algebraMap_apply k F F',
    ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']

/-- Tate's genus-change divisibility for a single purely inseparable constant step of prime degree
`p`, allowing constant growth into an exact constant field `k''` of `F'`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime {k : Type u}
    {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k k'] (hk' : finrank k k' = p) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' ≤ genus k F ∧ (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have hFF' : finrank F F' = p := finrank_eq_of_isIntegrallyClosedIn_of_finrank_prime hp hk' hex h
  have hn : finrank F F' = finrank k k' := hFF'.trans hk'.symm
  have hF' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime hp
  have : IsPurelyInseparable k' k'' :=
    isPurelyInseparable_enlargement_of_finrank_eq_prime hp hex hFF' (k'' := k'')
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow k' k'' p
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree
    hF hex h hn hex''
  have hsupp : (Function.support fun P : Place k F ↦ (P.singularityDegree k' F' : ℤ)) ⊆
      hfin.toFinset := fun P hP ↦ by simpa [Function.mem_support] using hP
  rw [finsum_eq_sum_of_support_subset _ hsupp] at heq
  have hgle : genus k'' F' ≤ genus k F := by
    have hm1 : (1 : ℤ) ≤ finrank k' k'' := by exact_mod_cast (finrank_pos (R := k') (M := k''))
    have hsum : (0 : ℤ) ≤ ∑ P ∈ hfin.toFinset, (P.singularityDegree k' F' : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    by_cases hg0 : genus k'' F' = 0 <;> [omega; nlinarith]
  have hid : (2 * ((genus k F : ℤ) - genus k'' F') : ℤ) =
      2 * ((finrank k' k'' : ℤ) - 1) * ((genus k'' F' : ℤ) - 1) +
        ∑ P ∈ hfin.toFinset, (2 * (P.singularityDegree k' F' : ℤ)) := by
    rw [← Finset.mul_sum]; linarith
  have hp1 : 1 ≤ p := hp.pos
  have hdvd_z : ((p : ℤ) - 1) ∣ 2 * ((genus k F : ℤ) - genus k'' F') := by
    rw [hid]
    refine dvd_add ?_ (Finset.dvd_sum fun P _ ↦ ?_)
    · rw [hm, Nat.cast_pow]
      exact (dvd_mul_of_dvd_right (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 m) 2).mul_right _
    · have hdvdP := Int.natCast_dvd_natCast.2
        (P.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime hk' hF hex h)
      rwa [Nat.cast_sub hp1, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hdvdP
  refine ⟨hgle, (Int.natCast_dvd_natCast.1 ?_)⟩
  simpa [hp1, hgle] using hdvd_z

/-- Single prime-step decomposition inside a nontrivial finite purely inseparable constant
extension `K → M` with exact constants on both sides: given an intermediate field `L` of degree `p`
over `K`, cutting out `L₁ = (E · L) ∩ M` as an intermediate field over `L` produces a strict
subextension `L₁ → M` with exact constants in `E · L` whose genus drop from `E / K` satisfies
Tate's divisibility. -/
private theorem exists_step_of_finrank_eq_prime {K M : Type u'} {E F' : Type v'} [Field K]
    [Field M] [Field E] [Field F'] [Algebra K M] [Algebra K E] [Algebra K F'] [Algebra M F']
    [Algebra E F'] [IsScalarTower K M F'] [IsScalarTower K E F'] {p : ℕ} [Fact p.Prime] [CharP K p]
    [IsPurelyInseparable K M] [FiniteDimensional K M] (L : IntermediateField K M)
    (hL : finrank K L = p) (hE : IsFunctionField K E) (hexK : IsIntegrallyClosedIn K E)
    (hEM : constantCompositum E M F' = ⊤) (hexM : IsIntegrallyClosedIn M F') :
    ∃ (L₁ : IntermediateField L M) (EL : Type v') (_ : Field EL) (_ : Algebra L₁ EL)
      (_ : Algebra EL F') (_ : IsScalarTower L₁ EL F'),
      finrank L₁ M < finrank K M ∧ IsFunctionField L₁ EL ∧ IsIntegrallyClosedIn L₁ EL ∧
        constantCompositum EL M F' = ⊤ ∧ genus L₁ EL ≤ genus K E ∧
        (p - 1) ∣ 2 * (genus K E - genus L₁ EL) := by
  let EL := constantCompositum E L F'
  let _ := constantCompositumAlgebra E L F'
  have := isScalarTower_constantCompositum E L F'
  have := isScalarTower_base_constantCompositum K E L F'
  have hEL : constantCompositum E L EL = ⊤ := (constantCompositum_eq_top_iff E L F' EL).2 rfl
  let L₀ : IntermediateField K M := (EL.restrictScalars K).comap (IsScalarTower.toAlgHom K M F')
  have hLL₀ : L ≤ L₀ := fun m hm ↦ by
    change algebraMap M F' (algebraMap L M ⟨m, hm⟩) ∈ EL
    rw [← IsScalarTower.algebraMap_apply L M F']
    exact algebraMap_mem_constantCompositum E L F' ⟨m, hm⟩
  let L₁ : IntermediateField L M := IntermediateField.extendScalars hLL₀
  have hmEL (m : L₁) : algebraMap L₁ F' m ∈ EL := by
    rw [IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
    exact show algebraMap M F' (m : M) ∈ EL from (IntermediateField.mem_extendScalars hLL₀).1 m.2
  let _ : Algebra L₁ EL := ((algebraMap L₁ F').codRestrict EL hmEL).toAlgebra
  have : IsScalarTower L L₁ EL := .of_algebraMap_eq fun c ↦ Subtype.ext <| by
    change algebraMap L F' c = algebraMap L₁ F' (algebraMap L L₁ c)
    rw [← IsScalarTower.algebraMap_apply L L₁ F']
  have hst : IsScalarTower L₁ EL F' := .of_algebraMap_eq fun m ↦ by
    rw [IntermediateField.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]
  have : FiniteDimensional L M := FiniteDimensional.right K L M
  have : FiniteDimensional L L₁ := FiniteDimensional.left L L₁ M
  have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
  have hexL₁ : IsIntegrallyClosedIn L₁ EL :=
    isIntegrallyClosedIn_iff.2 ⟨(algebraMap L₁ EL).injective, fun {y} hy ↦ by
      have hyM : IsIntegral M (y : F') := (hy.map (IsScalarTower.toAlgHom L₁ EL F')).tower_top
      obtain ⟨m, hm⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hyM
      have hm₀ : m ∈ L₀ := show algebraMap M F' m ∈ EL from hm.symm ▸ y.2
      refine ⟨⟨m, (IntermediateField.mem_extendScalars hLL₀).2 hm₀⟩, Subtype.ext ?_⟩
      rw [RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
        IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
      exact hm⟩
  obtain ⟨hgle₁, hdvd₁⟩ :=
    sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime hL hE hexK hEL (k'' := L₁) hexL₁
  have hlt : finrank L₁ M < finrank K M := by
    have h1 := finrank_mul_finrank K L M
    have h2 := finrank_mul_finrank L L₁ M
    have hp : p.Prime := Fact.out
    have := hp.one_lt
    have : 0 < finrank L L₁ := finrank_pos
    have : 0 < finrank L₁ M := finrank_pos
    nlinarith
  exact ⟨L₁, EL, inferInstance, inferInstance, inferInstance, hst, hlt,
    (hE.of_constantCompositum_eq_top hEL).of_isAlgebraic, hexL₁,
    constantCompositum_eq_top_of_eq_top E M F' EL hEM, hgle₁, hdvd₁⟩

/-- Induction over finite purely inseparable constant extensions with exact constants on both
sides, stepping along intermediate fields of prime degree `p`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite (p : ℕ)
    [Fact p.Prime] (n : ℕ) :
    ∀ (K M : Type u') (E F' : Type v') [Field K] [Field M] [Field E] [Field F'] [Algebra K M]
      [Algebra K E] [Algebra K F'] [Algebra M F'] [Algebra E F'] [IsScalarTower K M F']
      [IsScalarTower K E F'] [CharP K p] [IsPurelyInseparable K M] [FiniteDimensional K M],
      finrank K M = n → IsFunctionField K E → IsIntegrallyClosedIn K E →
      constantCompositum E M F' = ⊤ → IsIntegrallyClosedIn M F' →
      (p - 1) ∣ 2 * (genus K E - genus M F') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K M E F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hE hexK hEM hexM
  by_cases hgt : 1 < n
  · obtain ⟨L, hL⟩ := exists_intermediateField_finrank_eq_prime p (K := K) (M := M) (hn ▸ hgt)
    obtain ⟨L₁, EL, _, _, _, _, hlt, hFEL₁, hexL₁, hELM_top, hgle₁, hdvd₁⟩ :=
      exists_step_of_finrank_eq_prime L hL hE hexK hEM hexM
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap L L₁).injective p
    have : IsPurelyInseparable L M := IsPurelyInseparable.tower_top K L M
    have : IsPurelyInseparable L₁ M := IsPurelyInseparable.tower_top L L₁ M
    have : FiniteDimensional L M := FiniteDimensional.right K L M
    have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
    have hdvd₂ := ih _ (hn ▸ hlt) L₁ M EL F' rfl hFEL₁ hexL₁ hELM_top hexM
    have hgle₂ : genus M F' ≤ genus L₁ EL :=
      genus_le_genus_of_constantCompositum_eq_top hFEL₁ hELM_top
    have hsplit : 2 * (genus K E - genus M F') =
        2 * (genus K E - genus L₁ EL) + 2 * (genus L₁ EL - genus M F') := by omega
    rw [hsplit]
    exact dvd_add hdvd₁ hdvd₂
  · have hn1 : finrank K M = 1 := le_antisymm (hn ▸ not_lt.1 hgt) finrank_pos
    have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hn1
    have : Algebra.IsSeparable K M :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofBijective (Algebra.ofId K M) hbij)
    rw [genus_eq_genus_of_constantCompositum_eq_top hE hexK hEM, Nat.sub_self, mul_zero]
    exact dvd_zero _

/-- Tate's genus-change divisibility for a finite algebraic constant field extension with exact
constants on both sides, splitting `k → M` at the separable closure of `k` in `M`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn
    {k : Type u} {M : Type u'} {F : Type v} {FM : Type v'} [Field k] [Field M] [Field F]
    [Field FM] [Algebra k M] [Algebra k F] [Algebra k FM] [Algebra M FM] [Algebra F FM]
    [IsScalarTower k M FM] [IsScalarTower k F FM] {p : ℕ} [Fact p.Prime] [CharP k p]
    [FiniteDimensional k M] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hFM : constantCompositum F M FM = ⊤) (hexM : IsIntegrallyClosedIn M FM) :
    (p - 1) ∣ 2 * (genus k F - genus M FM) := by
  let S : IntermediateField k M := separableClosure k M
  let FS := constantCompositum F S FM
  let := constantCompositumAlgebra F S FM
  have := isScalarTower_constantCompositum F S FM
  have := isScalarTower_base_constantCompositum k F S FM
  have hFS : constantCompositum F S FS = ⊤ := (constantCompositum_eq_top_iff F S FM FS).2 rfl
  have hFFS : IsFunctionField S FS := hF.of_constantCompositum_eq_top hFS
  have hexS : IsIntegrallyClosedIn S FS := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hFS
  have hgS : genus S FS = genus k F := genus_eq_genus_of_constantCompositum_eq_top hF hex hFS
  have hFSM : constantCompositum FS M FM = ⊤ := constantCompositum_eq_top_of_eq_top F M FM FS hFM
  have : CharP S p := charP_of_injective_algebraMap (algebraMap k S).injective p
  have : IsPurelyInseparable S M := separableClosure.isPurelyInseparable k M
  rw [← hgS]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite p (finrank S M)
    S M FS FM rfl hFFS hexS hFSM hexM

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **Tate's genus-change theorem** (exact constants): for any algebraic constant field extension
`F' = F · k'` of a function field `F / k` in prime characteristic `p`, finite or infinite, if `k`
is exact in `F` and `k'` is exact in `F'`, then `p - 1` divides `2 (g(F / k) - g(F' / k'))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hex' : IsIntegrallyClosedIn k' F') :
    (p - 1) ∣ 2 * (genus k F - genus k' F') := by
  obtain ⟨L, _, hexL, hgL⟩ := exists_finiteDimensional_isIntegrallyClosedIn_genus_eq hF h hex'
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  have := isScalarTower_constantCompositum F L F'
  have := isScalarTower_base_constantCompositum k F L F'
  have hFL : constantCompositum F L FL = ⊤ := (constantCompositum_eq_top_iff F L F' FL).2 rfl
  rw [← hgL]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn hF hex hFL hexL

/-- Composing `k → k' → k''` preserves `constantCompositum F _ F' = ⊤` and the genus bound
`genus k'' F' ≤ genus k F`. -/
private theorem genus_le_and_constantCompositum_eq_top_of_enlargement [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) {k'' : Type*} [Field k'']
    [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k''] :
    letI : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
    ∃ (_ : IsScalarTower k k'' F') (_ : Algebra.IsAlgebraic k k''),
      constantCompositum F k'' F' = ⊤ ∧ genus k'' F' ≤ genus k F := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have hst : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have halg : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  have h'' : constantCompositum F k'' F' = ⊤ := by
    rw [eq_top_iff, ← h]
    refine (constantCompositum_le_iff F k' F').2 fun c ↦ ?_
    rw [IsScalarTower.algebraMap_apply k' k'' F']
    exact algebraMap_mem_constantCompositum F k'' F' (algebraMap k' k'' c)
  exact ⟨hst, halg, h'', genus_le_genus_of_constantCompositum_eq_top hF h''⟩

/-- **Tate's genus-change theorem** (allowing constant growth): for any algebraic constant field
extension `F' = F · k'` of `F / k` in prime characteristic `p` and any algebraic enlargement
`k'' / k'` inside `F'` that is exact in `F'`, `p - 1` divides `2 (g(F / k) - g(F' / k''))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  obtain ⟨_, _, h'', -⟩ := genus_le_and_constantCompositum_eq_top_of_enlargement hF h (k'' := k'')
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn hF hex h'' hex''

/-- **Tate's genus-change theorem for `algebraicClosure k' F'`**: specialization requiring no
exactness hypothesis on `k'` in `F'`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top {p : ℕ}
    [Fact p.Prime] [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    (p - 1) ∣ 2 * (genus k F - genus (algebraicClosure k' F') F') :=
  sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))

/-- **Odd-characteristic Tate divisibility**: for an odd prime `p`, `(p - 1) / 2` divides the genus
drop `g(F / k) - g(F' / k'')` across any algebraic constant field extension `F' = F · k'` with
exact constant field `k''` in `F'`. -/
theorem half_sub_one_dvd_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] (hp2 : p ≠ 2) [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    ((p - 1) / 2) ∣ genus k F - genus k'' F' := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  refine (Nat.mul_dvd_mul_iff_left two_pos).1 ?_
  rw [h2]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''

/-- **Genus conservation in small genus**: in characteristic `p > 0`, if `2 g(F / k) < p - 1`, then
the genus is unchanged under every algebraic constant field extension `F' = F · k'`, even when new
constants `k''` appear. -/
theorem genus_eq_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : 2 * genus k F < p - 1)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  obtain ⟨_, _, -, hgle⟩ := genus_le_and_constantCompositum_eq_top_of_enlargement hF h (k'' := k'')
  have hdvd := sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''
  have hzero : 2 * (genus k F - genus k'' F') = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

/-- **Genus conservation in odd characteristic**: for `p ≠ 2`, if `g(F / k) < (p - 1) / 2`, then
`g(F' / k'') = g(F / k)` across every algebraic constant field extension `F' = F · k'`. -/
theorem genus_eq_genus_of_genus_lt_half_sub_one {p : ℕ} [Fact p.Prime] [CharP k p] (hp2 : p ≠ 2)
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : genus k F < (p - 1) / 2)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  exact genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h (by omega) hex''

/-- **Exactness of constants in small positive genus**: if `1 ≤ g(F / k)`, `2 g(F / k) < p - 1`,
and `[F' : F] = [k' : k]` for a finite constant field extension `F' = F · k'`, then `k'` remains
the exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime]
    [CharP k p] [FiniteDimensional k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hn : finrank F F' = finrank k k') (hg1 : 1 ≤ genus k F) (hlt : 2 * genus k F < p - 1) :
    IsIntegrallyClosedIn k' F' :=
  isIntegrallyClosedIn_of_one_le_genus_of_genus_eq hF hex h hn hg1
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))
    (genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h hlt
      (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F')))

end Tate

end TauCeti
