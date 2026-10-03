/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.TwoGeneratorQuotient
public import TauCeti.NumberTheory.LocalField.WorkedExamples.UnramifiedQuadratic
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Torsion
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.NumberTheory.Multiplicity

/-!
# Sharp exponents for a tame frame

Let `L/K` be an extension of fields with finite automorphism group `G = Aut_K(L)`, and suppose
that `L` has finitely many `p`-power roots of unity, forming the cyclic group `μ_{p^∞}(L)` of
order `q(L) = p^k`. Let `σ, τ` generate `G`, with `τ` of order prime to `p` (a *tame frame*, as
supplied by a Frobenius lift and a generator of tame inertia on a tamely ramified layer).

This file proves the existence of **sharp exponents** (the exact sequence `(∗)` in the proof of
NSW (7.4.1)): natural numbers `a, b` through which `σ, τ` act on `μ_{p^∞}(L)`, such that the
left ideal `J = ℤ_p[G]·(σ - a) + ℤ_p[G]·(τ - b)` is exactly the annihilator of `μ_{p^∞}(L)`. In
other words the left `ℤ_p[G]`-module `ℤ_p[G] ⧸ J` has order `q(L)`, and it is isomorphic to the
`p`-power torsion of the `p`-adic completion `A(L)` of `Lˣ`, which is `μ_{p^∞}(L)` with its Galois
action.

The exponents are sharp in that `b` is chosen so that `b ^ orderOf τ - 1` has `p`-adic valuation
exactly that of `q(L)`; this bounds `ℤ_p[G] ⧸ J`, a cyclic `ℤ_p`-module, by `q(L)`. Not every lift
works: for `a = b = 1` the quotient is `ℤ_p[G] ⧸ I_G ≅ ℤ_p`, which is infinite.

## Main statements

* `TauCeti.exists_tameFrame_exponents`: the existence of sharp exponents for a tame frame.
* `TauCeti.finite_and_natCard_le_of_pow_orderOf_sub_one`: `ℤ_p[G] ⧸ J` has at most `p ^ k`
  elements when `b ^ orderOf τ - 1` is `p ^ k` times a `p`-adic unit.
* `TauCeti.not_exists_tameFrame_exponents_one_one`: when `q(L) = 2` and the automorphism group is
  nontrivial, the identity pair cannot have sharp exponents.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- A finite group of `p`-power roots of unity has order `p ^ k`, and a generator: every element
is a natural power of it. -/
private theorem exists_generator_pPowerRootsOfUnity (L : Type*) [Field L]
    (h : Finite (pPowerRootsOfUnity p L)) :
    ∃ ζ ∈ pPowerRootsOfUnity p L, IsPrimitiveRoot ζ (localRootOfUnityOrder p L h) ∧
      ∀ ξ ∈ pPowerRootsOfUnity p L, ∃ j : ℕ, ζ ^ j = ξ := by
  have := isCyclic_pPowerRootsOfUnity p L h
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := pPowerRootsOfUnity p L)
  have hprim : IsPrimitiveRoot (ζ : Lˣ) (localRootOfUnityOrder p L h) := by
    rw [localRootOfUnityOrder_def, ← hζ, ← Subgroup.orderOf_coe]
    exact IsPrimitiveRoot.orderOf _
  refine ⟨ζ, ζ.2, hprim, fun ξ hξ ↦ ?_⟩
  rw [pPowerRootsOfUnity_eq_rootsOfUnity_order p L h] at hξ
  have : NeZero (localRootOfUnityOrder p L h) := ⟨(localRootOfUnityOrder_pos p L h).ne'⟩
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_mem_rootsOfUnity hξ
  exact ⟨j, hj⟩

/-- A field automorphism acts on a finite group of `p`-power roots of unity as a power map, through
Mathlib's modular cyclotomic character. -/
private theorem exists_units_map_eq_pow {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L]
    (h : Finite (pPowerRootsOfUnity p L)) (g : L ≃ₐ[K] L) :
    ∃ c : ℕ, ∀ ξ ∈ pPowerRootsOfUnity p L, Units.map (g : L →* L) ξ = ξ ^ c := by
  have : NeZero (localRootOfUnityOrder p L h) := ⟨(localRootOfUnityOrder_pos p L h).ne'⟩
  refine ⟨(modularCyclotomicCharacter.toFun (localRootOfUnityOrder p L h)
    (g : L ≃+* L)).val, fun ξ hξ ↦ Units.ext ?_⟩
  rw [pPowerRootsOfUnity_eq_rootsOfUnity_order p L h] at hξ
  simpa using modularCyclotomicCharacter.toFun_spec' (g : L ≃+* L) hξ

/-- If `σ, τ` generate the monoid `G` and `b ^ orderOf τ - 1 = p ^ k * c` with `c` a unit of
`ℤ_p`, then `ℤ_p[G] ⧸ ℤ_p[G]·(σ - a, τ - b)` is finite with at most `p ^ k` elements: it is a
cyclic `ℤ_p`-module killed by `p ^ k`. -/
theorem finite_and_natCard_le_of_pow_orderOf_sub_one {G : Type*} [Monoid G]
    {σ τ : G} (hgen : Submonoid.closure {σ, τ} = ⊤) {a b c : ℤ_[p]} {k : ℕ} (hc : IsUnit c)
    (hbc : b ^ orderOf τ - 1 = (p : ℤ_[p]) ^ k * c) :
    Finite (MonoidAlgebra ℤ_[p] G ⧸
        Ideal.span {single σ (1 : ℤ_[p]) - single 1 a, single τ 1 - single 1 b}) ∧
      Nat.card (MonoidAlgebra ℤ_[p] G ⧸
        Ideal.span {single σ (1 : ℤ_[p]) - single 1 a, single τ 1 - single 1 b}) ≤ p ^ k := by
  have hp : p.Prime := Fact.out
  have hkill (y : MonoidAlgebra ℤ_[p] G ⧸
      Ideal.span {single σ (1 : ℤ_[p]) - single 1 a, single τ 1 - single 1 b}) :
      ((p : ℤ_[p]) ^ k) • y = 0 := by
    have hy := MonoidAlgebra.pow_orderOf_sub_one_smul_eq_zero_of_sub_mem (g := τ) (c := b)
      (Ideal.subset_span (by simp)) y
    obtain ⟨u, rfl⟩ := hc
    rwa [hbc, mul_comm, mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hy
  -- The class of `r • 1` only depends on the residue of `r` modulo `p ^ k`.
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hsurj : Function.Surjective fun z : ZMod (p ^ k) ↦ (z.val : ℤ_[p]) •
      (Submodule.Quotient.mk 1 : MonoidAlgebra ℤ_[p] G ⧸
        Ideal.span {single σ (1 : ℤ_[p]) - single 1 a, single τ 1 - single 1 b}) := by
    intro y
    obtain ⟨r, rfl⟩ := MonoidAlgebra.toSpanSingleton_mk_one_surjective hgen y
    refine ⟨PadicInt.toZModPow k r, ?_⟩
    have hmem : ((PadicInt.toZModPow k r).val : ℤ_[p]) - r ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ZMod.natCast_zmod_val, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    dsimp only
    rw [LinearMap.toSpanSingleton_apply,
      ← sub_add_cancel ((PadicInt.toZModPow k r).val : ℤ_[p]) r, ← hs, add_smul, mul_smul, hkill,
      smul_zero, zero_add]
  exact ⟨Finite.of_surjective _ hsurj,
    (Nat.card_le_card_of_surjective _ hsurj).trans (Nat.card_zmod _).le⟩

/-- If `ζ` generates the `p`-power roots of unity of `L` and `σ, τ` act on them through `a, b`, then
`ℤ_p[G] ⧸ ℤ_p[G]·(σ - a, τ - b)` maps onto the `p`-power torsion of `A(L)`, sending the class of
`x` to `x` applied to the class of `ζ`. -/
private theorem exists_surjective_pPowerTorsion_padicCompletionUnits {L : Type*} [Field L]
    {K : Type*} [Field K] [Algebra K L] {ζ : Lˣ} (hζμ : ζ ∈ pPowerRootsOfUnity p L)
    (hgenζ : ∀ ξ ∈ pPowerRootsOfUnity p L, ∃ j : ℕ, ζ ^ j = ξ) {σ τ : L ≃ₐ[K] L} {a b : ℕ}
    (ha : Units.map (σ : L →* L) ζ = ζ ^ a) (hb : Units.map (τ : L →* L) ζ = ζ ^ b) :
    ∃ φ : (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸
        Ideal.span {single σ (1 : ℤ_[p]) - single 1 (a : ℤ_[p]), single τ 1 - single 1 (b : ℤ_[p])})
        →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
        pPowerTorsion p (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)),
      Function.Surjective φ := by
  have ht₀ : Additive.ofMul (padicCompletionUnitsOf p L ζ) ∈
      pPowerTorsion p (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)) := by
    obtain ⟨n, hn⟩ := (mem_pPowerRootsOfUnity_iff p L ζ).mp hζμ
    refine mem_pPowerTorsion_iff.mpr ⟨n, Additive.toMul.injective ?_⟩
    rw [toMul_nsmul, toMul_ofMul, ← map_pow, hn, map_one, toMul_zero]
  -- The generators `g - e` of the ideal kill the class of `ζ`. The explicit arguments of
  -- `sub_smul` make the additive group structure of `A(L)` be synthesized before it is unified
  -- with the additive monoid structure underlying its module structure.
  have hker (g : L ≃ₐ[K] L) (e : ℕ) (hg : Units.map (g : L →* L) ζ = ζ ^ e) :
      single g (1 : ℤ_[p]) - single 1 (e : ℤ_[p]) ∈ LinearMap.ker
        (LinearMap.toSpanSingleton (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) _
          (Additive.ofMul (padicCompletionUnitsOf p L ζ))) := by
    have hg' : Units.map g.toRingEquiv.toMonoidHom ζ = ζ ^ e := by
      rw [← hg]
      ext
      simp
    refine LinearMap.mem_ker.mpr <| (sub_smul (single g (1 : ℤ_[p])) (single 1 (e : ℤ_[p]))
      (Additive.ofMul (padicCompletionUnitsOf p L ζ))).trans (sub_eq_zero.mpr ?_)
    rw [padicCompletionUnits_single_smul, padicCompletionUnits_single_smul, ← Nat.cast_one,
      padicCompletionUnits_natCast_smul, padicCompletionUnits_natCast_smul, one_nsmul,
      padicCompletionUnitsAut_of, hg', map_one, MulAut.one_apply, map_pow, ofMul_pow]
  have hJle : Ideal.span {single σ (1 : ℤ_[p]) - single 1 (a : ℤ_[p]),
      single τ 1 - single 1 (b : ℤ_[p])} ≤ LinearMap.ker (LinearMap.toSpanSingleton
        (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) _ (Additive.ofMul (padicCompletionUnitsOf p L ζ))) := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hker σ a ha, hker τ b hb⟩
  -- As above, `M₂` is given explicitly to fix the additive group structure of `A(L)`.
  let φ₀ := Submodule.liftQ (M₂ := Additive ↑(padicCompletionUnits p L)) _ _ hJle
  have hφ₀ (y : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) :
      φ₀ (Submodule.Quotient.mk y) = y • Additive.ofMul (padicCompletionUnitsOf p L ζ) :=
    rfl
  have hφ₀mem (y) : φ₀ y ∈ pPowerTorsion p (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)) := by
    induction y using Submodule.Quotient.induction_on with
    | H y => rw [hφ₀]; exact Submodule.smul_mem _ y ht₀
  refine ⟨φ₀.codRestrict _ hφ₀mem, fun x ↦ ?_⟩
  -- Every torsion element is the class of a power `ζ ^ j`, the image of the class of `j`.
  have hx := (mem_pPowerTorsion_padicCompletionUnits_iff p L x.1).mp x.2
  rw [torsion_padicCompletionUnits] at hx
  obtain ⟨ξ, hξ, hξx⟩ := hx
  obtain ⟨j, rfl⟩ := hgenζ ξ hξ
  refine ⟨Submodule.Quotient.mk (j : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)),
    Subtype.ext (Additive.toMul.injective ?_)⟩
  rw [LinearMap.codRestrict_apply, hφ₀, Nat.cast_smul_eq_nsmul, toMul_nsmul, toMul_ofMul, ← hξx,
    map_pow]

/-- **Sharp exponents for a tame frame** (the exact sequence `(∗)` in the proof of NSW (7.4.1)).
Let `σ, τ` generate the finite automorphism group `G` of `L/K`, with `τ` of order prime to `p`, and
suppose `L` has finitely many `p`-power roots of unity. Then there are natural numbers `a, b`
through which `σ, τ` act on `μ_{p^∞}(L)` such that the left ideal `J = (σ - a, τ - b)` of
`ℤ_p[G]` is the annihilator of `μ_{p^∞}(L)`: the quotient `ℤ_p[G] ⧸ J` has order
`q(L) = #μ_{p^∞}(L)`, and it is isomorphic as a left `ℤ_p[G]`-module to the `p`-power torsion of
the `p`-adic completion `A(L)` of `Lˣ`, which is `μ_{p^∞}(L)` with its Galois action.

Generation is needed: when `σ, τ` generate a proper subgroup `H` of `G` and `q(L) > 1`, the
quotient has order at least `q(L) ^ [G : H]`. -/
theorem exists_tameFrame_exponents {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (h : Finite (pPowerRootsOfUnity p L)) (σ τ : L ≃ₐ[K] L)
    (hgen : Subgroup.closure {σ, τ} = ⊤) (hτ : ¬ p ∣ orderOf τ) :
    ∃ a b : ℕ,
      (∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (σ : L →* L) ζ = ζ ^ a) ∧
      (∀ ζ ∈ pPowerRootsOfUnity p L, Units.map (τ : L →* L) ζ = ζ ^ b) ∧
      Nat.card (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸ Ideal.span
        {single σ (1 : ℤ_[p]) - a, single τ (1 : ℤ_[p]) - b}) = localRootOfUnityOrder p L h ∧
      Nonempty ((MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L) ⧸ Ideal.span
          {single σ (1 : ℤ_[p]) - a, single τ (1 : ℤ_[p]) - b})
        ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
        pPowerTorsion p (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
          (Additive ↑(padicCompletionUnits p L))) := by
  obtain ⟨k, hk⟩ := localRootOfUnityOrder_isPow p L h
  obtain ⟨ζ, hζμ, hζ, hgenζ⟩ := exists_generator_pPowerRootsOfUnity L h
  rw [hk] at hζ
  -- Exponents `a, b₀` through which `σ, τ` act, with `b₀ ^ orderOf τ ≡ 1 (mod q(L))`.
  obtain ⟨a, ha⟩ := exists_units_map_eq_pow h σ
  obtain ⟨b₀, hb₀⟩ := exists_units_map_eq_pow h τ
  have hτpow (m : ℕ) : Units.map ((τ ^ m : L ≃ₐ[K] L) : L →* L) ζ = ζ ^ (b₀ ^ m) := by
    induction m with
    | zero => ext; simp
    | succ m ih =>
      have hmap : Units.map ((τ ^ (m + 1) : L ≃ₐ[K] L) : L →* L) ζ =
          Units.map ((τ ^ m : L ≃ₐ[K] L) : L →* L) (Units.map (τ : L →* L) ζ) := by
        ext; simp [pow_succ, AlgEquiv.mul_apply]
      rw [hmap, hb₀ ζ hζμ, map_pow, ih, ← pow_mul, pow_succ, mul_comm]
  have hb₀n : b₀ ^ orderOf τ ≡ 1 [MOD p ^ k] := by
    rw [hζ.eq_orderOf, ← pow_eq_pow_iff_modEq, pow_one, ← hτpow, pow_orderOf_eq_one]
    ext; simp
  -- Move `b₀` so that `b ^ orderOf τ - 1 = p ^ k * c` with `c` a `p`-adic unit.
  obtain ⟨b, hbb₀, c, hc, hcp⟩ := exists_modEq_pow_sub_one_eq_mul hτ hb₀n
  have hb (ξ : Lˣ) (hξ : ξ ∈ pPowerRootsOfUnity p L) : Units.map (τ : L →* L) ξ = ξ ^ b := by
    rw [hb₀ ξ hξ]
    refine pow_eq_pow_of_modEq hbb₀.symm ?_
    rwa [pPowerRootsOfUnity_eq_rootsOfUnity_order p L h, hk] at hξ
  refine ⟨a, b, ha, hb, ?_⟩
  simp only [natCast_def]
  have hcu : IsUnit (c : ℤ_[p]) := PadicInt.isUnit_iff.mpr <| (PadicInt.norm_le_one _).antisymm <|
    not_lt.mp fun hlt ↦ hcp ((PadicInt.norm_int_lt_one_iff_dvd c).mp hlt)
  have hbc : (b : ℤ_[p]) ^ orderOf τ - 1 = (p : ℤ_[p]) ^ k * c := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) hc
  -- The quotient has at most `q(L)` elements and maps onto the torsion of `A(L)`, which has
  -- exactly `q(L)` elements.
  obtain ⟨_, hcardle⟩ := finite_and_natCard_le_of_pow_orderOf_sub_one (a := (a : ℤ_[p]))
    (by rw [← Subgroup.closure_toSubmonoid_of_finite, hgen, Subgroup.top_toSubmonoid]) hcu hbc
  obtain ⟨φ, hφ⟩ := exists_surjective_pPowerTorsion_padicCompletionUnits hζμ hgenζ
    (ha ζ hζμ) (hb ζ hζμ)
  have hcardT := natCard_pPowerTorsion_padicCompletionUnits p L
    (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) h
  have hbij := hφ.bijective_of_nat_card_le (hcardle.trans (hcardT.trans hk).ge)
  exact ⟨(Nat.card_eq_of_bijective φ hbij).trans hcardT, ⟨LinearEquiv.ofBijective φ hbij⟩⟩

/-! ### The generating hypothesis is necessary -/

/-- **The identity pair does not have sharp tame-frame exponents.** Suppose the finite group of
`2`-power roots of unity of `L` has order two and `Aut_K(L)` is finite and nontrivial. There are
no exponents through which the identity pair acts on those roots for which the corresponding
two-generator quotient of `ℤ_2[Aut_K(L)]` also has order two.

Indeed, the action equations on `-1` force both exponents to be odd. Reduction modulo two then
makes both relations vanish, so the quotient surjects onto `𝔽₂[Aut_K(L)]`, which has at least
four elements. This shows that the generating hypothesis of `exists_tameFrame_exponents` cannot
be omitted. -/
theorem not_exists_tameFrame_exponents_one_one (L : Type*) [Field L]
    (K : Type*) [Field K] [Algebra K L] [Finite (L ≃ₐ[K] L)] [Nontrivial (L ≃ₐ[K] L)]
    (hchar : (2 : L) ≠ 0) (hfinite : Finite (pPowerRootsOfUnity 2 L))
    (hq : localRootOfUnityOrder 2 L hfinite = 2) :
    ¬ ∃ a b : ℕ,
      (∀ ζ ∈ pPowerRootsOfUnity 2 L, Units.map ((1 : L ≃ₐ[K] L) : L →* L) ζ = ζ ^ a) ∧
      (∀ ζ ∈ pPowerRootsOfUnity 2 L, Units.map ((1 : L ≃ₐ[K] L) : L →* L) ζ = ζ ^ b) ∧
      Nat.card (MonoidAlgebra ℤ_[2] (L ≃ₐ[K] L) ⧸ Ideal.span
        {single (1 : L ≃ₐ[K] L) (1 : ℤ_[2]) - a,
          single (1 : L ≃ₐ[K] L) (1 : ℤ_[2]) - b}) = localRootOfUnityOrder 2 L hfinite := by
  classical
  rintro ⟨a, b, ha, hb, hcard⟩
  have hneg : (-1 : Lˣ) ∈ pPowerRootsOfUnity 2 L :=
    (mem_pPowerRootsOfUnity_iff 2 L _).2 ⟨1, by norm_num⟩
  have hne : (-1 : Lˣ) ≠ 1 := by
    intro h
    have hval := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at hval
    have htwo := congrArg (fun x : L ↦ x + 1) hval
    norm_num at htwo
    exact hchar htwo.symm
  have exponent_odd {n : ℕ}
      (hn : ∀ ζ ∈ pPowerRootsOfUnity 2 L,
        Units.map ((1 : L ≃ₐ[K] L) : L →* L) ζ = ζ ^ n) : Odd n :=
    (neg_one_pow_eq_neg_one_iff_odd (R := Lˣ) hne).1 <| by
      simpa using (hn (-1) hneg).symm
  have haodd : Odd a := exponent_odd ha
  have hbodd : Odd b := exponent_odd hb
  exact MonoidAlgebra.natCard_quotient_span_one_sub_natCast_ne_two haodd hbodd
    (hcard.trans hq)

/-- The identity pair on the unramified quadratic extension `ℚ₂(ζ₃)/ℚ₂` does not admit sharp
tame-frame exponents. This is the concrete rejection test showing that the generating hypothesis
of `exists_tameFrame_exponents` cannot be removed. -/
theorem not_exists_tameFrame_exponents_one_one_unramifiedQuadratic :
    ¬ ∃ a b : ℕ,
      (∀ ζ ∈ pPowerRootsOfUnity 2 UnramifiedQuadratic,
        Units.map ((1 : UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) :
          UnramifiedQuadratic →* UnramifiedQuadratic) ζ = ζ ^ a) ∧
      (∀ ζ ∈ pPowerRootsOfUnity 2 UnramifiedQuadratic,
        Units.map ((1 : UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) :
          UnramifiedQuadratic →* UnramifiedQuadratic) ζ = ζ ^ b) ∧
      Nat.card (MonoidAlgebra ℤ_[2]
        (UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) ⧸ Ideal.span
          {single (1 : UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) (1 : ℤ_[2]) - a,
            single (1 : UnramifiedQuadratic ≃ₐ[ℚ_[2]] UnramifiedQuadratic) (1 : ℤ_[2]) - b}) =
        localRootOfUnityOrder 2 UnramifiedQuadratic
          (finite_pPowerRootsOfUnity (by norm_num)) := by
  let _ := nontrivial_algEquiv_unramifiedQuadratic
  exact not_exists_tameFrame_exponents_one_one UnramifiedQuadratic ℚ_[2] (by norm_num)
    (finite_pPowerRootsOfUnity (by norm_num)) localRootOfUnityOrder_two_unramifiedQuadratic

end TauCeti
