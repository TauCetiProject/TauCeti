/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
import TauCeti.NumberTheory.LocalField.Kummer
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Local cohomology with trivial `ℤ/n` coefficients, by duality

Let `K` be a nonarchimedean local field and `n` a natural number invertible in `K`. Local Tate
duality for the trivial module `ℤ/n` computes its cohomology without a primitive `n`th root of
unity in `K`; its dual is `Hom(ℤ/n, μₙ) = μₙ`.

* In degree two, `H²(G_K, ℤ/n)` is dual to `H⁰(G_K, μₙ) = μₙ(K)`, so it is finite and vanishes
  when `K` has no `n`th root of unity other than `1`.
* In degree one, `H¹(G_K, ℤ/n)` is dual to `H¹(G_K, μₙ)`, which Kummer theory identifies with
  `Kˣ/(Kˣ)ⁿ`; so the two have the same order.

For a prime `p` and a finite compatible extension `K` of `ℚ_[p]`, combining both cases gives
`dim H²(G_K, 𝔽_p)` (`1` when `μ_p ⊆ K` and `0` when `μ_p ⊄ K`) and the Euler-characteristic
identity `dim H¹(G_K, 𝔽_p) = 1 + dim H²(G_K, 𝔽_p) + [K : ℚ_[p]]`. When `K` does not contain a
primitive `p`th root of unity, these are the inputs to the freeness of the maximal pro-`p`
quotient of `G_K` and to its generator rank.

## Main results

* `TauCeti.finite_cohomFp_two_absoluteGaloisGroup`: `H²(G_K, ℤ/n)` is finite when `n` is
  invertible in `K`.
* `TauCeti.ClassFieldTheory.subsingleton_cohomFp_two_absoluteGaloisGroup`: `H²(G_K, ℤ/n)` vanishes
  when `μₙ(K)` is trivial.
* `TauCeti.ClassFieldTheory.natCard_cohomFp_one_absoluteGaloisGroup`: `H¹(G_K, ℤ/n)` has as many
  elements as `Kˣ/(Kˣ)ⁿ`.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_not_mu`: away from the residue
  characteristic, `H¹(G_K, 𝔽_p)` has dimension one when `K` does not contain `μ_p`.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroup_le_two_of_coprime_ringChar`: away from the
  residue characteristic, `H¹(G_K, 𝔽_p)` has dimension at most two.
* `TauCeti.subsingleton_cohomFp_two_absoluteGaloisGroup_of_not_mu` and
  `TauCeti.finrank_cohomFp_two_absoluteGaloisGroup_of_not_mu`: `H²(G_K, 𝔽_p) = 0` for a prime `p`
  when `K` contains no primitive `p`th root of unity.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroup_of_not_mu`: `dim H¹(G_K, 𝔽_p) = [K : ℚ_[p]] + 1`
  for a finite compatible extension `K` of `ℚ_[p]` containing no primitive `p`th root of unity.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroup`: the Euler-characteristic identity
  `dim H¹(G_K, 𝔽_p) = 1 + dim H²(G_K, 𝔽_p) + [K : ℚ_[p]]` for a finite compatible extension `K`
  of `ℚ_[p]`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2, and §5.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6) and
  (7.3.9).
-/

public section

open ValuativeRel

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {K : Type} [Field K] {n : ℕ}

attribute [local instance] trivialZModAction

/-- An invariant homomorphism `ℤ/n → μₙ` takes `1` to a Galois-fixed `n`th root of unity of `Kˢ`,
that is to an `n`th root of unity of `K`. So `H⁰(G_K, Hom(ℤ/n, μₙ))` vanishes when `μₙ(K)` is
trivial. -/
private theorem eq_zero_of_mem_H0_internalHom_kummerCoeff (h : rootsOfUnity n K = ⊥)
    (φ : H0 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) (ZMod n) (KummerCoeff K n))) :
    φ = 0 := by
  set y := φ.1.toAddMonoidHom 1 with hy
  -- `y = φ 1` is fixed by `G_K`, so it is the image of some `a : K`
  have hfix (g : AbsoluteGaloisGroup K) : g • y = y :=
    (InternalHom.smul_eq_self_iff.1 (φ.2 g) 1).symm
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    ((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)).2 fun g ↦ by
      simpa using congrArg (fun v : KummerCoeff K n ↦
        ((v.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) (hfix g)
  -- `a` is an `n`th root of unity of `K`, hence `1`
  have hpow : a ^ n = 1 := (algebraMap K (SeparableClosure K)).injective (by
    rw [map_pow, ha, RingHom.map_one, ← Units.val_pow_eq_pow_val, (y.toMul).2, Units.val_one])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact (y.toMul : (SeparableClosure K)ˣ).ne_zero (by rw [← ha, map_zero])
  have ha1 : Units.mk0 a ha0 = 1 := by
    rw [← Subgroup.mem_bot, ← h, mem_rootsOfUnity]
    exact Units.ext (by simp [hpow])
  have hy0 : y = 0 := Additive.toMul.injective (Subtype.ext (Units.ext (by
    rw [← ha, ← Units.val_mk0 ha0, ha1]; simp)))
  -- a homomorphism out of `ℤ/n` vanishing at `1` vanishes
  ext x
  rw [← ZMod.intCast_zmod_cast x, ← zsmul_one, map_zsmul, ← hy, hy0, smul_zero]
  rfl

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`H²(G_K, ℤ/n)` vanishes when `K` has no nontrivial `n`th root of unity**, for a
nonarchimedean local field `K` in which `n` is invertible. By local Tate duality it is dual to
`H⁰(G_K, Hom(ℤ/n, μₙ))`, the `n`th roots of unity of `K`. -/
theorem subsingleton_cohomFp_two_absoluteGaloisGroup (hn : IsUnit (n : K))
    (h : rootsOfUnity n K = ⊥) : Subsingleton (cohomFp n (Field.absoluteGaloisGroup K) 2) := by
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  have : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n) := ⟨continuous_snd⟩
  have : LocallyCompactSpace (AbsoluteGaloisGroup K) :=
    (absoluteGaloisGroupRestrictEquiv K).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have hinj := (dualityMap2_kummerCoeff_bijective hn (ZMod n) fun _ ↦ by simp).injective
  have : Subsingleton (H2 (AbsoluteGaloisGroup K) (ZMod n)) :=
    ⟨fun x y ↦ hinj (AddMonoidHom.ext fun φ ↦ by
      rw [eq_zero_of_mem_H0_internalHom_kummerCoeff h φ, map_zero, map_zero])⟩
  exact ((cohomFpLinearEquiv n (absoluteGaloisGroupRestrictEquiv K) 2).toAddEquiv.trans
    (cohomFpAddEquivH2 n _ fun _ _ ↦ rfl)).subsingleton

/-- **`H¹(G_K, ℤ/n)` has as many elements as `Kˣ/(Kˣ)ⁿ`**, for a nonarchimedean local field `K`
in which `n` is invertible. By local Tate duality `H¹(G_K, ℤ/n)` is the group of homomorphisms
from `H¹(G_K, Hom(ℤ/n, μₙ)) = H¹(G_K, μₙ)` to `H²(G_K, μₙ) ≃ ℤ/n`, and Kummer theory identifies
`H¹(G_K, μₙ)` with `Kˣ/(Kˣ)ⁿ`, a finite group killed by `n`. No root of unity in `K` is needed. -/
theorem natCard_cohomFp_one_absoluteGaloisGroup (hn : IsUnit (n : K)) :
    Nat.card (cohomFp n (Field.absoluteGaloisGroup K) 1) =
      Nat.card (powerClassQuotient Kˣ n) := by
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast K
  have : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n) := ⟨continuous_snd⟩
  have : LocallyCompactSpace (AbsoluteGaloisGroup K) :=
    (absoluteGaloisGroupRestrictEquiv K).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have : (powerSubgroup Kˣ n).FiniteIndex := by
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact finiteIndex_range_powMonoidHom (NeZero.ne (n : K))
  have : Finite (powerClassQuotient Kˣ n) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Module (ZMod n) (KummerCoeff K n) := AddCommGroup.zmodModule fun x ↦
    Additive.toMul.injective (Subtype.ext (by simp))
  -- `H¹(G_K, Hom(ℤ/n, μₙ))` is `H¹(G_K, μₙ)`, which Kummer theory identifies with `Kˣ/(Kˣ)ⁿ`
  let e₁ : H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) (ZMod n) (KummerCoeff K n)) ≃+
      Additive (powerClassQuotient Kˣ n) :=
    (explicitCoeff1Equiv _ _ (InternalHom.zmodEquiv (AbsoluteGaloisGroup K))
      continuous_of_discreteTopology continuous_of_discreteTopology
      (InternalHom.zmodEquiv_smul fun _ _ ↦ rfl)).trans
      (MulEquiv.toAdditiveLeft (kummerIso K n hn)).symm
  let e₂ : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n) ≃+ ZMod n :=
    (muNRepH2Equiv n K).trans (h2MuEquivZMod K hn)
  rw [Nat.card_congr ((cohomFpLinearEquiv n (absoluteGaloisGroupRestrictEquiv K) 1).toAddEquiv.trans
      (cohomFpAddEquivH1 n _ fun _ _ ↦ rfl)).toEquiv,
    Nat.card_congr (Equiv.ofBijective _ (dualityMap1_kummerCoeff_bijective hn (ZMod n)
      fun _ ↦ by simp)),
    Nat.card_congr (AddEquiv.addMonoidHomCongrLeft e₁).toEquiv, e₂.natCard_addMonoidHom_zmod,
    Nat.card_congr Additive.toMul]
  -- `Kˣ/(Kˣ)ⁿ` is killed by `n`
  refine fun x ↦ Additive.toMul.injective ?_
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.toMul
  rw [toMul_nsmul, ← hg, ← QuotientGroup.mk_pow, toMul_zero, QuotientGroup.eq_one_iff]
  exact (mem_powerSubgroup_iff n).2 ⟨g, rfl⟩

end TauCeti.ClassFieldTheory

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [Fact p.Prime] in
/-- Degree-two absolute Galois cohomology with trivial `ℤ/p` coefficients is finite when
`p` is nonzero in the local field, even when `p` is not prime. At prime `p`, this also supplies
its finite-dimensionality over `𝔽_p`. -/
instance finite_cohomFp_two_absoluteGaloisGroup [NeZero (p : K)] :
    Finite (cohomFp p (Field.absoluteGaloisGroup K) 2) := by
  have : NeZero p := ⟨fun h ↦ NeZero.ne (p : K) (by simp [h])⟩
  exact ClassFieldTheory.finite_H (NeZero.ne (p : K))
    (trivialFp p (Field.absoluteGaloisGroup K))
    (isSmoothDiscrete_trivialFp p (Field.absoluteGaloisGroup K)) le_rfl

/-- **`H²(G_K, 𝔽_p)` vanishes** for a nonarchimedean local field `K` containing no primitive `p`th
root of unity, `p` being invertible in `K`: by local duality it is dual to `μ_p(K) = 1`. -/
theorem subsingleton_cohomFp_two_absoluteGaloisGroup_of_not_mu [NeZero (p : K)]
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Subsingleton (cohomFp p (Field.absoluteGaloisGroup K) 2) :=
  ClassFieldTheory.subsingleton_cohomFp_two_absoluteGaloisGroup (NeZero.ne (p : K)).isUnit
    (rootsOfUnity_eq_bot_iff.2 hmu)

/-- If a nonarchimedean local field `K` contains no primitive `p`th root of unity, with `p`
invertible in `K`, then `dim H²(G_K, 𝔽_p) = 0`. -/
theorem finrank_cohomFp_two_absoluteGaloisGroup_of_not_mu [NeZero (p : K)]
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 2) = 0 := by
  have := subsingleton_cohomFp_two_absoluteGaloisGroup_of_not_mu p K hmu
  exact Module.finrank_zero_of_subsingleton

/-- **Away from the residue characteristic, `H¹(G_K, 𝔽_p)` has dimension one when
`μ_p ⊄ K`.** This follows from local duality and Kummer theory: `H¹(G_K, 𝔽_p)` has as many
elements as `Kˣ/(Kˣ)^p`, whose order is `p` when `K` has no nontrivial `p`th root of unity. -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_not_mu
    (hpK : IsUnit ((p : ℕ) : 𝒪[K])) (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) = 1 := by
  have : NeZero (p : K) := ⟨natCast_ne_zero_of_isUnit hpK⟩
  have hcard := ClassFieldTheory.natCard_cohomFp_one_absoluteGaloisGroup
    (NeZero.ne (p : K)).isUnit
  rw [powerClassQuotient, powerSubgroup_eq_range_powMonoidHom,
    card_powerClasses_of_isUnit hpK, rootsOfUnity_eq_bot_iff.2 hmu, Subgroup.card_bot,
    mul_one] at hcard
  have hfin := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := cohomFp p (Field.absoluteGaloisGroup K) 1)
  rw [Nat.card_zmod, hcard] at hfin
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (by simpa using hfin.symm)

/-- **Away from the residue characteristic, `H¹(G_K, 𝔽_p)` has dimension at most two.** -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_le_two_of_isUnit
    (hpK : IsUnit ((p : ℕ) : 𝒪[K])) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) ≤ 2 := by
  by_cases hmu : ∃ ζ : K, IsPrimitiveRoot ζ p
  · rw [finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_exists_isPrimitiveRoot p K hpK hmu]
  · rw [finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_not_mu p K hpK hmu]
    omega

/-- **Degree-one local Galois cohomology has dimension at most two at every prime different from
the residue characteristic.** -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_le_two_of_coprime_ringChar
    (hp : p.Coprime (ringChar 𝓀[K])) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) ≤ 2 :=
  finrank_cohomFp_one_absoluteGaloisGroup_le_two_of_isUnit p K
    (IsLocalRing.isUnit_natCast_iff_not_dvd.2
      ((CharP.prime_ringChar 𝓀[K]).coprime_iff_not_dvd.mp hp.symm))

/-- **Away from the residue characteristic, the Euler-characteristic identity for trivial `𝔽_p`
coefficients holds**: `dim H¹(G_K, 𝔽_p) = 1 + dim H²(G_K, 𝔽_p)`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit
    (hpK : IsUnit ((p : ℕ) : 𝒪[K])) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) =
      1 + Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 2) := by
  have : NeZero (p : K) := ⟨natCast_ne_zero_of_isUnit hpK⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases hmu : ∃ ζ : K, IsPrimitiveRoot ζ p
  · obtain ⟨ζ, hζ⟩ := hmu
    rw [finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_exists_isPrimitiveRoot p K hpK
      ⟨ζ, hζ⟩, ClassFieldTheory.finrank_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot hζ]
  · rw [finrank_cohomFp_one_absoluteGaloisGroup_of_isUnit_of_not_mu p K hpK hmu,
      finrank_cohomFp_two_absoluteGaloisGroup_of_not_mu p K hmu, add_zero]

/-- If a finite compatible extension `K` of `ℚ_[p]` contains no primitive `p`th root of unity,
then `dim H¹(G_K, 𝔽_p) = [K : ℚ_[p]] + 1`: by local duality and Kummer theory `H¹(G_K, 𝔽_p)` has
as many elements as `Kˣ/(Kˣ)^p`, that is `p · #μ_p(K) · p ^ [K : ℚ_[p]]` with `μ_p(K) = 1`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_of_not_mu
    [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) =
      Module.finrank ℚ_[p] K + 1 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  have hcard := ClassFieldTheory.natCard_cohomFp_one_absoluteGaloisGroup
    (NeZero.ne (p : K)).isUnit
  rw [natCard_powerClassQuotient_eq_mul_pow_finrank, rootsOfUnity_eq_bot_iff.2 hmu,
    Subgroup.card_bot, mul_one] at hcard
  have hfin := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := cohomFp p (Field.absoluteGaloisGroup K) 1)
  rw [Nat.card_zmod, hcard] at hfin
  refine Nat.pow_right_injective (Fact.out : p.Prime).two_le ?_
  dsimp only
  rw [← hfin]
  ring

/-- **The Euler-characteristic identity for trivial `𝔽_p` coefficients** over a finite compatible
extension `K` of `ℚ_[p]`: `dim H¹(G_K, 𝔽_p) = 1 + dim H²(G_K, 𝔽_p) + [K : ℚ_[p]]`. When `μ_p ⊆ K`,
`dim H² = 1` and `dim H¹ = [K : ℚ_[p]] + 2`; when `μ_p ⊄ K`, `dim H² = 0` and
`dim H¹ = [K : ℚ_[p]] + 1`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroup
    [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) =
      1 + Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 2) +
        Module.finrank ℚ_[p] K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases hmu : ∃ ζ : K, IsPrimitiveRoot ζ p
  · obtain ⟨ζ, hζ⟩ := hmu
    rw [finrank_cohomFp_one_absoluteGaloisGroup_of_exists_isPrimitiveRoot p K ⟨ζ, hζ⟩,
      ClassFieldTheory.finrank_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot hζ]
    omega
  · rw [finrank_cohomFp_one_absoluteGaloisGroup_of_not_mu p K hmu,
      finrank_cohomFp_two_absoluteGaloisGroup_of_not_mu p K hmu]
    omega

end TauCeti
