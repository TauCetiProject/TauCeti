/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Padic.IntegralComparison
public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Localization

import TauCeti.Data.Int.Shift
import TauCeti.NumberTheory.HeckeRing.Normalizer
import TauCeti.RingTheory.Localization.Away.Basic

/-!
# The rational `p`-adic `GL_n` Hecke ring comparison and central localization

Following Proposition 3.16 and Theorem 3.20 of [Shimura][shimura1971] together with
Rhodes–Shemanske (1998, §3.2) and [Rhodes–Shemanske][rhodes1999] (§2), this file completes
the local `p`-adic `GL_n` comparison diagram:

1. **Integral-to-rational `p`-adic inclusion**: widening `padicIntEntries n p` to `⊤` inside
   `GL_n(ℚ_p)` gives the injective degree-preserving ring homomorphism
   `padicIntegralToRationalRingHom n p R` (and over `ℤ`,
   `padicIntegralToRational n p : PadicIntegralHeckeRing n p →+* PadicRationalHeckeRing n p`),
   stated independently of the localization presentation. Any negative exponent takes
   `padicIntPowDiagElem n p e` outside its range (in particular `p⁻¹I` in positive rank `n ≠ 0`).
2. **Rational `p`-adic comparison**: extending `SL_n(ℤ)` to `GL_n(ℤ_p)` along
   `castGLPadic n p : GL_n(ℚ) →* GL_n(ℚ_p)` identifies `𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) R`
   with `𝕋 ⊤ (GLnZp n p) R`, and over `ℤ` yields the degree-preserving ring isomorphism
   `pLocalRationalToPadicRingEquiv n p : pLocalRationalSubring n p ≃+* PadicRationalHeckeRing n p`
   forming a commutative square with `integralToRationalLocal`, `pLocalToPadicIntegralRingEquiv`,
   and `padicIntegralToRational`.
3. **Central localization and Laurent presentation**: the central scalar operator
   `padicScalarIntElem n p = [GL_n(ℤ_p) · (pI) · GL_n(ℤ_p)]` maps to the two-sided unit
   `padicScalarUnit n p` with inverse `padicScalarInvElem n p = [GL_n(ℤ_p) · (p⁻¹I) · GL_n(ℤ_p)]`
   in `PadicRationalHeckeRing n p`, exhibiting `PadicRationalHeckeRing n p` as the localization of
   `PadicIntegralHeckeRing n p` away from `padicScalarIntElem n p` (`IsLocalization.Away`,
   `padicRationalHeckeRing_ringHom_ext`, `padicRationalHeckeRingLift`,
   `eq_padicRationalHeckeRingLift_iff`) and, for `n ≠ 0`, presenting it as
   `Localization.Away (MvPolynomial.X (Fin.rev 0))` (`padicLaurentPolynomialRingEquiv`).

## Main definitions

* `HeckeRing.GLn.padicIntegralToRationalRingHom`, `HeckeRing.GLn.padicIntegralToRational`: the
  injective inclusion of the integral `p`-adic Hecke ring into the rational `p`-adic Hecke ring.
* `HeckeRing.GLn.pLocalPosToPadicRationalCosetEquiv`,
  `HeckeRing.GLn.pLocalPosToPadicRationalRingEquiv`,
  `HeckeRing.GLn.pLocalRationalToPadicRingEquiv`: the rational `p`-adic double-coset bijection and
  Hecke ring isomorphisms.
* `HeckeRing.GLn.padicScalarIntElem`, `HeckeRing.GLn.padicScalarInvElem`,
  `HeckeRing.GLn.padicScalarUnit`, `HeckeRing.GLn.padicRationalHeckeRingLift`: the central `pI` and
  `p⁻¹I` operators, their bundled unit, and the universal-property lift out of
  `PadicRationalHeckeRing n p`.
* `HeckeRing.GLn.padicLaurentPolynomialRingEquiv`: the Laurent presentation
  `Localization.Away (MvPolynomial.X (Fin.rev 0)) ≃+* PadicRationalHeckeRing n p` for `n ≠ 0`.

## Main results

* `HeckeRing.GLn.padicIntPowDiagElem_notMem_range_padicIntegralToRational`,
  `HeckeRing.GLn.padicIntPowDiagElem_neg_one_notMem_range_padicIntegralToRational`: operators with
  a negative `p`-exponent lie outside the integral `p`-adic subring.
* `HeckeRing.GLn.multiplicity_GLnZp_castGLPadic_of_mem_pLocalPosGL`,
  `HeckeRing.GLn.pLocalRationalToPadicRingEquiv_integralToRationalLocal`,
  `HeckeRing.GLn.deg_pLocalRationalToPadicRingEquiv`: structure-constant equality, compatibility
  with the integral comparison, and preservation of `LeftCosetModule.deg`.
* `HeckeRing.GLn.padicIntegralToRational_padicScalarIntElem_mul_padicScalarInvElem`,
  `HeckeRing.GLn.isLocalization_away_padicScalarIntElem`,
  `HeckeRing.GLn.eq_padicRationalHeckeRingLift_iff`: central invertibility of `pI` and the
  universal property of `padicIntegralToRational n p`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16 and Theorem 3.20.
* J. A. Rhodes and T. R. Shemanske, *Bruhat–Tits buildings and Hecke operators*, 12 June 1998
  author manuscript, §3.2.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open Matrix Subgroup DoubleCoset

open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

attribute [local instance] commRingPadicIntegralHeckeRing commRingPadicRationalHeckeRing
  commRingRationalHeckeRing

section PadicInclusion

/-- **Integral-to-rational `p`-adic Hecke ring embedding**: enlarging `padicIntEntries n p` to `⊤`
inside `GL_n(ℚ_p)` embeds `𝕋 (padicIntEntries n p) (GLnZp n p) R` injectively into
`𝕋 ⊤ (GLnZp n p) R` over any coefficient semiring `R`. -/
noncomputable def padicIntegralToRationalRingHom (R : Type*) [Semiring R] :
    𝕋 (padicIntEntries n p) (GLnZp n p) R →+*
      𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R :=
  HeckeCosetModule.mapSubmonoidRingHom R le_top

/-- `padicIntegralToRationalRingHom` coerces to `HeckeCosetModule.mapSubmonoid`. -/
theorem coe_padicIntegralToRationalRingHom (R : Type*) [Semiring R] :
    ⇑(padicIntegralToRationalRingHom n p R) =
      HeckeCosetModule.mapSubmonoid (H₁ := GLnZp n p) (H₂ := GLnZp n p) R le_top :=
  HeckeCosetModule.coe_mapSubmonoidRingHom R le_top

/-- The integral-to-rational `p`-adic Hecke ring inclusion over `ℤ`. -/
noncomputable abbrev padicIntegralToRational :
    PadicIntegralHeckeRing n p →+* PadicRationalHeckeRing n p :=
  padicIntegralToRationalRingHom n p ℤ

/-- `padicIntegralToRationalRingHom` maps each basis element to the corresponding `GL_n(ℚ_p)` basis
element. -/
@[simp]
theorem padicIntegralToRationalRingHom_single (R : Type*) [Semiring R]
    (D : HeckeCoset (padicIntEntries n p) (GLnZp n p) (GLnZp n p)) (b : R) :
    padicIntegralToRationalRingHom n p R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map le_top le_rfl le_rfl) b :=
  HeckeCosetModule.mapSubmonoidRingHom_single R le_top D b

/-- `padicIntegralToRationalRingHom` is injective over any coefficient semiring `R`. -/
theorem padicIntegralToRationalRingHom_injective (R : Type*) [Semiring R] :
    Function.Injective (padicIntegralToRationalRingHom n p R) :=
  HeckeCosetModule.mapSubmonoidRingHom_injective R le_top

/-- `padicIntegralToRational` is injective. -/
theorem padicIntegralToRational_injective :
    Function.Injective (padicIntegralToRational n p) :=
  padicIntegralToRationalRingHom_injective n p ℤ

/-- `padicIntegralToRationalRingHom` preserves `LeftCosetModule.deg`. -/
@[simp]
theorem deg_padicIntegralToRationalRingHom (R : Type*) [Semiring R]
    (f : 𝕋 (padicIntEntries n p) (GLnZp n p) R) :
    LeftCosetModule.deg (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R
        (padicIntegralToRationalRingHom n p R f) =
      LeftCosetModule.deg (padicIntEntries n p) (GLnZp n p) R f :=
  HeckeCosetModule.deg_mapSubmonoidRingHom R le_top f

/-- `padicIntegralToRational` sends `padicNatPowDiagElem n p e` to `padicIntPowDiagElem` at the
cast exponent tuple. -/
@[simp]
theorem padicIntegralToRational_padicNatPowDiagElem (e : Fin n → ℕ) :
    padicIntegralToRational n p (padicNatPowDiagElem n p e) =
      padicIntPowDiagElem n p (fun i ↦ (e i : ℤ)) := by
  rw [padicNatPowDiagElem_def, padicIntegralToRationalRingHom_single, padicNatPowDiagCoset_def,
    padicIntPowDiagElem_def, padicIntPowDiagCoset_def, HeckeCoset.map_mk]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (HeckeCoset.mk_congr_val (padicIntPowDiagGL_natCast n p e).symm)

/-- A `p`-adic diagonal matrix with a negative exponent does not have `ℤ_p`-entries. -/
theorem padicIntPowDiagGL_notMem_padicIntEntries_of_neg {e : Fin n → ℤ} {i : Fin n}
    (hi : e i < 0) : padicIntPowDiagGL n p e ∉ padicIntEntries n p := by
  intro hmem
  have hnorm := (hasPadicIntEntries_iff_norm_le_one n p).mp
    ((mem_padicIntEntries_iff n p).mp hmem) i i
  rw [padicIntPowDiagGL_coe, Matrix.diagonal_apply_eq, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_zpow, Padic.valuation_p, mul_one] at hnorm
  omega

/-- Any `p`-adic diagonal basis operator with a negative exponent lies outside the range of
`padicIntegralToRational`. -/
theorem padicIntPowDiagElem_notMem_range_padicIntegralToRational {e : Fin n → ℤ} {i : Fin n}
    (hi : e i < 0) :
    padicIntPowDiagElem n p e ∉ Set.range (padicIntegralToRational n p) := by
  classical
  rintro ⟨f, hf⟩
  let E := padicIntPowDiagCoset n p e
  have hE : E ∉ Set.range
      (HeckeCoset.map (le_top : padicIntEntries n p ≤ ⊤) (le_refl (GLnZp n p))
        (le_refl (GLnZp n p))) := by
    rw [HeckeCoset.mem_range_map_of_le_iff]
    intro hrep
    have hmem : padicIntPowDiagGL n p e ∈
        doubleCoset (E.rep : GL (Fin n) ℚ_[p]) (GLnZp n p) (GLnZp n p) := by
      rw [← HeckeCoset.toSet_eq_doubleCoset_rep]
      dsimp only [E]
      rw [padicIntPowDiagCoset_def, HeckeCoset.toSet_mk]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    exact padicIntPowDiagGL_notMem_padicIntEntries_of_neg n p hi
      (IsHeckeTriple.mem_of_mem_doubleCoset hrep hmem)
  have h0 : padicIntegralToRational n p f E = 0 := by
    rw [padicIntegralToRational, coe_padicIntegralToRationalRingHom]
    exact HeckeCosetModule.mapSubmonoid_apply_of_notMem_range ℤ le_top f hE
  rw [hf, padicIntPowDiagElem_def, HeckeCosetModule.single_apply, ite_eq_left rfl] at h0
  exact one_ne_zero h0

/-- **Positive-rank non-surjectivity**: for `n ≠ 0`, `[GL_n(ℤ_p) · (p⁻¹I) · GL_n(ℤ_p)]` does not lie
in the image of `padicIntegralToRational n p`. -/
theorem padicIntPowDiagElem_neg_one_notMem_range_padicIntegralToRational [NeZero n] :
    padicIntPowDiagElem n p (fun _ ↦ -1) ∉ Set.range (padicIntegralToRational n p) :=
  padicIntPowDiagElem_notMem_range_padicIntegralToRational n p (i := 0) (by norm_num)

end PadicInclusion

section RationalPadicComparison

/-- **Left-coset surjectivity for `(pLocalPosGL n p, GL_n(ℚ_p))`**: every `δ' ∈ GL_n(ℚ_p)`
translates on the left by `GL_n(ℤ_p)` into `(pLocalPosGL n p).toSubmonoid.map (castGLPadic n p)`. -/
theorem exists_mem_GLnZp_mul_mem_map_pLocalPosGL
    (δ' : (⊤ : Submonoid (GL (Fin n) ℚ_[p]))) :
    ∃ u ∈ GLnZp n p,
      u * (δ' : GL (Fin n) ℚ_[p]) ∈ (pLocalPosGL n p).toSubmonoid.map (castGLPadic n p) := by
  obtain ⟨k, hk⟩ :=
    exists_padicNatPowDiagGL_const_mul_mem_padicIntEntries n p (δ' : GL (Fin n) ℚ_[p])
  obtain ⟨u, hu, g₀, hg₀, hug₀⟩ :=
    exists_mem_GLnZp_mul_mem_map_pPrimaryPosDetInt n p ⟨_, hk⟩
  refine ⟨u, hu, intPowDiagGL n p (fun _ ↦ -(k : ℤ)) * g₀,
    (pLocalPosGL n p).mul_mem (intPowDiagGL_mem_pLocalPosGL n p _)
      (pPrimaryPosDetInt_le_pLocalPosGL n p hg₀), ?_⟩
  apply mul_left_cancel (a := padicNatPowDiagGL n p (fun _ ↦ k))
  rw [map_mul, ← padicIntPowDiagGL_def, padicIntPowDiagGL_const_neg, mul_inv_cancel_left, hug₀]
  simp only [← mul_assoc, padicNatPowDiagGL_const_comm n p k u]

/-- **Stabilizer transitivity for `(pLocalPosGL n p, GL_n(ℚ_p))`**: for every `g` in the image of
`pLocalPosGL n p` and every `u ∈ GL_n(ℤ_p)`, there exists `x` in the image of `SL_n(ℤ)` with
`x⁻¹ * u ∈ g • GL_n(ℤ_p)`. -/
theorem exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL
    (g : (pLocalPosGL n p).toSubmonoid.map (castGLPadic n p))
    (u : GL (Fin n) ℚ_[p]) (hu : u ∈ GLnZp n p) :
    ∃ x ∈ (SLnZ n).map (castGLPadic n p),
      x⁻¹ * u ∈ ConjAct.toConjAct (g : GL (Fin n) ℚ_[p]) • GLnZp n p := by
  obtain ⟨g₀, hg₀, hg_eq⟩ := g.2
  obtain ⟨-, k, hkg₀⟩ := (mem_pLocalPosGL_iff n p).mp hg₀
  obtain ⟨x, hx, hconj⟩ := exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp n p
    ⟨castGLPadic n p (natDiagGL n (fun _ ↦ p ^ k) * g₀), ⟨_, hkg₀, rfl⟩⟩ u hu
  refine ⟨x, hx, ?_⟩
  have hpk : castGLPadic n p (natDiagGL n (fun _ ↦ p ^ k)) =
      padicNatPowDiagGL n p (fun _ ↦ k) := by
    rw [padicNatPowDiagGL_def]
    exact congrArg (fun d ↦ castGLPadic n p (natDiagGL n d))
      (funext fun i ↦ (primePowDiag_apply n p (fun _ ↦ k) i).symm)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv] at hconj ⊢
  dsimp only at hconj
  rw [map_mul, hg_eq, hpk, _root_.mul_inv_rev, mul_assoc, mul_assoc] at hconj
  have hc : (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ *
      (x⁻¹ * u * (padicNatPowDiagGL n p (fun _ ↦ k) * (g : GL (Fin n) ℚ_[p]))) =
      x⁻¹ * u * (g : GL (Fin n) ℚ_[p]) := by
    rw [← mul_assoc (x⁻¹ * u), ← padicNatPowDiagGL_const_comm n p k (x⁻¹ * u), ← mul_assoc,
      inv_mul_cancel_left]
  rwa [hc, ← mul_assoc] at hconj

private theorem castGLPadic_pLocalPosGL_le :
    (pLocalPosGL n p).toSubmonoid.map (castGLPadic n p) ≤
      ((pLocalPosGL n p).map (castGLPadic n p)).toSubmonoid := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

/-- Hecke-triple instance on the `castGLPadic`-image of `(pLocalPosGL n p, SLnZ n)`. -/
noncomputable instance instIsHeckeTripleMapCastPLocalPosGL :
    IsHeckeTriple ((pLocalPosGL n p).toSubmonoid.map (castGLPadic n p))
      ((SLnZ n).map (castGLPadic n p)) ((SLnZ n).map (castGLPadic n p)) :=
  IsHeckeTriple.map (castGLPadic n p)

/-- Bijection between `p`-local rational `SL_n(ℤ)` double cosets and `p`-adic `GL_n(ℤ_p)` double
cosets in `GL_n(ℚ_p)`. -/
noncomputable def pLocalPosToPadicRationalCosetEquiv :
    HeckeCoset (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n) ≃
      HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p) :=
  (HeckeCoset.mapEquivOfInjective (castGLPadic n p) (castGLPadic_injective n p)).trans
    (HeckeCoset.mapEquivOfInf (map_SLnZ_eq_GLnZp_inf_map_pLocalPosGL n p) le_top
      (castGLPadic_pLocalPosGL_le n p)
      (exists_mem_GLnZp_mul_mem_map_pLocalPosGL n p)
      (exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL n p))

/-- Explicit action of `pLocalPosToPadicRationalCosetEquiv` on `HeckeCoset.mk`. -/
@[simp]
theorem pLocalPosToPadicRationalCosetEquiv_mk (g : (pLocalPosGL n p).toSubmonoid) :
    pLocalPosToPadicRationalCosetEquiv n p (HeckeCoset.mk (SLnZ n) (SLnZ n) g) =
      HeckeCoset.mk (GLnZp n p) (GLnZp n p) ⟨castGLPadic n p g, trivial⟩ := by
  simp only [pLocalPosToPadicRationalCosetEquiv, Equiv.trans_apply,
    HeckeCoset.mapEquivOfInjective_apply, HeckeCoset.mapHom_mk, HeckeCoset.mapEquivOfInf_apply,
    HeckeCoset.map_mk]
  exact HeckeCoset.mk_congr_val rfl

/-- `pLocalPosToPadicRationalCosetEquiv` preserves `HeckeCoset.degree`. -/
@[simp]
theorem degree_pLocalPosToPadicRationalCosetEquiv
    (D : HeckeCoset (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n)) :
    (pLocalPosToPadicRationalCosetEquiv n p D).degree = D.degree := by
  simp only [pLocalPosToPadicRationalCosetEquiv, Equiv.trans_apply,
    HeckeCoset.mapEquivOfInf_apply, HeckeCoset.mapEquivOfInjective_apply]
  rw [HeckeCoset.degree_map_of_inf (map_SLnZ_eq_GLnZp_inf_map_pLocalPosGL n p) le_top
      (castGLPadic_pLocalPosGL_le n p)
      (exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL n p),
    HeckeCoset.degree_mapHom_of_injective (castGLPadic_injective n p)]

/-- **Equality of rational structure constants**: double-coset multiplicities on
`(pLocalPosGL n p, SL_n(ℤ))` equal the `p`-adic multiplicities on `(GL_n(ℚ_p), GL_n(ℤ_p))`. -/
theorem multiplicity_GLnZp_castGLPadic_of_mem_pLocalPosGL {g₁ g₂ g : GL (Fin n) ℚ}
    (hg₁ : g₁ ∈ pLocalPosGL n p) (hg₂ : g₂ ∈ pLocalPosGL n p) (hg : g ∈ pLocalPosGL n p) :
    DoubleCoset.multiplicity (GLnZp n p) (GLnZp n p) (GLnZp n p)
        (castGLPadic n p g₁) (castGLPadic n p g₂) (castGLPadic n p g) =
      DoubleCoset.multiplicity (SLnZ n) (SLnZ n) (SLnZ n) g₁ g₂ g := by
  have hinf := DoubleCoset.multiplicity_eq_of_inf (map_SLnZ_eq_GLnZp_inf_map_pLocalPosGL n p)
    (⟨g₁, hg₁, rfl⟩ : castGLPadic n p g₁ ∈ (pLocalPosGL n p).map (castGLPadic n p))
    ⟨g₂, hg₂, rfl⟩ ⟨g, hg, rfl⟩
    (exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL n p
      ⟨castGLPadic n p g₁, ⟨g₁, hg₁, rfl⟩⟩)
    (exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL n p
      ⟨castGLPadic n p g₂, ⟨g₂, hg₂, rfl⟩⟩)
  exact hinf.trans (DoubleCoset.multiplicity_map_of_injective (castGLPadic n p)
    (castGLPadic_injective n p) (SLnZ n) (SLnZ n) (SLnZ n) g₁ g₂ g)

/-- **Rational `p`-adic Hecke ring isomorphism on `pLocalPosGL`** over any coefficient semiring
`R`. -/
noncomputable def pLocalPosToPadicRationalRingEquiv (R : Type*) [Semiring R] :
    𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) R ≃+*
      𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R :=
  (HeckeCosetModule.mapInjectiveRingEquiv R (castGLPadic n p) (castGLPadic_injective n p)).trans
    (HeckeCosetModule.mapSubgroupRingEquiv R (map_SLnZ_eq_GLnZp_inf_map_pLocalPosGL n p)
      le_top (castGLPadic_pLocalPosGL_le n p)
      (exists_mem_GLnZp_mul_mem_map_pLocalPosGL n p)
      (exists_mem_map_SLnZ_inv_mul_mem_conj_GLnZp_of_pLocalPosGL n p))

/-- `pLocalPosToPadicRationalRingEquiv` maps basis elements via
`pLocalPosToPadicRationalCosetEquiv`. -/
@[simp]
theorem pLocalPosToPadicRationalRingEquiv_single (R : Type*) [Semiring R]
    (D : HeckeCoset (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n)) (b : R) :
    pLocalPosToPadicRationalRingEquiv n p R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (pLocalPosToPadicRationalCosetEquiv n p D) b := by
  simp [pLocalPosToPadicRationalRingEquiv, pLocalPosToPadicRationalCosetEquiv]

/-- `pLocalPosToPadicRationalRingEquiv` preserves `LeftCosetModule.deg`. -/
@[simp]
theorem deg_pLocalPosToPadicRationalRingEquiv (R : Type*) [Semiring R]
    (f : 𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) R) :
    LeftCosetModule.deg (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R
        (pLocalPosToPadicRationalRingEquiv n p R f) =
      LeftCosetModule.deg (pLocalPosGL n p).toSubmonoid (SLnZ n) R f := by
  simp [pLocalPosToPadicRationalRingEquiv]

/-- Every element of `pLocalPosGL n p` lies in the `SL_n(ℤ)` double coset of `intPowDiagGL n p e`
for a monotone tuple `e : Fin n → ℤ`. -/
theorem exists_intPowDiagGL_mem_doubleCoset {g : GL (Fin n) ℚ} (hg : g ∈ pLocalPosGL n p) :
    ∃ e : Fin n → ℤ, Monotone e ∧
      g ∈ doubleCoset (intPowDiagGL n p e) (SLnZ n) (SLnZ n) := by
  obtain ⟨-, k, hkg⟩ := (mem_pLocalPosGL_iff n p).mp hg
  obtain ⟨f, hf, hcos⟩ := exists_primePowDiag_mem_doubleCoset n p hkg
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  refine ⟨fun i ↦ (f i : ℤ) - k, fun i j hij ↦ sub_le_sub_right (Int.ofNat_le.mpr (hf hij)) _,
    DoubleCoset.mem_doubleCoset.mpr ⟨x, hx, y, hy, ?_⟩⟩
  apply mul_left_cancel (a := natDiagGL n (fun _ ↦ p ^ k))
  have hcomm : natDiagGL n (fun _ ↦ p ^ k) * x = x * natDiagGL n (fun _ ↦ p ^ k) :=
    natDiagGL_const_comm n (p ^ k) x
  have hshift : natDiagGL n (fun _ ↦ p ^ k) * intPowDiagGL n p (fun i ↦ (f i : ℤ) - k) =
      natDiagGL n (primePowDiag n p f) := by
    have hfun : (fun i ↦ (f i : ℤ) - k + k) = fun i ↦ (f i : ℤ) := funext fun _ ↦ sub_add_cancel _ _
    rw [natDiagGL_const_comm, intPowDiagGL_mul_natDiagGL_const, hfun, intPowDiagGL_natCast]
  calc natDiagGL n (fun _ ↦ p ^ k) * g
      = x * natDiagGL n (primePowDiag n p f) * y := hxy
    _ = x * (natDiagGL n (fun _ ↦ p ^ k) * intPowDiagGL n p (fun i ↦ (f i : ℤ) - k)) * y := by
        rw [hshift]
    _ = natDiagGL n (fun _ ↦ p ^ k) * (x * intPowDiagGL n p (fun i ↦ (f i : ℤ) - k) * y) := by
        simp only [← mul_assoc, hcomm]

/-- The image of `𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) ℤ` inside `RationalHeckeRing n` is
`pLocalRationalSubring n p`. -/
theorem range_mapSubmonoidRingHom_pLocalPosGL :
    (HeckeCosetModule.mapSubmonoidRingHom (H := SLnZ n) ℤ
        (pLocalPosGL_le_glpos n p)).range =
      pLocalRationalSubring n p := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    induction f using HeckeCosetModule.induction_linear with
    | h0 => rw [map_zero]; exact (pLocalRationalSubring n p).zero_mem
    | hadd x y ihx ihy => rw [map_add]; exact (pLocalRationalSubring n p).add_mem ihx ihy
    | hsingle D c =>
      rw [HeckeCosetModule.mapSubmonoidRingHom_single, ← HeckeCosetModule.smul_single_one ℤ _ c]
      refine (pLocalRationalSubring n p).zsmul_mem ?_ c
      obtain ⟨e, he, hmem⟩ := exists_intPowDiagGL_mem_doubleCoset n p D.rep.2
      have hmap : HeckeCosetModule.single ℤ
          (D.map (pLocalPosGL_le_glpos n p) le_rfl le_rfl) 1 =
          intPowDiagElem n p e := by
        rw [intPowDiagElem_def]
        refine congrArg (HeckeCosetModule.single ℤ · 1) ?_
        conv_lhs => rw [← HeckeCoset.mk_rep D, HeckeCoset.map_mk]
        rw [intPowDiagCoset_def]
        exact HeckeCoset.mk_eq_mk_of_mem hmem
      rw [hmap]
      exact intPowDiagElem_mem_pLocalRationalSubring n p e he
  · rw [pLocalRationalSubring_le_iff]
    intro e _
    let D₀ : HeckeCoset (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n) :=
      HeckeCoset.mk _ _ ⟨intPowDiagGL n p e, intPowDiagGL_mem_pLocalPosGL n p e⟩
    refine ⟨HeckeCosetModule.single ℤ D₀ 1, ?_⟩
    rw [HeckeCosetModule.mapSubmonoidRingHom_single, intPowDiagElem_def, intPowDiagCoset_def]
    exact congrArg (HeckeCosetModule.single ℤ · 1) (HeckeCoset.map_mk _ _ _ _)

/-- Ring isomorphism between `𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) ℤ` and
`pLocalRationalSubring n p`. -/
noncomputable def pLocalPosToPLocalRationalRingEquiv :
    𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) ℤ ≃+* pLocalRationalSubring n p :=
  HeckeCosetModule.mapSubmonoidSubringEquiv (pLocalPosGL_le_glpos n p)
    (range_mapSubmonoidRingHom_pLocalPosGL n p)

/-- Coercion of `pLocalPosToPLocalRationalRingEquiv` to `RationalHeckeRing n`. -/
@[simp]
theorem pLocalPosToPLocalRationalRingEquiv_coe
    (f : 𝕋 (pLocalPosGL n p).toSubmonoid (SLnZ n) ℤ) :
    (pLocalPosToPLocalRationalRingEquiv n p f : RationalHeckeRing n) =
      HeckeCosetModule.mapSubmonoidRingHom (H := SLnZ n) ℤ
        (pLocalPosGL_le_glpos n p) f :=
  HeckeCosetModule.coe_mapSubmonoidSubringEquiv_apply _ _ f

/-- **The rational `p`-adic `GL_n` Hecke ring comparison**
(Rhodes–Shemanske 1998, §3.2; [Rhodes–Shemanske][rhodes1999] §2):
`pLocalRationalSubring n p` is canonically isomorphic to `PadicRationalHeckeRing n p`. -/
noncomputable def pLocalRationalToPadicRingEquiv :
    pLocalRationalSubring n p ≃+* PadicRationalHeckeRing n p :=
  (pLocalPosToPLocalRationalRingEquiv n p).symm.trans (pLocalPosToPadicRationalRingEquiv n p ℤ)

/-- Defining factorization of `pLocalRationalToPadicRingEquiv`. -/
theorem pLocalRationalToPadicRingEquiv_def :
    pLocalRationalToPadicRingEquiv n p =
      (pLocalPosToPLocalRationalRingEquiv n p).symm.trans
        (pLocalPosToPadicRationalRingEquiv n p ℤ) := (rfl)

/-- `pLocalRationalToPadicRingEquiv` sends each monotone `p`-power diagonal operator
`intPowDiagElem n p e` to `padicIntPowDiagElem n p e`. -/
@[simp]
theorem pLocalRationalToPadicRingEquiv_intPowDiagElem (e : Fin n → ℤ) (he : Monotone e) :
    pLocalRationalToPadicRingEquiv n p
        ⟨intPowDiagElem n p e, intPowDiagElem_mem_pLocalRationalSubring n p e he⟩ =
      padicIntPowDiagElem n p e := by
  let D₀ : HeckeCoset (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n) :=
    HeckeCoset.mk _ _ ⟨intPowDiagGL n p e, intPowDiagGL_mem_pLocalPosGL n p e⟩
  have hPLoc : pLocalPosToPLocalRationalRingEquiv n p (HeckeCosetModule.single ℤ D₀ 1) =
      ⟨intPowDiagElem n p e, intPowDiagElem_mem_pLocalRationalSubring n p e he⟩ := by
    apply Subtype.ext
    rw [pLocalPosToPLocalRationalRingEquiv_coe]
    dsimp only
    rw [HeckeCosetModule.mapSubmonoidRingHom_single, intPowDiagElem_def, intPowDiagCoset_def]
    exact congrArg (HeckeCosetModule.single ℤ · 1) (HeckeCoset.map_mk _ _ _ _)
  rw [pLocalRationalToPadicRingEquiv, ← hPLoc, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    pLocalPosToPadicRationalRingEquiv_single, pLocalPosToPadicRationalCosetEquiv_mk,
    padicIntPowDiagElem_def, padicIntPowDiagCoset_def]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (HeckeCoset.mk_congr_val (padicIntPowDiagGL_def n p e).symm)

/-- **Compatibility of the integral and rational `p`-adic comparisons**: the square formed by
`integralToRationalLocal`, `pLocalToPadicIntegralRingEquiv`, `pLocalRationalToPadicRingEquiv`, and
`padicIntegralToRational` commutes. -/
@[simp]
theorem pLocalRationalToPadicRingEquiv_integralToRationalLocal (x : pLocalSubring n p) :
    pLocalRationalToPadicRingEquiv n p (integralToRationalLocal n p x) =
      padicIntegralToRational n p (pLocalToPadicIntegralRingEquiv n p x) := by
  let φ₁ : pLocalSubring n p →+* PadicRationalHeckeRing n p :=
    (pLocalRationalToPadicRingEquiv n p).toRingHom.comp (integralToRationalLocal n p)
  let φ₂ : pLocalSubring n p →+* PadicRationalHeckeRing n p :=
    (padicIntegralToRational n p).comp (pLocalToPadicIntegralRingEquiv n p).toRingHom
  suffices hS : ∀ y : IntegralHeckeRing n, (hy : y ∈ pLocalSubring n p) →
      φ₁ ⟨y, hy⟩ = φ₂ ⟨y, hy⟩ from hS x.1 x.2
  intro y hy
  have hmem : y ∈ (φ₁.eqLocus φ₂).map (pLocalSubring n p).subtype := by
    have hle : pLocalSubring n p ≤ (φ₁.eqLocus φ₂).map (pLocalSubring n p).subtype := by
      rw [pLocalSubring_le_iff]
      intro e he
      have he_int : Monotone fun i ↦ (e i : ℤ) := fun _ _ hij ↦ Int.ofNat_le.mpr (he hij)
      rw [Subring.mem_map]
      refine ⟨⟨diagElem (primePowDiag n p e), diagElem_primePowDiag_mem_pLocalSubring n p e he⟩,
        ?_, rfl⟩
      rw [RingHom.mem_eqLocus]
      dsimp only [φ₁, φ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      have hint : integralToRationalLocal n p
          ⟨diagElem (primePowDiag n p e), diagElem_primePowDiag_mem_pLocalSubring n p e he⟩ =
          ⟨intPowDiagElem n p (fun i ↦ (e i : ℤ)),
            intPowDiagElem_mem_pLocalRationalSubring n p _ he_int⟩ :=
        Subtype.ext (by rw [integralToRationalLocal_coe]; exact (intPowDiagElem_natCast n p e).symm)
      rw [hint, pLocalRationalToPadicRingEquiv_intPowDiagElem n p _ he_int,
        pLocalToPadicIntegralRingEquiv_diagElem_primePowDiag n p e he,
        padicIntegralToRational_padicNatPowDiagElem]
    exact hle hy
  obtain ⟨⟨w, hw⟩, heq, hw_eq⟩ := hmem
  cases hw_eq
  exact heq

/-- `pLocalRationalToPadicRingEquiv` preserves `LeftCosetModule.deg`. -/
@[simp]
theorem deg_pLocalRationalToPadicRingEquiv (x : pLocalRationalSubring n p) :
    LeftCosetModule.deg (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) ℤ
        (pLocalRationalToPadicRingEquiv n p x) =
      LeftCosetModule.deg (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) ℤ
        (x : RationalHeckeRing n) := by
  obtain ⟨f, rfl⟩ := (pLocalPosToPLocalRationalRingEquiv n p).surjective x
  rw [pLocalRationalToPadicRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    deg_pLocalPosToPadicRationalRingEquiv, pLocalPosToPLocalRationalRingEquiv_coe,
    HeckeCosetModule.deg_mapSubmonoidRingHom]

end RationalPadicComparison

section CentralLocalizationAndLaurent

/-- The central integral `p`-adic Hecke operator `[GL_n(ℤ_p) · (pI) · GL_n(ℤ_p)]`. -/
noncomputable def padicScalarIntElem : PadicIntegralHeckeRing n p :=
  padicNatPowDiagElem n p (fun _ ↦ 1)

/-- Defining equation for `padicScalarIntElem`. -/
theorem padicScalarIntElem_def :
    padicScalarIntElem n p = padicNatPowDiagElem n p (fun _ ↦ 1) := (rfl)

/-- The central rational `p`-adic inverse operator `[GL_n(ℤ_p) · (p⁻¹I) · GL_n(ℤ_p)]`. -/
noncomputable def padicScalarInvElem : PadicRationalHeckeRing n p :=
  padicIntPowDiagElem n p (fun _ ↦ -1)

/-- Defining equation for `padicScalarInvElem`. -/
theorem padicScalarInvElem_def :
    padicScalarInvElem n p = padicIntPowDiagElem n p (fun _ ↦ -1) := (rfl)

/-- The central `pI` operator bundled as a unit of `PadicRationalHeckeRing n p` with inverse
`padicScalarInvElem n p`. -/
noncomputable def padicScalarUnit : (PadicRationalHeckeRing n p)ˣ :=
  HeckeCosetModule.unitOfMemNormalizer ℤ (x := padicIntPowDiagGL n p (fun _ ↦ 1))
    (Submonoid.mem_top _) (Submonoid.mem_top _)
    (padicIntPowDiagGL_const_mem_normalizer n p 1)

/-- Coercion of `padicScalarUnit` to `PadicRationalHeckeRing n p` is the image of
`padicScalarIntElem n p`. -/
@[simp]
theorem val_padicScalarUnit :
    (padicScalarUnit n p : PadicRationalHeckeRing n p) =
      padicIntegralToRational n p (padicScalarIntElem n p) := by
  rw [padicScalarUnit, HeckeCosetModule.val_unitOfMemNormalizer, padicScalarIntElem_def,
    padicIntegralToRational_padicNatPowDiagElem, padicIntPowDiagElem_def,
    padicIntPowDiagCoset_def]
  simp only [Nat.cast_one]

/-- Coercion of `(padicScalarUnit n p)⁻¹` to `PadicRationalHeckeRing n p` is
`padicScalarInvElem n p`. -/
@[simp]
theorem val_inv_padicScalarUnit :
    (↑(padicScalarUnit n p)⁻¹ : PadicRationalHeckeRing n p) = padicScalarInvElem n p := by
  rw [padicScalarUnit, HeckeCosetModule.val_inv_unitOfMemNormalizer, padicScalarInvElem_def,
    padicIntPowDiagElem_def, padicIntPowDiagCoset_def]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (HeckeCoset.mk_congr_val (by rw [← padicIntPowDiagGL_neg, Pi.neg_def]))

/-- **Central invertibility of `pI` in `PadicRationalHeckeRing`**: `[GL_n(ℤ_p) · (pI) · GL_n(ℤ_p)]`
multiplied on the right by `[GL_n(ℤ_p) · (p⁻¹I) · GL_n(ℤ_p)]` equals `1`. -/
@[simp]
theorem padicIntegralToRational_padicScalarIntElem_mul_padicScalarInvElem :
    padicIntegralToRational n p (padicScalarIntElem n p) * padicScalarInvElem n p = 1 := by
  rw [← val_padicScalarUnit, ← val_inv_padicScalarUnit, Units.mul_inv]

/-- `[GL_n(ℤ_p) · (p⁻¹I) · GL_n(ℤ_p)]` multiplied on the right by `[GL_n(ℤ_p) · (pI) · GL_n(ℤ_p)]`
equals `1`. -/
@[simp]
theorem padicScalarInvElem_mul_padicIntegralToRational_padicScalarIntElem :
    padicScalarInvElem n p * padicIntegralToRational n p (padicScalarIntElem n p) = 1 := by
  rw [← val_padicScalarUnit, ← val_inv_padicScalarUnit, Units.inv_mul]

/-- Multiplying `padicIntPowDiagElem n p e` by `padicScalarUnit n p ^ k` shifts every exponent
upward by `k`. -/
theorem padicIntPowDiagElem_mul_padicScalarUnit_pow (e : Fin n → ℤ) (k : ℕ) :
    padicIntPowDiagElem n p e * (padicScalarUnit n p : PadicRationalHeckeRing n p) ^ k =
      padicIntPowDiagElem n p (fun i ↦ e i + (k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul := HeckeCosetModule.single_mul_single_of_mem_normalizer_right
      (Δ := (⊤ : Submonoid (GL (Fin n) ℚ_[p]))) (Γ := GLnZp n p)
      (x := ⟨padicIntPowDiagGL n p (fun i ↦ e i + (k : ℤ)), Submonoid.mem_top _⟩)
      (y := ⟨padicIntPowDiagGL n p (fun _ ↦ 1), Submonoid.mem_top _⟩) ℤ
      (padicIntPowDiagGL_const_mem_normalizer n p 1)
    rw [pow_succ, ← mul_assoc, ih, val_padicScalarUnit, padicScalarIntElem_def,
      padicIntegralToRational_padicNatPowDiagElem]
    simp only [Nat.cast_one]
    rw [padicIntPowDiagElem_def, padicIntPowDiagElem_def,
      padicIntPowDiagCoset_def, padicIntPowDiagCoset_def, hmul,
      padicIntPowDiagElem_def, padicIntPowDiagCoset_def]
    refine congrArg (HeckeCosetModule.single ℤ · 1) (HeckeCoset.mk_congr_val ?_)
    rw [Submonoid.coe_mul, ← padicIntPowDiagGL_add]
    exact congrArg (padicIntPowDiagGL n p)
      (funext fun i ↦ by dsimp only [Pi.add_apply]; push_cast; ring)

/-- **Denominator clearing in `PadicRationalHeckeRing`**: every element of
`PadicRationalHeckeRing n p` multiplies into the image of `PadicIntegralHeckeRing n p` under a
power of `padicScalarUnit n p`. -/
theorem exists_mul_padicScalarUnit_pow_eq (z : PadicRationalHeckeRing n p) :
    ∃ (k : ℕ) (a : PadicIntegralHeckeRing n p),
      z * (padicScalarUnit n p : PadicRationalHeckeRing n p) ^ k =
        padicIntegralToRational n p a := by
  induction z using HeckeCosetModule.induction_linear with
  | h0 => exact ⟨0, 0, by simp⟩
  | hadd x y ihx ihy =>
    obtain ⟨k₁, a₁, h₁⟩ := ihx
    obtain ⟨k₂, a₂, h₂⟩ := ihy
    refine ⟨k₁ + k₂, a₁ * padicScalarIntElem n p ^ k₂ + a₂ * padicScalarIntElem n p ^ k₁, ?_⟩
    rw [add_mul, pow_add, ← mul_assoc, h₁,
      mul_comm ((padicScalarUnit n p : PadicRationalHeckeRing n p) ^ k₁),
      ← mul_assoc, h₂, map_add, map_mul, map_mul, map_pow, map_pow, ← val_padicScalarUnit]
  | hsingle D c =>
    obtain ⟨⟨e, he⟩, rfl⟩ := (padicIntPowDiagCosetEquiv n p).surjective D
    rw [padicIntPowDiagCosetEquiv_apply]
    dsimp only
    obtain ⟨k, f, hf_pt⟩ := TauCeti.exists_natCast_eq_add_natCast e
    have hf : (fun i ↦ (f i : ℤ)) = fun i ↦ e i + (k : ℤ) := funext hf_pt
    refine ⟨k, HeckeCosetModule.single ℤ (padicNatPowDiagCoset n p f) c, ?_⟩
    rw [← HeckeCosetModule.smul_single_one ℤ _ c, ← padicIntPowDiagElem_def,
      HeckeCosetModule.mul_def, HeckeCosetModule.smul_mul ℤ, ← HeckeCosetModule.mul_def,
      padicIntPowDiagElem_mul_padicScalarUnit_pow, ← hf, padicIntPowDiagElem_def,
      HeckeCosetModule.smul_single_one ℤ, padicIntegralToRational,
      padicIntegralToRationalRingHom_single, padicNatPowDiagCoset_def,
      padicIntPowDiagCoset_def, HeckeCoset.map_mk]
    exact congrArg (HeckeCosetModule.single ℤ · c)
      (HeckeCoset.mk_congr_val (padicIntPowDiagGL_natCast n p f))

/-- **`PadicRationalHeckeRing` as central localization of `PadicIntegralHeckeRing`**: equipped with
the `Algebra` structure from `padicIntegralToRational n p`, `PadicRationalHeckeRing n p` satisfies
`IsLocalization.Away (padicScalarIntElem n p)`. -/
theorem isLocalization_away_padicScalarIntElem :
    letI : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
      (padicIntegralToRational n p).toAlgebra
    IsLocalization.Away (padicScalarIntElem n p) (PadicRationalHeckeRing n p) := by
  let : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
    (padicIntegralToRational n p).toAlgebra
  refine IsLocalization.Away.mk (padicScalarIntElem n p)
    (val_padicScalarUnit n p ▸ (padicScalarUnit n p).isUnit)
    (fun z ↦ ?_)
    (fun _ _ hab ↦ ⟨0, by simp [padicIntegralToRational_injective n p hab]⟩)
  obtain ⟨k, a, hk⟩ := exists_mul_padicScalarUnit_pow_eq n p z
  exact ⟨k, a, by simpa only [val_padicScalarUnit, RingHom.algebraMap_toAlgebra] using hk⟩

/-- Ring homomorphisms out of `PadicRationalHeckeRing n p` into any semiring `R` are uniquely
determined by their precomposition with `padicIntegralToRational n p`. -/
theorem padicRationalHeckeRing_ringHom_ext {R : Type*} [Semiring R]
    {f₁ f₂ : PadicRationalHeckeRing n p →+* R}
    (h : f₁.comp (padicIntegralToRational n p) = f₂.comp (padicIntegralToRational n p)) :
    f₁ = f₂ := by
  let _ : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
    (padicIntegralToRational n p).toAlgebra
  have := isLocalization_away_padicScalarIntElem n p
  exact IsLocalization.ringHom_ext (Submonoid.powers (padicScalarIntElem n p)) h

/-- **Universal-property lift for `PadicRationalHeckeRing`**: any ring homomorphism
`g : PadicIntegralHeckeRing n p →+* R` into a semiring `R` sending `padicScalarIntElem n p` (`pI`)
to a unit extends uniquely across `padicIntegralToRational n p` to
`PadicRationalHeckeRing n p →+* R`. -/
noncomputable def padicRationalHeckeRingLift {R : Type*} [Semiring R]
    (g : PadicIntegralHeckeRing n p →+* R) (hg : IsUnit (g (padicScalarIntElem n p))) :
    PadicRationalHeckeRing n p →+* R :=
  letI : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
    (padicIntegralToRational n p).toAlgebra
  haveI := isLocalization_away_padicScalarIntElem n p
  IsLocalization.Away.liftSemiring (padicScalarIntElem n p) hg

/-- `padicRationalHeckeRingLift` extends `g` along `padicIntegralToRational`. -/
@[simp]
theorem padicRationalHeckeRingLift_padicIntegralToRational {R : Type*} [Semiring R]
    (g : PadicIntegralHeckeRing n p →+* R) (hg : IsUnit (g (padicScalarIntElem n p)))
    (a : PadicIntegralHeckeRing n p) :
    padicRationalHeckeRingLift n p g hg (padicIntegralToRational n p a) = g a := by
  let _ : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
    (padicIntegralToRational n p).toAlgebra
  have := isLocalization_away_padicScalarIntElem n p
  exact IsLocalization.Away.liftSemiring_eq (padicScalarIntElem n p) hg a

/-- Precomposing `padicRationalHeckeRingLift` with `padicIntegralToRational` recovers `g`. -/
@[simp]
theorem padicRationalHeckeRingLift_comp_padicIntegralToRational {R : Type*} [Semiring R]
    (g : PadicIntegralHeckeRing n p →+* R) (hg : IsUnit (g (padicScalarIntElem n p))) :
    (padicRationalHeckeRingLift n p g hg).comp (padicIntegralToRational n p) = g :=
  RingHom.ext (padicRationalHeckeRingLift_padicIntegralToRational n p g hg)

/-- `padicRationalHeckeRingLift` maps `padicScalarInvElem n p` (`p⁻¹I`) to the inverse of the unit
image of `padicScalarIntElem n p`. -/
@[simp]
theorem padicRationalHeckeRingLift_padicScalarInvElem {R : Type*} [Semiring R]
    (g : PadicIntegralHeckeRing n p →+* R) (hg : IsUnit (g (padicScalarIntElem n p))) :
    padicRationalHeckeRingLift n p g hg (padicScalarInvElem n p) = ↑hg.unit⁻¹ := by
  apply hg.unit.mul_right_inj.mp
  rw [Units.mul_inv, IsUnit.unit_spec,
    ← padicRationalHeckeRingLift_padicIntegralToRational n p g hg,
    ← map_mul, padicIntegralToRational_padicScalarIntElem_mul_padicScalarInvElem, map_one]

/-- **Universal property of `padicIntegralToRational`**: a ring homomorphism out of
`PadicRationalHeckeRing n p` equals `padicRationalHeckeRingLift n p g hg` if and only if its
precomposition with `padicIntegralToRational n p` is `g`. -/
theorem eq_padicRationalHeckeRingLift_iff {R : Type*} [Semiring R]
    (g : PadicIntegralHeckeRing n p →+* R) (hg : IsUnit (g (padicScalarIntElem n p)))
    (f : PadicRationalHeckeRing n p →+* R) :
    f = padicRationalHeckeRingLift n p g hg ↔
      f.comp (padicIntegralToRational n p) = g := by
  let _ : Algebra (PadicIntegralHeckeRing n p) (PadicRationalHeckeRing n p) :=
    (padicIntegralToRational n p).toAlgebra
  have := isLocalization_away_padicScalarIntElem n p
  exact IsLocalization.Away.eq_liftSemiring_iff (padicScalarIntElem n p) hg f

/-- **Laurent polynomial presentation of `PadicRationalHeckeRing`** ([Shimura][shimura1971]
Theorem 3.20 combined with the `p`-adic rational comparison): for `n ≠ 0`,
`PadicRationalHeckeRing n p` is isomorphic to `Localization.Away (MvPolynomial.X (Fin.rev 0))`. -/
noncomputable def padicLaurentPolynomialRingEquiv [NeZero n] :
    Localization.Away (MvPolynomial.X (Fin.rev (0 : Fin n)) : MvPolynomial (Fin n) ℤ) ≃+*
      PadicRationalHeckeRing n p :=
  (laurentPolynomialRingEquiv n (Fact.out : p.Prime)).trans (pLocalRationalToPadicRingEquiv n p)

/-- Defining factorization of `padicLaurentPolynomialRingEquiv`. -/
theorem padicLaurentPolynomialRingEquiv_def [NeZero n] :
    padicLaurentPolynomialRingEquiv n p =
      (laurentPolynomialRingEquiv n (Fact.out : p.Prime)).trans
        (pLocalRationalToPadicRingEquiv n p) := (rfl)

/-- On polynomials, `padicLaurentPolynomialRingEquiv` agrees with `padicPolynomialRingEquiv`
followed by `padicIntegralToRational`. -/
@[simp]
theorem padicLaurentPolynomialRingEquiv_algebraMap [NeZero n] (P : MvPolynomial (Fin n) ℤ) :
    padicLaurentPolynomialRingEquiv n p (algebraMap (MvPolynomial (Fin n) ℤ)
        (Localization.Away (MvPolynomial.X (Fin.rev (0 : Fin n)) : MvPolynomial (Fin n) ℤ)) P) =
      padicIntegralToRational n p (padicPolynomialRingEquiv n p P) := by
  rw [padicLaurentPolynomialRingEquiv, RingEquiv.trans_apply, laurentPolynomialRingEquiv_apply,
    laurentEvalHomLocal_algebraMap, pLocalRationalToPadicRingEquiv_integralToRationalLocal,
    padicPolynomialRingEquiv_apply]

/-- `padicLaurentPolynomialRingEquiv` sends the formal inverse of `X (Fin.rev 0)` to
`padicScalarInvElem n p` (`p⁻¹I`). -/
@[simp]
theorem padicLaurentPolynomialRingEquiv_invSelf [NeZero n] :
    padicLaurentPolynomialRingEquiv n p (IsLocalization.Away.invSelf
        (S := Localization.Away (MvPolynomial.X (Fin.rev (0 : Fin n)) : MvPolynomial (Fin n) ℤ))
        (MvPolynomial.X (Fin.rev (0 : Fin n)) : MvPolynomial (Fin n) ℤ)) =
      padicScalarInvElem n p := by
  have hinv : (↑(scalarLocalUnit n p)⁻¹ : pLocalRationalSubring n p) =
      ⟨intPowDiagElem n p (fun _ ↦ -1),
        intPowDiagElem_mem_pLocalRationalSubring n p _ monotone_const⟩ :=
    Subtype.ext (by rw [coe_inv_scalarLocalUnit, ← intPowDiagElem_const_neg_one])
  rw [padicLaurentPolynomialRingEquiv, RingEquiv.trans_apply, laurentPolynomialRingEquiv_apply,
    laurentEvalHomLocal_invSelf, hinv,
    pLocalRationalToPadicRingEquiv_intPowDiagElem n p _ monotone_const,
    padicScalarInvElem_def]

end CentralLocalizationAndLaurent

end HeckeRing.GLn

end
