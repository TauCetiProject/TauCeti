/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Coleman.Topology
public import TauCeti.RingTheory.AdicCompletion.Principal

import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.PiTopology
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Congruences, continuity, and the Coleman norm projector

For a prime `p` and `(p)`-adically complete commutative ring `O`, this file establishes:
1. Mod-`p ^ k` contraction (`k ≥ 1`) `f ≡ g (mod p ^ k) → N(f) ≡ N(g) (mod p ^ (k + 1))` at units
   `IsUnit g` (for all primes including `p = 2`) and char-`p` identity `N(f) = map (frobenius) f`,
   yielding `N(f) ≡ σ(f) (mod p)` for any Frobenius lift `σ : O →+* O`.
2. For a Frobenius-lifting automorphism `σ : O ≃+* O`, the corrected norm `N_σ(f) = σ⁻¹(N(f))` and
   multiplicative idempotent projector `normProjector : O⟦X⟧ˣ →* O⟦X⟧ˣ` onto `fixedUnits p O σ`
   with `L(f) ≡ N_σ^[n](f) (mod p ^ (n + 1))`, with no topology or compactness on `O`.
3. Continuity of `correctedNorm` and `normProjector` in the coefficientwise topology on `O⟦X⟧`
   when `O` has its `(p)`-adic topology (`IsAdic (Ideal.span {(p : O)})`), convergence
   `N_σ^[n](f) → normProjector f` in `O⟦X⟧ˣ`, closedness of `fixedUnits p O σ` when `O` is
   Hausdorff with the `(p)`-adic topology, and compactness when `O` is compact Hausdorff with the
   `(p)`-adic topology.

## Main definitions and results

* `TauCeti.Coleman.norm_sub_norm_mem_span_pow_succ`, `TauCeti.Coleman.norm_eq_map_frobenius`,
  `TauCeti.Coleman.norm_sub_map_mem_span_p`: contraction at units and mod-`p` Frobenius congruence.
* `TauCeti.Coleman.correctedNorm`, `TauCeti.Coleman.fixedUnits`, `TauCeti.Coleman.normProjector`,
  `TauCeti.Coleman.normProjector_sub_iterate_mem_span_pow`, `TauCeti.Coleman.eq_normProjector_iff`,
  `TauCeti.Coleman.correctedNorm_normProjector`, `TauCeti.Coleman.normProjector_correctedNorm`,
  `TauCeti.Coleman.normProjector_eq_self`, `TauCeti.Coleman.range_normProjector`: corrected norm,
  fixed subgroup, and algebraic projector.
* `TauCeti.Coleman.continuous_correctedNorm`, `TauCeti.Coleman.tendsto_iterate_correctedNorm`,
  `TauCeti.Coleman.continuous_normProjector`, `TauCeti.Coleman.isClosed_fixedUnits`,
  `TauCeti.Coleman.isCompact_fixedUnits`: continuity, convergence, closedness, and compactness.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §IV (Lemma 13,
  Prop. 14).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.3.
* R. Sharifi, *Iwasawa Theory*, §5.4 (Prop. 5.4.6, Cors. 5.4.7–5.4.8, Thm. 5.4.9).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10.
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`).
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section Congruences

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]

private theorem norm_eq_map_frobenius_of_isReduced {R : Type*} [CommRing R] [IsReduced R]
    [CharP R p] (f : R⟦X⟧) : norm p R f = PowerSeries.map (frobenius R p) f := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow : (norm p R f) ^ p = (PowerSeries.map (frobenius R p) f) ^ p := by
    rw [← map_pow (norm p R), ← PowerSeries.map_frobenius_expand p hp, PowerSeries.map_expand,
      ← frobeniusHom_eq_expand (CharP.cast_eq_zero R p), norm_frobeniusHom]
  rw [← PowerSeries.map_frobenius_expand p hp, ← PowerSeries.map_frobenius_expand p hp] at hpow
  exact PowerSeries.expand_injective p hp (PowerSeries.map_injective _ (frobenius_inj R p) hpow)

/-- Over any commutative ring of characteristic `p`, `norm` is coefficientwise Frobenius. -/
theorem norm_eq_map_frobenius {R : Type*} [CommRing R] [CharP R p] (f : R⟦X⟧) :
    norm p R f = PowerSeries.map (frobenius R p) f := by
  let F : (MvPolynomial ℕ (ZMod p))⟦X⟧ := PowerSeries.mk MvPolynomial.X
  let φ : MvPolynomial ℕ (ZMod p) →+* R :=
    MvPolynomial.eval₂Hom (ZMod.castHom dvd_rfl R) (fun n ↦ coeff n f)
  have hF : PowerSeries.map φ F = f := ext fun n ↦ by
    rw [coeff_map, coeff_mk, MvPolynomial.eval₂Hom_X']
  have hc : φ.comp (frobenius _ p) = (frobenius R p).comp φ :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, frobenius_def, map_pow]
  have h := congrArg (PowerSeries.map φ) (norm_eq_map_frobenius_of_isReduced (p := p) F)
  rwa [map_norm φ F, hF, ← RingHom.comp_apply, ← PowerSeries.map_comp, hc,
    PowerSeries.map_comp, RingHom.comp_apply, hF] at h

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Coleman's norm preserves congruences modulo `(p) ^ k`. -/
theorem norm_sub_norm_mem_span_pow {k : ℕ} {f g : O⟦X⟧}
    (hfg : f - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O f - norm p O g ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set q : O⟦X⟧ →+* O⟦X⟧ ⧸ Ideal.span {(p : O⟦X⟧)} ^ k := Ideal.Quotient.mk _
  rw [map_sub, sub_eq_zero, norm_eq_det_leftMulMatrix, norm_eq_det_leftMulMatrix,
    RingHom.map_det, RingHom.map_det]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hfg)
  have hpk : q (C ((p : O) ^ k)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr <| by
    rw [map_pow, map_natCast]; exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
  have hf : f = g + C ((p : O) ^ k) * h := by rw [map_pow, map_natCast, ← hh]; ring
  have hcoord (r : Fin p) : q (coord p O r f) = q (coord p O r g) := by
    rw [hf, map_add, coord_C_mul, map_add, map_mul, hpk, zero_mul, add_zero]
  congr 1; refine Matrix.ext fun i j ↦ ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leftMulMatrix_apply]
  split_ifs <;> simp [hcoord]

/-- **Contraction near `1`.** For `k ≥ 1` and `h ∈ O⟦X⟧`, `N(1 + p ^ k * h) ≡ 1 (mod p ^ (k + 1))`
for all primes `p` including `p = 2` (Coleman Lemma 13; Sharifi Prop. 5.4.6; RJW Lemma 10.11). -/
theorem norm_one_add_sub_one_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) (h : O⟦X⟧) :
    norm p O (1 + (p : O⟦X⟧) ^ k * h) - 1 ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  obtain ⟨r, hr⟩ := norm_one_add_frobeniusHom_mul (p := p) ((p : O⟦X⟧) ^ k) h
  rw [map_pow, map_natCast] at hr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨coord p O ⟨0, (Fact.out : p.Prime).pos⟩ h + r * (p : O⟦X⟧) ^ (k - 1), ?_⟩
  rw [hr, trace_eq_p_mul_coord_zero]
  have hk' : (p : O⟦X⟧) ^ (k + 1) * (p : O⟦X⟧) ^ (k - 1) = ((p : O⟦X⟧) ^ k) ^ 2 := by
    rw [← pow_add, ← pow_mul]; congr 1; omega
  rw [mul_add, mul_left_comm _ r, hk', pow_succ']; ring

/-- **Contraction at units.** For `k ≥ 1` and `IsUnit g`, if `f ≡ g (mod p ^ k)` then
`N(f) ≡ N(g) (mod p ^ (k + 1))` (Coleman Lemma 13; Sharifi Cor. 5.4.7; RJW Lemma 10.11). -/
theorem norm_sub_norm_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) {f g : O⟦X⟧} (hg : IsUnit g)
    (hfg : f - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O f - norm p O g ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hfg)
  have hf_eq : f = (u : O⟦X⟧) * (1 + (p : O⟦X⟧) ^ k * ((u⁻¹ : O⟦X⟧ˣ) * d)) := by
    rw [mul_add, mul_one, mul_left_comm, ← mul_assoc (u : O⟦X⟧), Units.mul_inv, one_mul, ← hd]
    ring
  have hnorm_eq : norm p O f - norm p O (u : O⟦X⟧) =
      norm p O (u : O⟦X⟧) * (norm p O (1 + (p : O⟦X⟧) ^ k * ((u⁻¹ : O⟦X⟧ˣ) * d)) - 1) := by
    rw [hf_eq, map_mul]; ring
  rw [hnorm_eq]
  exact Ideal.mul_mem_left _ _ (norm_one_add_sub_one_mem_span_pow_succ hk _)

/-- **Mod-`p` Frobenius congruence.** If `σ : O →+* O` lifts Frobenius modulo `(p)`, then
`N(f) ≡ σ(f) (mod p)` (Coleman §IV eq. (2); Sharifi Prop. 5.4.6; RJW Prop. 10.10). -/
theorem norm_sub_map_mem_span_p (σ : O →+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧) :
    norm p O f - PowerSeries.map σ f ∈ Ideal.span {(p : O⟦X⟧)} := by
  set q : O →+* O ⧸ Ideal.span {(p : O)} := Ideal.Quotient.mk _
  rw [← pow_one (Ideal.span {(p : O⟦X⟧)}), ← map_natCast (C : O →+* O⟦X⟧),
    PowerSeries.mem_span_C_pow_iff]
  intro n; rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
  nontriviality O ⧸ Ideal.span {(p : O)}
  have : CharP (O ⧸ Ideal.span {(p : O)}) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr <| by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hq : (frobenius (O ⧸ Ideal.span {(p : O)}) p).comp q = q.comp σ :=
    RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, frobenius_def, ← map_pow]
      exact (Ideal.Quotient.eq.mpr (hσ c)).symm
  have hmap : PowerSeries.map q (norm p O f) = PowerSeries.map q (PowerSeries.map σ f) := by
    rw [map_norm q f, norm_eq_map_frobenius, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      ← RingHom.comp_apply, ← PowerSeries.map_comp, hq]
  rw [map_sub, map_sub, ← coeff_map, hmap, coeff_map, sub_self]

end Congruences

section CorrectedNorm

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The corrected Coleman norm `N_σ : O⟦X⟧ˣ →* O⟦X⟧ˣ` sending `f` to `σ⁻¹(N(f))`. Inherits the
prime `p` and `(p)`-adic completeness hypotheses from `Coleman.normUnits` so `N` has no
non-finite-free fallback. -/
def correctedNorm (σ : O ≃+* O) : O⟦X⟧ˣ →* O⟦X⟧ˣ :=
  (Units.map (PowerSeries.map σ.symm.toRingHom).toMonoidHom).comp (normUnits p O)

/-- The subgroup of units of `O⟦X⟧` fixed by `correctedNorm p O σ`, under the supported prime `p`
and `(p)`-adic completeness hypotheses of `Coleman.normUnits`. -/
def fixedUnits (σ : O ≃+* O) : Subgroup O⟦X⟧ˣ :=
  (correctedNorm p O σ).eqLocus (MonoidHom.id O⟦X⟧ˣ)

variable {p O}

/-- The underlying power series of `correctedNorm p O σ f` is `σ⁻¹(N(f))`. -/
@[simp]
theorem coe_correctedNorm (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    (correctedNorm p O σ f : O⟦X⟧) = PowerSeries.map σ.symm.toRingHom (norm p O (f : O⟦X⟧)) := by
  simp [correctedNorm]

/-- Membership in `fixedUnits p O σ` is equality `correctedNorm p O σ f = f`. -/
@[simp]
theorem mem_fixedUnits_iff (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    f ∈ fixedUnits p O σ ↔ correctedNorm p O σ f = f := Iff.rfl

/-- A unit `f ∈ O⟦X⟧ˣ` is fixed by `correctedNorm p O σ` iff `N(f) = σ(f)`. -/
theorem mem_fixedUnits_iff_norm_eq_map (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    f ∈ fixedUnits p O σ ↔ norm p O (f : O⟦X⟧) = PowerSeries.map σ.toRingHom (f : O⟦X⟧) := by
  rw [mem_fixedUnits_iff, Units.ext_iff, coe_correctedNorm]
  have hinv (τ₁ τ₂ : O →+* O) (h : τ₁.comp τ₂ = RingHom.id O) (x : O⟦X⟧) :
      PowerSeries.map τ₁ (PowerSeries.map τ₂ x) = x := by
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp, h, PowerSeries.map_id, id_eq]
  exact ⟨fun h ↦ by conv_rhs => rw [← h]; rw [hinv _ _ σ.toRingHom_comp_symm_toRingHom],
    fun h ↦ by rw [h, hinv _ _ σ.symm_toRingHom_comp_toRingHom]⟩

/-- A constant unit `Units.map C u` is fixed by `correctedNorm p O σ` iff `σ u = u ^ p`. -/
theorem unitsMap_C_mem_fixedUnits_iff (σ : O ≃+* O) (u : Oˣ) :
    Units.map (C : O →+* O⟦X⟧).toMonoidHom u ∈ fixedUnits p O σ ↔ σ u = (u : O) ^ p := by
  rw [mem_fixedUnits_iff_norm_eq_map, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, norm_C, map_C]
  exact ⟨fun h ↦ (C_injective h).symm, fun h ↦ congrArg C h.symm⟩

section Projector

/-- `correctedNorm p O σ` contracts congruences modulo `(p) ^ k` (`k ≥ 1`) to `(p) ^ (k + 1)`. -/
theorem correctedNorm_sub_correctedNorm_mem_span_pow_succ (σ : O ≃+* O) {k : ℕ} (hk : 1 ≤ k)
    {f g : O⟦X⟧ˣ} (hfg : (f : O⟦X⟧) - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    (correctedNorm p O σ f : O⟦X⟧) - (correctedNorm p O σ g : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  rw [coe_correctedNorm, coe_correctedNorm, ← map_sub]
  have h := norm_sub_norm_mem_span_pow_succ hk g.isUnit hfg
  rw [← map_natCast (C : O →+* O⟦X⟧)] at h ⊢
  simpa only [map_natCast] using PowerSeries.map_mem_span_C_pow σ.symm.toRingHom h

/-- For a Frobenius lift `σ`, `N_σ(f) ≡ f (mod p)` for every unit `f ∈ O⟦X⟧ˣ`. -/
theorem correctedNorm_sub_self_mem_span_p (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    (correctedNorm p O σ f : O⟦X⟧) - (f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} := by
  have h := PowerSeries.map_mem_span_C_pow σ.symm.toRingHom (k := 1)
    (by rw [pow_one, map_natCast]; exact norm_sub_map_mem_span_p σ.toRingHom hσ f)
  simpa only [coe_correctedNorm, pow_one, map_natCast, map_sub, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, σ.symm_toRingHom_comp_toRingHom, PowerSeries.map_id, id_eq] using h

/-- Successive iterates satisfy `N_σ^[n + 1](f) ≡ N_σ^[n](f) (mod p ^ (n + 1))`. -/
theorem iterate_correctedNorm_succ_sub_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  induction n with
  | zero => simpa [pow_one] using correctedNorm_sub_self_mem_span_p σ hσ f
  | succ n ih =>
    simpa only [← Function.iterate_succ_apply'] using
      correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n) ih

/-- For `m ≤ n`, `N_σ^[n](f) ≡ N_σ^[m](f) (mod p ^ (m + 1))`. -/
theorem iterate_correctedNorm_sub_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) {m n : ℕ} (hmn : m ≤ n) :
    (((correctedNorm p O σ)^[n]) f : O⟦X⟧) - (((correctedNorm p O σ)^[m]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (m + 1) := by
  induction hmn with
  | refl => simp
  | @step n hmn ih =>
    simpa only [sub_add_sub_cancel] using add_mem
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)
        (iterate_correctedNorm_succ_sub_mem_span_pow σ hσ f n)) ih

private theorem exists_normProjector_series (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    ∃ g : O⟦X⟧, ∀ n : ℕ,
      g - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  have hc : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  obtain ⟨g, hg⟩ := hc.prec (f := fun n ↦ (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) fun {m n} hmn ↦ by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact Ideal.pow_le_pow_right (Nat.le_succ m)
      (iterate_correctedNorm_sub_mem_span_pow σ hσ f hmn)
  exact ⟨g, fun n ↦ by
    have h1 := hg (n + 1)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub] at h1
    simpa only [sub_add_sub_cancel] using
      add_mem h1 (iterate_correctedNorm_succ_sub_mem_span_pow σ hσ f n)⟩

private def normProjectorSeries (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) : O⟦X⟧ :=
  (exists_normProjector_series σ hσ f).choose

private theorem normProjectorSeries_sub_iterate (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    normProjectorSeries p O σ hσ f - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) :=
  (exists_normProjector_series σ hσ f).choose_spec n

private theorem normProjectorSeries_mul (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f g : O⟦X⟧ˣ) :
    normProjectorSeries p O σ hσ (f * g) =
      normProjectorSeries p O σ hσ f * normProjectorSeries p O σ hσ g := by
  have : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  set q : O⟦X⟧ →+* O⟦X⟧ ⧸ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := Ideal.Quotient.mk _
  have hfg : q (normProjectorSeries p O σ hσ (f * g)) =
      q ((((correctedNorm p O σ)^[n]) f : O⟦X⟧) * (((correctedNorm p O σ)^[n]) g : O⟦X⟧)) := by
    have hmem := normProjectorSeries_sub_iterate σ hσ (f * g) n
    rw [iterate_map_mul, Units.val_mul] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hf : q (normProjectorSeries p O σ hσ f) = q (((correctedNorm p O σ)^[n]) f : O⟦X⟧) :=
    Ideal.Quotient.eq.mpr (normProjectorSeries_sub_iterate σ hσ f n)
  have hg : q (normProjectorSeries p O σ hσ g) = q (((correctedNorm p O σ)^[n]) g : O⟦X⟧) :=
    Ideal.Quotient.eq.mpr (normProjectorSeries_sub_iterate σ hσ g n)
  rw [hfg, map_mul, map_mul, hf, hg]

private theorem normProjectorSeries_one (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    normProjectorSeries p O σ hσ 1 = 1 := by
  have : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  simpa only [iterate_map_one, Units.val_one] using normProjectorSeries_sub_iterate σ hσ 1 n

variable (p O)

/-- **Coleman's corrected-norm projector.** For `(p)`-adically complete `O` and Frobenius lift
`σ : O ≃+* O`, the multiplicative idempotent retraction `O⟦X⟧ˣ →* O⟦X⟧ˣ` onto `fixedUnits p O σ`
(Coleman Prop. 14; Sharifi Thm. 5.4.9; RJW Prop. 10.12 / Thm. 10.13). -/
def normProjector (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    O⟦X⟧ˣ →* O⟦X⟧ˣ where
  toFun f :=
    { val := normProjectorSeries p O σ hσ f
      inv := normProjectorSeries p O σ hσ f⁻¹
      val_inv := by rw [← normProjectorSeries_mul, mul_inv_cancel, normProjectorSeries_one]
      inv_val := by rw [← normProjectorSeries_mul, inv_mul_cancel, normProjectorSeries_one] }
  map_one' := Units.ext (normProjectorSeries_one σ hσ)
  map_mul' f g := Units.ext (normProjectorSeries_mul σ hσ f g)

variable {p O}

/-- **Uniform `(p)`-adic precision:** `normProjector f ≡ N_σ^[n](f) (mod p ^ (n + 1))`. -/
theorem normProjector_sub_iterate_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    (normProjector p O σ hσ f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) :=
  normProjectorSeries_sub_iterate σ hσ f n

/-- **Uniqueness:** `g = normProjector f` iff `g ≡ N_σ^[n](f) (mod p ^ (n + 1))` for all `n`. -/
theorem eq_normProjector_iff (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) {f g : O⟦X⟧ˣ} :
    g = normProjector p O σ hσ f ↔
      ∀ n : ℕ, (g : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
        Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  have : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  refine ⟨fun h n ↦ h ▸ normProjector_sub_iterate_mem_span_pow σ hσ f n, fun h ↦
    Units.ext ((IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_)⟩
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  simpa only [sub_sub_sub_cancel_right] using
    sub_mem (h n) (normProjector_sub_iterate_mem_span_pow σ hσ f n)

/-- Every value of `normProjector` is fixed by `correctedNorm`. -/
@[simp]
theorem correctedNorm_normProjector (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    correctedNorm p O σ (normProjector p O σ hσ f) = normProjector p O σ hσ f := by
  have : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  refine Units.ext ((IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have h1 := correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n)
    (normProjector_sub_iterate_mem_span_pow σ hσ f n)
  rw [← Function.iterate_succ_apply' (correctedNorm p O σ) n f] at h1
  simpa only [sub_sub_sub_cancel_right] using Ideal.pow_le_pow_right (Nat.le_add_right n 2)
    (sub_mem h1 (normProjector_sub_iterate_mem_span_pow σ hσ f (n + 1)))

/-- Applying `correctedNorm` before `normProjector` leaves the projection unchanged. -/
@[simp]
theorem normProjector_correctedNorm (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    normProjector p O σ hσ (correctedNorm p O σ f) = normProjector p O σ hσ f :=
  ((eq_normProjector_iff σ hσ).mpr fun n ↦ by
    rw [← Function.iterate_succ_apply]
    exact Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
      (normProjector_sub_iterate_mem_span_pow σ hσ f (n + 1))).symm

/-- Every value of `normProjector` lies in `fixedUnits p O σ`. -/
theorem normProjector_mem_fixedUnits (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    normProjector p O σ hσ f ∈ fixedUnits p O σ :=
  correctedNorm_normProjector σ hσ f

/-- `normProjector` fixes every fixed point of `correctedNorm`. -/
theorem normProjector_eq_self (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) {f : O⟦X⟧ˣ}
    (hf : correctedNorm p O σ f = f) :
    normProjector p O σ hσ f = f := by
  have : IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
    (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)
  refine Units.ext ((IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have hiter : ((correctedNorm p O σ)^[n]) f = f := Function.IsFixedPt.iterate hf n
  simpa only [hiter] using normProjector_sub_iterate_mem_span_pow σ hσ f n

/-- `normProjector` is idempotent. -/
@[simp]
theorem normProjector_idem (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    normProjector p O σ hσ (normProjector p O σ hσ f) = normProjector p O σ hσ f :=
  normProjector_eq_self σ hσ (correctedNorm_normProjector σ hσ f)

/-- The range of `normProjector p O σ hσ` is `fixedUnits p O σ`. -/
@[simp]
theorem range_normProjector (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    Set.range (normProjector p O σ hσ) = (fixedUnits p O σ : Set O⟦X⟧ˣ) := by
  ext f
  exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ normProjector_mem_fixedUnits σ hσ g,
    fun hf ↦ ⟨f, normProjector_eq_self σ hσ hf⟩⟩

private theorem coeff_normProjector_sub_iterate_mem (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n d : ℕ) :
    coeff d (normProjector p O σ hσ f : O⟦X⟧) -
        coeff d (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈ Ideal.span {(p : O)} ^ (n + 1) := by
  have h := normProjector_sub_iterate_mem_span_pow σ hσ f n
  rw [← map_natCast (C : O →+* O⟦X⟧), PowerSeries.mem_span_C_pow_iff] at h
  rw [← map_sub]; exact h d

end Projector

end CorrectedNorm

section Topology

open scoped PowerSeries.WithPiTopology Topology

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
variable [TopologicalSpace O] [IsTopologicalRing O]

/-- `correctedNorm p O σ` is continuous for the coefficientwise topology on `O⟦X⟧` when `O` has
its `(p)`-adic topology. -/
theorem continuous_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)})) (σ : O ≃+* O) :
    Continuous (correctedNorm p O σ) :=
  (Units.continuous_map (PowerSeries.WithPiTopology.continuous_map
    (hAdic.continuous_of_span_natCast hAdic σ.symm.toRingHom))).comp (continuous_normUnits hAdic)

/-- The fixed subgroup `fixedUnits p O σ` is closed in `O⟦X⟧ˣ` when `O` is Hausdorff with the
`(p)`-adic topology. -/
theorem isClosed_fixedUnits [T2Space O] (hAdic : IsAdic (Ideal.span {(p : O)})) (σ : O ≃+* O) :
    IsClosed (fixedUnits p O σ : Set O⟦X⟧ˣ) :=
  isClosed_eq (continuous_correctedNorm hAdic σ) continuous_id

/-- The fixed subgroup `fixedUnits p O σ` is compact in `O⟦X⟧ˣ` when `O` is compact Hausdorff
with the `(p)`-adic topology. -/
theorem isCompact_fixedUnits [CompactSpace O] [T2Space O] (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) : IsCompact (fixedUnits p O σ : Set O⟦X⟧ˣ) :=
  (isClosed_fixedUnits hAdic σ).isCompact

private theorem tendsto_val_iterate_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    Filter.Tendsto (fun n : ℕ ↦ (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) Filter.atTop
      (𝓝 (normProjector p O σ hσ f : O⟦X⟧)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_sub_nhds_zero_iff.mp <|
    hAdic.hasBasis_nhds_zero.tendsto_right_iff.mpr fun k _ ↦
      Filter.eventually_atTop.mpr ⟨k, fun n hkn ↦ ?_⟩
  rw [SetLike.mem_coe, ← neg_mem_iff, neg_sub]
  exact Ideal.pow_le_pow_right (by omega) (coeff_normProjector_sub_iterate_mem σ hσ f n d)

/-- **Topological convergence:** `((correctedNorm p O σ)^[n]) f → normProjector p O σ hσ f`. -/
theorem tendsto_iterate_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    Filter.Tendsto (fun n : ℕ ↦ ((correctedNorm p O σ)^[n]) f) Filter.atTop
      (𝓝 (normProjector p O σ hσ f)) := by
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff, nhds_prod_eq, Filter.tendsto_prod_iff']
  refine ⟨tendsto_val_iterate_correctedNorm hAdic σ hσ f,
    MulOpposite.continuous_op.continuousAt.tendsto.comp ?_⟩
  simpa only [← iterate_map_inv (correctedNorm p O σ), ← map_inv] using
    tendsto_val_iterate_correctedNorm hAdic σ hσ f⁻¹

private theorem continuous_val_normProjector (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    Continuous fun f : O⟦X⟧ˣ ↦ (normProjector p O σ hσ f : O⟦X⟧) := by
  refine continuous_iff_continuousAt.mpr fun f₀ ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun d ↦
      tendsto_sub_nhds_zero_iff.mp <|
        hAdic.hasBasis_nhds_zero.tendsto_right_iff.mpr fun k _ ↦ ?_
  have hg : Continuous fun f : O⟦X⟧ˣ ↦ coeff d (((correctedNorm p O σ)^[k]) f : O⟦X⟧) :=
    (PowerSeries.WithPiTopology.continuous_coeff O d).comp
      (Units.continuous_val.comp ((continuous_correctedNorm hAdic σ).iterate k))
  refine Filter.mem_of_superset ((tendsto_sub_nhds_zero_iff.mpr (hg.continuousAt (x := f₀)))
    (hAdic.hasBasis_nhds_zero.mem_of_mem (i := k) trivial)) fun f hf ↦ ?_
  have hL u := Ideal.pow_le_pow_right (Nat.le_succ k)
    (coeff_normProjector_sub_iterate_mem σ hσ u k d)
  simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, sub_add_sub_cancel,
    sub_sub_sub_cancel_right] using sub_mem (add_mem (hL f) hf) (hL f₀)

/-- **Continuity of Coleman's norm projector** for the coefficientwise topology on `O⟦X⟧` when `O`
has its `(p)`-adic topology. -/
theorem continuous_normProjector (hAdic : IsAdic (Ideal.span {(p : O)})) (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    Continuous (normProjector p O σ hσ) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_val_normProjector hAdic σ hσ, by
    simpa only [Function.comp_def, ← map_inv] using
      (continuous_val_normProjector hAdic σ hσ).comp continuous_inv⟩

end Topology

section Examples

open scoped PowerSeries.WithPiTopology Topology

example (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsLocalRing.maximalIdeal O = Ideal.span {(p : O)}) (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, IsLocalRing.residue O (σ c) = IsLocalRing.residue O c ^ p) :
    ∃ L : O⟦X⟧ˣ →* O⟦X⟧ˣ, Continuous L ∧ (∀ f, correctedNorm p O σ (L f) = L f) ∧
      (∀ f, correctedNorm p O σ f = f → L f = f) ∧
      (∀ f, Filter.Tendsto (fun n : ℕ ↦ ((correctedNorm p O σ)^[n]) f) Filter.atTop (𝓝 (L f))) := by
  have hσ' : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)} := fun c ↦ by
    rw [← hO, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hσ c, sub_self]
  exact ⟨normProjector p O σ hσ', continuous_normProjector hAdic σ hσ',
    correctedNorm_normProjector σ hσ', fun _ ↦ normProjector_eq_self σ hσ',
    tendsto_iterate_correctedNorm hAdic σ hσ'⟩

end Examples

end TauCeti.Coleman
