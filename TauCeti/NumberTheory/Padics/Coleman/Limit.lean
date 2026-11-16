/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.NumberTheory.Padics.Coleman.Norm

import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Congruences, continuity, and the Coleman norm projector

Let `p` be a prime and `O` a `(p)`-adically complete commutative ring. Building on Coleman's
norm `N` and trace `τ` in `TauCeti.NumberTheory.Padics.Coleman.Norm`, this file establishes:

1. **Mod-`p^k` congruences for `N`.** For every `k ≥ 1` and units `f, g ∈ O⟦X⟧ˣ` with
   `f ≡ g (mod p ^ k)`, we have `N(f) ≡ N(g) (mod p ^ (k + 1))` (uniformly for all primes,
   including `p = 2`). Over a reduced characteristic-`p` ring `R`, `N(f)` equals coefficientwise
   Frobenius `PowerSeries.map (frobenius R p) f`; hence whenever `O ⧸ (p)` is reduced and
   `σ : O →+* O` lifts Frobenius modulo `(p)`, `N(f) ≡ σ(f) (mod p)`.
2. **Corrected norm and algebraic projector.** For a Frobenius-lifting automorphism `σ : O ≃+* O`,
   the corrected norm `N_σ(f) = σ⁻¹(N(f))` on `O⟦X⟧ˣ` is `(p)`-adically contractive, yielding a
   multiplicative idempotent retraction `normProjector : O⟦X⟧ˣ →* O⟦X⟧ˣ` onto `fixedUnits p O σ`
   with `L(f) ≡ N_σ^[n](f) (mod p ^ (n + 1))`, needing no topology or compactness on `O`.
3. **Continuity and topological convergence.** When `O` carries the `(p)`-adic topology
   (`IsAdic (Ideal.span {(p : O)})`), `PowerSeries.WithPiTopology` makes `coord`, `norm`, `trace`,
   `correctedNorm`, and `normProjector` continuous, `N_σ^[n](f) → normProjector f` in `O⟦X⟧ˣ`,
   and `fixedUnits p O σ` is compact when `O` is compact Hausdorff.

## Main definitions

* `TauCeti.Coleman.correctedNorm`: the corrected norm `f ↦ σ⁻¹(N(f))` on `O⟦X⟧ˣ`.
* `TauCeti.Coleman.fixedUnits`: the subgroup `{f ∈ O⟦X⟧ˣ | correctedNorm p O σ f = f}`.
* `TauCeti.Coleman.normProjector`: the multiplicative retraction `O⟦X⟧ˣ →* O⟦X⟧ˣ` onto
  `fixedUnits p O σ`.

## Main results

* `TauCeti.Coleman.norm_sub_norm_mem_span_pow_succ`, `TauCeti.Coleman.norm_eq_map_frobenius`,
  `TauCeti.Coleman.norm_sub_map_mem_span_p`: contraction on units and mod-`p` Frobenius congruence.
* `TauCeti.Coleman.normProjector_sub_iterate_mem_span_pow`,
  `TauCeti.Coleman.correctedNorm_normProjector`, `TauCeti.Coleman.normProjector_eq_self`:
  algebraic precision and retraction properties of `normProjector`.
* `TauCeti.Coleman.continuous_coord`, `TauCeti.Coleman.continuous_norm`,
  `TauCeti.Coleman.continuous_trace`, `TauCeti.Coleman.continuous_correctedNorm`,
  `TauCeti.Coleman.tendsto_iterate_correctedNorm`, `TauCeti.Coleman.continuous_normProjector`,
  `TauCeti.Coleman.isCompact_fixedUnits`: continuity, convergence, and compactness.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §II.
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §3.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §3.5.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section Congruences

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]

omit [Fact p.Prime] in
/-- A power series lies in `(p) ^ k` in `O⟦X⟧` iff every coefficient lies in `(p) ^ k` in `O`. -/
private theorem mem_span_p_pow_iff_forall_coeff (k : ℕ) (f : O⟦X⟧) :
    f ∈ Ideal.span {(p : O⟦X⟧)} ^ k ↔ ∀ n : ℕ, coeff n f ∈ Ideal.span {(p : O)} ^ k := by
  have hspan : Ideal.span {(p : O⟦X⟧)} ^ k = (Ideal.span {(p : O)} ^ k).map C := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      map_pow, map_natCast]
  rw [hspan]
  refine PowerSeries.mem_map_C_iff_of_fg ?_
  rw [Ideal.span_singleton_pow]; exact ⟨{(p : O) ^ k}, by simp⟩

/-- Over a reduced ring of characteristic `p`, Coleman's norm coincides with coefficientwise
Frobenius. -/
theorem norm_eq_map_frobenius {R : Type*} [CommRing R] [IsReduced R] [CharP R p] (f : R⟦X⟧) :
    norm p R f = PowerSeries.map (frobenius R p) f := by
  have hp_zero : (p : R) = 0 := CharP.cast_eq_zero R p
  have : IsAdicComplete (Ideal.span {(p : R)}) R := by
    rw [hp_zero, Ideal.span_singleton_zero]; exact {}
  have hp_ne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow_eq : (norm p R f) ^ p = (PowerSeries.map (frobenius R p) f) ^ p := by
    calc (norm p R f) ^ p
        = norm p R (f ^ p) := (map_pow (norm p R) f p).symm
      _ = norm p R ((f.expand p hp_ne).map (frobenius R p)) := by
          rw [PowerSeries.map_frobenius_expand p hp_ne]
      _ = norm p R ((PowerSeries.map (frobenius R p) f).expand p hp_ne) := by
          rw [PowerSeries.map_expand]
      _ = norm p R (frobeniusHom p R (PowerSeries.map (frobenius R p) f)) := by
          rw [frobeniusHom_eq_expand hp_zero]
      _ = (PowerSeries.map (frobenius R p) f) ^ p := norm_frobeniusHom _
  have : CharP R⟦X⟧ p := ⟨fun n ↦ by
    rw [← map_natCast (C : R →+* R⟦X⟧), ← map_zero C, C_injective.eq_iff,
      CharP.cast_eq_zero_iff R p]⟩
  have hh : (norm p R f - PowerSeries.map (frobenius R p) f) ^ p = 0 := by
    rw [sub_pow_char, hpow_eq, sub_self]
  refine sub_eq_zero.mp (PowerSeries.ext fun n ↦ ?_)
  rw [map_zero]
  induction n using Nat.strongRecOn with
  | ind n ih =>
    obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.mpr ih
    have hc1 : coeff (p * n) ((X ^ n * g) ^ p) = coeff 0 (g ^ p) := by
      rw [mul_pow, ← pow_mul, mul_comm n p]; simpa using coeff_X_pow_mul (g ^ p) (p * n) 0
    have hc2 : coeff n (X ^ n * g) = coeff 0 g := by simpa using coeff_X_pow_mul g n 0
    exact IsReduced.eq_zero _ ⟨p, by
      rw [hg, hc2, coeff_zero_eq_constantCoeff, ← map_pow, ← coeff_zero_eq_constantCoeff, ← hc1,
        ← hg, hh, map_zero]⟩

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Coleman's norm preserves congruences modulo `(p) ^ k`. -/
theorem norm_sub_norm_mem_span_pow {k : ℕ} {f g : O⟦X⟧}
    (hfg : f - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O f - norm p O g ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  set I : Ideal O⟦X⟧ := Ideal.span {(p : O⟦X⟧)} ^ k
  set q : O⟦X⟧ →+* O⟦X⟧ ⧸ I := Ideal.Quotient.mk I
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, norm_eq_det_leftMulMatrix,
    norm_eq_det_leftMulMatrix, RingHom.map_det, RingHom.map_det]
  congr 1
  obtain ⟨h, hh⟩ :=
    Ideal.mem_span_singleton.mp (by simpa only [I, Ideal.span_singleton_pow] using hfg)
  have hf_eq : f = g + C ((p : O) ^ k) * h := by rw [map_pow, map_natCast, ← hh]; ring
  have hcoord (r : Fin p) : q (coord p O r f) = q (coord p O r g) := by
    rw [hf_eq, map_add, coord_C_mul, map_add, map_mul]
    have hq0 : q (C ((p : O) ^ k)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, map_pow, map_natCast]
      exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
    rw [hq0, zero_mul, add_zero]
  refine Matrix.ext fun i j ↦ ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leftMulMatrix_apply]
  split_ifs
  · exact hcoord _
  · rw [map_mul, map_mul, hcoord]

/-- **Contraction near `1`.** For every `k ≥ 1` and `h ∈ O⟦X⟧`,
`N(1 + p ^ k * h) ≡ 1 (mod p ^ (k + 1))`, uniformly for all primes `p` including `p = 2`. -/
theorem norm_one_add_sub_one_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) (h : O⟦X⟧) :
    norm p O (1 + (p : O⟦X⟧) ^ k * h) - 1 ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  let a : O⟦X⟧ := (p : O⟦X⟧) ^ k
  have ha_frob : frobeniusHom p O a = a := by simp only [a, map_pow, map_natCast]
  obtain ⟨r, hr⟩ := norm_one_add_frobeniusHom_mul (p := p) a h
  rw [ha_frob] at hr
  rw [sub_eq_iff_eq_add.mpr (by rw [hr]; ring :
      norm p O (1 + (p : O⟦X⟧) ^ k * h) = (trace p O h * a + r * a ^ 2) + 1)]
  refine add_mem ?_ ?_
  · rw [trace_eq_p_mul_coord_zero]
    have heq : (p : O⟦X⟧) * coord p O ⟨0, (Fact.out : p.Prime).pos⟩ h * a =
        (p : O⟦X⟧) ^ (k + 1) * coord p O ⟨0, (Fact.out : p.Prime).pos⟩ h := by
      simp only [a, pow_succ']; ring
    rw [heq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · have hsq : a ^ 2 = (p : O⟦X⟧) ^ (2 * k) := by simp only [a, ← pow_mul, mul_comm]
    rw [hsq]
    exact Ideal.mul_mem_left _ r (Ideal.pow_le_pow_right (by omega : k + 1 ≤ 2 * k)
      (Ideal.pow_mem_pow (Ideal.subset_span rfl) (2 * k)))

/-- **Contraction on units.** For every `k ≥ 1` and units `f, g ∈ O⟦X⟧ˣ`, if
`f ≡ g (mod p ^ k)` then `N(f) ≡ N(g) (mod p ^ (k + 1))`. -/
theorem norm_sub_norm_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) {f g : O⟦X⟧ˣ}
    (hfg : (f : O⟦X⟧) - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O (f : O⟦X⟧) - norm p O (g : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hfg)
  have hf_eq : (f : O⟦X⟧) = (g : O⟦X⟧) * (1 + (p : O⟦X⟧) ^ k * ((g⁻¹ : O⟦X⟧ˣ) * d)) := by
    calc (f : O⟦X⟧)
        = (g : O⟦X⟧) + (g : O⟦X⟧) * (g⁻¹ : O⟦X⟧ˣ) * ((p : O⟦X⟧) ^ k * d) := by
          rw [Units.mul_inv, one_mul, ← hd]; ring
      _ = (g : O⟦X⟧) * (1 + (p : O⟦X⟧) ^ k * ((g⁻¹ : O⟦X⟧ˣ) * d)) := by ring
  have hdiff : norm p O (f : O⟦X⟧) - norm p O (g : O⟦X⟧) =
      norm p O (g : O⟦X⟧) * (norm p O (1 + (p : O⟦X⟧) ^ k * ((g⁻¹ : O⟦X⟧ˣ) * d)) - 1) := by
    rw [hf_eq, map_mul]; ring
  rw [hdiff]
  exact Ideal.mul_mem_left _ _ (norm_one_add_sub_one_mem_span_pow_succ hk _)

/-- **Mod-`p` Frobenius congruence for Coleman's norm.** If `O ⧸ (p)` is reduced and
`σ : O →+* O` lifts Frobenius modulo `(p)`, then `N(f) ≡ σ(f) (mod p)` for all `f ∈ O⟦X⟧`. -/
theorem norm_sub_map_mem_span_p [IsReduced (O ⧸ Ideal.span {(p : O)})] (σ : O →+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧) :
    norm p O f - PowerSeries.map σ f ∈ Ideal.span {(p : O⟦X⟧)} := by
  set I : Ideal O := Ideal.span {(p : O)}
  set R := O ⧸ I
  set q : O →+* R := Ideal.Quotient.mk I
  rw [← pow_one (Ideal.span {(p : O⟦X⟧)}), mem_span_p_pow_iff_forall_coeff]
  intro n
  rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
  by_cases hnt : Nontrivial R
  · have hp0 : (p : R) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
    have : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
    have : IsAdicComplete (Ideal.span {(p : R)}) R := by
      rw [hp0, Ideal.span_singleton_zero]; exact {}
    have hq_comp : (frobenius R p).comp q = q.comp σ := RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, frobenius_def, ← map_pow]
      exact (Ideal.Quotient.eq.mpr (hσ c)).symm
    have hmap : PowerSeries.map q (norm p O f) = PowerSeries.map q (PowerSeries.map σ f) := by
      rw [map_norm q f, norm_eq_map_frobenius, ← RingHom.comp_apply, ← PowerSeries.map_comp,
        ← RingHom.comp_apply, ← PowerSeries.map_comp, hq_comp]
    have hcoeff := congrArg (coeff n) hmap
    simp only [coeff_map] at hcoeff
    rw [map_sub, coeff_map, map_sub, hcoeff, sub_self]
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact Subsingleton.elim _ _

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O] in
/-- If `O` is a local ring whose maximal ideal is generated by `p`, then `O ⧸ (p)` is a field
and hence reduced. -/
theorem isReduced_quotient_span_p_of_maximalIdeal [IsLocalRing O]
    (hO : IsLocalRing.maximalIdeal O = Ideal.span {(p : O)}) :
    IsReduced (O ⧸ Ideal.span {(p : O)}) := by
  rw [← hO]; infer_instance

end Congruences

section CorrectedNorm

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The corrected Coleman norm `N_σ : O⟦X⟧ˣ →* O⟦X⟧ˣ` sending `f` to `σ⁻¹(N(f))`. -/
def correctedNorm (σ : O ≃+* O) : O⟦X⟧ˣ →* O⟦X⟧ˣ :=
  (Units.map (PowerSeries.map σ.symm.toRingHom).toMonoidHom).comp (normUnits p O)

/-- The subgroup of units of `O⟦X⟧` fixed by the corrected Coleman norm `N_σ`. -/
def fixedUnits (σ : O ≃+* O) : Subgroup O⟦X⟧ˣ where
  carrier := {f | correctedNorm p O σ f = f}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢; rw [map_mul, hf, hg]
  one_mem' := map_one _
  inv_mem' {f} hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢; rw [map_inv, hf]

variable {p O}

/-- The underlying power series of `correctedNorm p O σ f` is `σ⁻¹(N(f))`. -/
@[simp]
theorem coe_correctedNorm (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    (correctedNorm p O σ f : O⟦X⟧) = PowerSeries.map σ.symm.toRingHom (norm p O (f : O⟦X⟧)) := by
  simp [correctedNorm]

/-- Membership in `fixedUnits p O σ` is equality `correctedNorm p O σ f = f`. -/
@[simp]
theorem mem_fixedUnits_iff (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    f ∈ fixedUnits p O σ ↔ correctedNorm p O σ f = f :=
  Iff.rfl

/-- A unit `f ∈ O⟦X⟧ˣ` is fixed by `correctedNorm p O σ` iff `N(f) = σ(f)`. -/
theorem mem_fixedUnits_iff_norm_eq_map (σ : O ≃+* O) (f : O⟦X⟧ˣ) :
    f ∈ fixedUnits p O σ ↔ norm p O (f : O⟦X⟧) = PowerSeries.map σ.toRingHom (f : O⟦X⟧) := by
  rw [mem_fixedUnits_iff, Units.ext_iff, coe_correctedNorm]
  have h1 : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id O := RingHom.ext σ.apply_symm_apply
  have h2 : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id O := RingHom.ext σ.symm_apply_apply
  exact ⟨fun h ↦ by
      have h' := congrArg (PowerSeries.map σ.toRingHom) h
      rwa [← RingHom.comp_apply, ← PowerSeries.map_comp, h1, PowerSeries.map_id] at h',
    fun h ↦ by
      have h' := congrArg (PowerSeries.map σ.symm.toRingHom) h
      rwa [← RingHom.comp_apply, ← PowerSeries.map_comp, h2, PowerSeries.map_id] at h'⟩

/-- A constant unit `C u` is fixed by `correctedNorm p O σ` iff `σ u = u ^ p`. -/
theorem C_mem_fixedUnits_iff [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (σ : O ≃+* O) (u : Oˣ) :
    Units.map (C : O →+* O⟦X⟧).toMonoidHom u ∈ fixedUnits p O σ ↔ σ u = (u : O) ^ p := by
  have hval : ((Units.map (C : O →+* O⟦X⟧).toMonoidHom u : O⟦X⟧ˣ) : O⟦X⟧) = C (u : O) := rfl
  rw [mem_fixedUnits_iff_norm_eq_map, hval, norm_C, map_C]
  exact ⟨fun h ↦ (C_injective h).symm, fun h ↦ congrArg C h.symm⟩

private theorem map_mem_span_p_pow {k : ℕ} (φ : O →+* O) {f : O⟦X⟧}
    (hf : f ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    PowerSeries.map φ f ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hf)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨PowerSeries.map φ h, by rw [hh, map_mul, map_pow, map_natCast]⟩

section Projector

variable [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- `correctedNorm p O σ` contracts congruences modulo `(p) ^ k` (`k ≥ 1`) to `(p) ^ (k + 1)`. -/
theorem correctedNorm_sub_correctedNorm_mem_span_pow_succ (σ : O ≃+* O) {k : ℕ} (hk : 1 ≤ k)
    {f g : O⟦X⟧ˣ} (hfg : (f : O⟦X⟧) - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    (correctedNorm p O σ f : O⟦X⟧) - (correctedNorm p O σ g : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  rw [coe_correctedNorm, coe_correctedNorm, ← map_sub]
  exact map_mem_span_p_pow σ.symm.toRingHom (norm_sub_norm_mem_span_pow_succ hk hfg)

variable [IsReduced (O ⧸ Ideal.span {(p : O)})]

/-- For a Frobenius lift `σ`, `N_σ(f) ≡ f (mod p)` for every unit `f ∈ O⟦X⟧ˣ`. -/
theorem correctedNorm_sub_self_mem_span_p (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    (correctedNorm p O σ f : O⟦X⟧) - (f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} := by
  have h := map_mem_span_p_pow (k := 1) σ.symm.toRingHom
    (by rw [pow_one]; exact norm_sub_map_mem_span_p σ.toRingHom hσ f)
  have hcomp : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id O := RingHom.ext σ.symm_apply_apply
  rw [pow_one, map_sub, ← RingHom.comp_apply, ← PowerSeries.map_comp, hcomp, PowerSeries.map_id]
    at h
  rw [coe_correctedNorm]; simpa only [id_eq] using h

/-- Successive iterates of `correctedNorm p O σ` satisfy
`N_σ^[n + 1](f) ≡ N_σ^[n](f) (mod p ^ (n + 1))`. -/
theorem iterate_correctedNorm_succ_sub_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  induction n with
  | zero => simpa [pow_one] using correctedNorm_sub_self_mem_span_p σ hσ f
  | succ n ih =>
    rw [Function.iterate_succ_apply' (correctedNorm p O σ) n f] at ih
    rw [Function.iterate_succ_apply' (correctedNorm p O σ) (n + 1) f,
      Function.iterate_succ_apply' (correctedNorm p O σ) n f]
    exact correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n) ih

/-- Iterates of `correctedNorm p O σ` form a `(p)`-adic Cauchy sequence: for `m ≤ n`,
`N_σ^[n](f) ≡ N_σ^[m](f) (mod p ^ (m + 1))`. -/
theorem iterate_correctedNorm_sub_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) {m n : ℕ} (hmn : m ≤ n) :
    (((correctedNorm p O σ)^[n]) f : O⟦X⟧) - (((correctedNorm p O σ)^[m]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (m + 1) := by
  induction hmn with
  | refl => simp
  | @step n hmn ih =>
    have hsplit : (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) -
        (((correctedNorm p O σ)^[m]) f : O⟦X⟧) =
        ((((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) +
        ((((correctedNorm p O σ)^[n]) f : O⟦X⟧) - (((correctedNorm p O σ)^[m]) f : O⟦X⟧)) := by ring
    rw [hsplit]
    exact add_mem (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)
      (iterate_correctedNorm_succ_sub_mem_span_pow σ hσ f n)) ih

private theorem exists_normProjector_series (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    ∃ g : O⟦X⟧, ∀ n : ℕ,
      g - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  set I : Ideal O := Ideal.span {(p : O)}
  have hex (d : ℕ) : ∃ c : O, ∀ n : ℕ,
      coeff d (((correctedNorm p O σ)^[n]) f : O⟦X⟧) - c ∈ I ^ (n + 1) := by
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → SModEq (I ^ m • (⊤ : Submodule O O))
        (coeff d (((correctedNorm p O σ)^[m]) f : O⟦X⟧))
        (coeff d (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) := fun {m _} hmn ↦ by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub, ← map_sub]
      exact Ideal.pow_le_pow_right (Nat.le_succ m)
        ((mem_span_p_pow_iff_forall_coeff (m + 1) _).mp
          (iterate_correctedNorm_sub_mem_span_pow σ hσ f hmn) d)
    obtain ⟨c, hc⟩ := IsPrecomplete.prec (I := I) (M := O) inferInstance hcauchy
    refine ⟨c, fun n ↦ ?_⟩
    have hstep := hc (n + 1); rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hstep
    have hdiff := (mem_span_p_pow_iff_forall_coeff (n + 1) _).mp
      (iterate_correctedNorm_succ_sub_mem_span_pow σ hσ f n) d
    rw [map_sub] at hdiff
    have hsub : coeff d (((correctedNorm p O σ)^[n]) f : O⟦X⟧) - c =
        (coeff d (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) - c) -
        (coeff d (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) -
          coeff d (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) := by ring
    rw [hsub]; exact sub_mem hstep hdiff
  choose c hc using hex
  exact ⟨mk c, fun n ↦ (mem_span_p_pow_iff_forall_coeff (n + 1) _).mpr fun d ↦ by
    rw [map_sub, coeff_mk, ← neg_mem_iff, neg_sub]; exact hc d n⟩

private def normProjectorSeries (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsReduced (O ⧸ Ideal.span {(p : O)})]
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) : O⟦X⟧ :=
  (exists_normProjector_series σ hσ f).choose

private theorem normProjectorSeries_sub_iterate (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    normProjectorSeries p O σ hσ f - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) :=
  (exists_normProjector_series σ hσ f).choose_spec n

omit [Fact p.Prime] [IsReduced (O ⧸ Ideal.span {(p : O)})] in
private theorem eq_of_sub_mem_span_pow {a b : O⟦X⟧}
    (h : ∀ n : ℕ, a - b ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1)) : a = b := by
  ext d; rw [← sub_eq_zero, ← map_sub]
  refine IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance (coeff d (a - b)) fun n ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n)
    ((mem_span_p_pow_iff_forall_coeff (n + 1) _).mp (h n) d)

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [IsReduced (O ⧸ Ideal.span {(p : O)})] in
private theorem iterate_correctedNorm_mul (σ : O ≃+* O) (n : ℕ) (f g : O⟦X⟧ˣ) :
    ((correctedNorm p O σ)^[n]) (f * g) =
      ((correctedNorm p O σ)^[n]) f * ((correctedNorm p O σ)^[n]) g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [IsReduced (O ⧸ Ideal.span {(p : O)})] in
private theorem iterate_correctedNorm_one (σ : O ≃+* O) (n : ℕ) :
    ((correctedNorm p O σ)^[n]) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

private theorem normProjectorSeries_mul (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f g : O⟦X⟧ˣ) :
    normProjectorSeries p O σ hσ (f * g) =
      normProjectorSeries p O σ hσ f * normProjectorSeries p O σ hσ g := by
  refine eq_of_sub_mem_span_pow (p := p) fun n ↦ ?_
  set Lf := normProjectorSeries p O σ hσ f
  set Lg := normProjectorSeries p O σ hσ g
  set Nf : O⟦X⟧ := (((correctedNorm p O σ)^[n]) f : O⟦X⟧)
  set Ng : O⟦X⟧ := (((correctedNorm p O σ)^[n]) g : O⟦X⟧)
  have h1 : normProjectorSeries p O σ hσ (f * g) - Nf * Ng ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
    have hmul : (((correctedNorm p O σ)^[n]) (f * g) : O⟦X⟧) = Nf * Ng := by
      rw [iterate_correctedNorm_mul, Units.val_mul]
    rw [← hmul]; exact normProjectorSeries_sub_iterate σ hσ (f * g) n
  have h2 : Lf * Lg - Nf * Ng ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
    have h2_eq : Lf * Lg - Nf * Ng = (Lf - Nf) * Lg + Nf * (Lg - Ng) := by ring
    rw [h2_eq]
    exact add_mem (Ideal.mul_mem_right _ _ (normProjectorSeries_sub_iterate σ hσ f n))
      (Ideal.mul_mem_left _ _ (normProjectorSeries_sub_iterate σ hσ g n))
  have hdiff_eq : normProjectorSeries p O σ hσ (f * g) - Lf * Lg =
      (normProjectorSeries p O σ hσ (f * g) - Nf * Ng) - (Lf * Lg - Nf * Ng) := by ring
  rw [hdiff_eq]; exact sub_mem h1 h2

private theorem normProjectorSeries_one (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    normProjectorSeries p O σ hσ 1 = 1 :=
  eq_of_sub_mem_span_pow (p := p) fun n ↦ by
    have h := normProjectorSeries_sub_iterate σ hσ 1 n
    rwa [iterate_correctedNorm_one, Units.val_one] at h

variable (p O)

/-- **Coleman's corrected-norm projector.** For a `(p)`-adically complete ring `O` with reduced
quotient `O ⧸ (p)` and Frobenius lift `σ : O ≃+* O`, `normProjector p O σ hσ` is the multiplicative
idempotent retraction `O⟦X⟧ˣ →* O⟦X⟧ˣ` onto `fixedUnits p O σ` obtained as the `(p)`-adic limit of
iterates of `correctedNorm p O σ`. -/
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

/-- **Uniform `(p)`-adic precision of `normProjector`.** For every unit `f ∈ O⟦X⟧ˣ` and `n : ℕ`,
`normProjector f ≡ N_σ^[n](f) (mod p ^ (n + 1))`. -/
theorem normProjector_sub_iterate_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    (normProjector p O σ hσ f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) :=
  normProjectorSeries_sub_iterate σ hσ f n

/-- Every value of `normProjector` is fixed by `correctedNorm`. -/
@[simp]
theorem correctedNorm_normProjector (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    correctedNorm p O σ (normProjector p O σ hσ f) = normProjector p O σ hσ f := by
  refine Units.ext (eq_of_sub_mem_span_pow (p := p) fun n ↦ ?_)
  have h1 : (correctedNorm p O σ (normProjector p O σ hσ f) : O⟦X⟧) -
      (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 2) := by
    rw [Function.iterate_succ_apply']
    exact correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n)
      (normProjector_sub_iterate_mem_span_pow σ hσ f n)
  have hsplit : (correctedNorm p O σ (normProjector p O σ hσ f) : O⟦X⟧) -
      (normProjector p O σ hσ f : O⟦X⟧) =
      ((correctedNorm p O σ (normProjector p O σ hσ f) : O⟦X⟧) -
        (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧)) -
      ((normProjector p O σ hσ f : O⟦X⟧) - (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧)) := by ring
  rw [hsplit]
  exact Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
    (sub_mem h1 (normProjector_sub_iterate_mem_span_pow σ hσ f (n + 1)))

/-- Every value of `normProjector` lies in `fixedUnits p O σ`. -/
theorem normProjector_mem_fixedUnits (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    normProjector p O σ hσ f ∈ fixedUnits p O σ :=
  correctedNorm_normProjector σ hσ f

/-- `normProjector` fixes every fixed point of `correctedNorm`. -/
theorem normProjector_eq_self (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) {f : O⟦X⟧ˣ}
    (hf : correctedNorm p O σ f = f) :
    normProjector p O σ hσ f = f :=
  Units.ext (eq_of_sub_mem_span_pow (p := p) fun n ↦ by
    have hiter : ((correctedNorm p O σ)^[n]) f = f := Function.IsFixedPt.iterate hf n
    simpa only [hiter] using normProjector_sub_iterate_mem_span_pow σ hσ f n)

/-- `normProjector` is idempotent. -/
@[simp]
theorem normProjector_idem (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    normProjector p O σ hσ (normProjector p O σ hσ f) = normProjector p O σ hσ f :=
  normProjector_eq_self σ hσ (correctedNorm_normProjector σ hσ f)

end Projector

end CorrectedNorm

section Topology

open scoped PowerSeries.WithPiTopology Topology

variable {p : ℕ} {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]

/-- Frobenius substitution `Φ` is continuous for the coefficientwise topology on `O⟦X⟧`. -/
theorem continuous_frobeniusHom : Continuous (frobeniusHom p O) := by
  have hfun : (frobeniusHom p O : O⟦X⟧ → O⟦X⟧) = fun f ↦ f.subst ((1 + X : O⟦X⟧) ^ p - 1) :=
    funext frobeniusHom_apply
  rw [hfun]
  exact Continuous.powerSeries_subst continuous_id continuous_const (fun _ ↦ by simp)

variable [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Each Coleman coordinate `coord p O i` is continuous for the coefficientwise `(p)`-adic
topology on `O⟦X⟧`. -/
theorem continuous_coord (hAdic : IsAdic (Ideal.span {(p : O)})) (i : Fin p) :
    Continuous (coord p O i) := by
  refine continuous_of_continuousAt_zero (coord p O i).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [map_zero]
  rw [hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  have hmem : ∀ s ∈ Finset.range (p ^ k * (n + 1)),
      {f : O⟦X⟧ | coeff s f ∈ Ideal.span {(p : O)} ^ k} ∈ 𝓝 (0 : O⟦X⟧) := fun s _ ↦ by
    have h0 : ContinuousAt (coeff s : O⟦X⟧ → O) 0 :=
      (PowerSeries.WithPiTopology.continuous_coeff O s).continuousAt
    rw [ContinuousAt, map_zero] at h0
    exact h0 (hAdic.hasBasis_nhds_zero.mem_of_mem trivial)
  refine Filter.mem_of_superset ((Filter.biInter_finset_mem _).mpr hmem) fun f hf ↦ ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_range] at hf
  exact coeff_coord_mem_pow_of_coeff_mem_pow k hf i

/-- Coleman's trace operator is continuous for the coefficientwise `(p)`-adic topology on `O⟦X⟧`. -/
theorem continuous_trace (hAdic : IsAdic (Ideal.span {(p : O)})) : Continuous (trace p O) := by
  rw [(funext trace_eq_p_mul_coord_zero :
    (trace p O : O⟦X⟧ → O⟦X⟧) = fun f ↦ (p : O⟦X⟧) * coord p O ⟨0, (Fact.out : p.Prime).pos⟩ f)]
  exact continuous_const.mul (continuous_coord hAdic _)

/-- Coleman's norm operator is continuous for the coefficientwise `(p)`-adic topology on `O⟦X⟧`. -/
theorem continuous_norm (hAdic : IsAdic (Ideal.span {(p : O)})) : Continuous (norm p O) := by
  rw [(funext norm_eq_det_leftMulMatrix :
    (norm p O : O⟦X⟧ → O⟦X⟧) = fun f ↦ Matrix.det (leftMulMatrix p O f))]
  have hentry (i j : Fin p) : Continuous fun f : O⟦X⟧ ↦ leftMulMatrix p O f i j := by
    simp_rw [leftMulMatrix_apply]; split_ifs
    · exact continuous_coord hAdic _
    · exact (continuous_coord hAdic _).mul continuous_const
  simp_rw [Matrix.det_apply]
  exact continuous_finsetSum _ fun τ _ ↦
    continuous_const.smul (continuous_finsetProd _ fun j _ ↦ hentry (τ j) j)

/-- Coleman's norm on units is continuous for the coefficientwise `(p)`-adic topology. -/
theorem continuous_normUnits (hAdic : IsAdic (Ideal.span {(p : O)})) :
    Continuous (normUnits p O) := by
  rw [Units.continuous_iff]
  have hval : (Units.val ∘ normUnits p O) = (norm p O ∘ Units.val) := funext coe_normUnits
  have hinv : (fun f : O⟦X⟧ˣ ↦ (((normUnits p O f)⁻¹ : O⟦X⟧ˣ) : O⟦X⟧)) =
      fun f ↦ norm p O (f⁻¹ : O⟦X⟧ˣ) := funext fun f ↦ by rw [← map_inv, coe_normUnits]
  rw [hval, hinv]
  exact ⟨(continuous_norm hAdic).comp Units.continuous_val,
    (continuous_norm hAdic).comp Units.continuous_coe_inv⟩

/-- The corrected Coleman norm `correctedNorm p O σ` is continuous whenever `σ.symm` is
continuous. -/
theorem continuous_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)})) {σ : O ≃+* O}
    (hσi : Continuous σ.symm) : Continuous (correctedNorm p O σ) := by
  have hmap : Continuous (PowerSeries.map σ.symm.toRingHom) :=
    continuous_pi fun d ↦ hσi.comp (continuous_apply d)
  exact (Units.continuous_map hmap).comp (continuous_normUnits hAdic)

/-- The fixed subgroup `fixedUnits p O σ` is closed in `O⟦X⟧ˣ` when `O` is Hausdorff and `σ.symm`
is continuous. -/
theorem isClosed_fixedUnits [T2Space O] (hAdic : IsAdic (Ideal.span {(p : O)})) {σ : O ≃+* O}
    (hσi : Continuous σ.symm) : IsClosed (fixedUnits p O σ : Set O⟦X⟧ˣ) :=
  isClosed_eq (continuous_correctedNorm hAdic hσi) continuous_id

/-- The fixed subgroup `fixedUnits p O σ` is compact in `O⟦X⟧ˣ` when `O` is compact Hausdorff
and `σ.symm` is continuous. -/
theorem isCompact_fixedUnits [CompactSpace O] [T2Space O] (hAdic : IsAdic (Ideal.span {(p : O)}))
    {σ : O ≃+* O} (hσi : Continuous σ.symm) : IsCompact (fixedUnits p O σ : Set O⟦X⟧ˣ) := by
  have : CompactSpace O⟦X⟧ := Pi.compactSpace
  exact (isClosed_fixedUnits hAdic hσi).isCompact

section ProjectorTopology

variable [IsReduced (O ⧸ Ideal.span {(p : O)})]

private theorem tendsto_val_iterate_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    Filter.Tendsto (fun n : ℕ ↦ (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) Filter.atTop
      (𝓝 (normProjector p O σ hσ f : O⟦X⟧)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  rw [← tendsto_sub_nhds_zero_iff, hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  refine Filter.eventually_atTop.mpr ⟨k, fun n hkn ↦ ?_⟩
  rw [SetLike.mem_coe, ← neg_mem_iff, neg_sub, ← map_sub]
  exact Ideal.pow_le_pow_right (Nat.le_trans hkn (Nat.le_succ n))
    ((mem_span_p_pow_iff_forall_coeff (n + 1) _).mp
      (normProjector_sub_iterate_mem_span_pow σ hσ f n) d)

/-- **Topological convergence of corrected-norm iterates.** For every unit `f ∈ O⟦X⟧ˣ`, the
iterates `((correctedNorm p O σ)^[n]) f` converge in `O⟦X⟧ˣ` to `normProjector p O σ hσ f`. -/
theorem tendsto_iterate_correctedNorm (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    Filter.Tendsto (fun n : ℕ ↦ ((correctedNorm p O σ)^[n]) f) Filter.atTop
      (𝓝 (normProjector p O σ hσ f)) := by
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff, nhds_prod_eq, Filter.tendsto_prod_iff']
  refine ⟨tendsto_val_iterate_correctedNorm hAdic σ hσ f, ?_⟩
  have hinv_iter (n : ℕ) : ((((correctedNorm p O σ)^[n]) f)⁻¹ : O⟦X⟧ˣ) =
      ((correctedNorm p O σ)^[n]) f⁻¹ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_inv, ih]
  have hval : Filter.Tendsto (fun n : ℕ ↦ (((((correctedNorm p O σ)^[n]) f)⁻¹ : O⟦X⟧ˣ) : O⟦X⟧))
      Filter.atTop (𝓝 (((normProjector p O σ hσ f)⁻¹ : O⟦X⟧ˣ) : O⟦X⟧)) := by
    simp_rw [hinv_iter, ← map_inv]
    exact tendsto_val_iterate_correctedNorm hAdic σ hσ f⁻¹
  exact MulOpposite.continuous_op.continuousAt.tendsto.comp hval

private theorem continuous_val_normProjector (hAdic : IsAdic (Ideal.span {(p : O)}))
    {σ : O ≃+* O} (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)})
    (hσi : Continuous σ.symm) :
    Continuous fun f : O⟦X⟧ˣ ↦ (normProjector p O σ hσ f : O⟦X⟧) := by
  refine continuous_iff_continuousAt.mpr fun f₀ ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun d ↦ ?_
  rw [← tendsto_sub_nhds_zero_iff, hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  let g : O⟦X⟧ˣ → O⟦X⟧ˣ := (correctedNorm p O σ)^[k]
  have hg_cont : Continuous fun f : O⟦X⟧ˣ ↦ coeff d (g f : O⟦X⟧) :=
    (PowerSeries.WithPiTopology.continuous_coeff O d).comp
      (Units.continuous_val.comp ((continuous_correctedNorm hAdic hσi).iterate k))
  have hnhds : {f : O⟦X⟧ˣ | coeff d (g f : O⟦X⟧) - coeff d (g f₀ : O⟦X⟧) ∈
      Ideal.span {(p : O)} ^ k} ∈ 𝓝 f₀ :=
    (tendsto_sub_nhds_zero_iff.mpr (hg_cont.continuousAt (x := f₀)))
      (hAdic.hasBasis_nhds_zero.mem_of_mem trivial)
  refine Filter.mem_of_superset hnhds fun f hf ↦ ?_
  have hL (u : O⟦X⟧ˣ) : coeff d (normProjector p O σ hσ u : O⟦X⟧) - coeff d (g u : O⟦X⟧) ∈
      Ideal.span {(p : O)} ^ k := by
    rw [← map_sub]
    exact Ideal.pow_le_pow_right (Nat.le_succ k)
      ((mem_span_p_pow_iff_forall_coeff (k + 1) _).mp
        (normProjector_sub_iterate_mem_span_pow σ hσ u k) d)
  simp only [Set.mem_ofPred_eq]
  have hsplit : coeff d (normProjector p O σ hσ f : O⟦X⟧) -
      coeff d (normProjector p O σ hσ f₀ : O⟦X⟧) =
      (coeff d (normProjector p O σ hσ f : O⟦X⟧) - coeff d (g f : O⟦X⟧)) +
      (coeff d (g f : O⟦X⟧) - coeff d (g f₀ : O⟦X⟧)) -
      (coeff d (normProjector p O σ hσ f₀ : O⟦X⟧) - coeff d (g f₀ : O⟦X⟧)) := by ring
  rw [hsplit]; exact sub_mem (add_mem (hL f) hf) (hL f₀)

/-- **Continuity of Coleman's norm projector.** Whenever `O` carries the `(p)`-adic topology and
`σ.symm` is continuous, `normProjector p O σ hσ : O⟦X⟧ˣ →* O⟦X⟧ˣ` is continuous. -/
theorem continuous_normProjector (hAdic : IsAdic (Ideal.span {(p : O)})) {σ : O ≃+* O}
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (hσi : Continuous σ.symm) :
    Continuous (normProjector p O σ hσ) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_val_normProjector hAdic hσ hσi, ?_⟩
  rw [(funext fun f ↦ by rw [← map_inv] :
    (fun f : O⟦X⟧ˣ ↦ (((normProjector p O σ hσ f)⁻¹ : O⟦X⟧ˣ) : O⟦X⟧)) =
      fun f ↦ (normProjector p O σ hσ f⁻¹ : O⟦X⟧))]
  exact (continuous_val_normProjector hAdic hσ hσi).comp continuous_inv

end ProjectorTopology

end Topology

section Examples

open scoped PowerSeries.WithPiTopology Topology

example (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsLocalRing.maximalIdeal O = Ideal.span {(p : O)})
    (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O)
    (hσ : ∀ c : O, IsLocalRing.residue O (σ c) = IsLocalRing.residue O c ^ p)
    (hσi : Continuous σ.symm) :
    ∃ L : O⟦X⟧ˣ →* O⟦X⟧ˣ,
      Continuous L ∧ (∀ f, correctedNorm p O σ (L f) = L f) ∧
      (∀ f, correctedNorm p O σ f = f → L f = f) ∧
      (∀ f, Filter.Tendsto (fun n : ℕ ↦ ((correctedNorm p O σ)^[n]) f) Filter.atTop (𝓝 (L f))) ∧
      (∀ f (n : ℕ), (L f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
        Ideal.span {(p : O⟦X⟧)} ^ (n + 1)) := by
  have : IsReduced (O ⧸ Ideal.span {(p : O)}) := isReduced_quotient_span_p_of_maximalIdeal hO
  have hσ' : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)} := fun c ↦ by
    rw [← hO, ← Ideal.Quotient.eq_zero_iff_mem]
    have hres : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (σ c - c ^ p) =
        IsLocalRing.residue O (σ c - c ^ p) := rfl
    rw [hres, map_sub, map_pow, hσ c, sub_self]; rfl
  exact ⟨normProjector p O σ hσ', continuous_normProjector hAdic hσ' hσi,
    correctedNorm_normProjector σ hσ', fun _ hf ↦ normProjector_eq_self σ hσ' hf,
    tendsto_iterate_correctedNorm hAdic σ hσ', normProjector_sub_iterate_mem_span_pow σ hσ'⟩

end Examples

end TauCeti.Coleman
