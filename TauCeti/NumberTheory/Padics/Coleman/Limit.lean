/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Coleman.Congruences
public import TauCeti.NumberTheory.Padics.Coleman.Topology

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.PiTopology
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Corrected-norm projector and `(p)`-adic convergence

For a prime `p` and `(p)`-adically complete commutative ring `O`, this file establishes:
1. For a Frobenius-lifting automorphism `σ : O ≃+* O`, the corrected norm `N_σ(f) = σ⁻¹(N(f))` and
   the multiplicative idempotent retraction `normProjectorToFixedUnits : O⟦X⟧ˣ →* fixedUnits p O σ`
   (and ambient `normProjector : O⟦X⟧ˣ →* O⟦X⟧ˣ`) with uniform precision
   `normProjector f ≡ N_σ^[n](f) (mod p ^ (n + 1))`, with no topology or compactness on `O`.
2. Continuity of `correctedNorm`, `normProjectorToFixedUnits`, and `normProjector` in the
   coefficientwise topology on `O⟦X⟧` when `O` has its `(p)`-adic topology
   (`IsAdic (Ideal.span {(p : O)})`), convergence `N_σ^[n](f) → normProjector f` in `O⟦X⟧ˣ`,
   closedness of `fixedUnits p O σ` when `O` is Hausdorff with the `(p)`-adic topology, and
   compactness when `O` is compact Hausdorff with the `(p)`-adic topology.

## Main definitions and results

* `TauCeti.Coleman.correctedNorm`, `TauCeti.Coleman.fixedUnits`,
  `TauCeti.Coleman.normProjectorToFixedUnits`, `TauCeti.Coleman.normProjector`,
  `TauCeti.Coleman.coe_normProjectorToFixedUnits`,
  `TauCeti.Coleman.normProjectorToFixedUnits_coe`,
  `TauCeti.Coleman.normProjectorToFixedUnits_comp_subtype`: corrected norm, fixed subgroup, and
  multiplicative retraction onto `fixedUnits p O σ`.
* `TauCeti.Coleman.normProjector_sub_iterate_mem_span_pow`, `TauCeti.Coleman.eq_normProjector_iff`,
  `TauCeti.Coleman.correctedNorm_normProjector`, `TauCeti.Coleman.normProjector_correctedNorm`,
  `TauCeti.Coleman.normProjector_eq_self`, `TauCeti.Coleman.range_normProjector`: precision,
  uniqueness, and algebraic projector properties.
* `TauCeti.Coleman.continuous_correctedNorm`, `TauCeti.Coleman.tendsto_iterate_correctedNorm`,
  `TauCeti.Coleman.continuous_normProjectorToFixedUnits`,
  `TauCeti.Coleman.continuous_normProjector`, `TauCeti.Coleman.isClosed_fixedUnits`,
  `TauCeti.Coleman.isCompact_fixedUnits`: continuity, convergence, closedness, and compactness.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §IV (Prop. 14).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.3.
* R. Sharifi, *Iwasawa Theory*, §5.4 (Cor. 5.4.8, Thm. 5.4.9).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10
  (Prop. 10.12, Thm. 10.13).
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`).
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

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

/-- For a Frobenius lift `σ` modulo `(p)`, successive iterates satisfy
`N_σ^[n + 1](f) ≡ N_σ^[n](f) (mod p ^ (n + 1))`. -/
theorem iterate_correctedNorm_succ_sub_mem_span_pow (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) (n : ℕ) :
    (((correctedNorm p O σ)^[n + 1]) f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  induction n with
  | zero => simpa [pow_one] using correctedNorm_sub_self_mem_span_p σ hσ f
  | succ n ih =>
    simpa only [← Function.iterate_succ_apply'] using
      correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n) ih

/-- For a Frobenius lift `σ` modulo `(p)` and `m ≤ n`,
`N_σ^[n](f) ≡ N_σ^[m](f) (mod p ^ (m + 1))`. -/
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

omit [Fact p.Prime] in
private theorem isAdicComplete_span_p :
    IsAdicComplete (Ideal.span {(p : O⟦X⟧)}) O⟦X⟧ :=
  (map_natCast (C : O →+* O⟦X⟧) p) ▸ PowerSeries.isAdicComplete_span_C (p : O)

omit [Fact p.Prime] in
private theorem eq_of_sub_mem_span_pow {x y : O⟦X⟧}
    (h : ∀ n : ℕ, x - y ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1)) : x = y := by
  have := isAdicComplete_span_p (p := p) (O := O)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O⟦X⟧)})).mpr fun n ↦ ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (h n)

private theorem exists_normProjector_series (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    ∃ g : O⟦X⟧, ∀ n : ℕ,
      g - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈ Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := by
  have hc := isAdicComplete_span_p (p := p) (O := O)
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

private theorem eq_normProjectorSeries_of_sub_iterate (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) {f : O⟦X⟧ˣ} {g : O⟦X⟧}
    (hg : ∀ n : ℕ, g - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1)) :
    g = normProjectorSeries p O σ hσ f :=
  eq_of_sub_mem_span_pow fun n ↦ by
    simpa only [sub_sub_sub_cancel_right] using
      sub_mem (hg n) (normProjectorSeries_sub_iterate σ hσ f n)

private theorem normProjectorSeries_mul (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f g : O⟦X⟧ˣ) :
    normProjectorSeries p O σ hσ (f * g) =
      normProjectorSeries p O σ hσ f * normProjectorSeries p O σ hσ g :=
  (eq_normProjectorSeries_of_sub_iterate σ hσ fun n ↦ by
    rw [iterate_map_mul, Units.val_mul]
    have hsplit : normProjectorSeries p O σ hσ f * normProjectorSeries p O σ hσ g -
        (((correctedNorm p O σ)^[n]) f : O⟦X⟧) * (((correctedNorm p O σ)^[n]) g : O⟦X⟧) =
        (normProjectorSeries p O σ hσ f - (((correctedNorm p O σ)^[n]) f : O⟦X⟧)) *
          normProjectorSeries p O σ hσ g +
        (((correctedNorm p O σ)^[n]) f : O⟦X⟧) *
          (normProjectorSeries p O σ hσ g - (((correctedNorm p O σ)^[n]) g : O⟦X⟧)) := by ring
    exact hsplit ▸ add_mem
      (Ideal.mul_mem_right _ _ (normProjectorSeries_sub_iterate σ hσ f n))
      (Ideal.mul_mem_left _ _ (normProjectorSeries_sub_iterate σ hσ g n))).symm

private theorem normProjectorSeries_one (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    normProjectorSeries p O σ hσ 1 = 1 :=
  (eq_normProjectorSeries_of_sub_iterate σ hσ fun n ↦ by
    simp only [iterate_map_one, Units.val_one, sub_self, zero_mem]).symm

private def normProjectorUnit (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) : O⟦X⟧ˣ →* O⟦X⟧ˣ where
  toFun f :=
    { val := normProjectorSeries p O σ hσ f
      inv := normProjectorSeries p O σ hσ f⁻¹
      val_inv := by rw [← normProjectorSeries_mul, mul_inv_cancel, normProjectorSeries_one]
      inv_val := by rw [← normProjectorSeries_mul, inv_mul_cancel, normProjectorSeries_one] }
  map_one' := Units.ext (normProjectorSeries_one σ hσ)
  map_mul' f g := Units.ext (normProjectorSeries_mul σ hσ f g)

private theorem correctedNorm_normProjectorUnit (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    correctedNorm p O σ (normProjectorUnit σ hσ f) = normProjectorUnit σ hσ f := by
  refine Units.ext (eq_normProjectorSeries_of_sub_iterate σ hσ fun n ↦ ?_)
  have h0 : (normProjectorUnit σ hσ f : O⟦X⟧) - (((correctedNorm p O σ)^[n]) f : O⟦X⟧) ∈
      Ideal.span {(p : O⟦X⟧)} ^ (n + 1) := normProjectorSeries_sub_iterate σ hσ f n
  have h1 := correctedNorm_sub_correctedNorm_mem_span_pow_succ σ (Nat.succ_pos n) h0
  rw [← Function.iterate_succ_apply' (correctedNorm p O σ) n f] at h1
  simpa only [sub_add_sub_cancel] using add_mem
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) h1)
    (iterate_correctedNorm_succ_sub_mem_span_pow σ hσ f n)

variable (p O)

/-- **Coleman's corrected-norm projector** valued in the fixed subgroup `fixedUnits p O σ`: for
`(p)`-adically complete `O` and Frobenius lift `σ : O ≃+* O`, the multiplicative retraction
`O⟦X⟧ˣ →* fixedUnits p O σ` (Coleman Prop. 14; Sharifi Thm. 5.4.9; RJW Thm. 10.13). -/
def normProjectorToFixedUnits (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    O⟦X⟧ˣ →* fixedUnits p O σ where
  toFun f := ⟨normProjectorUnit σ hσ f, correctedNorm_normProjectorUnit σ hσ f⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ f g)

/-- **Coleman's corrected-norm projector.** For `(p)`-adically complete `O` and Frobenius lift
`σ : O ≃+* O`, the multiplicative idempotent retraction `O⟦X⟧ˣ →* O⟦X⟧ˣ` onto `fixedUnits p O σ`
(Coleman Prop. 14; Sharifi Thm. 5.4.9; RJW Prop. 10.12 / Thm. 10.13). -/
def normProjector (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    O⟦X⟧ˣ →* O⟦X⟧ˣ :=
  (fixedUnits p O σ).subtype.comp (normProjectorToFixedUnits p O σ hσ)

variable {p O}

/-- Coercing `normProjectorToFixedUnits p O σ hσ f` to `O⟦X⟧ˣ` equals
`normProjector p O σ hσ f`. -/
@[simp]
theorem coe_normProjectorToFixedUnits (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    (normProjectorToFixedUnits p O σ hσ f : O⟦X⟧ˣ) = normProjector p O σ hσ f := (rfl)

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
        Ideal.span {(p : O⟦X⟧)} ^ (n + 1) :=
  ⟨fun h n ↦ h ▸ normProjector_sub_iterate_mem_span_pow σ hσ f n,
    fun h ↦ Units.ext (eq_normProjectorSeries_of_sub_iterate σ hσ h)⟩

/-- Every value of `normProjector` is fixed by `correctedNorm`. -/
@[simp]
theorem correctedNorm_normProjector (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧ˣ) :
    correctedNorm p O σ (normProjector p O σ hσ f) = normProjector p O σ hσ f :=
  (normProjectorToFixedUnits p O σ hσ f).prop

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
    normProjector p O σ hσ f = f :=
  ((eq_normProjector_iff σ hσ).mpr fun n ↦ by
    rw [Function.IsFixedPt.iterate hf n, sub_self]; exact zero_mem _).symm

/-- `normProjectorToFixedUnits` acts as the identity on elements of `fixedUnits p O σ`. -/
@[simp]
theorem normProjectorToFixedUnits_coe (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : fixedUnits p O σ) :
    normProjectorToFixedUnits p O σ hσ (f : O⟦X⟧ˣ) = f :=
  Subtype.ext (normProjector_eq_self σ hσ f.prop)

/-- `normProjectorToFixedUnits` is a retraction of the subgroup inclusion
`(fixedUnits p O σ).subtype`. -/
theorem normProjectorToFixedUnits_comp_subtype (σ : O ≃+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    (normProjectorToFixedUnits p O σ hσ).comp (fixedUnits p O σ).subtype =
      MonoidHom.id (fixedUnits p O σ) :=
  MonoidHom.ext (normProjectorToFixedUnits_coe σ hσ)

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

/-- **Topological convergence:** `((correctedNorm p O σ)^[n]) f → normProjector p O σ hσ f` in
the unit group topology on `O⟦X⟧ˣ` induced by the coefficientwise `(p)`-adic topology on
`O⟦X⟧`. -/
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
  refine Units.continuous_iff.mpr ⟨continuous_val_normProjector hAdic σ hσ, ?_⟩
  simpa only [Function.comp_def, ← map_inv] using
    (continuous_val_normProjector hAdic σ hσ).comp continuous_inv

/-- **Continuity of Coleman's norm projector into `fixedUnits p O σ`** in the subspace topology
induced by the coefficientwise `(p)`-adic topology on `O⟦X⟧ˣ`. -/
theorem continuous_normProjectorToFixedUnits (hAdic : IsAdic (Ideal.span {(p : O)}))
    (σ : O ≃+* O) (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) :
    Continuous (normProjectorToFixedUnits p O σ hσ) :=
  (continuous_normProjector hAdic σ hσ).subtype_mk _

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
