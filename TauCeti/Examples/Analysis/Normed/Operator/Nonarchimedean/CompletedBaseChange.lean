/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Int.WithZero
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.MetricSpace.Ultra.Pi
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.BaseChange
public import TauCeti.Analysis.Normed.Ring.Prod
public import TauCeti.Topology.MetricSpace.Ultra.Prod

/-!
# Checks for completed-tensor base change of `c₀` and `(Pr)` modules

This file exercises the completed-tensor base-change comparisons on model spaces and `(Pr)`
retracts:

1. **Empty, infinite, and identity base change**: `CompletedTensor R S C₀(Empty, R)` is a
   subsingleton, `c0_completedBaseChange` applies to both `Empty` and `ℕ`, and when `S = R`
   both `zeroAtInftyBaseChange` and `completedBaseChange` recover the identity.
2. **Mixed-characteristic coefficient rings with no common ground field**: for a prime `p`,
   `R = ℚ_[p] × (ZMod p)⸨X⸩` carries the maximum norm with multiplicative pseudo-uniformiser
   `ϖ_R = (p, X)` of norm `p⁻¹`, `S = (ZMod p)⸨X⸩` carries the `X`-adic norm with `‖X‖ = p⁻¹`
   and `ϖ_S = X`, and `φ : R →+* S` is the second projection. No division ring admits a unital
   homomorphism to `R`, since `p` is invertible in `ℚ_[p]` and zero in `(ZMod p)⸨X⸩`.
3. **Actual completed tensor on `I = ℕ`**: `zeroAtInftyBaseChange` and `zeroAtInftyEquiv` evaluate
   elementary tensors `(xᵢ, yᵢ)ᵢ ⊗ s ↦ (yᵢ * s)ᵢ`, while the inverse is the unconditional limit of
   `∑ i ∈ F, eᵢ ⊗ sᵢ`.
4. **Finite projective retracts `e Rⁿ` and `(1 - e) Rⁿ` for `e = (0, 1)`**: the commuting
   idempotent diagrams (`retractProj_comp_retractIncl`, `retractIncl_comp_retractProj`) identify
   `S ⊗̂_R (e Rⁿ) ≃L[S] (Fin n → S)` and show that `S ⊗̂_R ((1 - e) Rⁿ)` vanishes, including `n = 0`
   and identity base change, and transport Fredholm series along `completedBaseChange`.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap TauCeti TauCeti.NormedRing
  TauCeti.Huber.BanachModule
open scoped ZeroAtInfty LaurentSeries PowerSeries TensorProduct NNReal WithZero

/-! ### Empty, infinite, and identity base change -/

section Generic

variable {R S : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [NormedRing.IsTate R]
  [NormedCommRing S] [NormOneClass S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]

omit [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass S] in
/-- Over the empty index set, the completed scalar extension `S ⊗̂_R C₀(Empty, R)` is zero. -/
example (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    Subsingleton (CompletedTensor R S C₀(Empty, R)) :=
  ⟨fun x y ↦ (CompletedTensor.zeroAtInftyBaseChange Empty hS).injective (by ext i; exact i.elim)⟩

omit [NormedRing.IsTate R] in
/-- Product-seminorm base change `c0_completedBaseChange` applies to the empty index set. -/
example {L : ℝ} (hL : 1 ≤ L) (hφ : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖)
    (π : AddGroupSeminorm (S ⊗[R] C₀(Empty, R)))
    (hπ : ∀ z : S ⊗[R] C₀(Empty, R), π z = sInf {c : ℝ | 0 ≤ c ∧
      ∃ (n : ℕ) (s : Fin n → S) (x : Fin n → C₀(Empty, R)),
        z = ∑ j, s j ⊗ₜ[R] x j ∧ ∀ j, ‖s j‖ * ‖x j‖ ≤ c})
    (hsmul : ∀ (s : S) (z : S ⊗[R] C₀(Empty, R)), π (s • z) ≤ ‖s‖ * π z) :
    let _ := π.toSeminormedAddCommGroup
    let _ : IsBoundedSMul S (S ⊗[R] C₀(Empty, R)) := IsBoundedSMul.of_norm_smul_le hsmul
    let _ : UniformContinuousConstSMul S (S ⊗[R] C₀(Empty, R)) :=
      uniformContinuousConstSMul_of_continuousConstSMul S (S ⊗[R] C₀(Empty, R))
    ∃ e : UniformSpace.Completion (S ⊗[R] C₀(Empty, R)) ≃L[S] C₀(Empty, S),
      (∀ s x i, e ((s ⊗ₜ[R] x : S ⊗[R] C₀(Empty, R)) :
        UniformSpace.Completion (S ⊗[R] C₀(Empty, R))) i = s * algebraMap R S (x i)) ∧
      (∀ z, ‖e z‖ ≤ L * ‖z‖) ∧ (∀ y, ‖e.symm y‖ ≤ ‖y‖) :=
  CompletedTensor.c0_completedBaseChange (zero_le_one.trans hL) hφ π hπ hsmul

omit [NormedRing.IsTate R] in
/-- Product-seminorm base change `c0_completedBaseChange` applies to the infinite index set `ℕ`. -/
example {L : ℝ} (hL : 1 ≤ L) (hφ : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖)
    (π : AddGroupSeminorm (S ⊗[R] C₀(ℕ, R)))
    (hπ : ∀ z : S ⊗[R] C₀(ℕ, R), π z = sInf {c : ℝ | 0 ≤ c ∧
      ∃ (n : ℕ) (s : Fin n → S) (x : Fin n → C₀(ℕ, R)),
        z = ∑ j, s j ⊗ₜ[R] x j ∧ ∀ j, ‖s j‖ * ‖x j‖ ≤ c})
    (hsmul : ∀ (s : S) (z : S ⊗[R] C₀(ℕ, R)), π (s • z) ≤ ‖s‖ * π z) :
    let _ := π.toSeminormedAddCommGroup
    let _ : IsBoundedSMul S (S ⊗[R] C₀(ℕ, R)) := IsBoundedSMul.of_norm_smul_le hsmul
    let _ : UniformContinuousConstSMul S (S ⊗[R] C₀(ℕ, R)) :=
      uniformContinuousConstSMul_of_continuousConstSMul S (S ⊗[R] C₀(ℕ, R))
    ∃ e : UniformSpace.Completion (S ⊗[R] C₀(ℕ, R)) ≃L[S] C₀(ℕ, S),
      (∀ s x i, e ((s ⊗ₜ[R] x : S ⊗[R] C₀(ℕ, R)) :
        UniformSpace.Completion (S ⊗[R] C₀(ℕ, R))) i = s * algebraMap R S (x i)) ∧
      (∀ z, ‖e z‖ ≤ L * ‖z‖) ∧ (∀ y, ‖e.symm y‖ ≤ ‖y‖) :=
  CompletedTensor.c0_completedBaseChange (zero_le_one.trans hL) hφ π hπ hsmul

omit [NormOneClass R] in
/-- Identity base change (`S = R`) on `C₀(ℕ, R)` recovers the original operator `u`. -/
example (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    let hR : ∃ C : ℝ≥0, ∀ (r s : R), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖ :=
      ⟨1, fun r s ↦ by simpa using norm_mul_le r s⟩
    u.completedBaseChange (CompletedTensor.zeroAtInftyBaseChange ℕ hR)
      (CompletedTensor.zeroAtInftyBaseChange ℕ hR) = u := by
  intro hR
  rw [u.completedBaseChange_zeroAtInfty hR]
  exact u.mapCoeffs_id _

end Generic

/-! ### Mixed-characteristic ring `R = ℚ_[p] × (ZMod p)⸨X⸩` with no common ground field -/

namespace CompletedBaseChangeCheck

noncomputable section Setup

variable (p : ℕ) [hp : Fact p.Prime]

/-- Rank-one valuation structure on `(ZMod p)⸨X⸩` normalising `‖X‖ = p⁻¹`. -/
local instance laurentRankOne :
    (Valued.v : Valuation ((ZMod p)⸨X⸩) ℤᵐ⁰).RankOne where
  hom' := (WithZeroMulInt.toNNReal (Nat.cast_ne_zero.mpr hp.out.ne_zero)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by exact_mod_cast hp.out.one_lt)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨((PowerSeries.X : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩), ?_, ?_⟩
    · have h := _root_.LaurentSeries.valuation_X_pow (ZMod p) 1
      rw [pow_one] at h; rw [h]; exact WithZero.exp_ne_zero
    · have h := _root_.LaurentSeries.valuation_X_pow (ZMod p) 1
      rw [pow_one] at h; rw [h]; simp

open scoped Valued

/-- The uniformizer `X` in `(ZMod p)⸨X⸩`. -/
abbrev varX : (ZMod p)⸨X⸩ :=
  ((PowerSeries.X : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)

/-- Under the rank-one valuation with base `p`, `‖X‖ = p⁻¹`. -/
theorem norm_varX : ‖varX p‖ = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hv : Valued.v (varX p) = WithZero.exp (-1 : ℤ) := by
    simpa using _root_.LaurentSeries.valuation_X_pow (ZMod p) 1
  rw [Valued.toNormedField.norm_def]
  have hval : ((WithZeroMulInt.toNNReal hp0).comp MonoidWithZeroHom.ValueGroup₀.embedding)
      (Valued.v.restrict (varX p)) = (p : ℝ≥0)⁻¹ := by
    rw [MonoidWithZeroHom.comp_apply, Valuation.embedding_restrict, hv,
      WithZeroMulInt.toNNReal_neg_apply hp0 WithZero.exp_ne_zero, WithZero.log_exp, zpow_neg_one]
  exact congrArg ((↑) : ℝ≥0 → ℝ) hval

theorem varX_ne_zero : varX p ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_varX p]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero)

theorem norm_varX_lt_one : ‖varX p‖ < 1 := by
  rw [norm_varX p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- Multiplicative pseudo-uniformiser `ϖ_S = X` on `S = (ZMod p)⸨X⸩`. -/
def uniformizerS : PseudoUniformizer ((ZMod p)⸨X⸩) :=
  PseudoUniformizer.ofAlgebraMap (K := (ZMod p)⸨X⸩) (A := (ZMod p)⸨X⸩)
    (varX_ne_zero p) (norm_varX_lt_one p)

theorem norm_uniformizerS : ‖((uniformizerS p).unit : (ZMod p)⸨X⸩)‖ = (p : ℝ)⁻¹ := by
  rw [uniformizerS, PseudoUniformizer.coe_unit_ofAlgebraMap, Algebra.algebraMap_self_apply,
    norm_varX p]

/-- Multiplicative pseudo-uniformiser `p` on `ℚ_[p]`. -/
def uniformizerQp : PseudoUniformizer ℚ_[p] :=
  PseudoUniformizer.ofAlgebraMap (K := ℚ_[p]) (A := ℚ_[p])
    (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (by rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))

theorem norm_uniformizerQp : ‖((uniformizerQp p).unit : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [uniformizerQp, PseudoUniformizer.coe_unit_ofAlgebraMap, Algebra.algebraMap_self_apply,
    Padic.norm_p]

/-- Multiplicative pseudo-uniformiser `ϖ_R = (p, X)` on `R = ℚ_[p] × (ZMod p)⸨X⸩` with the
maximum norm, of norm `p⁻¹`. -/
def uniformizerR : PseudoUniformizer (ℚ_[p] × (ZMod p)⸨X⸩) :=
  (uniformizerQp p).prod (uniformizerS p) ((norm_uniformizerQp p).trans (norm_uniformizerS p).symm)

theorem coe_uniformizerR :
    ((uniformizerR p).unit : ℚ_[p] × (ZMod p)⸨X⸩) = ((p : ℚ_[p]), varX p) := by
  simp [uniformizerR, uniformizerQp, uniformizerS]

theorem norm_uniformizerR :
    ‖((uniformizerR p).unit : ℚ_[p] × (ZMod p)⸨X⸩)‖ = (p : ℝ)⁻¹ :=
  (PseudoUniformizer.norm_prod _ _ _).trans (norm_uniformizerQp p)

/-- `ℚ_[p] × (ZMod p)⸨X⸩` is a Banach–Tate ring via `(p, X)`. -/
local instance isTateProd : NormedRing.IsTate (ℚ_[p] × (ZMod p)⸨X⸩) :=
  ⟨⟨uniformizerR p⟩⟩

/-- **No common ground field.** No division ring admits a unital ring homomorphism into
`ℚ_[p] × (ZMod p)⸨X⸩`: `p` is nonzero in `ℚ_[p]` and zero in `(ZMod p)⸨X⸩`. -/
theorem isEmpty_ringHom_from_divisionRing (F : Type*) [DivisionRing F] :
    IsEmpty (F →+* ℚ_[p] × (ZMod p)⸨X⸩) := by
  refine ⟨fun f ↦ ?_⟩
  have hpF : (p : F) ≠ 0 := by
    intro h0
    have h1 : ((RingHom.fst ℚ_[p] ((ZMod p)⸨X⸩)).comp f) (p : F) = 0 := by simp [h0]
    rw [map_natCast] at h1
    exact Nat.cast_ne_zero.mpr hp.out.ne_zero h1
  have hu : IsUnit ((RingHom.snd ℚ_[p] ((ZMod p)⸨X⸩)) (f (p : F))) :=
    ((IsUnit.mk0 (p : F) hpF).map f).map (RingHom.snd _ _)
  have hz : (RingHom.snd ℚ_[p] ((ZMod p)⸨X⸩)) (f (p : F)) = 0 := by
    rw [← RingHom.comp_apply, map_natCast,
      ← map_natCast (algebraMap (ZMod p) ((ZMod p)⸨X⸩)),
      CharP.cast_eq_zero (ZMod p) p, map_zero]
  exact not_isUnit_zero (hz ▸ hu)

/-! ### Second-projection algebra structure and `I = ℕ` completed tensor checks -/

/-- Algebra structure on `(ZMod p)⸨X⸩` over `ℚ_[p] × (ZMod p)⸨X⸩` via the second projection. -/
local instance sndAlgebra : Algebra (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) :=
  (RingHom.snd ℚ_[p] ((ZMod p)⸨X⸩)).toAlgebra

theorem algebraMap_snd_apply (r : ℚ_[p] × (ZMod p)⸨X⸩) :
    algebraMap (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) r = r.2 :=
  (rfl)

theorem exists_norm_smul_snd :
    ∃ C : ℝ≥0, ∀ (r : ℚ_[p] × (ZMod p)⸨X⸩) (s : (ZMod p)⸨X⸩), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖ :=
  ⟨1, fun r s ↦ by
    rw [NNReal.coe_one, one_mul, Algebra.smul_def, algebraMap_snd_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (le_max_right ‖r.1‖ ‖r.2‖) (norm_nonneg s)⟩

/-- On `C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩) ⊗̂_R (ZMod p)⸨X⸩`, `Θ_φ` sends `(xᵢ, yᵢ)ᵢ ⊗ s` to `(yᵢ * s)ᵢ`. -/
example (xy : C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩)) (s : (ZMod p)⸨X⸩) (i : ℕ) :
    CompletedTensor.zeroAtInftyEquiv ℕ (exists_norm_smul_snd p)
      (CompletedTensor.tmul (ℚ_[p] × (ZMod p)⸨X⸩) C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩)
        xy s) i = (xy i).2 * s := by
  rw [CompletedTensor.zeroAtInftyEquiv_tmul_apply, Algebra.smul_def, algebraMap_snd_apply]

/-- On the opposite orientation `S ⊗̂_R C₀(ℕ, R)`, `zeroAtInftyBaseChange` sends `s ⊗ (xᵢ, yᵢ)ᵢ` to
`(s * yᵢ)ᵢ`, and its inverse is the limit over finite subsets `F ⊆ ℕ` of `∑ i ∈ F, sᵢ ⊗ eᵢ`. -/
example (xy : C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩)) (s : (ZMod p)⸨X⸩) (y : C₀(ℕ, (ZMod p)⸨X⸩)) :
    (∀ i : ℕ,
      CompletedTensor.zeroAtInftyBaseChange ℕ (exists_norm_smul_snd p)
        (CompletedTensor.tmul (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩)
          C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩) s xy) i = s * (xy i).2) ∧
    Tendsto
      (fun F : Finset ℕ ↦ ∑ i ∈ F,
        CompletedTensor.tmul (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩)
          C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩) (y i) (single i 1))
      atTop
      (𝓝 ((CompletedTensor.zeroAtInftyBaseChange ℕ (exists_norm_smul_snd p)).symm y)) :=
  ⟨fun i ↦ CompletedTensor.zeroAtInftyBaseChange_tmul_apply ℕ (exists_norm_smul_snd p) s xy i,
    CompletedTensor.hasSum_zeroAtInftyBaseChange_symm ℕ (exists_norm_smul_snd p) y⟩

/-! ### Finite projective retracts `e Rⁿ` and `(1 - e) Rⁿ` for `e = (0, 1)` -/

section IdempotentRetract

/-- For an element `c : R`, coordinatewise scalar projection `c • id` on `Fin n → R`. -/
noncomputable def idempProj {R : Type*} [NormedCommRing R] (c : R) (n : ℕ) :
    (Fin n → R) →L[R] (Fin n → R) :=
  c • ContinuousLinearMap.id R (Fin n → R)

/-- Model-space inclusion `(c Rⁿ) →L[R] C₀(Fin n, R)` of the range of `c • id`. -/
def idempIncl {R : Type*} [NormedCommRing R] (c : R) (n : ℕ) :
    (idempProj c n).range →L[R] C₀(Fin n, R) :=
  (equivFunOnFintype R R (I := Fin n)).toContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    (idempProj c n).range.subtypeL

/-- Model-space retraction `C₀(Fin n, R) →L[R] (c Rⁿ)` onto the range of `c • id`. -/
def idempRetr {R : Type*} [NormedCommRing R] (c : R) (n : ℕ) :
    C₀(Fin n, R) →L[R] (idempProj c n).range :=
  ((idempProj c n).codRestrict (idempProj c n).range fun v ↦ ⟨v, rfl⟩).comp
    (equivFunOnFintype R R (I := Fin n)).toContinuousLinearEquiv.toContinuousLinearMap

theorem idempRetr_comp_idempIncl {R : Type*} [NormedCommRing R] {c : R} (hc : c * c = c)
    (n : ℕ) :
    (idempRetr c n).comp (idempIncl c n) = .id R (idempProj c n).range := by
  refine ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_
  have hx : (((idempRetr c n).comp (idempIncl c n)) x : Fin n → R) = idempProj c n x := by
    simp [idempRetr, idempIncl]
  rw [hx, ContinuousLinearMap.id_apply]
  rcases x with ⟨_, u, rfl⟩
  ext k
  simp [idempProj, ← mul_assoc, hc]

theorem idempIncl_comp_idempRetr {R : Type*} [NormedCommRing R] (c : R) (n : ℕ) :
    (idempIncl c n).comp (idempRetr c n) = c • (1 : C₀(Fin n, R) →L[R] C₀(Fin n, R)) := by
  ext x k
  simp [idempIncl, idempRetr, idempProj, ContinuousLinearMap.one_def]

theorem hasPr_idempRange {R : Type} [NormedCommRing R] {c : R} (hc : c * c = c) (n : ℕ) :
    HasPr R (idempProj c n).range :=
  (hasPr_def R _).mpr ⟨Fin n, inferInstance, inferInstance,
    idempIncl c n, idempRetr c n, idempRetr_comp_idempIncl hc n⟩

/-- The nontrivial idempotent `e = (0, 1)` in `R = ℚ_[p] × (ZMod p)⸨X⸩`. -/
def idemSnd : ℚ_[p] × (ZMod p)⸨X⸩ := (0, 1)

theorem idemSnd_mul_self : idemSnd p * idemSnd p = idemSnd p := by
  ext <;> simp [idemSnd]

theorem one_sub_idemSnd_mul_self :
    (1 - idemSnd p) * (1 - idemSnd p) = 1 - idemSnd p := by
  ext <;> simp [idemSnd]

/-- **Commuting idempotent diagram for `e Rⁿ`**: `retractIncl ∘ retractProj` on `C₀(Fin n, S)` is
the identity, because `φ(e) = 1`. -/
theorem retractIncl_comp_retractProj_idemSnd (n : ℕ) :
    (CompletedTensor.retractIncl (Fin n) (exists_norm_smul_snd p) (idempIncl (idemSnd p) n)).comp
      (CompletedTensor.retractProj (Fin n) (exists_norm_smul_snd p)
        (idempRetr (idemSnd p) n)) = .id ((ZMod p)⸨X⸩) C₀(Fin n, (ZMod p)⸨X⸩) := by
  rw [CompletedTensor.retractIncl_comp_retractProj, idempIncl_comp_idempRetr,
    ContinuousLinearMap.mapCoeffs_smul, ContinuousLinearMap.mapCoeffs_one]
  have he : algebraMap (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) (idemSnd p) = 1 := rfl
  rw [he, one_smul, ContinuousLinearMap.one_def]

/-- **Tensor extension of `e Rⁿ` is `Sⁿ`** (for every `n : ℕ`, including `n = 0`). -/
def idemSndCompletedEquiv (n : ℕ) :
    CompletedTensor (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) (idempProj (idemSnd p) n).range
      ≃L[(ZMod p)⸨X⸩] (Fin n → (ZMod p)⸨X⸩) :=
  (ContinuousLinearEquiv.equivOfInverse'
    (CompletedTensor.retractIncl (Fin n) (exists_norm_smul_snd p) (idempIncl (idemSnd p) n))
    (CompletedTensor.retractProj (Fin n) (exists_norm_smul_snd p) (idempRetr (idemSnd p) n))
    (retractIncl_comp_retractProj_idemSnd p n)
    (CompletedTensor.retractProj_comp_retractIncl (exists_norm_smul_snd p)
      (idempRetr_comp_idempIncl (idemSnd_mul_self p) n))).trans
    (equivFunOnFintype ((ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) (I := Fin n)).toContinuousLinearEquiv

/-- In rank `n = 0`, `S ⊗̂_R (e R⁰)` is isomorphic to `Fin 0 → S` and hence a subsingleton. -/
example :
    Subsingleton
      (CompletedTensor (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) (idempProj (idemSnd p) 0).range) :=
  (idemSndCompletedEquiv p 0).injective.subsingleton

/-- **Commuting idempotent diagram for `(1 - e) Rⁿ`**: `retractIncl ∘ retractProj` on
`C₀(Fin n, S)` vanishes, because `φ(1 - e) = 0`. -/
theorem retractIncl_comp_retractProj_one_sub_idemSnd (n : ℕ) :
    (CompletedTensor.retractIncl (Fin n) (exists_norm_smul_snd p)
        (idempIncl (1 - idemSnd p) n)).comp
      (CompletedTensor.retractProj (Fin n) (exists_norm_smul_snd p)
        (idempRetr (1 - idemSnd p) n)) = 0 := by
  rw [CompletedTensor.retractIncl_comp_retractProj, idempIncl_comp_idempRetr,
    ContinuousLinearMap.mapCoeffs_smul, ContinuousLinearMap.mapCoeffs_one]
  have he : algebraMap (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩) (1 - idemSnd p) = 0 := by
    simp [algebraMap_snd_apply, idemSnd]
  ext f k
  simp [he]

/-- **Complementary retract `(1 - e) Rⁿ` extends to zero** for every `n : ℕ`. -/
theorem subsingleton_completedTensor_one_sub_idemSnd (n : ℕ) :
    Subsingleton
      (CompletedTensor (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩)
        (idempProj (1 - idemSnd p) n).range) := by
  have hzero (z : CompletedTensor (ℚ_[p] × (ZMod p)⸨X⸩) ((ZMod p)⸨X⸩)
      (idempProj (1 - idemSnd p) n).range) : z = 0 := by
    let inc := CompletedTensor.retractIncl (Fin n) (exists_norm_smul_snd p)
      (idempIncl (1 - idemSnd p) n)
    let prj := CompletedTensor.retractProj (Fin n) (exists_norm_smul_snd p)
      (idempRetr (1 - idemSnd p) n)
    have hri : prj.comp inc = .id ((ZMod p)⸨X⸩) _ :=
      CompletedTensor.retractProj_comp_retractIncl (exists_norm_smul_snd p)
        (idempRetr_comp_idempIncl (one_sub_idemSnd_mul_self p) n)
    have hir : inc.comp prj = 0 := retractIncl_comp_retractProj_one_sub_idemSnd p n
    have hz : z = prj (inc z) := (DFunLike.congr_fun hri z).symm
    have hinc0 : inc z = 0 :=
      (congrArg inc hz).trans (by simpa using DFunLike.congr_fun hir (inc z))
    rw [hz, hinc0, map_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

/-- Identity base change (`S = R`) on the closed summand `e Rⁿ` preserves every operator. -/
example (n : ℕ)
    (u : (idempProj (idemSnd p) n).range →L[ℚ_[p] × (ZMod p)⸨X⸩]
      (idempProj (idemSnd p) n).range) :
    have hc : IsClosed ((idempProj (idemSnd p) n).range : Set (Fin n → ℚ_[p] × (ZMod p)⸨X⸩)) := by
      have hset : ((idempProj (idemSnd p) n).range : Set (Fin n → ℚ_[p] × (ZMod p)⸨X⸩)) =
          {v | idemSnd p • v = v} := by
        ext v
        refine ⟨by rintro ⟨w, rfl⟩; simp [idempProj, ← mul_smul, idemSnd_mul_self],
          fun hv ↦ ⟨v, hv⟩⟩
      rw [hset]
      exact isClosed_eq (continuous_const_smul _) continuous_id
    let _ : CompleteSpace (idempProj (idemSnd p) n).range := hc.completeSpace_coe
    u.completedBaseChange (CompletedTensor.lid (ℚ_[p] × (ZMod p)⸨X⸩) _)
      (CompletedTensor.lid (ℚ_[p] × (ZMod p)⸨X⸩) _) = u := by
  intro hc
  let _ : CompleteSpace (idempProj (idemSnd p) n).range := hc.completeSpace_coe
  exact u.completedBaseChange_self

/-- **Fredholm series transport on `e Rⁿ`**: for any continuous endomorphism `u` of `e Rⁿ`
(automatically row compact since `Fin n` is finite), the Fredholm series of
`u.completedBaseChange (idemSndCompletedEquiv p n) (idemSndCompletedEquiv p n)` on `Sⁿ` equals
`PowerSeries.map φ u.charPowerSeries`. -/
example (n : ℕ)
    (u : (idempProj (idemSnd p) n).range →L[ℚ_[p] × (ZMod p)⸨X⸩]
      (idempProj (idemSnd p) n).range) :
    (u.completedBaseChange (idemSndCompletedEquiv p n)
        (idemSndCompletedEquiv p n)).charPowerSeries =
      PowerSeries.map (RingHom.snd ℚ_[p] ((ZMod p)⸨X⸩)) u.charPowerSeries := by
  have hu : u.IsPrCompact :=
    ContinuousLinearMap.isPrCompact_of_isRowCompact_comp
      (idempRetr_comp_idempIncl (idemSnd_mul_self p) n)
      (idempRetr_comp_idempIncl (idemSnd_mul_self p) n)
      (ContinuousLinearMap.isRowCompact_of_finite _)
  exact hu.charPowerSeries_completedBaseChange (exists_norm_smul_snd p) (idemSndCompletedEquiv p n)

end IdempotentRetract

end Setup

end CompletedBaseChangeCheck
