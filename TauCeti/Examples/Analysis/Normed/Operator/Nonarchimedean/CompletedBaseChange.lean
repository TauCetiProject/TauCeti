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

Exercises completed-tensor base change on model spaces and `(Pr)` retracts:
1. Empty (`Empty`), infinite (`ℕ`), and identity (`S = R`) base change (`c0_completedBaseChange`).
2. Mixed-characteristic `R = ℚ_[p] × (ZMod p)⸨X⸩` (`ϖ_R = (p, X)`, `‖ϖ_R‖ = p⁻¹`) mapping by `snd`
   to `S = (ZMod p)⸨X⸩` (`‖X‖ = p⁻¹`), with no division ring admitting a unital hom to `R`.
3. `I = ℕ` completed tensor (`zeroAtInftyEquiv`, `zeroAtInftyBaseChange`, inverse convergence).
4. Finite projective retracts `e Rⁿ` (`e = (0, 1)`) extending to `Sⁿ` and `(1 - e) Rⁿ` extending to
   `0` (including `n = 0`, `S = R`, and Fredholm series transport).
-/

public section

open Filter Topology ZeroAtInftyContinuousMap TauCeti TauCeti.NormedRing
  TauCeti.Huber.BanachModule
open scoped ZeroAtInfty LaurentSeries PowerSeries TensorProduct NNReal WithZero

/-! ### Empty, infinite, and identity base change -/

section Generic

variable {R S : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]

omit [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R] in
/-- Over the empty index set, the completed scalar extension `S ⊗̂_R C₀(Empty, R)` is zero. -/
example (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    Subsingleton (CompletedTensor R S C₀(Empty, R)) :=
  ⟨fun x y ↦ (CompletedTensor.zeroAtInftyBaseChange Empty hS).injective (by ext i; exact i.elim)⟩

private abbrev c0BaseChangeStmt (R S I : Type*) [NormedCommRing R] [NormedCommRing S]
    [IsUltrametricDist S] [Algebra R S] [TopologicalSpace I] (L : ℝ) : Prop :=
  ∀ (π : AddGroupSeminorm (S ⊗[R] C₀(I, R))),
    (∀ z, π z = sInf {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (s : Fin n → S) (x : Fin n → C₀(I, R)),
      z = ∑ j, s j ⊗ₜ[R] x j ∧ ∀ j, ‖s j‖ * ‖x j‖ ≤ c}) →
    ∀ (hsmul : ∀ (s : S) (z : S ⊗[R] C₀(I, R)), π (s • z) ≤ ‖s‖ * π z),
      let _ := π.toSeminormedAddCommGroup; let _ := IsBoundedSMul.of_norm_smul_le hsmul
      let _ := uniformContinuousConstSMul_of_continuousConstSMul S (S ⊗[R] C₀(I, R))
      ∃ e : UniformSpace.Completion (S ⊗[R] C₀(I, R)) ≃L[S] C₀(I, S),
        (∀ s x i, e ((s ⊗ₜ[R] x : S ⊗[R] C₀(I, R)) :
          UniformSpace.Completion (S ⊗[R] C₀(I, R))) i = s * algebraMap R S (x i)) ∧
        (∀ z, ‖e z‖ ≤ L * ‖z‖) ∧ (∀ y, ‖e.symm y‖ ≤ ‖y‖)

omit [IsUltrametricDist R] [CompleteSpace R] [NormedRing.IsTate R] in
/-- Product-seminorm base change `c0_completedBaseChange` applies to both `Empty` and `ℕ`. -/
example {L : ℝ} (hL : 1 ≤ L) (hφ : ∀ r : R, ‖algebraMap R S r‖ ≤ L * ‖r‖) :
    c0BaseChangeStmt R S Empty L ∧ c0BaseChangeStmt R S ℕ L :=
  ⟨fun π hπ hsmul ↦ CompletedTensor.c0_completedBaseChange (zero_le_one.trans hL) hφ π hπ hsmul,
   fun π hπ hsmul ↦ CompletedTensor.c0_completedBaseChange (zero_le_one.trans hL) hφ π hπ hsmul⟩

omit [NormOneClass R] in
/-- Identity base change (`S = R`) on `C₀(ℕ, R)` recovers the original operator `u`. -/
example (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    let hR : ∃ C : ℝ≥0, ∀ (r s : R), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖ :=
      ⟨1, fun r s ↦ by simpa using norm_mul_le r s⟩
    u.completedBaseChange (CompletedTensor.zeroAtInftyBaseChange ℕ hR)
      (CompletedTensor.zeroAtInftyBaseChange ℕ hR) = u := by
  intro hR; rw [u.completedBaseChange_zeroAtInfty hR]; exact u.mapCoeffs_id _

end Generic

/-! ### Mixed-characteristic ring `R = ℚ_[p] × (ZMod p)⸨X⸩` with no common ground field -/

namespace CompletedBaseChangeCheck

noncomputable section Setup

variable (p : ℕ) [hp : Fact p.Prime]

local notation "S₀(" p ")" => (ZMod p)⸨X⸩
local notation "R₀(" p ")" => (ℚ_[p] × (ZMod p)⸨X⸩)

/-- Rank-one valuation structure on `(ZMod p)⸨X⸩` normalising `‖X‖ = p⁻¹`. -/
local instance laurentRankOne : (Valued.v : Valuation S₀(p) ℤᵐ⁰).RankOne where
  hom' := (WithZeroMulInt.toNNReal (Nat.cast_ne_zero.mpr hp.out.ne_zero)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by exact_mod_cast hp.out.one_lt)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    have h : Valued.v ((PowerSeries.X : (ZMod p)⟦X⟧) : S₀(p)) = WithZero.exp (-1 : ℤ) := by
      simpa using _root_.LaurentSeries.valuation_X_pow (ZMod p) 1
    exact ⟨_, by rw [h]; exact WithZero.exp_ne_zero, by rw [h]; simp⟩

private theorem laurentRankOne_hom :
    Valuation.RankOne.hom (Valued.v : Valuation S₀(p) ℤᵐ⁰) =
      (WithZeroMulInt.toNNReal (Nat.cast_ne_zero.mpr hp.out.ne_zero)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding :=
  (rfl)

open scoped Valued

/-- The uniformizer `X` in `(ZMod p)⸨X⸩`. -/
abbrev varX : S₀(p) := ((PowerSeries.X : (ZMod p)⟦X⟧) : S₀(p))

/-- Under the rank-one valuation with base `p`, `‖X‖ = p⁻¹`. -/
theorem norm_varX : ‖varX p‖ = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hv : Valued.v (varX p) = WithZero.exp (-1 : ℤ) := by
    simpa using _root_.LaurentSeries.valuation_X_pow (ZMod p) 1
  rw [Valued.toNormedField.norm_def, laurentRankOne_hom p, MonoidWithZeroHom.comp_apply,
    Valuation.embedding_restrict, hv,
    WithZeroMulInt.toNNReal_neg_apply hp0 WithZero.exp_ne_zero, WithZero.log_exp, zpow_neg_one]
  simp

theorem varX_ne_zero : varX p ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_varX p]; exact inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero)

theorem norm_varX_lt_one : ‖varX p‖ < 1 := by
  rw [norm_varX p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- Multiplicative pseudo-uniformiser `ϖ_S = X` on `S = (ZMod p)⸨X⸩`. -/
def uniformizerS : PseudoUniformizer S₀(p) :=
  PseudoUniformizer.ofAlgebraMap (K := S₀(p)) (A := S₀(p)) (varX_ne_zero p) (norm_varX_lt_one p)

theorem norm_uniformizerS : ‖((uniformizerS p).unit : S₀(p))‖ = (p : ℝ)⁻¹ := by
  rw [uniformizerS, PseudoUniformizer.coe_unit_ofAlgebraMap, Algebra.algebraMap_self_apply,
    norm_varX p]

/-- Multiplicative pseudo-uniformiser `p` on `ℚ_[p]`. -/
def uniformizerQp : PseudoUniformizer ℚ_[p] :=
  PseudoUniformizer.ofAlgebraMap (K := ℚ_[p]) (A := ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (by rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))

theorem norm_uniformizerQp : ‖((uniformizerQp p).unit : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [uniformizerQp, PseudoUniformizer.coe_unit_ofAlgebraMap, Algebra.algebraMap_self_apply,
    Padic.norm_p]

/-- Multiplicative pseudo-uniformiser `ϖ_R = (p, X)` on `R = ℚ_[p] × (ZMod p)⸨X⸩` with the
maximum norm, of norm `p⁻¹`. -/
def uniformizerR : PseudoUniformizer R₀(p) :=
  (uniformizerQp p).prod (uniformizerS p) ((norm_uniformizerQp p).trans (norm_uniformizerS p).symm)

theorem coe_uniformizerR : ((uniformizerR p).unit : R₀(p)) = ((p : ℚ_[p]), varX p) := by
  simp [uniformizerR, uniformizerQp, uniformizerS]

theorem norm_uniformizerR : ‖((uniformizerR p).unit : R₀(p))‖ = (p : ℝ)⁻¹ :=
  (PseudoUniformizer.norm_prod _ _ _).trans (norm_uniformizerQp p)

/-- `ℚ_[p] × (ZMod p)⸨X⸩` is a Banach–Tate ring via `(p, X)`. -/
local instance isTateProd : NormedRing.IsTate R₀(p) := ⟨⟨uniformizerR p⟩⟩

/-- **No common ground field.** No division ring admits a unital ring homomorphism into
`ℚ_[p] × (ZMod p)⸨X⸩`: `p` is nonzero in `ℚ_[p]` and zero in `(ZMod p)⸨X⸩`. -/
theorem isEmpty_ringHom_from_divisionRing (F : Type*) [DivisionRing F] : IsEmpty (F →+* R₀(p)) := by
  refine ⟨fun f ↦ ?_⟩
  have hpF : (p : F) ≠ 0 := fun h0 ↦ Nat.cast_ne_zero (R := ℚ_[p]).mpr hp.out.ne_zero <| by
    simpa [h0] using (map_natCast ((RingHom.fst ℚ_[p] S₀(p)).comp f) p).symm
  have hu : IsUnit (RingHom.snd ℚ_[p] S₀(p) (f (p : F))) :=
    ((IsUnit.mk0 (p : F) hpF).map f).map (RingHom.snd _ _)
  have hz : RingHom.snd ℚ_[p] S₀(p) (f (p : F)) = 0 := by
    rw [← RingHom.comp_apply, map_natCast, ← map_natCast (algebraMap (ZMod p) S₀(p)),
      CharP.cast_eq_zero (ZMod p) p, map_zero]
  exact not_isUnit_zero (hz ▸ hu)

/-! ### Second-projection algebra structure and `I = ℕ` completed tensor checks -/

/-- Algebra structure on `(ZMod p)⸨X⸩` over `ℚ_[p] × (ZMod p)⸨X⸩` via the second projection. -/
local instance sndAlgebra : Algebra R₀(p) S₀(p) := (RingHom.snd ℚ_[p] S₀(p)).toAlgebra

theorem algebraMap_snd_apply (r : R₀(p)) : algebraMap R₀(p) S₀(p) r = r.2 := (rfl)

theorem exists_norm_smul_snd : ∃ C : ℝ≥0, ∀ (r : R₀(p)) (s : S₀(p)), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖ :=
  ⟨1, fun r s ↦ by
    rw [NNReal.coe_one, one_mul, Algebra.smul_def, algebraMap_snd_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (le_max_right ‖r.1‖ ‖r.2‖) (norm_nonneg s)⟩

local notation:70 S:71 " ⊗̂[" R "] " M:71 => (CompletedTensor R S M)

/-- On `C₀(ℕ, ℚ_[p] × (ZMod p)⸨X⸩) ⊗̂_R (ZMod p)⸨X⸩`, `Θ_φ` sends `(xᵢ, yᵢ)ᵢ ⊗ s` to `(yᵢ * s)ᵢ`. -/
example (xy : C₀(ℕ, R₀(p))) (s : S₀(p)) (i : ℕ) :
    CompletedTensor.zeroAtInftyEquiv ℕ (exists_norm_smul_snd p)
      (CompletedTensor.tmul R₀(p) C₀(ℕ, R₀(p)) S₀(p) xy s) i = (xy i).2 * s := by
  rw [CompletedTensor.zeroAtInftyEquiv_tmul_apply, Algebra.smul_def, algebraMap_snd_apply]

/-- On `S ⊗̂_R C₀(ℕ, R)`, `zeroAtInftyBaseChange` sends `s ⊗ (xᵢ, yᵢ)ᵢ` to `(s * yᵢ)ᵢ`, and its
inverse is the limit over finite subsets `F ⊆ ℕ` of `∑ i ∈ F, sᵢ ⊗ eᵢ`. -/
example (xy : C₀(ℕ, R₀(p))) (s : S₀(p)) (y : C₀(ℕ, S₀(p))) :
    (∀ i : ℕ, CompletedTensor.zeroAtInftyBaseChange ℕ (exists_norm_smul_snd p)
        (CompletedTensor.tmul R₀(p) S₀(p) C₀(ℕ, R₀(p)) s xy) i = s * (xy i).2) ∧
    Tendsto
      (fun F : Finset ℕ ↦ ∑ i ∈ F, CompletedTensor.tmul R₀(p) S₀(p) C₀(ℕ, R₀(p)) (y i) (single i 1))
      atTop (𝓝 ((CompletedTensor.zeroAtInftyBaseChange ℕ (exists_norm_smul_snd p)).symm y)) :=
  ⟨fun i ↦ CompletedTensor.zeroAtInftyBaseChange_tmul_apply ℕ (exists_norm_smul_snd p) s xy i,
    CompletedTensor.hasSum_zeroAtInftyBaseChange_symm ℕ (exists_norm_smul_snd p) y⟩

/-! ### Finite projective retracts `e Rⁿ` and `(1 - e) Rⁿ` for `e = (0, 1)` -/

section IdempotentRetract

section GenericIdemp

variable {R : Type*} [NormedCommRing R]

/-- For an element `c : R`, coordinatewise scalar projection `c • id` on `Fin n → R`. -/
noncomputable def idempProj (c : R) (n : ℕ) : (Fin n → R) →L[R] (Fin n → R) :=
  c • ContinuousLinearMap.id R (Fin n → R)

/-- Model-space inclusion `(c Rⁿ) →L[R] C₀(Fin n, R)` of the range of `c • id`. -/
def idempIncl (c : R) (n : ℕ) : (idempProj c n).range →L[R] C₀(Fin n, R) :=
  (equivFunOnFintype R R (I := Fin n)).toContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    (idempProj c n).range.subtypeL

/-- Model-space retraction `C₀(Fin n, R) →L[R] (c Rⁿ)` onto the range of `c • id`. -/
def idempRetr (c : R) (n : ℕ) : C₀(Fin n, R) →L[R] (idempProj c n).range :=
  ((idempProj c n).codRestrict (idempProj c n).range fun v ↦ ⟨v, rfl⟩).comp
    (equivFunOnFintype R R (I := Fin n)).toContinuousLinearEquiv.toContinuousLinearMap

theorem idempRetr_comp_idempIncl {c : R} (hc : c * c = c) (n : ℕ) :
    (idempRetr c n).comp (idempIncl c n) = .id R (idempProj c n).range :=
  ContinuousLinearMap.ext fun ⟨_, u, rfl⟩ ↦ Subtype.ext <| by
    have h : (((idempRetr c n).comp (idempIncl c n)) ⟨_, u, rfl⟩ : Fin n → R) =
        idempProj c n (idempProj c n u) := by simp [idempRetr, idempIncl]
    rw [h, ContinuousLinearMap.id_apply]; ext k; simp [idempProj, ← mul_assoc, hc]

theorem idempIncl_comp_idempRetr (c : R) (n : ℕ) :
    (idempIncl c n).comp (idempRetr c n) = c • (1 : C₀(Fin n, R) →L[R] C₀(Fin n, R)) := by
  ext x k; simp [idempIncl, idempRetr, idempProj, ContinuousLinearMap.one_def]

end GenericIdemp

theorem hasPr_idempRange {R : Type} [NormedCommRing R] {c : R} (hc : c * c = c) (n : ℕ) :
    HasPr R (idempProj c n).range :=
  (hasPr_def R _).mpr ⟨Fin n, inferInstance, inferInstance,
    idempIncl c n, idempRetr c n, idempRetr_comp_idempIncl hc n⟩

/-- The nontrivial idempotent `e = (0, 1)` in `R = ℚ_[p] × (ZMod p)⸨X⸩`. -/
def idemSnd : R₀(p) := (0, 1)

local notation "e₀(" p ")" => (idemSnd p)
local notation "hS₀(" p ")" => (exists_norm_smul_snd p)

theorem idemSnd_mul_self : e₀(p) * e₀(p) = e₀(p) := by ext <;> simp [idemSnd]

theorem one_sub_idemSnd_mul_self : (1 - e₀(p)) * (1 - e₀(p)) = 1 - e₀(p) := by
  ext <;> simp [idemSnd]

/-- **Commuting idempotent diagram for `e Rⁿ`**: `retractIncl ∘ retractProj` on `C₀(Fin n, S)` is
the identity, because `φ(e) = 1`. -/
theorem retractIncl_comp_retractProj_idemSnd (n : ℕ) :
    (CompletedTensor.retractIncl (Fin n) hS₀(p) (idempIncl e₀(p) n)).comp
      (CompletedTensor.retractProj (Fin n) hS₀(p) (idempRetr e₀(p) n)) =
      .id S₀(p) C₀(Fin n, S₀(p)) := by
  rw [CompletedTensor.retractIncl_comp_retractProj, idempIncl_comp_idempRetr,
    ContinuousLinearMap.mapCoeffs_smul, ContinuousLinearMap.mapCoeffs_one]
  have he : algebraMap R₀(p) S₀(p) e₀(p) = 1 := by simp [algebraMap_snd_apply, idemSnd]
  rw [he, one_smul, ContinuousLinearMap.one_def]

/-- **Tensor extension of `e Rⁿ` is `Sⁿ`** (for every `n : ℕ`, including `n = 0`). -/
def idemSndCompletedEquiv (n : ℕ) :
    (S₀(p) ⊗̂[R₀(p)] (idempProj e₀(p) n).range) ≃L[S₀(p)] (Fin n → S₀(p)) :=
  (ContinuousLinearEquiv.ofContinuousLinearMap
    (CompletedTensor.retractIncl (Fin n) hS₀(p) (idempIncl e₀(p) n))
    (CompletedTensor.retractProj (Fin n) hS₀(p) (idempRetr e₀(p) n))
    (retractIncl_comp_retractProj_idemSnd p n)
    (CompletedTensor.retractProj_comp_retractIncl hS₀(p)
      (idempRetr_comp_idempIncl (idemSnd_mul_self p) n))).trans
    (equivFunOnFintype S₀(p) S₀(p) (I := Fin n)).toContinuousLinearEquiv

/-- In rank `n = 0`, `S ⊗̂_R (e R⁰)` is isomorphic to `Fin 0 → S` and hence a subsingleton. -/
example : Subsingleton (S₀(p) ⊗̂[R₀(p)] (idempProj e₀(p) 0).range) :=
  (idemSndCompletedEquiv p 0).injective.subsingleton

/-- **Commuting idempotent diagram for `(1 - e) Rⁿ`**: `retractIncl ∘ retractProj` on
`C₀(Fin n, S)` vanishes, because `φ(1 - e) = 0`. -/
theorem retractIncl_comp_retractProj_one_sub_idemSnd (n : ℕ) :
    (CompletedTensor.retractIncl (Fin n) hS₀(p) (idempIncl (1 - e₀(p)) n)).comp
      (CompletedTensor.retractProj (Fin n) hS₀(p) (idempRetr (1 - e₀(p)) n)) = 0 := by
  rw [CompletedTensor.retractIncl_comp_retractProj, idempIncl_comp_idempRetr,
    ContinuousLinearMap.mapCoeffs_smul, ContinuousLinearMap.mapCoeffs_one]
  have he : algebraMap R₀(p) S₀(p) (1 - e₀(p)) = 0 := by simp [algebraMap_snd_apply, idemSnd]
  ext f k; simp [he]

/-- **Complementary retract `(1 - e) Rⁿ` extends to zero** for every `n : ℕ`. -/
theorem subsingleton_completedTensor_one_sub_idemSnd (n : ℕ) :
    Subsingleton (S₀(p) ⊗̂[R₀(p)] (idempProj (1 - e₀(p)) n).range) := by
  have hzero (z : S₀(p) ⊗̂[R₀(p)] (idempProj (1 - e₀(p)) n).range) : z = 0 := by
    let inc := CompletedTensor.retractIncl (Fin n) hS₀(p) (idempIncl (1 - e₀(p)) n)
    let prj := CompletedTensor.retractProj (Fin n) hS₀(p) (idempRetr (1 - e₀(p)) n)
    have hz : z = prj (inc z) := (DFunLike.congr_fun
      (CompletedTensor.retractProj_comp_retractIncl hS₀(p)
        (idempRetr_comp_idempIncl (one_sub_idemSnd_mul_self p) n)) z).symm
    have hinc0 : inc z = 0 := (congrArg inc hz).trans (by
      simpa using DFunLike.congr_fun (retractIncl_comp_retractProj_one_sub_idemSnd p n) (inc z))
    rw [hz, hinc0, map_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

/-- Identity base change (`S = R`) on the closed summand `e Rⁿ` preserves every operator. -/
example (n : ℕ) (u : (idempProj e₀(p) n).range →L[R₀(p)] (idempProj e₀(p) n).range) :
    have hc : IsClosed ((idempProj e₀(p) n).range : Set (Fin n → R₀(p))) := by
      have hset : ((idempProj e₀(p) n).range : Set (Fin n → R₀(p))) = {v | e₀(p) • v = v} :=
        Set.ext fun v ↦ ⟨by rintro ⟨w, rfl⟩; simp [idempProj, ← mul_smul, idemSnd_mul_self],
          fun hv ↦ ⟨v, hv⟩⟩
      rw [hset]; exact isClosed_eq (continuous_const_smul _) continuous_id
    let _ : CompleteSpace (idempProj e₀(p) n).range := hc.completeSpace_coe
    u.completedBaseChange (CompletedTensor.lid R₀(p) _) (CompletedTensor.lid R₀(p) _) = u := by
  intro hc; let _ : CompleteSpace (idempProj e₀(p) n).range := hc.completeSpace_coe
  exact u.completedBaseChange_self

/-- **Fredholm series transport on `e Rⁿ`**: for any continuous endomorphism `u` of `e Rⁿ`,
the Fredholm series of `u.completedBaseChange` on `Sⁿ` equals `PowerSeries.map φ u.charPowerSeries`.
-/
example (n : ℕ) (u : (idempProj e₀(p) n).range →L[R₀(p)] (idempProj e₀(p) n).range) :
    (u.completedBaseChange (idemSndCompletedEquiv p n)
        (idemSndCompletedEquiv p n)).charPowerSeries =
      PowerSeries.map (RingHom.snd ℚ_[p] S₀(p)) u.charPowerSeries :=
  (ContinuousLinearMap.isPrCompact_of_isRowCompact_comp
    (idempRetr_comp_idempIncl (idemSnd_mul_self p) n)
    (idempRetr_comp_idempIncl (idemSnd_mul_self p) n)
    (ContinuousLinearMap.isRowCompact_of_finite _)).charPowerSeries_completedBaseChange hS₀(p)
      (idemSndCompletedEquiv p n)

end IdempotentRetract

end Setup

end CompletedBaseChangeCheck
