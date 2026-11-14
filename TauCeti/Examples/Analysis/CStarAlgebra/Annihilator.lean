/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Annihilator
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

/-!
# Concrete examples of ideal annihilators and essential ideals in C⋆-algebras

This file exercises the two-sided ideal annihilator, essential-ideal, unitization-action, and
multiplier-homomorphism API across four distinct C⋆-algebraic regimes:

1. **Noncommutative unital matrix algebra** `CStarMatrix (Fin 2) (Fin 2) ℂ`:
   `(⊥).leftAnnihilator = ⊤`, `(⊤).leftAnnihilator = ⊥`, `¬ (⊥).IsClosedEssential`, and
   `(⊤).IsClosedEssential`.
2. **Direct product** `ℂ × ℂ`:
   the first-factor ideal `ℂ × {0} = ker snd` is a nontrivial proper closed ideal whose
   annihilator is `{0} × ℂ = ker fst ≠ ⊥`, so it is *not* essential and equals its own double
   annihilator, while `multiplierHom` is not injective.
3. **Genuinely nonunital algebra** `C₀(ℕ, ℂ)` of null complex sequences:
   `C₀(ℕ, ℂ)` has no left multiplicative identity, `(⊤).leftAnnihilator = ⊥`, and the proper closed
   ideal `{f ∈ C₀(ℕ, ℂ) | f 0 = 0}` has nonzero annihilator supported at `0`, exercising both
   `TwoSidedIdeal.leftAnnihilator_eq_comap_unitization` and `Submodule.unitizationModule` on a
   genuinely nonunital C⋆-algebra.
4. **Proper essential closed ideal** in `C(unitInterval, ℂ)`:
   `ker (evalStarAlgHom ℂ ℂ 0) = {f ∈ C([0, 1], ℂ) | f 0 = 0}` is a nonzero proper closed ideal
   whose annihilator is `⊥` by density of `(0, 1]` in `[0, 1]`; hence it is essential, embeds
   `C(unitInterval, ℂ)` isometrically into its multiplier algebra, and satisfies the strict
   inclusion `I < I.leftAnnihilator.leftAnnihilator = ⊤`.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra ZeroAtInfty

namespace TauCeti.AnnihilatorExample

/-! ### 1. Matrix C⋆-algebra `M₂(ℂ)` -/

section Matrix

/-- The C⋆-algebra of `2 × 2` complex matrices. -/
abbrev Mat2 := CStarMatrix (Fin 2) (Fin 2) ℂ

theorem mat2_leftAnnihilator_bot : (⊥ : TwoSidedIdeal Mat2).leftAnnihilator = ⊤ :=
  TwoSidedIdeal.leftAnnihilator_bot

theorem mat2_leftAnnihilator_top : (⊤ : TwoSidedIdeal Mat2).leftAnnihilator = ⊥ :=
  TwoSidedIdeal.leftAnnihilator_top

theorem mat2_not_isClosedEssential_bot : ¬ (⊥ : TwoSidedIdeal Mat2).IsClosedEssential :=
  TwoSidedIdeal.not_isClosedEssential_bot

theorem mat2_not_isEssential_bot : ¬ (⊥ : TwoSidedIdeal Mat2).IsEssential :=
  TwoSidedIdeal.not_isEssential_bot

theorem mat2_isClosedEssential_top : (⊤ : TwoSidedIdeal Mat2).IsClosedEssential :=
  TwoSidedIdeal.isClosedEssential_top

end Matrix

/-! ### 2. Complementary direct summands in `ℂ × ℂ` -/

section Prod

/-- The first-factor closed ideal `ℂ × {0}` in `ℂ × ℂ`. -/
abbrev firstFactorIdeal : TwoSidedIdeal (ℂ × ℂ) :=
  TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ ℂ ℂ)

/-- The second-factor closed ideal `{0} × ℂ` in `ℂ × ℂ`. -/
abbrev secondFactorIdeal : TwoSidedIdeal (ℂ × ℂ) :=
  TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ ℂ ℂ)

theorem firstFactorIdeal_ne_bot : firstFactorIdeal ≠ ⊥ := by
  intro h
  have hmem : ((1 : ℂ), (0 : ℂ)) ∈ firstFactorIdeal := by rw [TwoSidedIdeal.mem_ker]; rfl
  have hzero : ((1 : ℂ), (0 : ℂ)) = 0 := (TwoSidedIdeal.mem_bot _).mp (h ▸ hmem)
  exact one_ne_zero (congrArg Prod.fst hzero)

theorem firstFactorIdeal_ne_top : firstFactorIdeal ≠ ⊤ := by
  intro h
  have hmem : ((0 : ℂ), (1 : ℂ)) ∈ firstFactorIdeal := h.symm ▸ TwoSidedIdeal.mem_top _
  have hzero : (1 : ℂ) = 0 := (TwoSidedIdeal.mem_ker _).mp hmem
  exact one_ne_zero hzero

theorem leftAnnihilator_firstFactorIdeal :
    firstFactorIdeal.leftAnnihilator = secondFactorIdeal :=
  TwoSidedIdeal.leftAnnihilator_ker_snd_nonUnitalStarAlgHom

theorem doubleAnnihilator_firstFactorIdeal :
    firstFactorIdeal.leftAnnihilator.leftAnnihilator = firstFactorIdeal := by
  rw [leftAnnihilator_firstFactorIdeal]
  exact TwoSidedIdeal.leftAnnihilator_ker_fst_nonUnitalStarAlgHom

theorem not_isClosedEssential_firstFactorIdeal : ¬ firstFactorIdeal.IsClosedEssential := by
  rw [TwoSidedIdeal.isClosedEssential_ker_snd_nonUnitalStarAlgHom_iff]
  exact not_subsingleton ℂ

theorem not_injective_multiplierHom_firstFactorIdeal :
    ¬ Function.Injective firstFactorIdeal.multiplierHom := by
  rw [TwoSidedIdeal.multiplierHom_injective_iff_isClosedEssential]
  exact not_isClosedEssential_firstFactorIdeal

end Prod

/-! ### 3. Genuinely nonunital sequence algebra `C₀(ℕ, ℂ)` -/

section NullSequences

/-- `C₀(ℕ, ℂ)` has no left multiplicative identity, confirming that it is genuinely nonunital. -/
theorem no_left_identity_nullSeq : ¬ ∃ e : C₀(ℕ, ℂ), ∀ f : C₀(ℕ, ℂ), e * f = f := by
  rintro ⟨e, he⟩
  have he_one : ∀ n : ℕ, e n = 1 := by
    intro n
    have hn := DFunLike.congr_fun (he (ZeroAtInftyContinuousMap.single n 1)) n
    simpa using hn
  have hlim0 : Tendsto (e : ℕ → ℂ) cofinite (𝓝 0) := e.tendsto_cofinite
  have hlim1 : Tendsto (e : ℕ → ℂ) cofinite (𝓝 1) := by
    simpa only [funext he_one] using (tendsto_const_nhds (x := (1 : ℂ)) (f := cofinite))
  exact one_ne_zero (tendsto_nhds_unique hlim1 hlim0)

theorem leftAnnihilator_top_nullSeq : (⊤ : TwoSidedIdeal C₀(ℕ, ℂ)).leftAnnihilator = ⊥ :=
  TwoSidedIdeal.leftAnnihilator_top_of_isProperStar

theorem isClosedEssential_top_nullSeq : (⊤ : TwoSidedIdeal C₀(ℕ, ℂ)).IsClosedEssential :=
  TwoSidedIdeal.isClosedEssential_top

/-- Evaluation at `0 : ℕ` as a nonunital `⋆`-algebra homomorphism `C₀(ℕ, ℂ) →⋆ₙₐ[ℂ] ℂ`. -/
def evalZeroNullSeqHom : C₀(ℕ, ℂ) →⋆ₙₐ[ℂ] ℂ where
  toFun f := f 0
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalZeroNullSeqHom_apply (f : C₀(ℕ, ℂ)) : evalZeroNullSeqHom f = f 0 :=
  (rfl)

/-- The proper closed ideal `{f ∈ C₀(ℕ, ℂ) | f 0 = 0}` in the nonunital C⋆-algebra `C₀(ℕ, ℂ)`. -/
abbrev nullSeqVanishingAtZero : TwoSidedIdeal C₀(ℕ, ℂ) :=
  TwoSidedIdeal.ker evalZeroNullSeqHom

theorem single_zero_mem_leftAnnihilator_nullSeqVanishingAtZero :
    ZeroAtInftyContinuousMap.single 0 (1 : ℂ) ∈ nullSeqVanishingAtZero.leftAnnihilator := by
  rw [TwoSidedIdeal.mem_leftAnnihilator]
  intro f hf
  have hf0 : f 0 = 0 := (TwoSidedIdeal.mem_ker evalZeroNullSeqHom).mp hf
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [hf0]
  · simp [hk]

theorem not_isClosedEssential_nullSeqVanishingAtZero :
    ¬ nullSeqVanishingAtZero.IsClosedEssential := by
  rw [TwoSidedIdeal.isClosedEssential_iff_leftAnnihilator_eq_bot]
  intro hbot
  have hmem := single_zero_mem_leftAnnihilator_nullSeqVanishingAtZero
  rw [hbot, TwoSidedIdeal.mem_bot, ZeroAtInftyContinuousMap.single_eq_zero_iff] at hmem
  exact one_ne_zero hmem

/-- Concrete check of `TwoSidedIdeal.leftAnnihilator_eq_comap_unitization` on `C₀(ℕ, ℂ)`:
`ZeroAtInftyContinuousMap.single 0 1` lies in the pullback of the
`Unitization ℂ C₀(ℕ, ℂ)`-annihilator of `nullSeqVanishingAtZero`. -/
theorem single_zero_mem_comap_unitization_annihilator :
    letI := nullSeqVanishingAtZero.unitizationModule
    ZeroAtInftyContinuousMap.single 0 (1 : ℂ) ∈
      TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ C₀(ℕ, ℂ))
        (Module.annihilator (Unitization ℂ C₀(ℕ, ℂ)) nullSeqVanishingAtZero).toTwoSided := by
  let _ := nullSeqVanishingAtZero.unitizationModule
  rw [← nullSeqVanishingAtZero.leftAnnihilator_eq_comap_unitization]
  exact single_zero_mem_leftAnnihilator_nullSeqVanishingAtZero

/-- Concrete check of `Submodule.unitizationModule` on the closed left ideal
`nullSeqVanishingAtZero.toSubmodule` in `C₀(ℕ, ℂ)`. -/
theorem inr_single_zero_mem_submodule_unitization_annihilator :
    letI := nullSeqVanishingAtZero.toSubmodule.unitizationModule
      fun a x hx => nullSeqVanishingAtZero.mul_mem_left a x hx
    ((ZeroAtInftyContinuousMap.single 0 (1 : ℂ) : C₀(ℕ, ℂ)) : Unitization ℂ C₀(ℕ, ℂ)) ∈
      Module.annihilator (Unitization ℂ C₀(ℕ, ℂ)) nullSeqVanishingAtZero.toSubmodule := by
  let hmul : ∀ a : C₀(ℕ, ℂ), ∀ x ∈ nullSeqVanishingAtZero.toSubmodule,
      a * x ∈ nullSeqVanishingAtZero.toSubmodule :=
    fun a x hx => nullSeqVanishingAtZero.mul_mem_left a x hx
  let _ := nullSeqVanishingAtZero.toSubmodule.unitizationModule hmul
  rw [nullSeqVanishingAtZero.toSubmodule.mem_annihilator_unitization_iff hmul]
  intro f hf
  simpa using TwoSidedIdeal.mul_eq_zero_of_mem_leftAnnihilator
    single_zero_mem_leftAnnihilator_nullSeqVanishingAtZero hf

end NullSequences

/-! ### 4. Proper essential closed ideal in `C(unitInterval, ℂ)` -/

section UnitInterval

/-- The closed ideal `{f ∈ C(unitInterval, ℂ) | f 0 = 0}` of functions vanishing at `0`. -/
abbrev vanishingAtZero : TwoSidedIdeal C(unitInterval, ℂ) :=
  TwoSidedIdeal.ker (ContinuousMap.evalStarAlgHom ℂ ℂ (0 : unitInterval))

/-- The coordinate inclusion `t ↦ (t : ℂ)` on `unitInterval`, which vanishes at `0` and equals `1`
at `1`. -/
def coordMap : C(unitInterval, ℂ) where
  toFun t := ((t : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp continuous_subtype_val

@[simp]
theorem coordMap_apply (t : unitInterval) : coordMap t = ((t : ℝ) : ℂ) :=
  (rfl)

theorem coordMap_mem_vanishingAtZero : coordMap ∈ vanishingAtZero := by
  rw [TwoSidedIdeal.mem_ker]
  simp

theorem vanishingAtZero_ne_bot : vanishingAtZero ≠ ⊥ := by
  intro h
  have hzero : coordMap = 0 := (TwoSidedIdeal.mem_bot _).mp (h ▸ coordMap_mem_vanishingAtZero)
  have h1 : coordMap 1 = 0 := DFunLike.congr_fun hzero 1
  simp at h1

theorem vanishingAtZero_ne_top : vanishingAtZero ≠ ⊤ := by
  intro h
  have hmem : (1 : C(unitInterval, ℂ)) ∈ vanishingAtZero := h.symm ▸ TwoSidedIdeal.mem_top _
  have h10 : (1 : ℂ) = 0 := by simpa using (TwoSidedIdeal.mem_ker _).mp hmem
  exact one_ne_zero h10

/-- The annihilator of `{f ∈ C([0, 1], ℂ) | f 0 = 0}` in `C(unitInterval, ℂ)` is `⊥`. -/
theorem leftAnnihilator_vanishingAtZero : vanishingAtZero.leftAnnihilator = ⊥ := by
  refine le_bot_iff.mp fun f hf => (TwoSidedIdeal.mem_bot _).mpr ?_
  -- Testing against `coordMap` forces `f t = 0` for `t ≠ 0`, and `1 / (n + 1) → 0` gives `f 0 = 0`.
  have hmul : f * coordMap = 0 :=
    TwoSidedIdeal.mul_eq_zero_of_mem_leftAnnihilator hf coordMap_mem_vanishingAtZero
  have hpos : ∀ t : unitInterval, (t : ℝ) ≠ 0 → f t = 0 := by
    intro t ht
    have hft : f t * ((t : ℝ) : ℂ) = 0 := by simpa using DFunLike.congr_fun hmul t
    exact (mul_eq_zero.mp hft).resolve_right (Complex.ofReal_ne_zero.mpr ht)
  ext t
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := Subtype.ext ht
    subst ht0
    let u : ℕ → unitInterval := fun n =>
      ⟨1 / (n + 1 : ℝ), unitInterval.div_mem zero_le_one (by positivity) (by linarith)⟩
    have hu_tendsto : Tendsto u atTop (𝓝 (0 : unitInterval)) :=
      tendsto_subtype_rng.mpr tendsto_one_div_add_atTop_nhds_zero_nat
    have hfu_zero : (fun n => f (u n)) = fun _ => 0 := by
      funext n
      exact hpos (u n) (one_div_ne_zero (by positivity))
    have hfu_lim : Tendsto (fun n => f (u n)) atTop (𝓝 (f 0)) :=
      (f.continuous.tendsto 0).comp hu_tendsto
    rw [hfu_zero] at hfu_lim
    exact tendsto_nhds_unique hfu_lim tendsto_const_nhds
  · exact hpos t ht

/-- `vanishingAtZero` is a proper nonzero essential closed ideal of `C(unitInterval, ℂ)`. -/
theorem isClosedEssential_vanishingAtZero : vanishingAtZero.IsClosedEssential :=
  TwoSidedIdeal.isClosedEssential_iff_leftAnnihilator_eq_bot.mpr leftAnnihilator_vanishingAtZero

theorem isEssential_vanishingAtZero : vanishingAtZero.IsEssential :=
  TwoSidedIdeal.isClosedEssential_iff_isEssential.mp isClosedEssential_vanishingAtZero

/-- Because `vanishingAtZero` is essential, `C(unitInterval, ℂ)` embeds isometrically into
`𝓜(ℂ, vanishingAtZero)`. -/
theorem isometry_multiplierHom_vanishingAtZero : Isometry vanishingAtZero.multiplierHom :=
  isClosedEssential_vanishingAtZero.isometry_multiplierHom

/-- `vanishingAtZero` is strictly contained in its double annihilator `⊤`, showing that closed
ideals in C⋆-algebras need not equal their double annihilator. -/
theorem vanishingAtZero_lt_doubleAnnihilator :
    vanishingAtZero < vanishingAtZero.leftAnnihilator.leftAnnihilator := by
  rw [leftAnnihilator_vanishingAtZero, TwoSidedIdeal.leftAnnihilator_bot]
  exact lt_top_iff_ne_top.mpr vanishingAtZero_ne_top

end UnitInterval

end TauCeti.AnnihilatorExample
