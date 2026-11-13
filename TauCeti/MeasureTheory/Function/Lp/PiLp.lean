/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Linear isometric equivalence between `Lp` of a finite `PiLp` and `PiLp` of `Lp`

For a finite index type `ι` and any exponent `1 ≤ p ≤ ∞`, a measurable function into `PiLp p E`
belongs to `Lp (PiLp p E) p μ` iff each coordinate belongs to `Lp (E i) p μ`
(`MeasureTheory.memLp_piLp_iff`), with identical norm by finite-sum integration for `p < ∞` and
commuting finite and essential suprema for `p = ∞`.

This file bundles that correspondence as `MeasureTheory.Lp.piLpEquiv`, a linear isometry equivalence
`Lp (PiLp p E) p μ ≃ₗᵢ[𝕜] PiLp p (fun i ↦ Lp (E i) p μ)` over any normed ring `𝕜` acting boundedly
on the fibres (unitary at `p = 2` over `ℝ` or `ℂ`), together with isometric coordinate inclusion
`MeasureTheory.Lp.piLpSingleLI`, the coordinate sum `MeasureTheory.Lp.eq_sum_piLpSingleLI`,
`compLpL` and Hölder-scalar compatibility (`MeasureTheory.Lp.piLpEquiv_apply_eq_compLpL`,
`MeasureTheory.Lp.piLpSingleLI_apply_eq_compLpL`, `MeasureTheory.Lp.piLpEquiv_lpSMul`), and the
coordinatewise submodule restriction `MeasureTheory.Lp.subspacePiLpEquiv`.
-/

public noncomputable section

open ENNReal
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

section NormedRing

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] {μ : Measure α}

private theorem memLp_toLp_coord (g : ∀ i, Lp (E i) p μ) :
    MemLp (fun x ↦ WithLp.toLp p fun i ↦ g i x) p μ :=
  MemLp.of_eval_piLp (q := p) (f := fun x ↦ WithLp.toLp p fun i ↦ g i x) fun i ↦ Lp.memLp (g i)

private theorem norm_toLp_eval_eq (f : Lp (PiLp p E) p μ) :
    ‖WithLp.toLp p (fun i ↦ ((Lp.memLp f).eval_piLp i).toLp)‖ = ‖f‖ := by
  set g : ∀ i, Lp (E i) p μ := fun i ↦ ((Lp.memLp f).eval_piLp i).toLp
  have hg (i : ι) : ∀ᵐ x ∂μ, g i x = f x i := ((Lp.memLp f).eval_piLp i).coeFn_toLp
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hf0 : f = 0 := Lp.ext <| (Lp.coeFn_zero (PiLp p E) p μ).mono fun _ hx ↦
      hx ▸ Subsingleton.elim _ _
    simp [hf0, Subsingleton.elim (WithLp.toLp p g) 0]
  rcases eq_or_ne p ∞ with rfl | hp
  · refine le_antisymm ?_ ?_
    · rw [PiLp.norm_eq_ciSup]
      refine ciSup_le fun i ↦ Lp.norm_top_le_of_ae_bound (norm_nonneg f) ?_
      filter_upwards [hg i, Lp.ae_norm_le_norm_top f] with x hgi hfx
      exact hgi ▸ (PiLp.norm_apply_le (f x) i).trans hfx
    · refine Lp.norm_top_le_of_ae_bound (norm_nonneg (WithLp.toLp ∞ g)) ?_
      filter_upwards [ae_all_iff.mpr fun i ↦ (hg i).and (Lp.ae_norm_le_norm_top (g i))] with x hx
      rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
      exact ciSup_le fun i ↦
        (hx i).1 ▸ (hx i).2.trans (le_ciSup (Set.finite_range fun j ↦ ‖g j‖).bddAbove i)
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have hpow : (∑ i, ‖g i‖ ^ p.toReal) = ‖f‖ ^ p.toReal := by
      calc ∑ i, ‖g i‖ ^ p.toReal
          = ∑ i, ∫ x, ‖g i x‖ ^ p.toReal ∂μ := Finset.sum_congr rfl fun i _ ↦
              (Lp.integral_norm_rpow_eq_norm_rpow hp0 hp (g i)).symm
        _ = ∑ i, ∫ x, ‖f x i‖ ^ p.toReal ∂μ := Finset.sum_congr rfl fun i _ ↦
              integral_congr_ae <| (hg i).mono fun _ hgi ↦ by dsimp only; rw [hgi]
        _ = ∫ x, ∑ i, ‖f x i‖ ^ p.toReal ∂μ := (integral_finsetSum _ fun i _ ↦
              ((Lp.memLp f).eval_piLp i).integrable_norm_rpow hp0 hp).symm
        _ = ∫ x, ‖f x‖ ^ p.toReal ∂μ := integral_congr_ae <| .of_forall fun x ↦ by
              dsimp only; rw [PiLp.norm_eq_sum hr, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦
                Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hr.ne', Real.rpow_one]
        _ = ‖f‖ ^ p.toReal := Lp.integral_norm_rpow_eq_norm_rpow hp0 hp f
    rw [PiLp.norm_eq_sum hr, hpow, ← Real.rpow_mul (norm_nonneg f), mul_one_div_cancel hr.ne',
      Real.rpow_one]

variable (μ) in
/-- Coordinatewise evaluation identifies `Lp (PiLp p E) p μ` linear-isometrically with
`PiLp p (fun i ↦ Lp (E i) p μ)` for `1 ≤ p ≤ ∞` on a finite index type `ι`. -/
def piLpEquiv : Lp (PiLp p E) p μ ≃ₗᵢ[𝕜] PiLp p (fun i ↦ Lp (E i) p μ) where
  toFun f := WithLp.toLp p fun i ↦ ((Lp.memLp f).eval_piLp i).toLp
  invFun g := (memLp_toLp_coord p E fun i ↦ g i).toLp
  map_add' f₁ f₂ := by
    ext i : 1; simp only [PiLp.add_apply, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ ((Lp.coeFn_add f₁ f₂).mono fun _ hx ↦ by dsimp only; rw [hx]; rfl)
  map_smul' c f := by
    ext i : 1; simp only [RingHom.id_apply, PiLp.smul_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ ((Lp.coeFn_smul c f).mono fun _ hx ↦ by dsimp only; rw [hx]; rfl)
  left_inv f := Lp.ext <| by
    filter_upwards [(memLp_toLp_coord p E fun i ↦ ((Lp.memLp f).eval_piLp i).toLp).coeFn_toLp,
      ae_all_iff.mpr fun i ↦ ((Lp.memLp f).eval_piLp i).coeFn_toLp] with x hx hcoord
    exact hx.trans (PiLp.ext hcoord)
  right_inv g := by
    ext i : 1; apply Lp.ext
    have hmem := memLp_toLp_coord p E fun j ↦ g j
    filter_upwards [((Lp.memLp hmem.toLp).eval_piLp i).coeFn_toLp, hmem.coeFn_toLp] with x h₁ h₂
    rw [PiLp.toLp_apply, h₁, h₂, PiLp.toLp_apply]
  norm_map' := norm_toLp_eval_eq p E

variable (μ) in
/-- Isometric coordinate inclusion `Lp (E i) p μ →ₗᵢ[𝕜] Lp (PiLp p E) p μ` into slot `i`. -/
def piLpSingleLI [DecidableEq ι] (i : ι) : Lp (E i) p μ →ₗᵢ[𝕜] Lp (PiLp p E) p μ :=
  (piLpEquiv p 𝕜 E μ).symm.toLinearIsometry.comp
    (PiLp.singleLI (𝕜 := 𝕜) p (fun j ↦ Lp (E j) p μ) i)

variable {p 𝕜 E}

/-- Each coordinate of `piLpEquiv` agrees almost everywhere with pointwise coordinate evaluation. -/
theorem coeFn_piLpEquiv_apply (f : Lp (PiLp p E) p μ) (i : ι) :
    piLpEquiv p 𝕜 E μ f i =ᵐ[μ] fun x ↦ f x i :=
  ((Lp.memLp f).eval_piLp i).coeFn_toLp

/-- The inverse of `piLpEquiv` assembles a family of `Lp` functions coordinatewise a.e. -/
theorem coeFn_piLpEquiv_symm (g : PiLp p (fun i ↦ Lp (E i) p μ)) :
    (piLpEquiv p 𝕜 E μ).symm g =ᵐ[μ] fun x ↦ WithLp.toLp p fun i ↦ g i x :=
  (memLp_toLp_coord p E fun i ↦ g i).coeFn_toLp

/-- On `PiLp.single p i h`, `(piLpEquiv p 𝕜 E μ).symm` acts pointwise by `PiLp.single` a.e. -/
theorem coeFn_piLpEquiv_symm_single [DecidableEq ι] (i : ι) (h : Lp (E i) p μ) :
    (piLpEquiv p 𝕜 E μ).symm (PiLp.single p i h) =ᵐ[μ] fun x ↦ PiLp.single p i (h x) := by
  have hall : ∀ᵐ x ∂μ, ∀ j, (PiLp.single p i h : PiLp p fun j ↦ Lp (E j) p μ) j x =
      (PiLp.single p i (h x) : PiLp p E) j := ae_all_iff.mpr fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simp
    · exact (Lp.coeFn_zero (E j) p μ).mono fun _ hx ↦ by simpa [Pi.single_eq_of_ne hj] using hx
  filter_upwards [coeFn_piLpEquiv_symm (𝕜 := 𝕜) (PiLp.single p i h), hall] with x hx hcoord
  exact hx.trans (PiLp.ext hcoord)

/-- `piLpSingleLI` unfolds to `(piLpEquiv p 𝕜 E μ).symm` applied to `PiLp.single`. -/
theorem piLpSingleLI_eq_symm_single [DecidableEq ι] (i : ι) (h : Lp (E i) p μ) :
    piLpSingleLI p 𝕜 E μ i h = (piLpEquiv p 𝕜 E μ).symm (PiLp.single p i h) := by
  simp [piLpSingleLI]

/-- `piLpEquiv` sends `piLpSingleLI p 𝕜 E μ i h` to `PiLp.single p i h`. -/
@[simp] theorem piLpEquiv_piLpSingleLI [DecidableEq ι] (i : ι) (h : Lp (E i) p μ) :
    piLpEquiv p 𝕜 E μ (piLpSingleLI p 𝕜 E μ i h) = PiLp.single p i h := by
  rw [piLpSingleLI_eq_symm_single, LinearIsometryEquiv.apply_symm_apply]

/-- `piLpSingleLI` acts pointwise almost everywhere by `PiLp.single`. -/
theorem coeFn_piLpSingleLI [DecidableEq ι] (i : ι) (h : Lp (E i) p μ) :
    piLpSingleLI p 𝕜 E μ i h =ᵐ[μ] fun x ↦ PiLp.single p i (h x) := by
  rw [piLpSingleLI_eq_symm_single (𝕜 := 𝕜)]; exact coeFn_piLpEquiv_symm_single (𝕜 := 𝕜) i h

/-- Every `f : Lp (PiLp p E) p μ` is the finite sum of its coordinate inclusions `piLpSingleLI`. -/
theorem eq_sum_piLpSingleLI [DecidableEq ι] (f : Lp (PiLp p E) p μ) :
    f = ∑ i, piLpSingleLI p 𝕜 E μ i (piLpEquiv p 𝕜 E μ f i) :=
  (piLpEquiv p 𝕜 E μ).injective <| by
    simpa only [map_sum, piLpEquiv_piLpSingleLI] using
      (PiLp.univ_sum_single (piLpEquiv p 𝕜 E μ f)).symm

/-- Coordinate evaluation via `piLpEquiv` commutes with heterogeneous `Lp` scalar multiplication. -/
theorem piLpEquiv_lpSMul {q : ℝ≥0∞} [HolderTriple q p p] (a : Lp 𝕜 q μ) (f : Lp (PiLp p E) p μ)
    (i : ι) :
    piLpEquiv p 𝕜 E μ (a • f : Lp (PiLp p E) p μ) i =
      (a • piLpEquiv p 𝕜 E μ f i : Lp (E i) p μ) := Lp.ext <| by
  filter_upwards [coeFn_piLpEquiv_apply (𝕜 := 𝕜) (a • f : Lp (PiLp p E) p μ) i,
    Lp.coeFn_lpSMul (r := p) a f, Lp.coeFn_lpSMul (r := p) a (piLpEquiv p 𝕜 E μ f i),
    coeFn_piLpEquiv_apply (𝕜 := 𝕜) f i] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', PiLp.smul_apply, h₄]

private theorem norm_toLp_subspace_eq (N : ∀ i, Submodule 𝕜 (Lp (E i) p μ))
    (g : PiLp p (fun i ↦ Lp (E i) p μ)) (hg : ∀ i, g i ∈ N i) :
    ‖WithLp.toLp p (fun i ↦ (⟨g i, hg i⟩ : ↥(N i)))‖ = ‖g‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · exact absurd (Fact.out : (1 : ℝ≥0∞) ≤ 0) (by norm_num)
  · simp [PiLp.norm_eq_ciSup]
  · simp [PiLp.norm_eq_sum hp]

/-- Linear isometric identification of a submodule `M` of `Lp (PiLp p E) p μ` characterized
coordinatewise under `piLpEquiv` with `PiLp p (fun i ↦ ↥(N i))`. -/
def subspacePiLpEquiv (M : Submodule 𝕜 (Lp (PiLp p E) p μ)) (N : ∀ i, Submodule 𝕜 (Lp (E i) p μ))
    (hMN : ∀ f, f ∈ M ↔ ∀ i, piLpEquiv p 𝕜 E μ f i ∈ N i) :
    ↥M ≃ₗᵢ[𝕜] PiLp p (fun i ↦ ↥(N i)) where
  toFun f := WithLp.toLp p fun i ↦ ⟨piLpEquiv p 𝕜 E μ f.1 i, (hMN f.1).mp f.2 i⟩
  invFun g := ⟨(piLpEquiv p 𝕜 E μ).symm (WithLp.toLp p fun i ↦ (g i : Lp (E i) p μ)),
    (hMN _).mpr fun i ↦ by rw [LinearIsometryEquiv.apply_symm_apply]; exact (g i).2⟩
  map_add' _ _ := by ext i : 2; simp [map_add]
  map_smul' _ _ := by ext i : 2; simp [map_smul]
  left_inv f := Subtype.ext <| (piLpEquiv p 𝕜 E μ).symm_apply_apply f.1
  right_inv _ := by ext i : 2; simp
  norm_map' f := (norm_toLp_subspace_eq N (piLpEquiv p 𝕜 E μ f.1) ((hMN f.1).mp f.2)).trans
    ((LinearIsometryEquiv.norm_map _ f.1).trans (Submodule.norm_coe f))

/-- Coordinatewise evaluation of `subspacePiLpEquiv` in `Lp (E i) p μ`. -/
@[simp] theorem coe_subspacePiLpEquiv_apply (M : Submodule 𝕜 (Lp (PiLp p E) p μ))
    (N : ∀ i, Submodule 𝕜 (Lp (E i) p μ)) (hMN : ∀ f, f ∈ M ↔ ∀ i, piLpEquiv p 𝕜 E μ f i ∈ N i)
    (f : ↥M) (i : ι) :
    (subspacePiLpEquiv M N hMN f i : Lp (E i) p μ) = piLpEquiv p 𝕜 E μ f.1 i := (rfl)

/-- Coordinatewise evaluation of `(subspacePiLpEquiv M N hMN).symm` under `piLpEquiv`. -/
@[simp] theorem piLpEquiv_coe_subspacePiLpEquiv_symm (M : Submodule 𝕜 (Lp (PiLp p E) p μ))
    (N : ∀ i, Submodule 𝕜 (Lp (E i) p μ)) (hMN : ∀ f, f ∈ M ↔ ∀ i, piLpEquiv p 𝕜 E μ f i ∈ N i)
    (g : PiLp p (fun i ↦ ↥(N i))) (i : ι) :
    piLpEquiv p 𝕜 E μ ((subspacePiLpEquiv M N hMN).symm g : Lp (PiLp p E) p μ) i =
      (g i : Lp (E i) p μ) := by
  rw [← coe_subspacePiLpEquiv_apply M N hMN, LinearIsometryEquiv.apply_symm_apply]

/-- On `PiLp.single`, `(subspacePiLpEquiv M N hMN).symm` embeds via `(piLpEquiv p 𝕜 E μ).symm`. -/
theorem coe_subspacePiLpEquiv_symm_single [DecidableEq ι] (M : Submodule 𝕜 (Lp (PiLp p E) p μ))
    (N : ∀ i, Submodule 𝕜 (Lp (E i) p μ)) (hMN : ∀ f, f ∈ M ↔ ∀ i, piLpEquiv p 𝕜 E μ f i ∈ N i)
    (j : ι) (h : ↥(N j)) :
    ((subspacePiLpEquiv M N hMN).symm (PiLp.single p j h) : Lp (PiLp p E) p μ) =
      (piLpEquiv p 𝕜 E μ).symm (PiLp.single p j (h : Lp (E j) p μ)) := by
  apply (piLpEquiv p 𝕜 E μ).injective; rw [LinearIsometryEquiv.apply_symm_apply]; ext k : 1
  rw [piLpEquiv_coe_subspacePiLpEquiv_symm M N hMN]; rcases eq_or_ne k j with rfl | hkj <;> simp [*]

end NormedRing

section NontriviallyNormedField

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {μ : Measure α}

/-- Over a nontrivially normed field, coordinate evaluation is `(PiLp.proj p E i).compLpL p μ`. -/
theorem piLpEquiv_apply_eq_compLpL (f : Lp (PiLp p E) p μ) (i : ι) :
    piLpEquiv p 𝕜 E μ f i = (PiLp.proj (𝕜 := 𝕜) p E i).compLpL p μ f := Lp.ext <| by
  filter_upwards [coeFn_piLpEquiv_apply (𝕜 := 𝕜) f i, (PiLp.proj (𝕜 := 𝕜) p E i).coeFn_compLpL f]
    with x h₁ h₂
  rw [h₁, h₂, PiLp.proj_apply]

/-- Over a nontrivially normed field, `piLpSingleLI` is `(PiLp.singleCLM p E i).compLpL p μ`. -/
theorem piLpSingleLI_apply_eq_compLpL [DecidableEq ι] (i : ι) (h : Lp (E i) p μ) :
    piLpSingleLI p 𝕜 E μ i h = (PiLp.singleCLM (𝕜 := 𝕜) p E i).compLpL p μ h := Lp.ext <| by
  filter_upwards [coeFn_piLpSingleLI (𝕜 := 𝕜) i h, (PiLp.singleCLM (𝕜 := 𝕜) p E i).coeFn_compLpL h]
    with x h₁ h₂
  rw [h₁, h₂, PiLp.singleCLM_apply]

end NontriviallyNormedField

end MeasureTheory.Lp
