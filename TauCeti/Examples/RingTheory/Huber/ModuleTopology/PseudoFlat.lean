/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.RestrictedSeries
public import TauCeti.RingTheory.Huber.Padic.TateAlgebra
public import TauCeti.RingTheory.Huber.Restricted.TateAlgebra
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval

/-!
# Checks and non-examples for pseudoflat modules

Concrete instances, coordinate evaluations, and counterexamples exercising `IsPseudoFlat`,
`isPseudoFlat_zeroAtFilterSubmodule`, `isPseudoFlat_restrictedMvPowerSeriesCompletion`,
`isPseudoFlat_twoSidedRestrictedSubmodule`, `restrictedPowerSeriesTensorToNull`, and
`restrictedLaurentSeriesTensorToNull`:

* compatibility with flatness (`IsPseudoFlat.of_flat`) and degenerate zero modules (`PUnit`);
* `2`-pseudoflatness of the `p`-adic Tate algebra `ℚ_p⟨X₁, …, Xₖ⟩`, the two-sided restricted
  Laurent algebra `ℚ_p⟨T, T⁻¹⟩`, their product, and uncountable null-family modules `c₀(ℝ, ℚ_p)`,
  together with explicit coefficient extraction on pure tensors in both `ℚ_p⟨T⟩ ⊗ M` and
  `ℚ_p⟨T, T⁻¹⟩ ⊗ M`;
* a stably `⊤`-pseudocoherent cyclic quotient `ℚ_p⟨T⟩ ⧸ (T)` over the strongly noetherian Tate
  algebra `ℚ_p⟨T⟩` that is naturally complete and satisfies Corollary 2.4.9(c) bijectivity, yet
  fails both `⊤`-pseudoflatness and `2`-pseudoflatness;
* a formal counterexample (`TauCeti.Examples.exists_banach_projectors_not_isPseudoFlat`) over
  `A = ℚ_p⟨X, Y⟩` refuting the naive projector-only pro-projectivity criterion: an ultrametric
  Banach `A`-module admitting commuting `1`-Lipschitz `A`-linear projectors `πₖ` with finite free
  ranges converging pointwise to the identity, yet failing `m`-pseudoflatness for every `m : ℕ∞`.
-/

public section

noncomputable section

open Filter TensorProduct Topology UniformSpace
open TauCeti.Huber

namespace TauCeti.Examples

section DegenerateAndFlat

-- Every flat module (and in particular every finite free module) is `m`-pseudoflat for all `m`.
example (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (r : ℕ) (m : ℕ∞) :
    IsPseudoFlat A (Fin r → A) m :=
  IsPseudoFlat.of_flat

-- The zero module `PUnit` is `m`-pseudoflat for every `m`.
example (p : ℕ) [Fact p.Prime] (m : ℕ∞) : IsPseudoFlat ℚ_[p] PUnit m :=
  IsPseudoFlat.of_flat

end DegenerateAndFlat

section PadicRestrictedSeries

variable (p : ℕ) [Fact p.Prime]

-- `ℚ_p⟨X₁, …, Xₖ⟩`, `ℚ_p⟨T, T⁻¹⟩`, their product, and uncountable null-family modules `c₀(ℝ, ℚ_p)`
-- are all `2`-pseudoflat over `ℚ_[p]`.
example (k : ℕ) :
    IsPseudoFlat ℚ_[p] (restrictedMvPowerSeriesCompletion k ℚ_[p]) 2 ∧
      IsPseudoFlat ℚ_[p] (twoSidedRestrictedSubmodule ℚ_[p] ℚ_[p]) 2 ∧
      IsPseudoFlat ℚ_[p]
        (restrictedMvPowerSeriesCompletion k ℚ_[p] × twoSidedRestrictedSubmodule ℚ_[p] ℚ_[p]) 2 ∧
      IsPseudoFlat ℚ_[p]
        (Filter.zeroAtFilterSubmodule (β := ℚ_[p]) ℚ_[p] (Filter.cofinite : Filter ℝ)) 2 :=
  ⟨isPseudoFlat_restrictedMvPowerSeriesCompletion k ℚ_[p],
    isPseudoFlat_twoSidedRestrictedSubmodule ℚ_[p],
    (isPseudoFlat_restrictedMvPowerSeriesCompletion k ℚ_[p]).prod
      (isPseudoFlat_twoSidedRestrictedSubmodule ℚ_[p]),
    isPseudoFlat_zeroAtFilterSubmodule ℝ ℚ_[p]⟩

-- Coordinate extraction on the variable `X` in `ℚ_p⟨X⟩` and pure-tensor evaluation into null
-- sequences.
example (m : ℚ_[p]) :
    let X : restrictedMvPowerSeriesCompletion 1 ℚ_[p] :=
      ((weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion 1 ℚ_[p])
    restrictedCoeff (A := ℚ_[p]) 1 X = 1 ∧ restrictedCoeff (A := ℚ_[p]) 0 X = 0 ∧
      (restrictedPowerSeriesTensorToNullEquiv (.of_projective : IsNaturallyComplete ℚ_[p] ℚ_[p])
        (X ⊗ₜ[ℚ_[p]] m)).1 1 = m ∧
      (restrictedPowerSeriesTensorToNull (X ⊗ₜ[ℚ_[p]] m)).1 0 = 0 ∧
      Function.Bijective (restrictedPowerSeriesTensorToNull (A := ℚ_[p]) (M := ℚ_[p])) := by
  intro X
  have h1 : restrictedCoeff (A := ℚ_[p]) 1 X = 1 := by simp [X]
  have h0 : restrictedCoeff (A := ℚ_[p]) 0 X = 0 := by simp [X]
  exact ⟨h1, h0, by simp [h1],
    by rw [coe_restrictedPowerSeriesTensorToNull_tmul, h0, zero_smul],
    restrictedPowerSeriesTensorToNull_bijective .of_projective⟩

-- Pure-tensor evaluation on negative-degree Laurent monomials `a T⁻¹ ⊗ m` in `ℚ_p⟨T, T⁻¹⟩ ⊗ M`.
example (a m : ℚ_[p]) :
    let Tinv : twoSidedRestrictedSubmodule ℚ_[p] ℚ_[p] := twoSidedMonomial (-1) a
    (restrictedLaurentSeriesTensorToNullEquiv (.of_projective : IsNaturallyComplete ℚ_[p] ℚ_[p])
        (Tinv ⊗ₜ[ℚ_[p]] m)).1 (-1) = a • m ∧
      (restrictedLaurentSeriesTensorToNull (Tinv ⊗ₜ[ℚ_[p]] m)).1 1 = 0 ∧
      Function.Bijective (restrictedLaurentSeriesTensorToNull (A := ℚ_[p]) (M := ℚ_[p])) := by
  intro Tinv
  exact ⟨by simp [Tinv, coe_twoSidedMonomial], by simp [Tinv, coe_twoSidedMonomial],
    restrictedLaurentSeriesTensorToNull_bijective .of_projective⟩

end PadicRestrictedSeries

section NonExamples

-- Over the strongly noetherian Tate algebra `A = ℚ_p⟨T⟩`, the non-projective cyclic quotient
-- `Q = A ⧸ (T)` equipped with the module topology is stably `⊤`-pseudocoherent and naturally
-- complete (so Corollary 2.4.9(c) gives bijectivity of `A⟨T⟩ ⊗ Q → c₀(ℕ, Q)`), yet `Q` is neither
-- `⊤`-pseudoflat nor `2`-pseudoflat over `A`.
example (p : ℕ) [Fact p.Prime] :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let X : A :=
      ((weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) : A)
    let Q := A ⧸ Ideal.span ({X} : Set A)
    letI : TopologicalSpace Q := moduleTopology A Q
    haveI : IsModuleTopology A Q := ⟨rfl⟩
    haveI : ContinuousAdd Q := IsModuleTopology.toContinuousAdd A Q
    haveI : ContinuousSMul A Q := IsModuleTopology.toContinuousSMul A Q
    IsStablyPseudoCoherent A Q ⊤ ∧
      Function.Bijective (restrictedPowerSeriesTensorToNull (A := A) (M := Q)) ∧
      ¬ IsPseudoFlat A Q ⊤ ∧ ¬ IsPseudoFlat A Q 2 := by
  intro A X Q
  let : TopologicalSpace Q := moduleTopology A Q; have : IsModuleTopology A Q := ⟨rfl⟩
  have : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup A Q
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : ContinuousSMul A Q := IsModuleTopology.toContinuousSMul A Q
  have : Module.Finite A Q := .of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have hQ_spc : IsStablyPseudoCoherent A Q ⊤ := .of_isStronglyNoetherian
  have : Module.FinitePresentation A Q :=
    IsPseudoCoherentOver.one_iff.mp (hQ_spc.isPseudoCoherentOver.mono le_top)
  have hQ_nc : IsNaturallyComplete A Q := hQ_spc.isNaturallyComplete
  have hX_coeff1 : restrictedCoeff (A := ℚ_[p]) 1 X = 1 := by simp [X]
  have hX_ne : X ≠ 0 := fun h0 ↦
    (one_ne_zero : (1 : ℚ_[p]) ≠ 0) (by simpa [h0] using hX_coeff1.symm)
  have hX_reg : IsSMulRegular A X := fun a b (hab : X * a = X * b) ↦ mul_left_cancel₀ hX_ne hab
  have hX_not_unit : ¬ IsUnit X := fun ⟨u, hu⟩ ↦ by
    have hX_inv : X * (u⁻¹ : Units A) = 1 := by simp [← hu]
    have heq := congrArg (restrictedMvPowerSeriesCompletionEquiv 1 ℚ_[p]) hX_inv
    rw [map_mul, map_one, restrictedMvPowerSeriesCompletionEquiv_coe] at heq
    have hc := congrArg (fun f : weightedRestrictedSubring _ _ ↦
      MvPowerSeries.coeff (0 : Fin 1 →₀ ℕ) f.1) heq
    simp [Subring.coe_mul, coe_weightedX] at hc
  exact ⟨hQ_spc, restrictedPowerSeriesTensorToNull_bijective hQ_nc,
    not_isPseudoFlat_quotient_span_singleton hX_reg hX_not_unit hQ_spc,
    not_isPseudoFlat_quotient_span_singleton hX_reg hX_not_unit (hQ_spc.mono le_top)⟩

end NonExamples

/-! ### Formal counterexample to the projector-only pro-projectivity criterion -/

section ProjectorCounterexample

private abbrev Tate2 (p : ℕ) [Fact p.Prime] :=
  MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 2 ↦ (1 : ℝ))

private def tateVar {p : ℕ} [Fact p.Prime] (i : Fin 2) : Tate2 p :=
  ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ (Finsupp.single i 1) 1⟩

private theorem norm_p_pow_pos (p : ℕ) [Fact p.Prime] (k : ℕ) : 0 < ‖(p : ℚ_[p]) ^ (k + 1)‖ := by
  rw [norm_pow]
  exact pow_pos (norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) _

private theorem norm_p_pow_le_one (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ‖(p : ℚ_[p]) ^ (k + 1)‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

private def evalAt (p : ℕ) [Fact p.Prime] (k : ℕ) : Tate2 p →+* ℚ_[p] :=
  MvPowerSeries.restrictedEval₂ (RingHom.id ℚ_[p]) (fun _ : Fin 2 ↦ (p : ℚ_[p]) ^ (k + 1))
    (fun _ ↦ le_rfl) (fun _ ↦ norm_p_pow_le_one p k)

private def evalNorm (p : ℕ) [Fact p.Prime] (k : ℕ) (h : Tate2 p) : ℝ :=
  max ‖evalAt p k h‖ (‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖h‖)

private theorem evalNorm_nonneg (p : ℕ) [Fact p.Prime] (k : ℕ) (h : Tate2 p) :
    0 ≤ evalNorm p k h :=
  le_trans (norm_nonneg _) (le_max_left _ _)

private theorem evalNorm_zero (p : ℕ) [Fact p.Prime] (k : ℕ) : evalNorm p k 0 = 0 := by
  simp [evalNorm]

private theorem evalNorm_neg (p : ℕ) [Fact p.Prime] (k : ℕ) (h : Tate2 p) :
    evalNorm p k (-h) = evalNorm p k h := by
  simp [evalNorm]

private theorem evalNorm_add_le_max (p : ℕ) [Fact p.Prime] (k : ℕ) (h₁ h₂ : Tate2 p) :
    evalNorm p k (h₁ + h₂) ≤ max (evalNorm p k h₁) (evalNorm p k h₂) := by
  refine max_le ?_ ?_
  · rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · calc
      ‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖h₁ + h₂‖ ≤ ‖(p : ℚ_[p]) ^ (k + 1)‖ * max ‖h₁‖ ‖h₂‖ :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max h₁ h₂) (norm_nonneg _)
      _ = max (‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖h₁‖) (‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖h₂‖) :=
        mul_max_of_nonneg _ _ (norm_nonneg _)
      _ ≤ max (evalNorm p k h₁) (evalNorm p k h₂) :=
        max_le_max (le_max_right _ _) (le_max_right _ _)

private theorem evalNorm_mul_le (p : ℕ) [Fact p.Prime] (k : ℕ) (a h : Tate2 p) :
    evalNorm p k (a * h) ≤ ‖a‖ * evalNorm p k h := by
  refine max_le ?_ ?_
  · rw [map_mul, norm_mul]
    exact mul_le_mul (MvPowerSeries.norm_restrictedEval₂_le _ _ _ _ a) (le_max_left _ _)
      (norm_nonneg _) (norm_nonneg a)
  · calc
      ‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖a * h‖ ≤ ‖(p : ℚ_[p]) ^ (k + 1)‖ * (‖a‖ * ‖h‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le a h) (norm_nonneg _)
      _ = ‖a‖ * (‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖h‖) := by ring
      _ ≤ ‖a‖ * evalNorm p k h := mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg a)

/-- Ultrametric Banach `ℚ_p⟨X, Y⟩`-module of sequences `(fₖ)` with `evalNorm p k (fₖ) → 0`. -/
private structure WeightedC0 (p : ℕ) [Fact p.Prime] where
  toFun : ℕ → Tate2 p
  tendsto_zero : Tendsto (fun k ↦ evalNorm p k (toFun k)) atTop (𝓝 0)

namespace WeightedC0

variable {p : ℕ} [Fact p.Prime]

private theorem ext {f g : WeightedC0 p} (h : ∀ k, f.toFun k = g.toFun k) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact funext h

private theorem bddAbove_range (f : WeightedC0 p) :
    BddAbove (Set.range fun k ↦ evalNorm p k (f.toFun k)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (f.tendsto_zero.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨M, hM⟩ :=
    (((Finset.range N).image (fun k ↦ evalNorm p k (f.toFun k)) : Set ℝ)).toFinite.bddAbove
  refine ⟨max 1 M, ?_⟩
  rintro _ ⟨k, rfl⟩
  by_cases hk : k < N
  · exact le_trans (hM (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk))) (le_max_right _ _)
  · exact le_trans (hN k (not_lt.mp hk)).le (le_max_left _ _)

private instance : Zero (WeightedC0 p) := ⟨⟨0, by simp [evalNorm_zero]⟩⟩
private instance : Neg (WeightedC0 p) :=
  ⟨fun f ↦ ⟨-f.toFun, by simpa [evalNorm_neg] using f.tendsto_zero⟩⟩
private instance : Add (WeightedC0 p) :=
  ⟨fun f g ↦ ⟨f.toFun + g.toFun,
    squeeze_zero (fun k ↦ evalNorm_nonneg p k _) (fun k ↦ evalNorm_add_le_max p k _ _)
      (by simpa using f.tendsto_zero.max g.tendsto_zero)⟩⟩

private instance : AddCommGroup (WeightedC0 p) where
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := ext fun _ ↦ neg_add_cancel _
  add_comm f g := ext fun k ↦ add_comm (f.toFun k) (g.toFun k)

private theorem add_toFun (f g : WeightedC0 p) (k : ℕ) : (f + g).toFun k = f.toFun k + g.toFun k :=
  rfl

private theorem sub_toFun (f g : WeightedC0 p) (k : ℕ) : (f - g).toFun k = f.toFun k - g.toFun k :=
  by rw [sub_eq_add_neg]; exact (sub_eq_add_neg _ _).symm

private instance : Module (Tate2 p) (WeightedC0 p) where
  smul a f := ⟨fun k ↦ a * f.toFun k,
    squeeze_zero (fun k ↦ evalNorm_nonneg p k _) (fun k ↦ evalNorm_mul_le p k a (f.toFun k))
      (by simpa using f.tendsto_zero.const_mul ‖a‖)⟩
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

private theorem smul_toFun (a : Tate2 p) (f : WeightedC0 p) (k : ℕ) :
    (a • f).toFun k = a * f.toFun k := rfl

private def supNorm (f : WeightedC0 p) : ℝ := ⨆ k, evalNorm p k (f.toFun k)

private theorem supNorm_nonneg (f : WeightedC0 p) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun k ↦ evalNorm_nonneg p k (f.toFun k)

private theorem evalNorm_le_supNorm (f : WeightedC0 p) (k : ℕ) :
    evalNorm p k (f.toFun k) ≤ supNorm f :=
  le_ciSup f.bddAbove_range k

private theorem supNorm_le_iff {f : WeightedC0 p} {r : ℝ} :
    supNorm f ≤ r ↔ ∀ k, evalNorm p k (f.toFun k) ≤ r :=
  ⟨fun h k ↦ (evalNorm_le_supNorm f k).trans h, ciSup_le⟩

private theorem supNorm_add_le_max (f g : WeightedC0 p) :
    supNorm (f + g) ≤ max (supNorm f) (supNorm g) :=
  supNorm_le_iff.mpr fun k ↦
    (evalNorm_add_le_max p k _ _).trans
      (max_le_max (evalNorm_le_supNorm f k) (evalNorm_le_supNorm g k))

private instance : NormedAddCommGroup (WeightedC0 p) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := supNorm
      map_zero' := le_antisymm (supNorm_le_iff.mpr fun k ↦ (evalNorm_zero p k).le)
        (supNorm_nonneg 0)
      add_le' f g := (supNorm_add_le_max f g).trans
        (max_le_add_of_nonneg (supNorm_nonneg f) (supNorm_nonneg g))
      neg' f := by simp only [supNorm]; congr 1; ext k; exact evalNorm_neg p k _
      eq_zero_of_map_eq_zero' f hf := ext fun k ↦ by
        have hle : ‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖f.toFun k‖ ≤ 0 :=
          (le_max_right _ _).trans (hf ▸ evalNorm_le_supNorm f k)
        exact norm_eq_zero.mp <| le_antisymm
          (nonpos_of_mul_nonpos_right hle (norm_p_pow_pos p k)) (norm_nonneg _) }

private theorem norm_eq_supNorm (f : WeightedC0 p) : ‖f‖ = supNorm f := rfl

private instance : IsUltrametricDist (WeightedC0 p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm supNorm_add_le_max

private instance : IsBoundedSMul (Tate2 p) (WeightedC0 p) :=
  IsBoundedSMul.of_norm_smul_le fun a f ↦
    supNorm_le_iff.mpr fun k ↦
      (evalNorm_mul_le p k a (f.toFun k)).trans
        (mul_le_mul_of_nonneg_left (evalNorm_le_supNorm f k) (norm_nonneg a))

private instance : CompleteSpace (WeightedC0 p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hcauchy_coord (k : ℕ) : CauchySeq fun n ↦ (u n).toFun k := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε * ‖(p : ℚ_[p]) ^ (k + 1)‖)
      (mul_pos hε (norm_p_pow_pos p k))
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 : ‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖(u m).toFun k - (u n).toFun k‖ <
        ε * ‖(p : ℚ_[p]) ^ (k + 1)‖ := by
      calc
        ‖(p : ℚ_[p]) ^ (k + 1)‖ * ‖(u m).toFun k - (u n).toFun k‖ ≤
            evalNorm p k ((u m - u n).toFun k) := by rw [sub_toFun]; exact le_max_right _ _
        _ ≤ ‖u m - u n‖ := evalNorm_le_supNorm (u m - u n) k
        _ < ε * ‖(p : ℚ_[p]) ^ (k + 1)‖ := by rw [← dist_eq_norm]; exact hN m hm n hn
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_right (by simpa [mul_comm] using h1) (norm_p_pow_pos p k).le
  choose g hg using fun k ↦ cauchySeq_tendsto_of_complete (hcauchy_coord k)
  have hunif (ε : ℝ) (hε : 0 < ε) :
      ∃ N, ∀ m ≥ N, ∀ k, evalNorm p k ((u m).toFun k - g k) ≤ ε := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm k ↦ ?_⟩
    have hc : Continuous (evalNorm p k) :=
      (continuous_norm.comp (MvPowerSeries.continuous_restrictedEval₂ _ _ _ _)).max
        (continuous_const.mul continuous_norm)
    refine le_of_tendsto (hc.continuousAt.tendsto.comp (tendsto_const_nhds.sub (hg k)))
      (eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩)
    dsimp only [Function.comp_apply]; rw [← sub_toFun]
    exact (evalNorm_le_supNorm (u m - u n) k).trans
      ((dist_eq_norm _ _).symm.trans_le (hN m hm n hn).le)
  have hg_zero : Tendsto (fun k ↦ evalNorm p k (g k)) atTop (𝓝 0) := by
    refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun k ↦ hb.trans_le (evalNorm_nonneg p k _),
      fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [(u N).tendsto_zero.eventually (gt_mem_nhds (half_pos hε))] with k hk
    have hsplit : g k = (u N).toFun k + -((u N).toFun k - g k) := by abel
    calc
      evalNorm p k (g k) = evalNorm p k ((u N).toFun k + -((u N).toFun k - g k)) := by rw [← hsplit]
      _ ≤ max (evalNorm p k ((u N).toFun k)) (evalNorm p k ((u N).toFun k - g k)) := by
        simpa only [evalNorm_neg] using
          evalNorm_add_le_max p k ((u N).toFun k) (-((u N).toFun k - g k))
      _ ≤ max (ε / 2) (ε / 2) := max_le_max hk.le (hN N le_rfl k)
      _ < ε := by rw [max_self]; exact half_lt_self hε
  refine ⟨⟨g, hg_zero⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [dist_eq_norm]
  refine (supNorm_le_iff.mpr fun k ↦ ?_).trans_lt (half_lt_self hε)
  rw [sub_toFun]; exact hN m hm k

private def truncProj (n : ℕ) : WeightedC0 p →ₗ[Tate2 p] WeightedC0 p where
  toFun f := ⟨fun k ↦ if k < n then f.toFun k else 0,
    tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ by
      simp [Nat.not_lt.mpr hk, evalNorm_zero]⟩
  map_add' f g := ext fun k ↦ by
    dsimp only; rw [add_toFun, add_toFun]; by_cases hk : k < n <;> simp [hk]
  map_smul' a f := ext fun k ↦ by
    dsimp only; rw [smul_toFun, smul_toFun]; by_cases hk : k < n <;> simp [hk]

private theorem truncProj_toFun (n : ℕ) (f : WeightedC0 p) (k : ℕ) :
    (truncProj n f).toFun k = if k < n then f.toFun k else 0 := rfl

private theorem norm_truncProj_le (n : ℕ) (f : WeightedC0 p) : ‖truncProj n f‖ ≤ ‖f‖ := by
  rw [norm_eq_supNorm, norm_eq_supNorm]
  refine supNorm_le_iff.mpr fun k ↦ ?_
  rw [truncProj_toFun]; split_ifs
  · exact evalNorm_le_supNorm f k
  · rw [evalNorm_zero]; exact supNorm_nonneg f

private theorem truncProj_comp_of_le {k l : ℕ} (hkl : k ≤ l) :
    truncProj (p := p) l ∘ₗ truncProj k = truncProj k ∧
      truncProj (p := p) k ∘ₗ truncProj l = truncProj k := by
  constructor <;> refine LinearMap.ext fun f ↦ ext fun m ↦ ?_
  all_goals
    simp only [LinearMap.comp_apply, truncProj_toFun]
    by_cases h1 : m < k <;> by_cases h2 : m < l <;> simp [h1, h2]; omega

private def rangeTruncProjEquiv (n : ℕ) :
    LinearMap.range (truncProj (p := p) n) ≃ₗ[Tate2 p] (Fin n → Tate2 p) where
  toFun g i := g.1.toFun i.1
  invFun v :=
    let w : WeightedC0 p := ⟨fun k ↦ if h : k < n then v ⟨k, h⟩ else 0,
      tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ by
        simp [Nat.not_lt.mpr hk, evalNorm_zero]⟩
    ⟨w, ⟨w, ext fun k ↦ by
      rw [truncProj_toFun]; dsimp only [w]; by_cases hk : k < n <;> simp [hk]⟩⟩
  left_inv := fun ⟨g, ⟨f, hf⟩⟩ ↦ Subtype.ext <| ext fun k ↦ by
    subst hf; dsimp only; rw [truncProj_toFun]; by_cases hk : k < n <;> simp [hk]
  right_inv v := funext fun ⟨k, hk⟩ ↦ by simp [hk]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tendsto_truncProj (b : WeightedC0 p) :
    Tendsto (fun n ↦ truncProj n b) atTop (𝓝 b) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (b.tendsto_zero.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_eq_supNorm]
  refine (supNorm_le_iff.mpr fun k ↦ ?_).trans_lt (half_lt_self hε)
  rw [sub_toFun, truncProj_toFun]
  by_cases hk : k < n
  · simp [hk, evalNorm_zero, (half_pos hε).le]
  · simp only [hk, ↓reduceIte, zero_sub, evalNorm_neg]
    exact (hN k (le_trans hn (not_lt.mp hk))).le

private def constVar (i : Fin 2) : WeightedC0 p :=
  ⟨fun _ ↦ tateVar i,
    squeeze_zero (g := fun k ↦ ‖(p : ℚ_[p]) ^ (k + 1)‖) (fun k ↦ evalNorm_nonneg p k _)
      (fun k ↦ max_le (by simp [evalAt, tateVar]) (by rw [tateVar, MvPowerSeries.norm_X, mul_one]))
      (by
        simp_rw [norm_pow]
        exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℚ_[p]))
          Padic.norm_p_lt_one).comp (tendsto_add_atTop_nat 1))⟩

private theorem koszul_relation (u v : Tate2 p) (h : u * tateVar 0 + v * tateVar 1 = 0) :
    ∃ a : Tate2 p, u = a * tateVar 1 ∧ v = -(a * tateVar 0) := by
  have hps : (u : MvPowerSeries (Fin 2) ℚ_[p]) * MvPowerSeries.X 0 +
      (v : MvPowerSeries (Fin 2) ℚ_[p]) * MvPowerSeries.X 1 = 0 := by
    simpa [tateVar] using congrArg Subtype.val h
  let aps : MvPowerSeries (Fin 2) ℚ_[p] :=
    fun t ↦ MvPowerSeries.coeff (t + Finsupp.single 1 1) (u : MvPowerSeries _ _)
  have ha_res : MvPowerSeries.IsRestricted (fun _ : Fin 2 ↦ (1 : ℝ)) aps := by
    have hfun : (fun t : Fin 2 →₀ ℕ ↦
          ‖MvPowerSeries.coeff t aps‖ * t.prod (fun _ n ↦ (1 : ℝ) ^ n)) =
        (fun t : Fin 2 →₀ ℕ ↦
          ‖MvPowerSeries.coeff t (u : MvPowerSeries (Fin 2) ℚ_[p])‖ *
            t.prod (fun _ n ↦ (1 : ℝ) ^ n)) ∘ (· + Finsupp.single 1 1) := by
      funext t
      simp only [Function.comp_apply, one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]; rfl
    rw [MvPowerSeries.IsRestricted, hfun]
    exact u.2.comp (add_left_injective (Finsupp.single (1 : Fin 2) 1)).tendsto_cofinite
  have hu : (u : MvPowerSeries (Fin 2) ℚ_[p]) = aps * MvPowerSeries.X 1 := by
    refine MvPowerSeries.ext fun t ↦ ?_
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
    by_cases h1 : Finsupp.single (1 : Fin 2) 1 ≤ t
    · rw [ite_eq_left h1, MvPowerSeries.coeff_apply aps]; dsimp only [aps]
      rw [tsub_add_cancel_of_le h1]
    · rw [ite_eq_right h1]
      have h0 := congrArg (MvPowerSeries.coeff (t + Finsupp.single 0 1)) hps
      rw [map_add, map_zero, MvPowerSeries.X_def, MvPowerSeries.coeff_add_mul_monomial, mul_one,
        MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one] at h0
      have hnot : ¬ Finsupp.single (1 : Fin 2) 1 ≤ t + Finsupp.single 0 1 := fun hle ↦
        h1 fun i ↦ by
          fin_cases i
          · simp
          · simpa using hle 1
      simpa [hnot] using h0
  have hv : (v : MvPowerSeries (Fin 2) ℚ_[p]) = -(aps * MvPowerSeries.X 0) :=
    eq_neg_of_add_eq_zero_right <|
      (mul_right_mem_nonZeroDivisors_eq_zero_iff MvPowerSeries.X_mem_nonZeroDivisors).mp <| by
        calc
          (aps * MvPowerSeries.X 0 + (v : MvPowerSeries (Fin 2) ℚ_[p])) * MvPowerSeries.X 1 =
              (aps * MvPowerSeries.X 1) * MvPowerSeries.X 0 +
                (v : MvPowerSeries (Fin 2) ℚ_[p]) * MvPowerSeries.X 1 := by ring
          _ = 0 := by rw [← hu, hps]
  exact ⟨⟨aps, ha_res⟩, Subtype.ext hu, Subtype.ext hv⟩

private theorem not_isPseudoFlat (m : ℕ∞) : ¬ IsPseudoFlat (Tate2 p) (WeightedC0 p) m := by
  let A := Tate2 p; let B := WeightedC0 p
  let X : A := tateVar 0; let Y : A := tateVar 1
  let I : Ideal A := Ideal.span ({X, Y} : Set A)
  have : IsNoetherianRing A := MvPowerSeries.isNoetherianRing_isRestricted_subring
  have : Module.Finite A (A ⧸ I) := .of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  have hspc : IsStablyPseudoCoherent A (A ⧸ I) m :=
    (IsStablyPseudoCoherent.of_isStronglyNoetherian (A := A) (M := A ⧸ I)).mono le_top
  intro hpf
  have hinj : Function.Injective (I.subtype.rTensor B) :=
    hpf.rTensor_injective I.injective_subtype (Submodule.mkQ_surjective I)
      (LinearMap.exact_subtype_mkQ I) hspc
  let xI : I := ⟨X, Ideal.subset_span (by simp)⟩
  let yI : I := ⟨Y, Ideal.subset_span (by simp)⟩
  let xSeq : B := constVar 0; let ySeq : B := constVar 1
  let z : I ⊗[A] B := xI ⊗ₜ[A] ySeq - yI ⊗ₜ[A] xSeq
  have hz_map : I.subtype.rTensor B z = 0 := by
    have hsmul : X • ySeq = Y • xSeq := ext fun _ ↦ mul_comm X Y
    simp only [z, map_sub, LinearMap.rTensor_tmul, Submodule.coe_subtype, xI, yI]
    calc
      X ⊗ₜ[A] ySeq - Y ⊗ₜ[A] xSeq = (X • (1 : A)) ⊗ₜ[A] ySeq - (Y • (1 : A)) ⊗ₜ[A] xSeq := by
        simp only [smul_eq_mul, mul_one]
      _ = (1 : A) ⊗ₜ[A] (X • ySeq) - (1 : A) ⊗ₜ[A] (Y • xSeq) := by
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      _ = 0 := by rw [hsmul, sub_self]
  have hz_zero : z = 0 := hinj (hz_map.trans (map_zero _).symm)
  let relMap : B →ₗ[A] B × B :=
    LinearMap.prod (LinearMap.lsmul A B Y) (-(LinearMap.lsmul A B X))
  let q := (LinearMap.range relMap).mkQ
  let Q := (B × B) ⧸ LinearMap.range relMap
  let φ : (Fin 2 → A) →ₗ[A] I :=
    { toFun v := ⟨v 0 * X + v 1 * Y, Ideal.mem_span_pair.mpr ⟨v 0, v 1, rfl⟩⟩
      map_add' _ _ := Subtype.ext (by simp only [Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' _ _ := Subtype.ext (by
        simp only [RingHom.id_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]; ring) }
  have hφ_surj : Function.Surjective φ := fun ⟨_, hr⟩ ↦ by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hr
    exact ⟨![u, v], Subtype.ext huv⟩
  let ψ₀ : (Fin 2 → A) →ₗ[A] B →ₗ[A] Q :=
    { toFun v := q ∘ₗ LinearMap.prod (LinearMap.lsmul A B (v 0)) (LinearMap.lsmul A B (v 1))
      map_add' v w := LinearMap.ext fun b ↦ by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.prod_apply,
          Function.prod_apply, LinearMap.lsmul_apply, Pi.add_apply]
        rw [← map_add, Prod.mk_add_mk, add_smul, add_smul]
      map_smul' a v := LinearMap.ext fun b ↦ by
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          LinearMap.prod_apply, Function.prod_apply, LinearMap.lsmul_apply, Pi.smul_apply,
          smul_eq_mul]
        rw [← map_smul, Prod.smul_mk, mul_smul, mul_smul] }
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ₀ := fun v hv ↦ by
    obtain ⟨a, hu, hv'⟩ := koszul_relation (v 0) (v 1) (congrArg Subtype.val hv)
    refine LinearMap.ext fun b ↦ ?_
    simp only [ψ₀, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.lsmul_apply, LinearMap.zero_apply]
    dsimp only [q]; rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨a • b, Prod.ext ?_ ?_⟩
    · simp only [relMap, LinearMap.prod_apply, Function.prod_apply, LinearMap.lsmul_apply]
      rw [hu, mul_comm, mul_smul]
    · simp only [relMap, LinearMap.prod_apply, Function.prod_apply, LinearMap.neg_apply,
        LinearMap.lsmul_apply]
      rw [hv', neg_smul, mul_comm, mul_smul]
  let eI : ((Fin 2 → A) ⧸ LinearMap.ker φ) ≃ₗ[A] I := φ.quotKerEquivOfSurjective hφ_surj
  let ψ : I →ₗ[A] B →ₗ[A] Q :=
    (Submodule.liftQ (LinearMap.ker φ) ψ₀ hker).comp eI.symm.toLinearMap
  have hψ (v : Fin 2 → A) (b : B) : ψ (φ v) b = q (v 0 • b, v 1 • b) := by
    have hv : φ v = eI (Submodule.Quotient.mk v) := rfl
    rw [hv]
    simp only [ψ, ψ₀, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.prod_apply, Function.prod_apply, LinearMap.lsmul_apply]
  have hxI : xI = φ ![1, 0] := Subtype.ext (by simp [φ, xI])
  have hyI : yI = φ ![0, 1] := Subtype.ext (by simp [φ, yI])
  have hQ_zero : q (ySeq, -xSeq) = 0 := by
    have hlift := congrArg (TensorProduct.lift ψ) hz_zero
    simp only [z, hxI, hyI, map_sub, TensorProduct.lift.tmul, map_zero, hψ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, zero_smul] at hlift
    calc
      q (ySeq, -xSeq) = q ((ySeq, 0) - (0, xSeq)) := by simp [Prod.mk_sub_mk]
      _ = q (ySeq, 0) - q (0, xSeq) := map_sub q _ _
      _ = 0 := hlift
  obtain ⟨b, hb⟩ : (ySeq, -xSeq) ∈ LinearMap.range relMap :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range relMap)).mp hQ_zero
  have hxb : X • b = xSeq := neg_inj.mp (congrArg Prod.snd hb)
  have hb_one (k : ℕ) : b.toFun k = 1 := by
    have hk : X * b.toFun k = X := congrArg (fun f : B ↦ f.toFun k) hxb
    have hk' := congrArg Subtype.val hk
    simp only [Subring.coe_mul, X, tateVar] at hk'
    exact Subtype.ext <| sub_eq_zero.mp <|
      (mul_right_mem_nonZeroDivisors_eq_zero_iff MvPowerSeries.X_mem_nonZeroDivisors).mp <| by
        calc
          ((b.toFun k : MvPowerSeries (Fin 2) ℚ_[p]) - 1) * MvPowerSeries.X 0 =
              MvPowerSeries.X 0 * (b.toFun k : MvPowerSeries (Fin 2) ℚ_[p]) -
                MvPowerSeries.X 0 := by
            ring
          _ = 0 := sub_eq_zero.mpr hk'
  have h1le : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto b.tendsto_zero (Eventually.of_forall fun k ↦ by
      rw [hb_one k]; exact le_trans (by simp : (1 : ℝ) = ‖evalAt p k 1‖).le (le_max_left _ _))
  linarith

end WeightedC0

/-- **Counterexample to the naive projector-only pro-projectivity criterion.**
Over the strongly noetherian complete ultrametric Tate algebra `A = ℚ_p⟨X, Y⟩`, there exists an
ultrametric Banach `A`-module `B` (complete, Hausdorff, first-countable, bounded scalar action)
admitting a sequence of commuting `1`-Lipschitz (hence continuous and equicontinuous) `A`-linear
projectors `π : ℕ → (B →ₗ[A] B)` whose images are finite free
(`LinearMap.range (π k) ≃ₗ[A] (Fin k → A)`, hence finite projective) and which satisfy
`π k b → b` for every `b : B`, yet `B` fails `IsPseudoFlat A B m` for every `m : ℕ∞`
(in particular for `m = 2` and `m = ⊤`). -/
theorem exists_banach_projectors_not_isPseudoFlat (p : ℕ) [Fact p.Prime] :
    let A := MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 2 ↦ (1 : ℝ))
    ∃ (B : Type) (_ : NormedAddCommGroup B) (_ : IsUltrametricDist B) (_ : CompleteSpace B)
      (_ : Module A B) (_ : IsBoundedSMul A B) (π : ℕ → (B →ₗ[A] B)),
      (∀ k, Continuous (π k)) ∧
      (∀ k b, ‖π k b‖ ≤ ‖b‖) ∧
      (∀ k, Nonempty (LinearMap.range (π k) ≃ₗ[A] (Fin k → A))) ∧
      (∀ k, Module.Finite A (LinearMap.range (π k)) ∧
        Module.Projective A (LinearMap.range (π k))) ∧
      (∀ k l, k ≤ l → π l ∘ₗ π k = π k ∧ π k ∘ₗ π l = π k) ∧
      (∀ b : B, Tendsto (fun k ↦ π k b) atTop (𝓝 b)) ∧
      (∀ m : ℕ∞, ¬ IsPseudoFlat A B m) :=
  ⟨WeightedC0 p, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    WeightedC0.truncProj,
    fun n ↦ AddMonoidHomClass.continuous_of_bound (WeightedC0.truncProj n) 1 fun f ↦ by
      simpa using WeightedC0.norm_truncProj_le n f,
    WeightedC0.norm_truncProj_le,
    fun k ↦ ⟨WeightedC0.rangeTruncProjEquiv k⟩,
    fun k ↦ ⟨Module.Finite.equiv (WeightedC0.rangeTruncProjEquiv k).symm,
      Module.Projective.of_equiv (WeightedC0.rangeTruncProjEquiv k).symm⟩,
    fun _ _ hkl ↦ WeightedC0.truncProj_comp_of_le hkl,
    WeightedC0.tendsto_truncProj,
    WeightedC0.not_isPseudoFlat⟩

end ProjectorCounterexample

end TauCeti.Examples
