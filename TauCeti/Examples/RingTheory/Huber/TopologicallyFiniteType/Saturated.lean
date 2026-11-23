/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Huber.CompleteRankOneBase
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Saturated

import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Examples of saturated submodules, Artin–Rees, and adhesiveness

* Over the `p`-adic base `ℤ_[p]`, every `p`-saturated submodule of `Fin 3 → ℤ_[p]⟨ξ₁, ξ₂⟩` is
  finitely generated, `(p)`-adically complete, and closed in the `(p)`-adic module topology.
* For the non-admissible algebra `A = ℤ_[p]⟨T⟩ ⧸ (p² T)`, which has genuine `(p²)`-torsion
  witnessed by the class of `T`, the generic fibre `A[1/p]` is noetherian, `A` is `(p)`-adically
  complete, its `(p)`-primary torsion ideal `A[p^∞]` is nonzero and finitely generated, and
  `A ⧸ A[p^∞]` is finitely presented over `A`.
* Over the non-noetherian complete rank-one valuation base `𝓞_ℂ_[p]`, the maximal ideal
  `𝔪 ⊆ 𝓞_ℂ_[p]` is not `p`-saturated (`p • 1 ∈ 𝔪`, `1 ∉ 𝔪`) and is not finitely generated,
  showing that the `ϖ`-saturation hypothesis in
  `TauCeti.Huber.IsTopologicallyFinitePresentation.fg_of_forall_smul_mem` cannot be omitted.
  Nevertheless, `𝔪` still satisfies the Artin–Rees bound and carries the subspace `(p)`-adic
  topology from `𝓞_ℂ_[p]`, illustrating that those properties require neither saturation nor finite
  generation.
-/

public section

namespace TauCeti.HuberExamples

open IsLocalRing TauCeti TauCeti.Huber Topology

local instance (p : ℕ) [Fact p.Prime] : IsCompleteRankOneBase ℤ_[p] (p : ℤ_[p]) :=
  isCompleteRankOneBase_padicInt p

local instance (p : ℕ) [Fact p.Prime] : NonarchimedeanRing ℤ_[p] :=
  IsCompleteRankOneBase.nonarchimedeanRing (p : ℤ_[p])

local instance (p : ℕ) [Fact p.Prime] : IsCompleteRankOneBase 𝓞_ℂ_[p] (p : 𝓞_ℂ_[p]) :=
  isCompleteRankOneBase_padicComplexInt p

local instance (p : ℕ) [Fact p.Prime] : NonarchimedeanRing 𝓞_ℂ_[p] :=
  IsCompleteRankOneBase.nonarchimedeanRing (p : 𝓞_ℂ_[p])

-- Over `ℤ_[p]⟨ξ₁, ξ₂⟩`, every `p`-saturated submodule of `Fin 3 → ℤ_[p]⟨ξ₁, ξ₂⟩` is finitely
-- generated, `(p)`-adically complete, and closed in the `(p)`-adic module topology.
example (p : ℕ) [Fact p.Prime]
    (M : Submodule (restrictedMvPowerSeriesCompletion 2 ℤ_[p])
      (Fin 3 → restrictedMvPowerSeriesCompletion 2 ℤ_[p]))
    (hsat : ∀ x, (p : ℤ_[p]) • x ∈ M → x ∈ M) :
    let P := restrictedMvPowerSeriesCompletion 2 ℤ_[p]
    let Ip : Ideal P := Ideal.span {algebraMap ℤ_[p] P (p : ℤ_[p])}
    let _ : TopologicalSpace (Fin 3 → P) := Ip.adicModuleTopology (Fin 3 → P)
    M.FG ∧ IsAdicComplete Ip M ∧ IsClosed (M : Set (Fin 3 → P)) := by
  intro P Ip _
  have := IsCompleteRankOneBase.isAdicRing (p : ℤ_[p])
  have hP := isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion ℤ_[p] 2
  have hfg : M.FG := hP.fg_of_forall_smul_mem (p : ℤ_[p]) hsat
  exact ⟨hfg, hP.isAdicComplete_submodule_of_fg (p : ℤ_[p]) hfg,
    hP.isClosed_adicModuleTopology_of_fg (p : ℤ_[p]) hfg⟩

-- For `A = ℤ_[p]⟨T⟩ ⧸ (p² T)`, the generic fibre `A[1/p]` is noetherian, `A` is `(p)`-adically
-- complete, its `(p)`-primary torsion ideal `A[p^∞]` is nonzero and finitely generated, and
-- `A ⧸ A[p^∞]` is finitely presented over `A`.
example (p : ℕ) [Fact p.Prime] :
    let P := restrictedMvPowerSeriesCompletion 1 ℤ_[p]
    let T : P := ((weightedX (fun _ : Fin 1 ↦ ({1} : Set ℤ_[p])) isWeightFamily_one_weight 0 :
      weightedRestrictedSubring _ _) : P)
    let A := P ⧸ Ideal.span {algebraMap ℤ_[p] P (p : ℤ_[p]) ^ 2 * T}
    let Ip : Ideal A := Ideal.span {algebraMap ℤ_[p] A (p : ℤ_[p])}
    IsNoetherianRing (Localization.Away (algebraMap ℤ_[p] A (p : ℤ_[p]))) ∧
      IsAdicComplete Ip A ∧
      Ip.primaryComponent A ≠ ⊥ ∧
      (Ip.primaryComponent A).FG ∧
      Module.FinitePresentation A (A ⧸ Ip.primaryComponent A) := by
  intro P T A Ip
  have := IsCompleteRankOneBase.isAdicRing (p : ℤ_[p])
  have hA : IsTopologicallyFinitePresentation ℤ_[p] A :=
    (isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion ℤ_[p] 1).quotient
      (Submodule.fg_span_singleton _)
  refine ⟨hA.isNoetherianRing_localization_away (p : ℤ_[p]), hA.isAdicComplete (p : ℤ_[p]),
    ?_, hA.fg_primaryComponent (p : ℤ_[p]),
    hA.finitePresentation_quotient_primaryComponent (p : ℤ_[p])⟩
  -- The class of `T` lies in `A[p^∞]` (killed by `p²`) and is nonzero (evaluated at `T = 1`).
  have hT_mem : Ideal.Quotient.mk _ T ∈ Ip.primaryComponent A := by
    rw [Ideal.mem_primaryComponent_span_singleton_iff]
    refine ⟨2, ?_⟩
    rw [smul_eq_mul, ← Ideal.Quotient.mk_algebraMap, ← map_pow (Ideal.Quotient.mk _),
      ← map_mul (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  intro hbot
  have hT0 : (Ideal.Quotient.mk _ T : A) = 0 := by simpa [hbot] using hT_mem
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hT0
  obtain ⟨c, hc⟩ := hT0
  let _ : UniformSpace ℤ_[p] := IsTopologicalAddGroup.rightUniformSpace ℤ_[p]
  have : IsUniformAddGroup ℤ_[p] := isUniformAddGroup_of_addCommGroup
  obtain ⟨ε, ⟨-, hεA, hεT⟩, -⟩ :=
    existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
      (k := 1) (φ := RingHom.id ℤ_[p]) continuous_id fun _ ↦ 1
  have h1 := congrArg ε hc
  rw [map_mul, map_mul, map_pow, hεA, hεT] at h1
  exact IsCompleteRankOneBase.not_isUnit (ϖ := (p : ℤ_[p]))
    (IsUnit.of_mul_eq_one (ε c * (p : ℤ_[p]))
      (by simpa [RingHom.id_apply, sq, mul_assoc, mul_comm, mul_left_comm] using h1))

-- Non-example: over the non-noetherian complete rank-one valuation base `𝓞_ℂ_[p]`, the maximal
-- ideal `𝔪 ⊆ 𝓞_ℂ_[p]` is not `p`-saturated and not finitely generated, so the `ϖ`-saturation
-- hypothesis in `IsTopologicallyFinitePresentation.fg_of_forall_smul_mem` cannot be omitted; yet
-- `𝔪` still satisfies Artin–Rees and carries the subspace `(p)`-adic topology.
example (p : ℕ) [Fact p.Prime] :
    let M : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p] := maximalIdeal 𝓞_ℂ_[p]
    let Ip : Ideal 𝓞_ℂ_[p] := Ideal.span {(p : 𝓞_ℂ_[p])}
    IsTopologicallyFinitePresentation 𝓞_ℂ_[p] 𝓞_ℂ_[p] ∧
      ¬ (∀ x : 𝓞_ℂ_[p], (p : 𝓞_ℂ_[p]) • x ∈ M → x ∈ M) ∧
      ¬ M.FG ∧
      (∃ k : ℕ, ∀ m : ℕ, M ⊓ (Ip ^ (m + k) • ⊤) ≤ Ip ^ m • M) ∧
      @IsEmbedding M 𝓞_ℂ_[p] (Ip.adicModuleTopology M) (Ip.adicModuleTopology 𝓞_ℂ_[p])
        M.subtype := by
  intro M Ip
  have := IsCompleteRankOneBase.isAdicRing (p : 𝓞_ℂ_[p])
  have hself : IsTopologicallyFinitePresentation 𝓞_ℂ_[p] 𝓞_ℂ_[p] :=
    isTopologicallyFinitePresentation_self 𝓞_ℂ_[p]
  refine ⟨hself, fun hsat ↦ ?_, TauCeti.PadicComplexInt.not_fg_maximalIdeal p,
    hself.exists_inf_pow_smul_le (p : 𝓞_ℂ_[p]) M,
    hself.isEmbedding_subtype_adicModuleTopology (p : 𝓞_ℂ_[p]) M⟩
  have hp_mem : (p : 𝓞_ℂ_[p]) • (1 : 𝓞_ℂ_[p]) ∈ M := by
    rw [smul_eq_mul, mul_one, mem_maximalIdeal]
    exact IsCompleteRankOneBase.not_isUnit (ϖ := (p : 𝓞_ℂ_[p]))
  exact (maximalIdeal.isMaximal 𝓞_ℂ_[p]).ne_top (Ideal.eq_top_of_isUnit_mem M (hsat 1 hp_mem)
    isUnit_one)

end TauCeti.HuberExamples
