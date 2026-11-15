/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.CompleteRankOneBase
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.FinitePresentation
import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Examples of algebras topologically of finite presentation

Over a complete rank-one valuation base `O` with pseudouniformiser `ϖ`:

* `O⟨T⟩` and `O` itself are admissible, and `O⟨T⟩` is flat over `O`;
* `O ⧸ ϖᵐ` (`m ≥ 1`) is topologically of finite presentation but not admissible;
* `O⟨T⟩ ⧸ (ϖT)` is topologically of finite presentation but not admissible, the class of `T`
  being a nonzero `ϖ`-torsion element;
* the reductions `O⟨ξ⟩ ⧸ ϖᵐ` are finitely presented over `O ⧸ ϖᵐ`, and `O⟨ξ⟩` with its own
  topology is strictly topologically of finite type.
-/

open TauCeti TauCeti.Huber

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O]
  [NonarchimedeanRing O] (ϖ : O) [IsCompleteRankOneBase O ϖ]

-- With no variables, the base itself is admissible.
example : IsAdmissibleAlgebra ϖ O := by
  have := IsCompleteRankOneBase.isAdicRing ϖ
  refine ⟨isTopologicallyFinitePresentation_self O, ?_⟩
  rw [← isSMulRegular_iff_torsionBy_eq_bot]
  exact fun _ _ h ↦ mul_left_cancel₀ (IsCompleteRankOneBase.ne_zero (ϖ := ϖ)) h

-- The restricted power-series algebras are admissible, hence flat over `O`.
example (n : ℕ) : IsAdmissibleAlgebra ϖ (restrictedMvPowerSeriesCompletion n O) := by
  have := IsCompleteRankOneBase.isAdicRing ϖ
  exact isAdmissibleAlgebra_restrictedMvPowerSeriesCompletion O
    (.of_ne_zero (IsCompleteRankOneBase.ne_zero (ϖ := ϖ))) n

example (n : ℕ) : Module.Flat O (restrictedMvPowerSeriesCompletion n O) := by
  have := IsCompleteRankOneBase.isAdicRing ϖ
  have hϖ : ϖ ≠ 0 := IsCompleteRankOneBase.ne_zero
  exact ((isAdmissibleAlgebra_iff_flat hϖ).mp
    (isAdmissibleAlgebra_restrictedMvPowerSeriesCompletion O (.of_ne_zero hϖ) n)).2

-- `O ⧸ ϖᵐ` is topologically of finite presentation ...
example (m : ℕ) : IsTopologicallyFinitePresentation O (O ⧸ Ideal.span {ϖ ^ m}) := by
  have := IsCompleteRankOneBase.isAdicRing ϖ
  exact (isTopologicallyFinitePresentation_self O).quotient (Submodule.fg_span_singleton _)

-- ... but for `m ≥ 1` not admissible: the class of `ϖᵐ⁻¹` is nonzero `ϖ`-torsion.
example (m : ℕ) : ¬ IsAdmissibleAlgebra ϖ (O ⧸ Ideal.span {ϖ ^ (m + 1)}) := by
  intro h
  have hx : Ideal.Quotient.mk (Ideal.span {ϖ ^ (m + 1)}) (ϖ ^ m) ∈
      Submodule.torsionBy O (O ⧸ Ideal.span {ϖ ^ (m + 1)}) ϖ := by
    rw [Submodule.mem_torsionBy_iff, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, ← pow_succ']
    exact Ideal.mem_span_singleton_self _
  rw [h.torsionBy_eq_bot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  refine IsCompleteRankOneBase.not_isUnit (ϖ := ϖ) (IsUnit.of_mul_eq_one c ?_)
  refine mul_left_cancel₀ (pow_ne_zero m (IsCompleteRankOneBase.ne_zero (ϖ := ϖ))) ?_
  rw [mul_one, ← mul_assoc, ← pow_succ, ← hc]

-- `O⟨T⟩ ⧸ (ϖT)` is topologically of finite presentation but not admissible: the class of `T`
-- is nonzero, as evaluation at `T = 1` shows, and is killed by `ϖ`.
example :
    let P := restrictedMvPowerSeriesCompletion 1 O
    let T : P := ((weightedX (fun _ : Fin 1 ↦ ({1} : Set O)) isWeightFamily_one_weight 0 :
      weightedRestrictedSubring _ _) : P)
    IsTopologicallyFinitePresentation O (P ⧸ Ideal.span {algebraMap O P ϖ * T}) ∧
      ¬ IsAdmissibleAlgebra ϖ (P ⧸ Ideal.span {algebraMap O P ϖ * T}) := by
  intro P T
  refine ⟨(isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O 1).quotient
    (Submodule.fg_span_singleton _), fun h ↦ ?_⟩
  have hx : Ideal.Quotient.mk (Ideal.span {algebraMap O P ϖ * T}) T ∈
      Submodule.torsionBy O (P ⧸ Ideal.span {algebraMap O P ϖ * T}) ϖ := by
    rw [Submodule.mem_torsionBy_iff, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [h.torsionBy_eq_bot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  -- evaluate at `T = 1`
  have := IsCompleteRankOneBase.isAdicRing ϖ
  let _ : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  have : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  obtain ⟨ε, ⟨-, hεA, hεT⟩, -⟩ :=
    existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
      (k := 1) (φ := RingHom.id O) continuous_id fun _ ↦ 1
  have h1 := congrArg ε hc
  rw [map_mul, map_mul, hεA, hεT] at h1
  exact IsCompleteRankOneBase.not_isUnit (ϖ := ϖ)
    (IsUnit.of_mul_eq_one (ε c) (by simpa [mul_comm] using h1))

-- The reductions of `O⟨ξ⟩` modulo powers of `ϖ` are finitely presented.
example (n m : ℕ) : Algebra.FinitePresentation (O ⧸ Ideal.span {ϖ ^ m})
    (restrictedMvPowerSeriesCompletion n O ⧸
      (Ideal.span {ϖ ^ m}).map (algebraMap O (restrictedMvPowerSeriesCompletion n O))) := by
  have := IsCompleteRankOneBase.isAdicRing ϖ
  exact IsTopologicallyFinitePresentation.finitePresentation_quotient_pow
    (isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O n)
    IsCompleteRankOneBase.isAdic m

-- With its own topology, `O⟨ξ⟩` is strictly topologically of finite type.
example (n : ℕ) :
    IsStrictlyTopologicallyFiniteType (algebraMap O (restrictedMvPowerSeriesCompletion n O)) :=
  IsTopologicallyFinitePresentation.isStrictlyTopologicallyFiniteType
    (isTopologicallyFinitePresentation_restrictedMvPowerSeriesCompletion O n)
    IsCompleteRankOneBase.isAdic (Submodule.fg_span_singleton ϖ)
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion n IsCompleteRankOneBase.isAdic
      (Submodule.fg_span_singleton ϖ))
