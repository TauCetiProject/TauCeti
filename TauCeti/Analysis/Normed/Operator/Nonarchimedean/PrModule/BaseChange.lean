/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.RingTheory.Huber.BanachModule.ZeroAtInfty

/-!
# Completed-tensor base change of `(Pr)` modules, Fredholm series and Riesz projections

Let `R` be a complete ultrametric Tate normed commutative ring (`TauCeti.NormedRing.IsTate R`), and
`S` a complete ultrametric normed commutative `R`-algebra with bounded scalar action
(`∃ C : ℝ≥0, ∀ r s, ‖r • s‖ ≤ C * ‖r‖ * ‖s‖`). No ground field, Noetherianity or flatness is
assumed.

* `CompletedTensor.retractIncl` / `retractProj` transport a retract `M →ⁱ C₀(J, R) →ʳ M` to a
  retract of `S ⊗̂_R M` through `C₀(J, S)` whose composite is `(i ∘ r).mapCoeffs`, exact with
  `1 - (i ∘ r).mapCoeffs` (`exact_retractIncl_sub_idempotent`), transporting Fredholm series
  (`charPowerSeries_retract_baseChange`).
* Along realisations `αᵢ : S ⊗̂_R Mᵢ ≃L[S] Nᵢ`, `ContinuousLinearMap.completedBaseChange` preserves
  ring/polynomial operations, recovers `u` for `S = R` (`completedBaseChange_self`) and
  `u.mapCoeffs` on `C₀` (`completedBaseChange_zeroAtInfty`), respects changing realisations
  (`completedBaseChange_trans`), and transports `TauCeti.HasPr`, `IsPrCompact`, Fredholm series,
  Hasse derivatives, good zeros, coprime reverse-polynomial invertibility, operator-norm continuity,
  and Riesz and Riesz–Coleman projections (`IsRieszProjection.completedBaseChange`,
  `IsRieszColemanProjection.completedBaseChange`,
  `IsRieszColemanProjection.inverse_completedBaseChange`).

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5, 7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §§2.1–2.2.
-/

public section

open Polynomial ZeroAtInftyContinuousMap TauCeti TauCeti.Huber.BanachModule
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

universe u₁ u₂

local notation:70 S:71 " ⊗̂[" R "] " M:71 => (CompletedTensor R S M)

namespace TauCeti.Huber.BanachModule.CompletedTensor

section RetractTransport

variable {R : Type*} [NormedCommRing R]
  {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  {J : Type*} [TopologicalSpace J] [DiscreteTopology J]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M]

section ZeroSeq

variable [HasZeroSequenceOfUnits R]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

variable (J) in
/-- Extension of a model-space inclusion `i : M →L[R] C₀(J, R)` to
`S ⊗̂_R M →L[S] C₀(J, S)` via `zeroAtInftyBaseChange`. -/
noncomputable def retractIncl (i : M →L[R] C₀(J, R)) : (S ⊗̂[R] M) →L[S] C₀(J, S) :=
  (zeroAtInftyBaseChange J hS).toContinuousLinearMap.comp (baseChange S i)

/-- Explicit formula for `retractIncl`. -/
theorem retractIncl_def (i : M →L[R] C₀(J, R)) :
    retractIncl J hS i = (zeroAtInftyBaseChange J hS).toContinuousLinearMap.comp (baseChange S i) :=
  (rfl)

/-- `retractIncl` sends `s ⊗ m` to `(s * algebraMap R S (i m j))ⱼ`. -/
@[simp]
theorem retractIncl_tmul_apply (i : M →L[R] C₀(J, R)) (s : S) (m : M) (j : J) :
    retractIncl J hS i (tmul R S M s m) j = s * algebraMap R S (i m j) := by simp [retractIncl]

variable (J) in
/-- Extension of a model-space retraction `r : C₀(J, R) →L[R] M` to
`C₀(J, S) →L[S] S ⊗̂_R M` via `zeroAtInftyBaseChange`. -/
noncomputable def retractProj (r : C₀(J, R) →L[R] M) : C₀(J, S) →L[S] (S ⊗̂[R] M) :=
  (baseChange S r).comp (zeroAtInftyBaseChange J hS).symm.toContinuousLinearMap

/-- Explicit formula for `retractProj`. -/
theorem retractProj_def (r : C₀(J, R) →L[R] M) :
    retractProj J hS r =
      (baseChange S r).comp (zeroAtInftyBaseChange J hS).symm.toContinuousLinearMap := (rfl)

/-- `retractProj` sends a coordinate vector `single j s` to `s ⊗ r (single j 1)`. -/
@[simp]
theorem retractProj_single [DecidableEq J] (r : C₀(J, R) →L[R] M) (j : J) (s : S) :
    retractProj J hS r (single j s) = tmul R S M s (r (single j 1)) := by simp [retractProj]

/-- **Retract preservation.** A continuous `R`-linear retract `r ∘ i = id` of `M` through `C₀(J, R)`
extends to a continuous `S`-linear retract of `S ⊗̂_R M` through `C₀(J, S)`. -/
theorem retractProj_comp_retractIncl {i : M →L[R] C₀(J, R)} {r : C₀(J, R) →L[R] M}
    (hri : r.comp i = .id R M) :
    (retractProj J hS r).comp (retractIncl J hS i) = .id S (S ⊗̂[R] M) := by
  rw [retractProj, retractIncl, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (zeroAtInftyBaseChange J hS).symm.toContinuousLinearMap,
    ContinuousLinearEquiv.coe_symm_comp_coe, ContinuousLinearMap.id_comp,
    baseChange_comp_eq_id_of_retract S hri]

end ZeroSeq

section Tate

variable [TauCeti.NormedRing.IsTate R] [DecidableEq J]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

/-- **Commuting idempotent diagram.** For any `i : M →L[R] C₀(J, R)` and `r : C₀(J, R) →L[R] M`,
`retractIncl ∘ retractProj` on `C₀(J, S)` is the coefficientwise extension `(i ∘ r).mapCoeffs`. -/
theorem retractIncl_comp_retractProj (i : M →L[R] C₀(J, R)) (r : C₀(J, R) →L[R] M) :
    (retractIncl J hS i).comp (retractProj J hS r) =
      (i.comp r).mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS) := by
  rw [retractIncl, retractProj, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (baseChange S i), ← baseChange_comp]
  exact zeroAtInftyBaseChange_comp_baseChange_comp_symm J hS (i.comp r)

/-- **Operator extension through a retract.** Conjugating `baseChange S u` by `(retractIncl,
retractProj)` yields the coefficientwise extension of `i ∘ u ∘ r`. -/
theorem retractIncl_comp_baseChange_comp_retractProj
    {N : Type*} [SeminormedAddCommGroup N] [Module R N]
    {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    (i : N →L[R] C₀(I, R)) (r : C₀(J, R) →L[R] M) (u : M →L[R] N) :
    (retractIncl I hS i).comp ((baseChange S u).comp (retractProj J hS r)) =
      (i.comp (u.comp r)).mapCoeffs (algebraMap R S)
        (exists_norm_algebraMap_le_of_norm_smul_le hS) := by
  rw [retractIncl, retractProj, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (baseChange S u), ← baseChange_comp,
    ← ContinuousLinearMap.comp_assoc (baseChange S i), ← baseChange_comp]
  exact zeroAtInftyBaseChange_comp_baseChange_comp_symm I hS (i.comp (u.comp r))

/-- **Split exactness on `(Pr)` retracts.** Without assuming flatness of `S` over `R`, the extended
inclusion `retractIncl J hS i : S ⊗̂_R M →L[S] C₀(J, S)` of a retract `r ∘ i = id` is exact with
`1 - (i ∘ r).mapCoeffs`. -/
theorem exact_retractIncl_sub_idempotent {i : M →L[R] C₀(J, R)} {r : C₀(J, R) →L[R] M}
    (hri : r.comp i = .id R M) :
    Function.Exact (retractIncl J hS i)
      (ContinuousLinearMap.id S C₀(J, S) -
        (i.comp r).mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS)) := by
  have hpi : (ContinuousLinearMap.id R C₀(J, R) - i.comp r).comp i = 0 := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc,
      hri, ContinuousLinearMap.comp_id]
    exact sub_self i
  have hex := exact_baseChange_of_split S r (.id R C₀(J, R))
    (p := ContinuousLinearMap.id R C₀(J, R) - i.comp r) (i := i) hpi (fun _ ↦ by simp)
  let e := zeroAtInftyBaseChange J hS
  have hq : ContinuousLinearMap.id S C₀(J, S) -
        (i.comp r).mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS) =
      e.toContinuousLinearMap.comp
        ((baseChange S (ContinuousLinearMap.id R C₀(J, R) - i.comp r)).comp
          e.symm.toContinuousLinearMap) := by
    rw [baseChange_sub, baseChange_id, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
      zeroAtInftyBaseChange_comp_baseChange_comp_symm]
  intro y; rw [hq]
  refine ⟨fun hy ↦ let ⟨z, hz⟩ := (hex (e.symm y)).mp (e.injective (by simpa using hy))
      ⟨z, by simp [retractIncl, e, hz]⟩, ?_⟩
  rintro ⟨z, rfl⟩
  simp only [retractIncl, e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, (hex _).mpr ⟨z, rfl⟩, map_zero]

/-- **Topological determinant transport along any `(Pr)` retract.** For row-compact `u : M →L[R] M`
and any retract `r ∘ i = id` through `C₀(J, R)`, the Fredholm series of the extended operator on
`C₀(J, S)` equals `PowerSeries.map (algebraMap R S) u.charPowerSeries`. -/
theorem charPowerSeries_retract_baseChange [IsUltrametricDist R] [CompleteSpace R]
    {u : M →L[R] M} (hu : u.IsPrCompact) {i : M →L[R] C₀(J, R)} {r : C₀(J, R) →L[R] M}
    (hri : r.comp i = .id R M) :
    ((retractIncl J hS i).comp
        ((baseChange S u).comp (retractProj J hS r))).matrixCoeff.charPowerSeries =
      PowerSeries.map (algebraMap R S) u.charPowerSeries := by
  rw [retractIncl_comp_baseChange_comp_retractProj, hu.charPowerSeries_eq hri]
  exact (hu.isRowCompact_comp i r).charPowerSeries_map (algebraMap R S)
    (exists_norm_algebraMap_le_of_norm_smul_le hS)

end Tate

end RetractTransport

end TauCeti.Huber.BanachModule.CompletedTensor

namespace ContinuousLinearMap

open CompletedTensor

section Algebraic

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
  {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
  [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]
  [AddCommGroup N₁] [Module S N₁] [TopologicalSpace N₁]
  [AddCommGroup N₂] [Module S N₂] [TopologicalSpace N₂]
  [AddCommGroup N₃] [Module S N₃] [TopologicalSpace N₃]

/-- **Completed-tensor base change of a continuous linear map** along module realisations
`α₁ : S ⊗̂_R M₁ ≃L[S] N₁` and `α₂ : S ⊗̂_R M₂ ≃L[S] N₂`. -/
noncomputable def completedBaseChange (u : M₁ →L[R] M₂)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) : N₁ →L[S] N₂ :=
  α₂.toContinuousLinearMap.comp ((baseChange S u).comp α₁.symm.toContinuousLinearMap)

/-- Pointwise evaluation of `u.completedBaseChange α₁ α₂`. -/
@[simp]
theorem completedBaseChange_apply (u : M₁ →L[R] M₂)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) (x : N₁) :
    u.completedBaseChange α₁ α₂ x = α₂ (baseChange S u (α₁.symm x)) := (rfl)

/-- `completedBaseChange` preserves the identity operator. -/
@[simp]
theorem completedBaseChange_id (α : S ⊗̂[R] M₁ ≃L[S] N₁) :
    (ContinuousLinearMap.id R M₁).completedBaseChange α α = .id S N₁ := by ext x; simp

/-- `completedBaseChange` preserves operator composition. -/
theorem completedBaseChange_comp (v : M₂ →L[R] M₃) (u : M₁ →L[R] M₂)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) (α₃ : S ⊗̂[R] M₃ ≃L[S] N₃) :
    (v.comp u).completedBaseChange α₁ α₃ =
      (v.completedBaseChange α₂ α₃).comp (u.completedBaseChange α₁ α₂) := by
  ext x; simp [baseChange_comp]

/-- `completedBaseChange` sends `0` to `0`. -/
@[simp]
theorem completedBaseChange_zero (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (0 : M₁ →L[R] M₂).completedBaseChange α₁ α₂ = 0 := by ext x; simp

/-- `completedBaseChange` is additive. -/
@[simp]
theorem completedBaseChange_add [ContinuousAdd M₂] [ContinuousAdd N₂] (u v : M₁ →L[R] M₂)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (u + v).completedBaseChange α₁ α₂ =
      u.completedBaseChange α₁ α₂ + v.completedBaseChange α₁ α₂ := by ext x; simp [baseChange_add]

/-- `completedBaseChange` commutes with negation. -/
@[simp]
theorem completedBaseChange_neg [IsTopologicalAddGroup M₂] [IsTopologicalAddGroup N₂]
    (u : M₁ →L[R] M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (-u).completedBaseChange α₁ α₂ = -u.completedBaseChange α₁ α₂ := by ext x; simp [baseChange_neg]

/-- `completedBaseChange` commutes with subtraction. -/
@[simp]
theorem completedBaseChange_sub [IsTopologicalAddGroup M₂] [IsTopologicalAddGroup N₂]
    (u v : M₁ →L[R] M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (u - v).completedBaseChange α₁ α₂ =
      u.completedBaseChange α₁ α₂ - v.completedBaseChange α₁ α₂ := by ext x; simp [baseChange_sub]

/-- `completedBaseChange` is `R`-semilinear along `algebraMap R S`. -/
@[simp]
theorem completedBaseChange_smul [ContinuousConstSMul R M₂] [ContinuousConstSMul S N₂]
    (r : R) (u : M₁ →L[R] M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (r • u).completedBaseChange α₁ α₂ =
      algebraMap R S r • u.completedBaseChange α₁ α₂ := by
  ext x; simp only [completedBaseChange_apply, _root_.smul_apply, baseChange_smul, map_smul]

/-- `completedBaseChange` preserves `1` in the endomorphism ring. -/
@[simp]
theorem completedBaseChange_one (α : S ⊗̂[R] M₁ ≃L[S] N₁) :
    (1 : M₁ →L[R] M₁).completedBaseChange α α = 1 := completedBaseChange_id α

/-- `completedBaseChange` is multiplicative on endomorphisms. -/
@[simp]
theorem completedBaseChange_mul (u v : M₁ →L[R] M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁) :
    (u * v).completedBaseChange α α = u.completedBaseChange α α * v.completedBaseChange α α :=
  completedBaseChange_comp u v α α α

/-- `completedBaseChange` preserves natural powers on endomorphisms. -/
@[simp]
theorem completedBaseChange_pow (u : M₁ →L[R] M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁) (n : ℕ) :
    (u ^ n).completedBaseChange α α = u.completedBaseChange α α ^ n :=
  Nat.rec (by simp) (fun _ ih ↦ by rw [pow_succ, pow_succ, completedBaseChange_mul, ih]) n

/-- **Endomorphism ring homomorphism.** Along `α : S ⊗̂_R M₁ ≃L[S] N₁`,
`completedBaseChange · α α` is a unital ring homomorphism `(M₁ →L[R] M₁) →+* (N₁ →L[S] N₁)`. -/
noncomputable def completedBaseChangeRingHom [ContinuousAdd M₁] [ContinuousAdd N₁]
    (α : S ⊗̂[R] M₁ ≃L[S] N₁) : (M₁ →L[R] M₁) →+* (N₁ →L[S] N₁) :=
  ⟨⟨⟨(·.completedBaseChange α α), completedBaseChange_one α⟩, (completedBaseChange_mul · · α)⟩,
    completedBaseChange_zero α α, (completedBaseChange_add · · α α)⟩

@[simp]
theorem completedBaseChangeRingHom_apply [ContinuousAdd M₁] [ContinuousAdd N₁]
    (α : S ⊗̂[R] M₁ ≃L[S] N₁) (u : M₁ →L[R] M₁) :
    completedBaseChangeRingHom α u = u.completedBaseChange α α := (rfl)

/-- **Polynomial compatibility.** `completedBaseChange` intertwines polynomial evaluation along
`algebraMap R S`. -/
theorem aeval_completedBaseChange [IsTopologicalAddGroup M₁] [ContinuousConstSMul R M₁]
    [IsTopologicalAddGroup N₁] [ContinuousConstSMul S N₁]
    (u : M₁ →L[R] M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁) (P : R[X]) :
    Polynomial.aeval (u.completedBaseChange α α) (Polynomial.map (algebraMap R S) P) =
      (Polynomial.aeval u P).completedBaseChange α α := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, completedBaseChange_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      completedBaseChange_smul, completedBaseChange_pow]

/-- **Compatibility with changing module realisations and equivalent norms.** Post-composing
`α₁`, `α₂` with equivalences `e₁`, `e₂` conjugates `completedBaseChange` by `e₁` and `e₂`. -/
theorem completedBaseChange_trans {N₁' N₂' : Type*}
    [AddCommGroup N₁'] [Module S N₁'] [TopologicalSpace N₁']
    [AddCommGroup N₂'] [Module S N₂'] [TopologicalSpace N₂']
    (u : M₁ →L[R] M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂)
    (e₁ : N₁ ≃L[S] N₁') (e₂ : N₂ ≃L[S] N₂') :
    u.completedBaseChange (α₁.trans e₁) (α₂.trans e₂) =
      e₂.toContinuousLinearMap.comp
        ((u.completedBaseChange α₁ α₂).comp e₁.symm.toContinuousLinearMap) := by ext x; simp

/-- **Identity base change.** When `S = R` and `M₁`, `M₂` are complete Hausdorff nonarchimedean
`R`-modules, `completedBaseChange` along the unit equivalences `lid R M₁` and `lid R M₂` is `u`. -/
theorem completedBaseChange_self {R M₁ M₂ : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M₁] [Module R M₁] [UniformSpace M₁] [IsUniformAddGroup M₁]
    [NonarchimedeanAddGroup M₁] [ContinuousSMul R M₁] [CompleteSpace M₁] [T0Space M₁]
    [AddCommGroup M₂] [Module R M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [NonarchimedeanAddGroup M₂] [ContinuousSMul R M₂] [CompleteSpace M₂] [T0Space M₂]
    (u : M₁ →L[R] M₂) : u.completedBaseChange (lid R M₁) (lid R M₂) = u := by
  ext x
  exact (lid_baseChange_apply u ((lid R M₁).symm x)).trans
    (congrArg u ((lid R M₁).apply_symm_apply x))

end Algebraic

section ModelComparison

variable {R S : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  {J I : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [TopologicalSpace I] [DiscreteTopology I]

/-- **Model-space identification.** Under `zeroAtInftyBaseChange`, `completedBaseChange` of a
model-space operator `u : C₀(J, R) →L[R] C₀(I, R)` is its coefficientwise extension
`u.mapCoeffs`. -/
theorem completedBaseChange_zeroAtInfty
    (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    u.completedBaseChange (zeroAtInftyBaseChange J hS) (zeroAtInftyBaseChange I hS) =
      u.mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS) :=
  zeroAtInftyBaseChange_comp_baseChange_comp_symm I hS u

end ModelComparison

end ContinuousLinearMap

private theorem retractProj_comp_retractIncl_equiv {R S J M N : Type*} [NormedCommRing R]
    [HasZeroSequenceOfUnits R] [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
    [Algebra R S] [TopologicalSpace J] [DiscreteTopology J] [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module S N]
    (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)
    {i : M →L[R] C₀(J, R)} {r : C₀(J, R) →L[R] M} (hri : r.comp i = .id R M)
    (α : S ⊗̂[R] M ≃L[S] N) :
    (α.toContinuousLinearMap.comp (CompletedTensor.retractProj J hS r)).comp
      ((CompletedTensor.retractIncl J hS i).comp α.symm.toContinuousLinearMap) = .id S N := by
  ext y
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg α (DFunLike.congr_fun (CompletedTensor.retractProj_comp_retractIncl hS hri) (α.symm y))

namespace TauCeti.HasPr

open CompletedTensor

/-- **Property `(Pr)` transports along completed-tensor base change.** If `M` has property `(Pr)`
over `R` and `α : S ⊗̂_R M ≃L[S] N` realises its completed scalar extension as a seminormed
`S`-module in the same universe, then `N` has property `(Pr)` over `S`. -/
theorem completedBaseChange {R S : Type*} [NormedCommRing R] [HasZeroSequenceOfUnits R]
    [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
    {M N : Type u₁} [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module S N]
    (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)
    (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N) : HasPr S N := by
  obtain ⟨J, _, _, i, r, hri⟩ := (hasPr_def R M).mp hM
  exact (hasPr_def S N).mpr ⟨J, inferInstance, inferInstance,
    (retractIncl J hS i).comp α.symm.toContinuousLinearMap,
    α.toContinuousLinearMap.comp (retractProj J hS r),
    retractProj_comp_retractIncl_equiv hS hri α⟩

end TauCeti.HasPr

namespace ContinuousLinearMap

open CompletedTensor

section PrTransport

variable {R S : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  {M₁ N₁ : Type u₁} {M₂ N₂ : Type u₂}
  [SeminormedAddCommGroup M₁] [Module R M₁] [SeminormedAddCommGroup N₁] [Module S N₁]
  [SeminormedAddCommGroup M₂] [Module R M₂] [SeminormedAddCommGroup N₂] [Module S N₂]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

private theorem retractIncl_comp_completedBaseChange_comp_retractProj
    {J I : Type*} [TopologicalSpace J] [DiscreteTopology J]
    [TopologicalSpace I] [DiscreteTopology I]
    (i₂ : M₂ →L[R] C₀(I, R)) (r₁ : C₀(J, R) →L[R] M₁) (u : M₁ →L[R] M₂)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    ((retractIncl I hS i₂).comp α₂.symm.toContinuousLinearMap).comp
        ((u.completedBaseChange α₁ α₂).comp (α₁.toContinuousLinearMap.comp (retractProj J hS r₁))) =
      (retractIncl I hS i₂).comp ((baseChange S u).comp (retractProj J hS r₁)) := by
  ext y; simp [completedBaseChange_apply]

private theorem completedBaseChange_eq_retract_mapCoeffs
    {J I : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    [TopologicalSpace I] [DiscreteTopology I]
    {i₁ : M₁ →L[R] C₀(J, R)} {r₁ : C₀(J, R) →L[R] M₁} (h₁ : r₁.comp i₁ = .id R M₁)
    {i₂ : M₂ →L[R] C₀(I, R)} {r₂ : C₀(I, R) →L[R] M₂} (h₂ : r₂.comp i₂ = .id R M₂)
    (u : M₁ →L[R] M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    u.completedBaseChange α₁ α₂ =
      (α₂.toContinuousLinearMap.comp (retractProj I hS r₂)).comp
        (((i₂.comp (u.comp r₁)).mapCoeffs (algebraMap R S)
          (exists_norm_algebraMap_le_of_norm_smul_le hS)).comp
          ((retractIncl J hS i₁).comp α₁.symm.toContinuousLinearMap)) := by
  rw [← retractIncl_comp_baseChange_comp_retractProj hS i₂ r₁ u]; ext y
  have hr₁ := DFunLike.congr_fun (retractProj_comp_retractIncl hS h₁) (α₁.symm y)
  have hr₂ := DFunLike.congr_fun (retractProj_comp_retractIncl hS h₂) (baseChange S u (α₁.symm y))
  simp only [completedBaseChange_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, id_apply] at hr₁ hr₂ ⊢
  rw [hr₁, hr₂]

include hS

/-- **Row-compactness transports along completed-tensor base change.** -/
theorem IsPrCompact.completedBaseChange {u : M₁ →L[R] M₂} (hu : u.IsPrCompact)
    (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    (u.completedBaseChange α₁ α₂).IsPrCompact := by
  obtain ⟨J, _, _, _, I, _, _, i₁, r₁, i₂, r₂, h₁, h₂, hrc⟩ := (isPrCompact_def u).mp hu
  refine isPrCompact_of_isRowCompact_comp
    (retractProj_comp_retractIncl_equiv hS h₁ α₁) (retractProj_comp_retractIncl_equiv hS h₂ α₂) ?_
  rw [retractIncl_comp_completedBaseChange_comp_retractProj,
    retractIncl_comp_baseChange_comp_retractProj]
  exact hrc.mapCoeffs (algebraMap R S) (exists_norm_algebraMap_le_of_norm_smul_le hS)

section Fredholm

variable [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate S]

/-- **Completed-tensor base change of Fredholm series on `(Pr)` modules.** For row-compact
`u : M₁ →L[R] M₁` and any realisation `α : S ⊗̂_R M₁ ≃L[S] N₁`, the Fredholm series of
`u.completedBaseChange α α` is `PowerSeries.map (algebraMap R S) u.charPowerSeries`. -/
theorem IsPrCompact.charPowerSeries_completedBaseChange {u : M₁ →L[R] M₁} (hu : u.IsPrCompact)
    (α : S ⊗̂[R] M₁ ≃L[S] N₁) :
    (u.completedBaseChange α α).charPowerSeries =
      PowerSeries.map (algebraMap R S) u.charPowerSeries := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (hasPr_def R M₁).mp hu.hasPr_source
  rw [(hu.completedBaseChange hS α α).charPowerSeries_eq
    (retractProj_comp_retractIncl_equiv hS hri α),
    retractIncl_comp_completedBaseChange_comp_retractProj]
  exact charPowerSeries_retract_baseChange hS hu hri

/-- Values of Hasse derivatives of the Fredholm series commute with `completedBaseChange`. -/
theorem IsPrCompact.evalAt_hasseDeriv_charPowerSeries_completedBaseChange
    {u : M₁ →L[R] M₁} (hu : u.IsPrCompact) (α : S ⊗̂[R] M₁ ≃L[S] N₁) (k : ℕ) (a : R) :
    (PowerSeries.hasseDeriv k (u.completedBaseChange α α).charPowerSeries).evalAt
        (algebraMap R S a) =
      algebraMap R S ((PowerSeries.hasseDeriv k u.charPowerSeries).evalAt a) := by
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hS
  rw [hu.charPowerSeries_completedBaseChange hS α, PowerSeries.hasseDeriv_map,
    (hu.isEntire_charPowerSeries.hasseDeriv k).evalAt_map (algebraMap R S)
      (AddMonoidHomClass.continuous_of_bound (algebraMap R S) C hC)]

/-- Evaluation `H_u(a)` of the Fredholm series commutes with `completedBaseChange`. -/
theorem IsPrCompact.evalAt_charPowerSeries_completedBaseChange
    {u : M₁ →L[R] M₁} (hu : u.IsPrCompact) (α : S ⊗̂[R] M₁ ≃L[S] N₁) (a : R) :
    (u.completedBaseChange α α).charPowerSeries.evalAt (algebraMap R S a) =
      algebraMap R S (u.charPowerSeries.evalAt a) := by
  simpa using hu.evalAt_hasseDeriv_charPowerSeries_completedBaseChange hS α 0 a

/-- Good zeros of the Fredholm series transport along `completedBaseChange` with the same order. -/
theorem IsPrCompact.isGoodZero_charPowerSeries_completedBaseChange
    {u : M₁ →L[R] M₁} (hu : u.IsPrCompact) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {a : R} {h : ℕ} (ha : u.charPowerSeries.IsGoodZero a h) :
    (u.completedBaseChange α α).charPowerSeries.IsGoodZero (algebraMap R S a) h := by
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hS
  rw [hu.charPowerSeries_completedBaseChange hS α]
  exact ha.map hu.isEntire_charPowerSeries (algebraMap R S)
    (AddMonoidHomClass.continuous_of_bound (algebraMap R S) C hC)

end Fredholm

omit [CompleteSpace S] hS in
/-- **Coprime polynomial factors under completed-tensor base change.** If `Q : R[X]` has unit
leading coefficient and is coprime to `u.charPowerSeries` in `IsEntire.subring R`, then
`(Polynomial.map (algebraMap R S) Q).reverse` evaluates at `u.completedBaseChange α α` to a unit. -/
theorem IsPrCompact.isUnit_aeval_reverse_completedBaseChange
    [IsUltrametricDist R] [CompleteSpace R] [ContinuousConstSMul R M₁] [ContinuousConstSMul S N₁]
    {u : M₁ →L[R] M₁} (hu : u.IsPrCompact) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {Q : R[X]} (hQ : IsUnit Q.leadingCoeff)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨u.charPowerSeries, PowerSeries.IsEntire.mem_subring.mpr hu.isEntire_charPowerSeries⟩) :
    IsUnit (Polynomial.aeval (u.completedBaseChange α α)
      (Polynomial.map (algebraMap R S) Q).reverse) := by
  have huQ : IsUnit (Polynomial.aeval u Q.reverse) := (hu.isUnit_aeval_reverse_iff hQ).mpr hcop
  have hrev : (Polynomial.map (algebraMap R S) Q).reverse =
      Polynomial.map (algebraMap R S) Q.reverse :=
    (subsingleton_or_nontrivial S).elim (fun _ ↦ Subsingleton.elim _ _) fun _ ↦ by
      rw [Polynomial.reverse, Polynomial.reverse,
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (hQ.map _).ne_zero,
        Polynomial.reflect_map]
  rw [hrev, aeval_completedBaseChange]; exact huQ.map (completedBaseChangeRingHom α)

/-- **Operator-norm continuity of `completedBaseChange`** between `(Pr)` modules over Tate rings. -/
theorem continuous_completedBaseChange [TauCeti.NormedRing.IsTate S]
    [IsBoundedSMul R M₁] [IsBoundedSMul R M₂] [IsBoundedSMul S N₁] [IsBoundedSMul S N₂]
    (hM₁ : HasPr R M₁) (hM₂ : HasPr R M₂) (α₁ : S ⊗̂[R] M₁ ≃L[S] N₁) (α₂ : S ⊗̂[R] M₂ ≃L[S] N₂) :
    Continuous fun u : M₁ →L[R] M₂ ↦ u.completedBaseChange α₁ α₂ := by
  classical
  obtain ⟨J, _, _, i₁, r₁, h₁⟩ := (hasPr_def R M₁).mp hM₁
  obtain ⟨I, _, _, i₂, r₂, h₂⟩ := (hasPr_def R M₂).mp hM₂
  have hcont :=
    (lipschitzWith_comp_comp (α₂.toContinuousLinearMap.comp (retractProj I hS r₂))
      ((retractIncl J hS i₁).comp α₁.symm.toContinuousLinearMap)).continuous.comp <|
    (continuous_mapCoeffs (I := I) (J := J) (algebraMap R S)
      (exists_norm_algebraMap_le_of_norm_smul_le hS)).comp
      (lipschitzWith_comp_comp i₂ r₁).continuous
  exact hcont.congr fun u ↦ (completedBaseChange_eq_retract_mapCoeffs hS h₁ h₂ u α₁ α₂).symm

/-- `completedBaseChange` sends the operator-norm closure of `R[u]` into the closure of
`S[u.completedBaseChange α α]`. -/
theorem completedBaseChange_mem_closure_adjoin [TauCeti.NormedRing.IsTate S]
    [IsBoundedSMul R M₁] [IsBoundedSMul S N₁] (hM : HasPr R M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {u v : M₁ →L[R] M₁} (hv : v ∈ closure (Algebra.adjoin R {u} : Set (M₁ →L[R] M₁))) :
    v.completedBaseChange α α ∈
      closure (Algebra.adjoin S {u.completedBaseChange α α} : Set (N₁ →L[S] N₁)) := by
  refine map_mem_closure (f := fun w : M₁ →L[R] M₁ ↦ w.completedBaseChange α α)
    (continuous_completedBaseChange hS hM hM α α) hv fun w hw ↦ ?_
  simp only [SetLike.mem_coe]
  induction hw using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact Algebra.self_mem_adjoin_singleton S _
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, completedBaseChange_smul, completedBaseChange_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
  | add _ _ _ _ hx hy => rw [completedBaseChange_add]; exact Subalgebra.add_mem _ hx hy
  | mul _ _ _ _ hx hy => rw [completedBaseChange_mul]; exact Subalgebra.mul_mem _ hx hy

/-- **Riesz projections under completed-tensor base change.** On a `(Pr)` module `M₁` over `R`,
`completedBaseChange` transports a Riesz projection of `u` at `a` of order `h` to one of
`u.completedBaseChange α α` at `algebraMap R S a` of order `h` (no compactness needed). -/
theorem IsRieszProjection.completedBaseChange [TauCeti.NormedRing.IsTate S]
    [IsBoundedSMul R M₁] [IsBoundedSMul S N₁] (hM : HasPr R M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {u E : M₁ →L[R] M₁} {a : R} {h : ℕ} (hE : IsRieszProjection u a h E) :
    IsRieszProjection (u.completedBaseChange α α) (algebraMap R S a) h
      (E.completedBaseChange α α) := by
  let Φ := completedBaseChangeRingHom α
  have h1sub : Φ (1 - a • u) = 1 - algebraMap R S a • u.completedBaseChange α α := by
    simp [Φ, completedBaseChangeRingHom]
  have hu' : Φ u = u.completedBaseChange α α := rfl
  have hE' : Φ E = E.completedBaseChange α α := rfl
  exact isRieszProjection_def.mpr <| by
    simpa only [hu', h1sub, hE'] using
      (isRieszProjection_def.mp hE).map Φ fun {v} hv ↦
        completedBaseChange_mem_closure_adjoin hS hM α hv

/-- **Riesz–Coleman projections under completed-tensor base change.** On a `(Pr)` module `M₁` over
`R`, `completedBaseChange` transports a Riesz–Coleman projection of `u` for `Q` to one of
`u.completedBaseChange α α` for `Q.map (algebraMap R S)`, whenever `algebraMap R S` preserves the
degree of `Q` (in particular, whenever `Q` has invertible leading coefficient). No compactness is
needed. -/
theorem IsRieszColemanProjection.completedBaseChange [TauCeti.NormedRing.IsTate S]
    [IsBoundedSMul R M₁] [IsBoundedSMul S N₁] (hM : HasPr R M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {u E : M₁ →L[R] M₁} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hdeg : (Q.map (algebraMap R S)).natDegree = Q.natDegree) :
    IsRieszColemanProjection (u.completedBaseChange α α) (Q.map (algebraMap R S))
      (E.completedBaseChange α α) := by
  have hrev : (Q.map (algebraMap R S)).reverse = Q.reverse.map (algebraMap R S) := by
    rw [Polynomial.reverse, hdeg, Polynomial.reflect_map, Polynomial.reverse]
  exact isRieszColemanProjection_def.mpr <| by
    simpa only [completedBaseChangeRingHom_apply, aeval_completedBaseChange, hrev] using
      (isRieszColemanProjection_def.mp hE).map (completedBaseChangeRingHom α)
        (completedBaseChange_mem_closure_adjoin hS hM α)

/-- Completed-tensor base change commutes with taking the complementary inverse of a Riesz–Coleman
projection, whenever `algebraMap R S` preserves the degree of `Q`. -/
theorem IsRieszColemanProjection.inverse_completedBaseChange [TauCeti.NormedRing.IsTate S]
    [IsBoundedSMul R M₁] [IsBoundedSMul S N₁] (hM : HasPr R M₁) (α : S ⊗̂[R] M₁ ≃L[S] N₁)
    {u E : M₁ →L[R] M₁} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hdeg : (Q.map (algebraMap R S)).natDegree = Q.natDegree) :
    (isRieszColemanProjection_def.mp (hE.completedBaseChange hS hM α hdeg)).inverse =
      (isRieszColemanProjection_def.mp hE).inverse.completedBaseChange α α := by
  let Φ := completedBaseChangeRingHom α
  refine ((isRieszColemanProjection_def.mp (hE.completedBaseChange hS hM α hdeg)).eq_inverse
    ?_ ?_).symm
  · have hrev : (Q.map (algebraMap R S)).reverse = Q.reverse.map (algebraMap R S) := by
      rw [Polynomial.reverse, hdeg, Polynomial.reflect_map, Polynomial.reverse]
    simpa only [Φ, map_mul, map_sub, map_one, completedBaseChangeRingHom_apply,
      ← aeval_completedBaseChange, ← hrev] using
      congrArg Φ (isRieszColemanProjection_def.mp hE).spectral_mul_inverse
  · simpa only [Φ, map_mul, map_zero, completedBaseChangeRingHom_apply] using
      congrArg Φ (isRieszColemanProjection_def.mp hE).mul_inverse_eq_zero

end PrTransport

end ContinuousLinearMap
