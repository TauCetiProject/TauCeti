/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Lie.KacMoody.WeightModule
public import TauCeti.LinearAlgebra.End.Exp
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.Algebra.Lie.Sl2.Associative
import TauCeti.Algebra.Lie.Submodule.LocallyFinite
import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Integrable modules over Kac–Moody Lie algebras and the simple Weyl intertwiners

An `Enveloping R`-module `M` over `TauCeti.KacMoody.PresentedLieAlgebra R` is **integrable**
(`TauCeti.KacMoody.IsIntegrable R M`) when it is a weight module on which every Chevalley generator
`eᵢ` and `fᵢ` acts locally nilpotently. Together with Kac's category `O` this forms the subcategory
`TauCeti.KacMoody.IsIntegrableO R M` of integrable highest-weight modules. Concrete simple models
(`OneDimModule` and `RankOneModule`) live in `TauCeti.Algebra.Lie.KacMoody.IntegrableModel`.

Three structural mechanisms govern integrable Kac–Moody representations here:

1. **Spreading local nilpotence from generating sets.** By adjoint local nilpotence of
   `positiveGenerator R i` and `negativeGenerator R i` on `PresentedLieAlgebra R` (proved in
   `TauCeti.Algebra.Lie.KacMoody.Basic`), for any `x` with locally nilpotent `ad x` the vectors of
   an `Enveloping R`-module `M` annihilated by a power of `lieAction R M x` form an
   `Enveloping R`-submodule (`TauCeti.KacMoody.locallyNilpotentActionSubmodule`), specializing to
   `locallyNilpotentPositiveSubmodule` and `locallyNilpotentNegativeSubmodule`. Consequently, local
   nilpotence of `eᵢ` and `fᵢ` spreads from any `Enveloping R`-generating set to all of `M`.
2. **Integrality of primitive weights.** At any node `i` with `A i i = 2` in characteristic zero, a
   nonzero weight vector annihilated by `eᵢ` and by a power of `fᵢ` pairs with `R.coroot i` by a
   natural number `n : ℕ`. Thus every nonzero submodule of a module in `IsIntegrableO` (when
   `∀ i, A i i = 2`) contains a nonzero primitive vector whose weight takes natural-number values on
   all simple coroots.
3. **The simple Weyl intertwiners.** Over a field of characteristic zero, at any node `i` where
   `eᵢ` and `fᵢ` act locally nilpotently on `M` (in particular, on any integrable module), the
   operators `eᵢ` and `-fᵢ` exponentiate via `Module.End.locallyNilpotentExp` to the `K`-linear
   automorphism `sᵢ = exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ)` (`TauCeti.KacMoody.simpleWeylIntertwiner`).
   When `A i i = 2`, conjugation by `sᵢ` reflects the Cartan action according to
   `x ↦ x - αᵢ(x) • hᵢ` and restricts to a `K`-linear equivalence
   `M_μ ≃ₗ[K] M_{μ - μ(hᵢ) • αᵢ}`, forcing Weyl-invariance of weight multiplicities.

## Main definitions

* `TauCeti.KacMoody.locallyNilpotentActionSubmodule`,
  `TauCeti.KacMoody.locallyNilpotentPositiveSubmodule`,
  `TauCeti.KacMoody.locallyNilpotentNegativeSubmodule`: the `Enveloping R`-submodules of vectors
  annihilated by a power of `lieAction R M x`, `positiveAction R M i`, or `negativeAction R M i`.
* `TauCeti.KacMoody.IsIntegrable`: integrable `Enveloping R`-modules.
* `TauCeti.KacMoody.IsIntegrableO`: integrable modules in Kac's category `O`.
* `TauCeti.KacMoody.simpleWeylIntertwiner`: the simple reflection operator
  `exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ) : M ≃ₗ[K] M` at any node where `eᵢ` and `fᵢ` act locally
  nilpotently in characteristic zero.
* `TauCeti.KacMoody.simpleWeylIntertwinerWeightEquiv`: the induced `K`-linear equivalence
  `weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i)`.

## Main results

* `TauCeti.KacMoody.exists_lieAction_pow_eq_zero_of_span_eq_top`,
  `TauCeti.KacMoody.exists_positiveAction_pow_eq_zero_of_span_eq_top`,
  `TauCeti.KacMoody.exists_negativeAction_pow_eq_zero_of_span_eq_top`, and
  `TauCeti.KacMoody.IsIntegrable.of_span_eq_top`: local nilpotence spreads from any
  `Enveloping R`-generating set to the whole module.
* `TauCeti.KacMoody.IsIntegrable.submodule`, `TauCeti.KacMoody.IsIntegrable.quotient`,
  `TauCeti.KacMoody.IsIntegrable.prod`, `TauCeti.KacMoody.IsIntegrable.directSum`, and the
  corresponding closure theorems for `TauCeti.KacMoody.IsIntegrableO`.
* `KacMoody.exists_nat_apply_coroot_and_negativeAction_pow_succ_eq_zero_of_positiveAction_eq_zero`
  and `TauCeti.KacMoody.IsIntegrableO.exists_primitive_vector_of_ne_bot`: integrality of primitive
  weights and existence of dominant integral primitive vectors in nonzero submodules in
  characteristic zero.
* `TauCeti.KacMoody.cartanAction_simpleWeylIntertwiner_apply`,
  `TauCeti.KacMoody.simpleWeylIntertwiner_mem_weightSpace`,
  `TauCeti.KacMoody.finrank_weightSpace_sub_apply_coroot_smul_root`, and
  `TauCeti.KacMoody.weightSpace_sub_apply_coroot_smul_root_eq_bot_iff`: simple Weyl intertwiners
  reflect the Cartan action and preserve weight multiplicities.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
  §§3.5–3.8 and §10.1.
-/

public section

open DirectSum LieAlgebra Module

namespace TauCeti

namespace KacMoody

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}

/-! ### Spreading local nilpotence across an `Enveloping R`-module -/

section LocallyNilpotentSubmodule

/-- The vectors of `M` annihilated by some power of `lieAction R M x`, packaged as an
`Enveloping R`-submodule whenever `ad K (PresentedLieAlgebra R) x` is locally nilpotent. -/
noncomputable def locallyNilpotentActionSubmodule
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (x : PresentedLieAlgebra R)
    (hx : ∀ y : PresentedLieAlgebra R, ∃ k : ℕ, (ad K (PresentedLieAlgebra R) x ^ k) y = 0) :
    Submodule (Enveloping R) M :=
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  TauCeti.UniversalEnvelopingAlgebra.lieSubmoduleOrderIso
    (fun z m ↦
      (TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K
        (PresentedLieAlgebra R) M z m).symm)
    (TauCeti.locallyNilpotentSubmodule K M x hx)

/-- The vectors of `M` annihilated by some power of `positiveAction R M i`, packaged as an
`Enveloping R`-submodule via adjoint local nilpotence of `positiveGenerator R i`. -/
noncomputable def locallyNilpotentPositiveSubmodule
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Submodule (Enveloping R) M :=
  locallyNilpotentActionSubmodule R M (positiveGenerator R i)
    (exists_ad_positiveGenerator_pow_apply_eq_zero R i)

/-- The vectors of `M` annihilated by some power of `negativeAction R M i`, packaged as an
`Enveloping R`-submodule via adjoint local nilpotence of `negativeGenerator R i`. -/
noncomputable def locallyNilpotentNegativeSubmodule
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Submodule (Enveloping R) M :=
  locallyNilpotentActionSubmodule R M (negativeGenerator R i)
    (exists_ad_negativeGenerator_pow_apply_eq_zero R i)

variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

@[simp]
theorem mem_locallyNilpotentActionSubmodule {x : PresentedLieAlgebra R}
    {hx : ∀ y : PresentedLieAlgebra R, ∃ k : ℕ, (ad K (PresentedLieAlgebra R) x ^ k) y = 0}
    {m : M} :
    m ∈ locallyNilpotentActionSubmodule R M x hx ↔
      ∃ k : ℕ, (lieAction R M x ^ k) m = 0 := by
  let : LieRingModule (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  let : LieModule K (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  have hEnd : LieModule.toEnd K (PresentedLieAlgebra R) M x = lieAction R M x :=
    LinearMap.ext fun v ↦ by
      rw [LieModule.toEnd_apply_apply,
        TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K (PresentedLieAlgebra R) M,
        lieAction_apply]
  simp [locallyNilpotentActionSubmodule, hEnd]

@[simp]
theorem mem_locallyNilpotentPositiveSubmodule {i : I} {m : M} :
    m ∈ locallyNilpotentPositiveSubmodule R M i ↔
      ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  rw [locallyNilpotentPositiveSubmodule, mem_locallyNilpotentActionSubmodule,
    lieAction_positiveGenerator]

@[simp]
theorem mem_locallyNilpotentNegativeSubmodule {i : I} {m : M} :
    m ∈ locallyNilpotentNegativeSubmodule R M i ↔
      ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  rw [locallyNilpotentNegativeSubmodule, mem_locallyNilpotentActionSubmodule,
    lieAction_negativeGenerator]

/-- **Local nilpotence spreads from any `Enveloping R`-generating set.** If `ad x` is locally
nilpotent on `PresentedLieAlgebra R` and `lieAction R M x` acts nilpotently on every vector of an
`Enveloping R`-generating set `S`, then `lieAction R M x` acts locally nilpotently on all of `M`. -/
theorem exists_lieAction_pow_eq_zero_of_span_eq_top {x : PresentedLieAlgebra R}
    (hx : ∀ y : PresentedLieAlgebra R, ∃ k : ℕ, (ad K (PresentedLieAlgebra R) x ^ k) y = 0)
    {S : Set M} (hS : Submodule.span (Enveloping R) S = ⊤)
    (hnil : ∀ v ∈ S, ∃ k : ℕ, (lieAction R M x ^ k) v = 0) (m : M) :
    ∃ k : ℕ, (lieAction R M x ^ k) m = 0 := by
  have htop : locallyNilpotentActionSubmodule R M x hx = ⊤ := by
    rw [← top_le_iff, ← hS, Submodule.span_le]
    exact fun v hv ↦ mem_locallyNilpotentActionSubmodule.mpr (hnil v hv)
  exact mem_locallyNilpotentActionSubmodule.mp (htop ▸ Submodule.mem_top)

/-- **Local nilpotence of `eᵢ` spreads from any `Enveloping R`-generating set.** -/
theorem exists_positiveAction_pow_eq_zero_of_span_eq_top {S : Set M}
    (hS : Submodule.span (Enveloping R) S = ⊤) {i : I}
    (hnil : ∀ v ∈ S, ∃ k : ℕ, (positiveAction R M i ^ k) v = 0) (m : M) :
    ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  simpa only [lieAction_positiveGenerator] using
    exists_lieAction_pow_eq_zero_of_span_eq_top
      (exists_ad_positiveGenerator_pow_apply_eq_zero R i) hS
      (by simpa only [lieAction_positiveGenerator] using hnil) m

/-- **Local nilpotence of `fᵢ` spreads from any `Enveloping R`-generating set.** -/
theorem exists_negativeAction_pow_eq_zero_of_span_eq_top {S : Set M}
    (hS : Submodule.span (Enveloping R) S = ⊤) {i : I}
    (hnil : ∀ v ∈ S, ∃ k : ℕ, (negativeAction R M i ^ k) v = 0) (m : M) :
    ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  simpa only [lieAction_negativeGenerator] using
    exists_lieAction_pow_eq_zero_of_span_eq_top
      (exists_ad_negativeGenerator_pow_apply_eq_zero R i) hS
      (by simpa only [lieAction_negativeGenerator] using hnil) m

/-- On a simple `Enveloping R`-module, if `ad x` is locally nilpotent on `PresentedLieAlgebra R`
and `lieAction R M x` acts nilpotently at one nonzero vector then it acts locally nilpotently on
the whole module. -/
theorem exists_lieAction_pow_eq_zero_of_isSimpleModule [IsSimpleModule (Enveloping R) M]
    {x : PresentedLieAlgebra R}
    (hx : ∀ y : PresentedLieAlgebra R, ∃ k : ℕ, (ad K (PresentedLieAlgebra R) x ^ k) y = 0)
    {v : M} (hv : v ≠ 0) {k₀ : ℕ} (hk₀ : (lieAction R M x ^ k₀) v = 0) (m : M) :
    ∃ k : ℕ, (lieAction R M x ^ k) m = 0 :=
  exists_lieAction_pow_eq_zero_of_span_eq_top hx
    (IsSimpleModule.span_singleton_eq_top (Enveloping R) hv)
    (fun w hw ↦ by rcases Set.mem_singleton_iff.mp hw with rfl; exact ⟨k₀, hk₀⟩) m

/-- On a simple `Enveloping R`-module, if `eᵢ` acts nilpotently at one nonzero vector then it acts
locally nilpotently on the whole module. -/
theorem exists_positiveAction_pow_eq_zero_of_isSimpleModule [IsSimpleModule (Enveloping R) M]
    {i : I} {v : M} (hv : v ≠ 0) {k₀ : ℕ} (hk₀ : (positiveAction R M i ^ k₀) v = 0) (m : M) :
    ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  simpa only [lieAction_positiveGenerator] using
    exists_lieAction_pow_eq_zero_of_isSimpleModule
      (exists_ad_positiveGenerator_pow_apply_eq_zero R i) hv
      (by simpa only [lieAction_positiveGenerator] using hk₀) m

/-- On a simple `Enveloping R`-module, if `fᵢ` acts nilpotently at one nonzero vector then it acts
locally nilpotently on the whole module. -/
theorem exists_negativeAction_pow_eq_zero_of_isSimpleModule [IsSimpleModule (Enveloping R) M]
    {i : I} {v : M} (hv : v ≠ 0) {k₀ : ℕ} (hk₀ : (negativeAction R M i ^ k₀) v = 0) (m : M) :
    ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  simpa only [lieAction_negativeGenerator] using
    exists_lieAction_pow_eq_zero_of_isSimpleModule
      (exists_ad_negativeGenerator_pow_apply_eq_zero R i) hv
      (by simpa only [lieAction_negativeGenerator] using hk₀) m

end LocallyNilpotentSubmodule

/-! ### Integrable modules and `IsIntegrableO` -/

section IsIntegrable

/-- An `Enveloping R`-module `M` is **integrable** (`IsIntegrable R M`, Kac §3.6) when it is a
weight module on which every Chevalley generator `eᵢ` and `fᵢ` acts locally nilpotently. -/
structure IsIntegrable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : Prop where
  /-- `M` decomposes as the sum of its weight spaces. -/
  isWeightModule : IsWeightModule R M
  /-- Every `positiveAction R M i` acts locally nilpotently on `M`. -/
  locallyNilpotent_positiveAction : ∀ (i : I) (m : M), ∃ k : ℕ, (positiveAction R M i ^ k) m = 0
  /-- Every `negativeAction R M i` acts locally nilpotently on `M`. -/
  locallyNilpotent_negativeAction : ∀ (i : I) (m : M), ∃ k : ℕ, (negativeAction R M i ^ k) m = 0

/-- An `Enveloping R`-module `M` lies in `IsIntegrableO R M` (Kac's category `O_int`, §10.1) when it
lies in category `O` and is integrable. -/
structure IsIntegrableO (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : Prop extends IsCategoryO R M, IsIntegrable R M

variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module (Enveloping R) N]
  [IsScalarTower K (Enveloping R) N]

/-- A weight module is integrable as soon as `eᵢ` and `fᵢ` act locally nilpotently on an
`Enveloping R`-generating set. -/
theorem IsIntegrable.of_span_eq_top (hM : IsWeightModule R M) {S : Set M}
    (hS : Submodule.span (Enveloping R) S = ⊤)
    (hpos : ∀ i : I, ∀ v ∈ S, ∃ k : ℕ, (positiveAction R M i ^ k) v = 0)
    (hneg : ∀ i : I, ∀ v ∈ S, ∃ k : ℕ, (negativeAction R M i ^ k) v = 0) :
    IsIntegrable R M where
  isWeightModule := hM
  locallyNilpotent_positiveAction i := exists_positiveAction_pow_eq_zero_of_span_eq_top hS (hpos i)
  locallyNilpotent_negativeAction i := exists_negativeAction_pow_eq_zero_of_span_eq_top hS (hneg i)

/-- Integrability pulls back along injective `Enveloping R`-linear maps. -/
theorem IsIntegrable.of_injective (hN : IsIntegrable R N) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Injective f) : IsIntegrable R M where
  isWeightModule := hN.isWeightModule.of_injective hf
  locallyNilpotent_positiveAction i m := by
    obtain ⟨k, hk⟩ := hN.locallyNilpotent_positiveAction i (f m)
    exact ⟨k, hf (by rw [map_positiveAction_pow, hk, map_zero])⟩
  locallyNilpotent_negativeAction i m := by
    obtain ⟨k, hk⟩ := hN.locallyNilpotent_negativeAction i (f m)
    exact ⟨k, hf (by rw [map_negativeAction_pow, hk, map_zero])⟩

/-- Submodules of integrable modules are integrable. -/
theorem IsIntegrable.submodule (hM : IsIntegrable R M) (P : Submodule (Enveloping R) M) :
    IsIntegrable R P :=
  hM.of_injective P.injective_subtype

/-- Surjective `Enveloping R`-linear images of integrable modules are integrable. -/
theorem IsIntegrable.of_surjective (hM : IsIntegrable R M) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Surjective f) : IsIntegrable R N where
  isWeightModule := hM.isWeightModule.of_surjective hf
  locallyNilpotent_positiveAction i y := by
    obtain ⟨m, rfl⟩ := hf y
    obtain ⟨k, hk⟩ := hM.locallyNilpotent_positiveAction i m
    exact ⟨k, by rw [← map_positiveAction_pow, hk, map_zero]⟩
  locallyNilpotent_negativeAction i y := by
    obtain ⟨m, rfl⟩ := hf y
    obtain ⟨k, hk⟩ := hM.locallyNilpotent_negativeAction i m
    exact ⟨k, by rw [← map_negativeAction_pow, hk, map_zero]⟩

/-- Quotients of integrable modules are integrable. -/
theorem IsIntegrable.quotient (hM : IsIntegrable R M) (P : Submodule (Enveloping R) M) :
    IsIntegrable R (M ⧸ P) :=
  hM.of_surjective P.mkQ_surjective

/-- Binary products of integrable modules are integrable. -/
theorem IsIntegrable.prod (hM : IsIntegrable R M) (hN : IsIntegrable R N) :
    IsIntegrable R (M × N) where
  isWeightModule := hM.isWeightModule.prod hN.isWeightModule
  locallyNilpotent_positiveAction i x := by
    obtain ⟨k₁, hk₁⟩ := hM.locallyNilpotent_positiveAction i x.fst
    obtain ⟨k₂, hk₂⟩ := hN.locallyNilpotent_positiveAction i x.snd
    refine ⟨max k₁ k₂, Prod.ext ?_ ?_⟩
    · have h1 := map_positiveAction_pow (LinearMap.fst (Enveloping R) M N) i (max k₁ k₂) x
      exact h1.trans (Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁)
    · have h2 := map_positiveAction_pow (LinearMap.snd (Enveloping R) M N) i (max k₁ k₂) x
      exact h2.trans (Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂)
  locallyNilpotent_negativeAction i x := by
    obtain ⟨k₁, hk₁⟩ := hM.locallyNilpotent_negativeAction i x.fst
    obtain ⟨k₂, hk₂⟩ := hN.locallyNilpotent_negativeAction i x.snd
    refine ⟨max k₁ k₂, Prod.ext ?_ ?_⟩
    · have h1 := map_negativeAction_pow (LinearMap.fst (Enveloping R) M N) i (max k₁ k₂) x
      exact h1.trans (Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁)
    · have h2 := map_negativeAction_pow (LinearMap.snd (Enveloping R) M N) i (max k₁ k₂) x
      exact h2.trans (Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂)

/-- Arbitrary direct sums of integrable modules are integrable. -/
theorem IsIntegrable.directSum {κ : Type*} {P : κ → Type*} [∀ j, AddCommGroup (P j)]
    [∀ j, Module K (P j)] [∀ j, Module (Enveloping R) (P j)]
    [∀ j, IsScalarTower K (Enveloping R) (P j)] (hP : ∀ j, IsIntegrable R (P j)) :
    IsIntegrable R (⨁ j, P j) where
  isWeightModule := IsWeightModule.directSum fun j ↦ (hP j).isWeightModule
  locallyNilpotent_positiveAction i v := by
    classical
    refine DirectSum.induction_on v ⟨0, map_zero _⟩ (fun j m ↦ ?_) fun x y ⟨kx, hkx⟩ ⟨ky, hky⟩ ↦ ?_
    · obtain ⟨k, hk⟩ := (hP j).locallyNilpotent_positiveAction i m
      exact ⟨k, by
        rw [← DirectSum.lof_eq_of (Enveloping R), ← map_positiveAction_pow, hk, map_zero]⟩
    · refine ⟨max kx ky, ?_⟩
      rw [map_add, Module.End.pow_map_zero_of_le (le_max_left kx ky) hkx,
        Module.End.pow_map_zero_of_le (le_max_right kx ky) hky, add_zero]
  locallyNilpotent_negativeAction i v := by
    classical
    refine DirectSum.induction_on v ⟨0, map_zero _⟩ (fun j m ↦ ?_) fun x y ⟨kx, hkx⟩ ⟨ky, hky⟩ ↦ ?_
    · obtain ⟨k, hk⟩ := (hP j).locallyNilpotent_negativeAction i m
      exact ⟨k, by
        rw [← DirectSum.lof_eq_of (Enveloping R), ← map_negativeAction_pow, hk, map_zero]⟩
    · refine ⟨max kx ky, ?_⟩
      rw [map_add, Module.End.pow_map_zero_of_le (le_max_left kx ky) hkx,
        Module.End.pow_map_zero_of_le (le_max_right kx ky) hky, add_zero]

/-- `IsIntegrableO` pulls back along injective `Enveloping R`-linear maps. -/
theorem IsIntegrableO.of_injective (hN : IsIntegrableO R N) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Injective f) : IsIntegrableO R M :=
  { hN.toIsCategoryO.of_injective hf, hN.toIsIntegrable.of_injective hf with }

/-- Submodules of modules in `IsIntegrableO` lie in `IsIntegrableO`. -/
theorem IsIntegrableO.submodule (hM : IsIntegrableO R M) (P : Submodule (Enveloping R) M) :
    IsIntegrableO R P :=
  hM.of_injective P.injective_subtype

/-- Surjective `Enveloping R`-linear images of modules in `IsIntegrableO` lie in `IsIntegrableO`. -/
theorem IsIntegrableO.of_surjective (hM : IsIntegrableO R M) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Surjective f) : IsIntegrableO R N :=
  { hM.toIsCategoryO.of_surjective hf, hM.toIsIntegrable.of_surjective hf with }

/-- Quotients of modules in `IsIntegrableO` lie in `IsIntegrableO`. -/
theorem IsIntegrableO.quotient (hM : IsIntegrableO R M) (P : Submodule (Enveloping R) M) :
    IsIntegrableO R (M ⧸ P) :=
  hM.of_surjective P.mkQ_surjective

/-- Binary products of modules in `IsIntegrableO` lie in `IsIntegrableO`. -/
theorem IsIntegrableO.prod (hM : IsIntegrableO R M) (hN : IsIntegrableO R N) :
    IsIntegrableO R (M × N) :=
  { hM.toIsCategoryO.prod hN.toIsCategoryO, hM.toIsIntegrable.prod hN.toIsIntegrable with }

/-- Finite direct sums of modules in `IsIntegrableO` lie in `IsIntegrableO`. -/
theorem IsIntegrableO.directSum {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, Module (Enveloping R) (P j)]
    [∀ j, IsScalarTower K (Enveloping R) (P j)] (hP : ∀ j, IsIntegrableO R (P j)) :
    IsIntegrableO R (⨁ j, P j) :=
  { IsCategoryO.directSum fun j ↦ (hP j).toIsCategoryO,
    IsIntegrable.directSum fun j ↦ (hP j).toIsIntegrable with }

end IsIntegrable

/-! ### Integrality and dominance of primitive weights -/

section PrimitiveIntegrality

variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

private theorem root_coroot_eq_two {i : I} (hA : A i i = 2) : R.root i (R.coroot i) = 2 := by
  have hp := R.root_coroot i i
  rw [Matrix.map_apply, hA, Int.cast_two] at hp
  exact hp

/-- **Ladder commutator on a weight vector.** At any node `i` with `A i i = 2`, raising `fᵢᵏ⁺¹ v`
for `v ∈ weightSpace R M μ` shifts `eᵢ` past `fᵢᵏ⁺¹` with scalar correction
`(k + 1) * (μ(hᵢ) - k)`. -/
theorem positiveAction_negativeAction_pow_succ_apply {i : I} (hA : A i i = 2) {μ : Dual K H}
    {v : M} (hv : v ∈ weightSpace R M μ) (k : ℕ) :
    positiveAction R M i ((negativeAction R M i ^ (k + 1)) v) =
      (negativeAction R M i ^ (k + 1)) (positiveAction R M i v) +
        (((k + 1 : ℕ) : K) * (μ (R.coroot i) - k)) • (negativeAction R M i ^ k) v := by
  have hef : positiveAction R M i * negativeAction R M i -
      negativeAction R M i * positiveAction R M i = cartanAction R M (R.coroot i) := by
    rw [← Ring.lie_def, lie_positiveAction_negativeAction_self]
  have hhf : cartanAction R M (R.coroot i) * negativeAction R M i -
      negativeAction R M i * cartanAction R M (R.coroot i) = -(2 • negativeAction R M i) := by
    rw [← Ring.lie_def, lie_cartanAction_negativeAction, root_coroot_eq_two (R := R) hA,
      two_smul, two_smul]
  have h := LinearMap.congr_fun (TauCeti.Sl2.e_mul_f_pow_succ hef hhf k) v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    _root_.mul_apply_eq_comp, _root_.natCast_apply_eq_smul,
    cartanAction_apply_of_mem_weightSpace hv, ← Nat.cast_smul_eq_nsmul K, ← sub_smul, map_smul,
    smul_smul] at h
  exact h

/-- **Integrality of a primitive weight at node `i`.** Over a field of characteristic zero, if
`A i i = 2` and `v` is a nonzero weight vector of weight `μ` killed by `eᵢ` and by some power of
`fᵢ`, then `μ (R.coroot i)` is a natural number `n : ℕ` and `(fᵢ ^ (n + 1)) v = 0`. -/
theorem exists_nat_apply_coroot_and_negativeAction_pow_succ_eq_zero_of_positiveAction_eq_zero
    [CharZero K] {i : I} (hA : A i i = 2) {μ : Dual K H} {v : M} (hv0 : v ≠ 0)
    (hv : v ∈ weightSpace R M μ) (he : positiveAction R M i v = 0)
    (hnil : ∃ k : ℕ, (negativeAction R M i ^ k) v = 0) :
    ∃ n : ℕ, μ (R.coroot i) = n ∧ (negativeAction R M i ^ (n + 1)) v = 0 := by
  obtain ⟨n, hnz, hz⟩ :=
    TauCeti.exists_pow_smul_ne_zero_and_smul_eq_zero (x := negativeAction R M i) hv0 hnil
  simp only [Module.End.smul_def] at hnz hz
  have hz' : (negativeAction R M i ^ (n + 1)) v = 0 := by
    rwa [pow_succ', _root_.mul_apply_eq_comp]
  have hcomm := positiveAction_negativeAction_pow_succ_apply hA hv n
  rw [hz', he, map_zero, map_zero, zero_add, eq_comm, smul_eq_zero] at hcomm
  have hscalar : ((n + 1 : ℕ) : K) * (μ (R.coroot i) - n) = 0 := hcomm.resolve_right hnz
  have hn1 : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  exact ⟨n, sub_eq_zero.mp ((mul_eq_zero.mp hscalar).resolve_left hn1), hz'⟩

/-- **Existence of dominant integral primitive vectors in `IsIntegrableO`.** Over a field of
characteristic zero, when `∀ i, A i i = 2`, every nonzero `Enveloping R`-submodule `P` of a module
in `IsIntegrableO R M` contains a nonzero primitive vector whose weight pairs with every simple
coroot by a natural number. -/
theorem IsIntegrableO.exists_primitive_vector_of_ne_bot [CharZero K] (hA : ∀ i : I, A i i = 2)
    (hM : IsIntegrableO R M) {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ (μ : Dual K H) (v : M), v ∈ P ∧ v ≠ 0 ∧ v ∈ weightSpace R M μ ∧
      (∀ i : I, positiveAction R M i v = 0) ∧ ∀ i : I, ∃ n : ℕ, μ (R.coroot i) = n := by
  obtain ⟨μ, v, hvP, hv0, hvw, hprim⟩ := hM.toIsCategoryO.exists_primitive_vector_of_ne_bot hP
  refine ⟨μ, v, hvP, hv0, hvw, hprim, fun i ↦ ?_⟩
  obtain ⟨n, hn, -⟩ :=
    exists_nat_apply_coroot_and_negativeAction_pow_succ_eq_zero_of_positiveAction_eq_zero
      (hA i) hv0 hvw (hprim i) (hM.locallyNilpotent_negativeAction i v)
  exact ⟨n, hn⟩

end PrimitiveIntegrality

/-! ### The simple Weyl intertwiners -/

section SimpleWeylIntertwiner

variable [CharZero K]
variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- Kac's **simple Weyl intertwiner** `rᵢ^M = exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ) : M ≃ₗ[K] M` (§3.8) at
any node `i` where `positiveAction R M i` and `negativeAction R M i` act locally nilpotently over a
field of characteristic zero. -/
noncomputable def simpleWeylIntertwiner {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0) : M ≃ₗ[K] M :=
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  (Module.End.locallyNilpotentExp (positiveAction R M i) he).trans
    ((Module.End.locallyNilpotentExp (-negativeAction R M i)
        (fun m ↦ by simpa [Module.End.neg_pow_apply_eq_zero_iff] using hf m)).trans
      (Module.End.locallyNilpotentExp (positiveAction R M i) he))

/-- On any `ℚ`-module structure on `M` (which is unique by `subsingleton_rat_module`),
`simpleWeylIntertwiner` acts as the threefold composite `exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ)`. -/
theorem simpleWeylIntertwiner_apply [Module ℚ M] {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0) (m : M) :
    simpleWeylIntertwiner he hf m =
      Module.End.locallyNilpotentExp (positiveAction R M i) he
        (Module.End.locallyNilpotentExp (-negativeAction R M i)
          (fun x ↦ by simpa [Module.End.neg_pow_apply_eq_zero_iff] using hf x)
          (Module.End.locallyNilpotentExp (positiveAction R M i) he m)) := by
  have hrat : (Module.compHom M (algebraMap ℚ K) : Module ℚ M) = ‹Module ℚ M› :=
    Subsingleton.elim _ _
  dsimp only [simpleWeylIntertwiner, LinearEquiv.trans_apply]
  congr!

/-- On any `ℚ`-module structure on `M`, `(simpleWeylIntertwiner he hf).symm` acts as
`exp(-eᵢ) ∘ exp(fᵢ) ∘ exp(-eᵢ)`. -/
theorem simpleWeylIntertwiner_symm_apply [inst : Module ℚ M] {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0) (m : M) :
    (simpleWeylIntertwiner he hf).symm m =
      Module.End.locallyNilpotentExp (-positiveAction R M i)
        (fun x ↦ by simpa [Module.End.neg_pow_apply_eq_zero_iff] using he x)
        (Module.End.locallyNilpotentExp (negativeAction R M i) hf
          (Module.End.locallyNilpotentExp (-positiveAction R M i)
            (fun x ↦ by simpa [Module.End.neg_pow_apply_eq_zero_iff] using he x) m)) := by
  obtain rfl : inst = Module.compHom M (algebraMap ℚ K) := Subsingleton.elim _ _
  let : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  have hneg_symm (x : M) :
      (Module.End.locallyNilpotentExp (-negativeAction R M i)
        (fun y ↦ by simpa [Module.End.neg_pow_apply_eq_zero_iff] using hf y)).symm x =
        Module.End.locallyNilpotentExp (negativeAction R M i) hf x := by
    rw [Module.End.locallyNilpotentExp_symm]
    simp only [neg_neg]
  dsimp only [simpleWeylIntertwiner, LinearEquiv.symm_trans_apply]
  rw [Module.End.locallyNilpotentExp_symm, hneg_symm]

/-- **Naturality of `simpleWeylIntertwiner`.** Every `Enveloping R`-linear map intertwines
`simpleWeylIntertwiner`. -/
theorem map_simpleWeylIntertwiner {N : Type*} [AddCommGroup N] [Module K N]
    [Module (Enveloping R) N] [IsScalarTower K (Enveloping R) N] {i : I}
    (heM : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hfM : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (heN : ∀ y : N, ∃ k : ℕ, (positiveAction R N i ^ k) y = 0)
    (hfN : ∀ y : N, ∃ k : ℕ, (negativeAction R N i ^ k) y = 0)
    (f : M →ₗ[Enveloping R] N) (m : M) :
    f (simpleWeylIntertwiner heM hfM m) = simpleWeylIntertwiner heN hfN (f m) := by
  let : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  let : Module ℚ N := Module.compHom N (algebraMap ℚ K)
  have hpos : Function.Semiconj f (positiveAction R M i) (positiveAction R N i) :=
    map_positiveAction f i
  have hneg : Function.Semiconj f (-negativeAction R M i : Module.End K M)
      (-negativeAction R N i : Module.End K N) := fun x ↦ by
    simp [map_negativeAction]
  have hneg_nil_N (y : N) : ∃ k, ((-negativeAction R N i) ^ k) y = 0 := by
    simpa [Module.End.neg_pow_apply_eq_zero_iff] using hfN y
  rw [simpleWeylIntertwiner_apply, simpleWeylIntertwiner_apply,
    Module.End.map_locallyNilpotentExp _ _ heN f hpos,
    Module.End.map_locallyNilpotentExp _ _ hneg_nil_N f hneg,
    Module.End.map_locallyNilpotentExp _ _ heN f hpos]

/-- **Naturality of `(simpleWeylIntertwiner he hf).symm`.** Every `Enveloping R`-linear map
intertwines the inverse simple Weyl intertwiner. -/
theorem map_simpleWeylIntertwiner_symm {N : Type*} [AddCommGroup N] [Module K N]
    [Module (Enveloping R) N] [IsScalarTower K (Enveloping R) N] {i : I}
    (heM : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hfM : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (heN : ∀ y : N, ∃ k : ℕ, (positiveAction R N i ^ k) y = 0)
    (hfN : ∀ y : N, ∃ k : ℕ, (negativeAction R N i ^ k) y = 0)
    (f : M →ₗ[Enveloping R] N) (m : M) :
    f ((simpleWeylIntertwiner heM hfM).symm m) =
      (simpleWeylIntertwiner heN hfN).symm (f m) := by
  apply (simpleWeylIntertwiner heN hfN).injective
  rw [LinearEquiv.apply_symm_apply, ← map_simpleWeylIntertwiner heM hfM heN hfN f,
    LinearEquiv.apply_symm_apply]

omit [CharZero K] in
private theorem exp_positiveAction_cartanAction_apply [Module ℚ M] {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0) (x : H) (m : M) :
    Module.End.locallyNilpotentExp (positiveAction R M i) he (cartanAction R M x m) =
      cartanAction R M x (Module.End.locallyNilpotentExp (positiveAction R M i) he m) -
        R.root i x • positiveAction R M i
          (Module.End.locallyNilpotentExp (positiveAction R M i) he m) := by
  have h1 : ⁅positiveAction R M i, cartanAction R M x⁆ = -(R.root i x • positiveAction R M i) := by
    rw [← lie_skew, lie_cartanAction_positiveAction]
  have h2 : ⁅positiveAction R M i, ⁅positiveAction R M i, cartanAction R M x⁆⁆ = 0 := by
    rw [h1, lie_neg, lie_smul, lie_self, smul_zero, neg_zero]
  rw [Module.End.locallyNilpotentExp_apply_of_lie_lie_eq_zero _ _ h2, h1, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, sub_eq_add_neg]

private theorem exp_neg_negativeAction_step [Module ℚ M] {i : I} (hA : A i i = 2)
    (hneg : ∀ y : M, ∃ k : ℕ, ((-negativeAction R M i) ^ k) y = 0) (x : H) (m : M) :
    Module.End.locallyNilpotentExp (-negativeAction R M i) hneg
        ((cartanAction R M (x - R.root i x • R.coroot i) +
          R.root i x • positiveAction R M i) m) =
      (cartanAction R M x + R.root i x • positiveAction R M i)
        (Module.End.locallyNilpotentExp (-negativeAction R M i) hneg m) := by
  have hrc := root_coroot_eq_two (R := R) hA
  set g := cartanAction R M (x - R.root i x • R.coroot i) + R.root i x • positiveAction R M i
  have hrx : R.root i (x - R.root i x • R.coroot i) = -R.root i x := by
    rw [map_sub, map_smul, hrc, smul_eq_mul]
    ring
  have hd₁ : ⁅-negativeAction R M i, g⁆ =
      R.root i x • negativeAction R M i + R.root i x • cartanAction R M (R.coroot i) := by
    simp only [g, lie_add, neg_lie, ← lie_skew (negativeAction R M i) (cartanAction R M _),
      lie_cartanAction_negativeAction, hrx, neg_smul, neg_neg, lie_smul,
      ← lie_skew (negativeAction R M i) (positiveAction R M i),
      lie_positiveAction_negativeAction_self]
  have hd₂ : ⁅-negativeAction R M i, ⁅-negativeAction R M i, g⁆⁆ =
      -((2 : K) • (R.root i x • negativeAction R M i)) := by
    rw [hd₁, lie_add, neg_lie, lie_smul, lie_self, smul_zero, neg_zero, zero_add, neg_lie,
      lie_smul, ← lie_skew (negativeAction R M i) (cartanAction R M _),
      lie_cartanAction_negativeAction, hrc, neg_neg, smul_comm (R.root i x) (2 : K)]
  have hd₃ : ⁅-negativeAction R M i, ⁅-negativeAction R M i, ⁅-negativeAction R M i, g⁆⁆⁆ = 0 := by
    rw [hd₂, lie_neg, lie_smul, lie_smul, neg_lie, lie_self, neg_zero, smul_zero, smul_zero,
      neg_zero]
  have hhalf : ((2⁻¹ : ℚ) • ⁅-negativeAction R M i, ⁅-negativeAction R M i, g⁆⁆ :
      Module.End K M) = -(R.root i x • negativeAction R M i) := by
    rw [hd₂, smul_neg, ← Rat.cast_smul_eq_qsmul K, smul_smul, Rat.cast_inv, Rat.cast_ofNat,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  have hop : g + (R.root i x • negativeAction R M i + R.root i x • cartanAction R M (R.coroot i)) +
      -(R.root i x • negativeAction R M i) =
      cartanAction R M x + R.root i x • positiveAction R M i := by
    simp only [g, map_sub, map_smul]
    abel
  rw [Module.End.locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero (-negativeAction R M i) hneg
      hd₃ m,
    hhalf, hd₁, hop]

/-- **Conjugating the Cartan action by `simpleWeylIntertwiner`.** When `A i i = 2`,
`cartanAction R M x (simpleWeylIntertwiner he hf m) =
  simpleWeylIntertwiner he hf (cartanAction R M (x - R.root i x • R.coroot i) m)`. -/
theorem cartanAction_simpleWeylIntertwiner_apply {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (x : H) (m : M) :
    cartanAction R M x (simpleWeylIntertwiner he hf m) =
      simpleWeylIntertwiner he hf (cartanAction R M (x - R.root i x • R.coroot i) m) := by
  let : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  have hrc := root_coroot_eq_two (R := R) hA
  have hrx : R.root i (x - R.root i x • R.coroot i) = -R.root i x := by
    rw [map_sub, map_smul, hrc, smul_eq_mul]
    ring
  have hcomm_e (v : M) :
      Module.End.locallyNilpotentExp (positiveAction R M i) he (positiveAction R M i v) =
        positiveAction R M i (Module.End.locallyNilpotentExp (positiveAction R M i) he v) :=
    Module.End.locallyNilpotentExp_apply_of_lie_eq_zero _ _ (lie_self _) v
  rw [simpleWeylIntertwiner_apply, simpleWeylIntertwiner_apply,
    exp_positiveAction_cartanAction_apply he (x - R.root i x • R.coroot i) m, hrx, neg_smul,
    sub_neg_eq_add, ← LinearMap.smul_apply, ← LinearMap.add_apply,
    exp_neg_negativeAction_step hA _ x, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, exp_positiveAction_cartanAction_apply he x, hcomm_e, sub_add_cancel]

/-- Pushing `cartanAction` forward across `simpleWeylIntertwiner`. -/
theorem simpleWeylIntertwiner_cartanAction_apply {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (x : H) (m : M) :
    simpleWeylIntertwiner he hf (cartanAction R M x m) =
      cartanAction R M (x - R.root i x • R.coroot i) (simpleWeylIntertwiner he hf m) := by
  have hrc := root_coroot_eq_two (R := R) hA
  have hinv : (x - R.root i x • R.coroot i) -
      R.root i (x - R.root i x • R.coroot i) • R.coroot i = x := by
    rw [map_sub, map_smul, hrc, smul_eq_mul, sub_smul, mul_two, add_smul]
    abel
  rw [cartanAction_simpleWeylIntertwiner_apply he hf hA, hinv]

/-- **Simple Weyl intertwiners permute weight spaces by simple reflections.** When `A i i = 2`,
`simpleWeylIntertwiner he hf` maps `weightSpace R M μ` into
`weightSpace R M (μ - μ (R.coroot i) • R.root i)`. -/
theorem simpleWeylIntertwiner_mem_weightSpace {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) {μ : Dual K H} {m : M} (hm : m ∈ weightSpace R M μ) :
    simpleWeylIntertwiner he hf m ∈ weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  rw [cartanAction_simpleWeylIntertwiner_apply he hf hA,
    cartanAction_apply_of_mem_weightSpace hm, map_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply]
  simp only [smul_eq_mul, mul_comm (R.root i x) (μ (R.coroot i))]

/-- **Simple Weyl intertwiners permute weight spaces by simple reflections (inverse direction).**
When `A i i = 2`, `(simpleWeylIntertwiner he hf).symm` maps `weightSpace R M μ` into
`weightSpace R M (μ - μ (R.coroot i) • R.root i)`. -/
theorem simpleWeylIntertwiner_symm_mem_weightSpace {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) {μ : Dual K H} {m : M} (hm : m ∈ weightSpace R M μ) :
    (simpleWeylIntertwiner he hf).symm m ∈ weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  apply (simpleWeylIntertwiner he hf).injective
  rw [map_smul, LinearEquiv.apply_symm_apply, simpleWeylIntertwiner_cartanAction_apply he hf hA,
    LinearEquiv.apply_symm_apply, cartanAction_apply_of_mem_weightSpace hm, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [smul_eq_mul, mul_comm (R.root i x) (μ (R.coroot i))]

/-- **Weyl-reflection equivalence of weight spaces.** Over a field of characteristic zero, at any
node `i` with `A i i = 2` where `eᵢ` and `fᵢ` act locally nilpotently, `simpleWeylIntertwiner`
restricts to a `K`-linear equivalence
`weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i)`. -/
noncomputable def simpleWeylIntertwinerWeightEquiv {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (μ : Dual K H) :
    weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  have hrc := root_coroot_eq_two (R := R) hA
  have hinv : (μ - μ (R.coroot i) • R.root i) -
      (μ - μ (R.coroot i) • R.root i) (R.coroot i) • R.root i = μ := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hrc, smul_eq_mul]
    ring
  have hmap : (weightSpace R M μ).map (simpleWeylIntertwiner he hf).toLinearMap =
      weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
    refine le_antisymm ?_ fun w hw ↦ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact simpleWeylIntertwiner_mem_weightSpace he hf hA hv
    · refine ⟨(simpleWeylIntertwiner he hf).symm w, ?_,
        (simpleWeylIntertwiner he hf).apply_symm_apply w⟩
      have hw' := simpleWeylIntertwiner_symm_mem_weightSpace he hf hA hw
      rwa [hinv] at hw'
  exact (simpleWeylIntertwiner he hf).ofSubmodules _ _ hmap

@[simp]
theorem coe_simpleWeylIntertwinerWeightEquiv_apply {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (μ : Dual K H) (v : weightSpace R M μ) :
    (simpleWeylIntertwinerWeightEquiv he hf hA μ v : M) = simpleWeylIntertwiner he hf v := (rfl)

@[simp]
theorem coe_simpleWeylIntertwinerWeightEquiv_symm_apply {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (μ : Dual K H)
    (w : weightSpace R M (μ - μ (R.coroot i) • R.root i)) :
    ((simpleWeylIntertwinerWeightEquiv he hf hA μ).symm w : M) =
      (simpleWeylIntertwiner he hf).symm w := (rfl)

/-- Weight multiplicities are invariant under simple reflections at any node `i` with `A i i = 2`
where `eᵢ` and `fᵢ` act locally nilpotently. -/
theorem finrank_weightSpace_sub_apply_coroot_smul_root {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (μ : Dual K H) :
    Module.finrank K (weightSpace R M (μ - μ (R.coroot i) • R.root i)) =
      Module.finrank K (weightSpace R M μ) :=
  (simpleWeylIntertwinerWeightEquiv he hf hA μ).symm.finrank_eq

/-- The set of weights is preserved by simple reflections at any node `i` with `A i i = 2` where
`eᵢ` and `fᵢ` act locally nilpotently. -/
theorem weightSpace_sub_apply_coroot_smul_root_eq_bot_iff {i : I}
    (he : ∀ m : M, ∃ k : ℕ, (positiveAction R M i ^ k) m = 0)
    (hf : ∀ m : M, ∃ k : ℕ, (negativeAction R M i ^ k) m = 0)
    (hA : A i i = 2) (μ : Dual K H) :
    weightSpace R M (μ - μ (R.coroot i) • R.root i) = ⊥ ↔ weightSpace R M μ = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (simpleWeylIntertwinerWeightEquiv he hf hA μ).symm.toEquiv.subsingleton_congr

end SimpleWeylIntertwiner

end KacMoody

end TauCeti
