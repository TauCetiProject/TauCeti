/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Lie.KacMoody.WeightModule
public import TauCeti.Algebra.Lie.Sl2.Weyl.Standard
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
`TauCeti.KacMoody.IsIntegrableO R M` of integrable highest-weight modules.

Four structural mechanisms govern integrable Kac–Moody representations:

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
4. **Concrete simple integrable models.** For an arbitrary index type `I` and any weight `lam`
   vanishing on all simple coroots (`∀ i, lam (R.coroot i) = 0`),
   `TauCeti.KacMoody.OneDimModule R lam hlam` realizes the one-dimensional simple `IsIntegrableO`
   module of weight `lam` (covering `[IsEmpty I]` via `isEmptyElim`, trivial modules, and affine
   level-zero modules). For rank one (`[Unique I]`, `A default default = 2`),
   `TauCeti.KacMoody.RankOneModule R hA lam n hlam` equips `TauCeti.Sl2Std K n` over a field of
   characteristic zero (`[CharZero K]`) with an `Enveloping R`-action for any realization `H` and
   any weight `lam` with `lam (R.coroot default) = n`, giving an `(n + 1)`-dimensional simple
   `IsIntegrableO` module on which `simpleWeylIntertwiner` agrees with `TauCeti.Sl2Std.weylUnit`
   and squares to `(-1) ^ n`.

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
* `TauCeti.KacMoody.OneDimModule` (with `OneDimModule.equiv` and `OneDimModule.rep`): the
  one-dimensional simple `IsIntegrableO` module for any weight `lam` vanishing on all simple
  coroots.
* `TauCeti.KacMoody.RankOneModule` (with `RankOneModule.equiv`, `RankOneModule.basis`, and
  `RankOneModule.rep`): for `[Unique I]` and `A default default = 2`, the `(n + 1)`-dimensional
  module whose `Enveloping R`-action, simplicity, and `IsIntegrableO` structure are defined over
  `[CharZero K]`.

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
* `TauCeti.KacMoody.OneDimModule.isSimpleModule`, `TauCeti.KacMoody.OneDimModule.isIntegrableO`,
  `TauCeti.KacMoody.RankOneModule.isSimpleModule`, `TauCeti.KacMoody.RankOneModule.isIntegrableO`,
  `TauCeti.KacMoody.RankOneModule.equiv_simpleWeylIntertwiner_apply`,
  `TauCeti.KacMoody.RankOneModule.simpleWeylIntertwiner_basis`, and
  `TauCeti.KacMoody.RankOneModule.simpleWeylIntertwiner_simpleWeylIntertwiner_apply`: simplicity,
  integrability, and the Weyl square `(-1) ^ n` on the one-dimensional and rank-one models.

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

/-! ### Concrete simple integrable models -/

section OneDimModule

/-- **The one-dimensional module `K_λ`** for any weight `lam : Dual K H` vanishing on all simple
coroots (`∀ i : I, lam (R.coroot i) = 0`). It is an exposed type synonym for `K` on which
`cartanElement R x` acts by `lam x` and every Chevalley generator `eᵢ`, `fᵢ` acts by `0`. When
`I` is empty, the coroot-vanishing condition holds vacuously via `isEmptyElim`. -/
@[expose] def OneDimModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_lam : Dual K H) (_hlam : ∀ i : I, _lam (_R.coroot i) = 0) : Type _ := K

namespace OneDimModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (lam : Dual K H)
  (hlam : ∀ i : I, lam (R.coroot i) = 0)

instance : AddCommGroup (OneDimModule R lam hlam) := inferInstanceAs (AddCommGroup K)
instance : Module K (OneDimModule R lam hlam) := inferInstanceAs (Module K K)
instance : FiniteDimensional K (OneDimModule R lam hlam) :=
  inferInstanceAs (FiniteDimensional K K)
instance : Nontrivial (OneDimModule R lam hlam) := inferInstanceAs (Nontrivial K)

/-- The identity `K`-linear equivalence `OneDimModule R lam hlam ≃ₗ[K] K`. -/
def equiv : OneDimModule R lam hlam ≃ₗ[K] K := LinearEquiv.refl K K

@[simp]
theorem equiv_apply (v : OneDimModule R lam hlam) : equiv R lam hlam v = v := (rfl)

@[simp]
theorem equiv_symm_apply (c : K) : (equiv R lam hlam).symm c = c := (rfl)

@[simp]
theorem finrank_eq_one : Module.finrank K (OneDimModule R lam hlam) = 1 :=
  Module.finrank_self K

private def cartanHom : H →ₗ[K] Module.End K (OneDimModule R lam hlam) :=
  lam.smulRight 1

private theorem satisfiesRelations :
    SatisfiesRelations R (cartanHom R lam hlam) 0 0 where
  lie_cartan_cartan x y := by
    simp only [cartanHom, LinearMap.smulRight_apply, Ring.lie_def, mul_smul_comm,
      mul_one, mul_comm (lam x) (lam y), smul_smul, sub_self]
  lie_cartan_positive _ _ := by simp
  lie_cartan_negative _ _ := by simp
  lie_positive_negative_self i := by simp [cartanHom, hlam]
  lie_positive_negative_of_ne _ _ _ := by simp
  serre_positive _ _ := by simp
  serre_negative _ _ := by simp

/-- The `Enveloping R`-algebra representation defining the module action on
`OneDimModule R lam hlam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (OneDimModule R lam hlam) :=
  _root_.UniversalEnvelopingAlgebra.lift K (KacMoody.lift (satisfiesRelations R lam hlam))

noncomputable instance : Module (Enveloping R) (OneDimModule R lam hlam) :=
  Module.compHom (OneDimModule R lam hlam) (rep R lam hlam).toRingHom

/-- Scalar multiplication on `OneDimModule` is evaluation of `rep`. -/
theorem smul_def (u : Enveloping R) (v : OneDimModule R lam hlam) :
    u • v = rep R lam hlam u v := (rfl)

/-- Evaluating `rep` gives the `Enveloping R`-module scalar multiplication on `OneDimModule`. -/
@[simp]
theorem rep_apply (u : Enveloping R) (v : OneDimModule R lam hlam) :
    rep R lam hlam u v = u • v := (rfl)

instance : IsScalarTower K (Enveloping R) (OneDimModule R lam hlam) where
  smul_assoc c u v := by
    rw [smul_def, smul_def, AlgHom.map_smul_of_tower, LinearMap.smul_apply]

@[simp]
theorem cartanAction_apply_eq (x : H) (v : OneDimModule R lam hlam) :
    cartanAction R (OneDimModule R lam hlam) x v = lam x • v := by
  rw [cartanAction_apply, smul_def]
  simp [rep, cartanHom]

@[simp]
theorem positiveAction_apply_eq (i : I) (v : OneDimModule R lam hlam) :
    positiveAction R (OneDimModule R lam hlam) i v = 0 := by
  rw [positiveAction_apply, smul_def]
  simp [rep]

@[simp]
theorem negativeAction_apply_eq (i : I) (v : OneDimModule R lam hlam) :
    negativeAction R (OneDimModule R lam hlam) i v = 0 := by
  rw [negativeAction_apply, smul_def]
  simp [rep]

@[simp]
theorem weightSpace_self : weightSpace R (OneDimModule R lam hlam) lam = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_weightSpace_iff]
  exact fun x ↦ cartanAction_apply_eq R lam hlam x v

theorem weightSpace_eq_bot_of_ne {μ : Dual K H} (hμ : μ ≠ lam) :
    weightSpace R (OneDimModule R lam hlam) μ = ⊥ :=
  weightSpace_eq_bot_of_iSup_eq_top R (OneDimModule R lam hlam)
    (W := fun _ : Unit ↦ (⊤ : Submodule K (OneDimModule R lam hlam)))
    (w := fun _ : Unit ↦ lam) (fun _ ↦ by simp) (by simp) (by simpa using hμ)

/-- `OneDimModule R lam hlam` is a simple `Enveloping R`-module. -/
instance isSimpleModule : IsSimpleModule (Enveloping R) (OneDimModule R lam hlam) where
  eq_bot_or_eq_top P := by
    let : IsSimpleModule K (OneDimModule R lam hlam) := IsSimpleModule.congr (equiv R lam hlam)
    exact (eq_bot_or_eq_top (P.restrictScalars K)).imp
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))

/-- `OneDimModule R lam hlam` lies in `IsIntegrableO R`. -/
theorem isIntegrableO : IsIntegrableO R (OneDimModule R lam hlam) where
  isWeightModule := by
    rw [isWeightModule_iff, eq_top_iff, ← weightSpace_self R lam hlam]
    exact le_iSup (weightSpace R (OneDimModule R lam hlam)) lam
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hne
    refine hμ (weightSpace_eq_bot_of_ne R lam hlam fun h ↦ hne ?_)
    subst h
    exact CartanRealization.rootLE_refl μ⟩⟩
  locallyNilpotent_positiveAction i v := ⟨1, by simp⟩
  locallyNilpotent_negativeAction i v := ⟨1, by simp⟩

end OneDimModule

end OneDimModule

section RankOneModule

variable [Unique I]

/-- **The standard `(n + 1)`-dimensional rank-one Kac–Moody module `L(λ)`** for a single-node
index type `[Unique I]` with `A default default = 2` and `lam (R.coroot default) = n`. Over a
field of characteristic zero (`[CharZero K]`), it equips `TauCeti.Sl2Std K n` with the action of
`Enveloping R` for an arbitrary realization `H` of `A` (including realizations with central or
scaling directions), extending `Sl2Std.diag K n` from `R.coroot default` to all of `H` via `lam`,
yielding a simple module in `IsIntegrableO R`. -/
@[expose] def RankOneModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_hA : A default default = 2) (_lam : Dual K H) (n : ℕ)
    (_hlam : _lam (_R.coroot default) = n) : Type _ :=
  Sl2Std K n

namespace RankOneModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A default default = 2)
  (lam : Dual K H) (n : ℕ) (hlam : lam (R.coroot default) = n)

instance : AddCommGroup (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (AddCommGroup (Sl2Std K n))

instance : Module K (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module K (Sl2Std K n))

instance [CharZero K] : Module ℚ (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module ℚ (Sl2Std K n))

instance : FiniteDimensional K (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module.Finite K (Sl2Std K n))

instance : Nontrivial (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Nontrivial (Sl2Std K n))

/-- The identity `K`-linear equivalence `RankOneModule R hA lam n hlam ≃ₗ[K] Sl2Std K n`. -/
def equiv : RankOneModule R hA lam n hlam ≃ₗ[K] Sl2Std K n :=
  LinearEquiv.refl K (Sl2Std K n)

/-- The coordinate basis of `RankOneModule R hA lam n hlam` transported from `Sl2Std.basis K n`. -/
noncomputable def basis : Module.Basis (Fin (n + 1)) K (RankOneModule R hA lam n hlam) :=
  (Sl2Std.basis K n).map (equiv R hA lam n hlam).symm

@[simp]
theorem equiv_basis (k : Fin (n + 1)) :
    equiv R hA lam n hlam (basis R hA lam n hlam k) = Sl2Std.basis K n k := by
  simp [basis]

@[simp]
theorem finrank_eq : Module.finrank K (RankOneModule R hA lam n hlam) = n + 1 :=
  Sl2Std.finrank_eq

section CharZero

variable [CharZero K]

private noncomputable def sl2CartanHom : H →ₗ[K] Module.End K (Sl2Std K n) :=
  (lam - ((n : K) * 2⁻¹) • R.root default).smulRight 1 +
    ((2⁻¹ : K) • R.root default).smulRight (Sl2Std.diag K n)

private theorem sl2CartanHom_coroot (hA : A default default = 2) :
    sl2CartanHom R lam n (R.coroot default) =
      ((lam (R.coroot default) - (n : K)) • (1 : Module.End K (Sl2Std K n))) + Sl2Std.diag K n := by
  have hrc : R.root default (R.coroot default) = 2 := root_coroot_eq_two (R := R) hA
  simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hrc, smul_eq_mul]
  rw [mul_assoc (n : K) 2⁻¹ 2, inv_mul_cancel₀ two_ne_zero, mul_one, one_smul]

private noncomputable def sl2Rep (hA : A default default = 2) (hlam : lam (R.coroot default) = n) :
    Enveloping R →ₐ[K] Module.End K (Sl2Std K n) :=
  _root_.UniversalEnvelopingAlgebra.lift K <| KacMoody.lift <|
    { lie_cartan_cartan := fun x y ↦ by
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, lie_add, add_lie,
          lie_smul, smul_lie, Ring.lie_def (1 : Module.End K (Sl2Std K n)),
          Ring.lie_def _ (1 : Module.End K (Sl2Std K n)), mul_one, one_mul, sub_self, lie_self,
          smul_zero, add_zero]
      lie_cartan_positive := fun x j ↦ by
        rw [Unique.eq_default j]
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.raise K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_raise, smul_zero, zero_add, smul_smul, mul_assoc,
          mul_comm (R.root default x) 2, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
      lie_cartan_negative := fun x j ↦ by
        rw [Unique.eq_default j]
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.lower K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_lower, smul_zero, zero_add, smul_neg, smul_smul, mul_assoc,
          mul_comm (R.root default x) 2, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
      lie_positive_negative_self := fun i ↦ by
        rw [Unique.eq_default i, Sl2Std.lie_raise_lower, sl2CartanHom_coroot R lam n hA, hlam,
          sub_self, zero_smul, zero_add]
      lie_positive_negative_of_ne := fun i j hij ↦ absurd (Subsingleton.elim i j) hij
      serre_positive := fun _ _ ↦ by rw [lie_self, map_zero]
      serre_negative := fun _ _ ↦ by rw [lie_self, map_zero] :
        SatisfiesRelations R (sl2CartanHom R lam n) (fun _ ↦ Sl2Std.raise K n)
          (fun _ ↦ Sl2Std.lower K n) }

/-- The `Enveloping R`-algebra representation defining the module action on
`RankOneModule R hA lam n hlam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (RankOneModule R hA lam n hlam) :=
  ((equiv R hA lam n hlam).symm.conjAlgEquiv K).toAlgHom.comp (sl2Rep R lam n hA hlam)

noncomputable instance : Module (Enveloping R) (RankOneModule R hA lam n hlam) :=
  Module.compHom (RankOneModule R hA lam n hlam) (rep R hA lam n hlam).toRingHom

/-- Scalar multiplication on `RankOneModule` is evaluation of `rep`. -/
theorem smul_def (u : Enveloping R) (v : RankOneModule R hA lam n hlam) :
    u • v = rep R hA lam n hlam u v := (rfl)

/-- Evaluating `rep` gives the `Enveloping R`-module scalar multiplication on `RankOneModule`. -/
@[simp]
theorem rep_apply (u : Enveloping R) (v : RankOneModule R hA lam n hlam) :
    rep R hA lam n hlam u v = u • v := (rfl)

instance : IsScalarTower K (Enveloping R) (RankOneModule R hA lam n hlam) where
  smul_assoc c u v := by
    rw [smul_def, smul_def, AlgHom.map_smul_of_tower, LinearMap.smul_apply]

theorem positiveAction_eq (i : I) :
    positiveAction R (RankOneModule R hA lam n hlam) i =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.raise K n) := by
  ext v
  rw [positiveAction_apply, smul_def]
  simp [rep, sl2Rep]

theorem negativeAction_eq (i : I) :
    negativeAction R (RankOneModule R hA lam n hlam) i =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.lower K n) := by
  ext v
  rw [negativeAction_apply, smul_def]
  simp [rep, sl2Rep]

/-- The Cartan action of an arbitrary `x : H` on `RankOneModule R hA lam n hlam`. -/
theorem cartanAction_eq (x : H) :
    cartanAction R (RankOneModule R hA lam n hlam) x =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K
        ((lam x - (n : K) * 2⁻¹ * R.root default x) • (1 : Module.End K (Sl2Std K n)) +
          (2⁻¹ * R.root default x) • Sl2Std.diag K n) := by
  ext v
  rw [cartanAction_apply, smul_def]
  simp [rep, sl2Rep, sl2CartanHom]

theorem cartanAction_coroot (i : I) :
    cartanAction R (RankOneModule R hA lam n hlam) (R.coroot i) =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.diag K n) := by
  rw [Unique.eq_default i, cartanAction_eq]
  congr 1
  have hrc := root_coroot_eq_two (R := R) hA
  rw [hrc, hlam, mul_assoc (n : K) 2⁻¹ 2, inv_mul_cancel₀ two_ne_zero, mul_one, sub_self,
    zero_smul, zero_add, one_smul]

@[simp]
theorem equiv_positiveAction_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (positiveAction R (RankOneModule R hA lam n hlam) i v) =
      Sl2Std.raise K n (equiv R hA lam n hlam v) := by
  rw [positiveAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

@[simp]
theorem equiv_negativeAction_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (negativeAction R (RankOneModule R hA lam n hlam) i v) =
      Sl2Std.lower K n (equiv R hA lam n hlam v) := by
  rw [negativeAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Pointwise evaluation of the Cartan action of an arbitrary `x : H` under `equiv`. -/
theorem equiv_cartanAction_apply (x : H) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) x v) =
      (lam x - (n : K) * 2⁻¹ * R.root default x) • equiv R hA lam n hlam v +
        (2⁻¹ * R.root default x) • Sl2Std.diag K n (equiv R hA lam n hlam v) := by
  rw [cartanAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

@[simp]
theorem equiv_cartanAction_coroot_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) (R.coroot i) v) =
      Sl2Std.diag K n (equiv R hA lam n hlam v) := by
  rw [cartanAction_coroot]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Coordinate basis vector `vₖ` has weight `lam - k • αᵢ`. -/
theorem basis_mem_weightSpace (i : I) (k : Fin (n + 1)) :
    basis R hA lam n hlam k ∈
      weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i) := by
  rw [Unique.eq_default i, mem_weightSpace_iff]
  intro x
  apply (equiv R hA lam n hlam).injective
  rw [equiv_cartanAction_apply, map_smul, equiv_basis, Sl2Std.diag_basis]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_smul, ← add_smul, nsmul_eq_mul]
  congr 1
  have h2 : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  linear_combination ((n : K) * R.root default x - 2 * (k : K) * R.root default x) * h2

omit [CharZero K] in
private theorem iSup_span_basis_eq_top :
    (⨆ k : Fin (n + 1), K ∙ basis R hA lam n hlam k) = ⊤ := by
  rw [← Submodule.span_iUnion, Set.iUnion_singleton_eq_range, (basis R hA lam n hlam).span_eq]

include hA in
private theorem sub_nsmul_root_injective (i : I) :
    Function.Injective (fun k : Fin (n + 1) ↦ lam - (k : ℕ) • R.root i) := by
  rw [Unique.eq_default i]
  intro k₁ k₂ hk
  have hsub : (k₁ : ℕ) • R.root default = (k₂ : ℕ) • R.root default := sub_right_inj.mp hk
  have hev := congrArg (fun φ : Dual K H ↦ φ (R.coroot default)) hsub
  simp only [LinearMap.smul_apply, root_coroot_eq_two (R := R) hA, nsmul_eq_mul] at hev
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ (two_ne_zero (α := K)) hev))

/-- Each weight space `lam - k • αᵢ` of `RankOneModule` is the line spanned by `basis k`. -/
theorem weightSpace_sub_nsmul_root (i : I) (k : Fin (n + 1)) :
    weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i) =
      K ∙ basis R hA lam n hlam k :=
  weightSpace_eq_of_iSup_eq_top R (RankOneModule R hA lam n hlam)
    (W := fun j : Fin (n + 1) ↦ K ∙ basis R hA lam n hlam j)
    (w := fun j : Fin (n + 1) ↦ lam - (j : ℕ) • R.root i)
    (fun j ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr
      (basis_mem_weightSpace R hA lam n hlam i j))
    (iSup_span_basis_eq_top R hA lam n hlam) (sub_nsmul_root_injective R hA lam n i) k

/-- Every weight space `lam - k • αᵢ` of `RankOneModule` is one-dimensional. -/
@[simp]
theorem finrank_weightSpace_sub_nsmul_root (i : I) (k : Fin (n + 1)) :
    Module.finrank K
        (weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i)) = 1 := by
  rw [weightSpace_sub_nsmul_root]
  exact finrank_span_singleton ((basis R hA lam n hlam).ne_zero k)

theorem weightSpace_eq_bot_of_forall_ne {i : I} {μ : Dual K H}
    (hμ : ∀ k : Fin (n + 1), μ ≠ lam - (k : ℕ) • R.root i) :
    weightSpace R (RankOneModule R hA lam n hlam) μ = ⊥ :=
  weightSpace_eq_bot_of_iSup_eq_top R (RankOneModule R hA lam n hlam)
    (W := fun j : Fin (n + 1) ↦ K ∙ basis R hA lam n hlam j)
    (w := fun j : Fin (n + 1) ↦ lam - (j : ℕ) • R.root i)
    (fun j ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr
      (basis_mem_weightSpace R hA lam n hlam i j))
    (iSup_span_basis_eq_top R hA lam n hlam) fun ⟨k, hk⟩ ↦ hμ k hk.symm

/-- **`RankOneModule R hA lam n hlam` is a simple `Enveloping R`-module.** -/
instance isSimpleModule :
    IsSimpleModule (Enveloping R) (RankOneModule R hA lam n hlam) where
  eq_bot_or_eq_top P := by
    by_cases hP : P = ⊥
    · exact Or.inl hP
    · refine Or.inr (Submodule.eq_top_iff'.mpr fun v ↦ ?_)
      let e := equiv R hA lam n hlam
      set Q : Submodule K (Sl2Std K n) := (P.restrictScalars K).map e.toLinearMap
      have hQ_ne : Q ≠ ⊥ := by
        obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hP
        exact (Submodule.ne_bot_iff Q).mpr
          ⟨e x, Submodule.mem_map_of_mem hxP, (map_ne_zero_iff e e.injective).mpr hx0⟩
      have hQ_top : Q = ⊤ := Sl2Std.eq_top_of_raise_mem_of_lower_mem Q hQ_ne
        (fun _ hw ↦ by
          rcases hw with ⟨x, hx, rfl⟩
          exact ⟨positiveAction R _ default x,
            by rw [positiveAction_apply]; exact P.smul_mem _ hx, equiv_positiveAction_apply ..⟩)
        (fun _ hw ↦ by
          rcases hw with ⟨x, hx, rfl⟩
          exact ⟨negativeAction R _ default x,
            by rw [negativeAction_apply]; exact P.smul_mem _ hx, equiv_negativeAction_apply ..⟩)
      have hvQ : e v ∈ Q := hQ_top ▸ Submodule.mem_top
      obtain ⟨x, hxP, hxe⟩ := hvQ
      exact e.injective hxe ▸ hxP

/-- **`RankOneModule R hA lam n hlam` lies in `IsIntegrableO R`.** -/
theorem isIntegrableO : IsIntegrableO R (RankOneModule R hA lam n hlam) where
  isWeightModule := by
    rw [isWeightModule_iff, ← top_le_iff, ← (basis R hA lam n hlam).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact le_iSup (weightSpace R (RankOneModule R hA lam n hlam))
      (lam - (k : ℕ) • R.root default) (basis_mem_weightSpace R hA lam n hlam default k)
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hle
    refine hμ (weightSpace_eq_bot_of_forall_ne R hA lam n hlam (i := default) fun k hk ↦ hle ?_)
    rw [hk, CartanRealization.rootLE_iff, sub_sub_cancel]
    exact nsmul_mem (R.root_mem_posRootCone default) k⟩⟩
  locallyNilpotent_positiveAction i v := ⟨n + 1, by
    rw [positiveAction_eq, ← map_pow, Sl2Std.raise_pow_eq_zero, map_zero, LinearMap.zero_apply]⟩
  locallyNilpotent_negativeAction i v := ⟨n + 1, by
    rw [negativeAction_eq, ← map_pow, Sl2Std.lower_pow_eq_zero, map_zero, LinearMap.zero_apply]⟩

/-- On `RankOneModule R hA lam n hlam`, `simpleWeylIntertwiner` corresponds under `equiv` to
`TauCeti.Sl2Std.weylUnit K n`. -/
@[simp]
theorem equiv_simpleWeylIntertwiner_apply {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (simpleWeylIntertwiner he hf v) =
      (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) (equiv R hA lam n hlam v) := by
  let φ := (equiv R hA lam n hlam).symm.conjAlgEquiv K
  have hpos_nil : IsNilpotent (positiveAction R (RankOneModule R hA lam n hlam) i) :=
    ⟨n + 1, by rw [positiveAction_eq, ← map_pow, Sl2Std.raise_pow_eq_zero, map_zero]⟩
  have hneg_nil : IsNilpotent (-negativeAction R (RankOneModule R hA lam n hlam) i) :=
    ⟨n + 1, by
      rw [negativeAction_eq, ← map_neg, ← map_pow, neg_pow, Sl2Std.lower_pow_eq_zero, mul_zero,
        map_zero]⟩
  have hep : (Module.End.locallyNilpotentExp
      (positiveAction R (RankOneModule R hA lam n hlam) i) he).toLinearMap =
      φ (IsNilpotent.exp (Sl2Std.raise K n)) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ hpos_nil, positiveAction_eq,
      IsNilpotent.map_exp Sl2Std.isNilpotent_raise φ]
  have hfn : (Module.End.locallyNilpotentExp
      (-negativeAction R (RankOneModule R hA lam n hlam) i)
      (fun x ↦ by
        simpa [Module.End.neg_pow_apply_eq_zero_iff] using hf x)).toLinearMap =
      φ (IsNilpotent.exp (-(Sl2Std.lower K n))) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ hneg_nil, negativeAction_eq, ← map_neg,
      IsNilpotent.map_exp Sl2Std.isNilpotent_lower.neg φ]
  have hweyl : (simpleWeylIntertwiner he hf).toLinearMap =
      φ (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) := by
    ext x
    rw [LinearEquiv.coe_coe, simpleWeylIntertwiner_apply, Sl2Std.coe_weylUnit, map_mul, map_mul,
      _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp, ← LinearEquiv.coe_toLinearMap, hep,
      ← LinearEquiv.coe_toLinearMap, hfn]
  have hv := congrArg (fun g : Module.End K (RankOneModule R hA lam n hlam) ↦
    equiv R hA lam n hlam (g v)) hweyl
  simpa [φ, LinearEquiv.conjAlgEquiv_apply] using hv

/-- On the coordinate basis of `RankOneModule`, `simpleWeylIntertwiner` reverses the basis with
signs `(-1) ^ (n - k)`. -/
@[simp]
theorem simpleWeylIntertwiner_basis {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (k : Fin (n + 1)) :
    simpleWeylIntertwiner he hf (basis R hA lam n hlam k) =
      ((-1 : K) ^ (n - (k : ℕ))) • basis R hA lam n hlam k.rev := by
  apply (equiv R hA lam n hlam).injective
  rw [equiv_simpleWeylIntertwiner_apply, equiv_basis, map_smul, equiv_basis,
    Sl2Std.weylUnit_apply_basis]

/-- **Squaring `simpleWeylIntertwiner` on `RankOneModule`.** Two applications of the simple Weyl
intertwiner multiply every vector of `RankOneModule R hA lam n hlam` by `(-1) ^ n` (so on `n = 1`
it acts as `-1`, not `+1`, whereas on `n = 2` it acts as `+1`). -/
@[simp]
theorem simpleWeylIntertwiner_simpleWeylIntertwiner_apply {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (v : RankOneModule R hA lam n hlam) :
    simpleWeylIntertwiner he hf (simpleWeylIntertwiner he hf v) = (-1 : K) ^ n • v := by
  apply (equiv R hA lam n hlam).injective
  rw [equiv_simpleWeylIntertwiner_apply, equiv_simpleWeylIntertwiner_apply, map_smul,
    Sl2Std.weylUnit_weylUnit_apply]

end CharZero

end RankOneModule

end RankOneModule

end KacMoody

end TauCeti
