/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Lie.KacMoody.WeightModule
public import TauCeti.Algebra.Lie.Sl2.Weyl.Standard
public import TauCeti.LinearAlgebra.End.Exp
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.Algebra.Lie.Submodule.LocallyFinite
import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Integrable modules over Kac–Moody Lie algebras and the simple Weyl intertwiners

An `Enveloping R`-module `M` over `TauCeti.KacMoody.PresentedLieAlgebra R` is **integrable**
(`TauCeti.KacMoody.IsIntegrable R M`) when it is a weight module on which every Chevalley generator
`eᵢ` and `fᵢ` acts locally nilpotently. Together with Kac's category `O` this forms the subcategory
`TauCeti.KacMoody.IsIntegrableO R M` of integrable highest-weight modules.

Four structural mechanisms govern integrable Kac–Moody representations:

1. **Adjoint local nilpotence of Chevalley generators.** On `PresentedLieAlgebra R` itself, the
   Engel subalgebras of `positiveGenerator R i` and `negativeGenerator R i` equal `⊤` without any
   Generalized Cartan Matrix hypothesis or decidable equality on `I`: `(ad eᵢ)²` kills every Cartan
   element, `(ad eᵢ) ^ ((-A i j).toNat + 1)` kills `eⱼ` by Serre's relation, `(ad eᵢ)³` kills `fᵢ`,
   and `ad eᵢ` kills `fⱼ` for `j ≠ i`. Consequently, the vectors of any `Enveloping R`-module `M`
   annihilated by a power of `positiveAction R M i` (or `negativeAction R M i`) form an
   `Enveloping R`-submodule, so local nilpotence spreads from any `Enveloping R`-generating set to
   all of `M`.
2. **Integrality of primitive weights.** At any node `i` with `A i i = 2` in characteristic zero, a
   nonzero weight vector annihilated by `eᵢ` and by a power of `fᵢ` pairs with `R.coroot i` by a
   natural number `n : ℕ`. Thus every nonzero submodule of a module in `IsIntegrableO` (when
   `∀ i, A i i = 2`) contains a nonzero primitive vector whose weight takes natural-number values on
   all simple coroots.
3. **The simple Weyl intertwiners.** Over a field of characteristic zero, the locally nilpotent
   operators `eᵢ` and `-fᵢ` on an integrable module `M` exponentiate via
   `Module.End.locallyNilpotentExp` to the `K`-linear automorphism
   `sᵢ = exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ)` (`TauCeti.KacMoody.simpleWeylIntertwiner`). When
   `A i i = 2`, conjugation by `sᵢ` reflects the Cartan action according to
   `x ↦ x - αᵢ(x) • hᵢ` and restricts to a `K`-linear equivalence
   `M_μ ≃ₗ[K] M_{μ - μ(hᵢ) • αᵢ}`, forcing Weyl-invariance of weight multiplicities.
4. **Concrete simple integrable models.** When `I` is empty, `TauCeti.KacMoody.OneDimModule R lam`
   realizes the one-dimensional simple `IsIntegrableO` module of weight `lam`. For rank one
   (`I = Unit`, `A () () = 2`), `TauCeti.KacMoody.RankOneModule R hA lam n hlam` equips
   `TauCeti.Sl2Std K n` with an `Enveloping R`-action for any realization `H` and any weight `lam`
   with `lam (R.coroot ()) = n`, giving an `(n + 1)`-dimensional simple `IsIntegrableO` module on
   which `simpleWeylIntertwiner` agrees with `TauCeti.Sl2Std.weylUnit` and squares to `(-1) ^ n`.

## Main definitions

* `TauCeti.KacMoody.locallyNilpotentPositiveSubmodule`,
  `TauCeti.KacMoody.locallyNilpotentNegativeSubmodule`: the `Enveloping R`-submodules of vectors
  annihilated by a power of `positiveAction R M i` or `negativeAction R M i`.
* `TauCeti.KacMoody.IsIntegrable`: integrable `Enveloping R`-modules.
* `TauCeti.KacMoody.IsIntegrableO`: integrable modules in Kac's category `O`.
* `TauCeti.KacMoody.simpleWeylIntertwiner`: the simple reflection operator
  `exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ) : M ≃ₗ[K] M` on an integrable module in characteristic zero.
* `TauCeti.KacMoody.simpleWeylIntertwinerWeightEquiv`: the induced `K`-linear equivalence
  `weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i)`.
* `TauCeti.KacMoody.OneDimModule` (with `OneDimModule.equiv` and `OneDimModule.rep`): the
  one-dimensional simple `IsIntegrableO` module for `[IsEmpty I]`.
* `TauCeti.KacMoody.RankOneModule` (with `RankOneModule.equiv`, `RankOneModule.basis`, and
  `RankOneModule.rep`): the `(n + 1)`-dimensional simple `IsIntegrableO` module for rank one
  (`I = Unit`, `A () () = 2`).

## Main results

* `TauCeti.KacMoody.engel_positiveGenerator` and `TauCeti.KacMoody.engel_negativeGenerator`: the
  Engel subalgebras of `positiveGenerator R i` and `negativeGenerator R i` are `⊤`.
* `TauCeti.KacMoody.exists_positiveAction_pow_eq_zero_of_span_eq_top`,
  `TauCeti.KacMoody.exists_negativeAction_pow_eq_zero_of_span_eq_top`, and
  `TauCeti.KacMoody.IsIntegrable.of_span_eq_top`: local nilpotence of `eᵢ` and `fᵢ` spreads from
  any `Enveloping R`-generating set to the whole module.
* `TauCeti.KacMoody.IsIntegrable.submodule`, `TauCeti.KacMoody.IsIntegrable.quotient`,
  `TauCeti.KacMoody.IsIntegrable.prod`, `TauCeti.KacMoody.IsIntegrable.directSum`, and the
  corresponding closure theorems for `TauCeti.KacMoody.IsIntegrableO`.
* `TauCeti.KacMoody.exists_nat_coroot_of_positiveAction_eq_zero` and
  `TauCeti.KacMoody.IsIntegrableO.exists_primitive_vector_of_ne_bot`: integrality of primitive
  weights and existence of dominant integral primitive vectors in nonzero submodules in
  characteristic zero.
* `TauCeti.KacMoody.cartanAction_simpleWeylIntertwiner_apply`,
  `TauCeti.KacMoody.simpleWeylIntertwiner_mem_weightSpace`, and
  `TauCeti.KacMoody.finrank_weightSpace_reflect`: simple Weyl intertwiners reflect the Cartan
  action and preserve weight multiplicities.
* `TauCeti.KacMoody.OneDimModule.isSimpleModule`, `TauCeti.KacMoody.OneDimModule.isIntegrableO`,
  `TauCeti.KacMoody.RankOneModule.isSimpleModule`, `TauCeti.KacMoody.RankOneModule.isIntegrableO`,
  `TauCeti.KacMoody.RankOneModule.equiv_simpleWeylIntertwiner_apply`, and
  `TauCeti.KacMoody.RankOneModule.simpleWeylIntertwiner_simpleWeylIntertwiner_apply`: simplicity,
  integrability, and the Weyl square `(-1) ^ n` on the rank-zero and rank-one models.

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

/-! ### Adjoint local nilpotence of the Chevalley generators -/

section AdjointNilpotence

private theorem ad_positiveGenerator_sq_cartanElement
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) (x : H) :
    (ad K (PresentedLieAlgebra R) (positiveGenerator R i) ^ 2) (cartanElement R x) = 0 := by
  rw [sq, _root_.mul_apply_eq_comp, ad_apply, ad_apply,
    ← lie_skew (positiveGenerator R i) (cartanElement R x), lie_cartanElement_positiveGenerator,
    lie_neg, lie_smul, lie_self, smul_zero, neg_zero]

private theorem ad_negativeGenerator_sq_cartanElement
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) (x : H) :
    (ad K (PresentedLieAlgebra R) (negativeGenerator R i) ^ 2) (cartanElement R x) = 0 := by
  rw [sq, _root_.mul_apply_eq_comp, ad_apply, ad_apply,
    ← lie_skew (negativeGenerator R i) (cartanElement R x), lie_cartanElement_negativeGenerator,
    neg_neg, lie_smul, lie_self, smul_zero]

/-- **Adjoint local nilpotence of `eᵢ`.** The Engel subalgebra of `positiveGenerator R i` is the
whole Kac–Moody algebra `PresentedLieAlgebra R`, with no hypotheses on the integer matrix `A` or on
`I`. -/
@[simp]
theorem engel_positiveGenerator (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) :
    LieSubalgebra.engel K (positiveGenerator R i) = ⊤ := by
  classical
  rw [eq_top_iff, ← lieSpan_generators_eq_top R, LieSubalgebra.lieSpan_le]
  rintro _ ((⟨x, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;>
    rw [SetLike.mem_coe, LieSubalgebra.mem_engel_iff]
  · exact ⟨2, ad_positiveGenerator_sq_cartanElement R i x⟩
  · refine ⟨(-A i j).toNat + 1, ?_⟩
    rw [pow_succ, _root_.mul_apply_eq_comp, ad_apply]
    exact ad_pow_lie_positiveGenerator_positiveGenerator R i j
  · by_cases hij : i = j
    · subst hij
      refine ⟨2 + 1, ?_⟩
      rw [pow_succ, _root_.mul_apply_eq_comp, ad_apply,
        lie_positiveGenerator_negativeGenerator_self]
      exact ad_positiveGenerator_sq_cartanElement R i (R.coroot i)
    · refine ⟨1, ?_⟩
      rw [pow_one, ad_apply, lie_positiveGenerator_negativeGenerator_of_ne R hij]

/-- **Adjoint local nilpotence of `fᵢ`.** The Engel subalgebra of `negativeGenerator R i` is the
whole Kac–Moody algebra `PresentedLieAlgebra R`, with no hypotheses on `A` or `I`. -/
@[simp]
theorem engel_negativeGenerator (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) :
    LieSubalgebra.engel K (negativeGenerator R i) = ⊤ := by
  classical
  rw [eq_top_iff, ← lieSpan_generators_eq_top R, LieSubalgebra.lieSpan_le]
  rintro _ ((⟨x, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) <;>
    rw [SetLike.mem_coe, LieSubalgebra.mem_engel_iff]
  · exact ⟨2, ad_negativeGenerator_sq_cartanElement R i x⟩
  · by_cases hij : i = j
    · subst hij
      refine ⟨2 + 1, ?_⟩
      rw [pow_succ, _root_.mul_apply_eq_comp, ad_apply,
        ← lie_skew (negativeGenerator R i) (positiveGenerator R i),
        lie_positiveGenerator_negativeGenerator_self, map_neg,
        ad_negativeGenerator_sq_cartanElement, neg_zero]
    · refine ⟨1, ?_⟩
      rw [pow_one, ad_apply, ← lie_skew (negativeGenerator R i) (positiveGenerator R j),
        lie_positiveGenerator_negativeGenerator_of_ne R (Ne.symm hij), neg_zero]
  · refine ⟨(-A i j).toNat + 1, ?_⟩
    rw [pow_succ, _root_.mul_apply_eq_comp, ad_apply]
    exact ad_pow_lie_negativeGenerator_negativeGenerator R i j

theorem exists_ad_pow_positiveGenerator_eq_zero
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) (y : PresentedLieAlgebra R) :
    ∃ k : ℕ, (ad K (PresentedLieAlgebra R) (positiveGenerator R i) ^ k) y = 0 :=
  (LieSubalgebra.mem_engel_iff K (positiveGenerator R i) y).mp
    (by rw [engel_positiveGenerator]; trivial)

theorem exists_ad_pow_negativeGenerator_eq_zero
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (i : I) (y : PresentedLieAlgebra R) :
    ∃ k : ℕ, (ad K (PresentedLieAlgebra R) (negativeGenerator R i) ^ k) y = 0 :=
  (LieSubalgebra.mem_engel_iff K (negativeGenerator R i) y).mp
    (by rw [engel_negativeGenerator]; trivial)

end AdjointNilpotence

/-! ### Spreading local nilpotence across an `Enveloping R`-module -/

section LocallyNilpotentSubmodule

/-- The vectors of `M` annihilated by some power of `positiveAction R M i`, packaged as an
`Enveloping R`-submodule via adjoint local nilpotence of `positiveGenerator R i`. -/
noncomputable def locallyNilpotentPositiveSubmodule
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Submodule (Enveloping R) M :=
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  TauCeti.UniversalEnvelopingAlgebra.lieSubmoduleOrderIso
    (fun x m ↦
      (TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K
        (PresentedLieAlgebra R) M x m).symm)
    (TauCeti.locallyNilpotentSubmodule K M (positiveGenerator R i)
      (exists_ad_pow_positiveGenerator_eq_zero R i))

/-- The vectors of `M` annihilated by some power of `negativeAction R M i`, packaged as an
`Enveloping R`-submodule via adjoint local nilpotence of `negativeGenerator R i`. -/
noncomputable def locallyNilpotentNegativeSubmodule
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Submodule (Enveloping R) M :=
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  letI := TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  TauCeti.UniversalEnvelopingAlgebra.lieSubmoduleOrderIso
    (fun x m ↦
      (TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K
        (PresentedLieAlgebra R) M x m).symm)
    (TauCeti.locallyNilpotentSubmodule K M (negativeGenerator R i)
      (exists_ad_pow_negativeGenerator_eq_zero R i))

variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

@[simp]
theorem mem_locallyNilpotentPositiveSubmodule {i : I} {m : M} :
    m ∈ locallyNilpotentPositiveSubmodule R M i ↔
      ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  let : LieRingModule (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  let : LieModule K (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  have hEnd : LieModule.toEnd K (PresentedLieAlgebra R) M (positiveGenerator R i) =
      positiveAction R M i := LinearMap.ext fun v ↦ by
    rw [LieModule.toEnd_apply_apply,
      TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K (PresentedLieAlgebra R) M,
      positiveAction_apply]
  simp [locallyNilpotentPositiveSubmodule, hEnd]

@[simp]
theorem mem_locallyNilpotentNegativeSubmodule {i : I} {m : M} :
    m ∈ locallyNilpotentNegativeSubmodule R M i ↔
      ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  let : LieRingModule (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieRingModule K (PresentedLieAlgebra R) M
  let : LieModule K (PresentedLieAlgebra R) M :=
    TauCeti.UniversalEnvelopingAlgebra.asLieModule K (PresentedLieAlgebra R) M
  have hEnd : LieModule.toEnd K (PresentedLieAlgebra R) M (negativeGenerator R i) =
      negativeAction R M i := LinearMap.ext fun v ↦ by
    rw [LieModule.toEnd_apply_apply,
      TauCeti.UniversalEnvelopingAlgebra.asLieRingModule_bracket K (PresentedLieAlgebra R) M,
      negativeAction_apply]
  simp [locallyNilpotentNegativeSubmodule, hEnd]

/-- **Local nilpotence of `eᵢ` spreads from any `Enveloping R`-generating set.** -/
theorem exists_positiveAction_pow_eq_zero_of_span_eq_top {S : Set M}
    (hS : Submodule.span (Enveloping R) S = ⊤) {i : I}
    (hnil : ∀ v ∈ S, ∃ k : ℕ, (positiveAction R M i ^ k) v = 0) (m : M) :
    ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  have htop : locallyNilpotentPositiveSubmodule R M i = ⊤ := by
    rw [← top_le_iff, ← hS, Submodule.span_le]
    exact fun v hv ↦ mem_locallyNilpotentPositiveSubmodule.mpr (hnil v hv)
  exact mem_locallyNilpotentPositiveSubmodule.mp (htop ▸ Submodule.mem_top)

/-- **Local nilpotence of `fᵢ` spreads from any `Enveloping R`-generating set.** -/
theorem exists_negativeAction_pow_eq_zero_of_span_eq_top {S : Set M}
    (hS : Submodule.span (Enveloping R) S = ⊤) {i : I}
    (hnil : ∀ v ∈ S, ∃ k : ℕ, (negativeAction R M i ^ k) v = 0) (m : M) :
    ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  have htop : locallyNilpotentNegativeSubmodule R M i = ⊤ := by
    rw [← top_le_iff, ← hS, Submodule.span_le]
    exact fun v hv ↦ mem_locallyNilpotentNegativeSubmodule.mpr (hnil v hv)
  exact mem_locallyNilpotentNegativeSubmodule.mp (htop ▸ Submodule.mem_top)

/-- On a simple `Enveloping R`-module, if `eᵢ` acts nilpotently at one nonzero vector then it acts
locally nilpotently on the whole module. -/
theorem exists_positiveAction_pow_eq_zero_of_isSimpleModule [IsSimpleModule (Enveloping R) M]
    {i : I} {v : M} (hv : v ≠ 0) {k₀ : ℕ} (hk₀ : (positiveAction R M i ^ k₀) v = 0) (m : M) :
    ∃ k : ℕ, (positiveAction R M i ^ k) m = 0 := by
  have hne : Submodule.span (Enveloping R) ({v} : Set M) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.subset_span rfl, hv⟩
  exact exists_positiveAction_pow_eq_zero_of_span_eq_top
    ((eq_bot_or_eq_top _).resolve_left hne)
    (fun w hw ↦ by rcases Set.mem_singleton_iff.mp hw with rfl; exact ⟨k₀, hk₀⟩) m

/-- On a simple `Enveloping R`-module, if `fᵢ` acts nilpotently at one nonzero vector then it acts
locally nilpotently on the whole module. -/
theorem exists_negativeAction_pow_eq_zero_of_isSimpleModule [IsSimpleModule (Enveloping R) M]
    {i : I} {v : M} (hv : v ≠ 0) {k₀ : ℕ} (hk₀ : (negativeAction R M i ^ k₀) v = 0) (m : M) :
    ∃ k : ℕ, (negativeAction R M i ^ k) m = 0 := by
  have hne : Submodule.span (Enveloping R) ({v} : Set M) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.subset_span rfl, hv⟩
  exact exists_negativeAction_pow_eq_zero_of_span_eq_top
    ((eq_bot_or_eq_top _).resolve_left hne)
    (fun w hw ↦ by rcases Set.mem_singleton_iff.mp hw with rfl; exact ⟨k₀, hk₀⟩) m

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

private theorem map_positiveAction_pow (f : M →ₗ[Enveloping R] N) (i : I) (k : ℕ) (m : M) :
    f ((positiveAction R M i ^ k) m) = (positiveAction R N i ^ k) (f m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', _root_.mul_apply_eq_comp, map_positiveAction, ih,
      ← _root_.mul_apply_eq_comp, ← pow_succ']

private theorem map_negativeAction_pow (f : M →ₗ[Enveloping R] N) (i : I) (k : ℕ) (m : M) :
    f ((negativeAction R M i ^ k) m) = (negativeAction R N i ^ k) (f m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', _root_.mul_apply_eq_comp, map_negativeAction, ih,
      ← _root_.mul_apply_eq_comp, ← pow_succ']

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
    obtain ⟨k₁, hk₁⟩ := hM.locallyNilpotent_positiveAction i x.1
    obtain ⟨k₂, hk₂⟩ := hN.locallyNilpotent_positiveAction i x.2
    refine ⟨max k₁ k₂, Prod.ext ?_ ?_⟩
    · have h1 := map_positiveAction_pow (LinearMap.fst (Enveloping R) M N) i (max k₁ k₂) x
      exact h1.trans (Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁)
    · have h2 := map_positiveAction_pow (LinearMap.snd (Enveloping R) M N) i (max k₁ k₂) x
      exact h2.trans (Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂)
  locallyNilpotent_negativeAction i x := by
    obtain ⟨k₁, hk₁⟩ := hM.locallyNilpotent_negativeAction i x.1
    obtain ⟨k₂, hk₂⟩ := hN.locallyNilpotent_negativeAction i x.2
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
      refine ⟨k, ?_⟩
      change (positiveAction R (⨁ j, P j) i ^ k) (DirectSum.lof (Enveloping R) κ P j m) = 0
      rw [← map_positiveAction_pow, hk, map_zero]
    · refine ⟨max kx ky, ?_⟩
      rw [map_add, Module.End.pow_map_zero_of_le (le_max_left kx ky) hkx,
        Module.End.pow_map_zero_of_le (le_max_right kx ky) hky, add_zero]
  locallyNilpotent_negativeAction i v := by
    classical
    refine DirectSum.induction_on v ⟨0, map_zero _⟩ (fun j m ↦ ?_) fun x y ⟨kx, hkx⟩ ⟨ky, hky⟩ ↦ ?_
    · obtain ⟨k, hk⟩ := (hP j).locallyNilpotent_negativeAction i m
      refine ⟨k, ?_⟩
      change (negativeAction R (⨁ j, P j) i ^ k) (DirectSum.lof (Enveloping R) κ P j m) = 0
      rw [← map_negativeAction_pow, hk, map_zero]
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
  have hrc := root_coroot_eq_two (R := R) hA
  induction k with
  | zero =>
    simp [positiveAction_negativeAction_self_apply, cartanAction_apply_of_mem_weightSpace hv]
  | succ k ih =>
    have hw : (negativeAction R M i ^ (k + 1)) v ∈ weightSpace R M (μ - (k + 1) • R.root i) :=
      negativeAction_pow_mem_weightSpace hv i (k + 1)
    have hf2 : negativeAction R M i ((negativeAction R M i ^ k) v) =
        (negativeAction R M i ^ (k + 1)) v := by
      rw [pow_succ' (negativeAction R M i) k, _root_.mul_apply_eq_comp]
    have hscalar :
        ((k + 1 : ℕ) : K) * (μ (R.coroot i) - k) + (μ (R.coroot i) - (k + 1 : ℕ) * 2) =
          ((k + 1 + 1 : ℕ) : K) * (μ (R.coroot i) - (k + 1 : ℕ)) := by
      push_cast
      ring
    rw [pow_succ' (negativeAction R M i) (k + 1), _root_.mul_apply_eq_comp,
      _root_.mul_apply_eq_comp, positiveAction_negativeAction_self_apply, ih, map_add, map_smul,
      hf2, cartanAction_apply_of_mem_weightSpace hw, LinearMap.sub_apply, LinearMap.smul_apply,
      nsmul_eq_mul, hrc, add_assoc, ← add_smul, hscalar]

/-- **Integrality of a primitive weight at node `i`.** Over a field of characteristic zero, if
`A i i = 2` and `v` is a nonzero weight vector of weight `μ` killed by `eᵢ` and by some power of
`fᵢ`, then `μ (R.coroot i)` is a natural number `n : ℕ` (and `(fᵢ ^ (n + 1)) v = 0`). -/
theorem exists_nat_coroot_of_positiveAction_eq_zero [CharZero K] {i : I} (hA : A i i = 2)
    {μ : Dual K H} {v : M} (hv0 : v ≠ 0) (hv : v ∈ weightSpace R M μ)
    (he : positiveAction R M i v = 0) (hnil : ∃ k : ℕ, (negativeAction R M i ^ k) v = 0) :
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
  obtain ⟨n, hn, -⟩ := exists_nat_coroot_of_positiveAction_eq_zero (hA i) hv0 hvw (hprim i)
    (hM.locallyNilpotent_negativeAction i v)
  exact ⟨n, hn⟩

/-- Over a linearly ordered field of characteristic zero, the primitive weight produced by
`IsIntegrableO.exists_primitive_vector_of_ne_bot` is dominant (`CartanRealization.IsDominant`). -/
theorem isDominant_of_forall_exists_nat_coroot [LinearOrder K] [IsStrictOrderedRing K]
    {μ : Dual K H} (h : ∀ i : I, ∃ n : ℕ, μ (R.coroot i) = n) : R.IsDominant μ :=
  CartanRealization.isDominant_iff.mpr fun i ↦ by
    obtain ⟨n, hn⟩ := h i
    rw [hn]
    exact Nat.cast_nonneg n

end PrimitiveIntegrality

/-! ### The simple Weyl intertwiners -/

section SimpleWeylIntertwiner

variable [CharZero K]
variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- Kac's **simple Weyl intertwiner** `rᵢ^M = exp(eᵢ) ∘ exp(-fᵢ) ∘ exp(eᵢ) : M ≃ₗ[K] M` (§3.8) on
an integrable module `M` over a field of characteristic zero. -/
noncomputable def simpleWeylIntertwiner (hM : IsIntegrable R M) (i : I) : M ≃ₗ[K] M :=
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  (Module.End.locallyNilpotentExp (positiveAction R M i)
      (hM.locallyNilpotent_positiveAction i)).trans
    (((Module.End.locallyNilpotentExp (-negativeAction R M i)
        (fun m ↦ by
          simpa [Module.End.neg_pow_apply_eq_zero_iff] using
            hM.locallyNilpotent_negativeAction i m)).trans
      (Module.End.locallyNilpotentExp (positiveAction R M i)
        (hM.locallyNilpotent_positiveAction i))))

/-- On any `ℚ`-module structure on `M` (which is unique by `subsingleton_rat_module`),
`simpleWeylIntertwiner` acts as the threefold composite of `Module.End.locallyNilpotentExp`. -/
theorem simpleWeylIntertwiner_apply [Module ℚ M] (hM : IsIntegrable R M) (i : I) (m : M) :
    simpleWeylIntertwiner hM i m =
      Module.End.locallyNilpotentExp (positiveAction R M i) (hM.locallyNilpotent_positiveAction i)
        (Module.End.locallyNilpotentExp (-negativeAction R M i)
          (fun x ↦ by
            simpa [Module.End.neg_pow_apply_eq_zero_iff] using
              hM.locallyNilpotent_negativeAction i x)
          (Module.End.locallyNilpotentExp (positiveAction R M i)
            (hM.locallyNilpotent_positiveAction i) m)) := by
  have hrat : (Module.compHom M (algebraMap ℚ K) : Module ℚ M) = ‹Module ℚ M› :=
    Subsingleton.elim _ _
  dsimp only [simpleWeylIntertwiner, LinearEquiv.trans_apply]
  congr!

/-- **Naturality of `simpleWeylIntertwiner`.** Every `Enveloping R`-linear map between integrable
modules intertwines `simpleWeylIntertwiner`. -/
theorem map_simpleWeylIntertwiner {N : Type*} [AddCommGroup N] [Module K N]
    [Module (Enveloping R) N] [IsScalarTower K (Enveloping R) N]
    (hM : IsIntegrable R M) (hN : IsIntegrable R N) (f : M →ₗ[Enveloping R] N) (i : I) (m : M) :
    f (simpleWeylIntertwiner hM i m) = simpleWeylIntertwiner hN i (f m) := by
  let : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  let : Module ℚ N := Module.compHom N (algebraMap ℚ K)
  have hpos : Function.Semiconj f (positiveAction R M i) (positiveAction R N i) :=
    map_positiveAction f i
  have hneg : Function.Semiconj f (-negativeAction R M i : Module.End K M)
      (-negativeAction R N i : Module.End K N) := fun x ↦ by
    simp [map_negativeAction]
  have hneg_nil_N (y : N) : ∃ k, ((-negativeAction R N i) ^ k) y = 0 := by
    simpa [Module.End.neg_pow_apply_eq_zero_iff] using hN.locallyNilpotent_negativeAction i y
  rw [simpleWeylIntertwiner_apply, simpleWeylIntertwiner_apply,
    Module.End.map_locallyNilpotentExp _ _ (hN.locallyNilpotent_positiveAction i) f hpos,
    Module.End.map_locallyNilpotentExp _ _ hneg_nil_N f hneg,
    Module.End.map_locallyNilpotentExp _ _ (hN.locallyNilpotent_positiveAction i) f hpos]

private theorem two_inv_rat_smul_two_smul [Module ℚ M] (u : Module.End K M) :
    ((2⁻¹ : ℚ) • ((2 : K) • u) : Module.End K M) = u := by
  have hrat : (‹Module ℚ M› : Module ℚ M) = Module.compHom M (algebraMap ℚ K) :=
    Subsingleton.elim _ _
  ext v
  have hsmul (q : ℚ) (w : M) : q • w = algebraMap ℚ K q • w := by
    subst hrat
    rfl
  rw [LinearMap.smul_apply, hsmul, LinearMap.smul_apply, smul_smul, map_inv₀, map_ofNat,
    inv_mul_cancel₀ two_ne_zero, one_smul]

omit [CharZero K] in
private theorem exp_positiveAction_cartanAction_apply [Module ℚ M] (hM : IsIntegrable R M)
    (i : I) (x : H) (m : M) :
    Module.End.locallyNilpotentExp (positiveAction R M i) (hM.locallyNilpotent_positiveAction i)
        (cartanAction R M x m) =
      cartanAction R M x
          (Module.End.locallyNilpotentExp (positiveAction R M i)
            (hM.locallyNilpotent_positiveAction i) m) -
        R.root i x • positiveAction R M i
          (Module.End.locallyNilpotentExp (positiveAction R M i)
            (hM.locallyNilpotent_positiveAction i) m) := by
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
    rw [hd₂, smul_neg, two_inv_rat_smul_two_smul]
  have hop : g + (R.root i x • negativeAction R M i + R.root i x • cartanAction R M (R.coroot i)) +
      -(R.root i x • negativeAction R M i) =
      cartanAction R M x + R.root i x • positiveAction R M i := by
    simp only [g, map_sub, map_smul]
    abel
  rw [Module.End.locallyNilpotentExp_apply_of_lie_lie_lie_eq_zero (-negativeAction R M i) hneg
      hd₃ m,
    hhalf, hd₁, hop]

/-- **Conjugating the Cartan action by `simpleWeylIntertwiner`.** When `A i i = 2`,
`cartanAction R M x (simpleWeylIntertwiner hM i m) =
  simpleWeylIntertwiner hM i (cartanAction R M (x - R.root i x • R.coroot i) m)`. -/
theorem cartanAction_simpleWeylIntertwiner_apply (hM : IsIntegrable R M) {i : I} (hA : A i i = 2)
    (x : H) (m : M) :
    cartanAction R M x (simpleWeylIntertwiner hM i m) =
      simpleWeylIntertwiner hM i (cartanAction R M (x - R.root i x • R.coroot i) m) := by
  let : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  have hrc := root_coroot_eq_two (R := R) hA
  have hrx : R.root i (x - R.root i x • R.coroot i) = -R.root i x := by
    rw [map_sub, map_smul, hrc, smul_eq_mul]
    ring
  have hcomm_e (v : M) :
      Module.End.locallyNilpotentExp (positiveAction R M i) (hM.locallyNilpotent_positiveAction i)
          (positiveAction R M i v) =
        positiveAction R M i (Module.End.locallyNilpotentExp (positiveAction R M i)
          (hM.locallyNilpotent_positiveAction i) v) :=
    Module.End.locallyNilpotentExp_apply_of_lie_eq_zero _ _ (lie_self _) v
  rw [simpleWeylIntertwiner_apply, simpleWeylIntertwiner_apply,
    exp_positiveAction_cartanAction_apply hM i (x - R.root i x • R.coroot i) m, hrx, neg_smul,
    sub_neg_eq_add, ← LinearMap.smul_apply, ← LinearMap.add_apply,
    exp_neg_negativeAction_step hA _ x, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, exp_positiveAction_cartanAction_apply hM i x, hcomm_e, sub_add_cancel]

/-- Pushing `cartanAction` forward across `simpleWeylIntertwiner`. -/
theorem simpleWeylIntertwiner_cartanAction_apply (hM : IsIntegrable R M) {i : I} (hA : A i i = 2)
    (x : H) (m : M) :
    simpleWeylIntertwiner hM i (cartanAction R M x m) =
      cartanAction R M (x - R.root i x • R.coroot i) (simpleWeylIntertwiner hM i m) := by
  have hrc := root_coroot_eq_two (R := R) hA
  have hinv : (x - R.root i x • R.coroot i) -
      R.root i (x - R.root i x • R.coroot i) • R.coroot i = x := by
    rw [map_sub, map_smul, hrc, smul_eq_mul, sub_smul, mul_two, add_smul]
    abel
  rw [cartanAction_simpleWeylIntertwiner_apply hM hA, hinv]

/-- **Simple Weyl intertwiners permute weight spaces by simple reflections.** When `A i i = 2`,
`simpleWeylIntertwiner hM i` maps `weightSpace R M μ` into
`weightSpace R M (μ - μ (R.coroot i) • R.root i)`. -/
theorem simpleWeylIntertwiner_mem_weightSpace (hM : IsIntegrable R M) {i : I} (hA : A i i = 2)
    {μ : Dual K H} {m : M} (hm : m ∈ weightSpace R M μ) :
    simpleWeylIntertwiner hM i m ∈ weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  rw [cartanAction_simpleWeylIntertwiner_apply hM hA,
    cartanAction_apply_of_mem_weightSpace hm, map_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply]
  simp only [smul_eq_mul, mul_comm (R.root i x) (μ (R.coroot i))]

private theorem simpleWeylIntertwiner_symm_mem_weightSpace (hM : IsIntegrable R M) {i : I}
    (hA : A i i = 2) {μ : Dual K H} {m : M} (hm : m ∈ weightSpace R M μ) :
    (simpleWeylIntertwiner hM i).symm m ∈ weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  apply (simpleWeylIntertwiner hM i).injective
  rw [map_smul, LinearEquiv.apply_symm_apply, simpleWeylIntertwiner_cartanAction_apply hM hA,
    LinearEquiv.apply_symm_apply, cartanAction_apply_of_mem_weightSpace hm, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [smul_eq_mul, mul_comm (R.root i x) (μ (R.coroot i))]

/-- **Weyl-reflection equivalence of weight spaces.** For an integrable module `M` over a field of
characteristic zero and a node `i` with `A i i = 2`, `simpleWeylIntertwiner hM i` restricts to a
`K`-linear equivalence `weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i)`. -/
noncomputable def simpleWeylIntertwinerWeightEquiv (hM : IsIntegrable R M) {i : I}
    (hA : A i i = 2) (μ : Dual K H) :
    weightSpace R M μ ≃ₗ[K] weightSpace R M (μ - μ (R.coroot i) • R.root i) := by
  have hrc := root_coroot_eq_two (R := R) hA
  have hinv : (μ - μ (R.coroot i) • R.root i) -
      (μ - μ (R.coroot i) • R.root i) (R.coroot i) • R.root i = μ := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hrc, smul_eq_mul]
    ring
  exact
    { toFun := fun v ↦ ⟨simpleWeylIntertwiner hM i v.1,
        simpleWeylIntertwiner_mem_weightSpace hM hA v.2⟩
      invFun := fun w ↦ ⟨(simpleWeylIntertwiner hM i).symm w.1, by
        let m : M := w.1
        have hw := simpleWeylIntertwiner_symm_mem_weightSpace hM hA (m := m) w.2
        rwa [hinv] at hw⟩
      left_inv := fun v ↦ Subtype.ext ((simpleWeylIntertwiner hM i).symm_apply_apply v.1)
      right_inv := fun w ↦ Subtype.ext ((simpleWeylIntertwiner hM i).apply_symm_apply w.1)
      map_add' := fun v₁ v₂ ↦ Subtype.ext (map_add (simpleWeylIntertwiner hM i) v₁.1 v₂.1)
      map_smul' := fun c v ↦ Subtype.ext (map_smul (simpleWeylIntertwiner hM i) c v.1) }

@[simp]
theorem coe_simpleWeylIntertwinerWeightEquiv_apply (hM : IsIntegrable R M) {i : I}
    (hA : A i i = 2) (μ : Dual K H) (v : weightSpace R M μ) :
    (simpleWeylIntertwinerWeightEquiv hM hA μ v : M) = simpleWeylIntertwiner hM i v := (rfl)

/-- Weight multiplicities of an integrable module are invariant under simple reflections. -/
theorem finrank_weightSpace_reflect (hM : IsIntegrable R M) {i : I} (hA : A i i = 2)
    (μ : Dual K H) :
    Module.finrank K (weightSpace R M (μ - μ (R.coroot i) • R.root i)) =
      Module.finrank K (weightSpace R M μ) :=
  (simpleWeylIntertwinerWeightEquiv hM hA μ).symm.finrank_eq

/-- The set of weights of an integrable module is preserved by simple reflections. -/
theorem weightSpace_reflect_eq_bot_iff (hM : IsIntegrable R M) {i : I} (hA : A i i = 2)
    (μ : Dual K H) :
    weightSpace R M (μ - μ (R.coroot i) • R.root i) = ⊥ ↔ weightSpace R M μ = ⊥ := by
  let e := simpleWeylIntertwinerWeightEquiv hM hA μ
  rw [Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  refine ⟨fun h v hv ↦ ?_, fun h w hw ↦ ?_⟩
  · have h0 : e ⟨v, hv⟩ = 0 := Subtype.ext ((h _ (e ⟨v, hv⟩).2).trans Submodule.coe_zero.symm)
    exact congrArg Subtype.val ((map_eq_zero_iff e e.injective).mp h0)
  · have h0 : e.symm ⟨w, hw⟩ = 0 :=
      Subtype.ext ((h _ (e.symm ⟨w, hw⟩).2).trans Submodule.coe_zero.symm)
    exact congrArg Subtype.val ((map_eq_zero_iff e.symm e.symm.injective).mp h0)

end SimpleWeylIntertwiner

/-! ### Concrete simple integrable models -/

section OneDimModule

/-- **The one-dimensional module `K_λ` for an empty Dynkin diagram (`[IsEmpty I]`).** It is an
exposed type synonym for `K` on which `cartanElement R x` acts by `lam x` and the vacuous Chevalley
generators act trivially. -/
@[expose] def OneDimModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_lam : Dual K H) : Type _ := K

namespace OneDimModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (lam : Dual K H)

instance : AddCommGroup (OneDimModule R lam) := inferInstanceAs (AddCommGroup K)
instance : Module K (OneDimModule R lam) := inferInstanceAs (Module K K)
instance : FiniteDimensional K (OneDimModule R lam) := inferInstanceAs (FiniteDimensional K K)
instance : Nontrivial (OneDimModule R lam) := inferInstanceAs (Nontrivial K)

/-- The identity `K`-linear equivalence `OneDimModule R lam ≃ₗ[K] K`. -/
def equiv : OneDimModule R lam ≃ₗ[K] K := LinearEquiv.refl K K

theorem finrank_eq_one : Module.finrank K (OneDimModule R lam) = 1 :=
  Module.finrank_self K

section IsEmpty

variable [IsEmpty I]

private def cartanHom : H →ₗ[K] Module.End K (OneDimModule R lam) :=
  lam.smulRight 1

private theorem satisfiesRelations :
    SatisfiesRelations R (cartanHom R lam) isEmptyElim isEmptyElim where
  lie_cartan_cartan x y := by
    simp only [cartanHom, LinearMap.smulRight_apply, Ring.lie_def, mul_smul_comm,
      mul_one, mul_comm (lam x) (lam y), smul_smul, sub_self]
  lie_cartan_positive _ j := isEmptyElim j
  lie_cartan_negative _ j := isEmptyElim j
  lie_positive_negative_self i := isEmptyElim i
  lie_positive_negative_of_ne i := isEmptyElim i
  serre_positive i := isEmptyElim i
  serre_negative i := isEmptyElim i

/-- The enveloping-algebra representation on `OneDimModule R lam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (OneDimModule R lam) :=
  _root_.UniversalEnvelopingAlgebra.lift K (KacMoody.lift (satisfiesRelations R lam))

noncomputable instance : Module (Enveloping R) (OneDimModule R lam) :=
  Module.compHom (OneDimModule R lam) (rep R lam).toRingHom

instance : IsScalarTower K (Enveloping R) (OneDimModule R lam) where
  smul_assoc c u v := by
    change rep R lam (c • u) v = c • rep R lam u v
    rw [AlgHom.map_smul_of_tower, LinearMap.smul_apply]

@[simp]
theorem cartanAction_apply_eq (x : H) (v : OneDimModule R lam) :
    cartanAction R (OneDimModule R lam) x v = lam x • v := by
  rw [cartanAction_apply]
  change rep R lam (_root_.UniversalEnvelopingAlgebra.ι K (cartanElement R x)) v = lam x • v
  simp [rep, cartanHom]

@[simp]
theorem weightSpace_self : weightSpace R (OneDimModule R lam) lam = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_weightSpace_iff]
  exact fun x ↦ cartanAction_apply_eq R lam x v

theorem weightSpace_eq_bot_of_ne {μ : Dual K H} (hμ : μ ≠ lam) :
    weightSpace R (OneDimModule R lam) μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hμ
  have h1 := cartanAction_apply_of_mem_weightSpace hv x
  rw [cartanAction_apply_eq] at h1
  have hsub : (μ x - lam x) • v = 0 := by
    rw [sub_smul, ← h1, sub_self]
  exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hx)

/-- `OneDimModule R lam` is a simple `Enveloping R`-module. -/
instance isSimpleModule : IsSimpleModule (Enveloping R) (OneDimModule R lam) where
  eq_bot_or_eq_top P := by
    let : IsSimpleModule K (OneDimModule R lam) := IsSimpleModule.congr (equiv R lam)
    exact (eq_bot_or_eq_top (P.restrictScalars K)).imp
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))

/-- `OneDimModule R lam` lies in `IsIntegrableO R`. -/
theorem isIntegrableO : IsIntegrableO R (OneDimModule R lam) where
  isWeightModule := by
    rw [isWeightModule_iff, eq_top_iff, ← weightSpace_self R lam]
    exact le_iSup (weightSpace R (OneDimModule R lam)) lam
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hne
    refine hμ (weightSpace_eq_bot_of_ne R lam fun h ↦ hne ?_)
    subst h
    exact CartanRealization.rootLE_refl μ⟩⟩
  locallyNilpotent_positiveAction i := isEmptyElim i
  locallyNilpotent_negativeAction i := isEmptyElim i

end IsEmpty

end OneDimModule

end OneDimModule

section RankOneModule

variable {A : Matrix Unit Unit ℤ}

/-- **The standard `(n + 1)`-dimensional rank-one Kac–Moody module `L(λ)`** (`I = Unit`,
`A () () = 2`, `lam (R.coroot ()) = n`). It equips `TauCeti.Sl2Std K n` with the action of
`Enveloping R` for an arbitrary realization `H` of `A` (including realizations with central or
scaling directions), extending `Sl2Std.diag K n` from `R.coroot ()` to all of `H` via `lam`. -/
@[expose] def RankOneModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_hA : A () () = 2) (_lam : Dual K H) (n : ℕ) (_hlam : _lam (_R.coroot ()) = n) : Type _ :=
  Sl2Std K n

namespace RankOneModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A () () = 2)
  (lam : Dual K H) (n : ℕ) (hlam : lam (R.coroot ()) = n)

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

theorem finrank_eq : Module.finrank K (RankOneModule R hA lam n hlam) = n + 1 :=
  Sl2Std.finrank_eq

section CharZero

variable [CharZero K]

private noncomputable def sl2CartanHom : H →ₗ[K] Module.End K (Sl2Std K n) :=
  (lam - ((n : K) * 2⁻¹) • R.root ()).smulRight 1 +
    ((2⁻¹ : K) • R.root ()).smulRight (Sl2Std.diag K n)

private theorem sl2CartanHom_coroot (hA : A () () = 2) :
    sl2CartanHom R lam n (R.coroot ()) =
      ((lam (R.coroot ()) - (n : K)) • (1 : Module.End K (Sl2Std K n))) + Sl2Std.diag K n := by
  have hrc : R.root () (R.coroot ()) = 2 := root_coroot_eq_two (R := R) hA
  simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hrc, smul_eq_mul]
  rw [mul_assoc (n : K) 2⁻¹ 2, inv_mul_cancel₀ two_ne_zero, mul_one, one_smul]

private noncomputable def sl2Rep (hA : A () () = 2) (hlam : lam (R.coroot ()) = n) :
    Enveloping R →ₐ[K] Module.End K (Sl2Std K n) :=
  _root_.UniversalEnvelopingAlgebra.lift K <| KacMoody.lift <|
    { lie_cartan_cartan := fun x y ↦ by
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, lie_add, add_lie,
          lie_smul, smul_lie, Ring.lie_def (1 : Module.End K (Sl2Std K n)),
          Ring.lie_def _ (1 : Module.End K (Sl2Std K n)), mul_one, one_mul, sub_self, lie_self,
          smul_zero, add_zero]
      lie_cartan_positive := fun x _ ↦ by
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.raise K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_raise, smul_zero, zero_add, smul_smul, mul_assoc,
          mul_comm (R.root () x) 2, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
      lie_cartan_negative := fun x _ ↦ by
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.lower K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_lower, smul_zero, zero_add, smul_neg, smul_smul, mul_assoc,
          mul_comm (R.root () x) 2, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
      lie_positive_negative_self := fun () ↦ by
        rw [Sl2Std.lie_raise_lower, sl2CartanHom_coroot R lam n hA, hlam, sub_self, zero_smul,
          zero_add]
      lie_positive_negative_of_ne := fun i j hij ↦ absurd (Subsingleton.elim i j) hij
      serre_positive := fun _ _ ↦ by rw [lie_self, map_zero]
      serre_negative := fun _ _ ↦ by rw [lie_self, map_zero] :
        SatisfiesRelations R (sl2CartanHom R lam n) (fun _ ↦ Sl2Std.raise K n)
          (fun _ ↦ Sl2Std.lower K n) }

/-- The enveloping-algebra representation on `RankOneModule R hA lam n hlam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (RankOneModule R hA lam n hlam) :=
  ((equiv R hA lam n hlam).symm.conjAlgEquiv K).toAlgHom.comp (sl2Rep R lam n hA hlam)

noncomputable instance : Module (Enveloping R) (RankOneModule R hA lam n hlam) :=
  Module.compHom (RankOneModule R hA lam n hlam) (rep R hA lam n hlam).toRingHom

instance : IsScalarTower K (Enveloping R) (RankOneModule R hA lam n hlam) where
  smul_assoc c u v := by
    change rep R hA lam n hlam (c • u) v = c • rep R hA lam n hlam u v
    rw [AlgHom.map_smul_of_tower, LinearMap.smul_apply]

theorem positiveAction_eq :
    positiveAction R (RankOneModule R hA lam n hlam) () =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.raise K n) := by
  ext v
  rw [positiveAction_apply]
  change rep R hA lam n hlam (_root_.UniversalEnvelopingAlgebra.ι K (positiveGenerator R ())) v = _
  simp [rep, sl2Rep]

theorem negativeAction_eq :
    negativeAction R (RankOneModule R hA lam n hlam) () =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.lower K n) := by
  ext v
  rw [negativeAction_apply]
  change rep R hA lam n hlam (_root_.UniversalEnvelopingAlgebra.ι K (negativeGenerator R ())) v = _
  simp [rep, sl2Rep]

private theorem cartanAction_eq (x : H) :
    cartanAction R (RankOneModule R hA lam n hlam) x =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (sl2CartanHom R lam n x) := by
  ext v
  rw [cartanAction_apply]
  change rep R hA lam n hlam (_root_.UniversalEnvelopingAlgebra.ι K (cartanElement R x)) v = _
  simp [rep, sl2Rep]

theorem cartanAction_coroot :
    cartanAction R (RankOneModule R hA lam n hlam) (R.coroot ()) =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.diag K n) := by
  rw [cartanAction_eq, sl2CartanHom_coroot R lam n hA, hlam, sub_self, zero_smul, zero_add]

@[simp]
theorem equiv_positiveAction_apply (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (positiveAction R (RankOneModule R hA lam n hlam) () v) =
      Sl2Std.raise K n (equiv R hA lam n hlam v) := by
  rw [positiveAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

@[simp]
theorem equiv_negativeAction_apply (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (negativeAction R (RankOneModule R hA lam n hlam) () v) =
      Sl2Std.lower K n (equiv R hA lam n hlam v) := by
  rw [negativeAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

private theorem equiv_cartanAction_apply (x : H) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) x v) =
      sl2CartanHom R lam n x (equiv R hA lam n hlam v) := by
  rw [cartanAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

@[simp]
theorem equiv_cartanAction_coroot_apply (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) (R.coroot ()) v) =
      Sl2Std.diag K n (equiv R hA lam n hlam v) := by
  rw [cartanAction_coroot]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Coordinate basis vector `vₖ` has weight `lam - k • α`. -/
theorem basis_mem_weightSpace (k : Fin (n + 1)) :
    basis R hA lam n hlam k ∈
      weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root ()) := by
  rw [mem_weightSpace_iff]
  intro x
  apply (equiv R hA lam n hlam).injective
  rw [equiv_cartanAction_apply, map_smul, equiv_basis]
  simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, _root_.one_apply_eq_self, Sl2Std.diag_basis, smul_smul, ← add_smul,
    smul_eq_mul, nsmul_eq_mul]
  congr 1
  have h2 : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  linear_combination ((n : K) * R.root () x - 2 * (k : K) * R.root () x) * h2

theorem weightSpace_eq_bot_of_forall_ne {μ : Dual K H}
    (hμ : ∀ k : Fin (n + 1), μ ≠ lam - (k : ℕ) • R.root ()) :
    weightSpace R (RankOneModule R hA lam n hlam) μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  set w : Sl2Std K n := equiv R hA lam n hlam v
  have hdiag_μ : Sl2Std.diag K n w = μ (R.coroot ()) • w := by
    rw [← equiv_cartanAction_coroot_apply, cartanAction_apply_of_mem_weightSpace hv, map_smul]
  by_cases hc : ∀ k : Fin (n + 1), μ (R.coroot ()) ≠ (n : K) - 2 * (k : ℕ)
  · have hmem : w ∈ (Sl2Std.diag K n).eigenspace (μ (R.coroot ())) :=
      Module.End.mem_eigenspace_iff.mpr hdiag_μ
    rw [Sl2Std.eigenspace_diag_eq_bot hc] at hmem
    exact (map_eq_zero_iff (equiv R hA lam n hlam) (equiv R hA lam n hlam).injective).mp
      ((Submodule.mem_bot K).mp hmem)
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have hspan : w ∈ K ∙ Sl2Std.basis K n k := by
      rw [← Sl2Std.eigenspace_diag, Module.End.mem_eigenspace_iff, ← hk]
      exact hdiag_μ
    obtain ⟨c, hc_eq⟩ := Submodule.mem_span_singleton.mp hspan
    have hv_eq : v = c • basis R hA lam n hlam k := by
      apply (equiv R hA lam n hlam).injective
      rw [map_smul, equiv_basis]
      exact hc_eq.symm
    subst hv_eq
    by_cases hc0 : c = 0
    · simp [hc0]
    · exfalso
      apply hμ k
      ext x
      have h1 := cartanAction_apply_of_mem_weightSpace hv x
      have h2 := cartanAction_apply_of_mem_weightSpace
        (basis_mem_weightSpace R hA lam n hlam k) x
      rw [map_smul, h2, smul_comm] at h1
      have hsub : (μ x - (lam - (k : ℕ) • R.root ()) x) • (c • basis R hA lam n hlam k) = 0 := by
        rw [sub_smul, ← h1, sub_self]
      have hne : c • basis R hA lam n hlam k ≠ 0 :=
        smul_ne_zero hc0 ((basis R hA lam n hlam).ne_zero k)
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hne)

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
          exact ⟨positiveAction R _ () x,
            by rw [positiveAction_apply]; exact P.smul_mem _ hx, equiv_positiveAction_apply ..⟩)
        (fun _ hw ↦ by
          rcases hw with ⟨x, hx, rfl⟩
          exact ⟨negativeAction R _ () x,
            by rw [negativeAction_apply]; exact P.smul_mem _ hx, equiv_negativeAction_apply ..⟩)
      have hvQ : e v ∈ Q := hQ_top ▸ Submodule.mem_top
      obtain ⟨x, hxP, hxe⟩ := hvQ
      exact e.injective hxe ▸ hxP

/-- **`RankOneModule R hA lam n hlam` lies in `IsIntegrableO R`.** -/
theorem isIntegrableO : IsIntegrableO R (RankOneModule R hA lam n hlam) where
  isWeightModule := by
    rw [isWeightModule_iff, ← top_le_iff, ← (basis R hA lam n hlam).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact le_iSup (weightSpace R (RankOneModule R hA lam n hlam)) (lam - (k : ℕ) • R.root ())
      (basis_mem_weightSpace R hA lam n hlam k)
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hle
    refine hμ (weightSpace_eq_bot_of_forall_ne R hA lam n hlam fun k hk ↦ hle ?_)
    rw [hk, CartanRealization.rootLE_iff, sub_sub_cancel]
    exact nsmul_mem (R.root_mem_posRootCone ()) k⟩⟩
  locallyNilpotent_positiveAction _ v := ⟨n + 1, by
    rw [positiveAction_eq, ← map_pow, Sl2Std.raise_pow_eq_zero, map_zero, LinearMap.zero_apply]⟩
  locallyNilpotent_negativeAction _ v := ⟨n + 1, by
    rw [negativeAction_eq, ← map_pow, Sl2Std.lower_pow_eq_zero, map_zero, LinearMap.zero_apply]⟩

/-- On `RankOneModule R hA lam n hlam`, `simpleWeylIntertwiner` corresponds under `equiv` to
`TauCeti.Sl2Std.weylUnit K n`. -/
theorem equiv_simpleWeylIntertwiner_apply (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam
        (simpleWeylIntertwiner (isIntegrableO R hA lam n hlam).toIsIntegrable () v) =
      (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) (equiv R hA lam n hlam v) := by
  let φ := (equiv R hA lam n hlam).symm.conjAlgEquiv K
  have hpos_nil : IsNilpotent (positiveAction R (RankOneModule R hA lam n hlam) ()) :=
    ⟨n + 1, by rw [positiveAction_eq, ← map_pow, Sl2Std.raise_pow_eq_zero, map_zero]⟩
  have hneg_nil : IsNilpotent (-negativeAction R (RankOneModule R hA lam n hlam) ()) :=
    ⟨n + 1, by
      rw [negativeAction_eq, ← map_neg, ← map_pow, neg_pow, Sl2Std.lower_pow_eq_zero, mul_zero,
        map_zero]⟩
  have hep : (Module.End.locallyNilpotentExp
      (positiveAction R (RankOneModule R hA lam n hlam) ())
      ((isIntegrableO R hA lam n hlam).locallyNilpotent_positiveAction ())).toLinearMap =
      φ (IsNilpotent.exp (Sl2Std.raise K n)) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ hpos_nil, positiveAction_eq,
      IsNilpotent.map_exp Sl2Std.isNilpotent_raise φ]
  have hfn : (Module.End.locallyNilpotentExp
      (-negativeAction R (RankOneModule R hA lam n hlam) ())
      (fun x ↦ by
        simpa [Module.End.neg_pow_apply_eq_zero_iff] using
          (isIntegrableO R hA lam n hlam).locallyNilpotent_negativeAction () x)).toLinearMap =
      φ (IsNilpotent.exp (-(Sl2Std.lower K n))) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ hneg_nil, negativeAction_eq, ← map_neg,
      IsNilpotent.map_exp Sl2Std.isNilpotent_lower.neg φ]
  have hweyl : (simpleWeylIntertwiner (isIntegrableO R hA lam n hlam).toIsIntegrable ()).toLinearMap
      = φ (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) := by
    ext x
    rw [LinearEquiv.coe_coe, simpleWeylIntertwiner_apply, Sl2Std.coe_weylUnit, map_mul, map_mul,
      _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp]
    change (Module.End.locallyNilpotentExp _ _).toLinearMap
      ((Module.End.locallyNilpotentExp _ _).toLinearMap
        ((Module.End.locallyNilpotentExp _ _).toLinearMap x)) = _
    rw [hep, hfn]
  have hv := congrArg (fun g : Module.End K (RankOneModule R hA lam n hlam) ↦
    equiv R hA lam n hlam (g v)) hweyl
  simpa [φ, LinearEquiv.conjAlgEquiv_apply] using hv

/-- **Squaring `simpleWeylIntertwiner` on `RankOneModule`.** Two applications of the simple Weyl
intertwiner multiply every vector of `RankOneModule R hA lam n hlam` by `(-1) ^ n` (so on `n = 1`
it acts as `-1`, not `+1`, whereas on `n = 2` it acts as `+1`). -/
@[simp]
theorem simpleWeylIntertwiner_simpleWeylIntertwiner_apply (v : RankOneModule R hA lam n hlam) :
    simpleWeylIntertwiner (isIntegrableO R hA lam n hlam).toIsIntegrable ()
      (simpleWeylIntertwiner (isIntegrableO R hA lam n hlam).toIsIntegrable () v) =
        (-1 : K) ^ n • v := by
  apply (equiv R hA lam n hlam).injective
  rw [equiv_simpleWeylIntertwiner_apply, equiv_simpleWeylIntertwiner_apply, map_smul,
    Sl2Std.weylUnit_weylUnit_apply]

end CharZero

end RankOneModule

end RankOneModule

end KacMoody

end TauCeti
