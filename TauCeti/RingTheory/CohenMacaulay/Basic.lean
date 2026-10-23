/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import TauCeti.RingTheory.Depth.Basic

/-!
# Cohen–Macaulay modules over a local ring

A finite module `M` over a Noetherian local ring `R` is *Cohen–Macaulay* if `M = 0` or its depth
equals the dimension of its support (Stacks, Definition 10.103.1 (00N3)). Depth is Mathlib's
`IsLocalRing.depth`, defined through the vanishing of `Ext (R ⧸ 𝔪) M`, and the dimension of the
support is Mathlib's `Module.supportDim`. Since the depth of a finite nonzero module never exceeds
the dimension of its support (`IsLocalRing.depth_le_supportDim`), being Cohen–Macaulay is the
reverse inequality.

The zero module is Cohen–Macaulay by convention: its depth is `⊤` while its support dimension is
`⊥`, so the depth equation alone would exclude it.

## Main definitions and results

* `Module.IsCohenMacaulay R M`: the `R`-module `M` is Cohen–Macaulay.
* `Module.isCohenMacaulay_iff_supportDim_le_depth`: a finite nonzero module over a Noetherian local
  ring is Cohen–Macaulay if and only if the dimension of its support is at most its depth.
* `Module.isCohenMacaulay_quotSMulTop_iff`: for an `M`-regular element `x` of the maximal ideal,
  `M ⧸ x M` is Cohen–Macaulay if and only if `M` is (Stacks, Lemma 10.103.5 (0C6G)), and
  `Module.isCohenMacaulay_quotient_ofList_smul_iff` is the same for an `M`-regular sequence.
* `Module.isCohenMacaulay_of_krullDimLE_zero`: every finite module over a Noetherian local ring of
  dimension zero, such as a field, is Cohen–Macaulay.
* `Module.isCohenMacaulay_self_of_isDomain_of_krullDimLE_one`: a Noetherian local domain of
  dimension at most one, such as a discrete valuation ring, is Cohen–Macaulay over itself.
* `Module.IsCohenMacaulay.ringKrullDim_quotient_eq_supportDim` and
  `Module.IsCohenMacaulay.associatedPrimes_eq_minimalPrimes`: a Cohen–Macaulay module is unmixed.
  For every associated prime `p`, the dimension of `R ⧸ p` is the dimension of the support, and
  the associated primes are exactly the minimal primes of the support, so there are no embedded
  primes (Stacks, Lemma 10.103.7 (0BUS)).
-/

public section

universe u v w

open IsLocalRing RingTheory.Sequence Pointwise

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` over a local ring `R` is *Cohen–Macaulay* if it is zero or its depth equals
the dimension of its support. This is meant for finite modules over a Noetherian local ring, where
the depth never exceeds the dimension of the support. Stacks, Definition 10.103.1 (00N3). -/
@[stacks 00N3]
def IsCohenMacaulay : Prop :=
  Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M

/-- Unfolds `Module.IsCohenMacaulay`. -/
theorem isCohenMacaulay_iff : IsCohenMacaulay R M ↔
    Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  Iff.rfl

variable {R M}

/-- The zero module is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_subsingleton [Subsingleton M] : IsCohenMacaulay R M :=
  Or.inl ‹_›

/-- A nonzero module is Cohen–Macaulay if and only if its depth equals the dimension of its
support. -/
theorem isCohenMacaulay_iff_depth_eq [Nontrivial M] :
    IsCohenMacaulay R M ↔ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M := by
  rw [isCohenMacaulay_iff, or_iff_right (not_subsingleton M)]

/-- The depth of a nonzero Cohen–Macaulay module equals the dimension of its support. -/
theorem IsCohenMacaulay.depth_eq [Nontrivial M] (h : IsCohenMacaulay R M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M :=
  isCohenMacaulay_iff_depth_eq.1 h

/-- A finite nonzero module over a Noetherian local ring is Cohen–Macaulay if and only if the
dimension of its support is at most its depth, the reverse inequality being
`IsLocalRing.depth_le_supportDim`. -/
theorem isCohenMacaulay_iff_supportDim_le_depth [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] :
    IsCohenMacaulay R M ↔ supportDim R M ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞) := by
  rw [isCohenMacaulay_iff_depth_eq, le_antisymm_iff, and_iff_right depth_le_supportDim]

end Module

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] [Small.{w} R]
  {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]

/-- Being Cohen–Macaulay is invariant under linear equivalence. -/
theorem isCohenMacaulay_iff (e : M ≃ₗ[R] N) :
    Module.IsCohenMacaulay R M ↔ Module.IsCohenMacaulay R N := by
  rw [Module.isCohenMacaulay_iff, Module.isCohenMacaulay_iff, e.toEquiv.subsingleton_congr,
    depth_eq_of_linearEquiv e, Module.supportDim_eq_of_equiv e]

end LinearEquiv

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For an `M`-regular element `x` of the maximal ideal, `M ⧸ x M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G). -/
@[stacks 0C6G]
theorem isCohenMacaulay_quotSMulTop_iff {x : R} (reg : IsSMulRegular M x)
    (hx : x ∈ maximalIdeal R) : IsCohenMacaulay R (QuotSMulTop x M) ↔ IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact iff_of_true isCohenMacaulay_of_subsingleton isCohenMacaulay_of_subsingleton
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_quotSMulTop_succ_eq_depth reg hx, ← supportDim_quotSMulTop_succ_eq_supportDim reg hx,
    WithBot.coe_add, WithBot.coe_one, ENat.WithBot.add_one_cancel]

/-- For an `M`-regular sequence `r₁, …, rₙ`, `M ⧸ (r₁, …, rₙ) M` is Cohen–Macaulay if and only if
`M` is. Stacks, Lemma 10.103.5 (0C6G), applied `n` times. -/
theorem isCohenMacaulay_quotient_ofList_smul_iff (rs : List R) (reg : IsRegular M rs) :
    IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ↔ IsCohenMacaulay R M := by
  have := reg.nontrivial
  have := reg.quot_ofList_smul_nontrivial ⊤
  rw [isCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    ← depth_add_length_eq_depth_of_isRegular rs reg,
    ← supportDim_add_length_eq_supportDim_of_isRegular rs reg, WithBot.coe_add,
    WithBot.coe_natCast, ENat.WithBot.add_natCast_cancel]

/-- Every finite module over a Noetherian local ring of dimension zero is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_krullDimLE_zero [Ring.KrullDimLE 0 R] : IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact isCohenMacaulay_of_subsingleton
  refine isCohenMacaulay_iff_supportDim_le_depth.2 <|
    (supportDim_le_ringKrullDim R M).trans <| (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast zero_le

/-- Over a Noetherian local ring, the quotient by an associated prime of a Cohen–Macaulay module
has the dimension of the support of the module. Stacks, Lemma 10.103.7 (0BUS); H. Matsumura,
*Commutative Ring Theory*, Theorem 17.3 (i). -/
@[stacks 0BUS]
theorem IsCohenMacaulay.ringKrullDim_quotient_eq_supportDim (h : IsCohenMacaulay R M)
    {p : Ideal R} (hp : IsAssociatedPrime p M) : ringKrullDim (R ⧸ p) = supportDim R M := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  exact le_antisymm hp.ringKrullDim_quotient_le_supportDim
    (h.depth_eq ▸ depth_le_ringKrullDim_quotient_of_isAssociatedPrime hp)

/-- The associated primes of a Cohen–Macaulay module over a Noetherian local ring are the minimal
primes of its support: a Cohen–Macaulay module has no embedded primes. Stacks, Lemma 10.103.7
(0BUS). -/
@[stacks 0BUS]
theorem IsCohenMacaulay.associatedPrimes_eq_minimalPrimes (h : IsCohenMacaulay R M) :
    associatedPrimes R M = (annihilator R M).minimalPrimes := by
  refine Set.Subset.antisymm (fun p hp ↦ ?_)
    (associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M)
  have hp : IsAssociatedPrime p M := AssociatedPrimes.mem_iff.1 hp
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.1 fun _ ↦ not_isAssociatedPrime_of_subsingleton hp
  refine ⟨⟨hp.isPrime, Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le⟩,
    fun q ⟨hq, hann⟩ hqp ↦ by_contra fun hpq ↦ ?_⟩
  -- A prime `q ⊊ p` of the support would give `dim (R ⧸ p) + 1 ≤ dim (R ⧸ q) ≤ dim Supp M`,
  -- while `dim (R ⧸ p) = dim Supp M` is finite.
  have hle := (TauCeti.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_not_ge hqp hpq)).trans
    (supportDim_eq_ringKrullDim_quotient_annihilator R M ▸
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hann))
  rw [h.ringKrullDim_quotient_eq_supportDim hp] at hle
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 (supportDim_ne_bot_of_nontrivial R M)
  have hd_top : d ≠ ⊤ := by
    rintro rfl
    exact (hd ▸ (supportDim_le_ringKrullDim R M).trans_lt ringKrullDim_lt_top).ne rfl
  rw [← hd, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe,
    ENat.add_one_le_iff hd_top] at hle
  exact hle.false

end Module

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

/-- A Noetherian local domain of dimension at most one is Cohen–Macaulay over itself. -/
theorem isCohenMacaulay_self_of_isDomain_of_krullDimLE_one [Ring.KrullDimLE 1 R] :
    IsCohenMacaulay R R := by
  rw [isCohenMacaulay_iff_supportDim_le_depth, supportDim_self_eq_ringKrullDim]
  by_cases hm : maximalIdeal R = ⊥
  · rw [ringKrullDim_eq_zero_of_isField ((isField_iff_maximalIdeal_eq).2 hm)]
    exact_mod_cast zero_le
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  rw [← depth_quotSMulTop_succ_eq_depth (IsSMulRegular.of_ne_zero hx0) hx]
  refine (Ring.krullDimLE_iff.1 ‹_›).trans ?_
  exact_mod_cast le_add_self

example (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V] :
    IsCohenMacaulay K V :=
  isCohenMacaulay_of_krullDimLE_zero

example (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsCohenMacaulay A A :=
  isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Module
