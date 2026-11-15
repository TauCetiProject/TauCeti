/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.LinearAlgebra.End.IterateDirectLimit
public import TauCeti.LinearAlgebra.End.RangePow

/-!
# Stable module endomorphisms and their direct-limit localization

An `R`-linear endomorphism `T` of a module `M` is *stable at exponent `c`* (`Module.End.IsStableAt`)
if `1 ≤ c` and `M` admits a `T`-invariant complement `I` to `LinearMap.ker (T ^ c)` on which `T`
restricts to a bijection; `T` is *stable* (`Module.End.IsStable`) if it is stable at some positive
exponent. Such a complement `I` is uniquely forced to equal `LinearMap.range (T ^ c)`. Over a
ring:

* for a fixed exponent `c`, `T.IsStableAt c` holds if and only if `1 ≤ c` and
  `IsCompl (LinearMap.ker (T ^ c)) (LinearMap.range (T ^ c))`
  (`Module.End.isStableAt_iff_isCompl_ker_pow_range_pow`);
* `T.IsStable` holds if and only if both `LinearMap.ker (T ^ (c + 1)) = LinearMap.ker (T ^ c)` and
  `LinearMap.range (T ^ (c + 1)) = LinearMap.range (T ^ c)` at some stage `c`, if and only if `M`
  admits a Fitting-type decomposition
  `M = (⨆ n, LinearMap.ker (T ^ n)) ⊕ (⨅ n, LinearMap.range (T ^ n))` in which `T` is nilpotent
  on the left summand and bijective on the right summand.

In particular, every nilpotent endomorphism, every bijective endomorphism, and every endomorphism of
a module that is both Noetherian and Artinian is stable, without requiring finite-length hypotheses
in general. When `T` is stable, restricting the canonical localization map
`Module.End.toIterateDirectLimit T : M →ₗ[R] T.IterateDirectLimit` to the invertible summand
`⨅ n, LinearMap.range (T ^ n)` yields a canonical linear isomorphism
`Module.End.IsStable.iInfRangePowEquivIterateDirectLimit` identifying `M[T⁻¹]` with the stable
range, and pulling back along `toIterateDirectLimit` recovers the Fitting projection onto
`⨅ n, LinearMap.range (T ^ n)` along `⨆ n, LinearMap.ker (T ^ n)`.

## Main definitions

* `Module.End.IsStableAt`: stability of `T : Module.End R M` at a positive exponent `c`.
* `Module.End.IsStable`: existence of a positive stabilizing exponent `c`.
* `Module.End.IsStable.iInfRangePowEquivIterateDirectLimit`: canonical linear equivalence
  `(⨅ n, LinearMap.range (T ^ n)) ≃ₗ[R] T.IterateDirectLimit` for a stable endomorphism `T`.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Definition 11.9 and Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

namespace Module.End

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An endomorphism `T` of an `R`-module `M` is *stable at exponent `c`* if `1 ≤ c` and `M` admits a
`T`-invariant complement `I` to `LinearMap.ker (T ^ c)` on which `T` restricts to a bijection. -/
def IsStableAt (T : End R M) (c : ℕ) : Prop :=
  1 ≤ c ∧ ∃ I : Submodule R M, ∃ hI : I ∈ T.invtSubmodule,
    IsCompl (LinearMap.ker (T ^ c)) I ∧ Function.Bijective (T.restrict hI)

/-- Unfolding lemma for `Module.End.IsStableAt`. -/
theorem isStableAt_def (T : End R M) (c : ℕ) :
    T.IsStableAt c ↔ 1 ≤ c ∧ ∃ I : Submodule R M, ∃ hI : I ∈ T.invtSubmodule,
      IsCompl (LinearMap.ker (T ^ c)) I ∧ Function.Bijective (T.restrict hI) :=
  Iff.rfl

/-- An endomorphism `T` of an `R`-module `M` is *stable* if it is stable at some positive
exponent. -/
def IsStable (T : End R M) : Prop :=
  ∃ c, T.IsStableAt c

/-- Unfolding lemma for `Module.End.IsStable`. -/
theorem isStable_def (T : End R M) :
    T.IsStable ↔ ∃ c, T.IsStableAt c :=
  Iff.rfl

/-- A stabilizing exponent `c` in `Module.End.IsStableAt` is positive (`1 ≤ c`). -/
theorem IsStableAt.one_le {T : End R M} {c : ℕ} (h : T.IsStableAt c) : 1 ≤ c :=
  h.1

/-- Stability at a specific exponent `c` implies `Module.End.IsStable`. -/
theorem IsStableAt.isStable {T : End R M} {c : ℕ} (h : T.IsStableAt c) : T.IsStable :=
  ⟨c, h⟩

/-- Any `T`-invariant submodule `I` codisjoint from `LinearMap.ker (T ^ c)` on which `T` is
surjective equals `LinearMap.range (T ^ c)`. In particular, the invertible summand in
`Module.End.IsStableAt` is uniquely determined. -/
theorem eq_range_pow_of_codisjoint_of_surjective {T : End R M} {c : ℕ} {I : Submodule R M}
    (hI : I ∈ T.invtSubmodule) (hcod : Codisjoint (LinearMap.ker (T ^ c)) I)
    (hsurj : Function.Surjective (T.restrict hI)) :
    I = LinearMap.range (T ^ c) := by
  have hmaps : ∀ n : ℕ, ∀ v ∈ I, (T ^ n) v ∈ I := fun n ↦ by
    induction n with
    | zero => simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', mul_apply_eq_comp]
      exact hI (ih v hv)
  have hpow_surj : ∀ n : ℕ, ∀ y ∈ I, ∃ z ∈ I, (T ^ n) z = y := fun n ↦ by
    induction n with
    | zero => exact fun y hy ↦ ⟨y, hy, by simp⟩
    | succ n ih =>
      intro y hy
      obtain ⟨w, hw, rfl⟩ := ih y hy
      obtain ⟨⟨z, hz⟩, hzw⟩ := hsurj ⟨w, hw⟩
      refine ⟨z, hz, ?_⟩
      rw [pow_succ, mul_apply_eq_comp]
      exact congrArg (T ^ n) (congrArg Subtype.val hzw)
  refine le_antisymm (fun y hy ↦ ?_) ?_
  · obtain ⟨z, _, rfl⟩ := hpow_surj c y hy
    exact LinearMap.mem_range_self (T ^ c) z
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker (T ^ c) ⊔ I := by
      rw [hcod.eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.mem_ker.mp hu, zero_add]
    exact hmaps c v hv

/-- In `Module.End.IsStableAt`, any witnessing `T`-invariant complement `I` equals
`LinearMap.range (T ^ c)`. -/
theorem IsStableAt.eq_range_pow {T : End R M} {c : ℕ} {I : Submodule R M}
    (hI : I ∈ T.invtSubmodule) (hcompl : IsCompl (LinearMap.ker (T ^ c)) I)
    (hbij : Function.Bijective (T.restrict hI)) :
    I = LinearMap.range (T ^ c) :=
  eq_range_pow_of_codisjoint_of_surjective hI hcompl.codisjoint hbij.surjective

/-- An endomorphism annihilated by `T ^ c` with `1 ≤ c` is stable at `c`, with nilpotent summand
`⊤` and invertible summand `⊥`. -/
theorem IsStableAt.of_pow_eq_zero {T : End R M} {c : ℕ} (hc : 1 ≤ c) (h0 : T ^ c = 0) :
    T.IsStableAt c := by
  have hker : LinearMap.ker (T ^ c) = ⊤ := by simp [h0]
  refine ⟨hc, ⊥, invtSubmodule.bot_mem T, ?_, ?_⟩
  · rw [hker]
    exact isCompl_top_bot
  · exact ⟨Function.injective_of_subsingleton _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

/-- The zero endomorphism is stable at exponent `1`. -/
@[simp]
theorem IsStableAt.zero : (0 : End R M).IsStableAt 1 :=
  IsStableAt.of_pow_eq_zero le_rfl (pow_one 0)

/-- The zero endomorphism is stable. -/
@[simp]
theorem IsStable.zero : (0 : End R M).IsStable :=
  IsStableAt.zero.isStable

/-- Every nilpotent endomorphism is stable. -/
theorem _root_.IsNilpotent.isStable {T : End R M} (hT : IsNilpotent T) : T.IsStable := by
  obtain ⟨c, hc⟩ := hT
  refine ⟨c + 1, IsStableAt.of_pow_eq_zero (Nat.succ_le_succ (Nat.zero_le c)) ?_⟩
  rw [pow_succ, hc, zero_mul]

/-- A bijective endomorphism is stable at every positive exponent `c`, with nilpotent summand `⊥`
and invertible summand `⊤`. -/
theorem IsStableAt.of_bijective {T : End R M} (hT : Function.Bijective T) {c : ℕ} (hc : 1 ≤ c) :
    T.IsStableAt c := by
  have hker : LinearMap.ker (T ^ c) = ⊥ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot, pow_apply_eq_iterate]
    exact ⟨fun hx ↦ hT.injective.iterate c (by simpa using hx), fun hx ↦ by simp [hx]⟩
  refine ⟨hc, ⊤, invtSubmodule.top_mem T, ?_, ?_⟩
  · rw [hker]
    exact isCompl_bot_top
  · refine ⟨fun x y hxy ↦ Subtype.ext (hT.injective (congrArg Subtype.val hxy)), fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hT.surjective y.1
    exact ⟨⟨x, Submodule.mem_top⟩, Subtype.ext hx⟩

/-- A bijective endomorphism is stable. -/
theorem IsStable.of_bijective {T : End R M} (hT : Function.Bijective T) : T.IsStable :=
  (IsStableAt.of_bijective hT le_rfl).isStable

/-- The identity endomorphism `1` is stable at exponent `1`. -/
@[simp]
theorem IsStableAt.one : (1 : End R M).IsStableAt 1 :=
  IsStableAt.of_bijective Function.bijective_id le_rfl

/-- The identity endomorphism `1` is stable. -/
@[simp]
theorem IsStable.one : (1 : End R M).IsStable :=
  IsStableAt.one.isStable

/-- If `T` is stable at `c`, `LinearMap.ker (T ^ c)` and `LinearMap.range (T ^ c)` are
complementary submodules. -/
theorem IsStableAt.isCompl_ker_pow_range_pow {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    IsCompl (LinearMap.ker (T ^ c)) (LinearMap.range (T ^ c)) := by
  obtain ⟨_, I, hI, hcompl, hbij⟩ := h
  exact IsStableAt.eq_range_pow hI hcompl hbij ▸ hcompl

/-- If `T` is stable at `c`, `T` restricts to a bijection on `LinearMap.range (T ^ c)`. -/
theorem IsStableAt.bijective_restrict_range_pow {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    Function.Bijective (T.restrict fun _ hx ↦ T.mapsTo_range_pow c hx) := by
  obtain ⟨_, I, hI, hcompl, hbij⟩ := h
  exact LinearMap.bijective_restrict_of_eq (IsStableAt.eq_range_pow hI hcompl hbij) hbij

/-- Over any semiring, `T` is stable at `c` if and only if `1 ≤ c`, `LinearMap.ker (T ^ c)` and
`LinearMap.range (T ^ c)` are complementary submodules, and `T` restricts to a bijection on
`LinearMap.range (T ^ c)`. -/
theorem isStableAt_iff_isCompl_and_bijective_restrict_range_pow {T : End R M} {c : ℕ} :
    T.IsStableAt c ↔
      1 ≤ c ∧ IsCompl (LinearMap.ker (T ^ c)) (LinearMap.range (T ^ c)) ∧
        Function.Bijective (T.restrict fun _ hx ↦ T.mapsTo_range_pow c hx) :=
  ⟨fun h ↦ ⟨h.one_le, h.isCompl_ker_pow_range_pow, h.bijective_restrict_range_pow⟩,
    fun ⟨hc, hcompl, hbij⟩ ↦
      ⟨hc, LinearMap.range (T ^ c), fun _ hx ↦ T.mapsTo_range_pow c hx, hcompl, hbij⟩⟩

/-- If `T` is stable at `c`, the iterate-kernel chain has stabilized at `c`:
`LinearMap.ker (T ^ (c + 1)) = LinearMap.ker (T ^ c)`. -/
theorem IsStableAt.ker_pow_succ_eq {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    LinearMap.ker (T ^ (c + 1)) = LinearMap.ker (T ^ c) := by
  refine le_antisymm (fun x hx ↦ ?_) (T.iterateKer.monotone (Nat.le_succ c))
  rw [LinearMap.mem_ker, pow_succ', mul_apply_eq_comp] at hx
  exact LinearMap.mem_ker.mpr
    (Submodule.disjoint_def.mp h.isCompl_ker_pow_range_pow.disjoint _
      (T.iterateKer.monotone h.one_le (by simpa using hx))
      (LinearMap.mem_range_self (T ^ c) x))

/-- If `T` is stable at `c`, the iterate-range chain has stabilized at `c`:
`LinearMap.range (T ^ (c + 1)) = LinearMap.range (T ^ c)`. -/
theorem IsStableAt.range_pow_succ_eq {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    LinearMap.range (T ^ (c + 1)) = LinearMap.range (T ^ c) := by
  refine le_antisymm (T.iterateRange.monotone (Nat.le_succ c)) ?_
  rintro y ⟨x, rfl⟩
  obtain ⟨z, hz⟩ :=
    h.bijective_restrict_range_pow.surjective ⟨(T ^ c) x, LinearMap.mem_range_self _ x⟩
  obtain ⟨w, hw⟩ := z.2
  refine ⟨w, ?_⟩
  have hz' : T z.1 = (T ^ c) x := congrArg Subtype.val hz
  rw [pow_succ', mul_apply_eq_comp, hw, hz']

/-- If `T` is stable at `c`, `LinearMap.ker (T ^ d) = LinearMap.ker (T ^ c)` for every `d ≥ c`. -/
theorem IsStableAt.ker_pow_eq_of_le {T : End R M} {c d : ℕ} (h : T.IsStableAt c) (hcd : c ≤ d) :
    LinearMap.ker (T ^ d) = LinearMap.ker (T ^ c) := by
  rw [← Nat.add_sub_of_le hcd, LinearMap.ker_pow_add_eq_of_ker_pow_succ_eq h.ker_pow_succ_eq]

/-- If `T` is stable at `c`, `LinearMap.range (T ^ d) = LinearMap.range (T ^ c)` for every
`d ≥ c`. -/
theorem IsStableAt.range_pow_eq_of_le {T : End R M} {c d : ℕ} (h : T.IsStableAt c) (hcd : c ≤ d) :
    LinearMap.range (T ^ d) = LinearMap.range (T ^ c) := by
  rw [← Nat.add_sub_of_le hcd, LinearMap.range_pow_add_eq_of_range_pow_succ_eq h.range_pow_succ_eq]

/-- Stability at exponent `c` persists at every larger exponent `d ≥ c`. -/
theorem IsStableAt.mono {T : End R M} {c d : ℕ} (h : T.IsStableAt c) (hcd : c ≤ d) :
    T.IsStableAt d :=
  isStableAt_iff_isCompl_and_bijective_restrict_range_pow.mpr
    ⟨h.one_le.trans hcd, by
      rw [h.ker_pow_eq_of_le hcd, h.range_pow_eq_of_le hcd]
      exact h.isCompl_ker_pow_range_pow,
      LinearMap.bijective_restrict_of_eq (h.range_pow_eq_of_le hcd).symm
        h.bijective_restrict_range_pow⟩

/-- If `T` is stable at `c`, the eventual kernel `⨆ n, LinearMap.ker (T ^ n)` equals
`LinearMap.ker (T ^ c)`. -/
theorem IsStableAt.iSup_ker_pow_eq {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    (⨆ n, LinearMap.ker (T ^ n)) = LinearMap.ker (T ^ c) :=
  LinearMap.iSup_ker_pow_eq_of_ker_pow_succ_eq h.ker_pow_succ_eq

/-- If `T` is stable at `c`, the stable range `⨅ n, LinearMap.range (T ^ n)` equals
`LinearMap.range (T ^ c)`. -/
theorem IsStableAt.iInf_range_pow_eq {T : End R M} {c : ℕ} (h : T.IsStableAt c) :
    (⨅ n, LinearMap.range (T ^ n)) = LinearMap.range (T ^ c) :=
  LinearMap.iInf_range_pow_eq_of_range_pow_succ_eq h.range_pow_succ_eq

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Over a ring, `T` is stable at `c` if and only if `1 ≤ c` and `LinearMap.ker (T ^ c)` and
`LinearMap.range (T ^ c)` are complementary submodules of `M`. -/
theorem isStableAt_iff_isCompl_ker_pow_range_pow {T : End R M} {c : ℕ} :
    T.IsStableAt c ↔ 1 ≤ c ∧ IsCompl (LinearMap.ker (T ^ c)) (LinearMap.range (T ^ c)) := by
  constructor
  · exact fun h ↦ ⟨h.one_le, h.isCompl_ker_pow_range_pow⟩
  · rintro ⟨hc, hcompl⟩
    refine ⟨hc, LinearMap.range (T ^ c), fun _ hx ↦ T.mapsTo_range_pow c hx, hcompl, ?_⟩
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      have hTy : T y.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      exact Subtype.ext
        (Submodule.disjoint_def.mp hcompl.disjoint y.1
          (T.iterateKer.monotone hc (by simpa using hTy)) y.2)
    · intro y
      obtain ⟨x, hy⟩ := y.2
      have hx : x ∈ LinearMap.ker (T ^ c) ⊔ LinearMap.range (T ^ c) := by
        rw [hcompl.codisjoint.eq_top]
        exact Submodule.mem_top
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨w, rfl⟩ := hv
      refine ⟨⟨(T ^ c) ((T ^ (c - 1)) w), LinearMap.mem_range_self _ _⟩, Subtype.ext ?_⟩
      simp only [LinearMap.coe_restrict_apply, ← hy, map_add, LinearMap.mem_ker.mp hu, zero_add,
        ← mul_apply_eq_comp, ← pow_succ', ← pow_add]
      congr 2
      omega

/-- An endomorphism is stable if and only if both its iterate-kernel chain and its iterate-range
chain stop at some stage `c` (not necessarily positive: if they stop at `0`, they also stop at
`1`). -/
theorem isStable_iff_exists_ker_pow_eq_and_range_pow_eq {T : End R M} :
    T.IsStable ↔ ∃ c, LinearMap.ker (T ^ (c + 1)) = LinearMap.ker (T ^ c) ∧
      LinearMap.range (T ^ (c + 1)) = LinearMap.range (T ^ c) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.ker_pow_succ_eq, hc.range_pow_succ_eq⟩
  · rintro ⟨c, hker, hrange⟩
    refine ⟨c + 1, isStableAt_iff_isCompl_ker_pow_range_pow.mpr ⟨Nat.succ_le_succ c.zero_le, ?_⟩⟩
    have hker' : LinearMap.ker (T ^ (c + 1 + 1)) = LinearMap.ker (T ^ (c + 1)) := by
      rw [LinearMap.ker_pow_add_eq_of_ker_pow_succ_eq hker 2, hker]
    have hrange' : LinearMap.range (T ^ (c + 1 + 1)) = LinearMap.range (T ^ (c + 1)) := by
      rw [LinearMap.range_pow_add_eq_of_range_pow_succ_eq hrange 2, hrange]
    exact ⟨LinearMap.disjoint_ker_pow_range_pow_of_ker_pow_succ_eq hker',
      LinearMap.codisjoint_ker_pow_range_pow_of_range_pow_succ_eq hrange'⟩

/-- Fitting-type characterization of stability: `T` is stable if and only if
`⨆ n, LinearMap.ker (T ^ n)` and `⨅ n, LinearMap.range (T ^ n)` are complementary submodules,
`T` is nilpotent on `⨆ n, LinearMap.ker (T ^ n)`, and `T` is bijective on
`⨅ n, LinearMap.range (T ^ n)`. -/
theorem isStable_iff_isCompl_and_isNilpotent_and_bijective {T : End R M} :
    T.IsStable ↔
      IsCompl (⨆ n, LinearMap.ker (T ^ n)) (⨅ n, LinearMap.range (T ^ n)) ∧
        IsNilpotent (T.restrict fun _ hx ↦ T.mapsTo_iSup_ker_pow hx) ∧
        Function.Bijective (T.restrict fun _ hx ↦ T.mapsTo_iInf_range_pow hx) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨?_, ?_,
      LinearMap.bijective_restrict_of_eq hc.iInf_range_pow_eq.symm hc.bijective_restrict_range_pow⟩
    · rw [hc.iSup_ker_pow_eq, hc.iInf_range_pow_eq]
      exact hc.isCompl_ker_pow_range_pow
    · refine ⟨c, ?_⟩
      rw [Module.End.pow_restrict c]
      ext x
      have hx : x.1 ∈ LinearMap.ker (T ^ c) := hc.iSup_ker_pow_eq ▸ x.2
      exact LinearMap.mem_ker.mp hx
  · rintro ⟨hcompl, ⟨c, hnil⟩, hbij⟩
    have hker_eq : (⨆ n, LinearMap.ker (T ^ n)) = LinearMap.ker (T ^ (c + 1)) := by
      refine le_antisymm (fun x hx ↦ ?_) (le_iSup (fun n ↦ LinearMap.ker (T ^ n)) (c + 1))
      have hnil' : (T.restrict fun _ hy ↦ T.mapsTo_iSup_ker_pow hy) ^ (c + 1) = 0 := by
        rw [pow_succ, hnil, zero_mul]
      rw [Module.End.pow_restrict (c + 1)] at hnil'
      have hx0 := LinearMap.congr_fun hnil' ⟨x, hx⟩
      exact LinearMap.mem_ker.mpr (congrArg Subtype.val hx0)
    refine ⟨c + 1, Nat.succ_le_succ c.zero_le, ⨅ n, LinearMap.range (T ^ n),
      fun _ hx ↦ T.mapsTo_iInf_range_pow hx, hker_eq ▸ hcompl, hbij⟩

/-- For a stable endomorphism `T`, the eventual kernel `⨆ n, LinearMap.ker (T ^ n)` and stable range
`⨅ n, LinearMap.range (T ^ n)` are complementary submodules. -/
theorem IsStable.isCompl_iSup_ker_pow_iInf_range_pow {T : End R M} (h : T.IsStable) :
    IsCompl (⨆ n, LinearMap.ker (T ^ n)) (⨅ n, LinearMap.range (T ^ n)) :=
  (isStable_iff_isCompl_and_isNilpotent_and_bijective.mp h).1

/-- A stable endomorphism `T` restricts to a nilpotent endomorphism on
`⨆ n, LinearMap.ker (T ^ n)`. -/
theorem IsStable.isNilpotent_restrict_iSup_ker_pow {T : End R M} (h : T.IsStable) :
    IsNilpotent (T.restrict fun _ hx ↦ T.mapsTo_iSup_ker_pow hx) :=
  (isStable_iff_isCompl_and_isNilpotent_and_bijective.mp h).2.1

/-- A stable endomorphism `T` restricts to a bijection on `⨅ n, LinearMap.range (T ^ n)`. -/
theorem IsStable.bijective_restrict_iInf_range_pow {T : End R M} (h : T.IsStable) :
    Function.Bijective (T.restrict fun _ hx ↦ T.mapsTo_iInf_range_pow hx) :=
  (isStable_iff_isCompl_and_isNilpotent_and_bijective.mp h).2.2

/-- Fitting's lemma in stable-operator form: every endomorphism of a module that is both
Noetherian and Artinian is stable. -/
theorem IsStable.of_isNoetherian_of_isArtinian [IsNoetherian R M] [IsArtinian R M]
    (T : End R M) : T.IsStable := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow T)
  exact ⟨n + 1, isStableAt_iff_isCompl_ker_pow_range_pow.mpr
    ⟨Nat.succ_le_succ n.zero_le, hn (n + 1) (Nat.le_succ n)⟩⟩

/-- When `T` is stable, restricting the canonical localization map `M →ₗ[R] T.IterateDirectLimit`
to the stable range `⨅ n, LinearMap.range (T ^ n)` is bijective. -/
theorem IsStable.bijective_toIterateDirectLimit_comp_subtype {T : End R M} (h : T.IsStable) :
    Function.Bijective
      (T.toIterateDirectLimit ∘ₗ (⨅ n, LinearMap.range (T ^ n)).subtype) := by
  have ⟨c, hc⟩ := h
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      ← LinearMap.mem_ker, T.ker_toIterateDirectLimit] at hx
    exact Subtype.ext
      (Submodule.disjoint_def.mp h.isCompl_iSup_ker_pow_iInf_range_pow.disjoint x.1 hx x.2)
  · intro z
    obtain ⟨i, x, rfl⟩ := T.exists_ofIterateDirectLimitStage z
    let w : ↥(⨅ n, LinearMap.range (T ^ n)) :=
      ⟨(T ^ c) x, hc.iInf_range_pow_eq.symm ▸ LinearMap.mem_range_self (T ^ c) x⟩
    obtain ⟨v, hv⟩ := h.bijective_restrict_iInf_range_pow.surjective.iterate (i + c) w
    rw [← pow_apply_eq_iterate, Module.End.pow_restrict (i + c)] at hv
    have hv_val : (T ^ (i + c)) v.1 = (T ^ c) x := congrArg Subtype.val hv
    refine ⟨v, ?_⟩
    rw [LinearMap.comp_apply, Submodule.coe_subtype, ← T.ofIterateDirectLimitStage_pow (i + c),
      hv_val, T.ofIterateDirectLimitStage_add_pow i c x]

/-- For a stable endomorphism `T`, the canonical localization map restricts to an `R`-linear
isomorphism from the stable range `⨅ n, LinearMap.range (T ^ n)` onto `T.IterateDirectLimit`. -/
noncomputable def IsStable.iInfRangePowEquivIterateDirectLimit {T : End R M} (h : T.IsStable) :
    ↥(⨅ n, LinearMap.range (T ^ n)) ≃ₗ[R] T.IterateDirectLimit :=
  LinearEquiv.ofBijective
    (T.toIterateDirectLimit ∘ₗ (⨅ n, LinearMap.range (T ^ n)).subtype)
    h.bijective_toIterateDirectLimit_comp_subtype

/-- Evaluating `IsStable.iInfRangePowEquivIterateDirectLimit` applies `toIterateDirectLimit` to the
underlying vector. -/
@[simp]
theorem IsStable.iInfRangePowEquivIterateDirectLimit_apply {T : End R M} (h : T.IsStable)
    (x : ↥(⨅ n, LinearMap.range (T ^ n))) :
    h.iInfRangePowEquivIterateDirectLimit x = T.toIterateDirectLimit x.1 :=
  (rfl)

/-- `IsStable.iInfRangePowEquivIterateDirectLimit` intertwines the restriction of `T` to
`⨅ n, LinearMap.range (T ^ n)` with the canonical automorphism `T.iterateDirectLimitEquiv`. -/
theorem IsStable.iInfRangePowEquivIterateDirectLimit_restrict {T : End R M} (h : T.IsStable)
    (x : ↥(⨅ n, LinearMap.range (T ^ n))) :
    h.iInfRangePowEquivIterateDirectLimit
        (T.restrict (fun _ hx ↦ T.mapsTo_iInf_range_pow hx) x) =
      T.iterateDirectLimitEquiv (h.iInfRangePowEquivIterateDirectLimit x) := by
  rw [IsStable.iInfRangePowEquivIterateDirectLimit_apply,
    IsStable.iInfRangePowEquivIterateDirectLimit_apply, LinearMap.coe_restrict_apply,
    T.iterateDirectLimitEquiv_toIterateDirectLimit]

/-- Pulling back `T.toIterateDirectLimit` along `IsStable.iInfRangePowEquivIterateDirectLimit`
recovers the canonical Fitting projection `Submodule.projectionOnto` onto
`⨅ n, LinearMap.range (T ^ n)` along `⨆ n, LinearMap.ker (T ^ n)`. -/
theorem IsStable.iInfRangePowEquivIterateDirectLimit_symm_comp_toIterateDirectLimit
    {T : End R M} (h : T.IsStable) :
    h.iInfRangePowEquivIterateDirectLimit.symm.toLinearMap ∘ₗ T.toIterateDirectLimit =
      (⨅ n, LinearMap.range (T ^ n)).projectionOnto (⨆ n, LinearMap.ker (T ^ n))
        h.isCompl_iSup_ker_pow_iInf_range_pow.symm := by
  refine LinearMap.ext fun x ↦ h.iInfRangePowEquivIterateDirectLimit.injective ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    h.iInfRangePowEquivIterateDirectLimit.apply_symm_apply,
    h.iInfRangePowEquivIterateDirectLimit_apply, Submodule.coe_projectionOnto_apply]
  let hpq := h.isCompl_iSup_ker_pow_iInf_range_pow.symm
  let qProj := (⨆ n, LinearMap.ker (T ^ n)).projection (⨅ n, LinearMap.range (T ^ n)) hpq.symm x
  conv_lhs => rw [← Submodule.projection_add_projection_eq_self hpq x]
  have hker : T.toIterateDirectLimit qProj = 0 := by
    rw [← LinearMap.mem_ker, T.ker_toIterateDirectLimit]
    exact Submodule.projection_apply_mem hpq.symm x
  rw [map_add, hker, add_zero]

end Ring

end Module.End

end
