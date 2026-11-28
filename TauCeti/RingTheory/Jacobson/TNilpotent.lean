/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Superfluous

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Left T-nilpotence and Nakayama's lemma for all modules

A subset `S` of a ring is **left T-nilpotent** (*transfinitely nilpotent*, after Bass) when every
sequence `a 0, a 1, a 2, …` of elements of `S` has a vanishing initial product
`a 0 * a 1 * ⋯ * a (n - 1) = 0`. Taking a constant sequence shows that a left T-nilpotent set is
nil, and a nilpotent ideal is left T-nilpotent, but neither implication reverses in general.

Nakayama's lemma says that `J • M` is superfluous in `M` when `J` is the Jacobson radical and `M`
is finitely generated. Left T-nilpotence is exactly what makes this hold for *every* left module,
with no finiteness assumption: this is Bass's characterization, which underlies projective covers
over left perfect rings.

## Main definitions

* `TauCeti.IsLeftTNilpotent`: every sequence in `S` has a vanishing initial product.

## Main results

* `TauCeti.IsLeftTNilpotent.isNilpotent`: the members of a left T-nilpotent set are nilpotent.
* `TauCeti.IsLeftTNilpotent.of_isNilpotent`: a nilpotent ideal is left T-nilpotent.
* `TauCeti.IsLeftTNilpotent.isSuperfluous_smul_top`: **Nakayama's lemma for all modules**. If the
  left ideal `J` is left T-nilpotent, then `J • M` is superfluous in every module `M`, in every
  universe; `TauCeti.IsLeftTNilpotent.subsingleton_of_smul_top_eq_top` is the form `J • M = M →
  M = 0`.
* `TauCeti.isSuperfluous_smul_top_of_isNilpotent`: the special case of a nilpotent ideal.
* `TauCeti.isLeftTNilpotent_of_isSuperfluous_smul_top_finsupp`: conversely, superfluity of `J • F`
  in the single free module `F = ℕ →₀ A` already forces left T-nilpotence. For a sequence `a` in
  `J` with no vanishing initial product, the submodule spanned by the `eᵢ - a i • eᵢ₊₁` supplements
  `J • F` without being all of `F` (Bass's module).
* `TauCeti.isLeftTNilpotent_tfae`: the four conditions agree.

## References

* H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  Trans. Amer. Math. Soc. 95 (1960), 466–488, pp. 473–474.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., 28.3.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., (23.16).
-/

public section

namespace TauCeti

universe u v

section MonoidWithZero

variable {A : Type u} [MonoidWithZero A]

/-- A subset `S` of a ring is **left T-nilpotent** when every sequence `a 0, a 1, …` of elements of
`S` has a vanishing initial product `a 0 * a 1 * ⋯ * a (n - 1)`. New factors enter on the right,
which is the side matching Nakayama's lemma for left modules
(`TauCeti.IsLeftTNilpotent.isSuperfluous_smul_top`). -/
def IsLeftTNilpotent (S : Set A) : Prop :=
  ∀ a : ℕ → A, (∀ i, a i ∈ S) → ∃ n, ((List.range n).map a).prod = 0

/-- Left T-nilpotence, restated: this is the introduction and elimination rule for
`TauCeti.IsLeftTNilpotent`, whose body is not exposed outside this module. -/
theorem isLeftTNilpotent_iff {S : Set A} :
    IsLeftTNilpotent S ↔ ∀ a : ℕ → A, (∀ i, a i ∈ S) → ∃ n, ((List.range n).map a).prod = 0 :=
  (Iff.rfl)

/-- A subset of a left T-nilpotent set is left T-nilpotent. -/
theorem IsLeftTNilpotent.mono {S T : Set A} (hT : IsLeftTNilpotent T) (h : S ⊆ T) :
    IsLeftTNilpotent S :=
  fun a ha ↦ hT a fun i ↦ h (ha i)

/-- Every member of a left T-nilpotent set is nilpotent. -/
theorem IsLeftTNilpotent.isNilpotent {S : Set A} (hS : IsLeftTNilpotent S) {a : A} (ha : a ∈ S) :
    IsNilpotent a := by
  -- Apply the definition to the constant sequence at `a`.
  obtain ⟨n, hn⟩ := hS (fun _ ↦ a) fun _ ↦ ha
  exact ⟨n, by simpa [List.map_const', List.prod_replicate] using hn⟩

end MonoidWithZero

section Semiring

variable {A : Type u} {M : Type v} [Semiring A] [AddCommMonoid M] [Module A M]

/-- A nilpotent ideal is left T-nilpotent. -/
theorem IsLeftTNilpotent.of_isNilpotent {I : Ideal A} (hI : IsNilpotent I) :
    IsLeftTNilpotent (I : Set A) := by
  obtain ⟨n, hn⟩ := hI
  intro a ha
  refine ⟨n, ?_⟩
  -- The product of the first `k` terms of a sequence in `I` lies in `I ^ k`.
  have key : ∀ k, ((List.range k).map a).prod ∈ I ^ k := by
    intro k
    induction k with
    | zero => simp [Submodule.pow_zero]
    | succ k ih =>
      rw [List.prod_range_succ, Submodule.pow_succ]
      exact Ideal.mul_mem_mul ih (ha k)
  simpa [hn] using key n

/-- The step of Nakayama's lemma for all modules: if `J • ⊤ ⊔ K = ⊤` and `b • y ∉ K`, then some
`(b * a) • m` with `a ∈ J` is still outside `K`. The implication is stated inside the existential,
so that the witnesses can be chosen as total functions of `b` and `y`. -/
private theorem exists_mul_smul_notMem {J : Ideal A} {K : Submodule A M}
    (hK : J • (⊤ : Submodule A M) ⊔ K = ⊤) (b : A) (y : M) :
    ∃ a ∈ J, ∃ m : M, b • y ∉ K → (b * a) • m ∉ K := by
  by_cases hy : b • y ∈ K
  · exact ⟨0, J.zero_mem, 0, fun h ↦ (h hy).elim⟩
  by_contra! H
  apply hy
  -- Write `y = z + k` with `z ∈ J • ⊤` and `k ∈ K`; then `b • z ∈ K` because every `(b * a) • m`
  -- with `a ∈ J` is.
  obtain ⟨z, hz, k, hk, rfl⟩ := Submodule.mem_sup.mp (hK ▸ Submodule.mem_top : y ∈ _)
  rw [smul_add]
  refine K.add_mem ?_ (K.smul_mem b hk)
  refine Submodule.smul_induction_on (p := fun z ↦ b • z ∈ K) hz (fun a ha m _ ↦ ?_)
    fun x x' hx hx' ↦ by simpa only [smul_add] using K.add_mem hx hx'
  rw [smul_smul]
  exact (H a ha m).2

/-- **Nakayama's lemma for all modules.** If the left ideal `J` is left T-nilpotent, then `J • M`
is superfluous in every module `M`. Unlike `TauCeti.isSuperfluous_jacobson`, no finiteness of `M`
is needed; `TauCeti.isSuperfluous_smul_top_of_isNilpotent` is the special case of a nilpotent
ideal. -/
theorem IsLeftTNilpotent.isSuperfluous_smul_top {J : Ideal A} (hJ : IsLeftTNilpotent (J : Set A)) :
    IsSuperfluous (J • (⊤ : Submodule A M)) := by
  refine isSuperfluous_iff.mpr fun K hK ↦ ?_
  by_contra hne
  obtain ⟨y, -, hy⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  choose a ha m hm using exists_mul_smul_notMem hK
  -- Iterate the step: the state `(b, x)` records the running product `b` and an element `x` with
  -- `b • x ∉ K`.
  let s : ℕ → A × M := fun n ↦ Nat.rec (1, y) (fun _ p ↦ (p.1 * a p.1 p.2, m p.1 p.2)) n
  -- The defining equations of the recursion, which hold by `Nat.rec`'s computation rules.
  have hs0 : s 0 = (1, y) := rfl
  have hs : ∀ n, s (n + 1) = ((s n).1 * a (s n).1 (s n).2, m (s n).1 (s n).2) := fun _ ↦ rfl
  have key : ∀ n, (s n).1 = ((List.range n).map fun i ↦ a (s i).1 (s i).2).prod ∧
      (s n).1 • (s n).2 ∉ K := by
    intro n
    induction n with
    | zero => exact ⟨by simp [hs0], by simpa [hs0] using hy⟩
    | succ n ih => exact ⟨by rw [hs, List.prod_range_succ, ← ih.1], by rw [hs]; exact hm _ _ ih.2⟩
  obtain ⟨n, hn⟩ := hJ _ fun i ↦ ha _ _
  have hnK := (key n).2
  rw [(key n).1, hn, zero_smul] at hnK
  exact hnK K.zero_mem

/-- **Nakayama's lemma for a nilpotent ideal.** If `I` is a nilpotent ideal, then `I • M` is
superfluous in every module `M`: a nilpotent ideal is left T-nilpotent
(`TauCeti.IsLeftTNilpotent.of_isNilpotent`). -/
theorem isSuperfluous_smul_top_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I) :
    IsSuperfluous (I • (⊤ : Submodule A M)) :=
  (IsLeftTNilpotent.of_isNilpotent hI).isSuperfluous_smul_top

/-- **Nakayama's lemma for all modules**, in the form `J • M = M → M = 0`: over a left
T-nilpotent left ideal `J`, no nonzero module satisfies `J • M = M`. -/
theorem IsLeftTNilpotent.subsingleton_of_smul_top_eq_top {J : Ideal A}
    (hJ : IsLeftTNilpotent (J : Set A)) (h : J • (⊤ : Submodule A M) = ⊤) : Subsingleton M :=
  (Submodule.subsingleton_iff A).mp (isSuperfluous_top_iff.mp (h ▸ hJ.isSuperfluous_smul_top))

end Semiring

section Ring

variable {A : Type u} [Ring A]

/-- The shift `eᵢ ↦ a i • eᵢ₊₁` on `ℕ →₀ A`, whose `id - bassShift a` has as range the submodule
spanned by the relations `eᵢ - a i • eᵢ₊₁` of Bass's module. -/
private noncomputable def bassShift (a : ℕ → A) : (ℕ →₀ A) →ₗ[A] ℕ →₀ A :=
  Finsupp.linearCombination A fun i ↦ Finsupp.single (i + 1) (a i)

private theorem bassShift_apply_zero (a : ℕ → A) (f : ℕ →₀ A) : bassShift a f 0 = 0 := by
  simp [bassShift, Finsupp.linearCombination_apply, Finsupp.sum_apply]

private theorem bassShift_apply_succ (a : ℕ → A) (f : ℕ →₀ A) (n : ℕ) :
    bassShift a f (n + 1) = f n * a n := by
  simp +contextual [bassShift, Finsupp.linearCombination_apply, Finsupp.sum_apply,
    Finsupp.single_apply]

/-- The range of the shift lies in `J • ⊤` when the sequence lies in `J`. -/
private theorem bassShift_mem_smul_top {J : Ideal A} {a : ℕ → A} (ha : ∀ i, a i ∈ J)
    (f : ℕ →₀ A) : bassShift a f ∈ J • (⊤ : Submodule A (ℕ →₀ A)) := by
  have hle : LinearMap.range (bassShift a) ≤ J • (⊤ : Submodule A (ℕ →₀ A)) := by
    rw [bassShift, Finsupp.range_linearCombination, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using Submodule.smul_mem_smul (ha i)
      (Submodule.mem_top (x := Finsupp.single (i + 1) (1 : A)))
  exact hle (LinearMap.mem_range_self _ f)

/-- If `J • (ℕ →₀ A)` is superfluous in the free module `ℕ →₀ A`, then the left ideal `J` is left
T-nilpotent. Together with `TauCeti.IsLeftTNilpotent.isSuperfluous_smul_top`, a single countably
generated free module detects left T-nilpotence. -/
theorem isLeftTNilpotent_of_isSuperfluous_smul_top_finsupp {J : Ideal A}
    (h : IsSuperfluous (J • (⊤ : Submodule A (ℕ →₀ A)))) : IsLeftTNilpotent (J : Set A) := by
  intro a ha
  by_contra! hne
  -- Bass's module: for a sequence `a` in `J` without vanishing initial product, the submodule
  -- `D (ℕ →₀ A)` spanned by the `eᵢ - a i • eᵢ₊₁` supplements `J • (ℕ →₀ A)`, yet a preimage `f`
  -- of `e₀` would have `f n = a 0 * ⋯ * a (n - 1) ≠ 0` for every `n`.
  set D : (ℕ →₀ A) →ₗ[A] ℕ →₀ A := LinearMap.id - bassShift a with hD
  have hsup : J • ⊤ ⊔ LinearMap.range D = ⊤ := by
    refine eq_top_iff.mpr fun f _ ↦ ?_
    have hf : f = bassShift a f + D f := by simp [hD]
    rw [hf]
    exact Submodule.add_mem_sup (bassShift_mem_smul_top ha f) (LinearMap.mem_range_self _ f)
  obtain ⟨f, hf⟩ : Finsupp.single 0 1 ∈ LinearMap.range D :=
    h.eq_top_of_sup_eq_top hsup ▸ Submodule.mem_top
  -- Reading `f - bassShift a f = e₀` coefficientwise gives `f 0 = 1` and `f (n + 1) = f n * a n`.
  have hcoef : ∀ n, f n = ((List.range n).map a).prod := by
    intro n
    induction n with
    | zero => simpa [hD, bassShift_apply_zero] using congrArg (· 0) hf
    | succ n ih =>
      have hn := congrArg (· (n + 1)) hf
      simp only [hD, LinearMap.sub_apply, LinearMap.id_apply, Finsupp.sub_apply,
        bassShift_apply_succ, Finsupp.single_apply] at hn
      rw [List.prod_range_succ, ← ih]
      simpa [sub_eq_zero] using hn
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset f.support
  exact hne n (hcoef n ▸ Finsupp.notMem_support_iff.mp hn)

/-- **Bass's characterization of left T-nilpotence** (Nakayama's lemma for all modules). For a left
ideal `J` of `A`, the following are equivalent:
1. `J` is left T-nilpotent;
2. `J • M = M` forces `M = 0` for every module `M`;
3. `J • M` is superfluous in every module `M`;
4. `J • (ℕ →₀ A)` is superfluous in the free module `ℕ →₀ A`.

The modules range over the universe of `A`; the implications from (1) hold in every universe
(`TauCeti.IsLeftTNilpotent.isSuperfluous_smul_top`,
`TauCeti.IsLeftTNilpotent.subsingleton_of_smul_top_eq_top`). -/
theorem isLeftTNilpotent_tfae (J : Ideal A) :
    List.TFAE
      [IsLeftTNilpotent (J : Set A),
        ∀ (M : Type u) [AddCommGroup M] [Module A M], J • (⊤ : Submodule A M) = ⊤ → Subsingleton M,
        ∀ (M : Type u) [AddCommGroup M] [Module A M], IsSuperfluous (J • (⊤ : Submodule A M)),
        IsSuperfluous (J • (⊤ : Submodule A (ℕ →₀ A)))] := by
  tfae_have 1 → 2 := fun hJ _ _ _ ↦ hJ.subsingleton_of_smul_top_eq_top
  tfae_have 2 → 3 := by
    -- A supplement `K` of `J • M` makes `J • (M ⧸ K) = M ⧸ K`, so `M ⧸ K = 0`.
    intro h M _ _
    refine isSuperfluous_iff.mpr fun K hK ↦ ?_
    have hq : J • (⊤ : Submodule A (M ⧸ K)) = ⊤ := by
      have hmap := (Submodule.map_mkQ_eq_top K _).mpr (sup_comm K _ ▸ hK)
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap
    have := h _ hq
    exact Submodule.Quotient.subsingleton_iff.mp this
  tfae_have 3 → 4 := fun h ↦ h _
  tfae_have 4 → 1 := isLeftTNilpotent_of_isSuperfluous_smul_top_finsupp
  tfae_finish

end Ring

end TauCeti
