/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.RingTheory.AdicCompletion.Principal
import Mathlib.Algebra.FiveLemma
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Exact.Pi
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.AdicCompletion.Nilpotent

/-!
# Derived completeness of modules

Let `I` be an ideal of a commutative ring `R`. For `f ∈ R`, the *telescope* map
`(xₙ) ↦ (xₙ - f • xₙ₊₁)` on sequences `ℕ → M` is the shift map `TauCeti.ModuleTower.shift` of the
tower `M ←f M ←f ⋯` (`TauCeti.ModuleTower.shift_smulTower`), so its kernel and cokernel are the
`lim` and `lim¹` of this tower. A module `M` is *derived `I`-complete* when the telescope map is
bijective for every `f ∈ I`, that is, when `lim` and `lim¹` of every tower `M ←f M ←f ⋯` with
`f ∈ I` vanish (`TauCeti.isDerivedComplete_iff_lim_eq_bot_and_subsingleton_limOne`). Since the
derived limit of this tower is `RHom_R(R[1/f], M)`, this is the condition `RHom_R(R[1/f], M) = 0`
for all `f ∈ I` (Stacks, Tag 091P), stated without derived categories.

Derived completeness is a homological replacement for classical completeness that behaves well
in exact sequences. Derived complete modules are closed under kernels, cokernels, extensions and
arbitrary products, although not under submodules (`ℤ ⊆ ℤ_[p]`). A classically `I`-adically
complete module is derived `I`-complete. Conversely, for a finitely generated ideal `I`, a
derived complete module is `I`-adically precomplete, so it is classically complete exactly when
it is `I`-adically Hausdorff; Bhatt and Scholze give a derived complete module which is not
Hausdorff. Derived completeness is not closed under direct sums: if `f` is a non-zero-divisor and
not a unit, the free module `⊕_ℕ R` is not derived `f`-complete, although `R` is when it is
`f`-adically complete.

## Main definitions

* `TauCeti.telescope M f`: the map `(xₙ) ↦ (xₙ - f • xₙ₊₁)` on `ℕ → M`.
* `TauCeti.IsDerivedComplete I M`: `M` is derived `I`-complete.

## Main results

* `TauCeti.isDerivedComplete_iff_lim_eq_bot_and_subsingleton_limOne`: `M` is derived
  `I`-complete if and only if every tower `M ←f M ←f ⋯` with `f ∈ I` has vanishing `lim` and
  `lim¹`.
* `TauCeti.IsDerivedComplete.ker`, `TauCeti.IsDerivedComplete.quotient_range`,
  `TauCeti.IsDerivedComplete.of_exact`: kernels, cokernels and extensions of derived complete
  modules are derived complete.
* `TauCeti.IsDerivedComplete.pi`: products of derived complete modules are derived complete.
* `TauCeti.IsDerivedComplete.of_isAdicComplete`: an `I`-adically complete module is derived
  `I`-complete.
* `TauCeti.IsDerivedComplete.isPrecomplete`: for a finitely generated ideal, a derived complete
  module is `I`-adically precomplete.
* `TauCeti.isAdicComplete_iff_isDerivedComplete_and_isHausdorff`: for a finitely generated ideal,
  a module is `I`-adically complete if and only if it is derived complete and `I`-adically
  Hausdorff.
* `TauCeti.not_isDerivedComplete_finsupp`: `⊕_ℕ R` is not derived `f`-complete when `f` is a
  non-zero-divisor and not a unit.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Section 3.4, Definition 3.4.1, Proposition 3.4.2, Remark 3.4.3 and Lemma 3.4.14.
* [Stacks Project, Section 15.93, Tag 091N](https://stacks.math.columbia.edu/tag/091N), in
  particular Lemma 15.93.1 (Tag 091P) for the telescope description.
-/

public section

open Finset Function

namespace TauCeti

variable {R : Type*} [CommRing R] {I J : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

section Telescope

variable (M) in
/-- The telescope map `(xₙ) ↦ (xₙ - f • xₙ₊₁)` on sequences in `M`. It is the shift map of the
tower `M ←f M ←f ⋯` (`TauCeti.ModuleTower.shift_smulTower`), so its kernel and cokernel are the
`lim` and `lim¹` of this tower. -/
def telescope (f : R) : (ℕ → M) →ₗ[R] (ℕ → M) :=
  LinearMap.id - f • LinearMap.funLeft R M Nat.succ

/-- The `n`-th term of the telescope of `x` is `xₙ - f • xₙ₊₁`. -/
@[simp]
theorem telescope_apply (f : R) (x : ℕ → M) (n : ℕ) :
    telescope M f x n = x n - f • x (n + 1) :=
  (rfl)

/-- The telescope map of `0` is the identity. -/
@[simp]
theorem telescope_zero : telescope M (0 : R) = LinearMap.id := by
  ext x n
  simp

/-- The telescope map commutes with a linear map applied termwise. -/
theorem compLeft_comp_telescope (f : R) (g : M →ₗ[R] N) :
    g.compLeft ℕ ∘ₗ telescope M f = telescope N f ∘ₗ g.compLeft ℕ := by
  ext x n
  simp

/-- A sequence `z` with `zₖ - f • zₖ₊₁ = cₖ` is determined by its later terms through the partial
sums `zₖ = ∑_{j < n} fʲ • cₖ₊ⱼ + fⁿ • zₖ₊ₙ`. -/
theorem eq_sum_range_add_pow_smul_of_telescope_eq {f : R} {z c : ℕ → M}
    (h : telescope M f z = c) (k n : ℕ) :
    z k = ∑ j ∈ range n, f ^ j • c (k + j) + f ^ n • z (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z (k + n) = c (k + n) + f • z (k + n + 1) := by
      rw [← h, telescope_apply, sub_add_cancel]
    rw [ih, hn, smul_add, smul_smul, ← pow_succ, sum_range_succ, add_assoc, add_assoc]

/-- The telescope map of `f` is the shift map of the tower `M ←f M ←f ⋯`. -/
theorem ModuleTower.shift_smulTower (f : R) :
    (ModuleTower.smulTower M f).shift = telescope M f := by
  ext x n
  rw [ModuleTower.shift_apply, ModuleTower.smulTower_transition]
  -- `x` is a sequence in the carrier of `ModuleCat.of R M`, which is `M` by definition; the
  -- `LinearMap.smul_apply` and `telescope_apply` rewrites do not fire across this identification
  rfl

end Telescope

variable (I M) in
/-- A module `M` is *derived `I`-complete* when for every `f ∈ I` the telescope map
`(xₙ) ↦ (xₙ - f • xₙ₊₁)` on `ℕ → M` is bijective, that is, when the tower `M ←f M ←f ⋯` has
vanishing `lim` and `lim¹`. By Stacks, Tag 091P, this says that `RHom_R(R[1/f], M) = 0` for
every `f ∈ I`. -/
def IsDerivedComplete : Prop :=
  ∀ f ∈ I, Bijective (telescope M f)

/-- The defining property of derived completeness. -/
theorem isDerivedComplete_iff :
    IsDerivedComplete I M ↔ ∀ f ∈ I, Bijective (telescope M f) :=
  Iff.rfl

/-- A module `M` is derived `I`-complete exactly when for every `f ∈ I` the tower
`M ←f M ←f ⋯` has vanishing `lim` and `lim¹`. -/
theorem isDerivedComplete_iff_lim_eq_bot_and_subsingleton_limOne :
    IsDerivedComplete I M ↔ ∀ f ∈ I, (ModuleTower.smulTower M f).lim = ⊥ ∧
      Subsingleton (ModuleTower.smulTower M f).limOne := by
  refine forall₂_congr fun f _ ↦ ?_
  rw [ModuleTower.lim_eq_ker, LinearMap.ker_eq_bot, ModuleTower.subsingleton_limOne_iff,
    ModuleTower.shift_smulTower]
  rfl

namespace IsDerivedComplete

/-- For `f ∈ I`, the telescope map of `f` on a derived `I`-complete module is bijective. -/
theorem bijective (h : IsDerivedComplete I M) {f : R} (hf : f ∈ I) :
    Bijective (telescope M f) :=
  h f hf

/-- Derived completeness for an ideal implies derived completeness for every smaller ideal. -/
theorem of_le (h : IsDerivedComplete I M) (hJ : J ≤ I) : IsDerivedComplete J M :=
  fun f hf ↦ h f (hJ hf)

/-- Derived completeness is invariant under linear isomorphisms. -/
theorem of_linearEquiv (h : IsDerivedComplete I M) (e : M ≃ₗ[R] N) : IsDerivedComplete I N := by
  intro f hf
  have hc := compLeft_comp_telescope f e.symm.toLinearMap
  have he : Bijective (e.symm.toLinearMap.compLeft ℕ) :=
    ⟨e.symm.injective.comp_left, e.symm.surjective.comp_left⟩
  refine (Bijective.of_comp_iff' he _).1 ?_
  rw [← LinearMap.coe_comp, hc, LinearMap.coe_comp]
  exact (h.bijective hf).comp he

/-- Kernels of maps between derived complete modules are derived complete. -/
theorem ker (hM : IsDerivedComplete I M) (hN : IsDerivedComplete I N) (g : M →ₗ[R] N) :
    IsDerivedComplete I (LinearMap.ker g) := fun f hf ↦
  LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((LinearMap.ker g).subtype.compLeft ℕ) (g.compLeft ℕ)
    ((LinearMap.ker g).subtype.compLeft ℕ) (g.compLeft ℕ)
    (telescope _ f) (telescope M f) (telescope N f)
    (compLeft_comp_telescope f _) (compLeft_comp_telescope f g)
    (Exact.piMap fun _ ↦ LinearMap.exact_subtype_ker_map g)
    (Exact.piMap fun _ ↦ LinearMap.exact_subtype_ker_map g)
    (hM.bijective hf) (hN.bijective hf).1
    (Subtype.val_injective.comp_left) (Subtype.val_injective.comp_left)

/-- Cokernels of maps between derived complete modules are derived complete. -/
theorem quotient_range (hM : IsDerivedComplete I M) (hN : IsDerivedComplete I N)
    (g : M →ₗ[R] N) : IsDerivedComplete I (N ⧸ LinearMap.range g) := fun f hf ↦
  have hex : Exact (g.compLeft ℕ) ((LinearMap.range g).mkQ.compLeft ℕ) :=
    Exact.piMap (Z := fun _ : ℕ ↦ N ⧸ LinearMap.range g) fun _ ↦
      LinearMap.exact_map_mkQ_range g
  LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (g.compLeft ℕ) ((LinearMap.range g).mkQ.compLeft ℕ)
    (g.compLeft ℕ) ((LinearMap.range g).mkQ.compLeft ℕ)
    (telescope M f) (telescope N f) (telescope _ f)
    (compLeft_comp_telescope f g) (compLeft_comp_telescope f _) hex hex
    (hM.bijective hf).2 (hN.bijective hf)
    (Submodule.mkQ_surjective _).comp_left (Submodule.mkQ_surjective _).comp_left

/-- Extensions of derived complete modules are derived complete: in a short exact sequence
`0 → M₁ → M → M₂ → 0`, if `M₁` and `M₂` are derived complete then so is `M`. -/
theorem of_exact {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] {g : M₁ →ₗ[R] M} {g' : M →ₗ[R] M₂} (hg : Injective g) (hgg' : Exact g g')
    (hg' : Surjective g') (h₁ : IsDerivedComplete I M₁) (h₂ : IsDerivedComplete I M₂) :
    IsDerivedComplete I M := by
  intro f hf
  -- The five lemma, for the rows `0 → (ℕ → M₁) → (ℕ → M) → (ℕ → M₂) → 0`.
  have hex : Exact (g.compLeft ℕ) (g'.compLeft ℕ) := Exact.piMap fun _ ↦ hgg'
  have hex₀ := (LinearMap.exact_zero_iff_injective Unit (g.compLeft ℕ)).mpr hg.comp_left
  have hex₁ := (LinearMap.exact_zero_iff_surjective Unit (g'.compLeft ℕ)).mpr hg'.comp_left
  exact ⟨LinearMap.injective_of_surjective_of_injective_of_injective _ (g.compLeft ℕ)
      (g'.compLeft ℕ) _ (g.compLeft ℕ) (g'.compLeft ℕ) 0 (telescope M₁ f) (telescope M f)
      (telescope M₂ f) (by ext; simp) (compLeft_comp_telescope f g) (compLeft_comp_telescope f g')
      hex₀ hex hex₀ (surjective_to_subsingleton _) (h₁.bijective hf).1 (h₂.bijective hf).1,
    LinearMap.surjective_of_surjective_of_surjective_of_injective (g.compLeft ℕ)
      (g'.compLeft ℕ) _ (g.compLeft ℕ) (g'.compLeft ℕ) _ (telescope M₁ f) (telescope M f)
      (telescope M₂ f) 0 (compLeft_comp_telescope f g) (compLeft_comp_telescope f g')
      (by ext) hex₁ hex hex₁ (h₁.bijective hf).2 (h₂.bijective hf).2
      (fun _ _ _ ↦ Subsingleton.elim _ _)⟩

/-- Products of derived complete modules are derived complete. -/
theorem pi {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, IsDerivedComplete I (M i)) : IsDerivedComplete I (∀ i, M i) := by
  intro f hf
  refine ⟨fun x y hxy ↦ funext fun n ↦ funext fun i ↦ ?_, fun y ↦ ?_⟩
  · have := ((h i).bijective hf).1 (a₁ := fun n ↦ x n i) (a₂ := fun n ↦ y n i)
      (funext fun n ↦ by simpa using congr_fun (congr_fun hxy n) i)
    exact congr_fun this n
  · choose x hx using fun i ↦ ((h i).bijective hf).2 fun n ↦ y n i
    exact ⟨fun n i ↦ x i n, funext fun n ↦ funext fun i ↦ by simpa using congr_fun (hx i) n⟩

/-- In a derived `I`-complete module, every series `∑ fʲ • cⱼ` with `f ∈ I` has a sum `L` whose
remainder after `n` terms lies in `(f)ⁿ M`. -/
theorem exists_smodEq_sum_range (h : IsDerivedComplete I M) {f : R} (hf : f ∈ I) (c : ℕ → M) :
    ∃ L : M, ∀ n,
      (∑ j ∈ range n, f ^ j • c j) ≡ L [SMOD (Ideal.span {f} ^ n • ⊤ : Submodule R M)] := by
  obtain ⟨z, hz⟩ := (h.bijective hf).2 c
  refine ⟨z 0, fun n ↦ ?_⟩
  rw [eq_sum_range_add_pow_smul_of_telescope_eq hz 0 n]
  simp only [zero_add]
  rw [SModEq.sub_mem, sub_add_cancel_left]
  exact Submodule.neg_mem _ (Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) n) trivial)

/-- An `I`-adically complete module is derived `I`-complete. -/
theorem of_isAdicComplete [IsAdicComplete I M] : IsDerivedComplete I M := by
  intro f hf
  have : IsHausdorff (Ideal.span {f}) M := IsHausdorff.of_le (I.span_singleton_le_iff_mem.2 hf)
  have hmem (n : ℕ) (x : M) : f ^ n • x ∈ (Ideal.span {f} ^ n • ⊤ : Submodule R M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self f) n) trivial
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ funext fun k ↦ ?_, fun c ↦ ?_⟩
  · -- A sequence killed by the telescope map has `zₖ = fⁿ • zₖ₊ₙ` for every `n`.
    refine IsHausdorff.haus this _ fun n ↦ ?_
    rw [eq_sum_range_add_pow_smul_of_telescope_eq hz k n]
    simpa [SModEq.sub_mem] using hmem n (z (k + n))
  · -- Sum the tails `∑ⱼ fʲ • cₖ₊ⱼ` and compare `Lₖ` with `cₖ + f • Lₖ₊₁` modulo every `(f)ⁿ`.
    choose L hL using fun k ↦ IsAdicComplete.exists_smodEq_sum_range hf fun j ↦ c (k + j)
    refine ⟨L, funext fun k ↦ (IsHausdorff.eq_iff_smodEq (I := Ideal.span {f})).2 fun n ↦ ?_⟩
    have h₁ := (hL k (n + 1)).mono
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ))
    have h₂ := (hL (k + 1) n).smul f
    rw [sum_range_succ'] at h₁
    have hsum : ∑ j ∈ range n, f ^ (j + 1) • c (k + (j + 1)) =
        f • ∑ j ∈ range n, f ^ j • c (k + 1 + j) := by
      simp only [smul_sum, smul_smul, pow_succ', add_assoc, add_comm 1]
    rw [hsum, pow_zero, one_smul, add_zero] at h₁
    rw [telescope_apply]
    have h := h₁.symm.sub h₂.symm
    rwa [add_sub_cancel_left] at h

/-- A module annihilated by a power of `I` is derived `I`-complete. -/
theorem of_pow_smul_eq_bot {k : ℕ} (hk : I ^ k • (⊤ : Submodule R M) = ⊥) :
    IsDerivedComplete I M :=
  have := isAdicComplete_of_pow_smul_eq_bot hk
  of_isAdicComplete

end IsDerivedComplete

/-- Every module is derived complete for the zero ideal. -/
@[simp]
theorem isDerivedComplete_bot : IsDerivedComplete (⊥ : Ideal R) M := by
  intro f hf
  rw [Ideal.mem_bot.1 hf, telescope_zero]
  exact bijective_id

/-- Only the zero module is derived complete for the unit ideal: a constant sequence is killed by
the telescope map of `1`. -/
@[simp]
theorem isDerivedComplete_top_iff : IsDerivedComplete (⊤ : Ideal R) M ↔ Subsingleton M := by
  refine ⟨fun h ↦ ⟨fun x y ↦ ?_⟩, fun _ f _ ↦ ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun y ↦ ⟨y, Subsingleton.elim _ _⟩⟩⟩
  have := (h.bijective (Submodule.mem_top (x := 1))).1 (a₁ := fun _ ↦ x) (a₂ := fun _ ↦ y)
    (by ext; simp)
  exact congr_fun this 0

/-- For a finitely generated ideal `I`, a derived `I`-complete module is `I`-adically
precomplete: every `I`-adic Cauchy sequence has a limit. -/
theorem IsDerivedComplete.isPrecomplete (h : IsDerivedComplete I M) (hI : I.FG) :
    IsPrecomplete I M := by
  classical
  obtain ⟨s, hs⟩ := hI
  set v : s → R := Subtype.val
  have hv (i : s) : v i ∈ I := hs ▸ Ideal.subset_span i.2
  -- Some power `I ^ b k` lies in the ideal generated by the `k`-th powers of the generators.
  have hpow (k : ℕ) : ∃ b, I ^ b ≤ Ideal.span (Set.range fun i ↦ v i ^ k) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ ⟨s, hs⟩
    rw [← hs, Ideal.span_le]
    exact fun g hg ↦ ⟨k, Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩⟩
  choose b hb using hpow
  -- A monotone reindexing `a` with `I ^ a k ≤ span {vᵢᵏ}` and `k ≤ a k`.
  let a (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (b k + 1)
  have ha_mono : Monotone a := fun m n hmn ↦
    sum_le_sum_of_subset (range_subset_range.2 (Nat.succ_le_succ hmn))
  have hb_le (n : ℕ) : b n ≤ a n :=
    (Nat.le_succ _).trans (single_le_sum (f := fun k ↦ b k + 1) (fun _ _ ↦ Nat.zero_le _)
      (self_mem_range_succ n))
  have hn_le (n : ℕ) : n ≤ a n := le_of_lt <| by
    simpa using card_nsmul_le_sum (range (n + 1)) (fun k ↦ b k + 1) 1 fun _ _ ↦ Nat.le_add_left _ _
  refine ⟨fun x hx ↦ ?_⟩
  -- Write the successive differences of `x ∘ a` as combinations of `k`-th powers of generators.
  have hd (k : ℕ) : ∃ m : s → M, ∑ i, v i ^ k • m i = x (a (k + 1)) - x (a k) :=
    Submodule.mem_span_range_smul_top_iff_exists_fun.1 <| Submodule.smul_mono_left
      ((Ideal.pow_le_pow_right (hb_le k)).trans (hb k))
      (SModEq.sub_mem.1 (hx (ha_mono k.le_succ)).symm)
  choose m hm using hd
  -- Sum the resulting series separately for each generator.
  choose y hy using fun i ↦ h.exists_smodEq_sum_range (hv i) fun k ↦ m k i
  refine ⟨x (a 0) + ∑ i, y i, fun n ↦ (hx (hn_le n)).trans ?_⟩
  have htel : x (a n) = x (a 0) + ∑ i, ∑ k ∈ range n, v i ^ k • m k i := by
    rw [sum_comm, sum_congr rfl fun k _ ↦ hm k, sum_range_sub (fun k ↦ x (a k)),
      add_sub_cancel]
  rw [htel]
  refine (SModEq.refl _).add (SModEq.sum fun i _ ↦ (hy i n).mono ?_)
  exact Submodule.smul_mono_left (Ideal.pow_right_mono (I.span_singleton_le_iff_mem.2 (hv i)) n)

/-- **Classical and derived completeness.** For a finitely generated ideal `I`, a module is
`I`-adically complete if and only if it is derived `I`-complete and `I`-adically Hausdorff. -/
theorem isAdicComplete_iff_isDerivedComplete_and_isHausdorff (hI : I.FG) :
    IsAdicComplete I M ↔ IsDerivedComplete I M ∧ IsHausdorff I M :=
  ⟨fun _ ↦ ⟨.of_isAdicComplete, inferInstance⟩, fun ⟨h, hH⟩ ↦
    { toIsHausdorff := hH, toIsPrecomplete := h.isPrecomplete hI }⟩

/-- Derived completeness is not closed under direct sums: if `f` is a non-zero-divisor and not a
unit, the free module `⊕_ℕ R` is not derived `f`-complete. The sequence of basis vectors is not
a telescope difference, since the series `∑ₙ fⁿ • eₙ` would have to converge. -/
theorem not_isDerivedComplete_finsupp {f : R} (hf : f ∈ nonZeroDivisors R) (hu : ¬IsUnit f) :
    ¬IsDerivedComplete (Ideal.span {f}) (ℕ →₀ R) := by
  intro h
  obtain ⟨x, hx⟩ := (h.bijective (Ideal.mem_span_singleton_self f)).2
    fun n ↦ Finsupp.single n 1
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset (x 0).support
  -- The `k`-th coordinate of `x₀ = ∑_{j ≤ k} fʲ • eⱼ + fᵏ⁺¹ • xₖ₊₁` is `fᵏ (1 + f rₖ)`.
  have h₀ := congr($(eq_sum_range_add_pow_smul_of_telescope_eq hx 0 (k + 1)) k)
  rw [Finsupp.notMem_support_iff.1 hk, Finsupp.add_apply, Finset.sum_apply',
    sum_eq_single_of_mem k (self_mem_range_succ k) fun j _ hj ↦ by
      simp [hj]] at h₀
  simp only [zero_add, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h₀
  have h₁ : (1 + f * x (k + 1) k) * f ^ k = 0 := by rw [h₀]; ring
  rw [mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf k)] at h₁
  exact hu (.of_mul_eq_one (-x (k + 1) k) (by linear_combination -h₁))

end TauCeti
