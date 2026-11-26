/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Filtering finitely supported functions supported on a set

Keeping the values of a finitely supported function `f` at the points satisfying a predicate `p`
(`Finsupp.filter p f`) sends functions supported on `s` to functions supported on `t`, as soon as
every point of `s` satisfying `p` lies in `t`. This file packages this operation as a linear map
between the submodules `Finsupp.supported M R s` and `Finsupp.supported M R t`; Mathlib's
`Finsupp.restrictDom` is the case of the predicate `(· ∈ t)` on the whole space.

A linear map from a finitely generated module into `α →₀ M` takes values in the functions supported
on one finite set (`LinearMap.exists_finset_support_subset`).

A finitely generated submodule of `ℕ →₀ M` consists of functions supported on an initial segment
`{i | i < n}`, since its finitely many generators have finite supports.

## Main definitions

* `TauCeti.Finsupp.filterSupported`: `Finsupp.filter p` as a linear map
  `Finsupp.supported M R s →ₗ[R] Finsupp.supported M R t`.

## Main results

* `LinearMap.exists_finset_support_subset`: the values of a linear map from a finitely
  generated module into `α →₀ M` have their supports in one finite set.
* `TauCeti.Finsupp.filterSupported_comp_inclusion`,
  `TauCeti.Finsupp.inclusion_comp_filterSupported`: the filter commutes with the inclusions
  `Finsupp.supported M R s ≤ Finsupp.supported M R s'` given by enlarging the support.
* `TauCeti.Finsupp.sum_filterSupported_eq`: summing `filterSupported (g · = b)` over all `b` in
  a finite decidable codomain recovers the original supported function.
* `Finsupp.sub_single_mem_supported`: removing the value at one exceptional coordinate leaves a
  function supported on a prescribed set.
* `Finsupp.map_mem_supported_of_forall_single_mem`: a linear map that sends the basis vectors
  over `s` into `supported N R t` maps `supported M R s` into it.
* `Finsupp.map_mem_supported_of_map_single_eq_smul_single`: an operator
  `single j 1 ↦ c j • single (σ j) 1` maps `supported R R s` into `supported R R t` when `c j`
  vanishes whenever `σ` moves `j ∈ s` out of `t`.
* `Finsupp.mem_supported_of_apply_eq_sum`, `Finsupp.filter_of_apply_eq_sum`: a map of free
  modules given by matrix coefficients preserves the functions supported on a set that no nonzero
  coefficient leaves, and commutes with filtering by a predicate that no nonzero coefficient
  crosses.
* `Submodule.FG.exists_le_supported_Iio`: a finitely generated submodule of `ℕ →₀ M` is
  supported on some initial segment.
* `Finsupp.exists_support_map_subset_range`: a linear map `(ℕ →₀ M) →ₗ[R] (ℕ →₀ N)` from a
  finitely generated module `M` sends sequences supported in `Finset.range n` into some
  `Finset.range m`.
* `Finsupp.exists_mem_supported_lt`: a finitely supported function is supported on the points
  of rank below some bound, for any rank function to `ℕ`.
-/

public section

noncomputable section

namespace TauCeti.Finsupp

open _root_.Finsupp

variable {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Finsupp.filter p` as a linear map from the functions supported on `s` to the functions
supported on `t`, where every point of `s` satisfying `p` lies in `t`. -/
def filterSupported {s t : Set α} (p : α → Prop) [DecidablePred p] (h : ∀ a ∈ s, p a → a ∈ t) :
    supported M R s →ₗ[R] supported M R t :=
  LinearMap.codRestrict _
    { toFun := fun f ↦ filter p f.val
      map_add' := fun _ _ ↦ filter_add
      map_smul' := fun _ _ ↦ filter_smul }
    fun f ↦ (mem_supported R _).2 fun a ha ↦ by
      have ha : a ∈ (filter p f.val).support := ha
      rw [support_filter, Finset.mem_filter] at ha
      exact h a ((mem_supported R f.val).1 f.property ha.1) ha.2

/-- `TauCeti.Finsupp.filterSupported p h` filters the underlying finitely supported function. -/
@[simp]
theorem filterSupported_apply {s t : Set α} (p : α → Prop) [DecidablePred p]
    (h : ∀ a ∈ s, p a → a ∈ t) (f : supported M R s) :
    (filterSupported p h f : α →₀ M) = filter p (f : α →₀ M) :=
  (rfl)

/-- Filtering a function supported on `s` after viewing it as supported on a larger set `s'` is
filtering it directly. -/
theorem filterSupported_comp_inclusion {s s' t : Set α} (p : α → Prop) [DecidablePred p]
    (hs : s ⊆ s') (h : ∀ a ∈ s', p a → a ∈ t) :
    (filterSupported p h).comp (Submodule.inclusion (supported_mono (M := M) (R := R) hs)) =
      filterSupported p fun a ha ↦ h a (hs ha) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- Viewing the filter of a function as supported on a larger set `t'` is filtering it with target
`t'` directly. -/
theorem inclusion_comp_filterSupported {s t t' : Set α} (p : α → Prop) [DecidablePred p]
    (h : ∀ a ∈ s, p a → a ∈ t) (ht : t ⊆ t') :
    (Submodule.inclusion (supported_mono (M := M) (R := R) ht)).comp (filterSupported p h) =
      filterSupported p fun a ha hp ↦ ht (h a ha hp) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- Decomposing a function supported on `s` by the fibers of a map `g : α → β` into a finite
decidable type and summing over `β` recovers the function. -/
theorem sum_filterSupported_eq {β : Type*} [Fintype β] [DecidableEq β] {s : Set α} (g : α → β)
    (f : supported M R s) :
    ∑ b : β, filterSupported (g · = b) (fun _ ha _ ↦ ha) f = f := by
  refine Subtype.ext (Finsupp.ext fun a ↦ ?_)
  simp [Finsupp.finsetSum_apply, Finsupp.filter_apply]

/-- **A finitely generated module maps into finitely many coordinates**: the values of a linear
map from a finitely generated module into `α →₀ M` are all supported on one finite set, the union
of the supports of the images of finitely many generators
(Mathlib's `Finsupp.span_le_supported_biUnion_support`). -/
theorem _root_.LinearMap.exists_finset_support_subset {N : Type*} [AddCommMonoid N] [Module R N]
    [Module.Finite R N] (f : N →ₗ[R] α →₀ M) : ∃ T : Finset α, ∀ y, (f y).support ⊆ T := by
  classical
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := N)
  refine ⟨Finset.univ.biUnion fun a ↦ (f (x a)).support, fun y t ht ↦ ?_⟩
  -- `f y` lies in the span of the images of the generators.
  have hy : f y ∈ Submodule.span R (Set.range (f ∘ x)) := by
    rw [Set.range_comp, ← Submodule.map_span, hx, Submodule.map_top]
    exact LinearMap.mem_range_self f y
  have hsupp := (Finsupp.mem_supported R _).1 (Finsupp.span_le_supported_biUnion_support R _ hy) ht
  simp only [Set.mem_iUnion, Set.mem_range, Function.comp_apply, exists_prop] at hsupp
  obtain ⟨_, ⟨a, rfl⟩, hta⟩ := hsupp
  exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hta⟩

end TauCeti.Finsupp

namespace Submodule.FG

variable {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated submodule of `ℕ →₀ M` consists of functions vanishing from some
coordinate on. -/
theorem exists_le_supported_Iio {V : Submodule R (ℕ →₀ M)} (hV : V.FG) :
    ∃ n, V ≤ Finsupp.supported M R (Set.Iio n) := by
  obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 hV
  obtain ⟨b, hb⟩ := (hS.biUnion fun x _ ↦ x.support.finite_toSet).bddAbove
  exact ⟨b + 1, (Finsupp.span_le_supported_biUnion_support R S).trans
    (Finsupp.supported_mono fun i hi ↦ Nat.lt_succ_of_le (hb hi))⟩

end Submodule.FG

namespace Finsupp

variable {α β M N : Type*} (R : Type*) [Semiring R]

/-- Removing the value at an exceptional coordinate `k` leaves a function supported on `s`, if
every other point of the support lies in `s`. -/
theorem sub_single_mem_supported [AddCommGroup M] [Module R M] {s : Set α} (v : α →₀ M) (k : α)
    (hv : ∀ j ∈ v.support, j ∈ s ∨ j = k) :
    v - single k (v k) ∈ supported M R s := by
  classical
  rw [← erase_eq_sub_single, mem_supported, support_erase]
  exact fun j hj ↦ (hv j (Finset.mem_of_mem_erase hj)).resolve_right (Finset.ne_of_mem_erase hj)

/-- A linear map sending every basis vector `single j x` with `j ∈ s` into `supported N R t` maps
`supported M R s` into `supported N R t`. -/
theorem map_mem_supported_of_forall_single_mem [AddCommMonoid M] [Module R M] [AddCommMonoid N]
    [Module R N] {s : Set α} {t : Set β} (f : (α →₀ M) →ₗ[R] (β →₀ N))
    (hf : ∀ j ∈ s, ∀ x, f (single j x) ∈ supported N R t) {v : α →₀ M}
    (hv : v ∈ supported M R s) : f v ∈ supported N R t := by
  rw [← sum_single v, map_finsuppSum]
  exact Submodule.sum_mem _ fun j hj ↦ hf j ((mem_supported R v).1 hv hj) _

/-- A linear map sending each `single j 1` to a multiple `c j • single (σ j) 1` maps
`supported R R s` into `supported R R t`, if `c j = 0` whenever `j ∈ s` and `σ j ∉ t`. -/
theorem map_mem_supported_of_map_single_eq_smul_single {s : Set α} {t : Set β}
    (f : (α →₀ R) →ₗ[R] (β →₀ R)) (c : α → R) (σ : α → β)
    (hf : ∀ j, f (single j 1) = c j • single (σ j) 1) (hc : ∀ j ∈ s, σ j ∉ t → c j = 0)
    {v : α →₀ R} (hv : v ∈ supported R R s) : f v ∈ supported R R t := by
  refine map_mem_supported_of_forall_single_mem R f (fun j hj x ↦ ?_) hv
  rw [← smul_single_one, map_smul, hf]
  by_cases h : σ j ∈ t
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (single_mem_supported R _ h))
  · rw [hc j hj h, zero_smul, smul_zero]
    exact zero_mem _

end Finsupp

namespace Finsupp

variable {α R : Type*} [Semiring R] {f : (α →₀ R) → α →₀ R} {k : α → α → R}

/-- A map of free modules with matrix coefficients `k x y` maps the functions supported on `s` to
functions supported on `s`, when no nonzero coefficient leads out of `s`. -/
theorem mem_supported_of_apply_eq_sum (hf : ∀ v y, f v y = v.sum fun x a => a * k x y)
    {s : Set α} (hs : ∀ x ∈ s, ∀ y, k x y ≠ 0 → y ∈ s) {v : α →₀ R}
    (hv : v ∈ supported R R s) : f v ∈ supported R R s := by
  rw [mem_supported']
  intro y hy
  rw [hf, Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [not_ne_iff.mp (mt (hs x ((mem_supported _ _).mp hv hx) y) hy), mul_zero]

/-- A map of free modules with matrix coefficients `k x y` commutes with restricting a function to
the points satisfying `p`, when no nonzero coefficient joins a point satisfying `p` to one that
does not. -/
theorem filter_of_apply_eq_sum (hf : ∀ v y, f v y = v.sum fun x a => a * k x y)
    {p : α → Prop} [DecidablePred p] (hk : ∀ x y, k x y ≠ 0 → (p x ↔ p y))
    (v : α →₀ R) : f (v.filter p) = (f v).filter p := by
  have hk' (x y : α) (hxy : ¬(p x ↔ p y)) : k x y = 0 :=
    not_imp_comm.mp (hk x y) hxy
  ext y
  rw [filter_apply, hf, hf, sum_of_support_subset _ (s := v.support)
    (by rw [support_filter]; exact Finset.filter_subset _ _) _ fun _ _ => zero_mul _, Finsupp.sum]
  split_ifs with hy
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [filter_apply]
    split_ifs with hx
    · rfl
    · rw [zero_mul, hk' x y (fun h => hx (h.mpr hy)), mul_zero]
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [filter_apply]
    split_ifs with hx
    · rw [hk' x y (fun h => hy (h.mp hx)), mul_zero]
    · rw [zero_mul]

end Finsupp

namespace Finsupp

/-- A linear map `(ℕ →₀ M) →ₗ[R] (ℕ →₀ N)` from a finitely generated module `M` sends sequences
supported in `Finset.range n` into some `Finset.range m`. -/
theorem exists_support_map_subset_range {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] (φ : (ℕ →₀ M) →ₗ[R] (ℕ →₀ N)) (n : ℕ) :
    ∃ m, ∀ u : ℕ →₀ M, u.support ⊆ Finset.range n → (φ u).support ⊆ Finset.range m := by
  choose T hT using fun j : ℕ ↦ (φ.comp (lsingle j)).exists_finset_support_subset
  refine ⟨((Finset.range n).biUnion T).sup id + 1, fun u hu ↦ Finset.coe_subset.1 <|
    (mem_supported R (φ u)).1 <| map_mem_supported_of_forall_single_mem R φ
      (fun j hj x ↦ (mem_supported R _).2 fun k hk ↦ ?_) ((mem_supported R u).2
        (Finset.coe_subset.2 hu))⟩
  exact Finset.mem_coe.2 <| Finset.mem_range.2 <| Nat.lt_succ_of_le <|
    Finset.le_sup (f := id) (Finset.mem_biUnion.2 ⟨j, Finset.mem_coe.1 hj, hT j x hk⟩)

/-- A finitely supported function is supported on the points of rank below some bound, for any
rank function to `ℕ`. -/
theorem exists_mem_supported_lt {α M R : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (r : α → ℕ) (f : α →₀ M) : ∃ k, f ∈ supported M R {y | r y < k} :=
  ⟨f.support.sup (r · + 1), fun _ hy ↦ Nat.lt_of_succ_le (Finset.le_sup (f := (r · + 1)) hy)⟩

end Finsupp
