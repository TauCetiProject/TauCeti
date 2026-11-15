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
* `Finsupp.sub_single_mem_supported`: removing the value at one exceptional coordinate leaves a
  function supported on a prescribed set.
* `Finsupp.map_mem_supported_of_forall_single_mem`: a linear map that sends the basis vectors
  over `s` into `supported N R t` maps `supported M R s` into it.
* `Submodule.FG.exists_le_supported_Iio`: a finitely generated submodule of `ℕ →₀ M` is
  supported on some initial segment.
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
    { toFun := fun f ↦ filter p f.1
      map_add' := fun _ _ ↦ filter_add
      map_smul' := fun _ _ ↦ filter_smul }
    fun f ↦ (mem_supported R _).2 fun a ha ↦ by
      have ha : a ∈ (filter p f.1).support := ha
      rw [support_filter, Finset.mem_filter] at ha
      exact h a ((mem_supported R f.1).1 f.2 ha.1) ha.2

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

end Finsupp
