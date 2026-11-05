/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Order.Interval.Set.Fin
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Filtering finitely supported functions supported on a set

Keeping the values of a finitely supported function `f` at the points satisfying a predicate `p`
(`Finsupp.filter p f`) sends functions supported on `s` to functions supported on `t`, as soon as
every point of `s` satisfying `p` lies in `t`. This file packages this operation as a linear map
between the submodules `Finsupp.supported M R s` and `Finsupp.supported M R t`; Mathlib's
`Finsupp.restrictDom` is the case of the predicate `(· ∈ t)` on the whole space.

The coordinate inclusion `Finsupp.coordinateInclusion` embeds `Fin n → 𝕜` into `ℕ →₀ 𝕜`,
with range the functions supported on `Set.Iio n`. It commutes with extension by zero
between finite coordinate spaces.

A finitely generated submodule of `ℕ →₀ M` consists of functions supported on an initial segment
`{i | i < n}`, since its finitely many generators have finite supports.

## Main definitions

* `TauCeti.Finsupp.filterSupported`: `Finsupp.filter p` as a linear map
  `Finsupp.supported M R s →ₗ[R] Finsupp.supported M R t`.

## Main results

* `TauCeti.Finsupp.filterSupported_comp_inclusion`,
  `TauCeti.Finsupp.inclusion_comp_filterSupported`: the filter commutes with the inclusions
  `Finsupp.supported M R s ≤ Finsupp.supported M R s'` given by enlarging the support.
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

end TauCeti.Finsupp

namespace Finsupp

open Set

variable {𝕜 : Type*} [Field 𝕜]

/-- The coordinate inclusion `𝕜^n → ℕ →₀ 𝕜`, sending the `i`-th coordinate vector to the
`i`-th coordinate vector. -/
noncomputable def coordinateInclusion (n : ℕ) : (Fin n → 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.toLinearMap

@[simp]
theorem coordinateInclusion_single (n : ℕ) (i : Fin n) (a : 𝕜) :
    coordinateInclusion n (Pi.single i a) = Finsupp.single (i : ℕ) a := by
  simp [coordinateInclusion]

@[simp]
theorem coordinateInclusion_apply_val {n : ℕ} (v : Fin n → 𝕜) (i : Fin n) :
    coordinateInclusion n v i = v i := by
  simp [coordinateInclusion, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem coordinateInclusion_apply_of_le {n : ℕ} (v : Fin n → 𝕜) {i : ℕ} (hi : n ≤ i) :
    coordinateInclusion n v i = 0 := by
  simp only [coordinateInclusion, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Fin.range_val] using hi)

theorem coordinateInclusion_injective (n : ℕ) :
    Function.Injective (coordinateInclusion (𝕜 := 𝕜) n) :=
  (Finsupp.mapDomain_injective Fin.val_injective).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.injective

/-- The image of the coordinate inclusion of `𝕜^n` consists of the finitely supported functions
vanishing from coordinate `n` on. -/
theorem range_coordinateInclusion (n : ℕ) :
    LinearMap.range (coordinateInclusion (𝕜 := 𝕜) n) = Finsupp.supported 𝕜 𝕜 (Iio n) := by
  simpa [coordinateInclusion, LinearMap.range_comp, Fin.range_val] using
    Finsupp.lmapDomain_supported 𝕜 𝕜 (Fin.val : Fin n → ℕ) univ

/-- The coordinate inclusions are compatible with the inclusions `𝕜^m → 𝕜^n` onto the first
coordinates. -/
@[simp]
theorem coordinateInclusion_comp_extendByZero_castLE {m n : ℕ} (h : m ≤ n) :
    coordinateInclusion (𝕜 := 𝕜) n ∘ₗ Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE h) =
      coordinateInclusion m := by
  refine LinearMap.pi_ext fun i a ↦ ?_
  simp [Function.ExtendByZero.linearMap_single 𝕜 (Fin.castLE_injective h)]

end Finsupp

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
