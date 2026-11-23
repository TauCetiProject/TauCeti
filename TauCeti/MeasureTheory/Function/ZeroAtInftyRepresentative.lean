/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Representatives vanishing at infinity, as a linear map

Let `μ` be a measure charging every nonempty open set, and let `f` assign to each element `u` of a
module `M` a function `f u` which agrees `μ`-almost everywhere with a continuous function vanishing
at infinity. Two continuous functions agreeing almost everywhere are equal
(`Continuous.ae_eq_iff_eq`, `ZeroAtInftyContinuousMap.eq_of_ae_eq`), so this representative is
unique. If `f` is linear up to almost-everywhere equality, the representative therefore depends
linearly on `u`.

This is how Sobolev embeddings into `C₀` are built: the elements of a Sobolev space are
almost-everywhere classes of functions, and the embedding sends each one to its continuous
representative.

## Main declarations

* `ZeroAtInftyContinuousMap.eq_of_ae_eq`: two functions in `C₀` agreeing `μ`-almost everywhere
  are equal.
* `TauCeti.zeroAtInftyRepresentativeₗ`: the linear map sending `u` to the representative of `f u`
  in `C₀`.
* `TauCeti.ae_eq_zeroAtInftyRepresentativeₗ`, `TauCeti.zeroAtInftyRepresentativeₗ_eq_iff`: it
  represents `f u`, and is the only function in `C₀` that does.
-/

public section

noncomputable section

open MeasureTheory
open scoped ZeroAtInfty

/-- Two functions in `C₀` agreeing almost everywhere for a measure charging every nonempty open set
are equal. -/
theorem ZeroAtInftyContinuousMap.eq_of_ae_eq {X F : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] [TopologicalSpace F] [T2Space F]
    [Zero F] {g g' : C₀(X, F)} (h : ⇑g =ᵐ[μ] g') : g = g' :=
  ext <| congrFun <| (Continuous.ae_eq_iff_eq μ g.continuous g'.continuous).mp h

namespace TauCeti

variable {𝕜 M X F : Type*} [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] [TopologicalSpace F] [T2Space F]
  [AddCommMonoid F] [ContinuousAdd F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  {f : M → X → F}

/-- **The representative vanishing at infinity, as a linear map.** If every function `f u` agrees
`μ`-almost everywhere with a continuous function vanishing at infinity, and `f` is linear up to
`μ`-almost-everywhere equality, the map sending `u` to this representative, which is unique
(`TauCeti.zeroAtInftyRepresentativeₗ_eq_iff`), is linear. -/
def zeroAtInftyRepresentativeₗ (hf : ∀ u, ∃ g : C₀(X, F), f u =ᵐ[μ] g)
    (hadd : ∀ u v, f (u + v) =ᵐ[μ] f u + f v) (hsmul : ∀ (c : 𝕜) u, f (c • u) =ᵐ[μ] c • f u) :
    M →ₗ[𝕜] C₀(X, F) where
  toFun u := (hf u).choose
  map_add' u v := by
    refine ZeroAtInftyContinuousMap.eq_of_ae_eq (μ := μ) <|
      (hf (u + v)).choose_spec.symm.trans ?_
    rw [FunLike.coe_add]
    exact (hadd u v).trans ((hf u).choose_spec.add (hf v).choose_spec)
  map_smul' c u := by
    refine ZeroAtInftyContinuousMap.eq_of_ae_eq (μ := μ) <|
      (hf (c • u)).choose_spec.symm.trans ?_
    rw [RingHom.id_apply, FunLike.coe_smul]
    exact (hsmul c u).trans ((hf u).choose_spec.const_smul c)

variable (hf : ∀ u, ∃ g : C₀(X, F), f u =ᵐ[μ] g) (hadd : ∀ u v, f (u + v) =ᵐ[μ] f u + f v)
  (hsmul : ∀ (c : 𝕜) u, f (c • u) =ᵐ[μ] c • f u)

/-- The function `f u` agrees almost everywhere with its representative vanishing at infinity. -/
theorem ae_eq_zeroAtInftyRepresentativeₗ (u : M) :
    f u =ᵐ[μ] zeroAtInftyRepresentativeₗ hf hadd hsmul u :=
  (hf u).choose_spec

/-- The representative of `f u` is the only function in `C₀` agreeing almost everywhere with
`f u`. -/
theorem zeroAtInftyRepresentativeₗ_eq_iff (u : M) (g : C₀(X, F)) :
    zeroAtInftyRepresentativeₗ hf hadd hsmul u = g ↔ f u =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ ae_eq_zeroAtInftyRepresentativeₗ hf hadd hsmul u,
    fun h ↦ ZeroAtInftyContinuousMap.eq_of_ae_eq
      ((ae_eq_zeroAtInftyRepresentativeₗ hf hadd hsmul u).symm.trans h)⟩

end TauCeti
