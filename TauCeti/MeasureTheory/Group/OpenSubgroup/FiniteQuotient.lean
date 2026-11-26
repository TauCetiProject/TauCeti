/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Integrals over an open subgroup of functions factoring through a finite quotient

Let `H` be an open additive subgroup of a topological additive group `G` with a left-invariant
measure `μ`, and let `π : H →+ R` be a surjective, locally constant homomorphism onto a finite
group `R`, such as the reduction `O → O / ϖ O` of the ring of integers of a non-archimedean local
field. The translates of the kernel of `π` partition `H` into `#R` pieces of equal measure, so
integrating over `H` a function that factors through `π` is averaging over `R`:

* `MeasureTheory.card_smul_setIntegral_eq_measureReal_smul_sum`: if `f x = Φ (π x)` on `H`, then
  `#R • ∫ x in H, f x ∂μ = μ H • ∑ r, Φ r`.

This is how integrals over the integers of a local field of functions of level `ϖ`, such as
the local Gauss sums of tamely ramified characters, reduce to finite sums over the residue ring.
The file also records that a set integral over a subgroup is invariant under translation by an
element of the subgroup (`MeasureTheory.setIntegral_add_left_eq_self_of_mem`), and that a function
factoring on an open set through a locally constant map to a finite type is integrable there
(`MeasureTheory.integrableOn_of_eq_comp`).
-/

public section

namespace MeasureTheory

open Finset

variable {G R E : Type*} [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup E]

section OpenSet

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- A function that agrees on an open set `U` of finite measure with a function of a locally
constant map `π : U → R` to a finite type is integrable on `U`. -/
theorem integrableOn_of_eq_comp [Finite R] {U : Set G} (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    {π : U → R} (hπ : IsLocallyConstant π) {f : G → E} {Φ : R → E}
    (hf : ∀ x : U, f x = Φ (π x)) : IntegrableOn f U μ := by
  classical
  have := Fintype.ofFinite R
  -- the fibres of `π`, seen in `G`, are open
  let A (r : R) : Set G := Subtype.val '' (π ⁻¹' {r})
  have hA (r : R) : MeasurableSet (A r) :=
    (hU.isOpenMap_subtypeVal _ (hπ.isOpen_fiber r)).measurableSet
  have hmem {x : G} (hx : x ∈ U) (r : R) : x ∈ A r ↔ π ⟨x, hx⟩ = r := by
    simp [A, hx]
  have hint : IntegrableOn (fun x ↦ ∑ r, (A r).indicator (fun _ ↦ Φ r) x) U μ :=
    integrable_finsetSum _ fun r _ ↦
      (integrableOn_const (C := Φ r) hμU).indicator (hA r)
  refine hint.congr_fun (fun x hx ↦ ?_) hU.measurableSet
  dsimp only
  rw [hf ⟨x, hx⟩, Finset.sum_eq_single (π ⟨x, hx⟩)]
  · simp [Set.indicator_of_mem ((hmem hx _).mpr rfl)]
  · exact fun r _ hr ↦ Set.indicator_of_notMem (fun h ↦ hr ((hmem hx r).mp h).symm) _
  · simp

end OpenSet

section Subgroup

variable {S : Type*} [AddGroup G] [SetLike S G] [AddSubgroupClass S G] {H : S} [NormedSpace ℝ E]

/-- A set integral over an additive subgroup `H` is invariant under translation by an element of
`H`, for a left-invariant measure. -/
theorem setIntegral_add_left_eq_self_of_mem [MeasurableAdd G] [μ.IsAddLeftInvariant]
    (f : G → E) {s : G} (hs : s ∈ H) :
    ∫ x in (H : Set G), f (s + x) ∂μ = ∫ x in (H : Set G), f x ∂μ := by
  have hpre : (s + ·) ⁻¹' (H : Set G) = H := Set.ext fun _ ↦ add_mem_cancel_left hs
  simpa [hpre] using (measurePreserving_add_left μ s).setIntegral_preimage_emb
    (measurableEmbedding_addLeft s) f H

/-- **Integrating a function that factors through a finite quotient of an open subgroup.** Let
`π : H →+ R` be a surjective, locally constant homomorphism from an open subgroup `H` of `G`
onto a finite group `R`, and `μ` a left-invariant measure with `μ H < ∞`. If `f x = Φ (π x)` for
every `x ∈ H`, then `#R • ∫ x in H, f x ∂μ = μ H • ∑ r, Φ r`: the measure `μ` restricted to `H`
distributes its mass evenly over the fibres of `π`. -/
theorem card_smul_setIntegral_eq_measureReal_smul_sum [TopologicalSpace G]
    [ContinuousAdd G] [BorelSpace G] [μ.IsAddLeftInvariant] [AddGroup R] [Fintype R]
    [CompleteSpace E] (hH : IsOpen (H : Set G)) (hμH : μ H ≠ ⊤) {π : H →+ R}
    (hπ : Function.Surjective π) (hπc : IsLocallyConstant π) {f : G → E} {Φ : R → E}
    (hf : ∀ x : H, f x = Φ (π x)) :
    Fintype.card R • ∫ x in (H : Set G), f x ∂μ = μ.real H • ∑ r, Φ r := by
  let s : R → H := Function.surjInv hπ
  -- the translate of `f` by `s r` agrees on `H` with `x ↦ Φ (r + π x)`
  have hshift (r : R) (x : H) : f (s r + x) = Φ (r + π x) := by
    have h := hf (s r + x)
    rwa [map_add, Function.surjInv_eq hπ r] at h
  have hint (r : R) : IntegrableOn (fun x ↦ f (s r + x)) H μ :=
    integrableOn_of_eq_comp hH hμH hπc (Φ := fun q ↦ Φ (r + q)) (hshift r)
  calc Fintype.card R • ∫ x in (H : Set G), f x ∂μ
      = ∑ r : R, ∫ x in (H : Set G), f (s r + x) ∂μ := by
        simp [setIntegral_add_left_eq_self_of_mem f (s _).property]
    _ = ∫ x in (H : Set G), ∑ r : R, f (s r + x) ∂μ :=
        (integral_finsetSum _ fun r _ ↦ hint r).symm
    _ = ∫ _ in (H : Set G), ∑ r, Φ r ∂μ := by
        refine setIntegral_congr_fun hH.measurableSet fun x hx ↦ ?_
        simp only [hshift _ ⟨x, hx⟩]
        exact Fintype.sum_equiv (Equiv.addRight (π ⟨x, hx⟩)) _ _ fun _ ↦ rfl
    _ = μ.real H • ∑ r, Φ r := setIntegral_const _

end Subgroup

end MeasureTheory
