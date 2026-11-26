/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Integral.IntegrableOn

/-!
# Integrals over an open subgroup of functions factoring through a finite quotient

Let `H` be an open additive subgroup of a topological additive group `G` with a left-invariant
measure `μ`, and let `π : H →+ R` be a surjective, locally constant homomorphism onto a finite
group `R`, such as the reduction `O → O / ϖ O` of the ring of integers of a non-archimedean local
field. The translates of the kernel of `π` partition `H` into `#R` pieces of equal measure, so
integrating over `H` a function that factors through `π` is averaging over `R`, provided
`μ H < ∞`:

* `MeasureTheory.card_smul_setIntegral_eq_measureReal_smul_sum`: if `μ H < ∞` and
  `f x = Φ (π x)` on `H`, for `f` valued in a real Banach space, then
  `#R • ∫ x in H, f x ∂μ = μ.real H • ∑ r, Φ r`.

This is how integrals over the integers of a local field of functions of level `ϖ`, such as
the local Gauss sums of tamely ramified characters, reduce to finite sums over the residue ring.
The proof uses that a set integral over a subgroup is invariant under translation by an element
of the subgroup (`MeasureTheory.setIntegral_add_left_eq_self_of_mem`), and that a function
factoring on an open set of finite measure through a locally constant map to a finite type is
integrable there (`MeasureTheory.integrableOn_of_eq_comp`).
-/

public section

namespace MeasureTheory

open Finset

variable {G R E S : Type*} [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [AddGroup G] [SetLike S G] [AddSubgroupClass S G] {H : S}

/-- **Integrating a function that factors through a finite quotient of an open subgroup.** Let
`π : H →+ R` be a surjective, locally constant homomorphism from an open subgroup `H` of `G`
onto a finite group `R`, and `μ` a left-invariant measure with `μ H < ∞`. If `f`, valued in a
real Banach space, satisfies `f x = Φ (π x)` for every `x ∈ H`, then
`#R • ∫ x in H, f x ∂μ = μ.real H • ∑ r, Φ r`: the measure `μ` restricted to `H`
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

end MeasureTheory
