/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import Mathlib.RingTheory.Polynomial.IsIntegral
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Integral functions over a finite map to the sphere

For a finite holomorphic map `β : X → OnePoint ℂ` from a compact connected Riemann surface,
the integral closure of `ℂ[β]` in the meromorphic function field of `X` consists exactly of
functions with no poles away from the fibre over infinity. This makes holomorphy on the affine
part of `X` an algebraic condition, suitable for transport by field automorphisms.

The forward implication uses the order valuation at each point. For the reverse implication,
the coefficients of the fibre polynomial are holomorphic at every finite point of the sphere,
so they are polynomials in its coordinate.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §8, for the polynomial equation obtained from
  the elementary symmetric functions along the fibres of a finite map.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §§6.1–6.2,
  for the application to holomorphic modular functions and coefficient automorphisms.
-/

public noncomputable section

open OnePoint Polynomial Set
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

/-- A meromorphic function integral over `ℂ[g]` has no poles at points where `g` is finite. -/
theorem apply_ne_infty_of_isIntegral_adjoin_singleton {f g : MeromorphicFunction X}
    (hf : IsIntegral (Algebra.adjoin ℂ {g}) f) {x : X} (hg : g x ≠ ∞) : f x ≠ ∞ := by
  have hA : ∀ a ∈ Algebra.adjoin ℂ ({g} : Set (MeromorphicFunction X)), a x ≠ ∞ := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha => simpa only [Set.mem_singleton_iff.mp ha] using hg
    | algebraMap c => simp
    | add a b _ _ ha hb =>
      rw [add_apply_of_eq_coe (coe_finitePart ha).symm (coe_finitePart hb).symm]
      exact OnePoint.coe_ne_infty _
    | mul a b _ _ ha hb =>
      rw [mul_apply_of_eq_coe (coe_finitePart ha).symm (coe_finitePart hb).symm]
      exact OnePoint.coe_ne_infty _
  obtain ⟨p, hp, hpf⟩ := hf
  have heval : (p.map (Algebra.adjoin ℂ {g}).val.toRingHom).eval f = 0 := by
    rw [eval_map]
    exact hpf
  have hv := (order x).toValuation.le_one_of_root_monic (hp.map _)
    (fun i _ ↦ by
      rw [coeff_map]
      exact order_nonneg_iff.mpr (hA _ (p.coeff i).property)) heval
  exact order_nonneg_iff.mp hv

variable [CompactSpace X] [T2Space X] (β : FiniteHolomorphicMap X (OnePoint ℂ))
  (f : MeromorphicFunction X)

/-- A meromorphic function on a compact connected Riemann surface is integral over `ℂ[β]`
exactly when it has no poles away from the fibre over infinity. -/
theorem isIntegral_adjoin_comap_coordinate_iff :
    IsIntegral (Algebra.adjoin ℂ {comapₐ β β.holomorphic β.nonconstant coordinate}) f ↔
      ∀ x, β x ≠ ∞ → f x ≠ ∞ := by
  refine ⟨fun hf x hx ↦ apply_ne_infty_of_isIntegral_adjoin_singleton hf ?_, fun hf ↦ ?_⟩
  · simpa only [comapₐ_apply, comap_apply, coordinate_apply] using hx
  let φ := comapₐ β β.holomorphic β.nonconstant
  let A := Algebra.adjoin ℂ {φ coordinate}
  obtain ⟨p, hp, hdeg, hpf, hcoeff⟩ :=
    exists_monic_natDegree_eq_degree_eval₂_eq_zero β f
  have hmem (i : ℕ) : φ (p.coeff i) ∈ A := by
    obtain ⟨q, hq⟩ := (exists_aeval_coordinate_eq_iff (p.coeff i)).mpr
      (fun z ↦ hcoeff i z fun x hx ↦ hf x (by rw [hx]; exact OnePoint.coe_ne_infty z))
    rw [← hq, ← aeval_algHom_apply]
    exact Polynomial.aeval_mem_adjoin_singleton ℂ (φ coordinate) (p := q)
  have hzero : (p.map φ.toRingHom).eval f = 0 := by
    rwa [eval_map]
  exact IsIntegral.of_aeval_monic_of_isIntegral_coeff (R := A) (hp.map _)
    (by rw [natDegree_map_eq_of_injective φ.injective, hdeg]; exact (degree_pos β).ne')
    (hzero ▸ isIntegral_zero) (fun i ↦ by
      rw [coeff_map]
      exact isIntegral_algebraMap (x := (⟨_, hmem i⟩ : A)))

end TauCeti.RiemannSurface.MeromorphicFunction
