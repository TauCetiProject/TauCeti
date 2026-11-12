/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Lifting.Relative
public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic

/-!
# Relative lifting for Hurewicz fibrations

The strong deformation retraction of the cylinder `I × X` onto `{0} × X ∪ I × A` of an
NDR pair `(X, A)` (`TauCeti.NDRPair.cylinderHomotopyRel`), together with
`HasHomotopyLiftingProperty.zeroSetSDR_liftingInclusion`, gives the relative homotopy
lifting property: a homotopy in `B` lifts, starting at a prescribed lift and agreeing on `A` with a
prescribed lift over `A` (`TauCeti.IsHurewiczFibration.exists_lift_of_ndrPair`). For instance,
when the basepoint of the parameter space forms an NDR pair with it, the lift can follow an
arbitrary prescribed track of the basepoint.

## Main results

* `TauCeti.IsHurewiczFibration.exists_lift_of_ndrPair`: the relative homotopy lifting property
  with respect to an NDR pair.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapters 6 and 7.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- **Relative homotopy lifting for NDR pairs.** Let `(X, A)` be an NDR pair and `p` a Hurewicz
fibration. A homotopy `H : I × X → B` lifts to a homotopy `G : I × X → E` with prescribed initial
lift `f` and prescribed lift `g` over `I × A`, provided `f` and `g` agree at time `0`. -/
theorem IsHurewiczFibration.exists_lift_of_ndrPair (hp : IsHurewiczFibration.{w} p) {X : Type w}
    [TopologicalSpace X] {A : Set X} (N : NDRPair A) (f : C(X, E)) (H : C(I × X, B))
    (hH : ∀ x, H (0, x) = p (f x)) (g : C(I × A, E)) (hg : ∀ t (a : A), p (g (t, a)) = H (t, a))
    (hgf : ∀ a : A, g (0, a) = f a) :
    ∃ G : C(I × X, E), p ∘ G = H ∧ (∀ x, G (0, x) = f x) ∧ ∀ t (a : A), G (t, a) = g (t, a) := by
  -- glue `f` and `g` to a map on `{0} × X ∪ I × A`, extended over the cylinder by the retraction
  obtain ⟨k, hk₀, hkA⟩ :=
    N.hasHomotopyExtensionProperty.exists_extension_of_isClosed N.isClosed f g hgf
  obtain ⟨G, hG, hGJ⟩ := (hp.hasHomotopyLiftingProperty _).zeroSetSDR_liftingInclusion
    N.cylinderControl N.cylinderControl_eq_zero_iff N.cylinderRetraction ⟨N.cylinderHomotopyRel⟩
    (k.restrict (cylinderExtensionDomain A)) H fun ⟨⟨t, x⟩, hz⟩ ↦ by
      rcases mem_cylinderExtensionDomain_iff.1 hz with ht | hx
      · obtain rfl : t = 0 := ht
        simp [hk₀, hH]
      · simpa [hkA t ⟨x, hx⟩] using hg t ⟨x, hx⟩
  refine ⟨G, hG, fun x ↦ ?_, fun t a ↦ ?_⟩
  · simpa [hk₀] using hGJ ⟨(0, x), zero_mem_cylinderExtensionDomain x⟩
  · simpa [hkA] using hGJ ⟨(t, a), mem_cylinderExtensionDomain_of_mem a.2⟩

end TauCeti
