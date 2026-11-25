/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Regular.Locus
public import Mathlib.AlgebraicGeometry.AffineSpace
import TauCeti.RingTheory.Smooth.SeparablePoint

/-!
# Checks for smoothness at closed points over a perfect field

* Affine space over a perfect field is smooth, so its local rings at closed points are regular.
* Perfectness of the ground field cannot be dropped from
  `AlgebraicGeometry.Scheme.Hom.smooth_iff_isRegularLocalRing_closedPoints`: for an inseparable
  finite field extension `K / k` (such as `k(t ^ (1 / p))` over `𝔽_p(t)`), the only local ring of
  `Spec K` is the field `K`, which is regular, but `Spec K ⟶ Spec k` is not smooth.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.SmoothClosedPointsExample

-- The local rings of affine space at closed points are regular.
example (k : Type u) [Field k] [PerfectField k] (n : Type u) [Finite n] :
    ∀ x ∈ closedPoints (𝔸(n; Spec (.of k))),
      IsRegularLocalRing ((𝔸(n; Spec (.of k))).presheaf.stalk x) :=
  (Scheme.Hom.smooth_iff_isRegularLocalRing_closedPoints (𝔸(n; Spec (.of k)) ↘ Spec (.of k))).mp
    inferInstance

/-- A field extension `K / k` for which `Spec K ⟶ Spec k` is smooth is separable: the residue
field at the unique maximal ideal of a smooth `k`-algebra can be chosen separable. -/
theorem isSeparable_of_smooth (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K)))] : Algebra.IsSeparable k K := by
  have : Algebra.Smooth k K := by
    have := HasRingHomProperty.Spec_iff (P := @Smooth) |>.mp
      ‹Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K)))›
    exact RingHom.smooth_algebraMap.mp this
  obtain ⟨m, hm, -, hsep⟩ := TauCeti.Algebra.Smooth.exists_isMaximal_isSeparable k K
  obtain rfl : m = ⊥ := Ideal.eq_bot_of_prime m
  exact AlgEquiv.Algebra.isSeparable (AlgEquiv.quotientBot k K)

-- Over an imperfect field the closed-point criterion fails: `Spec K` has regular local rings at
-- all of its points, yet it is not smooth over `k` when `K / k` is inseparable.
example (k K : Type u) [Field k] [Field K] [Algebra k K]
    (hK : ¬ Algebra.IsSeparable k K) :
    (∀ x ∈ closedPoints (Spec (.of K)), IsRegularLocalRing ((Spec (.of K)).presheaf.stalk x)) ∧
      ¬ Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ hK (isSeparable_of_smooth k K)⟩

end TauCeti.SmoothClosedPointsExample
