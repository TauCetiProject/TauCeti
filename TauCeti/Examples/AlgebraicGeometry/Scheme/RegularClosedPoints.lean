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

-- Over an imperfect field the closed-point criterion fails: `Spec K` has regular local rings at
-- all of its points, yet it is not smooth over `k` when the finite extension `K / k` is
-- inseparable, although `Spec K ⟶ Spec k` is locally of finite type.
example (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (hK : ¬ Algebra.IsSeparable k K) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      (∀ x ∈ closedPoints (Spec (.of K)), IsRegularLocalRing ((Spec (.of K)).presheaf.stalk x)) ∧
      ¬ Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine ⟨?_, fun _ _ ↦ inferInstance, fun h ↦ hK ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  · have : Algebra.Smooth k K :=
      RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff (P := @Smooth) |>.mp h)
    exact TauCeti.Algebra.Smooth.isSeparable k K

end TauCeti.SmoothClosedPointsExample
