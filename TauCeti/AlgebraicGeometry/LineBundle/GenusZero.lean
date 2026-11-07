/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Effective

/-!
# Line bundles on curves of genus zero

On a proper regular integral curve of genus zero with constant global functions, degree
classifies line bundles up to isomorphism. No rational point is needed for injectivity:
Riemann–Roch makes a degree-zero line bundle effective, and positivity of residue degrees
forces its effective divisor to be zero. A rational point is needed to ensure that every
integer occurs as a degree; without one the image of degree may be a proper subgroup of `ℤ`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1 (Riemann–Roch).
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hφ : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k X))
  (hg : X.genus k = 0)

include hdim hφ hg in
/-- On a proper regular integral curve of genus zero with constant global functions, the only
line-bundle class of degree zero is the trivial class. This does not require a rational point.
Use this explicitly: simplification unfolds the genus hypothesis, so this is not a simp rule. -/
theorem eulerDegree_eq_zero_iff_of_genus_eq_zero (a : LineBundleClass X) :
    eulerDegree k a = 0 ↔ a = 1 := by
  refine ⟨fun ha ↦ ?_, fun h ↦ h ▸ eulerDegree_one k⟩
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [eulerDegree_mk] at ha
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨D, hD, -, hdeg, hclass⟩ :=
    InvertibleSheaf.exists_isEffective_iso_sheaf_of_genus_le_eulerDegree hdim hφ L
      (by simp only [← Scheme.genus_def, hg, ha, Nat.cast_zero, le_refl])
  have hzero : WeilDivisor.weightedDegree
      (fun x : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree x : ℤ)) D = 0 := by
    rw [WeilDivisor.weightedDegree_apply, ← SchemeWeilDivisor.relativeDegree_apply]
    exact hdeg.trans ha
  have hD0 : D = 0 := by
    apply (hD.weightedDegree_eq_zero_iff_of_pos_on_support ?_).mp hzero
    intro x _
    exact_mod_cast Nat.pos_of_ne_zero
      (Scheme.Hom.residueDegree_ne_zero_of_isClosed (X ↘ Spec (.of k))
        (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.2))
  simpa only [hD0, SchemeWeilDivisor.toLineBundleClass_zero] using hclass.symm

include hdim hφ hg in
/-- Degree is injective on line-bundle classes of a proper regular integral genus-zero curve
with constant global functions, even when the curve has no rational point. -/
theorem eulerDegree_injective_of_genus_eq_zero :
    Function.Injective (eulerDegree k : LineBundleClass X → ℤ) := by
  intro a b hab
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have h : eulerDegree k (a * b⁻¹) = 0 := by
    rw [eulerDegree_mul k hdim, eulerDegree_inv k hdim, hab, add_neg_cancel]
  exact mul_inv_eq_one.mp ((eulerDegree_eq_zero_iff_of_genus_eq_zero hdim hφ hg _).mp h)

end TauCeti.AlgebraicGeometry.LineBundleClass
