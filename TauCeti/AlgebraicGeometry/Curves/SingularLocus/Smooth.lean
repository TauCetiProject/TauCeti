/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
public import TauCeti.RingTheory.Syntomic.FittingIdeal

/-!
# The singular subscheme detects nonsmooth points

For a syntomic relative curve, the support of the first Fitting ideal of the relative
Kähler differentials is precisely the complement of the smooth locus. In particular, its
singular subscheme is empty exactly when the morphism is smooth. This connects the
scheme-theoretic singular subscheme used for nodal curves with pointwise smoothness.

The statement holds over arbitrary affine bases, without reducedness or Noetherian
hypotheses on the base.

## References

* The Stacks Project, Tag 0C58 (families of nodal curves and their singular subschemes).
* The Stacks Project, Tag 00T7 (standard smooth algebras and their differentials).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
  [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))]

/-- For a syntomic relative curve over an affine base, a point belongs to the support of
the singular subscheme exactly when it is outside the smooth locus. -/
@[simp]
theorem mem_support_singularLocus_iff_notMem_smoothLocus (x : X) :
    x ∈ (X.singularLocus R).support ↔ x ∉ (X ↘ Spec (.of R)).smoothLocus := by
  obtain ⟨U, hx, e, hU⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top
      1 (X ↘ Spec (.of R)) x
  let φ := ((X.baseRingToStructurePresheaf R).app (op U.1)).hom
  let : Algebra R Γ(X, U) := φ.toAlgebra
  have hφ : TauCeti.IsStandardSyntomicOfRelativeDimension 1 φ := by
    dsimp only [φ]
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
    exact (TauCeti.isStandardSyntomicOfRelativeDimension_respectsIso 1).right _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv hU
  have : TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension 1 R Γ(X, U) :=
    (TauCeti.isStandardSyntomicOfRelativeDimension_iff 1 φ).mp hφ
  have := TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.finitePresentation
    (n := 1) (R := R) (S := Γ(X, U))
  let q := U.2.primeIdealOf ⟨x, hx⟩
  have hs : x ∈ (X.singularLocus R).support ↔
      TauCeti.fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄R] 1 ≤ q.asIdeal := by
    rw [IdealSheafData.mem_support_iff_of_mem hx, X.singularLocus_ideal (R := R) U]
    let I := TauCeti.fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄R] 1
    have hq : U.2.fromSpec q = x := U.2.fromSpec_primeIdealOf ⟨x, hx⟩
    have hZ := congrArg (q ∈ ·) (U.2.fromSpec_preimage_zeroLocus (I : Set Γ(X, U)))
    have hpre := (Set.mem_preimage (f := U.2.fromSpec) (a := q)
      (s := X.zeroLocus (U := U.1) (I : Set Γ(X, U)))).symm.trans
        (hZ.to_iff.trans (PrimeSpectrum.mem_zeroLocus q (I : Set Γ(X, U))))
    simpa only [I, hq, SetLike.coe_subset_coe] using hpre
  have hm := (X ↘ Spec (.of R)).mem_smoothLocus_iff_isSmoothAt hx
  rw [← Scheme.baseRingToStructurePresheaf_app_eq_appLE] at hm
  rw [hs, hm]
  exact q.asIdeal.fittingIdeal_kaehlerDifferential_le_iff_not_isSmoothAt

/-- The support of the singular subscheme of a syntomic relative curve is the complement
of its smooth locus. -/
theorem support_singularLocus_eq_compl_smoothLocus :
    ((X.singularLocus R).support : Set X) = ((X ↘ Spec (.of R)).smoothLocus : Set X)ᶜ := by
  ext x
  exact X.mem_support_singularLocus_iff_notMem_smoothLocus (R := R) x

/-- A syntomic relative curve is smooth exactly when its singular ideal sheaf is the unit
ideal sheaf, equivalently when its singular subscheme is empty. -/
@[simp]
theorem singularLocus_eq_top_iff_smooth :
    X.singularLocus R = ⊤ ↔ Smooth (X ↘ Spec (.of R)) := by
  rw [← IdealSheafData.support_eq_bot_iff, ← Scheme.Hom.smoothLocus_eq_top_iff]
  constructor
  · intro h
    apply SetLike.coe_injective
    have hset := congrArg (fun Z : TopologicalSpace.Closeds X ↦ (Z : Set X)) h
    rw [X.support_singularLocus_eq_compl_smoothLocus, TopologicalSpace.Closeds.coe_bot] at hset
    exact Set.compl_empty_iff.mp hset
  · intro h
    apply SetLike.coe_injective
    rw [X.support_singularLocus_eq_compl_smoothLocus, h]
    simp

end AlgebraicGeometry.Scheme
