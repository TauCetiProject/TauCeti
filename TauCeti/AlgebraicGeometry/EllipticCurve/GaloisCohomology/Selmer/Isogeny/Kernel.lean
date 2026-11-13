/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Torsion
import Mathlib.GroupTheory.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel

/-!
# The left kernel in the isogeny Selmer comparison

For a separable isogeny `φ : E₁ → E₂` of degree `n`, the Kummer map induces an isomorphism

`E₂(K)[φ̂] / φ(E₁(K)[n]) ≃ ker (Sel_φ → Sel_n)`.

The rational torsion quotient is essential: the map from `Sel_φ` to `Sel_n` need not be
injective. Its kernel has order `k` satisfying

`k · #E₁(K)[n] = #E₂(K)[φ̂] · #E₁(K)[φ]`.

This identifies the left correction term when comparing multiplication descent with descent
by an isogeny and its dual. The results apply to any family of localisations; neither
finiteness of Sha nor finiteness of the Selmer groups is needed.

## References

* E. F. Schaefer and M. Stoll, *How to do a p-descent on an elliptic curve*, Trans. Amer. Math.
  Soc. 356 (2004), 1209–1231.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

variable {K : Type*} [Field K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

/-- The Kummer map on the rational dual kernel, valued in the kernel of
`Sel_φ → Sel_{deg φ}`. -/
def dualKerToSelmerKer : (ofIsogeny φ.dual).pointMapHom.ker →+
    (φ.selmerGroupToTorsion τ).ker :=
  ((φ.kummerMap.comp (ofIsogeny φ.dual).pointMapHom.ker.subtype).codRestrict
    (φ.selmerGroup τ) (fun Q ↦ φ.kummerMap_mem_selmerGroup τ Q)).codRestrict _ fun Q ↦ by
      apply AddMonoidHom.mem_ker.mpr
      apply (φ.selmerGroupToTorsion_eq_zero_iff τ).mpr
      exact ⟨Q, (Hom.mem_ker_pointMapHom_iff _ _).mp Q.property, rfl⟩

/-- On underlying cohomology classes, the map from the dual kernel is the Kummer map. -/
@[simp]
theorem coe_dualKerToSelmerKer (Q : (ofIsogeny φ.dual).pointMapHom.ker) :
    (((φ.dualKerToSelmerKer τ Q : (φ.selmerGroupToTorsion τ).ker) : φ.selmerGroup τ) :
        H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) = φ.kummerMap Q :=
  (rfl)

/-- Every class in the left kernel of the Selmer comparison comes from a rational point
killed by the dual isogeny. -/
theorem dualKerToSelmerKer_surjective : Function.Surjective (φ.dualKerToSelmerKer τ) := by
  intro c
  obtain ⟨Q, hQ, hc⟩ := (φ.selmerGroupToTorsion_eq_zero_iff τ).mp
    (AddMonoidHom.mem_ker.mp c.property)
  refine ⟨⟨Q, (Hom.mem_ker_pointMapHom_iff _ _).mpr hQ⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hc

/-- The rational dual-kernel points with trivial Kummer class are exactly the images of
rational degree-torsion points. No surjectivity of `φ` on rational points is asserted. -/
theorem ker_dualKerToSelmerKer :
    (φ.dualKerToSelmerKer τ).ker = φ.torsionToDualKer.range := by
  ext Q
  rw [AddMonoidHom.mem_ker]
  have hzero : φ.dualKerToSelmerKer τ Q = 0 ↔ φ.kummerMap Q = 0 := by
    simp only [← Subtype.val_inj, coe_dualKerToSelmerKer, ZeroMemClass.coe_zero]
  rw [hzero, φ.kummerMap_eq_zero_iff]
  constructor
  · rintro ⟨P, hP⟩
    have hPn : P ∈ Submodule.torsionBy ℤ W₁.toAffine.Point (φ.degree : ℤ) := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← φ.pointMap_dual_pointMap, hP]
      exact (Hom.mem_ker_pointMapHom_iff _ _).mp Q.property
    exact ⟨⟨P, hPn⟩, Subtype.ext (by simpa only [coe_torsionToDualKer] using hP)⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, by simpa only [coe_torsionToDualKer] using congrArg Subtype.val hP⟩

/-- The rational torsion quotient is precisely the kernel of `Sel_φ → Sel_{deg φ}`. -/
def dualKerQuotientEquivSelmerKer :
    (ofIsogeny φ.dual).pointMapHom.ker ⧸ φ.torsionToDualKer.range ≃+
      (φ.selmerGroupToTorsion τ).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (φ.ker_dualKerToSelmerKer τ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (φ.dualKerToSelmerKer_surjective τ))

/-- The quotient isomorphism sends the class of a dual-kernel point to its Kummer class. -/
@[simp]
theorem dualKerQuotientEquivSelmerKer_mk (Q : (ofIsogeny φ.dual).pointMapHom.ker) :
    φ.dualKerQuotientEquivSelmerKer τ (QuotientAddGroup.mk Q) =
      φ.dualKerToSelmerKer τ Q := by
  simp [dualKerQuotientEquivSelmerKer]

omit [DecidableEq K] in
/-- The left kernel of the Selmer comparison is finite, even if the Selmer groups are not
known to be finite. -/
theorem finite_ker_selmerGroupToTorsion : Finite (φ.selmerGroupToTorsion τ).ker := by
  classical
  have := (ofIsogeny φ.dual).finite_ker_pointMapHom (ofIsogeny_ne_zero φ.dual)
  exact Finite.of_surjective _ (φ.dualKerToSelmerKer_surjective τ)

/-- The order of the left kernel in the Selmer comparison, expressed using only rational
torsion. It is not in general the whole rational dual kernel. -/
theorem natCard_ker_selmerGroupToTorsion_mul_natCard_torsionBy :
    Nat.card (φ.selmerGroupToTorsion τ).ker *
        Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point (φ.degree : ℤ)) =
      Nat.card (ofIsogeny φ.dual).pointMapHom.ker *
        Nat.card (ofIsogeny φ).pointMapHom.ker := by
  have hk : Nat.card φ.torsionToDualKer.ker = Nat.card (ofIsogeny φ).pointMapHom.ker := by
    have heq : φ.kerToTorsion.range = φ.torsionToDualKer.ker := by
      ext P
      simp only [φ.mem_range_kerToTorsion_iff, AddMonoidHom.mem_ker,
        φ.torsionToDualKer_eq_zero_iff]
    rw [← heq]
    exact (Nat.card_congr (AddMonoidHom.ofInjective φ.kerToTorsion_injective).toEquiv).symm
  have h₁ := AddSubgroup.card_ker_mul_card_of_surjective (φ.dualKerToSelmerKer_surjective τ)
  rw [φ.ker_dualKerToSelmerKer τ] at h₁
  have h₂ := AddSubgroup.card_ker_mul_card_range φ.torsionToDualKer
  rw [hk] at h₂
  rw [← h₂, ← h₁]
  ring

end TauCeti.Isogeny
