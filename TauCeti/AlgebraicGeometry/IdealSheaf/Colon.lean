/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import TauCeti.RingTheory.Localization.Colon
import TauCeti.RingTheory.Ideal.Colon
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentation

/-!
# Colon ideal sheaves

The colon `(D : E)` is the largest quasi-coherent ideal sheaf whose product with `E` is
contained in `D`. It exists without finiteness assumptions. If the section ideals of `E` are
finitely generated, its section ideals on affine opens are the ordinary colon ideals.
This construction is the ideal-sheaf form of subtraction of effective Cartier divisors.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {D D' E E' F : X.IdealSheafData}

/-- The largest quasi-coherent ideal sheaf whose product with `E` is contained in `D`. -/
noncomputable def colon (D E : X.IdealSheafData) : X.IdealSheafData :=
  ofIdeals fun U ↦ (D.ideal U).colon (E.ideal U : Set Γ(X, U))

/-- Colon is the quasi-coherent ideal sheaf associated to the sectionwise colon ideals. -/
theorem colon_def (D E : X.IdealSheafData) :
    D.colon E = ofIdeals fun U ↦ (D.ideal U).colon (E.ideal U : Set Γ(X, U)) := (rfl)

/-- The section ideals of the colon sheaf are contained in the sectionwise colon ideals. -/
theorem ideal_colon_le (D E : X.IdealSheafData) (U : X.affineOpens) :
    (D.colon E).ideal U ≤ (D.ideal U).colon (E.ideal U : Set Γ(X, U)) :=
  ideal_ofIdeals_le _ _

/-- Colon is right adjoint to multiplication of ideal sheaves. -/
theorem le_colon_iff : F ≤ D.colon E ↔ F * E ≤ D := by
  rw [colon, le_ofIdeals_iff]
  simp only [Pi.le_def, le_def, ideal_mul, Pi.mul_apply, Ideal.le_colon_iff]

/-- Multiplication by an ideal sheaf is left adjoint to colon by that ideal sheaf. -/
theorem gc_mul_colon (E : X.IdealSheafData) :
    GaloisConnection (· * E) (·.colon E) := fun _ _ ↦ le_colon_iff.symm

/-- A product contained in `D` gives an inclusion into the colon by its second factor. -/
theorem le_colon_of_mul_le (h : F * E ≤ D) : F ≤ D.colon E := le_colon_iff.mpr h

/-- Multiplying the colon by its denominator gives an ideal sheaf contained in the numerator. -/
theorem colon_mul_le (D E : X.IdealSheafData) : D.colon E * E ≤ D := le_colon_iff.mp le_rfl

/-- Every ideal sheaf is contained in its colon by any ideal sheaf. -/
theorem le_colon (D E : X.IdealSheafData) : D ≤ D.colon E :=
  le_colon_of_mul_le fun _ ↦ Ideal.mul_le_left

/-- Colon is monotone in its numerator and antitone in its denominator. -/
theorem colon_mono (hD : D ≤ D') (hE : E' ≤ E) : D.colon E ≤ D'.colon E' := by
  apply le_colon_of_mul_le
  intro U
  exact (Ideal.mul_mono le_rfl (hE U)).trans ((colon_mul_le D E U).trans (hD U))

/-- Colon is the unit ideal sheaf exactly when the denominator is contained in the numerator. -/
@[simp]
theorem colon_eq_top_iff : D.colon E = ⊤ ↔ E ≤ D := by
  rw [eq_top_iff, le_colon_iff, top_mul]

/-- The colon of the unit ideal sheaf is the unit ideal sheaf. -/
@[simp]
theorem top_colon (E : X.IdealSheafData) : (⊤ : X.IdealSheafData).colon E = ⊤ :=
  colon_eq_top_iff.mpr le_top

/-- Colon of an ideal sheaf by itself is the unit ideal sheaf. -/
@[simp]
theorem colon_self (D : X.IdealSheafData) : D.colon D = ⊤ := colon_eq_top_iff.mpr le_rfl

/-- Colon by the unit ideal sheaf does not change an ideal sheaf. -/
@[simp]
theorem colon_top (D : X.IdealSheafData) : D.colon ⊤ = D := by
  apply eq_of_forall_le_iff
  intro F
  simp only [le_colon_iff, mul_top]

/-- Colon by the zero ideal sheaf is the unit ideal sheaf. -/
@[simp]
theorem colon_bot (D : X.IdealSheafData) : D.colon ⊥ = ⊤ := colon_eq_top_iff.mpr bot_le

/-- Colon preserves intersections in the numerator. -/
@[simp]
theorem inf_colon (D F E : X.IdealSheafData) :
    (D ⊓ F).colon E = D.colon E ⊓ F.colon E := by
  apply eq_of_forall_le_iff
  intro I
  simp only [le_colon_iff, le_inf_iff]

/-- Colon preserves arbitrary infima in its numerator. -/
@[simp]
theorem iInf_colon {ι : Sort*} (D : ι → X.IdealSheafData) (E : X.IdealSheafData) :
    (⨅ i, D i).colon E = ⨅ i, (D i).colon E := by
  apply eq_of_forall_le_iff
  intro I
  simp only [le_colon_iff, le_iInf_iff]

/-- Colon preserves infima of sets of numerator ideal sheaves. -/
@[simp]
theorem sInf_colon (s : Set X.IdealSheafData) (E : X.IdealSheafData) :
    (sInf s).colon E = ⨅ D ∈ s, D.colon E := by
  simp only [sInf_eq_iInf, iInf_colon]

/-- A supremum of denominators becomes an infimum of colon ideal sheaves. -/
@[simp]
theorem colon_iSup {ι : Sort*} (D : X.IdealSheafData) (E : ι → X.IdealSheafData) :
    D.colon (⨆ i, E i) = ⨅ i, D.colon (E i) := by
  apply eq_of_forall_le_iff
  intro I
  rw [le_colon_iff, mul_comm I, ← le_colon_iff, iSup_le_iff]
  simp only [le_colon_iff, le_iInf_iff, mul_comm]

/-- A supremum of a set of denominators becomes an infimum of colon ideal sheaves. -/
@[simp]
theorem colon_sSup (D : X.IdealSheafData) (s : Set X.IdealSheafData) :
    D.colon (sSup s) = ⨅ E ∈ s, D.colon E := by
  simp only [sSup_eq_iSup, colon_iSup]

/-- A sum in the denominator becomes an intersection of colon ideal sheaves. -/
@[simp]
theorem colon_sup (D E F : X.IdealSheafData) :
    D.colon (E ⊔ F) = D.colon E ⊓ D.colon F := by
  apply eq_of_forall_le_iff
  intro I
  simp only [le_colon_iff, le_inf_iff, mul_inf, sup_le_iff]

/-- Successive colon operations are colon by the product of their denominators. -/
theorem colon_mul (D E F : X.IdealSheafData) :
    D.colon (E * F) = (D.colon E).colon F := by
  apply eq_of_forall_le_iff
  intro I
  simp only [le_colon_iff]
  rw [mul_assoc, mul_comm F E]

/-- Over an affine scheme, the ideal-sheaf equivalence preserves colon without any finite
generation hypothesis. -/
theorem equivOfIsAffine_colon [IsAffine X] (D E : X.IdealSheafData) :
    equivOfIsAffine (D.colon E) =
      (equivOfIsAffine D).colon (equivOfIsAffine E : Set Γ(X, ⊤)) := by
  set e := equivOfIsAffine (X := X)
  apply eq_of_forall_le_iff
  intro I
  rw [← e.apply_symm_apply I, map_le_map_iff e, le_colon_iff,
    ← map_le_map_iff e, map_mul, e.apply_symm_apply]
  exact Ideal.le_colon_iff.symm

/-- Forming an ideal sheaf on an affine scheme commutes with colon. -/
theorem ofIdealTop_colon_ofIdealTop [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    (ofIdealTop I).colon (ofIdealTop J) = ofIdealTop (I.colon (J : Set Γ(X, ⊤))) := by
  apply EquivLike.injective (equivOfIsAffine (X := X))
  simp only [equivOfIsAffine_colon, ← equivOfIsAffine_symm_apply,
    OrderRingIso.apply_symm_apply]

/-- For a denominator of finite type, colon is computed on every affine open by ordinary
colon of the section ideals. -/
@[simp]
theorem ideal_colon (D E : X.IdealSheafData) (hE : ∀ U, (E.ideal U).FG)
    (U : X.affineOpens) :
    (D.colon E).ideal U = (D.ideal U).colon (E.ideal U : Set Γ(X, U)) := by
  let I : X.IdealSheafData :=
    { ideal V := (D.ideal V).colon (E.ideal V : Set Γ(X, V))
      map_ideal_basicOpen V f := by
        have := V.property.isLocalization_basicOpen f
        rw [← D.map_ideal_basicOpen, ← E.map_ideal_basicOpen]
        exact IsLocalization.map_colon (Submonoid.powers f) _ _ _ (hE V) }
  exact congrArg (fun J : X.IdealSheafData ↦ J.ideal U) (ofIdeals_ideal I)

/-- For a finite-type denominator, a regular principal factor cancels from a local colon
computation. The remaining factor is an arbitrary ideal. -/
theorem ideal_colon_eq_of_eq_span_mul {D E : X.IdealSheafData}
    (hEf : ∀ U, (E.ideal U).FG) {W : X.affineOpens} {v : Γ(X, W)}
    (hv : IsSMulRegular Γ(X, W) v) (hE : E.ideal W = Ideal.span {v})
    {J : Ideal Γ(X, W)} (hD : D.ideal W = Ideal.span {v} * J) :
    (D.colon E).ideal W = J := by
  rw [ideal_colon D E hEf, hE, hD, Ideal.colon_span]
  exact Ideal.span_singleton_mul_colon_singleton hv.isLeftRegular J

/-- Intersection with a locally principal ideal sheaf factors by that ideal and its colon.
The local generators need not be nonzerodivisors. -/
theorem inf_eq_colon_mul (D E : X.IdealSheafData)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a}) : D ⊓ E = D.colon E * E := by
  have hEf (U : X.affineOpens) : (E.ideal U).FG := by
    apply E.fg_ideal_of_forall_exists_fg _ U
    intro x
    obtain ⟨U, hxU, a, hEa⟩ := hE x
    refine ⟨U, hxU, ?_⟩
    rw [hEa]
    exact Submodule.fg_span_singleton a
  choose U hxU a hEa using hE
  refine ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
  rw [ideal_inf, Pi.inf_apply, ideal_mul, Pi.mul_apply, ideal_colon D E hEf,
    hEa x, Ideal.colon_span, mul_comm]
  exact Ideal.inf_span_singleton_eq_span_singleton_mul_colon _ _

/-- A subideal of a locally principal ideal factors by that ideal and its colon. -/
theorem eq_colon_mul (D E : X.IdealSheafData)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a}) (hle : D ≤ E) :
    D = D.colon E * E := by
  rw [← inf_eq_colon_mul D E hE, inf_eq_left.mpr hle]

end AlgebraicGeometry.Scheme.IdealSheafData
