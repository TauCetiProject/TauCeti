/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.RingTheory.Localization.AsSubring
public import TauCeti.LinearAlgebra.QuadraticForm.IntegralLattice.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule
import TauCeti.Algebra.Module.Lattice.BaseChange
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.LinearAlgebra.QuadraticForm.Restriction
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Localization of integral quadratic lattices

Localization is the span of the lattice over the localized ring inside the original quadratic
space. Clearing a denominator in a vector clears its square in the quadratic value. Mathlib's
`Submodule.localized'` supplies the carrier and `Submodule.toLocalized'` its canonical inclusion.
Integral isometric equivalences extend using `IsLocalizedModule.mapEquiv` for the underlying
linear equivalence. Membership, containment, and equality of embedded lattices can be tested at
all maximal ideals.

## References

* John Voight, *Quaternion algebras*, §9.4, especially Lemma 9.4.6 and Corollary 9.4.7.
-/

public section

open scoped nonZeroDivisors TensorProduct

namespace TauCeti.IntegralQuadraticLattice

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] {Q : QuadraticForm K V}
  (L : IntegralQuadraticLattice R Q)

section Localization

variable (S : Submonoid R) (hS : S ≤ R⁰)

local notation "Rₛ" => Localization.subalgebra K S hS

/-- The lattice over the localization at `S`, embedded in the same generic quadratic space. -/
noncomputable def localize : IntegralQuadraticLattice Rₛ Q := by
  have := isLocalizedModule_id S V Rₛ
  refine
    { carrier := L.carrier.localized' Rₛ S LinearMap.id
      isFullLattice := ?_
      integral := ?_ }
  · simpa [Submodule.localized'_eq_span] using
      (IsBaseChange.ofEquiv (LinearEquiv.refl K V)).isFullLattice_span_image (S := Rₛ) L.carrier
  · intro x hx
    obtain ⟨s, hs⟩ := (L.carrier.map_mem_localized'_iff Rₛ S LinearMap.id x).mp hx
    obtain ⟨r, hr⟩ := L.integral _ hs
    apply Submodule.mem_one.mp
    apply (IsLocalization.smul_mem_iff (s := s * s)).mp
    rw [Submonoid.smul_def, Submonoid.coe_mul, ← Q.map_smul_of_tower]
    exact Submodule.mem_one.mpr ⟨algebraMap R Rₛ r,
      (IsScalarTower.algebraMap_apply R Rₛ K r).symm.trans hr⟩

/-- The underlying submodule of a localized lattice is the span over the localized ring. -/
theorem carrier_localize :
    (L.localize S hS).carrier = Submodule.span Rₛ (L.carrier : Set V) := by
  simp [localize, Submodule.localized'_eq_span]

/-- A vector belongs to the localization exactly when some scalar in `S` carries it into the
original lattice. -/
theorem mem_localize_iff {x : V} :
    x ∈ (L.localize S hS).carrier ↔ ∃ s ∈ S, s • x ∈ L.carrier := by
  have := isLocalizedModule_id S V Rₛ
  simpa [localize, Subtype.exists] using
    L.carrier.map_mem_localized'_iff Rₛ S LinearMap.id x

/-- The canonical linear inclusion into the localized carrier. -/
noncomputable def toLocalize : L.carrier →ₗ[R] (L.localize S hS).carrier :=
  have := isLocalizedModule_id S V Rₛ
  L.carrier.toLocalized' Rₛ S LinearMap.id

/-- The inclusion into the localized lattice preserves the ambient vector. -/
@[simp]
theorem coe_toLocalize (x : L.carrier) : (L.toLocalize S hS x : V) = x := by
  have := isLocalizedModule_id S V Rₛ
  unfold toLocalize
  exact (L.carrier.toLocalized'_apply_coe Rₛ S LinearMap.id x).trans (LinearMap.id_apply _)

/-- The embedded local lattice realizes the module localization of the original carrier. -/
instance : IsLocalizedModule S (L.toLocalize S hS) :=
  have := isLocalizedModule_id S V Rₛ
  Submodule.isLocalizedModule Rₛ S LinearMap.id L.carrier

/-- Localization preserves the values of the integral form on the original lattice. -/
@[simp]
theorem integralForm_toLocalize (x : L.carrier) :
    (L.localize S hS).integralForm (L.toLocalize S hS x) = algebraMap R Rₛ (L.integralForm x) := by
  apply FaithfulSMul.algebraMap_injective Rₛ K
  rw [algebraMap_integralForm, coe_toLocalize, ← IsScalarTower.algebraMap_apply,
    algebraMap_integralForm]

/-- The pullback of the localized form to the scalar extension is characterized by the values
of the integral form on pure tensors with first factor one. -/
theorem eq_comp_localized_integralForm_iff (q : QuadraticForm Rₛ (Rₛ ⊗[R] L.carrier)) :
    q = (L.localize S hS).integralForm.comp
        (IsLocalizedModule.isBaseChange S Rₛ (L.toLocalize S hS)).equiv.toLinearMap ↔
      ∀ x : L.carrier, q (1 ⊗ₜ[R] x) = algebraMap R Rₛ (L.integralForm x) := by
  have h (x : L.carrier) :
      ((L.localize S hS).integralForm.comp
        (IsLocalizedModule.isBaseChange S Rₛ (L.toLocalize S hS)).equiv.toLinearMap)
          (1 ⊗ₜ[R] x) = algebraMap R Rₛ (L.integralForm x) := by
    simp [IsBaseChange.equiv_tmul]
  exact ⟨fun heq x ↦ heq ▸ h x, fun heq ↦ baseChange_ext fun x ↦ (heq x).trans (h x).symm⟩

variable {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
  {Q' : QuadraticForm K W} (M : IntegralQuadraticLattice R Q')

/-- An isometric equivalence of the integral forms extends over the localized ring. -/
noncomputable def localizeIsometryEquiv (e : L.integralForm.IsometryEquiv M.integralForm) :
    (L.localize S hS).integralForm.IsometryEquiv (M.localize S hS).integralForm := by
  let f := IsLocalizedModule.mapEquiv S (L.toLocalize S hS) (M.toLocalize S hS) Rₛ
    e.toLinearEquiv
  refine { toLinearEquiv := f, map_app' := fun x ↦ ?_ }
  have h : (M.localize S hS).integralForm.comp f.toLinearMap = (L.localize S hS).integralForm := by
    apply QuadraticMap.ext_of_span_range_eq_top (L.toLocalize S hS)
      (IsLocalizedModule.isBaseChange S Rₛ (L.toLocalize S hS)).span_range_eq_top
    intro y
    simp [f]
  exact DFunLike.congr_fun h x

/-- On integral vectors the localized isometric equivalence agrees with the original one. -/
@[simp]
theorem localizeIsometryEquiv_toLocalize (e : L.integralForm.IsometryEquiv M.integralForm)
    (x : L.carrier) :
    L.localizeIsometryEquiv S hS M e (L.toLocalize S hS x) = M.toLocalize S hS (e x) := by
  change (IsLocalizedModule.mapEquiv S (L.toLocalize S hS) (M.toLocalize S hS) Rₛ
    e.toLinearEquiv) (L.toLocalize S hS x) = _
  simp only [IsLocalizedModule.mapEquiv_apply, IsLocalizedModule.map_apply,
    LinearEquiv.coe_coe, QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Localization preserves the identity isometric equivalence. -/
@[simp]
theorem localizeIsometryEquiv_refl :
    L.localizeIsometryEquiv S hS L (.refl L.integralForm) =
      .refl (L.localize S hS).integralForm := by
  apply DFunLike.ext
  intro x
  refine DFunLike.congr_fun (LinearMap.ext_on_range
    (IsLocalizedModule.isBaseChange S Rₛ (L.toLocalize S hS)).span_range_eq_top ?_) x
  intro y
  exact L.localizeIsometryEquiv_toLocalize S hS L (.refl L.integralForm) y

/-- Localization commutes with composition of integral isometric equivalences. -/
@[simp]
theorem localizeIsometryEquiv_trans {U : Type*} [AddCommGroup U] [Module R U] [Module K U]
    [IsScalarTower R K U] {Q'' : QuadraticForm K U} (N : IntegralQuadraticLattice R Q'')
    (e : L.integralForm.IsometryEquiv M.integralForm)
    (f : M.integralForm.IsometryEquiv N.integralForm) :
    L.localizeIsometryEquiv S hS N (e.trans f) =
      (L.localizeIsometryEquiv S hS M e).trans (M.localizeIsometryEquiv S hS N f) := by
  apply DFunLike.ext
  intro x
  refine DFunLike.congr_fun (LinearMap.ext_on_range
    (IsLocalizedModule.isBaseChange S Rₛ (L.toLocalize S hS)).span_range_eq_top ?_) x
  intro y
  change L.localizeIsometryEquiv S hS N (e.trans f) (L.toLocalize S hS y) =
    M.localizeIsometryEquiv S hS N f (L.localizeIsometryEquiv S hS M e (L.toLocalize S hS y))
  simp only [localizeIsometryEquiv_toLocalize]
  rfl

/-- Localization commutes with inversion of integral isometric equivalences. -/
@[simp]
theorem localizeIsometryEquiv_symm (e : L.integralForm.IsometryEquiv M.integralForm) :
    M.localizeIsometryEquiv S hS L e.symm = (L.localizeIsometryEquiv S hS M e).symm := by
  apply DFunLike.ext
  intro x
  refine DFunLike.congr_fun (LinearMap.ext_on_range
    (IsLocalizedModule.isBaseChange S Rₛ (M.toLocalize S hS)).span_range_eq_top ?_) x
  intro y
  simp only [LinearEquiv.coe_coe, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    localizeIsometryEquiv_toLocalize]
  apply (L.localizeIsometryEquiv S hS M e).eq_symm_apply.mpr
  simp only [localizeIsometryEquiv_toLocalize, QuadraticMap.IsometryEquiv.apply_symm_apply]

end Localization

local notation "Sₚ" p => (@Ideal.primeCompl_le_nonZeroDivisors R _
  (Function.Injective.noZeroDivisors (algebraMap R K) (IsFractionRing.injective R K)
    (map_zero _) (map_mul _)) p _)

local notation "Rₚ" p => (Localization.subalgebra K (Ideal.primeCompl p) (Sₚ p))

/-- An embedded lattice is the intersection of its localizations at the maximal ideals. -/
theorem mem_iff_local {x : V} :
    x ∈ L.carrier ↔
      ∀ (p : Ideal R) [p.IsMaximal], x ∈ (L.localize p.primeCompl (Sₚ p)).carrier := by
  have localized (p : Ideal R) [p.IsMaximal] : IsLocalizedModule p.primeCompl
      (LinearMap.id (R := R) (M := V)) := isLocalizedModule_id p.primeCompl V (Rₚ p)
  refine ⟨fun hx p _ ↦ (L.mem_localize_iff p.primeCompl (Sₚ p)).mpr ⟨1, one_mem _, by simpa⟩,
    fun h ↦ @Submodule.mem_of_localization_maximal R V _ _ _ (fun _ _ ↦ V) _ _
      (fun _ _ ↦ LinearMap.id) localized
      x L.carrier fun p _ ↦ ?_⟩
  rw [← Submodule.restrictScalars_localized' (Rₚ p)]
  exact h p

/-- Containment of embedded lattices can be tested at all maximal ideals. -/
theorem le_iff_local {Q' : QuadraticForm K V} (M : IntegralQuadraticLattice R Q') :
    L.carrier ≤ M.carrier ↔
      ∀ (p : Ideal R) [p.IsMaximal],
        (L.localize p.primeCompl (Sₚ p)).carrier ≤ (M.localize p.primeCompl (Sₚ p)).carrier := by
  have localized (p : Ideal R) [p.IsMaximal] : IsLocalizedModule p.primeCompl
      (LinearMap.id (R := R) (M := V)) := isLocalizedModule_id p.primeCompl V (Rₚ p)
  refine ⟨fun h p _ ↦ ?_,
    fun h ↦ @Submodule.le_of_localization_maximal R V _ _ _ (fun _ _ ↦ V) _ _
      (fun _ _ ↦ LinearMap.id) localized _ _
      fun p _ ↦ ?_⟩
  · rw [L.carrier_localize, M.carrier_localize]
    exact Submodule.span_mono h
  · rw [← Submodule.restrictScalars_localized' (Rₚ p),
      ← Submodule.restrictScalars_localized' (Rₚ p)]
    exact fun _ hx ↦ h p hx

/-- In a fixed quadratic space two embedded lattices are equal exactly when their
localizations at every maximal ideal are equal. -/
theorem eq_iff_local (M : IntegralQuadraticLattice R Q) :
    L = M ↔ ∀ (p : Ideal R) [p.IsMaximal],
      L.localize p.primeCompl (Sₚ p) = M.localize p.primeCompl (Sₚ p) := by
  have localized (p : Ideal R) [p.IsMaximal] : IsLocalizedModule p.primeCompl
      (LinearMap.id (R := R) (M := V)) := isLocalizedModule_id p.primeCompl V (Rₚ p)
  refine ⟨fun h p _ ↦ congrArg (fun N ↦ N.localize p.primeCompl (Sₚ p)) h, fun h ↦ ?_⟩
  apply IntegralQuadraticLattice.ext
  exact @Submodule.eq_of_localization_maximal R V _ _ _ (fun p _ ↦ Rₚ p) _ _ _
    (fun _ _ ↦ V) _ _ _ _ (fun _ _ ↦ LinearMap.id) localized _ _ fun p _ ↦ congrArg carrier (h p)

end TauCeti.IntegralQuadraticLattice
