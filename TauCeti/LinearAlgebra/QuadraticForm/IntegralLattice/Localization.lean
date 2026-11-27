/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.LinearAlgebra.QuadraticForm.IntegralLattice.Basic
import TauCeti.Algebra.Module.Lattice.BaseChange
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.Algebra.Module.Submodule.LocalGlobal
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Localization of integral quadratic lattices

The localization at a prime is the span of the lattice over the local ring inside the
original quadratic space. Clearing a denominator in a vector clears its square in the
quadratic value. Integral isometries extend along the canonical inclusion. Membership,
containment, and equality of embedded lattices can be tested at all maximal ideals.

## References

* John Voight, *Quaternion algebras*, §9.4, especially Lemma 9.4.6 and Corollary 9.4.7.
-/

public section

namespace TauCeti.IntegralQuadraticLattice

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] {Q : QuadraticForm K V}
  (L : IntegralQuadraticLattice R Q)

section Prime

variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.subalgebra K p.primeCompl
  (@Ideal.primeCompl_le_nonZeroDivisors R _
    (Function.Injective.noZeroDivisors (algebraMap R K) (IsFractionRing.injective R K)
      (map_zero _) (map_mul _)) p _)

/-- The lattice over the localization at `p`, embedded in the same generic quadratic space. -/
noncomputable def localize : IntegralQuadraticLattice Rₚ Q := by
  have := isLocalizedModule_id p.primeCompl V Rₚ
  refine
    { carrier := L.carrier.localized' Rₚ p.primeCompl LinearMap.id
      isFullLattice := ?_
      integral := ?_ }
  · simpa [Submodule.localized'_eq_span] using
      (IsBaseChange.ofEquiv (LinearEquiv.refl K V)).isFullLattice_span_image (S := Rₚ) L.carrier
  · intro x hx
    obtain ⟨s, hs⟩ := (L.carrier.map_mem_localized'_iff Rₚ p.primeCompl LinearMap.id x).mp hx
    obtain ⟨r, hr⟩ := L.integral _ hs
    apply Submodule.mem_one.mp
    apply (IsLocalization.smul_mem_iff (s := s * s)).mp
    rw [Submonoid.smul_def, Submonoid.coe_mul, ← Q.map_smul_of_tower]
    exact Submodule.mem_one.mpr ⟨algebraMap R Rₚ r,
      (IsScalarTower.algebraMap_apply R Rₚ K r).symm.trans hr⟩

/-- The underlying submodule of a localized lattice is the span over the local ring. -/
theorem carrier_localize :
    (L.localize p).carrier = Submodule.span Rₚ (L.carrier : Set V) := by
  simp [localize, Submodule.localized'_eq_span]

/-- A vector belongs to the localization exactly when some scalar outside the prime carries it
into the original lattice. -/
theorem mem_localize_iff {x : V} :
    x ∈ (L.localize p).carrier ↔ ∃ s ∉ p, s • x ∈ L.carrier := by
  have := isLocalizedModule_id p.primeCompl V Rₚ
  simpa [localize, Subtype.exists] using
    L.carrier.map_mem_localized'_iff Rₚ p.primeCompl LinearMap.id x

/-- The canonical linear inclusion into the localized carrier. -/
noncomputable def toLocalize : L.carrier →ₗ[R] (L.localize p).carrier :=
  have := isLocalizedModule_id p.primeCompl V Rₚ
  L.carrier.toLocalized' Rₚ p.primeCompl LinearMap.id

/-- The inclusion into the localized lattice preserves the ambient vector. -/
@[simp]
theorem coe_toLocalize (x : L.carrier) : (L.toLocalize p x : V) = x := (rfl)

/-- The embedded local lattice realizes the module localization of the original carrier. -/
instance : IsLocalizedModule p.primeCompl (L.toLocalize p) :=
  have := isLocalizedModule_id p.primeCompl V Rₚ
  Submodule.isLocalizedModule Rₚ p.primeCompl LinearMap.id L.carrier

/-- Localization preserves the values of the integral form on the original lattice. -/
@[simp]
theorem integralForm_toLocalize (x : L.carrier) :
    (L.localize p).integralForm (L.toLocalize p x) = algebraMap R Rₚ (L.integralForm x) := by
  apply FaithfulSMul.algebraMap_injective Rₚ K
  rw [algebraMap_integralForm, coe_toLocalize, ← IsScalarTower.algebraMap_apply,
    algebraMap_integralForm]

variable {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
  {Q' : QuadraticForm K W} (M : IntegralQuadraticLattice R Q')

/-- An isometry of the integral forms extends to an isometry over the local ring. -/
noncomputable def localizeIsometryEquiv (e : L.integralForm.IsometryEquiv M.integralForm) :
    (L.localize p).integralForm.IsometryEquiv (M.localize p).integralForm := by
  let f := IsLocalizedModule.mapEquiv p.primeCompl (L.toLocalize p) (M.toLocalize p) Rₚ
    e.toLinearEquiv
  refine { toLinearEquiv := f, map_app' := fun x ↦ ?_ }
  have h : (M.localize p).integralForm.comp f.toLinearMap = (L.localize p).integralForm := by
    apply QuadraticMap.ext_of_span_range_eq_top (L.toLocalize p)
      (IsLocalizedModule.isBaseChange p.primeCompl Rₚ (L.toLocalize p)).span_range_eq_top
    intro y
    simp [f]
  exact DFunLike.congr_fun h x

/-- On integral vectors the localized isometry is the original isometry. -/
@[simp]
theorem localizeIsometryEquiv_toLocalize (e : L.integralForm.IsometryEquiv M.integralForm)
    (x : L.carrier) :
    L.localizeIsometryEquiv p M e (L.toLocalize p x) = M.toLocalize p (e x) :=
  IsLocalizedModule.map_apply p.primeCompl (L.toLocalize p) (M.toLocalize p)
    e.toLinearEquiv.toLinearMap x

/-- Localization takes the identity isometry to the identity isometry. -/
@[simp]
theorem localizeIsometryEquiv_refl :
    L.localizeIsometryEquiv p L (.refl L.integralForm) = .refl (L.localize p).integralForm :=
  DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun
    (IsLocalizedModule.map_id p.primeCompl (L.toLocalize p)) x

/-- Localization commutes with composition of integral isometries. -/
@[simp]
theorem localizeIsometryEquiv_trans {U : Type*} [AddCommGroup U] [Module R U] [Module K U]
    [IsScalarTower R K U] {Q'' : QuadraticForm K U} (N : IntegralQuadraticLattice R Q'')
    (e : L.integralForm.IsometryEquiv M.integralForm)
    (f : M.integralForm.IsometryEquiv N.integralForm) :
    L.localizeIsometryEquiv p N (e.trans f) =
      (L.localizeIsometryEquiv p M e).trans (M.localizeIsometryEquiv p N f) :=
  DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun
    (IsLocalizedModule.map_comp' p.primeCompl (L.toLocalize p) (M.toLocalize p) (N.toLocalize p)
      e.toLinearEquiv.toLinearMap f.toLinearEquiv.toLinearMap) x

end Prime

/-- An embedded lattice is the intersection of its localizations at the maximal ideals. -/
theorem mem_iff_local {x : V} :
    x ∈ L.carrier ↔ ∀ (p : Ideal R) [p.IsMaximal], x ∈ (L.localize p).carrier := by
  refine ⟨fun hx p _ ↦ (L.mem_localize_iff p).mpr ⟨1, p.one_notMem, by simpa using hx⟩,
    fun h ↦ L.carrier.mem_of_forall_maximal_exists_smul_mem x fun p _ ↦ ?_⟩
  exact (L.mem_localize_iff p).mp (h p)

/-- Containment of embedded lattices can be tested at all maximal ideals. -/
theorem le_iff_local {Q' : QuadraticForm K V} (M : IntegralQuadraticLattice R Q') :
    L.carrier ≤ M.carrier ↔
      ∀ (p : Ideal R) [p.IsMaximal], (L.localize p).carrier ≤ (M.localize p).carrier := by
  refine ⟨fun h p _ ↦ ?_, fun h x hx ↦ M.mem_iff_local.mpr fun p _ ↦
    h p (L.mem_iff_local.mp hx p)⟩
  rw [L.carrier_localize, M.carrier_localize]
  exact Submodule.span_mono h

/-- In a fixed quadratic space two embedded lattices are equal exactly when their
localizations at every maximal ideal are equal. -/
theorem eq_iff_local (M : IntegralQuadraticLattice R Q) :
    L = M ↔ ∀ (p : Ideal R) [p.IsMaximal], L.localize p = M.localize p := by
  refine ⟨fun h p _ ↦ congrArg (fun N ↦ N.localize p) h, fun h ↦ ?_⟩
  apply IntegralQuadraticLattice.ext
  exact le_antisymm ((L.le_iff_local M).mpr fun p _ ↦ (congrArg carrier (h p)).le)
    ((M.le_iff_local L).mpr fun p _ ↦ (congrArg carrier (h p)).ge)

end TauCeti.IntegralQuadraticLattice
