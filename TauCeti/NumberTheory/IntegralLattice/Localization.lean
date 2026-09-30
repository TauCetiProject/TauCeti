/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization

/-!
# Localizing an integral lattice at a prime

Let `L` be an integral lattice in a rational vector space `V`, with rational form `B`, and let `p`
be a prime.  Two `p`-adic objects are attached to `L`, and they are kept apart:

* the **integral localization** `L_p = ℤ_p ⊗[ℤ] L`, with the base change
  `B_{L,p} = L.integralForm.baseChange ℤ_p` of the integral form on the carrier;
* the **completed rational space** `V_p = ℚ_p ⊗[ℚ] V`, with the base change
  `B_{V,p} = B.baseChange ℚ_p` of the rational form.

The integral object is where scale, norm, Jordan splittings and integral duality live; the rational
object is where dimension, determinant square class and Hasse invariant live.  This file builds the
canonical `ℤ_p`-linear map `L_p → V_p`, `a ⊗ x ↦ a ⊗ x`, and proves that it is the bridge between
them:

* it is injective, and it becomes an isomorphism after extending scalars from `ℤ_p` to `ℚ_p`
  (`isBaseChange_localizationToCompletion`), so its image is a full `ℤ_p`-lattice in `V_p`;
* the localized integral form is the restriction of the completed rational form along it
  (`completedRationalForm_localizationToCompletion`).

Nothing here inverts `2`: bilinear-form base change needs no such hypothesis, so the construction
applies at `p = 2` exactly as at odd `p`.  The Gram matrix of `L_p` in a base-changed basis is the
image of the integral Gram matrix of `L`, and both local forms are nondegenerate exactly when `B`
is.

## Main definitions

* `TauCeti.IntegralLattice.LocalCarrier`: the integral localization `ℤ_p ⊗[ℤ] L`.
* `TauCeti.IntegralLattice.localIntegralForm`: its base-changed integral form.
* `TauCeti.IntegralLattice.completedRationalForm`: the rational form base-changed to the
  completed rational space `ℚ_p ⊗[ℚ] V`.
* `TauCeti.IntegralLattice.localizationToCompletion`: the canonical map `L_p → V_p`.
* `TauCeti.IntegralLattice.Isometry.localCarrierIsometry` and
  `TauCeti.IntegralLattice.Isometry.completedIsometry`: an isometry `L ≅ M` induces isometries
  `L_p ≅ M_p` and `V_p ≅ W_p`.

## Main results

* `TauCeti.IntegralLattice.isBaseChange_localizationToCompletion`: `V_p` is the scalar extension
  of `L_p` from `ℤ_p` to `ℚ_p` along the canonical map.
* `TauCeti.IntegralLattice.localizationToCompletion_injective`: the canonical map is injective.
* `TauCeti.IntegralLattice.span_range_localizationToCompletion`: its image spans `V_p` over `ℚ_p`.
* `TauCeti.IntegralLattice.completedRationalForm_localizationToCompletion`: the localized integral
  form is the restriction of the completed rational form.
* `TauCeti.IntegralLattice.toMatrix_localIntegralForm`: the Gram matrix of `L_p` is the image of
  the Gram matrix of `L`.
* `TauCeti.IntegralLattice.nondegenerate_localIntegralForm_iff` and
  `TauCeti.IntegralLattice.nondegenerate_completedRationalForm_iff`: both local forms are
  nondegenerate exactly when the rational form of `L` is.
* `TauCeti.IntegralLattice.Isometry.localizationToCompletion_localCarrierIsometry`: the canonical
  map is natural in isometries.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter VIII, for lattices in a quadratic
  space over the fraction field of a Dedekind domain, applied here to `ℤ_p ⊂ ℚ_p`.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, for integral forms over `ℤ_p`.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- The integral localization `ℤ_p ⊗[ℤ] L` of the carrier of an integral lattice. -/
abbrev LocalCarrier := ℤ_[p] ⊗[ℤ] L.carrier

/-- The integral form of an integral lattice, base-changed from `ℤ` to `ℤ_p`.  This is built from
the integral form on the carrier, not from the rational form on the ambient space. -/
noncomputable def localIntegralForm : LinearMap.BilinForm ℤ_[p] (L.LocalCarrier p) :=
  L.integralForm.baseChange ℤ_[p]

/-- The rational form of an integral lattice, base-changed from `ℚ` to `ℚ_p`. -/
noncomputable def completedRationalForm : LinearMap.BilinForm ℚ_[p] (ℚ_[p] ⊗[ℚ] V) :=
  L.form.baseChange ℚ_[p]

/-- The localized integral form on pure tensors. -/
@[simp]
theorem localIntegralForm_tmul (a b : ℤ_[p]) (x y : L) :
    L.localIntegralForm p (a ⊗ₜ x) (b ⊗ₜ y) = a * b * (L.integralForm x y : ℤ_[p]) := by
  rw [localIntegralForm, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  ring

/-- The completed rational form on pure tensors. -/
@[simp]
theorem completedRationalForm_tmul (a b : ℚ_[p]) (x y : V) :
    L.completedRationalForm p (a ⊗ₜ x) (b ⊗ₜ y) = a * b * (L.form x y : ℚ_[p]) := by
  rw [completedRationalForm, LinearMap.BilinForm.baseChange_tmul, Rat.smul_def]
  ring

/-- The localized integral form is symmetric. -/
theorem isSymm_localIntegralForm : (L.localIntegralForm p).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℤ_[p]
      (LinearMap.BilinForm.isSymm_iff.mp L.isSymm_integralForm))

/-- The completed rational form is symmetric. -/
theorem isSymm_completedRationalForm : (L.completedRationalForm p).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℚ_[p]
      (LinearMap.BilinForm.isSymm_iff.mp L.isSymm))

/-- The canonical `ℤ_p`-linear map from the integral localization of `L` to the completion of its
ambient space, sending `a ⊗ x` to `a ⊗ x`. -/
noncomputable def localizationToCompletion : L.LocalCarrier p →ₗ[ℤ_[p]] ℚ_[p] ⊗[ℚ] V :=
  (((TensorProduct.mk ℚ ℚ_[p] V 1).restrictScalars ℤ).comp L.carrier.subtype).liftBaseChange ℤ_[p]

/-- The canonical map on pure tensors. -/
@[simp]
theorem localizationToCompletion_tmul (a : ℤ_[p]) (x : L) :
    L.localizationToCompletion p (a ⊗ₜ x) = (a : ℚ_[p]) ⊗ₜ (x : V) := by
  rw [localizationToCompletion, LinearMap.liftBaseChange_tmul]
  simp [TensorProduct.smul_tmul', Algebra.smul_def]

/-- **The completion is the scalar extension of the localization.**  Extending scalars along the
canonical map `L_p → V_p` from `ℤ_p` to `ℚ_p` is an isomorphism `ℚ_p ⊗[ℤ_p] L_p ≃ V_p`. -/
theorem isBaseChange_localizationToCompletion :
    IsBaseChange ℚ_[p] (L.localizationToCompletion p) := by
  refine (TensorProduct.isBaseChange ℤ L ℤ_[p]).of_comp ?_
  -- Restricted to the unit pure tensors, the canonical map is `x ↦ 1 ⊗ x`, which is the
  -- composite of the rationalization `L → V` and the completion `V → V_p`: both base changes.
  -- The two composites carry different (propositionally equal) `ℤ`-module structures on `V_p`,
  -- one restricted from `ℤ_p` and one from `ℚ`, so they are matched by `convert`.
  convert (Submodule.IsLattice.isBaseChange_subtype L.carrier).comp
    (TensorProduct.isBaseChange ℚ V ℚ_[p])
  ext x
  simp

/-- **The canonical map `L_p → V_p` is injective.** -/
theorem localizationToCompletion_injective :
    Function.Injective (L.localizationToCompletion p) := by
  have h := L.isBaseChange_localizationToCompletion p
  have hmk : ⇑(L.localizationToCompletion p) =
      h.equiv ∘ TensorProduct.mk ℤ_[p] ℚ_[p] (L.LocalCarrier p) 1 := by
    ext x
    simp [h.equiv_tmul]
  rw [hmk]
  exact h.equiv.injective.comp
    (Module.Flat.tensorProduct_mk_injective ℤ_[p] (L.LocalCarrier p) ℚ_[p])

/-- **The image of `L_p` spans `V_p` over `ℚ_p`**, so `L_p` is full in the completion. -/
theorem span_range_localizationToCompletion :
    Submodule.span ℚ_[p] (Set.range (L.localizationToCompletion p)) = ⊤ := by
  have h := L.isBaseChange_localizationToCompletion p
  refine Submodule.eq_top_iff'.mpr fun v ↦ ?_
  obtain ⟨t, rfl⟩ := h.equiv.surjective v
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [h.equiv_tmul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
  | add s t hs ht => simpa only [map_add] using add_mem hs ht

/-- The image of the integral localization is a full `ℤ_p`-lattice in the completion. -/
instance isLattice_range_localizationToCompletion :
    (LinearMap.range (L.localizationToCompletion p)).IsLattice ℚ_[p] where
  fg := Submodule.fg_range _
  span_eq_top := by
    rw [LinearMap.coe_range]
    exact L.span_range_localizationToCompletion p

/-- **The localized integral form is the restriction of the completed rational form** along the
canonical map `L_p → V_p`. -/
@[simp]
theorem completedRationalForm_localizationToCompletion (x y : L.LocalCarrier p) :
    L.completedRationalForm p (L.localizationToCompletion p x)
        (L.localizationToCompletion p y) =
      algebraMap ℤ_[p] ℚ_[p] (L.localIntegralForm p x y) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b y =>
      rw [localizationToCompletion_tmul, localizationToCompletion_tmul,
        completedRationalForm_tmul, localIntegralForm_tmul, ← L.integralForm_cast x y,
        Rat.cast_intCast, PadicInt.algebraMap_apply]
      push_cast
      ring

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of the localized integral form in a base-changed carrier basis is the image
of the integral Gram matrix of the lattice. -/
@[simp]
theorem toMatrix_localIntegralForm (e : Basis ι ℤ L) :
    LinearMap.BilinForm.toMatrix (e.baseChange ℤ_[p]) (L.localIntegralForm p) =
      (L.gramMatrix e).map (Int.cast : ℤ → ℤ_[p]) := by
  rw [localIntegralForm, bilinForm_toMatrix_baseChange, gramMatrix_eq_toMatrix,
    algebraMap_int_eq, Int.coe_castRingHom]

end Gram

/-- The localized integral form is nondegenerate exactly when the rational form of the lattice
is. -/
theorem nondegenerate_localIntegralForm_iff :
    (L.localIntegralForm p).Nondegenerate ↔ L.form.Nondegenerate := by
  rw [localIntegralForm,
    nondegenerate_baseChange_iff L.integralForm (Module.Free.chooseBasis ℤ L),
    nondegenerate_integralForm_iff]

/-- The completed rational form is nondegenerate exactly when the rational form of the lattice
is. -/
theorem nondegenerate_completedRationalForm_iff :
    (L.completedRationalForm p).Nondegenerate ↔ L.form.Nondegenerate := by
  rw [completedRationalForm, nondegenerate_baseChange_iff L.form L.rationalBasis]

namespace Isometry

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {L} {M : IntegralLattice W}

/-- An isometry of integral lattices localizes to an isometry of the localized integral forms: the
base change to `ℤ_p` of its carrier equivalence. -/
noncomputable def localCarrierIsometry (e : Isometry L M) :
    (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p) :=
  LinearMap.BilinForm.IsometryEquiv.baseChange ℤ_[p]
    ⟨e.carrierEquiv, e.carrierEquiv_map_integralForm⟩

/-- The localized isometry on pure tensors. -/
@[simp]
theorem localCarrierIsometry_tmul (e : Isometry L M) (a : ℤ_[p]) (x : L) :
    e.localCarrierIsometry p (a ⊗ₜ x) = a ⊗ₜ e.carrierEquiv x :=
  LinearMap.BilinForm.IsometryEquiv.baseChange_tmul _ a x

/-- An isometry of integral lattices extends to an isometry of the completed rational forms. -/
noncomputable def completedIsometry (e : Isometry L M) :
    (L.completedRationalForm p).IsometryEquiv (M.completedRationalForm p) :=
  e.toIsometryEquiv.baseChange ℚ_[p]

/-- The completed isometry on pure tensors. -/
@[simp]
theorem completedIsometry_tmul (e : Isometry L M) (a : ℚ_[p]) (v : V) :
    e.completedIsometry p (a ⊗ₜ v) = a ⊗ₜ e v :=
  LinearMap.BilinForm.IsometryEquiv.baseChange_tmul _ a v

/-- **Localization is natural in isometries**: the canonical maps `L_p → V_p` and `M_p → W_p`
intertwine the localized and the completed isometries. -/
theorem localizationToCompletion_localCarrierIsometry (e : Isometry L M)
    (x : L.LocalCarrier p) :
    M.localizationToCompletion p (e.localCarrierIsometry p x) =
      e.completedIsometry p (L.localizationToCompletion p x) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a x => simp

end Isometry

end IntegralLattice

end TauCeti
