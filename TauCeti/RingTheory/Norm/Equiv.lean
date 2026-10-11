/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.Units
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Norm.Basic

/-!
# Norm groups under algebra isomorphisms

An isomorphism of extensions preserves the norm subgroup of the ground field's units.
This permits norm-index calculations in a model extension to be used for any isomorphic
extension. The proof uses Mathlib's `Algebra.norm_eq_of_algEquiv`.
The identity extension has the full norm group, as does every finite extension of an
algebraically closed field, since its algebra map is an isomorphism.

For a tower `L/F/K` with `F/K` normal, the norm `N_{L/F}` is equivariant for `Aut(L/K)`: the
norm of `σ x` is the restriction of `σ` to `F` applied to the norm of `x`, on elements and on
units. The proof uses Mathlib's `Algebra.norm_eq_of_equiv_equiv`.
-/

public section

namespace TauCeti

/-- The identity extension has the whole unit group as its norm group. -/
@[simp]
theorem normGroup_self (K : Type*) [Field K] : normGroup K K = ⊤ := by
  ext a
  simp only [mem_normGroup_iff, Subgroup.mem_top, iff_true]
  exact ⟨a, by rw [Algebra.norm_self]; rfl⟩

/-- Isomorphic finite field extensions have the same norm group in the ground field. -/
theorem _root_.AlgEquiv.normGroup_eq {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Module.Finite K L] [Module.Finite K M]
    (e : L ≃ₐ[K] M) : normGroup K L = normGroup K M := by
  ext a
  rw [mem_normGroup_iff, mem_normGroup_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Units.map e.toMonoidHom x, (Algebra.norm_eq_of_algEquiv e _).trans hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨Units.map e.symm.toMonoidHom x, (Algebra.norm_eq_of_algEquiv e.symm _).trans hx⟩

/-- Every unit is a norm in a finite extension of an algebraically closed field. -/
@[simp]
theorem normGroup_eq_top_of_isAlgClosed (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAlgClosed K] [FiniteDimensional K L] : normGroup K L = ⊤ := by
  let e := AlgEquiv.ofBijective (Algebra.ofId K L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))
  rw [e.symm.normGroup_eq, normGroup_self]

/-- **The norm is Galois-equivariant.** For a tower `L/F/K` with `F/K` normal and an automorphism
`σ` of `L/K`, the restriction of `σ` to `F` carries the norm `N_{L/F}(x)` to `N_{L/F}(σ x)`. -/
@[simp]
theorem _root_.AlgEquiv.restrictNormal_norm {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Normal K F]
    (σ : L ≃ₐ[K] L) (x : L) :
    σ.restrictNormal F (Algebra.norm F x) = Algebra.norm F (σ x) := by
  rw [Algebra.norm_eq_of_equiv_equiv (σ.restrictNormal F).toRingEquiv σ.toRingEquiv
    (RingHom.ext (σ.restrictNormal_commutes F)) x]
  exact (σ.restrictNormal F).toRingEquiv.apply_symm_apply _

/-- **The norm on units is Galois-equivariant.** For a tower `L/F/K` with `F/K` normal and an
automorphism `σ` of `L/K`, the restriction of `σ` to `F` carries `N_{L/F}(z)` to `N_{L/F}(σ z)`
for every unit `z` of `L`. -/
theorem _root_.AlgEquiv.restrictNormal_smul_normUnits {K F L : Type*} [Field K] [Field F]
    [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Normal K F]
    (σ : L ≃ₐ[K] L) (z : Lˣ) :
    σ.restrictNormal F • Algebra.normUnits F z = Algebra.normUnits F (σ • z) :=
  Units.ext (by
    simpa only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
      Algebra.coe_normUnits] using σ.restrictNormal_norm (F := F) (z : L))

end TauCeti
