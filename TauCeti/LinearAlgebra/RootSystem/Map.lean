/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# Transporting a root pairing onto a module and its linear dual

Given a root pairing `P : RootPairing ι R M N`, an index bijection `e : ι ≃ ι₂`, and a linear
equivalence `f : M ≃ₗ[R] M₂`, `RootPairing.mapDual P e f` transports `P` onto `M₂` paired with its
linear dual `Module.Dual R M₂` by evaluation, and `RootPairing.equivMapDual P e f` packages `(e, f)`
as the canonical equivalence `P.Equiv (P.mapDual e f)`.

## Main definitions

* `RootPairing.mapDual`: transport of `P` along `e : ι ≃ ι₂` and `f : M ≃ₗ[R] M₂` onto `M₂` and
  `Module.Dual R M₂` paired by `Module.Dual.eval R M₂`.
* `RootPairing.equivMapDual`: the canonical equivalence `P.Equiv (P.mapDual e f)`.
-/

public section

namespace RootPairing

variable {ι ι₂ R M N M₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂]
  (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂)

/-- Transport a root pairing along an index bijection `e : ι ≃ ι₂` and weight-space equivalence
`f : M ≃ₗ[R] M₂` onto `M₂` paired with its linear dual `Module.Dual R M₂` by evaluation. -/
noncomputable def mapDual : RootPairing ι₂ R M₂ (Module.Dual R M₂) :=
  P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)

instance [P.IsRootSystem] : (P.mapDual e f).IsRootSystem :=
  inferInstanceAs (P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)).IsRootSystem

@[simp]
theorem mapDual_toLinearMap :
    (P.mapDual e f).toLinearMap = Module.Dual.eval R M₂ := by
  ext x φ
  simp [mapDual, RootPairing.map]

theorem mapDual_toLinearMap_apply (x : M₂) (φ : Module.Dual R M₂) :
    (P.mapDual e f).toLinearMap x φ = φ x := by
  simp

@[simp]
theorem mapDual_root_apply (i : ι₂) :
    (P.mapDual e f).root i = f (P.root (e.symm i)) := by
  rfl

@[simp]
theorem mapDual_coroot (i : ι₂) :
    (P.mapDual e f).coroot i = (P.coroot' (e.symm i)).comp f.symm.toLinearMap := by
  ext x
  simp [mapDual, RootPairing.map, coroot']

theorem mapDual_coroot_apply (i : ι₂) (x : M₂) :
    (P.mapDual e f).coroot i x = P.coroot' (e.symm i) (f.symm x) := by
  simp

/-- The canonical equivalence of root pairings from `P` to `P.mapDual e f`. -/
noncomputable def equivMapDual : P.Equiv (P.mapDual e f) where
  weightMap := f.toLinearMap
  coweightMap := (P.flip.toPerfPair.trans f.symm.dualMap).symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by
    ext φ x
    simp
  root_weightMap := by
    ext i
    simp
  coroot_coweightMap := by
    ext i
    apply P.flip.toPerfPair.injective
    ext y
    simp [coroot']
  bijective_weightMap := f.bijective
  bijective_coweightMap := (P.flip.toPerfPair.trans f.symm.dualMap).symm.bijective

@[simp]
theorem equivMapDual_weightMap :
    (P.equivMapDual e f).weightMap = f.toLinearMap := by
  rfl

@[simp]
theorem equivMapDual_weightEquiv :
    (P.equivMapDual e f).weightEquiv = f :=
  LinearEquiv.ext fun _ ↦ rfl

@[simp]
theorem equivMapDual_coweightMap :
    (P.equivMapDual e f).coweightMap =
      (P.flip.toPerfPair.trans f.symm.dualMap).symm.toLinearMap := by
  rfl

@[simp]
theorem equivMapDual_indexEquiv :
    (P.equivMapDual e f).indexEquiv = e := by
  rfl

end RootPairing
