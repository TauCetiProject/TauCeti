/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Hom

import TauCeti.LinearAlgebra.RootSystem.Flip
import TauCeti.LinearAlgebra.RootSystem.HomInvariance.Basic

/-!
# Canonical bilinear forms under morphisms of root pairings

A morphism `f : P.Hom Q` of finite root pairings preserves the canonical root form `RootForm`:
its index bijection reindexes the sum of products of coroot values. Consequently, an equivalence
`e : P.Equiv Q` preserves and reflects anisotropy (`IsAnisotropic`). This file lives downstream of
`TauCeti.LinearAlgebra.RootSystem.HomInvariance.Basic` and
`Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear` without pulling in nondegeneracy,
invariant-form, or positive-definiteness theory.

## Main results

* `RootPairing.Hom.rootForm_weightMap`: a morphism of finite root pairings preserves the canonical
  root form.
* `RootPairing.Equiv.isAnisotropic` and `RootPairing.Equiv.isAnisotropic_iff`: an equivalence of
  finite root pairings preserves and reflects anisotropy.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  [Fintype ι] [Fintype ι₂]

/-- A morphism of finite root pairings preserves the canonical root form on weights. -/
@[simp]
theorem Hom.rootForm_weightMap (f : P.Hom Q) (x y : M) :
    Q.RootForm (f.weightMap x) (f.weightMap y) = P.RootForm x y := by
  simp only [RootPairing.rootForm_apply_apply]
  rw [← f.indexEquiv.sum_comp]
  simp only [Hom.coroot'_weightMap]

/-- An equivalence of finite root pairings transports anisotropy from the source to the target. -/
theorem Equiv.isAnisotropic (e : P.Equiv Q) [P.IsAnisotropic] : Q.IsAnisotropic where
  rootForm_root_ne_zero j := by
    obtain ⟨i, rfl⟩ := e.indexEquiv.surjective j
    rw [← Hom.root_weightMap_apply, e.toHom.rootForm_weightMap]
    exact IsAnisotropic.rootForm_root_ne_zero i
  corootForm_coroot_ne_zero j := by
    rw [CorootForm, ← e.toHom.flip.rootForm_weightMap, Hom.flip_weightMap,
      Hom.coroot_coweightMap_apply]
    exact IsAnisotropic.corootForm_coroot_ne_zero (e.indexEquiv.symm j)

/-- An equivalence of finite root pairings preserves and reflects anisotropy. -/
theorem Equiv.isAnisotropic_iff (e : P.Equiv Q) : P.IsAnisotropic ↔ Q.IsAnisotropic :=
  ⟨fun _ ↦ e.isAnisotropic, fun _ ↦ (Equiv.symm P Q e).isAnisotropic⟩

end RootPairing
