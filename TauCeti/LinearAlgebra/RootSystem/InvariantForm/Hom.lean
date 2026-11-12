/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# The canonical root form under morphisms

A morphism of finite root pairings preserves the canonical root form: its index bijection
reindexes the sum of products of coroot values. The weight map need not be bijective, and the
roots need not span the weight space. In particular diagram automorphisms preserve lengths
also on weights outside the root lattice.
-/

public section

namespace RootPairing.Hom

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  [Fintype ι] [Fintype ι₂]

/-- A morphism of finite root pairings preserves the canonical root form on weights. -/
@[simp]
theorem rootForm_weightMap (f : P.Hom Q) (x y : M) :
    Q.RootForm (f.weightMap x) (f.weightMap y) = P.RootForm x y := by
  have h (i : ι) (z : M) : Q.coroot' (f.indexEquiv i) (f.weightMap z) = P.coroot' i z := by
    simpa [RootPairing.coroot', Hom.coroot_coweightMap_apply] using
      congrArg (fun g : Module.Dual R M ↦ g z)
        (f.weight_coweight_transpose_apply P Q (Q.coroot (f.indexEquiv i)))
  simp only [RootPairing.rootForm_apply_apply]
  rw [← f.indexEquiv.sum_comp]
  simp only [h]

end RootPairing.Hom
