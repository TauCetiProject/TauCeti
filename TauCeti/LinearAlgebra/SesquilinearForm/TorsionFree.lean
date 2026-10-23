/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Separating bilinear maps and torsion

A module carrying a bilinear map that is separating in its first argument, with values in a
torsion-free module over a domain, is itself torsion-free: if `r • x = 0` with `r ≠ 0`, then
`r • B x y = B (r • x) y = 0` forces `B x y = 0` for every `y`, so `x = 0`. For instance, an
abelian group carrying a nondegenerate integral bilinear form is torsion-free, hence flat over `ℤ`.

## Main results

* `LinearMap.SeparatingLeft.isTorsionFree`: a module with a left-separating bilinear map into a
  torsion-free module is torsion-free.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.IsTorsionFree R P]

/-- A module carrying a bilinear map that separates points in its first argument, with values in a
torsion-free module, is torsion-free. -/
theorem SeparatingLeft.isTorsionFree {B : M →ₗ[R] N →ₗ[R] P} (hB : B.SeparatingLeft) :
    Module.IsTorsionFree R M :=
  .of_smul_eq_zero fun r x hrx ↦ or_iff_not_imp_left.2 fun hr ↦ hB x fun y ↦ by
    simpa [hrx, hr] using (B.map_smul₂ r x y).symm

end LinearMap
