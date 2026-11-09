/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Inner products on subcomodules

A subcomodule of an inner product space inherits the ambient inner product, just as its
underlying submodule does. This lets invariant subspaces of unitary comodules be treated as
inner product spaces without changing their native inherited coactions.
-/

public section

namespace TauCeti.Subcomodule

variable {𝕜 A M : Type*} [RCLike 𝕜] [AddCommMonoid A] [Module 𝕜 A] [Coalgebra 𝕜 A]
  [SeminormedAddCommGroup M] [InnerProductSpace 𝕜 M] [Comodule 𝕜 A M]

/-- The inner product on a subcomodule is the restricted inner product. -/
instance (W : Subcomodule 𝕜 A M) : InnerProductSpace 𝕜 W :=
  inferInstanceAs (InnerProductSpace 𝕜 W.toSubmodule)

/-- The inherited inner product agrees with the ambient inner product. -/
@[simp]
theorem coe_inner (W : Subcomodule 𝕜 A M) (x y : W) :
    inner 𝕜 x y = inner 𝕜 (x : M) (y : M) := (rfl)

/-- The inherited norm agrees with the ambient norm. -/
@[simp ←, norm_cast]
theorem norm_coe (W : Subcomodule 𝕜 A M) (x : W) : ‖(x : M)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜), coe_inner]

/-- The subcomodule inclusion preserves distances for the inherited inner product. -/
theorem isometry_subtype (W : Subcomodule 𝕜 A M) : Isometry (SMulMemClass.subtype W) := by
  apply (AddMonoidHomClass.isometry_iff_norm (SMulMemClass.subtype W)).mpr
  intro x
  rw [SMulMemClass.subtype_apply, norm_coe]

end TauCeti.Subcomodule
