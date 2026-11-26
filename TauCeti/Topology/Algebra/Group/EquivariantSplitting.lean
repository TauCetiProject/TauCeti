/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Splitting a space along an equivariant map to the acting group

Let a group `G` with continuous inversion act continuously on a space `X`, and let `r : X → G` be a
continuous map that is equivariant for left multiplication, `r (a • x) = a * r x`. Then `X` is
homeomorphic to `G` times the fibre `{x | r x = 1}` (`TauCeti.homeomorphProdFiber`): a point `x`
goes to `(r x, (r x)⁻¹ • x)`, and a pair `(a, y)` goes back to `a • y`. The map `r` is a
retraction onto each orbit `G • x` with `r x = 1`, and the homeomorphism says that `X` is a
trivial principal `G`-bundle over the fibre.

This is how the diffeomorphism group of a sphere splits as the orthogonal group times the fibre of
its orthogonal retraction, in `TauCeti.Geometry.Diffeomorphism.Sphere.OrthogonalRetraction`.

## Main definitions

* `TauCeti.homeomorphProdFiber r hr hrs`: the homeomorphism `X ≃ₜ G × {x // r x = 1}`.
-/

public section

namespace TauCeti

variable {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- **Splitting along an equivariant map to the acting group.** If `G` acts continuously on `X`
and `r : X → G` is continuous with `r (a • x) = a * r x`, then `X` is homeomorphic to `G` times
the fibre of `r` over `1`, by `x ↦ (r x, (r x)⁻¹ • x)` with inverse `(a, y) ↦ a • y`. -/
def homeomorphProdFiber (r : X → G) (hr : Continuous r) (hrs : ∀ (a : G) x, r (a • x) = a * r x) :
    X ≃ₜ G × {x : X // r x = 1} where
  toFun x := (r x, ⟨(r x)⁻¹ • x, (hrs _ x).trans (inv_mul_cancel _)⟩)
  invFun y := y.1 • (y.2 : X)
  left_inv x := smul_inv_smul (r x) x
  right_inv := by
    rintro ⟨a, x, hx⟩
    have ha : r (a • x) = a := by rw [hrs, hx, mul_one]
    ext : 1
    · exact ha
    · exact Subtype.ext (by simp only [ha, inv_smul_smul])
  continuous_toFun := hr.prodMk ((hr.inv.smul continuous_id).subtype_mk _)
  continuous_invFun := continuous_fst.smul (continuous_subtypeVal.comp continuous_snd)

variable (r : X → G) (hr : Continuous r) (hrs : ∀ (a : G) x, r (a • x) = a * r x)

@[simp]
theorem homeomorphProdFiber_apply_fst (x : X) : (homeomorphProdFiber r hr hrs x).1 = r x :=
  (rfl)

@[simp]
theorem coe_homeomorphProdFiber_apply_snd (x : X) :
    ((homeomorphProdFiber r hr hrs x).2 : X) = (r x)⁻¹ • x :=
  (rfl)

@[simp]
theorem homeomorphProdFiber_symm_apply (y : G × {x : X // r x = 1}) :
    (homeomorphProdFiber r hr hrs).symm y = y.1 • (y.2 : X) :=
  (rfl)

end TauCeti
