/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization

/-!
# Splitting a space along an equivariant map to the acting group

Let a group `G` with continuous inversion act continuously on a space `X`, and let `r : X → G` be a
continuous map that is equivariant for left multiplication, `r (a • x) = a * r x`. Then `X` is
homeomorphic to `G` times the fibre `{x | r x = 1}` (`TauCeti.homeomorphProdFiber`): a point `x`
goes to `(r x, (r x)⁻¹ • x)`, and a pair `(a, y)` goes back to `a • y`.

For `y` in the fibre, `r` maps the orbit `G • y` bijectively onto `G`, by `a • y ↦ a`, and
`z ↦ r z • y` is a retraction of `X` onto that orbit. The map `z ↦ (r z)⁻¹ • z` is the projection of
`X` onto the fibre, which meets every orbit exactly once. So the action is free, the fibre is a
global section of the orbit projection `X → X ⧸ G`, and `X` is a trivial principal `G`-bundle with
the fibre as base.

The homeomorphism is the chart `TauCeti.equivariantLocalSectionTrivialization` of the equivariant
map `r` to `G`, for `G` acting on itself by left multiplication, over all of `G`, with the identity
of `G` as section of the orbit map of `1`.

This is how the diffeomorphism group of a sphere splits as the orthogonal group times the fibre of
its orthogonal retraction, in `TauCeti.Geometry.Diffeomorphism.Sphere.OrthogonalRetraction`.

## Main definitions

* `TauCeti.homeomorphProdFiber r hr hrs`: the homeomorphism `X ≃ₜ G × {x // r x = 1}`.
-/

public section

open Bundle Set

namespace TauCeti

variable {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- **Splitting along an equivariant map to the acting group.** If `G` acts continuously on `X`
and `r : X → G` is continuous with `r (a • x) = a * r x`, then `X` is homeomorphic to `G` times
the fibre of `r` over `1`, by `x ↦ (r x, (r x)⁻¹ • x)` with inverse `(a, y) ↦ a • y`. This is the
chart `TauCeti.equivariantLocalSectionTrivialization` of `r` over all of `G`; when `X` is empty,
both sides are empty. -/
noncomputable def homeomorphProdFiber (r : X → G) (hr : Continuous r)
    (hrs : ∀ (a : G) x, r (a • x) = a * r x) : X ≃ₜ G × {x : X // r x = 1} :=
  letI := Classical.dec (Nonempty X)
  if hX : Nonempty X then
    -- The chart needs a point of the fibre; normalise any point of `X`.
    let e := equivariantLocalSectionTrivialization r hr (fun a x ↦ by rw [hrs, smul_eq_mul]) 1
      ⟨(r hX.some)⁻¹ • hX.some, by rw [hrs, inv_mul_cancel]⟩ univ isOpen_univ id continuousOn_id
      fun a _ ↦ mul_one a
    e.toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
      (by rw [e.source_eq, equivariantLocalSectionTrivialization_baseSet, preimage_univ])
      (by rw [e.target_eq, equivariantLocalSectionTrivialization_baseSet, univ_prod_univ])
  else
    haveI := not_nonempty_iff.mp hX
    Homeomorph.empty

variable {r : X → G} {hr : Continuous r} {hrs : ∀ (a : G) x, r (a • x) = a * r x}

@[simp]
theorem homeomorphProdFiber_apply_fst (x : X) : (homeomorphProdFiber r hr hrs x).1 = r x := by
  simp only [homeomorphProdFiber, (⟨x⟩ : Nonempty X), ↓reduceDIte]
  exact Trivialization.coe_fst' _
    (by rw [equivariantLocalSectionTrivialization_baseSet]; exact mem_univ _)

@[simp]
theorem coe_homeomorphProdFiber_apply_snd (x : X) :
    ((homeomorphProdFiber r hr hrs x).2 : X) = (r x)⁻¹ • x := by
  simp only [homeomorphProdFiber, (⟨x⟩ : Nonempty X), ↓reduceDIte]
  exact equivariantLocalSectionTrivialization_fiberCoordinate (mem_univ _)

@[simp]
theorem homeomorphProdFiber_symm_apply (y : G × {x : X // r x = 1}) :
    (homeomorphProdFiber r hr hrs).symm y = y.1 • (y.2 : X) := by
  simp only [homeomorphProdFiber, (⟨y.2⟩ : Nonempty X), ↓reduceDIte]
  exact equivariantLocalSectionTrivialization_symm_apply y

end TauCeti
