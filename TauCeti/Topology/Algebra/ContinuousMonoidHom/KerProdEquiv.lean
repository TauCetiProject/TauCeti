/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Splitting a commutative topological group along a continuous section

Let `f : G →ₜ* H` be a continuous homomorphism from a commutative topological group, and let
`s : H →ₜ* G` be a continuous homomorphic right inverse of `f`. Then `G` is isomorphic as a
topological group to the product of the kernel of `f` with `H`: an element `x` corresponds to its
kernel part `x · s(f x)⁻¹` and its image `f x`, with inverse `(k, t) ↦ k · s(t)`.

The kernel is given as any subgroup `N` with the same members as `f.ker`, so that a kernel with
its own name can be used directly.

## Main definitions

* `ContinuousMulEquiv.kerProdOfRightInverse` and `ContinuousAddEquiv.kerProdOfRightInverse`: the
  splitting `G ≃ₜ* N × H` determined by the section `s`.

## References

* N. Bourbaki, *General Topology*, Chapters 1–4, Springer (1989), Chapter III (Topological
  groups), § 6 (Products and direct sums).
-/

public section

/-- The kernel part `x · s(f x)⁻¹` of `x` lies in the kernel `N` of `f`. -/
@[to_additive /-- The kernel part `x - s(f x)` of `x` lies in the kernel `N` of `f`. -/]
theorem MonoidHom.mul_inv_apply_mem_of_rightInverse {G H : Type*} [Group G] [Group H]
    (f : G →* H) (s : H →* G) (hs : Function.RightInverse s f) {N : Subgroup G}
    (hN : ∀ x, x ∈ N ↔ f x = 1) (x : G) : x * (s (f x))⁻¹ ∈ N := by
  rw [hN, map_mul, map_inv, hs, mul_inv_cancel]

namespace ContinuousMulEquiv

variable {G H : Type*} [CommGroup G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] (f : G →ₜ* H) (s : H →ₜ* G) (hs : Function.RightInverse s f)
  {N : Subgroup G} (hN : ∀ x, x ∈ N ↔ f x = 1)

/-- **Splitting along a continuous section.** For a continuous homomorphism `f : G →ₜ* H` of a
commutative topological group with a continuous homomorphic right inverse `s`, the map
`x ↦ (x · s(f x)⁻¹, f x)` is an isomorphism of topological groups `G ≃ₜ* N × H`, where `N` is the
kernel of `f`. -/
@[to_additive kerProdOfRightInverse /-- **Splitting along a continuous section.** For a
continuous homomorphism `f : G →ₜ+ H` of a commutative topological additive group with a
continuous homomorphic right inverse `s`, the map `x ↦ (x - s(f x), f x)` is an isomorphism of
topological additive groups `G ≃ₜ+ N × H`, where `N` is the kernel of `f`. -/]
def kerProdOfRightInverse : G ≃ₜ* N × H where
  toFun x := (⟨x * (s (f x))⁻¹,
    f.toMonoidHom.mul_inv_apply_mem_of_rightInverse s.toMonoidHom hs hN x⟩, f x)
  invFun p := p.1 * s p.2
  left_inv x := by simp
  right_inv p := by
    have hp := (hN p.1).mp p.1.2
    ext
    · simp [hp, hs p.2]
    · simp [hp, hs p.2]
  map_mul' x y := by
    ext
    · simp only [Prod.fst_mul, Subgroup.coe_mul, map_mul, mul_inv]
      exact mul_mul_mul_comm x y _ _
    · exact map_mul f x y
  continuous_toFun :=
    ((continuous_id.mul (s.continuous.comp f.continuous).inv).subtype_mk _).prodMk f.continuous
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul (s.continuous.comp continuous_snd)

/-- The kernel component of the splitting is `x · s(f x)⁻¹`. -/
@[to_additive (attr := simp) coe_kerProdOfRightInverse_apply_fst /-- The kernel component of the
splitting is `x - s(f x)`. -/]
theorem coe_kerProdOfRightInverse_apply_fst (x : G) :
    ((kerProdOfRightInverse f s hs hN x).1 : G) = x * (s (f x))⁻¹ :=
  (rfl)

/-- The second component of the splitting is `f`. -/
@[to_additive (attr := simp) kerProdOfRightInverse_apply_snd /-- The second component of the
splitting is `f`. -/]
theorem kerProdOfRightInverse_apply_snd (x : G) : (kerProdOfRightInverse f s hs hN x).2 = f x :=
  (rfl)

/-- The inverse of the splitting multiplies a kernel element by the section. -/
@[to_additive (attr := simp) kerProdOfRightInverse_symm_apply /-- The inverse of the splitting
adds a kernel element to the section. -/]
theorem kerProdOfRightInverse_symm_apply (p : N × H) :
    (kerProdOfRightInverse f s hs hN).symm p = p.1 * s p.2 :=
  (rfl)

end ContinuousMulEquiv
