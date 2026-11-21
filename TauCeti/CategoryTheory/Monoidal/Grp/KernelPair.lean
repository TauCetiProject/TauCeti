/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel pairs of homomorphisms of group objects

For a homomorphism `f : G ⟶ H` from a group object to a monoid object, with kernel
`i : K ⟶ G`, the square with upper map `(k, g) ↦ i(k) * g` and left map `(k, g) ↦ g`
is cartesian. Thus the kernel pair of `f` is `K × G`, even when `f` is not an epimorphism.
This is the geometric identity used to transfer properties of a kernel to a faithfully flat
homomorphism of group schemes.

The kernel is specified by its pullback square over the identity, so the result also applies
to an unbundled group object and a chosen model of its kernel. Neither commutativity nor a
group structure on the chosen kernel or on the target is needed.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {K G H : C} [GrpObj G] [MonObj H]

/-- The kernel pair of a monoid homomorphism from a group object is the product of its kernel
with its source, with the two projections given by multiplication and the second projection. -/
theorem isPullback_mul_of_isPullback_one (f : G ⟶ H) [IsMonHom f] (i : K ⟶ G)
    (h : IsPullback i (toUnit K) f η[H]) :
    IsPullback ((fst K G ≫ i) * snd K G) (snd K G) f f := by
  refine IsPullback.of_isLimit' ⟨by simp [MonObj.mul_comp, h.w, ← Hom.one_def]⟩ ?_
  let k (s : PullbackCone f f) : s.pt ⟶ K :=
    h.lift (s.fst * s.snd⁻¹) (toUnit s.pt) (by
      rw [MonObj.mul_comp, s.condition, ← MonObj.mul_comp]
      simp [Hom.one_def])
  have hk (s : PullbackCone f f) : k s ≫ i = s.fst * s.snd⁻¹ := h.lift_fst ..
  refine PullbackCone.IsLimit.mk _ (fun s ↦ lift (k s) s.snd) (by simp [MonObj.comp_mul, hk])
    (by simp) fun s m hm₁ hm₂ ↦ hom_ext _ _ (h.hom_ext ?_ (by simp)) (by simpa using hm₂)
  simpa [hk, eq_mul_inv_iff_mul_eq, ← hm₂, MonObj.comp_mul] using hm₁

end TauCeti
