/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful

/-!
# Bounded ring homomorphisms

Mathlib defines a ring homomorphism `f : α →+* β` between seminormed rings to be bounded,
`RingHom.IsBounded f`, when `‖f x‖ ≤ C * ‖x‖` for some constant `C > 0`. This file shows that the
identity is bounded and that bounded homomorphisms compose, so that seminormed rings with bounded
homomorphisms form a category.

It also records the effect of the power trick on multiplicative seminorms: a multiplicative
seminorm `p` on `β` satisfies `p (f a) ≤ C * ‖a‖` for some `C > 0` exactly when it satisfies
`p (f a) ≤ ‖a‖`. Taking `f` to be the identity, the bounded multiplicative seminorms of a
seminormed ring are exactly those dominated by its norm; this is what makes the points of the
Berkovich spectrum contravariantly functorial along bounded homomorphisms.

## References

* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.2.
* M. Temkin, *Introduction to Berkovich analytic spaces*, Definition 2.2.2.1(i).
-/

public section

namespace RingHom

variable {α β γ : Type*}

section IsBounded

variable [SeminormedRing α] [SeminormedRing β] [SeminormedRing γ]

/-- The identity homomorphism of a seminormed ring is bounded. -/
theorem isBounded_id : (RingHom.id α).IsBounded :=
  ⟨1, one_pos, fun x => by simp⟩

/-- A composite of bounded ring homomorphisms is bounded. -/
theorem IsBounded.comp {g : β →+* γ} {f : α →+* β} (hg : g.IsBounded) (hf : f.IsBounded) :
    (g.comp f).IsBounded := by
  obtain ⟨C, hC, hgC⟩ := hg
  obtain ⟨D, hD, hfD⟩ := hf
  refine ⟨C * D, mul_pos hC hD, fun x => ?_⟩
  calc ‖g (f x)‖ ≤ C * ‖f x‖ := hgC (f x)
    _ ≤ C * (D * ‖x‖) := by gcongr; exact hfD x
    _ = C * D * ‖x‖ := (mul_assoc C D ‖x‖).symm

end IsBounded

/-- By the power trick, a multiplicative seminorm `p` on `β` is bounded along `f : α →+* β` by a
constant multiple of the norm of `α` exactly when it is bounded by the norm itself. -/
theorem isBoundedWrt_norm_iff {F : Type*} [SeminormedRing α] [Ring β] [FunLike F β ℝ]
    [MulRingSeminormClass F β ℝ] (p : F) (f : α →+* β) :
    f.IsBoundedWrt norm p ↔ ∀ a, p (f a) ≤ ‖a‖ := by
  refine ⟨fun hf a => ?_, fun h => ⟨1, one_pos, fun a => by simpa using h a⟩⟩
  -- `normRingSeminorm α` is the ring seminorm whose underlying function is `norm`.
  exact contraction_of_isPowMul_of_boundedWrt (normRingSeminorm α)
    (fun b n _ => map_pow p b n) hf a

end RingHom
