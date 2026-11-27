/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Geometry.Lie.EnvelopingAlgebra.Faithful
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation
public import TauCeti.Geometry.Manifold.Algebra.TypeTags

/-!
# Check: on the real line, `X²` is nonzero but kills the affine functions

Let `G = ℝ`, written multiplicatively as `Multiplicative ℝ` so that Mathlib's left-invariant
derivations apply, and let `X` be a left-invariant derivation of `C^∞(ℝ)`, such as `d/dx`.

* `X` sends every affine function `x ↦ a + b x` to a constant function: translating an affine
  function changes it by a constant, which `X` kills, so by left invariance `X f` is constant
  (`TauCeti.Examples.RealLineEnveloping.apply_eq_of_affine`). Hence `X²`, acting through
  `TauCeti.envelopingAction`, is `0` on the affine functions, the polynomials of degree at most one
  (`TauCeti.Examples.RealLineEnveloping.envelopingAction_ι_mul_ι_apply_of_affine`).
* For `X ≠ 0` (such `X` exist, `TauCeti.Examples.RealLineEnveloping.exists_ne_zero`), the element
  `X²` of `U(𝔤)` is nonzero, since `U(𝔤)` of the abelian `𝔤` is a polynomial ring, and the action
  of `U(𝔤)` on all of `C^∞(ℝ)` is faithful (`TauCeti.envelopingAction_injective`), so `X²` acts by
  a nonzero operator (`TauCeti.Examples.RealLineEnveloping.envelopingAction_ι_mul_ι_ne_zero`).

So faithfulness needs the action on all smooth functions, not on a finite-dimensional space of
them.
-/

public section

open scoped Manifold ContDiff LieGroup

noncomputable section

namespace TauCeti.Examples.RealLineEnveloping

/-- The real line as a Lie group, written multiplicatively. -/
abbrev RealLine : Type := Multiplicative ℝ

variable (X : LeftInvariantDerivation 𝓘(ℝ, ℝ) RealLine)

/-- A left-invariant derivation kills the constant functions. -/
theorem apply_algebraMap (c : ℝ) :
    X (algebraMap ℝ C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯ c) = 0 :=
  X.toDerivation.map_algebraMap c

/-- **A left-invariant derivation of `ℝ` sends an affine function to a constant function.** -/
theorem apply_eq_of_affine {f : C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯} {a b : ℝ}
    (hf : ∀ x, f x = a + b * x.toAdd) (g : RealLine) : X f g = X f 1 := by
  have hcomp : f.comp (𝑳 𝓘(ℝ, ℝ) g) =
      f + algebraMap ℝ C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯ (b * g.toAdd) := by
    ext x
    change f (g * x) = f x + b * g.toAdd
    rw [hf, hf, toAdd_mul]
    ring
  have h := congrArg (fun φ : C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯ ↦ φ 1)
    (LeftInvariantDerivation.comp_L (X := X) (f := f) (g := g))
  simp only [ContMDiffMap.comp_apply, L_apply, mul_one, hcomp, map_add, apply_algebraMap,
    add_zero] at h
  exact h

/-- A left-invariant derivation of `ℝ` sends an affine function to the constant `X f 1`. -/
theorem apply_of_affine_eq_algebraMap {f : C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯} {a b : ℝ}
    (hf : ∀ x, f x = a + b * x.toAdd) :
    X f = algebraMap ℝ C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯ (X f 1) := by
  ext g
  exact apply_eq_of_affine X hf g

/-- **`X²` kills the affine functions**, the polynomials of degree at most one. -/
theorem envelopingAction_ι_mul_ι_apply_of_affine {f : C^∞⟮𝓘(ℝ, ℝ), RealLine; ℝ⟯} {a b : ℝ}
    (hf : ∀ x, f x = a + b * x.toAdd) :
    envelopingAction 𝓘(ℝ, ℝ) RealLine
      (UniversalEnvelopingAlgebra.ι ℝ X * UniversalEnvelopingAlgebra.ι ℝ X) f = 0 := by
  rw [map_mul, mul_apply_eq_comp, LeftInvariantDerivation.envelopingAction_ι,
    LeftInvariantDerivation.leftInvariantDerivationToEnd_apply,
    LeftInvariantDerivation.leftInvariantDerivationToEnd_apply, apply_of_affine_eq_algebraMap X hf,
    apply_algebraMap]

/-- The real line has a nonzero left-invariant derivation. -/
theorem exists_ne_zero : ∃ X : LeftInvariantDerivation 𝓘(ℝ, ℝ) RealLine, X ≠ 0 := by
  let e := leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, ℝ)) (G := RealLine)
    BoundarylessManifold.isInteriorPoint
  have : Nontrivial (GroupLieAlgebra 𝓘(ℝ, ℝ) RealLine) := inferInstanceAs (Nontrivial ℝ)
  obtain ⟨v, hv⟩ := exists_ne (0 : GroupLieAlgebra 𝓘(ℝ, ℝ) RealLine)
  exact ⟨e.symm v, by simpa using hv⟩

/-- **`X²` acts by a nonzero operator on `C^∞(ℝ)` for `X ≠ 0`.** -/
theorem envelopingAction_ι_mul_ι_ne_zero (hX : X ≠ 0) :
    envelopingAction 𝓘(ℝ, ℝ) RealLine
      (UniversalEnvelopingAlgebra.ι ℝ X * UniversalEnvelopingAlgebra.ι ℝ X) ≠ 0 := by
  let U := UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation 𝓘(ℝ, ℝ) RealLine)
  let b := Module.Basis.ofVectorSpace ℝ (LeftInvariantDerivation 𝓘(ℝ, ℝ) RealLine)
  have : NoZeroDivisors U :=
    (UniversalEnvelopingAlgebra.mvPolynomialEquiv ℝ _ b).symm.injective.noZeroDivisors _
      (map_zero _) (map_mul _)
  have hι : UniversalEnvelopingAlgebra.ι ℝ X ≠ 0 := fun h ↦
    hX (UniversalEnvelopingAlgebra.ι_injective_of_isLieAbelian ℝ _ (by rw [h, map_zero]))
  exact (map_ne_zero_iff _ envelopingAction_injective).mpr (mul_self_ne_zero.mpr hι)

end TauCeti.Examples.RealLineEnveloping
