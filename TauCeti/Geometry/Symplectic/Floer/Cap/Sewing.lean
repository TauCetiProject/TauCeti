/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Basic
import Mathlib.Algebra.Torsor.Basic

/-!
# Sewing product cap classes

The class of a pair of pants relative to three reference caps is the difference between its
output reference cap and the cap obtained by gluing the inputs. For two composable pairs of
pants, this difference is the sum of the two component classes, regardless of the cap chosen
at the intermediate orbit. This is the cap bookkeeping needed for the coefficients of broken
products: the intermediate reference cap must cancel before the classes are used as Novikov
exponents.

`productClass_comp_fst` and `productClass_comp_snd` give the class-addition laws for the two
ways to insert a product into another product. `productClass_add_eq_add_iff` identifies equality
of the two sums with equality of the glued output caps. In particular, class agreement is not
assumed merely because the two configurations have the same external orbits.

These are torsor statements conditional on the equivariance of the given cap-gluing maps.
They do not construct gluing of geometric discs or identify the two glued maps. No regularity,
compactness, or associativity of Floer counts is asserted.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and the pair-of-pants product.
-/

public section

namespace TauCeti.Floer

variable {S : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {C₁ C₂ C₃ C₁₂ C₂₃ C₀ : Type*}
  [AddTorsor (PeriodGroup ω c) C₀]

/-- Sewing into the first input adds the component cap classes. The intermediate cap `D₁₂`
is arbitrary; only equivariance of the outer gluing in its sewn input is needed. The order is
outer class followed by inner class, so no commutative-group instance is required. -/
theorem productClass_comp_fst [AddTorsor (PeriodGroup ω c) C₁₂]
    (inner : C₁ → C₂ → C₁₂) (outer : C₁₂ → C₃ → C₀)
    (houter : ∀ (γ : PeriodGroup ω c) D₁₂ D₃,
      outer (γ +ᵥ D₁₂) D₃ = γ +ᵥ outer D₁₂ D₃)
    (D₁ : C₁) (D₂ : C₂) (D₃ : C₃) (D₁₂ : C₁₂) (D₀ : C₀) :
    productClass (fun D₁ D₂ => outer (inner D₁ D₂) D₃) D₁ D₂ D₀ =
      productClass outer D₁₂ D₃ D₀ + productClass inner D₁ D₂ D₁₂ := by
  have h := houter (D₁₂ -ᵥ inner D₁ D₂) (inner D₁ D₂) D₃
  rw [vsub_vadd] at h
  simp only [productClass_def, h, vsub_vadd_eq_vsub_sub, sub_add_cancel]

/-- Sewing into the second input adds the component cap classes, with cancellation of any
chosen intermediate cap `D₂₃`. Only equivariance in the sewn input of the outer gluing is used. -/
theorem productClass_comp_snd [AddTorsor (PeriodGroup ω c) C₂₃]
    (inner : C₂ → C₃ → C₂₃) (outer : C₁ → C₂₃ → C₀)
    (houter : ∀ (γ : PeriodGroup ω c) D₁ D₂₃,
      outer D₁ (γ +ᵥ D₂₃) = γ +ᵥ outer D₁ D₂₃)
    (D₁ : C₁) (D₂ : C₂) (D₃ : C₃) (D₂₃ : C₂₃) (D₀ : C₀) :
    productClass (fun D₂ D₃ => outer D₁ (inner D₂ D₃)) D₂ D₃ D₀ =
      productClass outer D₁ D₂₃ D₀ + productClass inner D₂ D₃ D₂₃ := by
  simpa only [productClass_def] using
    productClass_comp_fst inner (fun D₂₃ D₁ => outer D₁ D₂₃)
      (fun γ D₂₃ D₁ => houter γ D₁ D₂₃) D₂ D₃ D₁ D₂₃ D₀

/-- The sums of cap classes for the two decompositions of a three-input operation agree
exactly when their glued output caps agree. The intermediate caps on both sides are arbitrary.
Thus a geometric identification of the glued caps gives the required class agreement, without
an independent assumption about the periods or the reference caps. -/
theorem productClass_add_eq_add_iff
    [AddTorsor (PeriodGroup ω c) C₁₂] [AddTorsor (PeriodGroup ω c) C₂₃]
    (leftInner : C₁ → C₂ → C₁₂) (leftOuter : C₁₂ → C₃ → C₀)
    (rightInner : C₂ → C₃ → C₂₃) (rightOuter : C₁ → C₂₃ → C₀)
    (hleft : ∀ (γ : PeriodGroup ω c) D₁₂ D₃,
      leftOuter (γ +ᵥ D₁₂) D₃ = γ +ᵥ leftOuter D₁₂ D₃)
    (hright : ∀ (γ : PeriodGroup ω c) D₁ D₂₃,
      rightOuter D₁ (γ +ᵥ D₂₃) = γ +ᵥ rightOuter D₁ D₂₃)
    (D₁ : C₁) (D₂ : C₂) (D₃ : C₃) (D₁₂ : C₁₂) (D₂₃ : C₂₃) (D₀ : C₀) :
    productClass leftOuter D₁₂ D₃ D₀ + productClass leftInner D₁ D₂ D₁₂ =
        productClass rightOuter D₁ D₂₃ D₀ + productClass rightInner D₂ D₃ D₂₃ ↔
      leftOuter (leftInner D₁ D₂) D₃ = rightOuter D₁ (rightInner D₂ D₃) := by
  rw [← productClass_comp_fst leftInner leftOuter hleft D₁ D₂ D₃ D₁₂ D₀,
    ← productClass_comp_snd rightInner rightOuter hright D₁ D₂ D₃ D₂₃ D₀,
    productClass_def, productClass_def, vsub_right_cancel_iff]

end TauCeti.Floer
