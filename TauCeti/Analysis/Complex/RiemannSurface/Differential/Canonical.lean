/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Divisor
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Ratio

/-!
# Canonical divisors of a compact Riemann surface

Two `1`-forms `η` and `ω` on a Riemann surface have, at every point, coefficients in a chart whose
ratio does not depend on the chart: changing chart multiplies both coefficients by the same
nonzero derivative of the transition map. This ratio is the function `η / ω`
(`TauCeti.RiemannSurface.OneForm.ratio`), meromorphic where `η` and `ω` are, and of order
`ord_x η - ord_x ω` at every point where `ω` has finite order
(`TauCeti.RiemannSurface.OneForm.meromorphicOrderAt_ratio_add_order`).

On a compact connected Riemann surface it follows that any two `1`-forms which are meromorphic and
of finite order everywhere differ by a nonzero meromorphic function, so their divisors differ by
the principal divisor of that function and are linearly equivalent
(`TauCeti.RiemannSurface.OneForm.linearlyEquivalent_divisor`). A **canonical divisor**
(`TauCeti.RiemannSurface.IsCanonicalDivisor`) is the divisor of such a `1`-form. The canonical
divisors form exactly one linear equivalence class: any two are linearly equivalent, and a divisor
linearly equivalent to a canonical divisor `div ω` is canonical, being the divisor of `f ω` for a
meromorphic function `f` (`TauCeti.RiemannSurface.IsCanonicalDivisor.isCanonicalDivisor_iff`).
That a canonical divisor exists, i.e. that a nonzero meromorphic `1`-form exists, is not proved
here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the divisor of a meromorphic `1`-form and the canonical divisor class).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V §1 (canonical divisors).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry WeilDivisor

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace OneForm

variable [IsManifold 𝓘(ℂ) 1 X] {ω η : OneForm X}

section Connected

variable [ConnectedSpace X]

/-- The ratio `η / ω` of two `1`-forms meromorphic everywhere, as a meromorphic function. -/
def ratioFunction (η ω : OneForm X) (hη : ∀ x, η.MeromorphicAt x) (hω : ∀ x, ω.MeromorphicAt x) :
    MeromorphicFunction X :=
  MeromorphicFunction.ofMeromorphic fun x ↦ meromorphicAt_ratio (hη x) (hω x)

/-- Division by a fixed meromorphic differential is additive in the numerator. -/
theorem ratioFunction_add {θ : OneForm X} (hη : ∀ x, η.MeromorphicAt x)
    (hθ : ∀ x, θ.MeromorphicAt x) (hω : ∀ x, ω.MeromorphicAt x) :
    ratioFunction (η + θ) ω (fun x ↦ (hη x).add (hθ x)) hω =
      ratioFunction η ω hη hω + ratioFunction θ ω hθ hω := by
  have hadd : ratio (η + θ) ω = ratio η ω + ratio θ ω := by
    funext x
    simp only [ratio_def, coeff_add, Pi.add_apply, add_div]
  simpa only [ratioFunction, hadd] using
    (MeromorphicFunction.ofMeromorphic_add
      (fun x ↦ meromorphicAt_ratio (hη x) (hω x))
      (fun x ↦ meromorphicAt_ratio (hθ x) (hω x)))

/-- Division by a fixed meromorphic differential respects complex scalars in the numerator. -/
theorem ratioFunction_smul (c : ℂ) (hη : ∀ x, η.MeromorphicAt x)
    (hω : ∀ x, ω.MeromorphicAt x) :
    ratioFunction (c • η) ω (fun x ↦ (hη x).const_smul c) hω =
      c • ratioFunction η ω hη hω := by
  have hsmul : ratio (c • η) ω = (fun _ ↦ c) * ratio η ω := by
    funext x
    simp only [ratio_def, coeff_const_smul, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul, mul_div_assoc]
  simpa only [ratioFunction, hsmul, Algebra.smul_def, MeromorphicFunction.ofMeromorphic_const]
    using (MeromorphicFunction.ofMeromorphic_mul
      (fun x ↦ meromorphicAt_const c x) (fun x ↦ meromorphicAt_ratio (hη x) (hω x)))

variable (hη : ∀ x, η.MeromorphicAt x) (hω : ∀ x, ω.MeromorphicAt x)
include hη hω

/-- The finite part of the meromorphic function `η / ω` agrees with the pointwise ratio
`TauCeti.RiemannSurface.OneForm.ratio η ω` on a punctured neighbourhood of every point. -/
theorem finitePart_ratioFunction_eventuallyEq (x : X) :
    (ratioFunction η ω hη hω).finitePart =ᶠ[𝓝[≠] x] ratio η ω :=
  MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq _ x

/-- **`ord_x (η / ω) + ord_x ω = ord_x η`** for the ratio as a meromorphic function, at a point
where `ω` has finite order. -/
theorem order_ratioFunction_add_order {x : X} (hx : ω.order x ≠ ⊤) :
    MeromorphicFunction.order x (ratioFunction η ω hη hω) + ω.order x = η.order x := by
  rw [MeromorphicFunction.order_apply, RiemannSurface.meromorphicOrderAt_congr
    (finitePart_ratioFunction_eventuallyEq hη hω x)]
  exact meromorphicOrderAt_ratio_add_order (hη x) (hω x) hx

/-- If `η` and `ω` both have finite order at some point, their ratio is a nonzero meromorphic
function. -/
theorem ratioFunction_ne_zero (h : ∃ x, ω.order x ≠ ⊤ ∧ η.order x ≠ ⊤) :
    ratioFunction η ω hη hω ≠ 0 := by
  intro hf
  obtain ⟨x, hωx, hηx⟩ := h
  have := order_ratioFunction_add_order hη hω hωx
  rw [hf, AddValuation.map_zero, WithTop.top_add] at this
  exact hηx this.symm

variable [CompactSpace X] (hω₀ : ∀ x, ω.order x ≠ ⊤)
include hω₀


/-- **Divisors of `1`-forms differ by a principal divisor.** On a compact connected Riemann
surface, if `η` and `ω` are meromorphic and of finite order everywhere then
`div η = div (η / ω) + div ω`. -/
theorem divisor_eq_principalDivisor_add (hη₀ : ∀ x, η.order x ≠ ⊤) :
    η.divisor = (MeromorphicFunction.orderSystem X).principalDivisor
      (Additive.ofMul (Units.mk0 _ (ratioFunction_ne_zero hη hω
        ⟨Classical.arbitrary X, hω₀ _, hη₀ _⟩))) + ω.divisor := by
  have hne := ratioFunction_ne_zero hη hω ⟨Classical.arbitrary X, hω₀ _, hη₀ _⟩
  refine WeilDivisor.ext fun x ↦ ?_
  have hp := MeromorphicFunction.coe_coeff_principalDivisor_orderSystem
    (Additive.ofMul (Units.mk0 _ hne)) x
  simp only [toMul_ofMul, Units.val_mk0] at hp
  have hf₀ : MeromorphicFunction.order x (ratioFunction η ω hη hω) ≠ ⊤ :=
    (MeromorphicFunction.order x).ne_top_iff.2 hne
  rw [WeilDivisor.coeff_add, coeff_divisor hη, coeff_divisor hω,
    ← order_ratioFunction_add_order hη hω (hω₀ x), WithTop.untop₀_add hf₀ (hω₀ x), ← hp,
    WithTop.untop₀_coe]

/-- **Divisors of `1`-forms are linearly equivalent.** On a compact connected Riemann surface, the
divisors of two `1`-forms meromorphic and of finite order everywhere are linearly equivalent. -/
theorem linearlyEquivalent_divisor (hη₀ : ∀ x, η.order x ≠ ⊤) :
    (MeromorphicFunction.orderSystem X).LinearlyEquivalent η.divisor ω.divisor :=
  (MeromorphicFunction.orderSystem X).linearlyEquivalent_iff_exists_principalDivisor.2
    ⟨_, by rw [divisor_eq_principalDivisor_add hη hω hω₀ hη₀, add_sub_cancel_right]⟩

end Connected

end OneForm

section Canonical

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]

/-- A divisor `K` on a compact Riemann surface is **canonical** if it is the divisor of
a `1`-form which is meromorphic and of finite order at every point. -/
def IsCanonicalDivisor (K : WeilDivisor X) : Prop :=
  ∃ ω : OneForm X, (∀ x, ω.MeromorphicAt x) ∧ (∀ x, ω.order x ≠ ⊤) ∧ ω.divisor = K

/-- The divisor of a `1`-form meromorphic and of finite order everywhere is canonical. -/
theorem isCanonicalDivisor_divisor {ω : OneForm X} (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) : IsCanonicalDivisor ω.divisor :=
  ⟨ω, hω, hω₀, rfl⟩

/-- A canonical divisor is the divisor of a `1`-form meromorphic and of finite order
everywhere. -/
theorem IsCanonicalDivisor.exists_divisor_eq {K : WeilDivisor X} (hK : IsCanonicalDivisor K) :
    ∃ ω : OneForm X, (∀ x, ω.MeromorphicAt x) ∧ (∀ x, ω.order x ≠ ⊤) ∧ ω.divisor = K :=
  hK

namespace IsCanonicalDivisor

variable [ConnectedSpace X] {K K' D : WeilDivisor X}

/-- **Any two canonical divisors are linearly equivalent.** -/
theorem linearlyEquivalent (hK : IsCanonicalDivisor K) (hK' : IsCanonicalDivisor K') :
    (MeromorphicFunction.orderSystem X).LinearlyEquivalent K K' := by
  obtain ⟨η, hη, hη₀, rfl⟩ := hK
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK'
  exact OneForm.linearlyEquivalent_divisor hη hω hω₀ hη₀

/-- A divisor linearly equivalent to a canonical divisor is canonical. -/
theorem of_linearlyEquivalent (hK : IsCanonicalDivisor K)
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D K) :
    IsCanonicalDivisor D := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK
  obtain ⟨u, hu⟩ :=
    (MeromorphicFunction.orderSystem X).linearlyEquivalent_iff_exists_principalDivisor.1 h
  set f : MeromorphicFunction X := (Additive.toMul u).1
  have hf : f ≠ 0 := (Additive.toMul u).ne_zero
  have hfω (x : X) : (f.finitePart • ω).MeromorphicAt x :=
    (hω x).smul (f.meromorphicAt_finitePart x)
  refine ⟨f.finitePart • ω, hfω, fun x ↦ ?_, ?_⟩
  · rw [OneForm.order_smul (f.meromorphicAt_finitePart x) (hω x),
      ← MeromorphicFunction.order_apply]
    exact WithTop.add_ne_top.2 ⟨(MeromorphicFunction.order x).ne_top_iff.2 hf, hω₀ x⟩
  · rw [OneForm.divisor_smul f hf hω hω₀]
    have hu' : Additive.ofMul (Units.mk0 f hf) = u := by
      ext
      rfl
    rw [hu', hu, sub_add_cancel]

/-- **The canonical divisors form one linear equivalence class.** Given a canonical divisor `K`,
a divisor is canonical exactly when it is linearly equivalent to `K`. -/
theorem isCanonicalDivisor_iff (hK : IsCanonicalDivisor K) :
    IsCanonicalDivisor D ↔ (MeromorphicFunction.orderSystem X).LinearlyEquivalent D K :=
  ⟨fun hD ↦ hD.linearlyEquivalent hK, hK.of_linearlyEquivalent⟩

end IsCanonicalDivisor

end Canonical

end TauCeti.RiemannSurface
