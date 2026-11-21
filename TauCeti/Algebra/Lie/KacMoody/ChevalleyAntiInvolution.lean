/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import TauCeti.Algebra.Lie.KacMoody.Basic

import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode

/-!
# The Chevalley anti-involution of a Kac–Moody enveloping algebra

The anti-involution exchanges `eᵢ` with `fᵢ` and fixes the whole Cartan realization, not just
its coroot span. It is an algebra equivalence to the opposite algebra, whose inverse acts by
the same operation after removing the opposite tag. Fixing the Cartan pointwise is what allows
contravariant duality to preserve weights.

The normalization is the anti-involution `σ` of V. G. Kac, *Infinite-dimensional Lie algebras*,
3rd ed., §9.4. The construction uses the ordinary enveloping antipode
`UniversalEnvelopingAlgebra.antipodeOp` and the signed swap `TauCeti.IsSerreSystem.neg_swap`.
Unlike the antipode, `σ` does not negate the Cartan elements.
-/

public section

open LieAlgebra MulOpposite UniversalEnvelopingAlgebra

namespace TauCeti.KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

local notation "𝔤" => PresentedLieAlgebra R
local notation "U" => UniversalEnvelopingAlgebra K 𝔤
local notation "ιₖ" => UniversalEnvelopingAlgebra.ι K

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Algebra homomorphisms out of the enveloping algebra of a presentation agree if they agree
on the Cartan, raising and lowering generators. -/
@[ext]
theorem envelopingHom_ext {B : Type*} [Ring B] [Algebra K B] {g₁ g₂ : U →ₐ[K] B}
    (hH : ∀ x, g₁ (ιₖ (cartanElement R x)) = g₂ (ιₖ (cartanElement R x)))
    (hE : ∀ i, g₁ (ιₖ (positiveGenerator R i)) = g₂ (ιₖ (positiveGenerator R i)))
    (hF : ∀ i, g₁ (ιₖ (negativeGenerator R i)) = g₂ (ιₖ (negativeGenerator R i))) : g₁ = g₂ :=
  UniversalEnvelopingAlgebra.hom_ext K <|
    KacMoody.hom_ext (g₁ := g₁.toLieHom.comp ιₖ) (g₂ := g₂.toLieHom.comp ιₖ) hH hE hF

/-- The Lie-algebra restriction of the enveloping algebra antipode. -/
private noncomputable def antipodeι : 𝔤 →ₗ⁅K⁆ Uᵐᵒᵖ :=
  (antipodeOp (L := 𝔤) K).toLieHom.comp ιₖ

private theorem neg_antipodeι_apply (x : 𝔤) : -antipodeι R x = op (ιₖ x) := by
  simp [antipodeι]

/-- The unsigned swap of raising and lowering generators respects the presentation in the
opposite enveloping algebra. -/
private theorem satisfiesRelations_chevalleyAntiInvolution :
    SatisfiesRelations R (-((antipodeι R).toLinearMap ∘ₗ cartanElement R))
      (fun i ↦ -antipodeι R (negativeGenerator R i))
      (fun i ↦ -antipodeι R (positiveGenerator R i)) := by
  have h := (satisfiesRelations_generators R).map (antipodeι R)
  have s := h.isSerreSystem.neg_swap
  refine ⟨?_, ?_, ?_, s.lie_E_F_self, s.lie_E_F_of_ne, s.ad_pow_lie_E_E, s.ad_pow_lie_F_F⟩
  · intro x y
    simpa using h.lie_cartan_cartan x y
  · intro x i
    simpa using h.lie_cartan_negative x i
  · intro x i
    simpa using h.lie_cartan_positive x i

private noncomputable def chevalleyAntiInvolutionHom : U →ₐ[K] Uᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift K (KacMoody.lift (satisfiesRelations_chevalleyAntiInvolution R))

private theorem opComm_comp_chevalleyAntiInvolutionHom :
    (AlgHom.opComm (chevalleyAntiInvolutionHom R)).comp (chevalleyAntiInvolutionHom R) =
      AlgHom.id K U := by
  apply envelopingHom_ext R <;> intro x <;>
    simp [chevalleyAntiInvolutionHom, neg_antipodeι_apply]

/-- The Chevalley anti-involution, as an algebra equivalence to the opposite enveloping algebra.
It fixes every Cartan element and interchanges the positive and negative generators. -/
noncomputable def chevalleyAntiInvolution : U ≃ₐ[K] Uᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (chevalleyAntiInvolutionHom R) (AlgHom.opComm (chevalleyAntiInvolutionHom R))
    (by
      apply AlgHom.ext
      intro a
      apply unop_injective
      simpa using DFunLike.congr_fun (opComm_comp_chevalleyAntiInvolutionHom R) a.unop)
    (opComm_comp_chevalleyAntiInvolutionHom R)

-- Use the simp normal form of `UniversalEnvelopingAlgebra.ι` so these rules also match after
-- `map_mul` or `map_pow` exposes a generator.

/-- The Chevalley anti-involution fixes each element of the Cartan realization. -/
@[simp]
theorem chevalleyAntiInvolution_ι_cartanElement (x : H) :
    chevalleyAntiInvolution R (mkAlgHom K 𝔤 (TensorAlgebra.ι K (cartanElement R x))) =
      op (ιₖ (cartanElement R x)) := by
  simp [chevalleyAntiInvolution, chevalleyAntiInvolutionHom, neg_antipodeι_apply]

/-- The Chevalley anti-involution sends each raising generator to its lowering generator. -/
@[simp]
theorem chevalleyAntiInvolution_ι_positiveGenerator (i : I) :
    chevalleyAntiInvolution R (mkAlgHom K 𝔤 (TensorAlgebra.ι K (positiveGenerator R i))) =
      op (ιₖ (negativeGenerator R i)) := by
  simp [chevalleyAntiInvolution, chevalleyAntiInvolutionHom, neg_antipodeι_apply]

/-- The Chevalley anti-involution sends each lowering generator to its raising generator. -/
@[simp]
theorem chevalleyAntiInvolution_ι_negativeGenerator (i : I) :
    chevalleyAntiInvolution R (mkAlgHom K 𝔤 (TensorAlgebra.ι K (negativeGenerator R i))) =
      op (ιₖ (positiveGenerator R i)) := by
  simp [chevalleyAntiInvolution, chevalleyAntiInvolutionHom, neg_antipodeι_apply]

/-- The inverse equivalence applies the same anti-involution on underlying elements. -/
theorem chevalleyAntiInvolution_symm_apply (a : Uᵐᵒᵖ) :
    (chevalleyAntiInvolution R).symm a = (chevalleyAntiInvolution R a.unop).unop := by
  rw [chevalleyAntiInvolution, AlgEquiv.ofAlgHom_symm]
  rfl

/-- The Chevalley anti-involution reverses adjoint Cartan weights in the enveloping algebra. -/
theorem chevalleyAntiInvolution_cartanWeight_iff (u : U) (μ : Module.Dual K H) :
    (∀ x, ⁅ιₖ (cartanElement R x), (chevalleyAntiInvolution R u).unop⁆ =
      (-μ x) • (chevalleyAntiInvolution R u).unop) ↔
    (∀ x, ⁅ιₖ (cartanElement R x), u⁆ = μ x • u) := by
  refine forall_congr' fun x ↦ ?_
  have heq := (chevalleyAntiInvolution R).injective.eq_iff (a := ⁅ιₖ (cartanElement R x), u⁆)
    (b := μ x • u)
  rw [← heq, ← unop_inj]
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_smul, ι_apply,
    chevalleyAntiInvolution_ι_cartanElement, unop_sub, unop_mul, unop_smul, unop_op, neg_smul]
  rw [← neg_eq_iff_eq_neg, neg_sub]

-- Check both the exchange of generators and the reversal of factors on `eᵢ² fᵢ`.
example (i : I) :
    (chevalleyAntiInvolution R ((ιₖ (positiveGenerator R i)) ^ 2 *
      ιₖ (negativeGenerator R i))).unop =
    ιₖ (positiveGenerator R i) * (ιₖ (negativeGenerator R i)) ^ 2 := by
  simp

end TauCeti.KacMoody
