/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.CyclicCohomology.Cohomology
import Mathlib.Tactic.LinearCombination

/-!
# Cyclic cocycles from a trace and derivations

Let `τ : A → M` be a trace on a possibly nonunital algebra `A`, so `τ (x * y) = τ (y * x)`,
and let `δ, δ₁, δ₂` be derivations of `A`. This file constructs the cochains

`ψ_δ(a₀, a₁) = τ(a₀ δ(a₁))` and
`φ_{δ₁,δ₂}(a₀, a₁, a₂) = τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`

and proves that they are cyclic cocycles of degrees one and two when `τ` is invariant under the
derivations, `τ ∘ δ = 0`, and, in degree two, the two derivations commute.

On the smooth noncommutative two-torus, with its canonical trace and its two basic derivations,
`ψ_{δ₁}` and `ψ_{δ₂}` are the odd cocycles and `(2πi)⁻¹ φ_{δ₁,δ₂}` is the even cocycle in Connes'
computation of its periodic cyclic cohomology. On the smooth functions on the circle, with `τ` the
integral in the angle `θ` and `δ = d/dθ`, `ψ_δ` is `2πi` times the circle cocycle
`(2πi)⁻¹ ∫ a₀ da₁`.

The Hochschild cocycle identities use only the Leibniz rule and the trace property. Cyclicity is
an integration by parts and also uses `τ ∘ δ = 0` and, in degree two, `δ₁ δ₂ = δ₂ δ₁`.

Only the outer part of the derivation matters in degree one: for an inner derivation `⁅z, -⁆`,
the cocycle `ψ` is the Hochschild coboundary of the `0`-cochain `a ↦ -τ(a z)`, so its cyclic class
vanishes.

## Main definitions

* `TauCeti.traceDerivationCochain`: the `1`-cochain `(a₀, a₁) ↦ τ(a₀ δ(a₁))`.
* `TauCeti.traceDerivationCocycle`: the same, as a cyclic `1`-cocycle.
* `TauCeti.traceDerivationPairCochain`: the `2`-cochain
  `(a₀, a₁, a₂) ↦ τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`.
* `TauCeti.traceDerivationPairCocycle`: the same, as a cyclic `2`-cocycle.

## Main results

* `TauCeti.hochschildCoboundary_traceDerivationCochain` and
  `TauCeti.hochschildCoboundary_traceDerivationPairCochain`: the cochains are Hochschild cocycles
  for every trace.
* `TauCeti.traceDerivationCochain_mem_cyclicCochains` and
  `TauCeti.traceDerivationPairCochain_mem_cyclicCochains`: they are cyclic.
* `TauCeti.traceDerivationCochain_innerDerivation` and
  `TauCeti.cyclicCohomology.mk_traceDerivationCocycle_innerDerivation`: the cocycle of an inner
  derivation is a coboundary.
* `TauCeti.traceDerivationCochain_compLinearMap` and
  `TauCeti.traceDerivationPairCochain_compLinearMap`: naturality under homomorphisms intertwining
  the derivations.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III.
-/

public section

namespace TauCeti

variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]

/-! ### The degree-one cocycle `τ(a₀ δ(a₁))` -/

section One

variable (τ : A →ₗ[k] M) (δ : derivationLieAlgebra k A)

/-- The `1`-cochain `(a₀, a₁) ↦ τ(a₀ δ(a₁))` of a linear map `τ` and a derivation `δ`. -/
def traceDerivationCochain : MultilinearMap k (fun _ : Fin 2 ↦ A) M :=
  MultilinearMap.mk' (fun a ↦ τ (a 0 * (δ : Module.End k A) (a 1)))
    (fun a i x y ↦ by fin_cases i <;> simp [mul_add, add_mul])
    (fun a i c x ↦ by fin_cases i <;> simp [smul_mul_assoc, mul_smul_comm])

variable {τ δ}

/-- The defining formula `τ(a₀ δ(a₁))`. -/
@[simp]
theorem traceDerivationCochain_apply (a : Fin 2 → A) :
    traceDerivationCochain τ δ a = τ (a 0 * (δ : Module.End k A) (a 1)) :=
  (rfl)

/-- For a trace `τ`, the cochain `(a₀, a₁) ↦ τ(a₀ δ(a₁))` is a Hochschild cocycle. -/
theorem hochschildCoboundary_traceDerivationCochain (hτ : ∀ x y, τ (x * y) = τ (y * x)) :
    hochschildCoboundary k A M 1 (traceDerivationCochain τ δ) = 0 := by
  ext a
  rw [hochschildCoboundary_one_apply]
  simp only [traceDerivationCochain_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    derivationLieAlgebra.leibniz, mul_add, map_add, zero_apply, ← mul_assoc]
  rw [mul_assoc (a 2), hτ (a 2)]
  abel

/-- For a trace `τ` with `τ ∘ δ = 0`, the cochain `(a₀, a₁) ↦ τ(a₀ δ(a₁))` is cyclic:
`τ(a₁ δ(a₀)) = -τ(a₀ δ(a₁))`. -/
theorem traceDerivationCochain_mem_cyclicCochains (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ : ∀ x, τ ((δ : Module.End k A) x) = 0) :
    traceDerivationCochain τ δ ∈ cyclicCochains k A M 1 := by
  rw [mem_cyclicCochains_one_iff]
  intro x y
  have h := hδ (y * x)
  rw [derivationLieAlgebra.leibniz, map_add, hτ ((δ : Module.End k A) y)] at h
  simp only [traceDerivationCochain_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eq_neg_of_add_eq_zero_right h]

/-- The cyclic `1`-cocycle `(a₀, a₁) ↦ τ(a₀ δ(a₁))` of a trace `τ` and a derivation `δ` with
`τ ∘ δ = 0`. -/
def traceDerivationCocycle (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ : ∀ x, τ ((δ : Module.End k A) x) = 0) : cyclicCocycles k A M 1 :=
  ⟨⟨traceDerivationCochain τ δ, traceDerivationCochain_mem_cyclicCochains hτ hδ⟩,
    (mem_cyclicCocycles_iff k A M).2 (hochschildCoboundary_traceDerivationCochain hτ)⟩

/-- The underlying cochain of `TauCeti.traceDerivationCocycle` is
`TauCeti.traceDerivationCochain`. -/
@[simp]
theorem coe_traceDerivationCocycle (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ : ∀ x, τ ((δ : Module.End k A) x) = 0) :
    ((traceDerivationCocycle hτ hδ : cyclicCochains k A M 1) :
      MultilinearMap k (fun _ : Fin 2 ↦ A) M) = traceDerivationCochain τ δ :=
  (rfl)

end One

/-! ### The degree-two cocycle `τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` -/

section Two

variable (τ : A →ₗ[k] M) (δ₁ δ₂ : derivationLieAlgebra k A)

/-- The `2`-cochain `(a₀, a₁, a₂) ↦ τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` of a linear map `τ`
and two derivations `δ₁`, `δ₂`. -/
def traceDerivationPairCochain : MultilinearMap k (fun _ : Fin 3 ↦ A) M :=
  MultilinearMap.mk'
    (fun a ↦ τ (a 0 * ((δ₁ : Module.End k A) (a 1) * (δ₂ : Module.End k A) (a 2) -
      (δ₂ : Module.End k A) (a 1) * (δ₁ : Module.End k A) (a 2))))
    (fun a i x y ↦ by fin_cases i <;> simp [mul_add, add_mul, mul_sub] <;> abel)
    (fun a i c x ↦ by fin_cases i <;> simp [smul_mul_assoc, mul_smul_comm, mul_sub, smul_sub])

variable {τ δ₁ δ₂}

/-- The defining formula `τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`. -/
@[simp]
theorem traceDerivationPairCochain_apply (a : Fin 3 → A) :
    traceDerivationPairCochain τ δ₁ δ₂ a =
      τ (a 0 * ((δ₁ : Module.End k A) (a 1) * (δ₂ : Module.End k A) (a 2) -
        (δ₂ : Module.End k A) (a 1) * (δ₁ : Module.End k A) (a 2))) :=
  (rfl)

variable (τ δ₁ δ₂) in
/-- Exchanging the two derivations changes the sign of the cochain. -/
theorem traceDerivationPairCochain_swap :
    traceDerivationPairCochain τ δ₂ δ₁ = -traceDerivationPairCochain τ δ₁ δ₂ := by
  ext a
  simp only [traceDerivationPairCochain_apply, neg_apply, ← map_neg, ← mul_neg,
    neg_sub]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- For a trace `τ` and a map `ω : A → A → A` with
`ω(x y, z) - ω(x, y z) = x ω(y, z) - ω(x, y) z`, the cochain `τ(a₀ ω(a₁, a₂))` satisfies the
Hochschild cocycle identity. -/
private theorem trace_mul_hochschild_eq_zero {τ : A →ₗ[k] M} (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (ω : A → A → A) (hω : ∀ x y z, ω (x * y) z - ω x (y * z) = x * ω y z - ω x y * z)
    (a₀ a₁ a₂ a₃ : A) :
    τ (a₀ * a₁ * ω a₂ a₃) - τ (a₀ * ω (a₁ * a₂) a₃) + τ (a₀ * ω a₁ (a₂ * a₃)) -
      τ (a₃ * a₀ * ω a₁ a₂) = 0 := by
  have h := congrArg (fun x ↦ τ (a₀ * x)) (hω a₁ a₂ a₃)
  simp only [mul_sub, map_sub, ← mul_assoc] at h
  rw [mul_assoc a₃, hτ a₃]
  linear_combination (norm := abel) -h

/-- For a trace `τ`, the cochain `(a₀, a₁, a₂) ↦ τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` is a
Hochschild cocycle. -/
theorem hochschildCoboundary_traceDerivationPairCochain (hτ : ∀ x y, τ (x * y) = τ (y * x)) :
    hochschildCoboundary k A M 2 (traceDerivationPairCochain τ δ₁ δ₂) = 0 := by
  ext a
  rw [hochschildCoboundary_two_apply]
  simp only [traceDerivationPairCochain_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zero_apply]
  refine trace_mul_hochschild_eq_zero hτ (fun x y ↦ (δ₁ : Module.End k A) x *
    (δ₂ : Module.End k A) y - (δ₂ : Module.End k A) x * (δ₁ : Module.End k A) y)
    (fun x y z ↦ ?_) _ _ _ _
  simp only [derivationLieAlgebra.leibniz, add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
  abel

/-- For a trace `τ` invariant under two commuting derivations `δ₁` and `δ₂`, the cochain
`(a₀, a₁, a₂) ↦ τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` is cyclic. -/
theorem traceDerivationPairCochain_mem_cyclicCochains (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ₁ : ∀ x, τ ((δ₁ : Module.End k A) x) = 0) (hδ₂ : ∀ x, τ ((δ₂ : Module.End k A) x) = 0)
    (hcomm : Commute (δ₁ : Module.End k A) δ₂) :
    traceDerivationPairCochain τ δ₁ δ₂ ∈ cyclicCochains k A M 2 := by
  rw [mem_cyclicCochains_two_iff]
  intro x y z
  -- Integrate by parts: `τ(δ₁(z x δ₂(y))) = 0` and `τ(δ₂(z x δ₁(y))) = 0`.
  have h₁ := hδ₁ (z * x * (δ₂ : Module.End k A) y)
  have h₂ := hδ₂ (z * x * (δ₁ : Module.End k A) y)
  have hc : (δ₁ : Module.End k A) ((δ₂ : Module.End k A) y) =
      (δ₂ : Module.End k A) ((δ₁ : Module.End k A) y) := LinearMap.congr_fun hcomm.eq y
  simp only [derivationLieAlgebra.leibniz, mul_add, map_add, hc, mul_assoc] at h₁ h₂
  -- Rotate the trace to move `δ_j(z)` from the end of the right-hand side to the front.
  have r₁ : τ (x * ((δ₁ : Module.End k A) y * (δ₂ : Module.End k A) z)) =
      τ ((δ₂ : Module.End k A) z * (x * (δ₁ : Module.End k A) y)) := by
    rw [← mul_assoc, hτ]
  have r₂ : τ (x * ((δ₂ : Module.End k A) y * (δ₁ : Module.End k A) z)) =
      τ ((δ₁ : Module.End k A) z * (x * (δ₂ : Module.End k A) y)) := by
    rw [← mul_assoc, hτ]
  simp only [traceDerivationPairCochain_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_sub, map_sub, r₁, r₂]
  linear_combination (norm := abel) h₁ - h₂

/-- The cyclic `2`-cocycle `(a₀, a₁, a₂) ↦ τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` of a trace `τ`
invariant under two commuting derivations `δ₁` and `δ₂`. -/
def traceDerivationPairCocycle (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ₁ : ∀ x, τ ((δ₁ : Module.End k A) x) = 0) (hδ₂ : ∀ x, τ ((δ₂ : Module.End k A) x) = 0)
    (hcomm : Commute (δ₁ : Module.End k A) δ₂) : cyclicCocycles k A M 2 :=
  ⟨⟨traceDerivationPairCochain τ δ₁ δ₂,
      traceDerivationPairCochain_mem_cyclicCochains hτ hδ₁ hδ₂ hcomm⟩,
    (mem_cyclicCocycles_iff k A M).2 (hochschildCoboundary_traceDerivationPairCochain hτ)⟩

/-- The underlying cochain of `TauCeti.traceDerivationPairCocycle` is
`TauCeti.traceDerivationPairCochain`. -/
@[simp]
theorem coe_traceDerivationPairCocycle (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hδ₁ : ∀ x, τ ((δ₁ : Module.End k A) x) = 0) (hδ₂ : ∀ x, τ ((δ₂ : Module.End k A) x) = 0)
    (hcomm : Commute (δ₁ : Module.End k A) δ₂) :
    ((traceDerivationPairCocycle hτ hδ₁ hδ₂ hcomm : cyclicCochains k A M 2) :
      MultilinearMap k (fun _ : Fin 3 ↦ A) M) = traceDerivationPairCochain τ δ₁ δ₂ :=
  (rfl)

end Two

/-! ### Naturality -/

section Naturality

variable {B : Type*} [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  (τ : A →ₗ[k] M) (f : B →ₙₐ[k] A)

/-- Pulling the cochain `τ(a₀ δ(a₁))` back along a homomorphism `f` intertwining derivations
`δ'` of the source and `δ` of the target gives the cochain of `τ ∘ f` and `δ'`. -/
theorem traceDerivationCochain_compLinearMap {δ : derivationLieAlgebra k A}
    {δ' : derivationLieAlgebra k B}
    (hf : ∀ b, f ((δ' : Module.End k B) b) = (δ : Module.End k A) (f b)) :
    (traceDerivationCochain τ δ).compLinearMap (fun _ ↦ (f : B →ₗ[k] A)) =
      traceDerivationCochain (τ ∘ₗ (f : B →ₗ[k] A)) δ' := by
  ext a
  simp [hf]

/-- Pulling the cochain `τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))` back along a homomorphism `f`
intertwining derivations `δ₁'`, `δ₂'` of the source with `δ₁`, `δ₂` gives the cochain of `τ ∘ f`
and `δ₁'`, `δ₂'`. -/
theorem traceDerivationPairCochain_compLinearMap {δ₁ δ₂ : derivationLieAlgebra k A}
    {δ₁' δ₂' : derivationLieAlgebra k B}
    (hf₁ : ∀ b, f ((δ₁' : Module.End k B) b) = (δ₁ : Module.End k A) (f b))
    (hf₂ : ∀ b, f ((δ₂' : Module.End k B) b) = (δ₂ : Module.End k A) (f b)) :
    (traceDerivationPairCochain τ δ₁ δ₂).compLinearMap (fun _ ↦ (f : B →ₗ[k] A)) =
      traceDerivationPairCochain (τ ∘ₗ (f : B →ₗ[k] A)) δ₁' δ₂' := by
  ext a
  simp [hf₁, hf₂]

end Naturality

end NonUnital

/-! ### Inner derivations -/

section Inner

variable {A : Type*} [Ring A] [Algebra k A] {τ : A →ₗ[k] M}

/-- For a trace `τ`, the cochain `(a₀, a₁) ↦ τ(a₀ ⁅z, a₁⁆)` of the inner derivation `⁅z, -⁆` is the
Hochschild coboundary of the `0`-cochain `a ↦ -τ(a z)`. -/
theorem traceDerivationCochain_innerDerivation (hτ : ∀ x y, τ (x * y) = τ (y * x)) (z : A) :
    traceDerivationCochain τ (innerDerivation k z) =
      hochschildCoboundary k A M 0
        (MultilinearMap.ofSubsingleton k A M (0 : Fin 1) (-(τ ∘ₗ LinearMap.mulRight k z))) := by
  ext a
  rw [hochschildCoboundary_zero_apply]
  simp only [traceDerivationCochain_apply, coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def,
    MultilinearMap.ofSubsingleton_apply_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, mul_sub, map_sub, ← mul_assoc]
  rw [mul_assoc (a 1), hτ (a 1)]
  abel

/-- A trace vanishes on the values `⁅z, x⁆` of an inner derivation. -/
theorem map_innerDerivation_apply_eq_zero (hτ : ∀ x y, τ (x * y) = τ (y * x)) (z x : A) :
    τ ((innerDerivation k z : Module.End k A) x) = 0 := by
  rw [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def, map_sub, hτ, sub_self]

/-- For a trace `τ`, the cyclic `1`-cocycle `(a₀, a₁) ↦ τ(a₀ ⁅z, a₁⁆)` of an inner derivation has
zero cyclic cohomology class. -/
theorem cyclicCohomology.mk_traceDerivationCocycle_innerDerivation
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (z : A) :
    cyclicCohomology.mk k A M 1
      (traceDerivationCocycle hτ (map_innerDerivation_apply_eq_zero hτ z)) = 0 := by
  rw [cyclicCohomology.mk_eq_zero_iff, mem_cyclicCoboundaries_succ_iff]
  refine ⟨⟨MultilinearMap.ofSubsingleton k A M (0 : Fin 1) (-(τ ∘ₗ LinearMap.mulRight k z)),
    by simp⟩, Subtype.ext ?_⟩
  rw [coe_cyclicHochschildCoboundary_apply, coe_traceDerivationCocycle,
    traceDerivationCochain_innerDerivation hτ]

end Inner

end TauCeti
