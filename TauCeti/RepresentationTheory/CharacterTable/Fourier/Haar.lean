/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Fourier
public import TauCeti.RepresentationTheory.Compact.MonoidAlgebra

/-!
# Finite Fourier transform with probability Haar measure

The coefficient function of a group-algebra element uses counting convolution, whereas
`convolutionCLM` uses probability Haar measure. The linear equivalence
`monoidAlgebraHaarEquiv`, sending `f` to `g ↦ |G| * f.coeff g`, reconciles them
(`TauCeti/RepresentationTheory/Compact/MonoidAlgebra.lean`).

Composing its inverse with `fourierAlgEquiv` gives `haarFourierEquiv`, the Fourier
transform `F ↦ (|G|⁻¹ ∑ g, F g • ρᵢ g)ᵢ` along a complete family of irreducibles.
Its inverse is the trace formula `F g = ∑ i, dim(Vᵢ) trace(ρᵢ(g⁻¹) Tᵢ)`.
In particular, this normalization removes the group-order denominator from the inverse
and preserves the order of factors in convolution for noncommutative groups.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §3.4,
  Exercises 3.31–3.32, for the counting-measure Fourier transform.
-/

public section

open MeasureTheory Module
open scoped MonoidAlgebra

namespace TauCeti

section Fourier

variable {𝕜 G : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NeZero (Nat.card G : 𝕜)]

variable {ι : Type*} {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  (ρ : ∀ i, Representation 𝕜 G (V i)) [IsAlgClosed 𝕜]
  [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j ↦ IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

/-- Fourier transform with probability-Haar normalization, along a complete family
of irreducible representations of a finite group. -/
noncomputable def haarFourierEquiv : C(G, 𝕜) ≃ₗ[𝕜] Π i, Module.End 𝕜 (V i) := by
  let : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  exact (monoidAlgebraHaarEquiv 𝕜 G).symm.trans
    (fourierAlgEquiv ρ hind hcard).toLinearEquiv

/-- The normalized Fourier transform agrees with the algebraic Fourier transform after
scaling coefficient functions by the group order. -/
@[simp]
theorem haarFourierEquiv_monoidAlgebraHaarEquiv (f : 𝕜[G]) :
    haarFourierEquiv ρ hind hcard (monoidAlgebraHaarEquiv 𝕜 G f) = fourierAlgHom ρ f := by
  let : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  simp [haarFourierEquiv]

/-- The normalized Fourier transform is the algebraic Fourier transform of the coefficients
divided by the group order. -/
theorem haarFourierEquiv_apply_eq_fourierAlgHom (F : C(G, 𝕜)) :
    haarFourierEquiv ρ hind hcard F = fourierAlgHom ρ ((monoidAlgebraHaarEquiv 𝕜 G).symm F) := by
  rw [← haarFourierEquiv_monoidAlgebraHaarEquiv, LinearEquiv.apply_symm_apply]

/-- The inverse normalized Fourier transform of an algebraic Fourier transform is the scaled
coefficient function. -/
@[simp]
theorem haarFourierEquiv_symm_fourierAlgHom (f : 𝕜[G]) :
    (haarFourierEquiv ρ hind hcard).symm (fourierAlgHom ρ f) = monoidAlgebraHaarEquiv 𝕜 G f := by
  rw [LinearEquiv.symm_apply_eq, haarFourierEquiv_monoidAlgebraHaarEquiv]

/-- The inverse normalized Fourier transform of the identity family is the image of
`1 : 𝕜[G]`. -/
@[simp]
theorem haarFourierEquiv_symm_one :
    (haarFourierEquiv ρ hind hcard).symm 1 = monoidAlgebraHaarEquiv 𝕜 G 1 := by
  rw [← map_one (fourierAlgHom ρ), haarFourierEquiv_symm_fourierAlgHom]

/-- The inverse normalized Fourier transform is the algebraic inversion formula, scaled by the
group order. -/
theorem haarFourierEquiv_symm_eq_fourierInv [Finite G] [Finite ι] (T : Π i, Module.End 𝕜 (V i)) :
    (haarFourierEquiv ρ hind hcard).symm T = monoidAlgebraHaarEquiv 𝕜 G (fourierInv ρ T) := by
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  rw [LinearEquiv.symm_apply_eq, haarFourierEquiv_monoidAlgebraHaarEquiv,
    fourierAlgHom_fourierInv ρ hind hcard]

/-- The inverse normalized Fourier transform of a family concentrated on the operator `A` in
block `i` is `g ↦ dim(Vᵢ) trace(ρᵢ(g⁻¹) A)`. -/
@[simp]
theorem haarFourierEquiv_symm_single_apply [DecidableEq ι] (i : ι) (A : Module.End 𝕜 (V i))
    (g : G) :
    (haarFourierEquiv ρ hind hcard).symm (Pi.single i A) g =
      (finrank 𝕜 (V i) : 𝕜) * LinearMap.trace 𝕜 (V i) (ρ i g⁻¹ * A) := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  have : Finite ι := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  rw [haarFourierEquiv_symm_eq_fourierInv, MonoidAlgebra.monoidAlgebraHaarEquiv_apply,
    coeff_fourierInv_single, mul_inv_cancel_left₀ (NeZero.ne _)]

/-- Each Fourier block is the normalized finite average of the action operators. -/
theorem haarFourierEquiv_apply [Fintype G] (F : C(G, 𝕜)) (i : ι) :
    haarFourierEquiv ρ hind hcard F i =
      (Nat.card G : 𝕜)⁻¹ • ∑ g, F g • ρ i g := by
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  simp only [haarFourierEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    fourierAlgEquiv_apply, fourierAlgHom_apply_eq_sum,
    ContinuousMap.coeff_monoidAlgebraHaarEquiv_symm,
    Finset.smul_sum, mul_smul]

/-- The inverse probability-Haar Fourier transform is the dimension-weighted trace sum,
without a group-order denominator. -/
theorem haarFourierEquiv_symm_apply [Fintype ι] (T : Π i, Module.End 𝕜 (V i)) (g : G) :
    (haarFourierEquiv ρ hind hcard).symm T g =
      ∑ i, (finrank 𝕜 (V i) : 𝕜) * LinearMap.trace 𝕜 (V i) (ρ i g⁻¹ * T i) := by
  let : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  simp [haarFourierEquiv, fourierAlgEquiv_symm_apply, coeff_fourierInv,
    NeZero.ne (Nat.card G : 𝕜)]

end Fourier

section RCLikeFourier

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G]

variable {ι : Type*} {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  (ρ : ∀ i, Representation 𝕜 G (V i)) [IsAlgClosed 𝕜]
  [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j ↦ IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

/-- Probability-Haar convolution transforms into operator multiplication in each block,
in the original order of its factors. -/
@[simp]
theorem haarFourierEquiv_convolutionCLM_toLp [MeasurableSpace G] [BorelSpace G] (F H : C(G, 𝕜)) :
    haarFourierEquiv ρ hind hcard
      (convolutionCLM F (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)) =
        haarFourierEquiv ρ hind hcard F * haarFourierEquiv ρ hind hcard H := by
  obtain ⟨f, rfl⟩ := (monoidAlgebraHaarEquiv 𝕜 G).surjective F
  obtain ⟨h, rfl⟩ := (monoidAlgebraHaarEquiv 𝕜 G).surjective H
  rw [← MonoidAlgebra.monoidAlgebraHaarEquiv_mul]
  simp

/-- Operator multiplication in each block transforms back into probability-Haar convolution,
in the original order of its factors. -/
theorem haarFourierEquiv_symm_mul [MeasurableSpace G] [BorelSpace G]
    (S T : Π i, Module.End 𝕜 (V i)) :
    (haarFourierEquiv ρ hind hcard).symm (S * T) =
      convolutionCLM ((haarFourierEquiv ρ hind hcard).symm S)
        (ContinuousMap.toLp 2 (haarProb G) 𝕜 ((haarFourierEquiv ρ hind hcard).symm T)) := by
  rw [LinearEquiv.symm_apply_eq, haarFourierEquiv_convolutionCLM_toLp]
  simp

end RCLikeFourier

end TauCeti
