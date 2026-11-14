/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Fourier
public import TauCeti.RepresentationTheory.Compact.Convolution
public import TauCeti.RepresentationTheory.Compact.Finite

/-!
# Finite Fourier transform with probability Haar measure

The coefficient function of a group-algebra element uses counting convolution, whereas
`convolutionCLM` uses probability Haar measure. The linear equivalence
`groupAlgebraHaarEquiv` reconciles them by sending `f` to the continuous function
`g ↦ |G| * f.coeff g`. It takes group-algebra multiplication to the existing Haar
convolution, and the group-algebra unit to `|G|` times the indicator of the identity.

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

section Coefficients

variable (𝕜 G : Type*) [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [TopologicalSpace G] [DiscreteTopology G]
  [NeZero (Nat.card G : 𝕜)]

/-- The group algebra as continuous functions with probability-Haar normalization:
`f` is sent to `g ↦ |G| * f.coeff g`, with inverse dividing each value by `|G|`.
The coefficient-field topology is arbitrary, and the group order need only be invertible. -/
noncomputable def groupAlgebraHaarEquiv : 𝕜[G] ≃ₗ[𝕜] C(G, 𝕜) :=
  let : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  (LinearEquiv.smulOfNeZero 𝕜 𝕜[G] (Nat.card G : 𝕜) (NeZero.ne _)).trans
    ((MonoidAlgebra.coeffLinearEquiv 𝕜).trans
      ((Finsupp.linearEquivFunOnFinite 𝕜 𝕜 G).trans
        { ContinuousMap.equivFnOfDiscrete.symm with
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }))

variable {𝕜 G}

/-- The probability-Haar function associated to a group-algebra element. -/
@[simp]
theorem _root_.MonoidAlgebra.groupAlgebraHaarEquiv_apply (f : 𝕜[G]) (g : G) :
    groupAlgebraHaarEquiv 𝕜 G f g = (Nat.card G : 𝕜) * f.coeff g :=
  (rfl)

/-- Recover group-algebra coefficients by dividing by the group order. -/
@[simp]
theorem _root_.ContinuousMap.coeff_groupAlgebraHaarEquiv_symm (F : C(G, 𝕜)) (g : G) :
    ((groupAlgebraHaarEquiv 𝕜 G).symm F).coeff g = (Nat.card G : 𝕜)⁻¹ * F g := by
  simp [groupAlgebraHaarEquiv, Units.smul_def]

/-- The unit for probability-Haar convolution has value `|G|` at the identity and zero elsewhere. -/
@[simp high]
theorem groupAlgebraHaarEquiv_one_apply [One G] [DecidableEq G] (g : G) :
    groupAlgebraHaarEquiv 𝕜 G 1 g = if g = 1 then (Nat.card G : 𝕜) else 0 := by
  classical
  simp [MonoidAlgebra.one_def, Finsupp.single_apply, eq_comm]

end Coefficients

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G]

section Convolution

variable [MeasurableSpace G] [BorelSpace G]

/-- Multiplication in the group algebra corresponds to probability-Haar convolution
under the scaling `f ↦ |G| f`. -/
theorem _root_.MonoidAlgebra.groupAlgebraHaarEquiv_mul (f h : 𝕜[G]) :
    groupAlgebraHaarEquiv 𝕜 G (f * h) =
      convolutionCLM (groupAlgebraHaarEquiv 𝕜 G f)
        (ContinuousMap.toLp 2 (haarProb G) 𝕜 (groupAlgebraHaarEquiv 𝕜 G h)) := by
  classical
  let := Fintype.ofFinite G
  ext x
  rw [MonoidAlgebra.groupAlgebraHaarEquiv_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum_fintype _ _ (by simp), convolutionCLM_toLp_apply,
    integral_haarProb_eq_inv_mul_sum]
  simp only [MonoidAlgebra.groupAlgebraHaarEquiv_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  field_simp

end Convolution

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
  exact (groupAlgebraHaarEquiv 𝕜 G).symm.trans
    (fourierAlgEquiv ρ hind hcard).toLinearEquiv

/-- The normalized Fourier transform agrees with the algebraic Fourier transform after
scaling coefficient functions by the group order. -/
@[simp]
theorem haarFourierEquiv_groupAlgebraHaarEquiv (f : 𝕜[G]) :
    haarFourierEquiv ρ hind hcard (groupAlgebraHaarEquiv 𝕜 G f) = fourierAlgHom ρ f := by
  let : Finite G := Nat.finite_of_card_ne_zero fun h ↦
    NeZero.ne (Nat.card G : 𝕜) (by rw [h, Nat.cast_zero])
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  simp [haarFourierEquiv]

/-- Each Fourier block is the normalized finite average of the action operators. -/
theorem haarFourierEquiv_apply [Fintype G] (F : C(G, 𝕜)) (i : ι) :
    haarFourierEquiv ρ hind hcard F i =
      (Nat.card G : 𝕜)⁻¹ • ∑ g, F g • ρ i g := by
  let : Invertible (Nat.card G : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  simp only [haarFourierEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    fourierAlgEquiv_apply, fourierAlgHom_apply_eq_sum,
    ContinuousMap.coeff_groupAlgebraHaarEquiv_symm,
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

variable {ι : Type*} {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  (ρ : ∀ i, Representation 𝕜 G (V i)) [IsAlgClosed 𝕜]
  [∀ i, (ρ i).IsIrreducible]
  (hind : Pairwise fun i j ↦ IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

/-- Probability-Haar convolution transforms into operator multiplication in each block,
in the original order of its factors. -/
theorem haarFourierEquiv_convolution [MeasurableSpace G] [BorelSpace G] (F H : C(G, 𝕜)) :
    haarFourierEquiv ρ hind hcard
      (convolutionCLM F (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)) =
        haarFourierEquiv ρ hind hcard F * haarFourierEquiv ρ hind hcard H := by
  obtain ⟨f, rfl⟩ := (groupAlgebraHaarEquiv 𝕜 G).surjective F
  obtain ⟨h, rfl⟩ := (groupAlgebraHaarEquiv 𝕜 G).surjective H
  rw [← MonoidAlgebra.groupAlgebraHaarEquiv_mul]
  simp

end RCLikeFourier

end TauCeti
