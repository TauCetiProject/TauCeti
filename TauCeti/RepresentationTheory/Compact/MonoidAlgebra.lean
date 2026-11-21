/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Convolution
public import TauCeti.RepresentationTheory.Compact.Finite

/-!
# Finite group algebras as probability-Haar convolution algebras

The coefficient function of a group-algebra element uses counting convolution, whereas
`convolutionCLM` uses probability Haar measure. The linear equivalence
`monoidAlgebraHaarEquiv` reconciles them by sending `f` to the continuous function
`g ↦ |G| * f.coeff g`. It takes group-algebra multiplication to the existing Haar
convolution, in the original order of the factors, and the group-algebra unit to `|G|` times
the indicator of the identity.
-/

public section

open MeasureTheory
open scoped MonoidAlgebra

namespace TauCeti

section Coefficients

variable (𝕜 G : Type*) [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [TopologicalSpace G] [DiscreteTopology G]
  [NeZero (Nat.card G : 𝕜)]

/-- The monoid algebra as continuous functions with probability-Haar normalization:
`f` is sent to `g ↦ |G| * f.coeff g`, with inverse dividing each value by `|G|`.
The field `𝕜` may carry any topology with continuous addition and constant scalar
multiplication, `G` needs no algebraic structure, and `(Nat.card G : 𝕜) ≠ 0`, which in
particular forces `G` to be finite. -/
noncomputable def monoidAlgebraHaarEquiv : 𝕜[G] ≃ₗ[𝕜] C(G, 𝕜) :=
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
theorem _root_.MonoidAlgebra.monoidAlgebraHaarEquiv_apply (f : 𝕜[G]) (g : G) :
    monoidAlgebraHaarEquiv 𝕜 G f g = (Nat.card G : 𝕜) * f.coeff g :=
  (rfl)

/-- Recover group-algebra coefficients by dividing by the group order. -/
@[simp]
theorem _root_.ContinuousMap.coeff_monoidAlgebraHaarEquiv_symm (F : C(G, 𝕜)) (g : G) :
    ((monoidAlgebraHaarEquiv 𝕜 G).symm F).coeff g = (Nat.card G : 𝕜)⁻¹ * F g := by
  simp [monoidAlgebraHaarEquiv, Units.smul_def]

/-- The image of a single monoid-algebra term is supported at its index, with its coefficient
multiplied by the group order. -/
@[simp high]
theorem monoidAlgebraHaarEquiv_single_apply [DecidableEq G] (a : G) (c : 𝕜) (g : G) :
    monoidAlgebraHaarEquiv 𝕜 G (MonoidAlgebra.single a c) g =
      if g = a then (Nat.card G : 𝕜) * c else 0 := by
  simp [Finsupp.single_apply, eq_comm, mul_ite]

/-- The image of `1 : 𝕜[G]` under `monoidAlgebraHaarEquiv` has value `|G|` at `1` and zero
elsewhere. -/
@[simp high]
theorem monoidAlgebraHaarEquiv_one_apply [One G] [DecidableEq G] (g : G) :
    monoidAlgebraHaarEquiv 𝕜 G 1 g = if g = 1 then (Nat.card G : 𝕜) else 0 := by
  simpa only [MonoidAlgebra.one_def, mul_one] using
    (monoidAlgebraHaarEquiv_single_apply (𝕜 := 𝕜) (1 : G) (1 : 𝕜) g)

end Coefficients

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G]

section Convolution

variable [MeasurableSpace G] [BorelSpace G]

/-- Multiplication in the group algebra corresponds to probability-Haar convolution
under the scaling `f ↦ |G| f`. -/
theorem _root_.MonoidAlgebra.monoidAlgebraHaarEquiv_mul (f h : 𝕜[G]) :
    monoidAlgebraHaarEquiv 𝕜 G (f * h) =
      convolutionCLM (monoidAlgebraHaarEquiv 𝕜 G f)
        (ContinuousMap.toLp 2 (haarProb G) 𝕜 (monoidAlgebraHaarEquiv 𝕜 G h)) := by
  classical
  let := Fintype.ofFinite G
  ext x
  rw [MonoidAlgebra.monoidAlgebraHaarEquiv_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum_fintype _ _ (by simp), convolutionCLM_toLp_apply,
    integral_haarProb_eq_inv_mul_sum]
  simp only [MonoidAlgebra.monoidAlgebraHaarEquiv_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  field_simp

/-- Probability-Haar convolution corresponds to multiplication in the monoid algebra under the
inverse scaling `F ↦ |G|⁻¹ F`. -/
@[simp]
theorem _root_.ContinuousMap.monoidAlgebraHaarEquiv_symm_convolutionCLM_toLp
    (F H : C(G, 𝕜)) :
    (monoidAlgebraHaarEquiv 𝕜 G).symm
        (convolutionCLM F (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)) =
      (monoidAlgebraHaarEquiv 𝕜 G).symm F * (monoidAlgebraHaarEquiv 𝕜 G).symm H := by
  rw [LinearEquiv.symm_apply_eq, MonoidAlgebra.monoidAlgebraHaarEquiv_mul]
  simp

end Convolution

end TauCeti
