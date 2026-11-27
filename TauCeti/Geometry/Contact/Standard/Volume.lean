/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The volume form of the standard contact form

Let `V` be a real inner product space with an orthonormal basis `b₀, …, bₙ₋₁`, and let
`α = dz - ⟪p, dq⟫` be the standard contact form `TauCeti.innerProductContactForm` on `V × V × ℝ`,
with coordinates `(q, p, z)`. Reading `q` and `p` in the basis gives coordinates
`qᵢ = ⟪bᵢ, q⟫` and `pᵢ = ⟪bᵢ, p⟫`, with coordinate one-forms `dz, dq₀, dp₀, …, dqₙ₋₁, dpₙ₋₁`
(`TauCeti.innerProductContactCoordForm b`). In these coordinates the contact volume form is

`α ∧ (dα)ⁿ = n! dz ∧ dq₀ ∧ dp₀ ∧ ⋯ ∧ dqₙ₋₁ ∧ dpₙ₋₁`

(`TauCeti.wedge_innerProductContactForm_wedgePow_mextDerivₗ`). For
`V = EuclideanSpace ℝ (Fin n)` and its standard basis this is the volume form of
`dz - Σᵢ pᵢ dqᵢ` on `ℝ²ⁿ⁺¹`. It is nowhere zero, as the contact volume criterion
`TauCeti.SmoothForm.isContactForm_iff_wedge_wedgePow_apply_ne_zero` requires of a contact form,
and its coefficient `n!` is positive.

Both sides are top-degree forms, so they agree once they agree on the coordinate frame
`(∂_z, ∂_{q₀}, ∂_{p₀}, …)`, which is dual to the coordinate one-forms. There the right side takes
the value `n!`. On the left, `∂_z` lies in the kernel of `dα = Σᵢ dqᵢ ∧ dpᵢ` and `α(∂_z) = 1`, so
inserting `∂_z` gives `(dα)ⁿ` on the remaining vectors
(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_vecCons_of_forall`), and `(dα)ⁿ` takes the
value `n!` on the standard pairs `(∂_{qᵢ}, ∂_{pᵢ})`
(`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`).

## Main definitions

* `TauCeti.innerProductContactCoordForm b`: the coordinate one-forms
  `dz, dq₀, dp₀, …, dqₙ₋₁, dpₙ₋₁` on `V × V × ℝ` for an orthonormal basis `b` of `V`.

## Main results

* `TauCeti.wedge_innerProductContactForm_wedgePow_mextDerivₗ`: the standard contact form satisfies
  `α ∧ (dα)ⁿ = n! dz ∧ dq₀ ∧ dp₀ ∧ ⋯ ∧ dqₙ₋₁ ∧ dpₙ₋₁`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Chapter 2
  (the standard contact structure on `ℝ²ⁿ⁺¹`).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- The index `1 + 2 i + j` (after the `dz` slot) of the pair slot `(i, j)`, with `j = 0` for `dqᵢ`
and `j = 1` for `dpᵢ`. -/
private def innerProductContactIndex (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

/-- The coordinate covectors `dz, dq₀, dp₀, …` on `V × V × ℝ` of an orthonormal basis `b` of
`V`: `dz` reads the last coordinate, and `dqᵢ`, `dpᵢ` pair the first and second coordinates with
`bᵢ`. -/
private def innerProductContactCoord (b : OrthonormalBasis (Fin n) ℝ V) :
    Fin (1 + 2 * n) → (V × V × ℝ →L[ℝ] ℝ) :=
  Fin.append ![(ContinuousLinearMap.snd ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ))]
    fun s ↦ (innerSL ℝ (b ((innerProductContactIndex n).symm s).1)).comp
      (![ContinuousLinearMap.fst ℝ V (V × ℝ),
        (ContinuousLinearMap.fst ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ))]
          ((innerProductContactIndex n).symm s).2)

/-- The coordinate vectors `∂_{qᵢ} = (bᵢ, 0, 0)` and `∂_{pᵢ} = (0, bᵢ, 0)`, indexed by `(i, 0)` and
`(i, 1)`. -/
private def innerProductContactPair (b : OrthonormalBasis (Fin n) ℝ V) (x : V × V × ℝ)
    (p : Fin n × Fin 2) : TangentSpace 𝓘(ℝ, V × V × ℝ) x :=
  ![(b p.1, 0, 0), (0, b p.1, 0)] p.2

/-- The coordinate frame `(∂_z, ∂_{q₀}, ∂_{p₀}, …)` of `V × V × ℝ`, dual to the coordinate
covectors. -/
private def innerProductContactFrame (b : OrthonormalBasis (Fin n) ℝ V) (x : V × V × ℝ) :
    Fin (1 + 2 * n) → TangentSpace 𝓘(ℝ, V × V × ℝ) x :=
  Fin.append ![((0 : V), (0 : V), (1 : ℝ))]
    fun s ↦ innerProductContactPair b x ((innerProductContactIndex n).symm s)

/-- The coordinate frame is dual to the coordinate covectors. -/
private theorem innerProductContactCoord_frame (b : OrthonormalBasis (Fin n) ℝ V)
    (x : V × V × ℝ) (r s : Fin (1 + 2 * n)) :
    innerProductContactCoord b r (innerProductContactFrame b x s) = if r = s then 1 else 0 := by
  -- Split both indices into the `dz` slot and the slots `(i, j)` of the pairs `(dqᵢ, dpᵢ)`.
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r <;>
    refine Fin.addCases (fun s ↦ ?_) (fun s ↦ ?_) s
  · simp [innerProductContactCoord, innerProductContactFrame, Fin.fin_one_eq_zero]
  · obtain ⟨⟨i, j⟩, rfl⟩ := (innerProductContactIndex n).surjective s
    simp only [innerProductContactCoord, innerProductContactFrame, Fin.append_left,
      Fin.append_right, Equiv.symm_apply_apply]
    fin_cases j <;> simp [innerProductContactPair, Fin.ext_iff] <;> omega
  · obtain ⟨⟨i, j⟩, rfl⟩ := (innerProductContactIndex n).surjective r
    simp only [innerProductContactCoord, innerProductContactFrame, Fin.append_left,
      Fin.append_right, Equiv.symm_apply_apply]
    fin_cases j <;> simp [Fin.ext_iff, Fin.fin_one_eq_zero]
  · obtain ⟨⟨i, j⟩, rfl⟩ := (innerProductContactIndex n).surjective r
    obtain ⟨⟨i', j'⟩, rfl⟩ := (innerProductContactIndex n).surjective s
    simp only [innerProductContactCoord, innerProductContactFrame, Fin.append_right,
      Equiv.symm_apply_apply, (Fin.natAdd_injective _ _).eq_iff, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq]
    fin_cases j <;> fin_cases j' <;> simp [innerProductContactPair,
      orthonormal_iff_ite.1 b.orthonormal]

/-- The coordinate frame is linearly independent: the coordinate covectors map it to the standard
basis of `Fin (1 + 2 * n) → ℝ`. -/
private theorem linearIndependent_innerProductContactFrame (b : OrthonormalBasis (Fin n) ℝ V)
    (x : V × V × ℝ) : LinearIndependent ℝ (innerProductContactFrame b x) := by
  refine LinearIndependent.of_comp
    (ContinuousLinearMap.pi (innerProductContactCoord b)).toLinearMap ?_
  convert (Pi.basisFun ℝ (Fin (1 + 2 * n))).linearIndependent
  ext s r
  refine (innerProductContactCoord_frame b x r s).trans ?_
  rw [Pi.basisFun_apply, Pi.single_apply]

/-- The **coordinate one-forms** `dz, dq₀, dp₀, …, dqₙ₋₁, dpₙ₋₁` on `V × V × ℝ`, for an orthonormal
basis `b` of `V`: the coordinates of a point `(q, p, z)` are `z`, `qᵢ = ⟪bᵢ, q⟫` and
`pᵢ = ⟪bᵢ, p⟫`. The index `0` is `dz`, and the pair `(dqᵢ, dpᵢ)` follows at the indices
`1 + 2 i` and `2 + 2 i`. -/
def innerProductContactCoordForm (b : OrthonormalBasis (Fin n) ℝ V) (r : Fin (1 + 2 * n)) :
    SmoothForm 𝓘(ℝ, V × V × ℝ) (V × V × ℝ) ℝ 1 :=
  SmoothForm.const (ContinuousAlternatingMap.ofSubsingleton ℝ (V × V × ℝ) ℝ 0
    (innerProductContactCoord b r))

private theorem innerProductContactCoordForm_apply (b : OrthonormalBasis (Fin n) ℝ V)
    (r : Fin (1 + 2 * n)) (x : V × V × ℝ) (v : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    (innerProductContactCoordForm b r).val x ![v] = innerProductContactCoord b r v := by
  rw [innerProductContactCoordForm, SmoothForm.const_apply]
  -- On the model space `NormedSpace.fromTangentSpace` is the identity.
  rfl

/-- The coordinate one-form `dz` reads the last coordinate of a tangent vector. -/
@[simp]
theorem innerProductContactCoordForm_castAdd_apply (b : OrthonormalBasis (Fin n) ℝ V)
    (x : V × V × ℝ) (v : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    (innerProductContactCoordForm b (Fin.castAdd (2 * n) 0)).val x ![v] = v.2.2 := by
  rw [innerProductContactCoordForm_apply, innerProductContactCoord, Fin.append_left]
  -- The tangent space of the model space is `V × V × ℝ`, on which the coordinate covectors act
  -- by the projections.
  rfl

/-- The coordinate one-form `dqᵢ` pairs the first coordinate of a tangent vector with `bᵢ`. -/
@[simp]
theorem innerProductContactCoordForm_natAdd_zero_apply (b : OrthonormalBasis (Fin n) ℝ V)
    (i : Fin n) (x : V × V × ℝ) (v : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    (innerProductContactCoordForm b
        (Fin.natAdd 1 (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (i, 0))))).val x ![v] =
      ⟪b i, v.1⟫ := by
  rw [show Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (i, 0)) = innerProductContactIndex n (i, 0)
      from rfl, innerProductContactCoordForm_apply, innerProductContactCoord, Fin.append_right,
    Equiv.symm_apply_apply]
  -- The tangent space of the model space is `V × V × ℝ`, on which the coordinate covectors act
  -- by the projections.
  rfl

/-- The coordinate one-form `dpᵢ` pairs the second coordinate of a tangent vector with `bᵢ`. -/
@[simp]
theorem innerProductContactCoordForm_natAdd_one_apply (b : OrthonormalBasis (Fin n) ℝ V)
    (i : Fin n) (x : V × V × ℝ) (v : TangentSpace 𝓘(ℝ, V × V × ℝ) x) :
    (innerProductContactCoordForm b
        (Fin.natAdd 1 (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (i, 1))))).val x ![v] =
      ⟪b i, v.2.1⟫ := by
  rw [show Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (i, 1)) = innerProductContactIndex n (i, 1)
      from rfl, innerProductContactCoordForm_apply, innerProductContactCoord, Fin.append_right,
    Equiv.symm_apply_apply]
  -- The tangent space of the model space is `V × V × ℝ`, on which the coordinate covectors act
  -- by the projections.
  rfl

/-- The wedge product of the coordinate one-forms takes the value `1` on the coordinate frame. -/
private theorem wedgeFamily_innerProductContactCoordForm_apply_frame [FiniteDimensional ℝ V]
    (b : OrthonormalBasis (Fin n) ℝ V) (x : V × V × ℝ) :
    (SmoothForm.wedgeFamily (innerProductContactCoordForm b)).val x
      (innerProductContactFrame b x) = 1 := by
  rw [SmoothForm.wedgeFamily_apply, ← Matrix.det_one (n := Fin (1 + 2 * n)) (R := ℝ)]
  congr 1
  ext r s
  rw [Matrix.of_apply, innerProductContactCoordForm_apply, innerProductContactCoord_frame,
    Matrix.one_apply]

/-- The volume form of the standard contact form takes the value `n!` on the coordinate frame. -/
private theorem wedge_innerProductContactForm_apply_frame (b : OrthonormalBasis (Fin n) ℝ V)
    (x : V × V × ℝ) :
    (SmoothForm.wedge (innerProductContactForm V)
        ((mextDerivₗ 𝓘(ℝ, V × V × ℝ) 1 (innerProductContactForm V)).wedgePow n)).val x
      (innerProductContactFrame b x) = n.factorial := by
  simp only [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    SmoothForm.wedgePow_apply, mextDerivₗ_apply]
  rw [innerProductContactFrame, Fin.append_left_eq_cons]
  -- `∂_z` lies in the kernel of `dα`, so inserting it into `α ∧ (dα)ⁿ` leaves `α(∂_z) (dα)ⁿ`.
  refine (ContinuousAlternatingMap.pairedWedge_wedgePow_apply_vecCons_of_forall _ _ n
    (fun w ↦ ?_) _).trans ?_
  · rw [mextDeriv_innerProductContactForm_apply]
    simp
  -- `α(∂_z) = 1`, and `(dα)ⁿ` takes the value `n!` on the standard pairs `(∂_{qᵢ}, ∂_{pᵢ})`.
  simp only [innerProductContactIndex, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
  rw [innerProductContactForm_apply, ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv]
  · simp
  · intro i j
    refine (mextDeriv_innerProductContactForm_apply V x
      (innerProductContactPair b x (i, 0)) (innerProductContactPair b x (j, 0))).trans ?_
    simp [innerProductContactPair]
  · intro i j
    refine (mextDeriv_innerProductContactForm_apply V x
      (innerProductContactPair b x (i, 0)) (innerProductContactPair b x (j, 1))).trans ?_
    simp [innerProductContactPair, orthonormal_iff_ite.1 b.orthonormal]

/-- **The volume form of the standard contact form.** For an orthonormal basis `b` of `V`, the
standard contact form `α = dz - ⟪p, dq⟫` on `V × V × ℝ` satisfies

`α ∧ (dα)ⁿ = n! dz ∧ dq₀ ∧ dp₀ ∧ ⋯ ∧ dqₙ₋₁ ∧ dpₙ₋₁`

in the coordinates `qᵢ = ⟪bᵢ, q⟫`, `pᵢ = ⟪bᵢ, p⟫` and `z`. -/
theorem wedge_innerProductContactForm_wedgePow_mextDerivₗ [FiniteDimensional ℝ V]
    (b : OrthonormalBasis (Fin n) ℝ V) :
    SmoothForm.wedge (innerProductContactForm V)
        ((mextDerivₗ 𝓘(ℝ, V × V × ℝ) 1 (innerProductContactForm V)).wedgePow n) =
      (n.factorial : ℝ) • SmoothForm.wedgeFamily (innerProductContactCoordForm b) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  -- Both sides are top-degree forms, determined by their values on the coordinate frame.
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, V × V × ℝ) x) :=
    inferInstanceAs (FiniteDimensional ℝ (V × V × ℝ))
  have hrank : Fintype.card (Fin (1 + 2 * n)) = finrank ℝ (V × V × ℝ) := by
    simp [Module.finrank_prod, Module.finrank_eq_card_basis b.toBasis]
    ring
  set B := basisOfLinearIndependentOfCardEqFinrank' _
    (linearIndependent_innerProductContactFrame b x) hrank
  have hB : ⇑B = innerProductContactFrame b x :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ContinuousAlternatingMap.ext fun v ↦
    (ContinuousAlternatingMap.apply_eq_det_mul _ B v).trans
      ((congrArg _ ?_).trans (ContinuousAlternatingMap.apply_eq_det_mul _ B v).symm)
  rw [hB, wedge_innerProductContactForm_apply_frame,
    Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    wedgeFamily_innerProductContactCoordForm_apply_frame, smul_eq_mul, mul_one]

end TauCeti
