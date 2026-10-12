/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BottPeriodicity

/-!
# The negative-plane recurrence for real Clifford algebras

Adjoining a hyperbolic plane to a real quadratic module tensors its Clifford algebra with
`M₂(ℝ)` and leaves the form alone (`CliffordAlgebra.hyperbolicEquivTensor`). This file proves the
companion step for the **negative definite** plane: adjoining two generators which both square to
`-1` tensors the Clifford algebra with `Cliff(0,2) ≅ ℍ` **and negates the form**,

`Cliff(Q ⊥ ⟨-1, -1⟩) ≅ Cliff(-Q) ⊗ᵣ ℍ`.

The mechanism is the plane's volume element `ω = e₀e₁`. It squares to `-1` — rather than to `+1`,
as the hyperbolic volume element does — and it commutes with the old generators while
anticommuting with the two new ones, so `m ↦ ι m · ω` turns the old generators into generators
for the *negated* form. On the standard signature forms this reads

`Cliff(p, q + 2) ≅ Cliff(q, p) ⊗ᵣ ℍ`,

the negative-plane companion of `TauCeti.realCliffordSignatureSwitchRecurrenceEquiv`
(`Cliff(p + 2, q) ≅ Cliff(q, p) ⊗ᵣ M₂(ℝ)`). The two recurrences are what the eightfold
periodicity table of the real Clifford algebras is assembled from; composing them across four
negative generators already gives the signature-preserving four-step recurrence

`Cliff(p, q + 4) ≅ Cliff(p, q) ⊗ᵣ M₂(ℝ) ⊗ᵣ ℍ`

proved at the end of the file.

## Implementation notes

The generic statement is proved with `Cliff(0,2)` rather than `ℍ` on the right, and the
quaternions are reached at the very end by transporting along
`TauCeti.realCliffordZeroTwoEquivQuaternion`. That keeps the whole construction independent of the
quaternion model; the model is used only for the two identities the volume element has to satisfy,
which it inherits from the quaternion unit `k` it corresponds to.

The forward map is built from the universal property on the explicit generator
`(m, v) ↦ ι m ⊗ₜ ω + 1 ⊗ₜ ι v`, and its inverse from the two commuting inclusions
`Cliff(-Q) → Cliff(Q ⊥ ⟨-1, -1⟩)` and `Cliff(0,2) → Cliff(Q ⊥ ⟨-1, -1⟩)` through
`Algebra.TensorProduct.lift`. The base inclusion carries a sign: it sends `ι m` to
`-(ι (m, 0) · ω)` rather than to `ι (m, 0) · ω`. Either choice is a valid Clifford lift, since the
square is unchanged, but only the signed one inverts the unsigned forward map, precisely because
`ω² = -1` here where the hyperbolic volume element satisfies `ω² = 1`.

## Main definitions

* `TauCeti.realCliffordZeroTwoVolume`: the volume element `e₀e₁` of `Cliff(0,2)`, with its square
  and its anticommutation with the generators;
* `TauCeti.realCliffordNegativePlaneSplitIsometry`: the coordinate isometry separating the last
  two negative coordinates of a standard signature form;
* `CliffordAlgebra.negativePlaneEquivTensor`: `Cliff(Q ⊥ ⟨-1, -1⟩) ≅ Cliff(-Q) ⊗ᵣ Cliff(0,2)` for
  an arbitrary real quadratic module, and `CliffordAlgebra.negativePlaneEquivQuaternion` for its
  quaternionic form;
* `TauCeti.realCliffordQuaternionRecurrenceEquiv`: the standard-signature recurrence
  `Cliff(p, q + 2) ≅ Cliff(q, p) ⊗ᵣ ℍ`;
* `TauCeti.realCliffordFourNegativeRecurrenceEquiv`:
  `Cliff(p, q + 4) ≅ Cliff(p, q) ⊗ᵣ M₂(ℝ) ⊗ᵣ ℍ`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 7;
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Proposition 4.2.
-/

public section

open Module QuadraticMap
open scoped Quaternion TensorProduct
open CliffordAlgebra

namespace TauCeti

/-! ### The volume element of the negative definite plane -/

/-- The **volume element** of the negative definite plane: the product of the two coordinate
generators of `Cliff(0,2)`. It squares to `-1` and anticommutes with every generator, which is
what drives the negative-plane recurrence below. -/
noncomputable def realCliffordZeroTwoVolume : CliffordAlgebra (realCliffordForm 0 2) :=
  ι _ (Pi.single 0 1) * ι _ (Pi.single 1 1)

/-- The defining equation of the volume element: it is the product of the two coordinate
generators of `Cliff(0,2)`. This is deliberately not a `simp` lemma — the volume element is the
normal form, and the lemmas below which mention it do so in that form. -/
theorem realCliffordZeroTwoVolume_def :
    realCliffordZeroTwoVolume =
      ι (realCliffordForm 0 2) (Pi.single 0 1) *
        ι (realCliffordForm 0 2) (Pi.single 1 1) := (rfl)

/-- Under `Cliff(0,2) ≅ ℍ` the volume element is the quaternion unit `k = ij`. -/
@[simp]
theorem realCliffordZeroTwoEquivQuaternion_volume :
    realCliffordZeroTwoEquivQuaternion realCliffordZeroTwoVolume = ⟨0, 0, 0, 1⟩ := by
  have h : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 0, 1⟩ := by ext <;> simp
  rw [realCliffordZeroTwoVolume_def, map_mul, realCliffordZeroTwoEquivQuaternion_ι,
    realCliffordZeroTwoEquivQuaternion_ι]
  exact h

/-- The volume element of the negative definite plane squares to `-1`. -/
@[simp]
theorem realCliffordZeroTwoVolume_sq :
    realCliffordZeroTwoVolume * realCliffordZeroTwoVolume = -1 := by
  have h : (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) * ⟨0, 0, 0, 1⟩ = -1 := by ext <;> simp
  apply realCliffordZeroTwoEquivQuaternion.injective
  rw [map_mul, map_neg, map_one, realCliffordZeroTwoEquivQuaternion_volume]
  exact h

/-- The volume element of the negative definite plane anticommutes with every generator. -/
theorem realCliffordZeroTwoVolume_anticomm (v : Fin (0 + 2) → ℝ) :
    realCliffordZeroTwoVolume * ι (realCliffordForm 0 2) v +
      ι (realCliffordForm 0 2) v * realCliffordZeroTwoVolume = 0 := by
  have h : ∀ a b : ℝ, (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) * ⟨0, a, b, 0⟩ + ⟨0, a, b, 0⟩ * ⟨0, 0, 0, 1⟩ = 0 := by
    intro a b
    ext <;> simp
  apply realCliffordZeroTwoEquivQuaternion.injective
  rw [map_add, map_mul, map_mul, map_zero, realCliffordZeroTwoEquivQuaternion_volume,
    realCliffordZeroTwoEquivQuaternion_ι]
  exact h (v 0) (v 1)

/-! ### The negative-plane coordinate splitter -/

/-- The coordinate isometry which separates the last two negative coordinates of a standard
signature form as a negative definite plane. -/
def realCliffordNegativePlaneSplitIsometry (p q : ℕ) :
    (realCliffordForm p (q + 1 + 1)).IsometryEquiv
      ((realCliffordForm p q).prod (realCliffordForm 0 2)) :=
  realCliffordSplitIsometry p 0 q 2

/-- The positive coordinates retained by `realCliffordNegativePlaneSplitIsometry`. -/
@[simp]
theorem realCliffordNegativePlaneSplitIsometry_fst_pos (p q : ℕ)
    (v : Fin (p + (q + 1 + 1)) → ℝ) (i : Fin p) :
    (realCliffordNegativePlaneSplitIsometry p q v).1 (i.castAdd q) =
      v (i.castAdd (q + 1 + 1)) := by
  -- The bundled-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 0 q 2 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_pos]
  congr 1

/-- The negative coordinates retained by `realCliffordNegativePlaneSplitIsometry`. -/
@[simp]
theorem realCliffordNegativePlaneSplitIsometry_fst_neg (p q : ℕ)
    (v : Fin (p + (q + 1 + 1)) → ℝ) (i : Fin q) :
    (realCliffordNegativePlaneSplitIsometry p q v).1 (i.natAdd p) =
      v (i.castSucc.castSucc.natAdd p) := by
  -- The bundled-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 0 q 2 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_neg]
  congr 1

/-- The first of the two negative coordinates extracted by
`realCliffordNegativePlaneSplitIsometry`. -/
@[simp]
theorem realCliffordNegativePlaneSplitIsometry_snd_zero (p q : ℕ)
    (v : Fin (p + (q + 1 + 1)) → ℝ) :
    (realCliffordNegativePlaneSplitIsometry p q v).2 0 =
      v ((Fin.last q).castSucc.natAdd p) := by
  convert realCliffordSplitIsometry_snd_neg p 0 q 2 v (0 : Fin 2) using 1 <;>
    congr

/-- The second of the two negative coordinates extracted by
`realCliffordNegativePlaneSplitIsometry`. -/
@[simp]
theorem realCliffordNegativePlaneSplitIsometry_snd_one (p q : ℕ)
    (v : Fin (p + (q + 1 + 1)) → ℝ) :
    (realCliffordNegativePlaneSplitIsometry p q v).2 1 =
      v ((Fin.last (q + 1)).natAdd p) := by
  convert realCliffordSplitIsometry_snd_neg p 0 q 2 v (1 : Fin 2) using 1 <;>
    congr

end TauCeti

namespace CliffordAlgebra

section NegativePlane

open TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

private abbrev NegativePlaneAlgebra :=
  CliffordAlgebra (Q.prod (realCliffordForm 0 2))

private abbrev NegativePlaneTensor :=
  CliffordAlgebra (-Q) ⊗[ℝ] CliffordAlgebra (realCliffordForm 0 2)

/-! ### The forward map -/

private noncomputable def negativePlaneGenerator :
    M × (Fin (0 + 2) → ℝ) →ₗ[ℝ] NegativePlaneTensor Q :=
  LinearMap.coprod
    (((TensorProduct.mk ℝ (CliffordAlgebra (-Q))
        (CliffordAlgebra (realCliffordForm 0 2))).flip
        realCliffordZeroTwoVolume).comp (ι (-Q)))
    ((TensorProduct.mk ℝ (CliffordAlgebra (-Q))
        (CliffordAlgebra (realCliffordForm 0 2)) 1).comp
      (ι (realCliffordForm 0 2)))

private theorem negativePlaneGenerator_apply (x : M × (Fin (0 + 2) → ℝ)) :
    negativePlaneGenerator Q x =
      ι (-Q) x.1 ⊗ₜ[ℝ] realCliffordZeroTwoVolume +
        (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
          ι (realCliffordForm 0 2) x.2 :=
  rfl

private theorem algebraMap_tmul_neg_one (r : ℝ) :
    (algebraMap ℝ (CliffordAlgebra (-Q)) r) ⊗ₜ[ℝ]
        (-1 : CliffordAlgebra (realCliffordForm 0 2)) =
      algebraMap ℝ (NegativePlaneTensor Q) (-r) := by
  rw [map_neg, Algebra.TensorProduct.algebraMap_apply]
  exact TensorProduct.tmul_neg _ _

private theorem negativePlaneGenerator_sq (x : M × (Fin (0 + 2) → ℝ)) :
    negativePlaneGenerator Q x * negativePlaneGenerator Q x =
      algebraMap ℝ (NegativePlaneTensor Q) ((Q.prod (realCliffordForm 0 2)) x) := by
  rw [negativePlaneGenerator_apply]
  set A := ι (-Q) x.1 ⊗ₜ[ℝ] realCliffordZeroTwoVolume with hAdef
  set B := (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
    ι (realCliffordForm 0 2) x.2 with hBdef
  have hA : A * A = algebraMap ℝ (NegativePlaneTensor Q) (Q x.1) := by
    rw [hAdef, Algebra.TensorProduct.tmul_mul_tmul, ι_sq_scalar,
      realCliffordZeroTwoVolume_sq, algebraMap_tmul_neg_one, neg_apply, neg_neg]
  have hB : B * B =
      algebraMap ℝ (NegativePlaneTensor Q) (realCliffordForm 0 2 x.2) := by
    rw [hBdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      ι_sq_scalar, Algebra.TensorProduct.algebraMap_apply']
  have hAB : A * B + B * A = 0 := by
    rw [hAdef, hBdef, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, ← TensorProduct.tmul_add, realCliffordZeroTwoVolume_anticomm,
      TensorProduct.tmul_zero]
  have hexpand : (A + B) * (A + B) = A * A + (A * B + B * A) + B * B := by noncomm_ring
  rw [hexpand, hA, hB, hAB, add_zero, ← map_add, QuadraticMap.prod_apply]

private noncomputable def negativePlaneToTensor :
    NegativePlaneAlgebra Q →ₐ[ℝ] NegativePlaneTensor Q :=
  lift _ ⟨negativePlaneGenerator Q, negativePlaneGenerator_sq Q⟩

private theorem negativePlaneToTensor_ι_base (m : M) :
    negativePlaneToTensor Q (ι _ (m, 0)) =
      ι (-Q) m ⊗ₜ[ℝ] realCliffordZeroTwoVolume := by
  rw [negativePlaneToTensor, lift_ι_apply, negativePlaneGenerator_apply]
  simp

private theorem negativePlaneToTensor_ι_plane (v : Fin (0 + 2) → ℝ) :
    negativePlaneToTensor Q (ι _ (0, v)) =
      (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
        ι (realCliffordForm 0 2) v := by
  rw [negativePlaneToTensor, lift_ι_apply, negativePlaneGenerator_apply]
  simp

/-! ### The two inclusions into `Cliff(Q ⊥ ⟨-1, -1⟩)` -/

private noncomputable def negativePlaneRightInclusion :
    CliffordAlgebra (realCliffordForm 0 2) →ₐ[ℝ] NegativePlaneAlgebra Q :=
  map (Isometry.inr Q (realCliffordForm 0 2))

private theorem negativePlaneRightInclusion_ι (v : Fin (0 + 2) → ℝ) :
    negativePlaneRightInclusion Q (ι _ v) =
      ι _ (0, v) := by
  rw [negativePlaneRightInclusion, map_apply_ι]
  rfl

/-- The image of the plane's volume element inside `Cliff(Q ⊥ ⟨-1, -1⟩)`. -/
private noncomputable def negativePlaneVolume : NegativePlaneAlgebra Q :=
  negativePlaneRightInclusion Q realCliffordZeroTwoVolume

private theorem negativePlaneVolume_eq_mul :
    negativePlaneVolume Q =
      ι _ (0, (Pi.single 0 1 : Fin (0 + 2) → ℝ)) *
        ι _ (0, (Pi.single 1 1 : Fin (0 + 2) → ℝ)) := by
  rw [negativePlaneVolume, realCliffordZeroTwoVolume, map_mul,
    negativePlaneRightInclusion_ι, negativePlaneRightInclusion_ι]

private theorem negativePlaneVolume_sq :
    negativePlaneVolume Q * negativePlaneVolume Q = -1 := by
  rw [negativePlaneVolume, ← map_mul, realCliffordZeroTwoVolume_sq, map_neg, map_one]

private theorem negativePlaneVolume_anticomm (v : Fin (0 + 2) → ℝ) :
    negativePlaneVolume Q * ι _ (0, v) +
      ι _ (0, v) * negativePlaneVolume Q = 0 := by
  have h := congrArg (negativePlaneRightInclusion Q)
    (realCliffordZeroTwoVolume_anticomm v)
  rw [map_add, map_mul, map_mul, negativePlaneRightInclusion_ι, map_zero] at h
  exact h

private theorem negativePlaneVolume_comm_base (m : M) :
    Commute (ι _ (m, 0)) (negativePlaneVolume Q) := by
  rw [negativePlaneVolume_eq_mul]
  simpa using
    (commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
      (f₁ := Isometry.inl Q (realCliffordForm 0 2))
      (f₂ := Isometry.inr Q (realCliffordForm 0 2))
      (hf := fun _ _ => IsOrtho.inl_inr _ _)
      (ι Q m)
      (ι _ (Pi.single 0 1) * ι _ (Pi.single 1 1))
      (ι_mem_evenOdd_one Q m)
      (ι_mul_ι_mem_evenOdd_zero (realCliffordForm 0 2)
        (Pi.single 0 1) (Pi.single 1 1)))

private noncomputable def negativePlaneBaseGenerator : M →ₗ[ℝ] NegativePlaneAlgebra Q :=
  -((LinearMap.mulRight ℝ (negativePlaneVolume Q)).comp
    ((ι _).comp (LinearMap.inl ℝ M (Fin (0 + 2) → ℝ))))

private theorem negativePlaneBaseGenerator_apply (m : M) :
    negativePlaneBaseGenerator Q m =
      -(ι _ (m, 0) * negativePlaneVolume Q) := rfl

private theorem negativePlaneBaseGenerator_sq (m : M) :
    negativePlaneBaseGenerator Q m * negativePlaneBaseGenerator Q m =
      algebraMap ℝ (NegativePlaneAlgebra Q) ((-Q) m) := by
  rw [negativePlaneBaseGenerator_apply, neg_mul_neg, ← pow_two,
    (negativePlaneVolume_comm_base Q m).mul_pow, pow_two, pow_two,
    ι_sq_scalar, negativePlaneVolume_sq, QuadraticMap.prod_apply,
    neg_apply]
  simp [Algebra.algebraMap_eq_smul_one]

private noncomputable def negativePlaneBaseInclusion :
    CliffordAlgebra (-Q) →ₐ[ℝ] NegativePlaneAlgebra Q :=
  lift (-Q)
    ⟨negativePlaneBaseGenerator Q, negativePlaneBaseGenerator_sq Q⟩

private theorem negativePlaneBaseInclusion_ι (m : M) :
    negativePlaneBaseInclusion Q (ι (-Q) m) =
      -(ι _ (m, 0) * negativePlaneVolume Q) := by
  rw [negativePlaneBaseInclusion, lift_ι_apply,
    negativePlaneBaseGenerator_apply]

private theorem negativePlaneBaseInclusion_commute
    (x : CliffordAlgebra (-Q))
    (y : CliffordAlgebra (realCliffordForm 0 2)) :
    Commute (negativePlaneBaseInclusion Q x) (negativePlaneRightInclusion Q y) := by
  have hgen : ∀ (m : M) (z : CliffordAlgebra (realCliffordForm 0 2)),
      Commute (negativePlaneBaseInclusion Q (ι (-Q) m))
        (negativePlaneRightInclusion Q z) := by
    intro m z
    induction z using induction with
    | algebraMap r =>
        rw [(negativePlaneRightInclusion Q).commutes]
        exact (Algebra.commutes r _).symm
    | ι v =>
        rw [negativePlaneBaseInclusion_ι, negativePlaneRightInclusion_ι, Commute]
        have hic := ι_mul_ι_comm_of_isOrtho
          (IsOrtho.inl_inr (Q₁ := Q)
            (Q₂ := realCliffordForm 0 2) m v)
        have hoc : negativePlaneVolume Q * ι _ (0, v) =
            -(ι _ (0, v) * negativePlaneVolume Q) :=
          eq_neg_of_add_eq_zero_left (negativePlaneVolume_anticomm Q v)
        calc
          -(ι _ (m, 0) * negativePlaneVolume Q) *
              ι _ (0, v)
              = -(ι _ (m, 0) *
                (negativePlaneVolume Q * ι _ (0, v))) := by
                noncomm_ring
          _ = ι _ (m, 0) *
                ι _ (0, v) * negativePlaneVolume Q := by
                rw [hoc]; noncomm_ring
          _ = -(ι _ (0, v) *
                ι _ (m, 0)) * negativePlaneVolume Q := by rw [hic]
          _ = ι _ (0, v) *
                -(ι _ (m, 0) * negativePlaneVolume Q) := by
                noncomm_ring
    | mul a b ha hb => simpa only [map_mul] using ha.mul_right hb
    | add a b ha hb => simpa only [map_add] using ha.add_right hb
  induction x using induction with
  | algebraMap r =>
      rw [(negativePlaneBaseInclusion Q).commutes]
      exact Algebra.commutes r _
  | ι m => exact hgen m y
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb
  | add a b ha hb => simpa only [map_add] using ha.add_left hb

private noncomputable def tensorToNegativePlane :
    NegativePlaneTensor Q →ₐ[ℝ] NegativePlaneAlgebra Q :=
  Algebra.TensorProduct.lift (negativePlaneBaseInclusion Q) (negativePlaneRightInclusion Q)
    (negativePlaneBaseInclusion_commute Q)

/-! ### The two composites -/

private theorem tensorToNegativePlane_base (m : M) :
    tensorToNegativePlane Q
        (ι (-Q) m ⊗ₜ[ℝ] realCliffordZeroTwoVolume) =
      ι _ (m, 0) := by
  rw [tensorToNegativePlane, Algebra.TensorProduct.lift_tmul, negativePlaneBaseInclusion_ι,
    ← negativePlaneVolume, neg_mul, mul_assoc, negativePlaneVolume_sq]
  simp

private theorem tensorToNegativePlane_plane (v : Fin (0 + 2) → ℝ) :
    tensorToNegativePlane Q
        ((1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
          ι (realCliffordForm 0 2) v) =
      ι _ (0, v) := by
  rw [tensorToNegativePlane, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    negativePlaneRightInclusion_ι]

private theorem tensorToNegativePlane_comp_negativePlaneToTensor :
    (tensorToNegativePlane Q).comp (negativePlaneToTensor Q) = AlgHom.id ℝ _ := by
  apply hom_ext
  apply LinearMap.ext
  rintro ⟨m, v⟩
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.id_apply]
  rw [← Prod.fst_add_snd (m, v), map_add, map_add, negativePlaneToTensor_ι_base,
    negativePlaneToTensor_ι_plane, map_add, tensorToNegativePlane_base,
    tensorToNegativePlane_plane]

private theorem negativePlaneToTensor_volume :
    negativePlaneToTensor Q (negativePlaneVolume Q) =
      (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ] realCliffordZeroTwoVolume := by
  rw [negativePlaneVolume_eq_mul, map_mul, negativePlaneToTensor_ι_plane,
    negativePlaneToTensor_ι_plane, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    realCliffordZeroTwoVolume]

private theorem negativePlaneToTensor_comp_baseInclusion :
    (negativePlaneToTensor Q).comp (negativePlaneBaseInclusion Q) =
      Algebra.TensorProduct.includeLeft := by
  apply hom_ext
  ext m
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, negativePlaneBaseInclusion_ι, map_neg, map_mul,
    negativePlaneToTensor_ι_base, negativePlaneToTensor_volume,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, realCliffordZeroTwoVolume_sq,
    Algebra.TensorProduct.includeLeft_apply, TensorProduct.tmul_neg, neg_neg]

private theorem negativePlaneToTensor_comp_rightInclusion :
    (negativePlaneToTensor Q).comp (negativePlaneRightInclusion Q) =
      Algebra.TensorProduct.includeRight := by
  apply hom_ext
  ext v
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, negativePlaneRightInclusion_ι, negativePlaneToTensor_ι_plane,
    Algebra.TensorProduct.includeRight_apply]

private theorem negativePlaneToTensor_comp_tensorToNegativePlane :
    (negativePlaneToTensor Q).comp (tensorToNegativePlane Q) = AlgHom.id ℝ _ := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp only [AlgHom.toLinearMap_apply]
  rw [AlgHom.comp_apply, tensorToNegativePlane, Algebra.TensorProduct.lift_tmul, map_mul,
    ← AlgHom.comp_apply, ← AlgHom.comp_apply, negativePlaneToTensor_comp_baseInclusion,
    negativePlaneToTensor_comp_rightInclusion]
  simp

/-- **The negative-plane recurrence.** Adjoining two generators which square to `-1` to a real
quadratic module tensors its Clifford algebra with `Cliff(0,2)` and negates the form. -/
noncomputable def negativePlaneEquivTensor :
    CliffordAlgebra (Q.prod (realCliffordForm 0 2)) ≃ₐ[ℝ]
      (CliffordAlgebra (-Q) ⊗[ℝ]
        CliffordAlgebra (realCliffordForm 0 2)) :=
  AlgEquiv.ofAlgHom (negativePlaneToTensor Q) (tensorToNegativePlane Q)
    (negativePlaneToTensor_comp_tensorToNegativePlane Q)
    (tensorToNegativePlane_comp_negativePlaneToTensor Q)

/-- `negativePlaneEquivTensor` sends an old generator to `ι m ⊗ ω` and a new one to `1 ⊗ ι v`. -/
@[simp]
theorem negativePlaneEquivTensor_ι (x : M × (Fin (0 + 2) → ℝ)) :
    negativePlaneEquivTensor Q (ι _ x) =
      ι (-Q) x.1 ⊗ₜ[ℝ] realCliffordZeroTwoVolume +
        (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
          ι (realCliffordForm 0 2) x.2 := by
  rw [negativePlaneEquivTensor, AlgEquiv.ofAlgHom_apply]
  conv_lhs => rw [← Prod.fst_add_snd x]
  rw [map_add, map_add, negativePlaneToTensor_ι_base, negativePlaneToTensor_ι_plane]

/-- The inverse of `negativePlaneEquivTensor` on the tensor representing an old generator. -/
@[simp]
theorem negativePlaneEquivTensor_symm_apply_ι_base (m : M) :
    (negativePlaneEquivTensor Q).symm
        (ι (-Q) m ⊗ₜ[ℝ] realCliffordZeroTwoVolume) =
      ι _ (m, 0) :=
  tensorToNegativePlane_base Q m

/-- The inverse of `negativePlaneEquivTensor` on the tensor representing a new generator. -/
@[simp]
theorem negativePlaneEquivTensor_symm_apply_ι_plane (v : Fin (0 + 2) → ℝ) :
    (negativePlaneEquivTensor Q).symm
        ((1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
          ι (realCliffordForm 0 2) v) =
      ι _ (0, v) :=
  tensorToNegativePlane_plane Q v

/-- **The negative-plane recurrence, quaternionic form**: adjoining a negative definite plane
tensors the Clifford algebra with the quaternions and negates the form. -/
noncomputable def negativePlaneEquivQuaternion :
    CliffordAlgebra (Q.prod (realCliffordForm 0 2)) ≃ₐ[ℝ]
      (CliffordAlgebra (-Q) ⊗[ℝ] ℍ[ℝ]) :=
  (negativePlaneEquivTensor Q).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : CliffordAlgebra (-Q) ≃ₐ[ℝ] _)
      realCliffordZeroTwoEquivQuaternion)

/-- `negativePlaneEquivQuaternion` sends an old generator to `ι m ⊗ ω` and a new one to the
imaginary quaternion `v 0 · i + v 1 · j`, both read through `Cliff(0,2) ≅ ℍ`. -/
@[simp]
theorem negativePlaneEquivQuaternion_ι (x : M × (Fin (0 + 2) → ℝ)) :
    negativePlaneEquivQuaternion Q (ι _ x) =
      ι (-Q) x.1 ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion realCliffordZeroTwoVolume +
        (1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion
            (ι (realCliffordForm 0 2) x.2) := by
  simp only [negativePlaneEquivQuaternion, AlgEquiv.trans_apply, negativePlaneEquivTensor_ι,
    map_add, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq, AlgEquiv.coe_toAlgHom, map_one]

/-- The inverse of `negativePlaneEquivQuaternion` on the tensor representing an old generator:
the quaternion factor is the unit `k`, the image of the plane's volume element. -/
@[simp]
theorem negativePlaneEquivQuaternion_symm_apply_ι_base (m : M) :
    (negativePlaneEquivQuaternion Q).symm
        (ι (-Q) m ⊗ₜ[ℝ] (⟨0, 0, 0, 1⟩ : ℍ[ℝ])) =
      ι _ (m, 0) := by
  rw [AlgEquiv.symm_apply_eq, negativePlaneEquivQuaternion_ι]
  simp

/-- The inverse of `negativePlaneEquivQuaternion` on the tensor representing a new generator:
the quaternion factor is the imaginary quaternion `v 0 * i + v 1 * j`. -/
@[simp]
theorem negativePlaneEquivQuaternion_symm_apply_ι_plane (v : Fin (0 + 2) → ℝ) :
    (negativePlaneEquivQuaternion Q).symm
        ((1 : CliffordAlgebra (-Q)) ⊗ₜ[ℝ] (⟨0, v 0, v 1, 0⟩ : ℍ[ℝ])) =
      ι _ (0, v) := by
  rw [AlgEquiv.symm_apply_eq, negativePlaneEquivQuaternion_ι]
  simp only [Fin.isValue, map_zero, Nat.reduceAdd,
    realCliffordZeroTwoEquivQuaternion_volume,
    realCliffordZeroTwoEquivQuaternion_ι, right_eq_add]
  -- What is left is the vanishing base component; `simp` does not close it on its own.
  exact TensorProduct.zero_tmul _ _

end NegativePlane

end CliffordAlgebra

namespace TauCeti

/-! ### Negative-plane recurrences on standard signatures -/

/-- **The negative-plane signature recurrence** `Cliff(p, q + 2) ≅ Cliff(q, p) ⊗ ℍ`: two extra
negative generators switch the signature and tensor with the quaternions. This is the companion
of `TauCeti.realCliffordSignatureSwitchRecurrenceEquiv`, which does the same with two extra
positive generators and a factor of `M₂(ℝ)`. -/
noncomputable def realCliffordQuaternionRecurrenceEquiv (p q : ℕ) :
    CliffordAlgebra (realCliffordForm p (q + 1 + 1)) ≃ₐ[ℝ]
      CliffordAlgebra (realCliffordForm q p) ⊗[ℝ] ℍ[ℝ] :=
  (equivOfIsometry (realCliffordNegativePlaneSplitIsometry p q)).trans
    ((negativePlaneEquivQuaternion (realCliffordForm p q)).trans
      (Algebra.TensorProduct.congr
        (equivOfIsometry (realCliffordFormNegIsometry p q))
        (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] _)))

/-- The negative-plane signature recurrence on a Clifford generator: the coordinate isometry
splits off the last two negative coordinates, the generic recurrence multiplies the remaining
generator by the plane's volume element, and the negation isometry restores standard signature
coordinates. -/
@[simp]
theorem realCliffordQuaternionRecurrenceEquiv_ι (p q : ℕ)
    (v : Fin (p + (q + 1 + 1)) → ℝ) :
    realCliffordQuaternionRecurrenceEquiv p q (ι _ v) =
      ι (realCliffordForm q p)
            (realCliffordFormNegIsometry p q
              (realCliffordNegativePlaneSplitIsometry p q v).1) ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion realCliffordZeroTwoVolume +
        (1 : CliffordAlgebra (realCliffordForm q p)) ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion
            (ι (realCliffordForm 0 2)
              (realCliffordNegativePlaneSplitIsometry p q v).2) := by
  simp only [realCliffordQuaternionRecurrenceEquiv, AlgEquiv.trans_apply,
    equivOfIsometry_apply, map_apply_ι,
    negativePlaneEquivQuaternion_ι, map_add,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq, AlgEquiv.coe_toAlgHom, map_one,
    IsometryEquiv.toIsometry_apply]

/-- **The four-negative-generator recurrence** `Cliff(p, q + 4) ≅ Cliff(p, q) ⊗ M₂(ℝ) ⊗ ℍ`,
obtained by composing the negative-plane recurrence with the positive-plane one: four extra
negative generators restore the original signature. -/
noncomputable def realCliffordFourNegativeRecurrenceEquiv (p q : ℕ) :
    CliffordAlgebra (realCliffordForm p (q + 1 + 1 + 1 + 1)) ≃ₐ[ℝ]
      (CliffordAlgebra (realCliffordForm p q) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) ⊗[ℝ] ℍ[ℝ] :=
  (realCliffordQuaternionRecurrenceEquiv p (q + 1 + 1)).trans
    (Algebra.TensorProduct.congr (realCliffordSignatureSwitchRecurrenceEquiv q p)
      (AlgEquiv.refl : ℍ[ℝ] ≃ₐ[ℝ] _))

/-- The four-negative-generator recurrence on a Clifford generator: the negative-plane recurrence
splits off two of the four new coordinates, and the signature-switch recurrence transports the
remaining generator back to the original signature. -/
@[simp]
theorem realCliffordFourNegativeRecurrenceEquiv_ι (p q : ℕ)
    (v : Fin (p + (q + 1 + 1 + 1 + 1)) → ℝ) :
    realCliffordFourNegativeRecurrenceEquiv p q (ι _ v) =
      realCliffordSignatureSwitchRecurrenceEquiv q p
            (ι (realCliffordForm (q + 1 + 1) p)
              (realCliffordFormNegIsometry p (q + 1 + 1)
                (realCliffordNegativePlaneSplitIsometry p (q + 1 + 1) v).1)) ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion realCliffordZeroTwoVolume +
        (1 : CliffordAlgebra (realCliffordForm p q) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ) ⊗ₜ[ℝ]
          realCliffordZeroTwoEquivQuaternion
            (ι (realCliffordForm 0 2)
              (realCliffordNegativePlaneSplitIsometry p (q + 1 + 1) v).2) := by
  simp only [realCliffordFourNegativeRecurrenceEquiv, AlgEquiv.trans_apply,
    realCliffordQuaternionRecurrenceEquiv_ι, map_add, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq,
    AlgEquiv.coe_toAlgHom, map_one]

end TauCeti
