/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilizer
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# First-coordinate stabilization and block sums of compact real Spin groups

Splitting off the first coordinate of the positive-definite form `realCliffordForm (n + 1) 0`
identifies its underlying space `Fin (n + 1) → ℝ` with `ℝ × (Fin n → ℝ)` via `(r, v) ↦ Fin.cons r v`
(`TauCeti.realCliffordFirstSplitIsometry`). Composing with the right-summand inclusion `v ↦ (0, v)`
yields the first-coordinate quadratic isometry
`CliffordAlgebra.realCliffordSpinFirstInclusionIsometry n` from `realCliffordForm n 0` to
`realCliffordForm (n + 1) 0`, sending `v` to `Fin.cons 0 v`, and its Spin-group map

`CliffordAlgebra.realCliffordSpinFirstInclusion n : Spin(n) →* Spin(n + 1)`.

Its image fixes the first basis vector `Pi.single 0 1`, acts by the original Spin element on the
remaining `n` coordinates, preserves the central element `-1` in positive rank, and commutes with
the Spin projections onto the corresponding special-orthogonal first-coordinate block inclusions
`CliffordAlgebra.realCliffordSpecialOrthogonalFirstInclusion n : SO(n) →* SO(n + 1)`.

For arbitrary ranks `p` and `q`, splitting `realCliffordForm (p + q) 0` into its first `p` and last
`q` coordinates (`TauCeti.realCliffordSplitIsometry p q 0 0`, whose inverse is `Fin.append`) and
applying `CliffordAlgebra.spinGroupProd` gives the compact Spin block-sum homomorphism

`CliffordAlgebra.realCliffordSpinBlockSum p q : Spin(p) × Spin(q) →* Spin(p + q)`

and its special-orthogonal counterpart
`CliffordAlgebra.realCliffordSpecialOrthogonalBlockSum p q : SO(p) × SO(q) →* SO(p + q)`.
Placing the stabilization coordinate first makes block sum and stabilization strictly compatible up
to `Fin.cast` reindexing (`TauCeti.realCliffordFormCongr`): stabilizing `x ∈ Spin(n)` agrees with
forming the block sum `(1, x) ∈ Spin(1) × Spin(n)`, and stabilizing the first factor of a block sum
`(x, y) ∈ Spin(p) × Spin(q)` agrees with stabilizing `realCliffordSpinBlockSum p q (x, y)`. This
file also proves the left- and right-unit, associativity, and block-swap (`finAddFlip`) permutation
coherences of both block-sum homomorphisms, as well as the kernel and quotient description
`(Spin(p) × Spin(q)) / ⟨(-1, -1)⟩` in positive ranks.

## Main definitions

* `CliffordAlgebra.realCliffordSpinFirstInclusionIsometry n` and
  `CliffordAlgebra.realCliffordSpinFirstInclusion n`: the quadratic isometry `v ↦ Fin.cons 0 v`
  and induced stabilization homomorphism `Spin(n) →* Spin(n + 1)`.
* `CliffordAlgebra.realCliffordSpecialOrthogonalFirstInclusion n`: the corresponding block
  inclusion `SO(n) →* SO(n + 1)` fixing the first coordinate.
* `CliffordAlgebra.realCliffordSpinBlockInlIsometry p q` and
  `CliffordAlgebra.realCliffordSpinBlockInrIsometry p q`: the two block-inclusion quadratic
  isometries `u ↦ Fin.append u 0` and `v ↦ Fin.append 0 v`.
* `CliffordAlgebra.realCliffordSpinBlockSum p q` and
  `CliffordAlgebra.realCliffordSpecialOrthogonalBlockSum p q`: the compact Spin and special
  orthogonal block-sum homomorphisms.
* `CliffordAlgebra.realCliffordSpinBlockSumQuotientEquiv p q`: the isomorphism of
  `(Spin(p) × Spin(q)) / ⟨(-1, -1)⟩` with the range of `realCliffordSpinBlockSum p q` for positive
  `p` and `q`.

## Main results

* `CliffordAlgebra.realCliffordSpinFirstInclusion_injective` and
  `CliffordAlgebra.realCliffordSpecialOrthogonalFirstInclusion_injective`: injectivity of the
  first-coordinate Spin and special-orthogonal stabilization maps.
* `CliffordAlgebra.spinToSpecialOrthogonal_realCliffordSpinFirstInclusion` and
  `CliffordAlgebra.spinToSpecialOrthogonal_realCliffordSpinBlockSum`: compatibility of Spin
  stabilization and Spin block sum with the projections to `SO`.
* `CliffordAlgebra.realCliffordSpinBlockSum_zero_left` and
  `CliffordAlgebra.realCliffordSpinBlockSum_zero_right`: left- and right-unit coherences.
* `CliffordAlgebra.realCliffordSpinBlockSum_one_left`,
  `CliffordAlgebra.realCliffordSpinBlockSum_one_right`, and
  `CliffordAlgebra.realCliffordSpinFirstInclusion_blockSum`: compatibility of block sum with
  first- and last-coordinate stabilization.
* `CliffordAlgebra.realCliffordSpinBlockSum_assoc`: associativity coherence of the Spin block sum.
* `CliffordAlgebra.realCliffordBlockSwapIsometry_spinGroupEquiv_blockSum`: permutation coherence of
  the Spin block sum under swapping the two coordinate blocks.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§2–3.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti TauCeti.QuadraticMap

noncomputable section

/-! ### First-coordinate Spin and special-orthogonal stabilization -/

/-- The quadratic isometry `v ↦ Fin.cons 0 v` including `realCliffordForm n 0` into
`realCliffordForm (n + 1) 0` after the new first coordinate. -/
def realCliffordSpinFirstInclusionIsometry (n : ℕ) :
    realCliffordForm n 0 →qᵢ realCliffordForm (n + 1) 0 :=
  (realCliffordFirstSplitIsometry n).symm.toIsometry.comp
    (Isometry.inr (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0))

/-- `realCliffordSpinFirstInclusionIsometry` prepends `0` in the first coordinate. -/
@[simp]
theorem realCliffordSpinFirstInclusionIsometry_apply (n : ℕ) (v : Fin n → ℝ) :
    realCliffordSpinFirstInclusionIsometry n v = Fin.cons 0 v := by
  simp [realCliffordSpinFirstInclusionIsometry]

/-- The first-coordinate stabilization homomorphism `Spin(n) →* Spin(n + 1)` induced by
`v ↦ Fin.cons 0 v`. -/
def realCliffordSpinFirstInclusion (n : ℕ) :
    realCliffordSpinGroupZero n →* realCliffordSpinGroupZero (n + 1) :=
  (realCliffordSpinFirstInclusionIsometry n).spinGroupMap

/-- `realCliffordSpinFirstInclusion` is the Spin-group map of its defining quadratic isometry. -/
theorem realCliffordSpinFirstInclusion_eq_spinGroupMap (n : ℕ) :
    realCliffordSpinFirstInclusion n = (realCliffordSpinFirstInclusionIsometry n).spinGroupMap :=
  (rfl)

/-- The Clifford-algebra value of `realCliffordSpinFirstInclusion` is the image under
`CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry n)`. -/
@[simp]
theorem coe_realCliffordSpinFirstInclusion_apply (n : ℕ) (x : realCliffordSpinGroupZero n) :
    (realCliffordSpinFirstInclusion n x : CliffordAlgebra (realCliffordForm (n + 1) 0)) =
      CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry n)
        (x : CliffordAlgebra (realCliffordForm n 0)) :=
  Isometry.coe_spinGroupMap_apply _ _

/-- `realCliffordSpinFirstInclusion` agrees with `spinGroupProd` on `(1, x)` transported along
`realCliffordFirstSplitIsometry`. -/
theorem realCliffordSpinFirstInclusion_eq_spinGroupProd (n : ℕ) (x : realCliffordSpinGroupZero n) :
    realCliffordSpinFirstInclusion n x =
      (realCliffordFirstSplitIsometry n).symm.spinGroupEquiv
        (spinGroupProd (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0) (1, x)) := by
  rw [spinGroupProd_one_inr, IsometryEquiv.spinGroupEquiv_apply, ← MonoidHom.comp_apply,
    Isometry.spinGroupMap_comp]
  rfl

/-- The Clifford-algebra map induced by `realCliffordSpinFirstInclusionIsometry` is injective. -/
theorem realCliffordSpinFirstInclusionIsometry_map_injective (n : ℕ) :
    Function.Injective (CliffordAlgebra.map (realCliffordSpinFirstInclusionIsometry n)) := by
  have hinr : Isometry.inr (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0) =
      (IsometryEquiv.prodComm (realCliffordForm n 0)
        (QuadraticMap.sq (R := ℝ) (A := ℝ))).toIsometry.comp
        (Isometry.inl (realCliffordForm n 0) (QuadraticMap.sq (R := ℝ) (A := ℝ))) :=
    Isometry.ext fun _ ↦ by simp
  rw [realCliffordSpinFirstInclusionIsometry, hinr, ← CliffordAlgebra.map_comp_map,
    ← CliffordAlgebra.map_comp_map]
  refine (CliffordAlgebra.leftInverse_map_of_leftInverse
    (realCliffordFirstSplitIsometry n).symm.toIsometry
    (realCliffordFirstSplitIsometry n).toIsometry
    (realCliffordFirstSplitIsometry n).apply_symm_apply).injective.comp ?_
  exact (CliffordAlgebra.leftInverse_map_of_leftInverse
    (IsometryEquiv.prodComm (realCliffordForm n 0) (QuadraticMap.sq (R := ℝ) (A := ℝ))).toIsometry
    (IsometryEquiv.prodComm (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0)).toIsometry
    (IsometryEquiv.prodComm (realCliffordForm n 0)
      (QuadraticMap.sq (R := ℝ) (A := ℝ))).symm_apply_apply).injective.comp
    (CliffordAlgebra.map_inl_injective (realCliffordForm n 0)
      (QuadraticMap.sq (R := ℝ) (A := ℝ)))

/-- The first-coordinate stabilization homomorphism `Spin(n) →* Spin(n + 1)` is injective. -/
theorem realCliffordSpinFirstInclusion_injective (n : ℕ) :
    Function.Injective (realCliffordSpinFirstInclusion n) :=
  (realCliffordSpinFirstInclusionIsometry n).spinGroupMap_injective
    (realCliffordSpinFirstInclusionIsometry_map_injective n)

/-- In positive rank, first-coordinate Spin stabilization preserves the nontrivial kernel element
`-1`. -/
@[simp]
theorem realCliffordSpinFirstInclusion_negOne (n : ℕ) [NeZero n] :
    realCliffordSpinFirstInclusion n
        (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero) =
      spinGroup.negOne (realCliffordForm (n + 1) 0)
        (nondegenerate_realCliffordForm (n + 1) 0).ne_zero :=
  (realCliffordSpinFirstInclusionIsometry n).spinGroupMap_negOne
    (nondegenerate_realCliffordForm n 0).ne_zero

/-- `realCliffordSpinFirstInclusion` fixes the first coordinate `r` and acts by the original Spin
element on the tail `v` of `Fin.cons r v`. -/
@[simp]
theorem spinVectorAction_realCliffordSpinFirstInclusion_cons (n : ℕ)
    (x : realCliffordSpinGroupZero n) (r : ℝ) (v : Fin n → ℝ) :
    spinVectorAction (realCliffordForm (n + 1) 0) (realCliffordSpinFirstInclusion n x)
        (Fin.cons r v) =
      Fin.cons r (spinVectorAction (realCliffordForm n 0) x v) := by
  have h := Isometry.spinGroupMap_spinVectorAction
    (realCliffordFirstSplitIsometry n).symm.toIsometry
    (spinGroupProd (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0) (1, x)) (r, v)
  rw [← IsometryEquiv.spinGroupEquiv_apply, ← realCliffordSpinFirstInclusion_eq_spinGroupProd,
    spinVectorAction_spinGroupProd, spinVectorAction_one] at h
  simpa using h

/-- `realCliffordSpinFirstInclusion` fixes the first standard basis vector `Pi.single 0 1`. -/
@[simp]
theorem realCliffordSpinFirstInclusion_fixed_zero (n : ℕ) (x : realCliffordSpinGroupZero n) :
    spinVectorAction (realCliffordForm (n + 1) 0) (realCliffordSpinFirstInclusion n x)
        (Pi.single 0 1) =
      Pi.single 0 1 := by
  have hsingle : (Pi.single 0 (1 : ℝ) : Fin (n + 1) → ℝ) = Fin.cons 1 0 := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hsingle, spinVectorAction_realCliffordSpinFirstInclusion_cons, map_zero]

/-- The first-coordinate block inclusion `SO(n) →* SO(n + 1)` acting as the identity on coordinate
`0` and by the given special orthogonal transformation on the remaining `n` coordinates. -/
def realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    specialOrthogonalGroup (realCliffordForm n 0) →*
      specialOrthogonalGroup (realCliffordForm (n + 1) 0) :=
  (realCliffordFirstSplitIsometry n).symm.specialOrthogonalGroupCongr.toMonoidHom.comp
    ((specialOrthogonalGroupProd (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0)).comp
      (MonoidHom.inr _ _))

/-- `realCliffordSpecialOrthogonalFirstInclusion` fixes `r` and applies `g` to `v` on
`Fin.cons r v`. -/
@[simp]
theorem realCliffordSpecialOrthogonalFirstInclusion_apply_cons (n : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm n 0)) (r : ℝ) (v : Fin n → ℝ) :
    (realCliffordSpecialOrthogonalFirstInclusion n g :
        (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Fin.cons r v) =
      Fin.cons r ((g : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v) := by
  have hss : (realCliffordFirstSplitIsometry n).symm.symm = realCliffordFirstSplitIsometry n :=
    DFunLike.ext _ _ fun _ ↦ rfl
  simp [realCliffordSpecialOrthogonalFirstInclusion, hss]

/-- `realCliffordSpecialOrthogonalFirstInclusion` fixes the first standard basis vector
`Pi.single 0 1`. -/
@[simp]
theorem realCliffordSpecialOrthogonalFirstInclusion_fixed_zero (n : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm n 0)) :
    (realCliffordSpecialOrthogonalFirstInclusion n g :
        (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Pi.single 0 1) =
      Pi.single 0 1 := by
  have hsingle : (Pi.single 0 (1 : ℝ) : Fin (n + 1) → ℝ) = Fin.cons 1 0 := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hsingle, realCliffordSpecialOrthogonalFirstInclusion_apply_cons, map_zero]

/-- The first-coordinate block inclusion `SO(n) →* SO(n + 1)` is injective. -/
theorem realCliffordSpecialOrthogonalFirstInclusion_injective (n : ℕ) :
    Function.Injective (realCliffordSpecialOrthogonalFirstInclusion n) := by
  intro f g h
  have hprod := (specialOrthogonalGroupProd_injective
    (QuadraticMap.sq (R := ℝ) (A := ℝ)) (realCliffordForm n 0)) <|
    (realCliffordFirstSplitIsometry n).symm.specialOrthogonalGroupCongr.injective h
  exact (Prod.mk.inj hprod).2

/-- **First-coordinate Spin stabilization commutes with the projection to `SO`.** -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinFirstInclusion (n : ℕ)
    (x : realCliffordSpinGroupZero n) :
    spinToSpecialOrthogonal (realCliffordForm (n + 1) 0) (realCliffordSpinFirstInclusion n x) =
      realCliffordSpecialOrthogonalFirstInclusion n
        (spinToSpecialOrthogonal (realCliffordForm n 0) x) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro (w : Fin (n + 1) → ℝ)
  rw [← Fin.cons_self_tail w, coe_spinToSpecialOrthogonal_apply,
    spinVectorAction_realCliffordSpinFirstInclusion_cons,
    realCliffordSpecialOrthogonalFirstInclusion_apply_cons, coe_spinToSpecialOrthogonal_apply]

/-- Homomorphism-level compatibility of `realCliffordSpinFirstInclusion` with
`spinToSpecialOrthogonal`. -/
theorem spinToSpecialOrthogonal_comp_realCliffordSpinFirstInclusion (n : ℕ) :
    (spinToSpecialOrthogonal (realCliffordForm (n + 1) 0)).comp
        (realCliffordSpinFirstInclusion n) =
      (realCliffordSpecialOrthogonalFirstInclusion n).comp
        (spinToSpecialOrthogonal (realCliffordForm n 0)) :=
  MonoidHom.ext (spinToSpecialOrthogonal_realCliffordSpinFirstInclusion n)

/-- Compatibility of `realCliffordSpinFirstInclusion` with the packaged compact Spin double cover
in positive rank. -/
theorem realCliffordSpinDoubleCoverZero_rightHom_firstInclusion (n : ℕ) [NeZero n]
    (x : realCliffordSpinGroupZero n) :
    (realCliffordSpinDoubleCoverZero (n + 1)).rightHom (realCliffordSpinFirstInclusion n x) =
      realCliffordSpecialOrthogonalFirstInclusion n
        ((realCliffordSpinDoubleCoverZero n).rightHom x) := by
  simp

/-! ### Compact Spin and special-orthogonal block sums -/

/-- The quadratic isometry `u ↦ Fin.append u 0` embedding `realCliffordForm p 0` as the first `p`
coordinates of `realCliffordForm (p + q) 0`. -/
def realCliffordSpinBlockInlIsometry (p q : ℕ) :
    realCliffordForm p 0 →qᵢ realCliffordForm (p + q) 0 :=
  (realCliffordSplitIsometry p q 0 0).symm.toIsometry.comp
    (Isometry.inl (realCliffordForm p 0) (realCliffordForm q 0))

/-- `realCliffordSpinBlockInlIsometry` pads `u` on the right by `0`. -/
@[simp]
theorem realCliffordSpinBlockInlIsometry_apply (p q : ℕ) (u : Fin p → ℝ) :
    realCliffordSpinBlockInlIsometry p q u = (Fin.append u 0 : Fin (p + q) → ℝ) := by
  rw [realCliffordSpinBlockInlIsometry, Isometry.comp_apply, IsometryEquiv.toIsometry_apply,
    Isometry.inl_apply, realCliffordSplitIsometry_zero_symm_apply]

/-- The quadratic isometry `v ↦ Fin.append 0 v` embedding `realCliffordForm q 0` as the last `q`
coordinates of `realCliffordForm (p + q) 0`. -/
def realCliffordSpinBlockInrIsometry (p q : ℕ) :
    realCliffordForm q 0 →qᵢ realCliffordForm (p + q) 0 :=
  (realCliffordSplitIsometry p q 0 0).symm.toIsometry.comp
    (Isometry.inr (realCliffordForm p 0) (realCliffordForm q 0))

/-- `realCliffordSpinBlockInrIsometry` pads `v` on the left by `0`. -/
@[simp]
theorem realCliffordSpinBlockInrIsometry_apply (p q : ℕ) (v : Fin q → ℝ) :
    realCliffordSpinBlockInrIsometry p q v = (Fin.append 0 v : Fin (p + q) → ℝ) := by
  rw [realCliffordSpinBlockInrIsometry, Isometry.comp_apply, IsometryEquiv.toIsometry_apply,
    Isometry.inr_apply, realCliffordSplitIsometry_zero_symm_apply]

/-- Spin elements coming from the first `p` and last `q` coordinate blocks commute in
`Spin(p + q)`. -/
theorem commute_realCliffordSpinBlockInl_inr (p q : ℕ)
    (x : realCliffordSpinGroupZero p) (y : realCliffordSpinGroupZero q) :
    Commute ((realCliffordSpinBlockInlIsometry p q).spinGroupMap x)
      ((realCliffordSpinBlockInrIsometry p q).spinGroupMap y) := by
  rw [realCliffordSpinBlockInlIsometry, realCliffordSpinBlockInrIsometry,
    ← Isometry.spinGroupMap_comp, ← Isometry.spinGroupMap_comp, MonoidHom.comp_apply,
    MonoidHom.comp_apply]
  exact (commute_spinGroupMap_inl_spinGroupMap_inr
    (realCliffordForm p 0) (realCliffordForm q 0) x y).map _

/-- **The compact Spin block-sum homomorphism `Spin(p) × Spin(q) →* Spin(p + q)`**, multiplying the
images of the two native block-inclusion Spin maps. -/
def realCliffordSpinBlockSum (p q : ℕ) :
    realCliffordSpinGroupZero p × realCliffordSpinGroupZero q →*
      realCliffordSpinGroupZero (p + q) :=
  (realCliffordSplitIsometry p q 0 0).symm.spinGroupEquiv.toMonoidHom.comp
    (spinGroupProd (realCliffordForm p 0) (realCliffordForm q 0))

/-- `realCliffordSpinBlockSum` is `spinGroupProd` transported along
`(realCliffordSplitIsometry p q 0 0).symm`. -/
theorem realCliffordSpinBlockSum_apply (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    realCliffordSpinBlockSum p q x =
      (realCliffordSplitIsometry p q 0 0).symm.spinGroupEquiv
        (spinGroupProd (realCliffordForm p 0) (realCliffordForm q 0) x) :=
  (rfl)

/-- `realCliffordSpinBlockSum` multiplies the Spin images of the two coordinate-block inclusions
`u ↦ Fin.append u 0` and `v ↦ Fin.append 0 v`. -/
theorem realCliffordSpinBlockSum_eq_mul (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    realCliffordSpinBlockSum p q x =
      (realCliffordSpinBlockInlIsometry p q).spinGroupMap x.1 *
        (realCliffordSpinBlockInrIsometry p q).spinGroupMap x.2 := by
  rw [realCliffordSpinBlockSum_apply, spinGroupProd_apply, map_mul,
    IsometryEquiv.spinGroupEquiv_apply, IsometryEquiv.spinGroupEquiv_apply,
    ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, Isometry.spinGroupMap_comp,
    Isometry.spinGroupMap_comp]
  rfl

/-- Restricting `realCliffordSpinBlockSum` to `(x, 1)` gives the left-block Spin map. -/
@[simp]
theorem realCliffordSpinBlockSum_inl_one (p q : ℕ) (x : realCliffordSpinGroupZero p) :
    realCliffordSpinBlockSum p q (x, 1) =
      (realCliffordSpinBlockInlIsometry p q).spinGroupMap x := by
  rw [realCliffordSpinBlockSum_eq_mul, map_one, mul_one]

/-- Restricting `realCliffordSpinBlockSum` to `(1, y)` gives the right-block Spin map. -/
@[simp]
theorem realCliffordSpinBlockSum_one_inr (p q : ℕ) (y : realCliffordSpinGroupZero q) :
    realCliffordSpinBlockSum p q (1, y) =
      (realCliffordSpinBlockInrIsometry p q).spinGroupMap y := by
  rw [realCliffordSpinBlockSum_eq_mul, map_one, one_mul]

/-- `realCliffordSpinBlockSum` acts blockwise on `Fin.append u v`. -/
@[simp]
theorem spinVectorAction_realCliffordSpinBlockSum_append (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q)
    (u : Fin p → ℝ) (v : Fin q → ℝ) :
    spinVectorAction (realCliffordForm (p + q) 0) (realCliffordSpinBlockSum p q x)
        (Fin.append u v : Fin (p + q) → ℝ) =
      Fin.append (spinVectorAction (realCliffordForm p 0) x.1 u)
        (spinVectorAction (realCliffordForm q 0) x.2 v) := by
  have h := Isometry.spinGroupMap_spinVectorAction
    (realCliffordSplitIsometry p q 0 0).symm.toIsometry
    (spinGroupProd (realCliffordForm p 0) (realCliffordForm q 0) x) (u, v)
  rwa [← IsometryEquiv.spinGroupEquiv_apply, ← realCliffordSpinBlockSum_apply,
    spinVectorAction_spinGroupProd, IsometryEquiv.toIsometry_apply,
    IsometryEquiv.toIsometry_apply, realCliffordSplitIsometry_zero_symm_apply,
    realCliffordSplitIsometry_zero_symm_apply] at h

/-- **The compact special-orthogonal block-sum homomorphism `SO(p) × SO(q) →* SO(p + q)`.** -/
def realCliffordSpecialOrthogonalBlockSum (p q : ℕ) :
    specialOrthogonalGroup (realCliffordForm p 0) ×
        specialOrthogonalGroup (realCliffordForm q 0) →*
      specialOrthogonalGroup (realCliffordForm (p + q) 0) :=
  (realCliffordSplitIsometry p q 0 0).symm.specialOrthogonalGroupCongr.toMonoidHom.comp
    (specialOrthogonalGroupProd (realCliffordForm p 0) (realCliffordForm q 0))

/-- `realCliffordSpecialOrthogonalBlockSum` is `specialOrthogonalGroupProd` transported along
`(realCliffordSplitIsometry p q 0 0).symm`. -/
theorem realCliffordSpecialOrthogonalBlockSum_apply (p q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0) ×
      specialOrthogonalGroup (realCliffordForm q 0)) :
    realCliffordSpecialOrthogonalBlockSum p q g =
      (realCliffordSplitIsometry p q 0 0).symm.specialOrthogonalGroupCongr
        (specialOrthogonalGroupProd (realCliffordForm p 0) (realCliffordForm q 0) g) :=
  (rfl)

/-- `realCliffordSpecialOrthogonalBlockSum` acts blockwise on `Fin.append u v`. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSum_apply_append (p q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0) ×
      specialOrthogonalGroup (realCliffordForm q 0))
    (u : Fin p → ℝ) (v : Fin q → ℝ) :
    (realCliffordSpecialOrthogonalBlockSum p q g :
        (Fin (p + q) → ℝ) ≃ₗ[ℝ] (Fin (p + q) → ℝ)) (Fin.append u v : Fin (p + q) → ℝ) =
      Fin.append ((g.1 : (Fin p → ℝ) ≃ₗ[ℝ] (Fin p → ℝ)) u)
        ((g.2 : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ)) v) := by
  have h : (Fin.append u v : Fin (p + q) → ℝ) =
      (realCliffordSplitIsometry p q 0 0).symm (u, v) :=
    (realCliffordSplitIsometry_zero_symm_apply p q (u, v)).symm
  have hss : (realCliffordSplitIsometry p q 0 0).symm.symm = realCliffordSplitIsometry p q 0 0 :=
    DFunLike.ext _ _ fun _ ↦ rfl
  rw [h, realCliffordSpecialOrthogonalBlockSum_apply,
    IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, hss,
    IsometryEquiv.apply_symm_apply, specialOrthogonalGroupProd_apply,
    realCliffordSplitIsometry_zero_symm_apply]

/-- The special-orthogonal block-sum homomorphism `SO(p) × SO(q) →* SO(p + q)` is injective. -/
theorem realCliffordSpecialOrthogonalBlockSum_injective (p q : ℕ) :
    Function.Injective (realCliffordSpecialOrthogonalBlockSum p q) :=
  (realCliffordSplitIsometry p q 0 0).symm.specialOrthogonalGroupCongr.injective.comp
    (specialOrthogonalGroupProd_injective (realCliffordForm p 0) (realCliffordForm q 0))

/-- **The projection of `realCliffordSpinBlockSum` to `SO(p + q)`** is the special-orthogonal block
sum of the projections of its two factors. -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinBlockSum (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    spinToSpecialOrthogonal (realCliffordForm (p + q) 0) (realCliffordSpinBlockSum p q x) =
      realCliffordSpecialOrthogonalBlockSum p q
        (spinToSpecialOrthogonal (realCliffordForm p 0) x.1,
          spinToSpecialOrthogonal (realCliffordForm q 0) x.2) := by
  rw [realCliffordSpinBlockSum_apply,
    ← IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    spinToSpecialOrthogonal_spinGroupProd, realCliffordSpecialOrthogonalBlockSum_apply]

section Kernel

variable (p q : ℕ) [NeZero p] [NeZero q]

/-- For positive `p` and `q`, a pair in `Spin(p) × Spin(q)` lies in the kernel of
`realCliffordSpinBlockSum p q` exactly when it is `(1, 1)` or `(-1, -1)`. -/
theorem mem_ker_realCliffordSpinBlockSum_iff
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    x ∈ (realCliffordSpinBlockSum p q).ker ↔
      x = 1 ∨ x = (spinGroup.negOne (realCliffordForm p 0)
          (nondegenerate_realCliffordForm p 0).ne_zero,
        spinGroup.negOne (realCliffordForm q 0) (nondegenerate_realCliffordForm q 0).ne_zero) := by
  have : Nontrivial (Fin (p + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin p → ℝ))
  have : Nontrivial (Fin (q + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin q → ℝ))
  rw [MonoidHom.mem_ker, realCliffordSpinBlockSum_apply, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker,
    mem_ker_spinGroupProd_iff (nondegenerate_realCliffordForm p 0)
      (nondegenerate_realCliffordForm q 0)]

/-- For positive `p` and `q`, the kernel of `realCliffordSpinBlockSum p q` is generated by
`(-1, -1)`. -/
theorem ker_realCliffordSpinBlockSum :
    (realCliffordSpinBlockSum p q).ker =
      Subgroup.zpowers (spinGroup.negOne (realCliffordForm p 0)
          (nondegenerate_realCliffordForm p 0).ne_zero,
        spinGroup.negOne (realCliffordForm q 0) (nondegenerate_realCliffordForm q 0).ne_zero) := by
  have : Nontrivial (Fin (p + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin p → ℝ))
  have : Nontrivial (Fin (q + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin q → ℝ))
  refine le_antisymm (fun x hx ↦ ?_) (Subgroup.zpowers_le.mpr ?_)
  · rcases (mem_ker_realCliffordSpinBlockSum_iff p q x).mp hx with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · exact (mem_ker_realCliffordSpinBlockSum_iff p q _).mpr (Or.inr rfl)

/-- For positive `p` and `q`, `(Spin(p) × Spin(q)) / ⟨(-1, -1)⟩` is multiplicatively isomorphic to
the image of `realCliffordSpinBlockSum p q` in `Spin(p + q)`. -/
def realCliffordSpinBlockSumQuotientEquiv :
    (realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) ⧸
        Subgroup.zpowers (spinGroup.negOne (realCliffordForm p 0)
          (nondegenerate_realCliffordForm p 0).ne_zero,
        spinGroup.negOne (realCliffordForm q 0) (nondegenerate_realCliffordForm q 0).ne_zero) ≃*
      (realCliffordSpinBlockSum p q).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_realCliffordSpinBlockSum p q).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

/-- `realCliffordSpinBlockSumQuotientEquiv` sends the class of `x` to its block-sum image. -/
@[simp]
theorem coe_realCliffordSpinBlockSumQuotientEquiv_mk
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    (realCliffordSpinBlockSumQuotientEquiv p q x : realCliffordSpinGroupZero (p + q)) =
      realCliffordSpinBlockSum p q x :=
  (rfl)

end Kernel

/-! ### Unit, stabilization, associativity, and permutation coherences -/

/-- **Right-unit coherence for `realCliffordSpinBlockSum`**: summing with `Spin(0)` on the right is
the projection onto the first factor (with no cast needed, since `p + 0 = p` definitionally). -/
@[simp]
theorem realCliffordSpinBlockSum_zero_right (p : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero 0) :
    realCliffordSpinBlockSum p 0 x = x.1 := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have he : (realCliffordSplitIsometry p 0 0 0).symm =
      IsometryEquiv.prodUnique (realCliffordForm p 0) (realCliffordForm 0 0) :=
    DFunLike.ext _ _ fun ⟨u, v⟩ ↦ funext fun i ↦ by
      have hv : (v : Fin 0 → ℝ) = Fin.elim0 := Subsingleton.elim _ _
      rw [realCliffordSplitIsometry_zero_symm_apply, IsometryEquiv.prodUnique_apply, hv,
        Fin.append_elim0]
      simp
  rw [realCliffordSpinBlockSum_apply, he]
  exact prodUnique_spinGroupEquiv_spinGroupProd (realCliffordForm p 0) (realCliffordForm 0 0) x

/-- **Right-unit coherence for `realCliffordSpecialOrthogonalBlockSum`**. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSum_zero_right (p : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0) ×
      specialOrthogonalGroup (realCliffordForm 0 0)) :
    realCliffordSpecialOrthogonalBlockSum p 0 g = g.1 := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have he : (realCliffordSplitIsometry p 0 0 0).symm =
      IsometryEquiv.prodUnique (realCliffordForm p 0) (realCliffordForm 0 0) :=
    DFunLike.ext _ _ fun ⟨u, v⟩ ↦ funext fun i ↦ by
      have hv : (v : Fin 0 → ℝ) = Fin.elim0 := Subsingleton.elim _ _
      rw [realCliffordSplitIsometry_zero_symm_apply, IsometryEquiv.prodUnique_apply, hv,
        Fin.append_elim0]
      simp
  rw [realCliffordSpecialOrthogonalBlockSum_apply, he]
  exact prodUnique_specialOrthogonalGroupCongr_specialOrthogonalGroupProd
    (realCliffordForm p 0) (realCliffordForm 0 0) g

/-- **Left-unit coherence for `realCliffordSpinBlockSum`**: summing with `Spin(0)` on the left and
reindexing `0 + q = q` recovers the second factor. -/
theorem realCliffordSpinBlockSum_zero_left (q : ℕ)
    (x : realCliffordSpinGroupZero 0 × realCliffordSpinGroupZero q) :
    (realCliffordFormCongr (Nat.zero_add q) rfl).spinGroupEquiv
        (realCliffordSpinBlockSum 0 q x) = x.2 := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have he : (realCliffordSplitIsometry 0 q 0 0).symm.trans
      (realCliffordFormCongr (Nat.zero_add q) rfl) =
      IsometryEquiv.uniqueProd (realCliffordForm 0 0) (realCliffordForm q 0) :=
    DFunLike.ext _ _ fun ⟨u, v⟩ ↦ funext fun i ↦ by
      have hu : u = Fin.elim0 := Subsingleton.elim _ _
      subst hu
      simp only [IsometryEquiv.trans_apply, IsometryEquiv.uniqueProd_apply,
        realCliffordSplitIsometry_zero_symm_apply, Fin.elim0_append,
        realCliffordFormCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [realCliffordSpinBlockSum_apply, ← MulEquiv.trans_apply, ← IsometryEquiv.spinGroupEquiv_trans,
    he, uniqueProd_spinGroupEquiv_spinGroupProd]

/-- **Left-unit coherence for `realCliffordSpecialOrthogonalBlockSum`**. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSum_zero_left (q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm 0 0) ×
      specialOrthogonalGroup (realCliffordForm q 0)) :
    (realCliffordFormCongr (Nat.zero_add q) rfl).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum 0 q g) = g.2 := by
  have : IsEmpty (Fin (0 + 0)) := inferInstanceAs (IsEmpty (Fin 0))
  have he : (realCliffordSplitIsometry 0 q 0 0).symm.trans
      (realCliffordFormCongr (Nat.zero_add q) rfl) =
      IsometryEquiv.uniqueProd (realCliffordForm 0 0) (realCliffordForm q 0) :=
    DFunLike.ext _ _ fun ⟨u, v⟩ ↦ funext fun i ↦ by
      have hu : u = Fin.elim0 := Subsingleton.elim _ _
      subst hu
      simp only [IsometryEquiv.trans_apply, IsometryEquiv.uniqueProd_apply,
        realCliffordSplitIsometry_zero_symm_apply, Fin.elim0_append,
        realCliffordFormCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [realCliffordSpecialOrthogonalBlockSum_apply, ← MulEquiv.trans_apply,
    ← IsometryEquiv.specialOrthogonalGroupCongr_trans, he,
    uniqueProd_specialOrthogonalGroupCongr_specialOrthogonalGroupProd]

/-- **Single-step stabilization via left block sum**: forming `realCliffordSpinBlockSum 1 n (1, x)`
and reindexing `1 + n = n + 1` gives `realCliffordSpinFirstInclusion n x`. -/
theorem realCliffordSpinBlockSum_one_left (n : ℕ) (x : realCliffordSpinGroupZero n) :
    (realCliffordFormCongr (Nat.add_comm 1 n) rfl).spinGroupEquiv
        (realCliffordSpinBlockSum 1 n (1, x)) =
      realCliffordSpinFirstInclusion n x := by
  have hiso : (realCliffordFormCongr (Nat.add_comm 1 n) rfl).toIsometry.comp
      (realCliffordSpinBlockInrIsometry 1 n) =
      realCliffordSpinFirstInclusionIsometry n :=
    Isometry.ext fun v ↦ funext fun i ↦ by
      simp only [Isometry.comp_apply, IsometryEquiv.toIsometry_apply,
        realCliffordFormCongr_apply, realCliffordSpinBlockInrIsometry_apply,
        realCliffordSpinFirstInclusionIsometry_apply, Fin.append_left_eq_cons, Pi.zero_apply,
        Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [realCliffordSpinBlockSum_one_inr, IsometryEquiv.spinGroupEquiv_apply,
    ← MonoidHom.comp_apply, Isometry.spinGroupMap_comp, hiso,
    realCliffordSpinFirstInclusion_eq_spinGroupMap]

/-- **Single-step special-orthogonal stabilization via left block sum**. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSum_one_left (n : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm n 0)) :
    (realCliffordFormCongr (Nat.add_comm 1 n) rfl).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum 1 n (1, g)) =
      realCliffordSpecialOrthogonalFirstInclusion n g := by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm n 0) (posDef_realCliffordForm_zero n) g
  have hsum := spinToSpecialOrthogonal_realCliffordSpinBlockSum 1 n (1, x)
  rw [map_one] at hsum
  rw [← hsum, IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    realCliffordSpinBlockSum_one_left, spinToSpecialOrthogonal_realCliffordSpinFirstInclusion]

/-- **Last-coordinate inclusion via right block sum**: `realCliffordSpinBlockSum n 1 (x, 1)` equals
the last-coordinate inclusion `realCliffordSpinInclusion n x` on the nose. -/
theorem realCliffordSpinBlockSum_one_right (n : ℕ) (x : realCliffordSpinGroupZero n) :
    realCliffordSpinBlockSum n 1 (x, 1) = realCliffordSpinInclusion n x := by
  have hiso : realCliffordSpinBlockInlIsometry n 1 = realCliffordSpinInclusionIsometry n := by
    refine Isometry.ext fun u ↦ ?_
    rw [realCliffordSpinBlockInlIsometry_apply, realCliffordSpinInclusionIsometry_apply,
      IsometryEquiv.eq_symm_apply]
    refine Prod.ext (funext fun i ↦ ?_) ?_
    · have hcast : (i.castSucc : Fin (n + 1)) = Fin.castAdd 1 i := rfl
      simpa [Fin.castAdd_zero, hcast] using
        realCliffordPositiveSplitIsometry_fst_pos n 0 (Fin.append u 0 : Fin (n + 1) → ℝ) i
    · have hlast : (Fin.last n : Fin (n + 1)) = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp)
      simpa [Fin.castAdd_zero, hlast] using
        realCliffordPositiveSplitIsometry_snd n 0 (Fin.append u 0 : Fin (n + 1) → ℝ)
  rw [realCliffordSpinBlockSum_inl_one, hiso, realCliffordSpinInclusion_eq_spinGroupMap]

/-- **Compatibility of Spin block sum with first-coordinate stabilization**: stabilizing the first
factor of `(x, y) ∈ Spin(p) × Spin(q)` and reindexing `(p + 1) + q = (p + q) + 1` agrees with
stabilizing `realCliffordSpinBlockSum p q (x, y)`. -/
theorem realCliffordSpinFirstInclusion_blockSum (p q : ℕ)
    (x : realCliffordSpinGroupZero p) (y : realCliffordSpinGroupZero q) :
    (realCliffordFormCongr (Nat.add_right_comm p 1 q) rfl).spinGroupEquiv
        (realCliffordSpinBlockSum (p + 1) q (realCliffordSpinFirstInclusion p x, y)) =
      realCliffordSpinFirstInclusion (p + q) (realCliffordSpinBlockSum p q (x, y)) := by
  have h₁ : ((realCliffordFormCongr (Nat.add_right_comm p 1 q) rfl).toIsometry.comp
        (realCliffordSpinBlockInlIsometry (p + 1) q)).comp
        (realCliffordSpinFirstInclusionIsometry p) =
      (realCliffordSpinFirstInclusionIsometry (p + q)).comp
        (realCliffordSpinBlockInlIsometry p q) :=
    Isometry.ext fun u ↦ funext fun i ↦ by
      simp only [Isometry.comp_apply, IsometryEquiv.toIsometry_apply,
        realCliffordFormCongr_apply, realCliffordSpinBlockInlIsometry_apply,
        realCliffordSpinFirstInclusionIsometry_apply, Fin.append_cons, Function.comp_apply,
        Fin.cast_cast, Fin.cast_eq_self]
  have h₂ : (realCliffordFormCongr (Nat.add_right_comm p 1 q) rfl).toIsometry.comp
      (realCliffordSpinBlockInrIsometry (p + 1) q) =
      (realCliffordSpinFirstInclusionIsometry (p + q)).comp
        (realCliffordSpinBlockInrIsometry p q) :=
    Isometry.ext fun v ↦ funext fun i ↦ by
      have hzero : (0 : Fin (p + 1) → ℝ) = Fin.cons 0 (0 : Fin p → ℝ) := by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp
      simp only [Isometry.comp_apply, IsometryEquiv.toIsometry_apply,
        realCliffordFormCongr_apply, realCliffordSpinBlockInrIsometry_apply,
        realCliffordSpinFirstInclusionIsometry_apply, hzero, Fin.append_cons,
        Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [realCliffordSpinBlockSum_eq_mul, realCliffordSpinBlockSum_eq_mul,
    realCliffordSpinFirstInclusion_eq_spinGroupMap,
    realCliffordSpinFirstInclusion_eq_spinGroupMap, IsometryEquiv.spinGroupEquiv_apply,
    map_mul, map_mul, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    Isometry.spinGroupMap_comp, Isometry.spinGroupMap_comp, ← MonoidHom.comp_apply,
    Isometry.spinGroupMap_comp, h₁, h₂, ← Isometry.spinGroupMap_comp,
    ← Isometry.spinGroupMap_comp, MonoidHom.comp_apply, MonoidHom.comp_apply]

/-- **Compatibility of special-orthogonal block sum with first-coordinate stabilization**. -/
theorem realCliffordSpecialOrthogonalFirstInclusion_blockSum (p q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0))
    (h : specialOrthogonalGroup (realCliffordForm q 0)) :
    (realCliffordFormCongr (Nat.add_right_comm p 1 q) rfl).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum (p + 1) q
          (realCliffordSpecialOrthogonalFirstInclusion p g, h)) =
      realCliffordSpecialOrthogonalFirstInclusion (p + q)
        (realCliffordSpecialOrthogonalBlockSum p q (g, h)) := by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) g
  obtain ⟨y, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) h
  rw [← spinToSpecialOrthogonal_realCliffordSpinFirstInclusion,
    ← spinToSpecialOrthogonal_realCliffordSpinBlockSum (p + 1) q
      (realCliffordSpinFirstInclusion p x, y),
    IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    realCliffordSpinFirstInclusion_blockSum,
    spinToSpecialOrthogonal_realCliffordSpinFirstInclusion,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum]

/-- **Associativity coherence of `realCliffordSpinBlockSum`**: the two parenthesizations of a
threefold compact Spin block sum agree along `realCliffordFormCongr (Nat.add_assoc p q r) rfl`. -/
theorem realCliffordSpinBlockSum_assoc (p q r : ℕ)
    (x : realCliffordSpinGroupZero p) (y : realCliffordSpinGroupZero q)
    (z : realCliffordSpinGroupZero r) :
    (realCliffordFormCongr (Nat.add_assoc p q r) rfl).spinGroupEquiv
        (realCliffordSpinBlockSum (p + q) r (realCliffordSpinBlockSum p q (x, y), z)) =
      realCliffordSpinBlockSum p (q + r) (x, realCliffordSpinBlockSum q r (y, z)) := by
  let eL : (((realCliffordForm p 0).prod (realCliffordForm q 0)).prod
      (realCliffordForm r 0)).IsometryEquiv (realCliffordForm (p + (q + r)) 0) :=
    (((realCliffordSplitIsometry p q 0 0).symm.prod (.refl _)).trans
      (realCliffordSplitIsometry (p + q) r 0 0).symm).trans
      (realCliffordFormCongr (Nat.add_assoc p q r) rfl)
  let eR : ((realCliffordForm p 0).prod ((realCliffordForm q 0).prod
      (realCliffordForm r 0))).IsometryEquiv (realCliffordForm (p + (q + r)) 0) :=
    ((IsometryEquiv.refl _).prod (realCliffordSplitIsometry q r 0 0).symm).trans
      (realCliffordSplitIsometry p (q + r) 0 0).symm
  have he : eL = (IsometryEquiv.prodAssoc _ _ _).trans eR :=
    DFunLike.ext _ _ fun ⟨⟨u, v⟩, w⟩ ↦ funext fun i ↦ by
      have hrefl₁ : IsometryEquiv.refl (realCliffordForm r 0) w = w := rfl
      have hrefl₂ : IsometryEquiv.refl (realCliffordForm p 0) u = u := rfl
      simp only [eL, eR, IsometryEquiv.trans_apply, IsometryEquiv.prod_apply,
        IsometryEquiv.prodAssoc_apply, hrefl₁, hrefl₂]
      rw [realCliffordSplitIsometry_zero_symm_apply, realCliffordSplitIsometry_zero_symm_apply,
        realCliffordSplitIsometry_zero_symm_apply, realCliffordSplitIsometry_zero_symm_apply,
        realCliffordFormCongr_apply]
      simp [Fin.append_assoc]
  have hL : eL.spinGroupEquiv (spinGroupProd _ _ (spinGroupProd _ _ (x, y), z)) =
      (realCliffordFormCongr (Nat.add_assoc p q r) rfl).spinGroupEquiv
        (realCliffordSpinBlockSum (p + q) r (realCliffordSpinBlockSum p q (x, y), z)) := by
    dsimp only [eL]
    rw [IsometryEquiv.spinGroupEquiv_trans, IsometryEquiv.spinGroupEquiv_trans,
      MulEquiv.trans_apply, MulEquiv.trans_apply, spinGroupEquiv_prod_spinGroupProd,
      IsometryEquiv.spinGroupEquiv_refl, MulEquiv.refl_apply, ← realCliffordSpinBlockSum_apply,
      ← realCliffordSpinBlockSum_apply]
  have hR : eR.spinGroupEquiv (spinGroupProd _ _ (x, spinGroupProd _ _ (y, z))) =
      realCliffordSpinBlockSum p (q + r) (x, realCliffordSpinBlockSum q r (y, z)) := by
    dsimp only [eR]
    rw [IsometryEquiv.spinGroupEquiv_trans, MulEquiv.trans_apply,
      spinGroupEquiv_prod_spinGroupProd, IsometryEquiv.spinGroupEquiv_refl,
      MulEquiv.refl_apply, ← realCliffordSpinBlockSum_apply, ← realCliffordSpinBlockSum_apply]
  rw [← hL, ← hR, he, IsometryEquiv.spinGroupEquiv_trans, MulEquiv.trans_apply,
    prodAssoc_spinGroupEquiv_spinGroupProd]

/-- **Associativity coherence of `realCliffordSpecialOrthogonalBlockSum`**. -/
@[simp]
theorem realCliffordSpecialOrthogonalBlockSum_assoc (p q r : ℕ)
    (f : specialOrthogonalGroup (realCliffordForm p 0))
    (g : specialOrthogonalGroup (realCliffordForm q 0))
    (h : specialOrthogonalGroup (realCliffordForm r 0)) :
    (realCliffordFormCongr (Nat.add_assoc p q r) rfl).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum (p + q) r
          (realCliffordSpecialOrthogonalBlockSum p q (f, g), h)) =
      realCliffordSpecialOrthogonalBlockSum p (q + r)
        (f, realCliffordSpecialOrthogonalBlockSum q r (g, h)) := by
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) f
  obtain ⟨y, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) g
  obtain ⟨z, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm r 0) (posDef_realCliffordForm_zero r) h
  rw [← spinToSpecialOrthogonal_realCliffordSpinBlockSum p q (x, y),
    ← spinToSpecialOrthogonal_realCliffordSpinBlockSum (p + q) r
      (realCliffordSpinBlockSum p q (x, y), z),
    IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    realCliffordSpinBlockSum_assoc, spinToSpecialOrthogonal_realCliffordSpinBlockSum,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum]

/-- **Permutation coherence of `realCliffordSpinBlockSum`**: transporting along
`realCliffordBlockSwapIsometry p q` swaps the two factors of `realCliffordSpinBlockSum` in every
dimension, with no sign. -/
theorem realCliffordBlockSwapIsometry_spinGroupEquiv_blockSum (p q : ℕ)
    (x : realCliffordSpinGroupZero p × realCliffordSpinGroupZero q) :
    (realCliffordBlockSwapIsometry p q).spinGroupEquiv
        (realCliffordSpinBlockSum p q x) =
      realCliffordSpinBlockSum q p x.swap := by
  have he : (realCliffordSplitIsometry p q 0 0).symm.trans
      (realCliffordBlockSwapIsometry p q) =
      (IsometryEquiv.prodComm (realCliffordForm p 0) (realCliffordForm q 0)).trans
        (realCliffordSplitIsometry q p 0 0).symm :=
    DFunLike.ext _ _ fun ⟨u, v⟩ ↦ by
      simp only [IsometryEquiv.trans_apply]
      rw [realCliffordSplitIsometry_zero_symm_apply, realCliffordSplitIsometry_zero_symm_apply,
        realCliffordBlockSwapIsometry_append]
      rfl
  rw [realCliffordSpinBlockSum_apply, ← MulEquiv.trans_apply, ← IsometryEquiv.spinGroupEquiv_trans,
    he, IsometryEquiv.spinGroupEquiv_trans, MulEquiv.trans_apply,
    prodComm_spinGroupEquiv_spinGroupProd, realCliffordSpinBlockSum_apply]

/-- **Permutation coherence of `realCliffordSpecialOrthogonalBlockSum`**. -/
@[simp]
theorem realCliffordBlockSwapIsometry_specialOrthogonalGroupCongr_blockSum (p q : ℕ)
    (g : specialOrthogonalGroup (realCliffordForm p 0) ×
      specialOrthogonalGroup (realCliffordForm q 0)) :
    (realCliffordBlockSwapIsometry p q).specialOrthogonalGroupCongr
        (realCliffordSpecialOrthogonalBlockSum p q g) =
      realCliffordSpecialOrthogonalBlockSum q p g.swap := by
  obtain ⟨g₁, g₂⟩ := g
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm p 0) (posDef_realCliffordForm_zero p) g₁
  obtain ⟨y, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm q 0) (posDef_realCliffordForm_zero q) g₂
  rw [← spinToSpecialOrthogonal_realCliffordSpinBlockSum p q (x, y),
    IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    realCliffordBlockSwapIsometry_spinGroupEquiv_blockSum,
    spinToSpecialOrthogonal_realCliffordSpinBlockSum]
  rfl

end

end CliffordAlgebra
