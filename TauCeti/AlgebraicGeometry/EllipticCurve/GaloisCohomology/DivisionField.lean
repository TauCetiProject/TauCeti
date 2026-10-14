/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The `m`-division field of an elliptic curve

Let `W` be a Weierstrass curve over a field `K`, with separable closure `Kˢ` and absolute Galois
group `G_K`. The **`m`-division field** `K(E[m]) ⊆ Kˢ` is the field generated over `K` by the
coordinates of the points of `E(Kˢ)[m]` (Silverman VIII.1). An automorphism of `Kˢ` fixes it exactly
when it fixes every point of `E(Kˢ)[m]`, so its Galois group `G_{K(E[m])}` is the kernel of the
action of `G_K` on the coefficient module `E(Kˢ)[m]` (`WeierstrassCurve.TorsionCoeff`). That kernel
is normal, so `K(E[m])` is Galois over `K`, and for `W` elliptic and `m ≠ 0` the group `E(Kˢ)[m]`
is finite, so `K(E[m])` is a finite extension of `K`.

Over `K(E[m])` the Galois module `E[m]` becomes trivial, and Galois cohomology with coefficients
in `E[m]` is cohomology with constant coefficients. The inflation-restriction sequence

```text
0 ⟶ H¹(Gal(K(E[m])/K), E[m]) ⟶ H¹(G_K, E[m]) ⟶ H¹(G_{K(E[m])}, E[m])
```

has a finite group on the left, so restriction to `G_{K(E[m])}` has finite kernel
(`WeierstrassCurve.finite_ker_explicitRes1_divisionField`). This is how the finiteness of the
`m`-Selmer group of an elliptic curve over a number field (Silverman X.4.2) is reduced to the
finiteness of a group of homomorphisms out of `G_{K(E[m])}` unramified outside a finite set of
places.

## Main definitions

* `WeierstrassCurve.divisionField`: the `m`-division field `K(E[m])` inside `Kˢ`.

## Main results

* `WeierstrassCurve.divisionField_le_iff`: `K(E[m])` is the smallest intermediate field containing
  the coordinates of every point of `E(Kˢ)[m]`.
* `WeierstrassCurve.mem_fixingSubgroup_divisionField_iff`: an element of `G_K` fixes `K(E[m])`
  exactly when it fixes every point of `E(Kˢ)[m]`.
* `WeierstrassCurve.isGalois_divisionField`: `K(E[m])` is Galois over `K`.
* `WeierstrassCurve.finiteDimensional_divisionField`: for `W` elliptic and `m ≠ 0`, `K(E[m])` is
  finite over `K`.
* `WeierstrassCurve.finite_ker_explicitRes1_divisionField`: for `W` elliptic and `m ≠ 0`, the kernel
  of restriction `H¹(G_K, E[m]) → H¹(G_{K(E[m])}, E[m])` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (m : ℕ)

open scoped Classical in
/-- **The `m`-division field `K(E[m])`** of `W`: the subfield of the separable closure `Kˢ`
generated over `K` by the coordinates of the points of `W` over `Kˢ` killed by `m`. -/
def divisionField : IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K
    (Affine.Point.xCoord '' (AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m :
      Set (W⁄(SeparableClosure K)).toAffine.Point) ∪
      Affine.Point.yCoord '' (AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m :
      Set (W⁄(SeparableClosure K)).toAffine.Point))

open scoped Classical in
/-- `K(E[m])` is generated over `K` by the coordinates of the points of `E(Kˢ)[m]`. -/
theorem divisionField_def : W.divisionField m =
    IntermediateField.adjoin K
      (Affine.Point.xCoord '' (AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m :
        Set (W⁄(SeparableClosure K)).toAffine.Point) ∪
        Affine.Point.yCoord '' (AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m :
        Set (W⁄(SeparableClosure K)).toAffine.Point)) :=
  (rfl)

variable {W m}

open scoped Classical in
/-- **The universal property of `K(E[m])`**: it lies in an intermediate field `L` exactly when `L`
contains the coordinates of every point of `E(Kˢ)[m]`. -/
theorem divisionField_le_iff {L : IntermediateField K (SeparableClosure K)} :
    W.divisionField m ≤ L ↔
      ∀ P ∈ AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m,
        Affine.Point.xCoord P ∈ L ∧ Affine.Point.yCoord P ∈ L := by
  rw [divisionField_def, IntermediateField.adjoin_le_iff, Set.union_subset_iff,
    Set.image_subset_iff, Set.image_subset_iff]
  exact ⟨fun h P hP => ⟨h.1 hP, h.2 hP⟩, fun h => ⟨fun P hP => (h P hP).1, fun P hP => (h P hP).2⟩⟩

open scoped Classical in
/-- The `x`-coordinate of a point of `E(Kˢ)[m]` lies in `K(E[m])`. -/
theorem xCoord_mem_divisionField {P : (W⁄(SeparableClosure K)).toAffine.Point}
    (hP : P ∈ AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m) :
    Affine.Point.xCoord P ∈ W.divisionField m :=
  (divisionField_le_iff.1 le_rfl P hP).1

open scoped Classical in
/-- The `y`-coordinate of a point of `E(Kˢ)[m]` lies in `K(E[m])`. -/
theorem yCoord_mem_divisionField {P : (W⁄(SeparableClosure K)).toAffine.Point}
    (hP : P ∈ AddSubgroup.torsionBy (W⁄(SeparableClosure K)).toAffine.Point m) :
    Affine.Point.yCoord P ∈ W.divisionField m :=
  (divisionField_le_iff.1 le_rfl P hP).2

/-! ### The Galois group of `K(E[m])` -/

open scoped Classical in
/-- **The Galois group of `K(E[m])` is the kernel of the action on `E[m]`**: an element of `G_K`
fixes `K(E[m])` pointwise exactly when it fixes every point of `E(Kˢ)[m]`. -/
theorem mem_fixingSubgroup_divisionField_iff {σ : AbsoluteGaloisGroup K} :
    σ ∈ (W.divisionField m).fixingSubgroup ↔ ∀ P : W.TorsionCoeff m, σ • P = P := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  -- Both sides say that `σ` fixes the coordinates of every point of `E(Kˢ)[m]`: on the left
  -- because these generate `K(E[m])`, on the right through `pointCoeffEquiv`.
  simp only [divisionField_def, ← AlgEquiv.smul_def,
    IntermediateField.forall_mem_adjoin_smul_eq_self_iff, Set.forall_mem_union,
    Set.forall_mem_image, SetLike.mem_coe]
  refine ⟨fun h P => Subtype.ext ?_, fun h => ⟨fun P hP => ?_, fun P hP => ?_⟩⟩
  · -- `P` is the image of a point `Q` of `E(Kˢ)[m]`, whose coordinates `σ` fixes.
    set Q := (AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm P
    have hQ : W.pointCoeffEquiv Q = P := by simp [Q]
    rw [coe_smul_torsionCoeff, ← hQ, smul_pointCoeffEquiv,
      (Affine.Point.map_eq_self_iff σ.toAlgHom Q).2 ⟨h.1 Q.2, h.2 Q.2⟩]
  all_goals
    have hσ := congrArg Subtype.val (h (AddEquiv.torsionByCongr W.pointCoeffEquiv m ⟨P, hP⟩))
    rw [coe_smul_torsionCoeff, AddEquiv.torsionByCongr_apply_coe, smul_pointCoeffEquiv,
      W.pointCoeffEquiv.injective.eq_iff, Affine.Point.map_eq_self_iff] at hσ
  · exact hσ.1
  · exact hσ.2

variable (W m)

/-- **The Galois group of `K(E[m])` is normal in `G_K`**, being the kernel of the action of `G_K`
on `E(Kˢ)[m]`. -/
instance fixingSubgroup_divisionField_normal : (W.divisionField m).fixingSubgroup.Normal where
  conj_mem τ hτ σ := by
    rw [mem_fixingSubgroup_divisionField_iff] at hτ ⊢
    intro P
    rw [mul_smul, mul_smul, hτ, smul_inv_smul]

/-- **`K(E[m])` is Galois over `K`.** -/
instance isGalois_divisionField : IsGalois K (W.divisionField m) :=
  (InfiniteGalois.normal_iff_isGalois _).1 inferInstance

open scoped Classical in
/-- **`K(E[m])` is a finite extension of `K`** for `W` elliptic and `m ≠ 0`: it is generated by
the coordinates of the finitely many points of `E(Kˢ)[m]`, each algebraic over `K`. -/
instance finiteDimensional_divisionField [W.IsElliptic] [NeZero m] :
    FiniteDimensional K (W.divisionField m) := by
  have hfin := Set.finite_coe_iff.1
    ((W⁄(SeparableClosure K)).finite_torsionBy (Int.natCast_ne_zero.2 (NeZero.ne m)))
  have := ((hfin.image Affine.Point.xCoord).union (hfin.image Affine.Point.yCoord)).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/-! ### Restriction to the Galois group of `K(E[m])` -/

/-- **Restriction of `H¹(G_K, E[m])` to `G_{K(E[m])}` has finite kernel**, for `W` elliptic and
`m ≠ 0`. By inflation-restriction the kernel is the image of `H¹(Gal(K(E[m])/K), E[m])`, and both
the Galois group of the finite extension `K(E[m]) / K` and `E(Kˢ)[m]` are finite. -/
theorem finite_ker_explicitRes1_divisionField [W.IsElliptic] [NeZero m] :
    Finite (explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
      (W.divisionField m).fixingSubgroup).ker :=
  have : (W.divisionField m).fixingSubgroup.FiniteIndex :=
    ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩
  finite_ker_explicitRes1 _ _ _

end WeierstrassCurve
