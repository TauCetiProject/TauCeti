/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel

/-!
# The scalar subgroup of the general linear group

The scalar matrices `t ↦ t • 1` form the homomorphism `𝔾ₘ → GLₙ` given by the weight
cocharacter with every weight equal to `1`, `TauCeti.GeneralLinear.weightCocharacter (fun _ ↦ 1)`.
On points it is `TauCeti.GeneralLinear.scalarTorusPoints`. The kernel of its comorphism cuts out the
scheme-theoretic image of `𝔾ₘ`, the scalar subgroup of `GLₙ`: a copy of `𝔾ₘ` for `0 < n`, trivial
for `n = 0`.

Over a field the scalar subgroup is the center: a coordinate function lies in
`TauCeti.CommHopfAlgCat.centerDefiningIdeal` exactly when it vanishes on scalar matrices. One
inclusion is centrality of scalar points, read at the universal point of `𝔾ₘ`; the other is that
the universally central quotient point of the center is a scalar point
(`TauCeti.GeneralLinear.mem_centerPointsSubgroup_iff_exists_scalarTorusPoints`).

## Main declarations

* `TauCeti.GeneralLinear.weightCocharacterPoints_const_one`: the weight cocharacter with all
  weights `1` is the scalar-matrix map on points.
* `TauCeti.GeneralLinear.mem_centerDefiningIdeal_iff`: a coordinate function lies in the center
  ideal of `GLₙ` exactly when it vanishes on scalar matrices.
* `TauCeti.GeneralLinear.ker_weightCocharacter_const_one`: the center ideal of `GLₙ` is the kernel
  of the scalar cocharacter, so the center is the scalar subgroup.
* `TauCeti.GeneralLinear.powCocharacter_weightCocharacter`: the `m`-th power of the weight
  cocharacter with weights `w` has weights `w i * m`; so `t ↦ t ^ m • 1` is the `m`-th power of
  `t ↦ t • 1`.
* `TauCeti.GeneralLinear.ker_weightCocharacter_const`: for `m ≠ 0`, the kernel of
  `t ↦ t ^ m • 1` is still the center ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 2.4 and §21.
-/
public section

open CategoryTheory WithConv
open scoped LaurentPolynomial

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R] (n : ℕ)

/-- The weight cocharacter with every weight equal to `1` is the scalar-matrix map on points. -/
theorem weightCocharacterPoints_const_one {A : Type w} [CommRing A] [Algebra R A]
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    weightCocharacterPoints (N := n) (fun _ ↦ 1) f = scalarTorusPoints n f := by
  apply (pointsMulEquiv (R := R) (A := A) n).injective
  rw [pointsMulEquiv_weightCocharacterPoints, pointsMulEquiv_scalarTorusPoints]
  ext i j
  simp [Matrix.diagonal_apply]

/-- The `m`-th power `t ↦ λ(t ^ m)` of the weight cocharacter with weights `w` is the weight
cocharacter with weights `w i * m`. -/
theorem powCocharacter_weightCocharacter (w : Fin n → ℤ) (m : ℤ) :
    (weightCocharacter (R := R) w).powCocharacter m = weightCocharacter (fun i ↦ w i * m) := by
  let σ : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] :=
    AddMonoidAlgebra.mapDomainAlgHom R R (AddMonoidHom.mulRight m)
  let p : WithConv (R[T;T⁻¹] →ₐ[R] R[T;T⁻¹]) := toConv (AlgHom.id R R[T;T⁻¹])
  -- Both sides agree at the universal point `T` of `𝔾ₘ`: each is the diagonal point with
  -- entries `T ^ (w i * m)`.
  have hσ : MultiplicativeGroup.pointsMulEquiv (toConv σ) =
      MultiplicativeGroup.pointsMulEquiv p ^ m := by
    refine Units.ext ?_
    rw [MultiplicativeGroup.pointsMulEquiv_apply, laurentEvalEquiv_symm_apply,
      ofConv_toConv, ← (AlgHom.id R R[T;T⁻¹]).apply_laurentPolynomial_T_of_apply_T_one
        (u := MultiplicativeGroup.pointsMulEquiv p) (by simp [p])]
    -- `T n` is `single n 1`, on which `mapDomainAlgHom` acts through its domain map.
    rw [AlgHom.id_apply, LaurentPolynomial.T, LaurentPolynomial.T,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidHom.mulRight_apply, one_mul]
  have hpts : BialgHom.mapDomain (weightCocharacter (R := R) w) (toConv σ) =
      BialgHom.mapDomain (weightCocharacter (R := R) (N := n) (fun i ↦ w i * m)) p := by
    rw [mapDomain_weightCocharacter, mapDomain_weightCocharacter]
    apply (pointsMulEquiv (R := R) (A := R[T;T⁻¹]) n).injective
    rw [pointsMulEquiv_weightCocharacterPoints, pointsMulEquiv_weightCocharacterPoints, hσ]
    congr 1
    funext i
    rw [weightDiagonalUnits_apply, weightDiagonalUnits_apply, ← zpow_mul, mul_comm]
  refine BialgHom.ext fun x ↦ ?_
  have hx := congrArg (fun q ↦ q.ofConv x) hpts
  simp only [BialgHom.mapDomain_apply_apply, p, σ, AlgHom.id_apply,
    AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidHom.coe_mulRight] at hx
  rw [BialgHom.powCocharacter_apply]
  exact hx

section Field

variable (k : Type u) [Field k]

/-- Scalar matrices are central: a coordinate function in the center ideal vanishes on scalar
matrices. -/
private theorem centerDefiningIdeal_le_ker {x : coordinateHopfAlgebra k n}
    (hx : x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) :
    weightCocharacter (R := k) (N := n) (fun _ ↦ 1) x = 0 := by
  let p : WithConv (k[T;T⁻¹] →ₐ[k] k[T;T⁻¹]) := toConv (AlgHom.id k k[T;T⁻¹])
  have hp := scalarTorusPoints_mem_centerPointsSubgroup n p
  rw [← weightCocharacterPoints_const_one, ← mapDomain_weightCocharacter,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hp
  simpa only [BialgHom.mapDomain_apply_apply, p, ofConv_toConv, AlgHom.id_apply] using hp x hx

/-- The center of `GLₙ` consists of scalars: a coordinate function vanishing on scalar matrices
lies in the center ideal. -/
private theorem mem_centerDefiningIdeal_of_ker {x : coordinateHopfAlgebra k n}
    (hx : weightCocharacter (R := k) (N := n) (fun _ ↦ 1) x = 0) :
    x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  let I := CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)
  let A : CommAlgCat.{u} k := CommAlgCat.of k (coordinateHopfAlgebra k n ⧸ I.toIdeal)
  let q : WithConv (coordinateHopfAlgebra k n →ₐ[k] A) :=
    toConv (Ideal.Quotient.mkₐ k I.toIdeal)
  have hq : q ∈ CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hy)
  obtain ⟨f, hf⟩ := (mem_centerPointsSubgroup_iff_exists_scalarTorusPoints n A q).mp hq
  rw [← weightCocharacterPoints_const_one, ← mapDomain_weightCocharacter] at hf
  have hqx : q.ofConv x = 0 := by
    rw [← hf, BialgHom.mapDomain_apply_apply, hx, map_zero]
  exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hqx)

/-- **The center of `GLₙ` is its scalar subgroup**: a coordinate function lies in the center
ideal exactly when it vanishes on scalar matrices. -/
theorem mem_centerDefiningIdeal_iff {x : coordinateHopfAlgebra k n} :
    x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) ↔
      weightCocharacter (R := k) (N := n) (fun _ ↦ 1) x = 0 :=
  ⟨centerDefiningIdeal_le_ker n k, mem_centerDefiningIdeal_of_ker n k⟩

/-- **The center of `GLₙ` is its scalar subgroup**: the center ideal is the kernel of the
cocharacter `t ↦ t • 1`. -/
theorem ker_weightCocharacter_const_one :
    HopfIdeal.ker (weightCocharacter (R := k) (N := n) (fun _ ↦ 1)) =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  ext x
  rw [HopfIdeal.mem_ker, mem_centerDefiningIdeal_iff]

/-- For `m ≠ 0`, the cocharacter `t ↦ t ^ m • 1` has the same kernel as `t ↦ t • 1`: the center
ideal of `GLₙ`. Scheme-theoretically its image is the whole scalar subgroup, not a finite
subgroup `μ_m`. -/
theorem ker_weightCocharacter_const {m : ℤ} (hm : m ≠ 0) :
    HopfIdeal.ker (weightCocharacter (R := k) (N := n) (fun _ ↦ m)) =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  have hpow := powCocharacter_weightCocharacter (R := k) n (fun _ ↦ 1) m
  simp only [one_mul] at hpow
  ext x
  rw [HopfIdeal.mem_ker, mem_centerDefiningIdeal_iff, ← hpow, BialgHom.powCocharacter_apply,
    ← AddMonoidAlgebra.mapDomain_zero (· * m)]
  exact (AddMonoidAlgebra.mapDomain_injective (mul_left_injective₀ hm)).eq_iff

end Field

end TauCeti.GeneralLinear
