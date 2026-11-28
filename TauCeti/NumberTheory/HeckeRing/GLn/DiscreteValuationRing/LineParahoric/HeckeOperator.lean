/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiscreteValuationRing.LineParahoric.Basic
public import TauCeti.RepresentationTheory.HeckeOperator

/-!
# The Hecke relation for the stabiliser of a line

Let `R` be a discrete valuation ring with uniformizer `ϖ` and residue field with `q` elements, `K`
a field containing `R` in which `ϖ` maps to `π`, `ι` a finite index type with `n ≥ 2` elements,
`i ∈ ι`, `J ⊆ GL_ι(R)` the stabiliser of the line `k eᵢ` modulo the maximal ideal
(`HeckeRing.GLn.lineParahoric`) and `t = diag(1, …, π, …, 1)` with `π` in position `i`. For a
representation `ρ` of `GL_ι(K)` on a module over a commutative semiring, the double coset operators
`T⁺ = [J t J]` and `T⁻ = [J t⁻¹ J]` act on the `J`-invariant vectors. They satisfy the
**quadratic relation**

`T⁺ T⁻ y = q^{n-2} (y + (q - 1) ∑_{h ∈ GL_ι(R) / J} ρ(h) y)`

(`Representation.doubleCosetOperator_doubleCosetOperator_inv_lineParahoric`): composing
Hecke operators is convolving their functions, and `1_{J t J} ⋆ 1_{J t⁻¹ J}` is
`q^{n-2} (1_J + (q - 1) 1_{GL_ι(R)})` by the count of cosets
`HeckeRing.GLn.sum_indicator_doubleCoset_inv_lineParahoric`. Over a field in which the index
`[GL_ι(R) : J]` is nonzero, for instance of characteristic zero, it reads
`T⁺ T⁻ y = q^{n-2} (y + (qⁿ - 1) e y)` with `e` the mean over `GL_ι(R) / J`, the projector onto the
vectors fixed by `GL_ι(R)`
(`Representation.doubleCosetOperator_doubleCosetOperator_inv_lineParahoric_eq_mean`).

For a `ρ`-invariant sesquilinear form, in particular for the inner product of a unitary
representation, `T⁺` and `T⁻` are adjoint on the `J`-invariant vectors
(`Representation.sesqForm_doubleCosetOperator_lineParahoric_left_eq_right_inv`), since `J t J`
and `J t⁻¹ J` consist of the same number of left cosets of `J`.

## Main results

* `Representation.doubleCosetOperator_doubleCosetOperator_inv_lineParahoric`,
  `Representation.doubleCosetOperator_doubleCosetOperator_inv_lineParahoric_eq_mean`: the
  quadratic relation for `T⁺ T⁻`.
* `Representation.sesqForm_doubleCosetOperator_lineParahoric_left_eq_right_inv`: `T⁺` and `T⁻`
  are adjoint.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), ch. 3, for Hecke operators of double cosets.

The statements follow grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic PBC), `Lib/Adelic/TraceFormula/LineStabiliser.lean` (`New.lineRaise_lineLower`,
`New.inner_lineRaise`).
-/

public section

open IsLocalRing TauCeti Function HeckeRing.GLn
open scoped Pointwise

namespace Representation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] {ϖ : R} {π : Kˣ} {i : ι}

section CommSemiring

variable {A W : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W]
  (ρ : Representation A (GL ι K) W)

/-- **The quadratic relation for the stabiliser of a line.** Let `J` be the stabiliser of the line
`k eᵢ` modulo the maximal ideal, `t = diag(1, …, π, …, 1)` with `π` in position `i`, `q` the size
of the residue field and `n = |ι| ≥ 2`. On `J`-invariant vectors the double coset operators
`T⁺ = [J t J]` and `T⁻ = [J t⁻¹ J]` satisfy
`T⁺ T⁻ y = q^{n-2} (y + (q - 1) ∑_{h ∈ GL_ι(R) / J} ρ(h) y)`. -/
theorem doubleCosetOperator_doubleCosetOperator_inv_lineParahoric [Finite (ResidueField R)]
    (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) (hn : 2 ≤ Fintype.card ι) {y : W}
    (hy : y ∈ weightSpace (ρ.comp (lineParahoric R K i).subtype) 1) :
    ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π))
        (ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π))⁻¹ y) =
      Nat.card (ResidueField R) ^ (Fintype.card ι - 2) •
        (y + (Nat.card (ResidueField R) - 1) •
          ∑ᶠ h : integralGL R K ι ⧸ (lineParahoric R K i).subgroupOf (integralGL R K ι),
            ρ h.out y) := by
  have := isFiniteRelIndex_conjAct_lineParahoric (i := i) hϖ hπ
  have := isFiniteRelIndex_conjAct_inv_lineParahoric (i := i) hϖ hπ
  have := Fintype.ofFinite (DoubleCoset.DecompQuotient (lineParahoric R K i)
    (lineParahoric R K i) (diagGL (Pi.mulSingle i π)))
  have := isFiniteRelIndex_lineParahoric (i := i) hϖ hπ
  set J := lineParahoric R K i
  set K₀ := integralGL R K ι
  set a : A := ((Nat.card (ResidueField R) ^ (Fintype.card ι - 2) : ℕ) : A)
  set b : A := ((Nat.card (ResidueField R) ^ (Fintype.card ι - 2) *
    (Nat.card (ResidueField R) - 1) : ℕ) : A)
  -- by the count of cosets, `T⁺ T⁻` is the Hecke operator of `a 1_J + b 1_{GL_ι(R)}`
  have hfun : (fun x ↦ ∑ h : DoubleCoset.DecompQuotient J J (diagGL (Pi.mulSingle i π)),
      (DoubleCoset.doubleCoset (diagGL (Pi.mulSingle i π))⁻¹ (J : Set (GL ι K)) J).indicator
        (1 : GL ι K → A) (((h.out : GL ι K) * diagGL (Pi.mulSingle i π))⁻¹ * x)) =
      fun x ↦ ∑ j ∈ Finset.univ, ![a, b] j *
        ![(J : Set (GL ι K)).indicator 1, (K₀ : Set (GL ι K)).indicator 1] j x := by
    funext x
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact sum_indicator_doubleCoset_inv_lineParahoric hϖ hπ hn
      (Subgroup.isCosetSystem_out_mul J J _) x
  have hfin : ∀ j ∈ (Finset.univ : Finset (Fin 2)), (support fun r : GL ι K ⧸ J ↦
      (![(J : Set (GL ι K)).indicator 1, (K₀ : Set (GL ι K)).indicator 1] j : GL ι K → A)
        r.out).Finite :=
    Fin.forall_fin_two.mpr ⟨fun _ ↦ QuotientGroup.finite_support_indicator_of_le le_rfl,
      fun _ ↦ QuotientGroup.finite_support_indicator_of_le lineParahoric_le_integralGL⟩
  rw [doubleCosetOperator_doubleCosetOperator_apply (Subgroup.isCosetSystem_out_mul J J _) hy, hfun,
    heckeOperator_sum _ _ _ hfin, Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [heckeOperator_indicator_self_apply hy,
    heckeOperator_indicator_apply lineParahoric_le_integralGL hy, Nat.cast_smul_eq_nsmul,
    Nat.cast_smul_eq_nsmul, smul_add, mul_smul]

/-- **Adjointness of the Hecke operators of the stabiliser of a line.** For a `ρ`-invariant
sesquilinear form `B`, in particular for the inner product of a unitary representation, the
operators `T⁺ = [J t J]` and `T⁻ = [J t⁻¹ J]` are adjoint on the `J`-invariant vectors:
`B (T⁺ x) y = B x (T⁻ y)`. -/
theorem sesqForm_doubleCosetOperator_lineParahoric_left_eq_right_inv [StarRing A]
    {B : W →ₗ⋆[A] W →ₗ[A] A} (hB : ρ.IsInvariantSesqForm B) (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {x y : W}
    (hx : x ∈ weightSpace (ρ.comp (lineParahoric R K i).subtype) 1)
    (hy : y ∈ weightSpace (ρ.comp (lineParahoric R K i).subtype) 1) :
    B (ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π)) x) y =
      B x (ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π))⁻¹ y) :=
  ρ.sesqForm_doubleCosetOperator_left_eq_right_inv hB
    (relIndex_conjAct_inv_lineParahoric_eq hϖ hπ) hx hy

end CommSemiring

/-- **The quadratic relation with the spherical mean.** Over a field `𝕜` in which the index
`[GL_ι(R) : J]` is nonzero, for instance of characteristic zero,
let `e y = [GL_ι(R) : J]⁻¹ ∑_{h ∈ GL_ι(R) / J} ρ(h) y` be the mean over `GL_ι(R)` of a
`J`-invariant vector `y`, the projector onto the vectors fixed by `GL_ι(R)`; for a smooth
representation it is `Representation.smoothAverage` (`Representation.smoothAverage_apply_of_le`).
Then `T⁺ T⁻ y = q^{n-2} (y + (qⁿ - 1) e y)`. -/
theorem doubleCosetOperator_doubleCosetOperator_inv_lineParahoric_eq_mean {𝕜 V : Type*}
    [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (ρ : Representation 𝕜 (GL ι K) V)
    [Finite (ResidueField R)] (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (hN : ((lineParahoric R K i).relIndex (integralGL R K ι) : 𝕜) ≠ 0) (hn : 2 ≤ Fintype.card ι)
    {y : V}
    (hy : y ∈ weightSpace (ρ.comp (lineParahoric R K i).subtype) 1) :
    ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π))
        (ρ.doubleCosetOperator (lineParahoric R K i) (diagGL (Pi.mulSingle i π))⁻¹ y) =
      Nat.card (ResidueField R) ^ (Fintype.card ι - 2) •
        (y + (Nat.card (ResidueField R) ^ Fintype.card ι - 1) •
          (((lineParahoric R K i).relIndex (integralGL R K ι) : 𝕜)⁻¹ •
            ∑ᶠ h : integralGL R K ι ⧸ (lineParahoric R K i).subgroupOf (integralGL R K ι),
              ρ h.out y)) := by
  rw [ρ.doubleCosetOperator_doubleCosetOperator_inv_lineParahoric hϖ hπ hn hy,
    ← relIndex_lineParahoric_mul hϖ hπ, mul_comm, mul_smul,
    ← Nat.cast_smul_eq_nsmul 𝕜 ((lineParahoric R K i).relIndex _), smul_inv_smul₀ hN]

end Representation
