/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Geometry.ScatteringDiagram.SlabAlgebra.Basic
public import TauCeti.LinearAlgebra.GradedCorrespondence.Hom
public import TauCeti.LinearAlgebra.GradedCorrespondence.RestrictScalars
import TauCeti.Algebra.MonoidAlgebra.Grading

/-!
# Chamber Laurent maps and graded correspondences for slab algebras

Across a codimension-one slab with coefficient algebra `SlabAlgebra B q = B[X, Y] / (X Y - q)`,
the two adjacent chambers carry Laurent polynomial algebras `B[x, x⁻¹]` and `B[y, y⁻¹]`
(both represented by `B[T;T⁻¹]`), linked to the slab algebra by the `B`-algebra homomorphisms

* `SlabAlgebra.leftChamberMap q`: `X ↦ T 1`, `Y ↦ C q * T (-1)`,
* `SlabAlgebra.rightChamberMap q`: `X ↦ C q * T (-1)`, `Y ↦ T 1`.

Using the normal-form basis `SlabAlgebra.slabBasis q`, we compute the Laurent expansions of
every slab element in both chambers:

* `leftChamberMap q (Z q n) = C (q ^ n.toNat) * T (-n)`,
* `rightChamberMap q (Z q n) = C (q ^ (-n).toNat) * T n`,

from which the nonnegative Laurent coefficients read off the negative and nonnegative coordinates
of `slabBasis q` directly. Consequently:

* the product map `(leftChamberMap q, rightChamberMap q)` is **jointly injective** for arbitrary
  commutative rings `B` and arbitrary `q : B` (`SlabAlgebra.chamberProd_injective`);
* each chamber map is individually injective whenever `q` is regular
  (`SlabAlgebra.leftChamberMap_injective_of_isRegular`,
  `SlabAlgebra.rightChamberMap_injective_of_isRegular`);
* choosing incoming degree sets `I, J ⊆ Set.Ici (0 : ℤ)` produces a `B`-linear
  `GradedCorrespondence` (`SlabAlgebra.slabCorrespondence`) with multiplicative lifts and
  functorial morphisms (`SlabAlgebra.slabCorrespondenceHom`) along scalar/quotient homomorphisms
  `φ : B →ₐ[R] B'` sending `q` to `q'`.

Specializing `B = S[Λ]` for a tangential monoid or lattice `Λ` and identifying `(S[Λ])[T;T⁻¹]`
with `S[ℤ × Λ]` via `(AddMonoidAlgebra.curryAlgEquiv S).symm` yields the full-exponent graded
correspondence `SlabAlgebra.tangentialSlabCorrespondence`, explicit homogeneous transfer
coefficients in terms of the tangential expansion of `q^a`, and naturality in `(S, q)`.

## Main definitions and results

* `TauCeti.SlabAlgebra.leftChamberMap`, `TauCeti.SlabAlgebra.rightChamberMap`: the left and right
  chamber Laurent homomorphisms `SlabAlgebra B q →ₐ[B] B[T;T⁻¹]`.
* `TauCeti.SlabAlgebra.coeff_leftChamberMap`, `TauCeti.SlabAlgebra.coeff_rightChamberMap`,
  `TauCeti.SlabAlgebra.chamberProd_injective`: Laurent coefficient formulas and joint injectivity.
* `TauCeti.SlabAlgebra.slabCorrespondence`, `TauCeti.SlabAlgebra.slabCorrespondenceHom`: the
  `B`-linear graded correspondence across a slab and its functoriality.
* `TauCeti.SlabAlgebra.leftTangentialMap`, `TauCeti.SlabAlgebra.rightTangentialMap`,
  `TauCeti.SlabAlgebra.mapAlgHom_comp_leftTangentialMap`,
  `TauCeti.SlabAlgebra.mapAlgHom_comp_rightTangentialMap`,
  `TauCeti.SlabAlgebra.tangentialSlabCorrespondence`,
  `TauCeti.SlabAlgebra.tangentialSlabCorrespondence_transfer_single`: full-exponent chamber maps,
  their naturality, graded correspondence on `S[ℤ × Λ]`, and tangential expansion of homogeneous
  transfers.

## References

* M. Gross and B. Siebert, *An Invitation to Toric Degenerations*, §2.3, arXiv:0808.2749v2.
* M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*, Definitions 3.1–3.3, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace TauCeti

namespace SlabAlgebra

open LaurentPolynomial (C T T_pow T_add T_zero C_eq_algebraMap single_eq_C_mul_T)
open scoped LaurentPolynomial

variable {R B B' : Type*} [CommRing B] [CommRing B']

/-! ### Left and right chamber Laurent homomorphisms -/

/-- The left chamber homomorphism `SlabAlgebra B q →ₐ[B] B[T;T⁻¹]` sending `X ↦ T 1` and
`Y ↦ C q * T (-1)`. -/
def leftChamberMap (q : B) : SlabAlgebra B q →ₐ[B] B[T;T⁻¹] :=
  lift q (T 1) (C q * T (-1)) (by
    rw [mul_left_comm, ← T_add, add_neg_cancel, T_zero, mul_one, C_eq_algebraMap])

/-- The right chamber homomorphism `SlabAlgebra B q →ₐ[B] B[T;T⁻¹]` sending `X ↦ C q * T (-1)`
and `Y ↦ T 1`. -/
def rightChamberMap (q : B) : SlabAlgebra B q →ₐ[B] B[T;T⁻¹] :=
  lift q (C q * T (-1)) (T 1) (by
    rw [mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one, C_eq_algebraMap])

@[simp] theorem leftChamberMap_X (q : B) : leftChamberMap q (X q) = T 1 := lift_X _ _ _ _
@[simp] theorem leftChamberMap_Y (q : B) : leftChamberMap q (Y q) = C q * T (-1) := lift_Y _ _ _ _
@[simp] theorem rightChamberMap_X (q : B) : rightChamberMap q (X q) = C q * T (-1) := lift_X _ _ _ _
@[simp] theorem rightChamberMap_Y (q : B) : rightChamberMap q (Y q) = T 1 := lift_Y _ _ _ _

/-- In the left chamber, the normal-form basis element `Z q n` maps to
`C (q ^ n.toNat) * T (-n)`. -/
@[simp] theorem leftChamberMap_Z (q : B) (n : ℤ) :
    leftChamberMap q (Z q n) = C (q ^ n.toNat) * T (-n) := by
  rw [leftChamberMap, lift_Z]
  split_ifs with hn
  · rw [T_pow, mul_one, Int.ofNat_natAbs_of_nonpos hn.le, Int.toNat_of_nonpos hn.le,
      pow_zero, map_one, one_mul]
  · rw [mul_pow, ← map_pow, T_pow, mul_neg_one, Int.natAbs_of_nonneg (not_lt.mp hn)]
    congr 3; omega

/-- In the right chamber, the normal-form basis element `Z q n` maps to
`C (q ^ (-n).toNat) * T n`. -/
@[simp] theorem rightChamberMap_Z (q : B) (n : ℤ) :
    rightChamberMap q (Z q n) = C (q ^ (-n).toNat) * T n := by
  rw [rightChamberMap, lift_Z]
  split_ifs with hn
  · rw [mul_pow, ← map_pow, T_pow, mul_neg_one, Int.ofNat_natAbs_of_nonpos hn.le, neg_neg]
    congr 3; omega
  · rw [T_pow, mul_one, Int.natAbs_of_nonneg (not_lt.mp hn),
      Int.toNat_of_nonpos (by omega), pow_zero, map_one, one_mul]

/-- The `k`-th Laurent coefficient of `leftChamberMap q u` is the `(-k)`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_leftChamberMap (q : B) (u : SlabAlgebra B q) (k : ℤ) :
    (leftChamberMap q u).coeff k = ((slabBasis q).repr u (-k)) * q ^ (-k).toNat := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul_Z b m =>
    rw [map_smul, map_smul, leftChamberMap_Z, slabBasis_repr_Z, ← single_eq_C_mul_T,
      AddMonoidAlgebra.smul_single, smul_eq_mul, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne m (-k) with rfl | h <;> simp [neg_eq_iff_eq_neg, *]

/-- The `k`-th Laurent coefficient of `rightChamberMap q u` is the `k`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_rightChamberMap (q : B) (u : SlabAlgebra B q) (k : ℤ) :
    (rightChamberMap q u).coeff k = ((slabBasis q).repr u k) * q ^ (-k).toNat := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul_Z b m =>
    rw [map_smul, map_smul, rightChamberMap_Z, slabBasis_repr_Z, ← single_eq_C_mul_T,
      AddMonoidAlgebra.smul_single, smul_eq_mul, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne m k with rfl | h <;> simp [*]

@[simp] theorem coeff_leftChamberMap_natCast (q : B) (u : SlabAlgebra B q) (a : ℕ) :
    (leftChamberMap q u).coeff (a : ℤ) = (slabBasis q).repr u (-(a : ℤ)) := by
  rw [coeff_leftChamberMap, Int.toNat_of_nonpos (by omega), pow_zero, mul_one]

@[simp] theorem coeff_rightChamberMap_natCast (q : B) (u : SlabAlgebra B q) (a : ℕ) :
    (rightChamberMap q u).coeff (a : ℤ) = (slabBasis q).repr u (a : ℤ) := by
  rw [coeff_rightChamberMap, Int.toNat_of_nonpos (by omega), pow_zero, mul_one]

/-- **Joint injectivity of the chamber maps**: for every commutative ring `B` and every `q : B`,
an element of `SlabAlgebra B q` is uniquely determined by its left and right chamber Laurent
expansions. -/
theorem chamberProd_injective (q : B) :
    Function.Injective ((leftChamberMap q).toLinearMap.prod (rightChamberMap q).toLinearMap) := by
  intro u v huv
  have hL : leftChamberMap q u = leftChamberMap q v := congrArg Prod.fst huv
  have hR : rightChamberMap q u = rightChamberMap q v := congrArg Prod.snd huv
  apply (slabBasis q).repr.injective
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [Int.eq_neg_natAbs_of_nonpos hn.le, ← coeff_leftChamberMap_natCast,
      ← coeff_leftChamberMap_natCast, hL]
  · rw [← Int.natAbs_of_nonneg hn, ← coeff_rightChamberMap_natCast,
      ← coeff_rightChamberMap_natCast, hR]

/-- When `q` is regular in `B`, `leftChamberMap q` is individually injective. -/
theorem leftChamberMap_injective_of_isRegular {q : B} (hq : IsRegular q) :
    Function.Injective (leftChamberMap q) := fun _ _ huv =>
  (slabBasis q).repr.injective <| Finsupp.ext fun n => (hq.pow n.toNat).right <| by
    simpa [coeff_leftChamberMap] using congrArg (fun p : B[T;T⁻¹] => p.coeff (-n)) huv

/-- When `q` is regular in `B`, `rightChamberMap q` is individually injective. -/
theorem rightChamberMap_injective_of_isRegular {q : B} (hq : IsRegular q) :
    Function.Injective (rightChamberMap q) := fun _ _ huv =>
  (slabBasis q).repr.injective <| Finsupp.ext fun n => (hq.pow (-n).toNat).right <| by
    simpa [coeff_rightChamberMap] using congrArg (fun p : B[T;T⁻¹] => p.coeff n) huv

/-- Naturality of `leftChamberMap` along a coefficient `R`-algebra homomorphism `φ : B →ₐ[R] B'`
that sends `q` to `q'`. -/
theorem mapAlgHom_comp_leftChamberMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (AddMonoidAlgebra.mapAlgHom ℤ φ).comp ((leftChamberMap q).restrictScalars R) =
      ((leftChamberMap q').restrictScalars R).comp (mapAlgHom φ hq) :=
  algHom_ext_of_algebra (fun _ => by simp [← C_eq_algebraMap]) (by simp) (by simp [hq])

/-- Naturality of `rightChamberMap` along a coefficient `R`-algebra homomorphism `φ : B →ₐ[R] B'`
that sends `q` to `q'`. -/
theorem mapAlgHom_comp_rightChamberMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (AddMonoidAlgebra.mapAlgHom ℤ φ).comp ((rightChamberMap q).restrictScalars R) =
      ((rightChamberMap q').restrictScalars R).comp (mapAlgHom φ hq) :=
  algHom_ext_of_algebra (fun _ => by simp [← C_eq_algebraMap]) (by simp [hq]) (by simp)

/-! ### `B`-linear graded correspondence across a slab -/

/-- Auxiliary `B`-linear map reading the `k`-th Laurent coefficient and scaling a slab element. -/
private def coeffLiftLinearMap (q : B) (k : ℤ) (z : SlabAlgebra B q) :
    AddMonoidAlgebra.grade B k →ₗ[B] SlabAlgebra B q :=
  ((LinearMap.smulRight (1 : B →ₗ[B] B) z).comp
    ((Finsupp.lapply k).comp (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap)).comp
    (AddMonoidAlgebra.grade B k).subtype

@[simp] private theorem coeffLiftLinearMap_apply (q : B) (k : ℤ) (z : SlabAlgebra B q)
    (a : AddMonoidAlgebra.grade B k) :
    coeffLiftLinearMap q k z a = ((a : B[T;T⁻¹]).coeff k) • z := (rfl)

/-- The `B`-linear `GradedCorrespondence` across `SlabAlgebra B q` for incoming degree sets
`I, J ⊆ Set.Ici (0 : ℤ)` (such as `Set.Ici 0` for all nonnegative incoming powers or `Set.Ioi 0`
for strictly transverse incoming powers):
* on `i ∈ I` (`i ≥ 0`), `C b * T i` lifts from the left to `b • X q ^ i.natAbs = b • Z q (-i)`;
* on `j ∈ J` (`j ≥ 0`), `C b * T j` lifts from the right to `b • Y q ^ j.natAbs = b • Z q j`. -/
def slabCorrespondence (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    GradedCorrespondence (B := SlabAlgebra B q)
      (AddMonoidAlgebra.grade B) (AddMonoidAlgebra.grade B) I J where
  left := (leftChamberMap q).toLinearMap
  right := (rightChamberMap q).toLinearMap
  liftLeft i := coeffLiftLinearMap q (i : ℤ) (Z q (-(i : ℤ)))
  liftRight j := coeffLiftLinearMap q (j : ℤ) (Z q (j : ℤ))
  left_liftLeft i := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coeffLiftLinearMap_apply,
      Submodule.subtype_apply, map_smul, leftChamberMap_Z, neg_neg,
      Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.property)), pow_zero, map_one, one_mul,
      Algebra.smul_def, ← C_eq_algebraMap, ← single_eq_C_mul_T]
    exact AddMonoidAlgebra.single_coeff_of_mem_grade a.property
  right_liftRight j := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coeffLiftLinearMap_apply,
      Submodule.subtype_apply, map_smul, rightChamberMap_Z,
      Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.property)), pow_zero, map_one, one_mul,
      Algebra.smul_def, ← C_eq_algebraMap, ← single_eq_C_mul_T]
    exact AddMonoidAlgebra.single_coeff_of_mem_grade a.property

@[simp] theorem slabCorrespondence_left (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    (slabCorrespondence q hI hJ).left = (leftChamberMap q).toLinearMap := (rfl)

@[simp] theorem slabCorrespondence_right (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    (slabCorrespondence q hI hJ).right = (rightChamberMap q).toLinearMap := (rfl)

@[simp] theorem slabCorrespondence_liftLeft_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (i : I)
    (a : AddMonoidAlgebra.grade B (i : ℤ)) :
    (slabCorrespondence q hI hJ).liftLeft i a =
      ((a : B[T;T⁻¹]).coeff (i : ℤ)) • X q ^ (i : ℤ).natAbs := by
  have hZ : Z q (-(i : ℤ)) = X q ^ (i : ℤ).natAbs := by
    rw [← Int.natAbs_of_nonneg (hI i.property), Z_neg_natCast, Int.natAbs_natCast]
  rw [slabCorrespondence, coeffLiftLinearMap_apply, hZ]

@[simp] theorem slabCorrespondence_liftRight_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (j : J)
    (a : AddMonoidAlgebra.grade B (j : ℤ)) :
    (slabCorrespondence q hI hJ).liftRight j a =
      ((a : B[T;T⁻¹]).coeff (j : ℤ)) • Y q ^ (j : ℤ).natAbs := by
  rw [slabCorrespondence, coeffLiftLinearMap_apply, Z_of_nonneg q (hJ j.property)]

/-- The two chamber legs of `slabCorrespondence` are jointly injective for arbitrary `q`. -/
theorem slabCorrespondence_injective (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    Function.Injective
      ((slabCorrespondence q hI hJ).left.prod (slabCorrespondence q hI hJ).right) :=
  chamberProd_injective q

private theorem coeff_mul_of_mem_grade {k₁ k₂ : ℤ}
    (a₁ : AddMonoidAlgebra.grade B k₁) (a₂ : AddMonoidAlgebra.grade B k₂) :
    ((a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹])).coeff (k₁ + k₂) =
      (a₁ : B[T;T⁻¹]).coeff k₁ * (a₂ : B[T;T⁻¹]).coeff k₂ := by
  conv_lhs =>
    rw [← AddMonoidAlgebra.single_coeff_of_mem_grade a₁.property,
      ← AddMonoidAlgebra.single_coeff_of_mem_grade a₂.property]
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- Admissible left lifts of `slabCorrespondence` preserve products, supplying the multiplicativity
hypothesis of `GradedCorrespondence.transfer_mul`. -/
theorem slabCorrespondence_liftLeft_mul (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0)
    (i₁ i₂ : I) (hi : (i₁ : ℤ) + (i₂ : ℤ) ∈ I)
    (a₁ : AddMonoidAlgebra.grade B (i₁ : ℤ)) (a₂ : AddMonoidAlgebra.grade B (i₂ : ℤ)) :
    (slabCorrespondence q hI hJ).liftLeft ⟨(i₁ : ℤ) + (i₂ : ℤ), hi⟩
        ⟨(a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹]),
          SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (slabCorrespondence q hI hJ).liftLeft i₁ a₁ *
        (slabCorrespondence q hI hJ).liftLeft i₂ a₂ := by
  rw [slabCorrespondence_liftLeft_apply, slabCorrespondence_liftLeft_apply,
    slabCorrespondence_liftLeft_apply, coeff_mul_of_mem_grade a₁ a₂,
    Int.natAbs_add_of_nonneg (hI i₁.property) (hI i₂.property), pow_add, smul_mul_smul_comm]

/-- Admissible right lifts of `slabCorrespondence` preserve products, supplying the parallel
multiplicativity hypothesis for reverse crossing. -/
theorem slabCorrespondence_liftRight_mul (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0)
    (j₁ j₂ : J) (hj : (j₁ : ℤ) + (j₂ : ℤ) ∈ J)
    (a₁ : AddMonoidAlgebra.grade B (j₁ : ℤ)) (a₂ : AddMonoidAlgebra.grade B (j₂ : ℤ)) :
    (slabCorrespondence q hI hJ).liftRight ⟨(j₁ : ℤ) + (j₂ : ℤ), hj⟩
        ⟨(a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹]),
          SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (slabCorrespondence q hI hJ).liftRight j₁ a₁ *
        (slabCorrespondence q hI hJ).liftRight j₂ a₂ := by
  rw [slabCorrespondence_liftRight_apply, slabCorrespondence_liftRight_apply,
    slabCorrespondence_liftRight_apply, coeff_mul_of_mem_grade a₁ a₂,
    Int.natAbs_add_of_nonneg (hJ j₁.property) (hJ j₂.property), pow_add, smul_mul_smul_comm]

/-- Explicit right-chamber transfer of an incoming left monomial `C b * T i` across
`slabCorrespondence`. -/
theorem slabCorrespondence_transfer_C_mul_T (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0)
    (i : I) (b : B) (k : ℤ) :
    ((slabCorrespondence q hI hJ).transfer i k
        ⟨C b * T (i : ℤ), by
          rw [← single_eq_C_mul_T]
          exact AddMonoidAlgebra.single_mem_grade (i : ℤ) b⟩ : B[T;T⁻¹]) =
      if -(i : ℤ) = k then C (b * q ^ (i : ℤ).natAbs) * T (-(i : ℤ)) else 0 := by
  have hi : 0 ≤ (i : ℤ) := hI i.property
  have hc : (C b * T (i : ℤ)).coeff (i : ℤ) = b := by simp [← single_eq_C_mul_T]
  have himg : (slabCorrespondence q hI hJ).right
      ((slabCorrespondence q hI hJ).liftLeft i
        ⟨C b * T (i : ℤ), by
          rw [← single_eq_C_mul_T]
          exact AddMonoidAlgebra.single_mem_grade (i : ℤ) b⟩) =
      C (b * q ^ (i : ℤ).natAbs) * T (-(i : ℤ)) := by
    rw [slabCorrespondence_liftLeft_apply, hc, slabCorrespondence_right, AlgHom.toLinearMap_apply,
      map_smul, map_pow, rightChamberMap_X, mul_pow, ← map_pow, T_pow, mul_neg_one,
      Int.natAbs_of_nonneg hi, Algebra.smul_def, ← C_eq_algebraMap, ← mul_assoc, ← map_mul]
  rw [GradedCorrespondence.transfer_apply, himg, AddMonoidAlgebra.grade.decompose_apply,
    ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h <;> [rw [← h]; simp]

private theorem mapAlgHom_coeffLiftLinearMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q')
    (k : ℤ) (z : SlabAlgebra B q) (z' : SlabAlgebra B' q') (hz : mapAlgHom φ hq z = z')
    (a : (AddMonoidAlgebra.grade B k).restrictScalars R) :
    ∃ hmem : AddMonoidAlgebra.mapAlgHom ℤ φ a.val ∈ AddMonoidAlgebra.grade B' k,
      mapAlgHom φ hq (coeffLiftLinearMap q k z ⟨a.val, a.property⟩) =
        coeffLiftLinearMap q' k z' ⟨AddMonoidAlgebra.mapAlgHom ℤ φ a.val, hmem⟩ := by
  refine ⟨AddMonoidAlgebra.mapAlgHom_mem_grade φ
    ((Submodule.restrictScalars_mem R _ _).mp a.property), ?_⟩
  simp only [coeffLiftLinearMap_apply, AddMonoidAlgebra.coeff_mapAlgHom]
  rw [Algebra.smul_def ((a : B[T;T⁻¹]).coeff k) z, map_mul, mapAlgHom_algebraMap, hz,
    ← Algebra.smul_def (φ ((a : B[T;T⁻¹]).coeff k)) z']

/-- Functorial `R`-linear morphism of slab correspondences along an `R`-algebra homomorphism
`φ : B →ₐ[R] B'` sending `q` to `q'`, compatible with scalar extension and quotient towers. -/
def slabCorrespondenceHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q')
    {I J I' J' : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0)
    (hI' : I' ⊆ Set.Ici 0) (hJ' : J' ⊆ Set.Ici 0)
    (hII' : Set.MapsTo _root_.id I I') (hJJ' : Set.MapsTo _root_.id J J') :
    GradedCorrespondence.Hom
      ((slabCorrespondence q hI hJ).restrictScalars R)
      ((slabCorrespondence q' hI' hJ').restrictScalars R)
      _root_.id _root_.id where
  middle := (mapAlgHom φ hq).toLinearMap
  left := (AddMonoidAlgebra.mapAlgHom ℤ φ).toLinearMap
  right := (AddMonoidAlgebra.mapAlgHom ℤ φ).toLinearMap
  left_comm := LinearMap.ext fun u => by
    simpa [LinearMap.comp_apply] using AlgHom.congr_fun (mapAlgHom_comp_leftChamberMap φ hq) u
  right_comm := LinearMap.ext fun u => by
    simpa [LinearMap.comp_apply] using AlgHom.congr_fun (mapAlgHom_comp_rightChamberMap φ hq) u
  left_mem _ _ hx := (Submodule.restrictScalars_mem R _ _).mpr <|
    AddMonoidAlgebra.mapAlgHom_mem_grade φ ((Submodule.restrictScalars_mem R _ _).mp hx)
  right_mem _ _ hx := (Submodule.restrictScalars_mem R _ _).mpr <|
    AddMonoidAlgebra.mapAlgHom_mem_grade φ ((Submodule.restrictScalars_mem R _ _).mp hx)
  admissible_left := hII'
  admissible_right := hJJ'
  middle_liftLeft i a := by
    simp only [GradedCorrespondence.restrictScalars_liftLeft_apply, slabCorrespondence,
      AlgHom.toLinearMap_apply, _root_.id]
    exact (mapAlgHom_coeffLiftLinearMap φ hq (i : ℤ)
      (Z q (-(i : ℤ))) (Z q' (-(i : ℤ))) (mapAlgHom_Z φ hq _) a).choose_spec
  middle_liftRight j a := by
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, slabCorrespondence,
      AlgHom.toLinearMap_apply, _root_.id]
    exact (mapAlgHom_coeffLiftLinearMap φ hq (j : ℤ)
      (Z q (j : ℤ)) (Z q' (j : ℤ)) (mapAlgHom_Z φ hq _) a).choose_spec

/-! ### Tangential monoid algebras `S[Λ]` and full-exponent correspondences on `S[ℤ × Λ]` -/

section Tangential

variable {S S' Λ : Type*} [CommRing S] [CommRing S'] [AddCommMonoid Λ]

/-- Left full-exponent chamber homomorphism
`SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ)` sending a tangential
monomial `single m s` to `single (0, m) s` and `X` to `single (1, 0) 1`. -/
def leftTangentialMap (q : AddMonoidAlgebra S Λ) :
    SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ) :=
  (AddMonoidAlgebra.curryAlgEquiv S).symm.toAlgHom.comp ((leftChamberMap q).restrictScalars S)

/-- Right full-exponent chamber homomorphism
`SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ)` sending a tangential
monomial `single m s` to `single (0, m) s` and `Y` to `single (1, 0) 1`. -/
def rightTangentialMap (q : AddMonoidAlgebra S Λ) :
    SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ) :=
  (AddMonoidAlgebra.curryAlgEquiv S).symm.toAlgHom.comp ((rightChamberMap q).restrictScalars S)

@[simp] theorem leftTangentialMap_algebraMap_single (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) :
    leftTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s)) =
      AddMonoidAlgebra.single (0, m) s := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    AlgHom.commutes, ← C_eq_algebraMap]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 0 m s

@[simp] theorem rightTangentialMap_algebraMap_single (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) :
    rightTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s)) =
      AddMonoidAlgebra.single (0, m) s := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    AlgHom.commutes, ← C_eq_algebraMap]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 0 m s

@[simp] theorem leftTangentialMap_X (q : AddMonoidAlgebra S Λ) :
    leftTangentialMap q (X q) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    leftChamberMap_X]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 1 0 1

@[simp] theorem leftTangentialMap_Y (q : AddMonoidAlgebra S Λ) :
    leftTangentialMap q (Y q) = AddMonoidAlgebra.mapDomain (Prod.mk (-1 : ℤ)) q := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    leftChamberMap_Y, ← single_eq_C_mul_T]
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [AddMonoidAlgebra.single_add, map_add, AddMonoidAlgebra.mapDomain_add, hx, hy]
  | single m s =>
    rw [AddMonoidAlgebra.curryAlgEquiv_symm_single, AddMonoidAlgebra.mapDomain_single]

@[simp] theorem rightTangentialMap_X (q : AddMonoidAlgebra S Λ) :
    rightTangentialMap q (X q) = AddMonoidAlgebra.mapDomain (Prod.mk (-1 : ℤ)) q := by
  have h : rightTangentialMap q (X q) = leftTangentialMap q (Y q) := by
    simp [rightTangentialMap, leftTangentialMap]
  rw [h, leftTangentialMap_Y]

@[simp] theorem rightTangentialMap_Y (q : AddMonoidAlgebra S Λ) :
    rightTangentialMap q (Y q) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    rightChamberMap_Y]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 1 0 1

theorem leftTangentialMap_algebraMap_single_mul_Z
    (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) (n : ℤ) :
    leftTangentialMap q
        (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s) * Z q n) =
      (AddMonoidAlgebra.curryAlgEquiv S).symm
        (AddMonoidAlgebra.single (-n) (AddMonoidAlgebra.single m s * q ^ n.toNat)) := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgHom.restrictScalars_apply, map_mul, AlgHom.commutes, leftChamberMap_Z,
    ← C_eq_algebraMap, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T]

theorem rightTangentialMap_algebraMap_single_mul_Z
    (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) (n : ℤ) :
    rightTangentialMap q
        (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s) * Z q n) =
      (AddMonoidAlgebra.curryAlgEquiv S).symm
        (AddMonoidAlgebra.single n (AddMonoidAlgebra.single m s * q ^ (-n).toNat)) := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgHom.restrictScalars_apply, map_mul, AlgHom.commutes, rightChamberMap_Z,
    ← C_eq_algebraMap, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T]

/-- Joint injectivity of the full-exponent chamber maps into `S[ℤ × Λ]` for arbitrary `q`. -/
theorem tangentialChamberProd_injective (q : AddMonoidAlgebra S Λ) :
    Function.Injective
      ((leftTangentialMap q).toLinearMap.prod (rightTangentialMap q).toLinearMap) :=
  fun _ _ huv => chamberProd_injective q <| Prod.ext
    ((AddMonoidAlgebra.curryAlgEquiv S).symm.injective (congrArg Prod.fst huv))
    ((AddMonoidAlgebra.curryAlgEquiv S).symm.injective (congrArg Prod.snd huv))

private theorem mapAlgHom_mapDomain_mk [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (k : ℤ) (q : AddMonoidAlgebra S Λ) :
    AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ (AddMonoidAlgebra.mapDomain (Prod.mk k) q) =
      AddMonoidAlgebra.mapDomain (Prod.mk k) (AddMonoidAlgebra.mapAlgHom Λ φ q) := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [AddMonoidAlgebra.mapDomain_add, map_add, hx, hy]
  | single m s => simp

/-- Naturality of `leftTangentialMap` along a coefficient `R`-algebra homomorphism
`φ : S →ₐ[R] S'` sending `q` to `q'`. -/
theorem mapAlgHom_comp_leftTangentialMap [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq : AddMonoidAlgebra.mapAlgHom Λ φ q = q') :
    ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).comp
        ((leftTangentialMap q).restrictScalars R) =
      ((leftTangentialMap q').restrictScalars R).comp
        (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
          ((AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq)) := by
  refine algHom_ext_of_algebra (fun b => ?_) (by simp) ?_
  · induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp | add x y hx hy => simp [map_add, hx, hy] | single m s => simp
  · subst hq; simp [mapAlgHom_mapDomain_mk]

/-- Naturality of `rightTangentialMap` along a coefficient `R`-algebra homomorphism
`φ : S →ₐ[R] S'` sending `q` to `q'`. -/
theorem mapAlgHom_comp_rightTangentialMap [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq : AddMonoidAlgebra.mapAlgHom Λ φ q = q') :
    ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).comp
        ((rightTangentialMap q).restrictScalars R) =
      ((rightTangentialMap q').restrictScalars R).comp
        (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
          ((AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq)) := by
  refine algHom_ext_of_algebra (fun b => ?_) ?_ (by simp)
  · induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp | add x y hx hy => simp [map_add, hx, hy] | single m s => simp
  · subst hq; simp [mapAlgHom_mapDomain_mk]

/-- Auxiliary `S`-linear lift reading the `p`-th coefficient in `S[ℤ × Λ]` and scaling a
tangential monomial times a slab basis element. -/
private def tangentialLiftLinearMap (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) :
    AddMonoidAlgebra.grade S p →ₗ[S] SlabAlgebra (AddMonoidAlgebra S Λ) q :=
  ((LinearMap.smulRight LinearMap.id
      (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single p.2 1) * z)).comp
    ((Finsupp.lapply p).comp (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap)).comp
    (AddMonoidAlgebra.grade S p).subtype

private theorem tangentialLiftLinearMap_apply (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) (a : AddMonoidAlgebra.grade S p) :
    tangentialLiftLinearMap q p z a =
      algebraMap (AddMonoidAlgebra S Λ) _
        (AddMonoidAlgebra.single p.2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff p)) * z := by
  simp only [tangentialLiftLinearMap, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lapply_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  have hsmul (r : S) (x : AddMonoidAlgebra S Λ) :
      r • algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q) x =
        algebraMap _ _ (r • x) :=
    (LinearMap.map_smul_of_tower
      (Algebra.linearMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)) r x).symm
  rw [← smul_mul_assoc, hsmul, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- The `S`-linear full-exponent `GradedCorrespondence` across `SlabAlgebra S[Λ] q` on the monoid
algebras `S[ℤ × Λ]` graded by `AddMonoidAlgebra.grade S`, for admissible exponent sets
`I, J ⊆ {p : ℤ × Λ | 0 ≤ p.1}`. -/
def tangentialSlabCorrespondence (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    GradedCorrespondence (B := SlabAlgebra (AddMonoidAlgebra S Λ) q)
      (AddMonoidAlgebra.grade S) (AddMonoidAlgebra.grade S) I J where
  left := (leftTangentialMap q).toLinearMap
  right := (rightTangentialMap q).toLinearMap
  liftLeft i := tangentialLiftLinearMap q (i : ℤ × Λ) (Z q (-(i : ℤ × Λ).1))
  liftRight j := tangentialLiftLinearMap q (j : ℤ × Λ) (Z q (j : ℤ × Λ).1)
  left_liftLeft i := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply,
      tangentialLiftLinearMap_apply, leftTangentialMap_algebraMap_single_mul_Z,
      neg_neg, Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.val i.property)), pow_zero, mul_one,
      AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]
    exact AddMonoidAlgebra.single_coeff_of_mem_grade a.property
  right_liftRight j := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply,
      tangentialLiftLinearMap_apply, rightTangentialMap_algebraMap_single_mul_Z,
      Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.val j.property)), pow_zero, mul_one,
      AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]
    exact AddMonoidAlgebra.single_coeff_of_mem_grade a.property

@[simp] theorem tangentialSlabCorrespondence_left (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (tangentialSlabCorrespondence q hI hJ).left = (leftTangentialMap q).toLinearMap := (rfl)

@[simp] theorem tangentialSlabCorrespondence_right (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (tangentialSlabCorrespondence q hI hJ).right = (rightTangentialMap q).toLinearMap := (rfl)

@[simp] theorem tangentialSlabCorrespondence_liftLeft_apply (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (a : AddMonoidAlgebra.grade S (i : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftLeft i a =
      algebraMap (AddMonoidAlgebra S Λ) _
        (AddMonoidAlgebra.single (i : ℤ × Λ).2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff i)) *
        Z q (-(i : ℤ × Λ).1) :=
  tangentialLiftLinearMap_apply q i (Z q (-(i : ℤ × Λ).1)) a

@[simp] theorem tangentialSlabCorrespondence_liftRight_apply (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (j : J) (a : AddMonoidAlgebra.grade S (j : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftRight j a =
      algebraMap (AddMonoidAlgebra S Λ) _
        (AddMonoidAlgebra.single (j : ℤ × Λ).2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff j)) *
        Z q (j : ℤ × Λ).1 :=
  tangentialLiftLinearMap_apply q j (Z q (j : ℤ × Λ).1) a

/-- Explicit homogeneous transfer of an incoming monomial `single (d, m) s` across
`tangentialSlabCorrespondence`, expressed in terms of the tangential expansion of `q ^ d.natAbs`:
when `Λ` is an additive commutative group, the `(k, m')`-transfer is
`single (-d, m') (s * (q ^ d.natAbs).coeff (m' - m))` for `k = -d` and `0` otherwise. -/
theorem tangentialSlabCorrespondence_transfer_single
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (q : AddMonoidAlgebra S G)
    {I J : Set (ℤ × G)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (s : S) (k : ℤ) (m' : G) :
    ((tangentialSlabCorrespondence q hI hJ).transfer i (k, m')
        ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
          AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩ :
        AddMonoidAlgebra S (ℤ × G)) =
      if -(i : ℤ × G).1 = k then
        AddMonoidAlgebra.single (-(i : ℤ × G).1, m')
          (s * (q ^ (i : ℤ × G).1.natAbs).coeff (m' - (i : ℤ × G).2))
      else 0 := by
  have hi : 0 ≤ (i : ℤ × G).1 := hI i.val i.property
  have hto : (i : ℤ × G).1.toNat = (i : ℤ × G).1.natAbs := by omega
  let f : AddMonoidAlgebra S G :=
    AddMonoidAlgebra.single (i : ℤ × G).2 s * q ^ (i : ℤ × G).1.natAbs
  -- Lift the incoming monomial and push it to the right chamber.
  have himg : (tangentialSlabCorrespondence q hI hJ).right
      ((tangentialSlabCorrespondence q hI hJ).liftLeft i
        ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
          AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩) =
      (AddMonoidAlgebra.curryAlgEquiv S).symm
        (AddMonoidAlgebra.single (-(i : ℤ × G).1) f) := by
    rw [tangentialSlabCorrespondence_liftLeft_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same, tangentialSlabCorrespondence_right, AlgHom.toLinearMap_apply,
      rightTangentialMap_algebraMap_single_mul_Z, neg_neg, hto]
  -- Read off the `(k, m')`-coefficient of the uncurried image.
  have hcoeff : ((AddMonoidAlgebra.curryAlgEquiv S).symm
      (AddMonoidAlgebra.single (-(i : ℤ × G).1) f)).coeff (k, m') =
      if -(i : ℤ × G).1 = k then f.coeff m' else 0 := by
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [AddMonoidAlgebra.single_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      split_ifs <;> simp
    | single m₀ r =>
      rw [AddMonoidAlgebra.curryAlgEquiv_symm_single, AddMonoidAlgebra.coeff_single,
        AddMonoidAlgebra.coeff_single]
      rcases eq_or_ne (-(i : ℤ × G).1) k with rfl | hk <;>
        rcases eq_or_ne m₀ m' with rfl | hm <;> simp [*]
  -- Project to the `(k, m')` graded piece via `AddMonoidAlgebra.grade.decompose_apply`.
  rw [GradedCorrespondence.transfer_apply, himg, AddMonoidAlgebra.grade.decompose_apply, hcoeff]
  split_ifs with hk <;> [(subst hk; simp [f, sub_eq_neg_add]); simp]

private theorem mapAlgHom_tangentialLiftLinearMap [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq' : ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) q = q')
    (p : ℤ × Λ) (z : SlabAlgebra (AddMonoidAlgebra S Λ) q)
    (z' : SlabAlgebra (AddMonoidAlgebra S' Λ) q')
    (hz : mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq' z = z')
    (a : (AddMonoidAlgebra.grade S p).restrictScalars R) :
    ∃ hmem : AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ a.val ∈ AddMonoidAlgebra.grade S' p,
      mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq'
        (tangentialLiftLinearMap q p z ⟨a.val, a.property⟩) =
        tangentialLiftLinearMap q' p z' ⟨AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ a.val, hmem⟩ := by
  refine ⟨AddMonoidAlgebra.mapAlgHom_mem_grade φ
    ((Submodule.restrictScalars_mem R _ _).mp a.property), ?_⟩
  rw [tangentialLiftLinearMap_apply, tangentialLiftLinearMap_apply,
    AddMonoidAlgebra.coeff_mapAlgHom, map_mul, mapAlgHom_algebraMap, hz]
  simp

/-- Functorial `R`-linear morphism of full-exponent tangential slab correspondences along a
coefficient `R`-algebra homomorphism `φ : S →ₐ[R] S'` (covering scalar extensions and compatible
quotient towers `(S_k, q_k)`). -/
def tangentialSlabCorrespondenceHom [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq : AddMonoidAlgebra.mapAlgHom Λ φ q = q')
    {I J I' J' : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (hI' : ∀ p ∈ I', 0 ≤ p.1) (hJ' : ∀ p ∈ J', 0 ≤ p.1)
    (hII' : Set.MapsTo _root_.id I I') (hJJ' : Set.MapsTo _root_.id J J') :
    GradedCorrespondence.Hom
      ((tangentialSlabCorrespondence q hI hJ).restrictScalars R)
      ((tangentialSlabCorrespondence q' hI' hJ').restrictScalars R)
      _root_.id _root_.id where
  middle :=
    (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
      ((AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq)).toLinearMap
  left := ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).toLinearMap
  right := ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).toLinearMap
  left_comm := LinearMap.ext fun u => by
    simpa [LinearMap.comp_apply] using AlgHom.congr_fun (mapAlgHom_comp_leftTangentialMap φ hq) u
  right_comm := LinearMap.ext fun u => by
    simpa [LinearMap.comp_apply] using AlgHom.congr_fun (mapAlgHom_comp_rightTangentialMap φ hq) u
  left_mem _ _ hx := (Submodule.restrictScalars_mem R _ _).mpr <|
    AddMonoidAlgebra.mapAlgHom_mem_grade φ ((Submodule.restrictScalars_mem R _ _).mp hx)
  right_mem _ _ hx := (Submodule.restrictScalars_mem R _ _).mpr <|
    AddMonoidAlgebra.mapAlgHom_mem_grade φ ((Submodule.restrictScalars_mem R _ _).mp hx)
  admissible_left := hII'
  admissible_right := hJJ'
  middle_liftLeft i a := by
    have hq' := (AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq
    simp only [GradedCorrespondence.restrictScalars_liftLeft_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact (mapAlgHom_tangentialLiftLinearMap φ hq' i.val
      (Z q (-i.val.1)) (Z q' (-i.val.1)) (mapAlgHom_Z _ hq' _) a).choose_spec
  middle_liftRight j a := by
    have hq' := (AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact (mapAlgHom_tangentialLiftLinearMap φ hq' j.val
      (Z q j.val.1) (Z q' j.val.1) (mapAlgHom_Z _ hq' _) a).choose_spec

end Tangential

end SlabAlgebra

end TauCeti
