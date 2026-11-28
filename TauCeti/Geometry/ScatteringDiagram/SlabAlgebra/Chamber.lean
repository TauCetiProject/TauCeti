/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.LinearAlgebra.GradedCorrespondence.Hom
public import TauCeti.LinearAlgebra.GradedCorrespondence.RestrictScalars
public import TauCeti.RingTheory.Node.NormalForm
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.Grading
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.Polynomial.Laurent.Binomial

/-!
# Chamber Laurent maps and graded correspondences for nodal slab algebras

Across a codimension-one slab with algebra `NodeAlgebra B q = B[x, y] / (x y - q)`, the two
adjacent chambers carry Laurent algebras `B[T;T⁻¹]` linked by `B`-algebra homomorphisms:
* `NodeAlgebra.leftChamberMap q`: `coord q 0 ↦ T 1`, `coord q 1 ↦ C q * T (-1)`,
  sending `Z q n ↦ C (q ^ n.toNat) * T (-n)`;
* `NodeAlgebra.rightChamberMap q`: `coord q 0 ↦ C q * T (-1)`, `coord q 1 ↦ T 1`,
  sending `Z q n ↦ C (q ^ (-n).toNat) * T n`.

From the Laurent coefficients (`coeff_leftChamberMap`, `coeff_rightChamberMap`) we obtain:
* joint injectivity of `(leftChamberMap q, rightChamberMap q)` for arbitrary `B` and `q`
  (`NodeAlgebra.chamberProd_injective`), individual injectivity when `IsRegular q`, and the
  binomial expansion for `q = C t * (1 + T 1)` (`NodeAlgebra.rightChamberMap_binomial`);
* the `B`-linear `GradedCorrespondence` `NodeAlgebra.slabCorrespondence` with multiplicative
  lifts, explicit transfers (`slabCorrespondence_transfer_C_mul_T`,
  `slabCorrespondence_symm_transfer_C_mul_T`), and functoriality (`slabCorrespondenceHom`);
* for `B = S[Λ]`, full-exponent chamber maps (`leftTangentialMap`, `rightTangentialMap`) and the
  graded correspondence `tangentialSlabCorrespondence` on `S[ℤ × Λ]` with lift multiplicativity,
  explicit transfers (`tangentialSlabCorrespondence_transfer_single`), and functoriality.

## References

* M. Gross and B. Siebert, *An Invitation to Toric Degenerations*, §2.3, arXiv:0808.2749v2.
* M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*, Definitions 3.1–3.3, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace TauCeti

namespace NodeAlgebra

open LaurentPolynomial (C T T_pow T_add T_zero C_eq_algebraMap single_eq_C_mul_T)
open scoped LaurentPolynomial

variable {R B B' : Type*} [CommRing B] [CommRing B']

/-! ### Left and right chamber Laurent homomorphisms -/

/-- Left chamber homomorphism `NodeAlgebra B q →ₐ[B] B[T;T⁻¹]` sending
`coord q 0 ↦ T 1` and `coord q 1 ↦ C q * T (-1)`. -/
def leftChamberMap (q : B) : NodeAlgebra B q →ₐ[B] B[T;T⁻¹] :=
  lift q (T 1) (C q * T (-1)) (by
    rw [mul_left_comm, ← T_add, add_neg_cancel, T_zero, mul_one, C_eq_algebraMap])

/-- Right chamber homomorphism `NodeAlgebra B q →ₐ[B] B[T;T⁻¹]` sending
`coord q 0 ↦ C q * T (-1)` and `coord q 1 ↦ T 1`. -/
def rightChamberMap (q : B) : NodeAlgebra B q →ₐ[B] B[T;T⁻¹] :=
  lift q (C q * T (-1)) (T 1) (by
    rw [mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one, C_eq_algebraMap])

@[simp] theorem leftChamberMap_coord_zero (q : B) : leftChamberMap q (coord q 0) = T 1 :=
  lift_coord_zero _ _ _ _
@[simp] theorem leftChamberMap_coord_one (q : B) : leftChamberMap q (coord q 1) = C q * T (-1) :=
  lift_coord_one _ _ _ _
@[simp] theorem rightChamberMap_coord_zero (q : B) :
    rightChamberMap q (coord q 0) = C q * T (-1) := lift_coord_zero _ _ _ _
@[simp] theorem rightChamberMap_coord_one (q : B) : rightChamberMap q (coord q 1) = T 1 :=
  lift_coord_one _ _ _ _

/-- In the left chamber, `Z q n` maps to `C (q ^ n.toNat) * T (-n)`. -/
@[simp] theorem leftChamberMap_Z (q : B) (n : ℤ) :
    leftChamberMap q (Z q n) = C (q ^ n.toNat) * T (-n) := by
  rw [leftChamberMap, lift_Z]
  split_ifs with hn
  · have hto : n.toNat = 0 := by omega
    have hcast : (n.natAbs : ℤ) = -n := by omega
    simp [T_pow, hto, hcast]
  · have hnat : n.natAbs = n.toNat := by omega
    have hcast : (n.toNat : ℤ) = n := by omega
    simp [mul_pow, ← map_pow, T_pow, hnat, hcast]

/-- In the right chamber, `Z q n` maps to `C (q ^ (-n).toNat) * T n`. -/
@[simp] theorem rightChamberMap_Z (q : B) (n : ℤ) :
    rightChamberMap q (Z q n) = C (q ^ (-n).toNat) * T n := by
  rw [rightChamberMap, lift_Z]
  split_ifs with hn
  · have hnat : n.natAbs = (-n).toNat := by omega
    have hcast : ((-n).toNat : ℤ) = -n := by omega
    simp [mul_pow, ← map_pow, T_pow, hnat, hcast]
  · have hto : (-n).toNat = 0 := by omega
    have hcast : (n.natAbs : ℤ) = n := by omega
    simp [T_pow, hto, hcast]

private theorem coeff_chamberMap_aux (q : B) (f : NodeAlgebra B q →ₗ[B] B[T;T⁻¹])
    (e : ℤ ≃ ℤ) (c : ℤ → B) (hf : ∀ n : ℤ, f (Z q n) = C (c n) * T (e n))
    (u : NodeAlgebra B q) (k : ℤ) :
    (f u).coeff k = ((slabBasis q).repr u (e.symm k)) * c (e.symm k) := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul_Z b m =>
    rw [map_smul, map_smul, hf, slabBasis_repr_Z, ← single_eq_C_mul_T,
      AddMonoidAlgebra.smul_single, smul_eq_mul, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne (e m) k with rfl | h
    · simp
    · simp [e.eq_symm_apply, h]

/-- The `k`-th Laurent coefficient of `leftChamberMap q u` is the `(-k)`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_leftChamberMap (q : B) (u : NodeAlgebra B q) (k : ℤ) :
    (leftChamberMap q u).coeff k = ((slabBasis q).repr u (-k)) * q ^ (-k).toNat :=
  coeff_chamberMap_aux q (leftChamberMap q).toLinearMap (Equiv.neg ℤ)
    (fun n => q ^ n.toNat) (leftChamberMap_Z q) u k

/-- The `k`-th Laurent coefficient of `rightChamberMap q u` is the `k`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_rightChamberMap (q : B) (u : NodeAlgebra B q) (k : ℤ) :
    (rightChamberMap q u).coeff k = ((slabBasis q).repr u k) * q ^ (-k).toNat :=
  coeff_chamberMap_aux q (rightChamberMap q).toLinearMap (Equiv.refl ℤ)
    (fun n => q ^ (-n).toNat) (rightChamberMap_Z q) u k

@[simp] theorem coeff_leftChamberMap_natCast (q : B) (u : NodeAlgebra B q) (a : ℕ) :
    (leftChamberMap q u).coeff (a : ℤ) = (slabBasis q).repr u (-(a : ℤ)) := by
  rw [coeff_leftChamberMap, Int.toNat_of_nonpos (by omega), pow_zero, mul_one]

@[simp] theorem coeff_rightChamberMap_natCast (q : B) (u : NodeAlgebra B q) (a : ℕ) :
    (rightChamberMap q u).coeff (a : ℤ) = (slabBasis q).repr u (a : ℤ) := by
  rw [coeff_rightChamberMap, Int.toNat_of_nonpos (by omega), pow_zero, mul_one]

/-- **Joint injectivity of the chamber maps**: for every commutative ring `B` and every `q : B`,
an element of `NodeAlgebra B q` is uniquely determined by its left and right chamber Laurent
expansions. -/
theorem chamberProd_injective (q : B) :
    Function.Injective ((leftChamberMap q).toLinearMap.prod (rightChamberMap q).toLinearMap) := by
  intro u v huv
  have hL : leftChamberMap q u = leftChamberMap q v := congrArg Prod.fst huv
  have hR : rightChamberMap q u = rightChamberMap q v := congrArg Prod.snd huv
  apply (slabBasis q).repr.injective; ext n
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

/-- Naturality of `leftChamberMap` along a coefficient `R`-algebra homomorphism
`φ : B →ₐ[R] B'` sending `q` to `q'`. -/
theorem mapAlgHom_comp_leftChamberMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (AddMonoidAlgebra.mapAlgHom ℤ φ).comp ((leftChamberMap q).restrictScalars R) =
      ((leftChamberMap q').restrictScalars R).comp (mapAlgHom φ hq) :=
  algHom_ext_of_algebra (fun _ => by simp [← C_eq_algebraMap]) (by simp) (by simp [hq])

/-- Naturality of `rightChamberMap` along a coefficient `R`-algebra homomorphism
`φ : B →ₐ[R] B'` sending `q` to `q'`. -/
theorem mapAlgHom_comp_rightChamberMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (AddMonoidAlgebra.mapAlgHom ℤ φ).comp ((rightChamberMap q).restrictScalars R) =
      ((rightChamberMap q').restrictScalars R).comp (mapAlgHom φ hq) :=
  algHom_ext_of_algebra (fun _ => by simp [← C_eq_algebraMap]) (by simp [hq]) (by simp)

/-- In `S[w, w⁻¹][x, y] / (x y - t (1 + w))` (with `w = T 1` in `S[T;T⁻¹]` and `y = T 1` in
`(S[T;T⁻¹])[T;T⁻¹]`), `x^a w^b` maps in the right chamber to
`t^a y^{-a} ∑_{j=0}^a binom(a, j) w^{b + j}`. -/
theorem rightChamberMap_binomial {S : Type*} [CommRing S] (t : S) (a : ℕ) (b : ℤ) :
    let q : S[T;T⁻¹] := C t * (1 + T 1)
    rightChamberMap q (coord q 0 ^ a * algebraMap S[T;T⁻¹] (NodeAlgebra S[T;T⁻¹] q) (T b)) =
      C (C (t ^ a)) * T (-(a : ℤ)) * ∑ j ∈ Finset.range (a + 1),
        (a.choose j : (S[T;T⁻¹])[T;T⁻¹]) * C (T (b + j)) := by
  intro q
  calc rightChamberMap q (coord q 0 ^ a * algebraMap S[T;T⁻¹] (NodeAlgebra S[T;T⁻¹] q) (T b))
      = C (C (t ^ a) * ((1 + T 1 : S[T;T⁻¹]) ^ a * T b)) * T (-(a : ℤ)) := by
        rw [map_mul, map_pow, rightChamberMap_coord_zero, AlgHom.commutes]
        simp [q, mul_pow, map_mul, T_pow]; ring
    _ = C (C (t ^ a)) * T (-(a : ℤ)) * ∑ j ∈ Finset.range (a + 1),
          (a.choose j : (S[T;T⁻¹])[T;T⁻¹]) * C (T (b + j)) := by
        rw [LaurentPolynomial.one_add_T_pow_mul_T, map_mul, map_sum, mul_right_comm]
        exact congrArg _ (Finset.sum_congr rfl fun _ _ => by rw [mul_one, map_mul, map_natCast])

/-! ### `B`-linear graded correspondence across a slab -/

/-- Auxiliary `B`-linear map reading the `k`-th Laurent coefficient and scaling a slab element. -/
private def coeffLiftLinearMap (q : B) (k : ℤ) (z : NodeAlgebra B q) :
    AddMonoidAlgebra.grade B k →ₗ[B] NodeAlgebra B q :=
  ((LinearMap.smulRight (1 : B →ₗ[B] B) z).comp
    ((Finsupp.lapply k).comp (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap)).comp
    (AddMonoidAlgebra.grade B k).subtype

@[simp] private theorem coeffLiftLinearMap_apply (q : B) (k : ℤ) (z : NodeAlgebra B q)
    (a : AddMonoidAlgebra.grade B k) :
    coeffLiftLinearMap q k z a = ((a : B[T;T⁻¹]).coeff k) • z := by simp [coeffLiftLinearMap]

private theorem chamberMap_coeffLiftLinearMap (q : B) (f : NodeAlgebra B q →ₐ[B] B[T;T⁻¹])
    (k : ℤ) (z : NodeAlgebra B q) (hz : f z = T k) :
    f.toLinearMap.comp (coeffLiftLinearMap q k z) = (AddMonoidAlgebra.grade B k).subtype :=
  LinearMap.ext fun a => by
    simp [hz, Algebra.smul_def, ← C_eq_algebraMap, ← single_eq_C_mul_T,
      AddMonoidAlgebra.single_coeff_eq_of_mem_grade a.property]

/-- The `B`-linear `GradedCorrespondence` across `NodeAlgebra B q` for incoming degree sets
`I, J ⊆ Set.Ici (0 : ℤ)` (such as `Set.Ici 0` for all nonnegative incoming powers or `Set.Ioi 0`
for strictly transverse incoming powers):
* on `i ∈ I` (`i ≥ 0`), `C b * T i` lifts from the left to
  `b • coord q 0 ^ i.natAbs = b • Z q (-i)`;
* on `j ∈ J` (`j ≥ 0`), `C b * T j` lifts from the right to
  `b • coord q 1 ^ j.natAbs = b • Z q j`. -/
def slabCorrespondence (q : B) {I J : Set ℤ} (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    GradedCorrespondence (B := NodeAlgebra B q)
      (AddMonoidAlgebra.grade B) (AddMonoidAlgebra.grade B) I J where
  left := (leftChamberMap q).toLinearMap
  right := (rightChamberMap q).toLinearMap
  liftLeft i := coeffLiftLinearMap q (i : ℤ) (Z q (-(i : ℤ)))
  liftRight j := coeffLiftLinearMap q (j : ℤ) (Z q (j : ℤ))
  left_liftLeft i := chamberMap_coeffLiftLinearMap q (leftChamberMap q) (i : ℤ) (Z q (-(i : ℤ)))
    (by simp [Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.property))])
  right_liftRight j := chamberMap_coeffLiftLinearMap q (rightChamberMap q) (j : ℤ) (Z q (j : ℤ))
    (by simp [Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.property))])

@[simp] theorem slabCorrespondence_left (q : B) {I J : Set ℤ} (hI : I ⊆ Set.Ici 0)
    (hJ : J ⊆ Set.Ici 0) : (slabCorrespondence q hI hJ).left = (leftChamberMap q).toLinearMap :=
  (rfl)

@[simp] theorem slabCorrespondence_right (q : B) {I J : Set ℤ} (hI : I ⊆ Set.Ici 0)
    (hJ : J ⊆ Set.Ici 0) : (slabCorrespondence q hI hJ).right = (rightChamberMap q).toLinearMap :=
  (rfl)

@[simp] theorem slabCorrespondence_liftLeft_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (i : I) (a : AddMonoidAlgebra.grade B (i : ℤ)) :
    (slabCorrespondence q hI hJ).liftLeft i a =
      ((a : B[T;T⁻¹]).coeff (i : ℤ)) • coord q 0 ^ (i : ℤ).natAbs := by
  rw [slabCorrespondence, coeffLiftLinearMap_apply]
  congr 1; rw [← Int.natAbs_of_nonneg (hI i.property), Z_neg_natCast, Int.natAbs_natCast]

@[simp] theorem slabCorrespondence_liftRight_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (j : J) (a : AddMonoidAlgebra.grade B (j : ℤ)) :
    (slabCorrespondence q hI hJ).liftRight j a =
      ((a : B[T;T⁻¹]).coeff (j : ℤ)) • coord q 1 ^ (j : ℤ).natAbs := by
  rw [slabCorrespondence, coeffLiftLinearMap_apply, Z_of_nonneg q (hJ j.property)]

/-- Admissible left lifts of `slabCorrespondence` preserve products, supplying the multiplicativity
hypothesis of `GradedCorrespondence.transfer_mul`. -/
theorem slabCorrespondence_liftLeft_mul (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (i₁ i₂ : I)
    (hi : (i₁ : ℤ) + (i₂ : ℤ) ∈ I)
    (a₁ : AddMonoidAlgebra.grade B (i₁ : ℤ))
    (a₂ : AddMonoidAlgebra.grade B (i₂ : ℤ)) :
    (slabCorrespondence q hI hJ).liftLeft ⟨(i₁ : ℤ) + (i₂ : ℤ), hi⟩
        ⟨(a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹]), SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (slabCorrespondence q hI hJ).liftLeft i₁ a₁ *
        (slabCorrespondence q hI hJ).liftLeft i₂ a₂ := by
  simp only [slabCorrespondence_liftLeft_apply,
    AddMonoidAlgebra.coeff_mul_of_mem_grade a₁.property a₂.property,
    Int.natAbs_add_of_nonneg (hI i₁.property) (hI i₂.property), pow_add, smul_mul_smul_comm]

/-- Admissible right lifts of `slabCorrespondence` preserve products, supplying the parallel
multiplicativity hypothesis for reverse crossing. -/
theorem slabCorrespondence_liftRight_mul (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (j₁ j₂ : J)
    (hj : (j₁ : ℤ) + (j₂ : ℤ) ∈ J)
    (a₁ : AddMonoidAlgebra.grade B (j₁ : ℤ))
    (a₂ : AddMonoidAlgebra.grade B (j₂ : ℤ)) :
    (slabCorrespondence q hI hJ).liftRight ⟨(j₁ : ℤ) + (j₂ : ℤ), hj⟩
        ⟨(a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹]), SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (slabCorrespondence q hI hJ).liftRight j₁ a₁ *
        (slabCorrespondence q hI hJ).liftRight j₂ a₂ := by
  simp only [slabCorrespondence_liftRight_apply,
    AddMonoidAlgebra.coeff_mul_of_mem_grade a₁.property a₂.property,
    Int.natAbs_add_of_nonneg (hJ j₁.property) (hJ j₂.property), pow_add, smul_mul_smul_comm]

private theorem slab_transfer_C_mul_T_aux (q : B) {I J : Set ℤ}
    (c : GradedCorrespondence (B := NodeAlgebra B q)
      (AddMonoidAlgebra.grade B) (AddMonoidAlgebra.grade B) I J)
    (i : I) (hi : 0 ≤ (i : ℤ)) (b : B) (k : ℤ)
    (hm : C b * T (i : ℤ) ∈ AddMonoidAlgebra.grade B (i : ℤ))
    (himg : c.right (c.liftLeft i ⟨C b * T (i : ℤ), hm⟩) =
      b • (C q * T (-1)) ^ (i : ℤ).natAbs) :
    (c.transfer i k ⟨C b * T (i : ℤ), hm⟩ : B[T;T⁻¹]) =
      if -(i : ℤ) = k then C (b * q ^ (i : ℤ).natAbs) * T (-(i : ℤ)) else 0 := by
  have hsingle : b • (C q * T (-1)) ^ (i : ℤ).natAbs =
      AddMonoidAlgebra.single (-(i : ℤ)) (b * q ^ (i : ℤ).natAbs) := by
    simp [Algebra.smul_def, ← C_eq_algebraMap, mul_pow, T_pow, Int.natAbs_of_nonneg hi,
      single_eq_C_mul_T, mul_assoc]
  simp only [GradedCorrespondence.transfer_apply, himg, hsingle,
    AddMonoidAlgebra.grade.decompose_single, DirectSum.coe_of_apply]
  split_ifs with h <;> simp [h, single_eq_C_mul_T]

/-- Explicit right-chamber transfer of an incoming left monomial `C b * T i` across
`slabCorrespondence`. -/
theorem slabCorrespondence_transfer_C_mul_T (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (i : I) (b : B) (k : ℤ) :
    ((slabCorrespondence q hI hJ).transfer i k
        ⟨C b * T (i : ℤ), by
          rw [← single_eq_C_mul_T]
          exact AddMonoidAlgebra.single_mem_grade _ b⟩ : B[T;T⁻¹]) =
      if -(i : ℤ) = k then C (b * q ^ (i : ℤ).natAbs) * T (-(i : ℤ)) else 0 :=
  slab_transfer_C_mul_T_aux q (slabCorrespondence q hI hJ) i (hI i.property) b k _ <| by
    simp [slabCorrespondence_liftLeft_apply, ← single_eq_C_mul_T]

/-- Explicit left-chamber reverse transfer of an incoming right monomial `C b * T j` across
`(slabCorrespondence q hI hJ).symm`. -/
theorem slabCorrespondence_symm_transfer_C_mul_T (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (j : J) (b : B) (k : ℤ) :
    ((slabCorrespondence q hI hJ).symm.transfer j k
        ⟨C b * T (j : ℤ), by
          rw [← single_eq_C_mul_T]
          exact AddMonoidAlgebra.single_mem_grade _ b⟩ : B[T;T⁻¹]) =
      if -(j : ℤ) = k then C (b * q ^ (j : ℤ).natAbs) * T (-(j : ℤ)) else 0 :=
  slab_transfer_C_mul_T_aux q (slabCorrespondence q hI hJ).symm j (hJ j.property) b k _ <| by
    simp [slabCorrespondence_liftRight_apply, ← single_eq_C_mul_T]

private theorem mapAlgHom_coeffLiftLinearMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q')
    (k : ℤ) (z : NodeAlgebra B q) (z' : NodeAlgebra B' q') (hz : mapAlgHom φ hq z = z')
    (a : (AddMonoidAlgebra.grade B k).restrictScalars R) :
    mapAlgHom φ hq (coeffLiftLinearMap q k z ⟨a.val, a.property⟩) =
      coeffLiftLinearMap q' k z' ⟨AddMonoidAlgebra.mapAlgHom ℤ φ a.val,
        AddMonoidAlgebra.mapAlgHom_mem_grade φ
          ((Submodule.restrictScalars_mem R _ _).mp a.property)⟩ := by
  simp only [coeffLiftLinearMap_apply, AddMonoidAlgebra.coeff_mapAlgHom]
  rw [Algebra.smul_def ((a : B[T;T⁻¹]).coeff k) z, map_mul, mapAlgHom_algebraMap, hz,
    ← Algebra.smul_def (φ ((a : B[T;T⁻¹]).coeff k)) z']

/-- Functorial `R`-linear morphism of slab correspondences along an `R`-algebra homomorphism
`φ : B →ₐ[R] B'` sending `q` to `q'`, compatible with scalar extension and quotient towers. -/
def slabCorrespondenceHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q')
    {I J I' J' : Set ℤ} (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0)
    (hI' : I' ⊆ Set.Ici 0) (hJ' : J' ⊆ Set.Ici 0)
    (hII' : Set.MapsTo _root_.id I I') (hJJ' : Set.MapsTo _root_.id J J') :
    GradedCorrespondence.Hom ((slabCorrespondence q hI hJ).restrictScalars R)
      ((slabCorrespondence q' hI' hJ').restrictScalars R) _root_.id _root_.id where
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
    exact mapAlgHom_coeffLiftLinearMap φ hq (i : ℤ) _ _ (mapAlgHom_Z φ hq _) a
  middle_liftRight j a := by
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, slabCorrespondence,
      AlgHom.toLinearMap_apply, _root_.id]
    exact mapAlgHom_coeffLiftLinearMap φ hq (j : ℤ) _ _ (mapAlgHom_Z φ hq _) a

/-! ### Tangential monoid algebras `S[Λ]` and full-exponent correspondences on `S[ℤ × Λ]` -/

section Tangential

variable {S S' Λ : Type*} [CommRing S] [CommRing S'] [AddCommMonoid Λ]

/-- Left full-exponent chamber homomorphism
`NodeAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ)` sending
`single m s ↦ single (0, m) s` and `coord q 0 ↦ single (1, 0) 1`. -/
def leftTangentialMap (q : AddMonoidAlgebra S Λ) :
    NodeAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ) :=
  (AddMonoidAlgebra.curryAlgEquiv S).symm.toAlgHom.comp ((leftChamberMap q).restrictScalars S)

/-- Right full-exponent chamber homomorphism
`NodeAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ)` sending
`single m s ↦ single (0, m) s` and `coord q 1 ↦ single (1, 0) 1`. -/
def rightTangentialMap (q : AddMonoidAlgebra S Λ) :
    NodeAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ) :=
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

@[simp] theorem leftTangentialMap_coord_zero (q : AddMonoidAlgebra S Λ) :
    leftTangentialMap q (coord q 0) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    leftChamberMap_coord_zero]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 1 0 1

@[simp] theorem leftTangentialMap_coord_one (q : AddMonoidAlgebra S Λ) :
    leftTangentialMap q (coord q 1) = AddMonoidAlgebra.mapDomain (Prod.mk (-1 : ℤ)) q := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    leftChamberMap_coord_one, ← single_eq_C_mul_T]
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [AddMonoidAlgebra.single_add, map_add, AddMonoidAlgebra.mapDomain_add, hx, hy]
  | single m s =>
    rw [AddMonoidAlgebra.curryAlgEquiv_symm_single, AddMonoidAlgebra.mapDomain_single]

@[simp] theorem rightTangentialMap_coord_zero (q : AddMonoidAlgebra S Λ) :
    rightTangentialMap q (coord q 0) = AddMonoidAlgebra.mapDomain (Prod.mk (-1 : ℤ)) q := by
  rw [← leftTangentialMap_coord_one]; simp [rightTangentialMap, leftTangentialMap]

@[simp] theorem rightTangentialMap_coord_one (q : AddMonoidAlgebra S Λ) :
    rightTangentialMap q (coord q 1) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    rightChamberMap_coord_one]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single 1 0 1

theorem leftTangentialMap_algebraMap_single_mul_Z
    (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) (n : ℤ) :
    leftTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s) *
        Z q n) = (AddMonoidAlgebra.curryAlgEquiv S).symm
      (AddMonoidAlgebra.single (-n) (AddMonoidAlgebra.single m s * q ^ n.toNat)) := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    map_mul, AlgHom.commutes, leftChamberMap_Z, ← C_eq_algebraMap, ← mul_assoc, ← map_mul,
    ← single_eq_C_mul_T]

theorem rightTangentialMap_algebraMap_single_mul_Z
    (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) (n : ℤ) :
    rightTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s) *
        Z q n) = (AddMonoidAlgebra.curryAlgEquiv S).symm
      (AddMonoidAlgebra.single n (AddMonoidAlgebra.single m s * q ^ (-n).toNat)) := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    map_mul, AlgHom.commutes, rightChamberMap_Z, ← C_eq_algebraMap, ← mul_assoc, ← map_mul,
    ← single_eq_C_mul_T]

/-- Joint injectivity of the full-exponent chamber maps into `S[ℤ × Λ]` for arbitrary `q`. -/
theorem tangentialChamberProd_injective (q : AddMonoidAlgebra S Λ) :
    Function.Injective
      ((leftTangentialMap q).toLinearMap.prod (rightTangentialMap q).toLinearMap) :=
  fun _ _ huv => chamberProd_injective q <| Prod.ext
    ((AddMonoidAlgebra.curryAlgEquiv S).symm.injective (congrArg Prod.fst huv))
    ((AddMonoidAlgebra.curryAlgEquiv S).symm.injective (congrArg Prod.snd huv))

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
  · subst hq; simp [AddMonoidAlgebra.mapAlgHom_mapDomain]

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
  · subst hq; simp [AddMonoidAlgebra.mapAlgHom_mapDomain]

/-- Auxiliary `S`-linear lift reading the `p`-th coefficient in `S[ℤ × Λ]` and scaling a
tangential monomial times a slab basis element. -/
private def tangentialLiftLinearMap (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (z : NodeAlgebra (AddMonoidAlgebra S Λ) q) :
    AddMonoidAlgebra.grade S p →ₗ[S] NodeAlgebra (AddMonoidAlgebra S Λ) q :=
  ((LinearMap.smulRight LinearMap.id
      (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single p.2 1) * z)).comp
    ((Finsupp.lapply p).comp (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap)).comp
    (AddMonoidAlgebra.grade S p).subtype

private theorem tangentialLiftLinearMap_apply (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (z : NodeAlgebra (AddMonoidAlgebra S Λ) q) (a : AddMonoidAlgebra.grade S p) :
    tangentialLiftLinearMap q p z a = algebraMap (AddMonoidAlgebra S Λ) _
      (AddMonoidAlgebra.single p.2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff p)) * z := by
  simp only [tangentialLiftLinearMap, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lapply_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  rw [← smul_mul_assoc]; congr 1
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S (AddMonoidAlgebra S Λ),
    ← map_mul, ← Algebra.smul_def, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

private theorem tangentialMap_tangentialLiftLinearMap (q : AddMonoidAlgebra S Λ)
    (f : NodeAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] AddMonoidAlgebra S (ℤ × Λ))
    (p : ℤ × Λ) (z : NodeAlgebra (AddMonoidAlgebra S Λ) q)
    (hz : ∀ s : S,
      f (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single p.2 s) * z) =
        AddMonoidAlgebra.single p s) :
    f.toLinearMap.comp (tangentialLiftLinearMap q p z) = (AddMonoidAlgebra.grade S p).subtype :=
  LinearMap.ext fun a => by
    simp [tangentialLiftLinearMap_apply, hz,
      AddMonoidAlgebra.single_coeff_eq_of_mem_grade a.property]

/-- The `S`-linear full-exponent `GradedCorrespondence` across `NodeAlgebra S[Λ] q` on the monoid
algebras `S[ℤ × Λ]` graded by `AddMonoidAlgebra.grade S`, for admissible exponent sets
`I, J ⊆ {p : ℤ × Λ | 0 ≤ p.1}`. -/
def tangentialSlabCorrespondence (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    GradedCorrespondence (B := NodeAlgebra (AddMonoidAlgebra S Λ) q)
      (AddMonoidAlgebra.grade S) (AddMonoidAlgebra.grade S) I J where
  left := (leftTangentialMap q).toLinearMap
  right := (rightTangentialMap q).toLinearMap
  liftLeft i := tangentialLiftLinearMap q (i : ℤ × Λ) (Z q (-(i : ℤ × Λ).1))
  liftRight j := tangentialLiftLinearMap q (j : ℤ × Λ) (Z q (j : ℤ × Λ).1)
  left_liftLeft i := tangentialMap_tangentialLiftLinearMap q (leftTangentialMap q) (i : ℤ × Λ)
    (Z q (-(i : ℤ × Λ).1)) fun s => by
      simp only [leftTangentialMap_algebraMap_single_mul_Z, neg_neg,
        Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.val i.property)), pow_zero, mul_one,
        AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]
  right_liftRight j := tangentialMap_tangentialLiftLinearMap q (rightTangentialMap q) (j : ℤ × Λ)
    (Z q (j : ℤ × Λ).1) fun s => by
      simp only [rightTangentialMap_algebraMap_single_mul_Z,
        Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.val j.property)), pow_zero, mul_one,
        AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]

@[simp] theorem tangentialSlabCorrespondence_left (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (tangentialSlabCorrespondence q hI hJ).left = (leftTangentialMap q).toLinearMap := (rfl)

@[simp] theorem tangentialSlabCorrespondence_right (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (tangentialSlabCorrespondence q hI hJ).right = (rightTangentialMap q).toLinearMap := (rfl)

@[simp] theorem tangentialSlabCorrespondence_liftLeft_apply (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (a : AddMonoidAlgebra.grade S (i : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftLeft i a = algebraMap (AddMonoidAlgebra S Λ) _
      (AddMonoidAlgebra.single (i : ℤ × Λ).2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff i)) *
        Z q (-(i : ℤ × Λ).1) :=
  tangentialLiftLinearMap_apply q i (Z q (-(i : ℤ × Λ).1)) a

@[simp] theorem tangentialSlabCorrespondence_liftRight_apply (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (j : J) (a : AddMonoidAlgebra.grade S (j : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftRight j a = algebraMap (AddMonoidAlgebra S Λ) _
      (AddMonoidAlgebra.single (j : ℤ × Λ).2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff j)) *
        Z q (j : ℤ × Λ).1 :=
  tangentialLiftLinearMap_apply q j (Z q (j : ℤ × Λ).1) a

/-- Admissible left lifts of `tangentialSlabCorrespondence` preserve products, supplying the
multiplicativity hypothesis of `GradedCorrespondence.transfer_mul`. -/
theorem tangentialSlabCorrespondence_liftLeft_mul (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i₁ i₂ : I) (hi : (i₁ : ℤ × Λ) + (i₂ : ℤ × Λ) ∈ I)
    (a₁ : AddMonoidAlgebra.grade S (i₁ : ℤ × Λ))
    (a₂ : AddMonoidAlgebra.grade S (i₂ : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftLeft
        ⟨(i₁ : ℤ × Λ) + (i₂ : ℤ × Λ), hi⟩
        ⟨(a₁ : AddMonoidAlgebra S (ℤ × Λ)) * (a₂ : AddMonoidAlgebra S (ℤ × Λ)),
          SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (tangentialSlabCorrespondence q hI hJ).liftLeft i₁ a₁ *
        (tangentialSlabCorrespondence q hI hJ).liftLeft i₂ a₂ := by
  simp only [tangentialSlabCorrespondence_liftLeft_apply,
    AddMonoidAlgebra.coeff_mul_of_mem_grade a₁.property a₂.property, Prod.snd_add, Prod.fst_add,
    neg_add, ← AddMonoidAlgebra.single_mul_single, map_mul]
  rw [Z_add_eq_mul_of_same_sign q (Or.inr ⟨neg_nonpos.mpr (hI i₁.val i₁.property),
    neg_nonpos.mpr (hI i₂.val i₂.property)⟩)]; ring

/-- Admissible right lifts of `tangentialSlabCorrespondence` preserve products, supplying the
parallel multiplicativity hypothesis for reverse crossing. -/
theorem tangentialSlabCorrespondence_liftRight_mul (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (j₁ j₂ : J) (hj : (j₁ : ℤ × Λ) + (j₂ : ℤ × Λ) ∈ J)
    (a₁ : AddMonoidAlgebra.grade S (j₁ : ℤ × Λ))
    (a₂ : AddMonoidAlgebra.grade S (j₂ : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftRight
        ⟨(j₁ : ℤ × Λ) + (j₂ : ℤ × Λ), hj⟩
        ⟨(a₁ : AddMonoidAlgebra S (ℤ × Λ)) * (a₂ : AddMonoidAlgebra S (ℤ × Λ)),
          SetLike.mul_mem_graded a₁.property a₂.property⟩ =
      (tangentialSlabCorrespondence q hI hJ).liftRight j₁ a₁ *
        (tangentialSlabCorrespondence q hI hJ).liftRight j₂ a₂ := by
  simp only [tangentialSlabCorrespondence_liftRight_apply,
    AddMonoidAlgebra.coeff_mul_of_mem_grade a₁.property a₂.property, Prod.snd_add, Prod.fst_add,
    ← AddMonoidAlgebra.single_mul_single, map_mul]
  rw [Z_add_eq_mul_of_same_sign q
    (Or.inl ⟨hJ j₁.val j₁.property, hJ j₂.val j₂.property⟩)]; ring

private theorem tangential_transfer_single_aux {G : Type*} [AddCommGroup G] [DecidableEq G]
    (q : AddMonoidAlgebra S G) {I J : Set (ℤ × G)}
    (c : GradedCorrespondence (B := NodeAlgebra (AddMonoidAlgebra S G) q)
      (AddMonoidAlgebra.grade S) (AddMonoidAlgebra.grade S) I J)
    (i : I) (s : S) (k : ℤ) (m' : G)
    (himg : c.right (c.liftLeft i ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
        AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩) =
      (AddMonoidAlgebra.curryAlgEquiv S).symm (AddMonoidAlgebra.single (-(i : ℤ × G).1)
        (AddMonoidAlgebra.single (i : ℤ × G).2 s * q ^ (i : ℤ × G).1.natAbs))) :
    (c.transfer i (k, m') ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
        AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩ : AddMonoidAlgebra S (ℤ × G)) =
      if -(i : ℤ × G).1 = k then AddMonoidAlgebra.single (-(i : ℤ × G).1, m')
        (s * (q ^ (i : ℤ × G).1.natAbs).coeff (m' - (i : ℤ × G).2)) else 0 := by
  rw [GradedCorrespondence.transfer_apply, himg,
    AddMonoidAlgebra.decompose_grade_curryAlgEquiv_symm_single]
  split_ifs with hk <;> [simp [sub_eq_neg_add]; rfl]

/-- Explicit homogeneous transfer of an incoming left monomial `single (d, m) s` across
`tangentialSlabCorrespondence`, expressed in terms of the tangential expansion of `q ^ d.natAbs`:
when `Λ` is an additive commutative group, the `(k, m')`-transfer is
`single (-d, m') (s * (q ^ d.natAbs).coeff (m' - m))` for `k = -d` and `0` otherwise. -/
theorem tangentialSlabCorrespondence_transfer_single
    {G : Type*} [AddCommGroup G] [DecidableEq G] (q : AddMonoidAlgebra S G)
    {I J : Set (ℤ × G)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (s : S) (k : ℤ) (m' : G) :
    ((tangentialSlabCorrespondence q hI hJ).transfer i (k, m')
        ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
          AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩ : AddMonoidAlgebra S (ℤ × G)) =
      if -(i : ℤ × G).1 = k then AddMonoidAlgebra.single (-(i : ℤ × G).1, m')
        (s * (q ^ (i : ℤ × G).1.natAbs).coeff (m' - (i : ℤ × G).2)) else 0 :=
  tangential_transfer_single_aux q (tangentialSlabCorrespondence q hI hJ) i s k m' <| by
    have hi : (i : ℤ × G).1.toNat = (i : ℤ × G).1.natAbs := by
      have := hI i.val i.property; omega
    simp [rightTangentialMap_algebraMap_single_mul_Z, hi]

/-- Explicit left-chamber reverse transfer of an incoming right monomial `single (d, m) s` across
`(tangentialSlabCorrespondence q hI hJ).symm`. -/
theorem tangentialSlabCorrespondence_symm_transfer_single
    {G : Type*} [AddCommGroup G] [DecidableEq G] (q : AddMonoidAlgebra S G)
    {I J : Set (ℤ × G)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (j : J) (s : S) (k : ℤ) (m' : G) :
    ((tangentialSlabCorrespondence q hI hJ).symm.transfer j (k, m')
        ⟨AddMonoidAlgebra.single (j : ℤ × G) s,
          AddMonoidAlgebra.single_mem_grade (j : ℤ × G) s⟩ : AddMonoidAlgebra S (ℤ × G)) =
      if -(j : ℤ × G).1 = k then AddMonoidAlgebra.single (-(j : ℤ × G).1, m')
        (s * (q ^ (j : ℤ × G).1.natAbs).coeff (m' - (j : ℤ × G).2)) else 0 :=
  tangential_transfer_single_aux q (tangentialSlabCorrespondence q hI hJ).symm j s k m' <| by
    have hj : (j : ℤ × G).1.toNat = (j : ℤ × G).1.natAbs := by
      have := hJ j.val j.property; omega
    simp [leftTangentialMap_algebraMap_single_mul_Z, hj]

private theorem mapAlgHom_tangentialLiftLinearMap [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq' : ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) q = q')
    (p : ℤ × Λ) (z : NodeAlgebra (AddMonoidAlgebra S Λ) q)
    (z' : NodeAlgebra (AddMonoidAlgebra S' Λ) q')
    (hz : mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq' z = z')
    (a : (AddMonoidAlgebra.grade S p).restrictScalars R) :
    mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq'
        (tangentialLiftLinearMap q p z ⟨a.val, a.property⟩) =
      tangentialLiftLinearMap q' p z' ⟨AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ a.val,
        AddMonoidAlgebra.mapAlgHom_mem_grade φ
          ((Submodule.restrictScalars_mem R _ _).mp a.property)⟩ := by
  rw [tangentialLiftLinearMap_apply, tangentialLiftLinearMap_apply,
    AddMonoidAlgebra.coeff_mapAlgHom, map_mul, mapAlgHom_algebraMap, hz]; simp

/-- Functorial `R`-linear morphism of full-exponent tangential slab correspondences along an
`R`-algebra homomorphism `φ : S →ₐ[R] S'` (covering scalar extensions and quotient towers). -/
def tangentialSlabCorrespondenceHom [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq : AddMonoidAlgebra.mapAlgHom Λ φ q = q')
    {I J I' J' : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (hI' : ∀ p ∈ I', 0 ≤ p.1) (hJ' : ∀ p ∈ J', 0 ≤ p.1)
    (hII' : Set.MapsTo _root_.id I I') (hJJ' : Set.MapsTo _root_.id J J') :
    GradedCorrespondence.Hom ((tangentialSlabCorrespondence q hI hJ).restrictScalars R)
      ((tangentialSlabCorrespondence q' hI' hJ').restrictScalars R) _root_.id _root_.id where
  middle := (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
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
    simp only [GradedCorrespondence.restrictScalars_liftLeft_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact mapAlgHom_tangentialLiftLinearMap φ _ i.val _ _ (mapAlgHom_Z _ _ _) a
  middle_liftRight j a := by
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact mapAlgHom_tangentialLiftLinearMap φ _ j.val _ _ (mapAlgHom_Z _ _ _) a

end Tangential

end NodeAlgebra

end TauCeti
