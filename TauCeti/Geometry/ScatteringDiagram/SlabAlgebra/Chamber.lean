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
public import TauCeti.LinearAlgebra.GradedCorrespondence.Multiplication
public import TauCeti.LinearAlgebra.GradedCorrespondence.RestrictScalars

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
coefficients in terms of the tangential expansion of `q^a`, naturality in `(S, q)`, and the
binomial wall-crossing formula for `q = t (1 + w)` in `S[w, w⁻¹]`.

## Main definitions and results

* `TauCeti.SlabAlgebra.leftChamberMap`, `TauCeti.SlabAlgebra.rightChamberMap`: the left and right
  chamber Laurent homomorphisms `SlabAlgebra B q →ₐ[B] B[T;T⁻¹]`.
* `TauCeti.SlabAlgebra.coeff_leftChamberMap`, `TauCeti.SlabAlgebra.coeff_rightChamberMap`,
  `TauCeti.SlabAlgebra.chamberProd_injective`: Laurent coefficient formulas and joint injectivity.
* `TauCeti.SlabAlgebra.slabCorrespondence`, `TauCeti.SlabAlgebra.slabCorrespondenceHom`: the
  `B`-linear graded correspondence across a slab and its functoriality.
* `TauCeti.SlabAlgebra.leftTangentialMap`, `TauCeti.SlabAlgebra.rightTangentialMap`,
  `TauCeti.SlabAlgebra.tangentialSlabCorrespondence`,
  `TauCeti.SlabAlgebra.tangentialSlabCorrespondence_transfer_single`: full-exponent chamber maps,
  graded correspondence on `S[ℤ × Λ]`, and tangential expansion of homogeneous transfers.
* `TauCeti.SlabAlgebra.rightChamberMap_binomial`: binomial expansion of `w^b X^a` in the right
  chamber for `q = t (1 + w)` in `S[w, w⁻¹]`.

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
@[simp]
theorem leftChamberMap_Z (q : B) (n : ℤ) :
    leftChamberMap q (Z q n) = C (q ^ n.toNat) * T (-n) := by
  rw [leftChamberMap, lift_Z]
  split_ifs with hn
  · rw [T_pow, mul_one, show (n.natAbs : ℤ) = -n by omega, Int.toNat_of_nonpos hn.le,
      pow_zero, map_one, one_mul]
  · rw [mul_pow, ← map_pow, T_pow, show (n.natAbs : ℤ) * (-1) = -n by omega,
      show n.toNat = n.natAbs by omega]

/-- In the right chamber, the normal-form basis element `Z q n` maps to
`C (q ^ (-n).toNat) * T n`. -/
@[simp]
theorem rightChamberMap_Z (q : B) (n : ℤ) :
    rightChamberMap q (Z q n) = C (q ^ (-n).toNat) * T n := by
  rw [rightChamberMap, lift_Z]
  split_ifs with hn
  · rw [mul_pow, ← map_pow, T_pow, show (n.natAbs : ℤ) * (-1) = n by omega,
      show (-n).toNat = n.natAbs by omega]
  · rw [T_pow, mul_one, show (n.natAbs : ℤ) = n by omega,
      Int.toNat_of_nonpos (by omega), pow_zero, map_one, one_mul]

/-- The `k`-th Laurent coefficient of `leftChamberMap q u` is the `(-k)`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_leftChamberMap (q : B) (u : SlabAlgebra B q) (k : ℤ) :
    (leftChamberMap q u).coeff k = ((slabBasis q).repr u (-k)) * q ^ (-k).toNat := by
  induction u using DirectSum.Decomposition.inductionOn (weightSubmodule q) with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | @homogeneous m x =>
    obtain ⟨b, hb⟩ := (mem_weightSubmodule_iff q m x.1).mp x.2
    rw [← hb, map_smul, map_smul, leftChamberMap_Z, slabBasis_repr_Z, ← single_eq_C_mul_T,
      AddMonoidAlgebra.smul_single, smul_eq_mul, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : -m = k
    · simp [show m = -k by omega]
    · simp [h, show ¬ m = -k by omega]

/-- The `k`-th Laurent coefficient of `rightChamberMap q u` is the `k`-th slab basis coordinate
multiplied by `q ^ (-k).toNat`. -/
theorem coeff_rightChamberMap (q : B) (u : SlabAlgebra B q) (k : ℤ) :
    (rightChamberMap q u).coeff k = ((slabBasis q).repr u k) * q ^ (-k).toNat := by
  induction u using DirectSum.Decomposition.inductionOn (weightSubmodule q) with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | @homogeneous m x =>
    obtain ⟨b, hb⟩ := (mem_weightSubmodule_iff q m x.1).mp x.2
    rw [← hb, map_smul, map_smul, rightChamberMap_Z, slabBasis_repr_Z, ← single_eq_C_mul_T,
      AddMonoidAlgebra.smul_single, smul_eq_mul, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne m k with rfl | h <;> simp [*]

@[simp]
theorem coeff_leftChamberMap_natCast (q : B) (u : SlabAlgebra B q) (a : ℕ) :
    (leftChamberMap q u).coeff (a : ℤ) = (slabBasis q).repr u (-(a : ℤ)) := by
  rw [coeff_leftChamberMap, Int.toNat_of_nonpos (by omega), pow_zero, mul_one]

@[simp]
theorem coeff_rightChamberMap_natCast (q : B) (u : SlabAlgebra B q) (a : ℕ) :
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
  · rw [show n = -(n.natAbs : ℤ) by omega, ← coeff_leftChamberMap_natCast,
      ← coeff_leftChamberMap_natCast, hL]
  · rw [show n = (n.natAbs : ℤ) by omega, ← coeff_rightChamberMap_natCast,
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

private theorem single_coeff_of_mem_grade {S M : Type*} [CommSemiring S]
    {m : M} {x : AddMonoidAlgebra S M} (hx : x ∈ AddMonoidAlgebra.grade S m) :
    AddMonoidAlgebra.single m (x.coeff m) = x := by
  obtain ⟨s, rfl⟩ := (AddMonoidAlgebra.mem_grade_iff' S m x).mp hx
  simp [AddMonoidAlgebra.lsingle_apply]

private theorem mapAlgHom_mem_grade {R S S' M : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring S'] [Algebra R S] [Algebra R S'] [AddCommMonoid M]
    (φ : S →ₐ[R] S') (m : M) (x : AddMonoidAlgebra S M)
    (hx : x ∈ (AddMonoidAlgebra.grade S m).restrictScalars R) :
    AddMonoidAlgebra.mapAlgHom M φ x ∈ (AddMonoidAlgebra.grade S' m).restrictScalars R := by
  rw [Submodule.restrictScalars_mem, ← single_coeff_of_mem_grade hx,
    AddMonoidAlgebra.mapAlgHom_single]
  exact AddMonoidAlgebra.single_mem_grade m _

/-- Auxiliary `B`-linear map reading the `k`-th Laurent coefficient and scaling a slab element. -/
private def coeffLiftLinearMap (q : B) (k : ℤ) (z : SlabAlgebra B q) :
    AddMonoidAlgebra.grade B k →ₗ[B] SlabAlgebra B q :=
  ((LinearMap.smulRight (1 : B →ₗ[B] B) z).comp
    ((Finsupp.lapply k).comp (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap)).comp
    (AddMonoidAlgebra.grade B k).subtype

@[simp]
private theorem coeffLiftLinearMap_apply (q : B) (k : ℤ) (z : SlabAlgebra B q)
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
      Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.2)), pow_zero, map_one, one_mul,
      Algebra.smul_def, ← C_eq_algebraMap, ← single_eq_C_mul_T]
    exact single_coeff_of_mem_grade a.2
  right_liftRight j := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coeffLiftLinearMap_apply,
      Submodule.subtype_apply, map_smul, rightChamberMap_Z,
      Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.2)), pow_zero, map_one, one_mul,
      Algebra.smul_def, ← C_eq_algebraMap, ← single_eq_C_mul_T]
    exact single_coeff_of_mem_grade a.2

@[simp]
theorem slabCorrespondence_liftLeft_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (i : I)
    (a : AddMonoidAlgebra.grade B (i : ℤ)) :
    (slabCorrespondence q hI hJ).liftLeft i a =
      ((a : B[T;T⁻¹]).coeff (i : ℤ)) • X q ^ (i : ℤ).natAbs := by
  have hi : 0 ≤ (i : ℤ) := hI i.property
  rw [slabCorrespondence, coeffLiftLinearMap_apply,
    show -(i : ℤ) = -((i : ℤ).natAbs : ℤ) by omega, Z_neg_natCast]

@[simp]
theorem slabCorrespondence_liftRight_apply (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) (j : J)
    (a : AddMonoidAlgebra.grade B (j : ℤ)) :
    (slabCorrespondence q hI hJ).liftRight j a =
      ((a : B[T;T⁻¹]).coeff (j : ℤ)) • Y q ^ (j : ℤ).natAbs := by
  have hj : 0 ≤ (j : ℤ) := hJ j.property
  rw [slabCorrespondence, coeffLiftLinearMap_apply, Z_of_nonneg q hj]

/-- The two chamber legs of `slabCorrespondence` are jointly injective for arbitrary `q`. -/
theorem slabCorrespondence_injective (q : B) {I J : Set ℤ}
    (hI : I ⊆ Set.Ici 0) (hJ : J ⊆ Set.Ici 0) :
    Function.Injective
      ((slabCorrespondence q hI hJ).left.prod (slabCorrespondence q hI hJ).right) :=
  chamberProd_injective q

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
  have h1 : 0 ≤ (i₁ : ℤ) := hI i₁.property
  have h2 : 0 ≤ (i₂ : ℤ) := hI i₂.property
  have hcoeff : ((a₁ : B[T;T⁻¹]) * (a₂ : B[T;T⁻¹])).coeff ((i₁ : ℤ) + (i₂ : ℤ)) =
      (a₁ : B[T;T⁻¹]).coeff (i₁ : ℤ) * (a₂ : B[T;T⁻¹]).coeff (i₂ : ℤ) := by
    conv_lhs => rw [← single_coeff_of_mem_grade a₁.2, ← single_coeff_of_mem_grade a₂.2]
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  rw [slabCorrespondence_liftLeft_apply, slabCorrespondence_liftLeft_apply,
    slabCorrespondence_liftLeft_apply, hcoeff,
    show ((i₁ : ℤ) + (i₂ : ℤ)).natAbs = (i₁ : ℤ).natAbs + (i₂ : ℤ).natAbs by omega,
    pow_add, smul_mul_smul_comm]

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
    rw [slabCorrespondence_liftLeft_apply, hc]
    simp only [slabCorrespondence, AlgHom.toLinearMap_apply]
    rw [map_smul, map_pow, rightChamberMap_X, mul_pow, ← map_pow, T_pow,
      show ((i : ℤ).natAbs : ℤ) * (-1) = -(i : ℤ) by omega,
      Algebra.smul_def, ← C_eq_algebraMap, ← mul_assoc, ← map_mul]
  rw [GradedCorrespondence.transfer_apply, himg, ← single_eq_C_mul_T,
    AddMonoidAlgebra.grade.decompose_single, DirectSum.coe_of_apply]
  split_ifs <;> simp [single_eq_C_mul_T]

private theorem mapAlgHom_coeffLiftLinearMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q')
    (k : ℤ) (z : SlabAlgebra B q) (z' : SlabAlgebra B' q') (hz : mapAlgHom φ hq z = z')
    (a : (AddMonoidAlgebra.grade B k).restrictScalars R) :
    ∃ hmem : AddMonoidAlgebra.mapAlgHom ℤ φ a.1 ∈ AddMonoidAlgebra.grade B' k,
      mapAlgHom φ hq (coeffLiftLinearMap q k z ⟨a.1, a.2⟩) =
        coeffLiftLinearMap q' k z' ⟨AddMonoidAlgebra.mapAlgHom ℤ φ a.1, hmem⟩ := by
  have ha : (a : B[T;T⁻¹]) ∈ AddMonoidAlgebra.grade B k := a.property
  obtain ⟨b, hb⟩ := (AddMonoidAlgebra.mem_grade_iff' B k a.1).mp ha
  refine ⟨mapAlgHom_mem_grade φ k a.1 a.2, ?_⟩
  have hc1 : (a : B[T;T⁻¹]).coeff k = b := by
    rw [← hb, AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  have hc2 : ((AddMonoidAlgebra.mapAlgHom ℤ φ) (a : B[T;T⁻¹])).coeff k = φ b := by
    rw [← hb, AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.mapAlgHom_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  rw [coeffLiftLinearMap_apply, coeffLiftLinearMap_apply, hc1, hc2, Algebra.smul_def b z,
    map_mul, mapAlgHom_algebraMap, hz, ← Algebra.smul_def (φ b) z']

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
    simpa [slabCorrespondence] using AlgHom.congr_fun (mapAlgHom_comp_leftChamberMap φ hq) u
  right_comm := LinearMap.ext fun u => by
    simpa [slabCorrespondence] using AlgHom.congr_fun (mapAlgHom_comp_rightChamberMap φ hq) u
  left_mem := mapAlgHom_mem_grade φ
  right_mem := mapAlgHom_mem_grade φ
  admissible_left := hII'
  admissible_right := hJJ'
  middle_liftLeft i a := by
    obtain ⟨_, hEq⟩ := mapAlgHom_coeffLiftLinearMap φ hq (i : ℤ)
      (Z q (-(i : ℤ))) (Z q' (-(i : ℤ))) (mapAlgHom_Z φ hq _) a
    simp only [GradedCorrespondence.restrictScalars_liftLeft_apply, slabCorrespondence,
      AlgHom.toLinearMap_apply, _root_.id]
    exact hEq
  middle_liftRight j a := by
    obtain ⟨_, hEq⟩ := mapAlgHom_coeffLiftLinearMap φ hq (j : ℤ)
      (Z q (j : ℤ)) (Z q' (j : ℤ)) (mapAlgHom_Z φ hq _) a
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, slabCorrespondence,
      AlgHom.toLinearMap_apply, _root_.id]
    exact hEq

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

@[simp]
theorem leftTangentialMap_algebraMap_single (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) :
    leftTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s)) =
      AddMonoidAlgebra.single (0, m) s := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    AlgHom.commutes, ← C_eq_algebraMap]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single (0 : ℤ) m s

@[simp]
theorem rightTangentialMap_algebraMap_single (q : AddMonoidAlgebra S Λ) (m : Λ) (s : S) :
    rightTangentialMap q (algebraMap (AddMonoidAlgebra S Λ) _ (AddMonoidAlgebra.single m s)) =
      AddMonoidAlgebra.single (0, m) s := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    AlgHom.commutes, ← C_eq_algebraMap]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single (0 : ℤ) m s

@[simp]
theorem leftTangentialMap_X (q : AddMonoidAlgebra S Λ) :
    leftTangentialMap q (X q) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    leftChamberMap_X]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single (1 : ℤ) (0 : Λ) (1 : S)

@[simp]
theorem rightTangentialMap_Y (q : AddMonoidAlgebra S Λ) :
    rightTangentialMap q (Y q) = AddMonoidAlgebra.single (1, 0) 1 := by
  rw [rightTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply,
    rightChamberMap_Y]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single (1 : ℤ) (0 : Λ) (1 : S)

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
    LinearEquiv.coe_coe, Finsupp.lapply_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
  have hcoe : (AddMonoidAlgebra.coeffLinearEquiv S) (a : AddMonoidAlgebra S (ℤ × Λ)) =
      (a : AddMonoidAlgebra S (ℤ × Λ)).coeff := (rfl)
  have hsmul (r : S) (x : AddMonoidAlgebra S Λ) :
      r • algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q) x =
        algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q) (r • x) :=
    (LinearMap.map_smul_of_tower
      (Algebra.linearMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)) r x).symm
  rw [hcoe, ← smul_mul_assoc, hsmul, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

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
      neg_neg, Int.toNat_of_nonpos (neg_nonpos.mpr (hI i.1 i.2)), pow_zero, mul_one,
      AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]
    exact single_coeff_of_mem_grade a.2
  right_liftRight j := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply,
      tangentialLiftLinearMap_apply, rightTangentialMap_algebraMap_single_mul_Z,
      Int.toNat_of_nonpos (neg_nonpos.mpr (hJ j.1 j.2)), pow_zero, mul_one,
      AddMonoidAlgebra.curryAlgEquiv_symm_single, Prod.mk.eta]
    exact single_coeff_of_mem_grade a.2

@[simp]
theorem tangentialSlabCorrespondence_liftLeft_apply (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (a : AddMonoidAlgebra.grade S (i : ℤ × Λ)) :
    (tangentialSlabCorrespondence q hI hJ).liftLeft i a =
      algebraMap (AddMonoidAlgebra S Λ) _
        (AddMonoidAlgebra.single (i : ℤ × Λ).2 ((a : AddMonoidAlgebra S (ℤ × Λ)).coeff i)) *
        Z q (-(i : ℤ × Λ).1) :=
  tangentialLiftLinearMap_apply q i (Z q (-(i : ℤ × Λ).1)) a

@[simp]
theorem tangentialSlabCorrespondence_liftRight_apply (q : AddMonoidAlgebra S Λ)
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
  have hi : 0 ≤ (i : ℤ × G).1 := hI i.1 i.property
  have hto : (i : ℤ × G).1.toNat = (i : ℤ × G).1.natAbs := by omega
  let f : AddMonoidAlgebra S G :=
    AddMonoidAlgebra.single (i : ℤ × G).2 s * q ^ (i : ℤ × G).1.natAbs
  have hcur : (AddMonoidAlgebra.curryAlgEquiv S).symm
      (AddMonoidAlgebra.single (-(i : ℤ × G).1) f) =
      ∑ m₀ ∈ f.coeff.support, AddMonoidAlgebra.single (-(i : ℤ × G).1, m₀) (f.coeff m₀) := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
    rw [Finsupp.sum, ← AddMonoidAlgebra.lsingle_apply (R := ℕ), map_sum, map_sum]
    exact Finset.sum_congr rfl fun _ _ => AddMonoidAlgebra.curryAlgEquiv_symm_single _ _ _
  have himg : (tangentialSlabCorrespondence q hI hJ).right
      ((tangentialSlabCorrespondence q hI hJ).liftLeft i
        ⟨AddMonoidAlgebra.single (i : ℤ × G) s,
          AddMonoidAlgebra.single_mem_grade (i : ℤ × G) s⟩) =
      ∑ m₀ ∈ f.coeff.support, AddMonoidAlgebra.single (-(i : ℤ × G).1, m₀) (f.coeff m₀) := by
    rw [tangentialSlabCorrespondence_liftLeft_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
    simp only [tangentialSlabCorrespondence, AlgHom.toLinearMap_apply,
      rightTangentialMap_algebraMap_single_mul_Z, neg_neg, hto]
    exact hcur
  rw [GradedCorrespondence.transfer_apply, himg, DirectSum.decompose_sum, DirectSum.sum_apply,
    AddSubmonoidClass.coe_finsetSum]
  by_cases hk : -(i : ℤ × G).1 = k
  · subst hk
    simp only [↓reduceIte]
    by_cases hm' : m' ∈ f.coeff.support
    · rw [Finset.sum_eq_single m']
      · rw [DirectSum.decompose_of_mem_same (AddMonoidAlgebra.grade S (M := ℤ × G))
          (AddMonoidAlgebra.single_mem_grade (-(i : ℤ × G).1, m') (f.coeff m'))]
        simp [f, sub_eq_neg_add]
      · exact fun _ _ hm₀ => DirectSum.decompose_of_mem_ne _
          (AddMonoidAlgebra.single_mem_grade _ _) fun h => hm₀ (Prod.mk.inj h).2
      · exact fun h => absurd hm' h
    · rw [Finset.sum_eq_zero]
      · have h0 : s * (q ^ (i : ℤ × G).1.natAbs).coeff (m' - (i : ℤ × G).2) = 0 := by
          simpa [f, sub_eq_neg_add] using Finsupp.notMem_support_iff.mp hm'
        rw [h0, AddMonoidAlgebra.single_zero]
      · exact fun _ hm₀ => DirectSum.decompose_of_mem_ne _
          (AddMonoidAlgebra.single_mem_grade _ _) fun h => hm' ((Prod.mk.inj h).2 ▸ hm₀)
  · simp only [hk, ↓reduceIte]
    exact Finset.sum_eq_zero fun _ _ => DirectSum.decompose_of_mem_ne _
      (AddMonoidAlgebra.single_mem_grade _ _) fun h => hk (Prod.mk.inj h).1

private theorem mapAlgHom_tangentialLiftLinearMap [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (hq' : ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) q = q')
    (p : ℤ × Λ) (z : SlabAlgebra (AddMonoidAlgebra S Λ) q)
    (z' : SlabAlgebra (AddMonoidAlgebra S' Λ) q')
    (hz : mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq' z = z')
    (a : (AddMonoidAlgebra.grade S p).restrictScalars R) :
    ∃ hmem : AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ a.1 ∈ AddMonoidAlgebra.grade S' p,
      mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R) hq'
        (tangentialLiftLinearMap q p z ⟨a.1, a.2⟩) =
        tangentialLiftLinearMap q' p z' ⟨AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ a.1, hmem⟩ := by
  have ha : (a : AddMonoidAlgebra S (ℤ × Λ)) ∈ AddMonoidAlgebra.grade S p := a.property
  refine ⟨mapAlgHom_mem_grade φ p a.1 a.2, ?_⟩
  have hc : ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ) a.1).coeff p = φ (a.1.coeff p) := by
    conv_lhs => rw [← single_coeff_of_mem_grade ha, AddMonoidAlgebra.mapAlgHom_single]
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  rw [tangentialLiftLinearMap_apply, tangentialLiftLinearMap_apply, hc,
    map_mul, mapAlgHom_algebraMap, hz]
  simp

private theorem mapAlgHom_leftTangentialMap_Y [CommSemiring R] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (q : AddMonoidAlgebra S Λ) :
    AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ (leftTangentialMap q (Y q)) =
      leftTangentialMap (AddMonoidAlgebra.mapAlgHom Λ φ q)
        (Y (AddMonoidAlgebra.mapAlgHom Λ φ q)) := by
  simp only [leftTangentialMap, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgHom.restrictScalars_apply, leftChamberMap_Y]
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, add_mul, map_add, map_add, hx, hy, map_add, map_add, add_mul, map_add]
  | single m s =>
    simp only [AddMonoidAlgebra.mapAlgHom_single, ← single_eq_C_mul_T,
      AddMonoidAlgebra.curryAlgEquiv_symm_single]

private theorem rightTangentialMap_X_eq_leftTangentialMap_Y {S₀ : Type*} [CommRing S₀]
    (q₀ : AddMonoidAlgebra S₀ Λ) :
    rightTangentialMap q₀ (X q₀) = leftTangentialMap q₀ (Y q₀) := by
  simp [rightTangentialMap, leftTangentialMap]

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
  left_comm := by
    have hAlg : ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).comp
        ((leftTangentialMap q).restrictScalars R) =
      ((leftTangentialMap q').restrictScalars R).comp
        (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
          ((AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq)) := by
      refine algHom_ext_of_algebra (fun b => ?_) (by simp) (by
        cases hq; simp [mapAlgHom_leftTangentialMap_Y φ q])
      induction b using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | single m s => simp
    exact LinearMap.ext fun u => by
      simpa [tangentialSlabCorrespondence] using AlgHom.congr_fun hAlg u
  right_comm := by
    have hAlg : ((AddMonoidAlgebra.mapAlgHom (ℤ × Λ) φ).restrictScalars R).comp
        ((rightTangentialMap q).restrictScalars R) =
      ((rightTangentialMap q').restrictScalars R).comp
        (mapAlgHom ((AddMonoidAlgebra.mapAlgHom Λ φ).restrictScalars R)
          ((AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq)) := by
      refine algHom_ext_of_algebra (fun b => ?_) (by
        cases hq; simp [rightTangentialMap_X_eq_leftTangentialMap_Y,
          mapAlgHom_leftTangentialMap_Y φ q]) (by simp)
      induction b using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | single m s => simp
    exact LinearMap.ext fun u => by
      simpa [tangentialSlabCorrespondence] using AlgHom.congr_fun hAlg u
  left_mem := mapAlgHom_mem_grade φ
  right_mem := mapAlgHom_mem_grade φ
  admissible_left := hII'
  admissible_right := hJJ'
  middle_liftLeft i a := by
    have hq' := (AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq
    obtain ⟨_, hEq⟩ := mapAlgHom_tangentialLiftLinearMap φ hq' i.1
      (Z q (-i.1.1)) (Z q' (-i.1.1)) (mapAlgHom_Z _ hq' _) a
    simp only [GradedCorrespondence.restrictScalars_liftLeft_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact hEq
  middle_liftRight j a := by
    have hq' := (AlgHom.restrictScalars_apply R (AddMonoidAlgebra.mapAlgHom Λ φ) q).trans hq
    obtain ⟨_, hEq⟩ := mapAlgHom_tangentialLiftLinearMap φ hq' j.1
      (Z q j.1.1) (Z q' j.1.1) (mapAlgHom_Z _ hq' _) a
    simp only [GradedCorrespondence.restrictScalars_liftRight_apply, tangentialSlabCorrespondence,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, _root_.id]
    exact hEq

/-! ### Binomial wall-crossing expansion for `q = t (1 + w)` -/

/-- In the slab algebra `S[w, w⁻¹][X, Y] / (X Y - t (1 + w))` (with `w = T 1` in `S[T;T⁻¹]`
and `y = T 1` in `(S[T;T⁻¹])[T;T⁻¹]`), the incoming left monomial `X^a w^b` maps in the right
chamber to `t^a y^{-a} ∑_{j=0}^a binom(a, j) w^{b + j}`. -/
theorem rightChamberMap_binomial (t : S) (a : ℕ) (b : ℤ) :
    let q : S[T;T⁻¹] := C t * (1 + T 1)
    rightChamberMap q (X q ^ a * algebraMap S[T;T⁻¹] (SlabAlgebra S[T;T⁻¹] q) (T b)) =
      C (C (t ^ a)) * T (-(a : ℤ)) *
        ∑ j ∈ Finset.range (a + 1),
          (a.choose j : (S[T;T⁻¹])[T;T⁻¹]) * C (T (b + j)) := by
  intro q
  have h1T : (1 + T 1 : S[T;T⁻¹]) ^ a * T b =
      ∑ j ∈ Finset.range (a + 1), (a.choose j : S[T;T⁻¹]) * T (b + j) := by
    rw [add_comm (1 : S[T;T⁻¹]) (T 1), add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, T_pow, mul_one, mul_comm _ (a.choose j : S[T;T⁻¹]), mul_assoc,
      ← T_add, add_comm (j : ℤ) b]
  calc rightChamberMap q (X q ^ a * algebraMap S[T;T⁻¹] (SlabAlgebra S[T;T⁻¹] q) (T b))
      = C (C (t ^ a) * ((1 + T 1 : S[T;T⁻¹]) ^ a * T b)) * T (-(a : ℤ)) := by
        rw [map_mul, map_pow, rightChamberMap_X, AlgHom.commutes, ← C_eq_algebraMap, mul_pow,
          T_pow, show (a : ℤ) * (-1) = -(a : ℤ) by omega,
          mul_right_comm (C q ^ a) (T (-(a : ℤ))) (C (T b)), ← map_pow, ← map_mul]
        simp [q, mul_pow, mul_assoc]
    _ = C (C (t ^ a)) * T (-(a : ℤ)) *
          ∑ j ∈ Finset.range (a + 1),
            (a.choose j : (S[T;T⁻¹])[T;T⁻¹]) * C (T (b + j)) := by
        rw [h1T, map_mul, map_sum, mul_right_comm]
        exact congrArg _ (Finset.sum_congr rfl fun _ _ => by rw [map_mul, map_natCast])

end Tangential

end SlabAlgebra

end TauCeti
