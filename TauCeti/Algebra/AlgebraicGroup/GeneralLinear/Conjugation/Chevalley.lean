/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.Invariants
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Restriction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.LinearAlgebra.Matrix.Charpoly.Discriminant
import TauCeti.LinearAlgebra.Matrix.Charpoly.Separable
import TauCeti.RingTheory.MvPolynomial.Symmetric.Vieta
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Chevalley restriction for `GLₙ` and the characteristic polynomial on `Conj_{GLₙ}`

Let `K` be a field. A regular class function of `GLₙ` over `K` is determined by its restriction
to the diagonal torus
(`TauCeti.GeneralLinear.eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero`), so
the Chevalley restriction map from the class functions to the Weyl-invariant functions on the
torus is injective
(`TauCeti.GeneralLinear.injective_classFunctionsRestrict_diagonalTorusCoordinateMap`). The proof
evaluates a class function at the generic point of `GLₙ`, with values in an algebraic closure `L`
of the fraction field of `O(GLₙ)`. The generic matrix has nonzero discriminant, since it
specializes to a diagonal matrix with distinct entries, so over `L` its characteristic polynomial
is separable and the generic point is conjugate to a diagonal point
(`TauCeti.GeneralLinear.exists_eq_mul_diagonalPoint_mul_inv_of_separable`). A class function
takes the same value at conjugate points, and the generic point determines the function.

From this the conjugation invariants of `GLₙ` are computed, for `n ≥ 1`: the coefficients
`c₀, …, c_{n-1}` of the characteristic polynomial of the generic matrix, with `c₀ = (-1)ⁿ det`
inverted, are algebraically independent
(`TauCeti.GeneralLinear.charpolyCoeffAlgHom_injective`) and generate the invariants
(`TauCeti.GeneralLinear.charpolyCoeffAlgHom_surjective`), so

`O(GLₙ)^{GLₙ} ≅ K[c₀^{±1}, c₁, …, c_{n-1}]`

(`TauCeti.GeneralLinear.charpolyCoeffAlgEquiv`), and the characteristic polynomial
`Conj_{GLₙ} ⟶ 𝔸^{n-1} × 𝔾ₘ` is an isomorphism of schemes
(`TauCeti.GeneralLinear.isIso_charpolyQuotientMap`). Both halves are read at the generic
diagonal point, with values in `K[t₁^{±1}, …, tₙ^{±1}]`: there the characteristic polynomial
coefficients become the coefficients of `∏ⱼ (T - tⱼ)`, which are algebraically independent; and
the value of a class function, cleared of a power of `t₁ ⋯ tₙ`, is a symmetric polynomial, hence a
polynomial in those coefficients (`MvPolynomial.range_vietaAlgHom`).

This is the `GLₙ` case of the reductive quotient `Conj_H` of ArithmeticGaloisRepresentations
§1.11, *Reductive quotients over fields and DVRs*.

## Main declarations

* `TauCeti.GeneralLinear.diagonalPoint`: the point of `GLₙ` given by a diagonal matrix of units.
* `TauCeti.GeneralLinear.diagonalPoint_apply_comp_perm_of_mem_classFunctions`: a class function
  is symmetric in the entries of a diagonal point.
* `TauCeti.GeneralLinear.exists_eq_mul_diagonalPoint_mul_inv_of_separable`: over an
  algebraically closed field, a point with separable characteristic polynomial is conjugate to a
  diagonal point.
* `TauCeti.GeneralLinear.injective_classFunctionsRestrict_diagonalTorusCoordinateMap`: the
  Chevalley restriction map of `GLₙ` over a field is injective.
* `TauCeti.GeneralLinear.charpolyCoeffAlgEquiv`: `K[c₀^{±1}, c₁, …, c_{n-1}] ≃ O(GLₙ)^{GLₙ}`.
* `TauCeti.GeneralLinear.isIso_charpolyQuotientMap`: `Conj_{GLₙ} ≅ 𝔸^{n-1} × 𝔾ₘ`.

## References

* G. Böckle, M. Harris, C. Khare, J. A. Thorne, arXiv:1609.03491v2, §3.
* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS **25** (1965),
  §6.
-/

public section

open WithConv Polynomial

namespace TauCeti.GeneralLinear

universe u

section Ring

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The point of `GLₙ` with values in `A` given by the diagonal matrix with entries `t`. -/
noncomputable def diagonalPoint {A : Type*} [CommRing A] [Algebra R A] (t : Fin n → Aˣ) :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  (pointsMulEquiv n).symm (diagGL t)

/-- `diagonalPoint t` is the point of the invertible diagonal matrix `diagGL t`. -/
theorem diagonalPoint_def {A : Type*} [CommRing A] [Algebra R A] (t : Fin n → Aˣ) :
    diagonalPoint (R := R) t = (pointsMulEquiv n).symm (diagGL t) :=
  (rfl)

/-- Read as an invertible matrix, `diagonalPoint t` is `diagGL t`. -/
@[simp]
theorem pointToGeneralLinear_diagonalPoint {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) : pointToGeneralLinear n (diagonalPoint (R := R) t) = diagGL t :=
  by rw [← pointsMulEquiv_apply, diagonalPoint, MulEquiv.apply_symm_apply]

/-- The generic matrix evaluated at `diagonalPoint t` is the diagonal matrix with entries `t`. -/
@[simp]
theorem map_genericMatrix_diagonalPoint {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) :
    (genericMatrix R n).map (diagonalPoint (R := R) t).ofConv =
      Matrix.diagonal fun i ↦ (t i : A) := by
  rw [map_genericMatrix_eq_coe_pointToGeneralLinear, toConv_ofConv, ← pointsMulEquiv_apply,
    diagonalPoint, MulEquiv.apply_symm_apply, diagGL_coe]

/-- At `diagonalPoint t`, the coefficients of the characteristic polynomial are those of
`∏ⱼ (T - tⱼ)`. -/
theorem diagonalPoint_apply_coeff_charpoly {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) (k : ℕ) :
    (diagonalPoint (R := R) t).ofConv ((genericMatrix R n).charpoly.coeff k) =
      (∏ j, (Polynomial.X - Polynomial.C (t j : A))).coeff k := by
  rw [← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, ← Matrix.charpoly_map, AlgHom.coe_toRingHom,
    map_genericMatrix_diagonalPoint, Matrix.charpoly_diagonal]

/-- Permuting the entries of a diagonal point does not change the value of a class function. -/
theorem diagonalPoint_apply_comp_perm_of_mem_classFunctions {f : coordinateHopfAlgebra R n}
    (hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n))
    {A : Type*} [CommRing A] [Algebra R A] (t : Fin n → Aˣ) (σ : Equiv.Perm (Fin n)) :
    (diagonalPoint (R := R) fun i ↦ t (σ i)).ofConv f = (diagonalPoint (R := R) t).ofConv f := by
  let g := (pointsMulEquiv (R := R) (A := A) n).symm (permutationGL σ⁻¹)
  have h : (diagonalPoint (R := R) fun i ↦ t (σ i)) = g * diagonalPoint (R := R) t * g⁻¹ := by
    apply (pointsMulEquiv (R := R) (A := A) n).injective
    rw [map_mul, map_mul, map_inv, diagonalPoint, diagonalPoint, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, permutationGL_mul_diagGL_mul_inv]
    simp
  rw [h, HopfAlgebra.apply_mul_mul_inv_of_mem_classFunctions hf]

end Ring

section Field

variable {K : Type u} [Field K] {n : ℕ}

/-- **The generic matrix of `GLₙ` has nonzero discriminant**: it specializes to a diagonal matrix
with distinct entries over an algebraic closure of `K`. -/
private theorem discr_genericMatrix_ne_zero : (genericMatrix K n).discr ≠ 0 := by
  let L := AlgebraicClosure K
  let e := Infinite.natEmbedding L
  have he (i : Fin n) : e (i + 1) - e 0 ≠ 0 := sub_ne_zero.2 (fun h ↦ by simpa using e.injective h)
  let t : Fin n → Lˣ := fun i ↦ Units.mk0 _ (he i)
  intro h0
  have h := congrArg (diagonalPoint (R := K) t).ofConv h0
  rw [map_zero, ← AlgHom.coe_toRingHom, ← Matrix.discr_map] at h
  refine (Matrix.discr_diagonal_ne_zero_iff (d := fun i ↦ (t i : L))).2 ?_ ?_
  · intro i j hij
    simpa [t, Fin.val_inj] using e.injective (sub_left_injective hij)
  · simpa [map_genericMatrix_diagonalPoint] using h

/-- **A point of `GLₙ` with separable characteristic polynomial is conjugate to a diagonal
point** over an algebraically closed field. -/
theorem exists_eq_mul_diagonalPoint_mul_inv_of_separable {L : Type*} [Field L] [IsAlgClosed L]
    [Algebra K L] (x : WithConv (coordinateHopfAlgebra K n →ₐ[K] L))
    (hx : ((genericMatrix K n).map x.ofConv).charpoly.Separable) :
    ∃ (g : WithConv (coordinateHopfAlgebra K n →ₐ[K] L)) (s : Fin n → Lˣ),
      x = g * diagonalPoint (R := K) s * g⁻¹ := by
  set M := (genericMatrix K n).map x.ofConv
  obtain ⟨P, d, hPd⟩ := M.exists_mul_eq_mul_diagonal_of_separable (IsAlgClosed.splits _) hx
  have hM : (pointsMulEquiv n x : Matrix (Fin n) (Fin n) L) = M := by
    rw [pointsMulEquiv_apply, ← toConv_ofConv x, ← map_genericMatrix_eq_coe_pointToGeneralLinear,
      ofConv_toConv]
  have hd (i : Fin n) : d i ≠ 0 := by
    have hdet := congrArg Matrix.det hPd
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm, ← hM] at hdet
    have hu : IsUnit (pointsMulEquiv n x : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hP : (P : Matrix (Fin n) (Fin n) L).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit P)).ne_zero
    have hprod : ∏ i, d i ≠ 0 := fun h0 ↦ by
      rw [h0, mul_zero] at hdet
      exact (mul_ne_zero hP hu.ne_zero) hdet
    exact (Finset.prod_ne_zero_iff.1 hprod) i (Finset.mem_univ i)
  refine ⟨(pointsMulEquiv (R := K) (A := L) n).symm P, fun i ↦ Units.mk0 _ (hd i), ?_⟩
  apply (pointsMulEquiv (R := K) (A := L) n).injective
  rw [map_mul, map_mul, map_inv, diagonalPoint, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [hM, Units.val_mul, Units.val_mul, diagGL_coe]
  change M = (P : Matrix (Fin n) (Fin n) L) * Matrix.diagonal d *
    ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [← hPd, mul_assoc, Units.mul_inv, mul_one]

/-- A class function of `GLₙ` over a field vanishing at every diagonal point with values in an
algebraic closure of the fraction field of `O(GLₙ)` vanishes: the generic point is conjugate to
such a diagonal point. -/
private theorem eq_zero_of_forall_diagonalPoint {f : coordinateHopfAlgebra K n}
    (hf : f ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n))
    (h : ∀ t : Fin n → (AlgebraicClosure (FractionRing (coordinateHopfAlgebra K n)))ˣ,
      (diagonalPoint (R := K) t).ofConv f = 0) : f = 0 := by
  let O := coordinateHopfAlgebra K n
  let L := AlgebraicClosure (FractionRing O)
  let x₀ : O →ₐ[K] L := IsScalarTower.toAlgHom K O L
  have hx₀ : Function.Injective x₀ := by
    change Function.Injective (algebraMap O L)
    rw [IsScalarTower.algebraMap_eq O (FractionRing O) L]
    exact (algebraMap (FractionRing O) L).injective.comp (IsFractionRing.injective O _)
  have hsep : ((genericMatrix K n).map x₀).charpoly.Separable := by
    rw [← ((genericMatrix K n).map x₀).charpoly_monic.discr_ne_zero_iff]
    change ((genericMatrix K n).map (x₀ : O →+* L)).discr ≠ 0
    rw [Matrix.discr_map]
    exact (map_ne_zero_iff _ hx₀).2 discr_genericMatrix_ne_zero
  obtain ⟨g, s, hconj⟩ := exists_eq_mul_diagonalPoint_mul_inv_of_separable (toConv x₀) hsep
  have hval := HopfAlgebra.apply_mul_mul_inv_of_mem_classFunctions hf g (diagonalPoint s)
  rw [← hconj, ofConv_toConv, h s] at hval
  exact hx₀ (hval.trans (map_zero x₀).symm)

/-- **A class function of `GLₙ` over a field is determined by its restriction to the diagonal
torus**: if the restriction vanishes, so does the class function. -/
theorem eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero
    {f : coordinateHopfAlgebra K n}
    (hf : f ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n))
    (h : (diagonalTorusCoordinateMap (R := K) (N := n)).hom f = 0) : f = 0 := by
  refine eq_zero_of_forall_diagonalPoint hf fun t ↦ ?_
  let L := AlgebraicClosure (FractionRing (coordinateHopfAlgebra K n))
  let t' := (SplitTorus.pointsMulEquiv (R := K) (A := L) (σ := ULift.{u} (Fin n))).symm
    fun i ↦ t i.down
  have ht : diagonalTorusPoints t' = diagonalPoint (R := K) t := by
    apply (pointsMulEquiv (R := K) (A := L) n).injective
    rw [pointsMulEquiv_diagonalTorusPoints, diagonalPoint, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    congr 1
    funext i
    exact diagonalTorusCoordinates_apply _ i
  have h' := mapPointsFunctor_diagonalTorusCoordinateMap_app (R := K) (N := n)
    (CommAlgCat.of K L) t'
  rw [← ht, ← h', CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply, h, map_zero]

/-- **Chevalley restriction for `GLₙ` over a field is injective**: restriction from the class
functions of `GLₙ` to the Weyl-invariant functions on the diagonal torus is injective. -/
theorem injective_classFunctionsRestrict_diagonalTorusCoordinateMap :
    Function.Injective (BialgHom.classFunctionsRestrict
      (diagonalTorusCoordinateMap (R := K) (N := n)).hom
      (diagonalTorusCoordinateMap_surjective K n)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine Subtype.ext (eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero
    f.property ?_)
  simpa using congrArg Subtype.val hf

/-! ### The generic diagonal point -/

/-- The ring `K[t₁^{±1}, …, tₙ^{±1}]`, the localization of the polynomial ring at `t₁ ⋯ tₙ`. -/
private abbrev DiagRing (K : Type u) [Field K] (n : ℕ) :=
  Localization.Away (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) K)

private theorem isUnit_algebraMap_X (i : Fin n) :
    IsUnit (algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) (MvPolynomial.X i)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    (IsLocalization.Away.algebraMap_isUnit _)

/-- The diagonal entries `tᵢ` of the generic diagonal point. -/
private noncomputable def genericUnit (i : Fin n) : (DiagRing K n)ˣ :=
  (isUnit_algebraMap_X (K := K) i).unit

private theorem algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin n) K) (DiagRing K n)) :=
  IsLocalization.injective (M := Submonoid.powers (∏ i : Fin n, MvPolynomial.X i)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Finset.prod_ne_zero_iff.2 fun i _ ↦ MvPolynomial.X_ne_zero i))

/-- Specializing the generic diagonal entries to units `t` of `A`. -/
private noncomputable def specialize {A : Type*} [CommRing A] [Algebra K A] (t : Fin n → Aˣ) :
    DiagRing K n →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (∏ i : Fin n, MvPolynomial.X i)
    (f := MvPolynomial.aeval fun i ↦ (t i : A)) (by simp [map_prod])

private theorem specialize_genericUnit {A : Type*} [CommRing A] [Algebra K A]
    (t : Fin n → Aˣ) (i : Fin n) :
    specialize t (genericUnit (K := K) i : DiagRing K n) = t i := by
  simp [specialize, genericUnit, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem diagonalPoint_apply_eq_specialize {A : Type*} [CommRing A] [Algebra K A]
    (t : Fin n → Aˣ) (f : coordinateHopfAlgebra K n) :
    (diagonalPoint (R := K) t).ofConv f =
      specialize t ((diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv f) := by
  have h : diagonalPoint (R := K) t = AlgHom.mapValue (H := coordinateHopfAlgebra K n)
      (specialize t) (diagonalPoint (R := K) (genericUnit (K := K) (n := n))) := by
    rw [diagonalPoint, diagonalPoint, mapValue_pointsMulEquiv_symm_apply, map_diagGL]
    congr 2
    funext i
    ext
    simp [specialize_genericUnit]
  rw [h, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]

/-- **A class function of `GLₙ` over a field is determined by its value at the generic diagonal
point.** -/
private theorem eq_of_genericDiagonal {f g : coordinateHopfAlgebra K n}
    (hf : f ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n))
    (hg : g ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n))
    (h : (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv f =
      (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv g) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_diagonalPoint (Subalgebra.sub_mem _ hf hg) fun t ↦ ?_
  rw [diagonalPoint_apply_eq_specialize, map_sub, h, sub_self, map_zero]

private theorem genericDiagonal_coeff_charpoly (k : ℕ) :
    (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv
        ((genericMatrix K n).charpoly.coeff k) =
      algebraMap (MvPolynomial (Fin n) K) (DiagRing K n)
        ((∏ j : Fin n,
          (Polynomial.X - Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) K))).coeff k) := by
  rw [diagonalPoint_apply_coeff_charpoly, ← Polynomial.coeff_map, Polynomial.map_prod]
  simp [genericUnit]

private theorem genericDiagonal_aeval (p : MvPolynomial (Fin n) K) :
    (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv
        (MvPolynomial.aeval (fun i : Fin n ↦ (genericMatrix K n).charpoly.coeff i) p) =
      algebraMap (MvPolynomial (Fin n) K) (DiagRing K n)
        (MvPolynomial.vietaAlgHom K n p) := by
  have h : (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv.comp
        (MvPolynomial.aeval fun i : Fin n ↦ (genericMatrix K n).charpoly.coeff i) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (DiagRing K n)).comp
        (MvPolynomial.vietaAlgHom K n) :=
    MvPolynomial.algHom_ext fun i ↦ by
      simp [genericDiagonal_coeff_charpoly]
  exact AlgHom.congr_fun h p

private theorem specialize_algebraMap_rename (σ : Equiv.Perm (Fin n))
    (p : MvPolynomial (Fin n) K) :
    specialize (fun i ↦ genericUnit (K := K) (n := n) (σ i))
        (algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) p) =
      algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) (MvPolynomial.rename σ p) := by
  rw [specialize, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  change MvPolynomial.aeval _ p =
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (DiagRing K n)) (MvPolynomial.rename σ p)
  rw [← AlgHom.comp_apply]
  congr 1
  exact MvPolynomial.algHom_ext fun i ↦ by simp [genericUnit]

/-- The value of a class function at the generic diagonal point, cleared of denominators, is a
symmetric polynomial. -/
private theorem mem_symmetricSubalgebra_of_genericDiagonal {f : coordinateHopfAlgebra K n}
    (hf : f ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n)) {m : ℕ}
    {p : MvPolynomial (Fin n) K}
    (hp : (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv f *
        algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) (∏ i : Fin n, MvPolynomial.X i) ^ m =
      algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) p) :
    p ∈ MvPolynomial.symmetricSubalgebra (Fin n) K := by
  rw [MvPolynomial.mem_symmetricSubalgebra]
  intro σ
  have hprod : MvPolynomial.rename σ (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) K) =
      ∏ i, MvPolynomial.X i := by
    simp only [map_prod, MvPolynomial.rename_X]
    exact Equiv.prod_comp σ MvPolynomial.X
  have h := congrArg (specialize fun i ↦ genericUnit (K := K) (n := n) (σ i)) hp
  rw [map_mul, map_pow, specialize_algebraMap_rename, specialize_algebraMap_rename, hprod,
    ← diagonalPoint_apply_eq_specialize, diagonalPoint_apply_comp_perm_of_mem_classFunctions hf,
    hp] at h
  exact (algebraMap_injective h).symm

private theorem coeff_zero_prod_X_sub_C_X :
    (∏ j : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) K))).coeff
        0 = (-1) ^ n * ∏ j : Fin n, MvPolynomial.X j := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp [Finset.prod_neg]

/-! ### The conjugation invariants of `GLₙ` -/

variable [NeZero n]

/-- On polynomials in `c₀, …, c_{n-1}`, `charpolyCoeffAlgHom` is evaluation at the coefficients of
the characteristic polynomial of the generic matrix. -/
theorem coe_charpolyCoeffAlgHom_algebraMap (p : MvPolynomial (Fin n) K) :
    (charpolyCoeffAlgHom K n (algebraMap (MvPolynomial (Fin n) K) _ p) :
        coordinateHopfAlgebra K n) =
      MvPolynomial.aeval (fun i : Fin n ↦ (genericMatrix K n).charpoly.coeff i) p := by
  have h : ((HopfAlgebra.conjugationInvariants K (coordinateHopfAlgebra K n)).val.comp
      ((charpolyCoeffAlgHom K n).comp (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K)
        (Localization.Away (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) K))))) =
      MvPolynomial.aeval fun i : Fin n ↦ (genericMatrix K n).charpoly.coeff i :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h p

/-- **The characteristic polynomial coefficients are algebraically independent on `GLₙ`.** -/
theorem charpolyCoeffAlgHom_injective : Function.Injective (charpolyCoeffAlgHom K n) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨m, p, hp⟩ :=
    IsLocalization.Away.surj (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) K) q
  have h1 : charpolyCoeffAlgHom K n (algebraMap (MvPolynomial (Fin n) K) _ p) = 0 := by
    rw [← hp, map_mul, hq, zero_mul]
  have h2 := congrArg (fun x : HopfAlgebra.conjugationInvariants K (coordinateHopfAlgebra K n) ↦
    (diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv
      (x : coordinateHopfAlgebra K n)) h1
  simp only [coe_charpolyCoeffAlgHom_algebraMap, genericDiagonal_aeval, ZeroMemClass.coe_zero,
    map_zero] at h2
  have hp0 : p = 0 := MvPolynomial.vietaAlgHom_injective K n
    (algebraMap_injective (by rw [h2, map_zero, map_zero]))
  rw [hp0, map_zero] at hp
  exact ((IsLocalization.Away.algebraMap_isUnit _).pow m).mul_left_eq_zero.1 hp

/-- **The characteristic polynomial coefficients generate the class functions of `GLₙ`.** -/
theorem charpolyCoeffAlgHom_surjective : Function.Surjective (charpolyCoeffAlgHom K n) := by
  rintro ⟨f, hf₀⟩
  have hf : f ∈ HopfAlgebra.classFunctions K (coordinateHopfAlgebra K n) :=
    HopfAlgebra.conjugationInvariants_eq_classFunctions K (coordinateHopfAlgebra K n) ▸ hf₀
  let δ := diagonalPoint (R := K) (genericUnit (K := K) (n := n))
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj
    (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) K) (δ.ofConv f)
  have hsym := mem_symmetricSubalgebra_of_genericDiagonal hf hp
  rw [← MvPolynomial.range_vietaAlgHom] at hsym
  obtain ⟨Q, hQ⟩ := hsym
  let s : K := (-1) ^ (n * m)
  let x : MvPolynomial (Fin n) K := MvPolynomial.X 0
  let F := charpolyCoeffAlgHom K n
    (algebraMap _ _ (MvPolynomial.C s * Q) * IsLocalization.Away.invSelf x ^ m)
  have hF : F * charpolyCoeffAlgHom K n (algebraMap _ _ x) ^ m =
      charpolyCoeffAlgHom K n (algebraMap _ _ (MvPolynomial.C s * Q)) := by
    rw [← map_pow, ← map_mul, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf x),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨algebraMap _ _ (MvPolynomial.C s * Q) * IsLocalization.Away.invSelf x ^ m,
    Subtype.ext (eq_of_genericDiagonal (f := (F : coordinateHopfAlgebra K n)) ?_ hf ?_)⟩
  · exact HopfAlgebra.conjugationInvariants_eq_classFunctions K (coordinateHopfAlgebra K n) ▸
      F.property
  have h1 := congrArg (fun y : HopfAlgebra.conjugationInvariants K (coordinateHopfAlgebra K n) ↦
    δ.ofConv (y : coordinateHopfAlgebra K n)) hF
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_pow,
    coe_charpolyCoeffAlgHom_algebraMap, δ, genericDiagonal_aeval] at h1
  have hQ' : MvPolynomial.vietaAlgHom K n Q = p := hQ
  have hx : MvPolynomial.vietaAlgHom K n x = (-1) ^ n * ∏ j : Fin n, MvPolynomial.X j := by
    simp only [x, MvPolynomial.vietaAlgHom_X, Fin.val_zero,
      coeff_zero_prod_X_sub_C_X]
  simp only [hQ', hx, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, map_mul, mul_pow, map_pow,
    map_neg, map_one, ← pow_mul, ← IsScalarTower.algebraMap_apply] at h1
  change _ = δ.ofConv f
  have hs : algebraMap K (DiagRing K n) s = (-1) ^ (n * m) := by simp [s]
  rw [hs] at h1
  have key : ((diagonalPoint (R := K) (genericUnit (K := K) (n := n))).ofConv F -
      δ.ofConv f) * ((-1) ^ (n * m) *
        algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) (∏ i : Fin n, MvPolynomial.X i) ^ m) =
      0 := by
    linear_combination h1 - (-1) ^ (n * m) * hp
  have hu : IsUnit ((-1 : DiagRing K n) ^ (n * m) *
      algebraMap (MvPolynomial (Fin n) K) (DiagRing K n) (∏ i : Fin n, MvPolynomial.X i) ^ m) :=
    (isUnit_one.neg.pow _).mul ((IsLocalization.Away.algebraMap_isUnit _).pow m)
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 key)

/-- **The conjugation invariants of `GLₙ` over a field are the Laurent polynomial ring in the
coefficients of the characteristic polynomial.** -/
noncomputable def charpolyCoeffAlgEquiv :
    Localization.Away (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) K) ≃ₐ[K]
      HopfAlgebra.conjugationInvariants K (coordinateHopfAlgebra K n) :=
  AlgEquiv.ofBijective (charpolyCoeffAlgHom K n)
    ⟨charpolyCoeffAlgHom_injective, charpolyCoeffAlgHom_surjective⟩

/-- `charpolyCoeffAlgEquiv` is `charpolyCoeffAlgHom`. -/
@[simp]
theorem charpolyCoeffAlgEquiv_apply
    (x : Localization.Away (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) K)) :
    charpolyCoeffAlgEquiv x = charpolyCoeffAlgHom K n x :=
  AlgEquiv.ofBijective_apply _ _ x

open _root_.AlgebraicGeometry _root_.CategoryTheory in
/-- **`Conj_{GLₙ} ≅ 𝔸^{n-1} × 𝔾ₘ` over a field**: the characteristic polynomial on the
conjugation quotient is an isomorphism of schemes. -/
instance isIso_charpolyQuotientMap : IsIso (charpolyQuotientMap K n) := by
  rw [charpolyQuotientMap_eq]
  have : IsIso (CommRingCat.ofHom (charpolyCoeffAlgHom K n).toRingHom) :=
    (RingEquiv.toCommRingCatIso (charpolyCoeffAlgEquiv (K := K) (n := n)).toRingEquiv).isIso_hom
  infer_instance

end Field

end TauCeti.GeneralLinear
