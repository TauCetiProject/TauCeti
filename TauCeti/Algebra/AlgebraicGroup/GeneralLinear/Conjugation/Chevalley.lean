/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.Invariants
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Restriction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.LinearAlgebra.Matrix.Charpoly.Discriminant
import TauCeti.LinearAlgebra.Matrix.Charpoly.Separable
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClassFunction
import TauCeti.RingTheory.MvPolynomial.LocalizationAwayProdX
import TauCeti.RingTheory.MvPolynomial.Symmetric.Vieta
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Chevalley restriction for `GLₙ` and the characteristic polynomial on `Conj_{GLₙ}`

Let `R` be an integral domain. A regular class function of `GLₙ` over `R` is determined by its
restriction to the diagonal torus
(`TauCeti.GeneralLinear.eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero`), so
the Chevalley restriction map from the class functions to the Weyl-invariant functions on the
torus is injective
(`TauCeti.GeneralLinear.classFunctionsRestrict_diagonalTorusCoordinateMap_injective`). The proof
evaluates a class function at the generic point of `GLₙ`, with values in an algebraic closure `L`
of the fraction field of `O(GLₙ)`. The generic matrix has nonzero discriminant, since it
specializes to a diagonal matrix with distinct entries, so over `L` its characteristic polynomial
is separable and the generic point is conjugate to a diagonal point
(`TauCeti.GeneralLinear.exists_eq_mul_diagonalPoint_mul_inv_of_separable`). A class function
takes the same value at conjugate points, and the generic point determines the function.

From this the conjugation invariants of `GLₙ` are computed, for `n ≥ 1`: the coefficients
`c₀, …, c_{n-1}` of the characteristic polynomial of the generic matrix, with `c₀ = (-1)ⁿ det`
inverted, are algebraically independent over every commutative ring
(`TauCeti.GeneralLinear.charpolyCoeffAlgHom_injective`) and, over a domain, generate the
invariants (`TauCeti.GeneralLinear.charpolyCoeffAlgHom_surjective`), so

`O(GLₙ)^{GLₙ} ≅ R[c₀^{±1}, c₁, …, c_{n-1}]`

(`TauCeti.GeneralLinear.charpolyCoeffAlgEquiv`), and the characteristic polynomial
`Conj_{GLₙ} ⟶ 𝔸^{n-1} × 𝔾ₘ` is an isomorphism of schemes
(`TauCeti.GeneralLinear.isIso_charpolyQuotientMap`). Both halves are read at the generic
diagonal point, with values in `R[t₁^{±1}, …, tₙ^{±1}]`: there the characteristic polynomial
coefficients become the coefficients of `∏ⱼ (T - tⱼ)`, which are algebraically independent; and
the value of a class function, cleared of a power of `t₁ ⋯ tₙ`, is a symmetric polynomial, hence a
polynomial in those coefficients (`MvPolynomial.range_vietaAlgHom`).

## Main declarations

* `TauCeti.GeneralLinear.exists_eq_mul_diagonalPoint_mul_inv_of_separable`: a point with values
  in a field, whose characteristic polynomial splits and is separable, is conjugate to a diagonal
  point.
* `TauCeti.GeneralLinear.discr_genericMatrix_ne_zero`: over a domain, the generic matrix of `GLₙ`
  has nonzero discriminant.
* `TauCeti.GeneralLinear.classFunctionsRestrict_diagonalTorusCoordinateMap_injective`: the
  Chevalley restriction map of `GLₙ` over a domain is injective.
* `TauCeti.GeneralLinear.charpolyCoeffAlgEquiv`: `R[c₀^{±1}, c₁, …, c_{n-1}] ≃ O(GLₙ)^{GLₙ}`.
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

/-- At `diagonalPoint t`, the coefficients of the characteristic polynomial are those of
`∏ⱼ (T - tⱼ)`. -/
theorem diagonalPoint_apply_coeff_charpoly {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) (k : ℕ) :
    (diagonalPoint (R := R) t).ofConv ((genericMatrix R n).charpoly.coeff k) =
      (∏ j, (Polynomial.X - Polynomial.C (t j : A))).coeff k := by
  rw [← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, ← Matrix.charpoly_map, AlgHom.coe_toRingHom,
    map_genericMatrix_diagonalPoint, Matrix.charpoly_diagonal]

/-- **A point of `GLₙ` with split separable characteristic polynomial is conjugate to a diagonal
point.** -/
theorem exists_eq_mul_diagonalPoint_mul_inv_of_separable {L : Type*} [Field L] [Algebra R L]
    (x : WithConv (coordinateHopfAlgebra R n →ₐ[R] L))
    (hs : ((genericMatrix R n).map x.ofConv).charpoly.Splits)
    (hx : ((genericMatrix R n).map x.ofConv).charpoly.Separable) :
    ∃ (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] L)) (s : Fin n → Lˣ),
      x = g * diagonalPoint (R := R) s * g⁻¹ := by
  set M := (genericMatrix R n).map x.ofConv
  obtain ⟨P, d, hPd⟩ := M.exists_mul_eq_mul_diagonal_of_separable hs hx
  have hM : (pointsMulEquiv n x : Matrix (Fin n) (Fin n) L) = M := by
    rw [pointsMulEquiv_apply, ← toConv_ofConv x, ← map_genericMatrix_eq_coe_pointToGeneralLinear,
      ofConv_toConv]
  have hd := Matrix.isUnit_of_mul_eq_mul_diagonal (hM ▸ Units.isUnit _) hPd
  refine ⟨(pointsMulEquiv (R := R) (A := L) n).symm P, fun i ↦ (hd i).unit, ?_⟩
  apply (pointsMulEquiv (R := R) (A := L) n).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_diagonalPoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  simp only [hM, Units.val_mul, diagGL_coe, IsUnit.unit_spec]
  rw [← hPd, mul_assoc, Units.mul_inv, mul_one]

end Ring

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

/-- **The generic matrix of `GLₙ` has nonzero discriminant**: it specializes to a diagonal matrix
with distinct entries over an algebraic closure of the fraction field of `R`. -/
theorem discr_genericMatrix_ne_zero : (genericMatrix R n).discr ≠ 0 := by
  let L := AlgebraicClosure (FractionRing R)
  let e := Infinite.natEmbedding L
  have he (i : Fin n) : e (i + 1) - e 0 ≠ 0 := sub_ne_zero.2 (fun h ↦ by simpa using e.injective h)
  let t : Fin n → Lˣ := fun i ↦ Units.mk0 _ (he i)
  intro h0
  have h := congrArg (diagonalPoint (R := R) t).ofConv h0
  rw [map_zero, ← AlgHom.coe_toRingHom, ← Matrix.discr_map] at h
  refine (Matrix.discr_diagonal_ne_zero_iff (d := fun i ↦ (t i : L))).2 ?_ ?_
  · intro i j hij
    simpa [t, Fin.val_inj] using e.injective (sub_left_injective hij)
  · simpa [map_genericMatrix_diagonalPoint] using h

/-- A class function of `GLₙ` over a domain vanishing at every diagonal point with values in an
algebraic closure of the fraction field of `O(GLₙ)` vanishes. -/
private theorem eq_zero_of_forall_diagonalPoint {f : coordinateHopfAlgebra R n}
    (hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n))
    (h : ∀ t : Fin n → (AlgebraicClosure (FractionRing (coordinateHopfAlgebra R n)))ˣ,
      (diagonalPoint (R := R) t).ofConv f = 0) : f = 0 := by
  let O := coordinateHopfAlgebra R n
  let L := AlgebraicClosure (FractionRing O)
  let x₀ : O →ₐ[R] L := IsScalarTower.toAlgHom R O L
  have hx₀ : Function.Injective x₀ := by
    simp only [x₀, IsScalarTower.coe_toAlgHom', IsScalarTower.algebraMap_eq O (FractionRing O) L,
      RingHom.coe_comp]
    exact (algebraMap (FractionRing O) L).injective.comp (IsFractionRing.injective O _)
  -- The generic point `x₀` has separable characteristic polynomial, since the generic matrix has
  -- nonzero discriminant and `x₀` is injective.
  have hsep : ((genericMatrix R n).map x₀).charpoly.Separable := by
    have hdiscr := (map_ne_zero_iff _ hx₀).2 (discr_genericMatrix_ne_zero (R := R) (n := n))
    rw [← AlgHom.coe_toRingHom, ← Matrix.discr_map, Matrix.discr, AlgHom.coe_toRingHom] at hdiscr
    exact ((genericMatrix R n).map x₀).charpoly_monic.discr_ne_zero_iff.1 hdiscr
  obtain ⟨g, s, hconj⟩ :=
    exists_eq_mul_diagonalPoint_mul_inv_of_separable (toConv x₀) (IsAlgClosed.splits _) hsep
  have hval := HopfAlgebra.apply_mul_mul_inv_of_mem_classFunctions hf g (diagonalPoint s)
  rw [← hconj, ofConv_toConv, h s] at hval
  exact hx₀ (hval.trans (map_zero x₀).symm)

/-- **A class function of `GLₙ` over a domain is determined by its restriction to the diagonal
torus**: if the restriction vanishes, so does the class function. -/
theorem eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero
    {f : coordinateHopfAlgebra R n}
    (hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n))
    (h : (diagonalTorusCoordinateMap (R := R) (N := n)).hom f = 0) : f = 0 := by
  refine eq_zero_of_forall_diagonalPoint hf fun t ↦ ?_
  let L := AlgebraicClosure (FractionRing (coordinateHopfAlgebra R n))
  let t' := (SplitTorus.pointsMulEquiv (R := R) (A := L) (σ := ULift.{u} (Fin n))).symm
    fun i ↦ t i.down
  have ht : diagonalTorusPoints t' = diagonalPoint (R := R) t := by
    rw [diagonalTorusPoints_eq_diagonalPoint, MulEquiv.apply_symm_apply]
    congr 1
    funext i
    exact diagonalTorusCoordinates_apply _ i
  have h' := mapPointsFunctor_diagonalTorusCoordinateMap_app (R := R) (N := n)
    (CommAlgCat.of R L) t'
  rw [← ht, ← h', CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply, h, map_zero]

/-- **Chevalley restriction for `GLₙ` over a domain is injective**: restriction from the class
functions of `GLₙ` to the Weyl-invariant functions on the diagonal torus is injective. -/
theorem classFunctionsRestrict_diagonalTorusCoordinateMap_injective :
    Function.Injective (BialgHom.classFunctionsRestrict
      (diagonalTorusCoordinateMap (R := R) (N := n)).hom
      (diagonalTorusCoordinateMap_surjective R n)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine Subtype.ext (eq_zero_of_mem_classFunctions_of_diagonalTorusCoordinateMap_eq_zero
    f.property ?_)
  simpa using congrArg Subtype.val hf

end Domain

/-! ### The generic diagonal point -/

section GenericDiagonal

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The ring `R[t₁^{±1}, …, tₙ^{±1}]`, the localization of the polynomial ring at `t₁ ⋯ tₙ`. -/
private abbrev DiagRing (R : Type u) [CommRing R] (n : ℕ) :=
  Localization.Away (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) R)

/-- The diagonal entries `tᵢ` of the generic diagonal point. -/
private noncomputable def genericUnit (i : Fin n) : (DiagRing R n)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := DiagRing R n)
    (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) R)
    (Finset.dvd_prod_of_mem MvPolynomial.X (Finset.mem_univ i))).unit

/-- Specializing the generic diagonal entries to units `t` of `A`. -/
private noncomputable def specialize {A : Type*} [CommRing A] [Algebra R A] (t : Fin n → Aˣ) :
    DiagRing R n →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (∏ i : Fin n, MvPolynomial.X i)
    (f := MvPolynomial.aeval fun i ↦ (t i : A)) (by simp [map_prod])

@[simp]
private theorem specialize_algebraMap {A : Type*} [CommRing A] [Algebra R A] (t : Fin n → Aˣ)
    (p : MvPolynomial (Fin n) R) :
    specialize t (algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) p) =
      MvPolynomial.aeval (fun i ↦ (t i : A)) p := by
  simp [specialize, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

private theorem specialize_genericUnit {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) (i : Fin n) :
    specialize t (genericUnit (R := R) i : DiagRing R n) = t i := by
  simp [genericUnit]

private theorem diagonalPoint_apply_eq_specialize {A : Type*} [CommRing A] [Algebra R A]
    (t : Fin n → Aˣ) (f : coordinateHopfAlgebra R n) :
    (diagonalPoint (R := R) t).ofConv f =
      specialize t ((diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv f) := by
  have h : diagonalPoint (R := R) t = AlgHom.mapValue (H := coordinateHopfAlgebra R n)
      (specialize t) (diagonalPoint (R := R) (genericUnit (R := R) (n := n))) := by
    rw [mapValue_diagonalPoint]
    congr 1
    funext i
    ext
    simp [specialize_genericUnit]
  rw [h, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]

private theorem genericDiagonal_coeff_charpoly (k : ℕ) :
    (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv
        ((genericMatrix R n).charpoly.coeff k) =
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n)
        ((∏ j : Fin n,
          (Polynomial.X - Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) R))).coeff k) := by
  rw [diagonalPoint_apply_coeff_charpoly, ← Polynomial.coeff_map, Polynomial.map_prod]
  simp [genericUnit]

private theorem genericDiagonal_aeval (p : MvPolynomial (Fin n) R) :
    (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv
        (MvPolynomial.aeval (fun i : Fin n ↦ (genericMatrix R n).charpoly.coeff i) p) =
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n)
        (MvPolynomial.vietaAlgHom R n p) := by
  have h : (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv.comp
        (MvPolynomial.aeval fun i : Fin n ↦ (genericMatrix R n).charpoly.coeff i) =
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) (DiagRing R n)).comp
        (MvPolynomial.vietaAlgHom R n) :=
    MvPolynomial.algHom_ext fun i ↦ by
      simp [genericDiagonal_coeff_charpoly]
  exact AlgHom.congr_fun h p

private theorem specialize_algebraMap_rename (σ : Equiv.Perm (Fin n))
    (p : MvPolynomial (Fin n) R) :
    specialize (fun i ↦ genericUnit (R := R) (n := n) (σ i))
        (algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) p) =
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) (MvPolynomial.rename σ p) := by
  have h : MvPolynomial.aeval (fun i ↦ (genericUnit (R := R) (n := n) (σ i) : DiagRing R n)) =
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) (DiagRing R n)).comp
        (MvPolynomial.rename σ) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [genericUnit]
  rw [specialize_algebraMap, h, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]

/-- At the generic diagonal point, `charpolyCoeffAlgHom` reads a polynomial `p` in the
characteristic polynomial coefficients as `p` evaluated at the coefficients of `∏ⱼ (T - tⱼ)`. -/
private theorem genericDiagonal_charpolyCoeffAlgHom_algebraMap [NeZero n]
    (p : MvPolynomial (Fin n) R) :
    (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv
        (charpolyCoeffAlgHom R n (algebraMap (MvPolynomial (Fin n) R) _ p) :
          coordinateHopfAlgebra R n) =
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) (MvPolynomial.vietaAlgHom R n p) := by
  rw [coe_charpolyCoeffAlgHom_algebraMap, genericDiagonal_aeval]

/-- The value of a class function at the generic diagonal point, cleared of denominators, is a
symmetric polynomial. -/
private theorem mem_symmetricSubalgebra_of_genericDiagonal {f : coordinateHopfAlgebra R n}
    (hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n)) {m : ℕ}
    {p : MvPolynomial (Fin n) R}
    (hp : (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv f *
        algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) (∏ i : Fin n, MvPolynomial.X i) ^ m =
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) p) :
    p ∈ MvPolynomial.symmetricSubalgebra (Fin n) R := by
  rw [MvPolynomial.mem_symmetricSubalgebra]
  intro σ
  have hprod : MvPolynomial.rename σ (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) R) =
      ∏ i, MvPolynomial.X i := by
    simp only [map_prod, MvPolynomial.rename_X]
    exact Equiv.prod_comp σ MvPolynomial.X
  have h := congrArg (specialize fun i ↦ genericUnit (R := R) (n := n) (σ i)) hp
  rw [map_mul, map_pow, specialize_algebraMap_rename, specialize_algebraMap_rename, hprod,
    ← diagonalPoint_apply_eq_specialize, diagonalPoint_apply_comp_perm_of_mem_classFunctions hf,
    hp] at h
  exact (MvPolynomial.algebraMap_injective_of_isLocalizationAway_prod_X (DiagRing R n)
    Finset.univ h).symm

/-! ### The conjugation invariants of `GLₙ` -/

/-- **The characteristic polynomial coefficients are algebraically independent on `GLₙ`** over
every commutative ring. -/
theorem charpolyCoeffAlgHom_injective [NeZero n] :
    Function.Injective (charpolyCoeffAlgHom R n) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨m, p, hp⟩ :=
    IsLocalization.Away.surj (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) R) q
  have h1 : charpolyCoeffAlgHom R n (algebraMap (MvPolynomial (Fin n) R) _ p) = 0 := by
    rw [← hp, map_mul, hq, zero_mul]
  have h2 := genericDiagonal_charpolyCoeffAlgHom_algebraMap (R := R) p
  rw [h1, ZeroMemClass.coe_zero, map_zero] at h2
  have hp0 : p = 0 := MvPolynomial.vietaAlgHom_injective R n
    (MvPolynomial.algebraMap_injective_of_isLocalizationAway_prod_X (DiagRing R n) Finset.univ
      (by rw [← h2, map_zero, map_zero]))
  rw [hp0, map_zero] at hp
  exact ((IsLocalization.Away.algebraMap_isUnit _).pow m).mul_left_eq_zero.1 hp

end GenericDiagonal

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

/-- **A class function of `GLₙ` over a domain is determined by its value at the generic diagonal
point.** -/
private theorem eq_of_genericDiagonal {f g : coordinateHopfAlgebra R n}
    (hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n))
    (hg : g ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n))
    (h : (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv f =
      (diagonalPoint (R := R) (genericUnit (R := R) (n := n))).ofConv g) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_diagonalPoint (Subalgebra.sub_mem _ hf hg) fun t ↦ ?_
  rw [diagonalPoint_apply_eq_specialize, map_sub, h, sub_self, map_zero]

variable [NeZero n]

/-- **The characteristic polynomial coefficients generate the class functions of `GLₙ`.** -/
theorem charpolyCoeffAlgHom_surjective : Function.Surjective (charpolyCoeffAlgHom R n) := by
  rintro ⟨f, hf₀⟩
  have hf : f ∈ HopfAlgebra.classFunctions R (coordinateHopfAlgebra R n) :=
    HopfAlgebra.conjugationInvariants_eq_classFunctions R (coordinateHopfAlgebra R n) ▸ hf₀
  let δ := diagonalPoint (R := R) (genericUnit (R := R) (n := n))
  have hδ (q : MvPolynomial (Fin n) R) :
      δ.ofConv (charpolyCoeffAlgHom R n (algebraMap _ _ q) : coordinateHopfAlgebra R n) =
        algebraMap _ (DiagRing R n) (MvPolynomial.vietaAlgHom R n q) :=
    genericDiagonal_charpolyCoeffAlgHom_algebraMap q
  -- At the generic diagonal point, `f` is `p / (t₁ ⋯ tₙ)^m` with `p` a symmetric polynomial, so
  -- `p` is `vietaAlgHom Q` for a polynomial `Q` in the characteristic polynomial coefficients.
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj
    (∏ i : Fin n, MvPolynomial.X i : MvPolynomial (Fin n) R) (δ.ofConv f)
  obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).1 <| MvPolynomial.range_vietaAlgHom R n ▸
    mem_symmetricSubalgebra_of_genericDiagonal hf hp
  -- Since `c₀ = (-1)ⁿ t₁ ⋯ tₙ` at the generic diagonal point, the preimage of `f` is
  -- `(-1)^(nm) Q / c₀^m`.
  let s : R := (-1) ^ (n * m)
  let x : MvPolynomial (Fin n) R := MvPolynomial.X 0
  let F := charpolyCoeffAlgHom R n
    (algebraMap _ _ (MvPolynomial.C s * Q) * IsLocalization.Away.invSelf x ^ m)
  have hF : F * charpolyCoeffAlgHom R n (algebraMap _ _ x) ^ m =
      charpolyCoeffAlgHom R n (algebraMap _ _ (MvPolynomial.C s * Q)) := by
    rw [← map_pow, ← map_mul, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf x),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  -- Both `F` and `f` are class functions, so it suffices to compare their values at `δ`.
  refine ⟨algebraMap _ _ (MvPolynomial.C s * Q) * IsLocalization.Away.invSelf x ^ m,
    Subtype.ext (eq_of_genericDiagonal (f := (F : coordinateHopfAlgebra R n)) ?_ hf ?_)⟩
  · exact HopfAlgebra.conjugationInvariants_eq_classFunctions R (coordinateHopfAlgebra R n) ▸
      F.property
  -- Read `hF` at `δ`: `δ(F) · ((-1)ⁿ t₁ ⋯ tₙ)^m = (-1)^(nm) p`.
  have h1 := congrArg (fun y : HopfAlgebra.conjugationInvariants R (coordinateHopfAlgebra R n) ↦
    δ.ofConv (y : coordinateHopfAlgebra R n)) hF
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_pow, hδ] at h1
  have hx : MvPolynomial.vietaAlgHom R n x = (-1) ^ n * ∏ j : Fin n, MvPolynomial.X j := by
    simp only [x, MvPolynomial.vietaAlgHom_X, Fin.val_zero, MvPolynomial.prod_X_sub_C_coeff_zero]
  simp only [hQ, hx, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, map_mul, mul_pow, map_pow,
    map_neg, map_one, ← pow_mul, ← IsScalarTower.algebraMap_apply] at h1
  have hs : algebraMap R (DiagRing R n) s = (-1) ^ (n * m) := by simp [s]
  rw [hs] at h1
  -- Comparing with `hp`, `δ(F) - δ(f)` is killed by a unit.
  have key : (δ.ofConv F - δ.ofConv f) * ((-1) ^ (n * m) *
        algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) (∏ i : Fin n, MvPolynomial.X i) ^ m) =
      0 := by
    linear_combination h1 - (-1) ^ (n * m) * hp
  have hu : IsUnit ((-1 : DiagRing R n) ^ (n * m) *
      algebraMap (MvPolynomial (Fin n) R) (DiagRing R n) (∏ i : Fin n, MvPolynomial.X i) ^ m) :=
    (isUnit_one.neg.pow _).mul ((IsLocalization.Away.algebraMap_isUnit _).pow m)
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 key)

/-- **The conjugation invariants of `GLₙ` over a domain are `R[c₀^{±1}, c₁, …, c_{n-1}]`**: the
polynomial ring in the coefficients `c₀, …, c_{n-1}` of the characteristic polynomial with only the
constant coefficient `c₀ = (-1)ⁿ det` inverted. -/
noncomputable def charpolyCoeffAlgEquiv :
    Localization.Away (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) R) ≃ₐ[R]
      HopfAlgebra.conjugationInvariants R (coordinateHopfAlgebra R n) :=
  AlgEquiv.ofBijective (charpolyCoeffAlgHom R n)
    ⟨charpolyCoeffAlgHom_injective, charpolyCoeffAlgHom_surjective⟩

/-- `charpolyCoeffAlgEquiv` is `charpolyCoeffAlgHom`. -/
@[simp]
theorem charpolyCoeffAlgEquiv_apply
    (x : Localization.Away (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) R)) :
    charpolyCoeffAlgEquiv x = charpolyCoeffAlgHom R n x :=
  AlgEquiv.ofBijective_apply _ _ x

open _root_.AlgebraicGeometry _root_.CategoryTheory in
/-- **`Conj_{GLₙ} ≅ 𝔸^{n-1} × 𝔾ₘ` over a domain**: the characteristic polynomial on the
conjugation quotient is an isomorphism of schemes. -/
instance isIso_charpolyQuotientMap : IsIso (charpolyQuotientMap R n) := by
  rw [charpolyQuotientMap_eq]
  have : IsIso (CommRingCat.ofHom (charpolyCoeffAlgHom R n).toRingHom) :=
    (RingEquiv.toCommRingCatIso (charpolyCoeffAlgEquiv (R := R) (n := n)).toRingEquiv).isIso_hom
  infer_instance

end Domain

end TauCeti.GeneralLinear
