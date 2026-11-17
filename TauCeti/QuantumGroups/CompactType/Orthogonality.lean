/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Conjugate
public import TauCeti.Algebra.Coalgebra.Comodule.Schur
public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.QuantumGroups.CompactType.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.LinearAlgebra.Matrix.Transpose

/-!
# Weighted Schur orthogonality for Hopf star algebras

Let `A` be a star bialgebra (or Hopf star algebra) and `h : A → R` an invariant integral.
Right invariance averages `star (u i j) * v k l` into an intertwiner between the comodules of `u`
and `v`; left invariance averages `u i j * star (v k l)` similarly. Consequently, coefficients of
comodules admitting no nonzero intertwiner (in particular, simple comodules with distinct
coefficient spaces) with unitary coefficient matrices are orthogonal under `h`.

For a single simple comodule over an algebraically closed field with unitary coefficient matrix `u`,
any invertible matrix `Ft` unitarizing the conjugate corepresentation `u.map star`
(`(u.map star)ᴴ * Ft * (u.map star) = Ft`) determines both orthogonality relations under a
normalized two-sided invariant integral `h`:
* `h (star (u i j) * u k l) = δ j l * Ft⁻¹ i k / trace Ft⁻¹`,
* `h (u i j * star (u k l)) = δ i k * Ft j l / trace Ft`,
and (when `A` is a Hopf star algebra) implements the squared antipode via its transpose `F = Ftᵀ`:
`S²(u) = F * u * F⁻¹`. Over `ℝ` or `ℂ`, rescaling a positive definite unitarizer `Ft` so that
`trace Ft = trace Ft⁻¹` makes `Ft` unique. When `h` is an `AlgebraicHaar` on a complex Hopf star
algebra, the Haar Gram matrix of the conjugate comodule `u.map star` provides such a positive
definite unitarizer, yielding weighted Schur orthogonality.

## Main declarations

* `TauCeti.apply_star_mul_coefficientMatrix_eq_zero_of_forall_hom_eq_zero` and
  `TauCeti.apply_coefficientMatrix_mul_star_eq_zero_of_forall_hom_eq_zero`: orthogonality of
  comodules with no nonzero intertwiner under one-sided invariant integrals.
* `TauCeti.apply_star_mul_coefficientMatrix_eq_zero_of_matrixCoefficientSubmodule_ne` and
  `TauCeti.apply_coefficientMatrix_mul_star_eq_zero_of_matrixCoefficientSubmodule_ne`:
  orthogonality of simple comodules with distinct coefficient spaces.
* `Module.Basis.map_antipode_antipode_coefficientMatrix_eq`: `S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹` from any
  invertible unitarizer `Ft` of `u.map star`.
* `TauCeti.apply_star_mul_coefficientMatrix_eq_of_isUnit_unitarizer` and
  `TauCeti.apply_coefficientMatrix_mul_star_eq_of_isUnit_unitarizer`: weighted Schur orthogonality
  from a normalized two-sided invariant integral and any invertible unitarizer of `u.map star`
  (without assuming positivity of `h`).
* `Module.Basis.eq_of_apply_coefficientMatrix_mul_star_eq`: uniqueness of a trace-normalized
  positive definite weight matrix from the second orthogonality relation.
* `TauCeti.AlgebraicHaar.schurWeight` and `TauCeti.AlgebraicHaar.schurWeight_eq`: the canonical
  normalized positive definite weight matrix `Ft` for a finite basis.
* `TauCeti.schur_orthogonality` and `TauCeti.Comodule.IsUnitary.schur_orthogonality`: weighted
  Schur orthogonality with uniqueness of the normalized weight matrix.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.4.2 and Section 1.7.
-/

public noncomputable section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti

section InvariantAveraging

section Semiring

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Bialgebra R A] [StarRing A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]

/-- Right invariance averages `star (u i p) * v k q` into a matrix invariant under
`E ↦ uᴴ * E * v`. -/
private theorem conjTranspose_mul_rightAvg_mul [Fintype ι] [Fintype κ] {h : A →ₗ[R] R}
    (hh : h.IsRightInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N) (i : ι) (k : κ) :
    let u := Comodule.coefficientMatrix (C := A) b
    let v := Comodule.coefficientMatrix (C := A) c
    let E : Matrix ι κ R := Matrix.of fun p q ↦ h (star (u i p) * v k q)
    uᴴ * E.map (algebraMap R A) * v = E.map (algebraMap R A) := by
  intro u v E
  ext j l
  calc (uᴴ * E.map (algebraMap R A) * v) j l
      = ∑ p, ∑ q, h (star (u i p) * v k q) • (star (u p j) * v q l) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, E, Matrix.of_apply,
          Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
        rw [Finset.sum_comm]
    _ = h (star (u i j) * v k l) • (1 : A) := by
        simpa [u, v] using hh.sum_sum_mul
          (b.coefficientMatrixRepr (C := A) i j).star (c.coefficientMatrixRepr (C := A) k l)
    _ = (E.map (algebraMap R A)) j l := by
        simp [E, Algebra.algebraMap_eq_smul_one]

/-- Left invariance averages `u p j * star (v q l)` into a matrix invariant under
`E ↦ u * E * vᴴ`. -/
private theorem mul_leftAvg_mul_conjTranspose [Fintype ι] [Fintype κ] {h : A →ₗ[R] R}
    (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N) (j : ι) (l : κ) :
    let u := Comodule.coefficientMatrix (C := A) b
    let v := Comodule.coefficientMatrix (C := A) c
    let E : Matrix ι κ R := Matrix.of fun p q ↦ h (u p j * star (v q l))
    u * E.map (algebraMap R A) * vᴴ = E.map (algebraMap R A) := by
  intro u v E
  ext i k
  calc (u * E.map (algebraMap R A) * vᴴ) i k
      = ∑ p, ∑ q, h (u p j * star (v q l)) • (u i p * star (v k q)) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, E, Matrix.of_apply,
          Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
        rw [Finset.sum_comm]
    _ = h (u i j * star (v k l)) • (1 : A) := by
        simpa [u, v] using hh.sum_sum_mul
          (b.coefficientMatrixRepr (C := A) i j) (c.coefficientMatrixRepr (C := A) k l).star
    _ = (E.map (algebraMap R A)) i k := by
        simp [E, Algebra.algebraMap_eq_smul_one]

/-- Left-multiplying `uᴴ * E * v = E` by a unitary matrix `u` yields `u * E = E * v`. -/
private theorem mul_eq_mul_of_conjTranspose_mul_eq [Fintype ι] [Fintype κ] [DecidableEq ι]
    {u : Matrix ι ι A} {v : Matrix κ κ A} {E : Matrix ι κ A}
    (hu : u ∈ unitary (Matrix ι ι A)) (havg : uᴴ * E * v = E) : u * E = E * v := by
  have hu2 : u * uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hu.2
  calc u * E = u * (uᴴ * E * v) := by rw [havg]
    _ = (u * uᴴ) * E * v := by simp only [Matrix.mul_assoc]
    _ = E * v := by rw [hu2, Matrix.one_mul]

/-- Right-multiplying `u * E * vᴴ = E` by a unitary matrix `v` yields `u * E = E * v`. -/
private theorem mul_eq_mul_of_mul_conjTranspose_eq [Fintype ι] [Fintype κ] [DecidableEq κ]
    {u : Matrix ι ι A} {v : Matrix κ κ A} {E : Matrix ι κ A}
    (hv : v ∈ unitary (Matrix κ κ A)) (havg : u * E * vᴴ = E) : u * E = E * v := by
  have hv1 : vᴴ * v = 1 := by simpa [Matrix.star_eq_conjTranspose] using hv.1
  calc u * E = u * E * (vᴴ * v) := by rw [hv1, Matrix.mul_one]
    _ = (u * E * vᴴ) * v := by simp only [Matrix.mul_assoc]
    _ = E * v := by rw [havg]

/-- **General orthogonality under a right invariant integral.** If there is no nonzero comodule
morphism from `N` to `M` and `u` is unitary, then `h (star (u i j) * v k l) = 0`. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_forall_hom_eq_zero [Fintype ι] [DecidableEq ι]
    [Finite κ] (hzero : ∀ f : Comodule.Hom R A N M, f = 0)
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j : ι) (k l : κ) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) c k l) = 0 := by
  have : Fintype κ := Fintype.ofFinite κ
  set u := Comodule.coefficientMatrix (C := A) b
  set v := Comodule.coefficientMatrix (C := A) c
  let E : Matrix ι κ R := Matrix.of fun p q ↦ h (star (u i p) * v k q)
  have hinter : u * E.map (algebraMap R A) = E.map (algebraMap R A) * v :=
    mul_eq_mul_of_conjTranspose_mul_eq hu (conjTranspose_mul_rightAvg_mul hh b c i k)
  exact congrFun (congrFun (c.eq_zero_of_coefficientMatrix_mul_eq b hzero hinter) j) l

/-- **General orthogonality under a left invariant integral.** If there is no nonzero comodule
morphism from `N` to `M` and `v` is unitary, then `h (u i j * star (v k l)) = 0`. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_forall_hom_eq_zero [Finite ι]
    [Fintype κ] [DecidableEq κ] (hzero : ∀ f : Comodule.Hom R A N M, f = 0)
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hv : Comodule.coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (i j : ι) (k l : κ) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) c k l)) = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  set u := Comodule.coefficientMatrix (C := A) b
  set v := Comodule.coefficientMatrix (C := A) c
  let E : Matrix ι κ R := Matrix.of fun p q ↦ h (u p j * star (v q l))
  have hinter : u * E.map (algebraMap R A) = E.map (algebraMap R A) * v :=
    mul_eq_mul_of_mul_conjTranspose_eq hv (mul_leftAvg_mul_conjTranspose hh b c j l)
  exact congrFun (congrFun (c.eq_zero_of_coefficientMatrix_mul_eq b hzero hinter) i) k

end Semiring

section SimpleDistinct

variable {R A M N ι κ : Type*} [CommRing R] [StarRing R]
  [Ring A] [Bialgebra R A] [Module.Projective R A] [StarRing A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M]
  [AddCommGroup N] [Module R N] [Comodule R A N]

/-- **Schur orthogonality between non-isomorphic simple comodules (right invariant form).**
If `h` is right invariant and `u` is unitary, then `h (star (u i j) * v k l) = 0` whenever `M`
and `N` are simple comodules with distinct coefficient spaces. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_matrixCoefficientSubmodule_ne
    [Fintype ι] [DecidableEq ι]
    [IsSimpleOrder (Subcomodule R A M)] [IsSimpleOrder (Subcomodule R A N)]
    (hne : Comodule.matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      Comodule.matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j : ι) (k l : κ) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) c k l) = 0 := by
  have : Nontrivial N := Comodule.nontrivial_of_isSimpleOrder (R := R) (C := A)
  have : Nontrivial R := Module.nontrivial R N
  have : Module.Finite R N := Comodule.finite_of_isSimpleOrder (R := R) (C := A)
  have : Finite κ := Module.Finite.finite_basis c
  exact apply_star_mul_coefficientMatrix_eq_zero_of_forall_hom_eq_zero
    (Comodule.Hom.eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) hh b c hu i j k l

/-- **Schur orthogonality between non-isomorphic simple comodules (left invariant form).**
If `h` is left invariant and `v` is unitary, then `h (u i j * star (v k l)) = 0` whenever `M`
and `N` are simple comodules with distinct coefficient spaces. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_matrixCoefficientSubmodule_ne
    [Fintype κ] [DecidableEq κ]
    [IsSimpleOrder (Subcomodule R A M)] [IsSimpleOrder (Subcomodule R A N)]
    (hne : Comodule.matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      Comodule.matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hv : Comodule.coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (i j : ι) (k l : κ) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) c k l)) = 0 := by
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := R) (C := A)
  have : Nontrivial R := Module.nontrivial R M
  have : Module.Finite R M := Comodule.finite_of_isSimpleOrder (R := R) (C := A)
  have : Finite ι := Module.Finite.finite_basis b
  exact apply_coefficientMatrix_mul_star_eq_zero_of_forall_hom_eq_zero
    (Comodule.Hom.eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) hh b c hv i j k l

end SimpleDistinct

end InvariantAveraging

end TauCeti

namespace Module.Basis

open TauCeti

section SquaredAntipode

variable {R A M ι : Type*} [CommRing R] [StarRing R]
  [Semiring A] [HopfAlgebra R A] [StarRing A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]

/-- An invertible unitarizer `Ft` of `u.map star` satisfies
`Ft⁻¹ * (u.map star)ᴴ * Ft = (S² u)ᵀ`. -/
private theorem inv_mul_conjTranspose_map_star_mul (b : Basis ι R M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι R} (hFt : IsUnit Ft)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap R A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap R A)) :
    Ft⁻¹.map (algebraMap R A) * ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap R A) =
      ((Comodule.coefficientMatrix (C := A) b).map
        (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ := by
  set f := algebraMap R A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  set w := (u.map (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)))ᵀ
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt
  have hFInvF : Ft⁻¹.map f * Ft.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul Ft hdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have huw : ubar * w = 1 :=
    b.map_star_coefficientMatrix_mul_transpose_antipode_antipode hu
  calc Ft⁻¹.map f * ubarᴴ * Ft.map f
      = Ft⁻¹.map f * ubarᴴ * Ft.map f * (ubar * w) := by rw [huw, Matrix.mul_one]
    _ = Ft⁻¹.map f * (ubarᴴ * Ft.map f * ubar) * w := by simp only [Matrix.mul_assoc]
    _ = (Ft⁻¹.map f * Ft.map f) * w := by rw [hinv, Matrix.mul_assoc]
    _ = w := by rw [hFInvF, Matrix.one_mul]

/-- Any invertible unitarizer `Ft` of the conjugate corepresentation `u.map star`
implements the squared antipode on `u` via its transpose `Ftᵀ`:
`S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹`. -/
theorem map_antipode_antipode_coefficientMatrix_eq (b : Basis ι R M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι R} (hFt : IsUnit Ft)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap R A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap R A)) :
    (Comodule.coefficientMatrix (C := A) b).map
      (fun a ↦ HopfAlgebra.antipode R (HopfAlgebra.antipode R a)) =
      Ftᵀ.map (algebraMap R A) * Comodule.coefficientMatrix (C := A) b *
        (Ftᵀ)⁻¹.map (algebraMap R A) := by
  have hw := b.inv_mul_conjTranspose_map_star_mul hu hFt hinv
  have hubarT : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴᵀ =
      Comodule.coefficientMatrix (C := A) b := by
    ext i j
    simp [conjTranspose_apply]
  have htrans := congrArg Matrix.transpose hw
  rw [Matrix.transpose_mul_map_algebraMap, Matrix.transpose_map_algebraMap_mul, hubarT,
    Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc] at htrans
  simpa using htrans.symm

end SquaredAntipode

end Module.Basis

namespace TauCeti

section UnifiedOrthogonality

section BialgebraUnitarizer

variable {k A M ι : Type*} [Field k] [IsAlgClosed k] [StarRing k]
  [Ring A] [Bialgebra k A] [StarRing A] [StarModule k A] [StarCoalgebra k A]
  [AddCommGroup M] [Module k M] [Comodule k A M]
  [IsSimpleOrder (Subcomodule k A M)] [Fintype ι] [DecidableEq ι]

/-- Matrix Schur's lemma for the conjugate corepresentation `u.map star`: any scalar matrix
commuting with `(coefficientMatrix b).map star` on a simple comodule over an algebraically closed
field is a scalar multiple of the identity matrix. -/
private theorem exists_eq_smul_one_of_map_star_coefficientMatrix_mul_eq (b : Basis ι k M)
    {T : Matrix ι ι k}
    (hT : (Comodule.coefficientMatrix (C := A) b).map star * T.map (algebraMap k A) =
      T.map (algebraMap k A) * (Comodule.coefficientMatrix (C := A) b).map star) :
    ∃ c : k, T = c • (1 : Matrix ι ι k) := by
  let _ : Comodule k A (ι → k) := b.conjugateMatrixComodule (C := A)
  have : IsSimpleOrder (Subcomodule k A (ι → k)) := b.isSimpleOrder_conjugateMatrixComodule
  have hcomm : Comodule.coefficientMatrix (C := A) (Pi.basisFun k ι) * T.map (algebraMap k A) =
      T.map (algebraMap k A) * Comodule.coefficientMatrix (C := A) (Pi.basisFun k ι) := by
    simpa only [b.coefficientMatrix_conjugateMatrixComodule] using hT
  exact (Pi.basisFun k ι).exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm

/-- Right and left invariance factor `h (star (u i j) * u k l)` into `δ j l * C i k`, where `C`
has trace `1` and satisfies `ubar * C * ubarᴴ = C`. -/
private theorem exists_star_mul_factor {h : A →ₗ[k] k}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι k M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ C : Matrix ι ι k, C.trace = 1 ∧
      (Comodule.coefficientMatrix (C := A) b).map star * C.map (algebraMap k A) *
        ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ = C.map (algebraMap k A) ∧
      ∀ i j k l, h (star (Comodule.coefficientMatrix (C := A) b i j) *
        Comodule.coefficientMatrix (C := A) b k l) = if j = l then C i k else 0 := by
  set f := algebraMap k A
  set u := Comodule.coefficientMatrix (C := A) b
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := k) (C := A)
  obtain ⟨j₀⟩ := b.index_nonempty
  have hfactor (p r : ι) : ∃ c : k, ∀ q s, h (star (u p q) * u r s) = if q = s then c else 0 := by
    let E : Matrix ι ι k := Matrix.of fun q s ↦ h (star (u p q) * u r s)
    have hcomm : u * E.map f = E.map f * u :=
      mul_eq_mul_of_conjTranspose_mul_eq hu (conjTranspose_mul_rightAvg_mul hR b b p r)
    obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm
    exact ⟨c, fun q s ↦ by simpa [E, Matrix.one_apply] using congrFun (congrFun hc q) s⟩
  let C : Matrix ι ι k := Matrix.of fun p r ↦ h (star (u p j₀) * u r j₀)
  refine ⟨C, ?_, ?_, fun p q r s ↦ ?_⟩
  · have hu1 : (uᴴ * u) j₀ j₀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using congrFun (congrFun hu.1 j₀) j₀
    calc C.trace = ∑ p, h (star (u p j₀) * u p j₀) := rfl
      _ = h (∑ p, star (u p j₀) * u p j₀) := (map_sum h _ _).symm
      _ = h ((uᴴ * u) j₀ j₀) := by simp [Matrix.mul_apply, conjTranspose_apply]
      _ = 1 := by rw [hu1, h1]
  · let _ : Comodule k A (ι → k) := b.conjugateMatrixComodule (C := A)
    simpa only [b.coefficientMatrix_conjugateMatrixComodule, Matrix.map_apply, star_star] using
      mul_leftAvg_mul_conjTranspose hL (Pi.basisFun k ι) (Pi.basisFun k ι) j₀ j₀
  · obtain ⟨c, hc⟩ := hfactor p r
    have hcj : C p r = c := by simpa [C] using hc j₀ j₀
    rw [hcj]
    exact hc q s

/-- Left and right invariance factor `h (u i j * star (u k l))` into `δ i k * D j l`, where `D`
has trace `1` and satisfies `ubarᴴ * D * ubar = D`. -/
private theorem exists_mul_star_factor {h : A →ₗ[k] k}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι k M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ D : Matrix ι ι k, D.trace = 1 ∧
      ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ * D.map (algebraMap k A) *
        (Comodule.coefficientMatrix (C := A) b).map star = D.map (algebraMap k A) ∧
      ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) = if i = k then D j l else 0 := by
  set f := algebraMap k A
  set u := Comodule.coefficientMatrix (C := A) b
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := k) (C := A)
  obtain ⟨i₀⟩ := b.index_nonempty
  have hfactor (q s : ι) : ∃ d : k, ∀ p r, h (u p q * star (u r s)) = if p = r then d else 0 := by
    let E : Matrix ι ι k := Matrix.of fun p r ↦ h (u p q * star (u r s))
    have hcomm : u * E.map f = E.map f * u :=
      mul_eq_mul_of_mul_conjTranspose_eq hu (mul_leftAvg_mul_conjTranspose hL b b q s)
    obtain ⟨d, hd⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm
    exact ⟨d, fun p r ↦ by simpa [E, Matrix.one_apply] using congrFun (congrFun hd p) r⟩
  let D : Matrix ι ι k := Matrix.of fun q s ↦ h (u i₀ q * star (u i₀ s))
  refine ⟨D, ?_, ?_, fun p q r s ↦ ?_⟩
  · have hu2 : (u * uᴴ) i₀ i₀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using congrFun (congrFun hu.2 i₀) i₀
    calc D.trace = ∑ q, h (u i₀ q * star (u i₀ q)) := rfl
      _ = h (∑ q, u i₀ q * star (u i₀ q)) := (map_sum h _ _).symm
      _ = h ((u * uᴴ) i₀ i₀) := by simp [Matrix.mul_apply, conjTranspose_apply]
      _ = 1 := by rw [hu2, h1]
  · let _ : Comodule k A (ι → k) := b.conjugateMatrixComodule (C := A)
    simpa only [b.coefficientMatrix_conjugateMatrixComodule, Matrix.map_apply, star_star] using
      conjTranspose_mul_rightAvg_mul hR (Pi.basisFun k ι) (Pi.basisFun k ι) i₀ i₀
  · obtain ⟨d, hd⟩ := hfactor q s
    have hdi : D q s = d := by simpa [D] using hd i₀ i₀
    rw [hdi]
    exact hd p r

/-- **First weighted Schur orthogonality relation** for a normalized two-sided invariant integral
on a star bialgebra and any invertible unitarizer `Ft` of the conjugate corepresentation
`u.map star`. No positivity hypothesis on `h` or antipode on `A` is required. -/
theorem apply_star_mul_coefficientMatrix_eq_of_isUnit_unitarizer {h : A →ₗ[k] k}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι k M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι k} (hFt : IsUnit Ft)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap k A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap k A)) (i j l m : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) b l m) =
      if j = m then Ft⁻¹ i l / Ft⁻¹.trace else 0 := by
  set f := algebraMap k A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  obtain ⟨C, hCtr, hC_inv, hC_eq⟩ := exists_star_mul_factor h1 hL hR b hu
  have hcomm_ubar : ubar * (C * Ft).map f = (C * Ft).map f * ubar := by
    rw [Matrix.map_mul]
    calc ubar * (C.map f * Ft.map f)
        = ubar * C.map f * (ubarᴴ * Ft.map f * ubar) := by rw [hinv, Matrix.mul_assoc]
      _ = (ubar * C.map f * ubarᴴ) * Ft.map f * ubar := by simp only [Matrix.mul_assoc]
      _ = C.map f * Ft.map f * ubar := by rw [hC_inv]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_map_star_coefficientMatrix_mul_eq b hcomm_ubar
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt
  have hC_smul : C = c • Ft⁻¹ := by
    calc C = (C * Ft) * Ft⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Ft hdet, Matrix.mul_one]
      _ = (c • (1 : Matrix ι ι k)) * Ft⁻¹ := by rw [hc]
      _ = c • Ft⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hc_val : c = (Ft⁻¹.trace)⁻¹ := by
    have htr : c * Ft⁻¹.trace = 1 := by
      rw [← smul_eq_mul, ← Matrix.trace_smul, ← hC_smul, hCtr]
    exact eq_inv_of_mul_eq_one_left htr
  rw [hC_eq i j l m, hC_smul, hc_val]
  simp [Matrix.smul_apply, div_eq_inv_mul]

end BialgebraUnitarizer

section HopfUnitarizer

variable {k A M ι : Type*} [Field k] [IsAlgClosed k] [StarRing k]
  [Ring A] [HopfAlgebra k A] [StarRing A] [StarModule k A] [StarCoalgebra k A]
  [AddCommGroup M] [Module k M] [Comodule k A M]
  [IsSimpleOrder (Subcomodule k A M)] [Fintype ι] [DecidableEq ι]

/-- **Second weighted Schur orthogonality relation** for a normalized two-sided invariant integral
on a Hopf star algebra and any invertible unitarizer `Ft` of the conjugate corepresentation
`u.map star`. No positivity hypothesis on `h` is required. -/
theorem apply_coefficientMatrix_mul_star_eq_of_isUnit_unitarizer {h : A →ₗ[k] k}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι k M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι k} (hFt : IsUnit Ft)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap k A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap k A)) (i j l m : ι) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) b l m)) =
      if i = l then Ft j m / Ft.trace else 0 := by
  set f := algebraMap k A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  obtain ⟨D, hDtr, hD_inv, hD_eq⟩ := exists_mul_star_factor h1 hL hR b hu
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt
  have hFFInv : Ft.map f * Ft⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Ft hdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hw := b.inv_mul_conjTranspose_map_star_mul hu hFt hinv
  have huw := b.map_star_coefficientMatrix_mul_transpose_antipode_antipode hu
  have hcomm_ubar : ubar * (Ft⁻¹ * D).map f = (Ft⁻¹ * D).map f * ubar := by
    rw [Matrix.map_mul]
    calc ubar * (Ft⁻¹.map f * D.map f)
        = ubar * (Ft⁻¹.map f * (ubarᴴ * D.map f * ubar)) := by rw [hD_inv]
      _ = ubar * (Ft⁻¹.map f * ubarᴴ * (Ft.map f * Ft⁻¹.map f) * D.map f * ubar) := by
          rw [hFFInv, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (ubar * (Ft⁻¹.map f * ubarᴴ * Ft.map f)) * (Ft⁻¹.map f * D.map f) * ubar := by
          simp only [Matrix.mul_assoc]
      _ = Ft⁻¹.map f * D.map f * ubar := by rw [hw, huw, Matrix.one_mul]
  obtain ⟨d, hd⟩ := exists_eq_smul_one_of_map_star_coefficientMatrix_mul_eq b hcomm_ubar
  have hD_smul : D = d • Ft := by
    calc D = Ft * (Ft⁻¹ * D) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Ft hdet, Matrix.one_mul]
      _ = Ft * (d • (1 : Matrix ι ι k)) := by rw [hd]
      _ = d • Ft := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hd_val : d = (Ft.trace)⁻¹ := by
    have htr : d * Ft.trace = 1 := by
      rw [← smul_eq_mul, ← Matrix.trace_smul, ← hD_smul, hDtr]
    exact eq_inv_of_mul_eq_one_left htr
  rw [hD_eq i j l m, hD_smul, hd_val]
  simp [Matrix.smul_apply, div_eq_inv_mul]

end HopfUnitarizer

end UnifiedOrthogonality

end TauCeti

namespace Module.Basis

open TauCeti

section WeightUniqueness

/-- The second Schur orthogonality relation together with positive definiteness and
`trace Ft = trace Ft⁻¹` uniquely determines `Ft`. -/
theorem eq_of_apply_coefficientMatrix_mul_star_eq {𝕜 A M ι : Type*} [RCLike 𝕜]
    [Semiring A] [Algebra 𝕜 A] [Coalgebra 𝕜 A] [Star A]
    [AddCommMonoid M] [Module 𝕜 M] [Comodule 𝕜 A M] [Fintype ι] [DecidableEq ι]
    {h : A →ₗ[𝕜] 𝕜} (b : Basis ι 𝕜 M)
    {Ft₁ Ft₂ : Matrix ι ι 𝕜} (h₁ : Ft₁.PosDef) (h₂ : Ft₂.PosDef)
    (htr₁ : Ft₁.trace = Ft₁⁻¹.trace) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (heq₁ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₁ j l / Ft₁.trace else 0)
    (heq₂ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₂ j l / Ft₂.trace else 0) :
    Ft₁ = Ft₂ := by
  rcases isEmpty_or_nonempty ι with _ | hne
  · exact Subsingleton.elim _ _
  · have h1ne : Ft₁.trace ≠ 0 := h₁.trace_pos.ne'
    obtain ⟨i₀⟩ := hne
    have hsmul : Ft₁ = (Ft₁.trace / Ft₂.trace) • Ft₂ := by
      ext j l
      have hjl := (heq₁ i₀ j i₀ l).symm.trans (heq₂ i₀ j i₀ l)
      simp only [↓reduceIte] at hjl
      simp only [Matrix.smul_apply, smul_eq_mul]
      calc Ft₁ j l = (Ft₁ j l / Ft₁.trace) * Ft₁.trace := (div_mul_cancel₀ _ h1ne).symm
        _ = (Ft₂ j l / Ft₂.trace) * Ft₁.trace := by rw [hjl]
        _ = (Ft₁.trace / Ft₂.trace) * Ft₂ j l := by ring
    exact h₁.eq_of_trace_eq_trace_inv_of_eq_smul h₂ htr₁ htr₂ hsmul

end WeightUniqueness

end Module.Basis

namespace TauCeti

section AlgebraicHaarOrthogonality

variable {A : Type*} [Ring A] [HopfAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [StarCoalgebra ℂ A]

section GeneralBasis

variable {M ι : Type*} [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
  [Fintype ι] [DecidableEq ι]

/-- The canonical normalized positive definite Schur weight matrix `Ft` (whose transpose `F = Ftᵀ`
implements `S²` when the coefficient matrix is unitary) associated with a finite basis `b`. It is
obtained by trace-normalizing the Haar Gram matrix of `b.conjugateMatrixComodule`. -/
@[expose] def AlgebraicHaar.schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (C := A)
  Matrix.normalizePosDefTrace (Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι))

/-- Characterization of `AlgebraicHaar.schurWeight` as the trace normalization of the Haar Gram
matrix of `b.conjugateMatrixComodule`. -/
theorem AlgebraicHaar.schurWeight_eq (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    h.schurWeight b =
      let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (C := A)
      Matrix.normalizePosDefTrace (Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)) :=
  rfl

omit [DecidableEq ι] in
/-- The Haar Gram matrix of the conjugate matrix comodule `b.conjugateMatrixComodule` is positive
definite. -/
private theorem AlgebraicHaar.posDef_haarGramMatrix_conjugateMatrixComodule
    (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    letI : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (C := A)
    (Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)).PosDef := by
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (C := A)
  exact Comodule.posDef_haarGramMatrix (fun _ ha ↦ h.apply_star_mul_self_pos ha) (Pi.basisFun ℂ ι)

/-- The Schur weight matrix `h.schurWeight b` satisfies the unitarizing invariance identity
`(u.map star)ᴴ * (h.schurWeight b) * (u.map star) = h.schurWeight b` for the conjugate
corepresentation `u.map star`. See `AlgebraicHaar.posDef_schurWeight` for positive definiteness. -/
theorem AlgebraicHaar.conjTranspose_map_star_mul_schurWeight_mul (h : AlgebraicHaar A)
    (b : Basis ι ℂ M) :
    ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      (h.schurWeight b).map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      (h.schurWeight b).map (algebraMap ℂ A) := by
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (C := A)
  set G := Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)
  have hG : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (Comodule.coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa only [b.coefficientMatrix_conjugateMatrixComodule] using
      Comodule.conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul
        h.isRightInvariantIntegral (Pi.basisFun ℂ ι)
  have hmap : (h.schurWeight b).map (algebraMap ℂ A) =
      (algebraMap ℝ ℂ (Real.sqrt (RCLike.re G⁻¹.trace / RCLike.re G.trace))) •
        G.map (algebraMap ℂ A) := by
    rw [h.schurWeight_eq b, Matrix.normalizePosDefTrace_def]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    exact (Algebra.smul_def _ _).symm
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hG]

/-- The Schur weight matrix of any finite basis is positive definite. -/
theorem AlgebraicHaar.posDef_schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (h.schurWeight b).PosDef := by
  rw [h.schurWeight_eq b]
  exact (h.posDef_haarGramMatrix_conjugateMatrixComodule b).normalizePosDefTrace

/-- The Schur weight matrix is normalized so that `trace Ft = trace Ft⁻¹`. -/
theorem AlgebraicHaar.trace_schurWeight_eq_trace_inv (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (h.schurWeight b).trace = (h.schurWeight b)⁻¹.trace := by
  rw [h.schurWeight_eq b]
  exact (h.posDef_haarGramMatrix_conjugateMatrixComodule b).trace_normalizePosDefTrace_eq_trace_inv

/-- The transpose of `h.schurWeight b` implements `S²` on any unitary coefficient matrix:
`S²(u) = F * u * F⁻¹` where `F = (h.schurWeight b)ᵀ`. -/
theorem AlgebraicHaar.map_antipode_antipode_coefficientMatrix (h : AlgebraicHaar A)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (Comodule.coefficientMatrix (C := A) b).map
      (fun a ↦ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a)) =
      (h.schurWeight b)ᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        ((h.schurWeight b)ᵀ)⁻¹.map (algebraMap ℂ A) :=
  b.map_antipode_antipode_coefficientMatrix_eq hu (h.posDef_schurWeight b).isUnit
    (h.conjTranspose_map_star_mul_schurWeight_mul b)

end GeneralBasis

section SimpleBasis

variable {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

/-- First weighted Schur orthogonality identity in terms of `AlgebraicHaar.schurWeight`. -/
theorem AlgebraicHaar.apply_star_mul_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) b k l) =
      if j = l then (h.schurWeight b)⁻¹ i k / (h.schurWeight b)⁻¹.trace else 0 :=
  apply_star_mul_coefficientMatrix_eq_of_isUnit_unitarizer h.map_one' h.isLeftInvariantIntegral
    h.isRightInvariantIntegral b hu (h.posDef_schurWeight b).isUnit
    (h.conjTranspose_map_star_mul_schurWeight_mul b) i j k l

/-- Second weighted Schur orthogonality identity in terms of `AlgebraicHaar.schurWeight`. -/
theorem AlgebraicHaar.apply_coefficientMatrix_mul_star (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) b k l)) =
      if i = k then h.schurWeight b j l / (h.schurWeight b).trace else 0 :=
  apply_coefficientMatrix_mul_star_eq_of_isUnit_unitarizer h.map_one' h.isLeftInvariantIntegral
    h.isRightInvariantIntegral b hu (h.posDef_schurWeight b).isUnit
    (h.conjTranspose_map_star_mul_schurWeight_mul b) i j k l

/-- **Weighted Schur orthogonality.** For a simple finite comodule over a complex Hopf star
algebra with an algebraic Haar integral `h` and a basis `b` whose coefficient matrix `u` is
unitary, there is a unique positive definite matrix `Ft` with `trace Ft = trace Ft⁻¹` such that
`h (star (u i j) * u k l) = δ j l * Ft⁻¹ i k / trace Ft⁻¹` and
`h (u i j * star (u k l)) = δ i k * Ft j l / trace Ft`. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (Comodule.coefficientMatrix (C := A) b i j) *
          Comodule.coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  ⟨h.schurWeight b,
    ⟨h.posDef_schurWeight b, h.trace_schurWeight_eq_trace_inv b,
      h.apply_star_mul_coefficientMatrix b hu, h.apply_coefficientMatrix_mul_star b hu⟩,
    fun _ hFt ↦ b.eq_of_apply_coefficientMatrix_mul_star_eq hFt.1 (h.posDef_schurWeight b)
      hFt.2.1 (h.trace_schurWeight_eq_trace_inv b) hFt.2.2.2
      (h.apply_coefficientMatrix_mul_star b hu)⟩

/-- **Weighted Schur orthogonality for a unitary Hilbert comodule.** Specialization of
`TauCeti.schur_orthogonality` to an orthonormal basis of a simple finite-dimensional unitary
comodule. -/
theorem Comodule.IsUnitary.schur_orthogonality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Comodule ℂ A H]
    [IsSimpleOrder (Subcomodule ℂ A H)] (hH : Comodule.IsUnitary ℂ A H)
    (h : AlgebraicHaar A) (b : OrthonormalBasis ι ℂ H) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (Comodule.coefficientMatrix (C := A) b.toBasis i j) *
          Comodule.coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (Comodule.coefficientMatrix (C := A) b.toBasis i j *
          star (Comodule.coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  TauCeti.schur_orthogonality h b.toBasis (b.isUnitary_comodule_iff.mp hH)

end SimpleBasis

end AlgebraicHaarOrthogonality

end TauCeti
