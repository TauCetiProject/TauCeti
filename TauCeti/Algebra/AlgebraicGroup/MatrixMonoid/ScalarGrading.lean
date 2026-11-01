/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.MatrixMonoid.Homogeneous
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Homogeneous degree and the scalar matrices

Comodules over the coordinate bialgebra `R[Xᵢⱼ]` of the monoid of square matrices are the
rational representations of this monoid; for `GLₙ` they are the polynomial representations
(`TauCeti.GeneralLinear.existsUnique_matrixMonoidComodule_iff`). The coordinate bialgebra is the
direct sum of its subcoalgebras `A(d)` of homogeneous coordinates of degree `d`
(`TauCeti.MatrixMonoid.homogeneousSubcoalgebra`, Green's `A(n, d)`). Correspondingly, every
comodule `M` is the internal direct sum of its homogeneous components

`M_d = {m | ρ m ∈ M ⊗ A(d)}`,

each of which is a subcomodule.

The degree is detected by the scalar matrices. The multiplicative monoid `𝔸¹ = Spec R[t]` maps
to the matrices by `s ↦ s • 1`, with coordinate map `π : Xᵢⱼ ↦ δᵢⱼ t`
(`TauCeti.MatrixMonoid.scalarBialgHom`), where `R[t]` is the monoid algebra `R[ℕ]`. A vector `m`
is homogeneous of degree `d` exactly when the scalar matrices act on it through the character
`t ↦ tᵈ`, that is, when `(id ⊗ π) (ρ m) = m ⊗ tᵈ`. For a polynomial representation of `GLₙ`,
the scalar matrices with invertible entry form the central torus, so the degree is the weight of
that torus; this file works with the matrix monoid and does not state the comparison with
`GLₙ`. When the matrices are indexed by an empty type, the coordinate bialgebra is `R` and every
vector has degree `0`.

The proof rests on the identity `(id ⊗ π) (Δ f) = f ⊗ tᵉ` for a homogeneous coordinate `f` of
degree `e`. Coassociativity turns it into the identification of `M_d` with the weight space of
`tᵈ` for the corestriction of `M` along `π`, and the weight decomposition of comodules over the
monoid algebra `R[ℕ]` (`TauCeti.Comodule.isInternal_weightSpace`) gives the direct sum.
Everything holds over an arbitrary commutative ring.

## Main declarations

* `TauCeti.MatrixMonoid.scalarBialgHom`: the coordinate map `Xᵢⱼ ↦ δᵢⱼ t` of the scalar
  matrices.
* `TauCeti.MatrixMonoid.homogeneousSubcomodule`: the vectors of degree `d` of a comodule.
* `TauCeti.MatrixMonoid.mem_homogeneousSubcomodule_iff_lTensor_scalarBialgHom_coact`: a vector
  has degree `d` exactly when the scalar matrices act on it by `tᵈ`.
* `TauCeti.MatrixMonoid.isInternal_homogeneousSubcomodule`: a comodule is the internal direct
  sum of its homogeneous components.
* `TauCeti.MatrixMonoid.homogeneousSubcomodule_zero_eq_top`: for matrices of size zero every
  vector has degree `0`.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, Lecture Notes in Math. 830, Chapter 2.
-/

public section

open scoped TensorProduct
open MvPolynomial

namespace TauCeti.MatrixMonoid

variable (R : Type*) [CommRing R] (ι : Type*)

/-! ### The grading coaction on raw coordinates -/

/-- The grading coaction `Xᵢⱼ ↦ Xᵢⱼ ⊗ t`, which sends a monomial of degree `d` to its tensor
with `tᵈ`. -/
private noncomputable def grading :
    CoordinateRing R ι →ₐ[R] CoordinateRing R ι ⊗[R] MonoidAlgebra R (Multiplicative ℕ) :=
  aeval fun ij ↦ X ij ⊗ₜ MonoidAlgebra.single (.ofAdd 1) 1

private theorem grading_monomial_one (s : ι × ι →₀ ℕ) :
    grading R ι (monomial s 1) =
      monomial s 1 ⊗ₜ MonoidAlgebra.single (.ofAdd s.degree) 1 := by
  induction s using Finsupp.induction with
  | zero => simp [Algebra.TensorProduct.one_def, MonoidAlgebra.one_def]
  | single_add ij k s _ _ ih =>
    rw [monomial_single_add, map_mul, ih, map_pow, grading, aeval_X,
      Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
      MonoidAlgebra.single_pow, MonoidAlgebra.single_mul_single, map_add, Finsupp.degree_single]
    simp [← ofAdd_nsmul, ofAdd_add]

private theorem grading_monomial (s : ι × ι →₀ ℕ) (a : R) :
    grading R ι (monomial s a) =
      monomial s a ⊗ₜ MonoidAlgebra.single (.ofAdd s.degree) 1 := by
  rw [← mul_one a, ← smul_eq_mul, ← smul_monomial, map_smul, grading_monomial_one,
    TensorProduct.smul_tmul']

/-- The coefficient of `tᵈ` in the grading coaction is the homogeneous component of degree
`d`. -/
private theorem tensorComponent_grading (d : ℕ) (p : CoordinateRing R ι) :
    LinearMap.tensorComponent (Comodule.monoidCoeff R (Multiplicative ℕ) (.ofAdd d))
        (grading R ι p) = homogeneousComponent d p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [grading_monomial, LinearMap.tensorComponent_tmul,
      homogeneousComponent_of_mem (isHomogeneous_monomial a rfl)]
    by_cases h : d = s.degree <;> simp [h]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]

variable [DecidableEq ι]

/-- The coordinate map of the scalar matrices `s ↦ s • 1`, on the raw polynomial coordinates:
the diagonal entries go to the variable `t` of `R[t] = R[ℕ]` and the other entries to `0`. -/
private noncomputable def scalarAlgHomAux :
    CoordinateRing R ι →ₐ[R] MonoidAlgebra R (Multiplicative ℕ) :=
  aeval fun ij ↦ if ij.1 = ij.2 then MonoidAlgebra.single (.ofAdd 1) 1 else 0

private theorem counit_comp_scalarAlgHomAux :
    (Bialgebra.counitAlgHom R (MonoidAlgebra R (Multiplicative ℕ))).comp (scalarAlgHomAux R ι) =
      counit R ι := by
  ext ⟨i, j⟩
  by_cases h : i = j <;> simp [scalarAlgHomAux, h]

variable [Fintype ι]

/-- Matrix comultiplication followed by the scalar map on the right factor is the grading
coaction. -/
private theorem map_scalarAlgHomAux_comp_comul :
    (Algebra.TensorProduct.map (AlgHom.id R _) (scalarAlgHomAux R ι)).comp (comul R ι) =
      grading R ι := by
  ext ⟨i, j⟩
  simp [scalarAlgHomAux, grading, TensorProduct.tmul_ite]

/-- Matrix comultiplication followed by the scalar map on the left factor is the grading
coaction with its factors swapped. -/
private theorem map_scalarAlgHomAux_comp_comul' :
    (Algebra.TensorProduct.map (scalarAlgHomAux R ι) (AlgHom.id R _)).comp (comul R ι) =
      (Algebra.TensorProduct.comm R _ _).toAlgHom.comp (grading R ι) := by
  ext ⟨i, j⟩
  simp [scalarAlgHomAux, grading, TensorProduct.ite_tmul]

private theorem map_scalarAlgHomAux_comp_comul_eq :
    (Algebra.TensorProduct.map (scalarAlgHomAux R ι) (scalarAlgHomAux R ι)).comp (comul R ι) =
      (Bialgebra.comulAlgHom R (MonoidAlgebra R (Multiplicative ℕ))).comp
        (scalarAlgHomAux R ι) := by
  ext ⟨i, j⟩
  by_cases h : i = j <;> simp [scalarAlgHomAux, h, TensorProduct.ite_tmul, TensorProduct.tmul_ite]

/-! ### The scalar matrices -/

/-- The coordinate map of the scalar matrices `s ↦ s • 1`, the inclusion of the multiplicative
monoid `𝔸¹` into the monoid of matrices: the diagonal coordinates go to the variable `t` of
`R[t] = R[ℕ]` and the other coordinates to `0`. -/
noncomputable def scalarBialgHom :
    coordinateBialgebra R ι →ₐc[R] MonoidAlgebra R (Multiplicative ℕ) :=
  BialgHom.ofAlgHom ((scalarAlgHomAux R ι).comp (coordinateBialgebraAlgEquiv R ι).symm.toAlgHom)
    (by
      ext c
      obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
      simpa using congr($(counit_comp_scalarAlgHomAux R ι) x))
    (by
      ext c
      obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
      have h := congr($(map_scalarAlgHomAux_comp_comul_eq R ι) x)
      simp only [AlgHom.comp_apply] at h ⊢
      rw [Bialgebra.comulAlgHom_apply, coordinateBialgebra_comul_apply, ← AlgHom.comp_apply,
        ← Algebra.TensorProduct.map_comp]
      simpa [AlgHom.comp_assoc] using h)

private theorem scalarBialgHom_apply (x : CoordinateRing R ι) :
    scalarBialgHom R ι (coordinateBialgebraAlgEquiv R ι x) = scalarAlgHomAux R ι x := by
  simp [scalarBialgHom]

private theorem scalarBialgHom_toCoalgHom_apply (x : CoordinateRing R ι) :
    (scalarBialgHom R ι).toCoalgHom (coordinateBialgebraAlgEquiv R ι x) =
      scalarAlgHomAux R ι x :=
  scalarBialgHom_apply R ι x

/-- The scalar matrices have diagonal coordinates `t` and off-diagonal coordinates `0`. -/
@[simp]
theorem scalarBialgHom_X (i j : ι) :
    scalarBialgHom R ι (coordinateBialgebraAlgEquiv R ι (X (i, j))) =
      if i = j then MonoidAlgebra.single (.ofAdd 1) 1 else 0 := by
  simp [scalarBialgHom_apply, scalarAlgHomAux]

/-! ### Homogeneous components of coordinates -/

/-- The projection of the coordinate bialgebra onto its homogeneous coordinates of degree `d`. -/
private noncomputable def homogeneousProj (d : ℕ) :
    coordinateBialgebra R ι →ₗ[R] coordinateBialgebra R ι :=
  (coordinateBialgebraAlgEquiv R ι).toLinearMap ∘ₗ homogeneousComponent d ∘ₗ
    (coordinateBialgebraAlgEquiv R ι).symm.toLinearMap

private theorem homogeneousProj_apply (d : ℕ) (x : CoordinateRing R ι) :
    homogeneousProj R ι d (coordinateBialgebraAlgEquiv R ι x) =
      coordinateBialgebraAlgEquiv R ι (homogeneousComponent d x) := by
  simp [homogeneousProj]

private theorem homogeneousProj_mem (d : ℕ) (c : coordinateBialgebra R ι) :
    homogeneousProj R ι d c ∈ (homogeneousSubcoalgebra R ι d).toSubmodule := by
  obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
  rw [homogeneousProj_apply, Subcoalgebra.mem_toSubmodule, mem_homogeneousSubcoalgebra]
  exact homogeneousComponent_isHomogeneous d x

private theorem homogeneousProj_of_mem {d : ℕ} {c : coordinateBialgebra R ι}
    (hc : c ∈ (homogeneousSubcoalgebra R ι d).toSubmodule) : homogeneousProj R ι d c = c := by
  obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
  rw [Subcoalgebra.mem_toSubmodule, mem_homogeneousSubcoalgebra] at hc
  rw [homogeneousProj_apply, homogeneousComponent_eq_self hc]

private theorem homogeneousProj_comp_subtype (d : ℕ) :
    homogeneousProj R ι d ∘ₗ (homogeneousSubcoalgebra R ι d).toSubmodule.subtype =
      (homogeneousSubcoalgebra R ι d).toSubmodule.subtype :=
  LinearMap.ext fun c ↦ homogeneousProj_of_mem R ι c.2

private theorem homogeneousProj_idem (d : ℕ) :
    homogeneousProj R ι d ∘ₗ homogeneousProj R ι d = homogeneousProj R ι d :=
  LinearMap.ext fun c ↦ homogeneousProj_of_mem R ι (homogeneousProj_mem R ι d c)

/-- The coefficient of `tᵈ` in `(id ⊗ π) ∘ Δ`, where `π` is the scalar map, is the projection
onto the homogeneous coordinates of degree `d`. -/
private theorem tensorComponent_comp_comul (d : ℕ) :
    LinearMap.tensorComponent
        (Comodule.monoidCoeff R (Multiplicative ℕ) (.ofAdd d) ∘ₗ
          (scalarBialgHom R ι).toLinearMap) ∘ₗ Coalgebra.comul =
      homogeneousProj R ι d := by
  ext c
  obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
  rw [LinearMap.comp_apply, coordinateBialgebra_comul_apply, homogeneousProj_apply,
    ← tensorComponent_grading, ← map_scalarAlgHomAux_comp_comul, AlgHom.comp_apply]
  generalize comul R ι x = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [scalarBialgHom_toCoalgHom_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The coefficient of `tᵈ` in `(π ⊗ id) ∘ Δ`, where `π` is the scalar map, is the projection
onto the homogeneous coordinates of degree `d`. -/
private theorem lid_rTensor_comp_comul (d : ℕ) :
    (TensorProduct.lid R (coordinateBialgebra R ι)).toLinearMap ∘ₗ
        (Comodule.monoidCoeff R (Multiplicative ℕ) (.ofAdd d) ∘ₗ
          (scalarBialgHom R ι).toLinearMap).rTensor _ ∘ₗ Coalgebra.comul =
      homogeneousProj R ι d := by
  ext c
  obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
  have h : grading R ι x = (Algebra.TensorProduct.comm R _ _).symm
      (Algebra.TensorProduct.map (scalarAlgHomAux R ι) (AlgHom.id R _) (comul R ι x)) := by
    rw [← AlgHom.comp_apply, map_scalarAlgHomAux_comp_comul']
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coordinateBialgebra_comul_apply,
    homogeneousProj_apply, ← tensorComponent_grading, h]
  generalize comul R ι x = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [scalarBialgHom_toCoalgHom_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- On coordinates, the coefficient of `tᵈ` in the scalar map is the counit of the homogeneous
component of degree `d`. -/
private theorem monoidCoeff_comp_scalarBialgHom (d : ℕ) :
    Comodule.monoidCoeff R (Multiplicative ℕ) (.ofAdd d) ∘ₗ (scalarBialgHom R ι).toLinearMap =
      Coalgebra.counit ∘ₗ homogeneousProj R ι d := by
  rw [← lid_rTensor_comp_comul]
  refine LinearMap.ext fun c ↦ ?_
  have key (φ : coordinateBialgebra R ι →ₗ[R] R)
      (y : coordinateBialgebra R ι ⊗[R] coordinateBialgebra R ι) :
      Coalgebra.counit (TensorProduct.lid R _ (φ.rTensor _ y)) =
        φ (TensorProduct.rid R _ (Coalgebra.counit.lTensor _ y)) := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [mul_comm]
    | add y z hy hz => simp only [map_add, hy, hz]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, Coalgebra.lTensor_counit_comul,
    TensorProduct.rid_tmul, one_smul]

/-! ### Homogeneous components of comodules -/

section Comodule

variable (M : Type*) [AddCommMonoid M] [Module R M] [Comodule R (coordinateBialgebra R ι) M]

/-- The projection of a comodule onto its vectors of degree `d`: the coefficient of `tᵈ` in the
coaction of the scalar matrices. -/
private noncomputable def degreeProj (d : ℕ) : M →ₗ[R] M :=
  Comodule.coactComponent (R := R) (C := coordinateBialgebra R ι)
    (Comodule.monoidCoeff R (Multiplicative ℕ) (.ofAdd d) ∘ₗ (scalarBialgHom R ι).toLinearMap)

private theorem coact_degreeProj (d : ℕ) (m : M) :
    Comodule.coact (degreeProj R ι M d m) =
      (homogeneousProj R ι d).lTensor M (Comodule.coact (R := R) m) := by
  rw [degreeProj, Comodule.coact_coactComponent, tensorComponent_comp_comul]

private theorem rTensor_degreeProj_coact (d : ℕ) (m : M) :
    (degreeProj R ι M d).rTensor _ (Comodule.coact (R := R) m) =
      (homogeneousProj R ι d).lTensor M (Comodule.coact (R := R) m) := by
  rw [degreeProj, Comodule.rTensor_coactComponent_coact, lid_rTensor_comp_comul]

private theorem coact_mem_range_iff (d : ℕ) (m : M) :
    Comodule.coact (R := R) m ∈
        LinearMap.range ((homogeneousSubcoalgebra R ι d).toSubmodule.subtype.lTensor M) ↔
      (homogeneousProj R ι d).lTensor M (Comodule.coact (R := R) m) = Comodule.coact m := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx, ← LinearMap.lTensor_comp_apply, homogeneousProj_comp_subtype]
  · intro h
    refine ⟨(LinearMap.codRestrict (homogeneousSubcoalgebra R ι d).toSubmodule
      (homogeneousProj R ι d) (homogeneousProj_mem R ι d)).lTensor M (Comodule.coact m), ?_⟩
    rw [← LinearMap.lTensor_comp_apply, LinearMap.subtype_comp_codRestrict, h]

private theorem coact_degreeProj_mem_range (d : ℕ) (m : M) :
    Comodule.coact (degreeProj R ι M d m) ∈
      LinearMap.range ((homogeneousSubcoalgebra R ι d).toSubmodule.subtype.lTensor M) := by
  rw [coact_mem_range_iff, coact_degreeProj, ← LinearMap.lTensor_comp_apply, homogeneousProj_idem]

private theorem degreeProj_eq_self_iff (d : ℕ) (m : M) :
    degreeProj R ι M d m = m ↔
      (homogeneousProj R ι d).lTensor M (Comodule.coact (R := R) m) = Comodule.coact m := by
  constructor
  · intro h
    rw [← coact_degreeProj, h]
  · intro h
    rw [degreeProj, Comodule.coactComponent_apply, monoidCoeff_comp_scalarBialgHom, ← h,
      LinearMap.lTensor_def, LinearMap.tensorComponent_map, LinearMap.comp_assoc,
      homogeneousProj_idem, LinearMap.tensorComponent_def, LinearMap.comp_apply,
      LinearMap.lTensor_comp_apply, h]
    simp

/-- The vectors of degree `d` of a comodule over the matrix-coordinate bialgebra: those whose
coaction has all its coefficients in the homogeneous coordinates of degree `d`. They form a
subcomodule. -/
noncomputable def homogeneousSubcomodule (d : ℕ) : Subcomodule R (coordinateBialgebra R ι) M :=
  let N := (LinearMap.range ((homogeneousSubcoalgebra R ι d).toSubmodule.subtype.lTensor M)).comap
    (Comodule.coact (R := R) (C := coordinateBialgebra R ι) (M := M))
  Subcomodule.ofSubmodule N fun m hm ↦ by
    rw [Submodule.mem_comap, coact_mem_range_iff] at hm
    refine ⟨(LinearMap.codRestrict N (degreeProj R ι M d)
      (coact_degreeProj_mem_range R ι M d)).rTensor _ (Comodule.coact m), ?_⟩
    rw [← LinearMap.rTensor_def, ← LinearMap.rTensor_comp_apply, LinearMap.subtype_comp_codRestrict,
      rTensor_degreeProj_coact, hm]

variable {R ι M} in
/-- A vector has degree `d` exactly when its coaction lies in `M ⊗ A(d)`, for the homogeneous
coordinates `A(d)` of degree `d`. -/
@[simp]
theorem mem_homogeneousSubcomodule {d : ℕ} {m : M} :
    m ∈ homogeneousSubcomodule R ι M d ↔
      Comodule.coact (R := R) m ∈
        LinearMap.range ((homogeneousSubcoalgebra R ι d).toSubmodule.subtype.lTensor M) :=
  Iff.rfl

variable {R ι M} in
/-- **Homogeneous degree is the weight of the scalar matrices.** A vector of a comodule over the
matrix-coordinate bialgebra has degree `d` exactly when the scalar matrices act on it through
the character `t ↦ tᵈ`. -/
theorem mem_homogeneousSubcomodule_iff_lTensor_scalarBialgHom_coact {d : ℕ} {m : M} :
    m ∈ homogeneousSubcomodule R ι M d ↔
      (scalarBialgHom R ι).toLinearMap.lTensor M (Comodule.coact (R := R) m) =
        m ⊗ₜ MonoidAlgebra.single (.ofAdd d) 1 := by
  let := Comodule.Corestrict (R := R) (M := M) (scalarBialgHom R ι).toCoalgHom
  have hw : Comodule.weightProj R (Multiplicative ℕ) M (.ofAdd d) m = degreeProj R ι M d m := by
    rw [Comodule.weightProj_apply, Comodule.corestrict_coact_apply, LinearMap.tensorComponent_map,
      LinearMap.id_apply, degreeProj, Comodule.coactComponent_apply]
  rw [mem_homogeneousSubcomodule, coact_mem_range_iff, ← degreeProj_eq_self_iff, ← hw,
    LinearMap.lTensor_def, ← Comodule.corestrict_coact_apply, ← Comodule.mem_weightSpace]
  exact ⟨fun h ↦ h ▸ Comodule.weightProj_mem_weightSpace _ m, Comodule.weightProj_of_mem⟩

/-- For matrices of size zero, every vector of a comodule has degree `0`: the coordinate
bialgebra is then the base ring, and the scalar matrices act trivially. -/
theorem homogeneousSubcomodule_zero_eq_top [IsEmpty ι] : homogeneousSubcomodule R ι M 0 = ⊤ := by
  have hπ : (scalarBialgHom R ι).toLinearMap =
      Algebra.linearMap R (MonoidAlgebra R (Multiplicative ℕ)) ∘ₗ Coalgebra.counit := by
    refine LinearMap.ext fun c ↦ ?_
    obtain ⟨x, rfl⟩ := (coordinateBialgebraAlgEquiv R ι).surjective c
    have h : scalarAlgHomAux R ι = (Algebra.ofId R _).comp (counit R ι) :=
      MvPolynomial.algHom_ext fun ij ↦ isEmptyElim ij.1
    rw [LinearMap.comp_apply, coordinateBialgebra_counit_apply]
    exact (scalarBialgHom_toCoalgHom_apply R ι x).trans congr($h x)
  refine Subcomodule.ext fun m ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  rw [mem_homogeneousSubcomodule_iff_lTensor_scalarBialgHom_coact, hπ,
    LinearMap.lTensor_comp_apply, Comodule.lTensor_counit_coact]
  simp

end Comodule

/-- **A comodule over the matrix-coordinate bialgebra is the internal direct sum of its
homogeneous components.** -/
theorem isInternal_homogeneousSubcomodule (M : Type*) [AddCommGroup M] [Module R M]
    [Comodule R (coordinateBialgebra R ι) M] :
    DirectSum.IsInternal fun d ↦ (homogeneousSubcomodule R ι M d).toSubmodule := by
  let := Comodule.Corestrict (R := R) (M := M) (scalarBialgHom R ι).toCoalgHom
  have h (d : ℕ) : (homogeneousSubcomodule R ι M d).toSubmodule =
      Comodule.weightSpace R (Multiplicative ℕ) M (.ofAdd d) := by
    ext m
    rw [Subcomodule.mem_toSubmodule, mem_homogeneousSubcomodule_iff_lTensor_scalarBialgHom_coact,
      Comodule.mem_weightSpace, Comodule.corestrict_coact_apply, LinearMap.lTensor_def]
  simp_rw [h]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (Comodule.iSupIndep_weightSpace R (Multiplicative ℕ) M).comp
      Multiplicative.ofAdd.injective
  · rw [← Comodule.iSup_weightSpace_eq_top R (Multiplicative ℕ) M]
    exact Multiplicative.ofAdd.surjective.iSup_comp _

end TauCeti.MatrixMonoid
