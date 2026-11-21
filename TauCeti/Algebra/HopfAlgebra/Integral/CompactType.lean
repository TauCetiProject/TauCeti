/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Orthogonality
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.PositiveIntegral
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.HopfAlgebra.Integral.Sweedler

/-!
# Compact-type Hopf star algebras

Combining Sweedler's invariant integral (`TauCeti.sweedlerIntegral`) with unitarization, complete
reducibility of unitary comodules, cross-orthogonality, and weighted Schur orthogonality yields the
Dijkhuizen–Koornwinder characterization (`TauCeti.compactType_iff`) of compact-type Hopf star
algebras: a complex Hopf star algebra admits an algebraic Haar functional (`TauCeti.AlgebraicHaar`)
if and only if it is spanned as a complex vector space by the matrix entries of its
finite-dimensional unitary matrix corepresentations (`TauCeti.unitaryCoefficientSet`).

## Main declarations

* `TauCeti.AlgebraicHaar.sSup_simpleCoefficientSubmodules_eq_top` and
  `TauCeti.AlgebraicHaar.induction_simpleCoefficientSubmodules`: if `A` admits an `AlgebraicHaar`
  functional, then its simple coefficient spaces span `A`.
* `TauCeti.AlgebraicHaar.map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules`: Haar
  orthogonality of distinct simple coefficient spaces.
* `TauCeti.AlgebraicHaar.span_unitaryCoefficientSet_eq_top`: if `A` admits an `AlgebraicHaar`
  functional, then `unitaryCoefficientSet A` spans `A` over `ℂ`.
* `TauCeti.nonempty_algebraicHaar_of_span_unitaryCoefficientSet_eq_top`: if
  `unitaryCoefficientSet A` spans `A` over `ℂ`, then `A` admits an `AlgebraicHaar` functional.
* `TauCeti.compactType_iff`: Dijkhuizen–Koornwinder equivalence between existence of an
  `AlgebraicHaar` functional and spanning by unitary matrix coefficients.

## References

* M. S. Dijkhuizen and T. H. Koornwinder, *CQG algebras: a direct algebraic approach to compact
  quantum groups*, Lett. Math. Phys. 32 (1994), 315–330.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Theorem 3.2.12.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.6.6.
-/

public noncomputable section

open Module Matrix TauCeti.Comodule
open scoped TensorProduct ComplexOrder DirectSum

namespace TauCeti

universe u

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A]

-- If a simple unitary comodule `M` has conjugate coefficient space equal to that of another
-- simple unitary comodule `N`, then `0 ≤ h (star x * x)` on the coefficient space of `M`.
private theorem map_star_mul_self_nonneg_of_conj_unitary {M N ι κ : Type*}
    [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
    [AddCommGroup N] [Module ℂ N] [Comodule ℂ A N] [IsSimpleOrder (Subcomodule ℂ A N)]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {h : A →ₗ[ℂ] ℂ}
    (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (c : Basis κ ℂ N)
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hconj : (letI := b.conjugateMatrixComodule (A := A);
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := ι → ℂ)) =
        matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {x : A} (hx : x ∈ matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)) :
    0 ≤ h (star x * x) := by
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule (A := A)
  have : IsSimpleOrder (Subcomodule ℂ A (ι → ℂ)) := b.isSimpleOrder_conjugateMatrixComodule (A := A)
  obtain ⟨φ, hφ⟩ := (matrixCoefficientSubmodule_eq_iff (R := ℂ) (C := A)).mp hconj
  let T : Matrix κ ι ℂ := LinearMap.toMatrix (Pi.basisFun ℂ ι) c φ.toLinearMap
  have hTv (v : ι → ℂ) : T *ᵥ v = ⇑(c.repr (φ v)) := by
    simpa [T, funext (Pi.basisFun_repr ℂ ι v)] using
      φ.toLinearMap.toMatrix_mulVec_repr (Pi.basisFun ℂ ι) c v
  have hT_inj : Function.Injective T.mulVec := fun v w hvw ↦ (φ.bijective_of_ne_zero hφ).1 <|
    c.repr.injective <| DFunLike.coe_injective ((hTv v).symm.trans (hvw.trans (hTv w)))
  have hG : (Tᴴ * T).PosDef := Matrix.PosDef.conjTranspose_mul_self T hT_inj
  have hfv : coefficientMatrix (C := A) c * T.map (algebraMap ℂ A) =
      T.map (algebraMap ℂ A) * (coefficientMatrix (C := A) b).map star := by
    simpa [T, b.coefficientMatrix_conjugateMatrixComodule] using
      φ.coefficientMatrix_mul_toMatrix (Pi.basisFun ℂ ι) c
  have hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * (Tᴴ * T).map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = (Tᴴ * T).map (algebraMap ℂ A) := by
    set u := (coefficientMatrix (C := A) b).map star
    set f := algebraMap ℂ A
    have hGf : (Tᴴ * T).map f = (T.map f)ᴴ * T.map f := by
      rw [Matrix.map_mul, Matrix.conjTranspose_map _ fun z ↦ algebraMap_star_comm z]
    calc uᴴ * (Tᴴ * T).map f * u = (T.map f * u)ᴴ * (T.map f * u) := by
          simp only [hGf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (T.map f)ᴴ * ((coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c) *
            T.map f := by simp only [← hfv, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Tᴴ * T).map f := by rw [(Matrix.mem_unitary_iff_conjTranspose.mp hv).1,
            Matrix.mul_one, hGf]
  exact hr.map_star_mul_self_nonneg_of_conjTranspose_map_star_mul_mul_eq h1 b hu hG hGinv hx

namespace AlgebraicHaar

variable (h : AlgebraicHaar A)

include h in
/-- The simple coefficient spaces of a Hopf star algebra with an algebraic Haar functional span
it. -/
theorem sSup_simpleCoefficientSubmodules_eq_top :
    sSup (simpleCoefficientSubmodules ℂ A) = ⊤ :=
  (h.isRightInvariantIntegral.isLinearlyReductive h.toLinearMap_ne_zero
    h.map_star_mul_self_nonneg).sSup_simpleCoefficientSubmodules_eq_top

include h in
/-- Induction over the simple coefficient spaces of a Hopf star algebra with an algebraic Haar
functional: a property preserved by addition and holding on every simple coefficient space holds
on `A`. -/
@[elab_as_elim]
theorem induction_simpleCoefficientSubmodules {motive : A → Prop} (x : A)
    (mem : ∀ P ∈ simpleCoefficientSubmodules ℂ A, ∀ x ∈ P, motive x) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  have hx : x ∈ ⨆ P : simpleCoefficientSubmodules ℂ A, P.val := by
    rw [← sSup_eq_iSup', h.sSup_simpleCoefficientSubmodules_eq_top]
    exact Submodule.mem_top
  exact Submodule.iSup_induction (motive := motive) _ hx (fun P x hx ↦ mem P.val P.property x hx)
      zero add

/-- **Haar orthogonality of simple coefficient spaces.** If `P` and `Q` are distinct coefficient
spaces of simple comodules, then `h (star x * y) = 0` for `x ∈ P` and `y ∈ Q`. -/
theorem map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules {P Q : Submodule ℂ A}
    (hP : P ∈ simpleCoefficientSubmodules ℂ A) (hQ : Q ∈ simpleCoefficientSubmodules ℂ A)
    (hPQ : P ≠ Q) {x y : A} (hx : x ∈ P) (hy : y ∈ Q) : h (star x * y) = 0 := by
  obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
  obtain ⟨N, hN, rfl⟩ := mem_simpleCoefficientSubmodules.mp hQ
  have := hM
  have := hN
  have : Module.Finite ℂ M := finite_of_isSimpleOrder (C := A)
  have : Module.Finite ℂ N := finite_of_isSimpleOrder (C := A)
  obtain ⟨b, hb⟩ := exists_basis_coefficientMatrix_mem_unitary h.isRightInvariantIntegral
    h.toLinearMap_ne_zero h.map_star_mul_self_nonneg (Module.finBasis ℂ M)
  exact h.isRightInvariantIntegral.map_star_mul_eq_zero_of_mem_matrixCoefficientSubmodule b
    (Module.finBasis ℂ N) (Matrix.mem_unitary_iff_conjTranspose.mp hb).2
    (fun g ↦ by_contra fun hg ↦ hPQ (matrixCoefficientSubmodule_eq_of_ne_zero hg).symm) hx hy

include h in
/-- If a complex Hopf star algebra admits an `AlgebraicHaar` functional, then the matrix entries of
its finite-dimensional unitary comodules span `A`. -/
theorem span_unitaryCoefficientSet_eq_top :
    Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ := by
  rw [eq_top_iff, ← h.sSup_simpleCoefficientSubmodules_eq_top]
  refine sSup_le fun P hP ↦ ?_
  obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
  let _ := hM
  have : Module.Finite ℂ M := finite_of_isSimpleOrder (C := A)
  obtain ⟨b, hb⟩ := exists_basis_coefficientMatrix_mem_unitary h.isRightInvariantIntegral
    h.toLinearMap_ne_zero h.map_star_mul_self_nonneg (Module.finBasis ℂ M)
  exact b.matrixCoefficientSubmodule_le_of_coefficientMatrix_mem fun i j ↦
    Submodule.subset_span (b.coefficientMatrix_mem_unitaryCoefficientSet hb i j)

end AlgebraicHaar

private def simpleUnitaryCoefficientSubmodules (A : Type u) [Ring A] [StarRing A] [Bialgebra ℂ A] :
    Set (Submodule ℂ A) :=
  {P ∈ simpleCoefficientSubmodules ℂ A | ∃ (m : ℕ) (ρ : Comodule ℂ A (Fin m → ℂ)), letI := ρ
    IsSimpleOrder (Subcomodule ℂ A (Fin m → ℂ)) ∧
      coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin m)) ∈ unitary (Matrix (Fin m) (Fin m) A) ∧
      P = matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin m → ℂ)}

omit [StarCoalgebra ℂ A] in
private theorem isAtom_matrixCoefficientSubmodule_mem_simpleUnitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [Comodule ℂ A H] (hH : IsUnitary ℂ A H) {W : Subcomodule ℂ A H} (hW : IsAtom W) :
    matrixCoefficientSubmodule (R := ℂ) (C := A) (M := W) ∈
      simpleUnitaryCoefficientSubmodules A := by
  let _ := convolutionModule (R := ℂ) (C := A) (M := H)
  let _ := convolutionModule (R := ℂ) (C := A) (M := W)
  have := isSimpleModule_convolution_iff.mp (W.isSimpleModule_convolution_iff_isAtom.mpr hW)
  let bW := stdOrthonormalBasis ℂ W
  let _ : Comodule ℂ A (Fin (Module.finrank ℂ W) → ℂ) := Transport bW.toBasis.equivFun
  have : IsSimpleOrder (Subcomodule ℂ A (Fin (Module.finrank ℂ W) → ℂ)) :=
    (Subcomodule.transportOrderIso bW.toBasis.equivFun).symm.isSimpleOrder
  refine ⟨matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules, _, inferInstance,
    inferInstance, by simpa [bW.toBasis.coefficientMatrix_basisFun_transport_equivFun] using
      (W.isUnitary hH).coefficientMatrix_mem_unitary bW,
    (matrixCoefficientSubmodule_transport (C := A) bW.toBasis.equivFun).symm⟩

omit [StarCoalgebra ℂ A] in
private theorem sSup_simpleUnitaryCoefficientSubmodules_eq_top
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤) :
    sSup (simpleUnitaryCoefficientSubmodules A) = ⊤ := by
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  intro a ha
  obtain ⟨n, ρ, hU, i, j, rfl⟩ := mem_unitaryCoefficientSet_iff.mp ha
  let _ := ρ
  -- Transport the unitary matrix comodule on `Fin n → ℂ` to `EuclideanSpace ℂ (Fin n)`.
  let E := EuclideanSpace ℂ (Fin n)
  let bE := EuclideanSpace.basisFun (Fin n) ℂ
  let fE : (Fin n → ℂ) ≃ₗ[ℂ] E := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let _ : Comodule ℂ A E := Transport fE
  have hbE_mat : coefficientMatrix (C := A) bE.toBasis =
      coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) := by
    rw [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_eq_pi_basisFun]
    exact fE.coefficientMatrix_map_transport (Pi.basisFun ℂ (Fin n))
  have hUnit : IsUnitary ℂ A E := bE.isUnitary_comodule_iff.mpr (hbE_mat.symm ▸ hU)
  -- By complete reducibility of unitary comodules, `bE j` lies in the span of atomic subcomodules.
  have hatoms : sSup {W : Subcomodule ℂ A E | IsAtom W} = ⊤ :=
    isCompletelyReducible_iff_sSup_atoms_eq_top.mp hUnit.isCompletelyReducible
  have hv : bE.toBasis j ∈ ⨆ W : {W : Subcomodule ℂ A E | IsAtom W}, W.val.toSubmodule := by
    simp [← Subcomodule.sSup_toSubmodule, hatoms]
  have himg := Submodule.mem_map_of_mem
    (f := matrixCoefficientLinear (R := ℂ) (C := A) (bE.toBasis.coord i)) hv
  rw [Submodule.map_iSup] at himg
  rw [← hbE_mat, coefficientMatrix_apply, ← matrixCoefficientLinear_apply]
  -- Map through `matrixCoefficientLinear (bE.coord i)`: each atomic piece lands in `sSup`.
  suffices (⨆ W : {W : Subcomodule ℂ A E | IsAtom W}, W.val.toSubmodule.map
      (matrixCoefficientLinear (R := ℂ) (C := A) (bE.toBasis.coord i))) ≤
      sSup (simpleUnitaryCoefficientSubmodules A) from this himg
  refine iSup_le fun ⟨W, hW⟩ ↦
    le_trans ?_ (le_sSup (isAtom_matrixCoefficientSubmodule_mem_simpleUnitary hUnit hW))
  rintro _ ⟨w, hw, rfl⟩
  rw [matrixCoefficientLinear_apply,
    ← Subtype.coe_mk w (Subcomodule.mem_toSubmodule.mp hw),
    ← W.subtype_apply, matrixCoefficient_map]
  exact matrixCoefficient_mem_submodule _ _

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem mem_simpleUnitaryCoefficientSubmodules_of_mem
    (hSU_span : sSup (simpleUnitaryCoefficientSubmodules A) = ⊤) {Q : Submodule ℂ A}
    (hQ : Q ∈ simpleCoefficientSubmodules ℂ A) : Q ∈ simpleUnitaryCoefficientSubmodules A := by
  by_contra hQnot
  have htop : sSup (simpleCoefficientSubmodules ℂ A \ {Q}) = ⊤ := top_unique <| hSU_span ▸
    sSup_le_sSup fun P hP ↦ ⟨hP.1, fun hPQ ↦ hQnot (Set.mem_singleton_iff.mp hPQ ▸ hP)⟩
  have hdisj := htop ▸ sSupIndep_simpleCoefficientSubmodules hQ
  exact bot_notMem_simpleCoefficientSubmodules ((by simpa using hdisj.eq_bot : Q = ⊥) ▸ hQ)

private theorem map_star_mul_self_nonneg_of_mem_simpleCoefficientSubmodules
    (hSU_span : sSup (simpleUnitaryCoefficientSubmodules A) = ⊤) {h : A →ₗ[ℂ] ℂ}
    (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1) {P : Submodule ℂ A}
    (hP : P ∈ simpleCoefficientSubmodules ℂ A) {x : A} (hx : x ∈ P) : 0 ≤ h (star x * x) := by
  obtain ⟨_, m, ρ, hS, hU, rfl⟩ := mem_simpleUnitaryCoefficientSubmodules_of_mem hSU_span hP
  let _ := ρ
  have := hS
  obtain ⟨_, m', ρ', hS', hU', hEq'⟩ := mem_simpleUnitaryCoefficientSubmodules_of_mem hSU_span <| by
    have := (Pi.basisFun ℂ (Fin m)).isSimpleOrder_conjugateMatrixComodule (A := A)
    let _ := (Pi.basisFun ℂ (Fin m)).conjugateMatrixComodule (A := A)
    exact matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules (M := Fin m → ℂ)
  let _ := ρ'
  have := hS'
  exact map_star_mul_self_nonneg_of_conj_unitary hr h1 (Pi.basisFun ℂ (Fin m)) hU
    (Pi.basisFun ℂ (Fin m')) hU' hEq' hx

private theorem map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules_ne
    (hSU_span : sSup (simpleUnitaryCoefficientSubmodules A) = ⊤) {h : A →ₗ[ℂ] ℂ}
    (hr : h.IsRightInvariantIntegral) {P Q : Submodule ℂ A}
    (hP : P ∈ simpleCoefficientSubmodules ℂ A) (hQ : Q ∈ simpleCoefficientSubmodules ℂ A)
    (hPQ : P ≠ Q) {x y : A} (hx : x ∈ P) (hy : y ∈ Q) : h (star x * y) = 0 := by
  obtain ⟨_, m, ρ, hSP, hUnitP, rfl⟩ := mem_simpleUnitaryCoefficientSubmodules_of_mem hSU_span hP
  obtain ⟨_, n, σ, hSQ, _, rfl⟩ := mem_simpleUnitaryCoefficientSubmodules_of_mem hSU_span hQ
  let _ := ρ
  let _ := σ
  have := hSP
  have := hSQ
  refine hr.map_star_mul_eq_zero_of_mem_matrixCoefficientSubmodule (Pi.basisFun ℂ (Fin m))
    (Pi.basisFun ℂ (Fin n)) (Matrix.mem_unitary_iff_conjTranspose.mp hUnitP).2
    (fun g ↦ by_contra fun hg ↦ hPQ (matrixCoefficientSubmodule_eq_of_ne_zero hg).symm) hx hy

/-- If the matrix entries of finite-dimensional unitary comodules span a complex Hopf star algebra
`A`, then `A` admits an `AlgebraicHaar` functional. -/
theorem nonempty_algebraicHaar_of_span_unitaryCoefficientSet_eq_top
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤) : Nonempty (AlgebraicHaar A) := by
  classical
  -- Step 1: Decompose unitary comodules into simple unitary ones, so simple coefficient spaces
  -- span `A` and Sweedler's normalized invariant integral `h` is defined.
  have hSU_span := sSup_simpleUnitaryCoefficientSubmodules_eq_top hspan
  have hSimpleSpan : sSup (simpleCoefficientSubmodules ℂ A) = ⊤ :=
    top_unique (hSU_span ▸ sSup_le_sSup fun _ hP ↦ hP.1)
  let h := sweedlerIntegral hSimpleSpan
  have hr : h.IsRightInvariantIntegral := isRightInvariantIntegral_sweedlerIntegral hSimpleSpan
  have h1 : h 1 = 1 := sweedlerIntegral_one hSimpleSpan
  -- Step 2: Expand `a` along the internal direct sum of simple coefficient spaces; cross terms
  -- vanish by orthogonality and diagonal terms are nonnegative by weighted Schur orthogonality.
  refine ⟨AlgebraicHaar.ofIsRightInvariantIntegral h h1 hr fun a ↦ ?_⟩
  obtain ⟨d, rfl⟩ :=
    (Comodule.isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hSimpleSpan).2 a
  have ha : DirectSum.coeAddMonoidHom (fun P : simpleCoefficientSubmodules ℂ A ↦ P.val) d =
      ∑ P ∈ d.support, (d P : A) := by
    conv_lhs => rw [← DirectSum.sum_support_of d]
    simp [map_sum]
  rw [ha, star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  refine Finset.sum_nonneg fun P _ ↦ ?_
  rw [Finset.sum_eq_single P
    (fun Q _ hQP ↦ map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules_ne hSU_span hr
      P.property Q.property (Subtype.coe_ne_coe.mpr hQP.symm) (d P).property (d Q).property)
    (fun hPnot ↦ by simp [DFinsupp.notMem_support_iff.mp hPnot])]
  exact map_star_mul_self_nonneg_of_mem_simpleCoefficientSubmodules hSU_span hr h1 P.property
      (d P).property

/-- **Dijkhuizen–Koornwinder compact-type equivalence.** A complex Hopf star algebra admits an
algebraic Haar functional if and only if the matrix entries of its finite-dimensional unitary
comodules span the algebra over `ℂ`. -/
theorem compactType_iff :
    Nonempty (AlgebraicHaar A) ↔ Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ :=
  ⟨fun ⟨h⟩ ↦ h.span_unitaryCoefficientSet_eq_top,
    nonempty_algebraicHaar_of_span_unitaryCoefficientSet_eq_top⟩

end TauCeti
