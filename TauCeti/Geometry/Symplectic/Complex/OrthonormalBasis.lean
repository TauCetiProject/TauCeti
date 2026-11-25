/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.AlmostComplex.UnitaryGroup
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Geometry.Symplectic.Complex.Module.Hom
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Adapted orthonormal bases of an orthogonal complex structure

An orthogonal almost complex structure `J` on a finite-dimensional real inner product space
of dimension `2 * n` admits an orthonormal basis `(u₁, J u₁, …, uₙ, J uₙ)`. The statement
includes dimension zero. Every such basis is a Darboux basis for the associated symplectic form
`ω(v, w) = ⟪J v, w⟫` (`TauCeti.AlmostComplexStructure.symplecticForm`) and therefore induces the
symplectic orientation `ω.orientation`
(`TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`).

The construction takes a complex orthonormal basis for the Hermitian metric induced by `J`, whose
coordinates are a real linear isometry with `ℂⁿ` turning `J` into multiplication by `i`, then uses
`TauCeti.complexEuclideanRealLinearIsometryEquiv` to place each real coordinate immediately before
its imaginary coordinate. Both constructions preserve the original norm
and real scalar action.

Conversely, every even-dimensional real inner product space carries an orthogonal almost complex
structure: transport multiplication by `i` along a real linear isometry with `ℂⁿ`. In dimension
four, any unit vector extends to an oriented unitary orthonormal frame for a compatible symplectic
form
(`exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one`).

In dimension four, an adapted orthonormal basis can also be chosen to depend continuously on the
complex structure. For an orthogonal complex structure `K`, a unit vector `a` and a vector `c`
outside the complex line spanned by `a` and `K a`, the vectors `(a, K a, u, K u)`, with `u` the
normalized component of `c` orthogonal to `a` and `K a`, form an orthonormal basis adapted to `K`.
The orthogonal transformation carrying a fixed basis adapted to `J₀` to it depends continuously on
`K` while `c` stays outside that complex line.

## Main results

* `TauCeti.AlmostComplexStructure.exists_linearIsometryEquiv_euclideanSpace`: an orthogonal almost
  complex structure is multiplication by `i` in a real linear isometry with `ℂⁿ`.
* `TauCeti.SymplecticForm.apply_map_map_eq_im_inner`: in such an isometry, a symplectic form whose
  metric `ω(·, J ·)` is the inner product is the imaginary part of the Hermitian product.
* `TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`: adapted orthonormal bases
  exist in every even dimension `2 * n`.
* `TauCeti.AlmostComplexStructure.exists_orthonormal_forall_inner_apply_eq_zero`: up to half the
  dimension, there are families of `r` vectors orthonormal for the Hermitian metric of `J`.
* `TauCeti.AlmostComplexStructure.exists_forall_norm_apply_eq`: orthogonal almost complex
  structures exist in even dimension.
* `TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`: every adapted
  orthonormal basis in dimension `2 * n` induces the symplectic orientation of `ω(v, w) = ⟪J v, w⟫`.
* `TauCeti.AlmostComplexStructure.orthonormal_of_norm_eq_one_of_inner_eq_zero`: unit vectors
  `ξ`, `η` with `η` orthogonal to `ξ` and `J ξ` give the orthonormal family `(ξ, J ξ, η, J η)`.
* `TauCeti.AlmostComplexStructure.exists_unitary_orthonormalBasis_of_norm_eq_one`,
  `exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one`, and
  `exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation`:
  existence of oriented unitary frames and completion of a unit vector in dimension four.
* `OrthonormalBasis.exists_almostComplexStructure_finFour`: every orthonormal four-frame carries
  an almost complex structure with `J e₀ = e₁` and `J e₂ = e₃`, without an orientation assumption.
* `OrthonormalBasis.complexCoords_two_almostComplexStructure_apply`,
  `TauCeti.AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply`: for such a
  unitary frame, the complex coordinates `OrthonormalBasis.complexCoords` turn `J` into
  multiplication by `i`, and they are the coordinates of the complex basis `(e₀, e₂)` of `(V, J)`,
  hence a `ℂ`-linear equivalence from the complex vector space `(V, J)` to `ℂ²`.
* `TauCeti.AlmostComplexStructure.unitaryGroupFrameEquiv`: for such a unitary frame and the form
  `Q v = -‖v‖²`, the isomorphism `U(2) ≃* U(V, J)` sending a unitary matrix to the rotation acting
  as that matrix in the complex coordinates (`complexCoords_unitaryGroupFrameEquiv_apply`,
  `complexCoords_unitaryGroupFrameEquiv_symm_apply`).
* `TauCeti.AlmostComplexStructure.exists_complexCoords_apply_eq_mulVec_of_norm_map`: a real linear
  map preserving norms and commuting with `J` acts as a unitary matrix in the complex coordinates
  of a unitary frame.
* `ContinuousLinearMap.orthonormal_adaptedFourFrame`, `ContinuousLinearMap.adaptedFourBasis`: for
  an orthogonal complex structure `K`, a unit vector `a` and a vector `c` with nonzero residual
  `ContinuousLinearMap.complexLineResidual`, the vectors `(a, K a, u, K u)`, with `u` the
  normalized residual of `c`, form an orthonormal basis.
* `OrthonormalBasis.apply_unitaryToAdaptedFourBasis_apply`,
  `OrthonormalBasis.continuousOn_unitaryToAdaptedFourBasis`: the orthogonal transformation
  carrying a basis adapted to `J₀` to the basis `(a, K a, u, K u)` intertwines `J₀` with `K`, and
  depends continuously on `K`.
* `TauCeti.AlmostComplexStructure.basisOfOrthonormalBasis`: for an orthonormal basis with
  `e (2k + 1) = J (e (2k))`, the vectors `e (2k)` form a basis of the complex vector space
  `(V, J)`, with coordinates `⟪e (2k), x⟫ + i ⟪e (2k + 1), x⟫`.
* `TauCeti.AlmostComplexStructure.basisOfOrthonormalBasisFinFour`: its case of an orthonormal
  four-frame with `J e₀ = e₁` and `J e₂ = e₃`, the basis `(e₀, e₂)` with coordinates
  `⟪e₀, x⟫ + i ⟪e₁, x⟫` and `⟪e₂, x⟫ + i ⟪e₃, x⟫`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1.
-/

public section

namespace TauCeti.AlmostComplexStructure

open Module
open scoped RealInnerProductSpace

section EvenDimension

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **A unitary frame from `ℂⁿ`.** An orthogonal almost complex structure `J` on a
finite-dimensional real inner product space is multiplication by `i` in some real linear isometry
`Φ : ℂⁿ ≃ V`: `Φ (i • x) = J (Φ x)`. -/
theorem exists_linearIsometryEquiv_euclideanSpace (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    ∃ (n : ℕ) (Φ : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] V),
      ∀ x, Φ (Complex.I • x) = J (Φ x) := by
  let := J.complexInnerProductSpace hJ
  let := J.complexInnerProductSpace_isScalarTower hJ
  have hI (v : V) : Complex.I • v = J v := by
    rw [J.complexInnerProductSpace_smul_def hJ]
    simp
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  let b := stdOrthonormalBasis ℂ V
  let f : V ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (finrank ℂ V)) :=
    { b.repr.toLinearEquiv.restrictScalars ℝ with norm_map' := b.repr.norm_map }
  exact ⟨_, f.symm, fun x ↦ (b.repr.symm.map_smul Complex.I x).trans (hI _)⟩

/-- An orthogonal complex structure admits an orthonormal basis consisting of consecutive
pairs `(u₁, J u₁, …, uₙ, J uₙ)`, including the empty basis in dimension zero. -/
theorem exists_adapted_orthonormalBasis (J : AlmostComplexStructure V) (hJ : ∀ v, ‖J v‖ = ‖v‖)
    (n : ℕ) (hdim : finrank ℝ V = 2 * n) :
    ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ V,
      ∀ k : Fin n, b ⟨2 * k.val + 1, by omega⟩ = J (b ⟨2 * k.val, by omega⟩) := by
  obtain ⟨m, Φ, hΦ⟩ := J.exists_linearIsometryEquiv_euclideanSpace hJ
  obtain rfl : m = n := by
    have h := Φ.toLinearEquiv.finrank_eq
    rw [hdim, ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
      finrank_euclideanSpace_fin] at h
    omega
  let e := Φ.symm.trans (complexEuclideanRealLinearIsometryEquiv m)
  refine ⟨OrthonormalBasis.ofRepr e, fun k ↦ ?_⟩
  have hsingle :
      (complexEuclideanRealLinearIsometryEquiv m).symm
          (EuclideanSpace.single ⟨2 * k.val + 1, by omega⟩ (1 : ℝ)) =
        Complex.I • (complexEuclideanRealLinearIsometryEquiv m).symm
          (EuclideanSpace.single ⟨2 * k.val, by omega⟩ (1 : ℝ)) := by
    ext j
    simp only [complexEuclideanRealLinearIsometryEquiv_symm_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [PiLp.single_apply, Fin.ext_iff, finProdFinEquiv, Equiv.coe_fn_mk,
      Fin.cast_mk]
    split_ifs <;> first | omega | norm_num
  simp only [OrthonormalBasis.coe_ofRepr, e, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_symm]
  rw [hsingle]
  exact hΦ _

/-- Up to half the dimension, there are families of `r` vectors that are orthonormal for the
Hermitian metric of an orthogonal almost complex structure `J`: `u` is orthonormal and
`⟪J uᵢ, uⱼ⟫ = 0` for all `i` and `j`. -/
theorem exists_orthonormal_forall_inner_apply_eq_zero {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) :
    ∃ u : Fin r → V, Orthonormal ℝ u ∧ ∀ i j, ⟪J (u i), u j⟫ = 0 := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  obtain ⟨b, hb⟩ := exists_adapted_orthonormalBasis J (norm_apply hJ) n (by omega)
  refine ⟨fun i ↦ b ⟨2 * i, by omega⟩, ?_, fun i j ↦ ?_⟩
  · exact b.orthonormal.comp _ fun i j h ↦ Fin.ext (by simpa using congrArg Fin.val h)
  · rw [← hb ⟨i, by omega⟩]
    exact b.orthonormal.2 (by simp [Fin.ext_iff]; omega)

/-- An even-dimensional real inner product space admits an orthogonal almost complex structure,
including the zero structure in dimension zero. -/
theorem exists_forall_norm_apply_eq (hV : Even (finrank ℝ V)) :
    ∃ J : AlmostComplexStructure V, ∀ v, ‖J v‖ = ‖v‖ := by
  obtain ⟨n, hn⟩ := hV
  -- A real linear isometry `e : V ≃ ℂⁿ`; then `J = e⁻¹ ∘ (i • ·) ∘ e`.
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    ((stdOrthonormalBasis ℝ V).reindex (finCongr (by omega))).repr.trans
      (complexEuclideanRealLinearIsometryEquiv n).symm
  let L := DistribSMul.toLinearMap ℝ (EuclideanSpace ℂ (Fin n)) Complex.I
  refine ⟨⟨e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap, ?_⟩, fun v ↦ ?_⟩
  · ext v
    simp [L, smul_smul]
  · simp [L, norm_smul]

/-- **Every adapted orthonormal basis induces the symplectic orientation.** For a symplectic form
`ω` and an almost complex structure `J` satisfying `ω(v, w) = ⟪J v, w⟫` on a `2 * n`-dimensional
real inner product space, any orthonormal basis `b` with `b (2k + 1) = J (b (2k))` is a Darboux
basis of `ω` and therefore induces `ω.orientation`. -/
theorem toBasis_orientation_eq_symplecticForm_orientation {n : ℕ} {ω : SymplecticForm V}
    {J : AlmostComplexStructure V} (hω : ∀ v w, ω v w = ⟪J v, w⟫) (hdim : finrank ℝ V = 2 * n)
    {b : OrthonormalBasis (Fin (2 * n)) ℝ V}
    (hb : ∀ k : Fin n, b ⟨2 * k.val + 1, by omega⟩ = J (b ⟨2 * k.val, by omega⟩)) :
    b.toBasis.orientation = ω.orientation hdim := by
  let E : Fin n × Fin 2 ≃ Fin (2 * n) :=
    (finProdFinEquiv (m := n) (n := 2)).trans (finCongr (Nat.mul_comm n 2))
  let c : Basis (Fin n × Fin 2) ℝ V := b.toBasis.reindex E.symm
  have hc (p : Fin n × Fin 2) : c p = b (E p) := by simp [c]
  have hE0 (i : Fin n) : E (i, 0) = ⟨2 * i.val, by omega⟩ := by
    ext; simp [E, finProdFinEquiv]
  have hE1 (i : Fin n) : E (i, 1) = ⟨2 * i.val + 1, by omega⟩ := by
    ext; simp [E, finProdFinEquiv]; omega
  have hb_inner := orthonormal_iff_ite.1 b.orthonormal
  have hcd : ω.IsDarbouxBasis c := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · rw [hc, hc, hE0, hE0, hω, ← hb i, hb_inner, ite_eq_right_iff]
      intro h
      simp only [Fin.ext_iff] at h
      omega
    · rw [hc, hc, hE1, hE1, hb i, hω, J.apply_apply, inner_neg_left, hb_inner, neg_eq_zero,
        ite_eq_right_iff]
      intro h
      simp only [Fin.ext_iff] at h
      omega
    · rw [hc, hc, hE0, hE1, hω, ← hb i, hb_inner]
      have hij : (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n)) = ⟨2 * j.val + 1, by omega⟩ ↔ i = j := by
        simp only [Fin.ext_iff]
        omega
      simp only [hij]
  have hre : c.reindex E = b.toBasis := Basis.eq_of_apply_eq fun x ↦ by simp [c]
  rw [← hre]
  exact hcd.orientation_reindex hdim (Nat.mul_comm n 2)

end EvenDimension

section OrthonormalFour

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For an orthogonal almost complex structure `J`, unit vectors `ξ` and `η` with `η` orthogonal
to `ξ` and to `J ξ` give the orthonormal family `(ξ, J ξ, η, J η)`. -/
theorem orthonormal_of_norm_eq_one_of_inner_eq_zero {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {ξ η : V} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hξη : ⟪ξ, η⟫ = 0) (hJξη : ⟪J ξ, η⟫ = 0) :
    Orthonormal ℝ ![ξ, J ξ, η, J η] := by
  have hskew (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
    J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v w
  have hξJη : ⟪ξ, J η⟫ = 0 := by rw [← neg_eq_zero, ← hskew, hJξη]
  have hJξJη : ⟪J ξ, J η⟫ = 0 := by rw [hJ, hξη]
  refine ⟨fun i ↦ by fin_cases i <;> simp [hξ, hη, J.norm_apply hJ], fun {i j} hij ↦ ?_⟩
  have hξJ := J.inner_self_apply hJ ξ
  have hηJη := J.inner_self_apply hJ η
  fin_cases i <;> fin_cases j <;> dsimp only <;> first
    | exact absurd rfl hij
    | exact hξJ | exact hξη | exact hξJη | exact hJξη | exact hJξJη | exact hηJη
    | (rw [real_inner_comm]; first
        | exact hξJ | exact hξη | exact hξJη | exact hJξη | exact hJξJη | exact hηJη)

end OrthonormalFour

end TauCeti.AlmostComplexStructure

/-! ### Adapted orthonormal bases depending continuously on the complex structure -/

namespace ContinuousLinearMap

open Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The component of `c` orthogonal to `a` and `K a`, `c - ⟪a, c⟫ • a - ⟪K a, c⟫ • K a`. For an
orthogonal complex structure `K` and a unit vector `a`, the vectors `a` and `K a` are orthonormal
and span the complex line of `a`. -/
def complexLineResidual (K : V →L[ℝ] V) (a c : V) : V :=
  c - ⟪a, c⟫ • a - ⟪K a, c⟫ • K a

theorem complexLineResidual_def (K : V →L[ℝ] V) (a c : V) :
    K.complexLineResidual a c = c - ⟪a, c⟫ • a - ⟪K a, c⟫ • K a :=
  (rfl)

/-- The residual is orthogonal to `a`, for a unit vector `a` orthogonal to `K a`. -/
theorem inner_complexLineResidual {K : V →L[ℝ] V} {a : V} (ha : ‖a‖ = 1) (haK : ⟪a, K a⟫ = 0)
    (c : V) : ⟪a, K.complexLineResidual a c⟫ = 0 := by
  simp only [complexLineResidual, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ha,
    haK]
  ring

/-- The residual is orthogonal to `K a`, for a unit vector `K a` orthogonal to `a`. -/
theorem inner_apply_complexLineResidual {K : V →L[ℝ] V} {a : V} (hKa : ‖K a‖ = 1)
    (haK : ⟪a, K a⟫ = 0) (c : V) : ⟪K a, K.complexLineResidual a c⟫ = 0 := by
  simp only [complexLineResidual, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hKa, real_inner_comm a (K a), haK]
  ring

/-- The residual depends continuously on `K`. -/
theorem continuous_complexLineResidual (a c : V) :
    Continuous fun K : V →L[ℝ] V ↦ K.complexLineResidual a c := by
  unfold complexLineResidual
  fun_prop

/-- In dimension greater than two, some vector of a basis lies outside the span of `a` and `K a`:
its residual is nonzero. -/
theorem exists_complexLineResidual_ne_zero [FiniteDimensional ℝ V] (hV : 2 < finrank ℝ V)
    (K : V →L[ℝ] V) (a : V) {ι : Type*} (b : Basis ι ℝ V) :
    ∃ i, K.complexLineResidual a (b i) ≠ 0 := by
  by_contra! h
  have hle : (⊤ : Submodule ℝ V) ≤ Submodule.span ℝ (Set.range ![a, K a]) := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b i = ⟪a, b i⟫ • a + ⟪K a, b i⟫ • K a := by
      have h' := h i
      rwa [complexLineResidual, sub_sub, sub_eq_zero] at h'
    rw [hi]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h2 := (Submodule.finrank_mono hle).trans (finrank_range_le_card _)
  rw [finrank_top, Fintype.card_fin] at h2
  omega

/-- The vectors `(a, K a, u, K u)`, where `u` is the normalized residual of `c`, the normalized
component of `c` orthogonal to `a` and `K a`. -/
noncomputable def adaptedFourFrame (K : V →L[ℝ] V) (a c : V) : Fin 4 → V :=
  ![a, K a, ‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c,
    K (‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c)]

theorem adaptedFourFrame_def (K : V →L[ℝ] V) (a c : V) :
    K.adaptedFourFrame a c = ![a, K a, ‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c,
      K (‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c)] :=
  (rfl)

@[simp]
theorem adaptedFourFrame_zero (K : V →L[ℝ] V) (a c : V) : K.adaptedFourFrame a c 0 = a :=
  (rfl)

@[simp]
theorem adaptedFourFrame_one (K : V →L[ℝ] V) (a c : V) : K.adaptedFourFrame a c 1 = K a :=
  (rfl)

@[simp]
theorem adaptedFourFrame_two (K : V →L[ℝ] V) (a c : V) :
    K.adaptedFourFrame a c 2 = ‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c :=
  (rfl)

@[simp]
theorem adaptedFourFrame_three (K : V →L[ℝ] V) (a c : V) :
    K.adaptedFourFrame a c 3 = K (‖K.complexLineResidual a c‖⁻¹ • K.complexLineResidual a c) :=
  (rfl)

/-- For an orthogonal complex structure `K`, a unit vector `a` and a vector `c` outside the complex
line of `a`, the vectors `(a, K a, u, K u)` are orthonormal. -/
theorem orthonormal_adaptedFourFrame {K : V →L[ℝ] V} (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : K.complexLineResidual a c ≠ 0) :
    Orthonormal ℝ (K.adaptedFourFrame a c) := by
  let J : TauCeti.AlmostComplexStructure V :=
    ⟨K.toLinearMap, LinearMap.ext fun v ↦ by simpa using hK₂ v⟩
  -- `J` is built from `K.toLinearMap`, so `J v` unfolds to `K v`: `hK` says `J` is orthogonal and
  -- the family `(a, J a, u, J u)` below is `K.adaptedFourFrame a c`.
  have hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫ := hK
  have haK : ⟪a, K a⟫ = 0 := J.inner_self_apply hJ a
  have hKa : ‖K a‖ = 1 := (J.norm_apply hJ a).trans ha
  exact TauCeti.AlmostComplexStructure.orthonormal_of_norm_eq_one_of_inner_eq_zero hJ ha
    (norm_smul_inv_norm hr) (by rw [inner_smul_right, inner_complexLineResidual ha haK, mul_zero])
    (by
      rw [inner_smul_right]
      exact mul_eq_zero_of_right _ (inner_apply_complexLineResidual hKa haK c))

variable [Fact (finrank ℝ V = 4)]

/-- The orthonormal basis `(a, K a, u, K u)` of a four-dimensional space adapted to an orthogonal
complex structure `K`, for a unit vector `a` and a vector `c` outside the complex line of `a`, where
`u` is the normalized residual of `c`. -/
noncomputable def adaptedFourBasis (K : V →L[ℝ] V) (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : K.complexLineResidual a c ≠ 0) :
    OrthonormalBasis (Fin 4) ℝ V :=
  (basisOfOrthonormalOfCardEqFinrank (orthonormal_adaptedFourFrame hK hK₂ ha hr)
    ((Fintype.card_fin 4).trans (Fact.out : finrank ℝ V = 4).symm)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact orthonormal_adaptedFourFrame hK hK₂ ha hr)

/-- The vectors of `adaptedFourBasis` are `(a, K a, u, K u)`. -/
@[simp]
theorem coe_adaptedFourBasis {K : V →L[ℝ] V} (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : K.complexLineResidual a c ≠ 0) :
    (K.adaptedFourBasis hK hK₂ ha hr : Fin 4 → V) = K.adaptedFourFrame a c := by
  rw [adaptedFourBasis, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

end ContinuousLinearMap

namespace TauCeti.AlmostComplexStructure

open Module
open scoped RealInnerProductSpace

section DimensionFour

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]

local instance finiteDimensional_of_finrank_eq_four : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-- Four-dimensional specialization of `toBasis_orientation_eq_symplecticForm_orientation`: a
unitary orthonormal basis `e` (`J (e 0) = e 1`, `J (e 2) = e 3`) induces `ω.orientation Fact.out`
when `ω(v, w) = ⟪J v, w⟫`. -/
theorem toBasis_orientation_eq_symplecticForm_orientation_four {ω : SymplecticForm V}
    {J : AlmostComplexStructure V} (hω : ∀ v w, ω v w = ⟪J v, w⟫)
    {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) :
    e.toBasis.orientation = ω.orientation Fact.out :=
  toBasis_orientation_eq_symplecticForm_orientation (n := 2) hω Fact.out fun k ↦ by
    fin_cases k
    · exact h₀.symm
    · exact h₂.symm

/-- Given an orthogonal almost complex structure `J` on a four-dimensional real inner product space
`V` and a unit vector `ξ`, there exists a unitary orthonormal basis `e` extending `e 0 = ξ`,
`J (e 0) = e 1`, `J (e 2) = e 3`. -/
theorem exists_unitary_orthonormalBasis_of_norm_eq_one {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {ξ : V} (hξ : ‖ξ‖ = 1) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V, e 0 = ξ ∧ J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  classical
  obtain ⟨η, hη_norm, hηK⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    ({ξ, J ξ} : Finset V) (by
      rw [Fact.out (p := finrank ℝ V = 4)]
      exact Finset.card_le_two.trans_lt (by norm_num))
  -- `J` as a continuous linear map: `K v` unfolds to `J v`, so `hJ` and `J.apply_apply` apply to
  -- `K`. Since `η` is a unit vector orthogonal to `ξ` and `J ξ`, it is its own residual.
  let K : V →L[ℝ] V := LinearMap.toContinuousLinearMap J.toLinearMap
  have hr : K.complexLineResidual ξ η = η := by
    simp [ContinuousLinearMap.complexLineResidual_def, K, hηK ξ (by simp), hηK (J ξ) (by simp)]
  have hr₀ : K.complexLineResidual ξ η ≠ 0 := by
    rw [hr, ← norm_ne_zero_iff, hη_norm]
    exact one_ne_zero
  have he := K.coe_adaptedFourBasis hJ J.apply_apply hξ hr₀
  refine ⟨K.adaptedFourBasis hJ J.apply_apply hξ hr₀, ?_, ?_, ?_⟩
  · simp [he]
  · simp [he, K]
  · simp [he, hr, hη_norm, K]

/-- **Every pair `(ω, J)` whose associated bilinear form `ω(·, J ·)` is the inner product induces
an oriented unitary orthonormal frame extending any given unit vector `ξ`.** -/
theorem exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one
    {ω : SymplecticForm V} {J : AlmostComplexStructure V} (hg : ∀ v w, ⟪v, w⟫ = ω v (J w))
    {ξ : V} (hξ : ‖ξ‖ = 1) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      e.toBasis.orientation = ω.orientation Fact.out ∧
        e 0 = ξ ∧ J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  have hinv := ω.invariant_of_apply_apply_eq_inner fun v w ↦ (hg v w).symm
  have hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫ := fun v w ↦ by
    rw [hg, hg]
    exact hinv.associatedBilinForm_invariant v w
  have hω : ∀ v w, ω v w = ⟪J v, w⟫ := fun v w ↦ by
    rw [hg]
    exact hinv.symplecticForm_apply_eq_associatedBilinForm_apply_left_apply v w
  obtain ⟨e, he₀, h₀, h₂⟩ := exists_unitary_orthonormalBasis_of_norm_eq_one hJ hξ
  exact ⟨e, toBasis_orientation_eq_symplecticForm_orientation_four hω h₀ h₂, he₀, h₀, h₂⟩

/-- **Every pair `(ω, J)` whose associated bilinear form `ω(·, J ·)` is the inner product admits a
positively oriented unitary orthonormal frame for `ω.orientation Fact.out`.** -/
theorem exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation
    {ω : SymplecticForm V} {J : AlmostComplexStructure V} (hg : ∀ v w, ⟪v, w⟫ = ω v (J w)) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      e.toBasis.orientation = ω.orientation Fact.out ∧ J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  have hv : finrank ℝ V = 4 := Fact.out
  let ξ := stdOrthonormalBasis ℝ V ⟨0, by omega⟩
  have hξ : ‖ξ‖ = 1 := (stdOrthonormalBasis ℝ V).orthonormal.1 _
  obtain ⟨e, he, _, h₀, h₂⟩ :=
    exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one hg hξ
  exact ⟨e, he, h₀, h₂⟩

end DimensionFour

section ComplexBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} {n : ℕ} {e : OrthonormalBasis (Fin (2 * n)) ℝ V}

/-- The even vectors `e (2k)` of an orthonormal basis adapted to `J`, `e (2k + 1) = J (e (2k))`,
span the complex vector space `(V, J)`. -/
private theorem top_le_span_apply_two_mul
    (hb : ∀ k : Fin n, e ⟨2 * k.val + 1, by omega⟩ = J (e ⟨2 * k.val, by omega⟩)) :
    letI := J.complexModule
    ⊤ ≤ Submodule.span ℂ (Set.range fun k : Fin n ↦ e ⟨2 * k.val, by omega⟩) := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  set S := Submodule.span ℂ (Set.range fun k : Fin n ↦ e ⟨2 * k.val, by omega⟩)
  have hS (i : Fin (2 * n)) : e i ∈ S := by
    obtain ⟨k, rfl | rfl⟩ : ∃ k : Fin n,
        i = ⟨2 * k.val, by omega⟩ ∨ i = ⟨2 * k.val + 1, by omega⟩ :=
      ⟨⟨i.val / 2, by omega⟩, by simp only [Fin.ext_iff]; omega⟩
    · exact Submodule.subset_span ⟨k, rfl⟩
    · rw [hb k, ← J.complexModule_I_smul]
      exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  intro x _
  rw [← e.sum_repr' x]
  exact S.sum_mem fun i _ ↦ S.smul_of_tower_mem _ (hS i)

/-- The even vectors `e (2k)` of an orthonormal basis adapted to `J` are linearly independent over
`ℂ` in `(V, J)`: they span it, and there are `n = dim_ℂ (V, J)` of them. -/
private theorem linearIndependent_apply_two_mul
    (hb : ∀ k : Fin n, e ⟨2 * k.val + 1, by omega⟩ = J (e ⟨2 * k.val, by omega⟩)) :
    letI := J.complexModule
    LinearIndependent ℂ fun k : Fin n ↦ e ⟨2 * k.val, by omega⟩ := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  have : FiniteDimensional ℝ V := Module.Finite.of_basis e.toBasis
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_apply_two_mul hb) ?_
  have h := Module.finrank_mul_finrank ℝ ℂ V
  rw [Complex.finrank_real_complex, Module.finrank_eq_card_basis e.toBasis] at h
  simp only [Fintype.card_fin] at h ⊢
  omega

/-- **The complex basis of an adapted orthonormal basis.** If `e` is an orthonormal basis with
`e (2k + 1) = J (e (2k))` for every `k`, as produced by `exists_adapted_orthonormalBasis`, then the
vectors `e (2k)` form a basis of the complex vector space `(V, J)`. The `k`-th coordinate of `x` in
it is `⟪e (2k), x⟫ + i ⟪e (2k + 1), x⟫` (`basisOfOrthonormalBasis_repr_apply`). -/
noncomputable def basisOfOrthonormalBasis
    (hb : ∀ k : Fin n, e ⟨2 * k.val + 1, by omega⟩ = J (e ⟨2 * k.val, by omega⟩)) :
    letI := J.complexModule
    Basis (Fin n) ℂ V :=
  letI := J.complexModule
  Basis.mk (linearIndependent_apply_two_mul hb) (top_le_span_apply_two_mul hb)

/-- The `k`-th vector of the complex basis of an adapted orthonormal basis `e` is `e (2k)`. -/
@[simp]
theorem basisOfOrthonormalBasis_apply
    (hb : ∀ k : Fin n, e ⟨2 * k.val + 1, by omega⟩ = J (e ⟨2 * k.val, by omega⟩)) (k : Fin n) :
    letI := J.complexModule
    basisOfOrthonormalBasis hb k = e ⟨2 * k.val, by omega⟩ := by
  simp [basisOfOrthonormalBasis]

/-- The `k`-th coordinate of `x` in the complex basis of an adapted orthonormal basis `e` is
`⟪e (2k), x⟫ + i ⟪e (2k + 1), x⟫`. -/
@[simp]
theorem basisOfOrthonormalBasis_repr_apply
    (hb : ∀ k : Fin n, e ⟨2 * k.val + 1, by omega⟩ = J (e ⟨2 * k.val, by omega⟩)) (x : V)
    (k : Fin n) :
    letI := J.complexModule
    (basisOfOrthonormalBasis hb).repr x k =
      (⟪e ⟨2 * k.val, by omega⟩, x⟫ : ℂ) + Complex.I * ⟪e ⟨2 * k.val + 1, by omega⟩, x⟫ := by
  let := J.complexModule
  have hx := (basisOfOrthonormalBasis hb).sum_repr x
  have ho (i j : Fin (2 * n)) : ⟪e i, e j⟫ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 e.orthonormal i j
  -- Pairing `x = ∑ⱼ cⱼ • e (2j)` with `e (2k)` and `e (2k + 1)` reads off `c k`.
  have hpair (j : Fin n) :
      ((⟨2 * k.val, by omega⟩ : Fin (2 * n)) = ⟨2 * j.val, by omega⟩ ↔ k = j) ∧
        ((⟨2 * k.val, by omega⟩ : Fin (2 * n)) = ⟨2 * j.val + 1, by omega⟩ ↔ False) ∧
        ((⟨2 * k.val + 1, by omega⟩ : Fin (2 * n)) = ⟨2 * j.val, by omega⟩ ↔ False) ∧
        ((⟨2 * k.val + 1, by omega⟩ : Fin (2 * n)) = ⟨2 * j.val + 1, by omega⟩ ↔ k = j) := by
    simp only [Fin.ext_iff, iff_false]
    omega
  obtain ⟨hre, him⟩ : ⟪e ⟨2 * k.val, by omega⟩, x⟫ = ((basisOfOrthonormalBasis hb).repr x k).re ∧
      ⟪e ⟨2 * k.val + 1, by omega⟩, x⟫ = ((basisOfOrthonormalBasis hb).repr x k).im := by
    constructor <;> (conv_lhs => rw [← hx]) <;>
      simp [inner_sum, J.complexModule_smul_def, ← hb, inner_add_right, real_inner_smul_right, ho,
        hpair]
  rw [hre, him, mul_comm]
  exact (Complex.re_add_im _).symm

section FinFour

variable {e : OrthonormalBasis (Fin 4) ℝ V}

/-- **The complex basis of a unitary four-frame.** If `e` is an orthonormal basis with `J e₀ = e₁`
and `J e₂ = e₃`, then `e₀, e₂` is a basis of the complex vector space `(V, J)`: the case `n = 2` of
`basisOfOrthonormalBasis`, for frames indexed by `Fin 4`. The coordinates of `x` in it are
`z₀(x) = ⟪e₀, x⟫ + i ⟪e₁, x⟫` and `z₂(x) = ⟪e₂, x⟫ + i ⟪e₃, x⟫`
(`basisOfOrthonormalBasisFinFour_repr_apply_zero`, `basisOfOrthonormalBasisFinFour_repr_apply_one`).
-/
noncomputable def basisOfOrthonormalBasisFinFour (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) :
    letI := J.complexModule
    Basis (Fin 2) ℂ V :=
  basisOfOrthonormalBasis (n := 2) (e := e) fun k ↦ by
    fin_cases k
    exacts [h₀.symm, h₂.symm]

/-- The first vector of the basis `(e₀, e₂)` of `(V, J)` is `e₀`. -/
@[simp]
theorem basisOfOrthonormalBasisFinFour_zero (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) :
    letI := J.complexModule
    basisOfOrthonormalBasisFinFour h₀ h₂ 0 = e 0 :=
  basisOfOrthonormalBasis_apply _ 0

/-- The second vector of the basis `(e₀, e₂)` of `(V, J)` is `e₂`. -/
@[simp]
theorem basisOfOrthonormalBasisFinFour_one (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) :
    letI := J.complexModule
    basisOfOrthonormalBasisFinFour h₀ h₂ 1 = e 2 :=
  basisOfOrthonormalBasis_apply _ 1

/-- The first coordinate of `x` in the basis `(e₀, e₂)` of `(V, J)` is
`z₀(x) = ⟪e₀, x⟫ + i ⟪e₁, x⟫`. -/
@[simp]
theorem basisOfOrthonormalBasisFinFour_repr_apply_zero (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    (x : V) :
    letI := J.complexModule
    (basisOfOrthonormalBasisFinFour h₀ h₂).repr x 0 = (⟪e 0, x⟫ : ℂ) + Complex.I * ⟪e 1, x⟫ :=
  basisOfOrthonormalBasis_repr_apply _ x 0

/-- The second coordinate of `x` in the basis `(e₀, e₂)` of `(V, J)` is
`z₂(x) = ⟪e₂, x⟫ + i ⟪e₃, x⟫`. -/
@[simp]
theorem basisOfOrthonormalBasisFinFour_repr_apply_one (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    (x : V) :
    letI := J.complexModule
    (basisOfOrthonormalBasisFinFour h₀ h₂).repr x 1 = (⟪e 2, x⟫ : ℂ) + Complex.I * ⟪e 3, x⟫ :=
  basisOfOrthonormalBasis_repr_apply _ x 1

/-- **Complex coordinates of a unitary frame.** For a unitary frame `e`, `J e₀ = e₁` and
`J e₂ = e₃`, the coordinates of the complex basis `(e₀, e₂)` of `(V, J)`
(`basisOfOrthonormalBasisFinFour`) are the complex coordinates `e.complexCoords 2`. So these are a
`ℂ`-linear equivalence from `(V, J)` to `ℂ²`. -/
theorem basisOfOrthonormalBasisFinFour_equivFun_apply (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    (v : V) :
    letI := J.complexModule
    (basisOfOrthonormalBasisFinFour h₀ h₂).equivFun v = e.complexCoords 2 v := by
  let := J.complexModule
  rw [OrthonormalBasis.complexCoords_two_apply]
  ext i
  fin_cases i <;> simp [mul_comm]

end FinFour

end ComplexBasis

end TauCeti.AlmostComplexStructure

namespace TauCeti.SymplecticForm

open scoped RealInnerProductSpace

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- **A symplectic form in a unitary frame is the imaginary part of the Hermitian product.** If
the inner product of `V` is the metric `ω(·, J ·)` and a real linear isometry `Φ : F → V` from a
complex inner product space turns multiplication by `i` into `J`, then
`ω(Φ x, Φ y) = Im ⟪x, y⟫`. -/
theorem apply_map_map_eq_im_inner (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (Φ : F →ₗᵢ[ℝ] V)
    (hΦ : ∀ x, Φ (Complex.I • x) = J (Φ x)) (x y : F) :
    ω (Φ x) (Φ y) = (inner ℂ x y).im := by
  let := InnerProductSpace.complexToReal (G := F)
  -- `Φ y = J (Φ (-i • y))`, and the metric of `J` is the inner product.
  have hy : Φ y = J (Φ ((-Complex.I) • y)) := by
    rw [← hΦ, smul_smul]
    simp
  rw [hy, hg, Φ.inner_map_map, real_inner_eq_re_inner ℂ, inner_smul_right]
  simp

end TauCeti.SymplecticForm

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- An orthonormal four-frame carries an almost complex structure rotating its two coordinate
planes: `J e₀ = e₁` and `J e₂ = e₃`. -/
theorem exists_almostComplexStructure_finFour (e : OrthonormalBasis (Fin 4) ℝ V) :
    ∃ J : TauCeti.AlmostComplexStructure V, J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  let L := e.toBasis.constr ℝ ![e 1, -e 0, e 3, -e 2]
  have hL (i : Fin 4) : L (e i) = ![e 1, -e 0, e 3, -e 2] i := e.toBasis.constr_basis ℝ _ i
  have hsquare : L.comp L = -LinearMap.id := by
    apply e.toBasis.ext
    intro i
    fin_cases i <;> simp [LinearMap.comp_apply, hL, map_neg]
  exact ⟨⟨L, hsquare⟩, hL 0, hL 2⟩

section ComplexCoords

variable {J : TauCeti.AlmostComplexStructure V} {e : OrthonormalBasis (Fin 4) ℝ V}

/-- In the complex coordinates `OrthonormalBasis.complexCoords` of a unitary frame `e`,
`J e₀ = e₁` and `J e₂ = e₃`, the complex structure `J` is multiplication by `i`. -/
theorem complexCoords_two_almostComplexStructure_apply (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    (v : V) : e.complexCoords 2 (J v) = Complex.I • e.complexCoords 2 v := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  obtain ⟨z, rfl⟩ := (e.complexCoords 2).symm.surjective v
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply, complexCoords_two_symm_apply,
    complexCoords_two_symm_apply]
  simp only [map_add, map_smul, h₀, h₁, h₂, h₃, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  module

end ComplexCoords

section UnitaryToAdaptedFourBasis

open Module
open scoped RealInnerProductSpace

variable [Fact (finrank ℝ V = 4)] [CompleteSpace V]

open scoped Classical in
/-- The orthogonal transformation of `V` carrying the orthonormal basis `β` to the basis
`(a, K a, u, K u)` adapted to `K` (`ContinuousLinearMap.adaptedFourBasis`), where `a = β 0` and `u`
is the normalized residual of `c`, when `K` is a complex structure and `c` lies outside the complex
line of `a`; and `1` otherwise. -/
noncomputable def unitaryToAdaptedFourBasis (β : OrthonormalBasis (Fin 4) ℝ V) (c : V)
    (K : unitary (V →L[ℝ] V)) : unitary (V →L[ℝ] V) :=
  if h : (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
      (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0 then
    Unitary.linearIsometryEquiv.symm (β.equiv ((K : V →L[ℝ] V).adaptedFourBasis
      (Unitary.inner_map_map K) h.1 (β.orthonormal.1 0) h.2) (Equiv.refl _))
  else 1

variable {β : OrthonormalBasis (Fin 4) ℝ V} {c : V} {K : unitary (V →L[ℝ] V)}

/-- When `K` is a complex structure and `c` lies outside the complex line of `β 0`,
`unitaryToAdaptedFourBasis` carries `β i` to the `i`-th adapted vector. -/
theorem unitaryToAdaptedFourBasis_apply_basis (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0) (i : Fin 4) :
    (β.unitaryToAdaptedFourBasis c K : V →L[ℝ] V) (β i) =
      (K : V →L[ℝ] V).adaptedFourFrame (β 0) c i := by
  rw [unitaryToAdaptedFourBasis, dite_eq_left ⟨hK₂, hr⟩]
  simp

private theorem unitaryToAdaptedFourBasis_apply_eq_sum
    (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0) (v : V) :
    (β.unitaryToAdaptedFourBasis c K : V →L[ℝ] V) v =
      ∑ i, ⟪β i, v⟫ • (K : V →L[ℝ] V).adaptedFourFrame (β 0) c i := by
  conv_lhs => rw [← β.sum_repr' v]
  simp [map_sum, map_smul, unitaryToAdaptedFourBasis_apply_basis hK₂ hr]

/-- `unitaryToAdaptedFourBasis` intertwines `J₀` with `K`, when `β` is adapted to `J₀`:
`β 1 = J₀ (β 0)` and `β 3 = J₀ (β 2)`. -/
theorem apply_unitaryToAdaptedFourBasis_apply {J₀ : V →L[ℝ] V} (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (hβ₁ : β 1 = J₀ (β 0)) (hβ₃ : β 3 = J₀ (β 2))
    (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0) (v : V) :
    (K : V →L[ℝ] V) ((β.unitaryToAdaptedFourBasis c K : V →L[ℝ] V) v) =
      (β.unitaryToAdaptedFourBasis c K : V →L[ℝ] V) (J₀ v) := by
  have hΦ := unitaryToAdaptedFourBasis_apply_basis hK₂ hr
  set Φ : V →L[ℝ] V := ((β.unitaryToAdaptedFourBasis c K : unitary (V →L[ℝ] V)) : V →L[ℝ] V)
  have key : (((K : V →L[ℝ] V) ∘L Φ : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      ((Φ ∘L J₀ : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
    refine β.toBasis.ext fun i ↦ ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, Function.comp_apply]
    fin_cases i <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · simp [hΦ, ← hβ₁]
    · rw [hΦ 1, hβ₁, hJ₀, map_neg, hΦ 0]
      simp [hK₂]
    · simp [hΦ, ← hβ₃]
    · rw [hΦ 3, hβ₃, hJ₀, map_neg, hΦ 2]
      simp [hK₂]
  exact LinearMap.congr_fun key v

variable (β c) in
/-- `unitaryToAdaptedFourBasis` depends continuously on the complex structure `K`, while `c` stays
outside the complex line of `β 0`. -/
theorem continuousOn_unitaryToAdaptedFourBasis :
    ContinuousOn (β.unitaryToAdaptedFourBasis c)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0} := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_clm_apply.2 fun v ↦ ?_)
  have hK : Continuous fun K : unitary (V →L[ℝ] V) ↦ (K : V →L[ℝ] V) := continuous_subtypeVal
  have hres : Continuous fun K : unitary (V →L[ℝ] V) ↦
      (K : V →L[ℝ] V).complexLineResidual (β 0) c :=
    (ContinuousLinearMap.continuous_complexLineResidual _ _).comp hK
  have hunit : ContinuousOn (fun K : unitary (V →L[ℝ] V) ↦
      ‖(K : V →L[ℝ] V).complexLineResidual (β 0) c‖⁻¹ •
        (K : V →L[ℝ] V).complexLineResidual (β 0) c)
      {K | (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0} :=
    (hres.norm.continuousOn.inv₀ fun _ hK ↦ norm_ne_zero_iff.2 hK).smul hres.continuousOn
  have hvec (i : Fin 4) : ContinuousOn
      (fun K : unitary (V →L[ℝ] V) ↦ (K : V →L[ℝ] V).adaptedFourFrame (β 0) c i)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0} := by
    fin_cases i
    · exact continuousOn_const
    · exact (hK.clm_apply continuous_const).continuousOn
    · exact hunit.mono fun _ hK ↦ hK.2
    · exact hK.continuousOn.clm_apply (hunit.mono fun _ hK ↦ hK.2)
  have hsum : ContinuousOn (fun K : unitary (V →L[ℝ] V) ↦
      ∑ i, ⟪β i, v⟫ • (K : V →L[ℝ] V).adaptedFourFrame (β 0) c i)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        (K : V →L[ℝ] V).complexLineResidual (β 0) c ≠ 0} :=
    continuousOn_finsetSum Finset.univ fun i _ ↦ continuousOn_const.smul (hvec i)
  exact hsum.congr fun K hK ↦ unitaryToAdaptedFourBasis_apply_eq_sum hK.1 hK.2 v

end UnitaryToAdaptedFourBasis

end OrthonormalBasis

namespace TauCeti.AlmostComplexStructure

section UnitaryGroupFrame

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} {e : OrthonormalBasis (Fin 4) ℝ V} {Q : QuadraticForm ℝ V}

/-- The real linear automorphism of `V` acting as the matrix `g` in the complex coordinates
`e.complexCoords 2` of the frame `e`. -/
private noncomputable def frameRotation (e : OrthonormalBasis (Fin 4) ℝ V)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) : V ≃ₗ[ℝ] V :=
  (e.complexCoords 2).trans
    (((Matrix.UnitaryGroup.toLinearEquiv g).restrictScalars ℝ).trans (e.complexCoords 2).symm)

private theorem complexCoords_frameRotation_apply (g : Matrix.unitaryGroup (Fin 2) ℂ) (v : V) :
    e.complexCoords 2 (frameRotation e g v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e.complexCoords 2 v :=
  (e.complexCoords 2).apply_symm_apply _

/-- The automorphism `frameRotation e g` is a rotation: it preserves norms because `g` is unitary
and the complex coordinates are isometric, and its real determinant is `|det g|² = 1`. -/
private theorem frameRotation_mem_specialOrthogonalGroup (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    frameRotation e g ∈ QuadraticMap.specialOrthogonalGroup Q := by
  refine QuadraticMap.mem_specialOrthogonalGroup_iff.2
    ⟨QuadraticMap.mem_orthogonalGroup_iff.2 fun v ↦ ?_, Units.ext ?_⟩
  · rw [hQ, hQ, ← e.norm_toLp_complexCoords (n := 2), complexCoords_frameRotation_apply,
      ← e.norm_toLp_complexCoords (n := 2) v]
    have h := Matrix.UnitaryGroup.toLinearIsometryEquiv_apply g
      (WithLp.toLp 2 (e.complexCoords 2 v))
    rw [WithLp.ofLp_toLp] at h
    rw [← h, LinearIsometryEquiv.norm_map]
  · rw [LinearEquiv.coe_det, Units.val_one]
    have h := LinearMap.det_conj
      (((Matrix.UnitaryGroup.toLinearEquiv g).restrictScalars ℝ : (Fin 2 → ℂ) ≃ₗ[ℝ] _) :
        (Fin 2 → ℂ) →ₗ[ℝ] _) (e.complexCoords 2).symm
    refine h.trans ?_
    have hg := Matrix.det_of_mem_unitary g.property
    rw [Unitary.mem_iff_star_mul_self] at hg
    have hn : (Complex.normSq (g : Matrix (Fin 2) (Fin 2) ℂ).det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hg
    refine (LinearMap.det_restrictScalars_eq_normSq
      (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ))).trans ?_
    rw [LinearMap.det_toLin']
    exact_mod_cast hn

/-- The rotation `frameRotation e g` commutes with `J` for a unitary frame `e`, because the complex
coordinates turn `J` into multiplication by `i`. -/
private theorem frameRotation_apply_almostComplexStructure (h₀ : J (e 0) = e 1)
    (h₂ : J (e 2) = e 3) (g : Matrix.unitaryGroup (Fin 2) ℂ) (v : V) :
    frameRotation e g (J v) = J (frameRotation e g v) := by
  refine (e.complexCoords 2).injective ?_
  rw [complexCoords_frameRotation_apply, e.complexCoords_two_almostComplexStructure_apply h₀ h₂,
    e.complexCoords_two_almostComplexStructure_apply h₀ h₂, complexCoords_frameRotation_apply,
    Matrix.mulVec_smul]

/-- For a unitary frame `e`, the homomorphism `U(2) → U(V, J)` sending `g` to the rotation acting
as `g` in the complex coordinates of `e`. -/
private noncomputable def frameRotationHom (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1)
    (h₂ : J (e 2) = e 3) : Matrix.unitaryGroup (Fin 2) ℂ →* J.unitaryGroup Q where
  toFun g := ⟨⟨frameRotation e g, frameRotation_mem_specialOrthogonalGroup hQ g⟩,
    mem_unitaryGroup_iff.2 (frameRotation_apply_almostComplexStructure h₀ h₂ g)⟩
  map_one' := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun v ↦
    (e.complexCoords 2).injective <| by
      rw [complexCoords_frameRotation_apply]
      simp
  map_mul' g g' := Subtype.ext <| Subtype.ext <| LinearEquiv.ext fun v ↦
    (e.complexCoords 2).injective <| by
      simp only [Subgroup.coe_mul, mul_apply_eq_comp]
      rw [complexCoords_frameRotation_apply, complexCoords_frameRotation_apply,
        complexCoords_frameRotation_apply, Matrix.UnitaryGroup.mul_val, Matrix.mulVec_mulVec]

/-- **A complex linear isometry is a unitary matrix in a unitary frame.** A real linear map `A` of
`V` preserving norms and commuting with `J` acts as a unitary matrix in the complex coordinates of
a unitary frame `e`, `J e₀ = e₁` and `J e₂ = e₃`: these coordinates are `ℂ`-linear for `J` and
carry `V` isometrically onto `ℂ²`. -/
theorem exists_complexCoords_apply_eq_mulVec_of_norm_map (h₀ : J (e 0) = e 1)
    (h₂ : J (e 2) = e 3) (A : V →ₗ[ℝ] V) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hJA : ∀ v, A (J v) = J (A v)) :
    ∃ g : Matrix.unitaryGroup (Fin 2) ℂ, ∀ v, e.complexCoords 2 (A v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e.complexCoords 2 v := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  -- The complex coordinates of `e` are `ℂ`-linear for the complex structure `J` on `V`.
  let C := (basisOfOrthonormalBasisFinFour h₀ h₂).equivFun
  have hCv (v : V) : C v = e.complexCoords 2 v :=
    basisOfOrthonormalBasisFinFour_equivFun_apply h₀ h₂ v
  have hC (z : Fin 2 → ℂ) : ‖C.symm z‖ = ‖WithLp.toLp 2 z‖ := by
    rw [← OrthonormalBasis.norm_toLp_complexCoords (n := 2) e, ← hCv, LinearEquiv.apply_symm_apply]
  -- The matrix `g` is `A` read in the complex coordinates, a `ℂ`-linear isometry of `ℂ²`.
  let L : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).symm.toLinearMap ∘ₗ
        C.toLinearMap ∘ₗ
        ((isComplexLinearMap_iff_apply J J A).2 hJA).toComplexLinearMap ∘ₗ
        C.symm.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).toLinearMap
      norm_map' x := by
        obtain ⟨z, rfl⟩ := (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).symm.surjective x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          IsComplexLinearMap.toComplexLinearMap_apply, WithLp.coe_symm_linearEquiv,
          WithLp.coe_linearEquiv, hCv]
        rw [OrthonormalBasis.norm_toLp_complexCoords (n := 2), hA, hC] }
  refine ⟨Matrix.UnitaryGroup.toLinearIsometryEquiv.symm (L.toLinearIsometryEquiv rfl),
    fun v ↦ ?_⟩
  have h := congrArg WithLp.ofLp (Matrix.UnitaryGroup.toLinearIsometryEquiv_apply
    (Matrix.UnitaryGroup.toLinearIsometryEquiv.symm (L.toLinearIsometryEquiv rfl))
    (WithLp.toLp 2 (e.complexCoords 2 v)))
  rw [MulEquiv.apply_symm_apply, LinearIsometry.toLinearIsometryEquiv_apply] at h
  dsimp only at h
  rw [← h]
  simp only [L, LinearIsometry.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    IsComplexLinearMap.toComplexLinearMap_apply, WithLp.coe_linearEquiv,
    WithLp.coe_symm_linearEquiv, WithLp.ofLp_toLp, hCv]
  rw [← hCv v, LinearEquiv.symm_apply_apply]

/-- Every rotation in `U(V, J)` acts as a unitary matrix in the complex coordinates of the unitary
frame `e`. -/
private theorem exists_complexCoords_apply_eq_mulVec (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (A : J.unitaryGroup Q) :
    ∃ g : Matrix.unitaryGroup (Fin 2) ℂ, ∀ v, e.complexCoords 2
        (((A : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e.complexCoords 2 v := by
  have hA (v : V) : ‖((A : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v‖ = ‖v‖ := by
    have h := QuadraticMap.map_app_of_mem_orthogonalGroup
      (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q
        (A : QuadraticMap.specialOrthogonalGroup Q).property) v
    rw [hQ, hQ, neg_inj] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  exact exists_complexCoords_apply_eq_mulVec_of_norm_map h₀ h₂
    ((A : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V).toLinearMap hA
    (mem_unitaryGroup_iff.1 A.property)

/-- **The unitary group in a unitary frame.** For a unitary frame `e`, `J e₀ = e₁` and
`J e₂ = e₃`, of a space with `Q v = -‖v‖²`, the isomorphism `U(2) ≃* U(V, J)` sending a unitary
matrix `g` to the rotation acting as `g` in the complex coordinates `e.complexCoords 2`
(`complexCoords_unitaryGroupFrameEquiv_apply`, `complexCoords_unitaryGroupFrameEquiv_symm_apply`).
-/
noncomputable def unitaryGroupFrameEquiv (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1)
    (h₂ : J (e 2) = e 3) : Matrix.unitaryGroup (Fin 2) ℂ ≃* J.unitaryGroup Q :=
  MulEquiv.ofBijective (frameRotationHom hQ h₀ h₂)
    ⟨fun g g' h ↦ Subtype.ext <| Matrix.toLin'.injective <| LinearMap.ext fun z ↦ by
        obtain ⟨v, rfl⟩ := (e.complexCoords 2).surjective z
        have h' := congrArg (fun A : J.unitaryGroup Q ↦ e.complexCoords 2
          (((A : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v)) h
        simpa only [Matrix.toLin'_apply] using
          (complexCoords_frameRotation_apply g v).symm.trans
            (h'.trans (complexCoords_frameRotation_apply g' v)),
      fun A ↦ by
        obtain ⟨g, hg⟩ := exists_complexCoords_apply_eq_mulVec hQ h₀ h₂ A
        refine ⟨g, Subtype.ext (Subtype.ext (LinearEquiv.ext fun v ↦
          (e.complexCoords 2).injective ?_))⟩
        rw [hg]
        exact complexCoords_frameRotation_apply g v⟩

/-- The rotation `unitaryGroupFrameEquiv g` acts as `g` in the complex coordinates of the frame. -/
theorem complexCoords_unitaryGroupFrameEquiv_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (g : Matrix.unitaryGroup (Fin 2) ℂ) (v : V) :
    e.complexCoords 2
        (((unitaryGroupFrameEquiv hQ h₀ h₂ g : QuadraticMap.specialOrthogonalGroup Q) :
          V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e.complexCoords 2 v :=
  complexCoords_frameRotation_apply g v

/-- A rotation `A` in `U(V, J)` acts as the unitary matrix `(unitaryGroupFrameEquiv).symm A` in the
complex coordinates of the frame. -/
theorem complexCoords_unitaryGroupFrameEquiv_symm_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (A : J.unitaryGroup Q) (v : V) :
    e.complexCoords 2 (((A : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v) =
      ((unitaryGroupFrameEquiv hQ h₀ h₂).symm A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        e.complexCoords 2 v := by
  conv_lhs => rw [← (unitaryGroupFrameEquiv hQ h₀ h₂).apply_symm_apply A]
  exact complexCoords_unitaryGroupFrameEquiv_apply hQ h₀ h₂ _ v

end UnitaryGroupFrame

end TauCeti.AlmostComplexStructure
