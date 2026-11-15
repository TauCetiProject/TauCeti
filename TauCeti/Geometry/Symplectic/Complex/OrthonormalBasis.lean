/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Adapted orthonormal bases of an orthogonal complex structure

An orthogonal almost complex structure `J` on a finite-dimensional real inner product space
of dimension `2 * n` admits an orthonormal basis `(u₁, J u₁, …, uₙ, J uₙ)`. The statement
includes dimension zero. Every such basis is a Darboux basis for the associated symplectic form
`ω(v, w) = ⟪J v, w⟫` (`TauCeti.AlmostComplexStructure.symplecticForm`) and therefore induces the
symplectic orientation `ω.orientation`
(`TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`).

The construction takes a complex orthonormal basis for the Hermitian metric induced by `J`,
then uses `TauCeti.complexEuclideanRealLinearIsometryEquiv` to place each real coordinate
immediately before its imaginary coordinate. Both constructions preserve the original norm
and real scalar action.

Conversely, every even-dimensional real inner product space carries an orthogonal almost complex
structure: transport multiplication by `i` along a real linear isometry with `ℂⁿ`. In dimension
four, any unit vector extends to an oriented unitary orthonormal frame for a compatible symplectic
form
(`exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one`).

## Main results

* `TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`: adapted orthonormal bases
  exist in every even dimension `2 * n`.
* `TauCeti.AlmostComplexStructure.exists_forall_norm_apply_eq`: orthogonal almost complex
  structures exist in even dimension.
* `TauCeti.AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation`: every adapted
  orthonormal basis in dimension `2 * n` induces the symplectic orientation of `ω(v, w) = ⟪J v, w⟫`.
* `TauCeti.AlmostComplexStructure.exists_unitary_orthonormalBasis_of_norm_eq_one`,
  `exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation_of_norm_eq_one`, and
  `exists_orthonormalBasis_toBasis_orientation_eq_symplecticForm_orientation`:
  existence of oriented unitary frames and completion of a unit vector in dimension four.
* `OrthonormalBasis.exists_almostComplexStructure_finFour`: every orthonormal four-frame carries
  an almost complex structure with `J e₀ = e₁` and `J e₂ = e₃`, without an orientation assumption.
* `TauCeti.AlmostComplexStructure.det_eq_of_orthonormalBasis`: for such a frame, `e₀, e₂` is a
  basis of the complex vector space `(V, J)`, which computes the determinant of a complex-linear
  map of `(V, J)` from its frame coordinates.

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

/-- An orthogonal complex structure admits an orthonormal basis consisting of consecutive
pairs `(u₁, J u₁, …, uₙ, J uₙ)`, including the empty basis in dimension zero. -/
theorem exists_adapted_orthonormalBasis (J : AlmostComplexStructure V) (hJ : ∀ v, ‖J v‖ = ‖v‖)
    (n : ℕ) (hdim : finrank ℝ V = 2 * n) :
    ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ V,
      ∀ k : Fin n, b ⟨2 * k.val + 1, by omega⟩ = J (b ⟨2 * k.val, by omega⟩) := by
  classical
  let := J.complexInnerProductSpace hJ
  let := J.complexInnerProductSpace_isScalarTower hJ
  have hI (v : V) : Complex.I • v = J v := by
    rw [J.complexInnerProductSpace_smul_def hJ]
    simp
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  have hn : finrank ℂ V = n := by
    have h := Module.finrank_mul_finrank ℝ ℂ V
    rw [Complex.finrank_real_complex, hdim] at h
    omega
  let b := (stdOrthonormalBasis ℂ V).reindex (finCongr hn)
  let f : V ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { b.repr.toLinearEquiv.restrictScalars ℝ with norm_map' := b.repr.norm_map }
  let e := f.trans (complexEuclideanRealLinearIsometryEquiv n)
  refine ⟨OrthonormalBasis.ofRepr e, fun k ↦ ?_⟩
  have hsingle :
      (complexEuclideanRealLinearIsometryEquiv n).symm
          (EuclideanSpace.single ⟨2 * k.val + 1, by omega⟩ (1 : ℝ)) =
        Complex.I • (complexEuclideanRealLinearIsometryEquiv n).symm
          (EuclideanSpace.single ⟨2 * k.val, by omega⟩ (1 : ℝ)) := by
    ext j
    simp only [complexEuclideanRealLinearIsometryEquiv_symm_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [PiLp.single_apply, Fin.ext_iff, finProdFinEquiv, Equiv.coe_fn_mk,
      Fin.cast_mk]
    split_ifs <;> first | omega | norm_num
  simp only [OrthonormalBasis.coe_ofRepr, e, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply]
  rw [hsingle]
  exact (b.repr.symm.map_smul Complex.I _).trans (hI _)

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
  have hskew (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
    J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v w
  have hself (v : V) : ⟪v, J v⟫ = 0 := by rw [real_inner_comm, J.inner_apply_self hJ]
  obtain ⟨η, hη_norm, hηK⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    ({ξ, J ξ} : Finset V) (by
      rw [Fact.out (p := finrank ℝ V = 4)]
      exact Finset.card_le_two.trans_lt (by norm_num))
  have hξη : ⟪ξ, η⟫ = 0 := hηK ξ (by simp)
  have hJξη : ⟪J ξ, η⟫ = 0 := hηK (J ξ) (by simp)
  have hξJη : ⟪ξ, J η⟫ = 0 := by rw [← neg_eq_zero, ← hskew, hJξη]
  have hJξJη : ⟪J ξ, J η⟫ = 0 := by rw [hJ, hξη]
  have hon₄ : Orthonormal ℝ ![ξ, J ξ, η, J η] := by
    refine ⟨fun i ↦ by fin_cases i <;> simp [hξ, hη_norm, J.norm_apply hJ], fun {i j} hij ↦ ?_⟩
    have hξJ := hself ξ
    have hηJη := hself η
    fin_cases i <;> fin_cases j <;> dsimp only <;> first
      | exact absurd rfl hij
      | exact hξJ | exact hξη | exact hξJη | exact hJξη | exact hJξJη | exact hηJη
      | (rw [real_inner_comm]; first
          | exact hξJ | exact hξη | exact hξJη | exact hJξη | exact hJξJη | exact hηJη)
  have hcard : Fintype.card (Fin 4) = finrank ℝ V :=
    (Fintype.card_fin 4).trans (Fact.out : finrank ℝ V = 4).symm
  let e : OrthonormalBasis (Fin 4) ℝ V :=
    (basisOfOrthonormalOfCardEqFinrank hon₄ hcard).toOrthonormalBasis
      (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])
  have he_coe : (e : Fin 4 → V) = ![ξ, J ξ, η, J η] := by
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  exact ⟨e, congrFun he_coe 0, by simp [he_coe], by simp [he_coe]⟩

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

section Det

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} {e : OrthonormalBasis (Fin 4) ℝ V}

/-- The two complex frame coordinates `⟪e₀, x⟫ + i ⟪e₁, x⟫` and `⟪e₂, x⟫ + i ⟪e₃, x⟫` of
`s e₀ + t e₂` in `(V, J)` are `s` and `t`. -/
private theorem frameCoord_smul_add_smul (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (s t : ℂ) :
    letI := J.complexModule
    ((⟪e 0, s • e 0 + t • e 2⟫ : ℂ) + Complex.I * ⟪e 1, s • e 0 + t • e 2⟫ = s) ∧
      ((⟪e 2, s • e 0 + t • e 2⟫ : ℂ) + Complex.I * ⟪e 3, s • e 0 + t • e 2⟫ = t) := by
  let := J.complexModule
  have ho (i j : Fin 4) : ⟪e i, e j⟫ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 e.orthonormal i j
  simp only [J.complexModule_smul_def, h₀, h₂, inner_add_right, inner_smul_right, ho]
  refine ⟨Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩ <;> simp

/-- In `(V, J)`, every vector is `z₀ e₀ + z₂ e₂` for its two complex frame coordinates. -/
private theorem eq_frameCoord_smul_add_smul (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (x : V) :
    letI := J.complexModule
    x = ((⟪e 0, x⟫ : ℂ) + Complex.I * ⟪e 1, x⟫) • e 0 +
      ((⟪e 2, x⟫ : ℂ) + Complex.I * ⟪e 3, x⟫) • e 2 := by
  let := J.complexModule
  simp only [J.complexModule_smul_def, h₀, h₂]
  conv_lhs => rw [← e.sum_repr' x, Fin.sum_univ_four]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  module

/-- **The complex determinant in a unitary frame.** If `e` is an orthonormal basis with
`J e₀ = e₁` and `J e₂ = e₃`, then `e₀, e₂` is a basis of the complex vector space `(V, J)`, in which
`x` has the coordinates `z₀(x) = ⟪e₀, x⟫ + i ⟪e₁, x⟫` and `z₂(x) = ⟪e₂, x⟫ + i ⟪e₃, x⟫`. So the
determinant of a complex-linear map `F` of `(V, J)` is
`z₀(F e₀) z₂(F e₂) - z₂(F e₀) z₀(F e₂)`. -/
theorem det_eq_of_orthonormalBasis (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    (F : letI := J.complexModule; V →ₗ[ℂ] V) :
    letI := J.complexModule
    LinearMap.det F =
      ((⟪e 0, F (e 0)⟫ : ℂ) + Complex.I * ⟪e 1, F (e 0)⟫) *
          ((⟪e 2, F (e 2)⟫ : ℂ) + Complex.I * ⟪e 3, F (e 2)⟫) -
        ((⟪e 2, F (e 0)⟫ : ℂ) + Complex.I * ⟪e 3, F (e 0)⟫) *
          ((⟪e 0, F (e 2)⟫ : ℂ) + Complex.I * ⟪e 1, F (e 2)⟫) := by
  let := J.complexModule
  have hli : LinearIndependent ℂ ![e 0, e 2] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    have h := frameCoord_smul_add_smul h₀ h₂ s t
    simp only [hst, inner_zero_right, Complex.ofReal_zero, mul_zero, add_zero] at h
    exact ⟨h.1.symm, h.2.symm⟩
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ![e 0, e 2]) := fun x _ ↦ by
    rw [eq_frameCoord_smul_add_smul h₀ h₂ x]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  set b := Basis.mk hli hsp
  have hb0 : b 0 = e 0 := by simp [b]
  have hb1 : b 1 = e 2 := by simp [b]
  -- The coordinates of `x` in the basis `(e₀, e₂)` are its two complex frame coordinates.
  have hrepr (x : V) : b.repr x 0 = (⟪e 0, x⟫ : ℂ) + Complex.I * ⟪e 1, x⟫ ∧
      b.repr x 1 = (⟪e 2, x⟫ : ℂ) + Complex.I * ⟪e 3, x⟫ := by
    have hx : b.repr x = b.repr (((⟪e 0, x⟫ : ℂ) + Complex.I * ⟪e 1, x⟫) • b 0 +
        ((⟪e 2, x⟫ : ℂ) + Complex.I * ⟪e 3, x⟫) • b 1) := by
      rw [hb0, hb1, ← eq_frameCoord_smul_add_smul h₀ h₂ x]
    rw [hx, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    norm_num
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, (hrepr _).1, (hrepr _).2, hb0, hb1]
  ring

end Det

end TauCeti.AlmostComplexStructure

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

end OrthonormalBasis
