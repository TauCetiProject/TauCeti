/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Analysis.Matrix.Cayley
public import TauCeti.Analysis.Matrix.HermitianSignature.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# The localization axiom for the Maslov index of paths

For a real symmetric matrix `A`, the graph `{x + i A x}` of `A` is a Lagrangian subspace of `ℂⁿ`
meeting `ℝⁿ` in the kernel of `A`. Its unitary frames `U` all have the same Souriau map
`U Uᵀ`, namely the Cayley transform `(1 + i A) (1 - i A)⁻¹` of `A` (`Matrix.cayley`). The
**localization axiom** of Robbin and Salamon computes the Maslov index of a path of such graphs
relative to `ℝⁿ`: if `t ↦ A t` is a continuous path of real symmetric matrices and `γ` a path of
unitary frames with `γ t γ tᵀ = cayley (A t)`, then

`μ(γ) = (sign (A 1) - sign (A 0)) / 2`,

half the change of the signature of `A`
(`Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`). The index only sees
the endpoints of `A`; in particular it vanishes when `A 0` and `A 1` have the same signature.
Frames of the form `(1 + i A) M`, with `M` real, have Souriau map `cayley A`
(`Matrix.UnitaryGroup.souriau_eq_cayley_of_coe_eq_mul`), so the hypothesis holds for every path of
frames of the graphs of `A t` of this form.

The case of diagonal matrices is `Matrix.UnitaryGroup.maslovIndex_eq_sum_sign_of_diagonal_arctan`.
The general case reduces to it in three steps.

* **Naturality.** Moving a path of frames by a fixed real orthogonal matrix `O`, which preserves
  `ℝⁿ`, does not change its Maslov index (`Matrix.UnitaryGroup.maslovIndex_map_mul_left`): the
  Souriau maps are conjugated by `O`, which preserves their determinants and spectra.
* **Segments.** Along the segment `t ↦ t A` from `0` to a symmetric matrix `A = O D Oᵀ`, with `D`
  diagonal and `O` orthogonal, the graphs are framed by `O diag (e^{i arctan (t λⱼ)})`, whose index
  is `sign (A) / 2` by naturality and the diagonal case.
* **Homotopy.** The Maslov index of `γ` is the angle swept by `t ↦ det (cayley (A t))` together
  with spectral terms at the endpoints. Symmetric matrices form a convex, hence simply connected,
  space, so `A` is homotopic to the path through `0` made of two segments, and the swept angle
  only depends on the endpoints.

## Main results

* `Matrix.UnitaryGroup.souriau_eq_cayley_of_coe_eq_mul`: the frames `(1 + i A) M` of the graph
  of `A` have Souriau map `cayley A`.
* `Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`: the localization
  axiom.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the localization axiom).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148.
-/

public section

open Complex
open scoped unitInterval

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace UnitaryGroup

/-! ### Real symmetric matrices -/

/-- The space of real symmetric matrices. -/
private abbrev SymmMatrix (n : Type*) := ↥{B : Matrix n n ℝ | B.IsHermitian}

/-- **The Souriau map of a frame of a graph.** A unitary frame `U = (1 + i A) M`, with `M` a
real matrix, of the graph `{x + i A x}` of a real symmetric matrix `A` has Souriau map the
Cayley transform of `A`. -/
theorem souriau_eq_cayley_of_coe_eq_mul {U : unitaryGroup n ℂ} {A M : Matrix n n ℝ}
    (hA : A.IsHermitian)
    (hU : (U : Matrix n n ℂ) = (1 + Complex.I • A.map (↑)) * M.map ((↑) : ℝ → ℂ)) :
    (souriau U : Matrix n n ℂ) = cayley (A.map (↑)) := by
  set X : Matrix n n ℂ := 1 + Complex.I • A.map (↑) with hXdef
  set Y : Matrix n n ℂ := 1 - Complex.I • A.map (↑) with hYdef
  set N : Matrix n n ℂ := M.map (↑) with hNdef
  have hAc := hA.map_ofReal
  have hX := hAc.isUnit_det_one_add_I_smul
  have hAT : (A.map ((↑) : ℝ → ℂ))ᵀ = A.map (↑) := by
    rw [← transpose_map, ← conjTranspose_eq_transpose_of_trivial, hA.eq]
  have hXT : Xᵀ = X := by rw [hXdef, transpose_add, transpose_one, transpose_smul, hAT]
  have hXH : Xᴴ = Y := by
    rw [hXdef, hYdef, conjTranspose_add, conjTranspose_one, conjTranspose_smul, hAc.eq,
      star_def, conj_I, neg_smul, sub_eq_add_neg]
  have hNH : Nᴴ = Nᵀ := by
    rw [hNdef, ← conjTranspose_map _ fun _ => (conj_ofReal _).symm,
      conjTranspose_eq_transpose_of_trivial, transpose_map]
  -- Unitarity of `U` gives `Nᵀ (Y X) N = 1`, hence `N Nᵀ = (Y X)⁻¹`.
  have hunit : Nᵀ * (Y * X) * N = 1 := by
    have h := mem_unitaryGroup_iff'.1 U.2
    rw [star_eq_conjTranspose, hU, conjTranspose_mul, hXH, hNH] at h
    simpa only [Matrix.mul_assoc] using h
  have hNN : N * Nᵀ = (Y * X)⁻¹ :=
    (inv_eq_left_inv (by rw [Matrix.mul_assoc, mul_eq_one_comm.1 hunit])).symm
  calc (souriau U : Matrix n n ℂ) = X * (N * Nᵀ) * X := by
        rw [coe_souriau, hU, transpose_mul, hXT]
        simp only [Matrix.mul_assoc]
    _ = X * (X⁻¹ * Y⁻¹) * X := by rw [hNN, Matrix.mul_inv_rev]
    _ = Y⁻¹ * X := by rw [mul_nonsing_inv_cancel_left _ _ hX]
    _ = cayley (A.map (↑)) := (cayley_eq_inv_mul _).symm

/-- The determinant of the Cayley transform of a real symmetric matrix, as a point of the
circle. -/
private noncomputable def cayleyDet (B : SymmMatrix n) : Circle :=
  detCircle ⟨cayley (B.1.map ((↑) : ℝ → ℂ)), B.2.map_ofReal.cayley_mem_unitaryGroup⟩

private theorem continuous_cayleyDet : Continuous (cayleyDet (n := n)) := by
  have hz : Continuous fun B : SymmMatrix n => det (1 + Complex.I • B.1.map ((↑) : ℝ → ℂ)) :=
    Continuous.matrix_det (A := fun B : SymmMatrix n => 1 + Complex.I • B.1.map ((↑) : ℝ → ℂ))
      (continuous_const.add
        ((continuous_subtype_val.matrix_map continuous_ofReal).const_smul Complex.I))
  have hc : Continuous fun B : SymmMatrix n => (cayleyDet B : ℂ) :=
    (hz.div (continuous_conj.comp hz) fun B => (map_ne_zero _).2
      B.2.map_ofReal.isUnit_det_one_add_I_smul.ne_zero).congr fun B => by
        simp only [cayleyDet, coe_detCircle]
        exact B.2.map_ofReal.det_cayley.symm
  exact continuous_induced_rng.2 hc

/-- A frame whose Souriau map is the Cayley transform of `B` has Maslov phase `det (cayley B)`. -/
private theorem detCircle_souriau_eq_cayleyDet {U : unitaryGroup n ℂ} {B : SymmMatrix n}
    (h : (souriau U : Matrix n n ℂ) = cayley (B.1.map ((↑) : ℝ → ℂ))) :
    detCircle (souriau U) = cayleyDet B :=
  congrArg detCircle (Subtype.ext h)

/-- **The Maslov index through a path of symmetric matrices.** If the Souriau maps of `γ` are the
Cayley transforms along a path `P` of symmetric matrices, the Maslov index of `γ` is read off the
angle swept by `t ↦ det (cayley (P t))` and the endpoints of `P`. -/
private theorem maslovIndex_eq_angleChange_cayleyDet {U V : unitaryGroup n ℂ} (γ : Path U V)
    {B₀ B₁ : SymmMatrix n} (P : Path B₀ B₁)
    (h : ∀ t, (souriau (γ t) : Matrix n n ℂ) = cayley ((P t).1.map ((↑) : ℝ → ℂ))) :
    maslovIndex γ = Circle.angleChange (P.map continuous_cayleyDet) / (2 * Real.pi) -
      (spectralAngleSum (cayley (B₁.1.map ((↑) : ℝ → ℂ))) -
        spectralAngleSum (cayley (B₀.1.map ((↑) : ℝ → ℂ)))) := by
  have h0 := h 0
  have h1 := h 1
  rw [γ.source, P.source] at h0
  rw [γ.target, P.target] at h1
  rw [maslovIndex_def, Circle.angleChange_congr (detSouriauPath γ) (P.map continuous_cayleyDet)
    fun t => by simpa using detCircle_souriau_eq_cayleyDet (h t), h0, h1]

/-! ### Segments of symmetric matrices -/

/-- The segment `t ↦ t B` from `0` to a symmetric matrix `B`. -/
private def segment (B : SymmMatrix n) : Path (⟨0, isHermitian_zero⟩ : SymmMatrix n) B where
  toFun t := ⟨(t : ℝ) • B.1, B.2.smul (IsSelfAdjoint.all _)⟩
  continuous_toFun := (continuous_subtype_val.smul continuous_const).subtype_mk _
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

omit [Fintype n] [DecidableEq n] in
private theorem coe_segment_apply (B : SymmMatrix n) (t : I) :
    ((segment B t : SymmMatrix n) : Matrix n n ℝ) = (t : ℝ) • B.1 :=
  (rfl)

/-- The eigenvector matrix of a symmetric matrix, as a unitary complex matrix. -/
private noncomputable def eigenFrame (B : SymmMatrix n) : unitaryGroup n ℂ :=
  ⟨(B.2.eigenvectorUnitary : Matrix n n ℝ).map (↑),
    map_ofReal_mem_unitaryGroup B.2.eigenvectorUnitary.2⟩

private theorem eigenFrame_mul_transpose (B : SymmMatrix n) :
    (eigenFrame B : Matrix n n ℂ) * (eigenFrame B : Matrix n n ℂ)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self B.2.eigenvectorUnitary
  rw [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  simp only [eigenFrame, ← transpose_map]
  -- `Matrix.map_mul` at `Complex.ofRealHom`, whose coercion is `(↑)` (`Complex.ofRealHom_eq_coe`).
  exact (Matrix.map_mul (f := Complex.ofRealHom)).symm.trans <| by
    rw [h, Matrix.map_one _ (by simp) (by simp)]

/-- The diagonal frames `diag (e^{i arctan (t λⱼ)})` of the graphs of `t D`, for `D` the
diagonal matrix of eigenvalues of `B`. -/
private noncomputable def diagonalFrame (B : SymmMatrix n) :
    Path (TauCeti.unitaryTorusHom n fun j => Circle.exp (Real.arctan ((0 : I) * B.2.eigenvalues j)))
      (TauCeti.unitaryTorusHom n fun j => Circle.exp (Real.arctan ((1 : I) * B.2.eigenvalues j)))
    where
  toFun t := TauCeti.unitaryTorusHom n fun j => Circle.exp (Real.arctan (t * B.2.eigenvalues j))
  continuous_toFun := TauCeti.continuous_unitaryTorusHom.comp <| continuous_pi fun _ =>
    Circle.exp.continuous.comp (Real.continuous_arctan.comp
      (continuous_subtype_val.mul continuous_const))
  source' := rfl
  target' := rfl

/-- The frames `O diag (e^{i arctan (t λⱼ)})` of the graphs of `t B = O (t D) Oᵀ`. -/
private noncomputable def segmentFrame (B : SymmMatrix n) :=
  (diagonalFrame B).map (continuous_const_mul (eigenFrame B))

private theorem segmentFrame_apply (B : SymmMatrix n) (t : I) :
    segmentFrame B t = eigenFrame B * diagonalFrame B t :=
  (rfl)

/-- A real symmetric matrix, read as a complex matrix, in its eigenvector frame. -/
private theorem map_ofReal_smul_eq (B : SymmMatrix n) (t : ℝ) :
    ((t • B.1).map ((↑) : ℝ → ℂ)) = (eigenFrame B : Matrix n n ℂ) *
      diagonal (fun j => ((t * B.2.eigenvalues j : ℝ) : ℂ)) * (eigenFrame B : Matrix n n ℂ)ᵀ := by
  have hsmul : (t • B.1).map ((↑) : ℝ → ℂ) = (t : ℂ) • B.1.map ((↑) : ℝ → ℂ) := by
    ext i j
    simp
  have hdiag : diagonal (fun j => ((t * B.2.eigenvalues j : ℝ) : ℂ)) =
      (t : ℂ) • (diagonal (RCLike.ofReal ∘ B.2.eigenvalues)).map ((↑) : ℝ → ℂ) := by
    simp [diagonal_map, ← diagonal_smul, Pi.smul_def]
  have h := B.2.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] at h
  rw [hsmul, hdiag, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  conv_lhs => rw [h]
  simp only [eigenFrame, ← transpose_map]
  -- `Matrix.map_mul` at `Complex.ofRealHom`, whose coercion is `(↑)` (`Complex.ofRealHom_eq_coe`).
  exact (Matrix.map_mul (f := Complex.ofRealHom)).trans
    (congrArg (· * _) (Matrix.map_mul (f := Complex.ofRealHom)))

/-- The frames `O diag (e^{i arctan (t λⱼ)})` frame the graphs of the segment `t ↦ t B`: their
Souriau maps are the Cayley transforms of `t B`. -/
private theorem souriau_segmentFrame (B : SymmMatrix n) (t : I) :
    (souriau (segmentFrame B t) : Matrix n n ℂ) =
      cayley ((segment B t).1.map ((↑) : ℝ → ℂ)) := by
  have hO := eigenFrame_mul_transpose B
  have hD : (souriau (diagonalFrame B t) : Matrix n n ℂ) =
      diagonal fun j => exp (↑(2 * Real.arctan (t * B.2.eigenvalues j)) * Complex.I) := by
    rw [coe_souriau_of_coe_eq_diagonal (d := fun j =>
      exp (↑(Real.arctan (t * B.2.eigenvalues j)) * Complex.I))
        (by simp [diagonalFrame, Circle.coe_exp])]
    congr 1
    funext j
    rw [sq, ← exp_add]
    push_cast
    ring_nf
  rw [segmentFrame_apply, coe_segment_apply, coe_souriau_mul_left, hD, map_ofReal_smul_eq,
    cayley_conj hO (mul_eq_one_comm.1 hO), cayley_diagonal_ofReal]

/-- Along the segment from `0` to `B`, the Maslov index of the graphs is `sign (B) / 2`. -/
private theorem maslovIndex_segmentFrame (B : SymmMatrix n) :
    maslovIndex (segmentFrame B) = (signature B.1 : ℝ) / 2 := by
  have hsig : signature B.1 = B.2.signature :=
    (IsHermitian.signature_map_ofReal (𝕜 := ℝ) (M := B.1) B.2).symm
  rw [hsig, segmentFrame, maslovIndex_map_mul_left _ (eigenFrame_mul_transpose B),
    maslovIndex_eq_sum_sign_of_diagonal_arctan (diagonalFrame B)
      (a := fun j t => t * B.2.eigenvalues j)
      (fun j => continuous_subtype_val.mul continuous_const)
      (fun t => by simp [diagonalFrame, Circle.coe_exp]),
    IsHermitian.signature_def, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy (B.2.eigenvalues j) 0 with h | h | h
  · simp [h, Real.sign_of_neg, h.not_gt]
  · simp [h]
  · simp [h, Real.sign_of_pos]

/-- **The localization axiom of Robbin and Salamon.** Let `t ↦ A t` be a continuous path of real
symmetric matrices and `γ` a path of unitary frames of their graphs `{x + i A t x}`, that is, with
Souriau maps `γ t γ tᵀ` the Cayley transforms `(1 + i A t) (1 - i A t)⁻¹`. Then the Maslov index
of `γ` relative to `ℝⁿ` is half the change of the signature of `A`. -/
theorem maslovIndex_eq_signature_sub_of_souriau_eq_cayley {U V : unitaryGroup n ℂ}
    (γ : Path U V) {A : I → Matrix n n ℝ} (hAc : Continuous A) (hA : ∀ t, (A t).IsHermitian)
    (hγ : ∀ t, (souriau (γ t) : Matrix n n ℂ) = cayley ((A t).map ((↑) : ℝ → ℂ))) :
    maslovIndex γ = (signature (A 1) - signature (A 0) : ℝ) / 2 := by
  have : ContractibleSpace (SymmMatrix n) :=
    Convex.contractibleSpace (fun _ hB _ hC a b _ _ _ =>
      (hB.smul (IsSelfAdjoint.all a)).add (hC.smul (IsSelfAdjoint.all b))) ⟨0, isHermitian_zero⟩
  let B₀ : SymmMatrix n := ⟨A 0, hA 0⟩
  let B₁ : SymmMatrix n := ⟨A 1, hA 1⟩
  let P : Path B₀ B₁ := ⟨⟨fun t => ⟨A t, hA t⟩, hAc.subtype_mk _⟩, rfl, rfl⟩
  -- In the simply connected space of symmetric matrices, `P` is homotopic to the path through
  -- `0` made of two segments, so it sweeps the same angle.
  have hangle : Circle.angleChange (P.map continuous_cayleyDet) =
      Circle.angleChange ((segment B₁).map continuous_cayleyDet) -
        Circle.angleChange ((segment B₀).map continuous_cayleyDet) := by
    rw [Circle.angleChange_eq_of_homotopic ((SimplyConnectedSpace.paths_homotopic P
      ((segment B₀).symm.trans (segment B₁))).map ⟨_, continuous_cayleyDet⟩)]
    simp only [ContinuousMap.coe_mk, Path.map_trans, Circle.angleChange_trans]
    rw [← Path.map_symm, Circle.angleChange_symm]
    ring
  have hγ' := maslovIndex_eq_angleChange_cayleyDet γ P hγ
  have h₀ := maslovIndex_eq_angleChange_cayleyDet (segmentFrame B₀) (segment B₀)
    (souriau_segmentFrame B₀)
  have h₁ := maslovIndex_eq_angleChange_cayleyDet (segmentFrame B₁) (segment B₁)
    (souriau_segmentFrame B₁)
  rw [maslovIndex_segmentFrame] at h₀ h₁
  rw [hγ', hangle, sub_div, sub_div]
  linarith

end UnitaryGroup

end Matrix
