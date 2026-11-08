/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The graph of a loop of symplectic matrices and its Maslov index

Identify `ℝ^{n ⊕ n}` with `ℂⁿ` by `φ (x, y) = x + i y`, the convention of `Matrix.realify`, so that
the standard symplectic form and complex structure of `ℝ^{n ⊕ n}` are those of `ℂⁿ`. The graph of
a symplectic matrix `A` is a Lagrangian subspace of `ℝ^{n ⊕ n} × ℝ^{n ⊕ n}` with the symplectic
form `(-ω) ⊕ ω`. Its first factor carries the complex structure `-J`, which `conj ∘ φ` turns into
multiplication by `i`. So in `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}` the graph is the real subspace

`Γ(A) = {(conj (φ x), φ (A x)) | x ∈ ℝ^{n ⊕ n}}`

(`TauCeti.GLSymplectic.graphSubspace`, characterized by
`TauCeti.GLSymplectic.mem_graphSubspace_iff`). It is the image of the real points `ℝ^{n ⊕ n}` of
`ℂ^{n ⊕ n}` under the complex matrix `TauCeti.GLSymplectic.graphFrame A`, whose columns are the
images of the real basis vectors. That matrix is invertible when `A` is symplectic
(`TauCeti.GLSymplectic.isUnit_det_graphFrame`), so the graphs of a loop `γ` of symplectic matrices
form a loop of maximal totally real subspaces with a continuous frame
(`TauCeti.GLSymplectic.graphLoop`).

The main result is that **the Maslov index of the graph loop is twice the Maslov index of the
loop**, `μ(Γ ∘ γ) = 2 μ(γ)` (`TauCeti.GLSymplectic.maslovIndex_graphLoop`). Here `μ(γ)` is the
degree of `t ↦ ρ(γ t)` (`TauCeti.GLSymplectic.maslovIndex`) and `μ(Γ ∘ γ)` is the native Maslov
index of loops of totally real subspaces (`TauCeti.TotallyRealLoop.maslovIndex`), the degree of the
determinant phase `det / conj det` of a frame. This fixes the factor two between the Maslov index of
a loop of symplectic matrices, which measures the winding of a symplectic trivialization along a
loop, and the Maslov index of its graph. Graphs relative to the diagonal are also how the
Conley–Zehnder index of symplectic paths is expressed as a Robbin–Salamon index.

## Proof

The determinant of the frame is `det ((A₁₂ - A₂₁) + i (A₁₁ + A₂₂))` by a Schur complement
(`TauCeti.GLSymplectic.det_graphFrame`), and its phase is the Maslov phase of the graph
(`TauCeti.GLSymplectic.coe_graphPhase_eq_maslovPhase`). The realification of
`(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)` is `A J + J A`, which is invertible when `A` is symplectic
(`SymplecticGroup.isUnit_det_mul_J_add_J_mul`), so the frame is invertible. For a realified
unitary matrix `A = U_ℝ` the complex matrix is `2 i U`, so the graph phase is
`(-1)ⁿ (det U)² = (-1)ⁿ ρ(A)²`
(`TauCeti.GLSymplectic.coe_graphPhase_inclusion`). A general loop is deformed to its loop of
orthogonal polar factors through symplectic matrices, which changes no degree
(`TauCeti.GLSymplectic.degree_map_inclusion_polarUnitary`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.3 (the Maslov index of loops
  of Lagrangian subspaces and of loops of symplectic matrices).
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (graphs of symplectic paths and the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Complex
open scoped unitInterval ComplexConjugate

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The graph frame -/

/-- The **graph frame** of a real matrix `A` on `ℝ^{n ⊕ n}`: the complex matrix sending the real
point `x` of `ℂ^{n ⊕ n}` to `(conj (φ x), φ (A x))`, where `φ (x, y) = x + i y`. Its columns are the
images of the real basis vectors, so it frames the graph `TauCeti.GLSymplectic.graphSubspace A`. -/
noncomputable def graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 (-(Complex.I • 1))
    (A.toBlocks₁₁.map (↑) + Complex.I • A.toBlocks₂₁.map (↑))
    (A.toBlocks₁₂.map (↑) + Complex.I • A.toBlocks₂₂.map (↑))

/-- The graph frame sends the real point `x` to `(conj (φ x), φ (A x))`, where `φ (x, y) = x + i y`.
-/
theorem graphFrame_mulVec (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x : n ⊕ n → ℝ) :
    graphFrame A *ᵥ (fun k => (x k : ℂ)) =
      Sum.elim (fun i => conj ((x (.inl i) : ℂ) + x (.inr i) * Complex.I))
        (fun i => ((A *ᵥ x) (.inl i) : ℂ) + (A *ᵥ x) (.inr i) * Complex.I) := by
  ext (i | i)
  · simp [graphFrame, fromBlocks_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      mul_comm]
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, graphFrame, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, toBlocks₁₁,
      toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, Sum.elim_inr, smul_eq_mul, ofReal_add,
      ofReal_sum, ofReal_mul]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring

/-- The complex `n × n` matrix `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)`, whose determinant is that of the
graph frame and whose realification is `A J + J A`. -/
private noncomputable def graphCore (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix n n ℂ :=
  (A.toBlocks₁₂ - A.toBlocks₂₁).map ((↑) : ℝ → ℂ) +
    Complex.I • (A.toBlocks₁₁ + A.toBlocks₂₂).map ((↑) : ℝ → ℂ)

/-- The determinant of the graph frame is `det ((A₁₂ - A₂₁) + i (A₁₁ + A₂₂))`. -/
theorem det_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphFrame A).det =
      ((A.toBlocks₁₂ - A.toBlocks₂₁).map ((↑) : ℝ → ℂ) +
    Complex.I • (A.toBlocks₁₁ + A.toBlocks₂₂).map ((↑) : ℝ → ℂ)).det := by
  rw [graphFrame, det_fromBlocks_one₁₁]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_apply, smul_eq_mul, ofReal_sub,
    ofReal_add]
  ring_nf
  rw [I_sq]
  ring

/-- The realification of `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)` is `A J + J A`. -/
private theorem realify_graphCore (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphCore A).realify = A * J n ℝ + J n ℝ * A := by
  ext (i | i) (j | j) <;>
    simp [graphCore, J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, toBlocks₁₁,
      toBlocks₁₂, toBlocks₂₁, toBlocks₂₂] <;> ring

/-- **The graph frame of a symplectic matrix is invertible.** -/
theorem isUnit_det_graphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hA : A ∈ symplecticGroup n ℝ) :
    IsUnit (graphFrame A).det := by
  have h := SymplecticGroup.isUnit_det_mul_J_add_J_mul hA
  rw [← realify_graphCore, det_realify] at h
  rw [det_graphFrame, isUnit_iff_ne_zero]
  intro h0
  apply (isUnit_iff_ne_zero.1 h)
  simp [graphCore, h0]

omit [Fintype n] in
/-- The graph frame depends continuously on the matrix. -/
theorem continuous_graphFrame : Continuous (graphFrame : Matrix (n ⊕ n) (n ⊕ n) ℝ → _) := by
  refine Continuous.matrix_fromBlocks continuous_const continuous_const ?_ ?_ <;>
  refine continuous_matrix fun i j => ?_ <;>
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, toBlocks₁₁,
    toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply] <;>
  fun_prop

/-! ### The graph subspace -/

/-- The **graph** of a real matrix `A` on `ℝ^{n ⊕ n}`, as a real subspace of
`ℂ^{n ⊕ n} = ℂⁿ × ℂⁿ`: the image of the real points under the graph frame, that is, the set of
`(conj (φ x), φ (A x))` (`TauCeti.GLSymplectic.mem_graphSubspace_iff`). -/
noncomputable def graphSubspace (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Submodule ℝ (n ⊕ n → ℂ) :=
  (LinearMap.range (Complex.ofRealAm.toLinearMap.compLeft (n ⊕ n))).map
    ((Matrix.toLin' (graphFrame A)).restrictScalars ℝ)

/-- A vector of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}` lies on the graph of `A` exactly when it is
`(conj (φ x), φ (A x))` for a real vector `x`, where `φ (x, y) = x + i y`. -/
theorem mem_graphSubspace_iff {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} {w : n ⊕ n → ℂ} :
    w ∈ graphSubspace A ↔ ∃ x : n ⊕ n → ℝ,
      Sum.elim (fun i => conj ((x (.inl i) : ℂ) + x (.inr i) * Complex.I))
        (fun i => ((A *ᵥ x) (.inl i) : ℂ) + (A *ᵥ x) (.inr i) * Complex.I) = w := by
  simp only [graphSubspace, Submodule.mem_map, LinearMap.mem_range, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (graphFrame_mulVec A x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, graphFrame_mulVec A x⟩

/-- The graph of a symplectic matrix is maximal totally real. -/
theorem isMaximalTotallyReal_graphSubspace {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (n ⊕ n → ℂ) Complex.I).restrictScalars ℝ)
      (graphSubspace A) :=
  letI := invertibleOfIsUnitDet _ (isUnit_det_graphFrame hA)
  isMaximalTotallyReal_range_compLeft_ofReal.map_linearEquiv (Matrix.toLinearEquiv' _ this)

/-- The graph frame of a symplectic matrix, as a complex-linear automorphism of `ℂ^{n ⊕ n}`. -/
noncomputable def graphFrameEquiv (A : GLSymplectic n ℝ) : (n ⊕ n → ℂ) ≃L[ℂ] (n ⊕ n → ℂ) :=
  letI := invertibleOfIsUnitDet _ (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2))
  (Matrix.toLinearEquiv' (graphFrame (A : GL (n ⊕ n) ℝ)) this).toContinuousLinearEquiv

/-- The graph frame automorphism acts as its matrix. -/
theorem coe_graphFrameEquiv (A : GLSymplectic n ℝ) :
    ((graphFrameEquiv A).toLinearEquiv : (n ⊕ n → ℂ) →ₗ[ℂ] (n ⊕ n → ℂ)) =
      Matrix.toLin' (graphFrame (A : GL (n ⊕ n) ℝ)) :=
  (rfl)

/-- The graph of a symplectic matrix is the image of the real points under its graph frame
automorphism. -/
theorem graphSubspace_eq_map (A : GLSymplectic n ℝ) :
    graphSubspace (A : GL (n ⊕ n) ℝ) =
      (LinearMap.range (Complex.ofRealAm.toLinearMap.compLeft (n ⊕ n))).map
        (((graphFrameEquiv A).toLinearEquiv : (n ⊕ n → ℂ) →ₗ[ℂ] (n ⊕ n → ℂ)).restrictScalars ℝ) :=
  (rfl)

/-- The graph frame automorphism depends continuously on the symplectic matrix. -/
theorem continuous_graphFrameEquiv :
    Continuous fun A : GLSymplectic n ℝ =>
      (graphFrameEquiv A : (n ⊕ n → ℂ) →L[ℂ] (n ⊕ n → ℂ)) := by
  let e : Matrix (n ⊕ n) (n ⊕ n) ℂ →ₗ[ℂ] ((n ⊕ n → ℂ) →L[ℂ] (n ⊕ n → ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Matrix.toLin'.toLinearMap
  have he : Continuous e := e.continuous_of_finiteDimensional
  refine (he.comp (continuous_graphFrame.comp
    (Units.continuous_val.comp continuous_subtype_val))).congr fun A => ?_
  ext1 v
  rfl

/-! ### The graph phase -/

/-- The determinant of the graph frame of a symplectic matrix does not vanish. -/
theorem det_graphFrame_ne_zero (A : GLSymplectic n ℝ) :
    (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0 :=
  (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2)).ne_zero

/-- The **graph phase** of a symplectic matrix `A`: the determinant phase `det F / conj (det F)` of
its graph frame `F`, which is the Maslov phase of the graph of `A` relative to the real points. -/
noncomputable def graphPhase (A : GLSymplectic n ℝ) : Circle :=
  Circle.ofConjDivSelf (conj (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det)
    ((map_ne_zero _).2 (det_graphFrame_ne_zero A))

/-- The graph phase is `det F / conj (det F)` for the graph frame `F`. -/
theorem coe_graphPhase (A : GLSymplectic n ℝ) :
    (graphPhase A : ℂ) =
      (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det /
        conj (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det := by
  simp [graphPhase]

/-- **The graph phase is the Maslov phase of the graph** relative to the real points of
`ℂ^{n ⊕ n}`. -/
theorem coe_graphPhase_eq_maslovPhase (A : GLSymplectic n ℝ) :
    (graphPhase A : ℂ) = isMaximalTotallyReal_range_compLeft_ofReal.maslovPhase
      (isMaximalTotallyReal_graphSubspace (mem_iff_mem_symplecticGroup.1 A.2)) := by
  -- `graphSubspace A` is by definition the image of the real points under the graph frame
  -- (`graphSubspace_eq_map`), so the two maximal-totally-real proofs concern the same subspace.
  refine Eq.trans ?_ ((isMaximalTotallyReal_range_compLeft_ofReal.maslovPhase_map
    (graphFrameEquiv A).toLinearEquiv).symm.trans rfl)
  rw [coe_graphPhase, coe_graphFrameEquiv, LinearMap.det_toLin']

/-- The graph phase depends continuously on the symplectic matrix. -/
theorem continuous_graphPhase : Continuous (graphPhase : GLSymplectic n ℝ → Circle) := by
  have hd : Continuous fun A : GLSymplectic n ℝ =>
      (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det :=
    (continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val)).matrix_det
  refine Continuous.subtype_mk ?_ _
  refine (hd.div (continuous_conj.comp hd) fun A => ?_).congr fun A => (coe_graphPhase A).symm
  exact (map_ne_zero _).2 (det_graphFrame_ne_zero A)

/-- On an orthogonal symplectic matrix, the realification of a unitary matrix `U`, the graph phase
is `(-1)ⁿ (det U)² = (-1)ⁿ ρ²`: the graph frame has determinant `det (2 i U) = (2 i)ⁿ det U`. -/
theorem coe_graphPhase_inclusion (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    (graphPhase (Subgroup.inclusion inf_le_left U) : ℂ) =
      (-1) ^ Fintype.card n * (maslovPhase (Subgroup.inclusion inf_le_left U) : ℂ) ^ 2 := by
  set V := unitaryGroupEquivSymplecticInfOrthogonal.symm U
  have hV : (((Subgroup.inclusion inf_le_left U : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ) = (V : Matrix n n ℂ).realify := by
    rw [Subgroup.coe_inclusion,
      ← realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply,
      GeneralLinearGroup.coe_realify, Unitary.val_toUnits_apply]
  have hcore : (((V : Matrix n n ℂ).realify.toBlocks₁₂ - (V : Matrix n n ℂ).realify.toBlocks₂₁).map
      ((↑) : ℝ → ℂ) + Complex.I • ((V : Matrix n n ℂ).realify.toBlocks₁₁ +
        (V : Matrix n n ℂ).realify.toBlocks₂₂).map ((↑) : ℝ → ℂ) : Matrix n n ℂ) =
      (2 * Complex.I) • (V : Matrix n n ℂ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, toBlocks₁₁,
      toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, realify_apply_inl_inl,
      realify_apply_inl_inr, realify_apply_inr_inl, realify_apply_inr_inr, RCLike.re_to_complex,
      RCLike.im_to_complex, smul_eq_mul, ofReal_sub, ofReal_neg, ofReal_add]
    apply Complex.ext <;> simp <;> ring
  have hdet : (graphFrame (((Subgroup.inclusion inf_le_left U : GLSymplectic n ℝ) :
      GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det =
      (2 * Complex.I) ^ Fintype.card n * (V : Matrix n n ℂ).det := by
    rw [det_graphFrame, hV, hcore, det_smul]
  have hρ : (maslovPhase (Subgroup.inclusion inf_le_left U) : ℂ) = (V : Matrix n n ℂ).det := by
    rw [maslovPhase_inclusion, coe_detCircle]
  have hconj : conj (V : Matrix n n ℂ).det = ((V : Matrix n n ℂ).det)⁻¹ := by
    rw [← coe_detCircle, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  have hne : (V : Matrix n n ℂ).det ≠ 0 := by
    rw [← coe_detCircle]
    exact Circle.coe_ne_zero _
  have h2I : (2 * Complex.I) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (by simp)
  rw [coe_graphPhase, hdet, hρ, map_mul, map_pow, hconj, map_mul, map_ofNat, conj_I,
    show 2 * -Complex.I = (-1) * (2 * Complex.I) by ring, mul_pow]
  field_simp
  rw [← mul_pow, ← mul_pow]
  ring_nf

/-! ### The Maslov index of the graph loop -/

/-- The **graph loop** of a loop `γ` of symplectic matrices: the loop `t ↦ Γ(γ t)` of graphs, as a
loop of maximal totally real subspaces of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`, framed by the graph frames. -/
noncomputable def graphLoop {A : GLSymplectic n ℝ} (γ : Path A A) :
    TotallyRealLoop (n ⊕ n → ℂ) where
  toFun t := graphSubspace (γ t : GL (n ⊕ n) ℝ)
  exists_frame := ⟨_, isMaximalTotallyReal_range_compLeft_ofReal, fun t => graphFrameEquiv (γ t),
    continuous_graphFrameEquiv.comp γ.continuous, fun _ => rfl⟩
  toFun_zero_eq_toFun_one := by simp

/-- The graph loop at time `t` is the graph of `γ t`. -/
@[simp]
theorem graphLoop_apply {A : GLSymplectic n ℝ} (γ : Path A A) (t : I) :
    graphLoop γ t = graphSubspace (γ t : GL (n ⊕ n) ℝ) :=
  (rfl)

/-- **The Maslov index of the graph loop is twice the Maslov index of the loop.** For a loop `γ`
of symplectic matrices, the loop of graphs `t ↦ Γ(γ t)` in `ℂⁿ × ℂⁿ` has native Maslov index
`2 μ(γ)`. -/
theorem maslovIndex_graphLoop {A : GLSymplectic n ℝ} (γ : Path A A) :
    (graphLoop γ).maslovIndex = 2 * maslovIndex γ := by
  have hL₀ := isMaximalTotallyReal_range_compLeft_ofReal (ι := n ⊕ n)
  -- The Maslov phase of the graph relative to the real points is the graph phase.
  have hphase (t : I) : ((γ.map continuous_graphPhase) t : ℂ) =
      hL₀.maslovPhase ((graphLoop γ).isMaximalTotallyReal t) :=
    coe_graphPhase_eq_maslovPhase (γ t)
  -- On the orthogonal polar factors the graph phase is `(-1)ⁿ ρ²`.
  let c : Circle := ⟨(-1) ^ Fintype.card n, mem_sphere_zero_iff_norm.2 (by simp)⟩
  have hunit : Circle.degree ((γ.map continuous_inclusion_polarUnitary).map continuous_graphPhase) =
      Circle.degree ((Path.refl c).mul ((γ.map continuous_maslovPhase).map (continuous_pow 2))) :=
    Circle.degree_congr _ _ fun t => by
      rw [Path.mul_apply, Path.refl_apply]
      refine Circle.ext ?_
      simp only [Path.map_coe, Function.comp_apply, Circle.coe_mul]
      rw [coe_graphPhase_inclusion, maslovPhase_inclusion_polarUnitary]
      simp [c]
  rw [(graphLoop γ).maslovIndex_eq_degree hL₀ _ hphase, ← degree_map_inclusion_polarUnitary,
    hunit, Circle.degree_mul, Circle.degree_refl, Circle.degree_map_pow, maslovIndex_def]
  push_cast
  ring

end TauCeti.GLSymplectic
