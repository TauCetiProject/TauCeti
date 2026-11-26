/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.PositiveDefiniteMatrix
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.LinearAlgebra.Matrix.Hermitian.TraceZero
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The positive-definite matrices of determinant one

Over `𝕜 = ℝ` or `ℂ`, the positive-definite matrices of determinant one,

`P₁ = {P ∈ Matrix n n 𝕜 | P positive definite, det P = 1}`

(`Matrix.PosDefDetOne n 𝕜`), form an embedded submanifold of the positive-definite cone
`Matrix.posDefOpens n 𝕜`, itself an open subset of the real vector space of Hermitian (over `ℝ`,
symmetric) matrices. They are the positive factors in the polar decomposition
`A = P U` of the matrices of determinant one, where `U` is special unitary (special orthogonal
over `ℝ`).

The determinant of a positive-definite matrix is a positive real number, and along the ray
`t ↦ eᵗ P` it is `e^(t · card n) det P`, so `1` is a regular value of the real part of the
determinant (the determinant read as a real function) on the cone when `n` is nonempty. Hence
`P₁` is a regular level, and it carries the analytic atlas of `TauCeti.regularLevelChartedSpace`,
modelled on a real vector space of dimension one less than that of the Hermitian matrices
(`Matrix.PosDefDetOne.Model`). As for the special linear group, the atlas is chosen
nonconstructively: its public properties are the manifold instance
`Matrix.PosDefDetOne.instIsManifold` and the smooth embedding
`Matrix.PosDefDetOne.isSmoothEmbedding_subtypeVal` into the cone. For an empty index type, `P₁`
is a point and carries the discrete atlas.

The matrix exponential restricts to **exponential coordinates** on `P₁`: since
`det (exp X) = exp (trace X)`, it maps the trace-free Hermitian matrices
(`Matrix.traceZeroSelfAdjoint n 𝕜`) onto `P₁`, and with the matrix logarithm as inverse it is a
global real diffeomorphism (`Matrix.traceZeroExpDiffeomorph`). This is the restriction to `P₁` of
the exponential coordinates `Matrix.hermitianExpDiffeomorph` on the whole cone.

To state or use these results, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`, as for the cone.

## Main declarations

* `Matrix.PosDefDetOne`: the positive-definite matrices of determinant one, as a subtype of the
  positive-definite cone.
* `Matrix.PosDefDetOne.instChartedSpace`, `Matrix.PosDefDetOne.instIsManifold`: the analytic
  regular-level manifold structure (the discrete one on a point for an empty index type).
* `Matrix.PosDefDetOne.isSmoothEmbedding_subtypeVal`: the inclusion into the positive-definite cone
  is an analytic embedding.
* `Matrix.PosDefDetOne.contMDiff_subtypeVal_comp_iff`: a map into `P₁` is `C^k` exactly when it is
  `C^k` into the cone.
* `Matrix.traceZeroExpDiffeomorph`: the exponential coordinates `X ↦ exp X` on `P₁`, with inverse
  the matrix logarithm.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Corollary 5.14 (the regular level set theorem).
-/

public noncomputable section

open NormedSpace Manifold
open scoped Manifold ContDiff Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n 𝕜) in
/-- The **positive-definite matrices of determinant one**, as a subtype of the positive-definite
cone `Matrix.posDefOpens n 𝕜`. For a nonempty index type they carry the regular-level manifold
structure `Matrix.PosDefDetOne.instChartedSpace`; for an empty one they form a point, with the
discrete structure. -/
abbrev PosDefDetOne : Type _ :=
  {P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1}

namespace PosDefDetOne

variable (n 𝕜) in
/-- The model vector space of the positive-definite matrices of determinant one. For a nonempty
index type its dimension is one less than the real dimension of the Hermitian matrices; for an
empty one both dimensions are `0`. -/
abbrev Model : Type :=
  Fin (Module.finrank ℝ (selfAdjoint (Matrix n n 𝕜)) - 1) → ℝ

/-- The real part of the determinant on the positive-definite cone, whose level `1` is
`PosDefDetOne`. -/
private def reDet (P : posDefOpens n 𝕜) : ℝ :=
  RCLike.re ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det

/-- A positive-definite matrix has determinant one exactly when the real part of its determinant
is one, its determinant being a positive real number. -/
private theorem det_eq_one_iff_reDet_eq_one (P : posDefOpens n 𝕜) :
    ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1 ↔ reDet P = 1 := by
  have him := (RCLike.pos_iff.1 ((mem_posDefOpens _).1 P.property).det_pos).2
  refine ⟨fun h ↦ by simp [reDet, h], fun h ↦ RCLike.ext ?_ ?_⟩
  · simpa [reDet] using h
  · simpa using him

private theorem contMDiff_reDet :
    ContMDiff 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, ℝ) ω (reDet (n := n) (𝕜 := 𝕜)) := by
  have hdet : ContDiff ℝ ω (fun A : Matrix n n 𝕜 ↦ A.det) :=
    ContDiff.matrix_det fun i j ↦ (entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap.contDiff
  exact (RCLike.reCLM.contDiff.comp hdet).contMDiff.comp contMDiff_coe_posDefOpens

/-- For a nonempty index type, `1` is a regular value of the real part of the determinant on the
positive-definite cone: along the ray `t ↦ eᵗ P` the determinant is `e^(t · card n) det P`. -/
private theorem isRegularValue_reDet [Nonempty n] :
    TauCeti.IsRegularValue 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, ℝ)
      (reDet (n := n) (𝕜 := 𝕜)) 1 := by
  rw [TauCeti.isRegularValue_iff]
  intro P hP
  have hP1 : ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1 :=
    (det_eq_one_iff_reDet_eq_one P).2 hP
  -- The ray through `P` in the cone.
  let γ : ℝ → posDefOpens n 𝕜 := fun t ↦
    ⟨Real.exp t • (P : selfAdjoint (Matrix n n 𝕜)), by
      rw [mem_posDefOpens, selfAdjoint.val_smul]
      exact ((mem_posDefOpens _).1 P.property).smul (Real.exp_pos t)⟩
  have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ω γ :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (posDefOpens n 𝕜) γ).1
      (Real.contDiff_exp.smul contDiff_const).contMDiff
  have hγ0 : γ 0 = P := Subtype.ext (by simp [γ])
  have hcomp : reDet ∘ γ = fun t ↦ Real.exp t ^ Fintype.card n := by
    funext t
    simp only [Function.comp_apply, reDet, γ, selfAdjoint.val_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, hP1, mul_one]
    rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hderiv : HasDerivAt (fun t ↦ Real.exp t ^ Fintype.card n) (Fintype.card n : ℝ) 0 := by
    simpa using (Real.hasDerivAt_exp 0).fun_pow (Fintype.card n)
  -- The chain rule along the ray computes the derivative of `reDet` in the direction `γ' 0`.
  have hchain := mfderiv_comp (0 : ℝ) ((contMDiff_reDet (n := n) (𝕜 := 𝕜)).mdifferentiableAt
    (by simp)) (hγ.mdifferentiableAt (by simp))
  -- The unit tangent vector at `0` of the parameter line.
  let v : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) := (1 : ℝ)
  have hv : mfderiv 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, ℝ) reDet (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) γ 0 v) = (Fintype.card n : ℝ) := by
    have h := DFunLike.congr_fun hchain v
    rw [ContinuousLinearMap.comp_apply, hcomp, mfderiv_eq_fderiv,
      hderiv.hasFDerivAt.fderiv] at h
    rw [← h]
    -- The identifications of the tangent spaces of `ℝ` with `ℝ` are the identity.
    exact one_smul ℝ (Fintype.card n : ℝ)
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [TauCeti.isRegularPoint_iff, ← hγ0]
  intro (y : ℝ)
  refine ⟨(y / Fintype.card n) • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) γ 0 v, ?_⟩
  rw [map_smul, hv]
  exact div_mul_cancel₀ y hcard

/-- The properties of the chosen atlas on `PosDefDetOne`: it is an analytic manifold structure for
which the inclusion into the cone is an analytic embedding. -/
private abbrev IsEmbeddedAtlas (c : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜)) : Prop :=
  letI := c
  IsManifold 𝓘(ℝ, Model n 𝕜) ω (PosDefDetOne n 𝕜) ∧
    IsSmoothEmbedding 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ω
      (Subtype.val : PosDefDetOne n 𝕜 → posDefOpens n 𝕜)

/-- For an empty index type, `PosDefDetOne` is a point, with the discrete manifold structure. -/
private theorem exists_charts_of_isEmpty [IsEmpty n] :
    ∃ c : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜), IsEmbeddedAtlas c := by
  have : Subsingleton (PosDefDetOne n 𝕜) :=
    ⟨fun P Q ↦ Subtype.ext (Subtype.ext (Subtype.ext (Subsingleton.elim _ _)))⟩
  have : IsEmpty (Fin (Module.finrank ℝ (selfAdjoint (Matrix n n 𝕜)) - 1)) := by
    have : Subsingleton (selfAdjoint (Matrix n n 𝕜)) :=
      ⟨fun X Y ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton, Nat.zero_sub]
    infer_instance
  let : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜) := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Model n 𝕜) ω (PosDefDetOne n 𝕜) := IsManifold.of_discreteTopology ω
  exact ⟨inferInstance, inferInstance,
    contMDiff_of_subsingleton.isImmersion_of_injective_mfderiv (by simp)
      (fun x u v _ ↦
        (tangentSpaceCastModel 𝓘(ℝ, Model n 𝕜) x).injective (Subsingleton.elim _ _)),
    .subtypeVal⟩

/-- For a nonempty index type, `PosDefDetOne` carries the atlas of the regular level `1` of the
real part of the determinant, for which its inclusion into the cone is an analytic embedding. -/
private theorem exists_charts_of_nonempty [Nonempty n] :
    ∃ c : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜), IsEmbeddedAtlas c := by
  -- Mathlib gives the finite dimension through the submodule of self-adjoint elements.
  have : FiniteDimensional ℝ (selfAdjoint (Matrix n n 𝕜)) :=
    FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))
  have hfm (P : posDefOpens n 𝕜) (_ : reDet P = 1) :
      ContMDiffAt 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) 𝓘(ℝ, ℝ) ω reDet P :=
    contMDiff_reDet.contMDiffAt
  have hreg := isRegularValue_reDet (n := n) (𝕜 := 𝕜)
  have hdim : Module.finrank ℝ (selfAdjoint (Matrix n n 𝕜)) - Module.finrank ℝ ℝ =
      Module.finrank ℝ (selfAdjoint (Matrix n n 𝕜)) - 1 := by
    rw [Module.finrank_self]
  let cL := TauCeti.regularLevelChartedSpace (fun P hP ↦ (hfm P hP).of_le (by simp)) hreg hdim
  have hL : IsManifold 𝓘(ℝ, Model n 𝕜) ω {P : posDefOpens n 𝕜 // reDet P = 1} :=
    TauCeti.isManifold_regularLevel (by simp) hfm hreg hdim
  have hLemb : IsSmoothEmbedding 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ω
      (Subtype.val : {P : posDefOpens n 𝕜 // reDet P = 1} → posDefOpens n 𝕜) :=
    TauCeti.isSmoothEmbedding_coe_regularLevel (by simp) hfm hreg hdim
  -- Transport the atlas of the level `reDet = 1` along the identity of points.
  let e : PosDefDetOne n 𝕜 ≃ₜ {P : posDefOpens n 𝕜 // reDet P = 1} :=
    (Homeomorph.refl _).subtype det_eq_one_iff_reDet_eq_one
  let c := e.pullbackChartedSpace (cM := cL)
  let := c
  have hm : IsManifold 𝓘(ℝ, Model n 𝕜) ω (PosDefDetOne n 𝕜) :=
    e.pullback_isManifold (cM := cL) (manifoldM := hL) 𝓘(ℝ, Model n 𝕜) ω
  let d := e.pullbackDiffeomorph (cM := cL) 𝓘(ℝ, Model n 𝕜) ω
  have hd : (Subtype.val : {P : posDefOpens n 𝕜 // reDet P = 1} → posDefOpens n 𝕜) ∘ d =
      Subtype.val := by
    funext P
    rw [Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph]
    -- `e` is the identity on underlying points.
    rfl
  refine ⟨c, hm, ?_⟩
  rw [← hd]
  exact TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph d.isLocalDiffeomorph
    d.toHomeomorph.isEmbedding hLemb

/-- The regular-level manifold structure on `PosDefDetOne`, with the analytic embedding into the
cone; for an empty index type, the discrete structure on a point. -/
private theorem exists_charts :
    ∃ c : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜), IsEmbeddedAtlas c := by
  cases isEmpty_or_nonempty n
  · exact exists_charts_of_isEmpty
  · exact exists_charts_of_nonempty

/-- The analytic atlas on the positive-definite matrices of determinant one, chosen
nonconstructively: for a nonempty index type, among the atlases of a regular level; for an empty
one, the discrete atlas on a point. Its public properties are `Matrix.PosDefDetOne.instIsManifold`
and `Matrix.PosDefDetOne.isSmoothEmbedding_subtypeVal`; individual charts are not specified. -/
@[instance_reducible]
instance instChartedSpace : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜) :=
  -- The private witness cannot be unfolded in exported data. Proof irrelevance identifies this
  -- witness with the one used by `choose_spec` below. The private predicate `IsEmbeddedAtlas`
  -- cannot appear in this exported type either, so the abbreviation is unfolded by hand.
  Classical.choose (show ∃ c : ChartedSpace (Model n 𝕜) (PosDefDetOne n 𝕜),
    letI := c
    IsManifold 𝓘(ℝ, Model n 𝕜) ω (PosDefDetOne n 𝕜) ∧
      IsSmoothEmbedding 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ω
        (Subtype.val : PosDefDetOne n 𝕜 → posDefOpens n 𝕜) from by exact exists_charts)

/-- The positive-definite matrices of determinant one form a real analytic manifold. -/
instance instIsManifold : IsManifold 𝓘(ℝ, Model n 𝕜) ω (PosDefDetOne n 𝕜) :=
  (Classical.choose_spec exists_charts).1

/-- The inclusion of the positive-definite matrices of determinant one into the positive-definite
cone is an analytic embedding. -/
theorem isSmoothEmbedding_subtypeVal :
    IsSmoothEmbedding 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) ω
      (Subtype.val : PosDefDetOne n 𝕜 → posDefOpens n 𝕜) :=
  (Classical.choose_spec exists_charts).2

/-- The inclusion into the positive-definite cone has every regularity. -/
theorem contMDiff_subtypeVal {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) k
      (Subtype.val : PosDefDetOne n 𝕜 → posDefOpens n 𝕜) :=
  (isSmoothEmbedding_subtypeVal (n := n) (𝕜 := 𝕜)).contMDiff.of_le le_top

/-- The inclusion into the matrices has every regularity. -/
theorem contMDiff_coe {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun P : PosDefDetOne n 𝕜 ↦ ((P.val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜)) :=
  contMDiff_coe_posDefOpens.comp contMDiff_subtypeVal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the positive-definite matrices of determinant one is `C^k` exactly when it is
`C^k` as a map into the positive-definite cone. -/
theorem contMDiff_subtypeVal_comp_iff {k : ℕ∞ω} {f : M → PosDefDetOne n 𝕜} :
    ContMDiff I 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)) k (Subtype.val ∘ f) ↔
      ContMDiff I 𝓘(ℝ, Model n 𝕜) k f := by
  have h := isSmoothEmbedding_subtypeVal (n := n) (𝕜 := 𝕜)
  exact (IsSmoothEmbedding.contMDiff_iff_comp ⟨h.isImmersion.of_le le_top, h.isEmbedding⟩).symm

end PosDefDetOne

/-! ### Exponential coordinates -/

variable (n 𝕜) in
/-- **Exponential coordinates on the positive-definite matrices of determinant one**: the matrix
exponential is a global real diffeomorphism from the trace-free Hermitian matrices (symmetric
matrices over `ℝ`) onto the positive-definite matrices of determinant one, with inverse the matrix
logarithm. It is the restriction of `Matrix.hermitianExpDiffeomorph`; the regularity order `k` can
be arbitrary, including analytic. -/
def traceZeroExpDiffeomorph (k : ℕ∞ω) :
    traceZeroSelfAdjoint n 𝕜 ≃ₘ^k⟮𝓘(ℝ, traceZeroSelfAdjoint n 𝕜),
      𝓘(ℝ, PosDefDetOne.Model n 𝕜)⟯ PosDefDetOne n 𝕜 where
  toEquiv := (hermitianExpDiffeomorph n 𝕜 k).toEquiv.subtypeEquiv fun X ↦ by
    rw [mem_traceZeroSelfAdjoint, Diffeomorph.coe_toEquiv, coe_hermitianExpDiffeomorph_apply,
      (isHermitian_iff_isSelfAdjoint.2 X.property).det_exp_eq_one_iff]
  contMDiff_toFun := by
    -- The spaces are named so that the subspace's normed structure is found by instance search:
    -- the definition of `traceZeroSelfAdjoint` is not exposed to unification here.
    have hι : ContDiff ℝ k (traceZeroSelfAdjoint n 𝕜).subtypeL :=
      ContinuousLinearMap.contDiff (E := traceZeroSelfAdjoint n 𝕜)
        (F := selfAdjoint (Matrix n n 𝕜)) _
    exact PosDefDetOne.contMDiff_subtypeVal_comp_iff.1
      ((hermitianExpDiffeomorph n 𝕜 k).contMDiff.comp hι.contMDiff)
  contMDiff_invFun := by
    -- Mathlib gives the finite dimension through the submodule of self-adjoint elements.
    have : FiniteDimensional ℝ (selfAdjoint (Matrix n n 𝕜)) :=
      FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))
    -- A continuous linear projection onto the trace-free subspace reads the inverse, a map into
    -- the Hermitian matrices, as a map into that subspace.
    obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional (traceZeroSelfAdjoint n 𝕜)
    refine (π.contDiff.contMDiff.comp ((hermitianExpDiffeomorph n 𝕜 k).symm.contMDiff.comp
      PosDefDetOne.contMDiff_subtypeVal)).congr fun P ↦ ?_
    exact (hπ ⟨_, _⟩).symm

/-- The underlying matrix of the exponential coordinates is the matrix exponential. -/
@[simp]
theorem coe_traceZeroExpDiffeomorph_apply (k : ℕ∞ω) (X : traceZeroSelfAdjoint n 𝕜) :
    (((traceZeroExpDiffeomorph n 𝕜 k X).val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      exp ((X : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
  coe_hermitianExpDiffeomorph_apply k _

/-- The inverse exponential coordinates are the continuous-functional-calculus matrix
logarithm. -/
@[simp]
theorem coe_traceZeroExpDiffeomorph_symm_apply (k : ℕ∞ω) (P : PosDefDetOne n 𝕜) :
    (((traceZeroExpDiffeomorph n 𝕜 k).symm P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      cfc Real.log ((P.val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
  coe_hermitianExpDiffeomorph_symm_apply k _

end Matrix
