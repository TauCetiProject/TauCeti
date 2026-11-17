/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Group.HomCompletion
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Variational.Fredholm
public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace
public import TauCeti.Analysis.Normed.Operator.NormedAddGroupHom
import TauCeti.Analysis.Normed.Operator.Coercive

/-!
# The spectrum of a coercive variational problem

Let `B` be a bounded coercive bilinear form on a real Hilbert space `V` and let `J : V →L[ℝ] H`
be a continuous linear map into a real inner-product space.  The **variational eigenvalue
problem** attached to this pair asks for `κ : ℝ` and `u ≠ 0` with

`B u v = κ ⟪J u, J v⟫` for every `v : V`.

This file studies that problem through the canonical `H`-forcing **solution operator** on `H`
constructed in `TauCeti.Analysis.InnerProductSpace.LaxMilgram`.  For an invertible bounded
sesquilinear form `B` over `[RCLike 𝕜]` (`hB : IsUnit (continuousLinearMapOfBilin B)`),
`InnerProductSpace.formSolutionMap B hB J` sends `h : H` to the unique `u : V` with
`B u v = ⟪h, J v⟫` for all `v`, and `InnerProductSpace.formSolutionOperator B hB J` composes it
with `J` to give `S : H →L[𝕜] H`. At `𝕜 = ℝ`, a coercive form `hB : IsCoercive B` supplies the
invertibility witness `hB.isUnit_continuousLinearMapOfBilin`. These constructions, their
completion compatibility, their kernel and eigenvector correspondence, and their compactness,
symmetry and positivity properties do not require `H` to be complete. Spectral existence and
triviality of the orthogonal complement of the eigenspaces also hold without completeness; the
Hilbert-basis theorem assumes it.

`S` is the right object to spectralize.  It is compact as soon as `J` is, it is symmetric as
soon as `B` is, and its nonzero eigenvalues are exactly the reciprocals of the variational
eigenvalues: `S` has eigenvalue `κ⁻¹` at `κ • J u` precisely when `u` solves the variational
eigenvalue problem for `κ`. Mathlib's spectral theorem for compact symmetric operators applies
on the completion of `H`. The factorization through `V` brings eigenvectors at nonzero eigenvalues
back into `H`, yielding spectral existence and trivial orthogonal complement of the eigenspaces.
Eigenspaces at *nonzero* eigenvalues are finite dimensional. The eigenspace at `0` is the kernel
of `S`, which is `(range J)ᗮ` (`InnerProductSpace.ker_formSolutionOperator`) and so can be
infinite dimensional; it vanishes when `J` has dense range
(`InnerProductSpace.eigenspace_formSolutionOperator_zero_eq_bot`).

Coercivity forces every variational eigenvalue to be positive, and quantitatively to be at
least the coercivity constant whenever `J` is a contraction; this is the abstract form of the
statement that the first eigenvalue of a Dirichlet problem is bounded below by the constant in
the corresponding Poincaré inequality.  These estimates only need a real normed source and a
seminormed inner-product target, without completeness of either space.

The kernel of `S` is the orthogonal complement of the range of `J`
(`InnerProductSpace.ker_formSolutionOperator`), so dense range of `J` makes `S` injective
(`InnerProductSpace.formSolutionOperator_injective`). This is the hypothesis under which every
eigenvector of `S` comes from a variational eigenfunction.

## Main declarations

* `InnerProductSpace.formSolutionMap_toComplL_apply`,
  `InnerProductSpace.formSolutionOperator_toComplL_apply`, and
  `InnerProductSpace.norm_formSolutionOperator_toComplL`: passing the target `H` to its completion
  `Completion H` commutes with `formSolutionMap` and `formSolutionOperator` and preserves the
  operator norm.
* `InnerProductSpace.eigenspace_formSolutionOperator_zero_eq_bot`: when `J` has dense range and
  `B` has no nonzero isotropic vectors, `0` is not an eigenvalue of `formSolutionOperator`.
* `IsCoercive.hasEigenvalue_formSolutionOperator_iff`: the reciprocal correspondence between
  the nonzero eigenvalues of `S` and the variational eigenvalues.
* `IsCoercive.exists_ne_zero_forall_apply_eq_smul_inner`: existence of a variational
  eigenvalue.
* `IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`: the reciprocal of the norm
  of the solution operator is a variational eigenvalue.
* `IsCoercive.pos_of_forall_apply_eq_smul_inner` and
  `IsCoercive.le_of_forall_apply_eq_smul_inner`: positivity of a variational eigenvalue, and
  the lower bound by the coercivity constant.
* `IsCoercive.orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot` and
  `IsCoercive.orthogonalComplement_iSup_eigenspaces_ne_zero_formSolutionOperator_eq_bot`: the
  eigenspaces of `S` have trivial orthogonal complement, and only the nonzero eigenvalues are
  needed when `S` is injective.
* `IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner`: the variational eigenfunctions
  form an orthonormal basis of `H`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5 (eigenvalues of symmetric elliptic
operators); H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Section 6.4.
-/

public section

noncomputable section

open Module.End UniformSpace
open scoped InnerProductSpace

/-! ### Completion compatibility and zero eigenspace -/

namespace InnerProductSpace

section Completion

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Passing the target to its completion preserves the solution map on the original space. -/
@[simp]
theorem formSolutionMap_toComplL_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (J : V →L[𝕜] H) (h : H) :
    formSolutionMap B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)
        (h : Completion H) =
      formSolutionMap B hB J h := by
  apply (eq_formSolutionMap B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J) ?_).symm
  intro v
  simp only [apply_formSolutionMap, ContinuousLinearMap.comp_apply, Completion.coe_toComplL,
    Completion.inner_coe]

/-- The solution operator on the completion agrees with the original operator on embedded
vectors. -/
@[simp]
theorem formSolutionOperator_toComplL_apply (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (J : V →L[𝕜] H) (h : H) :
    formSolutionOperator B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)
        (h : Completion H) =
      (formSolutionOperator B hB J h : Completion H) := by
  simp only [formSolutionOperator_apply, formSolutionMap_toComplL_apply,
    ContinuousLinearMap.comp_apply, Completion.coe_toComplL]

/-- Passing the target to its completion preserves the norm of the solution operator. -/
@[simp]
theorem norm_formSolutionOperator_toComplL (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (J : V →L[𝕜] H) :
    ‖formSolutionOperator B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)‖ =
      ‖formSolutionOperator B hB J‖ := by
  let S := formSolutionOperator B hB J
  -- Use the bounded-additive completion norm theorem through the underlying function.
  let Sg := S.toAddMonoidHom.mkNormedAddGroupHom ‖S‖ S.le_opNorm
  have hSg : ⇑Sg = S := by
    simpa only [LinearMap.toAddMonoidHom_coe (S : H →ₗ[𝕜] H),
      ContinuousLinearMap.coe_coe S] using
      NormedAddGroupHom.coe_mkNormedAddGroupHom S.toAddMonoidHom ‖S‖ S.le_opNorm
  have hext :
      ⇑(formSolutionOperator B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)) =
        Sg.completion := by
    apply Completion.ext
      (formSolutionOperator B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)).continuous
      Sg.completion.continuous
    intro h
    simp only [formSolutionOperator_toComplL_apply, NormedAddGroupHom.completion_coe, hSg, S]
  calc
    ‖formSolutionOperator B hB ((Completion.toComplL : H →L[𝕜] Completion H).comp J)‖
        = ‖Sg.completion‖ :=
          ContinuousLinearMap.norm_eq_normedAddGroupHom _ _ (congrFun hext)
    _ = ‖Sg‖ := Sg.norm_completion
    _ = ‖formSolutionOperator B hB J‖ :=
          (S.norm_eq_normedAddGroupHom Sg fun h => (congrFun hSg h).symm).symm

end Completion

section ZeroEigenspace

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- With `J` of dense range and no nonzero isotropic vectors for `B`, `0` is not an eigenvalue of
the solution operator. -/
theorem eigenspace_formSolutionOperator_zero_eq_bot (B : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hB : IsUnit (continuousLinearMapOfBilin B)) (hdef : ∀ u, B u u = 0 → u = 0)
    {J : V →L[𝕜] H} (hJ : DenseRange J) :
    eigenspace (formSolutionOperator B hB J : H →ₗ[𝕜] H) 0 = ⊥ := by
  rw [eigenspace_zero, LinearMap.ker_eq_bot]
  exact formSolutionOperator_injective B hB hdef hJ

end ZeroEigenspace

end InnerProductSpace

namespace IsCoercive

section Perturbation

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The form perturbation operator on `V` is the solution map precomposed with `J`, where the
solution operator on `H` is the same pair of maps composed in the other order. -/
theorem formPerturbationOperator_eq_comp (hB : IsCoercive B) (J : V →L[ℝ] H) :
    hB.formPerturbationOperator J =
      (InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J).comp J := by
  ext u
  rw [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.eq_formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J fun v =>
    hB.apply_formPerturbationOperator J u v

end Perturbation

/-! ### Variational eigenvalues -/

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A variational eigenvalue is positive: coercivity bounds the energy of an eigenfunction
below by a positive multiple of its squared norm. -/
theorem pos_of_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) : 0 < kappa := by
  have henergy := hB.apply_self_pos hu
  rw [heq u] at henergy
  exact pos_of_mul_pos_left henergy real_inner_self_nonneg

/-- **A variational eigenvalue is at least the coercivity constant**, when `J` is a
contraction.  For the Dirichlet problem this is the statement that the first eigenvalue is
bounded below by the constant appearing in the Poincaré inequality. -/
theorem le_of_forall_apply_eq_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H} {C : ℝ}
    (hlower : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w) (hJ : ∀ w : V, ‖J w‖ ≤ ‖w‖) {kappa : ℝ} {u : V}
    (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) : C ≤ kappa := by
  have hkappa : 0 < kappa := hB.pos_of_forall_apply_eq_smul_inner J hu heq
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hself : B u u = kappa * ‖J u‖ ^ 2 := by
    rw [heq u, real_inner_self_eq_norm_sq]
  have hJu : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := hJ u
    nlinarith [norm_nonneg (J u)]
  have hstep : kappa * ‖J u‖ ^ 2 ≤ kappa * ‖u‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hJu hkappa.le
  have hsq : 0 < ‖u‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (by linarith [hlower u]) hsq

/-- **A variational eigenfunction has nonzero image in `H`.**  If `J u` vanished, the
eigenvalue equation would make the energy of `u` vanish too, which coercivity forbids for
`u ≠ 0`. -/
theorem apply_ne_zero_of_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H)
    {kappa : ℝ} {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) :
    J u ≠ 0 := by
  intro hzero
  obtain ⟨C, hC, hle⟩ := id hB
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hself : B u u = 0 := by rw [heq u, hzero, inner_zero_left, mul_zero]
  have h2 : 0 < C * ‖u‖ * ‖u‖ := mul_pos (mul_pos hC hpos) hpos
  linarith [hle u]

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A variational eigenfunction produces an eigenvector of the solution operator with
eigenvalue `κ⁻¹`; coercivity ensures that `κ` is positive. -/
theorem hasEigenvector_formSolutionOperator (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) :
    HasEigenvector
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      kappa⁻¹ (kappa • J u) := by
  have hkappa := (hB.pos_of_forall_apply_eq_smul_inner J hu heq).ne'
  have hsol :
      u = InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J
        (kappa • J u) :=
    InnerProductSpace.eq_formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J fun v => by
      rw [heq v, real_inner_smul_left]
  refine ⟨mem_eigenspace_iff.mpr ?_,
    smul_ne_zero hkappa (hB.apply_ne_zero_of_forall_apply_eq_smul_inner J hu heq)⟩
  rw [ContinuousLinearMap.coe_coe, InnerProductSpace.formSolutionOperator_apply, ← hsol, smul_smul,
    inv_mul_cancel₀ hkappa, one_smul]

/-- An eigenvector of the solution operator with nonzero eigenvalue produces a variational
eigenfunction for the reciprocal eigenvalue. -/
theorem exists_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H) {mu : ℝ}
    (hmu : mu ≠ 0)
    (h : HasEigenvalue
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      mu) :
    ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = mu⁻¹ * ⟪J u, J v⟫_ℝ := by
  obtain ⟨w, hw, hwne⟩ := h.exists_hasEigenvector
  have hSw :
      J (InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J w) =
        mu • w := by
    have := mem_eigenspace_iff.mp hw
    rwa [ContinuousLinearMap.coe_coe, InnerProductSpace.formSolutionOperator_apply] at this
  refine ⟨InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J w,
    ?_, fun v => ?_⟩
  · intro hzero
    rw [hzero, map_zero] at hSw
    rcases smul_eq_zero.mp hSw.symm with hz | hz
    · exact hmu hz
    · exact hwne hz
  · rw [InnerProductSpace.apply_formSolutionMap, hSw, real_inner_smul_left, ← mul_assoc,
      inv_mul_cancel₀ hmu, one_mul]

/-- **The variational eigenvalues are the reciprocals of the nonzero eigenvalues of the
solution operator.** -/
theorem hasEigenvalue_formSolutionOperator_iff (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    (hkappa : kappa ≠ 0) :
    HasEigenvalue
        (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
          H →ₗ[ℝ] H)
        kappa⁻¹ ↔
      ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ :=
      hB.exists_forall_apply_eq_smul_inner J (inv_ne_zero hkappa) h
    exact ⟨u, hu, by simpa only [inv_inv] using heq⟩
  · rintro ⟨u, hu, heq⟩
    exact hasEigenvalue_of_hasEigenvector
      (hB.hasEigenvector_formSolutionOperator J hu heq)

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **The reciprocal of the norm of the solution operator is a variational eigenvalue.**
Compactness of `J` is what makes `‖S‖` itself an eigenvalue of `S`, and positivity of `S` is what
excludes `-‖S‖`. -/
private theorem exists_ne_zero_forall_apply_eq_inv_norm_smul_inner_of_completeSpace
    [CompleteSpace H] (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u)
    (hJne : J ≠ 0) :
    ∃ u : V, u ≠ 0 ∧
      ∀ v : V, B u v =
        ‖InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J‖⁻¹ *
          ⟪J u, J v⟫_ℝ := by
  obtain ⟨w, hw⟩ : ∃ w : V, J w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hJne
  have _ : Nontrivial H := nontrivial_of_ne (J w) 0 hw
  set S := InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J with hS
  have hSne : S ≠ 0 := by
    rw [hS]
    exact InnerProductSpace.formSolutionOperator_ne_zero B hB.isUnit_continuousLinearMapOfBilin
      (fun _ => hB.eq_zero_of_apply_self_eq_zero) hJne
  have hnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hSne
  have hcompact : IsCompactOperator S :=
    InnerProductSpace.isCompactOperator_formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin
      hJ
  have hsym : LinearMap.IsSymmetric (S : H →ₗ[ℝ] H) :=
    InnerProductSpace.isSymmetric_formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J
      fun u v => (hsymm u v).trans (star_trivial _).symm
  have hnorm_or_neg : ‖S‖ ∈ spectrum ℝ S ∨ -‖S‖ ∈ spectrum ℝ S := by
    simp_rw [spectrum, Set.mem_compl_iff]
    by_contra! h
    obtain ⟨d, hd, hle⟩ := S.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
    have hsup := ciSup_le hle
    have heq := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hsym
    linarith
  have hnorm_mem : ‖S‖ ∈ spectrum ℝ S := hnorm_or_neg.resolve_right fun hneg => by
    have hneg_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) (-‖S‖) :=
      (hcompact.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hnorm_pos.ne')).mpr hneg
    have hnonneg : 0 ≤ -‖S‖ := eigenvalue_nonneg_of_nonneg hneg_eigen fun f => by
      simpa only [hS, ContinuousLinearMap.coe_coe, RCLike.re_to_real] using
        InnerProductSpace.re_inner_formSolutionOperator_self_nonneg B
          hB.isUnit_continuousLinearMapOfBilin
          (fun u => by simpa only [RCLike.re_to_real] using hB.apply_self_nonneg u) J f
    linarith
  have hnorm_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) ‖S‖ :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hnorm_pos.ne').mpr hnorm_mem
  refine (hB.hasEigenvalue_formSolutionOperator_iff J (inv_ne_zero hnorm_pos.ne')).mp ?_
  simpa only [hS, inv_inv] using hnorm_eigen

/-- **The reciprocal of the norm of the solution operator is a variational eigenvalue.**
Compactness of `J` ensures attainment, even when `H` is incomplete. -/
theorem exists_ne_zero_forall_apply_eq_inv_norm_smul_inner (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J)
    (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    ∃ u : V, u ≠ 0 ∧
      ∀ v : V, B u v =
        ‖InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J‖⁻¹ *
          ⟪J u, J v⟫_ℝ := by
  have hJc : (Completion.toComplL : H →L[ℝ] Completion H).comp J ≠ 0 := by
    intro hz
    apply hJne
    ext v
    apply Completion.coe_injective
    simpa only [ContinuousLinearMap.comp_apply, Completion.coe_toComplL, zero_apply,
      Completion.coe_zero] using DFunLike.congr_fun hz v
  simpa only [InnerProductSpace.norm_formSolutionOperator_toComplL, ContinuousLinearMap.comp_apply,
    Completion.coe_toComplL, Completion.inner_coe] using
    hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner_of_completeSpace
      (hJ.clm_comp (Completion.toComplL : H →L[ℝ] Completion H)) hsymm hJc

/-- **Existence of a variational eigenvalue.** For a symmetric form and a nonzero compact `J`,
the variational eigenvalue problem has a nonzero eigenvalue with an eigenfunction. -/
theorem exists_ne_zero_forall_apply_eq_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    ∃ kappa : ℝ, kappa ≠ 0 ∧ ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ := by
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner hJ hsymm hJne
  exact ⟨_, inv_ne_zero (norm_ne_zero_iff.mpr
    (InnerProductSpace.formSolutionOperator_ne_zero B hB.isUnit_continuousLinearMapOfBilin
      (fun _ => hB.eq_zero_of_apply_self_eq_zero) hJne)),
    u, hu, heq⟩

/-! ### The spectral theorem for the solution operator -/

/-- Eigenspaces of the solution operator at nonzero eigenvalues are finite dimensional. -/
theorem finiteDimensional_eigenspace_formSolutionOperator (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) {mu : ℝ} (hmu : mu ≠ 0) :
    FiniteDimensional ℝ
      (eigenspace
        (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
          H →ₗ[ℝ] H)
        mu) :=
  IsCompactOperator.finiteDimensional_eigenspace
    (InnerProductSpace.isCompactOperator_formSolutionOperator B
      hB.isUnit_continuousLinearMapOfBilin hJ)
    hmu

/-- Every vector in an eigenspace of the completed solution operator at a nonzero eigenvalue
comes from the same eigenspace of the original operator. -/
theorem exists_mem_eigenspace_formSolutionOperator_of_mem_eigenspace_toComplL
    (hB : IsCoercive B) (J : V →L[ℝ] H) {mu : ℝ} {w : Completion H} (hmu : mu ≠ 0)
    (hw : w ∈ eigenspace
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin
        (Completion.toComplL.comp J) : Completion H →ₗ[ℝ] Completion H)
      mu) :
    ∃ y ∈ eigenspace
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      mu, (y : Completion H) = w := by
  let Jc : V →L[ℝ] Completion H := Completion.toComplL.comp J
  have heq :
      InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin Jc w =
        mu • w :=
    mem_eigenspace_iff.mp hw
  let y : H :=
    mu⁻¹ • J (InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin Jc w)
  have hy : (y : Completion H) = w := by
    have hfactor :
        (J (InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin Jc w) :
            Completion H) =
          InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin Jc w := by
      simp only [InnerProductSpace.formSolutionOperator_apply, Jc, ContinuousLinearMap.comp_apply,
        Completion.coe_toComplL]
    simp only [y, Completion.coe_smul, hfactor, heq, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  refine ⟨y, mem_eigenspace_iff.mpr ?_, hy⟩
  apply Completion.coe_injective
  simpa only [ContinuousLinearMap.coe_coe,
    ← InnerProductSpace.formSolutionOperator_toComplL_apply, hy, Completion.coe_smul] using heq

/-- **The spectral theorem for the solution operator**: its eigenspaces have trivial orthogonal
complement in `H`, even when `H` is incomplete. -/
theorem orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J)
    (hsymm : ∀ u v : V, B u v = B v u) :
    (⨆ mu : ℝ, eigenspace
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      mu)ᗮ = ⊥ := by
  let Jc : V →L[ℝ] Completion H := Completion.toComplL.comp J
  let Sc := InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin Jc
  have hsym := InnerProductSpace.isSymmetric_formSolutionOperator B
    hB.isUnit_continuousLinearMapOfBilin Jc fun u v => (hsymm u v).trans (star_trivial _).symm
  have htotal := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (InnerProductSpace.isCompactOperator_formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin
      (hJ.clm_comp (Completion.toComplL : H →L[ℝ] Completion H))) hsym
  refine le_antisymm (fun x hx => ?_) bot_le
  -- Test the image of `x` against the completed eigenspaces; it is automatically orthogonal
  -- to the kernel, and nonzero eigenvectors come from `H` through the factorization by `J`.
  have hScx : Sc (x : Completion H) = 0 := by
    apply (Submodule.mem_bot ℝ).mp
    rw [← htotal, ← Submodule.iInf_orthogonal]
    simp only [Submodule.mem_iInf, Submodule.mem_orthogonal']
    intro mu w hw
    have heq : Sc w = mu • w := mem_eigenspace_iff.mp hw
    have hinner : ⟪Sc (x : Completion H), w⟫_ℝ = ⟪(x : Completion H), Sc w⟫_ℝ := hsym _ _
    rw [hinner, heq, inner_smul_right]
    rcases eq_or_ne mu 0 with rfl | hmu
    · simp
    · obtain ⟨y, hy_eigen, hy⟩ :=
        hB.exists_mem_eigenspace_formSolutionOperator_of_mem_eigenspace_toComplL J hmu hw
      have hxy := (Submodule.mem_orthogonal' _ x).mp hx y (Submodule.mem_iSup_of_mem mu hy_eigen)
      rw [← hy, Completion.inner_coe, hxy, mul_zero]
  have hx_eigen : x ∈ eigenspace
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      0 := by
    apply mem_eigenspace_iff.mpr
    apply Completion.coe_injective
    simpa only [ContinuousLinearMap.coe_coe, Sc, Jc,
      InnerProductSpace.formSolutionOperator_toComplL_apply, Completion.coe_smul, zero_smul,
      Completion.coe_zero] using hScx
  exact (Submodule.mem_bot ℝ).mpr (inner_self_eq_zero.mp
    ((Submodule.mem_orthogonal' _ x).mp hx x (Submodule.mem_iSup_of_mem 0 hx_eigen)))

/-- **The nonzero eigenspaces of the solution operator have trivial orthogonal complement**
when `J` is compact, the form is symmetric, and the solution operator is injective. -/
theorem orthogonalComplement_iSup_eigenspaces_ne_zero_formSolutionOperator_eq_bot
    (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J)
    (hzero : eigenspace
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H)
      0 = ⊥)
    (hsymm : ∀ u v : V, B u v = B v u) :
    (⨆ mu : ℝ, ⨆ _ : mu ≠ 0,
      eigenspace
        (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
          H →ₗ[ℝ] H)
        mu)ᗮ = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← hB.orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot hJ hsymm]
  refine Submodule.orthogonal_le (iSup_le fun mu => ?_)
  rcases eq_or_ne mu 0 with rfl | hne
  · rw [hzero]
    exact bot_le
  · exact le_iSup₂ (f := fun mu (_ : mu ≠ 0) =>
      eigenspace
        (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
          H →ₗ[ℝ] H)
        mu) mu hne

/-- **The variational eigenfunctions form an orthonormal basis of `H`.**  For a symmetric form
and a compact `J` of dense range, `H` has an orthonormal basis `b` each of whose vectors is `J u`
for an eigenfunction `u` of the variational problem at a positive eigenvalue `κ`, and the
solution operator is diagonal in that basis: its value, equivalently the `J`-image of the
solution of `B u v = ⟪h, J v⟫`, is the eigenfunction expansion `∑ κ⁻¹ ⟪b i, h⟫ b i`.
This is the abstract form of the eigenfunction expansion of a symmetric elliptic operator; `H`
is not assumed separable, so the basis is indexed by a set of vectors of `H` as in
`exists_hilbertBasis`. -/
theorem exists_hilbertBasis_forall_apply_eq_smul_inner [CompleteSpace H] (hB : IsCoercive B)
    {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hJdense : DenseRange J) (hsymm : ∀ u v : V, B u v = B v u) :
    ∃ (s : Set H) (b : HilbertBasis s ℝ H) (kappa : s → ℝ) (u : s → V),
      ⇑b = ((↑) : s → H) ∧ (∀ x : s, 0 < kappa x) ∧ (∀ x : s, u x ≠ 0) ∧
      (∀ x : s, J (u x) = (x : H)) ∧
      (∀ (x : s) (v : V), B (u x) v = kappa x * ⟪J (u x), J v⟫_ℝ) ∧
      ∀ h : H, HasSum (fun x : s => (kappa x)⁻¹ • b.repr h x • b x)
        (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J h) := by
  have hker : LinearMap.ker
      (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J :
        H →ₗ[ℝ] H) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (InnerProductSpace.formSolutionOperator_injective B
      hB.isUnit_continuousLinearMapOfBilin (fun _ => hB.eq_zero_of_apply_self_eq_zero) hJdense)
  obtain ⟨s, b, nu, hb, hnu, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero
    (InnerProductSpace.isCompactOperator_formSolutionOperator B
      hB.isUnit_continuousLinearMapOfBilin hJ)
    (InnerProductSpace.isSymmetric_formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J
      fun u v => (hsymm u v).trans (star_trivial _).symm)
    hker
  have hdiag : ∀ x : s,
      InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin J (b x) =
        nu x • b x := by
    intro x
    rw [hb]
    simpa only [ContinuousLinearMap.coe_coe] using mem_eigenspace_iff.mp (hev x).1
  have hSx : ∀ x : s,
      J (InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H)) =
        nu x • (x : H) := by
    intro x
    simpa only [ContinuousLinearMap.coe_coe, InnerProductSpace.formSolutionOperator_apply] using
      mem_eigenspace_iff.mp (hev x).1
  have hJu : ∀ x : s,
      J ((nu x)⁻¹ •
        InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H)) =
        (x : H) := fun x => by
    rw [map_smul, hSx, smul_smul, inv_mul_cancel₀ (hnu x), one_smul]
  have heq : ∀ (x : s) (v : V),
      B ((nu x)⁻¹ •
        InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H)) v =
      (nu x)⁻¹ * ⟪J ((nu x)⁻¹ •
        InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H)),
        J v⟫_ℝ := fun x v => by
    rw [hJu, map_smul, smul_apply, smul_eq_mul, InnerProductSpace.apply_formSolutionMap]
  have hune : ∀ x : s,
      (nu x)⁻¹ •
        InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H) ≠
        0 := by
    intro x hzero
    have h0 := hJu x
    rw [hzero, map_zero] at h0
    exact (hev x).2 h0.symm
  refine ⟨s, b, fun x => (nu x)⁻¹,
    fun x => (nu x)⁻¹ •
      InnerProductSpace.formSolutionMap B hB.isUnit_continuousLinearMapOfBilin J (x : H),
    hb, fun x => hB.pos_of_forall_apply_eq_smul_inner J (hune x) (heq x), hune, hJu, heq,
    fun h => ?_⟩
  simpa only [inv_inv] using
    (InnerProductSpace.formSolutionOperator B hB.isUnit_continuousLinearMapOfBilin
      J).hasSum_smul_repr_of_apply_eq_smul b nu hdiag h

end IsCoercive
