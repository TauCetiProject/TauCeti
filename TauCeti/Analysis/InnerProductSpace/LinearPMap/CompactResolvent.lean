/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.OneAddSq

/-!
# Self-adjoint operators with compact resolvent

Every nonreal scalar lies in the resolvent set of a self-adjoint partial linear map `D` on a
Hilbert space. Hence `D` has compact resolvent exactly when `R(z) = (z - D)⁻¹` is compact at one,
equivalently every, nonreal `z`; in particular exactly when `(D - i)⁻¹ = R(-i, -D)` is compact,
which is the usual normalization for the Dirac operator of a spectral triple.

On a complex Hilbert space the bounded inverse `K = (1 + D²)⁻¹` of `LinearPMap.invOneAddSq` is
`R(i)* R(i)`, a positive injective operator, and it is compact when `D` has compact resolvent.
Mathlib's spectral theorem for compact self-adjoint operators then applies to `K`: its eigenspaces
for nonzero eigenvalues are finite-dimensional
(`LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq`, from
`ContinuousLinearMap.finite_dimensional_eigenspace`) and, since `ker K = 0`, they span a dense
subspace of the Hilbert space. Each of them lies in every iterated domain `D(Dⁿ)` and is
invariant under `D`
(`LinearPMap.eigenspace_invOneAddSq_le_domainPow`, `LinearPMap.apply_mem_eigenspace_invOneAddSq`).
These are the ingredients for an orthonormal eigenbasis of `D`, obtained by diagonalizing `D` on
each of these finite-dimensional invariant subspaces in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis`.

## Main results

* `IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent`: a self-adjoint operator
  has compact resolvent exactly when its resolvent at a given nonreal point is compact.
* `IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent_neg_neg`: the same for the
  inverse `(D - z)⁻¹`.
* `LinearPMap.mem_resolventSet_unitaryConj_iff`, `LinearPMap.resolvent_unitaryConj`,
  `LinearPMap.hasCompactResolvent_unitaryConj_iff`: unitary conjugation preserves the resolvent
  set, conjugates the resolvent, and preserves compact resolvent.
* `LinearPMap.finiteDimensional_of_hasCompactResolvent_toPMap_top` and
  `IsSelfAdjoint.hasCompactResolvent_toPMap_top_iff`: a bounded operator has compact resolvent only
  in finite dimensions, and for a bounded self-adjoint operator on a complex Hilbert space the two
  conditions are equivalent.
* `IsSelfAdjoint.invOneAddSq_eq_adjoint_comp`: `(1 + D²)⁻¹ = R(i)* R(i)`.
* `IsSelfAdjoint.isPositive_invOneAddSq`: `(1 + D²)⁻¹` is a positive operator.
* `LinearPMap.HasCompactResolvent.hasOrthogonalProjection_ker`: the finite-dimensional kernel of
  an operator with compact resolvent admits an orthogonal projection.
* `LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq`: for compact
  resolvent, the eigenspaces of `(1 + D²)⁻¹` for nonzero eigenvalues are finite-dimensional.
* `IsSelfAdjoint.orthogonalComplement_iSup_eigenspaces_invOneAddSq_eq_bot`: for compact
  resolvent, the eigenspaces of `(1 + D²)⁻¹` for nonzero eigenvalues span a dense subspace.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.
-/

public section

noncomputable section

namespace TauCeti

open _root_.LinearPMap Module End

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {A : E →ₗ.[𝕜] E} {z : 𝕜}

/-- A self-adjoint operator has compact resolvent exactly when its resolvent `(z - A)⁻¹` at a
given nonreal point `z` is compact. -/
theorem _root_.IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent
    (hA : IsSelfAdjoint A) (hz : RCLike.im z ≠ 0) :
    A.HasCompactResolvent ↔ IsCompactOperator (A.resolvent z) :=
  LinearPMap.hasCompactResolvent_iff_isCompactOperator_resolvent
    (hA.mem_resolventSet_of_im_ne_zero hz)

/-- A self-adjoint operator has compact resolvent exactly when the inverse
`(A - z)⁻¹ = R(-z, -A)` at a given nonreal point `z` is compact. For `z = i` this is the
condition that `(A - i)⁻¹` be compact. -/
theorem _root_.IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent_neg_neg
    (hA : IsSelfAdjoint A) (hz : RCLike.im z ≠ 0) :
    A.HasCompactResolvent ↔ IsCompactOperator ((-A).resolvent (-z)) := by
  rw [← hasCompactResolvent_neg_iff]
  exact LinearPMap.hasCompactResolvent_iff_isCompactOperator_resolvent
    (mem_resolventSet_neg_iff.mpr (hA.mem_resolventSet_of_im_ne_zero hz))

/-- An operator with compact resolvent has a finite-dimensional, hence complete, kernel, which
therefore admits an orthogonal projection. -/
theorem _root_.LinearPMap.HasCompactResolvent.hasOrthogonalProjection_ker {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {A : F →ₗ.[𝕜] F} (h : A.HasCompactResolvent) :
    A.ker.HasOrthogonalProjection := by
  have := h.finiteDimensional_ker
  infer_instance

end RCLike

section UnitaryConj

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {z : 𝕜} {R : E →L[𝕜] E}

/-- Unitary conjugation transports a resolvent at `z` to the conjugated operator
`U ∘ R ∘ U⁻¹`. -/
theorem _root_.LinearPMap.IsResolventAt.unitaryConj (h : IsResolventAt A z R) (U : E ≃ₗᵢ[𝕜] F) :
    IsResolventAt (unitaryConj U A) z
      (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L R ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap) where
  mem_domain y := by
    rw [mem_unitaryConj_domain_iff]
    simpa using h.mem_domain (U.symm y)
  smul_sub_apply y := by
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, unitaryConj_apply]
    have hEq : (⟨U.symm (U (R (U.symm y))), by simpa using h.mem_domain (U.symm y)⟩ : A.domain) =
        ⟨R (U.symm y), h.mem_domain (U.symm y)⟩ := Subtype.ext (U.symm_apply_apply _)
    rw [hEq, ← _root_.map_smul, ← _root_.map_sub, h.smul_sub_apply (U.symm y), U.apply_symm_apply]
  apply_smul_sub x := by
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, unitaryConj_apply]
    rw [_root_.map_sub U.symm, _root_.map_smul U.symm, U.symm_apply_apply,
      h.apply_smul_sub ⟨U.symm (x : F), (mem_unitaryConj_domain_iff (U := U) (A := A)).1 x.2⟩,
      U.apply_symm_apply]

/-- Unitary conjugation preserves the resolvent set. -/
@[simp]
theorem _root_.LinearPMap.mem_resolventSet_unitaryConj_iff (U : E ≃ₗᵢ[𝕜] F) :
    z ∈ (unitaryConj U A).resolventSet ↔ z ∈ A.resolventSet := by
  simp only [mem_resolventSet_iff]
  refine ⟨fun ⟨R, hR⟩ ↦ ?_, fun ⟨R, hR⟩ ↦ ⟨_, hR.unitaryConj U⟩⟩
  have h := hR.unitaryConj U.symm
  rw [unitaryConj_unitaryConj_symm] at h
  exact ⟨_, h⟩

/-- The resolvent of a unitary conjugate is the conjugate of the resolvent. -/
theorem _root_.LinearPMap.resolvent_unitaryConj (U : E ≃ₗᵢ[𝕜] F) (hz : z ∈ A.resolventSet) :
    (unitaryConj U A).resolvent z =
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A.resolvent z ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
  (isResolventAt_resolvent ((mem_resolventSet_unitaryConj_iff U).2 hz)).unique
    ((isResolventAt_resolvent hz).unitaryConj U)

private theorem hasCompactResolvent_unitaryConj (U : E ≃ₗᵢ[𝕜] F) (h : A.HasCompactResolvent) :
    (unitaryConj U A).HasCompactResolvent := by
  obtain ⟨z, hz, hc⟩ := hasCompactResolvent_def.1 h
  refine hasCompactResolvent_def.2 ⟨z, (mem_resolventSet_unitaryConj_iff U).2 hz, ?_⟩
  rw [resolvent_unitaryConj U hz, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (hc.comp_clm _).clm_comp _

/-- Unitary conjugation preserves compact resolvent. -/
@[simp]
theorem _root_.LinearPMap.hasCompactResolvent_unitaryConj_iff (U : E ≃ₗᵢ[𝕜] F) :
    (unitaryConj U A).HasCompactResolvent ↔ A.HasCompactResolvent :=
  ⟨fun h ↦ by simpa only [unitaryConj_unitaryConj_symm] using
    hasCompactResolvent_unitaryConj U.symm h, hasCompactResolvent_unitaryConj U⟩

end UnitaryConj

/-- A bounded linear operator defined on the entire space has compact resolvent only if the space
is finite-dimensional. -/
theorem _root_.LinearPMap.finiteDimensional_of_hasCompactResolvent_toPMap_top
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (h : ((T : E →ₗ[𝕜] E).toPMap ⊤).HasCompactResolvent) :
    FiniteDimensional 𝕜 E := by
  obtain ⟨z, hz, hcomp⟩ := hasCompactResolvent_def.1 h
  have hres := isResolventAt_resolvent hz
  have hid : ((z • ContinuousLinearMap.id 𝕜 E - T) ∘L
      ((T : E →ₗ[𝕜] E).toPMap ⊤).resolvent z : E → E) = id := funext fun y ↦ by
    simpa using hres.smul_sub_apply y
  exact FiniteDimensional.of_isCompactOperator_id
    (hid ▸ hcomp.clm_comp (z • ContinuousLinearMap.id 𝕜 E - T))

section Complex

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- A bounded self-adjoint operator on a complex Hilbert space has compact resolvent if and only
if the Hilbert space is finite-dimensional. -/
theorem _root_.IsSelfAdjoint.hasCompactResolvent_toPMap_top_iff {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) :
    ((T : H →ₗ[ℂ] H).toPMap ⊤).HasCompactResolvent ↔ FiniteDimensional ℂ H := by
  refine ⟨LinearPMap.finiteDimensional_of_hasCompactResolvent_toPMap_top, fun _ ↦ ?_⟩
  have : ProperSpace H := FiniteDimensional.proper ℂ H
  rw [(LinearPMap.isSelfAdjoint_toPMap_top hT).hasCompactResolvent_iff_isCompactOperator_resolvent
    (z := Complex.I) (by simp)]
  exact isCompactOperator_of_locallyCompactSpace_dom _

/-- For an operator with compact resolvent, the eigenspaces of the compact operator
`(1 + A²)⁻¹` for nonzero eigenvalues are finite-dimensional. -/
theorem _root_.LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq
    (hp : I ∈ A.resolventSet) (h : A.HasCompactResolvent) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (eigenspace (A.invOneAddSq : End ℂ H) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (h.isCompactOperator_invOneAddSq hp) μ hμ

/-- For a self-adjoint operator, `(1 + A²)⁻¹ = R(i)* R(i)`. -/
theorem _root_.IsSelfAdjoint.invOneAddSq_eq_adjoint_comp (hA : IsSelfAdjoint A) :
    A.invOneAddSq = (A.resolvent I).adjoint ∘L A.resolvent I := by
  rw [hA.adjoint_resolvent hA.I_mem_resolventSet, conj_I, invOneAddSq_def]

/-- For a self-adjoint operator, `(1 + A²)⁻¹` is a positive operator. -/
theorem _root_.IsSelfAdjoint.isPositive_invOneAddSq (hA : IsSelfAdjoint A) :
    A.invOneAddSq.IsPositive := by
  rw [hA.invOneAddSq_eq_adjoint_comp]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- For a self-adjoint operator `A` with compact resolvent, the eigenspaces of the compact positive
injective operator `(1 + A²)⁻¹` for nonzero eigenvalues span a dense subspace: their orthogonal
complement is zero. -/
theorem _root_.IsSelfAdjoint.orthogonalComplement_iSup_eigenspaces_invOneAddSq_eq_bot
    (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    (⨆ (μ : ℂ) (_ : μ ≠ 0), eigenspace (A.invOneAddSq : End ℂ H) μ)ᗮ = ⊥ := by
  have h0 := eigenspace_invOneAddSq_zero_eq_bot hA.I_mem_resolventSet hA.neg_I_mem_resolventSet
  have hsup := iSup_split_single (fun μ => eigenspace (A.invOneAddSq : End ℂ H) μ) 0
  rw [h0, bot_sup_eq] at hsup
  rw [← hsup]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (h.isCompactOperator_invOneAddSq hA.I_mem_resolventSet)
    hA.isPositive_invOneAddSq.isSymmetric

end Complex

end TauCeti
