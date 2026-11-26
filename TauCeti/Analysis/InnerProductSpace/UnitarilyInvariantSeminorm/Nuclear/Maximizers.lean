/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Finite
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Basic

import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Isometry

/-!
# Maximizers in nuclear-norm trace duality

For a linear map `A` between finite-dimensional inner product spaces, a contraction `D` attains
the nuclear seminorm of `A` in the real trace pairing exactly when `D ∘ |A| = A`. Thus the
maximizing directions extend the canonical polar factor from the orthogonal complement of
`ker A`. The remaining block is a contraction from `ker A` to `(range A)ᗮ`. Its squared
Frobenius seminorm is the excess over the squared Frobenius seminorm of the polar factor.

The equality proof uses `LinearMap.trace_adjoint_comp_eq_sum_singularValues_mul_inner` and
the equality criterion `eq_of_norm_le_re_inner_eq_norm_sq`. The block proof uses
`LinearMap.normalPart` and `opNorm_add_eq_max_of_twoSidedOrthogonal`.
-/

public section

open LinearMap Module
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

private theorem comp_operatorAbs_eq_iff_apply_rightSingularBasis {D A : E →ₗ[𝕜] F} :
    D ∘ₗ A.operatorAbs = A ↔
      ∀ i : Fin (finrank 𝕜 E), A.singularValues i ≠ 0 →
        D (A.rightSingularBasis i) = A.leftSingularVector i := by
  constructor
  · intro h i hi
    have hσ : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := by simpa using hi
    have hv := LinearMap.congr_fun h (A.rightSingularBasis i)
    rw [comp_apply, A.operatorAbs_rightSingularBasis, map_smul, A.apply_rightSingularBasis i] at hv
    exact smul_right_injective F hσ hv
  · intro h
    apply A.rightSingularBasis.toBasis.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, comp_apply, A.operatorAbs_rightSingularBasis,
      map_smul]
    rw [A.apply_rightSingularBasis i]
    by_cases hi : A.singularValues i = 0
    · simp [hi]
    · rw [h i hi]

/-- A contraction attains the nuclear seminorm in the real trace pairing exactly when it
factors the map through its modulus. -/
theorem re_trace_adjoint_comp_eq_nuclear_iff {D A : E →ₗ[𝕜] F} (hD : opNorm 𝕜 E F D ≤ 1) :
    RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A ↔ D ∘ₗ A.operatorAbs = A := by
  have hDv (i : Fin (finrank 𝕜 E)) : ‖D (A.rightSingularBasis i)‖ ≤ 1 := by
    have h := D.toContinuousLinearMap.le_opNorm (A.rightSingularBasis i)
    rw [LinearMap.coe_toContinuousLinearMap', A.rightSingularBasis.norm_eq_one, mul_one,
      ← opNorm_apply] at h
    exact h.trans hD
  have hle (i : Fin (finrank 𝕜 E)) :
      RCLike.re ⟪D (A.rightSingularBasis i), A.leftSingularVector i⟫_𝕜 ≤ 1 :=
    (RCLike.re_le_norm _).trans <| (norm_inner_le_norm _ _).trans <|
      (mul_le_mul (hDv i) (A.norm_leftSingularVector_le_one i)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [comp_operatorAbs_eq_iff_apply_rightSingularBasis,
    D.trace_adjoint_comp_eq_sum_singularValues_mul_inner A, map_sum, nuclear_apply,
    ← A.sum_fin_singularValues (fun s ↦ s) rfl]
  simp only [RCLike.re_ofReal_mul]
  -- Each summand is bounded above by its singular value, so equality holds termwise.
  rw [Finset.sum_eq_sum_iff_of_le (fun i _ ↦
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hle i) (A.singularValues_nonneg i))]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : A.singularValues i = 0
  · simp [hi]
  have hu : ‖A.leftSingularVector i‖ = 1 := A.orthonormal_leftSingularVector.1 ⟨i, hi⟩
  constructor
  · intro h _
    refine eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ((hDv i).trans_eq hu.symm) ?_
    rw [hu, one_pow]
    exact mul_left_cancel₀ hi (h.trans (mul_one _).symm)
  · intro h
    rw [h hi, inner_self_eq_norm_sq, hu, one_pow, mul_one]

/-- The canonical polar factor is a contraction. -/
theorem _root_.LinearMap.opNorm_polarFactor_le_one (A : E →ₗ[𝕜] F) :
    opNorm 𝕜 E F A.polarFactor ≤ 1 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  have hproj := A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self
  have h := (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr hproj).norm_le
  rw [← opNorm_apply, opNorm_apply_adjoint_comp_self] at h
  exact le_of_sq_le_sq (by simpa only [one_pow] using h) zero_le_one

/-- The polar factor of a nonzero map has operator norm one. -/
theorem _root_.LinearMap.opNorm_polarFactor_of_ne_zero {A : E →ₗ[𝕜] F} (hA : A ≠ 0) :
    opNorm 𝕜 E F A.polarFactor = 1 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  have hproj := A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self
  have hn : adjoint A.polarFactor ∘ₗ A.polarFactor ≠ 0 := by
    intro h
    have hU : A.polarFactor = 0 := by
      simpa only [h, comp_zero] using A.isPartialIsometry_polarFactor.comp_adjoint_comp.symm
    exact hA (by simpa only [hU, zero_comp] using A.polarFactor_comp_operatorAbs.symm)
  have h := (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr hproj).norm_eq_one
    (fun he ↦ hn (LinearMap.toContinuousLinearMap.injective (by simpa using he)))
  rw [← opNorm_apply, opNorm_apply_adjoint_comp_self] at h
  refine le_antisymm A.opNorm_polarFactor_le_one (le_of_sq_le_sq ?_ (apply_nonneg _ _))
  simpa only [one_pow] using h.ge

/-- The real trace of the modulus is the nuclear seminorm. This computes the value of the
trace pairing at the polar factor. -/
@[simp]
theorem _root_.LinearMap.re_trace_operatorAbs (A : E →ₗ[𝕜] F) :
    RCLike.re (trace 𝕜 E A.operatorAbs) = nuclear 𝕜 E F A := by
  rw [← A.adjoint_polarFactor_comp]
  exact (re_trace_adjoint_comp_eq_nuclear_iff A.opNorm_polarFactor_le_one).mpr
    A.polarFactor_comp_operatorAbs

/-- The nuclear seminorm is the maximum real trace pairing over the operator-norm unit ball.
The canonical polar factor attains it. -/
theorem _root_.LinearMap.isGreatest_re_trace_adjoint_comp (A : E →ₗ[𝕜] F) :
    IsGreatest {r : ℝ | ∃ D : E →ₗ[𝕜] F, opNorm 𝕜 E F D ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = r} (nuclear 𝕜 E F A) := by
  refine ⟨⟨A.polarFactor, A.opNorm_polarFactor_le_one, by simp⟩, ?_⟩
  rintro r ⟨D, hD, rfl⟩
  calc
    _ ≤ ‖trace 𝕜 E (adjoint D ∘ₗ A)‖ := RCLike.re_le_norm _
    _ ≤ opNorm 𝕜 E F D * nuclear 𝕜 E F A := norm_trace_adjoint_comp_le_opNorm_mul_nuclear D A
    _ ≤ nuclear 𝕜 E F A := by simpa using
      mul_le_mul_of_nonneg_right hD (apply_nonneg _ A)

private theorem mapsTo_ker_orthogonal_range_of_comp_operatorAbs_eq {D A : E →ₗ[𝕜] F}
    (hD : opNorm 𝕜 E F D ≤ 1) (h : D ∘ₗ A.operatorAbs = A) :
    Set.MapsTo D A.ker (LinearMap.range A)ᗮ := by
  let := FiniteDimensional.completeSpace 𝕜 E
  let := FiniteDimensional.completeSpace 𝕜 F
  have hDadj : opNorm 𝕜 F E (adjoint D) ≤ 1 := by
    rw [opNorm_apply, adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map, ← opNorm_apply]
    exact hD
  simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
    LinearMap.coe_toContinuousLinearMap'] at hDadj
  intro x hx
  refine (Submodule.mem_orthogonal _ _).mpr ?_
  rintro _ ⟨y, rfl⟩
  have hy : D (A.operatorAbs y) = A y := LinearMap.congr_fun h y
  have hnorm : ‖D (A.operatorAbs y)‖ = ‖A.operatorAbs y‖ := by
    rw [hy, norm_operatorAbs_apply]
  -- The adjoint composition fixes every vector on which the contraction preserves the norm.
  have hgram : adjoint D (D (A.operatorAbs y)) = A.operatorAbs y := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
    · rw [← hnorm]
      exact hDadj _
    · rw [adjoint_inner_left, inner_self_eq_norm_sq, hnorm]
  rw [← hy, ← adjoint_inner_left, hgram]
  exact Submodule.inner_left_of_mem_orthogonal hx (A.range_operatorAbs ▸ mem_range_self _ y)

private theorem exists_contraction_on_ker_of_comp_operatorAbs_eq {D A : E →ₗ[𝕜] F}
    (hD : opNorm 𝕜 E F D ≤ 1) (h : D ∘ₗ A.operatorAbs = A) :
    ∃ T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ, opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 ∧
      D = A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
        A.ker.orthogonalProjectionOnto.toLinearMap := by
  have hmaps := mapsTo_ker_orthogonal_range_of_comp_operatorAbs_eq hD h
  let T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ :=
    (D ∘ₗ A.ker.subtype).codRestrict _ fun x ↦ hmaps x.property
  have hT (x : A.ker) : (T x : F) = D x := rfl
  simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
    LinearMap.coe_toContinuousLinearMap'] at hD ⊢
  refine ⟨T, fun x ↦ ?_, ?_⟩
  · rw [← Submodule.norm_coe, hT]
    exact hD x
  · ext x
    obtain ⟨u, hu, v, hv, rfl⟩ := A.ker.exists_add_mem_mem_orthogonal x
    have hvD := (A.comp_operatorAbs_eq_iff_eqOn_polarFactor D).mp h hv
    have hprojV : A.ker.orthogonalProjectionOnto v = 0 :=
      A.ker.orthogonalProjectionOnto_eq_zero_iff.mpr hv
    have hprojU : A.ker.orthogonalProjectionOnto u = ⟨u, hu⟩ :=
      A.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u, hu⟩
    simp [A.polarFactor_apply_of_mem_ker hu, hprojU, hprojV, hT, hvD, add_comm]

private theorem normalPart_polarFactor_subtype_comp (A : E →ₗ[𝕜] F)
    (T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ) :
    let B : E →ₗ[𝕜] F := (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap
    A.polarFactor.normalPart B = B := by
  simp only [LinearMap.normalPart_def, A.range_polarFactor, A.ker_polarFactor]
  ext x
  simp only [comp_apply, ContinuousLinearMap.coe_coe, Submodule.subtype_apply]
  rw [← A.ker.coe_orthogonalProjectionOnto_apply x,
    A.ker.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact (LinearMap.range A)ᗮ.starProjection_mem_subspace_eq_self _

private theorem opNorm_le_one_polarFactor_add_ker {A : E →ₗ[𝕜] F}
    {T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ} (hT : opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1) :
    opNorm 𝕜 E F (A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap) ≤ 1 := by
  let B : E →ₗ[𝕜] F := (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
    A.ker.orthogonalProjectionOnto.toLinearMap
  have hB : opNorm 𝕜 E F B ≤ 1 := by
    simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
      LinearMap.coe_toContinuousLinearMap'] at hT ⊢
    intro x
    have hnorm : ‖B x‖ = ‖T (A.ker.orthogonalProjectionOnto x)‖ := (rfl)
    rw [hnorm]
    exact (hT _).trans (A.ker.norm_orthogonalProjectionOnto_apply_le x)
  have h₁ := A.polarFactor.adjoint_comp_normalPart_eq_zero B
  have h₂ := A.polarFactor.comp_adjoint_normalPart_eq_zero B
  rw [normalPart_polarFactor_subtype_comp A T] at h₁ h₂
  calc
    _ = opNorm 𝕜 E F (A.polarFactor + B) := (rfl)
    _ = max (opNorm 𝕜 E F A.polarFactor) (opNorm 𝕜 E F B) :=
      opNorm_add_eq_max_of_twoSidedOrthogonal h₁ h₂
    _ ≤ 1 := max_le A.opNorm_polarFactor_le_one hB

/-- A maximizing contraction is the polar factor plus a contraction from the kernel of the
map to the orthogonal complement of its range, extended by zero on the initial space. -/
theorem opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff {D A : E →ₗ[𝕜] F} :
    opNorm 𝕜 E F D ≤ 1 ∧ RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A ↔
    ∃ T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ, opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 ∧
      D = A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
        A.ker.orthogonalProjectionOnto.toLinearMap := by
  constructor
  · rintro ⟨hD, ht⟩
    exact exists_contraction_on_ker_of_comp_operatorAbs_eq hD
      ((re_trace_adjoint_comp_eq_nuclear_iff hD).mp ht)
  · rintro ⟨T, hT, rfl⟩
    have hD := opNorm_le_one_polarFactor_add_ker hT
    refine ⟨hD, (re_trace_adjoint_comp_eq_nuclear_iff hD).mpr
      ((A.comp_operatorAbs_eq_iff_eqOn_polarFactor _).mpr ?_)⟩
    intro x hx
    simp [A.ker.orthogonalProjectionOnto_eq_zero_iff.mpr hx]

/-- The maximizer of the real trace pairing on the operator-norm unit ball is unique exactly
when the map is injective or surjective. -/
theorem _root_.LinearMap.existsUnique_opNorm_le_one_re_trace_adjoint_comp_eq_nuclear_iff
    (A : E →ₗ[𝕜] F) :
    (∃! D : E →ₗ[𝕜] F, opNorm 𝕜 E F D ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A) ↔
      Function.Injective A ∨ Function.Surjective A := by
  have hU : opNorm 𝕜 E F A.polarFactor ≤ 1 ∧
      RCLike.re (trace 𝕜 E (adjoint A.polarFactor ∘ₗ A)) = nuclear 𝕜 E F A :=
    ⟨A.opNorm_polarFactor_le_one, by simp⟩
  constructor
  · rintro ⟨D, _, hD⟩
    by_contra! hA
    let : Nontrivial A.ker := Submodule.nontrivial_iff_ne_bot.mpr
      fun h ↦ hA.1 (LinearMap.ker_eq_bot.mp h)
    let : Nontrivial (LinearMap.range A)ᗮ := Submodule.nontrivial_iff_ne_bot.mpr
      fun h ↦ hA.2 (LinearMap.range_eq_top.mp (Submodule.orthogonal_eq_bot_iff.mp h))
    obtain ⟨⟨v, hv⟩⟩ := NormedSpace.sphere_nonempty_rclike 𝕜 (E := A.ker) (r := 1) zero_le_one
    obtain ⟨⟨w, hw⟩⟩ := NormedSpace.sphere_nonempty_rclike 𝕜
      (E := (LinearMap.range A)ᗮ) (r := 1) zero_le_one
    rw [Metric.mem_sphere, dist_zero_right] at hv hw
    let T := (InnerProductSpace.rankOne 𝕜 w v).toLinearMap
    have hT : opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 := by
      rw [opNorm_apply]
      dsimp only [T]
      rw [← LinearMap.coe_toContinuousLinearMap_symm, LinearEquiv.apply_symm_apply,
        InnerProductSpace.norm_rankOne, hv, hw, mul_one]
    let D' := A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap
    have hD' := hD D' (opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mpr ⟨T, hT, rfl⟩)
    have he := LinearMap.congr_fun (hD'.trans (hD _ hU).symm) (v : E)
    have hw0 : (w : F) = 0 := by simpa [D', T, inner_self_eq_norm_sq_to_K, hv] using he
    simp [← Submodule.norm_coe, hw0] at hw
  · intro h
    refine ⟨A.polarFactor, hU, fun D hD ↦ ?_⟩
    obtain ⟨T, _, rfl⟩ := opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mp hD
    have hT : T = 0 := by
      rcases h with h | h
      · let : Subsingleton A.ker :=
          Submodule.subsingleton_iff_eq_bot.mpr (LinearMap.ker_eq_bot.mpr h)
        ext x
        rw [Subsingleton.elim x 0]
        simp
      · let : Subsingleton (LinearMap.range A)ᗮ := Submodule.subsingleton_iff_eq_bot.mpr
          (Submodule.orthogonal_eq_bot_iff.mpr (LinearMap.range_eq_top.mpr h))
        exact LinearMap.ext fun x ↦ Subsingleton.elim (T x) _
    simp [hT]

/-- The squared Frobenius seminorm of the polar factor is the rank of the original map. -/
theorem _root_.LinearMap.sq_frobenius_polarFactor (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A.polarFactor ^ 2 = finrank 𝕜 (LinearMap.range A) := by
  let U := A.polarFactor
  let b := stdOrthonormalBasis 𝕜 E
  have h := U.trace_adjoint_comp_self_eq_sum_norm_apply_sq b
  rw [← sq_frobenius_apply b] at h
  have htr := A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self.isIdempotentElem
    |>.isProj_range.trace
  rw [U.range_adjoint_comp_self, U.finrank_range_adjoint, A.range_polarFactor] at htr
  rw [htr] at h
  exact_mod_cast h.symm

/-- The squared Frobenius seminorm of the polar factor plus an orthogonal kernel block is the
rank of the original map plus the squared Frobenius seminorm of that block. -/
theorem _root_.LinearMap.sq_frobenius_polarFactor_add_ker (A : E →ₗ[𝕜] F)
    (T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ) :
    frobenius 𝕜 E F (A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap) ^ 2 =
      finrank 𝕜 (LinearMap.range A) + frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  let := FiniteDimensional.completeSpace 𝕜 A.ker
  let B : E →ₗ[𝕜] F := (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
    A.ker.orthogonalProjectionOnto.toLinearMap
  have horth := A.polarFactor.adjoint_comp_normalPart_eq_zero B
  rw [normalPart_polarFactor_subtype_comp A T] at horth
  have hB : frobenius 𝕜 E F B ^ 2 = frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
    have hproj (x : A.ker) :
        ‖(ContinuousLinearMap.adjoint A.ker.orthogonalProjectionOnto) x‖ = ‖x‖ := by
      rw [A.ker.adjoint_orthogonalProjectionOnto]
      rfl
    have h := ContinuousLinearMap.hilbertSchmidtEnergy_isometry_comp_coisometry
      (LinearMap.range A)ᗮ.subtypeL (fun _ ↦ rfl) T.toContinuousLinearMap
      A.ker.orthogonalProjectionOnto hproj
      (stdOrthonormalBasis 𝕜 E).toHilbertBasis (stdOrthonormalBasis 𝕜 A.ker).toHilbertBasis
    simp only [ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
      ContinuousLinearMap.toLinearMap_comp, Submodule.toLinearMap_subtypeL,
      LinearMap.coe_toContinuousLinearMap] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp h
  calc
    _ = frobenius 𝕜 E F (A.polarFactor + B) ^ 2 := (rfl)
    _ = frobenius 𝕜 E F A.polarFactor ^ 2 + frobenius 𝕜 E F B ^ 2 :=
      sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero (by rw [horth, map_zero, map_zero])
    _ = _ := by rw [A.sq_frobenius_polarFactor, hB]

/-- Every maximizing contraction distinct from the polar factor has strictly greater
Frobenius seminorm. -/
theorem frobenius_polarFactor_lt_of_re_trace_adjoint_comp_eq_nuclear {D A : E →ₗ[𝕜] F}
    (hD : opNorm 𝕜 E F D ≤ 1) (ht : RCLike.re (trace 𝕜 E (adjoint D ∘ₗ A)) = nuclear 𝕜 E F A)
    (hDne : D ≠ A.polarFactor) : frobenius 𝕜 E F A.polarFactor < frobenius 𝕜 E F D := by
  obtain ⟨T, _, hDeq⟩ := opNorm_le_one_and_re_trace_adjoint_comp_eq_nuclear_iff.mp ⟨hD, ht⟩
  have hTne : T ≠ 0 := by
    intro hT
    exact hDne (by simpa [hT] using hDeq)
  have hTpos : 0 < frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
    rw [frobenius_apply_eq_sqrt_sum_sq_singularValues, Finsupp.sum,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr
      (fun h ↦ hTne ((T.singularValues_eq_zero_iff).mp h))
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨i, hi,
      sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)⟩
  apply (sq_lt_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [A.sq_frobenius_polarFactor, hDeq, A.sq_frobenius_polarFactor_add_ker]
  exact lt_add_of_pos_right _ hTpos

end TauCeti.UnitarilyInvariantSeminorm
