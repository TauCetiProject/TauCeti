/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology
public import TauCeti.Analysis.Normed.Module.Ball.SelfAdjoint
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import TauCeti.Analysis.VonNeumannAlgebra.MatrixAmplification

import TauCeti.Algebra.Star.Basic

/-!
# The Kaplansky density theorem

Let `S` be a unital star subalgebra of the bounded operators on a complex Hilbert space `H`. By the
bicommutant theorem, `S` is strongly dense in its double commutant `S''`. The **Kaplansky density
theorem** sharpens this to the unit balls: the strong operator closure of the closed unit ball of
`S` is the closed unit ball of `S''`
(`StarSubalgebra.closure_unitBall_eq_unitBall_double_centralizer`). The same holds for the
self-adjoint parts of the closed balls of any radius `r`
(`StarSubalgebra.closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer`)
and for the positive parts of the unit balls
(`StarSubalgebra.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer`). All closures
are taken in Mathlib's strong operator copy `H →Lₚₜ[ℂ] H`.

In each case the inclusion `⊆` holds because the right-hand side is weak operator closed, hence
strong operator closed. For the inclusion `⊇`:

* *Self-adjoint part.* For `0 < r`, a self-adjoint element `x ∈ S''` of norm at most `r` is
  `r` times the Kaplansky function `t ↦ 2t / (1 + t²)` of the self-adjoint element
  `y = cfc kaplanskyFunInv (r⁻¹ • x)` of `S''`. The self-adjoint part of `S` is strongly dense in
  that of `S''`, so `y` is a strong limit of self-adjoint elements `yᵢ ∈ S`. The Kaplansky
  function is strongly continuous on self-adjoint operators without any norm bound, so the
  self-adjoint elements `r • cfc kaplanskyFun yᵢ` of norm at most `r` converge strongly to `x`.
  They lie in the norm closure of `S`, whose self-adjoint elements of norm at most `r` are norm
  limits of self-adjoint elements of norm at most `r` of `S`
  (`TauCeti.closure_inter_selfAdjoint_inter_closedBall`).
* *Positive part.* For `0 ≤ x` in the unit ball of `S''`, approximate `√x` by self-adjoint
  contractions `yᵢ ∈ S`; multiplication is strongly continuous on bounded sets, so the positive
  contractions `yᵢ²` converge strongly to `x`.
* *Unit ball.* For a contraction `x ∈ S''`, the operator `[[0, x], [x⋆, 0]]` on `H ⊕ H` is a
  self-adjoint contraction in the double commutant of the matrix amplification `M₂(S)`
  (`StarSubalgebra.mem_centralizer_centralizer_piLpMatrix_iff`). Approximate it by self-adjoint
  contractions of `M₂(S)`; their `(0, 1)` entries are contractions in `S` converging strongly
  to `x`.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.5; Jones,
*Von Neumann Algebras*, Theorem 5.2.1.
-/

public section

open Filter Topology TauCeti

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The weak operator closed sets of operators used to cut out the right-hand sides of the
Kaplansky density theorem. -/
private theorem isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H)) (r : ℝ)
    {P : Set (H →L[ℂ] H)} (hP : IsClosed (ContinuousLinearMapWOT.ofCLM '' P)) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      {x | x ∈ S.centralizer.centralizer ∧ x ∈ P ∧ ‖x‖ ≤ r}) := by
  refine ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
    ?_
  have hball : {x : H →L[ℂ] H | ‖x‖ ≤ r} = Metric.closedBall 0 r := by
    ext x; simp
  rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_mem_eq, Set.ofPred_mem_eq, hball,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact S.centralizer.isClosed_image_ofCLM_centralizer.inter
    (ContinuousLinearMapWOT.isCompact_image_ofCLM_inter_closedBall_of_isClosed hP 0 r).isClosed

/-- **The Kaplansky density theorem for self-adjoint parts.** For a unital star subalgebra `S` of
`B(H)`, the strong operator closure of the self-adjoint elements of norm at most `r` of `S` is the
set of self-adjoint elements of norm at most `r` of its double commutant `S''`. -/
theorem closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ r}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ r} := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hxsa, hxr⟩ => ⟨Set.subset_centralizer_centralizer hx, hxsa, hxr⟩)
    (isClosed_image_toPointwiseConvergenceCLM_inter _ r
      ContinuousLinearMapWOT.isClosed_image_ofCLM_setOf_isSelfAdjoint)) ?_
  rintro _ ⟨x, ⟨hx, hxsa, hxr⟩, rfl⟩
  rcases ((norm_nonneg x).trans hxr).eq_or_lt with rfl | hr
  · obtain rfl : x = 0 := norm_le_zero_iff.mp hxr
    exact subset_closure ⟨0, ⟨zero_mem S, .zero _, norm_zero.le⟩, rfl⟩
  -- Rescale `x` to the self-adjoint contraction `z = r⁻¹ • x` of `S''`.
  set z := ((r⁻¹ : ℝ) : ℂ) • x
  have hxz : (r : ℂ) • z = x := by
    simp only [z, Complex.ofReal_inv]
    exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hr.ne') x
  have hz : z ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := Set.smul_mem_centralizer _ hx
  have hzsa : IsSelfAdjoint z := IsSelfAdjoint.smul (Complex.conj_ofReal _) hxsa
  have hz₁ : ‖z‖ ≤ 1 := by
    simpa [z, norm_smul, abs_of_pos hr] using inv_mul_le_one_of_le₀ hxr hr.le
  -- `z = cfc kaplanskyFun y` for the self-adjoint element `y = cfc kaplanskyFunInv z` of `S''`.
  set y := cfc kaplanskyFunInv z
  have hy : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    S.cfc_mem_centralizer_centralizer kaplanskyFunInv hz
  have hysa : IsSelfAdjoint y := cfc_predicate kaplanskyFunInv z
  have hzy : cfc kaplanskyFun y = z := hzsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hz₁
  -- `y` is a strong limit of self-adjoint elements of `S`.
  have hyS : q y ∈ closure (q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H))) :=
    S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint ▸ ⟨y, ⟨hy, hysa⟩, rfl⟩
  obtain ⟨l, hl, hlS, hlim⟩ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mp hyS
  -- Applying `r` times the Kaplansky function, `x` is a strong limit of self-adjoint elements of
  -- norm at most `r` of the norm closure of `S`.
  have hclos : q x ∈ closure (q '' {w | w ∈ closure (S : Set (H →L[ℂ] H)) ∧ IsSelfAdjoint w ∧
      ‖w‖ ≤ r}) := by
    refine ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mpr
      ⟨l.map fun a => (r : ℂ) • cfc kaplanskyFun a, hl.map _, eventually_map.mpr ?_, fun v => ?_⟩
    · filter_upwards [hlS] with a ⟨haS, _⟩
      refine ⟨?_, IsSelfAdjoint.smul (Complex.conj_ofReal r) (cfc_predicate _ a), ?_⟩
      · have := S.isClosed_topologicalClosure -- Supplies the closedness instance of `cfc_mem`.
        rw [← S.topologicalClosure_coe]
        exact SMulMemClass.smul_mem _
          (cfc_mem (s := S.topologicalClosure) (𝕜' := ℂ) kaplanskyFun (S.le_topologicalClosure haS))
      · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
        exact mul_le_of_le_one_right hr.le (norm_cfc_kaplanskyFun_le a)
    · rw [tendsto_map'_iff, ← hxz, ← hzy]
      exact (tendsto_cfc_kaplanskyFun_apply (x := id) (hlS.mono fun a ha => ha.2) hysa hlim
        v).const_smul (r : ℂ)
  -- These are norm, hence strong, limits of self-adjoint elements of norm at most `r` of `S`.
  refine closure_minimal ?_ isClosed_closure hclos
  rintro _ ⟨w, ⟨hw, hwsa, hwr⟩, rfl⟩
  have hw' : w ∈ closure ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩
      Metric.closedBall 0 r) := by
    rw [TauCeti.closure_inter_selfAdjoint_inter_closedBall ℂ S r]
    exact ⟨⟨hw, hwsa⟩, mem_closedBall_zero_iff.mpr hwr⟩
  refine closure_mono (Set.image_mono ?_)
    (image_closure_subset_closure_image q.continuous ⟨w, hw', rfl⟩)
  rintro a ⟨⟨ha, hasa⟩, har⟩
  exact ⟨ha, hasa, mem_closedBall_zero_iff.mp har⟩

/-- **The Kaplansky density theorem for positive parts.** For a unital star subalgebra `S` of
`B(H)`, the strong operator closure of the positive contractions of `S` is the set of positive
contractions of its double commutant `S''`. -/
theorem closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ 0 ≤ x ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ 0 ≤ x ∧ ‖x‖ ≤ 1} := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hx₀, hx₁⟩ => ⟨Set.subset_centralizer_centralizer hx, hx₀, hx₁⟩)
    (isClosed_image_toPointwiseConvergenceCLM_inter _ 1
      (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := 0)))) ?_
  rintro _ ⟨x, ⟨hx, hx₀, hx₁⟩, rfl⟩
  -- `√x` is a self-adjoint contraction of `S''`.
  have hr : CFC.sqrt x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [CFC.sqrt_eq_real_sqrt x hx₀]
    exact S.cfcₙ_mem_centralizer_centralizer Real.sqrt hx
  have hr₁ : ‖CFC.sqrt x‖ ≤ 1 := by
    rw [CFC.norm_sqrt x hx₀]
    exact Real.sqrt_le_one.mpr hx₁
  have hrS : q (CFC.sqrt x) ∈ closure (q '' {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) :=
    S.closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer 1 ▸
      ⟨CFC.sqrt x, ⟨hr, (CFC.sqrt_nonneg x).isSelfAdjoint, hr₁⟩, rfl⟩
  obtain ⟨l, hl, hlS, hlim⟩ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mp hrS
  -- Squares of self-adjoint contractions converge strongly, since they are uniformly bounded.
  refine ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mpr
    ⟨l.map fun a => a * a, hl.map _, eventually_map.mpr ?_, fun v => ?_⟩
  · filter_upwards [hlS] with a ⟨haS, hasa, ha₁⟩
    refine ⟨mul_mem haS haS, ?_, (norm_mul_le a a).trans
      ((mul_le_mul ha₁ ha₁ (norm_nonneg a) zero_le_one).trans_eq (one_mul 1))⟩
    simpa [hasa.star_eq] using star_mul_self_nonneg a
  · rw [tendsto_map'_iff, ← CFC.sqrt_mul_sqrt_self x hx₀]
    exact ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
      (hlS.mono fun a ha => ha.2.2) v

/-- The operator `[[0, x], [x⋆, 0]]` on `H ⊕ H`. -/
private noncomputable def offDiag (x : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
  ContinuousLinearMap.ofPiLpEntries ![![0, x], ![star x, 0]]

private theorem isSelfAdjoint_offDiag (x : H →L[ℂ] H) : IsSelfAdjoint (offDiag x) :=
  ContinuousLinearMap.ext_piLpEntry fun i j => by
    fin_cases i <;> fin_cases j <;> simp [offDiag]

private theorem norm_offDiag_le {x : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) : ‖offDiag x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_two, add_comm (‖w 0‖ ^ 2)]
  have h₀ : ‖x (w 1)‖ ≤ ‖w 1‖ := (x.le_of_opNorm_le hx _).trans_eq (one_mul _)
  have h₁ : ‖star x (w 0)‖ ≤ ‖w 0‖ :=
    ((star x).le_of_opNorm_le (by rwa [norm_star]) _).trans_eq (one_mul _)
  simp only [offDiag, ContinuousLinearMap.ofPiLpEntries_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zero_apply, zero_add, add_zero]
  gcongr

/-- **The Kaplansky density theorem.** For a unital star subalgebra `S` of `B(H)`, the strong
operator closure of the closed unit ball of `S` is the closed unit ball of its double commutant
`S''`. -/
theorem closure_unitBall_eq_unitBall_double_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  have hball := isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H)) 1
    (P := Set.univ) (by simp [Set.image_univ_of_surjective ContinuousLinearMapWOT.ofCLM_surjective])
  simp only [Set.mem_univ, true_and] at hball
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hx₁⟩ => ⟨Set.subset_centralizer_centralizer hx, hx₁⟩) hball) ?_
  rintro _ ⟨x, ⟨hx, hx₁⟩, rfl⟩
  -- `[[0, x], [x⋆, 0]]` is a self-adjoint contraction in the double commutant of `M₂(S)`.
  have hX : offDiag x ∈ ((S.piLpMatrix (Fin 2) : Set _)).centralizer.centralizer := by
    refine (S.mem_centralizer_centralizer_piLpMatrix_iff).mpr fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [offDiag, hx, StarMemClass.star_mem_centralizer_centralizer S hx,
        Set.zero_mem_centralizer]
  have hXS : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ (offDiag x) ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ ''
        {Y | Y ∈ S.piLpMatrix (Fin 2) ∧ IsSelfAdjoint Y ∧ ‖Y‖ ≤ 1}) :=
    closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer
      (S.piLpMatrix (Fin 2)) 1 ▸
        ⟨offDiag x, ⟨hX, isSelfAdjoint_offDiag x, norm_offDiag_le hx₁⟩, rfl⟩
  obtain ⟨l, hl, hlS, hlim⟩ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mp hXS
  -- The `(0, 1)` entries of the approximants are contractions of `S` converging strongly to `x`.
  refine ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mpr
    ⟨l.map fun Y => Y.piLpEntry 0 1, hl.map _, eventually_map.mpr ?_, fun v => ?_⟩
  · filter_upwards [hlS] with Y ⟨hY, _, hY₁⟩
    exact ⟨mem_piLpMatrix.mp hY 0 1, (Y.norm_piLpEntry_le 0 1).trans hY₁⟩
  · have hx01 : (offDiag x).piLpEntry 0 1 = x := by simp [offDiag]
    rw [tendsto_map'_iff, ← hx01]
    simp only [Function.comp_def, ContinuousLinearMap.piLpEntry_apply]
    exact ((PiLp.continuous_apply 2 _ 0).tendsto _).comp (hlim _)

end StarSubalgebra
