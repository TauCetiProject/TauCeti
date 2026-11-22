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
public import TauCeti.Analysis.Normed.Algebra.StarSubalgebra
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
self-adjoint parts of the unit balls
(`StarSubalgebra.closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer`) and
for their positive parts
(`StarSubalgebra.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer`). These closures
are taken in Mathlib's strong operator copy `H →Lₚₜ[ℂ] H`.

All three statements also hold in the finer strong-star topology, on the type copy
`TauCeti.ContinuousLinearMapStrongStar`, where the adjoints of the approximants converge as well
(`StarSubalgebra.closure_strongStar_unitBall_eq_unitBall_double_centralizer` and its
self-adjoint and positive companions). For a finite index type `ι`, applying the theorem to the
matrix amplification `Mᵢ(S)` shows that the contractions of `Mᵢ(S)` are strongly and strong-star
dense among the contractions on `PiLp 2 (fun _ : ι => H)` with all matrix entries in `S''`
(`StarSubalgebra.closure_piLpMatrix_unitBall_eq_unitBall_piLpEntry_double_centralizer`,
`StarSubalgebra.closure_strongStar_piLpMatrix_unitBall_eq_unitBall_piLpEntry_double_centralizer`).

As a consequence, `S` is a von Neumann algebra, that is `S'' = S`, exactly when its closed unit
ball is weak operator compact
(`StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`): compactness makes
that ball weak operator closed, and by Kaplansky density it then contains the unit ball of `S''`.

In each density statement the inclusion `⊆` holds because the right-hand side is weak operator
closed, hence strong and strong-star closed. For the inclusion `⊇`:

* *Self-adjoint part.* A self-adjoint contraction `x ∈ S''` is the Kaplansky function
  `t ↦ 2t / (1 + t²)` of the self-adjoint element `y = cfc kaplanskyFunInv x` of `S''`. The
  self-adjoint part of `S` is strongly dense in that of `S''`, so `y` is a strong limit of
  self-adjoint elements `yᵢ ∈ S`. The Kaplansky function is strongly continuous on self-adjoint
  operators without any norm bound, so the self-adjoint contractions `cfc kaplanskyFun yᵢ`
  converge strongly to `x`. They lie in the norm closure of `S`, whose self-adjoint contractions
  are norm limits of self-adjoint contractions of `S`
  (`StarSubalgebra.closure_selfAdjoint_unitBall`).
* *Positive part.* For `0 ≤ x` in the unit ball of `S''`, approximate `√x` by self-adjoint
  contractions `yᵢ ∈ S`; multiplication is strongly continuous on bounded sets, so the positive
  contractions `yᵢ²` converge strongly to `x`.
* *Strong-star forms of these.* Strong and strong-star convergence agree for nets of self-adjoint
  operators with a self-adjoint limit.
* *Unit ball.* For a contraction `x ∈ S''`, the operator `[[0, x], [x⋆, 0]]` on `H ⊕ H` is a
  self-adjoint contraction in the double commutant of the matrix amplification `M₂(S)`
  (`StarSubalgebra.mem_centralizer_centralizer_piLpMatrix_iff`). Approximate it strong-star by
  self-adjoint contractions of `M₂(S)`; their `(0, 1)` entries are contractions in `S` converging
  strong-star, hence strongly, to `x`, because taking a matrix entry is strong-star continuous
  (`TauCeti.ContinuousLinearMapStrongStar.continuous_piLpEntry`).

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.5; Jones,
*Von Neumann Algebras*, Theorem 5.2.1 and Corollary 5.2.2.
-/

public section

open Filter Topology TauCeti

namespace TauCeti.ContinuousLinearMapStrongStar

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [Fintype ι] [DecidableEq ι]

/-- Taking the `(i, j)` matrix entry of an operator on the Hilbert sum `PiLp 2 (fun _ : ι => H)`
is continuous for the strong-star topologies. -/
theorem continuous_piLpEntry (i j : ι) :
    Continuous fun Y : ContinuousLinearMapStrongStar 𝕜 (PiLp 2 (fun _ : ι => H))
      (PiLp 2 (fun _ : ι => H)) => ofCLM (Y.toCLM.piLpEntry i j) := by
  refine continuous_of_continuous_apply (fun v => ?_) fun v => ?_
  · simpa only [ContinuousLinearMap.piLpEntry_apply, PiLp.proj_apply, Function.comp_def] using
      (PiLp.proj 2 (𝕜 := 𝕜) (fun _ : ι => H) i).continuous.comp
        (continuous_toCLM_apply (PiLp.single 2 (β := fun _ : ι => H) j v))
  · -- The adjoint of the `(i, j)` entry is the `(j, i)` entry of the adjoint.
    refine ((PiLp.proj 2 (𝕜 := 𝕜) (fun _ : ι => H) j).continuous.comp
      (continuous_adjoint_apply (PiLp.single 2 (β := fun _ : ι => H) i v))).congr fun Y => ?_
    simp [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.piLpEntry_star]

end TauCeti.ContinuousLinearMapStrongStar

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The weak operator closed sets of operators used to cut out the right-hand sides of the
Kaplansky density theorem. -/
private theorem isClosed_image_ofCLM_inter (S : Set (H →L[ℂ] H))
    {P : Set (H →L[ℂ] H)} (hP : IsClosed (ContinuousLinearMapWOT.ofCLM '' P)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      {x | x ∈ S.centralizer.centralizer ∧ x ∈ P ∧ ‖x‖ ≤ 1}) := by
  have hball : {x : H →L[ℂ] H | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x; simp
  rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_mem_eq, Set.ofPred_mem_eq, hball,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact S.centralizer.isClosed_image_ofCLM_centralizer.inter
    (hP.inter (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 1).isClosed)

/-- The closed unit ball of a double commutant is weak operator closed. -/
private theorem isClosed_image_ofCLM_unitBall (S : Set (H →L[ℂ] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' {x | x ∈ S.centralizer.centralizer ∧ ‖x‖ ≤ 1}) := by
  simpa using isClosed_image_ofCLM_inter S (P := Set.univ)
    (by simp [Set.image_univ_of_surjective ContinuousLinearMapWOT.ofCLM_surjective])

/-- **The Kaplansky density theorem for self-adjoint parts.** For a unital star subalgebra `S` of
`B(H)`, the strong operator closure of the self-adjoint contractions of `S` is the set of
self-adjoint contractions of its double commutant `S''`. -/
theorem closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1} := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hxsa, hx₁⟩ => ⟨Set.subset_centralizer_centralizer hx, hxsa, hx₁⟩)
    (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      (isClosed_image_ofCLM_inter _
        ContinuousLinearMapWOT.isClosed_image_ofCLM_setOf_isSelfAdjoint))) ?_
  rintro _ ⟨x, ⟨hx, hxsa, hx₁⟩, rfl⟩
  -- `x = cfc kaplanskyFun y` for the self-adjoint element `y = cfc kaplanskyFunInv x` of `S''`.
  set y := cfc kaplanskyFunInv x
  have hy : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    S.cfc_mem_centralizer_centralizer kaplanskyFunInv hx
  have hysa : IsSelfAdjoint y := cfc_predicate kaplanskyFunInv x
  have hxy : cfc kaplanskyFun y = x := hxsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hx₁
  -- `y` is a strong limit of self-adjoint elements of `S`.
  have hyS : q y ∈ closure (q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H))) :=
    S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint ▸ ⟨y, ⟨hy, hysa⟩, rfl⟩
  obtain ⟨l, hl, hlS, hlim⟩ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mp hyS
  -- Applying the Kaplansky function, `x` is a strong limit of self-adjoint contractions of the
  -- norm closure of `S`.
  have hclos : q x ∈ closure (q '' {z | z ∈ closure (S : Set (H →L[ℂ] H)) ∧ IsSelfAdjoint z ∧
      ‖z‖ ≤ 1}) := by
    refine ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mpr
      ⟨l.map (cfc kaplanskyFun), hl.map _, eventually_map.mpr ?_, fun v => ?_⟩
    · filter_upwards [hlS] with a ⟨haS, _⟩
      refine ⟨?_, cfc_predicate _ a, norm_cfc_kaplanskyFun_le a⟩
      have := S.isClosed_topologicalClosure -- Supplies the closedness instance of `cfc_mem`.
      rw [← S.topologicalClosure_coe]
      exact cfc_mem (s := S.topologicalClosure) (𝕜' := ℂ) kaplanskyFun (S.le_topologicalClosure haS)
    · rw [tendsto_map'_iff, ← hxy]
      exact tendsto_cfc_kaplanskyFun_apply (x := id) (hlS.mono fun a ha => ha.2) hysa hlim v
  -- These are norm, hence strong, limits of self-adjoint contractions of `S`.
  refine closure_minimal ?_ isClosed_closure hclos
  rintro _ ⟨z, ⟨hz, hzsa, hz₁⟩, rfl⟩
  exact image_closure_subset_closure_image q.continuous
    ⟨z, S.closure_selfAdjoint_unitBall ▸ ⟨hz, hzsa, hz₁⟩, rfl⟩

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
    (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      (isClosed_image_ofCLM_inter _ (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := 0)))))
    ?_
  rintro _ ⟨x, ⟨hx, hx₀, hx₁⟩, rfl⟩
  -- `√x` is a self-adjoint contraction of `S''`.
  have hr : CFC.sqrt x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [CFC.sqrt_eq_real_sqrt x hx₀]
    exact S.cfcₙ_mem_centralizer_centralizer Real.sqrt hx
  have hr₁ : ‖CFC.sqrt x‖ ≤ 1 := by
    rw [CFC.norm_sqrt x hx₀]
    exact Real.sqrt_le_one.mpr hx₁
  have hrS : q (CFC.sqrt x) ∈ closure (q '' {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) :=
    S.closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer ▸
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

/-! ### The strong-star forms -/

/-- **The Kaplansky density theorem for self-adjoint parts, strong-star form.** For a unital star
subalgebra `S` of `B(H)`, the strong-star closure of the self-adjoint contractions of `S` is the set
of self-adjoint contractions of its double commutant `S''`. -/
theorem closure_strongStar_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1} :=
  ContinuousLinearMapStrongStar.closure_image_ofCLM_eq_of_isStarNormal
    (fun _ hx => hx.2.1.isStarNormal)
    S.closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer

/-- **The Kaplansky density theorem for positive parts, strong-star form.** For a unital star
subalgebra `S` of `B(H)`, the strong-star closure of the positive contractions of `S` is the set of
positive contractions of its double commutant `S''`. -/
theorem closure_strongStar_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapStrongStar.ofCLM '' {x | x ∈ S ∧ 0 ≤ x ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ 0 ≤ x ∧ ‖x‖ ≤ 1} :=
  ContinuousLinearMapStrongStar.closure_image_ofCLM_eq_of_isStarNormal
    (fun _ hx => (IsSelfAdjoint.of_nonneg hx.2.1).isStarNormal)
    S.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer

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

/-- **The Kaplansky density theorem, strong-star form.** For a unital star subalgebra `S` of
`B(H)`, the strong-star closure of the closed unit ball of `S` is the closed unit ball of its double
commutant `S''`. -/
theorem closure_strongStar_unitBall_eq_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapStrongStar.ofCLM '' {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hx₁⟩ => ⟨Set.subset_centralizer_centralizer hx, hx₁⟩)
    (ContinuousLinearMapStrongStar.isClosed_image_ofCLM_of_isClosed_image_wot
      (isClosed_image_ofCLM_unitBall _))) ?_
  rintro _ ⟨x, ⟨hx, hx₁⟩, rfl⟩
  -- `[[0, x], [x⋆, 0]]` is a self-adjoint contraction in the double commutant of `M₂(S)`, so it is
  -- a strong-star limit of self-adjoint contractions of `M₂(S)`.
  have hX : offDiag x ∈ ((S.piLpMatrix (Fin 2) : Set _)).centralizer.centralizer := by
    refine (S.mem_centralizer_centralizer_piLpMatrix_iff).mpr fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [offDiag, hx, StarMemClass.star_mem_centralizer_centralizer S hx,
        Set.zero_mem_centralizer]
  have hXS : ContinuousLinearMapStrongStar.ofCLM (offDiag x) ∈
      closure (ContinuousLinearMapStrongStar.ofCLM ''
        {Y | Y ∈ S.piLpMatrix (Fin 2) ∧ IsSelfAdjoint Y ∧ ‖Y‖ ≤ 1}) :=
    closure_strongStar_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer
      (S.piLpMatrix (Fin 2)) ▸ ⟨offDiag x, ⟨hX, isSelfAdjoint_offDiag x, norm_offDiag_le hx₁⟩, rfl⟩
  -- Taking the `(0, 1)` entry is strong-star continuous, and sends these approximants to
  -- contractions of `S` and `[[0, x], [x⋆, 0]]` to `x`.
  have hx01 : (offDiag x).piLpEntry 0 1 = x := by simp [offDiag]
  rw [← hx01]
  refine (map_mem_closure (ContinuousLinearMapStrongStar.continuous_piLpEntry (0 : Fin 2) 1)
    hXS ?_ :)
  rintro _ ⟨Y, ⟨hY, _, hY₁⟩, rfl⟩
  exact ⟨_, ⟨mem_piLpMatrix.mp hY 0 1, (Y.norm_piLpEntry_le 0 1).trans hY₁⟩, rfl⟩

/-! ### The strong operator form -/

/-- **The Kaplansky density theorem.** For a unital star subalgebra `S` of `B(H)`, the strong
operator closure of the closed unit ball of `S` is the closed unit ball of its double commutant
`S''`. -/
theorem closure_unitBall_eq_unitBall_double_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  refine subset_antisymm (closure_minimal
    (Set.image_mono fun x ⟨hx, hx₁⟩ => ⟨Set.subset_centralizer_centralizer hx, hx₁⟩)
    (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      (isClosed_image_ofCLM_unitBall _))) ?_
  -- Strong-star density implies strong density.
  rintro _ ⟨x, hx, rfl⟩
  have hxS : ContinuousLinearMapStrongStar.ofCLM x ∈
      closure (ContinuousLinearMapStrongStar.ofCLM '' {x | x ∈ S ∧ ‖x‖ ≤ 1}) :=
    S.closure_strongStar_unitBall_eq_unitBall_double_centralizer ▸ ⟨x, hx, rfl⟩
  refine map_mem_closure (f := fun A : ContinuousLinearMapStrongStar ℂ H H =>
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H A.toCLM)
    ContinuousLinearMapStrongStar.continuous_toPointwiseConvergenceCLM hxS ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

/-! ### Matrix amplifications -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Kaplansky density theorem for matrix amplifications, strong-star form.** For a unital
star subalgebra `S` of `B(H)` and a finite index type `ι`, the strong-star closure of the closed
unit ball of the matrix amplification `Mᵢ(S)` consists of the contractions on the Hilbert sum
`PiLp 2 (fun _ : ι => H)` all of whose matrix entries lie in `S''`. -/
theorem closure_strongStar_piLpMatrix_unitBall_eq_unitBall_piLpEntry_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapStrongStar.ofCLM '' {T | T ∈ S.piLpMatrix ι ∧ ‖T‖ ≤ 1}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {T | (∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) ∧
          ‖T‖ ≤ 1} := by
  simp_rw [closure_strongStar_unitBall_eq_unitBall_double_centralizer,
    mem_centralizer_centralizer_piLpMatrix_iff]

/-- **The Kaplansky density theorem for matrix amplifications.** For a unital star subalgebra `S`
of `B(H)` and a finite index type `ι`, the strong operator closure of the closed unit ball of the
matrix amplification `Mᵢ(S)` consists of the contractions on the Hilbert sum
`PiLp 2 (fun _ : ι => H)` all of whose matrix entries lie in `S''`. -/
theorem closure_piLpMatrix_unitBall_eq_unitBall_piLpEntry_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | T ∈ S.piLpMatrix ι ∧ ‖T‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) ∧
          ‖T‖ ≤ 1} := by
  simp_rw [closure_unitBall_eq_unitBall_double_centralizer,
    mem_centralizer_centralizer_piLpMatrix_iff]

/-! ### The unit-ball criterion -/

/-- **The unit-ball criterion.** A unital star subalgebra `S` of `B(H)` equals its double
commutant, that is, is a von Neumann algebra, exactly when its closed unit ball is weak operator
compact. -/
theorem double_commutant_iff_isCompact_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsCompact (ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact VonNeumannAlgebra.isCompact_image_ofCLM_inter_closedBall ⟨S, h⟩ 0 1
  -- By Kaplansky density, every contraction of `S''` lies in the weak operator closure of the
  -- unit ball of `S`, which is compact, hence closed.
  have hball {y : H →L[ℂ] H} (hy : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
      (hy₁ : ‖y‖ ≤ 1) : y ∈ S := by
    have hyS : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H y ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          {x | x ∈ S ∧ ‖x‖ ≤ 1}) :=
      S.closure_unitBall_eq_unitBall_double_centralizer ▸ ⟨y, ⟨hy, hy₁⟩, rfl⟩
    replace hyS := ContinuousLinearMapWOT.ofCLM_mem_closure_image_of_toPointwiseConvergenceCLM hyS
    have hS : {x | x ∈ S ∧ ‖x‖ ≤ 1} = (S : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1 := by
      ext x; simp
    rw [hS, h.isClosed.closure_eq, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image] at hyS
    exact hyS.1
  -- A general element of `S''` is a multiple of a contraction of `S''`.
  refine subset_antisymm (fun x hx => ?_) Set.subset_centralizer_centralizer
  obtain rfl | hx₀ := eq_or_ne x 0
  · exact zero_mem S
  have hxS := hball (Set.smul_mem_centralizer ((‖x‖ : ℂ)⁻¹) hx) (norm_smul_inv_norm hx₀).le
  simpa [smul_smul, norm_ne_zero_iff.mpr hx₀] using S.smul_mem hxS (‖x‖ : ℂ)

end StarSubalgebra
