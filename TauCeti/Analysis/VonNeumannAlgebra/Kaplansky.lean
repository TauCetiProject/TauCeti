/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
public import TauCeti.Analysis.InnerProductSpace.Amplification
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology
public import TauCeti.Analysis.LocallyConvex.UltrastrongTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import TauCeti.Analysis.VonNeumannAlgebra.MatrixAmplification
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.LocallyConvex.WeakOperatorTopology
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# The Kaplansky density theorem

Let `S` be a unital star subalgebra of the bounded operators on a complex Hilbert space `H`. By the
bicommutant theorem, `S` is strongly dense in its double commutant `S''`. The **Kaplansky density
theorem** sharpens this to norm balls: for every radius `r : ℝ`, the strong-star, strong, weak,
ultrastrong, and ultraweak closures of `S ∩ closedBall 0 r` all equal `S'' ∩ closedBall 0 r`. In
particular, the strong operator closure of the closed unit ball of `S` is the closed unit ball of
`S''` (`StarSubalgebra.closure_unitBall_eq_unitBall_double_centralizer`), and the same holds for
the self-adjoint parts
(`StarSubalgebra.closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer`) and the
positive parts
(`StarSubalgebra.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer`), as well as at
every radius `r : ℝ` and for `Icc 0 1`.

Combining bounded strong density with the agreement of strong and ultrastrong (respectively, weak
and ultraweak) topologies on norm-bounded sets extends the bicommutant theorem to the ultrastrong
and ultraweak topologies (`StarSubalgebra.closure_image_ultrastrong`,
`StarSubalgebra.closure_image_ultraweak`) and characterizes concrete von Neumann algebras among
unital star subalgebras by weak operator compactness of closed balls of positive radius
(`StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`).

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Theorem 5.3.5.
* V. F. R. Jones, *Von Neumann Algebras*, Theorem 5.2.1 and Corollary 5.2.2.
* J. Peterson, *Notes on von Neumann Algebras*, Theorem 2.6.4.
* C. Houdayer, *An invitation to von Neumann algebras*, lecture notes, Université Paris-Sud
  (2017), Theorem 3.16.
-/

public section

open Filter Metric Set TauCeti
open scoped InnerProduct InnerProductSpace Topology

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Unit-ball Kaplansky density theorems -/

/-- The weak operator closed sets of operators used to cut out the right-hand sides of the
Kaplansky density theorem. -/
private theorem isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H))
    {P : Set (H →L[ℂ] H)} (hP : IsClosed (ContinuousLinearMapWOT.ofCLM '' P)) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      {x | x ∈ S.centralizer.centralizer ∧ x ∈ P ∧ ‖x‖ ≤ 1}) := by
  refine ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
    ?_
  have hball : {x : H →L[ℂ] H | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x; simp
  rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_mem_eq, Set.ofPred_mem_eq, hball,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact S.centralizer.isClosed_image_ofCLM_centralizer.inter
    (hP.inter (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 1).isClosed)

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
    (isClosed_image_toPointwiseConvergenceCLM_inter _
      ContinuousLinearMapWOT.isClosed_image_ofCLM_setOf_isSelfAdjoint)) ?_
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
  have hz' : z ∈ closure ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1) := by
    rw [StarMemClass.closure_inter_selfAdjoint_inter_closedBall_zero ℂ S 1]
    exact ⟨⟨hz, hzsa⟩, mem_closedBall_zero_iff.mpr hz₁⟩
  refine closure_mono (Set.image_mono fun a ha ↦ ?_)
    (image_closure_subset_closure_image q.continuous ⟨z, hz', rfl⟩)
  exact ⟨ha.1.1, ha.1.2, mem_closedBall_zero_iff.mp ha.2⟩

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
    (isClosed_image_toPointwiseConvergenceCLM_inter _
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

/-! ### Shared closure helpers -/

private theorem closure_sot_inter_closedBall_of_unit (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {C : Set (H →L[ℂ] H)} (hC0 : (0 : H →L[ℂ] H) ∈ C)
    (hCsmul : ∀ {t : ℝ} {x : H →L[ℂ] H}, 0 < t → x ∈ C → (t : ℂ) • x ∈ C) {r : ℝ}
    (hclosed : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ C ∩ closedBall 0 r)))
    (hunit : ∀ {b : H →L[ℂ] H}, b ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer → b ∈ C →
      ‖b‖ ≤ 1 → ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          ((S : Set (H →L[ℂ] H)) ∩ C ∩ closedBall 0 1))) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ C ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ C ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  refine subset_antisymm (closure_minimal (Set.image_mono <|
      inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨b, ⟨⟨hb, hbC⟩, hbr⟩, rfl⟩
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact ((closedBall_eq_empty.2 hr).subset hbr).elim
  · rw [closedBall_zero, mem_singleton_iff] at hbr
    subst hbr
    exact subset_closure ⟨0, ⟨⟨S.zero_mem, hC0⟩, mem_closedBall_self le_rfl⟩, rfl⟩
  · have hcb_cc : ((r⁻¹ : ℝ) : ℂ) • b ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
      VonNeumannAlgebra.mem_adjoin_coe.mp
        (SMulMemClass.smul_mem _ (VonNeumannAlgebra.mem_adjoin_coe.mpr hb))
    have hcb1 : ‖((r⁻¹ : ℝ) : ℂ) • b‖ ≤ 1 := by
      rw [mem_closedBall, dist_zero_right] at hbr
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_le_iff₀ hr, mul_one]
      exact hbr
    have hmem := hunit hcb_cc (hCsmul (inv_pos.2 hr) hbC) hcb1
    have hscaled := map_mem_closure (f := fun T : H →Lₚₜ[ℂ] H ↦ (r : ℂ) • T) (by fun_prop) hmem
      (t := q '' ((S : Set (H →L[ℂ] H)) ∩ C ∩ closedBall 0 r)) (by
        rintro _ ⟨a, ⟨⟨ha, haC⟩, har⟩, rfl⟩
        refine ⟨(r : ℂ) • a, ⟨⟨SMulMemClass.smul_mem _ ha, hCsmul hr haC⟩, ?_⟩,
          (map_smul q (r : ℂ) a).symm⟩
        rw [mem_closedBall, dist_zero_right] at har ⊢
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
        exact mul_le_of_le_one_right hr.le har)
    have hrc : (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • b) = b := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
    rwa [← map_smul, hrc] at hscaled

/-! ### Self-adjoint Kaplansky density for arbitrary radii -/

/-- **Self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the strong operator
closure of the self-adjoint elements of `S` in `closedBall 0 r` equals the self-adjoint elements of
`S''` in `closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) := by
  refine S.closure_sot_inter_closedBall_of_unit (IsSelfAdjoint.zero _)
    (fun _ hx ↦ (by simp [IsSelfAdjoint] : IsSelfAdjoint (_ : ℂ)).smul hx) ?_ ?_
  · rw [Set.image_inter (ContinuousLinearMap.toPointwiseConvergenceCLM_injective
          (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)),
      ← S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  · intro b hb hbsa hb1
    have hb_mem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) :=
      S.closure_selfAdjoint_unitBall_eq_selfAdjoint_unitBall_double_centralizer ▸
        ⟨b, ⟨hb, hbsa, hb1⟩, rfl⟩
    refine closure_mono (Set.image_mono (s := {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}) ?_) hb_mem
    rintro x ⟨hx, hxsa, hx1⟩
    exact ⟨⟨hx, hxsa⟩, by simpa using hx1⟩

/-- **Weak operator self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the weak
operator closure of `S ∩ selfAdjoint _ ∩ closedBall 0 r` equals
`S'' ∩ selfAdjoint _ ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) := by
  refine ContinuousLinearMapWOT.closure_image_ofCLM_eq_of_subset_closure_toPointwiseConvergenceCLM
    (inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer)) ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r).ge
  rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
    ← S.closure_image_ofCLM_inter_selfAdjoint]
  exact isClosed_closure.inter
    (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed

/-- **Finite-vector self-adjoint Kaplansky approximation.** Every self-adjoint `x ∈ S''` can be
approximated on finitely many vectors by a self-adjoint `s ∈ S` with `‖s‖ ≤ ‖x‖`. -/
theorem exists_isSelfAdjoint_norm_le_forall_norm_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hxsa : IsSelfAdjoint x)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, IsSelfAdjoint s ∧ ‖s‖ ≤ ‖x‖ ∧ ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  have hmem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall ‖x‖]
    exact ⟨x, ⟨⟨hx, hxsa⟩, by simp⟩, rfl⟩
  obtain ⟨s, ⟨⟨hs, hssa⟩, hsr⟩, hlt⟩ :=
    PointwiseConvergenceCLM.exists_mem_forall_norm_sub_apply_lt_of_mem_closure hmem v hε
  exact ⟨s, hs, hssa, by simpa using hsr, hlt⟩

/-! ### Strong-star, strong, weak, and matrix-amplified Kaplansky density -/

/-- **Strong-star Kaplansky density theorem.** For every radius `r : ℝ`, the closure in the
strong-star topology (simultaneous strong convergence of an operator and its adjoint) of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_strongStar_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  have hclosed : IsClosed (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
      (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
    have hq_closed : IsClosed
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
      rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
      exact isClosed_closure.inter
        (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
    convert hq_closed.preimage
      TauCeti.ContinuousLinearMapStrongStar.continuous_toPointwiseConvergenceCLM using 1
    ext A
    obtain ⟨x, rfl⟩ : ∃ x, TauCeti.ContinuousLinearMapStrongStar.ofCLM x = A := ⟨A.toCLM, rfl⟩
    rw [Set.mem_preimage, hq_inj.mem_set_image,
      TauCeti.ContinuousLinearMapStrongStar.ofCLM_injective.mem_set_image]
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩
  -- Dilate `x` to `[0, x; star x, 0]` on the `2`-fold Hilbert sum `PiLp 2 (fun _ : Fin 2 => H)`.
  let S₂ := S.piLpMatrix (Fin 2)
  set q₂ := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (PiLp 2 (fun _ : Fin 2 => H)) (PiLp 2 (fun _ : Fin 2 => H))
  have hx_star : star x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    StarMemClass.star_mem_centralizer_centralizer S hx
  let X : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
    PiLp.singleEntryCLM (0 : Fin 2) 1 x + PiLp.singleEntryCLM 1 0 (star x)
  have hX_cc : X ∈ (S₂ : Set _).centralizer.centralizer := by
    rw [S.mem_centralizer_centralizer_piLpMatrix_iff]
    intro i j; fin_cases i <;> fin_cases j <;> simp [X, hx, hx_star, Set.zero_mem_centralizer]
  have hqX : q₂ X ∈ closure (q₂ '' ((S₂ : Set _) ∩
      (selfAdjoint (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) : Set _) ∩
        closedBall 0 r)) := by
    rw [S₂.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r]
    refine ⟨X, ⟨⟨hX_cc, PiLp.isSelfAdjoint_singleEntryCLM_add_singleEntryCLM_star 0 1 x⟩, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hxr ⊢
    rwa [PiLp.norm_singleEntryCLM_add_singleEntryCLM_star (by decide : (0 : Fin 2) ≠ 1) x]
  obtain ⟨l, hl, hlS, hlim⟩ :=
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff.mp hqX
  -- The `(0, 1)` entries of the approximants converge strong-star to `x`, using `(1, 0)` for `x†`.
  have := hl
  refine mem_closure_of_tendsto (b := l) (f := fun Y :
      PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) ↦
      TauCeti.ContinuousLinearMapStrongStar.ofCLM (Y.piLpEntry 0 1)) ?_ ?_
  · rw [TauCeti.ContinuousLinearMapStrongStar.tendsto_iff_forall_tendsto]
    refine ⟨fun u ↦ ?_, fun v ↦ ?_⟩
    · have hx01 : (X.piLpEntry 0 1) u = x u := by simp [X]
      rw [← hx01]
      simpa [ContinuousLinearMap.piLpEntry_apply, Function.comp_def] using
        ((PiLp.continuous_apply 2 _ 0).tendsto _).comp (hlim (PiLp.single 2 1 u))
    · have hx10 : (X.piLpEntry 1 0) v = (x†) v := by
        simp [X, ContinuousLinearMap.star_eq_adjoint]
      have hlim' : Tendsto (fun Y : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) ↦
          Y.piLpEntry 1 0 v) l (𝓝 ((x†) v)) := by
        rw [← hx10]
        simpa [ContinuousLinearMap.piLpEntry_apply, Function.comp_def] using
          ((PiLp.continuous_apply 2 _ 1).tendsto _).comp (hlim (PiLp.single 2 0 v))
      refine hlim'.congr' (hlS.mono fun Y ⟨⟨_, hYsa⟩, _⟩ ↦ ?_)
      simp [← ContinuousLinearMap.star_eq_adjoint, hYsa.star_piLpEntry 0 1]
  · filter_upwards [hlS] with Y ⟨⟨hY, _⟩, hYr⟩
    refine ⟨Y.piLpEntry 0 1, ⟨(mem_piLpMatrix.1 hY) 0 1, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hYr ⊢
    exact (Y.norm_piLpEntry_le 0 1).trans hYr

/-- **Kaplansky's density theorem for closed norm balls.** For every radius `r : ℝ`, the strong
operator closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hclosed : IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : TauCeti.ContinuousLinearMapStrongStar.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) :=
    S.closure_image_strongStar_ofCLM_inter_closedBall r ▸ ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def] using mem_closure_image
    TauCeti.ContinuousLinearMapStrongStar.continuous_toPointwiseConvergenceCLM.continuousAt hx'

/-- **The Kaplansky density theorem.** For a unital star subalgebra `S` of `B(H)`, the strong
operator closure of the closed unit ball of `S` is the closed unit ball of its double commutant
`S''`. -/
theorem closure_unitBall_eq_unitBall_double_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  have h1 : {x : H →L[ℂ] H | x ∈ S ∧ ‖x‖ ≤ 1} = (S : Set (H →L[ℂ] H)) ∩ closedBall 0 1 := by
    ext; simp
  have h2 : {x : H →L[ℂ] H | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} =
      (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 1 := by
    ext; simp
  rw [h1, h2]
  exact S.closure_image_toPointwiseConvergenceCLM_inter_closedBall 1

/-- **Weak operator Kaplansky density theorem.** For every radius `r : ℝ`, the weak operator
closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  refine ContinuousLinearMapWOT.closure_image_ofCLM_eq_of_subset_closure_toPointwiseConvergenceCLM
    (inter_subset_inter_left _ Set.subset_centralizer_centralizer) ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r).ge
  rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact ((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).inter
    (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed

/-- **Matrix amplification of Kaplansky's density theorem for closed balls.** On the finite Hilbert
sum `PiLp 2 (fun _ : ι => H)`, for every radius `r : ℝ`, the strong operator closure of the closed
ball of operators with matrix entries in `A` equals the closed ball of operators with matrix entries
in `A''`. -/
theorem closure_image_toPointwiseConvergenceCLM_piLpEntry_inter_closedBall
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        ({T | ∀ i j, T.piLpEntry i j ∈ A} ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        ({T | ∀ i j, T.piLpEntry i j ∈ (A : Set (H →L[ℂ] H)).centralizer.centralizer} ∩
          closedBall 0 r) := by
  have h := (A.piLpMatrix ι).closure_image_toPointwiseConvergenceCLM_inter_closedBall r
  have h1 : (A.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) =
      {T | ∀ i j, T.piLpEntry i j ∈ A} := by
    ext T
    exact StarSubalgebra.mem_piLpMatrix
  have h2 : (A.piLpMatrix ι :
        Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))).centralizer.centralizer =
      {T | ∀ i j, T.piLpEntry i j ∈ (A : Set (H →L[ℂ] H)).centralizer.centralizer} := by
    ext T
    simp only [A.mem_centralizer_centralizer_piLpMatrix_iff, Set.mem_ofPred_eq]
  rwa [h2, h1] at h

/-- **Matrix amplification of Kaplansky's density theorem.** On the finite Hilbert sum
`PiLp 2 (fun _ : ι => H)`, the strong operator closure of the contractions whose matrix entries lie
in `A` is the set of contractions whose matrix entries lie in `A''`. -/
theorem closure_unitBall_piLpEntry_eq_unitBall_double_centralizer
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ A) ∧ ‖T‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ (A : Set (H →L[ℂ] H)).centralizer.centralizer) ∧
          ‖T‖ ≤ 1} := by
  have hball (P : (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) → Prop) :
      {T | P T ∧ ‖T‖ ≤ 1} = {T | P T} ∩ closedBall 0 1 := by ext; simp
  simpa only [hball] using
    A.closure_image_toPointwiseConvergenceCLM_piLpEntry_inter_closedBall ι 1

/-- **Finite-vector strong-star Kaplansky approximation.** Every `x ∈ S''` can be approximated
simultaneously with its adjoint on finitely many vectors by `s ∈ S` satisfying `‖s‖ ≤ ‖x‖`. -/
theorem exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖s‖ ≤ ‖x‖ ∧
      ∀ i, ‖x (v i) - s (v i)‖ < ε ∧ ‖star x (v i) - star s (v i)‖ < ε := by
  have hmem : TauCeti.ContinuousLinearMapStrongStar.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_strongStar_ofCLM_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  let U : Set (TauCeti.ContinuousLinearMapStrongStar ℂ H H) :=
    ⋂ i, {T | ‖x (v i) - T.toCLM (v i)‖ < ε ∧ ‖(x†) (v i) - (T.toCLM†) (v i)‖ < ε}
  have hU_open : IsOpen U := isOpen_iInter_of_finite fun i ↦
    (isOpen_lt (continuous_const.sub
      (TauCeti.ContinuousLinearMapStrongStar.continuous_toCLM_apply (v i))).norm
        continuous_const).inter
      (isOpen_lt (continuous_const.sub
        (TauCeti.ContinuousLinearMapStrongStar.continuous_adjoint_apply (v i))).norm
        continuous_const)
  have hmemU : TauCeti.ContinuousLinearMapStrongStar.ofCLM x ∈ U :=
    Set.mem_iInter.2 fun i ↦ by simp [hε]
  obtain ⟨_, ⟨hU, s, ⟨hs, hsr⟩, rfl⟩⟩ := mem_closure_iff.1 hmem U hU_open hmemU
  refine ⟨s, hs, by simpa using hsr, fun i ↦ ?_⟩
  simpa only [Set.mem_ofPred_eq, ContinuousLinearMap.star_eq_adjoint] using Set.mem_iInter.1 hU i

/-! ### Positive-part Kaplansky density for arbitrary radii -/

/-- **Positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The strong operator
closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) := by
  refine S.closure_sot_inter_closedBall_of_unit (mem_Ici.2 le_rfl)
    (fun {t x} ht hx ↦ mem_Ici.2 <| by
      have htx : (t : ℂ) • x = t • x := (RCLike.real_smul_eq_coe_smul (K := ℂ) t x).symm
      rw [htx]
      exact smul_nonneg ht.le hx) ?_ ?_
  · have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
      (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
    have hIci_closed : IsClosed
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          Ici (0 : H →L[ℂ] H)) :=
      ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
        ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici
    rw [Set.image_inter hq_inj, Set.image_inter hq_inj,
      ← S.closure_image_toPointwiseConvergenceCLM]
    exact (isClosed_closure.inter hIci_closed).inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  · intro b hb hb0 hb1
    have hb_mem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          {x | x ∈ S ∧ 0 ≤ x ∧ ‖x‖ ≤ 1}) :=
      S.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer ▸
        ⟨b, ⟨hb, hb0, hb1⟩, rfl⟩
    refine closure_mono (Set.image_mono (s := {x | x ∈ S ∧ 0 ≤ x ∧ ‖x‖ ≤ 1}) ?_) hb_mem
    rintro x ⟨hx, hx0, hx1⟩
    exact ⟨⟨hx, hx0⟩, by simpa using hx1⟩

/-- **Positive-part Kaplansky density theorem.** The strong operator closure of the positive
contractions `S ∩ Icc 0 1` equals the positive contractions `S'' ∩ Icc 0 1`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  have hIcc : Ici (0 : H →L[ℂ] H) ∩ closedBall 0 1 = Icc 0 1 := by
    ext; simp only [mem_inter_iff, mem_Ici, mem_closedBall_zero_iff,
      CStarAlgebra.mem_Icc_iff_norm_le_one]
  simpa only [Set.inter_assoc, hIcc] using
    S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall 1

/-- **Weak operator positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The
weak operator closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) := by
  refine ContinuousLinearMapWOT.closure_image_ofCLM_eq_of_subset_closure_toPointwiseConvergenceCLM
    (inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer)) ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall r).ge
  rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact (((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).inter
    ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici).inter
    (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed

/-- **Weak operator positive-part Kaplansky density theorem.** The weak operator closure of the
positive contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ofCLM_inter_Icc_zero_one (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  have hIcc : Ici (0 : H →L[ℂ] H) ∩ closedBall 0 1 = Icc 0 1 := by
    ext; simp only [mem_inter_iff, mem_Ici, mem_closedBall_zero_iff,
      CStarAlgebra.mem_Icc_iff_norm_le_one]
  simpa only [Set.inter_assoc, hIcc] using
    S.closure_image_ofCLM_inter_Ici_zero_inter_closedBall 1

/-- **Finite-vector positive Kaplansky approximation.** Every positive `x ∈ S''` can be approximated
on finitely many vectors by a positive `s ∈ S` with `‖s‖ ≤ ‖x‖`. -/
theorem exists_nonneg_norm_le_forall_norm_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hx0 : 0 ≤ x)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, 0 ≤ s ∧ ‖s‖ ≤ ‖x‖ ∧ ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  have hmem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall ‖x‖]
    exact ⟨x, ⟨⟨hx, hx0⟩, by simp⟩, rfl⟩
  obtain ⟨s, ⟨⟨hs, hs0⟩, hsr⟩, hlt⟩ :=
    PointwiseConvergenceCLM.exists_mem_forall_norm_sub_apply_lt_of_mem_closure hmem v hε
  exact ⟨s, hs, hs0, by simpa using hsr, hlt⟩

/-! ### Ultrastrong and ultraweak Kaplansky density and bicommutant closures -/

/-- **Ultrastrong Kaplansky density theorem.** For every radius `r : ℝ`, the ultrastrong closure of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrong_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) :=
  ContinuousLinearMapUltrastrong.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r)

/-- **Ultraweak Kaplansky density theorem.** For every radius `r : ℝ`, the ultraweak closure of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ultraweak_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) :=
  ContinuousLinearMapUltraweak.closure_image_ofCLM_of_closure_image_WOT
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_ofCLM_inter_closedBall r)

/-- **Ultrastrong self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the
ultrastrong closure of `S ∩ selfAdjoint _ ∩ closedBall 0 r` equals
`S'' ∩ selfAdjoint _ ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrong_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) :=
  ContinuousLinearMapUltrastrong.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r)

/-- **Ultraweak self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the ultraweak
closure of `S ∩ selfAdjoint _ ∩ closedBall 0 r` equals `S'' ∩ selfAdjoint _ ∩ closedBall 0 r`. -/
theorem closure_image_ultraweak_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) :=
  ContinuousLinearMapUltraweak.closure_image_ofCLM_of_closure_image_WOT
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_ofCLM_inter_selfAdjoint_inter_closedBall r)

/-- **Ultrastrong positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The
ultrastrong closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrong_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) :=
  ContinuousLinearMapUltrastrong.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall r)

/-- **Ultrastrong positive-part Kaplansky density theorem.** The ultrastrong closure of the positive
contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ultrastrong_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  have hIcc : Ici (0 : H →L[ℂ] H) ∩ closedBall 0 1 = Icc 0 1 := by
    ext; simp only [mem_inter_iff, mem_Ici, mem_closedBall_zero_iff,
      CStarAlgebra.mem_Icc_iff_norm_le_one]
  simpa only [Set.inter_assoc, hIcc] using
    S.closure_image_ultrastrong_inter_Ici_zero_inter_closedBall 1

/-- **Ultraweak positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The
ultraweak closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_ultraweak_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) :=
  TauCeti.ContinuousLinearMapUltraweak.closure_image_ofCLM_of_closure_image_WOT
    (fun _ ⟨_, hT⟩ ↦ by simpa using hT)
    (S.closure_image_ofCLM_inter_Ici_zero_inter_closedBall r)

/-- **Ultraweak positive-part Kaplansky density theorem.** The ultraweak closure of the positive
contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ultraweak_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  have hIcc : Ici (0 : H →L[ℂ] H) ∩ closedBall 0 1 = Icc 0 1 := by
    ext; simp only [mem_inter_iff, mem_Ici, mem_closedBall_zero_iff,
      CStarAlgebra.mem_Icc_iff_norm_le_one]
  simpa only [Set.inter_assoc, hIcc] using
    S.closure_image_ultraweak_inter_Ici_zero_inter_closedBall 1

/-- **Ultrastrong bicommutant closure.** The ultrastrong closure of a unital star subalgebra `S`
equals its double commutant `S''`. -/
theorem closure_image_ultrastrong (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[ℂ] H))) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
  have hclosed : IsClosed (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
      (S : Set (H →L[ℂ] H)).centralizer.centralizer) := by
    convert ((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).preimage
      (TauCeti.ContinuousLinearMapUltraweak.continuous_toWOT.comp
        TauCeti.ContinuousLinearMapUltraweak.continuous_ofUltrastrong) using 1
    ext A
    obtain ⟨x, rfl⟩ : ∃ x, TauCeti.ContinuousLinearMapUltrastrong.ofCLM x = A := ⟨A.toCLM, rfl⟩
    simp [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective.mem_set_image]
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : TauCeti.ContinuousLinearMapUltrastrong.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_ultrastrong_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  exact closure_mono (Set.image_mono inter_subset_left) hx'

/-- **Ultraweak bicommutant closure.** The ultraweak closure of a unital star subalgebra `S` equals
its double commutant `S''`. -/
theorem closure_image_ultraweak (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM '' (S : Set (H →L[ℂ] H))) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
  have hclosed : IsClosed (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
      (S : Set (H →L[ℂ] H)).centralizer.centralizer) := by
    convert ((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).preimage
      TauCeti.ContinuousLinearMapUltraweak.continuous_toWOT using 1
    ext A
    obtain ⟨x, rfl⟩ : ∃ x, TauCeti.ContinuousLinearMapUltraweak.ofCLM x = A := ⟨A.toCLM, rfl⟩
    simp [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
      TauCeti.ContinuousLinearMapUltraweak.ofCLM_injective.mem_set_image]
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : TauCeti.ContinuousLinearMapUltrastrong.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[ℂ] H))) :=
    S.closure_image_ultrastrong ▸ ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def] using
    mem_closure_image TauCeti.ContinuousLinearMapUltraweak.continuous_ofUltrastrong.continuousAt hx'

/-- A unital star subalgebra equals its double commutant if and only if it is ultrastrongly
closed. -/
theorem double_commutant_iff_isClosed_image_ultrastrong (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[ℂ] H))) := by
  rw [← closure_eq_iff_isClosed, S.closure_image_ultrastrong,
    (Set.image_injective.mpr TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective).eq_iff]

/-- A unital star subalgebra equals its double commutant if and only if it is ultraweakly
closed. -/
theorem double_commutant_iff_isClosed_image_ultraweak (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (TauCeti.ContinuousLinearMapUltraweak.ofCLM '' (S : Set (H →L[ℂ] H))) := by
  rw [← closure_eq_iff_isClosed, S.closure_image_ultraweak,
    (Set.image_injective.mpr TauCeti.ContinuousLinearMapUltraweak.ofCLM_injective).eq_iff]

/-! ### Bounded-ball closedness and WOT-compactness criteria for `S'' = S` -/

/-- For `r > 0`, a unital star subalgebra equals its double commutant if and only if its closed
ball of radius `r` is strong operator closed. -/
theorem double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  refine ⟨fun hS ↦ ?_, fun hcl ↦ ?_⟩
  · rw [Set.image_inter hq_inj]
    exact (S.double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM.mp hS).inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  · have hball : (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r =
        (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r :=
      Set.image_injective.mpr hq_inj
        (by rw [← S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r, hcl.closure_eq])
    refine subset_antisymm (fun x hx ↦ ?_) Set.subset_centralizer_centralizer
    by_cases hx0 : x = 0
    · exact hx0 ▸ S.zero_mem
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      let c : ℂ := ((r / ‖x‖ : ℝ) : ℂ)
      have hcx_mem : c • x ∈ (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r := hball ▸
        ⟨VonNeumannAlgebra.mem_adjoin_coe.mp
          (SMulMemClass.smul_mem c (VonNeumannAlgebra.mem_adjoin_coe.mpr hx)),
        by simp [c, norm_smul, div_mul_cancel₀ _ hxn.ne', abs_of_pos hr]⟩
      exact inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (div_pos hr hxn).ne') x ▸
        SMulMemClass.smul_mem c⁻¹ hcx_mem.1

/-- For `r > 0`, a unital star subalgebra equals its double commutant if and only if its closed
ball of radius `r` is weak operator closed. -/
theorem double_commutant_iff_isClosed_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  refine ⟨fun hS ↦ ?_, fun hcl ↦ ?_⟩
  · rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
    exact (S.double_commutant_iff_isClosed_image_ofCLM.mp hS).inter
      (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed
  · rw [S.double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM_inter_closedBall hr]
    have hball : (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r =
        (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r :=
      Set.image_injective.mpr ContinuousLinearMapWOT.ofCLM_injective
        (by rw [← S.closure_image_ofCLM_inter_closedBall r, hcl.closure_eq])
    rw [← hball, ← S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r]
    exact isClosed_closure

/-- **Weak-compact closed-ball characterization of von Neumann algebras** (Jones, Corollary 5.2.2).
For `r > 0`, a unital star subalgebra `S` equals its double commutant if and only if its closed
ball of radius `r` is weak operator compact. -/
theorem double_commutant_iff_isCompact_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsCompact (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [S.double_commutant_iff_isClosed_image_ofCLM_inter_closedBall hr]
  exact ⟨fun hcl ↦ (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).of_isClosed_subset
    hcl (Set.image_mono inter_subset_right), IsCompact.isClosed⟩

end StarSubalgebra

/-! ### Consequences for concrete von Neumann algebras -/

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra is closed in the ultrastrong operator topology. -/
theorem isClosed_image_ultrastrong (M : VonNeumannAlgebra H) :
    IsClosed (TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (M : Set (H →L[ℂ] H))) :=
  M.toStarSubalgebra.double_commutant_iff_isClosed_image_ultrastrong.mp M.centralizer_centralizer

/-- A concrete von Neumann algebra is closed in the ultraweak operator topology. -/
theorem isClosed_image_ultraweak (M : VonNeumannAlgebra H) :
    IsClosed (TauCeti.ContinuousLinearMapUltraweak.ofCLM '' (M : Set (H →L[ℂ] H))) :=
  M.toStarSubalgebra.double_commutant_iff_isClosed_image_ultraweak.mp M.centralizer_centralizer

/-- The von Neumann algebra generated by `s` is the ultrastrong closure of the star algebra
generated by `s`. -/
theorem image_ultrastrong_adjoin_eq_closure (s : Set (H →L[ℂ] H)) :
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (adjoin s : Set (H →L[ℂ] H)) =
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.closure_image_ultrastrong, ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- The von Neumann algebra generated by `s` is the ultraweak closure of the star algebra
generated by `s`. -/
theorem image_ultraweak_adjoin_eq_closure (s : Set (H →L[ℂ] H)) :
    TauCeti.ContinuousLinearMapUltraweak.ofCLM '' (adjoin s : Set (H →L[ℂ] H)) =
      closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.closure_image_ultraweak, ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
strong operator closure of the closed ball of the star algebra generated by `s`. -/
theorem image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure
    (s : Set (H →L[ℂ] H)) (r : ℝ) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_toPointwiseConvergenceCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
weak operator closure of the closed ball of the star algebra generated by `s`. -/
theorem image_ofCLM_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    ContinuousLinearMapWOT.ofCLM '' ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (ContinuousLinearMapWOT.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ofCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
ultrastrong closure of the closed ball of the star algebra generated by `s`. -/
theorem image_ultrastrong_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ultrastrong_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
ultraweak closure of the closed ball of the star algebra generated by `s`. -/
theorem image_ultraweak_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ultraweak_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- An operator belongs to the von Neumann algebra generated by `s` if and only if it can be
approximated on every finite set of vectors by elements of `StarAlgebra.adjoin ℂ s`. -/
theorem mem_adjoin_iff_forall_exists_norm_sub_apply_lt
    {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ adjoin s ↔
      ∀ (v : Finset H) {ε : ℝ}, 0 < ε →
        ∃ t ∈ StarAlgebra.adjoin ℂ s, ∀ w ∈ v, ‖x w - t w‖ < ε := by
  rw [← SetLike.mem_coe,
    ← (ContinuousLinearMap.toPointwiseConvergenceCLM_injective
      (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)).mem_set_image,
    image_toPointwiseConvergenceCLM_adjoin_eq_closure,
    ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm]
  simp only [SetLike.mem_coe]

/-- **Bounded strong-star approximation in a generated von Neumann algebra.** Every element
`x ∈ adjoin s` can be approximated simultaneously with its adjoint on finitely many vectors by
`t ∈ StarAlgebra.adjoin ℂ s` satisfying `‖t‖ ≤ ‖x‖`. -/
theorem exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt_of_mem_adjoin
    {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} (hx : x ∈ adjoin s)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ StarAlgebra.adjoin ℂ s, ‖t‖ ≤ ‖x‖ ∧
      ∀ i, ‖x (v i) - t (v i)‖ < ε ∧ ‖star x (v i) - star t (v i)‖ < ε := by
  have hx_cc : x ∈ (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← mem_adjoin_coe, adjoin_starAlgebraAdjoin]
    exact hx
  exact (StarAlgebra.adjoin ℂ s).exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt
    hx_cc v hε

end VonNeumannAlgebra
