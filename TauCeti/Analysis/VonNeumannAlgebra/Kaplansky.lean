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
public import TauCeti.Analysis.Normed.Module.Ball.SelfAdjoint
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import TauCeti.Analysis.VonNeumannAlgebra.MatrixAmplification
import TauCeti.Algebra.Star.Basic
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
the self-adjoint parts at any radius `r`
(`StarSubalgebra.closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer`)
and the positive parts
(`StarSubalgebra.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer`),
as well as at every radius `r : ℝ` and for `Icc 0 1`, and in the strong-star topology
(`StarSubalgebra.closure_strongStar_unitBall_eq_unitBall_double_centralizer`,
`StarSubalgebra.closure_image_strongStar_ofCLM_inter_closedBall`).

Combining bounded strong (respectively, weak) density with the agreement of strong and ultrastrong
(respectively, weak and ultraweak) topologies on norm-bounded sets yields the bounded ultrastrong
and ultraweak Kaplansky density theorems
(`StarSubalgebra.closure_image_ultrastrongOfCLM_inter_closedBall`,
`StarSubalgebra.closure_image_ultraweakOfCLM_inter_closedBall`, together with their self-adjoint
and positive-part variants) and characterizes concrete von Neumann algebras among unital star
subalgebras by weak operator compactness of closed balls of positive radius
(`StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`), as well as the
matrix-amplified strong operator and strong-star Kaplansky density theorems
(`StarSubalgebra.closure_image_toPointwiseConvergenceCLM_piLpMatrix_inter_closedBall`,
`StarSubalgebra.closure_image_strongStar_ofCLM_piLpMatrix_inter_closedBall`). For the unbounded
ultrastrong and ultraweak bicommutant theorems themselves, see
`StarSubalgebra.closure_image_ultrastrongOfCLM` and
`StarSubalgebra.closure_image_ultraweakOfCLM` in
`TauCeti.Analysis.VonNeumannAlgebra.UltraweakClosure`.

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

/-! ### Unit-ball and self-adjoint Kaplansky density theorems -/

/-- The weak operator closed sets of operators used to cut out the right-hand sides of the
Kaplansky density theorem. -/
private theorem isClosed_image_ofCLM_inter (S : Set (H →L[ℂ] H)) (r : ℝ)
    {P : Set (H →L[ℂ] H)} (hP : IsClosed (ContinuousLinearMapWOT.ofCLM '' P)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      (S.centralizer.centralizer ∩ P ∩ closedBall 0 r)) := by
  rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
    Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
  exact (S.centralizer.isClosed_image_ofCLM_centralizer.inter hP).inter
    (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed

private theorem isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H))
    {P : Set (H →L[ℂ] H)} (hP : IsClosed (ContinuousLinearMapWOT.ofCLM '' P)) (r : ℝ) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S.centralizer.centralizer ∩ P ∩ closedBall 0 r)) :=
  ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
    (isClosed_image_ofCLM_inter S r hP)

private theorem isClosed_image_toPointwiseConvergenceCLM_double_centralizer_inter_closedBall
    (S : Set (H →L[ℂ] H)) (r : ℝ) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S.centralizer.centralizer ∩ closedBall 0 r)) := by
  simpa only [Set.inter_univ] using
    isClosed_image_toPointwiseConvergenceCLM_inter S (P := Set.univ)
      (by
        rw [Set.image_univ, ContinuousLinearMapWOT.ofCLM_surjective.range_eq]
        exact isClosed_univ) r

omit [CompleteSpace H] in
private theorem setOf_mem_and_pred_and_norm_le_eq_inter
    (A : Set (H →L[ℂ] H)) (P : (H →L[ℂ] H) → Prop) (r : ℝ) :
    {x | x ∈ A ∧ P x ∧ ‖x‖ ≤ r} = A ∩ {x | P x} ∩ closedBall 0 r := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
    and_assoc]

omit [CompleteSpace H] in
private theorem setOf_mem_and_norm_le_eq_inter
    (A : Set (H →L[ℂ] H)) (r : ℝ) :
    {x | x ∈ A ∧ ‖x‖ ≤ r} = A ∩ closedBall 0 r := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]

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
    (by
      rw [setOf_mem_and_pred_and_norm_le_eq_inter]
      exact isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H))
        ContinuousLinearMapWOT.isClosed_image_ofCLM_setOf_isSelfAdjoint r)) ?_
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
    (by
      rw [setOf_mem_and_pred_and_norm_le_eq_inter]
      exact isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H))
        (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := 0)) 1)) ?_
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

/-! ### Strong-star forms for self-adjoint and positive parts -/

/-- **The Kaplansky density theorem for self-adjoint parts, strong-star form.** For a unital star
subalgebra `S` of `B(H)`, the strong-star closure of the self-adjoint elements of norm at most `r`
of `S` is the set of self-adjoint elements of norm at most `r` of its double commutant `S''`. -/
theorem closure_strongStar_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ S ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ r}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ r} :=
  ContinuousLinearMapStrongStar.closure_image_ofCLM_eq_of_isStarNormal
    (fun _ hx => hx.2.1.isStarNormal)
    (S.closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer r)

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

/-! ### Shared closure helpers -/

private theorem smul_mem_centralizer_centralizer_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    {t s : ℝ} (ht : 0 < t) (hts : t * ‖x‖ ≤ s) :
    (t : ℂ) • x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 s := by
  refine ⟨Set.smul_mem_centralizer (t : ℂ) hx, ?_⟩
  simpa [norm_smul, abs_of_pos ht] using hts

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
  · obtain ⟨hcb_cc, hcb1⟩ := S.smul_mem_centralizer_centralizer_inter_closedBall hb
      (inv_pos.2 hr) (inv_mul_le_one_of_le₀ (mem_closedBall_zero_iff.1 hbr) hr.le)
    have hmem := hunit hcb_cc (hCsmul (inv_pos.2 hr) hbC) (mem_closedBall_zero_iff.1 hcb1)
    have hscaled := map_mem_closure (f := fun T : H →Lₚₜ[ℂ] H ↦ (r : ℂ) • T) (by fun_prop) hmem
      (t := q '' ((S : Set (H →L[ℂ] H)) ∩ C ∩ closedBall 0 r)) (by
        rintro _ ⟨a, ⟨⟨ha, haC⟩, har⟩, rfl⟩
        refine ⟨(r : ℂ) • a, ⟨⟨SMulMemClass.smul_mem _ ha, hCsmul hr haC⟩, ?_⟩,
          (map_smul q (r : ℂ) a).symm⟩
        simpa [norm_smul, abs_of_pos hr] using
          mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.1 har))
    have hrc : (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • b) = b := by simp [smul_smul, hr.ne']
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
  have hsa : {x : H →L[ℂ] H | IsSelfAdjoint x} = (selfAdjoint (H →L[ℂ] H) : Set _) := rfl
  simpa only [← SetLike.mem_coe, setOf_mem_and_pred_and_norm_le_eq_inter, hsa] using
    S.closure_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer r

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

private theorem isClosed_image_strongStar_ofCLM_double_centralizer_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    IsClosed (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) :=
  ContinuousLinearMapStrongStar.isClosed_image_ofCLM_of_isClosed_image_wot <| by
    simpa only [Set.inter_univ] using isClosed_image_ofCLM_inter (S : Set (H →L[ℂ] H)) r
      (P := Set.univ)
      (by simp [Set.image_univ_of_surjective ContinuousLinearMapWOT.ofCLM_surjective])

private theorem dilation_mem_piLpMatrix_double_centralizer_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H} {r : ℝ}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hxr : x ∈ closedBall 0 r) :
    PiLp.singleEntryCLM (0 : Fin 2) 1 x + PiLp.singleEntryCLM 1 0 (star x) ∈
      ((S.piLpMatrix (Fin 2) :
          Set (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
            PiLp 2 (fun _ : Fin 2 => H))).centralizer.centralizer ∩
        (selfAdjoint (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) : Set _) ∩
        closedBall 0 r) := by
  have hx_star : star x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    StarMemClass.star_mem_centralizer_centralizer S hx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [S.mem_centralizer_centralizer_piLpMatrix_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hx, hx_star, Set.zero_mem_centralizer]
  · simp [selfAdjoint.mem_iff, PiLp.star_singleEntryCLM, add_comm]
  · rw [mem_closedBall, dist_zero_right] at hxr ⊢
    rwa [PiLp.norm_singleEntryCLM_add_singleEntryCLM_star (by decide : (0 : Fin 2) ≠ 1) x]

/-- **Strong-star Kaplansky density theorem.** For every radius `r : ℝ`, the closure in the
strong-star topology (simultaneous strong convergence of an operator and its adjoint) of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_strongStar_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      (S.isClosed_image_strongStar_ofCLM_double_centralizer_inter_closedBall r)) ?_
  rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩
  -- `[[0, x], [x⋆, 0]]` is a self-adjoint element of norm `≤ r` in the double commutant of `M₂(S)`.
  let S₂ := S.piLpMatrix (Fin 2)
  let X := PiLp.singleEntryCLM (0 : Fin 2) 1 x + PiLp.singleEntryCLM 1 0 (star x)
  have hXS : TauCeti.ContinuousLinearMapStrongStar.ofCLM X ∈
      closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        {Y | Y ∈ S₂ ∧ IsSelfAdjoint Y ∧ ‖Y‖ ≤ r}) := by
    rw [closure_strongStar_selfAdjoint_closedBall_eq_selfAdjoint_closedBall_double_centralizer S₂ r]
    obtain ⟨⟨hX, hXsa⟩, hXr⟩ :=
      S.dilation_mem_piLpMatrix_double_centralizer_selfAdjoint_inter_closedBall hx hxr
    exact ⟨X, ⟨hX, hXsa, mem_closedBall_zero_iff.mp hXr⟩, rfl⟩
  -- Taking the `(0, 1)` entry is strong-star continuous and sends approximants into
  -- `S ∩ closedBall 0 r`.
  have hx01 : TauCeti.ContinuousLinearMapStrongStar.ofCLM
      ((TauCeti.ContinuousLinearMapStrongStar.ofCLM X).toCLM.piLpEntry (0 : Fin 2) 1) =
      TauCeti.ContinuousLinearMapStrongStar.ofCLM x := by
    simp [X]
  rw [← hx01]
  refine map_mem_closure
    (f := fun Y : TauCeti.ContinuousLinearMapStrongStar ℂ (PiLp 2 (fun _ : Fin 2 => H))
        (PiLp 2 (fun _ : Fin 2 => H)) =>
      TauCeti.ContinuousLinearMapStrongStar.ofCLM (Y.toCLM.piLpEntry (0 : Fin 2) 1))
    (TauCeti.ContinuousLinearMapStrongStar.continuous_piLpEntry (0 : Fin 2) 1) hXS ?_
  rintro _ ⟨Y, ⟨hY, _, hYr⟩, rfl⟩
  exact ⟨Y.piLpEntry 0 1, ⟨(mem_piLpMatrix.mp hY) 0 1,
    mem_closedBall_zero_iff.mpr ((Y.norm_piLpEntry_le 0 1).trans hYr)⟩, rfl⟩

/-- **The Kaplansky density theorem, strong-star form.** For a unital star subalgebra `S` of
`B(H)`, the strong-star closure of the closed unit ball of `S` is the closed unit ball of its double
commutant `S''`. -/
theorem closure_strongStar_unitBall_eq_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapStrongStar.ofCLM '' {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMapStrongStar.ofCLM ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  simp only [← SetLike.mem_coe, setOf_mem_and_norm_le_eq_inter]
  exact S.closure_image_strongStar_ofCLM_inter_closedBall 1

/-- **Kaplansky's density theorem for closed norm balls.** For every radius `r : ℝ`, the strong
operator closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      (isClosed_image_toPointwiseConvergenceCLM_double_centralizer_inter_closedBall
        (S : Set (H →L[ℂ] H)) r)) ?_
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
  simp only [← SetLike.mem_coe, setOf_mem_and_norm_le_eq_inter]
  exact S.closure_image_toPointwiseConvergenceCLM_inter_closedBall 1

/-- **Matrix-amplified Kaplansky density theorem for closed norm balls.** On the finite Hilbert
sum `PiLp 2 (fun _ : ι => H)`, for every radius `r : ℝ`, the strong operator closure of
`S.piLpMatrix ι ∩ closedBall 0 r` equals the closed ball of operators whose matrix entries lie in
`S''`. -/
theorem closure_image_toPointwiseConvergenceCLM_piLpMatrix_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        ((S.piLpMatrix ι :
          Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) ∩
          closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        ({T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) |
          ∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer} ∩
          closedBall 0 r) := by
  convert (S.piLpMatrix ι).closure_image_toPointwiseConvergenceCLM_inter_closedBall r using 3
  ext T
  exact S.mem_centralizer_centralizer_piLpMatrix_iff.symm

/-- **Matrix-amplified strong-star Kaplansky density theorem.** On the finite Hilbert sum
`PiLp 2 (fun _ : ι => H)`, for every radius `r : ℝ`, the strong-star closure of
`S.piLpMatrix ι ∩ closedBall 0 r` equals the closed ball of operators whose matrix entries lie in
`S''`. -/
theorem closure_image_strongStar_ofCLM_piLpMatrix_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((S.piLpMatrix ι :
          Set (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) ∩
          closedBall 0 r)) =
      TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ({T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) |
          ∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer} ∩
          closedBall 0 r) := by
  convert (S.piLpMatrix ι).closure_image_strongStar_ofCLM_inter_closedBall r using 3
  ext T
  exact S.mem_centralizer_centralizer_piLpMatrix_iff.symm

/-- **The Kaplansky density theorem for matrix amplifications, strong-star form.** For a unital
star subalgebra `S` of `B(H)` and a finite index type `ι`, the strong-star closure of the closed
unit ball of the matrix amplification `Mᵢ(S)` consists of the contractions on the Hilbert sum
`PiLp 2 (fun _ : ι => H)` all of whose matrix entries lie in `S''`. -/
theorem closure_strongStar_piLpMatrix_unitBall_eq_unitBall_piLpEntry_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | T ∈ S.piLpMatrix ι ∧ ‖T‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) ∧
          ‖T‖ ≤ 1} := by
  simp_rw [closure_unitBall_eq_unitBall_double_centralizer,
    mem_centralizer_centralizer_piLpMatrix_iff]

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

private theorem inter_Ici_zero_inter_closedBall_one (A : Set (H →L[ℂ] H)) :
    A ∩ Ici 0 ∩ closedBall 0 1 = A ∩ Icc 0 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ici, Metric.mem_closedBall, dist_zero_right,
    CStarAlgebra.mem_Icc_iff_norm_le_one, and_assoc]

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
      exact smul_nonneg ht.le hx)
    (isClosed_image_toPointwiseConvergenceCLM_inter (S : Set (H →L[ℂ] H))
      (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := 0)) r) ?_
  · intro b hb hb0 hb1
    have hb_mem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          {x | x ∈ S ∧ 0 ≤ x ∧ ‖x‖ ≤ 1}) :=
      S.closure_nonneg_unitBall_eq_nonneg_unitBall_double_centralizer ▸
        ⟨b, ⟨hb, hb0, hb1⟩, rfl⟩
    simp only [← SetLike.mem_coe, setOf_mem_and_pred_and_norm_le_eq_inter] at hb_mem
    exact hb_mem

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
  rw [← inter_Ici_zero_inter_closedBall_one, ← inter_Ici_zero_inter_closedBall_one]
  exact S.closure_image_ofCLM_inter_Ici_zero_inter_closedBall 1

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

/-! ### Ultrastrong and ultraweak Kaplansky density -/

/-- **Ultrastrong Kaplansky density theorem.** For every radius `r : ℝ`, the ultrastrong closure of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrongOfCLM_inter_closedBall
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
theorem closure_image_ultraweakOfCLM_inter_closedBall
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
theorem closure_image_ultrastrongOfCLM_inter_selfAdjoint_inter_closedBall
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
theorem closure_image_ultraweakOfCLM_inter_selfAdjoint_inter_closedBall
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
theorem closure_image_ultrastrongOfCLM_inter_Ici_zero_inter_closedBall
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
theorem closure_image_ultrastrongOfCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  rw [← inter_Ici_zero_inter_closedBall_one, ← inter_Ici_zero_inter_closedBall_one]
  exact S.closure_image_ultrastrongOfCLM_inter_Ici_zero_inter_closedBall 1

/-- **Ultraweak positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The
ultraweak closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_ultraweakOfCLM_inter_Ici_zero_inter_closedBall
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
theorem closure_image_ultraweakOfCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  rw [← inter_Ici_zero_inter_closedBall_one, ← inter_Ici_zero_inter_closedBall_one]
  exact S.closure_image_ultraweakOfCLM_inter_Ici_zero_inter_closedBall 1

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
      have hcx_mem : ((r / ‖x‖ : ℝ) : ℂ) • x ∈ (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r :=
        hball ▸ S.smul_mem_centralizer_centralizer_inter_closedBall hx (div_pos hr hxn)
          (div_mul_cancel₀ r hxn.ne').le
      exact inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (div_pos hr hxn).ne') x ▸
        SMulMemClass.smul_mem _ hcx_mem.1

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
    exact ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      hcl

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

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
strong-star closure of the closed ball of the star algebra generated by `s`. -/
theorem image_strongStar_ofCLM_adjoin_inter_closedBall_eq_closure
    (s : Set (H →L[ℂ] H)) (r : ℝ) :
    TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (TauCeti.ContinuousLinearMapStrongStar.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_strongStar_ofCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

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
theorem image_ultrastrongOfCLM_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ultrastrongOfCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin, coe_adjoin_coe]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
ultraweak closure of the closed ball of the star algebra generated by `s`. -/
theorem image_ultraweakOfCLM_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ultraweakOfCLM_inter_closedBall r,
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

/-- An operator `x` belongs to the von Neumann algebra generated by `s` if and only if it can be
approximated on every finite set of vectors by elements of `StarAlgebra.adjoin ℂ s` with norm at
most `‖x‖`. -/
theorem mem_adjoin_iff_forall_exists_norm_le_and_norm_sub_apply_lt
    {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ adjoin s ↔
      ∀ (v : Finset H) {ε : ℝ}, 0 < ε →
        ∃ t ∈ StarAlgebra.adjoin ℂ s, ‖t‖ ≤ ‖x‖ ∧ ∀ w ∈ v, ‖x w - t w‖ < ε := by
  refine ⟨fun hx v {ε} hε ↦ ?_,
    fun h ↦ mem_adjoin_iff_forall_exists_norm_sub_apply_lt.2 fun v {ε} hε ↦ ?_⟩
  · have hmem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
      rw [← image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure]
      exact ⟨x, ⟨hx, by simp⟩, rfl⟩
    obtain ⟨t, ⟨ht, htnorm⟩, hlt⟩ :=
      ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm.mp hmem v hε
    exact ⟨t, ht, by simpa using htnorm, hlt⟩
  · obtain ⟨t, ht, -, hlt⟩ := h v hε
    exact ⟨t, ht, hlt⟩

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
