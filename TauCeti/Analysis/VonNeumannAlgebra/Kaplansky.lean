/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Analysis.InnerProductSpace.Amplification
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky

/-!
# Kaplansky's density theorem

Let `S` be a unital star subalgebra of bounded operators on a complex Hilbert space `H`. While the
von Neumann bicommutant theorem identifies the strong and weak operator closures of `S` with its
double commutant `S''`, unbounded strong approximations cannot pass through nonlinear operations or
into the ultrastrong and ultraweak topologies. **Kaplansky's density theorem** shows that norm
bounds are preserved at no cost: for every radius `r : ℝ`, the strong-star, strong, weak,
ultrastrong, and ultraweak closures of `S ∩ closedBall 0 r` all equal `S'' ∩ closedBall 0 r`. The
analogous bounded density statements hold for the self-adjoint parts and for the positive
contractions `S ∩ Icc 0 1`.

Combining bounded strong density with the agreement of strong and ultrastrong (respectively, weak
and ultraweak) topologies on norm-bounded sets extends the bicommutant theorem to the ultrastrong
and ultraweak topologies (`StarSubalgebra.closure_image_ultrastrong`,
`StarSubalgebra.closure_image_ultraweak`) and characterizes concrete von Neumann algebras among
unital star subalgebras by weak operator compactness of closed balls of positive radius
(`StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`).

## Main results

* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall`:
  self-adjoint Kaplansky density on closed balls.
* `StarSubalgebra.closure_strongStar_inter_closedBall`: strong-star Kaplansky density on closed
  balls.
* `StarSubalgebra.closure_unitBall_eq_unitBall_double_centralizer` and
  `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_closedBall`: strong operator
  Kaplansky density.
* `StarSubalgebra.closure_unitBall_piLpMatrix`: matrix amplification of Kaplansky's density
  theorem on `PiLp 2 (fun _ : ι => H)`.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one` and
  `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall`:
  positive-part Kaplansky density.
* `StarSubalgebra.closure_image_ultrastrong` and `StarSubalgebra.closure_image_ultraweak`: the
  ultrastrong and ultraweak closures of `S` equal `S''`.
* `StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`: for `r > 0`,
  `S'' = S` if and only if `S ∩ closedBall 0 r` is weak operator compact.
* `VonNeumannAlgebra.image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure` and
  `VonNeumannAlgebra.image_ofCLM_adjoin_inter_closedBall_eq_closure`: bounded strong and weak
  closures of generated von Neumann algebras.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Theorem 5.3.5.
* V. F. R. Jones, *Von Neumann Algebras*, Theorem 5.2.1 and Corollary 5.2.2.
* J. Peterson, *Notes on von Neumann Algebras*, Theorem 2.6.4.
* C. Houdayer, *Subfactors and Planar Algebras*, Theorem 3.16.
-/

public section

open Filter Metric Set
open scoped InnerProductSpace Topology

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Self-adjoint Kaplansky density -/

/-- Every self-adjoint contraction in `S''` lies in the strong operator closure of the self-adjoint
contractions of `S`. -/
private theorem mem_closure_selfAdjoint_closedBall_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {b : H →L[ℂ] H}
    (hb : b ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    (hbsa : IsSelfAdjoint b) (hb1 : ‖b‖ ≤ 1) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let toCLM : (H →Lₚₜ[ℂ] H) → (H →L[ℂ] H) :=
    (UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite}).symm
  -- Realize `S''` as a concrete von Neumann algebra so `cfc_mem` applies directly.
  let M : VonNeumannAlgebra H := VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))
  have hbM : b ∈ M := VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hb
  let y : H →L[ℂ] H := cfc TauCeti.kaplanskyFunInv b
  have hy_cc : y ∈ (S.topologicalClosure : Set (H →L[ℂ] H)).centralizer.centralizer :=
    Set.centralizer_subset (Set.centralizer_subset S.le_topologicalClosure)
      (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp
        (cfc_mem (𝕜' := ℂ) TauCeti.kaplanskyFunInv hbM))
  have hysa : IsSelfAdjoint y := IsSelfAdjoint.cfc
  have hyb : cfc TauCeti.kaplanskyFun y = b :=
    hbsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hb1
  -- Approximate `y` strongly by self-adjoint elements of `S.topologicalClosure`.
  let A₀ : Set (H →L[ℂ] H) :=
    (S.topologicalClosure : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H)
  have hqy : q y ∈ closure (q '' A₀) := by
    rw [S.topologicalClosure.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨y, ⟨hy_cc, hysa⟩, rfl⟩
  let l : Filter (H →Lₚₜ[ℂ] H) := 𝓝[q '' A₀] (q y)
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqy
  have hmem : ∀ᶠ T in l, toCLM T ∈ A₀ := by
    refine (eventually_mem_nhdsWithin (a := q y) (s := q '' A₀)).mono ?_
    rintro T ⟨a, ha, rfl⟩
    exact ha
  -- Push the unbounded self-adjoint net through the strongly continuous Kaplansky function.
  have hlim : Tendsto (fun T : H →Lₚₜ[ℂ] H ↦ q (cfc TauCeti.kaplanskyFun (toCLM T))) l
      (𝓝 (q b)) := by
    rw [← hyb]
    exact TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun
      (hmem.mono fun T hT ↦ hT.2) hysa
      (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (q y))))
  have : IsClosed (S.topologicalClosure : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  have hcl_bar : q b ∈ closure (q ''
      (closure (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) := by
    refine mem_closure_of_tendsto hlim (hmem.mono fun T hT ↦ ?_)
    refine ⟨cfc TauCeti.kaplanskyFun (toCLM T), ⟨⟨?_, IsSelfAdjoint.cfc⟩, ?_⟩, rfl⟩
    · exact cfc_mem (𝕜' := ℂ) (s := S.topologicalClosure) TauCeti.kaplanskyFun hT.1
    · simpa [mem_closedBall, dist_zero_right] using TauCeti.norm_cfc_kaplanskyFun_le (toCLM T)
  -- Pull norm-bounded approximations from `closure S` back to `S` via norm continuity.
  rw [← S.closure_inter_selfAdjoint_inter_closedBall_zero 1] at hcl_bar
  exact closure_minimal (image_closure_subset_closure_image q.continuous) isClosed_closure hcl_bar

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
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hclosed : IsClosed (q ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
        closedBall 0 r)) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  refine subset_antisymm (closure_minimal (Set.image_mono <|
      inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨b, ⟨⟨hb, hbsa⟩, hbr⟩, rfl⟩
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact ((closedBall_eq_empty.2 hr).subset hbr).elim
  · rw [closedBall_zero, mem_singleton_iff] at hbr
    subst hbr
    exact subset_closure ⟨0, ⟨⟨S.zero_mem, .zero _⟩, mem_closedBall_self le_rfl⟩, rfl⟩
  · let c : ℂ := (r⁻¹ : ℝ)
    have hcb_cc : c • b ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
      VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp
        (SMulMemClass.smul_mem c (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hb))
    have hc_sa : IsSelfAdjoint c := by simp [c, IsSelfAdjoint]
    have hcb_sa : IsSelfAdjoint (c • b) := hc_sa.smul hbsa
    have hcb1 : ‖c • b‖ ≤ 1 := by
      rw [mem_closedBall, dist_zero_right] at hbr
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_le_iff₀ hr, mul_one]
      exact hbr
    have hmem := S.mem_closure_selfAdjoint_closedBall_one hcb_cc hcb_sa hcb1
    have hscaled := map_mem_closure (f := fun T : H →Lₚₜ[ℂ] H ↦ (r : ℂ) • T) (by fun_prop) hmem
      (t := q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) (by
        rintro _ ⟨a, ⟨⟨ha, hasa⟩, har⟩, rfl⟩
        have hr_sa : IsSelfAdjoint (r : ℂ) := by simp [IsSelfAdjoint]
        refine ⟨(r : ℂ) • a, ⟨⟨SMulMemClass.smul_mem _ ha, hr_sa.smul hasa⟩, ?_⟩,
          (map_smul q (r : ℂ) a).symm⟩
        rw [mem_closedBall, dist_zero_right] at har ⊢
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
        exact mul_le_of_le_one_right hr.le har)
    have hrc : (r : ℂ) • (c • b) = b := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
    rwa [← map_smul, hrc] at hscaled

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
  have hclosed : IsClosed (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
        closedBall 0 r)) := by
    rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective,
      ← S.closure_image_ofCLM_inter_selfAdjoint]
    exact isClosed_closure.inter
      (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed
  refine subset_antisymm (closure_minimal (Set.image_mono <|
      inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hx'

/-- **Finite-vector self-adjoint Kaplansky approximation.** Every self-adjoint `x ∈ S''` can be
approximated on finitely many vectors by a self-adjoint `s ∈ S` with `‖s‖ ≤ ‖x‖`. -/
theorem exists_isSelfAdjoint_norm_le_forall_norm_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hxsa : IsSelfAdjoint x)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, IsSelfAdjoint s ∧ ‖s‖ ≤ ‖x‖ ∧ ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : q x ∈ closure (q ''
      ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall ‖x‖]
    exact ⟨x, ⟨⟨hx, hxsa⟩, by simp⟩, rfl⟩
  let U : Set (H →Lₚₜ[ℂ] H) := {T | ∀ i, ‖x (v i) - T (v i)‖ < ε}
  have hU_open : IsOpen U := by
    have heq : U = ⋂ i, {T : H →Lₚₜ[ℂ] H | ‖x (v i) - T (v i)‖ < ε} := by
      ext T; simp [U]
    rw [heq]
    refine isOpen_iInter_of_finite fun i ↦ isOpen_lt ?_ continuous_const
    exact (continuous_const.sub ((continuous_apply (v i)).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) H H).continuous)).norm
  have hU_x : q x ∈ U := fun i ↦ by
    have hqx : (q x) (v i) = x (v i) := rfl
    simp [hqx, hε]
  obtain ⟨_, ⟨hU, s, ⟨⟨hs, hssa⟩, hsr⟩, rfl⟩⟩ := mem_closure_iff.1 hmem U hU_open hU_x
  exact ⟨s, hs, hssa, by simpa using hsr, hU⟩

/-! ### Strong-star, strong, weak, and matrix-amplified Kaplansky density -/

/-- The strong-star image `x ↦ (x, star x)` of `S'' ∩ closedBall 0 r` is closed in
`(H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H)`. -/
private theorem isClosed_strongStar_centralizer_centralizer_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun x : H →L[ℂ] H ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
         ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let toCLM : (H →Lₚₜ[ℂ] H) → (H →L[ℂ] H) :=
    (UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite}).symm
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hfst : IsClosed ((Prod.fst : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) → H →Lₚₜ[ℂ] H) ⁻¹'
      (q '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r))) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact (isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)).preimage
      continuous_fst
  have hgraph : IsClosed {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
      toCLM p.2 = star (toCLM p.1)} := by
    have heq : {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) | toCLM p.2 = star (toCLM p.1)} =
        ⋂ (u : H) (v : H), {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
          ⟪p.2 u, v⟫_ℂ = ⟪u, p.1 v⟫_ℂ} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.eq_adjoint_iff]
      rfl
    rw [heq]
    have heval (w : H) : Continuous fun T : H →Lₚₜ[ℂ] H ↦ T w :=
      (continuous_apply w).comp
        (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) H H).continuous
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_eq (((heval u).comp continuous_snd).inner continuous_const)
        (continuous_const.inner ((heval v).comp continuous_fst))
  convert hfst.inter hgraph using 1
  ext ⟨A, B⟩
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Prod.mk.injEq]
  exact ⟨fun ⟨x, hx, hA, hB⟩ ↦ ⟨⟨x, hx, hA⟩, by subst hA hB; rfl⟩,
    fun ⟨⟨x, hx, hA⟩, hB⟩ ↦ ⟨x, hx, hA, by subst hA; exact hq_inj hB.symm⟩⟩

/-- **Strong-star Kaplansky density theorem.** For every radius `r : ℝ`, the closure in the
strong-star topology (simultaneous strong convergence of an operator and its adjoint) of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_strongStar_inter_closedBall (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure ((fun x : H →L[ℂ] H ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
         ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
    (fun x : H →L[ℂ] H ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
         ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  set emb : (H →L[ℂ] H) → (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) := fun x ↦ (q x, q (star x))
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      (S.isClosed_strongStar_centralizer_centralizer_inter_closedBall r)) ?_
  rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩
  -- Dilate `x` to `[0, x; star x, 0]` on the `2`-fold Hilbert sum `PiLp 2 (fun _ : Fin 2 => H)`.
  let S₂ := S.piLpMatrix (Fin 2)
  set q₂ := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (PiLp 2 (fun _ : Fin 2 => H)) (PiLp 2 (fun _ : Fin 2 => H))
  let toCLM₂ : (PiLp 2 (fun _ : Fin 2 => H) →Lₚₜ[ℂ] PiLp 2 (fun _ : Fin 2 => H)) →
      (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) :=
    (UniformConvergenceCLM.ofFun (RingHom.id ℂ) (PiLp 2 (fun _ : Fin 2 => H))
      {s : Set (PiLp 2 (fun _ : Fin 2 => H)) | s.Finite}).symm
  have hx_star : star x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp
      (star_mem (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hx))
  let X : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
    PiLp.singleEntryCLM (0 : Fin 2) 1 x + PiLp.singleEntryCLM 1 0 (star x)
  have hX_cc : X ∈
      (S₂ : Set (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
        PiLp 2 (fun _ : Fin 2 => H))).centralizer.centralizer := by
    rw [S.coe_piLpMatrix_centralizer_centralizer (Fin 2)]
    intro i j
    fin_cases i <;> fin_cases j
    · simp [X]
    · simpa [X] using hx
    · simpa [X] using hx_star
    · simp [X]
  have hX_sa : IsSelfAdjoint X :=
    PiLp.isSelfAdjoint_singleEntryCLM_add_singleEntryCLM_star 0 1 x
  have hX_r : X ∈ closedBall 0 r := by
    rw [mem_closedBall, dist_zero_right] at hxr ⊢
    rwa [PiLp.norm_singleEntryCLM_add_singleEntryCLM_star (by decide : (0 : Fin 2) ≠ 1) x]
  have hqX : q₂ X ∈ closure (q₂ '' ((S₂ : Set _) ∩
      (selfAdjoint (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) : Set _) ∩
        closedBall 0 r)) := by
    rw [S₂.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r]
    exact ⟨X, ⟨⟨hX_cc, hX_sa⟩, hX_r⟩, rfl⟩
  -- Project a `2 × 2` operator matrix to its `(0, 1)` and `(1, 0)` strong-operator blocks.
  let projEntry (i j : Fin 2) :
      (PiLp 2 (fun _ : Fin 2 => H) →Lₚₜ[ℂ] PiLp 2 (fun _ : Fin 2 => H)) → (H →Lₚₜ[ℂ] H) :=
    fun T ↦ q ((toCLM₂ T).piLpEntry i j)
  have hproj_cont (i j : Fin 2) : Continuous (projEntry i j) := by
    refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun h ↦ ?_
    let w : PiLp 2 (fun _ : Fin 2 => H) := PiLp.single 2 j h
    have heq : (fun T : PiLp 2 (fun _ : Fin 2 => H) →Lₚₜ[ℂ] PiLp 2 (fun _ : Fin 2 => H) ↦
        projEntry i j T h) = fun T ↦ T w i := by
      ext T
      exact ContinuousLinearMap.piLpEntry_apply (toCLM₂ T) i j h
    rw [heq]
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) i).continuous.comp
      ((continuous_apply w).comp
        (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) _ _).continuous)
  let Φ : (PiLp 2 (fun _ : Fin 2 => H) →Lₚₜ[ℂ] PiLp 2 (fun _ : Fin 2 => H)) →
      (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) := fun T ↦ (projEntry 0 1 T, projEntry 1 0 T)
  have hΦ_cont : Continuous Φ := (hproj_cont 0 1).prodMk (hproj_cont 1 0)
  have hΦX : Φ (q₂ X) = emb x := by
    have hX_toCLM : toCLM₂ (q₂ X) = X := rfl
    simp only [Φ, projEntry, emb, hX_toCLM]
    simp [X]
  rw [← hΦX]
  refine map_mem_closure hΦ_cont hqX ?_
  rintro _ ⟨Y, ⟨⟨hY, hYsa⟩, hYr⟩, rfl⟩
  refine ⟨Y.piLpEntry 0 1, ⟨(S.mem_piLpMatrix_iff.1 hY) 0 1, ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right] at hYr ⊢
    exact (Y.norm_piLpEntry_le 0 1).trans hYr
  · have h10 : Y.piLpEntry 1 0 = star (Y.piLpEntry 0 1) := by
      have := congrArg (fun Z ↦ Z.piLpEntry 1 0) hYsa.star_eq
      simpa [ContinuousLinearMap.piLpEntry_star] using this.symm
    have hY_toCLM : toCLM₂ (q₂ Y) = Y := rfl
    simp [Φ, projEntry, emb, hY_toCLM, h10]

/-- **Kaplansky's density theorem for closed norm balls.** For every radius `r : ℝ`, the strong
operator closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hclosed : IsClosed (q ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hss : (q x, q (star x)) ∈ closure ((fun a : H →L[ℂ] H ↦ (q a, q (star a))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
    rw [S.closure_strongStar_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  exact map_mem_closure (f := Prod.fst) continuous_fst hss
    (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)

/-- **Kaplansky's density theorem.** The strong operator closure of the unit ball of a unital
star subalgebra of bounded operators on a complex Hilbert space is the unit ball of its double
commutant. -/
theorem closure_unitBall_eq_unitBall_double_centralizer
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ A ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1} := by
  have h1 : {x : H →L[ℂ] H | x ∈ A ∧ ‖x‖ ≤ 1} = (A : Set (H →L[ℂ] H)) ∩ closedBall 0 1 := by
    ext x; simp
  have h2 : {x : H →L[ℂ] H |
      x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1} =
      (A : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 1 := by
    ext x; simp
  rw [h1, h2, A.closure_image_toPointwiseConvergenceCLM_inter_closedBall 1]

/-- **Weak operator Kaplansky density theorem.** For every radius `r : ℝ`, the weak operator
closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  have hclosed : IsClosed (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
    exact ((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).inter
      (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hx'

/-- **Matrix amplification of Kaplansky's density theorem.** On the finite Hilbert sum
`PiLp 2 (fun _ : ι => H)`, the strong operator closure of the unit ball of `A.piLpMatrix ι` is the
set of contractions whose matrix entries lie in `A''`. -/
theorem closure_unitBall_piLpMatrix (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ A) ∧ ‖T‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (PiLp 2 (fun _ : ι => H)) (PiLp 2 (fun _ : ι => H)) ''
        {T | (∀ i j, T.piLpEntry i j ∈ (A : Set (H →L[ℂ] H)).centralizer.centralizer) ∧
          ‖T‖ ≤ 1} := by
  simpa only [mem_piLpMatrix_iff, A.coe_piLpMatrix_centralizer_centralizer ι, Set.mem_ofPred_eq]
    using (A.piLpMatrix ι).closure_unitBall_eq_unitBall_double_centralizer

/-- **Finite-vector strong-star Kaplansky approximation.** Every `x ∈ S''` can be approximated
simultaneously with its adjoint on finitely many vectors by `s ∈ S` satisfying `‖s‖ ≤ ‖x‖`. -/
theorem exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖s‖ ≤ ‖x‖ ∧
      ∀ i, ‖x (v i) - s (v i)‖ < ε ∧ ‖star x (v i) - star s (v i)‖ < ε := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : (q x, q (star x)) ∈ closure ((fun a : H →L[ℂ] H ↦ (q a, q (star a))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_strongStar_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  let U : Set ((H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H)) :=
    {p | ∀ i, ‖x (v i) - p.1 (v i)‖ < ε ∧ ‖star x (v i) - p.2 (v i)‖ < ε}
  have heval (w : H) : Continuous fun T : H →Lₚₜ[ℂ] H ↦ T w :=
    (continuous_apply w).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) H H).continuous
  have hU_open : IsOpen U := by
    have heq : U = ⋂ i, {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) | ‖x (v i) - p.1 (v i)‖ < ε} ∩
        {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) | ‖star x (v i) - p.2 (v i)‖ < ε} := by
      ext p; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_lt (continuous_const.sub ((heval (v i)).comp continuous_fst)).norm
        continuous_const).inter
      (isOpen_lt (continuous_const.sub ((heval (v i)).comp continuous_snd)).norm
        continuous_const)
  have hU_x : (q x, q (star x)) ∈ U := fun i ↦ by
    have hqx : (q x) (v i) = x (v i) := rfl
    have hqsx : (q (star x)) (v i) = (star x) (v i) := rfl
    simp [hqx, hqsx, hε]
  obtain ⟨_, ⟨hU, s, ⟨hs, hsr⟩, rfl⟩⟩ := mem_closure_iff.1 hmem U hU_open hU_x
  exact ⟨s, hs, by simpa using hsr, hU⟩

/-! ### Positive-part Kaplansky density -/

/-- **Positive-part Kaplansky density theorem.** The strong operator closure of the positive
contractions `S ∩ Icc 0 1` equals the positive contractions `S'' ∩ Icc 0 1`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let toCLM : (H →Lₚₜ[ℂ] H) → (H →L[ℂ] H) :=
    (UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite}).symm
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hIcc_closed : IsClosed (q '' Icc (0 : H →L[ℂ] H) 1) := by
    convert (ContinuousLinearMapWOT.isClosed_image_ofCLM_Icc
      (a := (0 : H →L[ℂ] H)) (b := 1)).preimage
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM using 1
    ext T
    simp only [q, Set.mem_image, Set.mem_preimage,
      ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, congrArg ContinuousLinearMapWOT.ofCLM h⟩,
      fun ⟨a, ha, h⟩ ↦ ⟨a, ha, ContinuousLinearMapWOT.ofCLM_injective h⟩⟩
  have hclosed : IsClosed (q ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1)) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact isClosed_closure.inter hIcc_closed
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, ⟨hx, hxIcc⟩, rfl⟩
  obtain ⟨hx0, hx1⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.1 hxIcc
  -- Approximate `CFC.sqrt x` by self-adjoint contractions in `S`, then square strongly.
  have hy_cc : CFC.sqrt x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    refine VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp ?_
    rw [CFC.sqrt_eq_cfc]
    exact cfc_nnreal_mem (𝕜 := ℂ) NNReal.sqrt
      (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hx)
  let y : H →L[ℂ] H := CFC.sqrt x
  have hysa : IsSelfAdjoint y := (CFC.sqrt_nonneg x).isSelfAdjoint
  have hy1 : ‖y‖ ≤ 1 := by
    rw [CFC.norm_sqrt x hx0]
    exact Real.sqrt_le_one.2 hx1
  let B₀ : Set (H →L[ℂ] H) :=
    (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1
  have hqy : q y ∈ closure (q '' B₀) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall 1]
    exact ⟨y, ⟨⟨hy_cc, hysa⟩, by simpa using hy1⟩, rfl⟩
  let l : Filter (H →Lₚₜ[ℂ] H) := 𝓝[q '' B₀] (q y)
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqy
  have hmem : ∀ᶠ T in l, toCLM T ∈ B₀ := by
    refine (eventually_mem_nhdsWithin (a := q y) (s := q '' B₀)).mono ?_
    rintro T ⟨a, ha, rfl⟩
    exact ha
  have hconv : ∀ v, Tendsto (fun T : H →Lₚₜ[ℂ] H ↦ toCLM T v) l (𝓝 (y v)) :=
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.1
      (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (q y))))
  have hsq : Tendsto (fun T : H →Lₚₜ[ℂ] H ↦ q (toCLM T * toCLM T)) l (𝓝 (q x)) := by
    have hyx : y * y = x := CFC.sqrt_mul_sqrt_self x hx0
    rw [← hyx, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro v
    exact ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hconv hconv
      (hmem.mono fun T hT ↦ by simpa using hT.2) v
  refine mem_closure_of_tendsto hsq (hmem.mono fun T hT ↦ ?_)
  rcases hT with ⟨⟨haS, hasa⟩, har⟩
  refine ⟨toCLM T * toCLM T, ⟨S.mul_mem haS haS, CStarAlgebra.mem_Icc_iff_norm_le_one.2 ⟨?_, ?_⟩⟩,
    rfl⟩
  · simpa [hasa.star_eq] using star_mul_self_nonneg (toCLM T)
  · rw [mem_closedBall, dist_zero_right] at har
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) har).trans har)

/-- **Positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The strong operator
closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hIci_closed : IsClosed (q '' Ici (0 : H →L[ℂ] H)) := by
    convert (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := (0 : H →L[ℂ] H))).preimage
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM using 1
    ext T
    simp only [q, Set.mem_image, Set.mem_preimage,
      ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, congrArg ContinuousLinearMapWOT.ofCLM h⟩,
      fun ⟨a, ha, h⟩ ↦ ⟨a, ha, ContinuousLinearMapWOT.ofCLM_injective h⟩⟩
  have hclosed : IsClosed (q ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r)) := by
    rw [Set.image_inter hq_inj, Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact (isClosed_closure.inter hIci_closed).inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  refine subset_antisymm (closure_minimal (Set.image_mono <|
      inter_subset_inter_left _ (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, ⟨⟨hx, hx0⟩, hxr⟩, rfl⟩
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact ((closedBall_eq_empty.2 hr).subset hxr).elim
  · rw [closedBall_zero, mem_singleton_iff] at hxr
    subst hxr
    exact subset_closure ⟨0, ⟨⟨S.zero_mem, mem_Ici.2 le_rfl⟩, mem_closedBall_self le_rfl⟩, rfl⟩
  · let c : ℂ := (r⁻¹ : ℝ)
    have hcx_cc : c • x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
      VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp
        (SMulMemClass.smul_mem c (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hx))
    have hcx0 : 0 ≤ c • x := by
      have hc_eq : c • x = (r⁻¹ : ℝ) • x := by
        simpa [c] using (RCLike.real_smul_eq_coe_smul (K := ℂ) r⁻¹ x).symm
      rw [hc_eq]
      exact smul_nonneg (inv_nonneg.2 hr.le) hx0
    have hcx1 : ‖c • x‖ ≤ 1 := by
      rw [mem_closedBall, dist_zero_right] at hxr
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_le_iff₀ hr, mul_one]
      exact hxr
    have hmem : q (c • x) ∈ closure (q '' ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) := by
      rw [S.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one]
      exact ⟨c • x, ⟨hcx_cc, CStarAlgebra.mem_Icc_iff_norm_le_one.2 ⟨hcx0, hcx1⟩⟩, rfl⟩
    have hscaled := map_mem_closure (f := fun T : H →Lₚₜ[ℂ] H ↦ (r : ℂ) • T) (by fun_prop) hmem
      (t := q '' ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) (by
        rintro _ ⟨a, ⟨ha, haIcc⟩, rfl⟩
        obtain ⟨ha0, ha1⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.1 haIcc
        have hra0 : 0 ≤ (r : ℂ) • a := by
          have hr_eq : (r : ℂ) • a = r • a :=
            (RCLike.real_smul_eq_coe_smul (K := ℂ) r a).symm
          rw [hr_eq]
          exact smul_nonneg hr.le ha0
        refine ⟨(r : ℂ) • a, ⟨⟨SMulMemClass.smul_mem _ ha, hra0⟩, ?_⟩,
          (map_smul q (r : ℂ) a).symm⟩
        rw [mem_closedBall, dist_zero_right, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
        exact mul_le_of_le_one_right hr.le ha1)
    have hrc : (r : ℂ) • (c • x) = x := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
    rwa [← map_smul, hrc] at hscaled

/-- **Weak operator positive-part Kaplansky density theorem.** The weak operator closure of the
positive contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ofCLM_inter_Icc_zero_one (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  have hclosed : IsClosed (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1)) := by
    rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
    exact ((S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer).inter
      ContinuousLinearMapWOT.isClosed_image_ofCLM_Icc
  refine subset_antisymm
    (closure_minimal (Set.image_mono (inter_subset_inter_left _ Set.subset_centralizer_centralizer))
      hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hx'

/-- **Finite-vector positive Kaplansky approximation.** Every positive `x ∈ S''` can be approximated
on finitely many vectors by a positive `s ∈ S` with `‖s‖ ≤ ‖x‖`. -/
theorem exists_nonneg_norm_le_forall_norm_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hx0 : 0 ≤ x)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, 0 ≤ s ∧ ‖s‖ ≤ ‖x‖ ∧ ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : q x ∈ closure (q '' ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall ‖x‖]
    exact ⟨x, ⟨⟨hx, hx0⟩, by simp⟩, rfl⟩
  let U : Set (H →Lₚₜ[ℂ] H) := {T | ∀ i, ‖x (v i) - T (v i)‖ < ε}
  have hU_open : IsOpen U := by
    have heq : U = ⋂ i, {T : H →Lₚₜ[ℂ] H | ‖x (v i) - T (v i)‖ < ε} := by
      ext T; simp [U]
    rw [heq]
    refine isOpen_iInter_of_finite fun i ↦ isOpen_lt ?_ continuous_const
    exact (continuous_const.sub ((continuous_apply (v i)).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id ℂ) H H).continuous)).norm
  have hU_x : q x ∈ U := fun i ↦ by
    have hqx : (q x) (v i) = x (v i) := rfl
    simp [hqx, hε]
  obtain ⟨_, ⟨hU, s, ⟨⟨hs, hs0⟩, hsr⟩, rfl⟩⟩ := mem_closure_iff.1 hmem U hU_open hU_x
  exact ⟨s, hs, hs0, by simpa using hsr, hU⟩

/-! ### Ultrastrong and ultraweak Kaplansky density and bicommutant closures -/

/-- **Ultrastrong Kaplansky density theorem.** For every radius `r : ℝ`, the ultrastrong closure of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrong_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltrastrong.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltrastrong.ofCLM_mem_closure_image_iff_of_norm_le (C := r)
      (by rintro T ⟨_, hT⟩; simpa using hT),
    S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective.mem_set_image]

/-- **Ultraweak Kaplansky density theorem.** For every radius `r : ℝ`, the ultraweak closure of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ultraweak_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltraweak.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltraweak.ofCLM_mem_closure_image_iff_of_norm_le (C := r)
      (by rintro T ⟨_, hT⟩; simpa using hT),
    S.closure_image_ofCLM_inter_closedBall r,
    ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltraweak.ofCLM_injective.mem_set_image]

/-- **Ultrastrong self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the
ultrastrong closure of `S ∩ selfAdjoint _ ∩ closedBall 0 r` equals
`S'' ∩ selfAdjoint _ ∩ closedBall 0 r`. -/
theorem closure_image_ultrastrong_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltrastrong.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltrastrong.ofCLM_mem_closure_image_iff_of_norm_le (C := r)
      (by rintro T ⟨_, hT⟩; simpa using hT),
    S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective.mem_set_image]

/-- **Ultraweak self-adjoint Kaplansky density theorem.** For every radius `r : ℝ`, the ultraweak
closure of `S ∩ selfAdjoint _ ∩ closedBall 0 r` equals `S'' ∩ selfAdjoint _ ∩ closedBall 0 r`. -/
theorem closure_image_ultraweak_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltraweak.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltraweak.ofCLM_mem_closure_image_iff_of_norm_le (C := r)
      (by rintro T ⟨_, hT⟩; simpa using hT),
    S.closure_image_ofCLM_inter_selfAdjoint_inter_closedBall r,
    ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltraweak.ofCLM_injective.mem_set_image]

/-- **Ultrastrong positive-part Kaplansky density theorem.** The ultrastrong closure of the positive
contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ultrastrong_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltrastrong.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltrastrong.ofCLM_mem_closure_image_iff_of_norm_le (C := 1)
      (by rintro T ⟨_, hT⟩; exact (CStarAlgebra.mem_Icc_iff_norm_le_one.1 hT).2),
    S.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective.mem_set_image]

/-- **Ultraweak positive-part Kaplansky density theorem.** The ultraweak closure of the positive
contractions `S ∩ Icc 0 1` equals `S'' ∩ Icc 0 1`. -/
theorem closure_image_ultraweak_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  ext A
  obtain ⟨x, rfl⟩ : ∃ x : H →L[ℂ] H, TauCeti.ContinuousLinearMapUltraweak.ofCLM x = A :=
    ⟨A.toCLM, rfl⟩
  rw [TauCeti.ContinuousLinearMapUltraweak.ofCLM_mem_closure_image_iff_of_norm_le (C := 1)
      (by rintro T ⟨_, hT⟩; exact (CStarAlgebra.mem_Icc_iff_norm_le_one.1 hT).2),
    S.closure_image_ofCLM_inter_Icc_zero_one,
    ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
    TauCeti.ContinuousLinearMapUltraweak.ofCLM_injective.mem_set_image]

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
    simp only [Set.mem_image, Set.mem_preimage, Function.comp_apply]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by rw [← h]⟩,
      fun ⟨a, ha, h⟩ ↦ ⟨a, ha,
        TauCeti.ContinuousLinearMapUltrastrong.toCLM_injective
          (ContinuousLinearMapWOT.ofCLM_injective h)⟩⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hball : TauCeti.ContinuousLinearMapUltrastrong.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_ultrastrong_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  exact closure_mono (Set.image_mono inter_subset_left) hball

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
    simp only [Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, by rw [← h]⟩,
      fun ⟨a, ha, h⟩ ↦ ⟨a, ha,
        TauCeti.ContinuousLinearMapUltraweak.toCLM_injective
          (ContinuousLinearMapWOT.ofCLM_injective h)⟩⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hball : TauCeti.ContinuousLinearMapUltraweak.ofCLM x ∈
      closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_ultraweak_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  exact closure_mono (Set.image_mono inter_subset_left) hball

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
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  constructor
  · intro hS
    rw [Set.image_inter hq_inj]
    exact (S.double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM.mp hS).inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)
  · intro hcl
    have hball : (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r =
        (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r := by
      apply Set.image_injective.mpr hq_inj
      rw [← S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r, hcl.closure_eq]
    refine subset_antisymm (fun x hx ↦ ?_) Set.subset_centralizer_centralizer
    by_cases hx0 : x = 0
    · subst hx0; exact S.zero_mem
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      let c : ℂ := ((r / ‖x‖ : ℝ) : ℂ)
      have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (div_pos hr hxn).ne'
      have hcx_cc : c • x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
        VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mp
          (SMulMemClass.smul_mem c (VonNeumannAlgebra.mem_adjoin_coe_starSubalgebra.mpr hx))
      have hcx_ball : c • x ∈ closedBall 0 r := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (div_pos hr hxn).le, div_mul_cancel₀ _ hxn.ne']
      have hcx_mem : c • x ∈ (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r :=
        hball ▸ ⟨hcx_cc, hcx_ball⟩
      have hinv : c⁻¹ • (c • x) = x := inv_smul_smul₀ hc0 x
      exact hinv ▸ SMulMemClass.smul_mem c⁻¹ hcx_mem.1

/-- For `r > 0`, a unital star subalgebra equals its double commutant if and only if its closed
ball of radius `r` is weak operator closed. -/
theorem double_commutant_iff_isClosed_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  constructor
  · intro hS
    rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
    exact (S.double_commutant_iff_isClosed_image_ofCLM.mp hS).inter
      (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed
  · intro hcl
    rw [S.double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM_inter_closedBall hr]
    have hball : (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r =
        (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r := by
      apply Set.image_injective.mpr ContinuousLinearMapWOT.ofCLM_injective
      rw [← S.closure_image_ofCLM_inter_closedBall r, hcl.closure_eq]
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
  refine ⟨fun hcl ↦ ?_, IsCompact.isClosed⟩
  have hsub : ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r) ⊆
      ContinuousLinearMapWOT.ofCLM '' closedBall 0 r :=
    Set.image_mono inter_subset_right
  exact (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).of_isClosed_subset hcl hsub

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

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
strong operator closure of the closed ball of the star algebra generated by `s`. -/
theorem image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure
    (s : Set (H →L[ℂ] H)) (r : ℝ) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_toPointwiseConvergenceCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin,
    coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]

/-- For every radius `r : ℝ`, the closed ball of the von Neumann algebra generated by `s` is the
weak operator closure of the closed ball of the star algebra generated by `s`. -/
theorem image_ofCLM_adjoin_inter_closedBall_eq_closure (s : Set (H →L[ℂ] H)) (r : ℝ) :
    ContinuousLinearMapWOT.ofCLM '' ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (ContinuousLinearMapWOT.ofCLM ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_ofCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin,
    coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]

/-- **Bounded strong-star approximation in a generated von Neumann algebra.** Every element
`x ∈ adjoin s` can be approximated simultaneously with its adjoint on finitely many vectors by
`t ∈ StarAlgebra.adjoin ℂ s` satisfying `‖t‖ ≤ ‖x‖`. -/
theorem exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt_of_mem_adjoin
    {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} (hx : x ∈ adjoin s)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ StarAlgebra.adjoin ℂ s, ‖t‖ ≤ ‖x‖ ∧
      ∀ i, ‖x (v i) - t (v i)‖ < ε ∧ ‖star x (v i) - star t (v i)‖ < ε := by
  have hx_cc : x ∈ (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← mem_adjoin_coe_starSubalgebra, adjoin_starAlgebraAdjoin]
    exact hx
  exact (StarAlgebra.adjoin ℂ s).exists_norm_le_forall_norm_sub_apply_lt_and_norm_star_sub_apply_lt
    hx_cc v hε

end VonNeumannAlgebra
