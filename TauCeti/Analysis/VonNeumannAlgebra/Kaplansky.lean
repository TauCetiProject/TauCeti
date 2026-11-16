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
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Kaplansky's density theorem

Let `S` be a unital star subalgebra of bounded operators on a complex Hilbert space `H`. While the
von Neumann bicommutant theorem identifies the strong and weak operator closures of `S` with its
double commutant `S''`, unbounded strong approximations cannot pass through nonlinear operations or
into the ultrastrong and ultraweak topologies. **Kaplansky's density theorem** shows that norm
bounds are preserved at no cost: for every radius `r : ℝ`, the strong-star, strong, weak,
ultrastrong, and ultraweak closures of `S ∩ closedBall 0 r` all equal `S'' ∩ closedBall 0 r`. The
analogous bounded density statements hold for the self-adjoint parts and for the positive elements
`S ∩ Ici 0 ∩ closedBall 0 r` (in particular, the positive contractions `S ∩ Icc 0 1`).

The self-adjoint step builds on two existing formalizations in Tau Ceti: strong operator continuity
of the continuous functional calculus for `t ↦ t / (1 + t²)` in
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky` (`TauCeti.kaplanskyFun`,
`TauCeti.kaplanskyFunInv`, `TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun`), and the
unbounded self-adjoint bicommutant closure
`StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint` in
`TauCeti.Analysis.VonNeumannAlgebra.Bicommutant`.

Combining bounded strong density with the agreement of strong and ultrastrong (respectively, weak
and ultraweak) topologies on norm-bounded sets extends the bicommutant theorem to the ultrastrong
and ultraweak topologies (`StarSubalgebra.closure_image_ultrastrong`,
`StarSubalgebra.closure_image_ultraweak`) and characterizes concrete von Neumann algebras among
unital star subalgebras by weak operator compactness of closed balls of positive radius
(`StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`).

## Main results

* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall`:
  self-adjoint Kaplansky density on closed balls.
* `StarSubalgebra.closure_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall`:
  strong-star Kaplansky density on closed balls.
* `StarSubalgebra.closure_unitBall_eq_unitBall_double_centralizer` and
  `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_closedBall`: strong operator
  Kaplansky density.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_piLpEntry_inter_closedBall` and
  `StarSubalgebra.closure_unitBall_piLpEntry_eq_unitBall_double_centralizer`: matrix amplification
  of Kaplansky's density theorem on `PiLp 2 (fun _ : ι => H)`.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall` and
  `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one` (with WOT,
  ultrastrong, and ultraweak counterparts): positive-part Kaplansky density.
* `StarSubalgebra.closure_image_ultrastrong` and `StarSubalgebra.closure_image_ultraweak`: the
  ultrastrong and ultraweak closures of `S` equal `S''`.
* `StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`: for `r > 0`,
  `S'' = S` if and only if `S ∩ closedBall 0 r` is weak operator compact.
* `VonNeumannAlgebra.image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure`,
  `VonNeumannAlgebra.image_ofCLM_adjoin_inter_closedBall_eq_closure`,
  `VonNeumannAlgebra.image_ultrastrong_adjoin_eq_closure`,
  `VonNeumannAlgebra.image_ultraweak_adjoin_eq_closure`, and
  `VonNeumannAlgebra.mem_adjoin_iff_forall_exists_norm_sub_apply_lt`: closures and strong
  approximation characterizations of generated von Neumann algebras.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Theorem 5.3.5.
* V. F. R. Jones, *Von Neumann Algebras*, Theorem 5.2.1 and Corollary 5.2.2.
* J. Peterson, *Notes on von Neumann Algebras*, Theorem 2.6.4.
* C. Houdayer, *An invitation to von Neumann algebras*, lecture notes, Université Paris-Sud
  (2017), Theorem 3.16.
-/

public section

open Filter Metric Set
open TauCeti (ContinuousLinearMapUltrastrong ContinuousLinearMapUltraweak)
open scoped InnerProductSpace Topology

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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

private theorem isClosed_image_of_isClosed_image_comp {α β γ : Type*}
    [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {g : β → γ} {h : α → γ} {s : Set α}
    (hfg : ∀ a, g (f a) = h a) (hg_cont : Continuous g) (hg_inj : Function.Injective g)
    (hs : IsClosed (h '' s)) :
    IsClosed (f '' s) := by
  rw [← Set.preimage_image_eq (f '' s) hg_inj, Set.image_image]
  simpa only [Function.comp_def, hfg] using hs.preimage hg_cont

private theorem closure_image_comp_of_closure_image {α β γ : Type*}
    [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {g : β → γ} {h : α → γ} {A B : Set α}
    (hfg : ∀ a, g (f a) = h a) (hf_inj : Function.Injective f) (hg_cont : Continuous g)
    (hclosed : IsClosed (h '' B)) (hf : closure (f '' A) = f '' B) :
    closure (h '' A) = h '' B := by
  have hAB : A ⊆ B := (Set.image_subset_image_iff hf_inj).1 (subset_closure.trans hf.subset)
  refine subset_antisymm (closure_minimal (Set.image_mono hAB) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : f x ∈ closure (f '' A) := hf ▸ ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def, hfg] using
    mem_closure_image hg_cont.continuousAt hx'

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
  -- Realize `S''` as a concrete von Neumann algebra so `cfc_mem` applies directly.
  let y : H →L[ℂ] H := cfc TauCeti.kaplanskyFunInv b
  have hy_cc : y ∈ (S.topologicalClosure : Set (H →L[ℂ] H)).centralizer.centralizer :=
    Set.centralizer_subset (Set.centralizer_subset S.le_topologicalClosure)
      (VonNeumannAlgebra.mem_adjoin_coe.mp
        (cfc_mem (𝕜' := ℂ) TauCeti.kaplanskyFunInv (VonNeumannAlgebra.mem_adjoin_coe.mpr hb)))
  let A₀ : Set (H →L[ℂ] H) :=
    (S.topologicalClosure : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H)
  have hqy : q y ∈ closure (q '' A₀) := by
    rw [S.topologicalClosure.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨y, ⟨hy_cc, IsSelfAdjoint.cfc⟩, rfl⟩
  let l : Filter (H →Lₚₜ[ℂ] H) := 𝓝[q '' A₀] (q y)
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqy
  have hmem : ∀ᶠ T in l, PointwiseConvergenceCLM.toCLM T ∈ A₀ := by
    refine (eventually_mem_nhdsWithin (a := q y) (s := q '' A₀)).mono ?_
    rintro T ⟨a, ha, rfl⟩
    rwa [PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM]
  -- Push the unbounded self-adjoint net through the strongly continuous Kaplansky function.
  have hlim : Tendsto (fun T : H →Lₚₜ[ℂ] H ↦
      q (cfc TauCeti.kaplanskyFun (PointwiseConvergenceCLM.toCLM T))) l (𝓝 (q b)) := by
    rw [← hbsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hb1]
    exact TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun
      (hmem.mono fun _ hT ↦ hT.2) IsSelfAdjoint.cfc
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr fun T ↦
        (PointwiseConvergenceCLM.toPointwiseConvergenceCLM_toCLM T).symm)
  have : IsClosed (S.topologicalClosure : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  have hcl_bar : q b ∈ closure (q ''
      (closure (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) :=
    mem_closure_of_tendsto hlim (hmem.mono fun T hT ↦
      ⟨cfc TauCeti.kaplanskyFun (PointwiseConvergenceCLM.toCLM T),
        ⟨⟨cfc_mem (𝕜' := ℂ) (s := S.topologicalClosure) TauCeti.kaplanskyFun hT.1,
          IsSelfAdjoint.cfc⟩,
        by simpa [mem_closedBall, dist_zero_right] using
          TauCeti.norm_cfc_kaplanskyFun_le (PointwiseConvergenceCLM.toCLM T)⟩,
        rfl⟩)
  -- Pull norm-bounded approximations from `closure S` back to `S` via norm continuity.
  rw [← StarMemClass.closure_inter_selfAdjoint_inter_closedBall_zero ℂ S 1] at hcl_bar
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
  refine S.closure_sot_inter_closedBall_of_unit (IsSelfAdjoint.zero _)
    (fun _ hx ↦ (by simp [IsSelfAdjoint] : IsSelfAdjoint (_ : ℂ)).smul hx) ?_
    (fun hb hbsa hb1 ↦ S.mem_closure_selfAdjoint_closedBall_one hb hbsa hb1)
  rw [Set.image_inter (ContinuousLinearMap.toPointwiseConvergenceCLM_injective
        (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)),
    ← S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
  exact isClosed_closure.inter
    (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)

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
  refine ContinuousLinearMapWOT.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r)
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

/-- The strong-star image `x ↦ (x, star x)` of `S'' ∩ closedBall 0 r` is closed in
`(H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H)`. -/
private theorem isClosed_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun x : H →L[ℂ] H ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
         ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hfst : IsClosed ((Prod.fst : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) → H →Lₚₜ[ℂ] H) ⁻¹'
      (q '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r))) := by
    rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
    exact (isClosed_closure.inter
      (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)).preimage
      continuous_fst
  have hgraph : IsClosed {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
      PointwiseConvergenceCLM.toCLM p.2 = star (PointwiseConvergenceCLM.toCLM p.1)} := by
    have heq : {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
          PointwiseConvergenceCLM.toCLM p.2 = star (PointwiseConvergenceCLM.toCLM p.1)} =
        ⋂ (u : H) (v : H), {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
          ⟪p.2 u, v⟫_ℂ = ⟪u, p.1 v⟫_ℂ} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.eq_adjoint_iff, PointwiseConvergenceCLM.toCLM_apply]
    rw [heq]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_eq (((continuous_eval_const u).comp continuous_snd).inner continuous_const)
        (continuous_const.inner ((continuous_eval_const v).comp continuous_fst))
  convert hfst.inter hgraph using 1
  ext ⟨A, B⟩
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Prod.mk.injEq]
  refine ⟨fun ⟨x, hx, hA, hB⟩ ↦ ⟨⟨x, hx, hA⟩, ?_⟩, fun ⟨⟨x, hx, hA⟩, hB⟩ ↦ ⟨x, hx, hA, ?_⟩⟩
  · rw [← hA, ← hB, PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM,
      PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM]
  · rw [← hA, PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM] at hB
    rw [← PointwiseConvergenceCLM.toPointwiseConvergenceCLM_toCLM B, hB]

/-- **Strong-star Kaplansky density theorem.** For every radius `r : ℝ`, the closure in the
strong-star topology (simultaneous strong convergence of an operator and its adjoint) of
`S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
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
      (S.isClosed_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall r)) ?_
  rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩
  -- Dilate `x` to `[0, x; star x, 0]` on the `2`-fold Hilbert sum `PiLp 2 (fun _ : Fin 2 => H)`.
  let S₂ := S.piLpMatrix (Fin 2)
  set q₂ := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (PiLp 2 (fun _ : Fin 2 => H)) (PiLp 2 (fun _ : Fin 2 => H))
  have hx_star : star x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.mem_adjoin_coe.mp (star_mem (VonNeumannAlgebra.mem_adjoin_coe.mpr hx))
  let X : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
    PiLp.singleEntryCLM (0 : Fin 2) 1 x + PiLp.singleEntryCLM 1 0 (star x)
  have hX_cc : X ∈ (S₂ : Set _).centralizer.centralizer := by
    rw [S.centralizer_centralizer_coe_piLpMatrix (Fin 2)]
    intro i j; fin_cases i <;> fin_cases j <;> simp [X, hx, hx_star]
  have hqX : q₂ X ∈ closure (q₂ '' ((S₂ : Set _) ∩
      (selfAdjoint (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) : Set _) ∩
        closedBall 0 r)) := by
    rw [S₂.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall r]
    refine ⟨X, ⟨⟨hX_cc, PiLp.isSelfAdjoint_singleEntryCLM_add_singleEntryCLM_star 0 1 x⟩, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hxr ⊢
    rwa [PiLp.norm_singleEntryCLM_add_singleEntryCLM_star (by decide : (0 : Fin 2) ≠ 1) x]
  let Φ : (PiLp 2 (fun _ : Fin 2 => H) →Lₚₜ[ℂ] PiLp 2 (fun _ : Fin 2 => H)) →
      (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) :=
    fun T ↦ (PointwiseConvergenceCLM.piLpEntryCLM ℂ H 0 1 T,
      PointwiseConvergenceCLM.piLpEntryCLM ℂ H 1 0 T)
  have hΦ_eq (T : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) :
      Φ (q₂ T) = (q (T.piLpEntry 0 1), q (T.piLpEntry 1 0)) :=
    Prod.ext (PointwiseConvergenceCLM.piLpEntryCLM_toPointwiseConvergenceCLM 0 1 T)
      (PointwiseConvergenceCLM.piLpEntryCLM_toPointwiseConvergenceCLM 1 0 T)
  have hΦX : Φ (q₂ X) = emb x := by
    rw [hΦ_eq]
    simp [emb, X]
  rw [← hΦX]
  refine map_mem_closure ((PointwiseConvergenceCLM.piLpEntryCLM ℂ H 0 1).continuous.prodMk
    (PointwiseConvergenceCLM.piLpEntryCLM ℂ H 1 0).continuous) hqX ?_
  rintro _ ⟨Y, ⟨⟨hY, hYsa⟩, hYr⟩, rfl⟩
  refine ⟨Y.piLpEntry 0 1, ⟨(S.mem_piLpMatrix_iff.1 hY) 0 1, ?_⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right] at hYr ⊢
    exact (Y.norm_piLpEntry_le 0 1).trans hYr
  · rw [hΦ_eq, ← hYsa.star_piLpEntry 0 1]

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
  refine closure_image_comp_of_closure_image (g := Prod.fst) (fun _ ↦ rfl)
    (fun _ _ h ↦ hq_inj (congrArg Prod.fst h)) continuous_fst ?_
    (S.closure_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall r)
  rw [Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
  exact isClosed_closure.inter
    (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)

/-- **Kaplansky's density theorem.** The strong operator closure of the unit ball of a unital
star subalgebra of bounded operators on a complex Hilbert space is the unit ball of its double
commutant. -/
theorem closure_unitBall_eq_unitBall_double_centralizer
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ A ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1} := by
  have hball (s : Set (H →L[ℂ] H)) : {x | x ∈ s ∧ ‖x‖ ≤ 1} = s ∩ closedBall 0 1 := by ext; simp
  simpa only [← SetLike.mem_coe, hball] using
    A.closure_image_toPointwiseConvergenceCLM_inter_closedBall 1

/-- **Weak operator Kaplansky density theorem.** For every radius `r : ℝ`, the weak operator
closure of `S ∩ closedBall 0 r` equals `S'' ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  refine ContinuousLinearMapWOT.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r)
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
  rwa [A.centralizer_centralizer_coe_piLpMatrix ι, coe_piLpMatrix] at h

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
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : (q x, q (star x)) ∈ closure ((fun a : H →L[ℂ] H ↦ (q a, q (star a))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_prodMk_toPointwiseConvergenceCLM_star_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, by simp⟩, rfl⟩
  let U : Set ((H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H)) :=
    {T | ∀ i, ‖x (v i) - T (v i)‖ < ε} ×ˢ {T | ∀ i, ‖star x (v i) - T (v i)‖ < ε}
  have hU_open : IsOpen U :=
    (PointwiseConvergenceCLM.isOpen_setOf_forall_norm_sub_apply_lt x v ε).prod
      (PointwiseConvergenceCLM.isOpen_setOf_forall_norm_sub_apply_lt (star x) v ε)
  have hmemU : (q x, q (star x)) ∈ U :=
    ⟨fun i ↦ by
        rw [ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply, sub_self, norm_zero]
        exact hε,
      fun i ↦ by
        rw [ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply, sub_self, norm_zero]
        exact hε⟩
  obtain ⟨_, ⟨⟨hU₁, hU₂⟩, s, ⟨hs, hsr⟩, rfl⟩⟩ := mem_closure_iff.1 hmem U hU_open hmemU
  exact ⟨s, hs, by simpa using hsr, fun i ↦
    ⟨by simpa only [q, ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply] using hU₁ i,
      by simpa only [q, ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply] using hU₂ i⟩⟩

/-! ### Positive-part Kaplansky density -/

/-- Every positive contraction in `S''` lies in the strong operator closure of the positive
contractions of `S`. -/
private theorem mem_closure_Ici_zero_closedBall_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {b : H →L[ℂ] H}
    (hb : b ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    (hb0 : b ∈ Ici (0 : H →L[ℂ] H)) (hb1 : ‖b‖ ≤ 1) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H b ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 1)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  -- Approximate `CFC.sqrt b` by self-adjoint contractions in `S`, then square strongly.
  let y : H →L[ℂ] H := CFC.sqrt b
  have hy_cc : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.mem_adjoin_coe.mp <| by
      simp only [y, CFC.sqrt_eq_cfc]
      exact cfc_nnreal_mem (𝕜 := ℂ) NNReal.sqrt (VonNeumannAlgebra.mem_adjoin_coe.mpr hb)
  let B₀ : Set (H →L[ℂ] H) := (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1
  have hqy : q y ∈ closure (q '' B₀) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall 1]
    exact ⟨y, ⟨⟨hy_cc, (CFC.sqrt_nonneg b).isSelfAdjoint⟩,
      by simpa [y, CFC.norm_sqrt b hb0] using Real.sqrt_le_one.2 hb1⟩, rfl⟩
  let l : Filter (H →Lₚₜ[ℂ] H) := 𝓝[q '' B₀] (q y)
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqy
  have hmem : ∀ᶠ T in l, PointwiseConvergenceCLM.toCLM T ∈ B₀ := by
    refine (eventually_mem_nhdsWithin (a := q y) (s := q '' B₀)).mono ?_
    rintro T ⟨a, ha, rfl⟩
    rwa [PointwiseConvergenceCLM.toCLM_toPointwiseConvergenceCLM]
  have hconv : ∀ v, Tendsto (fun T : H →Lₚₜ[ℂ] H ↦ PointwiseConvergenceCLM.toCLM T v) l
      (𝓝 (y v)) := fun v ↦ by
    simpa only [q, id_eq, PointwiseConvergenceCLM.toCLM_apply,
      ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply] using
      PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.1
        (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (q y)))) v
  have hsq : Tendsto (fun T : H →Lₚₜ[ℂ] H ↦
      q (PointwiseConvergenceCLM.toCLM T * PointwiseConvergenceCLM.toCLM T)) l (𝓝 (q b)) := by
    rw [← CFC.sqrt_mul_sqrt_self b hb0, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro v
    simpa only [q, y, ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply,
      ContinuousLinearMap.mul_def] using
      ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hconv hconv
        (hmem.mono fun _ hT ↦ by simpa using hT.2) v
  refine mem_closure_of_tendsto hsq (hmem.mono fun T ⟨⟨haS, hasa⟩, har⟩ ↦ ?_)
  refine ⟨PointwiseConvergenceCLM.toCLM T * PointwiseConvergenceCLM.toCLM T,
    ⟨⟨S.mul_mem haS haS,
      by simpa [hasa.star_eq] using star_mul_self_nonneg (PointwiseConvergenceCLM.toCLM T)⟩, ?_⟩,
    rfl⟩
  rw [mem_closedBall, dist_zero_right] at har ⊢
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) har).trans har)

private theorem inter_Ici_zero_inter_closedBall_one (T : Set (H →L[ℂ] H)) :
    T ∩ Ici 0 ∩ closedBall 0 1 = T ∩ Icc 0 1 := by
  ext x
  simp only [mem_inter_iff, mem_Ici, mem_closedBall_zero_iff,
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
      exact smul_nonneg ht.le hx) ?_
    (fun hb hb0 hb1 ↦ S.mem_closure_Ici_zero_closedBall_one hb hb0 hb1)
  have hq_inj := ContinuousLinearMap.toPointwiseConvergenceCLM_injective
    (𝕜₂ := ℂ) (σ := RingHom.id ℂ) (E := H) (F := H)
  have hIci_closed : IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        Ici (0 : H →L[ℂ] H)) :=
    ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici
  rw [Set.image_inter hq_inj, Set.image_inter hq_inj, ← S.closure_image_toPointwiseConvergenceCLM]
  exact (isClosed_closure.inter hIci_closed).inter
    (PointwiseConvergenceCLM.isClosed_image_toPointwiseConvergenceCLM_closedBall 0 r)

/-- **Positive-part Kaplansky density theorem.** The strong operator closure of the positive
contractions `S ∩ Icc 0 1` equals the positive contractions `S'' ∩ Icc 0 1`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Icc 0 1) := by
  simpa only [inter_Ici_zero_inter_closedBall_one] using
    S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall 1

/-- **Weak operator positive-part Kaplansky density theorem for arbitrary radius `r : ℝ`.** The
weak operator closure of `S ∩ Ici 0 ∩ closedBall 0 r` equals `S'' ∩ Ici 0 ∩ closedBall 0 r`. -/
theorem closure_image_ofCLM_inter_Ici_zero_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ Ici 0 ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Ici 0 ∩ closedBall 0 r) := by
  refine ContinuousLinearMapWOT.closure_image_ofCLM_of_closure_image_toPointwiseConvergenceCLM ?_
    (S.closure_image_toPointwiseConvergenceCLM_inter_Ici_zero_inter_closedBall r)
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
  simpa only [inter_Ici_zero_inter_closedBall_one] using
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
  simpa only [inter_Ici_zero_inter_closedBall_one] using
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
  simpa only [inter_Ici_zero_inter_closedBall_one] using
    S.closure_image_ultraweak_inter_Ici_zero_inter_closedBall 1

/-- **Ultrastrong bicommutant closure.** The ultrastrong closure of a unital star subalgebra `S`
equals its double commutant `S''`. -/
theorem closure_image_ultrastrong (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[ℂ] H))) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
  have hclosed : IsClosed (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
      (S : Set (H →L[ℂ] H)).centralizer.centralizer) :=
    isClosed_image_of_isClosed_image_comp
      (g := fun A : TauCeti.ContinuousLinearMapUltrastrong ℂ H H ↦
        ContinuousLinearMapWOT.ofCLM (TauCeti.ContinuousLinearMapUltraweak.ofCLM A.toCLM).toCLM)
      (fun a ↦ by simp)
      (TauCeti.ContinuousLinearMapUltraweak.continuous_toWOT.comp
        TauCeti.ContinuousLinearMapUltraweak.continuous_ofUltrastrong)
      (fun _ _ h ↦ TauCeti.ContinuousLinearMapUltrastrong.toCLM_injective <| by
        simpa using ContinuousLinearMapWOT.ofCLM_injective h)
      (S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer
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
        (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
  closure_image_comp_of_closure_image
    (g := fun A : TauCeti.ContinuousLinearMapUltrastrong ℂ H H ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM A.toCLM)
    (fun a ↦ by simp)
    TauCeti.ContinuousLinearMapUltrastrong.ofCLM_injective
    TauCeti.ContinuousLinearMapUltraweak.continuous_ofUltrastrong
    (isClosed_image_of_isClosed_image_comp
      (g := fun A : TauCeti.ContinuousLinearMapUltraweak ℂ H H ↦
        ContinuousLinearMapWOT.ofCLM A.toCLM)
      (fun a ↦ by simp)
      TauCeti.ContinuousLinearMapUltraweak.continuous_toWOT
      (fun _ _ h ↦ TauCeti.ContinuousLinearMapUltraweak.toCLM_injective
        (ContinuousLinearMapWOT.ofCLM_injective h))
      (S : Set (H →L[ℂ] H)).centralizer.isClosed_image_ofCLM_centralizer)
    S.closure_image_ultrastrong

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
    PointwiseConvergenceCLM.toPointwiseConvergenceCLM_mem_closure_image_iff]
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
