/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.LocallyConvex.UltrastrongTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Algebra.StarSubalgebra
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
import TauCeti.Analysis.InnerProductSpace.Amplification
import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology

/-!
# The Kaplansky density theorem

Let `H` be a complete complex Hilbert space and `S` a unital star subalgebra of the bounded
operators `H →L[ℂ] H`. The **Kaplansky density theorem** refines the bicommutant theorem by
preserving operator-norm bounds: every closed ball of radius `r` in `S` is dense in the
corresponding closed ball of the double commutant `S''` in the strong operator topology, and
indeed in the strong-star, weak operator, ultrastrong, and ultraweak topologies. The same holds
for the self-adjoint parts and for the positive parts (in particular, the positive contractions
`0 ≤ a ≤ 1`).

As a consequence, a unital star subalgebra `S` equals its double commutant if and only if its
closed ball of any positive radius `r` is weak operator compact (equivalently, strong operator
closed).

## Proof outline

1. **Self-adjoint part.** For a norm-closed unital star subalgebra `B`, any self-adjoint
   contraction `x ∈ B''` is `cfc kaplanskyFun y` for `y = cfc kaplanskyFunInv x ∈ B''`, which is
   the strong operator limit of self-adjoint operators `a ∈ B` by the bicommutant theorem for
   self-adjoint parts. Applying the strongly continuous bounded function `cfc kaplanskyFun` yields
   self-adjoint contractions in `B` converging strongly to `x`. Passing from a general `S` to its
   norm closure `S.topologicalClosure` uses continuous real-part projection and radial rescaling,
   and arbitrary radii `r` follow by scaling.
2. **Strong-star and general ball forms.** For `x ∈ S''` with `‖x‖ ≤ r`, the `2 × 2` off-diagonal
   Hermitian block `[[0, x], [star x, 0]]` on `PiLp 2 (fun _ : Fin 2 => H)` is self-adjoint, has
   norm `‖x‖ ≤ r`, and lies in the double commutant of the matrix algebra `S.piLpMatrix (Fin 2)`.
   Applying the self-adjoint case to this block and reading off the `(0, 1)` and `(1, 0)` entries
   simultaneously approximates `x` and `star x` strongly by bounded operators in `S`. Bounded-set
   agreement of the ultrastrong/strong and ultraweak/weak operator topologies immediately yields
   the ultrastrong and ultraweak ball closures.
3. **Positive part.** For `0 ≤ x ∈ S''` with `‖x‖ ≤ r`, the self-adjoint case approximates
   `CFC.sqrt x` strongly by self-adjoint `y ∈ S` with `‖y‖ ≤ √r`; squaring gives positive
   operators `y * y ∈ S` of norm at most `r` converging strongly to `x` by bounded composition
   continuity.

## Main results

* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall`:
  self-adjoint Kaplansky density for every radius `r`.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_prod_star_inter_closedBall` and
  `StarSubalgebra.exists_norm_le_and_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`:
  strong-star Kaplansky density in closure and finite-vector forms.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_closedBall` and
  `StarSubalgebra.closure_unitBall_eq_unitBall_double_centralizer`:
  strong operator Kaplansky density for arbitrary radii and for the closed unit ball.
* `StarSubalgebra.closure_image_ofCLM_inter_closedBall`,
  `StarSubalgebra.closure_image_ultrastrong_inter_closedBall`, and
  `StarSubalgebra.closure_image_ultraweak_inter_closedBall`:
  weak operator, ultrastrong, and ultraweak Kaplansky density.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Ici_inter_closedBall` and
  `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one`:
  positive Kaplansky density.
* `StarSubalgebra.double_commutant_iff_isCompact_image_ofCLM_inter_closedBall`:
  a unital star subalgebra equals its double commutant iff its closed ball of positive radius is
  weak operator compact.
* `VonNeumannAlgebra.image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure`,
  `VonNeumannAlgebra.exists_norm_le_and_forall_norm_sub_apply_lt_of_mem_adjoin`, and
  `VonNeumannAlgebra.mem_adjoin_iff_exists_mem_closure_closedBall`:
  bounded strong approximation for generated von Neumann algebras.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Theorem 5.3.5.
* V. F. R. Jones, *Von Neumann Algebras*, Theorem 5.2.1 and Corollary 5.2.2.
* C. Houdayer, *Von Neumann Algebras*, Theorem 3.16.
* J. Peterson, *Notes on von Neumann Algebras*, Theorem 2.6.4.
-/

public section

open Filter Metric Topology

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Self-adjoint Kaplansky density -/

/-- The SOT image of `S'' ∩ closedBall 0 r` is closed. -/
private theorem isClosed_sot_double_centralizer_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
  refine ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM ?_
  rw [← VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset]
  exact ((VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))).isCompact_image_ofCLM_inter_closedBall
    0 r).isClosed

/-- Self-adjoint Kaplansky density on the closed unit ball for a norm-closed star subalgebra. -/
private theorem mem_closure_selfAdjoint_unitBall_of_isClosed
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    {x : H →L[ℂ] H} (hx : x ∈ (B : Set (H →L[ℂ] H)).centralizer.centralizer)
    (hxsa : IsSelfAdjoint x) (hx1 : ‖x‖ ≤ 1) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hM : (VonNeumannAlgebra.adjoin (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      (B : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq B).subset
  set y : H →L[ℂ] H := cfc TauCeti.kaplanskyFunInv x
  have hy : y ∈ (B : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM] at hx ⊢
    exact cfc_mem (𝕜' := ℂ) TauCeti.kaplanskyFunInv hx
  have hysa : IsSelfAdjoint y := cfc_predicate TauCeti.kaplanskyFunInv x
  have hy_cl : q y ∈ closure (q '' ((B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H))) := by
    rw [B.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨y, ⟨hy, hysa⟩, rfl⟩
  let l : Filter (H →Lₚₜ[ℂ] H) :=
    𝓝 (q y) ⊓ 𝓟 (q '' ((B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H)))
  have : l.NeBot := mem_closure_iff_clusterPt.mp hy_cl
  have hmem : ∀ᶠ T in l, (T : H →L[ℂ] H) ∈ (B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) := by
    filter_upwards [Filter.mem_inf_of_right (mem_principal_self _)] with T hT
    rcases hT with ⟨a, ha, rfl⟩
    exact ha
  have htend : Tendsto (fun T : H →Lₚₜ[ℂ] H => q (cfc TauCeti.kaplanskyFun (T : H →L[ℂ] H))) l
      (𝓝 (q x)) := by
    rw [← hxsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hx1]
    exact TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun
      (hmem.mono fun _ h => h.2) hysa (Filter.tendsto_inf_left tendsto_id)
  refine mem_closure_of_tendsto htend (hmem.mono fun T hT => ?_)
  exact ⟨cfc TauCeti.kaplanskyFun (T : H →L[ℂ] H),
    ⟨⟨cfc_mem (𝕜' := ℂ) TauCeti.kaplanskyFun hT.1,
      cfc_predicate TauCeti.kaplanskyFun (T : H →L[ℂ] H)⟩,
      mem_closedBall_zero_iff.mpr (TauCeti.norm_cfc_kaplanskyFun_le (T : H →L[ℂ] H))⟩, rfl⟩

/-- Self-adjoint Kaplansky density on the closed unit ball for an arbitrary unital star
subalgebra. -/
private theorem mem_closure_selfAdjoint_unitBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {x : H →L[ℂ] H} (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    (hxsa : IsSelfAdjoint x) (hx1 : ‖x‖ ≤ 1) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let B : StarSubalgebra ℂ (H →L[ℂ] H) := S.topologicalClosure
  have : IsClosed (B : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  -- The norm closure `B` has the same commutant, hence the same double commutant, as `S`.
  have hBc : (B : Set (H →L[ℂ] H)).centralizer = (S : Set (H →L[ℂ] H)).centralizer := by
    refine subset_antisymm (Set.centralizer_subset S.le_topologicalClosure) ?_
    rw [← Set.centralizer_centralizer_centralizer (S : Set (H →L[ℂ] H))]
    refine Set.centralizer_subset ?_
    rw [StarSubalgebra.topologicalClosure_coe]
    exact closure_minimal Set.subset_centralizer_centralizer (Set.isClosed_centralizer _)
  have hxB : q x ∈ closure (q '' ((B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩
      closedBall 0 1)) :=
    B.mem_closure_selfAdjoint_unitBall_of_isClosed (congrArg Set.centralizer hBc ▸ hx) hxsa hx1
  -- Every self-adjoint contraction in `B` is a norm limit of self-adjoint contractions in `S`.
  have hsub : (B : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1 ⊆
      closure ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1) := by
    rintro b ⟨⟨hbB, hbsa⟩, hb1⟩
    rw [mem_closedBall_zero_iff] at hb1
    let rePart : (H →L[ℂ] H) → (H →L[ℂ] H) := fun a => (2⁻¹ : ℂ) • (a + star a)
    let f : (H →L[ℂ] H) → (H →L[ℂ] H) := fun a => (max 1 ‖rePart a‖)⁻¹ • rePart a
    have hre_cont : Continuous rePart := (continuous_id.add continuous_star).const_smul (2⁻¹ : ℂ)
    have hf_cont : Continuous f :=
      ((continuous_const.max (continuous_norm.comp hre_cont)).inv₀ fun a =>
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne').smul hre_cont
    have hfb : f b = b := by
      have hreb : rePart b = b := by
        simp only [rePart, hbsa.star_eq, ← two_smul ℂ b, smul_smul,
          inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
      simp [f, hreb, max_eq_left hb1]
    rw [← hfb]
    refine map_mem_closure hf_cont (S.topologicalClosure_coe ▸ hbB) fun a ha => ?_
    have hrea_mem : rePart a ∈ S := SMulMemClass.smul_mem _ (add_mem ha (star_mem ha))
    have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by simp [IsSelfAdjoint]
    have hrea_sa : IsSelfAdjoint (rePart a) := h2.smul (.add_star_self a)
    have hpos : 0 < max 1 ‖rePart a‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp only [f]
      rw [← Complex.coe_smul]
      exact SMulMemClass.smul_mem _ hrea_mem
    · dsimp only [f]
      rw [← Complex.coe_smul]
      exact IsSelfAdjoint.smul (Complex.conj_ofReal _) hrea_sa
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_le_iff₀ hpos, mul_one]
      exact le_max_right _ _
  refine closure_minimal ((Set.image_mono hsub).trans (image_closure_subset_closure_image ?_))
    isClosed_closure hxB
  exact PointwiseConvergenceCLM.continuous_of_continuous_eval fun v =>
    (ContinuousLinearMap.apply ℂ H v).continuous

/-- **Self-adjoint Kaplansky density.** For a unital star subalgebra `S` of `H →L[ℂ] H` and every
radius `r`, the strong operator closure of the self-adjoint operators in `S` of norm at most `r`
is the set of self-adjoint operators in `S''` of norm at most `r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩
          selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hclosed : IsClosed (q '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩
      selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) := by
    have h1 := S.isClosed_sot_double_centralizer_inter_closedBall r
    have h2 :=
      ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
        (ContinuousLinearMapWOT.isClosed_image_ofCLM_selfAdjoint (𝕜 := ℂ) (E := H))
    convert h1.inter h2 using 1
    rw [← Set.image_inter ContinuousLinearMap.toPointwiseConvergenceCLM_injective]
    congr 1
    exact Set.inter_right_comm _ _ _
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      (Set.inter_subset_inter_left _ Set.subset_centralizer_centralizer))) hclosed) ?_
  rintro _ ⟨x, ⟨⟨hx, hxsa⟩, hxr⟩, rfl⟩
  rw [mem_closedBall_zero_iff] at hxr
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · linarith [norm_nonneg x]
  · have hx0 : x = 0 := norm_le_zero_iff.mp hxr
    subst hx0
    exact subset_closure ⟨0, ⟨⟨zero_mem S, IsSelfAdjoint.zero _⟩, by simp⟩, rfl⟩
  · -- Scale `x` into the unit ball, apply the unit-ball theorem, and scale back by `r`.
    let y : H →L[ℂ] H := ((r⁻¹ : ℝ) : ℂ) • x
    have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
        (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
      VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
    have hy : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
      rw [← hM] at hx ⊢
      exact SMulMemClass.smul_mem _ hx
    have hysa : IsSelfAdjoint y := IsSelfAdjoint.smul (Complex.conj_ofReal r⁻¹) hxsa
    have hy1 : ‖y‖ ≤ 1 := by
      simp only [y, Complex.coe_smul]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_le_iff₀ hr, mul_one]
      exact hxr
    have hrx : (r : ℂ) • q y = q x := by
      have h : (r : ℂ) • y = x := by
        simp only [y, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
          Complex.ofReal_one, one_smul]
      exact (map_smul q (r : ℂ) y).symm.trans (congrArg q h)
    rw [← hrx]
    refine map_mem_closure (continuous_const_smul (r : ℂ))
      (S.mem_closure_selfAdjoint_unitBall hy hysa hy1) ?_
    rintro _ ⟨a, ⟨⟨haS, hasa⟩, ha1⟩, rfl⟩
    rw [mem_closedBall_zero_iff] at ha1
    refine ⟨(r : ℂ) • a, ⟨⟨SMulMemClass.smul_mem _ haS,
      IsSelfAdjoint.smul (Complex.conj_ofReal r) hasa⟩, ?_⟩, (map_smul q (r : ℂ) a).symm⟩
    rw [mem_closedBall_zero_iff, Complex.coe_smul, norm_smul, Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left ha1 hr.le).trans_eq (mul_one r)

/-! ### Strong-star and general Kaplansky density -/

/-- The strong-star image `x ↦ (q x, q (star x))` of `S'' ∩ closedBall 0 r` is closed in the
product of two strong operator topologies. -/
private theorem isClosed_prod_star_double_centralizer_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun x : H →L[ℂ] H =>
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
          ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
  have h1 := (S.isClosed_sot_double_centralizer_inter_closedBall r).preimage
    (continuous_fst : Continuous (Prod.fst : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) → _))
  have h2 : IsClosed {p : (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) |
      ContinuousLinearMapWOT.ofCLM (p.2 : H →L[ℂ] H) =
        star (ContinuousLinearMapWOT.ofCLM (p.1 : H →L[ℂ] H))} :=
    isClosed_eq
      (ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.comp continuous_snd)
      (continuous_star.comp
        (ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.comp continuous_fst))
  convert h1.inter h2 using 1
  ext ⟨A, B⟩
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
  constructor
  · rintro ⟨a, ha, hEq⟩
    obtain ⟨hA, hB⟩ := Prod.mk.inj hEq
    refine ⟨⟨a, ha, hA⟩, ?_⟩
    rw [← hB, ← hA]
    rfl
  · rintro ⟨⟨a, ha, hA⟩, hB⟩
    refine ⟨a, ha, Prod.ext hA ?_⟩
    rw [← hA] at hB
    exact (ContinuousLinearMapWOT.ofCLM_injective hB).symm

/-- **Strong-star Kaplansky density.** For a unital star subalgebra `S` of `H →L[ℂ] H` and every
radius `r`, the pairs `(a, star a)` for `a ∈ S` with `‖a‖ ≤ r` are dense in the corresponding pairs
for `a ∈ S''` with `‖a‖ ≤ r`, in the product of two strong operator topologies. -/
theorem closure_image_toPointwiseConvergenceCLM_prod_star_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure ((fun x : H →L[ℂ] H =>
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
            ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      (fun x : H →L[ℂ] H =>
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x,
            ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (star x))) ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  set φ : (H →L[ℂ] H) → (H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H) := fun x => (q x, q (star x))
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer))
      (S.isClosed_prod_star_double_centralizer_inter_closedBall r)) ?_
  rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩
  rw [mem_closedBall_zero_iff] at hxr
  -- Lift `x` to the self-adjoint `2 × 2` block `[[0, x], [star x, 0]]` on `H ⊕ H`.
  let H₂ := PiLp 2 (fun _ : Fin 2 => H)
  set q₂ := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H₂ H₂
  let X : H₂ →L[ℂ] H₂ := ContinuousLinearMap.ofPiLpEntry ![![0, x], ![star x, 0]]
  have hX_mem : X ∈ (S.piLpMatrix (Fin 2) : Set (H₂ →L[ℂ] H₂)).centralizer.centralizer := by
    rw [S.mem_centralizer_centralizer_piLpMatrix_iff]
    have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
        (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
      VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
    have hx_star : star x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
      rw [← hM] at hx ⊢
      exact star_mem hx
    intro i j
    fin_cases i <;> fin_cases j <;> simp [X, hx, hx_star, Set.zero_mem_centralizer]
  have hX_sa : IsSelfAdjoint X := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_piLpEntry]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [X]
  have hX_norm : ‖X‖ ≤ r := by
    dsimp only [X]
    rw [ContinuousLinearMap.norm_ofPiLpEntry_offDiag, norm_star, max_self]
    exact hxr
  have hX_cl : q₂ X ∈ closure (q₂ '' ((S.piLpMatrix (Fin 2) : Set (H₂ →L[ℂ] H₂)) ∩
      selfAdjoint (H₂ →L[ℂ] H₂) ∩ closedBall 0 r)) := by
    rw [closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall]
    exact ⟨X, ⟨⟨hX_mem, hX_sa⟩, mem_closedBall_zero_iff.mpr hX_norm⟩, rfl⟩
  -- Projecting `H₂ →Lₚₜ[ℂ] H₂` to the `(0, 1)` and `(1, 0)` entries is SOT-continuous.
  let entrySOT (i j : Fin 2) : (H₂ →Lₚₜ[ℂ] H₂) → (H →Lₚₜ[ℂ] H) :=
    fun T => q ((T : H₂ →L[ℂ] H₂).piLpEntry i j)
  have hentry_cont (i j : Fin 2) : Continuous (entrySOT i j) :=
    PointwiseConvergenceCLM.continuous_of_continuous_eval fun v =>
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => H) i).comp
        (continuous_eval_const (PiLp.single (p := 2) (β := fun _ : Fin 2 => H) j v) :
          Continuous fun T : H₂ →Lₚₜ[ℂ] H₂ =>
            T (PiLp.single (p := 2) (β := fun _ : Fin 2 => H) j v))).congr
        fun T => (ContinuousLinearMap.piLpEntry_apply (T : H₂ →L[ℂ] H₂) i j v).symm
  have hψ_X : (entrySOT 0 1 (q₂ X), entrySOT 1 0 (q₂ X)) = φ x := by simp [entrySOT, φ, X, q₂]
  rw [← hψ_X]
  refine map_mem_closure (f := fun T => (entrySOT 0 1 T, entrySOT 1 0 T))
    ((hentry_cont 0 1).prodMk (hentry_cont 1 0)) hX_cl ?_
  rintro _ ⟨A, ⟨⟨hAS, hAsa⟩, hAr⟩, rfl⟩
  rw [mem_closedBall_zero_iff] at hAr
  have h10 : A.piLpEntry 1 0 = star (A.piLpEntry 0 1) :=
    ((ContinuousLinearMap.isSelfAdjoint_iff_piLpEntry A).mp hAsa 1 0).symm
  refine ⟨A.piLpEntry 0 1, ⟨(S.mem_piLpMatrix_iff.mp hAS) 0 1, mem_closedBall_zero_iff.mpr
    ((A.norm_piLpEntry_le 0 1).trans hAr)⟩, ?_⟩
  simp [entrySOT, φ, q₂, h10]

/-- **Strong-star Kaplansky density (finite-vector form).** An operator `x` in the double
commutant of a unital star subalgebra `S` is simultaneously approximated on any finite family of
vectors, together with its adjoint `star x`, by elements `a ∈ S` with `‖a‖ ≤ ‖x‖`. -/
theorem exists_norm_le_and_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ S, ‖a‖ ≤ ‖x‖ ∧ (∀ i, ‖x (v i) - a (v i)‖ < ε) ∧
      (∀ i, ‖star x (v i) - star a (v i)‖ < ε) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : (q x, q (star x)) ∈ closure ((fun a : H →L[ℂ] H => (q a, q (star a))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 ‖x‖)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_prod_star_inter_closedBall ‖x‖]
    exact ⟨x, ⟨hx, mem_closedBall_zero_iff.mpr le_rfl⟩, rfl⟩
  let U : Set ((H →Lₚₜ[ℂ] H) × (H →Lₚₜ[ℂ] H)) :=
    (⋂ i : ι, {p | ‖q x (v i) - p.1 (v i)‖ < ε}) ∩
      (⋂ i : ι, {p | ‖q (star x) (v i) - p.2 (v i)‖ < ε})
  have hU_open : IsOpen U := by
    refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_lt
        ((continuous_const.sub ((continuous_eval_const (v i)).comp continuous_fst)).norm)
        continuous_const
    · exact isOpen_lt
        ((continuous_const.sub ((continuous_eval_const (v i)).comp continuous_snd)).norm)
        continuous_const
  have hU_mem : (q x, q (star x)) ∈ U := by simp [U, hε]
  obtain ⟨_, hU_p, ⟨a, ⟨haS, hanorm⟩, rfl⟩⟩ := mem_closure_iff.mp hmem U hU_open hU_mem
  rw [mem_closedBall_zero_iff] at hanorm
  simp only [U, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, q,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] at hU_p
  exact ⟨a, haS, hanorm, hU_p.1, hU_p.2⟩

/-- **The Kaplansky density theorem (strong operator topology).** For a unital star subalgebra `S`
of `H →L[ℂ] H` and every radius `r`, the strong operator closure of the closed ball of radius `r`
in `S` is the closed ball of radius `r` in its double commutant `S''`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer))
      (S.isClosed_sot_double_centralizer_inter_closedBall r)) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hmem : (q x, q (star x)) ∈ closure ((fun a : H →L[ℂ] H => (q a, q (star a))) ''
      ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_prod_star_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  exact map_mem_closure (f := Prod.fst) continuous_fst hmem
    (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)

/-- **The Kaplansky density theorem (unit-ball form).** For a unital star subalgebra `S` of
`H →L[ℂ] H`, the strong operator closure of the closed unit ball of `S` is the closed unit ball of
its double commutant `S''`. -/
theorem closure_unitBall_eq_unitBall_double_centralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ S ∧ ‖x‖ ≤ 1}) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        {x | x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer ∧ ‖x‖ ≤ 1} := by
  simpa only [Set.inter_def, SetLike.mem_coe, mem_closedBall_zero_iff] using
    S.closure_image_toPointwiseConvergenceCLM_inter_closedBall 1

/-- **The Kaplansky density theorem (weak operator topology).** For a unital star subalgebra `S`
of `H →L[ℂ] H` and every radius `r`, the weak operator closure of the closed ball of radius `r` in
`S` is the closed ball of radius `r` in its double commutant `S''`. -/
theorem closure_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      ContinuousLinearMapWOT.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  have hwot : IsClosed (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    rw [← VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset]
    exact ((VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))).isCompact_image_ofCLM_inter_closedBall
      0 r).isClosed
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer)) hwot) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hmem : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  simpa only [Set.image_image, Function.comp_def,
    ContinuousLinearMap.toPointwiseConvergenceCLM_apply] using
    mem_closure_image
      ContinuousLinearMapWOT.continuous_ofPointwiseConvergenceCLM.continuousAt hmem

/-- **The Kaplansky density theorem (ultrastrong topology).** For a unital star subalgebra `S` of
`H →L[ℂ] H` and every radius `r`, the ultrastrong closure of the closed ball of radius `r` in `S`
is the closed ball of radius `r` in its double commutant `S''`. -/
theorem closure_image_ultrastrong_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltrastrong.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set u := TauCeti.ContinuousLinearMapUltrastrong.ofCLM (𝕜 := ℂ) (E := H) (F := H)
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hclosed : IsClosed (u '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩
      closedBall 0 r)) := by
    convert (S.isClosed_sot_double_centralizer_inter_closedBall r).preimage
      TauCeti.ContinuousLinearMapUltrastrong.continuous_toPointwiseConvergenceCLM using 1
    ext A
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, TauCeti.ContinuousLinearMapUltrastrong.equiv.injective
        (ContinuousLinearMap.toPointwiseConvergenceCLM_injective h)⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer)) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  -- On the closed ball of radius `r`, the ultrastrong topology agrees with the strong topology.
  let B : Set (TauCeti.ContinuousLinearMapUltrastrong ℂ H H) := u '' closedBall 0 r
  have hind := TauCeti.ContinuousLinearMapUltrastrong.isInducing_restrict_toPointwiseConvergenceCLM
    (s := B) (C := r) (by rintro _ ⟨a, ha, rfl⟩; exact mem_closedBall_zero_iff.mp ha)
  let s₀ : Set B := Subtype.val ⁻¹' (u '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r))
  have himg : B.domRestrict (fun A : TauCeti.ContinuousLinearMapUltrastrong ℂ H H => q A.toCLM) ''
      s₀ = q '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r) := by
    ext T
    simp only [Set.mem_image, Set.mem_preimage, Set.domRestrict_apply, Subtype.exists, s₀, B, u]
    constructor
    · rintro ⟨_, ⟨_, _, rfl⟩, ⟨a, ha, hEq⟩, rfl⟩
      exact ⟨a, ha, by cases hEq; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨u a, ⟨a, ha.2, rfl⟩, ⟨a, ha, rfl⟩, rfl⟩
  have hmem_s₀ : (⟨u x, ⟨x, hx.2, rfl⟩⟩ : B) ∈ closure s₀ := by
    rw [hind.closure_eq_preimage_closure_image, Set.mem_preimage, himg,
      S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  exact closure_mono (Set.image_preimage_subset Subtype.val _)
    (image_closure_subset_closure_image continuous_subtype_val ⟨_, hmem_s₀, rfl⟩)

/-- **The Kaplansky density theorem (ultraweak topology).** For a unital star subalgebra `S` of
`H →L[ℂ] H` and every radius `r`, the ultraweak closure of the closed ball of radius `r` in `S` is
the closed ball of radius `r` in its double commutant `S''`. -/
theorem closure_image_ultraweak_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) =
      TauCeti.ContinuousLinearMapUltraweak.ofCLM ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r) := by
  set w := TauCeti.ContinuousLinearMapUltraweak.ofCLM (𝕜 := ℂ) (E := H) (F := H)
  have hwot : IsClosed (ContinuousLinearMapWOT.ofCLM ''
      ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r)) := by
    rw [← VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset]
    exact ((VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))).isCompact_image_ofCLM_inter_closedBall
      0 r).isClosed
  have hclosed : IsClosed (w '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩
      closedBall 0 r)) := by
    convert hwot.preimage TauCeti.ContinuousLinearMapUltraweak.continuous_toWOT using 1
    ext A
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, TauCeti.ContinuousLinearMapUltraweak.equiv.injective
        (ContinuousLinearMapWOT.ofCLM_injective h)⟩
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer)) hclosed) ?_
  rintro _ ⟨x, hx, rfl⟩
  -- On the closed ball of radius `r`, the ultraweak topology agrees with the weak operator
  -- topology.
  let B : Set (TauCeti.ContinuousLinearMapUltraweak ℂ H H) := w '' closedBall 0 r
  have hind := TauCeti.ContinuousLinearMapUltraweak.isInducing_restrict_toWOT
    (s := B) (C := r) (by rintro _ ⟨a, ha, rfl⟩; exact mem_closedBall_zero_iff.mp ha)
  let s₀ : Set B := Subtype.val ⁻¹' (w '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r))
  have himg : B.domRestrict (fun A : TauCeti.ContinuousLinearMapUltraweak ℂ H H =>
      ContinuousLinearMapWOT.ofCLM A.toCLM) '' s₀ =
      ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r) := by
    ext T
    simp only [Set.mem_image, Set.mem_preimage, Set.domRestrict_apply, Subtype.exists, s₀, B, w]
    constructor
    · rintro ⟨_, ⟨_, _, rfl⟩, ⟨a, ha, hEq⟩, rfl⟩
      exact ⟨a, ha, by cases hEq; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨w a, ⟨a, ha.2, rfl⟩, ⟨a, ha, rfl⟩, rfl⟩
  have hmem_s₀ : (⟨w x, ⟨x, hx.2, rfl⟩⟩ : B) ∈ closure s₀ := by
    rw [hind.closure_eq_preimage_closure_image, Set.mem_preimage, himg,
      S.closure_image_ofCLM_inter_closedBall r]
    exact ⟨x, hx, rfl⟩
  exact closure_mono (Set.image_preimage_subset Subtype.val _)
    (image_closure_subset_closure_image continuous_subtype_val ⟨_, hmem_s₀, rfl⟩)

/-! ### Positive Kaplansky density -/

/-- **Positive Kaplansky density.** For a unital star subalgebra `S` of `H →L[ℂ] H` and every
radius `r`, the strong operator closure of the positive operators in `S` of norm at most `r` is
the set of positive operators in `S''` of norm at most `r`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Ici_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Set.Ici 0 ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Set.Ici 0 ∩ closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hclosed : IsClosed (q '' ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩
      Set.Ici 0 ∩ closedBall 0 r)) := by
    have h1 := S.isClosed_sot_double_centralizer_inter_closedBall r
    have h2 :=
      ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
        (ContinuousLinearMapWOT.isClosed_image_ofCLM_Ici (a := (0 : H →L[ℂ] H)))
    convert h1.inter h2 using 1
    rw [← Set.image_inter ContinuousLinearMap.toPointwiseConvergenceCLM_injective]
    congr 1
    exact Set.inter_right_comm _ _ _
  refine subset_antisymm
    (closure_minimal (Set.image_mono (Set.inter_subset_inter_left _
      (Set.inter_subset_inter_left _ Set.subset_centralizer_centralizer))) hclosed) ?_
  rintro _ ⟨x, ⟨⟨hx, hx0⟩, hxr⟩, rfl⟩
  rw [Set.mem_Ici] at hx0
  rw [mem_closedBall_zero_iff] at hxr
  have hr : 0 ≤ r := (norm_nonneg x).trans hxr
  -- Approximate `CFC.sqrt x` strongly by self-adjoint operators in `S` of norm at most `√r`,
  -- then square them using bounded composition continuity.
  have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
  set y : H →L[ℂ] H := CFC.sqrt x
  have hy : y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM] at hx ⊢
    exact cfcₙ_nnreal_mem (𝕜 := ℂ) NNReal.sqrt hx
  have hy_cl : q y ∈ closure (q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩
      closedBall 0 √r)) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall √r]
    exact ⟨y, ⟨⟨hy, (CFC.sqrt_nonneg x).isSelfAdjoint⟩,
      mem_closedBall_zero_iff.mpr (by rw [CFC.norm_sqrt x hx0]; exact Real.sqrt_le_sqrt hxr)⟩, rfl⟩
  let toCLM : (H →Lₚₜ[ℂ] H) → (H →L[ℂ] H) := fun T => T
  let l : Filter (H →Lₚₜ[ℂ] H) :=
    𝓝 (q y) ⊓ 𝓟 (q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 √r))
  have : l.NeBot := mem_closure_iff_clusterPt.mp hy_cl
  have hmem : ∀ᶠ T in l,
      toCLM T ∈ (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 √r := by
    filter_upwards [Filter.mem_inf_of_right (mem_principal_self _)] with T hT
    rcases hT with ⟨a, ha, rfl⟩
    exact ha
  have hlim : ∀ v, Tendsto (fun T : H →Lₚₜ[ℂ] H => toCLM T v) l (𝓝 (y v)) :=
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (Filter.tendsto_inf_left tendsto_id)
  have hsq_tend : Tendsto (fun T : H →Lₚₜ[ℂ] H => q (toCLM T * toCLM T)) l (𝓝 (q x)) := by
    rw [← CFC.sqrt_mul_sqrt_self x hx0, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro v
    exact ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
      (hmem.mono fun _ h => mem_closedBall_zero_iff.mp h.2) v
  refine mem_closure_of_tendsto hsq_tend (hmem.mono fun T hT => ?_)
  refine ⟨toCLM T * toCLM T, ⟨⟨mul_mem hT.1.1 hT.1.1, ?_⟩, ?_⟩, rfl⟩
  · have hmul : toCLM T * toCLM T = star (toCLM T) * toCLM T := by rw [hT.1.2.star_eq]
    rw [Set.mem_Ici, hmul]
    exact star_mul_self_nonneg (toCLM T)
  · have hTn : ‖toCLM T‖ ≤ √r := mem_closedBall_zero_iff.mp hT.2
    rw [mem_closedBall_zero_iff]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul hTn hTn (norm_nonneg _) (Real.sqrt_nonneg r)).trans_eq (Real.mul_self_sqrt hr))

/-- **Positive Kaplansky density (unit-ball form).** The strong operator closure of the positive
contractions `0 ≤ a ≤ 1` in a unital star subalgebra `S` is the set of positive contractions in
its double commutant `S''`. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Icc_zero_one
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ Set.Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Set.Icc 0 1) := by
  have hIcc : Set.Icc (0 : H →L[ℂ] H) 1 = Set.Ici 0 ∩ closedBall 0 1 := by
    ext x
    rw [CStarAlgebra.mem_Icc_iff_norm_le_one, Set.mem_inter_iff, Set.mem_Ici,
      mem_closedBall_zero_iff]
  simpa only [hIcc, Set.inter_assoc] using
    S.closure_image_toPointwiseConvergenceCLM_inter_Ici_inter_closedBall 1

/-! ### Unit-ball characterizations of von Neumann algebras -/

/-- A unital star subalgebra equals its double commutant if and only if its closed ball of any
positive radius `r` is closed in the strong operator topology. -/
theorem double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  constructor
  · intro h
    rw [← h]
    exact S.isClosed_sot_double_centralizer_inter_closedBall r
  · intro hclosed
    have hball : (S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ closedBall 0 r =
        (S : Set (H →L[ℂ] H)) ∩ closedBall 0 r := by
      apply Set.image_injective.mpr ContinuousLinearMap.toPointwiseConvergenceCLM_injective
      rw [← S.closure_image_toPointwiseConvergenceCLM_inter_closedBall r, hclosed.closure_eq]
    refine subset_antisymm (fun x hx => ?_) Set.subset_centralizer_centralizer
    by_cases hx0 : x = 0
    · exact hx0 ▸ zero_mem S
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hc : 0 < r / ‖x‖ := div_pos hr hxn
      have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
          (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
        VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
      have hcx_cc : ((r / ‖x‖ : ℝ) : ℂ) • x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
        rw [← hM] at hx ⊢
        exact SMulMemClass.smul_mem _ hx
      have hcx_ball : ((r / ‖x‖ : ℝ) : ℂ) • x ∈ closedBall 0 r := by
        rw [mem_closedBall_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le,
          div_mul_cancel₀ r hxn.ne']
      have hcx_S : ((r / ‖x‖ : ℝ) : ℂ) • x ∈ S := (hball.subset ⟨hcx_cc, hcx_ball⟩).1
      have hx_eq : (((r / ‖x‖ : ℝ)⁻¹ : ℝ) : ℂ) • (((r / ‖x‖ : ℝ) : ℂ) • x) = x := by
        rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
      rw [← hx_eq]
      exact SMulMemClass.smul_mem _ hcx_S

/-- **Unit-ball compactness characterization of von Neumann algebras.** A unital star subalgebra
equals its double commutant if and only if its closed ball of any positive radius `r` is weak
operator compact. -/
theorem double_commutant_iff_isCompact_image_ofCLM_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {r : ℝ} (hr : 0 < r) :
    (S : Set (H →L[ℂ] H)).centralizer.centralizer = S ↔
      IsCompact (ContinuousLinearMapWOT.ofCLM '' ((S : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  constructor
  · intro h
    let M : VonNeumannAlgebra H := ⟨S, h⟩
    exact M.isCompact_image_ofCLM_inter_closedBall 0 r
  · intro hcomp
    rw [S.double_commutant_iff_isClosed_image_toPointwiseConvergenceCLM_inter_closedBall hr]
    exact ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      hcomp.isClosed

end StarSubalgebra

/-! ### Bounded strong approximation for generated von Neumann algebras -/

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every closed norm ball of the von Neumann algebra generated by `s` is the strong operator
closure of the corresponding ball of the star algebra generated by `s`. -/
theorem image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure
    (s : Set (H →L[ℂ] H)) (r : ℝ) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((adjoin s : Set (H →L[ℂ] H)) ∩ closedBall 0 r) =
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  rw [(StarAlgebra.adjoin ℂ s).closure_image_toPointwiseConvergenceCLM_inter_closedBall r,
    ← adjoin_starAlgebraAdjoin,
    coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]

/-- **Strong-star Kaplansky density for a generated von Neumann algebra.** An operator `x` in
`VonNeumannAlgebra.adjoin s` is simultaneously approximated on any finite family of vectors,
together with `star x`, by elements `t ∈ StarAlgebra.adjoin ℂ s` with `‖t‖ ≤ ‖x‖`. -/
theorem exists_norm_le_and_forall_norm_sub_apply_lt_of_mem_adjoin
    {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} (hx : x ∈ adjoin s)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ StarAlgebra.adjoin ℂ s, ‖t‖ ≤ ‖x‖ ∧ (∀ i, ‖x (v i) - t (v i)‖ < ε) ∧
      (∀ i, ‖star x (v i) - star t (v i)‖ < ε) := by
  refine StarSubalgebra.exists_norm_le_and_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    (StarAlgebra.adjoin ℂ s) ?_ v hε
  rw [← coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset, adjoin_starAlgebraAdjoin]
  exact hx

/-- An operator lies in the von Neumann algebra generated by `s` if and only if it is a strong
operator limit of a norm-bounded subset of the star algebra generated by `s`. -/
theorem mem_adjoin_iff_exists_mem_closure_closedBall {s : Set (H →L[ℂ] H)} {x : H →L[ℂ] H} :
    x ∈ adjoin s ↔ ∃ r : ℝ,
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H x ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          ((StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H)) ∩ closedBall 0 r)) := by
  constructor
  · intro hx
    refine ⟨‖x‖, ?_⟩
    rw [← image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure]
    exact ⟨x, ⟨hx, mem_closedBall_zero_iff.mpr le_rfl⟩, rfl⟩
  · rintro ⟨r, hr⟩
    rw [← image_toPointwiseConvergenceCLM_adjoin_inter_closedBall_eq_closure] at hr
    exact ((ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image).mp hr).1

end VonNeumannAlgebra
