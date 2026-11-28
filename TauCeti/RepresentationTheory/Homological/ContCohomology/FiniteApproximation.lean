/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.GroupAction.FixedPoints
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.GroupAction.ForcedDiscrete
public import TauCeti.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.GroupTheory.QuotientGroup.Map
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Finite-quotient approximation of continuous 1-cochains

For a profinite group acting isometrically on seminormed coefficients, approximate continuous
1-cochains uniformly by finite-quotient cochains in a dense discrete coefficient module. The
approximants take values fixed by the subgroup defining the quotient, and their differentials
approximate the original differential to the same precision. This supplies the finite cochains
used in the trace-homotopy argument for the cohomology of completed algebraic closures. In that
application the discrete-action hypothesis comes from open stabilizers for the Krull topology
and the dense map is the completion inclusion.

* `TauCeti.ContCohomology.norm_d1_apply_sub_lt_three_mul` bounds the difference of degree-one
  differentials.
* `ContinuousMap.exists_finiteQuotient_approx_d1` constructs the approximating cochain and
  controls its differential. It uses `TauCeti.dense_setOf_comp_quotientMk` and
  `TauCeti.exists_openNormalSubgroup_smul_eq_self_range`.

See Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory*, §14.3, Lemma 14.3.1.
-/

public section

open TauCeti TauCeti.ContCohomology

namespace TauCeti.ContCohomology

variable {G E : Type*} [Mul G] [SeminormedAddCommGroup E] [DistribSMul G E]
  [IsIsometricSMul G E]

/-- For an isometric action, the difference of the degree-one differentials is bounded by
three times a uniform strict bound on the difference of the cochains. -/
theorem norm_d1_apply_sub_lt_three_mul {f a : G → E} {ε : ℝ}
    (ha : ∀ g, ‖f g - a g‖ < ε) (g h : G) :
    ‖d1 G E f (g, h) - d1 G E a (g, h)‖ < 3 * ε := by
  have hsmul : ‖g • (f h - a h)‖ < ε := by
    rw [IsIsometricSMul.norm_smul]
    exact ha h
  have hdiff : d1 G E f (g, h) - d1 G E a (g, h) = d1 G E (f - a) (g, h) := by
    rw [map_sub, Pi.sub_apply]
  rw [hdiff, d1_apply]
  simp only [Pi.sub_apply]
  calc
    _ ≤ (‖g • (f h - a h)‖ + ‖f (g * h) - a (g * h)‖) + ‖f g - a g‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ < (ε + ε) + ε := add_lt_add (add_lt_add hsmul (ha (g * h))) (ha g)
    _ = 3 * ε := by ring

end TauCeti.ContCohomology

namespace ContinuousMap

variable {G A E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [AddCommGroup A] [DistribMulAction G A] [ContinuousSMul G (ForcedDiscrete A)]
  [SeminormedAddCommGroup E] [DistribMulAction G E] [IsIsometricSMul G E]

/-- A continuous cochain can be approximated uniformly, together with its differential, by a
cochain on a finite quotient with values in the subgroup invariants of a dense discrete
coefficient module. Both errors are bounded by the same prescribed positive radius. -/
theorem exists_finiteQuotient_approx_d1 (f : C(G, E)) (φ : A →+[G] E)
    (hφ : DenseRange φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : OpenNormalSubgroup G) (a : G ⧸ U.toSubgroup → FixedPoints.addSubgroup U.toSubgroup A),
      (∀ g : G, ‖f g - φ (a (QuotientGroup.mk g))‖ < ε) ∧
      ∀ g h : G, ‖d1 G E f (g, h) -
        φ (d1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup A) a
          (QuotientGroup.mk g, QuotientGroup.mk h))‖ < ε := by
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨b, ⟨V, c, hc⟩, hb⟩ :=
    (dense_setOf_comp_quotientMk (G := G) E).exists_dist_lt f (half_pos hthird)
  -- Replace each of the finitely many approximating values by a dense coefficient.
  choose x hx using fun q ↦ hφ.exists_dist_lt (c q) (half_pos hthird)
  obtain ⟨W, hW⟩ :=
    exists_openNormalSubgroup_smul_eq_self_range (G := G) (ForcedDiscrete.addEquiv A ∘ x)
  let U := V ⊓ W
  let π := QuotientGroup.mapOfLE (inf_le_left : U.toSubgroup ≤ V.toSubgroup)
  let a (q : G ⧸ U.toSubgroup) : FixedPoints.addSubgroup U.toSubgroup A :=
    ⟨x (π q), (FixedPoints.mem_addSubgroup _ _ _).2 fun u ↦ by
      have hu : (u : G) ∈ W := (inf_le_right : U ≤ W) u.property
      have hfix := hW u hu (π q)
      simp only [Function.comp_apply, ForcedDiscrete.smul_addEquiv] at hfix
      exact (ForcedDiscrete.addEquiv A).injective hfix⟩
  have ha (g : G) : ‖f g - φ (a (QuotientGroup.mk g))‖ < ε / 3 := by
    have hcg : c (QuotientGroup.mk g) = b g := congrFun hc g
    have hfg : dist (f g) (c (QuotientGroup.mk g)) < (ε / 3) / 2 := by
      rw [hcg]
      exact ContinuousMap.dist_lt_iff_of_nonempty.mp hb g
    have ha' : (a (QuotientGroup.mk g) : A) = x (QuotientGroup.mk g) :=
      congrArg x (QuotientGroup.mapOfLE_mk (inf_le_left : U.toSubgroup ≤ V.toSubgroup) g)
    rw [ha', ← dist_eq_norm]
    exact (dist_triangle _ (c (QuotientGroup.mk g)) _).trans_lt
      (add_halves (ε / 3) ▸ add_lt_add hfg (hx (QuotientGroup.mk g)))
  have hle : ε / 3 ≤ ε := div_le_self hε.le (by norm_num)
  refine ⟨U, a, fun g ↦ (ha g).trans_le hle, fun g h ↦ ?_⟩
  -- Pulling back the quotient differential agrees with differentiating the approximant.
  have hmap :
      φ (d1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup A) a
        (QuotientGroup.mk g, QuotientGroup.mk h)) =
      d1 G E (fun k ↦ φ (a (QuotientGroup.mk k))) (g, h) := by
    simp only [d1_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub, map_add, map_sub,
      coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup, map_smul,
      QuotientGroup.mk_mul]
  rw [hmap]
  calc
    _ < 3 * (ε / 3) := norm_d1_apply_sub_lt_three_mul ha g h
    _ = ε := by ring

end ContinuousMap
