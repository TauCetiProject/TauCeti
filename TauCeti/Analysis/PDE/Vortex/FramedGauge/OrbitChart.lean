/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.CoulombGauge
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SliceChart
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice
import Mathlib.Topology.LocalAtTarget
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Proper
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Slice

/-!
# The Coulomb slices chart the orbit space of framed plane vortex fields and the vortex moduli

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts freely and continuously on the continuous
fields of the affine space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)`
(`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb slice is cut out by the
gauge-fixing condition `d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the formal `L²` adjoint of
the infinitesimal gauge action at `x`. This file proves the slice theorem: near `x`, the Coulomb
slice is a chart of the orbit space `A_m^k / G_(k+1)`.

There is an open neighbourhood `V` of `x` such that `y ↦ [y]` is an open embedding of the fields
of `V` in the Coulomb slice of `x` into `A_m^k / G_(k+1)`
(`TauCeti.Vortex.SobolevFieldSpace.`
`exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero`). So each gauge orbit near the
orbit of `x` meets the slice near `x` exactly once, and the slice near `x` is homeomorphic to an
open neighbourhood of `[x]`. The inputs are the existence of the Coulomb gauge near `x`, a
continuous gauge moving each nearby field into the slice
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice`),
its local uniqueness near `1`
(`TauCeti.Vortex.SobolevFieldSpace.exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice`),
and the properness of the action (`TauCeti.Vortex.SobolevFieldSpace.properSMul`), which excludes
gauges far from `1` between fields near `x`. The topological argument is
`ProperSMul.exists_isOpen_isOpenEmbedding_quotientMk_inter`.

**The vortex moduli.** At a plane vortex `x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in every `A_m^j`,
the vortices in its Coulomb slice form a `2m`-dimensional analytic submanifold near it, with the
chart `TauCeti.Vortex.coulombSliceChart` on their real coordinates. The slice theorem carries this
chart to the orbit space. A gauge orbit of a field in the slice near `x₀` is a vortex orbit exactly
when that field is a vortex, since the vortex equation is gauge invariant
(`TauCeti.Vortex.SobolevFieldSpace.mk_mem_vortexModuli_iff`). So the open embedding of the slice
near `x₀` into `A_m^(k+1) / G_(k+2)` restricts to an open embedding of the vortices of the slice
near `x₀` into the moduli space `TauCeti.Vortex.SobolevFieldSpace.vortexModuli` of vortex orbits.
Composed with the Coulomb slice chart, it gives a chart of the vortex moduli at the orbit of `x₀`,
modelled on `ℝ^(2m)` and sending that orbit to `0`
(`TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli`). The chart reads an
orbit through its representative in the Coulomb slice near `x₀`, and on such a representative it is
the Coulomb slice chart
(`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_openPartialHomeomorph_vortexModuli_eq`). The two
orders of the same field space, `↑(k + 1)` for the gauge action and `↑k + 1` for the real chart,
are identified by `TauCeti.Vortex.SobolevFieldSpace.congrOrder`.

With these charts, invariance of domain makes the zero divisor a homeomorphism from the vortex
moduli onto `Sym^m ℂ` (`TauCeti.Analysis.PDE.Vortex.FramedGauge.SymmetricPower`). Whether the
transition maps of the charts are smooth is not treated here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.`
  `exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero`: near a field, its Coulomb
  slice embeds openly into the orbit space.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_openPartialHomeomorph_vortexModuli_eq`: near a
  vortex lying in every `A_m^j`, the Coulomb slice chart induces a chart of the vortex moduli
  space.
* `TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli`: the vortex moduli
  space is locally homeomorphic to `ℝ^(2m)` at the orbit of every vortex lying in every `A_m^j`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open BesselPotentialSpace Filter Topology SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

section

variable [Fact (1 < k)]

/-- **The slice theorem for framed plane vortex fields.** Let `x` be a continuous field of
`A_m^k`, `k ≥ 3`. There is an open neighbourhood `V` of `x` such that `y ↦ [y]` is an open
embedding into the orbit space `A_m^k / G_(k+1)` of the fields `y ∈ V` in the Coulomb slice
`d₀* (y - x) = 0` of `x`. -/
theorem exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero
    (hs : 1 < (k : ℝ) + 1) (hk : 3 ≤ k) (x : SobolevFieldSpace f m k) :
    ∃ V : Set (SobolevFieldSpace f m k), IsOpen V ∧ x ∈ V ∧
      IsOpenEmbedding fun y : ↥(V ∩ {y | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0}) ↦
        Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
          (SobolevFieldSpace f m k)) (y : SobolevFieldSpace f m k) := by
  have := properSMul f m hs (by omega)
  obtain ⟨U₁, hU₁, γ, hγ, hγx, hγS⟩ :=
    exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice hs hk x
  obtain ⟨U₂, hU₂, N, hN, huniq⟩ :=
    exists_mem_nhds_forall_eq_one_of_smul_mem_coulombSlice hs hk x
  obtain ⟨V, hV, hxV, -, hemb⟩ := ProperSMul.exists_isOpen_isOpenEmbedding_quotientMk_inter
    (S := {y : SobolevFieldSpace f m k | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0})
    (IsCancelSMul.stabilizer_eq_bot x) (Filter.inter_mem hU₁ hU₂) (hγ.mono Set.inter_subset_left)
    hγx (fun y hy ↦ mem_coulombSlice.1 (hγS y hy.1)) hN fun y hy u hu hy₀ huy₀ ↦
      huniq y hy.2 u hu (mem_coulombSlice.2 hy₀) (mem_coulombSlice.2 huy₀)
  exact ⟨V, hV, hxV, hemb⟩

end

/-! ### Charts of the vortex moduli -/

/-- The real coordinates of a field `y` of `A_m^(k+1)` are a zero of the slice equation through a
field `x` exactly when `y` is a vortex in the Coulomb slice of `x`. This is
`TauCeti.Vortex.realSobolevSliceEquation_realSubRef_eq_zero_iff` for the fields of order
`↑(k + 1)`, on which `G_(k+2)` acts, read at the order `↑k + 1` of the real chart. -/
theorem realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff (hk : 2 ≤ k)
    (x y : SobolevFieldSpace f m (k + 1 : ℕ)) :
    realSobolevSliceEquation f m hk (congrOrder (Nat.cast_succ k) x)
        ((congrOrder (Nat.cast_succ k) y).realSubRef (k.cast_add_one_pos (α := ℝ)).le) = 0 ↔
      y ∈ coulombSlice x ∧ ∀ z, equation y z = 0 := by
  simp only [realSobolevSliceEquation_realSubRef_eq_zero_iff, mem_coulombSlice, coe_congrOrder,
    funext_iff, Pi.zero_apply]

variable [Fact (1 < k + 1)] {hs : 1 < ((k + 1 : ℕ) : ℝ) + 1}

/-- The real coordinates, at the order `↑k + 1`, of the vortices in the Coulomb slice of `x₀` that
lie in an open set `V` embed them openly into the zero set of the slice equation through `x₀`. -/
private theorem isOpenEmbedding_realSubRef_congrOrder (hk : 2 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) {V : Set (SobolevFieldSpace f m (k + 1 : ℕ))}
    (hV : IsOpen V) :
    IsOpenEmbedding fun p : {y : ↥(V ∩ {y | ∀ z, gaugeAdjoint x₀ (⇑y - ⇑x₀) z = 0}) |
        Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
          (SobolevFieldSpace f m (k + 1 : ℕ))) (y : SobolevFieldSpace f m (k + 1 : ℕ)) ∈
            vortexModuli f m hs} ↦
      (⟨(congrOrder (Nat.cast_succ k) p.val.val).realSubRef (k.cast_add_one_pos (α := ℝ)).le,
        (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ _).2
          ⟨mem_coulombSlice.2 p.val.property.2,
            (mk_mem_vortexModuli_iff (by omega)).1 p.property⟩⟩ :
        {u | realSobolevSliceEquation f m hk (congrOrder (Nat.cast_succ k) x₀) u = 0}) := by
  have hs' : 1 < (k : ℝ) + 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set φ : SobolevFieldSpace f m (k + 1 : ℕ) ≃ₜ
      (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :=
    (congrOrder (Nat.cast_succ k)).trans (realSubRefHomeomorph hs')
  have hφ (y : SobolevFieldSpace f m (k + 1 : ℕ)) :
      φ y = (congrOrder (Nat.cast_succ k) y).realSubRef (k.cast_add_one_pos (α := ℝ)).le := by
    simp [φ]
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1 ?_, ?_⟩
  · convert φ.isEmbedding.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) using 1
    exact funext fun p ↦ (hφ _).symm
  -- The image consists of the zeros whose field lies in `V`.
  convert (hV.preimage φ.symm.continuous).preimage continuous_subtypeVal
  ext u
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    simpa [← hφ] using p.val.property.1
  · have h0 := u.property
    rw [Set.mem_ofPred_eq, ← φ.apply_symm_apply u.val, hφ,
      realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff] at h0
    exact ⟨⟨⟨φ.symm u, hu, mem_coulombSlice.1 h0.1⟩, mk_mem_vortexModuli h0.2⟩,
      Subtype.ext ((hφ _).symm.trans (φ.apply_symm_apply u.val))⟩

/-- **The Coulomb slice chart is a chart of the vortex moduli.** Let `x₀` be a continuous vortex
of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`. There are an open neighbourhood `V` of
`x₀` and a chart `e` of the vortex moduli space in `A_m^(k+1) / G_(k+2)` with values in `ℝ^(2m)`,
such that

* every orbit in the source of `e` has a representative in `V` in the Coulomb slice of `x₀`;
* on the orbit of a vortex `y ∈ V` in the Coulomb slice of `x₀`, `e` is the Coulomb slice chart
  `coulombSliceChart` at the real coordinates of `y`, and the orbit lies in the source of `e`
  exactly when these coordinates lie in the source of the Coulomb slice chart. -/
theorem exists_isOpen_openPartialHomeomorph_vortexModuli_eq (hk : 2 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x₀ z = 0) :
    ∃ V : Set (SobolevFieldSpace f m (k + 1 : ℕ)), IsOpen V ∧ x₀ ∈ V ∧
      ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
        (∀ q ∈ e.source, ∃ y ∈ V ∩ coulombSlice x₀, Quotient.mk _ y =
          (q : MulAction.orbitRel.Quotient (SobolevTopologicalGaugeGroup hs)
            (SobolevFieldSpace f m (k + 1 : ℕ)))) ∧
        ∀ y ∈ V, ∀ (hS : y ∈ coulombSlice x₀) (hy : ∀ z, equation y z = 0),
          let p : {u | realSobolevSliceEquation f m hk (congrOrder (Nat.cast_succ k) x₀) u = 0} :=
            ⟨_, (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ y).2 ⟨hS, hy⟩⟩
          let q : vortexModuli f m hs :=
            ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩
          let c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀)
            (coe_congrOrder _ x₀ ▸ hmem) (coe_congrOrder _ x₀ ▸ hsol)
          (q ∈ e.source ↔ p ∈ c.source) ∧ e q = c p := by
  have hk3 : 3 ≤ k + 1 := by omega
  have hmem' : ∀ j : ℕ, ⇑(congrOrder (Nat.cast_succ k) x₀) ∈ framedFieldSpace f m j :=
    coe_congrOrder _ x₀ ▸ hmem
  have hsol' : ∀ z, equation (congrOrder (Nat.cast_succ k) x₀) z = 0 :=
    coe_congrOrder _ x₀ ▸ hsol
  -- The slice theorem embeds the slice near `x₀` openly into the orbit space, so its vortices
  -- into the vortex moduli; their real coordinates embed them openly into the source of the
  -- Coulomb slice chart. The chart is the composite.
  obtain ⟨V, hV, hx₀V, hemb⟩ :=
    exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero hs hk3 x₀
  set ι := fun y : ↥(V ∩ {y | ∀ z, gaugeAdjoint x₀ (⇑y - ⇑x₀) z = 0}) ↦
    Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
      (SobolevFieldSpace f m (k + 1 : ℕ))) (y : SobolevFieldSpace f m (k + 1 : ℕ))
  have hι := hemb.restrictPreimage (vortexModuli f m hs)
  have hψ := isOpenEmbedding_realSubRef_congrOrder (hs := hs) hk x₀ hV
  have hne : Nonempty (ι ⁻¹' vortexModuli f m hs) :=
    ⟨⟨⟨x₀, hx₀V, mem_coulombSlice.1 (self_mem_coulombSlice x₀)⟩,
      mk_mem_vortexModuli hsol⟩⟩
  -- The same nonempty domain, written as the domain of the real coordinates.
  have : Nonempty {y : ↥(V ∩ {y | ∀ z, gaugeAdjoint x₀ (⇑y - ⇑x₀) z = 0}) |
      Quotient.mk _ (y : SobolevFieldSpace f m (k + 1 : ℕ)) ∈ vortexModuli f m hs} := hne
  refine ⟨V, hV, hx₀V, (hι.toOpenPartialHomeomorph _).symm.trans
    ((hψ.toOpenPartialHomeomorph _).trans (coulombSliceChart hk _ hmem' hsol')),
    fun q hq ↦ ?_, fun y hyV hS hy ↦ ?_⟩
  · obtain ⟨p, rfl⟩ : q ∈ Set.range ((vortexModuli f m hs).restrictPreimage ι) := by
      simpa using hq.1
    exact ⟨p.val.val, ⟨p.val.property.1, mem_coulombSlice.2 p.val.property.2⟩, rfl⟩
  · set p : ι ⁻¹' vortexModuli f m hs :=
      ⟨⟨y, hyV, mem_coulombSlice.1 hS⟩, mk_mem_vortexModuli hy⟩
    have hp : (hι.toOpenPartialHomeomorph _).symm ⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ = p :=
      hι.toOpenPartialHomeomorph_left_inv _ (x := p)
    have hq : (⟨Quotient.mk _ y, mk_mem_vortexModuli hy⟩ : vortexModuli f m hs) ∈
        Set.range ((vortexModuli f m hs).restrictPreimage ι) := ⟨p, rfl⟩
    -- The real coordinates of `p` are those of its field `y`.
    have hψp : hψ.toOpenPartialHomeomorph _ p =
        ⟨_, (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ y).2 ⟨hS, hy⟩⟩ :=
      Subtype.ext <| by rw [IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    refine ⟨?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        IsOpenEmbedding.toOpenPartialHomeomorph_target,
        IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_preimage, hp,
        hψp, Set.mem_univ, true_and, hq]
    · rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply, hp, hψp]

/-- **The vortex moduli space is locally homeomorphic to `ℝ^(2m)`.** Let `x₀` be a continuous
vortex of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, such as the smooth end-normalized
vortices of `TauCeti.Vortex.exists_contDiff_sobolevVortexDivisor_eq`. Then the vortex moduli space
in `A_m^(k+1) / G_(k+2)` has a chart at the orbit of `x₀` with values in `ℝ^(2m)`, sending that
orbit to `0`. -/
theorem exists_openPartialHomeomorph_vortexModuli (hk : 2 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x₀ z = 0) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      ⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ ∈ e.source ∧
        e ⟨Quotient.mk _ x₀, mk_mem_vortexModuli hsol⟩ = 0 := by
  obtain ⟨V, -, hx₀V, e, -, he⟩ :=
    exists_isOpen_openPartialHomeomorph_vortexModuli_eq (hs := hs) hk x₀ hmem hsol
  obtain ⟨hsrc, hval⟩ := he x₀ hx₀V (self_mem_coulombSlice x₀) hsol
  exact ⟨e, hsrc.2 (mem_coulombSliceChart_source hk _ _ _),
    hval.trans (coulombSliceChart_apply_self hk _ _ _)⟩

end SobolevFieldSpace

end TauCeti.Vortex
