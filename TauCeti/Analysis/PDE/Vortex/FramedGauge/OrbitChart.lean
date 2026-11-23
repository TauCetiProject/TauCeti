/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.CoulombGauge
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SliceChart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SobolevOrder
public import TauCeti.Analysis.PDE.Vortex.Moduli.Topology
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice
public import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.LocalAtTarget
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
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

**Global charts and comparison with `Sym^m ℂ` and the smooth framed moduli.** For `k ≥ 4`, every
continuous vortex of `A_m^k` is `C²` and has a smooth representative in `⋂_j A_m^j` in its
`G_(k+1)`-orbit (`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`), so every
point of `vortexModuli` admits a `ℝ^(2m)`-chart (`vortexModuliChartedSpace`). Moreover, the zero
divisor gives a continuous bijection `vortexModuliEquiv : vortexModuli ≃ Sym ℂ m`. Composed with
`Sym.coeffHomeomorph ℂ m : Sym ℂ m ≃ₜ ℂᵐ`, invariance of domain turns it into a
homeomorphism `vortexModuliHomeomorph : vortexModuli ≃ₜ Sym ℂ m`, and hence a homeomorphism
`vortexModuliHomeomorphFramedVortexModuli` with the smooth framed moduli space
`framedVortices 1 m / framedGaugeGroup` of `TauCeti.Vortex.framedVortexModuliHomeomorph`. Whether
the transition maps of the Coulomb slice charts are smooth is not treated here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.`
  `exists_isOpen_isOpenEmbedding_quotientMk_gaugeAdjoint_sub_eq_zero`: near a field, its Coulomb
  slice embeds openly into the orbit space.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_openPartialHomeomorph_vortexModuli_eq`: near a
  vortex lying in every `A_m^j`, the Coulomb slice chart induces a chart of the vortex moduli
  space.
* `TauCeti.Vortex.SobolevFieldSpace.exists_openPartialHomeomorph_vortexModuli`: the vortex moduli
  space is locally homeomorphic to `ℝ^(2m)` at the orbit of every vortex lying in every `A_m^j`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliChartedSpace`: for `k ≥ 4`, `vortexModuli` is
  charted on `ℝ^(2m)` at every orbit.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`: for `k ≥ 4`, the divisor identifies
  `vortexModuli` homeomorphically with `Sym ℂ m`.
* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorphFramedVortexModuli`: for `k ≥ 4`,
  `vortexModuli` is homeomorphic to the smooth framed vortex moduli space.

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

section

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

end

section Global

open scoped ContDiff

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-- **Every vortex orbit has a `ℝ^(2m)`-chart.** For `k ≥ 4`, every point `q` of `vortexModuli`
in `A_m^k / G_(k+1)` admits a chart modelled on `Fin (2 * m) → ℝ` sending `q` to `0`, without
assuming a smooth representative in advance
(`exists_sobolevGaugeGroup_smul_mem_framedFieldSpace`). -/
theorem exists_openPartialHomeomorph_vortexModuli_of_lt (hk : 3 < k) (q : vortexModuli f m hs) :
    ∃ e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ),
      q ∈ e.source ∧ e q = 0 := by
  revert hs q
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  intro hs q
  rcases q with ⟨q, hq⟩
  obtain ⟨x, hsol, rfl⟩ := mem_vortexModuli_iff.1 hq
  have hxc2 : ContDiff ℝ 2 x :=
    x.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k' + 1))
  obtain ⟨y, hyc, hys, -, u, hu, -⟩ :=
    exists_sobolevGaugeGroup_smul_mem_framedFieldSpace (hs := hs)
      ⟨x.toFramedFieldSpace, mem_sobolevVortices.2 ⟨hxc2, hsol⟩⟩
  let y' : SobolevFieldSpace f m (k' + 1 : ℕ) := ⟨y.val, y.val.property, hyc.continuous⟩
  have hxy : Quotient.mk (MulAction.orbitRel (SobolevTopologicalGaugeGroup hs)
      (SobolevFieldSpace f m (k' + 1 : ℕ))) y' = Quotient.mk _ x := by
    refine Quotient.sound (orbitRel_iff.2 ⟨u⁻¹, u⁻¹.property, ?_⟩)
    have h := congrArg (fun z : framedFieldSpace f m (k'.succ : ℕ) ↦
      ((u⁻¹ • z : framedFieldSpace f m (k'.succ : ℕ)) : ℂ → EuclideanSpace ℝ (Fin 4))) hu.symm
    rw [inv_smul_smul, coe_sobolevGaugeGroup_smul] at h
    exact h
  have hqeq :
      (⟨Quotient.mk _ y', mk_mem_vortexModuli (mem_sobolevVortices.1 y.property).2⟩ :
        vortexModuli f m hs) =
      ⟨Quotient.mk _ x, mk_mem_vortexModuli hsol⟩ := Subtype.ext hxy
  obtain ⟨e, hesrc, he0⟩ := exists_openPartialHomeomorph_vortexModuli (hs := hs) (by omega : 2 ≤ k')
    y' (fun j ↦ hys j) (mem_sobolevVortices.1 y.property).2
  exact ⟨e, hqeq ▸ hesrc, hqeq ▸ he0⟩

/-- **The charted space structure on `vortexModuli`.** For `k ≥ 4`, the Sobolev moduli space of
framed vortices is charted on `Fin (2 * m) → ℝ` at every orbit. -/
@[instance_reducible]
noncomputable def vortexModuliChartedSpace (hk : 3 < k) :
    ChartedSpace (Fin (2 * m) → ℝ) (vortexModuli f m hs) where
  atlas := Set.range fun q ↦ (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose
  chartAt q := (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose
  mem_chart_source q := (exists_openPartialHomeomorph_vortexModuli_of_lt hk q).choose_spec.1
  chart_mem_atlas q := Set.mem_range_self q

/-! ### Comparison with `Sym ℂ m` and the smooth framed moduli -/

/-- Two smooth fields of `A_m^k`, `k ≥ 2`, lie in the same `G_(k+1)`-orbit in
`SobolevFieldSpace f m k` if and only if they are related by a smooth framed gauge. -/
theorem orbitRel_iff_exists_framedGaugeGroup_smul_eq {x y : SobolevFieldSpace f m k}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) :
    MulAction.orbitRel (SobolevTopologicalGaugeGroup hs) (SobolevFieldSpace f m k) x y ↔
      ∃ u : framedGaugeGroup, u • (x : ℂ → EuclideanSpace ℝ (Fin 4)) = y := by
  have h := exists_framedGaugeGroup_smul_eq_iff_exists_sobolevGaugeGroup_smul_eq (hs := hs)
    (y := x.toFramedFieldSpace) (x := y.toFramedFieldSpace) hy hx
  rw [orbitRel_iff]
  simpa only [Subtype.ext_iff, coe_sobolevGaugeGroup_smul, coe_toFramedFieldSpace, Subtype.exists,
    exists_prop] using h.symm

/-- For `k ≥ 4`, the vortex moduli subset `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` is in canonical
bijection with `sobolevVortexSubMulAction hk / sobolevGaugeGroup hs`, since every continuous field
of `A_m^k` is `C²`. -/
noncomputable def vortexModuliEquivSobolevVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :=
  (Equiv.ofBijective
    (Quotient.lift
      (fun x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk ↦
        (⟨Quotient.mk _ ⟨x.val, x.val.property,
            (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).1.continuous⟩,
          mk_mem_vortexModuli
            (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).2⟩ :
          vortexModuli f m hs))
      fun x y h ↦ Subtype.ext <| Quotient.sound <| orbitRel_iff.2 <| by
        obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
        have hinv := congrArg
          (fun z : framedFieldSpace f m k ↦ (z : ℂ → EuclideanSpace ℝ (Fin 4)))
          (inv_smul_smul u y.val)
        rw [coe_sobolevGaugeGroup_smul] at hinv
        exact ⟨u⁻¹, u⁻¹.property, hinv⟩)
    ⟨Quotient.ind₂ fun x y h ↦ Quotient.sound <| MulAction.orbitRel_apply.2 <|
        MulAction.mem_orbit_iff.2 <| by
          obtain ⟨u, hu, hxy⟩ := orbitRel_iff.1 (Quotient.exact (congrArg Subtype.val h).symm)
          exact ⟨⟨u, hu⟩, Subtype.ext (Subtype.ext hxy)⟩,
      fun ⟨q, hq⟩ ↦ by
        obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
        have hx2 : ContDiff ℝ 2 x :=
          x.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k))
        exact ⟨Quotient.mk'' ⟨x.toFramedFieldSpace, mem_sobolevVortexSubMulAction.2
          (mem_sobolevVortices.2 ⟨hx2, hx⟩)⟩, rfl⟩⟩).symm

/-- The inverse of `vortexModuliEquivSobolevVortexModuli` sends the orbit of a `C²` vortex of
`A_m^k` to its orbit in `vortexModuli`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_symm_mk (hk : 3 < k)
    (x : sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) :
    (vortexModuliEquivSobolevVortexModuli hk).symm (Quotient.mk'' x) =
      ⟨Quotient.mk _ ⟨x.val, x.val.property,
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).1.continuous⟩,
        mk_mem_vortexModuli
          (mem_sobolevVortices.1 (mem_sobolevVortexSubMulAction.1 x.property)).2⟩ := by
  rw [vortexModuliEquivSobolevVortexModuli]
  rfl

/-- `vortexModuliEquivSobolevVortexModuli` sends the orbit of a continuous vortex `x` of `A_m^k` to
its `sobolevGaugeGroup`-orbit in `sobolevVortexSubMulAction`. -/
@[simp]
theorem vortexModuliEquivSobolevVortexModuli_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliEquivSobolevVortexModuli (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      Quotient.mk'' ⟨x.toFramedFieldSpace, mem_sobolevVortexSubMulAction.2
        (mem_sobolevVortices.2
          ⟨x.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k)), hx⟩)⟩ := by
  refine ((vortexModuliEquivSobolevVortexModuli hk).eq_symm_apply).1 ?_
  rw [vortexModuliEquivSobolevVortexModuli_symm_mk]
  exact Subtype.ext (congrArg (Quotient.mk _) (ext rfl))

/-- **The divisor bijection on `vortexModuli`.** For `k ≥ 4`, the zero divisor identifies the
Sobolev vortex moduli space `vortexModuli f m hs ⊆ A_m^k / G_(k+1)` bijectively with `Sym ℂ m`. -/
noncomputable def vortexModuliEquiv (hk : 3 < k) : vortexModuli f m hs ≃ Sym ℂ m :=
  (vortexModuliEquivSobolevVortexModuli hk).trans (sobolevVortexModuliEquiv hk)

/-- `vortexModuliEquiv` sends the orbit of a vortex to its zero divisor. -/
@[simp]
theorem vortexModuliEquiv_mk (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) :
    vortexModuliEquiv (hs := hs) hk ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ =
      sobolevVortexDivisor ⟨x.toFramedFieldSpace, mem_sobolevVortices.2
        ⟨x.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k)), hx⟩⟩ := by
  rw [vortexModuliEquiv, Equiv.trans_apply, vortexModuliEquivSobolevVortexModuli_mk hk hx,
    sobolevVortexModuliEquiv_apply, sobolevVortexModuliDivisor_mk]

/-- **Bijection between `vortexModuli` and the smooth framed vortex moduli.** For `k ≥ 4`, the
Sobolev vortex moduli space `vortexModuli f m hs` is canonically in bijection with the smooth
framed vortex moduli space via their zero divisors. -/
noncomputable def vortexModuliEquivFramedVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction 1 m) :=
  (vortexModuliEquivSobolevVortexModuli hk).trans (sobolevVortexModuliEquivFramedVortexModuli hk)

/-- On the orbit of a smooth vortex in `A_m^k`, `vortexModuliEquivFramedVortexModuli` agrees with
taking its `framedGaugeGroup`-orbit. -/
theorem vortexModuliEquivFramedVortexModuli_mk_of_eq (hk : 3 < k) {x : SobolevFieldSpace f m k}
    (hx : ∀ z, equation x z = 0) (x' : framedVortexSubMulAction 1 m)
    (hxx' : (x : ℂ → EuclideanSpace ℝ (Fin 4)) = x') :
    vortexModuliEquivFramedVortexModuli (hs := hs) hk
        ⟨Quotient.mk _ x, mk_mem_vortexModuli hx⟩ = Quotient.mk'' x' := by
  rw [vortexModuliEquivFramedVortexModuli, Equiv.trans_apply,
    vortexModuliEquivSobolevVortexModuli_mk hk hx]
  exact sobolevVortexModuliEquivFramedVortexModuli_mk_of_eq _ x' hxx'

/-- For `k ≥ 3`, the restriction of the quotient map `A_m^k → A_m^k / G_(k+1)` to the vortices is
a quotient map onto `vortexModuli`. -/
theorem isQuotientMap_vortexModuli_quotientMk (hk : 3 ≤ k) :
    IsQuotientMap fun x : {x : SobolevFieldSpace f m k | ∀ z, equation x z = 0} ↦
      (⟨Quotient.mk _ x.val, mk_mem_vortexModuli x.property⟩ : vortexModuli f m hs) := by
  refine isQuotientMap_of_isOpenQuotientMap_of_isInducing Subtype.val Subtype.val
    (fun x ↦ ⟨Quotient.mk _ x.val, mk_mem_vortexModuli x.property⟩)
    (Quotient.mk _) rfl .subtypeVal
    (fun ⟨q, hq⟩ ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_vortexModuli_iff.1 hq
      exact ⟨⟨x, hx⟩, rfl⟩)
    MulAction.isOpenQuotientMap_quotientMk .subtypeVal ?_
  rintro x ⟨_, ⟨y, hy, rfl⟩, hyx⟩
  exact ⟨⟨x, (mk_mem_vortexModuli_iff hk).1
    (hyx ▸ mk_mem_vortexModuli (hs := hs) y.property)⟩, rfl⟩

/-- **The divisor on `vortexModuli` is continuous.** For `k ≥ 4`, `vortexModuliEquiv` is
continuous with respect to the quotient topology on `vortexModuli` and the topology of `Sym ℂ m`. -/
theorem continuous_vortexModuliEquiv (hk : 3 < k) :
    Continuous (vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) := by
  rw [(isQuotientMap_vortexModuli_quotientMk (f := f) (m := m) (hs := hs)
    (by omega : 3 ≤ k)).continuous_iff, continuous_iff_continuousAt]
  intro x₀
  have hs1 : (1 : ℝ) < k := by exact_mod_cast (Fact.out : 1 < k)
  refine tendsto_of_tendsto hs1 continuous_subtypeVal.continuousAt ?_ (.of_forall fun x ↦ ?_)
  · dsimp only [Function.comp_apply]
    rw [vortexModuliEquiv_mk hk x₀.property]
    exact isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨x₀.val.toFramedFieldSpace, mem_sobolevVortices.2
        ⟨x₀.val.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k)), x₀.property⟩⟩
  · dsimp only [Function.comp_apply]
    rw [vortexModuliEquiv_mk hk x.property]
    exact isZeroMultiplicity_sectionValue_sobolevVortexDivisor
      ⟨x.val.toFramedFieldSpace, mem_sobolevVortices.2
        ⟨x.val.contDiff (n := 2) (by exact_mod_cast (by omega : 2 + 1 < k)), x.property⟩⟩

/-- **The Sobolev moduli space of framed vortices is homeomorphic to `Sym ℂ m`** (Taubes). For
`k ≥ 4`, the divisor identifies `vortexModuli f m hs` homeomorphically with `Sym ℂ m`, by
continuity of the divisor, the `ℝ^(2m)`-charts (`vortexModuliChartedSpace`), the elementary
symmetric chart `Sym.coeffHomeomorph ℂ m`, and Brouwer's invariance of domain. -/
noncomputable def vortexModuliHomeomorph (hk : 3 < k) : vortexModuli f m hs ≃ₜ Sym ℂ m where
  toEquiv := vortexModuliEquiv hk
  continuous_toFun := continuous_vortexModuliEquiv hk
  continuous_invFun := continuous_def.2 fun U hU ↦ by
    let _ := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    let ψ := Sym.coeffHomeomorph ℂ m
    have hEF : Module.finrank ℝ (Fin (2 * m) → ℝ) = Module.finrank ℝ (Fin m → ℂ) := by
      rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex]
      simp [mul_comm]
    have hψ : IsOpenEmbedding (ψ ∘ vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) :=
      (ψ.continuous.comp (continuous_vortexModuliEquiv hk)).isOpenEmbedding_of_injective
        (ψ.injective.comp (vortexModuliEquiv hk).injective) hEF
    have he : IsOpenEmbedding (vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) := by
      have heq :
          (vortexModuliEquiv (f := f) (m := m) (hs := hs) hk :
            vortexModuli f m hs → Sym ℂ m) =
            ψ.symm ∘ (ψ ∘ vortexModuliEquiv (f := f) (m := m) (hs := hs) hk) :=
        funext fun q ↦ (ψ.symm_apply_apply _).symm
      rw [heq]
      exact ψ.symm.isOpenEmbedding.comp hψ
    change IsOpen ((vortexModuliEquiv hk).symm ⁻¹' U)
    rw [← Equiv.image_eq_preimage_symm]
    exact he.isOpenMap U hU

/-- Underlying equivalence of `vortexModuliHomeomorph`. -/
@[simp]
theorem coe_vortexModuliHomeomorph (hk : 3 < k) :
    ⇑(vortexModuliHomeomorph (f := f) (m := m) (hs := hs) hk) = vortexModuliEquiv hk := by
  rw [vortexModuliHomeomorph]
  rfl

/-- **Homeomorphism between `vortexModuli` and the smooth framed vortex moduli.** For `k ≥ 4`, the
Sobolev vortex moduli space `vortexModuli f m hs` is homeomorphic to the orbit space of the smooth
framed vortices `framedVortices 1 m` with the topology of locally uniform convergence, identifying
orbits with the same zero divisor. -/
noncomputable def vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k) :
    vortexModuli f m hs ≃ₜ
      MulAction.orbitRel.Quotient framedGaugeGroup (framedVortices 1 m) :=
  (vortexModuliHomeomorph hk).trans (framedVortexModuliHomeomorph one_pos m).symm

/-- Passing from `vortexModuli` to `framedVortices 1 m / framedGaugeGroup` and then taking the
divisor recovers `vortexModuliEquiv`. -/
@[simp]
theorem framedVortexModuliHomeomorph_vortexModuliHomeomorphFramedVortexModuli (hk : 3 < k)
    (q : vortexModuli f m hs) :
    framedVortexModuliHomeomorph one_pos m
        (vortexModuliHomeomorphFramedVortexModuli hk q) =
      vortexModuliEquiv hk q := by
  simp [vortexModuliHomeomorphFramedVortexModuli]

end Global

end SobolevFieldSpace

end TauCeti.Vortex
