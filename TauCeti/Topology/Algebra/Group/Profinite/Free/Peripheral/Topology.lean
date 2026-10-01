/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Profinite
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Group

/-!
# The peripheral automorphism group as a profinite group

Let `F` be a topologically finitely generated pro-`p` group, so that the group `ContinuousAut F`
of its continuous automorphisms is profinite for the congruence topology. For a finite family
`x : Fin r → F`, the *peripheral graph* is the set of pairs `(φ, u)` of a continuous automorphism
and a `p`-adic unit such that `φ` is peripheral of exponent `u` for `x`. Each of the `r + 1`
defining conditions `IsConj (y ^ u) (φ y)`, for `y` in the peripheral tuple of `x`, pulls back
the closed conjugacy relation of `F` along the jointly continuous map `(φ, u) ↦ (y ^ u, φ y)`,
so the graph is closed in `ContinuousAut F × ℤ_[p]ˣ`.

The group `peripheralAut hF x` of peripheral automorphisms is the projection of the graph to the
first factor. Since `ℤ_[p]ˣ` is compact, that projection is a closed map, so `peripheralAut hF x`
is a closed subgroup of the profinite group `ContinuousAut F`, hence a profinite group itself.
This is the topological input for taking profinite and `p`-adic powers of peripheral
automorphisms.

For the basis of a free pro-`p` group of positive rank the exponent character
`exponent hF e hr : peripheralAut hF (basis e) →* ℤ_[p]ˣ` has the peripheral graph as its graph,
so it is continuous by the closed graph theorem for maps into a compact space.

## Main results

* `TauCeti.Peripheral.isClosed_peripheralGraph`: the pairs `(φ, u)` with `IsPeripheralAut hF x u φ`
  form a closed subset of `ContinuousAut F × ℤ_[p]ˣ`.
* `TauCeti.Peripheral.isClosed_peripheralAut`: `peripheralAut hF x` is closed in `ContinuousAut F`.
* `TauCeti.Peripheral.compactSpace_peripheralAut`,
  `TauCeti.Peripheral.totallyDisconnectedSpace_peripheralAut`: `peripheralAut hF x` is a
  profinite group.
* `TauCeti.Peripheral.graph_exponent`: the graph of the exponent character is the peripheral
  graph of the basis.
* `TauCeti.Peripheral.continuous_exponent`: the exponent character is continuous.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms of free pro-`p` groups and their common exponent.
-/

public section

namespace TauCeti.Peripheral

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

section Closed

variable (hF : IsProP p F) (x : Fin r → F)

/-- **The peripheral graph is closed.** For a topologically finitely generated pro-`p` group `F`
and a family `x`, the pairs `(φ, u)` of a continuous automorphism and a `p`-adic unit with
`IsPeripheralAut hF x u φ` form a closed subset of `ContinuousAut F × ℤ_[p]ˣ`. -/
theorem isClosed_peripheralGraph (hfg : IsTopologicallyFinitelyGenerated F) :
    IsClosed {q : ContinuousAut F × ℤ_[p]ˣ | IsPeripheralAut hF x q.2 q.1} := by
  -- for a fixed element `y`, the `u`-th power of `y` and the value `φ y` both depend continuously
  -- on `(φ, u)`, so the pairs with `IsConj (y ^ u) (φ y)` form a closed set
  have hclosed (y : F) :
      IsClosed {q : ContinuousAut F × ℤ_[p]ˣ | IsConj (hF.padicPow y (q.2 : ℤ_[p])) (q.1 y)} := by
    have hpow : Continuous fun q : ContinuousAut F × ℤ_[p]ˣ ↦ hF.padicPow y (q.2 : ℤ_[p]) :=
      hF.continuous_padicPow.comp
        ((Units.continuous_val.comp continuous_snd).prodMk continuous_const)
    have heval : Continuous fun q : ContinuousAut F × ℤ_[p]ˣ ↦ q.1 y :=
      (ContinuousAut.continuous_eval hfg).comp (continuous_fst.prodMk continuous_const)
    exact (isClosed_isConj_pair F).preimage (hpow.prodMk heval)
  simp only [isPeripheralAut_iff, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i ↦ hclosed (x i)).inter (hclosed (cusp x))

/-- **The peripheral automorphisms form a closed subgroup** of `ContinuousAut F` for the
congruence topology, when `F` is topologically finitely generated. -/
theorem isClosed_peripheralAut (hfg : IsTopologicallyFinitelyGenerated F) :
    IsClosed (peripheralAut hF x : Set (ContinuousAut F)) := by
  -- the subgroup is the projection of the closed peripheral graph along the compact factor
  -- `ℤ_[p]ˣ`, and projecting along a compact factor is a closed map
  have himage : (peripheralAut hF x : Set (ContinuousAut F)) =
      Prod.fst '' {q : ContinuousAut F × ℤ_[p]ˣ | IsPeripheralAut hF x q.2 q.1} := by
    ext φ
    simp
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_peripheralGraph hF x hfg)

/-- The peripheral automorphism group of a topologically finitely generated pro-`p` group is
compact. -/
theorem compactSpace_peripheralAut (hfg : IsTopologicallyFinitelyGenerated F) :
    CompactSpace (peripheralAut hF x) :=
  have := ContinuousAut.compactSpace hfg
  isCompact_iff_compactSpace.mp (isClosed_peripheralAut hF x hfg).isCompact

/-- The peripheral automorphism group of a topologically finitely generated pro-`p` group is
totally disconnected. -/
theorem totallyDisconnectedSpace_peripheralAut (hfg : IsTopologicallyFinitelyGenerated F) :
    TotallyDisconnectedSpace (peripheralAut hF x) :=
  have := ContinuousAut.totallyDisconnectedSpace hfg
  inferInstance

end Closed

section Exponent

variable (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (hr : 0 < r)

/-- The graph of the exponent character is the peripheral graph of the basis, pulled back to the
peripheral automorphism group. -/
theorem graph_exponent :
    Function.graph (exponent hF e hr) =
      (fun q : peripheralAut hF (basis e) × ℤ_[p]ˣ ↦ ((q.1 : ContinuousAut F), q.2)) ⁻¹'
        {q : ContinuousAut F × ℤ_[p]ˣ | IsPeripheralAut hF (basis e) q.2 q.1} := by
  ext ⟨φ, u⟩
  exact exponent_eq_iff hF e hr φ u

/-- **The exponent character is continuous.** Its graph is closed, being the peripheral graph of
the basis, and its target `ℤ_[p]ˣ` is compact. -/
theorem continuous_exponent : Continuous (exponent hF e hr) := by
  have hfg : IsTopologicallyFinitelyGenerated F :=
    (isTopologicallyFinitelyGenerated_congr e).mpr (isTopologicallyFinitelyGenerated_freeProP p _)
  refine continuous_of_isClosed_graph ?_
  rw [graph_exponent]
  exact (isClosed_peripheralGraph hF (basis e) hfg).preimage
    (continuous_subtype_val.prodMap continuous_id)

end Exponent

end TauCeti.Peripheral
