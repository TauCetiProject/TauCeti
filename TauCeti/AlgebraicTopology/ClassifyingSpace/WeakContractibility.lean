/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CountableJoin
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.WeakContractibility
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Weak contractibility of the countable join

An indexed join is weakly contractible when nonempty family members occur at infinitely many
indices.  Compactness reduces each map from a cube to a finite vertex restriction, and a fresh
index cones off that restriction.  We deduce path-connectedness, simple connectedness, and the
vanishing of every positive-dimensional homotopy group.  The final results specialize these
facts to Milnor's countable join `universalGSpace`.

## Main results

* `TauCeti.pathConnectedSpace_realization_indexedJoin`: path-connectedness of the indexed join.
* `TauCeti.simplyConnectedSpace_realization_indexedJoin`: simple connectedness.
* `TauCeti.subsingleton_homotopyGroup_realization_indexedJoin`: vanishing homotopy groups.
* `TauCeti.instSimplyConnectedSpaceUniversalGSpace`: simple connectedness of the countable join.
* `TauCeti.subsingleton_homotopyGroup_universalGSpace`: all its positive-dimensional homotopy
  groups vanish.
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval Topology.Homotopy

universe u v

namespace TauCeti

variable {ι : Type u} {A : ι → Type v}

/-- An indexed join is path-connected if nonempty family members occur at infinitely many
indices. -/
theorem pathConnectedSpace_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) :
    PathConnectedSpace (indexedJoin A).Realization := by
  constructor
  · obtain ⟨i, hi⟩ := hA.nonempty
    obtain ⟨a⟩ := hi
    exact ⟨(indexedJoin A).vertex ⟨i, a⟩⟩
  · intro x y
    let f : C(Bool, (indexedJoin A).Realization) :=
      ⟨fun b => if b then y else x, continuous_of_discreteTopology⟩
    obtain ⟨c, ⟨H⟩⟩ := ContinuousMap.nullhomotopic_to_indexedJoin f
      (isCompact_range f.continuous) hA
    refine ⟨(H.evalAt false).trans (H.evalAt true).symm⟩

/-- An indexed join is simply connected if nonempty family members occur at infinitely many
indices. -/
theorem simplyConnectedSpace_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) :
    SimplyConnectedSpace (indexedJoin A).Realization := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace_realization_indexedJoin hA, ?_⟩
  intro x γ
  obtain ⟨c, F, hF⟩ :=
    ContinuousMap.exists_homotopy_to_const_to_indexedJoin γ.toContinuousMap
      (isCompact_range γ.continuous) hA
  let α₀ : Path x c := (F.evalAt 0).cast γ.source.symm rfl
  let α₁ : Path x c := (F.evalAt 1).cast γ.target.symm rfl
  have hα : α₀ = α₁ := by
    apply DFunLike.coe_injective
    funext t
    exact hF t 0 1 (γ.source.trans γ.target.symm)
  have hkey := (Path.Homotopic.map_trans_evalAt F Path.id).pathCast γ.source.symm rfl
  have hleft :
      (((Path.id.map γ.continuous).trans (F.evalAt 1)).cast γ.source.symm rfl) =
        γ.trans α₁ := by
    ext t
    rfl
  have hright :
      (((F.evalAt 0).trans
        (Path.id.map (ContinuousMap.const I c).continuous)).cast γ.source.symm rfl) =
          α₀.trans (Path.refl c) := by
    ext t
    rfl
  rw [hleft, hright, ← hα] at hkey
  exact Path.Homotopic.trans_right_cancel
    ((hkey.trans (Path.Homotopic.trans_refl α₀)).trans
      (Path.Homotopic.refl_trans α₀).symm)

/-- Every positive-dimensional homotopy group of an indexed join is trivial if nonempty family
members occur at infinitely many indices. -/
theorem subsingleton_homotopyGroup_realization_indexedJoin
    (hA : {i | Nonempty (A i)}.Infinite) (N : Type*) [Finite N] [Nonempty N]
    (x : (indexedJoin A).Realization) :
    Subsingleton (HomotopyGroup N (indexedJoin A).Realization x) := by
  classical
  let _ : Fintype N := Fintype.ofFinite N
  let _ : SimplyConnectedSpace (indexedJoin A).Realization :=
    simplyConnectedSpace_realization_indexedJoin hA
  have h_one : ∀ a : HomotopyGroup N (indexedJoin A).Realization x, a = 1 := by
    intro a
    refine Quotient.inductionOn a ?_
    intro p
    obtain ⟨c, H, hH⟩ :=
      ContinuousMap.exists_homotopy_to_const_to_indexedJoin p.1
        (isCompact_range p.1.continuous) hA
    let γ : Path x c :=
      (H.evalAt 0).cast (_root_.GenLoop.boundary p 0 zero_mem_cubeBoundary).symm rfl
    let Hforward : GenLoop.HomotopyAlong γ p
        (_root_.GenLoop.const : Ω^ N (indexedJoin A).Realization c) := {
      toHomotopy := H
      map_boundary := by
        intro t z hz
        change H (t, z) = H (t, 0)
        exact hH t z 0
          ((_root_.GenLoop.boundary p z hz).trans
            (_root_.GenLoop.boundary p 0 zero_mem_cubeBoundary).symm) }
    let Hback : GenLoop.HomotopyAlong γ.symm
        (_root_.GenLoop.const : Ω^ N (indexedJoin A).Realization c)
        (_root_.GenLoop.const : Ω^ N (indexedJoin A).Realization x) := {
      toFun := fun tz => γ.symm tz.1
      continuous_toFun := γ.symm.continuous.comp continuous_fst
      map_zero_left := fun _ => γ.symm.source
      map_one_left := fun _ => γ.symm.target
      map_boundary := fun _ _ _ => rfl }
    let ap : HomotopyGroup N (indexedJoin A).Realization x := ⟦p⟧
    let ac : HomotopyGroup N (indexedJoin A).Realization x :=
      ⟦(_root_.GenLoop.const : Ω^ N (indexedJoin A).Realization x)⟧
    have hmem :
        ac ∈ MulAction.orbit (FundamentalGroup (indexedJoin A).Realization x) ap := by
      exact (homotopyGroup_mem_orbit_iff_exists_homotopyAlong
        (a := ap) (b := ac) rfl rfl).2
        ⟨γ.trans γ.symm, ⟨Hforward.trans Hback⟩⟩
    have horbit :
        (1 : HomotopyGroup N (indexedJoin A).Realization x) ∈
          MulAction.orbit (FundamentalGroup (indexedJoin A).Realization x) ap := by
      simpa only [ac, HomotopyGroup.mk_const_eq_one] using hmem
    obtain ⟨g, hg⟩ := horbit
    simpa only [ap] using
      (fundamentalGroup_smul_eq_self g ap).symm.trans hg
  exact ⟨fun a b => (h_one a).trans (h_one b).symm⟩

private theorem infinite_nonempty_const_nat (G : Type u) [Nonempty G] :
    {_i : ℕ | Nonempty G}.Infinite :=
  Set.infinite_univ.mono fun _ _ => inferInstance

/-- Milnor's countable join of a nonempty type is simply connected. -/
instance instSimplyConnectedSpaceUniversalGSpace (G : Type u) [Nonempty G] :
    SimplyConnectedSpace (universalGSpace G) :=
  simplyConnectedSpace_realization_indexedJoin (infinite_nonempty_const_nat G)

/-- Every positive-dimensional homotopy group of Milnor's countable join is trivial. -/
theorem subsingleton_homotopyGroup_universalGSpace (G : Type u) [Nonempty G]
    (n : ℕ) (x : universalGSpace G) :
    Subsingleton (π_ (n + 1) (universalGSpace G) x) :=
  subsingleton_homotopyGroup_realization_indexedJoin
    (infinite_nonempty_const_nat G) (Fin (n + 1)) x

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Every map from a compact space to Milnor's countable join is nullhomotopic. -/
theorem nullhomotopic_to_universalGSpace {G : Type u} [Nonempty G]
    (f : C(X, universalGSpace G)) : f.Nullhomotopic :=
  nullhomotopic_to_indexedJoin f (isCompact_range f.continuous)
    (infinite_nonempty_const_nat G)

end ContinuousMap
