/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Topology.Algebra.ContinuousZModDual
public import TauCeti.Topology.Algebra.Group.Profinite.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The continuous `ZMod p`-dual is bounded by the topological generator rank

A topological generating set converging to `1` bounds the continuous `𝔽_p`-dual
`TauCeti.continuousZModDual p G` of a topological group from above: a continuous character has
open kernel, hence is trivial on all but finitely many members of such a set, and it is determined
by its values there, so restriction is a linear injection of the dual into the finitely supported
`𝔽_p`-valued functions on the set. Minimising over the generating sets of a profinite group turns
this into a bound by the topological generator rank, and a finite generating set turns it into
finite-dimensionality.

Nothing here is pro-`p`, and nothing here needs the group to be commutative. The reverse
inequality does need the group to be pro-`p`, but not to be commutative: its dual basis argument
runs on the elementary abelian Frattini quotient, and the equality it yields,
`TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`, holds for an arbitrary
profinite pro-`p` group.

## Main results

* `TauCeti.rank_continuousZModDual_le_of_convergesToOne`: a topological generating set converging
  to `1` bounds the dimension of the continuous `𝔽_p`-dual by its cardinality.
* `TauCeti.rank_continuousZModDual_le_topologicalGeneratorRank`: the dimension of the continuous
  `𝔽_p`-dual of a profinite group is at most its topological generator rank.
* `TauCeti.finite_continuousZModDual`: the continuous `𝔽_p`-dual of a topologically finitely
  generated topological group is finite-dimensional.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

open scoped Cardinal

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- **A generating set converging to `1` bounds the dimension of the continuous `𝔽_p`-dual.**
Restriction to the set is injective because a character with open kernel is determined by its
values on a topological generating set, and it lands in the finitely supported functions because
the kernel of a continuous character is an open neighbourhood of `1`. -/
theorem rank_continuousZModDual_le_of_convergesToOne {s : Set G} (hs : ConvergesToOne s)
    (hgen : (Subgroup.closure s).topologicalClosure = ⊤) :
    Module.rank (ZMod p) (continuousZModDual p G) ≤ #(s : Set G) := by
  classical
  have hopen (x : continuousZModDual p G) :
      IsOpen (((Additive.toMul x).ker : Subgroup G) : Set G) :=
    (MonoidHom.continuous_iff_isOpen_ker _).mp (Additive.toMul x).continuous
  have hsupp (x : continuousZModDual p G) :
      (Function.support fun y : s ↦ Multiplicative.toAdd (Additive.toMul x (y : G))).Finite := by
    refine ((convergesToOne_iff.mp hs _
      ((hopen x).mem_nhds (Subgroup.one_mem _))).preimage
        Subtype.val_injective.injOn).subset fun y hy ↦ ?_
    exact ⟨y.2, fun hmem ↦ hy (by simpa [MonoidHom.mem_ker] using hmem)⟩
  let R : continuousZModDual p G →ₗ[ZMod p] (s →₀ ZMod p) :=
    AddMonoidHom.toZModLinearMap p
      { toFun := fun x ↦ Finsupp.ofSupportFinite _ (hsupp x)
        map_zero' := Finsupp.ext fun z ↦ by
          simp [Finsupp.ofSupportFinite_coe]
        map_add' := fun x y ↦ Finsupp.ext fun z ↦ by
          simp [Finsupp.ofSupportFinite_coe, toMul_add] }
  have hRapply (x : continuousZModDual p G) (y : s) :
      R x y = Multiplicative.toAdd (Additive.toMul x (y : G)) :=
    congrFun Finsupp.ofSupportFinite_coe y
  have hinj : Function.Injective R := fun x y hxy ↦ by
    apply Additive.toMul.injective
    have heq : ((Additive.toMul x : G →ₜ* Multiplicative (ZMod p)) : G →* Multiplicative (ZMod p))
        = ((Additive.toMul y : G →ₜ* Multiplicative (ZMod p)) : G →* Multiplicative (ZMod p)) :=
      MonoidHom.eq_of_eqOn_of_isOpen_ker hgen (hopen x) (hopen y) fun w hw ↦ by
        have h₁ := hRapply x ⟨w, hw⟩
        have h₂ := hRapply y ⟨w, hw⟩
        rw [hxy] at h₁
        exact Multiplicative.toAdd.injective (h₁.symm.trans h₂)
    ext z
    exact DFunLike.congr_fun heq z
  calc
    Module.rank (ZMod p) (continuousZModDual p G) ≤ Module.rank (ZMod p) (s →₀ ZMod p) :=
      R.rank_le_of_injective hinj
    _ = #(s : Set G) := by rw [rank_finsupp_self]; simp

/-- **The dimension of the continuous `𝔽_p`-dual of a profinite group is at most its topological
generator rank.** No pro-`p` hypothesis is needed for this half. -/
theorem rank_continuousZModDual_le_topologicalGeneratorRank [CompactSpace G]
    [TotallyDisconnectedSpace G] :
    Module.rank (ZMod p) (continuousZModDual p G) ≤ topologicalGeneratorRank G := by
  obtain ⟨s, hs, hgen, hcard⟩ := exists_convergesToOne_mk_eq_topologicalGeneratorRank G
  exact hcard ▸ rank_continuousZModDual_le_of_convergesToOne hs hgen

/-- **The continuous `𝔽_p`-dual of a topologically finitely generated topological group is
finite-dimensional**, its dimension being bounded by the cardinality of a finite topological
generating set. Neither a pro-`p` hypothesis nor compactness is needed: a finite set converges to
`1` in any topological group. -/
theorem finite_continuousZModDual (hfg : IsTopologicallyFinitelyGenerated G) :
    Module.Finite (ZMod p) (continuousZModDual p G) := by
  obtain ⟨s, hs⟩ := isTopologicallyFinitelyGenerated_iff.mp hfg
  exact Module.rank_lt_aleph0_iff.mp <|
    (rank_continuousZModDual_le_of_convergesToOne s.finite_toSet.convergesToOne hs).trans_lt
      s.finite_toSet.lt_aleph0

end TauCeti
