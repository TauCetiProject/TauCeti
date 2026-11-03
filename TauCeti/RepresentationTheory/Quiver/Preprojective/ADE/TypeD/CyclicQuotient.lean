/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic

/-!
# The cyclic quotient of the type-`D` preprojective algebra

The cyclic quotient `Π / [Π, Π]` of an algebra is its zeroth Hochschild homology. For the
preprojective algebra `Π(Q)` of a quiver `Q` whose underlying graph is a tree, Liu and Wang
identify its degree-`(q + 2)` piece with the second Hochschild cohomology `HH^{2,q}` of the
two-dimensional Ginzburg algebra `Π₂(Q)`, which controls the `A∞` deformations of the zigzag
algebra of the tree. This file shows that for `Dₙ` the cyclic quotient is concentrated in path
degree zero, where it is free on the vertices, over every commutative ring in which `2` is a unit.

## The argument

In the Bourbaki labelling write `c = n - 3` for the branch node, `x` and `y` for the backtracks
from it into the two leaves, and `q` for its backtrack into the long arm, so that `x * x = 0`,
`y * y = 0` and `x + y + q = 0`. Every path is, by the normal forms of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic`, a multiple of a valley word
on the long arm, or a path through the branch node with a word `w` in `x` and `y` in its middle.
A path between distinct vertices is a commutator with its target idempotent. A closed path is
treated by rotating one of its factors from the front to the back:

* a closed valley word on the long arm, which does not reach the branch node, rotates, by the
  ladder relations of the arm, into a power of `q`
  (`TauCeti.ladderValley_mem_commutatorSubmodule_of_u_eq_zero`);
* the powers of `q` are sums of commutators, since `q ^ j` rotates into `±` the `j`-th power of
  the backtrack at the next vertex of the arm, and the backtrack at its far end vanishes
  (`TauCeti.pow_d_mul_u_mem_commutatorSubmodule`);
* a closed path through the branch node rotates into `w` times a power of `x + y = -q` or times
  `x` or `y`, a nonempty word in `x` and `y`.

The words in `x` and `y` are spanned by the alternating words `x (x + y) ^ t` and
`y (x + y) ^ t`. The backtrack `x` rotates into the backtrack at its leaf, which is zero. For odd
`t` the word `x (x + y) ^ t` and its rotation `(x + y) ^ t x` sum to the power `(x + y) ^ (t + 1)`,
so twice the word is a sum of commutators (`TauCeti.mul_add_pow_mem_commutatorSubmodule`). This is
the only place where `2` must be a unit. Characteristic two is the bad characteristic of type `D`
in Liu and Wang's intrinsic formality theorem; the nonvanishing of the cyclic quotient in positive
degrees in characteristic two is not proved here.

Consequently the commutator submodule of `Π⁺(Dₙ)` is exactly the kernel of the augmentation onto
the vertex coefficients, and the augmentation induces `Π⁺(Dₙ) / [Π⁺(Dₙ), Π⁺(Dₙ)] ≃ k^{Dₙ}`.
Through the bipartite sign rescaling, the same vanishing holds for the additive preprojective
algebra of every orientation of `Dₙ`.
These consequences, and the case of a path between distinct vertices, do not depend on the graph;
they are in `TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient`.

## Main results

* `TauCeti.signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule`: if `2` is a unit, every path
  of positive length in `Π⁺(Dₙ)` lies in `[Π⁺(Dₙ), Π⁺(Dₙ)]`.
* `TauCeti.signlessPreprojectiveGrade_D_le_commutatorSubmodule`: if `2` is a unit, every piece of
  positive path degree of `Π⁺(Dₙ)` lies in `[Π⁺(Dₙ), Π⁺(Dₙ)]`.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_D_eq_ker`: if `2` is a unit, the
  commutator submodule is the kernel of the augmentation.
* `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_D`: over a nontrivial commutative
  ring in which `2` is a unit, the cyclic quotient of `Π⁺(Dₙ)` has dimension `n`.
* `TauCeti.preprojectiveMk_D_ofPath_mem_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_D_le_commutatorSubmodule`: the same vanishing in positive degrees for
  the preprojective algebra `Π(Q)` of every orientation `Q` of `Dₙ`.

## References

* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006, for the cyclic quotient
  of the preprojective algebra of a Dynkin quiver.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of the cyclic quotient in the deformation theory
  of zigzag algebras and for the bad characteristics.
* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the cyclic quotient as zeroth Hochschild
  homology.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

/-! ### Graphs with a long arm and two leaves at its end -/

section ForkGraph

variable (k : Type*) [CommRing k] {n : ℕ} {G : SimpleGraph (Fin n)} {c : ℕ}
  (hn : n = c + 3)
  (hG : ∀ i j : Fin n, G.Adj i j ↔ (i : ℕ) + 1 = j ∧ (j : ℕ) ≤ c ∨ (j : ℕ) + 1 = i ∧ (i : ℕ) ≤ c ∨
    (i : ℕ) = c ∧ c < j ∨ (j : ℕ) = c ∧ c < i)
include hn hG

local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver G)

omit hn in
/-- The backtrack from the branch node into a leaf rotates into the backtrack at the leaf, which
vanishes. -/
private theorem forkTurn_mem_commutatorSubmodule {l : ℕ} (hl : c < l) (hln : l < n) :
    forkTurn k G c l ∈ commutatorSubmodule k Π := by
  rw [forkTurn, mul_mem_commutatorSubmodule_comm, signlessArrow_mul_signlessArrow_leaf k hG hl hln]
  exact zero_mem _

/-- The positive powers of the sum of the two leaf backtracks, which is minus the backtrack into
the long arm, are sums of commutators. -/
private theorem forkTurn_add_pow_succ_mem_commutatorSubmodule (t : ℕ) :
    (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)) ^ (t + 1) ∈ commutatorSubmodule k Π := by
  rw [forkTurn_add_eq_neg_forkDown_mul_forkUp k hn hG, neg_pow]
  exact neg_one_pow_mul_mem_commutatorSubmodule (pow_d_mul_u_mem_commutatorSubmodule k
    (forkDown_mul_forkUp_add k hn hG) (forkUp_self_eq_zero k hG) t.succ_pos) (t + 1)

/-- If `2` is a unit, every element of a positive power of the span of the two leaf backtracks
is a sum of commutators. -/
private theorem mem_commutatorSubmodule_of_mem_forkSpan_pow (h2 : IsUnit (2 : k)) {t : ℕ}
    (ht : 0 < t) {w : Π} (hw : w ∈ forkSpan k G c ^ t) : w ∈ commutatorSubmodule k Π := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hx := forkTurn_mul_self k hG (l := c + 1) (by omega) (by omega)
  have hy := forkTurn_mul_self k hG (l := c + 2) (by omega) (by omega)
  have hx₀ := forkTurn_mem_commutatorSubmodule k hG (l := c + 1) (by omega) (by omega)
  have hy₀ := forkTurn_mem_commutatorSubmodule k hG (l := c + 2) (by omega) (by omega)
  have hs := forkTurn_add_pow_succ_mem_commutatorSubmodule k hn hG
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp (span_pair_pow_succ_le (R := ℤ) hx hy t hw)
  refine add_mem (zsmul_mem ?_ α) (zsmul_mem ?_ β)
  · exact mul_add_pow_mem_commutatorSubmodule h2 hx hy hx₀ hs t
  · rw [add_comm (forkTurn k G c (c + 1))] at hs ⊢
    exact mul_add_pow_mem_commutatorSubmodule h2 hy hx hy₀ hs t

omit hn hG in
/-- A nonempty word in the leaf backtracks ends at the branch node. -/
private theorem forkSpan_pow_succ_mul_vertexIdempotent {t : ℕ} {w : Π}
    (hw : w ∈ forkSpan k G c ^ (t + 1)) {v : Fin n} (hv : (v : ℕ) = c) :
    w * π (vertexIdempotent k (vertex G v)) = w := by
  have hturn {l : ℕ} : forkTurn k G c l * π (vertexIdempotent k (vertex G v)) =
      forkTurn k G c l := by
    rw [forkTurn, mul_assoc, signlessArrow_mul_vertexIdempotent, ite_eq_left hv.symm]
  rw [pow_succ] at hw
  refine Submodule.mul_induction_on hw (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hb
    rw [mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, hturn, hturn]
  · rw [add_mul, ha, hb]

/-- A closed path from a vertex `a` of the long arm through the branch node, with a word `w` in
the leaf backtracks in its middle, is a sum of commutators when `2` is a unit: rotating its climb
from the branch node back to `a` to the end leaves `w` times a positive power of `x + y`. -/
private theorem ladderValley_mul_mul_forkEntry_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    {a : Fin n} {h t : ℕ} (hh : c - (a : ℕ) = h + 1) {w : Π} (hw : w ∈ forkSpan k G c ^ t) :
    ladderValley (forkUp k G c) (forkDown k G c) 0 0 (h + 1) * w *
      (ladderValley (forkUp k G c) (forkDown k G c) 0 (h + 1) 0 *
        π (vertexIdempotent k (vertex G a))) ∈ commutatorSubmodule k Π := by
  have heX : π (vertexIdempotent k (vertex G a)) *
      ladderValley (forkUp k G c) (forkDown k G c) 0 0 (h + 1) =
        ladderValley (forkUp k G c) (forkDown k G c) 0 0 (h + 1) := by
    rw [← u_mul_ladderValley, ← mul_assoc, zero_add, forkUp,
      vertexIdempotent_mul_signlessArrow, ite_eq_left (by omega)]
  -- The descent to the branch node followed by the climb back is a power of `q = -(x + y)`.
  have hYX : ladderValley (forkUp k G c) (forkDown k G c) 0 (h + 1) 0 *
      ladderValley (forkUp k G c) (forkDown k G c) 0 0 (h + 1) =
        ((-1 : ℤ) ^ ((h + 1).choose 2 + (h + 1))) •
          (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)) ^ (h + 1) := by
    rw [ladderValley_mul_ladderValley_zero_eq_pow (forkDown_mul_forkUp_add k hn hG),
      eq_neg_of_add_eq_zero_left (forkDown_mul_forkUp_add_forkTurn k hn hG),
      neg_pow (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)), ← mul_assoc, ← pow_add]
    simp [zsmul_eq_mul]
  have hsum : forkTurn k G c (c + 1) + forkTurn k G c (c + 2) ∈ forkSpan k G c :=
    add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hlow : w * (forkTurn k G c (c + 1) + forkTurn k G c (c + 2)) ^ (h + 1) ∈
      commutatorSubmodule k Π := by
    refine mem_commutatorSubmodule_of_mem_forkSpan_pow k hn hG h2 (t := t + (h + 1)) (by omega) ?_
    rw [pow_add]
    exact Submodule.mul_mem_mul hw (Submodule.pow_mem_pow _ hsum _)
  rw [mul_assoc, mul_mem_commutatorSubmodule_comm, mul_assoc, mul_assoc, heX, hYX, mul_smul_comm]
  exact zsmul_mem hlow _

/-- **Every closed path of positive length is a sum of commutators**, when `2` is a unit. -/
private theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_fork
    (h2 : IsUnit (2 : k)) {a : Fin n} (p : Path (vertex G a) (vertex G a)) (hp : 0 < p.length) :
    π (ofPath ⟨_, _, p⟩) ∈ commutatorSubmodule k Π := by
  -- The path has one of the normal forms of `forkNormalForm_ofPath`. A closed valley word on the
  -- long arm is handled by the ladder; a path through the branch node is rotated so that its
  -- final step comes first, leaving a nonempty word in the leaf backtracks. A path at the branch
  -- node whose word is empty is an integer multiple of its idempotent, and it vanishes since its
  -- augmentation does.
  have hspan {t : ℕ} (ht : 0 < t) {w : Π} (hw : w ∈ forkSpan k G c ^ t) :
      w ∈ commutatorSubmodule k Π :=
    mem_commutatorSubmodule_of_mem_forkSpan_pow k hn hG h2 ht hw
  have hnf := forkNormalForm_ofPath k hn hG p
  rw [ForkNormalForm] at hnf
  simp only [vertexEquiv_symm_vertex, ← vertexIdempotent_eq_ofPath] at hnf
  rcases hnf with ⟨m, s, r, ε, hm, hL, hs, hr, hz⟩ |
    ⟨t, s₀, w, D, hw, -, hj, -, hz, ε, hD⟩ | ⟨t, s₀, w, D, hw, -, hj, -, hz, ε, hD⟩ |
    ⟨hL, -, -, -⟩
  · -- A closed valley word on the long arm.
    obtain rfl : s = r := by omega
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hd : forkDown k G c (m + s) * π (vertexIdempotent k (vertex G a)) =
        forkDown k G c (m + s) := by
      rw [forkDown, signlessArrow_mul_vertexIdempotent, ite_eq_left (by omega)]
    rw [hz, ← ladderValley_mul_d, mul_assoc, hd, ladderValley_mul_d]
    exact zsmul_mem (ladderValley_mem_commutatorSubmodule_of_u_eq_zero k
      (forkDown_mul_forkUp_add k hn hG) (forkUp_self_eq_zero k hG) m s.succ_pos) ε
  · -- A path through the branch node from a vertex of the long arm.
    rw [forkEntry, ite_eq_left hj] at hD
    rcases Nat.eq_zero_or_pos (c - a) with h0 | hpos
    · -- At the branch node itself the path is the word `w`.
      rw [h0, ladderValley_zero_zero, one_mul] at hz hD
      rw [hz, hD, mul_smul_comm]
      cases t with
      | succ t =>
        rw [forkSpan_pow_succ_mul_vertexIdempotent k hw (by omega)]
        exact zsmul_mem (hspan t.succ_pos hw) ε
      | zero =>
        -- A word without backtracks is an integer, which vanishes by the augmentation.
        rw [pow_zero] at hw
        obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hw
        have hform : ε • (algebraMap ℤ Π y * π (vertexIdempotent k (vertex G a))) =
            algebraMap k Π ((ε * y : ℤ) : k) * π (vertexIdempotent k (vertex G a)) := by
          simp [zsmul_eq_mul, mul_assoc]
        have hpath : π (ofPath ⟨_, _, p⟩) =
            algebraMap k Π ((ε * y : ℤ) : k) * π (vertexIdempotent k (vertex G a)) := by
          rw [hz, hD, mul_smul_comm, hform]
        rw [hform, ← hpath,
          signlessPreprojectiveMk_ofPath_eq_zero_of_eq_algebraMap_mul k p hp hpath]
        exact zero_mem _
    · -- Rotating the climb out of the branch node to the end leaves `w` times a power of `q`.
      obtain ⟨h, hh⟩ : ∃ h, c - (a : ℕ) = h + 1 := ⟨c - a - 1, by omega⟩
      rw [hz, hD, hh, mul_smul_comm]
      exact zsmul_mem (ladderValley_mul_mul_forkEntry_mem_commutatorSubmodule k hn hG h2 hh hw) ε
  · -- A path through the branch node from a leaf.
    rw [forkEntry, ite_eq_right (by omega)] at hD
    have heX : π (vertexIdempotent k (vertex G a)) * signlessArrow k G c a =
        signlessArrow k G c a := by
      rw [vertexIdempotent_mul_signlessArrow, ite_eq_left rfl]
    have hWX : w * D * signlessArrow k G c a = ε • (w * forkTurn k G c a) := by
      rw [hD, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, heX, ← forkTurn]
    have hturn : forkTurn k G c a ∈ forkSpan k G c := by
      obtain hl | hl : (a : ℕ) = c + 1 ∨ (a : ℕ) = c + 2 := by omega
      all_goals exact Submodule.subset_span (by simp [hl])
    have hlow : w * forkTurn k G c a ∈ commutatorSubmodule k Π := by
      refine hspan (t := t + 1) t.succ_pos ?_
      rw [pow_succ]
      exact Submodule.mul_mem_mul hw hturn
    rw [hz, mul_assoc, mul_mem_commutatorSubmodule_comm, hWX]
    exact zsmul_mem hlow ε
  · -- The empty path at a leaf has length zero.
    omega

end ForkGraph

/-! ### The `Dₙ` diagram -/

variable (k : Type*) {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Q" => DoubledQuiver DG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

section CommRing

variable [CommRing k]

/-- **Every path of positive length in the signless algebra of `Dₙ` is a sum of commutators**,
over every commutative ring in which `2` is a unit. -/
theorem signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (x : Quiver.TotalPath Q) (hx : 0 < x.2.2.length) :
    σ (ofPath x) ∈ commutatorSubmodule k Π := by
  by_cases hn : 3 ≤ n
  swap
  · -- Below rank three the diagram has no edges, hence no paths of positive length.
    obtain ⟨a, b, p⟩ := x
    cases p with
    | nil =>
      simp only [Path.length_nil] at hx
      omega
    | cons q e => exact absurd e.down (not_diagramGraph_D_adj (n := n) (by omega) _ _)
  obtain ⟨a', b', p⟩ := x
  obtain ⟨a, rfl⟩ := exists_eq_vertex DG a'
  obtain ⟨b, rfl⟩ := exists_eq_vertex DG b'
  by_cases hab : a = b
  · subst hab
    exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_fork k (c := n - 3)
      (by omega) (diagramGraph_D_adj hn) h2 p hx
  · exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne k p
      fun h => hab (vertex_injective DG h)

/-- **The cyclic quotient of the signless algebra of `Dₙ` vanishes in positive degrees** when `2`
is a unit: every homogeneous piece of positive path degree lies in the commutator submodule. -/
theorem signlessPreprojectiveGrade_D_le_commutatorSubmodule (h2 : IsUnit (2 : k)) {d : ℕ}
    (hd : 0 < d) : signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k h2) hd

/-- **The commutator submodule of the signless algebra of `Dₙ` is the augmentation kernel** when
`2` is a unit. The augmentation onto the commutative algebra of vertex coefficients kills
commutators, and every element of its kernel is a combination of paths of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_D_eq_ker (h2 : IsUnit (2 : k)) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k h2)

/-- **The cyclic quotient of the signless algebra of `Dₙ` has dimension `n`** over every
nontrivial commutative ring in which `2` is a unit, one for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_D [Nontrivial k]
    (h2 : IsUnit (2 : k)) : Module.finrank k (cyclicQuotient k Π) = n := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k h2),
    ← Nat.card_congr (vertexEquiv DG), Nat.card_fin, DynkinType.rank_D]

end CommRing

/-! ### Orientations -/

section Orientation

variable [CommRing k] (o : Orientation (diagramGraph (DynkinType.D n).cartanMatrix))

/-- **Every path of positive length in the preprojective algebra of an orientation of `Dₙ` is a
sum of commutators**, over every commutative ring in which `2` is a unit. -/
theorem preprojectiveMk_D_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver DG o))) (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver DG o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver DG o)) :=
  (dColoring n).preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_D_ofPath_mem_commutatorSubmodule k h2) x hx

/-- **The cyclic quotient of the preprojective algebra of an orientation of `Dₙ` vanishes in
positive degrees** when `2` is a unit: every homogeneous piece of positive path degree lies in the
commutator submodule. -/
theorem preprojectiveGrade_D_le_commutatorSubmodule (h2 : IsUnit (2 : k)) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver DG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver DG o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_D_ofPath_mem_commutatorSubmodule k o h2) hd

end Orientation

end TauCeti
