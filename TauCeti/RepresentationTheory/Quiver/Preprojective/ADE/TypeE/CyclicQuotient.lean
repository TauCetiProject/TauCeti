/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic

/-!
# The cyclic quotient of the `E₆` preprojective algebra

The cyclic quotient `Π / [Π, Π]` of an algebra is its zeroth Hochschild homology. For the
preprojective algebra `Π(Q)` of a quiver `Q` whose underlying graph is a tree, Liu and Wang
identify its degree-`(q + 2)` piece with the second Hochschild cohomology `HH^{2,q}` of the
two-dimensional Ginzburg algebra `Π₂(Q)`, which controls the `A∞` deformations of the zigzag
algebra of the tree. This file shows that for `E₆` the cyclic quotient is concentrated in path
degree zero, where it is free on the vertices, over every commutative ring in which `2` and `3`
are units.

## The argument

In the Bourbaki labelling of `Eₙ`, write `x`, `y` and `z` for the backtracks from the branch node
into the leaf, into the arm of length two and into the long arm, so that `x ^ 2 = 0`, `y ^ 3 = 0`
and `x + y + z = 0`. By the normal forms of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic`, a path is, up to sign, a
valley word on one arm, or a climb out of the branch node after a word `w` in `x` and `y` and a
descent into the branch node. A path between distinct vertices is a commutator with its target
idempotent. A closed path is rotated:

* a closed valley word on an arm rotates, by the ladder relations of the arm, into a power of the
  backtrack into that arm (`TauCeti.ladderValley_mem_commutatorSubmodule_of_u_eq_zero`);
* a closed path through the branch node from a vertex of an arm rotates into `±` the word `w`
  times a power of the backtrack into that arm, a nonempty word in `x` and `y`.

So for every `n`, if every nonempty word in `x` and `y` is a sum of commutators, then so is every
closed path of positive length in the signless algebra of `Eₙ`. The powers of `x`, `y` and `z` are
sums of commutators (`TauCeti.pow_d_mul_u_mem_commutatorSubmodule`). For `E₆` the long arm has
two nodes, so `(x + y) ^ 3 = (-z) ^ 3 = 0`, and
`TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_three_eq_zero` shows that every
nonempty word in `x` and `y` is a sum of commutators once `2` and `3` are units. These are the bad
characteristics of `E₆` in Liu and Wang's intrinsic formality theorem; the nonvanishing of the
cyclic quotient in positive degrees in characteristic two or three is not proved here.

Consequently the commutator submodule of `Π⁺(E₆)` is exactly the kernel of the augmentation onto
the vertex coefficients, and the augmentation induces `Π⁺(E₆) / [Π⁺(E₆), Π⁺(E₆)] ≃ k^{E₆}`.
Through the bipartite sign rescaling, the same vanishing holds for the additive preprojective
algebra of every orientation of `E₆`. These consequences, and the case of a path between distinct
vertices, do not depend on the graph; they are in
`TauCeti.RepresentationTheory.Quiver.Preprojective.CyclicQuotient`.

## Main results

* `TauCeti.signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule`: if `2` and `3` are units,
  every path of positive length in `Π⁺(E₆)` lies in `[Π⁺(E₆), Π⁺(E₆)]`.
* `TauCeti.signlessPreprojectiveGrade_E6_le_commutatorSubmodule`: if `2` and `3` are units, every
  piece of positive path degree of `Π⁺(E₆)` lies in `[Π⁺(E₆), Π⁺(E₆)]`.
* `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_E6_eq_ker`: if `2` and `3` are units,
  the commutator submodule is the kernel of the augmentation.
* `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E6`: over a nontrivial commutative
  ring in which `2` and `3` are units, the cyclic quotient of `Π⁺(E₆)` has dimension `6`.
* `TauCeti.preprojectiveMk_E6_ofPath_mem_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_E6_le_commutatorSubmodule`: the same vanishing in positive degrees
  for the preprojective algebra `Π(Q)` of every orientation `Q` of `E₆`.

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

attribute [local instance] eNeighborSetFintype

/-! ### Closed paths in the signless algebra of `Eₙ` -/

section EGraph

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "G" => diagramGraph (CartanMatrix.E n)
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver G)

/-- Two rungs of the arms which are the same node are both the branch node, or the same rung of
the same arm. -/
private theorem eArm_eq_eArm {a b : Fin 3} {p q : ℕ} (hp : eArm n a p < n)
    (h : eArm n a p = eArm n b q) : p = 0 ∧ q = 0 ∨ a = b ∧ p = q := by
  fin_cases a <;> fin_cases b <;> simp only [eArm, Fin.reduceFinMk, Fin.isValue] at hp h ⊢ <;>
    (try split_ifs at hp h) <;> simp <;> omega

/-- Every arm has a last rung, from which there is no step away from the branch node. -/
private theorem exists_eUp_eq_zero (a : Fin 3) : ∃ N, eUp k n a N = 0 := by
  fin_cases a
  · exact ⟨1, signlessArrow_e_eq_zero k (by simp [eArm])⟩
  · exact ⟨2, signlessArrow_e_eq_zero k (by simp [eArm])⟩
  · exact ⟨n - 3, signlessArrow_e_eq_zero k (by simp [eArm]; omega)⟩

variable (hn : 4 ≤ n)
include hn

/-- The positive powers of the backtrack from the branch node into an arm are sums of
commutators. -/
private theorem eTurn_pow_mem_commutatorSubmodule (a : Fin 3) {j : ℕ} (hj : 0 < j) :
    eTurn k n a ^ j ∈ commutatorSubmodule k Π := by
  obtain ⟨N, hN⟩ := exists_eUp_eq_zero k a
  exact pow_d_mul_u_mem_commutatorSubmodule k (eDown_mul_eUp_add k hn a) hN hj

omit hn in
/-- A nonempty word in the backtracks at the branch node ends at the branch node. -/
private theorem eSpan_pow_succ_mul_vertexIdempotent {t : ℕ} {w : Π} (hw : w ∈ eSpan k n ^ (t + 1))
    {v : Fin n} (hv : (v : ℕ) = 3) : w * π (vertexIdempotent k (vertex G v)) = w := by
  have hturn (a : Fin 3) : eTurn k n a * π (vertexIdempotent k (vertex G v)) = eTurn k n a := by
    rw [eTurn, mul_assoc, eUp, signlessArrow_mul_vertexIdempotent, eArm_zero,
      ite_eq_left hv.symm]
  rw [pow_succ] at hw
  refine Submodule.mul_induction_on hw (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hb
    rw [mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, hturn, hturn]
  · rw [add_mul, ha, hb]

/-- **Closed paths reduce to words at the branch node.** If every nonempty word in the
backtracks at the branch node of `Eₙ` is a sum of commutators, then so is every closed path of
positive length in the signless algebra. -/
private theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan
    (hspan : ∀ t, 0 < t → ∀ w ∈ eSpan k n ^ t, w ∈ commutatorSubmodule k Π) {a : Fin n}
    (p : Path (vertex G a) (vertex G a)) (hp : 0 < p.length) :
    π (ofPath ⟨_, _, p⟩) ∈ commutatorSubmodule k Π := by
  have hnf := eNormalForm_ofPath k hn p
  simp only [vertexEquiv_symm_vertex, ← vertexIdempotent_eq_ofPath] at hnf
  rcases hnf with ⟨b, m, s, r, ε, hm, hL, hs, hr, hz⟩ |
    ⟨b, c, h, t, s₀, w, ε, hw, hs₀, hh, hL, hz⟩
  · -- A closed valley word on an arm rotates into a power of the backtrack into the arm.
    obtain rfl : s = r := by
      rcases eArm_eq_eArm (hs ▸ a.2) (hs.trans hr.symm) with h | h <;> omega
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hd : eDown k n b (m + s) * π (vertexIdempotent k (vertex G a)) = eDown k n b (m + s) := by
      rw [eDown, signlessArrow_mul_vertexIdempotent, ite_eq_left (by rw [← hs, add_assoc])]
    obtain ⟨N, hN⟩ := exists_eUp_eq_zero k b
    rw [hz, ← ladderValley_mul_d, mul_assoc, hd, ladderValley_mul_d]
    exact zsmul_mem (ladderValley_mem_commutatorSubmodule_of_u_eq_zero k
      (eDown_mul_eUp_add k hn b) hN m s.succ_pos) ε
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · -- At the branch node itself the path is, up to sign, the nonempty word `w`.
    rw [eArm_zero] at hh
    obtain rfl : s₀ = 0 := by
      rcases eArm_eq_eArm (hs₀ ▸ a.2) (hs₀.trans (hh.symm.trans (eArm_zero n c).symm)) with
        h | h <;> omega
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [hz, ladderValley_zero_zero, ladderValley_zero_zero, one_mul, one_mul, mul_smul_comm,
      eSpan_pow_succ_mul_vertexIdempotent k hw hh.symm]
    exact zsmul_mem (hspan _ t.succ_pos w hw) ε
  -- Away from the branch node the descent retraces the climb; rotating the climb to the end
  -- leaves `w` times a power of the backtrack into the arm.
  obtain ⟨rfl, rfl⟩ : c = b ∧ h = s₀ := by
    rcases eArm_eq_eArm (hh ▸ a.2) (hh.trans hs₀.symm) with h' | h'
    · omega
    · exact ⟨h'.1.symm, h'.2⟩
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have heX : π (vertexIdempotent k (vertex G a)) * ladderValley (eUp k n c) (eDown k n c) 0 0
      (h + 1) = ladderValley (eUp k n c) (eDown k n c) 0 0 (h + 1) := by
    rw [← u_mul_ladderValley, ← mul_assoc, zero_add, eUp, vertexIdempotent_mul_signlessArrow,
      ite_eq_left hh]
  have hYX : ladderValley (eUp k n c) (eDown k n c) 0 (h + 1) 0 *
      ladderValley (eUp k n c) (eDown k n c) 0 0 (h + 1) =
        (-1) ^ (h + 1).choose 2 * eTurn k n c ^ (h + 1) :=
    ladderValley_mul_ladderValley_zero_eq_pow (eDown_mul_eUp_add k hn c) (h + 1)
  have hlow : w * eTurn k n c ^ (h + 1) ∈ commutatorSubmodule k Π := by
    refine hspan (t + (h + 1)) (by omega) _ ?_
    rw [pow_add]
    exact Submodule.mul_mem_mul hw (Submodule.pow_mem_pow _ (eTurn_mem_eSpan k hn c) _)
  rw [hz, mul_assoc, mul_mem_commutatorSubmodule_comm, mul_smul_comm, smul_mul_assoc]
  refine zsmul_mem ?_ ε
  rw [mul_assoc, mul_assoc, heX, hYX, ← mul_assoc,
    ← ((Commute.neg_one_left w).pow_left _).eq, mul_assoc]
  exact neg_one_pow_mul_mem_commutatorSubmodule hlow _

end EGraph

/-! ### The `E₆` diagram -/

/-- **Nonempty words at the branch node of `E₆` are sums of commutators** when `2` and `3` are
units. -/
private theorem mem_commutatorSubmodule_of_mem_eSpan_six_pow (k : Type*) [CommRing k]
    (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) (t : ℕ) (ht : 0 < t) (w)
    (hw : w ∈ eSpan k 6 ^ t) :
    w ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 6)))) := by
  have hsum : eTurn k 6 0 + eTurn k 6 1 = -eTurn k 6 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k (by norm_num))
  refine mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_three_eq_zero h2 h3
    (eTurn_zero_sq k (by norm_num)) (eTurn_one_pow_three k (by norm_num)) ?_
    (by simpa only [pow_one] using eTurn_pow_mem_commutatorSubmodule k (by norm_num) 0 one_pos)
    (by simpa only [pow_one] using eTurn_pow_mem_commutatorSubmodule k (by norm_num) 1 one_pos)
    (eTurn_pow_mem_commutatorSubmodule k (by norm_num) 1 two_pos) ?_ ht hw
  · rw [hsum, neg_pow, eTurn_two_pow k (n := 6) (by norm_num), mul_zero]
  · rw [hsum, neg_sq]
    exact eTurn_pow_mem_commutatorSubmodule k (by norm_num) 2 two_pos

variable (k : Type*)

local notation "EG" => diagramGraph DynkinType.E6.cartanMatrix
local notation "Q" => DoubledQuiver EG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

section CommRing

variable [CommRing k]

/-- **Every path of positive length in the signless algebra of `E₆` is a sum of commutators**,
over every commutative ring in which `2` and `3` are units. -/
theorem signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (x : Quiver.TotalPath Q) (hx : 0 < x.2.2.length) :
    σ (ofPath x) ∈ commutatorSubmodule k Π := by
  -- The `E₆` Cartan matrix is `CartanMatrix.E 6`, for which the normal forms are proved.
  have key : ∀ C : Matrix (Fin 6) (Fin 6) ℤ, C = CartanMatrix.E 6 →
      ∀ x : Quiver.TotalPath (DoubledQuiver (diagramGraph C)), 0 < x.2.2.length →
        signlessPreprojectiveMk k _ (ofPath x) ∈ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
    rintro C rfl ⟨a', b', p⟩ hx
    obtain ⟨a, rfl⟩ := exists_eq_vertex (diagramGraph (CartanMatrix.E 6)) a'
    obtain ⟨b, rfl⟩ := exists_eq_vertex (diagramGraph (CartanMatrix.E 6)) b'
    by_cases hab : a = b
    · subst hab
      exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan k (by norm_num)
        (mem_commutatorSubmodule_of_mem_eSpan_six_pow k h2 h3) p hx
    · exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne k p
        fun h => hab (vertex_injective _ h)
  exact key _ DynkinType.cartanMatrix_E6 x hx

/-- **The cyclic quotient of the signless algebra of `E₆` vanishes in positive degrees** when `2`
and `3` are units: every homogeneous piece of positive path degree lies in the commutator
submodule. -/
theorem signlessPreprojectiveGrade_E6_le_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k h2 h3) hd

/-- **The commutator submodule of the signless algebra of `E₆` is the augmentation kernel** when
`2` and `3` are units. The augmentation onto the commutative algebra of vertex coefficients kills
commutators, and every element of its kernel is a combination of paths of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_E6_eq_ker (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k h2 h3)

/-- **The cyclic quotient of the signless algebra of `E₆` has dimension `6`** over every
nontrivial commutative ring in which `2` and `3` are units, one for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E6 [Nontrivial k]
    (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) : Module.finrank k (cyclicQuotient k Π) = 6 := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k h2 h3),
    ← Nat.card_congr (vertexEquiv EG), Nat.card_fin, DynkinType.rank_E6]

end CommRing

/-! ### Orientations -/

section Orientation

variable [CommRing k] (o : Orientation EG)

/-- **Every path of positive length in the preprojective algebra of an orientation of `E₆` is a
sum of commutators**, over every commutative ring in which `2` and `3` are units. -/
theorem preprojectiveMk_E6_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (x : Quiver.TotalPath (Symmetrify (OrientedQuiver EG o)))
    (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver EG o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver EG o)) :=
  e6Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_E6_ofPath_mem_commutatorSubmodule k h2 h3) x hx

/-- **The cyclic quotient of the preprojective algebra of an orientation of `E₆` vanishes in
positive degrees** when `2` and `3` are units: every homogeneous piece of positive path degree
lies in the commutator submodule. -/
theorem preprojectiveGrade_E6_le_commutatorSubmodule (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver EG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver EG o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_E6_ofPath_mem_commutatorSubmodule k o h2 h3) hd

end Orientation

end TauCeti
