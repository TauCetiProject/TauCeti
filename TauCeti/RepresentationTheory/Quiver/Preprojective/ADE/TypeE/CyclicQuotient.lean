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
# The cyclic quotients of the `E₆`, `E₇` and `E₈` preprojective algebras

The cyclic quotient `Π / [Π, Π]` of an algebra is its zeroth Hochschild homology. For the
preprojective algebra `Π(Q)` of a quiver `Q` whose underlying graph is a tree, Liu and Wang
identify its degree-`(q + 2)` piece with the second Hochschild cohomology `HH^{2,q}` of the
two-dimensional Ginzburg algebra `Π₂(Q)`, which controls the `A∞` deformations of the zigzag
algebra of the tree. This file shows that for `E₆`, `E₇` and `E₈` the cyclic quotient is
concentrated in path degree zero, where it is free on the vertices, over every commutative ring in
which `2` and `3`, respectively `2`, `3` and `5` for `E₈`, are units.

## The argument

In the Bourbaki labelling of `Eₙ` the node `3` is the branch node; write `x`, `y` and `z` for the
backtracks from it into the leaf `1`, into the arm `2, 0` and into the long arm `4, 5, …`, so that
`x + y + z = 0`. By the normal forms of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic`, every path is a multiple of a
valley word on one arm, or a climb out of the branch node after a word `w` in `x` and `y` and a
descent into the branch node. A path between distinct vertices is a commutator with its target
idempotent. A closed path is treated by rotating one of its factors from the front to the back:

* a closed valley word on an arm, which does not reach the branch node, rotates, by the ladder
  relations of the arm, into a power of the backtrack into that arm, and these powers are sums of
  commutators since the arm ends (`TauCeti.ladderValley_mem_commutatorSubmodule_of_u_eq_zero`);
* a closed path through the branch node rotates into `w` times a power of `x`, `y` or `z`, a word
  in `x` and `y` which is nonempty since the path has positive length.

So for every `n ≥ 4`, every path of positive length in the signless algebra of `Eₙ` is a sum of
commutators as soon as every nonempty word in `x` and `y` is. For `E₆` the long arm has two nodes,
so `x ^ 2 = 0`, `y ^ 3 = 0` and `(x + y) ^ 3 = (-z) ^ 3 = 0`, and the words in `x` and `y` are
sums of commutators when `2` and `3` are units
(`TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow`). For `E₇` the long arm has three nodes,
so `(x + y) ^ 4 = z ^ 4 = 0`, and the same holds when `2` and `3` are units
(`TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four`). For `E₈` the long arm
has four nodes, so `(x + y) ^ 5 = z ^ 5 = 0`, and the words in `x` and `y` are sums of commutators
when `2`, `3` and `5` are units
(`TauCeti.mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_five`).
These are the bad characteristics of `E₆`, `E₇` and `E₈` in Liu and Wang's intrinsic formality
theorem; the nonvanishing of the cyclic quotient in positive degrees in the bad characteristics is
not proved here.

Consequently the commutator submodule of `Π⁺(Eₙ)` for `n = 6, 7, 8` is exactly the kernel of the
augmentation onto the vertex coefficients, and the augmentation induces
`Π⁺(Eₙ) / [Π⁺(Eₙ), Π⁺(Eₙ)] ≃ k^{Eₙ}`. Through the bipartite sign rescaling, the same vanishing
holds for the additive preprojective algebra of every orientation of `E₆`, `E₇` and `E₈`. The `E₈`
statements are about the graph
`TauCeti.zigzagE8Graph`, whose preprojective algebras the finite-dimensionality results of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic` also concern.

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
* `TauCeti.signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule`,
  `TauCeti.signlessPreprojectiveGrade_E7_le_commutatorSubmodule`,
  `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_E7_eq_ker`,
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E7`,
  `TauCeti.preprojectiveMk_E7_ofPath_mem_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_E7_le_commutatorSubmodule`: the corresponding statements for `E₇`,
  whose cyclic quotient has dimension `7`.
* `TauCeti.signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule`,
  `TauCeti.signlessPreprojectiveGrade_E8_le_commutatorSubmodule`,
  `TauCeti.commutatorSubmodule_signlessPreprojectiveAlgebra_E8_eq_ker`,
  `TauCeti.finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E8`,
  `TauCeti.preprojectiveMk_E8_ofPath_mem_commutatorSubmodule` and
  `TauCeti.preprojectiveGrade_E8_le_commutatorSubmodule`: the corresponding statements for `E₈`
  when `2`, `3` and `5` are units, with a cyclic quotient of dimension `8`.

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

/-! ### Closed paths in `Eₙ` -/

/-- Two nodes on arms of `Eₙ` coincide only at the same distance from the branch node, and on the
same arm unless both are the branch node. -/
private theorem eArm_eq_eArm {n : ℕ} {a b : Fin 3} {p q : ℕ} (h : eArm n a p = eArm n b q)
    (hlt : eArm n a p < n) : p = q ∧ (p = 0 ∨ a = b) := by
  rcases p with _ | _ | _ | p <;> rcases q with _ | _ | _ | q <;>
    fin_cases a <;> fin_cases b <;> simp [eArm] at h hlt ⊢ <;> omega

section EGraph

variable (k : Type*) [CommRing k] {n : ℕ} (hn : 4 ≤ n)
include hn

local notation "G" => diagramGraph (CartanMatrix.E n)
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver G)

/-- Every arm of `Eₙ` ends: there is no step away from the branch node beyond its last node. -/
private theorem exists_eUp_eq_zero (a : Fin 3) : ∃ N, eUp k n a N = 0 := by
  fin_cases a
  · exact ⟨1, signlessArrow_e_eq_zero k (by simp [eArm])⟩
  · exact ⟨2, signlessArrow_e_eq_zero k (by simp [eArm])⟩
  · exact ⟨n - 4, signlessArrow_e_eq_zero k (by simp [eArm]; omega)⟩

/-- The positive powers of a backtrack at the branch node of `Eₙ` are sums of commutators. -/
private theorem eTurn_pow_mem_commutatorSubmodule (a : Fin 3) {j : ℕ} (hj : 0 < j) :
    eTurn k n a ^ j ∈ commutatorSubmodule k Π := by
  obtain ⟨N, hN⟩ := exists_eUp_eq_zero k hn a
  exact pow_d_mul_u_mem_commutatorSubmodule k (eDown_mul_eUp_add k hn a) hN hj

omit hn in
/-- A nonempty word in the backtracks at the branch node ends at the branch node. -/
private theorem eSpan_pow_succ_mul_vertexIdempotent {t : ℕ} {w : Π} (hw : w ∈ eSpan k n ^ (t + 1))
    {v : Fin n} (hv : (v : ℕ) = 3) : w * π (vertexIdempotent k (vertex G v)) = w := by
  have hturn (a : Fin 3) : eTurn k n a * π (vertexIdempotent k (vertex G v)) = eTurn k n a := by
    rw [eTurn, mul_assoc, eUp, signlessArrow_mul_vertexIdempotent,
      ite_eq_left (by rw [eArm_zero, hv])]
  rw [pow_succ] at hw
  refine Submodule.mul_induction_on hw (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hb
    rw [mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, hturn, hturn]
  · rw [add_mul, ha, hb]

/-- **Every closed path of positive length in the signless algebra of `Eₙ` is a sum of
commutators**, once every nonempty word in the backtracks at the branch node is. -/
private theorem signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan
    (hspan : ∀ t, ∀ w ∈ eSpan k n ^ (t + 1), w ∈ commutatorSubmodule k Π) {a : Fin n}
    (p : Path (vertex G a) (vertex G a)) (hp : 0 < p.length) :
    π (ofPath ⟨_, _, p⟩) ∈ commutatorSubmodule k Π := by
  have hnf := eNormalForm_ofPath k hn p
  rw [ENormalForm] at hnf
  simp only [vertexEquiv_symm_vertex, ← vertexIdempotent_eq_ofPath] at hnf
  rcases hnf with ⟨c, m, s, r, ε, -, hL, hs, hr, hz⟩ |
    ⟨c, c', h, t, s₀, ε, w, hw, hs₀, hh, hL, hz⟩
  · -- A closed valley word on an arm rotates into a power of the backtrack into the arm.
    obtain rfl : s = r := by
      have := (eArm_eq_eArm (hs.trans hr.symm) (hs ▸ a.2)).1
      omega
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hd : eDown k n c (m + s) * π (vertexIdempotent k (vertex G a)) = eDown k n c (m + s) := by
      rw [eDown, signlessArrow_mul_vertexIdempotent, ite_eq_left (by rw [← hs, add_assoc])]
    obtain ⟨N, hN⟩ := exists_eUp_eq_zero k hn c
    rw [hz, ← ladderValley_mul_d, mul_assoc, hd, ladderValley_mul_d]
    exact zsmul_mem (ladderValley_mem_commutatorSubmodule_of_u_eq_zero k
      (eDown_mul_eUp_add k hn c) hN m s.succ_pos) ε
  obtain ⟨rfl, hc⟩ := eArm_eq_eArm (hh.trans hs₀.symm) (hh ▸ a.2)
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · -- At the branch node the path is the word `w`, which is nonempty.
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [ladderValley_zero_zero, one_mul] at hz
    rw [hz, mul_smul_comm, eSpan_pow_succ_mul_vertexIdempotent k hw (by rw [← hh, eArm_zero])]
    exact zsmul_mem (hspan t w hw) ε
  · -- On an arm, rotating the climb out of the branch node to the end leaves `w` times a power of
    -- the backtrack into the arm.
    obtain rfl := hc.resolve_left hpos.ne'
    obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    have heX : π (vertexIdempotent k (vertex G a)) *
        ladderValley (eUp k n c) (eDown k n c) 0 0 (h + 1) =
          ladderValley (eUp k n c) (eDown k n c) 0 0 (h + 1) := by
      rw [← u_mul_ladderValley, ← mul_assoc, zero_add, eUp, vertexIdempotent_mul_signlessArrow,
        ite_eq_left hh]
    have hYX : ladderValley (eUp k n c) (eDown k n c) 0 (h + 1) 0 *
        ladderValley (eUp k n c) (eDown k n c) 0 0 (h + 1) =
          ((-1 : ℤ) ^ (h + 1).choose 2) • eTurn k n c ^ (h + 1) := by
      rw [ladderValley_mul_ladderValley_zero_eq_pow (eDown_mul_eUp_add k hn c), zsmul_eq_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, eTurn]
    have hlow : w * eTurn k n c ^ (h + 1) ∈ eSpan k n ^ (t + h + 1) := by
      rw [show t + h + 1 = t + (h + 1) by omega, pow_add]
      exact Submodule.mul_mem_mul hw (Submodule.pow_mem_pow _ (eTurn_mem_eSpan k hn c) _)
    rw [hz, mul_assoc, mul_mem_commutatorSubmodule_comm, mul_smul_comm, smul_mul_assoc, mul_assoc,
      mul_assoc, heX, hYX, mul_smul_comm]
    exact zsmul_mem (zsmul_mem (hspan _ _ hlow) _) ε

end EGraph

variable (k : Type*) [CommRing k]

/-! ### The `E₆` diagram -/

section E6

/-- If `2` and `3` are units, every nonempty word in the backtracks at the branch node of `E₆` is
a sum of commutators. -/
private theorem mem_commutatorSubmodule_of_mem_eSpan_six_pow (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (t : ℕ) (w : signlessPreprojectiveAlgebra k
      (DoubledQuiver (diagramGraph (CartanMatrix.E 6))))
    (hw : w ∈ eSpan k 6 ^ (t + 1)) :
    w ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 6)))) := by
  have hn : 4 ≤ 6 := by norm_num
  have hsum : eTurn k 6 0 + eTurn k 6 1 = -eTurn k 6 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k hn)
  refine mem_commutatorSubmodule_of_mem_span_pair_pow h2 h3 (eTurn_zero_sq k hn)
    (eTurn_one_pow_three k hn) ?_ ?_ ?_ (eTurn_pow_mem_commutatorSubmodule k hn 1 two_pos) ?_ hw
  · rw [hsum, neg_pow, eTurn_two_pow k (n := 6) hn, mul_zero]
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 0 one_pos
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 1 one_pos
  · rw [hsum, neg_pow]
    exact neg_one_pow_mul_mem_commutatorSubmodule
      (eTurn_pow_mem_commutatorSubmodule k hn 2 two_pos) 2

local notation "EG" => diagramGraph DynkinType.E6.cartanMatrix
local notation "Q" => DoubledQuiver EG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

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
    obtain ⟨a, rfl⟩ := exists_eq_vertex _ a'
    obtain ⟨b, rfl⟩ := exists_eq_vertex _ b'
    by_cases hab : a = b
    · subst hab
      exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan k (n := 6)
        (by norm_num) (mem_commutatorSubmodule_of_mem_eSpan_six_pow k h2 h3) p hx
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

/-! #### Orientations of `E₆` -/

variable (o : Orientation EG)

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
positive degrees** when `2` and `3` are units: every homogeneous piece of positive path degree lies
in the commutator submodule. -/
theorem preprojectiveGrade_E6_le_commutatorSubmodule (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver EG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver EG o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_E6_ofPath_mem_commutatorSubmodule k o h2 h3) hd

end E6

/-! ### The `E₇` diagram -/

section E7

/-- If `2` and `3` are units, every nonempty word in the backtracks at the branch node of `E₇` is
a sum of commutators. -/
private theorem mem_commutatorSubmodule_of_mem_eSpan_seven_pow (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (t : ℕ) (w : signlessPreprojectiveAlgebra k
      (DoubledQuiver (diagramGraph (CartanMatrix.E 7))))
    (hw : w ∈ eSpan k 7 ^ (t + 1)) :
    w ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 7)))) := by
  have hn : 4 ≤ 7 := by norm_num
  have hsum : eTurn k 7 0 + eTurn k 7 1 = -eTurn k 7 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k hn)
  have hpow {j : ℕ} (hj : 0 < j) : (eTurn k 7 0 + eTurn k 7 1) ^ j ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 7)))) := by
    rw [hsum, neg_pow]
    exact neg_one_pow_mul_mem_commutatorSubmodule (eTurn_pow_mem_commutatorSubmodule k hn 2 hj) j
  refine mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_four h2 h3 (eTurn_zero_sq k hn)
    (eTurn_one_pow_three k hn) ?_ ?_ ?_ (eTurn_pow_mem_commutatorSubmodule k hn 1 two_pos)
    (hpow two_pos) (hpow three_pos) hw
  · rw [hsum, neg_pow, eTurn_two_pow k (n := 7) hn, mul_zero]
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 0 one_pos
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 1 one_pos

local notation "EG" => diagramGraph DynkinType.E7.cartanMatrix
local notation "Q" => DoubledQuiver EG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

/-- **Every path of positive length in the signless algebra of `E₇` is a sum of commutators**,
over every commutative ring in which `2` and `3` are units. -/
theorem signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (x : Quiver.TotalPath Q) (hx : 0 < x.2.2.length) :
    σ (ofPath x) ∈ commutatorSubmodule k Π := by
  -- The `E₇` Cartan matrix is `CartanMatrix.E 7`, for which the normal forms are proved.
  have key : ∀ C : Matrix (Fin 7) (Fin 7) ℤ, C = CartanMatrix.E 7 →
      ∀ x : Quiver.TotalPath (DoubledQuiver (diagramGraph C)), 0 < x.2.2.length →
        signlessPreprojectiveMk k _ (ofPath x) ∈ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph C))) := by
    rintro C rfl ⟨a', b', p⟩ hx
    obtain ⟨a, rfl⟩ := exists_eq_vertex _ a'
    obtain ⟨b, rfl⟩ := exists_eq_vertex _ b'
    by_cases hab : a = b
    · subst hab
      exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan k (n := 7)
        (by norm_num) (mem_commutatorSubmodule_of_mem_eSpan_seven_pow k h2 h3) p hx
    · exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne k p
        fun h => hab (vertex_injective _ h)
  exact key _ DynkinType.cartanMatrix_E7 x hx

/-- **The cyclic quotient of the signless algebra of `E₇` vanishes in positive degrees** when `2`
and `3` are units: every homogeneous piece of positive path degree lies in the commutator
submodule. -/
theorem signlessPreprojectiveGrade_E7_le_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k h2 h3) hd

/-- **The commutator submodule of the signless algebra of `E₇` is the augmentation kernel** when
`2` and `3` are units. The augmentation onto the commutative algebra of vertex coefficients kills
commutators, and every element of its kernel is a combination of paths of positive length. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_E7_eq_ker (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k h2 h3)

/-- **The cyclic quotient of the signless algebra of `E₇` has dimension `7`** over every
nontrivial commutative ring in which `2` and `3` are units, one for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E7 [Nontrivial k]
    (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) : Module.finrank k (cyclicQuotient k Π) = 7 := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k h2 h3),
    ← Nat.card_congr (vertexEquiv EG), Nat.card_fin, DynkinType.rank_E7]

/-! #### Orientations of `E₇` -/

variable (o : Orientation EG)

/-- **Every path of positive length in the preprojective algebra of an orientation of `E₇` is a
sum of commutators**, over every commutative ring in which `2` and `3` are units. -/
theorem preprojectiveMk_E7_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (x : Quiver.TotalPath (Symmetrify (OrientedQuiver EG o)))
    (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver EG o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver EG o)) :=
  e7Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_E7_ofPath_mem_commutatorSubmodule k h2 h3) x hx

/-- **The cyclic quotient of the preprojective algebra of an orientation of `E₇` vanishes in
positive degrees** when `2` and `3` are units: every homogeneous piece of positive path degree lies
in the commutator submodule. -/
theorem preprojectiveGrade_E7_le_commutatorSubmodule (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver EG o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver EG o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_E7_ofPath_mem_commutatorSubmodule k o h2 h3) hd

end E7

/-! ### The `E₈` diagram -/

section E8

/-- If `2`, `3` and `5` are units, every nonempty word in the backtracks at the branch node of
`E₈` is a sum of commutators. -/
private theorem mem_commutatorSubmodule_of_mem_eSpan_eight_pow (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k)) (t : ℕ) (w : signlessPreprojectiveAlgebra k
      (DoubledQuiver (diagramGraph (CartanMatrix.E 8))))
    (hw : w ∈ eSpan k 8 ^ (t + 1)) :
    w ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 8)))) := by
  have hn : 4 ≤ 8 := by norm_num
  have hsum : eTurn k 8 0 + eTurn k 8 1 = -eTurn k 8 2 :=
    eq_neg_of_add_eq_zero_left (eTurn_add_eTurn_add_eTurn k hn)
  -- The powers of `x + y = -z` are sums of commutators since the long arm ends.
  have hpow {j : ℕ} (hj : 0 < j) : (eTurn k 8 0 + eTurn k 8 1) ^ j ∈ commutatorSubmodule k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph (CartanMatrix.E 8)))) := by
    rw [hsum, neg_pow]
    exact neg_one_pow_mul_mem_commutatorSubmodule (eTurn_pow_mem_commutatorSubmodule k hn 2 hj) j
  refine mem_commutatorSubmodule_of_mem_span_pair_pow_of_add_pow_five h2 h3 h5
    (eTurn_zero_sq k hn) (eTurn_one_pow_three k hn) ?_ ?_ ?_
    (eTurn_pow_mem_commutatorSubmodule k hn 1 two_pos) (hpow two_pos) (hpow three_pos)
    (hpow four_pos) hw
  · rw [hsum, neg_pow, eTurn_two_pow k (n := 8) hn, mul_zero]
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 0 one_pos
  · simpa using eTurn_pow_mem_commutatorSubmodule k hn 1 one_pos

local notation "Q" => DoubledQuiver zigzagE8Graph
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q

/-- **Every path of positive length in the signless algebra of `E₈` is a sum of commutators**,
over every commutative ring in which `2`, `3` and `5` are units. -/
theorem signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k)) (x : Quiver.TotalPath Q)
    (hx : 0 < x.2.2.length) :
    σ (ofPath x) ∈ commutatorSubmodule k Π := by
  -- The `E₈` graph is the diagram of `CartanMatrix.E 8`, for which the normal forms are proved.
  have key : ∀ G : SimpleGraph (Fin 8), G = diagramGraph (CartanMatrix.E 8) →
      ∀ x : Quiver.TotalPath (DoubledQuiver G), 0 < x.2.2.length →
        signlessPreprojectiveMk k _ (ofPath x) ∈ commutatorSubmodule k
          (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
    rintro G rfl ⟨a', b', p⟩ hx
    obtain ⟨a, rfl⟩ := exists_eq_vertex _ a'
    obtain ⟨b, rfl⟩ := exists_eq_vertex _ b'
    by_cases hab : a = b
    · subst hab
      exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_eSpan k (n := 8)
        (by norm_num) (mem_commutatorSubmodule_of_mem_eSpan_eight_pow k h2 h3 h5) p hx
    · exact signlessPreprojectiveMk_ofPath_mem_commutatorSubmodule_of_ne k p
        fun h => hab (vertex_injective _ h)
  exact key _ (by rw [zigzagE8Graph_eq_diagramGraph, DynkinType.cartanMatrix_E8]; rfl) x hx

/-- **The cyclic quotient of the signless algebra of `E₈` vanishes in positive degrees** when `2`,
`3` and `5` are units: every homogeneous piece of positive path degree lies in the commutator
submodule. -/
theorem signlessPreprojectiveGrade_E8_le_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k)) {d : ℕ} (hd : 0 < d) :
    signlessPreprojectiveGrade k Q d ≤ commutatorSubmodule k Π :=
  signlessPreprojectiveGrade_le_commutatorSubmodule k
    (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k h2 h3 h5) hd

/-- **The commutator submodule of the signless algebra of `E₈` is the augmentation kernel** when
`2`, `3` and `5` are units. -/
theorem commutatorSubmodule_signlessPreprojectiveAlgebra_E8_eq_ker (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k)) :
    commutatorSubmodule k Π =
      LinearMap.ker (signlessPreprojectiveAugmentation (R := Q) k).toLinearMap :=
  commutatorSubmodule_signlessPreprojectiveAlgebra_eq_ker k
    (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k h2 h3 h5)

/-- **The cyclic quotient of the signless algebra of `E₈` has dimension `8`** over every
nontrivial commutative ring in which `2`, `3` and `5` are units, one for each vertex. -/
theorem finrank_cyclicQuotient_signlessPreprojectiveAlgebra_E8 [Nontrivial k]
    (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k)) :
    Module.finrank k (cyclicQuotient k Π) = 8 := by
  rw [finrank_cyclicQuotient_signlessPreprojectiveAlgebra k
      (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k h2 h3 h5),
    ← Nat.card_congr (vertexEquiv zigzagE8Graph), Nat.card_fin]

/-! #### Orientations of `E₈` -/

variable (o : Orientation zigzagE8Graph)

/-- **Every path of positive length in the preprojective algebra of an orientation of `E₈` is a
sum of commutators**, over every commutative ring in which `2`, `3` and `5` are units. -/
theorem preprojectiveMk_E8_ofPath_mem_commutatorSubmodule (h2 : IsUnit (2 : k))
    (h3 : IsUnit (3 : k)) (h5 : IsUnit (5 : k))
    (x : Quiver.TotalPath (Symmetrify (OrientedQuiver zigzagE8Graph o)))
    (hx : 0 < x.2.2.length) :
    preprojectiveMk k (OrientedQuiver zigzagE8Graph o) (ofPath x) ∈
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph o)) :=
  zigzagE8Coloring.preprojectiveMk_ofPath_mem_commutatorSubmodule k o
    (signlessPreprojectiveMk_E8_ofPath_mem_commutatorSubmodule k h2 h3 h5) x hx

/-- **The cyclic quotient of the preprojective algebra of an orientation of `E₈` vanishes in
positive degrees** when `2`, `3` and `5` are units: every homogeneous piece of positive path
degree lies in the commutator submodule. -/
theorem preprojectiveGrade_E8_le_commutatorSubmodule (h2 : IsUnit (2 : k)) (h3 : IsUnit (3 : k))
    (h5 : IsUnit (5 : k)) {d : ℕ} (hd : 0 < d) :
    preprojectiveGrade k (OrientedQuiver zigzagE8Graph o) d ≤
      commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph o)) :=
  preprojectiveGrade_le_commutatorSubmodule k
    (preprojectiveMk_E8_ofPath_mem_commutatorSubmodule k o h2 h3 h5) hd

end E8

end TauCeti
