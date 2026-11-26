/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.MultipleCover
public import Mathlib.Data.Finset.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The expected dimension of sphere-tree strata of Floer moduli spaces

A sequence of Floer solutions, such as pairs of pants of a fixed class `A` with fixed asymptotic
orbits, can converge to a *core* solution of class `A₀` carrying trees of pseudoholomorphic
spheres. On a positively spherically monotone or a spherically `c₁`-zero target such limits are
ruled out in the rigid and one-dimensional problems that define the pair-of-pants product and its
chain-level identities by a dimension count: after reduction to simple spheres the bubbled strata
have expected dimension at least two below that of the unbubbled problem. This file proves that
dimension count.

**The reduced stratum.** Each nonconstant bubble `v ∈ ι` of class `B v` is a `m v`-fold cover of a
simple sphere, and bubbles with the same image are grouped together: the simple images form a type
`κ`, `ρ v ∈ κ` is the image of `v`, and `B v = m v • B' (ρ v)`. Constant (ghost) bubbles have class
zero and are discarded. The simple spheres are joined to the core and to each other along a tree
of nodes: `parent w` is the component that `w` is attached to (`none` for the core), `node w` is
the point of that component at which `w` is attached and `root w` the point of `w` itself. The
*special points* of a component are the nodes on it, counted once if several spheres are attached
at the same point (`TauCeti.Floer.sphereTreeSpecialPoints`). The stratum is cut out of the product
of the moduli space of the core, of expected dimension `I₀`, with its special points, and of the
moduli spaces of the simple spheres with their special points, by one incidence condition of real
codimension `2n` at each node, for a target of real dimension `2n`. Its expected dimension is

`I₀ + ∑_w D(0, c₁(B' w)) + 2 #(special points) - 2n #κ`

(`TauCeti.Floer.sphereTreeDimension`), where `D(0, c) = 2(n - 3) + 2c` is the dimension of the
unparametrized simple spheres of Chern number `c` (`TauCeti.unmarkedVirtualDimension`). There are
at most two special points per node, with equality exactly when the special points of each
component are distinct (`TauCeti.Floer.sum_card_sphereTreeSpecialPoints_le`,
`TauCeti.Floer.sum_card_sphereTreeSpecialPoints_eq`), so the expected dimension is at most
`I₀ + 2 ∑_w c₁(B' w) - 2 #κ` (`TauCeti.Floer.sphereTreeDimension_le`), with equality for distinct
special points (`TauCeti.Floer.sphereTreeDimension_eq`).

**The dimension count.** Let `ind A` be the expected dimension of the unbubbled problem in class
`A`, which changes by `2 c₁(B)` when the class changes by `B`; for the pair of pants with capped
asymptotic orbits of gradings `μ₁`, `μ₂`, `μ₀` it is `μ₁ + μ₂ - μ₀ - n + 2 c₁(A)`. The core has
class `A₀` and the limit has class `A = A₀ + ∑_v B v`, so the core has expected dimension
`ind A - 2 ∑_v m v c₁(B' (ρ v))`. Every simple image is the image of a bubble and every bubble
covers it at least once, so if every simple sphere has `c₁ ≥ N` the reduced stratum has
expected dimension at most

`ind A - 2 #κ - 2 N (∑_v m v - #κ)`

(`TauCeti.Floer.sphereTreeDimension_le_sub_of_le_chern`). Covering a simple sphere several times
and bubbling the same simple sphere several times both lower the dimension.

* On a target where `c₁` is nonnegative on the classes of simple spheres, the stratum has
  expected dimension at most `ind A - 2 #κ`
  (`TauCeti.Floer.sphereTreeDimension_le_sub_two_mul_card`). This covers the spherically
  `c₁`-zero branch, where `c₁ = 0`.
* On a positively monotone target, `ω = τ c₁` with `τ > 0`, a nonconstant pseudoholomorphic sphere
  has positive area, hence `c₁ ≥ 1`, and the stratum has expected dimension at most
  `ind A - 2 ∑_v m v` (`TauCeti.Floer.sphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern`).
* In both cases a stratum with at least one nonconstant bubble has expected dimension at most
  `ind A - 2` (`TauCeti.Floer.sphereTreeDimension_le_sub_two`), so it has negative expected
  dimension in the problems with `ind A ≤ 1`
  (`TauCeti.Floer.sphereTreeDimension_neg_of_le_one`): the rigid counts of the product, of the
  differential and of the continuation maps, and the one-dimensional moduli spaces whose boundaries
  give their chain-level identities.

These are statements about expected dimensions. That a stratum of negative expected dimension is
empty for generic data is the transversality of the evaluation maps of simple spheres, which is not
proved here; nor is the identification of a Gromov–Floer limit with a reduced stratum.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 6.1 (simple stable maps and the reduction of a stable
  map) and Theorem 6.6.1 (semipositive targets).
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on sphere bubbling in semipositive Floer theory.
-/

public section

open Finset

namespace TauCeti.Floer

variable {κ P : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq P]

/-- The special points of a component of a tree of spheres attached to a core: the component is
the core for `x = none` and the sphere `v` for `x = some v`. Its special points are the points
`node w` at which the spheres `w` with `parent w = x` are attached to it, and for a sphere `v` also
the point `root v` at which `v` itself is attached to its parent. Points at which several spheres
are attached are counted once. -/
def sphereTreeSpecialPoints (parent : κ → Option κ) (node root : κ → P) (x : Option κ) :
    Finset P :=
  (univ.filter (parent · = x)).image node ∪ (x.map root).toFinset

theorem mem_sphereTreeSpecialPoints_iff {parent : κ → Option κ} {node root : κ → P}
    {x : Option κ} {p : P} :
    p ∈ sphereTreeSpecialPoints parent node root x ↔
      (∃ w, parent w = x ∧ node w = p) ∨ ∃ v, x = some v ∧ root v = p := by
  simp [sphereTreeSpecialPoints, eq_comm]

@[simp]
theorem sphereTreeSpecialPoints_none (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeSpecialPoints parent node root none = (univ.filter (parent · = none)).image node := by
  simp [sphereTreeSpecialPoints]

@[simp]
theorem sphereTreeSpecialPoints_some (parent : κ → Option κ) (node root : κ → P) (v : κ) :
    sphereTreeSpecialPoints parent node root (some v) =
      insert (root v) ((univ.filter (parent · = some v)).image node) := by
  rw [sphereTreeSpecialPoints, Option.map_some, Option.toFinset_some, union_comm, ← insert_eq]

/-- Each node contributes at most two special points, one on each of the two components it
joins. -/
theorem sum_card_sphereTreeSpecialPoints_le (parent : κ → Option κ) (node root : κ → P) :
    ∑ x, #(sphereTreeSpecialPoints parent node root x) ≤ 2 * Fintype.card κ := by
  calc ∑ x, #(sphereTreeSpecialPoints parent node root x)
      ≤ ∑ x : Option κ, (#(univ.filter (parent · = x)) + #(x.map root).toFinset) :=
        sum_le_sum fun x _ => (card_union_le _ _).trans (by grw [card_image_le])
    _ = 2 * Fintype.card κ := by
        rw [sum_add_distrib, ← card_eq_sum_card_fiberwise (by simp), Fintype.sum_option]
        simp [two_mul]

/-- The special points of the components of a tree of spheres are distinct exactly when there are
two special points per node: the spheres attached to one component are attached at distinct
points, and never at the point at which that component is itself attached. -/
theorem sum_card_sphereTreeSpecialPoints_eq {parent : κ → Option κ} {node root : κ → P}
    (hnode : ∀ v w, parent v = parent w → node v = node w → v = w)
    (hroot : ∀ v w, parent w = some v → node w ≠ root v) :
    ∑ x, #(sphereTreeSpecialPoints parent node root x) = 2 * Fintype.card κ := by
  have hcard (x : Option κ) : #(sphereTreeSpecialPoints parent node root x) =
      #(univ.filter (parent · = x)) + #(x.map root).toFinset := by
    rw [sphereTreeSpecialPoints, card_union_of_disjoint, card_image_of_injOn]
    · intro v hv w hw
      exact hnode v w (by simp_all)
    · rw [disjoint_right]
      rintro p hp
      obtain ⟨v, rfl, rfl⟩ : ∃ v, x = some v ∧ root v = p := by simpa [eq_comm] using hp
      simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
      exact fun w hw => hroot v w hw
  simp_rw [hcard]
  rw [sum_add_distrib, ← card_eq_sum_card_fiberwise (by simp), Fintype.sum_option]
  simp [two_mul]

/-- The expected dimension of a stratum of a moduli space of Floer solutions whose limits carry a
tree of simple pseudoholomorphic spheres, in a target of real dimension `2n`. The core has expected
dimension `I₀`, the simple spheres `v` have Chern numbers `c v`, and they are attached along the
tree `parent`, at the points `node v` of their parents and `root v` of themselves. It is `I₀`, plus
the dimensions `2(n - 3) + 2 c v` of the unparametrized spheres, plus two for each special point
of each component, minus the codimension `2n` of the incidence condition at each node. -/
def sphereTreeDimension (n I₀ : ℤ) (c : κ → ℤ) (parent : κ → Option κ) (node root : κ → P) : ℤ :=
  I₀ + ∑ v, unmarkedVirtualDimension n 0 (c v) +
    2 * ∑ x, (#(sphereTreeSpecialPoints parent node root x) : ℤ) - 2 * n * Fintype.card κ

theorem sphereTreeDimension_def (n I₀ : ℤ) (c : κ → ℤ) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n I₀ c parent node root =
      I₀ + ∑ v, unmarkedVirtualDimension n 0 (c v) +
        2 * ∑ x, (#(sphereTreeSpecialPoints parent node root x) : ℤ) -
          2 * n * Fintype.card κ := by
  rw [sphereTreeDimension]

/-- Without bubbles the stratum is the moduli space of the core. -/
@[simp]
theorem sphereTreeDimension_of_isEmpty [IsEmpty κ] (n I₀ : ℤ) (c : κ → ℤ)
    (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n I₀ c parent node root = I₀ := by
  rw [sphereTreeDimension, Fintype.sum_option]
  simp

/-- The expected dimension of a sphere-tree stratum differs from that of its core by twice the
total Chern number of the simple spheres minus twice the number of nodes, and two for each
special point lost to a coincidence. -/
theorem sphereTreeDimension_eq_sub (n I₀ : ℤ) (c : κ → ℤ) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n I₀ c parent node root =
      I₀ + 2 * ∑ v, c v - 2 * Fintype.card κ -
        2 * (2 * Fintype.card κ - ∑ x, (#(sphereTreeSpecialPoints parent node root x) : ℤ)) := by
  simp_rw [sphereTreeDimension, unmarkedVirtualDimension_def]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  push_cast
  ring

/-- The expected dimension of a sphere-tree stratum is at most that of its core, plus twice the
total Chern number of the simple spheres, minus twice the number of nodes. -/
theorem sphereTreeDimension_le (n I₀ : ℤ) (c : κ → ℤ) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n I₀ c parent node root ≤
      I₀ + 2 * ∑ v, c v - 2 * Fintype.card κ := by
  have h := sum_card_sphereTreeSpecialPoints_le parent node root
  rw [sphereTreeDimension_eq_sub]
  have : (∑ x, (#(sphereTreeSpecialPoints parent node root x) : ℤ)) ≤ 2 * Fintype.card κ := by
    exact_mod_cast h
  linarith

/-- When the special points of every component are distinct, the expected dimension of a
sphere-tree stratum is that of its core, plus twice the total Chern number of the simple spheres,
minus twice the number of nodes. -/
theorem sphereTreeDimension_eq {n I₀ : ℤ} {c : κ → ℤ} {parent : κ → Option κ}
    {node root : κ → P} (hnode : ∀ v w, parent v = parent w → node v = node w → v = w)
    (hroot : ∀ v w, parent w = some v → node w ≠ root v) :
    sphereTreeDimension n I₀ c parent node root = I₀ + 2 * ∑ v, c v - 2 * Fintype.card κ := by
  have h := sum_card_sphereTreeSpecialPoints_eq hnode hroot
  rw [sphereTreeDimension_eq_sub]
  have : (∑ x, (#(sphereTreeSpecialPoints parent node root x) : ℤ)) = 2 * Fintype.card κ := by
    exact_mod_cast h
  rw [this]
  ring

section Reduction

variable {G : Type*} [AddCommMonoid G] {ι : Type*} [Fintype ι]

/-- **The dimension count for sphere bubbles.** Let `ind A` be the expected dimension of a Floer
problem in class `A`, changing by `2 c₁(B)` when the class changes by `B`. Let a limit of class
`A₀ + ∑ v, B v` consist of a core of class `A₀` and nonconstant bubbles `v` of classes
`B v = m v • B' (ρ v)`, `m v`-fold covers of the simple spheres `ρ v`, every simple sphere being
the image of some bubble. If every simple sphere has Chern number at least `N`, the reduced
stratum has expected dimension at most `ind (A₀ + ∑ v, B v) - 2 #κ - 2 N (∑ v, m v - #κ)`. -/
theorem sphereTreeDimension_le_sub_of_le_chern {n N : ℤ} (c : G →+ ℤ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, N ≤ c (B' w))
    (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ≤
      ind (A₀ + ∑ v, B v) - 2 * Fintype.card κ -
        2 * N * (∑ v, (m v : ℤ) - Fintype.card κ) := by
  -- `M w` is the total covering multiplicity of the simple sphere `w` by the bubbles.
  set M : κ → ℤ := fun w => ∑ v with ρ v = w, (m v : ℤ) with hM
  have hcB : c (∑ v, B v) = ∑ w, M w * c (B' w) := by
    simp only [map_sum, hB, map_nsmul, nsmul_eq_mul, hM, sum_mul]
    rw [← sum_fiberwise univ ρ fun v => (m v : ℤ) * c (B' (ρ v))]
    refine sum_congr rfl fun w _ => sum_congr rfl fun v hv => ?_
    rw [(mem_filter.1 hv).2]
  have hsum : ∑ v, (m v : ℤ) = ∑ w, M w := (sum_fiberwise univ ρ _).symm
  have hM1 (w : κ) : 1 ≤ M w := by
    obtain ⟨v, rfl⟩ := hρ w
    calc (1 : ℤ) ≤ m v := by exact_mod_cast hm v
      _ ≤ M (ρ v) := single_le_sum (fun _ _ => Int.natCast_nonneg _) (by simp)
  have hexcess : N * ∑ w, (M w - 1) ≤ ∑ w, (M w - 1) * c (B' w) := by
    rw [mul_sum]
    exact sum_le_sum fun w _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hc w) (by linarith [hM1 w])
  have hdim := sphereTreeDimension_le n (ind A₀) (fun w => c (B' w)) parent node root
  simp only [sub_mul, one_mul, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    mul_one] at hexcess
  rw [hind, hcB, hsum]
  linarith

/-- On a target where every simple sphere has nonnegative first Chern number, for instance a
spherically `c₁`-zero target, the reduced stratum of a limit with sphere bubbles has expected
dimension at most `ind (A₀ + ∑ v, B v) - 2 #κ`, two less for each simple sphere. -/
theorem sphereTreeDimension_le_sub_two_mul_card {n : ℤ} (c : G →+ ℤ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ≤
      ind (A₀ + ∑ v, B v) - 2 * Fintype.card κ := by
  simpa using sphereTreeDimension_le_sub_of_le_chern c hind A₀ hB hm hρ hc parent node root
    (n := n)

/-- On a positively monotone target, `ω = τ c₁` with `τ > 0`, the simple spheres, which have
positive area, have first Chern number at least one, and the reduced stratum of a limit with sphere
bubbles has expected dimension at most `ind (A₀ + ∑ v, B v) - 2 ∑ v, m v`: two less for each
bubble, counted with its covering multiplicity. -/
theorem sphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern {n : ℤ} {τ : ℝ}
    (ω : G →+ ℝ) (c : G →+ ℤ) (hω : ∀ A, ω A = τ * c A) (hτ : 0 < τ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (harea : ∀ w, 0 < ω (B' w)) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ≤
      ind (A₀ + ∑ v, B v) - 2 * ∑ v, (m v : ℤ) := by
  have hc (w : κ) : 1 ≤ c (B' w) := by
    have h := harea w
    rw [hω] at h
    have : (0 : ℤ) < c (B' w) := by exact_mod_cast pos_of_mul_pos_right h hτ.le
    omega
  have := sphereTreeDimension_le_sub_of_le_chern c hind A₀ hB hm hρ hc parent node
    root (n := n)
  linarith

/-- On a target where every simple sphere has nonnegative first Chern number, a stratum with at
least one nonconstant sphere bubble has expected dimension at most two less than the unbubbled
problem. -/
theorem sphereTreeDimension_le_sub_two [Nonempty κ] {n : ℤ} (c : G →+ ℤ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ≤
      ind (A₀ + ∑ v, B v) - 2 := by
  have := sphereTreeDimension_le_sub_two_mul_card c hind A₀ hB hm hρ hc parent node root (n := n)
  have hκ : (1 : ℤ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  linarith

/-- **Exclusion of sphere bubbles in rigid and one-dimensional problems.** On a target where every
simple sphere has nonnegative first Chern number, such as a positively monotone or a spherically
`c₁`-zero target, if the unbubbled problem in class `A₀ + ∑ v, B v` has expected dimension at most
one, every reduced stratum with at least one nonconstant sphere bubble has negative expected
dimension. -/
theorem sphereTreeDimension_neg_of_le_one [Nonempty κ] {n : ℤ} (c : G →+ ℤ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (hA : ind (A₀ + ∑ v, B v) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root < 0 := by
  have := sphereTreeDimension_le_sub_two c hind A₀ hB hm hρ hc parent node root (n := n)
  linarith

end Reduction

end TauCeti.Floer
