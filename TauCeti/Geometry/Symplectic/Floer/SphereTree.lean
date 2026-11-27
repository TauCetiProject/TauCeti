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
import TauCeti.Algebra.BigOperators.Fin

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
at most two special points per node, with equality when the special points of each component
are distinct (`TauCeti.Floer.sum_card_sphereTreeSpecialPoints_le`,
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
* On a target with `ω = τ c₁` and `τ ≥ 0`, which is positively monotone because nonconstant
  spheres exist, a nonconstant pseudoholomorphic sphere has positive area, hence `c₁ ≥ 1`, and
  the stratum has expected dimension at most `ind A - 2 ∑_v m v`
  (`TauCeti.Floer.sphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern`).
* In both cases a stratum with at least one nonconstant bubble has expected dimension at most
  `ind A - 2` (`TauCeti.Floer.sphereTreeDimension_le_sub_two`), so it has negative expected
  dimension in the problems with `ind A ≤ 1`
  (`TauCeti.Floer.sphereTreeDimension_neg_of_le_one`): the rigid counts of the product and of the
  continuation maps, and the one-dimensional moduli spaces of pairs of pants and of continuation
  maps whose boundaries give their chain-level identities. Conversely, in these problems a stratum
  without bubbles has the expected dimension `ind A` of the core, so a stratum has nonnegative
  expected dimension exactly when it has no nonconstant bubble and `ind A ≥ 0`
  (`TauCeti.Floer.sphereTreeDimension_nonneg_iff`). Here `ind A` is the dimension before any
  quotient by translations of the core itself; translations of pieces of the core, such as the
  cylinders broken off a pair of pants below, may already be divided out in it.

**Translations and broken configurations.** A Floer cylinder of a time-independent cylindrical
datum is taken modulo the `ℝ`-translation of its domain, which lowers the expected dimension by
one. This includes a *stationary* cylinder `(s, t) ↦ x(t)` carrying sphere bubbles, as appears in
the limit when spheres bubble off at an orbit: its core has expected dimension `0`, and the
translation acts on the positions of the nodes on it. The quotient stratum of a cylinder problem
in class `A` with at least one bubble therefore has expected dimension at most `ind A - 3`, so it
is negative for `ind A ≤ 2` (`TauCeti.Floer.sphereTreeDimension_sub_one_neg_of_le_two`): the
rigid differential (`ind A = 1`) and the one-dimensional spaces behind `d² = 0` (`ind A = 2`).
For a single simple sphere of class `B` attached at a point of a stationary cylinder over `x` the
quotient stratum has expected dimension `2 c₁(B) - 3`, that of the simple spheres of class `B`
through the loop `x`.

A Gromov–Floer limit is in general a broken configuration: finitely many levels `ℓ`, such as a
pair of pants and chains of Floer cylinders at its ends, each carrying its own tree of spheres,
with the cylinder levels `ℓ ∈ T` taken modulo translation. The expected dimension of such a
stratum is the sum of those of the levels, minus `#T`
(`TauCeti.Floer.brokenSphereTreeDimension`). The expected indices `ind_ℓ` of the levels add up to
the index of the unbroken problem obtained by gluing them, so with the hypotheses above on every
level the stratum has expected dimension at most `∑_ℓ ind_ℓ (A ℓ) - #T - 2 #κ`, with `#κ` the total
number of simple spheres (`TauCeti.Floer.brokenSphereTreeDimension_le_sub_two_mul_card`; with the
covering multiplicities in the monotone case,
`TauCeti.Floer.brokenSphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern`). Without
bubbles it is exactly `∑_ℓ ind_ℓ (A ℓ) - #T` (`TauCeti.Floer.brokenSphereTreeDimension_of_isEmpty`).
Two consequences say which strata survive in the problems that define the product:

* a stratum with at least one nonconstant bubble has negative expected dimension as soon as
  `∑_ℓ ind_ℓ (A ℓ) ≤ #T + 1` (`TauCeti.Floer.brokenSphereTreeDimension_neg_of_le_card_add_one`);
* a stratum with more cylinder levels than its total index has negative expected dimension
  (`TauCeti.Floer.brokenSphereTreeDimension_neg_of_lt_card`).

So in the rigid problems (`∑_ℓ ind_ℓ (A ℓ) = 0`) only strata without cylinder levels and without
bubbles remain (`TauCeti.Floer.brokenSphereTreeDimension_neg_of_nonpos`), and in the
one-dimensional problems (`∑_ℓ ind_ℓ (A ℓ) = 1`) only strata without bubbles and with at most one
cylinder level (`TauCeti.Floer.brokenSphereTreeDimension_neg_of_le_one`); those with one cylinder
level have expected dimension `0`, and they are the ends of the one-dimensional moduli spaces.
Levels that are not taken modulo translation, such as continuation cylinders, pairs of pants and
planes, are the levels outside `T`.

**Broken limits of pairs of pants.** Besides bubbling, a sequence of pairs of pants can lose energy
along its three ends, where Floer cylinders break off. The core of such a limit is a broken pair of
pants: a pair of pants together with chains of Floer cylinders at its two inputs and at its output,
each cylinder taken modulo its `ℝ`-translation. The pieces meet at nondegenerate orbits, so the
expected dimension of the core is the sum of those of its pieces
(`TauCeti.Floer.brokenPantsDimension`, built from `TauCeti.Floer.cylinderChainDimension`). Unlike
the levels of `TauCeti.Floer.brokenSphereTreeDimension`, which each carry their own tree, its
spheres form one tree attached to any of the pieces, so its special points are points of all of
them. The gradings of the intermediate orbits telescope (`TauCeti.Floer.cylinderChainDimension_eq`):
the expected dimension of a broken pair of pants is the index `μ₁ + μ₂ - μ₀ - n + 2 c₁(A)` of the
unbroken problem in its total class `A`, minus the number `k` of cylinders that have broken off
(`TauCeti.Floer.brokenPantsDimension_eq`). The class of the limit is the sum of the classes of its
pieces, as for the sewing of cap classes (`TauCeti.Floer.productClass_comp_out`,
`TauCeti.Floer.productClass_comp_in`, `TauCeti.Floer.cylinderClass_comp`). With sphere trees
attached, the expected dimension of the stratum is at most `μ₁ + μ₂ - μ₀ - n + 2 c₁(A) - k - 2 #κ`
when `c₁` is nonnegative on simple spheres
(`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_le`). This states exactly which strata
of the product's rigid and one-dimensional problems have nonnegative expected dimension
(`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_nonneg_iff`): in a problem of expected
dimension `0`, only the unbroken pairs of pants without bubbles; in a problem of expected dimension
`1`, the unbroken pairs of pants and those with a single broken-off cylinder, all without bubbles.
The latter are the boundary of the one-dimensional moduli spaces that gives the Leibniz rule of the
product.

**One-parameter families.** The chain homotopies behind the identities of the product count
solutions over a one-parameter family of Floer problems: the homotopies comparing two choices of
auxiliary data or exchanging the inputs, which are families of pairs of pants, and the
associativity family of four-holed spheres. A limit over a face of dimension `p` of the parameter
space, `p = 1` at interior parameters and `p = 0` at an end point, has expected dimension that of
its configuration plus `p`. In a family whose unbubbled strata have expected dimension at most one,
a stratum therefore has nonnegative expected dimension exactly when it has no nonconstant bubble
and at most `ind + p` of its levels are taken modulo translation, `ind` being the total index of its
levels (`TauCeti.Floer.brokenSphereTreeDimension_add_nonneg_iff`), and likewise for a broken pair of
pants (`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_add_nonneg_iff`). A homotopy has
index `-1`: its rigid counts come from unbroken configurations at interior parameters, and its
one-dimensional spaces, of index `0`, end at a single broken-off cylinder at an interior parameter
or at an unbroken configuration at an end point.

The associativity family consists of four-holed spheres with three inputs and one output, whose
index is `μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A)`. A broken four-holed sphere has that index in its
total class minus the number of broken-off cylinders
(`TauCeti.Floer.brokenFourHoledSphereDimension_eq`). At its two long-neck ends the four-holed sphere
breaks into two pairs of pants, one glued into the first or the second input of the other, possibly
with cylinders broken off between them; their expected dimensions add up to the index of the
four-holed sphere minus the number of broken-off cylinders, because the grading of the capped
generator at which they meet cancels
(`TauCeti.Floer.brokenPantsDimension_add_brokenPantsDimension_fst`,
`TauCeti.Floer.brokenPantsDimension_add_brokenPantsDimension_snd`). Hence in the one-dimensional
problem of the family, of index `0`, the strata of nonnegative expected dimension are the unbroken
four-holed spheres and those with a single broken-off cylinder at interior parameters
(`TauCeti.Floer.sphereTreeDimension_brokenFourHoledSphereDimension_add_nonneg_iff`), and at the
two ends the two composites of unbroken pairs of pants meeting at a capped generator
(`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_add_brokenPantsDimension_fst_nonneg_iff`,
`TauCeti.Floer.sphereTreeDimension_brokenPantsDimension_add_brokenPantsDimension_snd_nonneg_iff`),
all without sphere bubbles.

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
  ext
  simp [sphereTreeSpecialPoints]

omit [DecidableEq P] in
/-- Counting the nodes once from the component each sphere is attached to and once from the sphere
itself gives two per sphere. -/
private theorem sum_card_filter_parent_add_card_root (parent : κ → Option κ) (root : κ → P) :
    ∑ x : Option κ, (#(univ.filter (parent · = x)) + #(x.map root).toFinset) =
      2 * Fintype.card κ := by
  rw [sum_add_distrib, ← card_eq_sum_card_fiberwise (by simp), Fintype.sum_option]
  simp [two_mul]

/-- Each node contributes at most two special points, one on each of the two components it
joins. -/
theorem sum_card_sphereTreeSpecialPoints_le (parent : κ → Option κ) (node root : κ → P) :
    ∑ x, #(sphereTreeSpecialPoints parent node root x) ≤ 2 * Fintype.card κ :=
  (sum_le_sum fun x _ => (card_union_le _ _).trans (by grw [card_image_le])).trans_eq
    (sum_card_filter_parent_add_card_root parent root)

/-- When the special points of each component of a tree of spheres are distinct, there are exactly
two special points per node. Distinctness means that the spheres attached to one component are
attached at distinct points, and never at the point at which that component is itself attached. -/
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
  exact sum_card_filter_parent_add_card_root parent root

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

/-- On a target with `ω = τ c₁` and `τ ≥ 0`, for instance a positively monotone one, the simple
spheres, which have positive area, have first Chern number at least one, and the reduced stratum
of a limit with sphere bubbles has expected dimension at most `ind (A₀ + ∑ v, B v) - 2 ∑ v, m v`:
two less for each bubble, counted with its covering multiplicity. -/
theorem sphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern {n : ℤ} {τ : ℝ}
    (ω : G → ℝ) (c : G →+ ℤ) (hω : ∀ A, ω A = τ * c A) (hτ : 0 ≤ τ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (harea : ∀ w, 0 < ω (B' w)) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ≤
      ind (A₀ + ∑ v, B v) - 2 * ∑ v, (m v : ℤ) := by
  have hc (w : κ) : 1 ≤ c (B' w) := by
    have h := harea w
    rw [hω] at h
    have : (0 : ℤ) < c (B' w) := by exact_mod_cast pos_of_mul_pos_right h hτ
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

/-- **Exclusion of sphere bubbles for cylinders modulo translation.** On a target where every
simple sphere has nonnegative first Chern number, if a cylinder problem in class
`A₀ + ∑ v, B v` has expected dimension at most two before the quotient by the `ℝ`-translation,
every reduced stratum with at least one nonconstant sphere bubble has negative expected dimension
after that quotient. The core may be a stationary cylinder, of class `A₀ = 0` and expected
dimension `ind 0 = 0`, on which the translation moves the nodes. -/
theorem sphereTreeDimension_sub_one_neg_of_le_two [Nonempty κ] {n : ℤ} (c : G →+ ℤ)
    {ind : G → ℤ} (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G}
    {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (hA : ind (A₀ + ∑ v, B v) ≤ 2)
    (parent : κ → Option κ) (node root : κ → P) :
    sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root - 1 < 0 := by
  have := sphereTreeDimension_le_sub_two c hind A₀ hB hm hρ hc parent node root (n := n)
  linarith

/-- **The strata of rigid and one-dimensional problems with nonnegative expected dimension.** On a
target where every simple sphere has nonnegative first Chern number, if the unbubbled problem in
class `A₀ + ∑ v, B v` has expected dimension at most one, a reduced stratum has nonnegative
expected dimension exactly when it has no nonconstant sphere bubble and the unbubbled problem has
nonnegative expected dimension. -/
theorem sphereTreeDimension_nonneg_iff {n : ℤ} (c : G →+ ℤ) {ind : G → ℤ}
    (hind : ∀ A B, ind (A + B) = ind A + 2 * c B) (A₀ : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (hA : ind (A₀ + ∑ v, B v) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (ind A₀) (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ 0 ≤ ind (A₀ + ∑ v, B v) := by
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
    -- Without simple spheres there are no bubbles, since every bubble covers a simple sphere.
    have : IsEmpty ι := Function.isEmpty ρ
    simp [hκ]
  | inr hκ =>
    have := sphereTreeDimension_neg_of_le_one c hind A₀ hB hm hρ hc hA parent node root (n := n)
    simp only [not_isEmpty_of_nonempty, false_and, iff_false, not_le]
    exact this

end Reduction

section Broken

/-! ### Broken configurations -/

variable {L : Type*} [Fintype L] {κ : L → Type*} [∀ ℓ, Fintype (κ ℓ)] [∀ ℓ, DecidableEq (κ ℓ)]
  {P : L → Type*} [∀ ℓ, DecidableEq (P ℓ)]

/-- The expected dimension of a stratum of broken configurations with sphere trees, in a target of
real dimension `2n`. The configuration has the levels `ℓ`, such as a pair of pants and the Floer
cylinders broken off at its ends; the level `ℓ` has a core of expected dimension `I ℓ` carrying
the tree of simple spheres `κ ℓ`, with Chern numbers `c ℓ`, attached along `parent ℓ` at the
points `node ℓ` and `root ℓ`. The levels in `T` are taken modulo the `ℝ`-translation of their
domains, as the Floer cylinders of time-independent cylindrical data are. The expected dimension
is the sum of the dimensions `TauCeti.Floer.sphereTreeDimension` of the levels, minus one for each
level in `T`. -/
def brokenSphereTreeDimension (n : ℤ) (I : L → ℤ) (c : ∀ ℓ, κ ℓ → ℤ)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) (T : Finset L) : ℤ :=
  ∑ ℓ, sphereTreeDimension n (I ℓ) (c ℓ) (parent ℓ) (node ℓ) (root ℓ) - #T

theorem brokenSphereTreeDimension_def (n : ℤ) (I : L → ℤ) (c : ∀ ℓ, κ ℓ → ℤ)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) (T : Finset L) :
    brokenSphereTreeDimension n I c parent node root T =
      ∑ ℓ, sphereTreeDimension n (I ℓ) (c ℓ) (parent ℓ) (node ℓ) (root ℓ) - #T := by
  rw [brokenSphereTreeDimension]

/-- Without bubbles, the stratum of broken configurations is the product of the moduli spaces of
its levels, with one translation divided out of each level in `T`. -/
@[simp]
theorem brokenSphereTreeDimension_of_isEmpty [∀ ℓ, IsEmpty (κ ℓ)] (n : ℤ) (I : L → ℤ)
    (c : ∀ ℓ, κ ℓ → ℤ) (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ)
    (T : Finset L) :
    brokenSphereTreeDimension n I c parent node root T = ∑ ℓ, I ℓ - #T := by
  simp [brokenSphereTreeDimension]

variable {G : Type*} [AddCommMonoid G] {ι : L → Type*} [∀ ℓ, Fintype (ι ℓ)]

/-- **The dimension count for broken configurations.** Let the level `ℓ` of a broken configuration
be a Floer problem whose expected dimension `ind ℓ A` changes by `2 c₁(B)` when its class `A`
changes by `B`. Let its limit consist of a core of class `A₀ ℓ` and nonconstant bubbles `v` of
classes `B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)`, covering the simple spheres `κ ℓ`, every simple sphere
being the image of some bubble. If every simple sphere has Chern number at least `N`, the stratum
has expected dimension at most `∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 #κ - 2 N (∑ m - #κ)`, where
`#κ` is the total number of simple spheres and `∑ m` the total covering multiplicity of the
bubbles. -/
theorem brokenSphereTreeDimension_le_sub_of_le_chern {n N : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, N ≤ c (B' ℓ w))
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) (T : Finset L) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
        T ≤
      ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 * ∑ ℓ, (Fintype.card (κ ℓ) : ℤ) -
        2 * N * (∑ ℓ, ∑ v, (m ℓ v : ℤ) - ∑ ℓ, (Fintype.card (κ ℓ) : ℤ)) := by
  have h := sum_le_sum fun ℓ (_ : ℓ ∈ univ) =>
    sphereTreeDimension_le_sub_of_le_chern (n := n) c (hind ℓ) (A₀ ℓ) (hB ℓ) (hm ℓ) (hρ ℓ)
      (hc ℓ) (parent ℓ) (node ℓ) (root ℓ)
  simp only [sum_sub_distrib, ← mul_sum] at h
  rw [brokenSphereTreeDimension]
  linarith

/-- On a target where every simple sphere has nonnegative first Chern number, the stratum of
broken configurations has expected dimension at most `∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 #κ`,
two less for each simple sphere of any level. -/
theorem brokenSphereTreeDimension_le_sub_two_mul_card {n : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w))
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) (T : Finset L) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
        T ≤
      ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 * ∑ ℓ, (Fintype.card (κ ℓ) : ℤ) := by
  simpa using brokenSphereTreeDimension_le_sub_of_le_chern c hind A₀ hB hm hρ hc parent node root
    T (n := n)

/-- On a target with `ω = τ c₁` and `τ ≥ 0`, for instance a positively monotone one, the stratum
of broken configurations has expected dimension at most
`∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 ∑ m`: two less for each bubble of any level, counted with
its covering multiplicity. -/
theorem brokenSphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern {n : ℤ} {τ : ℝ}
    (ω : G → ℝ) (c : G →+ ℤ) (hω : ∀ A, ω A = τ * c A) (hτ : 0 ≤ τ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (harea : ∀ ℓ w, 0 < ω (B' ℓ w))
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) (T : Finset L) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
        T ≤
      ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 * ∑ ℓ, ∑ v, (m ℓ v : ℤ) := by
  have h := sum_le_sum fun ℓ (_ : ℓ ∈ univ) =>
    sphereTreeDimension_le_sub_two_mul_sum_of_area_eq_mul_chern (n := n) ω c hω hτ (hind ℓ) (A₀ ℓ)
      (hB ℓ) (hm ℓ) (hρ ℓ) (harea ℓ) (parent ℓ) (node ℓ) (root ℓ)
  simp only [sum_sub_distrib, ← mul_sum] at h
  rw [brokenSphereTreeDimension]
  linarith

/-- On a target where every simple sphere has nonnegative first Chern number, a stratum of broken
configurations with at least one nonconstant sphere bubble has expected dimension at most
`∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2`. -/
theorem brokenSphereTreeDimension_le_sub_two {n : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w))
    (hκ : ∃ ℓ, Nonempty (κ ℓ)) (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ)
    (T : Finset L) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
        T ≤
      ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) - #T - 2 := by
  obtain ⟨ℓ₀, _⟩ := hκ
  have h := brokenSphereTreeDimension_le_sub_two_mul_card c hind A₀ hB hm hρ hc parent node root
    T (n := n)
  have hcard : (1 : ℤ) ≤ ∑ ℓ, (Fintype.card (κ ℓ) : ℤ) :=
    calc (1 : ℤ) ≤ Fintype.card (κ ℓ₀) := by exact_mod_cast Fintype.card_pos
      _ ≤ ∑ ℓ, (Fintype.card (κ ℓ) : ℤ) :=
        single_le_sum (fun _ _ => Int.natCast_nonneg _) (mem_univ ℓ₀)
  linarith

/-- **Exclusion of sphere bubbles in broken configurations.** On a target where every simple
sphere has nonnegative first Chern number, if the levels have total expected index at most
`#T + 1`, every stratum of broken configurations with at least one nonconstant sphere bubble has
negative expected dimension. -/
theorem brokenSphereTreeDimension_neg_of_le_card_add_one {n : ℤ} (c : G →+ ℤ)
    {ind : L → G → ℤ} (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G)
    {B : ∀ ℓ, ι ℓ → G} {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w))
    (hκ : ∃ ℓ, Nonempty (κ ℓ)) (T : Finset L)
    (hA : ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) ≤ #T + 1)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
      T < 0 := by
  have := brokenSphereTreeDimension_le_sub_two c hind A₀ hB hm hρ hc hκ parent node root T
    (n := n)
  linarith

/-- **Exclusion of multiply broken configurations.** On a target where every simple sphere has
nonnegative first Chern number, a stratum of broken configurations with more levels taken modulo
translation than the total expected index of its levels has negative expected dimension, with or
without bubbles. -/
theorem brokenSphereTreeDimension_neg_of_lt_card {n : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w)) (T : Finset L)
    (hA : ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) < #T)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
      T < 0 := by
  have h := brokenSphereTreeDimension_le_sub_two_mul_card c hind A₀ hB hm hρ hc parent node root
    T (n := n)
  have hcard : (0 : ℤ) ≤ ∑ ℓ, (Fintype.card (κ ℓ) : ℤ) := sum_nonneg fun _ _ => by positivity
  linarith

/-- **The strata of a rigid problem.** On a target where every simple sphere has nonnegative first
Chern number, if the levels have total expected index at most zero, as in the rigid counts of the
product and of the continuation maps, every stratum with a level taken modulo translation or with
a nonconstant sphere bubble has negative expected dimension. -/
theorem brokenSphereTreeDimension_neg_of_nonpos {n : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w)) (T : Finset L)
    (hT : T.Nonempty ∨ ∃ ℓ, Nonempty (κ ℓ)) (hA : ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) ≤ 0)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
      T < 0 := by
  rcases hT with hT | hκ
  · refine brokenSphereTreeDimension_neg_of_lt_card c hind A₀ hB hm hρ hc T ?_ parent node root
    have : (0 : ℤ) < #T := by exact_mod_cast hT.card_pos
    linarith
  · exact brokenSphereTreeDimension_neg_of_le_card_add_one c hind A₀ hB hm hρ hc hκ T
      (by linarith [Int.natCast_nonneg #T]) parent node root

/-- **The strata of a one-dimensional problem.** On a target where every simple sphere has
nonnegative first Chern number, if the levels have total expected index at most one, as in the
one-dimensional moduli spaces whose ends give the chain-level identities of the product and of the
continuation maps, every stratum with at least two levels taken modulo translation or with a
nonconstant sphere bubble has negative expected dimension. -/
theorem brokenSphereTreeDimension_neg_of_le_one {n : ℤ} (c : G →+ ℤ) {ind : L → G → ℤ}
    (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G) {B : ∀ ℓ, ι ℓ → G}
    {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w)) (T : Finset L)
    (hT : 2 ≤ #T ∨ ∃ ℓ, Nonempty (κ ℓ)) (hA : ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) ≤ 1)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) :
    brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node root
      T < 0 := by
  rcases hT with hT | hκ
  · refine brokenSphereTreeDimension_neg_of_lt_card c hind A₀ hB hm hρ hc T ?_ parent node root
    have : (2 : ℤ) ≤ #T := by exact_mod_cast hT
    linarith
  · exact brokenSphereTreeDimension_neg_of_le_card_add_one c hind A₀ hB hm hρ hc hκ T
      (by linarith [Int.natCast_nonneg #T]) parent node root

/-- **The strata of a family of broken configurations.** Let a family of Floer problems depend on
parameters, and consider its limits over a face of dimension `p` of the parameter space: the
interior of a one-parameter family has `p = 1`, its end points `p = 0`. Such a stratum of broken
configurations with sphere trees has expected dimension
`TauCeti.Floer.brokenSphereTreeDimension` plus `p`. On a target where every simple sphere has
nonnegative first Chern number, if the stratum without bubbles has expected dimension
`∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) + p - #T` at most one, the stratum has nonnegative expected
dimension exactly when it has no nonconstant sphere bubble and at most
`∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) + p` of its levels are taken modulo translation. -/
theorem brokenSphereTreeDimension_add_nonneg_iff {n : ℤ} (p : ℤ) (c : G →+ ℤ)
    {ind : L → G → ℤ} (hind : ∀ ℓ A B, ind ℓ (A + B) = ind ℓ A + 2 * c B) (A₀ : L → G)
    {B : ∀ ℓ, ι ℓ → G} {B' : ∀ ℓ, κ ℓ → G} {m : ∀ ℓ, ι ℓ → ℕ} {ρ : ∀ ℓ, ι ℓ → κ ℓ}
    (hB : ∀ ℓ v, B ℓ v = m ℓ v • B' ℓ (ρ ℓ v)) (hm : ∀ ℓ v, 0 < m ℓ v)
    (hρ : ∀ ℓ, Function.Surjective (ρ ℓ)) (hc : ∀ ℓ w, 0 ≤ c (B' ℓ w)) (T : Finset L)
    (hA : ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) + p - #T ≤ 1)
    (parent : ∀ ℓ, κ ℓ → Option (κ ℓ)) (node root : ∀ ℓ, κ ℓ → P ℓ) :
    0 ≤ brokenSphereTreeDimension n (fun ℓ => ind ℓ (A₀ ℓ)) (fun ℓ w => c (B' ℓ w)) parent node
        root T + p ↔
      (∀ ℓ, IsEmpty (κ ℓ)) ∧ (#T : ℤ) ≤ ∑ ℓ, ind ℓ (A₀ ℓ + ∑ v, B ℓ v) + p := by
  by_cases hκ : ∀ ℓ, IsEmpty (κ ℓ)
  · -- Without simple spheres there are no bubbles, since every bubble covers a simple sphere.
    have : ∀ ℓ, IsEmpty (ι ℓ) := fun ℓ => Function.isEmpty (ρ ℓ)
    simp only [brokenSphereTreeDimension_of_isEmpty, univ_eq_empty, sum_empty, add_zero, hκ,
      implies_true, true_and]
    constructor <;> intro h <;> linarith
  · obtain ⟨ℓ, hℓ⟩ := not_forall.1 hκ
    have := brokenSphereTreeDimension_le_sub_two c hind A₀ hB hm hρ hc
      ⟨ℓ, not_isEmpty_iff.1 hℓ⟩ parent node root T (n := n)
    simp only [hκ, false_and, iff_false, not_le]
    linarith

end Broken

/-! ### Broken limits of pairs of pants -/

section BrokenPants

variable {G : Type*} [AddCommMonoid G] {ι : Type*} [Fintype ι]

/-- The expected dimension of a chain of `k` Floer cylinders, each taken modulo its
`ℝ`-translation. The cylinder `j` runs from a capped orbit of grading `g j.castSucc` at its positive
end to a capped orbit of grading `g j.succ` at its negative end, in the class `C j` relative to the
two caps. Its index is `g j.castSucc - g j.succ + 2 c₁(C j)`, and the translation lowers its
dimension by one. -/
def cylinderChainDimension (c : G →+ ℤ) {k : ℕ} (g : Fin (k + 1) → ℤ) (C : Fin k → G) : ℤ :=
  ∑ j, (g j.castSucc - g j.succ + 2 * c (C j) - 1)

theorem cylinderChainDimension_def (c : G →+ ℤ) {k : ℕ} (g : Fin (k + 1) → ℤ) (C : Fin k → G) :
    cylinderChainDimension c g C = ∑ j, (g j.castSucc - g j.succ + 2 * c (C j) - 1) := by
  rw [cylinderChainDimension]

/-- The indices of the cylinders of a chain add up to the index of a single cylinder from the first
capped orbit to the last one, in the sum of their classes. So the expected dimension of the chain
is that index minus the number of cylinders. -/
theorem cylinderChainDimension_eq (c : G →+ ℤ) {k : ℕ} (g : Fin (k + 1) → ℤ) (C : Fin k → G) :
    cylinderChainDimension c g C = g 0 - g (Fin.last k) + 2 * c (∑ j, C j) - k := by
  rw [cylinderChainDimension, ← Fin.sum_univ_castSucc_sub_succ g]
  simp [sum_sub_distrib, sum_add_distrib, map_sum, mul_sum]

/-- The expected dimension of a broken limit of pairs of pants in a target of real dimension `2n`,
before bubbling. Its pair of pants has inputs at capped orbits of gradings `g₁ (last k₁)` and
`g₂ (last k₂)`, output at a capped orbit of grading `g₀ 0`, and class `A` relative to these caps,
so its index is `g₁ (last k₁) + g₂ (last k₂) - g₀ 0 - n + 2 c₁(A)`. At its first input a chain of
`k₁` Floer cylinders has broken off, running from the capped generator of grading `g₁ 0` to the
pair of pants (`TauCeti.Floer.cylinderChainDimension`), and likewise a chain of `k₂` cylinders at
its second input. At its output a chain of `k₀` cylinders runs from the pair of pants to the capped
generator of grading `g₀ (last k₀)`. The orbits at which the pieces meet are nondegenerate, hence
isolated, so matching the pieces there imposes no condition and the expected dimensions add. -/
def brokenPantsDimension (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (C₀ : Fin k₀ → G) (A : G) : ℤ :=
  g₁ (Fin.last k₁) + g₂ (Fin.last k₂) - g₀ 0 - n + 2 * c A + cylinderChainDimension c g₁ C₁ +
    cylinderChainDimension c g₂ C₂ + cylinderChainDimension c g₀ C₀

theorem brokenPantsDimension_def (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (C₀ : Fin k₀ → G) (A : G) :
    brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A =
      g₁ (Fin.last k₁) + g₂ (Fin.last k₂) - g₀ 0 - n + 2 * c A + cylinderChainDimension c g₁ C₁ +
        cylinderChainDimension c g₂ C₂ + cylinderChainDimension c g₀ C₀ := by
  rw [brokenPantsDimension]

/-- **The index of a broken pair of pants.** The expected dimension of a broken limit of pairs of
pants is the index `μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` of the unbroken problem between the capped
generators of gradings `μ₁ = g₁ 0`, `μ₂ = g₂ 0` and `μ₀ = g₀ (last k₀)`, in the total class
`A' = A + ∑ C₁ + ∑ C₂ + ∑ C₀`, minus one for each of the `k₁ + k₂ + k₀` cylinders that have broken
off. -/
theorem brokenPantsDimension_eq (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G)
    (C₀ : Fin k₀ → G) (A : G) :
    brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A =
      g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n + 2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j) -
        (k₁ + k₂ + k₀) := by
  rw [brokenPantsDimension, cylinderChainDimension_eq, cylinderChainDimension_eq,
    cylinderChainDimension_eq, map_add, map_add, map_add]
  ring

/-- **Sphere trees on broken pairs of pants.** On a target where every simple sphere has
nonnegative first Chern number, a stratum of limits of pairs of pants consisting of a broken pair of
pants with `k₁ + k₂ + k₀` cylinders broken off at its ends and a tree of simple spheres attached to
it has expected dimension at most `μ₁ + μ₂ - μ₀ - n + 2 c₁(A') - (k₁ + k₂ + k₀) - 2 #κ`, where `A'`
is the total class of the limit, including its bubbles: one less for each broken-off cylinder and
two less for each simple sphere. The points of `P` at which spheres are attached to the broken pair
of pants lie on any of its pieces. -/
theorem sphereTreeDimension_brokenPantsDimension_le (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ}
    (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (C₀ : Fin k₀ → G) (A : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ}
    {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w)) (parent : κ → Option κ)
    (node root : κ → P) :
    sphereTreeDimension n (brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A) (fun w => c (B' w))
        parent node root ≤
      g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
          2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + k₀) -
        2 * Fintype.card κ := by
  rw [brokenPantsDimension_eq]
  exact sphereTreeDimension_le_sub_two_mul_card c
    (ind := fun A' => g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n + 2 * c A' - (k₁ + k₂ + k₀))
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc parent node root

/-- **The strata of one-parameter families of pairs of pants.** Consider a family of pair-of-pants
problems, such as the homotopies that compare the products of two choices of auxiliary data or
exchange the inputs, and its limits over a face of dimension `p` of the parameter space: `p = 1`
in the interior of a one-parameter family and `p = 0` at its end points. The core of such a limit
is a broken pair of pants, whose expected dimension in the family is
`TauCeti.Floer.brokenPantsDimension` plus `p`. On a target where every simple sphere has
nonnegative first Chern number, if this is at most one, the stratum with a tree of simple spheres
attached has nonnegative expected dimension exactly when it has no nonconstant sphere bubble and
at most `μ₁ + μ₂ - μ₀ - n + 2 c₁(A') + p` cylinders have broken off, `A'` being the total class.
So the rigid counts of a homotopy, of index `-1`, come from unbroken pairs of pants at interior
parameters only; the one-dimensional spaces of index `0` meet the strata of a single broken-off
cylinder at interior parameters and of unbroken pairs of pants at the end points. -/
theorem sphereTreeDimension_brokenPantsDimension_add_nonneg_iff (n p : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ)
    (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₀ : Fin k₀ → G) (A : G) {B : ι → G} {B' : κ → G}
    {m : ι → ℕ} {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + k₀) + p ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A + p)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) + p := by
  rw [brokenPantsDimension_eq]
  refine (sphereTreeDimension_nonneg_iff c
    (ind := fun A' => g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n + 2 * c A' - (k₁ + k₂ + k₀) + p)
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc hA parent node root).trans ?_
  exact and_congr_right fun _ => by constructor <;> intro h <;> linarith

/-- **The strata of the product's rigid and one-dimensional problems.** On a target where every
simple sphere has nonnegative first Chern number, consider the limits of pairs of pants between
capped generators of gradings `μ₁ = g₁ 0`, `μ₂ = g₂ 0` and `μ₀ = g₀ (last k₀)`, in a total class
`A'` for which the stratum of broken pairs of pants with `k₁ + k₂ + k₀` broken-off cylinders has
expected dimension at most one. For instance, the problem has expected dimension
`μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` at most one, as for the rigid products and for the one-dimensional
moduli spaces behind the Leibniz rule. Such a stratum with a tree of simple spheres attached has
nonnegative expected dimension exactly when it has no nonconstant sphere bubble and at most
`μ₁ + μ₂ - μ₀ - n + 2 c₁(A')` cylinders have broken off. So in a problem of expected dimension
zero only the unbroken pairs of pants remain, and in a problem of expected dimension one the
unbroken ones and those with a single broken-off cylinder. -/
theorem sphereTreeDimension_brokenPantsDimension_nonneg_iff (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₀ : ℕ}
    (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (C₀ : Fin k₀ → G) (A : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ}
    {ρ : ι → κ} (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v)
    (hρ : Function.Surjective ρ) (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (brokenPantsDimension n c g₁ g₂ g₀ C₁ C₂ C₀ A) (fun w => c (B' w))
        parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 - g₀ (Fin.last k₀) - n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₀ j + ∑ v, B v) := by
  simpa only [add_zero] using sphereTreeDimension_brokenPantsDimension_add_nonneg_iff n 0 c g₁ g₂
    g₀ C₁ C₂ C₀ A hB hm hρ hc (by simpa only [add_zero] using hA) parent node root

end BrokenPants

/-! ### The associativity family -/

section Associativity

variable {G : Type*} [AddCommMonoid G] {ι : Type*} [Fintype ι]

/-- The expected dimension of a broken limit of four-holed spheres with three inputs and one
output, in a target of real dimension `2n`, before bubbling. Its four-holed sphere has inputs at
capped orbits of gradings `g₁ (last k₁)`, `g₂ (last k₂)` and `g₃ (last k₃)`, output at a capped
orbit of grading `g₀ 0`, and class `A` relative to these caps, so its index is
`g₁ (last k₁) + g₂ (last k₂) + g₃ (last k₃) - g₀ 0 - 2n + 2 c₁(A)`. As for
`TauCeti.Floer.brokenPantsDimension`, at each input `i` a chain of `kᵢ` Floer cylinders
(`TauCeti.Floer.cylinderChainDimension`) runs from the capped generator of grading `gᵢ 0` to the
four-holed sphere, and at its output a chain of `k₀` cylinders runs from the four-holed sphere to
the capped generator of grading `g₀ (last k₀)`. -/
def brokenFourHoledSphereDimension (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ)
    (g₂ : Fin (k₂ + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G) (C₀ : Fin k₀ → G) (A : G) : ℤ :=
  g₁ (Fin.last k₁) + g₂ (Fin.last k₂) + g₃ (Fin.last k₃) - g₀ 0 - 2 * n + 2 * c A +
    cylinderChainDimension c g₁ C₁ + cylinderChainDimension c g₂ C₂ +
      cylinderChainDimension c g₃ C₃ + cylinderChainDimension c g₀ C₀

theorem brokenFourHoledSphereDimension_def (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₃ k₀ : ℕ}
    (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G)
    (C₀ : Fin k₀ → G) (A : G) :
    brokenFourHoledSphereDimension n c g₁ g₂ g₃ g₀ C₁ C₂ C₃ C₀ A =
      g₁ (Fin.last k₁) + g₂ (Fin.last k₂) + g₃ (Fin.last k₃) - g₀ 0 - 2 * n + 2 * c A +
        cylinderChainDimension c g₁ C₁ + cylinderChainDimension c g₂ C₂ +
          cylinderChainDimension c g₃ C₃ + cylinderChainDimension c g₀ C₀ := by
  rw [brokenFourHoledSphereDimension]

/-- **The index of a broken four-holed sphere.** The expected dimension of a broken limit of
four-holed spheres is the index `μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A')` of the unbroken problem between
the capped generators of gradings `μᵢ = gᵢ 0` and `μ₀ = g₀ (last k₀)`, in the total class
`A' = A + ∑ C₁ + ∑ C₂ + ∑ C₃ + ∑ C₀`, minus one for each of the `k₁ + k₂ + k₃ + k₀` cylinders that
have broken off. -/
theorem brokenFourHoledSphereDimension_eq (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k₃ k₀ : ℕ}
    (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G)
    (C₀ : Fin k₀ → G) (A : G) :
    brokenFourHoledSphereDimension n c g₁ g₂ g₃ g₀ C₁ C₂ C₃ C₀ A =
      g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
          2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, C₀ j) -
        (k₁ + k₂ + k₃ + k₀) := by
  rw [brokenFourHoledSphereDimension, cylinderChainDimension_eq, cylinderChainDimension_eq,
    cylinderChainDimension_eq, cylinderChainDimension_eq]
  simp only [map_add]
  ring

/-- **The strata of the associativity family at interior parameters.** On a target where every
simple sphere has nonnegative first Chern number, consider the limits of the one-parameter family
of four-holed spheres joining the two ways of composing two pairs of pants, over a face of
dimension `p` of its parameter space. Their core is a broken four-holed sphere, of expected
dimension `TauCeti.Floer.brokenFourHoledSphereDimension` plus `p`. If this is at most one, the
stratum with a tree of simple spheres attached has nonnegative expected dimension exactly when it
has no nonconstant sphere bubble and at most `μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A') + p` cylinders
have broken off, `A'` being the total class. So in the one-dimensional problem, of index `0`, the
strata at interior parameters (`p = 1`) are the unbroken four-holed spheres and those with a single
Floer cylinder broken off at one of the four ends, the faces at which a differential of one of the
complexes appears. -/
theorem sphereTreeDimension_brokenFourHoledSphereDimension_add_nonneg_iff (n p : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G)
    (C₀ : Fin k₀ → G) (A : G) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, C₀ j + ∑ v, B v) -
          (k₁ + k₂ + k₃ + k₀) + p ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n (brokenFourHoledSphereDimension n c g₁ g₂ g₃ g₀ C₁ C₂ C₃ C₀ A + p)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k₃ + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, C₀ j + ∑ v, B v) + p := by
  rw [brokenFourHoledSphereDimension_eq]
  refine (sphereTreeDimension_nonneg_iff c
    (ind := fun A' => g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n + 2 * c A' -
      (k₁ + k₂ + k₃ + k₀) + p)
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc hA parent node root).trans ?_
  exact and_congr_right fun _ => by constructor <;> intro h <;> linarith

/-- **The long-neck end of the associativity family composing the first two inputs.** At this
end the four-holed sphere breaks into a broken pair of pants `P` with inputs `x₁`, `x₂` and a
broken pair of pants `Q` whose first input receives the output of `P`, with a chain of cylinders
broken off between them: the output chain `h` of `P` ends at the capped generator at which the
first input chain `h'` of `Q` starts. The expected dimensions of `P` and `Q` add up to the index
`μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A')` of the four-holed sphere between the outer capped generators,
in the total class `A'`, minus the number of cylinders that have broken off, including those
between `P` and `Q`. -/
theorem brokenPantsDimension_add_brokenPantsDimension_fst (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k k' k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (h : Fin (k + 1) → ℤ)
    (h' : Fin (k' + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (D : Fin k → G) (D' : Fin k' → G) (C₃ : Fin k₃ → G) (C₀ : Fin k₀ → G)
    (A₁ A₂ : G) (hh : h (Fin.last k) = h' 0) :
    brokenPantsDimension n c g₁ g₂ h C₁ C₂ D A₁ + brokenPantsDimension n c h' g₃ g₀ D' C₃ C₀ A₂ =
      g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
          2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₃ j +
            ∑ j, C₀ j) -
        (k₁ + k₂ + k + k' + k₃ + k₀) := by
  rw [brokenPantsDimension_eq, brokenPantsDimension_eq, hh]
  simp only [map_add]
  ring

/-- **The long-neck end of the associativity family composing the last two inputs.** At this end
the four-holed sphere breaks into a broken pair of pants `P` with inputs `x₂`, `x₃` and a broken
pair of pants `Q` whose second input receives the output of `P`, with a chain of cylinders broken
off between them: the output chain `h` of `P` ends at the capped generator at which the second
input chain `h'` of `Q` starts. The expected dimensions of `P` and `Q` add up to the index
`μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A')` of the four-holed sphere between the outer capped generators,
in the total class `A'`, minus the number of cylinders that have broken off, including those
between `P` and `Q`. -/
theorem brokenPantsDimension_add_brokenPantsDimension_snd (n : ℤ) (c : G →+ ℤ)
    {k₁ k₂ k k' k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ)
    (h : Fin (k + 1) → ℤ) (h' : Fin (k' + 1) → ℤ) (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G)
    (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G) (D : Fin k → G) (D' : Fin k' → G) (C₀ : Fin k₀ → G)
    (A₁ A₂ : G) (hh : h (Fin.last k) = h' 0) :
    brokenPantsDimension n c g₂ g₃ h C₂ C₃ D A₁ + brokenPantsDimension n c g₁ h' g₀ C₁ D' C₀ A₂ =
      g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
          2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, D j + ∑ j, D' j +
            ∑ j, C₀ j) -
        (k₁ + k₂ + k₃ + k + k' + k₀) := by
  rw [brokenPantsDimension_eq, brokenPantsDimension_eq, hh]
  simp only [map_add]
  ring

/-- **The strata at the long-neck end composing the first two inputs.** On a target where every
simple sphere has nonnegative first Chern number, consider the limits of the associativity family
at its end composing the first two inputs: a broken pair of pants `P` glued into the first input of
a broken pair of pants `Q`, as in
`TauCeti.Floer.brokenPantsDimension_add_brokenPantsDimension_fst`, with a tree of simple spheres
attached. The end point is a face of dimension zero of the parameter space, so the expected
dimension of the core is the sum of those of `P` and `Q`. If this is at most one, the stratum has
nonnegative expected dimension exactly when it has no nonconstant sphere bubble and at most
`μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A')` cylinders have broken off. In the one-dimensional problem, of
index `0`, the only such strata are two unbroken pairs of pants meeting at a capped generator:
the composite product. -/
theorem sphereTreeDimension_brokenPantsDimension_add_brokenPantsDimension_fst_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k k' k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ)
    (h : Fin (k + 1) → ℤ) (h' : Fin (k' + 1) → ℤ) (g₃ : Fin (k₃ + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (D : Fin k → G)
    (D' : Fin k' → G) (C₃ : Fin k₃ → G) (C₀ : Fin k₀ → G) (A₁ A₂ : G)
    (hh : h (Fin.last k) = h' 0) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₃ j +
          ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + k + k' + k₃ + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (brokenPantsDimension n c g₁ g₂ h C₁ C₂ D A₁ +
          brokenPantsDimension n c h' g₃ g₀ D' C₃ C₀ A₂)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k + k' + k₃ + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, D j + ∑ j, D' j + ∑ j, C₃ j +
          ∑ j, C₀ j + ∑ v, B v) := by
  rw [brokenPantsDimension_add_brokenPantsDimension_fst n c g₁ g₂ h h' g₃ g₀ C₁ C₂ D D' C₃ C₀
    A₁ A₂ hh]
  refine (sphereTreeDimension_nonneg_iff c
    (ind := fun A' => g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n + 2 * c A' -
      (k₁ + k₂ + k + k' + k₃ + k₀))
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc hA parent node root).trans ?_
  exact and_congr_right fun _ => sub_nonneg

/-- **The strata at the long-neck end composing the last two inputs.** On a target where every
simple sphere has nonnegative first Chern number, consider the limits of the associativity family
at its end composing the last two inputs: a broken pair of pants `P` glued into the second input of
a broken pair of pants `Q`, as in
`TauCeti.Floer.brokenPantsDimension_add_brokenPantsDimension_snd`, with a tree of simple spheres
attached. If the expected dimension of the core is at most one, the stratum has nonnegative
expected dimension exactly when it has no nonconstant sphere bubble and at most
`μ₁ + μ₂ + μ₃ - μ₀ - 2n + 2 c₁(A')` cylinders have broken off. In the one-dimensional problem, of
index `0`, the only such strata are two unbroken pairs of pants meeting at a capped generator:
the composite product. -/
theorem sphereTreeDimension_brokenPantsDimension_add_brokenPantsDimension_snd_nonneg_iff
    (n : ℤ) (c : G →+ ℤ) {k₁ k₂ k k' k₃ k₀ : ℕ} (g₁ : Fin (k₁ + 1) → ℤ) (g₂ : Fin (k₂ + 1) → ℤ)
    (g₃ : Fin (k₃ + 1) → ℤ) (h : Fin (k + 1) → ℤ) (h' : Fin (k' + 1) → ℤ)
    (g₀ : Fin (k₀ + 1) → ℤ) (C₁ : Fin k₁ → G) (C₂ : Fin k₂ → G) (C₃ : Fin k₃ → G)
    (D : Fin k → G) (D' : Fin k' → G) (C₀ : Fin k₀ → G) (A₁ A₂ : G)
    (hh : h (Fin.last k) = h' 0) {B : ι → G} {B' : κ → G} {m : ι → ℕ} {ρ : ι → κ}
    (hB : ∀ v, B v = m v • B' (ρ v)) (hm : ∀ v, 0 < m v) (hρ : Function.Surjective ρ)
    (hc : ∀ w, 0 ≤ c (B' w))
    (hA : g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, D j + ∑ j, D' j +
          ∑ j, C₀ j + ∑ v, B v) - (k₁ + k₂ + k₃ + k + k' + k₀) ≤ 1)
    (parent : κ → Option κ) (node root : κ → P) :
    0 ≤ sphereTreeDimension n
        (brokenPantsDimension n c g₂ g₃ h C₂ C₃ D A₁ +
          brokenPantsDimension n c g₁ h' g₀ C₁ D' C₀ A₂)
        (fun w => c (B' w)) parent node root ↔
      IsEmpty κ ∧ (k₁ + k₂ + k₃ + k + k' + k₀ : ℤ) ≤ g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n +
        2 * c (A₁ + A₂ + ∑ j, C₁ j + ∑ j, C₂ j + ∑ j, C₃ j + ∑ j, D j + ∑ j, D' j +
          ∑ j, C₀ j + ∑ v, B v) := by
  rw [brokenPantsDimension_add_brokenPantsDimension_snd n c g₁ g₂ g₃ h h' g₀ C₁ C₂ C₃ D D' C₀
    A₁ A₂ hh]
  refine (sphereTreeDimension_nonneg_iff c
    (ind := fun A' => g₁ 0 + g₂ 0 + g₃ 0 - g₀ (Fin.last k₀) - 2 * n + 2 * c A' -
      (k₁ + k₂ + k₃ + k + k' + k₀))
    (fun _ _ => by rw [map_add]; ring) _ hB hm hρ hc hA parent node root).trans ?_
  exact and_congr_right fun _ => sub_nonneg

end Associativity

end TauCeti.Floer
