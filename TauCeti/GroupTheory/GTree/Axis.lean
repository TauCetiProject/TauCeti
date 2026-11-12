/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.FixedPoint
public import TauCeti.GroupTheory.GTree.Line
public import TauCeti.Combinatorics.Graph.Serre.GeodesicLine
public import TauCeti.Algebra.Group.Action.Pow

/-!
# The axis of a hyperbolic automorphism of a tree

Let `g` act on a tree without inversions, with translation length `ℓ(g) = min_v d(v, g v)`. The
*characteristic set* `GTree.axis g` consists of the vertices moved by exactly `ℓ(g)`. For an
elliptic element it is the set of fixed vertices. For a hyperbolic element it is the *axis*: a
geodesic line `c : ℤ → V`, with `d(c m, c n) = |m - n|`, on which `g` acts as the translation
`g • c n = c (n + ℓ(g))`. The axis is the only geodesic line invariant under `g`, it is contained
in every nonempty convex set of vertices invariant under `g`, and every vertex `v` satisfies
`d(v, g v) = ℓ(g) + 2 d(v, axis)`.

The argument follows Serre. At a vertex `x` moved by `ℓ(g)`, the geodesic from `x` to `g • x`
cannot be followed by its translate with backtracking: otherwise `g` would either invert an edge
or move the second vertex of the geodesic by `ℓ(g) - 2`. Hence, when `ℓ(g) > 0`, the translates
of this geodesic by the powers of `g` line up into a geodesic line. Conversely, let `C` be a
convex invariant set and `a` a vertex of `C` nearest to `v`, and suppose that `C` contains the
vertices fixed by `g` in case `g` fixes `a`. Then the geodesic from `v` to `a`, the geodesic from
`a` to `g • a` and the translate of the first one, reversed, form a geodesic from `v` to `g • v`,
so that `d(v, g v) = d(a, g a) + 2 d(v, a)`.

Consequently `ℓ(gⁿ) = |n| ℓ(g)`, so that `gⁿ` is hyperbolic exactly when `g` is and `n ≠ 0`, and a
nonzero power of a hyperbolic element has the same axis.

## Main declarations

* `TauCeti.GTree.axis`: the characteristic set of an element, its axis when it is hyperbolic.
* `TauCeti.GTree.smul_ne_rev_of_mem_axis`, `TauCeti.GTree.mem_axis_of_isReduced`: a vertex `x`
  lies in the characteristic set exactly when the geodesic from `x` to `g • x` is followed by its
  translate without backtracking.
* `TauCeti.GTree.dist_pow_smul_of_mem_axis`, `TauCeti.GTree.dist_zpow_smul_of_mem_axis`:
  `d(x, gⁿ x) = |n| ℓ(g)` on the characteristic set.
* `TauCeti.GTree.dist_smul_eq_dist_smul_add_two_mul_dist`: the displacement of a vertex in terms
  of its nearest vertex `a` in a convex invariant set `C`, provided that `C` contains the vertices
  fixed by `g` in case `g` fixes `a`.
* `TauCeti.GTree.IsHyperbolic.exists_range_eq_axis`: the axis of a hyperbolic element is a
  geodesic line translated by the translation length.
* `TauCeti.GTree.IsHyperbolic.axis_subset`, `TauCeti.GTree.IsHyperbolic.range_eq_axis`: the axis
  lies in every nonempty convex invariant set, and it is the unique invariant geodesic line.
* `TauCeti.GTree.axis_eq_range_of_smul_eq_add`, `TauCeti.GTree.isHyperbolic_of_smul_eq_add`: a
  geodesic line translated by `g` by a nonzero amount `t` is the axis of `g`, which is then
  hyperbolic; `TauCeti.GTree.translationLength_eq_natAbs_of_smul_eq_add`: `ℓ(g) = |t|` for every
  amount `t`.
* `TauCeti.GTree.dist_smul_eq_translationLength_add`: `d(v, g v) = ℓ(g) + 2 d(v, axis)`.
* `TauCeti.GTree.translationLength_zpow`, `TauCeti.GTree.isHyperbolic_zpow_iff`,
  `TauCeti.GTree.IsHyperbolic.axis_zpow`: `ℓ(gⁿ) = |n| ℓ(g)`, `gⁿ` is hyperbolic exactly when `g`
  is and `n ≠ 0`, and `gⁿ` then has the axis of `g`.
* `TauCeti.GTree.line_axis`: on the line, every vertex lies on the axis of every translation.

## References

* J.-P. Serre, *Trees*, Chapter I, §6.4, Propositions 24 and 25.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1 and
  the appendix.
-/

public section

universe u v w

namespace TauCeti
namespace GTree

open SerreGraph _root_.MulAction Pointwise

variable {G : Type w} [Group G] {T : GTree.{u, v} G}

/-! ### The characteristic set -/

variable (T) in
/-- The characteristic set of an element `g`: the vertices moved by exactly the translation
length of `g`. It is the set of fixed vertices of an elliptic element and the axis of a
hyperbolic element. -/
def axis (g : G) : Set T.V :=
  {v | T.dist v (g • v) = T.translationLength g}

theorem mem_axis_iff {g : G} {v : T.V} :
    v ∈ T.axis g ↔ T.dist v (g • v) = T.translationLength g := Iff.rfl

variable (T) in
/-- Some vertex is moved by exactly the translation length. -/
@[simp] theorem axis_nonempty (g : G) : (T.axis g).Nonempty :=
  exists_dist_eq_translationLength g

/-- The characteristic set of an element, as a type, is nonempty. -/
instance (g : G) : Nonempty (T.axis g) :=
  (T.axis_nonempty g).to_subtype

variable (T) in
/-- Every vertex lies in the characteristic set of the identity. -/
@[simp] theorem axis_one : T.axis (1 : G) = Set.univ :=
  Set.eq_univ_of_forall fun v => by rw [mem_axis_iff, one_smul, dist_self, translationLength_one]

variable (T) in
/-- In a tree with at most one vertex, the characteristic set of every element is everything. -/
@[simp] theorem axis_eq_univ_of_subsingleton [Subsingleton T.V] (g : G) : T.axis g = Set.univ :=
  (T.axis_nonempty g).eq_univ

/-- The characteristic set of `g` is invariant under `g`. -/
@[simp] theorem smul_mem_axis_iff {g : G} {v : T.V} : g • v ∈ T.axis g ↔ v ∈ T.axis g := by
  rw [mem_axis_iff, mem_axis_iff, dist_smul]

/-- The characteristic set of `g` is invariant under every element commuting with `g`. -/
theorem smul_mem_axis_iff_of_commute {g h : G} (hgh : Commute g h) {v : T.V} :
    h • v ∈ T.axis g ↔ v ∈ T.axis g := by
  rw [mem_axis_iff, mem_axis_iff, ← mul_smul, hgh.eq, mul_smul, dist_smul]

/-- The characteristic set of `g` is invariant under `g⁻¹`. -/
@[simp] theorem inv_smul_mem_axis_iff {g : G} {v : T.V} : g⁻¹ • v ∈ T.axis g ↔ v ∈ T.axis g :=
  smul_mem_axis_iff_of_commute (Commute.refl g).inv_right

/-- The characteristic set of `g` is invariant under the powers of `g`. -/
@[simp] theorem pow_smul_mem_axis_iff {g : G} (n : ℕ) {v : T.V} :
    g ^ n • v ∈ T.axis g ↔ v ∈ T.axis g :=
  smul_mem_axis_iff_of_commute (Commute.self_pow g n)

/-- The characteristic set of `g` is invariant under the integer powers of `g`. -/
@[simp] theorem zpow_smul_mem_axis_iff {g : G} (n : ℤ) {v : T.V} :
    g ^ n • v ∈ T.axis g ↔ v ∈ T.axis g :=
  smul_mem_axis_iff_of_commute (Commute.self_zpow g n)

/-- An element and its inverse have the same characteristic set. -/
@[simp] theorem axis_inv (g : G) : T.axis g⁻¹ = T.axis g := by
  ext v
  rw [mem_axis_iff, mem_axis_iff, translationLength_inv, ← T.dist_smul g v, smul_inv_smul,
    dist_comm]

/-- The characteristic set of a conjugate `h * g * h⁻¹` is the translate by `h` of the
characteristic set of `g`. -/
theorem mem_axis_conj_iff {g h : G} {v : T.V} : v ∈ T.axis (h * g * h⁻¹) ↔ h⁻¹ • v ∈ T.axis g := by
  rw [mem_axis_iff, mem_axis_iff, translationLength_conj, ← T.dist_smul h (h⁻¹ • v),
    smul_inv_smul, mul_smul, mul_smul]

variable (T) in
/-- The translate by `h` of the characteristic set of `g` is the characteristic set of the
conjugate `h * g * h⁻¹`. -/
theorem smul_axis (g h : G) : h • T.axis g = T.axis (h * g * h⁻¹) := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_axis_conj_iff]

/-- A fixed vertex lies in the characteristic set. -/
theorem mem_axis_of_smul_eq {g : G} {v : T.V} (hv : g • v = v) : v ∈ T.axis g := by
  rw [mem_axis_iff, hv, dist_self, eq_comm, translationLength_eq_zero_iff]
  exact isElliptic_iff.mpr ⟨v, hv⟩

/-- The characteristic set of an elliptic element is its set of fixed vertices. -/
theorem IsElliptic.axis_eq_fixedBy {g : G} (hg : T.IsElliptic g) : T.axis g = fixedBy T.V g := by
  ext v
  rw [mem_axis_iff, translationLength_eq_zero_iff.mpr hg, dist_eq_zero_iff (T.nonempty_path _ _),
    mem_fixedBy, eq_comm]

/-! ### Powers of an element along its characteristic set -/

/-- At a vertex `x` moved by the translation length, the reduced path from `x` to `g • x` is
followed by its translate under `g` without backtracking. -/
theorem smul_ne_rev_of_mem_axis {g : G} {x : T.V} (hx : x ∈ T.axis g) {p : T.Path x (g • x)}
    (hp : Path.IsReduced T.toSerreGraph p) :
    ∀ e ∈ (Path.darts T.toSerreGraph p).getLast?,
      ∀ f ∈ (Path.darts T.toSerreGraph p).head?, g • f ≠ T.rev e := by
  intro e he f hf hfe
  have hlen : p.length = T.translationLength g := by
    rw [← mem_axis_iff.mp hx, (IsTree.isAcyclic _ T.isTree).dist_eq_length hp]
  rcases Nat.lt_or_ge p.length 2 with h | h
  · -- A path with one dart: `g` would invert it.
    obtain ⟨a, ha⟩ : ∃ a, Path.darts T.toSerreGraph p = [a] := by
      rw [← List.length_eq_one_iff, Path.length_darts]
      have : p.length ≠ 0 := fun h0 => by
        rw [← Path.length_darts, List.length_eq_zero_iff] at h0
        simp [h0] at he
      omega
    simp only [ha, List.getLast?_singleton, List.head?_cons, Option.mem_def,
      Option.some.injEq] at he hf
    subst he hf
    exact T.smul_ne_rev g _ hfe
  · -- Otherwise `g` moves the second vertex of the path by two less than the translation length.
    have h₁ := Path.dist_tgt_src_add_two_le p hf he h
    have h₂ := translationLength_le g (T.tgt f)
    rw [← tgt_smul, hfe, tgt_rev] at h₂
    omega

/-- A vertex `x` moved by the translation length satisfies `d(x, gⁿ x) = n ℓ(g)`. -/
theorem dist_pow_smul_of_mem_axis {g : G} {x : T.V} (hx : x ∈ T.axis g) (n : ℕ) :
    T.dist x (g ^ n • x) = n * T.translationLength g := by
  obtain ⟨p, hp, -⟩ := T.isTree.existsUnique_isReduced x (g • x)
  rw [dist_pow_smul_eq_mul hp (smul_ne_rev_of_mem_axis hx hp) n, mem_axis_iff.mp hx]

/-- A vertex `x` moved by the translation length satisfies `d(x, gⁿ x) = |n| ℓ(g)` for every
integer `n`. -/
theorem dist_zpow_smul_of_mem_axis {g : G} {x : T.V} (hx : x ∈ T.axis g) (n : ℤ) :
    T.dist x (g ^ n • x) = n.natAbs * T.translationLength g := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, Int.natAbs_natCast, dist_pow_smul_of_mem_axis hx]
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← T.dist_smul (g ^ k),
      smul_inv_smul, dist_comm, dist_pow_smul_of_mem_axis hx]

/-- If a reduced path from `x` to `g • x` is followed by its translate under `g` without
backtracking, then `x` is moved by the translation length of `g`. -/
theorem mem_axis_of_isReduced {g : G} {x : T.V} {p : T.Path x (g • x)}
    (hp : Path.IsReduced T.toSerreGraph p) (hg : ∀ e ∈ (Path.darts T.toSerreGraph p).getLast?,
      ∀ f ∈ (Path.darts T.toSerreGraph p).head?, g • f ≠ T.rev e) : x ∈ T.axis g :=
  dist_smul_eq_translationLength_of_isReduced hp hg

/-! ### Displacement and the nearest vertex of a convex invariant set -/

/-- Let `q` be a path from `v` to `a` and `p` a path from `a` to `g • a` such that `q` followed by
`p` is reduced and does not end with the translate under `g` of the last dart of `q`. Then
`d(v, g v) = 2 |q| + |p|`. -/
private theorem dist_smul_eq_of_isReduced_comp {g : G} {v a : T.V} {q : T.Path v a}
    {p : T.Path a (g • a)} (hqp : Path.IsReduced T.toSerreGraph (q.comp p))
    (h : ∀ e ∈ (Path.darts T.toSerreGraph (q.comp p)).getLast?,
      ∀ f ∈ (Path.darts T.toSerreGraph q).getLast?, g • f ≠ e) :
    T.dist v (g • v) = 2 * q.length + p.length := by
  -- `q`, then `p`, then the translate of `q` reversed, is a reduced path from `v` to `g • v`.
  have hred : Path.IsReduced T.toSerreGraph ((q.comp p).comp (smulPath g q).reverse) := by
    refine (Path.isReduced_comp_iff _ _ _).mpr ⟨hqp, (Path.isReduced_reverse _ _).mpr
      ((isReduced_smulPath g q).mpr (hqp.of_comp_left T.toSerreGraph)), fun e he f hf => ?_⟩
    simp only [Path.darts_reverse, darts_smulPath, List.head?_map, List.head?_reverse,
      List.getLast?_map, Option.map_map, Option.mem_def, Option.map_eq_some_iff,
      Function.comp_apply] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    rw [Ne, T.rev_injective.eq_iff]
    exact h e he f' hf'
  rw [(IsTree.isAcyclic _ T.isTree).dist_eq_length hred, Quiver.Path.length_comp,
    Quiver.Path.length_comp, Quiver.Path.length_reverse, length_smulPath]
  omega

/-- Let `C` be a convex set of vertices invariant under `g`, and let `a` be a vertex of `C`
nearest to `v`. Suppose that `C` contains the vertices fixed by `g` in case `g` fixes `a`. Then
`d(v, g v) = d(a, g a) + 2 d(v, a)`. -/
theorem dist_smul_eq_dist_smul_add_two_mul_dist {g : G} {C : Set T.V} (hC : T.IsConvex C)
    (hgC : ∀ x, g • x ∈ C ↔ x ∈ C) {v a : T.V} (ha : a ∈ C)
    (hmin : ∀ b ∈ C, T.dist v a ≤ T.dist v b) (hfix : g • a = a → ∀ x, g • x = x → x ∈ C) :
    T.dist v (g • v) = T.dist a (g • a) + 2 * T.dist v a := by
  have hacyc := IsTree.isAcyclic _ T.isTree
  obtain ⟨q, hq, -⟩ := T.isTree.existsUnique_isReduced v a
  obtain ⟨p, hp, -⟩ := T.isTree.existsUnique_isReduced a (g • a)
  have hqC : ∀ e ∈ Path.darts T.toSerreGraph q, T.src e ∉ C := fun e he =>
    hacyc.src_notMem_of_forall_dist_le hmin hq he
  have hga : g • a ∈ C := (hgC a).mpr ha
  have hqp := hC.isReduced_comp ha hga hq (fun e he => hqC e (List.mem_of_mem_getLast? he)) hp
  rw [dist_smul_eq_of_isReduced_comp hqp, hacyc.dist_eq_length hp, hacyc.dist_eq_length hq]
  · omega
  intro e he f hf hfe
  have hf' := hqC f (List.mem_of_mem_getLast? hf)
  rcases eq_or_ne (Path.darts T.toSerreGraph p) [] with hnil | hne
  · -- `g` fixes `a`, so it would fix the last dart of `q`, which starts outside `C`.
    rw [Path.darts_comp, hnil, List.append_nil] at he
    obtain rfl : e = f := Option.some.inj (he.symm.trans hf)
    refine hf' (hfix (Path.eq_of_darts_eq_nil _ p hnil).symm _ ?_)
    rw [← src_smul, hfe]
  · -- The last dart of `p` starts in `C`, but the translate of a dart of `q` does not.
    rw [Path.darts_comp, List.getLast?_append_of_ne_nil _ hne] at he
    have he' : T.src e ∈ C := isConvex_iff.mp hC a ha _ hga p hp e (List.mem_of_mem_getLast? he)
    rw [← hfe, src_smul, hgC] at he'
    exact hf' he'

/-- The characteristic set of a hyperbolic element is contained in every nonempty convex set of
vertices invariant under it. -/
theorem IsHyperbolic.axis_subset {g : G} (hg : T.IsHyperbolic g) {C : Set T.V}
    (hC : T.IsConvex C) (hgC : ∀ x, g • x ∈ C ↔ x ∈ C) (hne : C.Nonempty) : T.axis g ⊆ C := by
  intro v hv
  obtain ⟨a, ha, hmin⟩ := exists_forall_dist_le hne v
  have h := dist_smul_eq_dist_smul_add_two_mul_dist hC hgC ha hmin
    fun h => absurd h (isHyperbolic_iff.mp hg a)
  have := translationLength_le g a
  rw [mem_axis_iff.mp hv] at h
  rwa [(dist_eq_zero_iff (T.nonempty_path v a)).mp (by omega)]

/-! ### Geodesic lines translated by an element -/

section Translation

variable {g : G} {c : ℤ → T.V} {t : ℤ}

/-- If `g` translates a geodesic line by `t ≠ 0`, every vertex is moved by `|t|` plus twice its
distance to some vertex of the line. -/
private theorem exists_dist_smul_eq_natAbs_add
    (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs) (ht : t ≠ 0)
    (hg : ∀ n, g • c n = c (n + t)) (v : T.V) :
    ∃ m, T.dist v (g • v) = t.natAbs + 2 * T.dist v (c m) := by
  obtain ⟨_, ⟨m, rfl⟩, hmin⟩ := exists_forall_dist_le (Set.range_nonempty c) v
  have hne : g • c m ≠ c m := fun h => by
    have := hc (m + t) m
    rw [← hg, h, dist_self] at this
    omega
  have hgC : ∀ x, g • x ∈ Set.range c ↔ x ∈ Set.range c := by
    refine fun x => ⟨fun ⟨n, hn⟩ => ⟨n - t, ?_⟩, fun ⟨n, hn⟩ => ⟨n + t, by rw [← hn, hg]⟩⟩
    rw [← smul_left_cancel_iff g, hg, sub_add_cancel, hn]
  refine ⟨m, ?_⟩
  rw [dist_smul_eq_dist_smul_add_two_mul_dist
    ((IsTree.isAcyclic _ T.isTree).isConvex_range_of_dist_eq_natAbs hc) hgC (Set.mem_range_self m)
    hmin fun h => absurd h hne, hg, hc]
  congr 1
  omega

/-- An element translating a geodesic line by a nonzero amount is hyperbolic. -/
theorem isHyperbolic_of_smul_eq_add (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs)
    (ht : t ≠ 0) (hg : ∀ n, g • c n = c (n + t)) : T.IsHyperbolic g := by
  refine isHyperbolic_iff.mpr fun v hv => ?_
  obtain ⟨m, hm⟩ := exists_dist_smul_eq_natAbs_add hc ht hg v
  rw [hv, dist_self] at hm
  omega

/-- If `g` translates a geodesic line by `t`, its translation length is `|t|`. -/
theorem translationLength_eq_natAbs_of_smul_eq_add
    (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs)
    (hg : ∀ n, g • c n = c (n + t)) : T.translationLength g = t.natAbs := by
  refine le_antisymm ?_ ?_
  · have h := translationLength_le g (c 0)
    rw [hg, hc] at h
    omega
  · obtain rfl | ht := eq_or_ne t 0
    · simp
    obtain ⟨v, hv⟩ := exists_dist_eq_translationLength (T := T) g
    obtain ⟨m, hm⟩ := exists_dist_smul_eq_natAbs_add hc ht hg v
    omega

/-- A geodesic line translated by `g` by a nonzero amount is the axis of `g`. -/
theorem axis_eq_range_of_smul_eq_add (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs)
    (ht : t ≠ 0) (hg : ∀ n, g • c n = c (n + t)) : T.axis g = Set.range c := by
  have hℓ := translationLength_eq_natAbs_of_smul_eq_add hc hg
  refine Set.Subset.antisymm (fun v hv => ?_) ?_
  · obtain ⟨m, hm⟩ := exists_dist_smul_eq_natAbs_add hc ht hg v
    rw [mem_axis_iff.mp hv, hℓ] at hm
    exact ⟨m, ((dist_eq_zero_iff (T.nonempty_path v (c m))).mp (by omega)).symm⟩
  · rintro _ ⟨m, rfl⟩
    rw [mem_axis_iff, hg, hc, hℓ]
    omega

end Translation

/-! ### The axis of a hyperbolic element -/

/-- Through a vertex `x` moved by the translation length `ℓ` of `g` there is a family of vertices
indexed by the integers, with consecutive members at distance at most one, shifted by `ℓ` under
`g`: the translates of a geodesic from `x` to `g • x` by the powers of `g`. -/
private theorem exists_smul_eq_add_translationLength {g : G} {x : T.V} (hx : x ∈ T.axis g)
    (hℓ : 0 < T.translationLength g) :
    ∃ c : ℤ → T.V, c 0 = x ∧ (∀ n, c (n + T.translationLength g) = g • c n) ∧
      ∀ n, T.dist (c n) (c (n + 1)) ≤ 1 := by
  obtain ⟨u, hu₀, hu, hstep⟩ := exists_forall_dist_succ_le_one (T.nonempty_path x (g • x))
  rw [mem_axis_iff.mp hx] at hu
  set ℓ : ℤ := ((T.translationLength g : ℕ) : ℤ)
  have hℓ' : 0 < ℓ := by omega
  refine ⟨fun n => g ^ (n / ℓ) • u (n % ℓ).toNat, by simp [hu₀], fun n => ?_, fun n => ?_⟩
  · simp only [Int.add_emod_right, Int.add_ediv_of_dvd_right (dvd_refl ℓ), Int.ediv_self hℓ'.ne']
    rw [add_comm, zpow_one_add, mul_smul]
  · -- Both vertices are translates by `g ^ (n / ℓ)` of consecutive vertices of the geodesic.
    have hr₀ := Int.emod_nonneg n hℓ'.ne'
    have hr := Int.emod_lt_of_pos n hℓ'
    have hdiv := Int.emod_add_mul_ediv n ℓ
    have key : g ^ ((n + 1) / ℓ) • u ((n + 1) % ℓ).toNat =
        g ^ (n / ℓ) • u ((n % ℓ).toNat + 1) := by
      rcases (Int.add_one_le_iff.mpr hr).lt_or_eq with h | h
      · obtain ⟨h₁, h₂⟩ := (Int.ediv_emod_unique (a := n + 1) (q := n / ℓ) hℓ').mpr
          ⟨by omega, by omega, h⟩
        rw [h₁, h₂]
        congr 2
        omega
      · obtain ⟨h₁, h₂⟩ := (Int.ediv_emod_unique (a := n + 1) (q := n / ℓ + 1) (r := 0) hℓ').mpr
          ⟨by rw [mul_add, mul_one]; omega, le_rfl, hℓ'⟩
        rw [h₁, h₂, show (n % ℓ).toNat + 1 = T.translationLength g by omega, hu, Int.toNat_zero,
          hu₀, zpow_add_one, mul_smul]
    beta_reduce
    rw [key, dist_smul]
    exact (hstep _).2

/-- A family of vertices indexed by the integers, with consecutive members at distance at most
one, that starts on the axis of a hyperbolic element `g` and is shifted by the translation length
under `g`, is a geodesic line. -/
private theorem dist_eq_natAbs_of_smul_eq_add_translationLength {g : G} {c : ℤ → T.V}
    (hℓ : 0 < T.translationLength g) (h₀ : c 0 ∈ T.axis g)
    (hg : ∀ n, c (n + T.translationLength g) = g • c n)
    (hstep : ∀ n, T.dist (c n) (c (n + 1)) ≤ 1) (m n : ℤ) :
    T.dist (c m) (c n) = (m - n).natAbs := by
  have hup := dist_le_natAbs (fun _ => T.nonempty_path _ _) hstep
  have hpow (k : ℕ) (n : ℤ) : c (n + (k * T.translationLength g : ℕ)) = g ^ k • c n := by
    rw [pow_smul_eq_add_nsmul (fun n => (hg n).symm), nsmul_eq_mul, Nat.cast_mul]
  -- It suffices to treat `m ≤ n`; translate both vertices to nonnegative indices and compare
  -- with the distance from `c 0` to its image under a large power of `g`.
  wlog hmn : m ≤ n generalizing m n
  · rw [dist_comm, this n m (le_of_not_ge hmn)]
    omega
  refine le_antisymm (hup m n) ?_
  set k := m.natAbs
  set N := (n + (k * T.translationLength g : ℕ)).toNat
  have hk : k ≤ k * T.translationLength g := Nat.le_mul_of_pos_right k hℓ
  have hN : N ≤ N * T.translationLength g := Nat.le_mul_of_pos_right N hℓ
  have h₁ := hup 0 (m + (k * T.translationLength g : ℕ))
  have h₂ : T.dist (c (m + (k * T.translationLength g : ℕ)))
      (c (n + (k * T.translationLength g : ℕ))) = T.dist (c m) (c n) := by
    rw [hpow, hpow, dist_smul]
  have h₃ := hup (n + (k * T.translationLength g : ℕ)) (N * T.translationLength g : ℕ)
  have h₄ : T.dist (c 0) (c (N * T.translationLength g : ℕ)) = N * T.translationLength g := by
    rw [← zero_add ((N * T.translationLength g : ℕ) : ℤ), hpow, dist_pow_smul_of_mem_axis h₀]
  have htri := dist_triangle (T.nonempty_path (c 0) (c (m + (k * T.translationLength g : ℕ))))
    (T.nonempty_path _ (c (N * T.translationLength g : ℕ)))
  have htri' := dist_triangle
    (T.nonempty_path (c (m + (k * T.translationLength g : ℕ)))
      (c (n + (k * T.translationLength g : ℕ))))
    (T.nonempty_path _ (c (N * T.translationLength g : ℕ)))
  omega

/-- **The axis of a hyperbolic element.** Through every vertex `x` of the axis of a hyperbolic
element `g` there is a geodesic line `c`, with `c 0 = x`, whose vertices are exactly those of the
axis and on which `g` acts as the translation by its translation length. -/
theorem IsHyperbolic.exists_range_eq_axis {g : G} (hg : T.IsHyperbolic g) {x : T.V}
    (hx : x ∈ T.axis g) :
    ∃ c : ℤ → T.V, c 0 = x ∧ (∀ m n, T.dist (c m) (c n) = (m - n).natAbs) ∧
      (∀ n, g • c n = c (n + T.translationLength g)) ∧ Set.range c = T.axis g := by
  have hℓ := translationLength_pos_iff.mpr hg
  obtain ⟨c, hc₀, hgc, hstep⟩ := exists_smul_eq_add_translationLength hx hℓ
  have hc := dist_eq_natAbs_of_smul_eq_add_translationLength hℓ (hc₀ ▸ hx) hgc hstep
  exact ⟨c, hc₀, hc, fun n => (hgc n).symm,
    (axis_eq_range_of_smul_eq_add hc (by omega) fun n => (hgc n).symm).symm⟩

variable (T) in
/-- The characteristic set of an element is convex: the fixed vertices of an elliptic element and
the axis of a hyperbolic element span subtrees. -/
theorem isConvex_axis (g : G) : T.IsConvex (T.axis g) := by
  by_cases hg : T.IsHyperbolic g
  · obtain ⟨x, hx⟩ := T.axis_nonempty g
    obtain ⟨c, -, hc, -, hrange⟩ := hg.exists_range_eq_axis hx
    rw [← hrange]
    exact (IsTree.isAcyclic _ T.isTree).isConvex_range_of_dist_eq_natAbs hc
  · rw [(not_isHyperbolic_iff.mp hg).axis_eq_fixedBy]
    exact T.isConvex_fixedBy g

/-- **Uniqueness of the axis.** A geodesic line mapped into itself by a hyperbolic element is its
axis. -/
theorem IsHyperbolic.range_eq_axis {g : G} (hg : T.IsHyperbolic g) {c : ℤ → T.V}
    (hc : ∀ m n, T.dist (c m) (c n) = (m - n).natAbs) (hgc : ∀ n, g • c n ∈ Set.range c) :
    Set.range c = T.axis g := by
  -- The image of the line is a geodesic line inside the line, so it is the whole line.
  have hrange : Set.range (fun n => g • c n) = Set.range c :=
    range_eq_of_range_subset_of_dist_eq_natAbs (fun m n => by rw [dist_smul, hc]) hc
      (Set.range_subset_iff.mpr hgc)
  have hinv : ∀ x, g • x ∈ Set.range c ↔ x ∈ Set.range c := by
    refine fun x => ⟨fun h => ?_, fun ⟨n, hn⟩ => hn ▸ hgc n⟩
    rw [← hrange] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, smul_left_cancel g hn⟩
  obtain ⟨x, hx⟩ := T.axis_nonempty g
  obtain ⟨c₀, -, hc₀, -, hr⟩ := hg.exists_range_eq_axis hx
  have hsub := hg.axis_subset ((IsTree.isAcyclic _ T.isTree).isConvex_range_of_dist_eq_natAbs hc)
    hinv (Set.range_nonempty c)
  rw [← hr] at hsub ⊢
  exact (range_eq_of_range_subset_of_dist_eq_natAbs hc₀ hc hsub).symm

/-! ### Displacement and the distance to the characteristic set -/

/-- A vertex is moved by at most the translation length plus twice its distance to any vertex of
the characteristic set. -/
theorem dist_smul_le_of_mem_axis {g : G} {a : T.V} (ha : a ∈ T.axis g) (v : T.V) :
    T.dist v (g • v) ≤ T.translationLength g + 2 * T.dist v a :=
  (T.dist_smul_le_dist_smul_add_two_mul_dist g a v).trans_eq <| by rw [mem_axis_iff.mp ha]

/-- A vertex `v` is moved by the translation length plus twice its distance to a nearest vertex
`a` of the characteristic set. -/
theorem dist_smul_eq_translationLength_add_two_mul_dist {g : G} {v a : T.V} (ha : a ∈ T.axis g)
    (hmin : ∀ b ∈ T.axis g, T.dist v a ≤ T.dist v b) :
    T.dist v (g • v) = T.translationLength g + 2 * T.dist v a := by
  rw [dist_smul_eq_dist_smul_add_two_mul_dist (T.isConvex_axis g) (fun _ => smul_mem_axis_iff) ha
    hmin fun _ _ => mem_axis_of_smul_eq, mem_axis_iff.mp ha]

/-- Every vertex `v` satisfies `d(v, g v) = ℓ(g) + 2 d(v, A)`, where `A` is the characteristic
set of `g`: its set of fixed vertices if `g` is elliptic and its axis if `g` is hyperbolic. -/
theorem dist_smul_eq_translationLength_add (g : G) (v : T.V) :
    T.dist v (g • v) = T.translationLength g + 2 * ⨅ a : T.axis g, T.dist v a := by
  obtain ⟨a, ha, hmin⟩ := exists_forall_dist_le (T.axis_nonempty g) v
  rw [dist_smul_eq_translationLength_add_two_mul_dist ha hmin]
  congr 2
  exact le_antisymm (le_ciInf fun b => hmin b b.2)
    (ciInf_le (OrderBot.bddBelow _) (⟨a, ha⟩ : T.axis g))

/-! ### Translation lengths and characteristic sets of powers -/

/-- The `n`-th power of `g`, for an integer `n`, has translation length `|n| ℓ(g)`. -/
@[simp] theorem translationLength_zpow (g : G) (n : ℤ) :
    T.translationLength (g ^ n) = n.natAbs * T.translationLength g := by
  by_cases hg : T.IsHyperbolic g
  · obtain ⟨x, hx⟩ := T.axis_nonempty g
    obtain ⟨c, -, hc, hgc, -⟩ := hg.exists_range_eq_axis hx
    rw [translationLength_eq_natAbs_of_smul_eq_add hc (zpow_smul_eq_add_zsmul hgc n),
      smul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  · have hg := not_isHyperbolic_iff.mp hg
    rw [translationLength_eq_zero_iff.mpr hg, translationLength_eq_zero_iff.mpr (hg.zpow n),
      mul_zero]

/-- The `n`-th power of `g` has translation length `n ℓ(g)`. -/
@[simp] theorem translationLength_pow (g : G) (n : ℕ) :
    T.translationLength (g ^ n) = n * T.translationLength g := by
  rw [← zpow_natCast, translationLength_zpow, Int.natAbs_natCast]

/-- An integer power of `g` is elliptic exactly when `g` is elliptic or the exponent is zero. -/
@[simp] theorem isElliptic_zpow_iff {g : G} {n : ℤ} :
    T.IsElliptic (g ^ n) ↔ T.IsElliptic g ∨ n = 0 := by
  rw [← translationLength_eq_zero_iff, ← translationLength_eq_zero_iff, translationLength_zpow,
    Nat.mul_eq_zero, Int.natAbs_eq_zero, or_comm]

/-- A power of `g` is elliptic exactly when `g` is elliptic or the exponent is zero. -/
@[simp] theorem isElliptic_pow_iff {g : G} {n : ℕ} :
    T.IsElliptic (g ^ n) ↔ T.IsElliptic g ∨ n = 0 := by
  rw [← translationLength_eq_zero_iff, ← translationLength_eq_zero_iff, translationLength_pow,
    Nat.mul_eq_zero, or_comm]

/-- An integer power of `g` is hyperbolic exactly when `g` is hyperbolic and the exponent is
nonzero. -/
@[simp] theorem isHyperbolic_zpow_iff {g : G} {n : ℤ} :
    T.IsHyperbolic (g ^ n) ↔ T.IsHyperbolic g ∧ n ≠ 0 := by
  rw [← not_iff_not, not_isHyperbolic_iff, isElliptic_zpow_iff, not_and_or, not_isHyperbolic_iff,
    not_ne_iff]

/-- A power of `g` is hyperbolic exactly when `g` is hyperbolic and the exponent is nonzero. -/
@[simp] theorem isHyperbolic_pow_iff {g : G} {n : ℕ} :
    T.IsHyperbolic (g ^ n) ↔ T.IsHyperbolic g ∧ n ≠ 0 := by
  rw [← not_iff_not, not_isHyperbolic_iff, isElliptic_pow_iff, not_and_or, not_isHyperbolic_iff,
    not_ne_iff]

/-- A nonzero integer power of a hyperbolic element is hyperbolic. -/
theorem IsHyperbolic.zpow {g : G} (hg : T.IsHyperbolic g) {n : ℤ} (hn : n ≠ 0) :
    T.IsHyperbolic (g ^ n) :=
  isHyperbolic_zpow_iff.mpr ⟨hg, hn⟩

/-- A nonzero power of a hyperbolic element is hyperbolic. -/
theorem IsHyperbolic.pow {g : G} (hg : T.IsHyperbolic g) {n : ℕ} (hn : n ≠ 0) :
    T.IsHyperbolic (g ^ n) :=
  isHyperbolic_pow_iff.mpr ⟨hg, hn⟩

variable (T) in
/-- The characteristic set of `g` is contained in that of every integer power of `g`. -/
theorem axis_subset_axis_zpow (g : G) (n : ℤ) : T.axis g ⊆ T.axis (g ^ n) := fun _ hx => by
  rw [mem_axis_iff, dist_zpow_smul_of_mem_axis hx, translationLength_zpow]

variable (T) in
/-- The characteristic set of `g` is contained in that of every power of `g`. -/
theorem axis_subset_axis_pow (g : G) (n : ℕ) : T.axis g ⊆ T.axis (g ^ n) := fun _ hx => by
  rw [mem_axis_iff, dist_pow_smul_of_mem_axis hx, translationLength_pow]

/-- A nonzero integer power of a hyperbolic element has the same axis. -/
theorem IsHyperbolic.axis_zpow {g : G} (hg : T.IsHyperbolic g) {n : ℤ} (hn : n ≠ 0) :
    T.axis (g ^ n) = T.axis g := by
  obtain ⟨x, hx⟩ := T.axis_nonempty g
  obtain ⟨c, -, hc, hgc, hrange⟩ := hg.exists_range_eq_axis hx
  have hℓ := translationLength_pos_iff.mpr hg
  rw [axis_eq_range_of_smul_eq_add hc (smul_ne_zero hn (by omega))
    (zpow_smul_eq_add_zsmul hgc n), hrange]

/-- A nonzero power of a hyperbolic element has the same axis. -/
theorem IsHyperbolic.axis_pow {g : G} (hg : T.IsHyperbolic g) {n : ℕ} (hn : n ≠ 0) :
    T.axis (g ^ n) = T.axis g := by
  simpa only [zpow_natCast] using hg.axis_zpow (Int.natCast_ne_zero.mpr hn)

/-! ### The line -/

/-- Every vertex of the line lies on the axis of every translation. -/
@[simp] theorem line_axis (k : Multiplicative ℤ) : line.axis k = Set.univ :=
  Set.eq_univ_of_forall fun v => by rw [mem_axis_iff, line_dist_smul, line_translationLength]

end GTree
end TauCeti
