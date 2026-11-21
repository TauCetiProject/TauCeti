/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Bridge
public import TauCeti.GroupTheory.GTree.OrbitHull

/-!
# The minimal invariant subtree of a subgroup

Let `G` act on a tree `T` without inversions and let `H` be a subgroup of `G`. The *minimal
subtree* `μ_T(H)` (`GTree.minimalSubtree`) is the union of the axes of the hyperbolic elements of
`H`. If `H` contains a hyperbolic element, then `μ_T(H)` is the smallest nonempty convex set of
vertices invariant under `H`; in particular it is the unique minimal `H`-invariant subtree of `T`.
If every element of `H` is elliptic, then `μ_T(H)` is empty.

The key step is convexity, which rests on the following computation. Let `g` and `h` have
disjoint characteristic sets `A_g` and `A_h` (axes, or sets of fixed vertices), and let `p ∈ A_g`
and `q ∈ A_h` be at minimal distance. Going from `h⁻¹ q` along `A_h` to `q`, across to `p`, along
`A_g` to `g p` and back to `g q` is a reduced path from `h⁻¹ q` to `(g h) (h⁻¹ q)` which is followed
by its translate under `g h` without backtracking. Hence `g h` is hyperbolic, with translation
length `ℓ(g h) = ℓ(g) + ℓ(h) + 2 d(p, q)`, and its axis passes through `p` and `q`. So two axes of
hyperbolic elements of `H` are either joined directly, or through the axis of their product, and
in both cases the union of the axes involved is convex. Minimality holds because the axis of a
hyperbolic element lies in every nonempty convex set invariant under it
(`GTree.IsHyperbolic.axis_subset`).

## Main declarations

* `TauCeti.GTree.translationLength_mul_of_disjoint_axis`: if `g` and `h` have disjoint
  characteristic sets at distance `d`, then `g h`, which is hyperbolic
  (`TauCeti.GTree.isHyperbolic_mul_of_disjoint_axis`), has translation length `ℓ(g) + ℓ(h) + 2 d`.
* `TauCeti.GTree.mem_axis_mul_of_disjoint_axis_left`,
  `TauCeti.GTree.mem_axis_mul_of_disjoint_axis_right`: its axis passes through the two ends of a
  shortest path between the characteristic sets.
* `TauCeti.GTree.minimalSubtree`: the union of the axes of the hyperbolic elements of `H`.
* `TauCeti.GTree.isConvex_minimalSubtree`, `TauCeti.GTree.smul_mem_minimalSubtree_iff`,
  `TauCeti.GTree.minimalSubtree_subset`: it is convex, invariant under `H`, and contained in every
  nonempty convex set invariant under `H`.
* `TauCeti.GTree.eq_minimalSubtree_iff`: when `H` contains a hyperbolic element, a nonempty convex
  `H`-invariant set is minimal among such sets exactly when it is `μ_T(H)`.
* `TauCeti.GTree.isMinimal_iff_minimalSubtree_eq_univ`: a tree with a hyperbolic element is
  minimal exactly when it is the union of the axes of all hyperbolic elements.

## References

* J.-P. Serre, *Trees*, Chapter I, §6.4 and §6.5.
* M. Culler and J. W. Morgan, *Group actions on ℝ-trees*, Proc. London Math. Soc. (3) 55 (1987),
  §1.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1,
  Proposition 1.1.
-/

public section

universe u v w

namespace TauCeti
namespace GTree

open SerreGraph _root_.MulAction
open scoped Pointwise

variable {G : Type w} [Group G] {T : GTree.{u, v} G}

/-! ### Products of elements with disjoint characteristic sets -/

/-- Let `p` be a vertex of the characteristic set of `g` nearest to `q`. Then the reduced path from
`q` to `p`, followed by the reduced path from `p` to `g • p` and by the translate of the first path
reversed, is a reduced path from `q` to `g • q`. -/
private theorem isReduced_comp_comp_smulPath_reverse {g : G} {p q : T.V} (hp : p ∈ T.axis g)
    (hmin : ∀ p' ∈ T.axis g, T.dist q p ≤ T.dist q p') {r : T.Path q p}
    (hr : Path.IsReduced T.toSerreGraph r) {b : T.Path p (g • p)}
    (hb : Path.IsReduced T.toSerreGraph b) :
    Path.IsReduced T.toSerreGraph ((r.comp b).comp (smulPath g r).reverse) := by
  -- Its length `2 d(q, p) + ℓ(g)` is the distance from `q` to `g • q`.
  refine Path.isReduced_of_length_le_dist (le_of_eq ?_)
  have hacyc := IsTree.isAcyclic _ T.isTree
  have hdr := hacyc.dist_eq_length hr
  have hdb := hacyc.dist_eq_length hb
  have hpA := mem_axis_iff.mp hp
  rw [dist_smul_eq_translationLength_add_two_mul_dist hp hmin]
  simp only [Quiver.Path.length_comp, Quiver.Path.length_reverse, length_smulPath]
  omega

/-- Let `q` be a vertex of the characteristic set of `h`, and let `s` be a reduced path from `q` to
`g • q` whose first dart `f` ends outside that set and whose last dart is the reverse of `g • f`.
Then the reduced path from `h⁻¹ • q` to `q` followed by `s` is reduced, and `h⁻¹ • q` lies in the
characteristic set of `g * h`. -/
private theorem mem_axis_mul_of_isReduced {g h : G} {q : T.V} (hq : q ∈ T.axis h)
    {s : T.Path q (g • q)} (hs : Path.IsReduced T.toSerreGraph s) {f : T.E}
    (hhead : (Path.darts T.toSerreGraph s).head? = some f)
    (hlast : (Path.darts T.toSerreGraph s).getLast? = some (T.rev (g • f)))
    (hf : T.tgt f ∉ T.axis h) {a : T.Path (h⁻¹ • q) q} (ha : Path.IsReduced T.toSerreGraph a) :
    Path.IsReduced T.toSerreGraph (a.comp s) ∧ h⁻¹ • q ∈ T.axis (g * h) := by
  have hqa : h⁻¹ • q ∈ T.axis h := inv_smul_mem_axis_iff.mpr hq
  have haA : ∀ e ∈ Path.darts T.toSerreGraph a, T.src e ∈ T.axis h ∧ T.tgt e ∈ T.axis h :=
    fun e he => ⟨(T.isConvex_axis h).src_mem hqa hq ha he,
      (T.isConvex_axis h).tgt_mem hqa hq ha he⟩
  -- The darts of `a` start in the characteristic set of `h`, while `f` ends outside of it.
  have has : Path.IsReduced T.toSerreGraph (a.comp s) := by
    refine (Path.isReduced_comp_iff _ a s).mpr ⟨ha, hs, fun e he f' hf' hfe => ?_⟩
    rw [hhead, Option.mem_some_iff] at hf'
    subst hf'
    rw [hfe, tgt_rev] at hf
    exact hf (haA e (List.mem_of_mem_getLast? he)).1
  refine ⟨has, ?_⟩
  have hgx : g • q = (g * h) • (h⁻¹ • q) := by rw [mul_smul, smul_inv_smul]
  -- The translate of `a.comp s` under `g * h` follows it without backtracking.
  refine mem_axis_of_isReduced (p := (a.comp s).cast rfl hgx) (by rwa [Path.isReduced_cast])
    fun e he f' hf' hfe => ?_
  rw [Path.darts_cast, Path.darts_comp, List.getLast?_append, hlast, Option.some_or,
    Option.mem_some_iff] at he
  subst he
  rw [rev_rev, mul_smul, smul_left_cancel_iff] at hfe
  rw [Path.darts_cast, Path.darts_comp, List.head?_append] at hf'
  cases hfa : (Path.darts T.toSerreGraph a).head? with
  | some f'' =>
    -- The first dart of `a` ends in the characteristic set of `h`, unlike `f`.
    rw [hfa, Option.some_or, Option.mem_some_iff] at hf'
    subst hf'
    rw [← hfe, tgt_smul, smul_mem_axis_iff] at hf
    exact hf (haA f'' (List.mem_of_mem_head? hfa)).2
  | none =>
    -- Otherwise `h` would fix `f`, hence its target.
    rw [hfa, Option.none_or, hhead, Option.mem_some_iff] at hf'
    subst hf'
    exact hf (mem_axis_of_smul_eq (by rw [← tgt_smul, hfe]))

/-- Let `g` and `h` have disjoint characteristic sets, and let `p` and `q` be vertices of these
at minimal distance. Then `h⁻¹ • q` lies in the characteristic set of `g * h` and is moved by
`ℓ(g) + ℓ(h) + 2 d(p, q)`, and `p` and `q` lie in the characteristic set of `g * h`. -/
private theorem exists_mem_axis_mul_of_disjoint_axis {g h : G}
    (hd : Disjoint (T.axis g) (T.axis h)) {p q : T.V} (hp : p ∈ T.axis g) (hq : q ∈ T.axis h)
    (hmin : ∀ p' ∈ T.axis g, ∀ q' ∈ T.axis h, T.dist p q ≤ T.dist p' q') :
    (∃ x ∈ T.axis (g * h), T.dist x ((g * h) • x) =
      T.translationLength g + T.translationLength h + 2 * T.dist p q) ∧
      p ∈ T.axis (g * h) ∧ q ∈ T.axis (g * h) := by
  have hacyc := IsTree.isAcyclic _ T.isTree
  have hqp : q ≠ p := fun hqp => Set.disjoint_left.mp hd hp (hqp ▸ hq)
  -- The reduced paths: `a` from `h⁻¹ • q` to `q`, `r` from `q` to `p` and `b` from `p` to `g • p`.
  obtain ⟨a, ha, -⟩ := T.isTree.existsUnique_isReduced (h⁻¹ • q) q
  obtain ⟨r, hr, -⟩ := T.isTree.existsUnique_isReduced q p
  obtain ⟨b, hb, -⟩ := T.isTree.existsUnique_isReduced p (g • p)
  have hrne : Path.darts T.toSerreGraph r ≠ [] := fun h0 => hqp (Path.eq_of_darts_eq_nil _ r h0)
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp (mt List.head?_eq_none_iff.mp hrne)
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp hrne)
  -- Since `q` is a vertex of the characteristic set of `h` nearest to `p`, the first dart of `r`
  -- ends outside of it.
  have hfr : T.rev f ∈ Path.darts T.toSerreGraph r.reverse := by
    rw [Path.darts_reverse, List.map_reverse, List.mem_reverse]
    exact List.mem_map_of_mem (List.mem_of_mem_head? hf)
  have hfA : T.tgt f ∉ T.axis h := by
    rw [← src_rev]
    exact hacyc.src_notMem_of_forall_dist_le (fun b hb => hmin p hp b hb)
      ((Path.isReduced_reverse _ r).mpr hr) hfr
  -- The path `s` from `q` along `r`, `b` and back along the translate of `r`.
  have hmin' : ∀ p' ∈ T.axis g, T.dist q p ≤ T.dist q p' := fun p' hp' => by
    simpa only [dist_comm q] using hmin p' hp' q hq
  have hs := isReduced_comp_comp_smulPath_reverse hp hmin' hr hb
  obtain ⟨has, hxA⟩ := mem_axis_mul_of_isReduced hq hs (by simp [hf]) (by simp [hf]) hfA ha
  -- The reduced path `a.comp s` joins two vertices of the characteristic set of `g * h`, and
  -- passes through `p` and `q`.
  have hgxA : g • q ∈ T.axis (g * h) := by simpa [mul_smul] using smul_mem_axis_iff.mpr hxA
  have hmem : ∀ e' ∈ Path.darts T.toSerreGraph r,
      e' ∈ Path.darts T.toSerreGraph (a.comp ((r.comp b).comp (smulPath g r).reverse)) :=
    fun e' he' => by simp [he']
  refine ⟨⟨_, hxA, ?_⟩, ?_, ?_⟩
  · -- Its length is `ℓ(h) + d(q, g • q)`, where `d(q, g • q) = ℓ(g) + 2 d(q, p)`.
    have hda := hacyc.dist_eq_length ha
    have hds := hacyc.dist_eq_length hs
    have hgq := dist_smul_eq_translationLength_add_two_mul_dist hp hmin'
    have hqA : T.dist (h⁻¹ • q) q = T.translationLength h := by
      simpa only [smul_inv_smul] using mem_axis_iff.mp (inv_smul_mem_axis_iff.mpr hq)
    rw [show (g * h) • (h⁻¹ • q) = g • q by rw [mul_smul, smul_inv_smul], hacyc.dist_eq_length has,
      Quiver.Path.length_comp, dist_comm p q]
    omega
  · rw [← Path.tgt_eq_of_mem_getLast?_darts _ r he]
    exact (T.isConvex_axis _).tgt_mem hxA hgxA has (hmem e (List.mem_of_mem_getLast? he))
  · rw [← Path.src_eq_of_mem_head?_darts _ r hf]
    exact (T.isConvex_axis _).src_mem hxA hgxA has (hmem f (List.mem_of_mem_head? hf))

/-- **The translation length of a product.** If `g` and `h` have disjoint characteristic sets,
and `p` and `q` are vertices of these at minimal distance, then
`ℓ(g * h) = ℓ(g) + ℓ(h) + 2 d(p, q)`. -/
theorem translationLength_mul_of_disjoint_axis {g h : G} (hd : Disjoint (T.axis g) (T.axis h))
    {p q : T.V} (hp : p ∈ T.axis g) (hq : q ∈ T.axis h)
    (hmin : ∀ p' ∈ T.axis g, ∀ q' ∈ T.axis h, T.dist p q ≤ T.dist p' q') :
    T.translationLength (g * h) =
      T.translationLength g + T.translationLength h + 2 * T.dist p q := by
  obtain ⟨⟨x, hx, hdist⟩, -, -⟩ := exists_mem_axis_mul_of_disjoint_axis hd hp hq hmin
  rw [← mem_axis_iff.mp hx, hdist]

/-- If `g` and `h` have disjoint characteristic sets, then the characteristic set of `g * h`
contains the vertex `p` of the characteristic set of `g` nearest to that of `h`. -/
theorem mem_axis_mul_of_disjoint_axis_left {g h : G} (hd : Disjoint (T.axis g) (T.axis h))
    {p q : T.V} (hp : p ∈ T.axis g) (hq : q ∈ T.axis h)
    (hmin : ∀ p' ∈ T.axis g, ∀ q' ∈ T.axis h, T.dist p q ≤ T.dist p' q') :
    p ∈ T.axis (g * h) :=
  (exists_mem_axis_mul_of_disjoint_axis hd hp hq hmin).2.1

/-- If `g` and `h` have disjoint characteristic sets, then the characteristic set of `g * h`
contains the vertex `q` of the characteristic set of `h` nearest to that of `g`. -/
theorem mem_axis_mul_of_disjoint_axis_right {g h : G} (hd : Disjoint (T.axis g) (T.axis h))
    {p q : T.V} (hp : p ∈ T.axis g) (hq : q ∈ T.axis h)
    (hmin : ∀ p' ∈ T.axis g, ∀ q' ∈ T.axis h, T.dist p q ≤ T.dist p' q') :
    q ∈ T.axis (g * h) :=
  (exists_mem_axis_mul_of_disjoint_axis hd hp hq hmin).2.2

/-- The characteristic sets of two elements contain vertices at minimal distance. -/
private theorem exists_mem_axis_forall_dist_le (g h : G) :
    ∃ p ∈ T.axis g, ∃ q ∈ T.axis h,
      ∀ p' ∈ T.axis g, ∀ q' ∈ T.axis h, T.dist p q ≤ T.dist p' q' := by
  obtain ⟨⟨p, q⟩, ⟨hp, hq⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun x : T.V × T.V => x.1 ∈ T.axis g ∧ x.2 ∈ T.axis h) (fun x => T.dist x.1 x.2)
    ((T.axis_nonempty g).prod (T.axis_nonempty h))
  exact ⟨p, hp, q, hq, fun p' hp' q' hq' =>
    (le_total _ _).elim id (hmin (j := (p', q')) ⟨hp', hq'⟩)⟩

/-! ### The minimal subtree -/

variable (T) in
/-- The minimal subtree `μ_T(H)` of a subgroup `H`: the union of the axes of the hyperbolic
elements of `H`. When `H` contains a hyperbolic element, it is the smallest nonempty convex set of
vertices invariant under `H` (`GTree.minimalSubtree_subset`); when every element of `H` is
elliptic, it is empty. -/
def minimalSubtree (H : Subgroup G) : Set T.V :=
  ⋃ g ∈ H, ⋃ (_ : T.IsHyperbolic g), T.axis g

variable {H K : Subgroup G}

theorem mem_minimalSubtree_iff {v : T.V} :
    v ∈ T.minimalSubtree H ↔ ∃ g ∈ H, T.IsHyperbolic g ∧ v ∈ T.axis g := by
  simp only [minimalSubtree, Set.mem_iUnion, exists_prop]

/-- The axis of a hyperbolic element of `H` lies in the minimal subtree of `H`. -/
theorem IsHyperbolic.axis_subset_minimalSubtree {g : G} (hg : T.IsHyperbolic g) (hgH : g ∈ H) :
    T.axis g ⊆ T.minimalSubtree H :=
  fun _ hv => mem_minimalSubtree_iff.mpr ⟨g, hgH, hg, hv⟩

/-- The minimal subtree of `H` is nonempty exactly when `H` contains a hyperbolic element. -/
theorem minimalSubtree_nonempty_iff :
    (T.minimalSubtree H).Nonempty ↔ ∃ g ∈ H, T.IsHyperbolic g := by
  refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨g, hgH, hg⟩ => ?_⟩
  · obtain ⟨g, hgH, hg, -⟩ := mem_minimalSubtree_iff.mp hv
    exact ⟨g, hgH, hg⟩
  · exact (T.axis_nonempty g).mono (hg.axis_subset_minimalSubtree hgH)

/-- The minimal subtree of `H` is empty exactly when every element of `H` is elliptic. -/
theorem minimalSubtree_eq_empty_iff : T.minimalSubtree H = ∅ ↔ ∀ g ∈ H, T.IsElliptic g := by
  rw [← Set.not_nonempty_iff_eq_empty, minimalSubtree_nonempty_iff]
  simp only [not_exists, not_and, ← not_isHyperbolic_iff]

variable (T) in
/-- A larger subgroup has a larger minimal subtree. -/
theorem minimalSubtree_mono (h : H ≤ K) : T.minimalSubtree H ⊆ T.minimalSubtree K :=
  Set.biUnion_subset_biUnion_left h

variable (T) in
/-- The trivial subgroup has no hyperbolic element, so its minimal subtree is empty. -/
@[simp] theorem minimalSubtree_bot : T.minimalSubtree ⊥ = ∅ :=
  minimalSubtree_eq_empty_iff.mpr fun g hg => by
    rw [Subgroup.mem_bot.mp hg]
    exact T.isElliptic_one

variable (T H) in
/-- The translate by `g` of the minimal subtree of `H` is the minimal subtree of the conjugate
subgroup `g H g⁻¹`. -/
theorem minimalSubtree_map_conj (g : G) :
    T.minimalSubtree (H.map (MulAut.conj g : G →* G)) = g • T.minimalSubtree H := by
  ext v
  simp only [mem_minimalSubtree_iff, Subgroup.mem_map, MonoidHom.coe_ofClass, MulAut.conj_apply,
    exists_exists_and_eq_and, isHyperbolic_conj_iff, mem_axis_conj_iff,
    Set.mem_smul_set_iff_inv_smul_mem]

/-- The minimal subtree of `H` is invariant under `H`. -/
@[simp] theorem smul_mem_minimalSubtree_iff {g : G} (hg : g ∈ H) {v : T.V} :
    g • v ∈ T.minimalSubtree H ↔ v ∈ T.minimalSubtree H := by
  have key : ∀ g ∈ H, ∀ v, v ∈ T.minimalSubtree H → g • v ∈ T.minimalSubtree H := by
    intro g hg v hv
    obtain ⟨k, hkH, hk, hv⟩ := mem_minimalSubtree_iff.mp hv
    refine mem_minimalSubtree_iff.mpr ⟨g * k * g⁻¹, H.mul_mem (H.mul_mem hg hkH) (H.inv_mem hg),
      isHyperbolic_conj_iff.mpr hk, ?_⟩
    rwa [mem_axis_conj_iff, inv_smul_smul]
  exact ⟨fun h => by simpa using key g⁻¹ (H.inv_mem hg) _ h, key g hg v⟩

/-- The minimal subtree of `H` is invariant under `H`. -/
@[simp] theorem smul_set_minimalSubtree {g : G} (hg : g ∈ H) :
    g • T.minimalSubtree H = T.minimalSubtree H := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_mem_minimalSubtree_iff (H.inv_mem hg)]

variable (T H) in
/-- **The minimal subtree is a subtree.** The union of the axes of the hyperbolic elements of a
subgroup is convex. -/
theorem isConvex_minimalSubtree : T.IsConvex (T.minimalSubtree H) := by
  rw [isConvex_iff]
  intro a ha b hb p hp e he
  obtain ⟨g, hgH, hg, hag⟩ := mem_minimalSubtree_iff.mp ha
  obtain ⟨h, hhH, hh, hbh⟩ := mem_minimalSubtree_iff.mp hb
  -- It suffices to find a convex set inside the minimal subtree containing both ends of `p`.
  suffices ∃ C, T.IsConvex C ∧ C ⊆ T.minimalSubtree H ∧ a ∈ C ∧ b ∈ C by
    obtain ⟨C, hC, hCH, haC, hbC⟩ := this
    exact hCH (hC.src_mem haC hbC hp he)
  have hgμ := hg.axis_subset_minimalSubtree hgH
  have hhμ := hh.axis_subset_minimalSubtree hhH
  by_cases hd : (T.axis g ∩ T.axis h).Nonempty
  · -- Two axes which meet have a convex union.
    exact ⟨_, T.isTree.isConvex_union (T.isConvex_axis g) (T.isConvex_axis h) hd,
      Set.union_subset hgμ hhμ, Or.inl hag, Or.inr hbh⟩
  · -- Two disjoint axes are joined by the axis of the product, which meets both.
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hd
    obtain ⟨p, hp, q, hq, hmin⟩ := exists_mem_axis_forall_dist_le (T := T) g h
    have hgh := isHyperbolic_mul_of_disjoint_axis hd
    have hghμ := hgh.axis_subset_minimalSubtree (H.mul_mem hgH hhH)
    have h₁ := T.isTree.isConvex_union (T.isConvex_axis g) (T.isConvex_axis (g * h))
      ⟨p, hp, mem_axis_mul_of_disjoint_axis_left hd hp hq hmin⟩
    refine ⟨_, T.isTree.isConvex_union h₁ (T.isConvex_axis h)
      ⟨q, Or.inr (mem_axis_mul_of_disjoint_axis_right hd hp hq hmin), hq⟩,
      Set.union_subset (Set.union_subset hgμ hghμ) hhμ, Or.inl (Or.inl hag), Or.inr hbh⟩

/-- **Minimality of the minimal subtree.** The minimal subtree of `H` is contained in every
nonempty convex set of vertices invariant under `H`. -/
theorem minimalSubtree_subset {C : Set T.V} (hC : T.IsConvex C)
    (hHC : ∀ h ∈ H, ∀ v ∈ C, h • v ∈ C) (hne : C.Nonempty) : T.minimalSubtree H ⊆ C := by
  intro v hv
  obtain ⟨g, hgH, hg, hv⟩ := mem_minimalSubtree_iff.mp hv
  refine hg.axis_subset hC (fun x => ⟨fun hx => ?_, hHC g hgH x⟩) hne hv
  simpa using hHC g⁻¹ (H.inv_mem hgH) _ hx

variable (T H) in
/-- The minimal subtree of `H` is contained in the convex hull of every orbit of `H`. -/
theorem minimalSubtree_subset_orbitHull (x : T.V) : T.minimalSubtree H ⊆ T.orbitHull H x :=
  minimalSubtree_subset (isConvex_orbitHull T H x)
    (fun _ hh _ hv => (smul_mem_orbitHull_iff hh).mpr hv) (orbitHull_nonempty T H x)

/-- **Uniqueness of the minimal subtree.** If `H` contains a hyperbolic element, then a nonempty
convex set of vertices invariant under `H` contains no smaller such set exactly when it is the
minimal subtree of `H`. -/
theorem eq_minimalSubtree_iff (hH : ∃ g ∈ H, T.IsHyperbolic g) {C : Set T.V}
    (hC : T.IsConvex C) (hHC : ∀ h ∈ H, ∀ v ∈ C, h • v ∈ C) (hne : C.Nonempty) :
    C = T.minimalSubtree H ↔ ∀ C' ⊆ C, C'.Nonempty → T.IsConvex C' →
      (∀ h ∈ H, ∀ v ∈ C', h • v ∈ C') → C' = C := by
  have hμ : ∀ h ∈ H, ∀ v ∈ T.minimalSubtree H, h • v ∈ T.minimalSubtree H :=
    fun h hh v hv => (smul_mem_minimalSubtree_iff hh).mpr hv
  refine ⟨?_, fun hmin => (hmin _ (minimalSubtree_subset hC hHC hne)
    (minimalSubtree_nonempty_iff.mpr hH) (isConvex_minimalSubtree T H) hμ).symm⟩
  rintro rfl C' hC'C hne' hC' hHC'
  exact hC'C.antisymm (minimalSubtree_subset hC' hHC' hne')

/-- A `G`-tree in which some element is hyperbolic is minimal exactly when it is the union of the
axes of the hyperbolic elements of `G`. -/
theorem isMinimal_iff_minimalSubtree_eq_univ (hT : ∃ g : G, T.IsHyperbolic g) :
    T.IsMinimal ↔ T.minimalSubtree ⊤ = Set.univ := by
  obtain ⟨g, hg⟩ := hT
  refine ⟨fun hmin => isMinimal_iff.mp hmin _
    (minimalSubtree_nonempty_iff.mpr ⟨g, Subgroup.mem_top g, hg⟩) (isConvex_minimalSubtree T ⊤)
    fun h v hv => (smul_mem_minimalSubtree_iff (Subgroup.mem_top h)).mpr hv,
    fun h => isMinimal_iff.mpr fun C hne hC hGC => ?_⟩
  exact Set.eq_univ_of_univ_subset
    (h ▸ minimalSubtree_subset hC (fun h _ v hv => hGC h v hv) hne)

/-- On the line, the union of the axes of the nontrivial translations is the whole line. -/
@[simp] theorem line_minimalSubtree_top : line.minimalSubtree ⊤ = Set.univ :=
  (isMinimal_iff_minimalSubtree_eq_univ
    ⟨Multiplicative.ofAdd 1, line_isHyperbolic (by decide)⟩).mp line_isMinimal

end GTree
end TauCeti
