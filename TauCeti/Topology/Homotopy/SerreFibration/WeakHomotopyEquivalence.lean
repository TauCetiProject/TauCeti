/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

import TauCeti.Topology.Homotopy.TopCat.Path

/-!
# Weak homotopy equivalences between Serre fibrations

Consider a map of Serre fibrations, that is, a commutative square

```
E --f--> E'
|        |
p        p'
v        v
B --g--> B'
```

in which `p` and `p'` are Serre fibrations (`TauCeti.TopCat.serreFibrations`). When `g` is a weak
homotopy equivalence, `f` is a weak homotopy equivalence if and only if, for every point `b` of
`B`, the induced map of fibres `p⁻¹(b) → p'⁻¹(g b)` (`CategoryTheory.CommSq.fiberMap`) is a weak
homotopy equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap`, combining
`TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq` and
`TauCeti.TopCat.isWeakHomotopyEquivalence_fiberMap`).

This is the five lemma applied to the exact homotopy sequences of `p` and `p'`, which the boundary
maps make into a map of exact sequences (`TauCeti.TopCat.fibrationBoundary_map`). In positive
degrees the terms around `π_n(E)` and `π_n(F)` are groups and the usual diagram chase applies. At
the low end of the sequences only pointed-set exactness is available, so the bijections on path
components are proved separately by path lifting and exactness at `π_0` of the fibre together with
surjectivity and injectivity on fundamental groups. Every fibre is used, not only the fibre over a
chosen base point, since `B` need not be path connected, and empty fibres are handled without
nonemptiness assumptions.

A special case is **base change along a weak homotopy equivalence**. The base change of a Serre
fibration `p : E → B` along a weak homotopy equivalence `g : B' → B` has total space weakly
equivalent to `E` (`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`): the base change has
the same fibres (`TopCat.Hom.fiberPullbackFstIso`). Pulling back along a CW approximation of the
base in this way replaces a Serre fibration over an arbitrary base by one over a CW complex,
without changing the weak homotopy type of the total space.

Another is **restriction over a weakly equivalent subspace**. If the inclusion of subspaces
`S ⊆ T` of the base is a weak homotopy equivalence, so is the inclusion `p⁻¹(S) ⊆ p⁻¹(T)`
(`TauCeti.TopCat.isWeakHomotopyEquivalence_inclusion_preimage`): the restrictions of `p` over `S`
and over `T` are Serre fibrations with the same fibres. For instance the preimage of a
deformation retract of the base is weakly equivalent to the preimage of the ambient subspace.

A third is **base change to a weakly contractible space**. The inclusion of a fibre of a Serre
fibration into its base change along a map `g : K ⟶ B` from a space whose homotopy groups vanish
at `k` (`TopCat.Hom.pullbackFiberι`), is a weak homotopy equivalence
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackFiberι`): it is the inclusion of a fibre of a
Serre fibration over a base with no homotopy. Applying this to a path in `B` connects the fibres
over any two joined points of `B` by a zigzag of weak homotopy equivalences
(`TauCeti.TopCat.exists_isWeakHomotopyEquivalence_fiber_of_joined`), showing in particular that
path-connectedness of the fibre is constant on each path component of `B`
(`TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`).

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`: a map of Serre fibrations which is a weak
  homotopy equivalence on the bases and on every fibre is one on the total spaces.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_fiberMap`: a map of Serre fibrations which is a weak
  homotopy equivalence on the total spaces and on the bases induces a weak homotopy equivalence on
  every fibre.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_iff_forall_fiberMap`: over a weak homotopy equivalence
  of bases, a map of Serre fibrations is a weak homotopy equivalence on total spaces if and only if
  it is one on every fibre.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`: base change of a Serre fibration along a
  weak homotopy equivalence.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_inclusion_preimage`: restriction of a Serre fibration
  over a weakly equivalent subspace.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackFiberι`: the fibre inclusions into a base
  change of a Serre fibration to a weakly contractible space.
* `TauCeti.TopCat.exists_isWeakHomotopyEquivalence_fiber_of_joined`,
  `TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`: fibres of a Serre fibration over joined
  points are connected by a zigzag of weak homotopy equivalences and are simultaneously
  path-connected.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory Function Set
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B E' B' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {f : E ⟶ E'} {g : B ⟶ B'}

/-! ### The comparison of the two exact sequences -/

section Comparison

variable (sq : CommSq f p p' g) {b : B} (e : p.fiber b) {N : Type*} {x' : E'}

/-- On homotopy groups, the fibre inclusion of `p` followed by `f` is the fibre map followed by
the fibre inclusion of `p'`. -/
private theorem map_map_fiberι (hx : f e.val = x') (w : HomotopyGroup N (p.fiber b) e) :
    HomotopyGroup.map f.hom hx
        (HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) w) =
      HomotopyGroup.map (p'.fiberι (g b)).hom
        ((TopCat.Hom.fiberι_apply p' (g b) _).trans ((sq.fiberMap_apply_coe b e).trans hx))
        (HomotopyGroup.map (sq.fiberMap b).hom rfl w) := by
  rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (congrArg TopCat.Hom.hom (sq.fiberMap_comp_fiberι b)).symm _ _ w

include sq in
/-- On homotopy groups, `p' ∘ f = g ∘ p`. -/
private theorem map_proj_map (hx : f e.val = x') (hx' : p' x' = g b) (x : HomotopyGroup N E e.val) :
    HomotopyGroup.map p'.hom hx' (HomotopyGroup.map f.hom hx x) =
      HomotopyGroup.map g.hom rfl (HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.property) x)
          := by
  rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (congrArg TopCat.Hom.hom sq.w) _ _ x

variable {sq}

/-- **Surjectivity on positive-dimensional homotopy groups.** The map `f` is surjective on
`π_{n+1}`, at a point of the fibre over `b`. -/
private theorem surjective_map_option (hp : serreFibrations p) (hp' : serreFibrations p')
    [Finite N] (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (hx : f e.val = x') :
    Surjective (HomotopyGroup.map (N := Option N) f.hom hx) := by
  classical
  -- Work at the base point `(sq.fiberMap b e).1 = f e.1` of the exact sequence of `p'`.
  obtain rfl : (sq.fiberMap b e).val = x' := (sq.fiberMap_apply_coe b e).trans hx
  have hx' := Set.mem_singleton_iff.1 (sq.fiberMap b e).property
  intro x
  -- The projection of `x` to `B'` comes from `B`, by an element `y` whose boundary vanishes,
  -- since it vanishes after applying the fibre map.
  obtain ⟨y, hy⟩ := (hg.map_bijective (Option N) b).2 (HomotopyGroup.map p'.hom hx' x)
  have hy0 : fibrationBoundary hp e y = ⟦GenLoop.const⟧ := by
    apply (hfib.map_bijective N e).1
    rw [← fibrationBoundary_map sq hp hp', hy, HomotopyGroup.map_mk, GenLoop.map_const]
    exact (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp').1 ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).2 hy0
  -- Then `x * (f z)⁻¹` lies over the trivial element, so it comes from the fibre of `p'`, and
  -- hence from the fibre of `p`.
  have hw : HomotopyGroup.map p'.hom hx' (x * (HomotopyGroup.map f.hom hx z)⁻¹) = 1 := by
    rw [HomotopyGroup.map_mul, HomotopyGroup.map_inv, map_proj_map sq e hx hx', hz, hy,
      mul_inv_cancel]
  obtain ⟨w, hw⟩ := (mem_range_homotopyGroupMap_fiberι_iff hp').2
    (hw.trans HomotopyGroup.mk_const_eq_one.symm)
  obtain ⟨v, rfl⟩ := (hfib.map_bijective (Option N) e).2 w
  refine ⟨HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) v * z, ?_⟩
  rw [HomotopyGroup.map_mul, map_map_fiberι sq e hx, hw, inv_mul_cancel_right]

/-- **Injectivity on positive-dimensional homotopy groups.** The map `f` is injective on
`π_{n+1}`, at a point of the fibre over `b`. -/
private theorem injective_map_option (hp : serreFibrations p) (hp' : serreFibrations p')
    [Finite N] (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (hx : f e.val = x') :
    Injective (HomotopyGroup.map (N := Option N) f.hom hx) := by
  classical
  -- Work at the base point `(sq.fiberMap b e).1 = f e.1` of the exact sequence of `p'`.
  obtain rfl : (sq.fiberMap b e).val = x' := (sq.fiberMap_apply_coe b e).trans hx
  refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Option N) f.hom hx)).2
    fun x hx1 ↦ ?_
  rw [HomotopyGroup.mapHom_apply] at hx1
  -- The projection of `x` to `B` is trivial, because `g` is injective, so `x` comes from the
  -- fibre of `p`.
  have hpx : HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.property) x = 1 := by
    apply (hg.map_bijective (Option N) b).1
    rw [← map_proj_map sq e hx (Set.mem_singleton_iff.1 (sq.fiberMap b e).property), hx1,
      HomotopyGroup.map_one, HomotopyGroup.map_one]
  obtain ⟨w, rfl⟩ := (mem_range_homotopyGroupMap_fiberι_iff hp).2
    (hpx.trans HomotopyGroup.mk_const_eq_one.symm)
  -- The image of `w` in the fibre of `p'` dies in `E'`, so it is a boundary, of an element which
  -- comes from `B` since `g` is surjective.
  obtain ⟨y', hy'⟩ : HomotopyGroup.map (sq.fiberMap b).hom rfl w ∈
      range (fibrationBoundary hp' (sq.fiberMap b e)) := by
    rw [mem_range_fibrationBoundary_iff hp', HomotopyGroup.mk_const_eq_one, ← hx1,
      map_map_fiberι sq e hx]
  obtain ⟨y, rfl⟩ := (hg.map_bijective (Option (Option N)) b).2 y'
  rw [fibrationBoundary_map sq hp hp'] at hy'
  -- Since the fibre map is injective, `w` itself is a boundary, so it dies in `E`.
  rw [← (hfib.map_bijective (Option N) e).1 hy', ← HomotopyGroup.mk_const_eq_one]
  exact (mem_range_fibrationBoundary_iff hp).1 ⟨y, rfl⟩

/-- **Injectivity on path components, within a fibre.** Two points of the fibre of `p` over `b`
whose images are joined in `E'` are joined in `E`. -/
private theorem joined_of_joined_map_of_fiber (hp : serreFibrations p)
    (hp' : serreFibrations p') (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (y : p.fiber b)
    (h : Joined (f e.val) (f y.val)) : Joined e.val y.val := by
  -- The image of `y` in the fibre of `p'` is joined to the base point in `E'`, so its class is a
  -- boundary, of an element which comes from `B` since `g` is surjective on `π_1`.
  obtain ⟨y', hy'⟩ := (joined_iff_mem_range_fibrationBoundary hp' (e := sq.fiberMap b e)
    (sq.fiberMap b y)).1 <| by rwa [sq.fiberMap_apply_coe, sq.fiberMap_apply_coe]
  obtain ⟨γ, rfl⟩ := (hg.map_bijective (Option (Fin 0)) b).2 y'
  rw [fibrationBoundary_map sq hp hp'] at hy'
  -- Since the fibre map is injective on `π_0`, the class of `y` itself is a boundary, so it is
  -- joined to the base point in `E`.
  refine (joined_iff_mem_range_fibrationBoundary hp (e := e) y).2
    ⟨γ, (hfib.map_bijective (Fin 0) e).1 (hy'.trans ?_)⟩
  rw [HomotopyGroup.map_mk]
  exact congrArg _ (GenLoop.ext _ _ fun t ↦ by
    rw [GenLoop.map_apply, genLoopHomeoOfIsEmpty_symm_apply, genLoopHomeoOfIsEmpty_symm_apply])

end Comparison

/-! ### Path components -/

section Components

variable {sq : CommSq f p p' g}

/-- **Surjectivity on path components.** Every point of `E'` is joined to a point in the image
of `f`. -/
private theorem exists_joined_of_commSq (hp' : serreFibrations p')
    (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (x' : E') :
    ∃ x, Joined (f x) x' := by
  -- Lift a path from `p' x'` to a point `g b` of the image of `g`, ending in the fibre of `p'`
  -- over `g b`, and use surjectivity of the fibre map on path components.
  obtain ⟨b, hb⟩ := hg.exists_joined (p' x')
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp' hb.somePath.symm
  have hΓ1 : p' (Γ 1) = g b := (congrFun hΓ 1).trans hb.somePath.symm.target
  obtain ⟨y, hy⟩ := (hfib b).exists_joined ⟨Γ 1, hΓ1⟩
  have hyE : Joined (f y.val) (Γ 1) := by
    simpa only [sq.fiberMap_apply_coe] using hy.map continuous_subtypeVal
  exact ⟨y.val, hyE.trans (Joined.symm ⟨⟨Γ, hΓ0, rfl⟩⟩)⟩

/-- **Injectivity on path components.** Two points of `E` whose images are joined in `E'` are
joined in `E`. -/
private theorem joined_of_joined_map (hp : serreFibrations p) (hp' : serreFibrations p')
    (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) {a₁ a₂ : E}
    (h : Joined (f a₁) (f a₂)) : Joined a₁ a₂ := by
  -- The images of `a₂` and `a₁` in `B` are joined, since `g` is injective on path components.
  have hpa : Joined (p a₂) (p a₁) := by
    rw [← hg.joined_iff]
    have hw (a : E) : g (p a) = p' (f a) := (ConcreteCategory.congr_hom sq.w a).symm
    rw [hw, hw]
    exact h.symm.map p'.hom.continuous
  -- Lifting a path between them moves `a₂` into the fibre of `p` over `p a₁`.
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp hpa.somePath
  have hΓ1 : p (Γ 1) = p a₁ := (congrFun hΓ 1).trans hpa.somePath.target
  have h₂ : Joined a₂ (Γ 1) := ⟨⟨Γ, hΓ0, rfl⟩⟩
  exact (joined_of_joined_map_of_fiber ⟨a₁, rfl⟩ hp hp' hg (hfib (p a₁)) ⟨Γ 1, hΓ1⟩
    (h.trans (h₂.map f.hom.continuous))).trans h₂.symm

end Components

/-! ### The comparison theorem -/

/-- **A map of Serre fibrations which is a weak homotopy equivalence on the bases and on every
fibre is a weak homotopy equivalence on the total spaces.** For a commutative square
`f ≫ p' = p ≫ g` of Serre fibrations `p : E → B` and `p' : E' → B'`, if `g` is a weak homotopy
equivalence and so is the induced map `p⁻¹(b) → p'⁻¹(g b)` for every `b : B`, then `f` is a weak
homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_of_commSq (hp : serreFibrations p) (hp' : serreFibrations p')
    (sq : CommSq f p p' g) (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) :
    f.hom.IsWeakHomotopyEquivalence := by
  refine ContinuousMap.isWeakHomotopyEquivalence_iff_joined.2
    ⟨exists_joined_of_commSq hp' hg hfib, fun _ _ ↦ joined_of_joined_map hp hp' hg hfib,
      fun n a ↦ ?_⟩
  -- The exact sequences index `π_{n+1}` by `Option (Fin n)`; reindex along `Fin (n + 1)`.
  exact (HomotopyGroup.bijective_map_iff_of_equiv f.hom rfl (finSuccEquiv n).symm).1
    ⟨injective_map_option ⟨a, rfl⟩ hp hp' hg (hfib (p a)) rfl,
      surjective_map_option ⟨a, rfl⟩ hp hp' hg (hfib (p a)) rfl⟩

section FiberComparison

variable (sq : CommSq f p p' g) {b : B}

/-- **Injectivity on positive-dimensional homotopy groups of the fibre.** -/
private theorem injective_fiberMap_option (hp : serreFibrations p) (hp' : serreFibrations p')
    {N : Type*} [Finite N] (hf : f.hom.IsWeakHomotopyEquivalence)
    (hg : g.hom.IsWeakHomotopyEquivalence) (e : p.fiber b) :
    Injective (HomotopyGroup.map (N := Option N) (sq.fiberMap b).hom
      (rfl : sq.fiberMap b e = sq.fiberMap b e)) := by
  classical
  have hx : f e.val = (sq.fiberMap b e).val := (sq.fiberMap_apply_coe b e).symm
  refine (injective_iff_map_eq_one
    (HomotopyGroup.mapHom (N := Option N) (sq.fiberMap b).hom
      (rfl : sq.fiberMap b e = sq.fiberMap b e))).2 fun w hw1 ↦ ?_
  rw [HomotopyGroup.mapHom_apply] at hw1
  have hfw : HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) w = 1 := by
    apply ((HomotopyGroup.bijective_map_congr (rfl : f.hom = f.hom) hx rfl).2
      (hf.map_bijective (Option N) e.val)).1
    rw [map_map_fiberι sq e hx, hw1, HomotopyGroup.map_one, HomotopyGroup.map_one]
  obtain ⟨y, rfl⟩ := (mem_range_fibrationBoundary_iff hp).2
    (hfw.trans HomotopyGroup.mk_const_eq_one.symm)
  have hgy : fibrationBoundary hp' (sq.fiberMap b e) (HomotopyGroup.map g.hom rfl y) =
      ⟦GenLoop.const⟧ := by
    rw [fibrationBoundary_map sq hp hp', hw1, HomotopyGroup.mk_const_eq_one]
  obtain ⟨z', hz'⟩ := (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp').2 hgy
  obtain ⟨z, rfl⟩ := ((HomotopyGroup.bijective_map_congr (rfl : f.hom = f.hom) hx rfl).2
    (hf.map_bijective (Option (Option N)) e.val)).2 z'
  have hpz : HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.property) z = y := by
    apply (hg.map_bijective (Option (Option N)) b).1
    rw [← map_proj_map sq e hx (Set.mem_singleton_iff.1 (sq.fiberMap b e).property), hz']
  exact ((mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).1 ⟨z, hpz⟩).trans
    HomotopyGroup.mk_const_eq_one

/-- **Surjectivity on positive-dimensional homotopy groups of the fibre.** -/
private theorem surjective_fiberMap_option (hp : serreFibrations p) (hp' : serreFibrations p')
    {N : Type*} [Finite N] (hf : f.hom.IsWeakHomotopyEquivalence)
    (hg : g.hom.IsWeakHomotopyEquivalence) (e : p.fiber b) :
    Surjective (HomotopyGroup.map (N := Option N) (sq.fiberMap b).hom
      (rfl : sq.fiberMap b e = sq.fiberMap b e)) := by
  classical
  have hx : f e.val = (sq.fiberMap b e).val := (sq.fiberMap_apply_coe b e).symm
  have hxι : p'.fiberι (g b) (sq.fiberMap b e) = (sq.fiberMap b e).val :=
    TopCat.Hom.fiberι_apply p' (g b) (sq.fiberMap b e)
  intro w'
  obtain ⟨z, hz⟩ := ((HomotopyGroup.bijective_map_congr (rfl : f.hom = f.hom) hx rfl).2
    (hf.map_bijective (Option N) e.val)).2
    (HomotopyGroup.map (p'.fiberι (g b)).hom hxι w')
  have hpz : HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.property) z = 1 := by
    apply (hg.map_bijective (Option N) b).1
    rw [← map_proj_map sq e hx (Set.mem_singleton_iff.1 (sq.fiberMap b e).property), hz,
      HomotopyGroup.map_one]
    exact ((mem_range_homotopyGroupMap_fiberι_iff hp').1 ⟨w', rfl⟩).trans
      HomotopyGroup.mk_const_eq_one
  obtain ⟨v, rfl⟩ := (mem_range_homotopyGroupMap_fiberι_iff hp).2
    (hpz.trans HomotopyGroup.mk_const_eq_one.symm)
  have hu' : HomotopyGroup.map (p'.fiberι (g b)).hom hxι
      (w' * (HomotopyGroup.map (sq.fiberMap b).hom rfl v)⁻¹) = 1 := by
    rw [HomotopyGroup.map_mul, HomotopyGroup.map_inv, ← map_map_fiberι sq e hx, hz,
      mul_inv_cancel]
  obtain ⟨y', hy'⟩ := (mem_range_fibrationBoundary_iff hp').2
    (hu'.trans HomotopyGroup.mk_const_eq_one.symm)
  obtain ⟨y, rfl⟩ := (hg.map_bijective (Option (Option N)) b).2 y'
  rw [fibrationBoundary_map sq hp hp'] at hy'
  refine ⟨fibrationBoundary hp e y * v, ?_⟩
  rw [HomotopyGroup.map_mul, hy', inv_mul_cancel_right]

/-- **Surjectivity on path components of the fibre.** -/
private theorem exists_joined_fiberMap (hp : serreFibrations p) (hp' : serreFibrations p')
    (hf : f.hom.IsWeakHomotopyEquivalence) (hg : g.hom.IsWeakHomotopyEquivalence)
    (y' : p'.fiber (g b)) : ∃ x, Joined (sq.fiberMap b x) y' := by
  obtain ⟨e₀, he₀⟩ := hf.exists_joined y'.val
  have hpb : Joined (p e₀) b := by
    rw [← hg.joined_iff]
    have hw : g (p e₀) = p' (f e₀) := (ConcreteCategory.congr_hom sq.w e₀).symm
    rw [hw, ← Set.mem_singleton_iff.1 y'.property]
    exact he₀.map p'.hom.continuous
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp hpb.somePath
  let e : p.fiber b := ⟨Γ 1, (congrFun hΓ 1).trans hpb.somePath.target⟩
  have he_join : Joined e₀ e.val := ⟨⟨Γ, hΓ0, rfl⟩⟩
  have hy'E : Joined (sq.fiberMap b e).val y'.val := by
    rw [sq.fiberMap_apply_coe]
    exact (he_join.symm.map f.hom.continuous).trans he₀
  obtain ⟨γ', hγ'⟩ :=
    (joined_iff_mem_range_fibrationBoundary hp' (e := sq.fiberMap b e) y').1 hy'E
  obtain ⟨γ, rfl⟩ := (hg.map_bijective (Option (Fin 0)) b).2 γ'
  rw [fibrationBoundary_map sq hp hp'] at hγ'
  rcases Quotient.exists_rep (fibrationBoundary hp e γ) with ⟨β, hβ⟩
  rw [← hβ, HomotopyGroup.map_mk] at hγ'
  refine ⟨β 0, ?_⟩
  have h₀ := HomotopyGroup.mk_eq_mk_iff_joined.1 hγ'
  rwa [GenLoop.map_apply, genLoopHomeoOfIsEmpty_symm_apply] at h₀

/-- **Injectivity on path components of the fibre.** -/
private theorem joined_of_joined_fiberMap (hp : serreFibrations p) (hp' : serreFibrations p')
    (hf : f.hom.IsWeakHomotopyEquivalence) (hg : g.hom.IsWeakHomotopyEquivalence)
    {x₁ x₂ : p.fiber b} (h : Joined (sq.fiberMap b x₁) (sq.fiberMap b x₂)) : Joined x₁ x₂ := by
  have hx₁ : f x₁.val = (sq.fiberMap b x₁).val := (sq.fiberMap_apply_coe b x₁).symm
  have hxE : Joined x₁.val x₂.val :=
    hf.joined_iff.1 (by simpa only [sq.fiberMap_apply_coe] using h.map continuous_subtypeVal)
  obtain ⟨γ, hγ⟩ := (joined_iff_mem_range_fibrationBoundary hp (e := x₁) x₂).1 hxE
  have hγ' : fibrationBoundary hp' (sq.fiberMap b x₁) (HomotopyGroup.map g.hom rfl γ) =
      ⟦GenLoop.const⟧ := by
    rw [fibrationBoundary_map sq hp hp', hγ, HomotopyGroup.map_mk]
    refine HomotopyGroup.mk_eq_mk_iff_joined.2 ?_
    rw [GenLoop.map_apply, genLoopHomeoOfIsEmpty_symm_apply, GenLoop.const_apply]
    exact h.symm
  obtain ⟨z', hz'⟩ := (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp').2 hγ'
  obtain ⟨z, rfl⟩ := ((HomotopyGroup.bijective_map_congr (rfl : f.hom = f.hom) hx₁ rfl).2
    (hf.map_bijective (Option (Fin 0)) x₁.val)).2 z'
  have hpz : HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 x₁.property) z = γ := by
    apply (hg.map_bijective (Option (Fin 0)) b).1
    rw [← map_proj_map sq x₁ hx₁ (Set.mem_singleton_iff.1 (sq.fiberMap b x₁).property), hz']
  have hγ0 :=
    ((mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).1 ⟨z, hpz⟩).symm.trans hγ
  have h₂₁ := HomotopyGroup.mk_eq_mk_iff_joined.1 hγ0
  rw [GenLoop.const_apply, genLoopHomeoOfIsEmpty_symm_apply] at h₂₁
  exact h₂₁

end FiberComparison

/-- **A map of Serre fibrations which is a weak homotopy equivalence on the total spaces and on the
bases induces a weak homotopy equivalence on every fibre.** Empty fibres are covered without extra
hypotheses. -/
theorem isWeakHomotopyEquivalence_fiberMap (hp : serreFibrations p) (hp' : serreFibrations p')
    (sq : CommSq f p p' g) (hf : f.hom.IsWeakHomotopyEquivalence)
    (hg : g.hom.IsWeakHomotopyEquivalence) (b : B) :
    (sq.fiberMap b).hom.IsWeakHomotopyEquivalence := by
  refine ContinuousMap.isWeakHomotopyEquivalence_iff_joined.2
    ⟨exists_joined_fiberMap sq hp hp' hf hg, fun _ _ ↦ joined_of_joined_fiberMap sq hp hp' hf hg,
      fun n e ↦ ?_⟩
  exact (HomotopyGroup.bijective_map_iff_of_equiv (sq.fiberMap b).hom rfl
    (finSuccEquiv n).symm).1
    ⟨injective_fiberMap_option sq hp hp' hf hg e,
      surjective_fiberMap_option sq hp hp' hf hg e⟩

/-- **Over a weak homotopy equivalence of bases, a map of Serre fibrations is a weak homotopy
equivalence on total spaces if and only if it is one on every fibre.** -/
theorem isWeakHomotopyEquivalence_iff_forall_fiberMap (hp : serreFibrations p)
    (hp' : serreFibrations p') (sq : CommSq f p p' g) (hg : g.hom.IsWeakHomotopyEquivalence) :
    f.hom.IsWeakHomotopyEquivalence ↔ ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence :=
  ⟨fun hf b ↦ isWeakHomotopyEquivalence_fiberMap hp hp' sq hf hg b,
    isWeakHomotopyEquivalence_of_commSq hp hp' sq hg⟩

/-- **Base change of a Serre fibration along a weak homotopy equivalence.** If `p : E → B` is a
Serre fibration and `g : B' → B` a weak homotopy equivalence, the projection
`B' ×_B E → E` of the base change of `p` along `g` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_pullbackSnd (hp : serreFibrations p) {B' : TopCat.{u}}
    {g : B' ⟶ B} (hg : g.hom.IsWeakHomotopyEquivalence) :
    (TopCat.pullbackSnd g p).hom.IsWeakHomotopyEquivalence := by
  let sq : CommSq (TopCat.pullbackSnd g p) (TopCat.pullbackFst g p) p g :=
    (IsPullback.of_isLimit (TopCat.pullbackConeIsLimit g p)).flip.toCommSq
  refine isWeakHomotopyEquivalence_of_commSq (mem_serreFibrations_pullbackFst hp g) hp sq hg
    fun b' ↦ ?_
  -- The base change has the same fibres as `p`, by the homeomorphism `fiberPullbackFstIso`.
  rw [sq.fiberMap_pullbackSnd b']
  exact (mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso _)

/-- **Restriction of a Serre fibration over a weakly equivalent subspace.** If `p : E ⟶ B` is a
Serre fibration and `S ⊆ T` are subspaces of `B` whose inclusion is a weak homotopy equivalence,
then the inclusion `p⁻¹(S) ⊆ p⁻¹(T)` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_inclusion_preimage (hp : serreFibrations p) {S T : Set B}
    (hST : S ⊆ T) (h : (ContinuousMap.inclusion hST).IsWeakHomotopyEquivalence) :
    (ContinuousMap.inclusion
      (preimage_mono hST : p ⁻¹' S ⊆ p ⁻¹' T)).IsWeakHomotopyEquivalence := by
  let sq : CommSq (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono hST : p ⁻¹' S ⊆ p ⁻¹' T)))
      (TopCat.ofHom (p.hom.restrictPreimage S)) (TopCat.ofHom (p.hom.restrictPreimage T))
      (TopCat.ofHom (ContinuousMap.inclusion hST)) := ⟨rfl⟩
  refine isWeakHomotopyEquivalence_of_commSq (mem_serreFibrations_restrictPreimage hp S)
    (mem_serreFibrations_restrictPreimage hp T) sq h fun b ↦ ?_
  -- Both fibres over `b` consist of the points of `E` over `b`, so the fibre map is invertible.
  have hy (y : (TopCat.ofHom (p.hom.restrictPreimage T)).fiber (ContinuousMap.inclusion hST b)) :
      p y.val.val = b.val :=
    congrArg Subtype.val (mem_singleton_iff.1 y.property)
  have : IsIso (sq.fiberMap b) :=
    ⟨TopCat.ofHom ⟨fun y ↦ ⟨⟨y.val.val, by simp [hy y]⟩, Subtype.ext (hy y)⟩,
      by fun_prop⟩,
      by ext x; simpa using congrArg Subtype.val (sq.fiberMap_apply_coe b x),
      by ext x; simpa using congrArg Subtype.val (sq.fiberMap_apply_coe b _)⟩
  exact (mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso (sq.fiberMap b))

/-- **Fibre inclusions over a weakly contractible base are weak homotopy equivalences.** If `p` is
a Serre fibration and every homotopy group of `K` at `k` vanishes, the inclusion of the fibre of `p`
over `g k` into the base change of `p` along `g : K ⟶ B`, at `k`, is a weak homotopy
equivalence. -/
theorem isWeakHomotopyEquivalence_pullbackFiberι (hp : serreFibrations p) {K : TopCat.{u}}
    (g : K ⟶ B) {k : K} {b : B} (h : g k = b) (hK : ∀ n, Subsingleton (π_ n K k)) :
    (p.pullbackFiberι g h).hom.IsWeakHomotopyEquivalence := by
  subst h
  -- Up to the identification of the fibres of the base change, this is the inclusion of the fibre
  -- of the base change over `k`, which is a weak equivalence since `K` has no homotopy.
  rw [TopCat.Hom.pullbackFiberι_eq_fiberPullbackFstIso_inv_comp_fiberι, TopCat.hom_comp]
  refine ContinuousMap.IsWeakHomotopyEquivalence.comp ?_
    ((mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso _))
  exact isWeakHomotopyEquivalence_fiberι_of_mem_serreFibrations
    (mem_serreFibrations_pullbackFst hp g) hK

/-- **Fibres of a Serre fibration over joined points are connected by a zigzag of weak homotopy
equivalences**, through the pullback of `p` along a path between them. -/
theorem exists_isWeakHomotopyEquivalence_fiber_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) :
    ∃ (P : TopCat.{u}) (f₀ : p.fiber b₀ ⟶ P) (f₁ : p.fiber b₁ ⟶ P),
      f₀.hom.IsWeakHomotopyEquivalence ∧ f₁.hom.IsWeakHomotopyEquivalence :=
  let γ := _root_.TopCat.pathEquiv.symm hb.somePath
  ⟨_, p.pullbackFiberι γ.hom γ.hom₀, p.pullbackFiberι γ.hom γ.hom₁,
    isWeakHomotopyEquivalence_pullbackFiberι hp γ.hom γ.hom₀ fun _ ↦ inferInstance,
    isWeakHomotopyEquivalence_pullbackFiberι hp γ.hom γ.hom₁ fun _ ↦ inferInstance⟩

/-- **Fibres of a Serre fibration over points in the same path component are simultaneously
path-connected.** -/
theorem pathConnectedSpace_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) : PathConnectedSpace (p.fiber b₀) ↔ PathConnectedSpace (p.fiber b₁) := by
  obtain ⟨_, _, _, h₀, h₁⟩ := exists_isWeakHomotopyEquivalence_fiber_of_joined hp hb
  exact h₀.pathConnectedSpace_iff.trans h₁.pathConnectedSpace_iff.symm

end TauCeti.TopCat
