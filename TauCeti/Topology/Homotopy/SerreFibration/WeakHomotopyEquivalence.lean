/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

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

in which `p` and `p'` are Serre fibrations (`TauCeti.TopCat.serreFibrations`). If `g` is a weak
homotopy equivalence and, for every point `b` of `B`, the induced map of fibres
`p⁻¹(b) → p'⁻¹(g b)` (`CategoryTheory.CommSq.fiberMap`) is a weak homotopy equivalence, then `f`
is a weak homotopy equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`).

This is the five lemma applied to the exact homotopy sequences of `p` and `p'`, which the boundary
maps make into a map of exact sequences (`TauCeti.TopCat.fibrationBoundary_map`). In positive
degrees the terms around `π_n(E)` are groups and the usual diagram chase applies. At the low end
of the sequences only pointed-set exactness is available, so the bijection on path components is
proved separately: surjectivity by lifting a path in `B'` to `E'`, and injectivity by first moving
both points into one fibre by path lifting, then using exactness at `π_0` of that fibre together
with surjectivity of `g` on fundamental groups. Every fibre is used, not only the fibre over a
chosen base point, since `B` need not be path connected.

Two special cases:

* **Base change along a weak homotopy equivalence.** The base change of a Serre fibration
  `p : E → B` along a weak homotopy equivalence `g : B' → B` has total space weakly equivalent to
  `E` (`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`): the base change has the same
  fibres (`TopCat.Hom.fiberPullbackFstIso`). Pulling back along a CW approximation of the base
  in this way replaces a Serre fibration over an arbitrary base by one over a CW complex,
  without changing the weak homotopy type of the total space.
* **Weakly contractible fibres.** A Serre fibration whose fibres are all path connected, with
  trivial higher homotopy groups, is a weak homotopy equivalence
  (`TauCeti.TopCat.isWeakHomotopyEquivalence_of_forall_fiber`). Nonemptiness of every fibre,
  which is part of path connectedness, is needed: otherwise `p` misses a point of `B`.

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_of_commSq`: a map of Serre fibrations which is a weak
  homotopy equivalence on the bases and on every fibre is one on the total spaces.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`: base change of a Serre fibration along a
  weak homotopy equivalence.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_of_forall_fiber`: a Serre fibration with weakly
  contractible fibres is a weak homotopy equivalence.

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
private theorem map_map_fiberι (hx : f e.1 = x') (w : HomotopyGroup N (p.fiber b) e) :
    HomotopyGroup.map f.hom hx
        (HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) w) =
      HomotopyGroup.map (p'.fiberι (g b)).hom
        ((TopCat.Hom.fiberι_apply p' (g b) _).trans ((sq.fiberMap_apply_coe b e).trans hx))
        (HomotopyGroup.map (sq.fiberMap b).hom rfl w) := by
  rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (congrArg TopCat.Hom.hom (sq.fiberMap_comp_fiberι b)).symm _ _ w

include sq in
/-- On homotopy groups, `p' ∘ f = g ∘ p`. -/
private theorem map_proj_map (hx : f e.1 = x') (hx' : p' x' = g b) (x : HomotopyGroup N E e.1) :
    HomotopyGroup.map p'.hom hx' (HomotopyGroup.map f.hom hx x) =
      HomotopyGroup.map g.hom rfl (HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2) x) := by
  rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (congrArg TopCat.Hom.hom sq.w) _ _ x

variable {sq}

/-- **Surjectivity on positive-dimensional homotopy groups.** The map `f` is surjective on
`π_{n+1}`, at a point of the fibre over `b`. -/
private theorem surjective_map_option (hp : serreFibrations p) (hp' : serreFibrations p')
    [Finite N] (hg : g.hom.IsWeakHomotopyEquivalence)
    (hfib : (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (hx : f e.1 = x') :
    Surjective (HomotopyGroup.map (N := Option N) f.hom hx) := by
  classical
  -- Work at the base point `(sq.fiberMap b e).1 = f e.1` of the exact sequence of `p'`.
  obtain rfl : (sq.fiberMap b e).1 = x' := (sq.fiberMap_apply_coe b e).trans hx
  have hx' := Set.mem_singleton_iff.1 (sq.fiberMap b e).2
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
    (hfib : (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) (hx : f e.1 = x') :
    Injective (HomotopyGroup.map (N := Option N) f.hom hx) := by
  classical
  -- Work at the base point `(sq.fiberMap b e).1 = f e.1` of the exact sequence of `p'`.
  obtain rfl : (sq.fiberMap b e).1 = x' := (sq.fiberMap_apply_coe b e).trans hx
  refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Option N) f.hom hx)).2
    fun x hx1 ↦ ?_
  rw [HomotopyGroup.mapHom_apply] at hx1
  -- The projection of `x` to `B` is trivial, because `g` is injective, so `x` comes from the
  -- fibre of `p`.
  have hpx : HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2) x = 1 := by
    apply (hg.map_bijective (Option N) b).1
    rw [← map_proj_map sq e hx (Set.mem_singleton_iff.1 (sq.fiberMap b e).2), hx1,
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
    (h : Joined (f e.1) (f y.1)) : Joined e.1 y.1 := by
  -- Points of the fibres are zero-dimensional generalized loops, whose classes are their path
  -- components (`homotopyGroupEquivZerothHomotopyOfIsEmpty`).
  let ℓ : Ω^ (Fin 0) (p.fiber b) e := (genLoopHomeoOfIsEmpty (Fin 0) e).symm y
  have hℓ : ℓ 0 = y := genLoopHomeoOfIsEmpty_symm_apply y 0
  -- The image of `y` in the fibre of `p'` is joined to the base point in `E'`, so its class is a
  -- boundary, of an element which comes from `B` since `g` is surjective on `π_1`.
  obtain ⟨y', hy'⟩ : HomotopyGroup.map (sq.fiberMap b).hom rfl (⟦ℓ⟧ : HomotopyGroup _ _ _) ∈
      range (fibrationBoundary hp' (sq.fiberMap b e)) := by
    rw [mem_range_fibrationBoundary_iff hp', HomotopyGroup.map_mk]
    apply (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) _).injective
    rw [homotopyGroupEquivZerothHomotopyOfIsEmpty_map_mk,
      homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply, hℓ,
      TopCat.Hom.fiberι_apply, sq.fiberMap_apply_coe, sq.fiberMap_apply_coe]
    exact ZerothHomotopy.sound h.symm.somePath
  obtain ⟨γ, rfl⟩ := (hg.map_bijective (Option (Fin 0)) b).2 y'
  rw [fibrationBoundary_map sq hp hp'] at hy'
  -- Since the fibre map is injective on `π_0`, the class of `y` itself is a boundary, so it is
  -- joined to the base point in `E`.
  have h0 := (mem_range_fibrationBoundary_iff hp).1 ⟨γ, (hfib.map_bijective (Fin 0) e).1 hy'⟩
  have h1 := congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) e.1) h0
  rw [homotopyGroupEquivZerothHomotopyOfIsEmpty_map_mk,
    homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, hℓ, TopCat.Hom.fiberι_apply] at h1
  exact (Quotient.exact h1).symm

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
  have hyE : Joined (f y.1) (Γ 1) := by
    simpa only [sq.fiberMap_apply_coe] using hy.map continuous_subtype_val
  exact ⟨y.1, hyE.trans (Joined.symm ⟨⟨Γ, hΓ0, rfl⟩⟩)⟩

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
  have h₁ : sq.fiberMap b' = (p.fiberPullbackFstIso g b').hom := by
    ext x
    exact (sq.fiberMap_apply_coe b' x).trans
      ((TopCat.pullbackSnd_apply g p x.1).trans (p.fiberPullbackFstIso_hom_apply_coe g b' x).symm)
  rw [h₁]
  exact (mem_weakEquivalences_iff _).1 (weakEquivalences.of_isIso _)

/-- **A Serre fibration with weakly contractible fibres is a weak homotopy equivalence.** If every
fibre of the Serre fibration `p : E → B` is path connected (in particular nonempty) and has
trivial homotopy groups in positive degrees, then `p` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_of_forall_fiber (hp : serreFibrations p)
    (hconn : ∀ b, PathConnectedSpace (p.fiber b))
    (hπ : ∀ b (x : p.fiber b) n, Subsingleton (HomotopyGroup (Fin (n + 1)) (p.fiber b) x)) :
    p.hom.IsWeakHomotopyEquivalence := by
  let sq : CommSq p p (𝟙 B) (𝟙 B) := ⟨rfl⟩
  refine isWeakHomotopyEquivalence_of_commSq hp (MorphismProperty.id_mem _ B) sq
    ((mem_weakEquivalences_iff _).1 (weakEquivalences.id_mem B)) fun b ↦ ?_
  -- The fibre of the identity is a point, so the fibre map is a weak homotopy equivalence
  -- exactly when the fibre of `p` is weakly contractible.
  have : Subsingleton (TopCat.Hom.fiber (𝟙 B) ((𝟙 B : B ⟶ B) b)) :=
    ⟨fun x y ↦ Subtype.ext <| by
      simpa using (Set.mem_singleton_iff.1 x.2).trans (Set.mem_singleton_iff.1 y.2).symm⟩
  refine ContinuousMap.isWeakHomotopyEquivalence_iff_joined.2
    ⟨fun y ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ y ▸ Joined.refl _⟩,
      fun _ _ _ ↦ PathConnectedSpace.joined _ _, fun n x ↦ ?_⟩
  have := hπ b x n
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩

end TauCeti.TopCat
