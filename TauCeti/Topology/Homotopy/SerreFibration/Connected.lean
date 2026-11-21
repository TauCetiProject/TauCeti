/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

import Mathlib.Analysis.Convex.Contractible

/-!
# Connectivity of a Serre fibration and of its fibres

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`). Then `p` is an
`n`-connected map (`ContinuousMap.IsNConnected`) exactly when every fibre `p⁻¹(b)` is nonempty
and `(n - 1)`-connected, that is, when `π_k(p⁻¹(b), e)` is trivial for every `k < n` and every
point `e` of the fibre (`TauCeti.TopCat.isNConnected_iff_of_mem_serreFibrations`). In particular
`p` is a weak homotopy equivalence exactly when every fibre is nonempty and weakly contractible
(`TauCeti.TopCat.isWeakHomotopyEquivalence_iff_of_mem_serreFibrations`).

The hypothesis is on every fibre. A condition on a single fibre says nothing about the path
components of `B` that do not contain its base point, and nonemptiness of the fibres is part of
the hypothesis: the empty map to a nonempty space is a Serre fibration, and its fibres have no
points at which to evaluate homotopy groups.

Dually, over an `n`-connected base the fibre is `n`-connected in the total space: if `π_k(B, b)` is
trivial for every `k ≤ n` (for `k = 0` this says that `B` is path-connected), then the inclusion
of the fibre `p⁻¹(b) → E` is an `n`-connected map
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). In particular, over a weakly
contractible base the fibre inclusion is a weak homotopy equivalence
(`TopCat.isWeakHomotopyEquivalence_fiberι_of_mem_serreFibrations`), so pulling back `p`
along a map from a weakly contractible space yields a weak homotopy equivalence from each fibre
into the pullback (`TopCat.isWeakHomotopyEquivalence_fiberPullback`). Applying this to a
path in `B` connects the fibres over any two joined points of `B` by a zigzag of weak homotopy
equivalences (`TopCat.exists_isWeakHomotopyEquivalence_fiber_of_joined`), showing in
particular that path-connectedness of the fibre is constant on each path component of `B`
(`TopCat.pathConnectedSpace_fiber_iff_of_joined`). In the opposite range, where the
base has no homotopy, the fibre inclusion is bijective: if `π_{k+1}(B, b)` and `π_{k+2}(B, b)` are
trivial, it induces a bijection `π_{k+1}(p⁻¹(b)) → π_{k+1}(E)`
(`TauCeti.TopCat.bijective_homotopyGroupMap_fiberι_of_mem_serreFibrations`).

## Implementation notes

Both directions read the long exact homotopy sequence of the fibration
(`TauCeti.TopCat.mem_range_fibrationBoundary_iff`,
`TauCeti.TopCat.mem_range_homotopyGroupMap_fiberι_iff`,
`TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`). At its low end, where
`π_0` is only a pointed set, the comparisons go through path components
(`HomotopyGroup.map_injective_of_isEmpty_of_joined`,
`HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined`), and path lifting supplies them: a
path in `B` between the projections of two points of `E` lifts to a path from the first point into
the fibre of the second (`TauCeti.TopCat.joined_of_mem_serreFibrations`), and a path from the image
of `p` to a point `b` lifts to a point of the fibre over `b`
(`TauCeti.TopCat.nonempty_fiber_of_mem_serreFibrations`).

## Main results

* `TauCeti.TopCat.isNConnected_iff_of_mem_serreFibrations`: a Serre fibration is `n`-connected
  exactly when its fibres are nonempty and `(n - 1)`-connected.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_iff_of_mem_serreFibrations`: a Serre fibration is a
  weak homotopy equivalence exactly when its fibres are nonempty and weakly contractible.
* `TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`: over an `n`-connected base, the
  inclusion of a fibre is `n`-connected.
* `TopCat.isWeakHomotopyEquivalence_fiberι_of_mem_serreFibrations`,
  `TopCat.isWeakHomotopyEquivalence_fiberPullback`: over a weakly contractible base (or
  pullback along a map from one), the fibre inclusion is a weak homotopy equivalence.
* `TopCat.exists_isWeakHomotopyEquivalence_fiber_of_joined`,
  `TopCat.pathConnectedSpace_fiber_iff_of_joined`: fibres of a Serre fibration over joined
  points are connected by a zigzag of weak homotopy equivalences and are simultaneously
  path-connected.
* `TauCeti.TopCat.bijective_homotopyGroupMap_fiberι_of_mem_serreFibrations`: where the homotopy
  groups of the base vanish, the inclusion of a fibre is bijective on homotopy groups.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {n : ℕ}

/-- A Serre fibration whose fibres are nonempty and `(n - 1)`-connected is `n`-connected. -/
private theorem isNConnected_of_forall_fiber (hp : serreFibrations p)
    (hF : ∀ b, Nonempty (p.fiber b) ∧
      ∀ (e : p.fiber b) k, k < n → Subsingleton (π_ k (p.fiber b) e)) :
    p.hom.IsNConnected n := by
  classical
  refine ⟨fun b ↦ ?_, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · -- Every fibre is nonempty, so `p` is surjective.
    obtain ⟨e⟩ := (hF b).1
    have he : p.hom e.val = b := Set.mem_singleton_iff.1 e.property
    exact ⟨e.val, by rw [he]⟩
  · cases k with
    | zero =>
      -- In degree zero, homotopy classes are path components, and paths lift into the fibre.
      refine HomotopyGroup.map_injective_of_isEmpty_of_joined _ rfl fun a c h ↦ ?_
      have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (⟨c, rfl⟩ : p.fiber (p c))).2
        ((hF _).2 _ 0 hk)
      exact joined_of_mem_serreFibrations hp h
    | succ k =>
      -- In positive degrees the induced map is a homomorphism, and by exactness at `π_k(E)` its
      -- kernel comes from the trivial group `π_k(F)`.
      have := (hF (p x)).2 ⟨x, rfl⟩ (k + 1) hk
      exact injective_homotopyGroupMap_of_subsingleton (N := Fin (k + 1)) hp (e := ⟨x, rfl⟩)
  · cases k with
    | zero =>
      -- In degree zero, every point of `B` is the projection of a point of its fibre.
      refine HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined _ rfl fun b ↦ ?_
      obtain ⟨e⟩ := (hF b).1
      exact ⟨e.val, by rw [Set.mem_singleton_iff.1 e.property]⟩
    | succ k =>
      -- Split off the first direction: by exactness at `π_{k+1}(B)`, a class lifts to `E` since
      -- its boundary lies in the trivial group `π_k(F)`.
      have := (hF (p x)).2 ⟨x, rfl⟩ k hk
      let φ := (finSuccEquiv k).symm
      intro c
      obtain ⟨a, ha⟩ := surjective_homotopyGroupMap_of_subsingleton hp (e := ⟨x, rfl⟩)
        ((HomotopyGroup.congrEquiv φ).symm c)
      exact ⟨HomotopyGroup.congrEquiv φ a,
        (HomotopyGroup.map_congrEquiv _ _ φ a).trans ((Equiv.eq_symm_apply _).1 ha)⟩

/-- The fibres of an `n`-connected Serre fibration are `(n - 1)`-connected. -/
private theorem subsingleton_homotopyGroup_fiber (hp : serreFibrations p)
    (hf : p.hom.IsNConnected n) {b : B} (e : p.fiber b) {k : ℕ} (hk : k < n) :
    Subsingleton (π_ k (p.fiber b) e) := by
  obtain ⟨x, hx⟩ := e
  obtain rfl : p x = b := Set.mem_singleton_iff.1 hx
  suffices h : ∀ a : π_ k (p.fiber (p x)) ⟨x, hx⟩, a = ⟦GenLoop.const⟧ from
    ⟨fun a c ↦ (h a).trans (h c).symm⟩
  intro a
  -- The image of `a` in `π_k(E)` projects trivially, and `p` is injective on `π_k`.
  have h₁ : HomotopyGroup.map (p.fiberι (p x)).hom (TopCat.Hom.fiberι_apply p (p x) ⟨x, hx⟩) a =
      ⟦GenLoop.const⟧ := by
    apply hf.map_injective (Fin k) (by simpa using hk) x
    exact ((mem_range_homotopyGroupMap_fiberι_iff hp).1 ⟨a, rfl⟩).trans
      (by rw [HomotopyGroup.map_mk, GenLoop.map_const])
  -- So `a` is the boundary of a class of `π_{k+1}(B)`, which lifts to `E` since `p` is surjective
  -- on `π_{k+1}`; the boundary of a lifted class is trivial.
  obtain ⟨c, rfl⟩ := (mem_range_fibrationBoundary_iff hp).2 h₁
  obtain ⟨d, rfl⟩ := hf.map_surjective (Option (Fin k)) (by simpa using hk) x c
  exact (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).1 ⟨d, rfl⟩

/-- **A Serre fibration is `n`-connected exactly when its fibres are nonempty and
`(n - 1)`-connected.** For a Serre fibration `p : E → B`, the map `p` is `n`-connected exactly
when, for every `b : B`, the fibre `p⁻¹(b)` is nonempty and `π_k(p⁻¹(b), e)` is trivial for every
`k < n` and every point `e` of the fibre. For `k = 0` this says that the fibre is path-connected,
and for `n = 0` the condition is that every fibre is nonempty. -/
theorem isNConnected_iff_of_mem_serreFibrations (hp : serreFibrations p) (n : ℕ) :
    p.hom.IsNConnected n ↔ ∀ b, Nonempty (p.fiber b) ∧
      ∀ (e : p.fiber b) k, k < n → Subsingleton (π_ k (p.fiber b) e) :=
  ⟨fun hf b ↦ ⟨(hf.exists_joined b).elim fun _ ↦ nonempty_fiber_of_mem_serreFibrations hp,
      fun e _ hk ↦ subsingleton_homotopyGroup_fiber hp hf e hk⟩,
    isNConnected_of_forall_fiber hp⟩

/-- **A Serre fibration is a weak homotopy equivalence exactly when its fibres are nonempty and
weakly contractible.** For a Serre fibration `p : E → B`, the map `p` is a weak homotopy
equivalence exactly when, for every `b : B`, the fibre `p⁻¹(b)` is nonempty and every homotopy
group `π_k(p⁻¹(b), e)`, including the set `π_0` of path components, is trivial. -/
theorem isWeakHomotopyEquivalence_iff_of_mem_serreFibrations (hp : serreFibrations p) :
    p.hom.IsWeakHomotopyEquivalence ↔ ∀ b, Nonempty (p.fiber b) ∧
      ∀ (e : p.fiber b) k, Subsingleton (π_ k (p.fiber b) e) := by
  simp_rw [ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected,
    isNConnected_iff_of_mem_serreFibrations hp]
  exact ⟨fun h b ↦ ⟨(h 0 b).1, fun e k ↦ (h (k + 1) b).2 e k (Nat.lt_add_one k)⟩,
    fun h _ b ↦ ⟨(h b).1, fun e k _ ↦ (h b).2 e k⟩⟩

/-! ### The fibre inclusion over a highly connected base -/

section FiberInclusion

variable {b : B}

/-- The fibre inclusion `p⁻¹(b) → E` as the inclusion of a subspace. Unlike
`ContinuousMap.subtypeVal (p ⁻¹' {b})`, whose domain is `Set.Elem` with the subtype topology, its
domain is the `TopCat` fibre `p.fiber b`, so it matches `p.fiberι b` and the homotopy groups of
`p.fiber b` under `rw`, and its value at `e` reduces to `e.1`. -/
private abbrev fiberVal (p : E ⟶ B) (b : B) : C(p.fiber b, E) :=
  ⟨Subtype.val, continuous_subtypeVal⟩

private theorem fiberι_hom_eq_fiberVal : (p.fiberι b).hom = fiberVal p b :=
  ContinuousMap.ext (TopCat.Hom.fiberι_apply p b)

/-- The map induced by the fibre inclusion on homotopy groups, read through `fiberVal`, whose
value at a point of the fibre is the underlying point of `E`. -/
private theorem homotopyGroupMap_fiberι_eq {N : Type*} {e : p.fiber b}
    (a : HomotopyGroup N (p.fiber b) e) :
    HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) a =
      HomotopyGroup.map (fiberVal p b) rfl a :=
  HomotopyGroup.map_congr fiberι_hom_eq_fiberVal _ _ a

/-- **Injectivity on path components of the fibre inclusion.** If `π_1(B, b)` is trivial, two
points of the fibre over `b` that are joined in `E` are joined in the fibre. -/
private theorem joined_of_joined_fiberι (hp : serreFibrations p) (hB : Subsingleton (π_ 1 B b))
    {e y : p.fiber b} (h : Joined e.val y.val) : Joined e y := by
  -- The point `y` is joined to `e` in `E`, so its class is a boundary.
  obtain ⟨c, hc⟩ := (joined_iff_mem_range_fibrationBoundary hp y).1 h
  -- Since `π_1(B, b)` is trivial, it is the boundary of the constant loop, which is constant.
  have : Subsingleton (HomotopyGroup (Option (Fin 0)) B b) :=
    (HomotopyGroup.congrEquiv (finSuccEquiv 0).symm).subsingleton
  rw [Subsingleton.elim c ⟦GenLoop.const⟧, fibrationBoundary_const] at hc
  have h1 := HomotopyGroup.mk_eq_mk_iff_joined.1 hc
  rw [GenLoop.const_apply, genLoopHomeoOfIsEmpty_symm_apply] at h1
  exact h1

/-- Every point of `E` is joined to a point of the fibre over `b` when `B` is path-connected: lift
a path from its projection to `b`. -/
private theorem exists_joined_fiberι (hp : serreFibrations p) [PathConnectedSpace B] (x : E) :
    ∃ y : p.fiber b, Joined (fiberVal p b y) x := by
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp
    (PathConnectedSpace.somePath (p x) b)
  refine ⟨⟨Γ 1, (congrFun hΓ 1).trans (PathConnectedSpace.somePath (p x) b).target⟩, ?_⟩
  exact Joined.symm ⟨⟨Γ, hΓ0, rfl⟩⟩

/-- **The fibre of a Serre fibration over an `n`-connected base is `n`-connected in the total
space.** Let `p : E → B` be a Serre fibration and `b : B` a point such that `π_k(B, b)` is trivial
for every `k ≤ n`; for `k = 0` this says that `B` is path-connected. Then the inclusion of the
fibre `p⁻¹(b) → E` is an `n`-connected map: it induces isomorphisms `π_k(p⁻¹(b)) → π_k(E)` for
`k < n` and surjections for `k = n`, and every point of `E` is joined to the fibre. -/
theorem isNConnected_fiberι_of_mem_serreFibrations (hp : serreFibrations p) {n : ℕ}
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) : (p.fiberι b).hom.IsNConnected n := by
  classical
  have : PathConnectedSpace B :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero b).2 (hB 0 n.zero_le)
  rw [fiberι_hom_eq_fiberVal]
  refine ⟨fun x ↦ exists_joined_fiberι hp x, fun k hk e ↦ ?_, fun k hk e ↦ ?_⟩
  · cases k with
    | zero =>
      -- In degree zero, homotopy classes are path components.
      exact HomotopyGroup.map_injective_of_isEmpty_of_joined _ rfl fun a c h ↦
        joined_of_joined_fiberι hp (hB 1 hk) h
    | succ k =>
      -- In positive degrees the induced map is a homomorphism, and by exactness at `π_k(F)` its
      -- kernel consists of boundaries of classes of the trivial group `π_{k+1}(B, b)`.
      have : Subsingleton (HomotopyGroup (Option (Fin (k + 1))) B b) :=
        @Equiv.subsingleton _ _ (HomotopyGroup.congrEquiv (finSuccEquiv (k + 1)).symm)
          (hB (k + 2) hk)
      refine (injective_iff_map_eq_one
        (HomotopyGroup.mapHom (N := Fin (k + 1)) (x := e) (fiberVal p b) rfl)).2 fun c hc ↦ ?_
      rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one,
        ← homotopyGroupMap_fiberι_eq] at hc
      obtain ⟨a, rfl⟩ := (mem_range_fibrationBoundary_iff hp).2 hc
      rw [Subsingleton.elim a ⟦GenLoop.const⟧, fibrationBoundary_const,
        HomotopyGroup.mk_const_eq_one]
  · cases k with
    | zero =>
      -- In degree zero, every point of `E` is joined to the fibre.
      exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined _ rfl fun x ↦
        exists_joined_fiberι hp x
    | succ k =>
      -- By exactness at `π_{k+1}(E)`, a class comes from the fibre since its projection lies in
      -- the trivial group `π_{k+1}(B, b)`.
      have := hB (k + 1) hk
      intro c
      obtain ⟨a, ha⟩ := (mem_range_homotopyGroupMap_fiberι_iff hp (e := e) (a := c)).2
        (Subsingleton.elim _ _)
      exact ⟨a, (homotopyGroupMap_fiberι_eq a).symm.trans ha⟩

/-- **The fibre inclusion is bijective where the base has no homotopy.** Let `p : E → B` be a
Serre fibration and `b : B` a point such that `π_{k+1}(B, b)` and `π_{k+2}(B, b)` are trivial.
Then the inclusion of the fibre `p⁻¹(b) → E` induces a bijection
`π_{k+1}(p⁻¹(b), e) → π_{k+1}(E, e)` at every point `e` of the fibre. -/
theorem bijective_homotopyGroupMap_fiberι_of_mem_serreFibrations (hp : serreFibrations p) {k : ℕ}
    (hB₁ : Subsingleton (π_ (k + 1) B b)) (hB₂ : Subsingleton (π_ (k + 2) B b)) (e : p.fiber b) :
    Function.Bijective (HomotopyGroup.map (N := Fin (k + 1)) (p.fiberι b).hom
      (TopCat.Hom.fiberι_apply p b e)) := by
  have : Subsingleton (HomotopyGroup (Option (Fin (k + 1))) B b) :=
    @Equiv.subsingleton _ _ (HomotopyGroup.congrEquiv (finSuccEquiv (k + 1)).symm) hB₂
  -- By exactness at `π_{k+1}(E)`, every class comes from the fibre, since its projection lies in
  -- the trivial group `π_{k+1}(B, b)`.
  refine ⟨?_, fun c ↦ (mem_range_homotopyGroupMap_fiberι_iff hp).2 (Subsingleton.elim _ _)⟩
  -- By exactness at `π_{k+1}(F)`, the kernel consists of boundaries of classes of the trivial
  -- group `π_{k+2}(B, b)`.
  refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Fin (k + 1)) (p.fiberι b).hom
    (TopCat.Hom.fiberι_apply p b e))).2 fun c hc ↦ ?_
  rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at hc
  obtain ⟨a, rfl⟩ := (mem_range_fibrationBoundary_iff hp).2 hc
  rw [Subsingleton.elim a ⟦GenLoop.const⟧, fibrationBoundary_const, HomotopyGroup.mk_const_eq_one]

end FiberInclusion

end TauCeti.TopCat

namespace TopCat

open TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- **The fibre of a Serre fibration over a weakly contractible base is weakly homotopy equivalent
to the total space.** If `π_k(B, b)` is trivial for every `k : ℕ`, then the inclusion
`p⁻¹(b) → E` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_fiberι_of_mem_serreFibrations (hp : serreFibrations p) {b : B}
    (hB : ∀ k, Subsingleton (π_ k B b)) : (p.fiberι b).hom.IsWeakHomotopyEquivalence :=
  ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun _ ↦
    TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations hp fun k _ ↦ hB k

/-! ### Fibres over joined points -/

section JoinedFibers

/-- **Pulling a Serre fibration back over a weakly contractible base turns every fibre map into a
weak homotopy equivalence.** For a Serre fibration `p : E ⟶ B` and a morphism `g : C ⟶ B` from a
space `C` whose homotopy groups at `t` vanish in every degree (for instance, a contractible
space), the canonical map `p⁻¹(g t) ⟶ C ×_B E` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_fiberPullback (hp : serreFibrations p) {C : TopCat.{u}}
    (g : C ⟶ B) (t : C) (hC : ∀ k, Subsingleton (π_ k C t)) :
    ((p.fiberPullbackFstIso g t).inv ≫ (TopCat.pullbackFst g p).fiberι t).hom
      |>.IsWeakHomotopyEquivalence := by
  have hι : ((TopCat.pullbackFst g p).fiberι t).hom.IsWeakHomotopyEquivalence :=
    isWeakHomotopyEquivalence_fiberι_of_mem_serreFibrations
      (mem_serreFibrations_pullbackFst hp g) hC
  have he : (p.fiberPullbackFstIso g t).inv.hom.IsWeakHomotopyEquivalence :=
    (TopCat.homeoOfIso (p.fiberPullbackFstIso g t).symm).toHomotopyEquiv
      |>.isWeakHomotopyEquivalence
  rw [TopCat.hom_comp]
  exact hι.comp he

/-- A path `γ` in `B` lifted to a morphism `TopCat.I ⟶ B` in `TopCat.{u}`. -/
private def pathHom {b₀ b₁ : B} (γ : Path b₀ b₁) : TopCat.I.{u} ⟶ B :=
  TopCat.ofHom ⟨fun t ↦ γ (TopCat.I.homeomorph t),
    γ.continuous.comp TopCat.I.homeomorph.continuous⟩

private theorem pathHom_apply {b₀ b₁ : B} (γ : Path b₀ b₁) (t : TopCat.I.{u}) :
    pathHom γ t = γ (TopCat.I.homeomorph t) :=
  rfl

private theorem pathHom_zero {b₀ b₁ : B} (γ : Path b₀ b₁) : pathHom γ 0 = b₀ := by
  rw [pathHom_apply, TopCat.I.homeomorph_zero, γ.source]

private theorem pathHom_one {b₀ b₁ : B} (γ : Path b₀ b₁) : pathHom γ 1 = b₁ := by
  rw [pathHom_apply, TopCat.I.homeomorph_one, γ.target]

/-- **Fibres of a Serre fibration over joined points are connected by a zigzag of weak homotopy
equivalences**, through the pullback of `p` along a path between them. -/
theorem exists_isWeakHomotopyEquivalence_fiber_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) :
    ∃ (P : TopCat.{u}) (f₀ : p.fiber b₀ ⟶ P) (f₁ : p.fiber b₁ ⟶ P),
      f₀.hom.IsWeakHomotopyEquivalence ∧ f₁.hom.IsWeakHomotopyEquivalence := by
  let γ := hb.somePath
  let g := pathHom γ
  have : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have : ContractibleSpace TopCat.I.{u} := TopCat.I.homeomorph.contractibleSpace
  have h₀ := isWeakHomotopyEquivalence_fiberPullback hp g 0 fun _ ↦ inferInstance
  have h₁ := isWeakHomotopyEquivalence_fiberPullback hp g 1 fun _ ↦ inferInstance
  let e₀ : p.fiber b₀ ≅ p.fiber (g 0) := eqToIso (congrArg p.fiber (pathHom_zero γ).symm)
  let e₁ : p.fiber b₁ ≅ p.fiber (g 1) := eqToIso (congrArg p.fiber (pathHom_one γ).symm)
  refine ⟨_, e₀.hom ≫ (p.fiberPullbackFstIso g 0).inv ≫ (TopCat.pullbackFst g p).fiberι 0,
    e₁.hom ≫ (p.fiberPullbackFstIso g 1).inv ≫ (TopCat.pullbackFst g p).fiberι 1, ?_, ?_⟩
  · rw [TopCat.hom_comp]
    exact h₀.comp (TopCat.homeoOfIso e₀).toHomotopyEquiv.isWeakHomotopyEquivalence
  · rw [TopCat.hom_comp]
    exact h₁.comp (TopCat.homeoOfIso e₁).toHomotopyEquiv.isWeakHomotopyEquivalence

/-- **Fibres of a Serre fibration over points in the same path component are simultaneously
path-connected.** -/
theorem pathConnectedSpace_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) : PathConnectedSpace (p.fiber b₀) ↔ PathConnectedSpace (p.fiber b₁) := by
  obtain ⟨_, _, _, h₀, h₁⟩ := exists_isWeakHomotopyEquivalence_fiber_of_joined hp hb
  exact h₀.pathConnectedSpace_iff.trans h₁.pathConnectedSpace_iff.symm

end JoinedFibers

end TopCat
