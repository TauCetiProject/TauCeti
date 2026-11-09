/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

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

## Implementation notes

Both directions read the long exact homotopy sequence of the fibration
(`TauCeti.TopCat.mem_range_fibrationBoundary_iff`,
`TauCeti.TopCat.mem_range_homotopyGroupMap_fiberι_iff`,
`TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`). At its low end, where
`π_0` is only a pointed set, path lifting supplies the remaining comparisons: a path in `B`
between the projections of two points of `E` lifts to a path from the first point into the fibre
of the second, and a path from the image of `p` to a point `b` lifts to a point of the fibre over
`b`.

## Main results

* `TauCeti.TopCat.isNConnected_iff_of_mem_serreFibrations`: a Serre fibration is `n`-connected
  exactly when its fibres are nonempty and `(n - 1)`-connected.
* `TauCeti.TopCat.isWeakHomotopyEquivalence_iff_of_mem_serreFibrations`: a Serre fibration is a
  weak homotopy equivalence exactly when its fibres are nonempty and weakly contractible.

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

/-- **Path lifting into a path-connected fibre.** If the fibre of a Serre fibration over `p y` is
path-connected, then a point `x` whose projection is joined to `p y` is joined to `y`. -/
private theorem joined_of_joined_proj (hp : serreFibrations p) {x y : E}
    (hy : ∀ a c : p.fiber (p y), Joined a c) (h : Joined (p x) (p y)) : Joined x y := by
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp h.somePath
  have hΓ1 : p (Γ 1) = p y := (congrFun hΓ 1).trans h.somePath.target
  exact Joined.trans ⟨⟨Γ, hΓ0, rfl⟩⟩ ((hy ⟨Γ 1, hΓ1⟩ ⟨y, rfl⟩).map continuous_subtype_val)

/-- **Lifting the base point of a path.** If every point of `B` is joined to the image of a Serre
fibration `p`, then every fibre of `p` is nonempty. -/
private theorem nonempty_fiber_of_exists_joined (hp : serreFibrations p)
    (h : ∀ b, ∃ x, Joined (p x) b) (b : B) : Nonempty (p.fiber b) := by
  obtain ⟨x, hx⟩ := h b
  obtain ⟨Γ, -, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp hx.somePath
  exact ⟨⟨Γ 1, (congrFun hΓ 1).trans hx.somePath.target⟩⟩

/-- A Serre fibration whose fibres are nonempty and `(n - 1)`-connected is `n`-connected. -/
private theorem isNConnected_of_forall_fiber (hp : serreFibrations p)
    (hF : ∀ b, Nonempty (p.fiber b) ∧
      ∀ (e : p.fiber b) k, k < n → Subsingleton (π_ k (p.fiber b) e)) :
    p.hom.IsNConnected n := by
  classical
  refine ⟨fun b ↦ ?_, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · -- Every fibre is nonempty, so `p` is surjective.
    obtain ⟨e⟩ := (hF b).1
    have he : p.hom e.1 = b := Set.mem_singleton_iff.1 e.2
    exact ⟨e.1, by rw [he]⟩
  · cases k with
    | zero =>
      -- In degree zero, homotopy classes are path components, and paths lift into the fibre.
      intro c d hcd
      induction c using Quotient.inductionOn with | h γ => ?_
      induction d using Quotient.inductionOn with | h δ => ?_
      apply (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x).injective
      have := congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) _) hcd
      rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
        homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply, GenLoop.map_apply] at this
      rw [homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
        homotopyGroupEquivZerothHomotopyOfIsEmpty_mk]
      refine ZerothHomotopy.sound (joined_of_joined_proj hp (fun a c ↦ ?_)
        (Quotient.exact this)).somePath
      exact ((pathConnectedSpace_iff_subsingleton_homotopyGroup_zero a).2
        ((hF _).2 a 0 hk)).joined a c
    | succ k =>
      -- In positive degrees the induced map is a homomorphism, and by exactness at `π_k(E)` its
      -- kernel comes from the trivial group `π_k(F)`.
      have := (hF (p x)).2 ⟨x, rfl⟩ (k + 1) hk
      refine (injective_iff_map_eq_one
        (HomotopyGroup.mapHom (N := Fin (k + 1)) (x := x) p.hom rfl)).2 fun c hc ↦ ?_
      rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at hc
      obtain ⟨a, rfl⟩ := (mem_range_homotopyGroupMap_fiberι_iff hp (e := ⟨x, rfl⟩)).2 hc
      rw [Subsingleton.elim a 1, HomotopyGroup.map_one]
  · cases k with
    | zero =>
      -- In degree zero, every point of `B` is the projection of a point of its fibre.
      intro c
      induction c using Quotient.inductionOn with | h γ => ?_
      obtain ⟨e⟩ := (hF (γ 0)).1
      refine ⟨⟦(genLoopHomeoOfIsEmpty (Fin 0) x).symm e.1⟧,
        (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) _).injective ?_⟩
      rw [HomotopyGroup.map_mk, homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
        homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply,
        ← genLoopHomeoOfIsEmpty_apply, Homeomorph.apply_symm_apply]
      exact congrArg ZerothHomotopy.mk (Set.mem_singleton_iff.1 e.2)
    | succ k =>
      -- Split off the first direction: by exactness at `π_{k+1}(B)`, a class lifts to `E` since
      -- its boundary lies in the trivial group `π_k(F)`.
      have := (hF (p x)).2 ⟨x, rfl⟩ k hk
      let φ := (finSuccEquiv k).symm
      intro c
      obtain ⟨a, ha⟩ := (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp (e := ⟨x, rfl⟩)
        (a := (HomotopyGroup.congrEquiv φ).symm c)).2 (Subsingleton.elim _ _)
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
  ⟨fun hf b ↦ ⟨nonempty_fiber_of_exists_joined hp hf.exists_joined b,
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

end TauCeti.TopCat
