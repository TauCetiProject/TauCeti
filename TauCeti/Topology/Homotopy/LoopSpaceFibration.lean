/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.OpenBoxLifting

/-!
# Loop spaces of Hurewicz fibrations

For a Hurewicz fibration `p : E → B` and a point `e : E`, the induced map
`Ω E e → Ω B (p e)`, `γ ↦ p ∘ γ`, on the fixed-interval loop spaces `Ω X x = Path x x` (with the
compact-open topology) is again a Hurewicz fibration (`TauCeti.IsHurewiczFibration.loopMap`), and
so is the induced map on double loop spaces (`TauCeti.IsHurewiczFibration.loopMap_loopMap`).  A
homotopy of loops is a map from a square whose two sides are at the base point, so a lift is a
relative lift for the open box (`TauCeti.IsHurewiczFibration.exists_lift_openBox`).

The statement is for the fixed-interval loop space.  The analogous statement for Moore loops,
through the comparison of Moore loops with fixed-interval loops, is not proved here: lifting a
Moore loop of length zero requires a lift that is constant over constant paths.

## Main results

* `TauCeti.IsHurewiczFibration.loopMap`: `Ω p` is a Hurewicz fibration.
* `TauCeti.IsHurewiczFibration.loopMap_loopMap`: `Ω² p` is a Hurewicz fibration.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open unitInterval Topology.Homotopy

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- The map `Ω E e → Ω B (p e)` induced by a continuous map `p` is continuous. -/
theorem continuous_loopMap (hp : Continuous p) (e : E) :
    Continuous fun γ : Ω E e ↦ (γ.map hp : Ω B (p e)) :=
  continuous_induced_rng.2 <| (ContinuousMap.continuous_postcomp ⟨p, hp⟩).comp
    continuous_induced_dom

/-- **The loop map of a Hurewicz fibration is a Hurewicz fibration**: for a Hurewicz fibration
`p : E → B` and `e : E`, the induced map `Ω E e → Ω B (p e)` on fixed-interval loop spaces is a
Hurewicz fibration. -/
theorem IsHurewiczFibration.loopMap (hp : IsHurewiczFibration.{w} p) (e : E) :
    IsHurewiczFibration.{w} fun γ : Ω E e ↦ (γ.map hp.continuous : Ω B (p e)) := by
  refine isHurewiczFibration_iff.2 ⟨continuous_loopMap hp.continuous e, fun A _ f H hH ↦ ?_⟩
  -- The lifting problem as a relative lifting problem for the open box, coordinates `(u, t)`.
  let g : C(A × (I × I), E) := ⟨fun y ↦ f y.1 y.2.1, by fun_prop⟩
  let H' : C(A × (I × I), B) := ⟨fun y ↦ H (y.2.2, y.1) y.2.1, by fun_prop⟩
  have hg : ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → p (g (a, x)) = H' (a, x) := by
    rintro a ⟨u, t⟩ (h | h | h)
    · simp only at h
      subst h
      simp [g, H', hH a]
    · simp only at h
      subst h
      simp [g, H']
    · simp only at h
      subst h
      simp [g, H']
  obtain ⟨G, hG, hGg⟩ := hp.exists_lift_openBox g H' hg
  have hG₀ : ∀ y : I × A, G (y.2, (0, y.1)) = e := fun y ↦ by
    rw [hGg _ _ (Or.inr (Or.inl rfl))]
    simp [g]
  have hG₁ : ∀ y : I × A, G (y.2, (1, y.1)) = e := fun y ↦ by
    rw [hGg _ _ (Or.inr (Or.inr rfl))]
    simp [g]
  let L : I × A → Ω E e := fun y ↦
    ⟨⟨fun u ↦ G (y.2, (u, y.1)), by fun_prop⟩, hG₀ y, hG₁ y⟩
  have hL : Continuous L := by
    refine Path.continuous_uncurry_iff.1 ?_
    exact G.continuous.comp ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.prodMk (continuous_fst.comp continuous_fst)))
  refine ⟨⟨L, hL⟩, funext fun y ↦ Path.ext (funext fun u ↦ ?_),
    fun a ↦ Path.ext (funext fun u ↦ ?_)⟩
  · have := congrFun hG (y.2, (u, y.1))
    simpa [L, H'] using this
  · simpa [L, g] using hGg a (u, 0) (Or.inl rfl)

/-- **The double loop map of a Hurewicz fibration is a Hurewicz fibration.** -/
theorem IsHurewiczFibration.loopMap_loopMap (hp : IsHurewiczFibration.{w} p) (e : E) :
    IsHurewiczFibration.{w} fun Γ : Ω (Ω E e) (Path.refl e) ↦
      (Γ.map (hp.loopMap e).continuous : Ω (Ω B (p e)) ((Path.refl e).map hp.continuous)) :=
  (hp.loopMap e).loopMap (Path.refl e)

end TauCeti
