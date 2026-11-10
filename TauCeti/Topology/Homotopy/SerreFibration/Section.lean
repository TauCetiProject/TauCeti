/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# Serre fibrations with a section

Let `p : E → B` be a Serre fibration with a section `s`, and let `e = s b` be the base point of the
fibre `F = p⁻¹(b)`. Then `p` induces a split surjection `π_n(E, e) → π_n(B, b)` in every degree
(`TauCeti.TopCat.surjective_homotopyGroupMap_of_section`), so every boundary map
`π_{n+1}(B, b) → π_n(F, e)` of the exact homotopy sequence is trivial
(`TauCeti.TopCat.fibrationBoundary_eq_of_section`), and the fibre inclusion is injective on
homotopy groups in positive degrees (`TauCeti.TopCat.injective_homotopyGroupMap_fiberι_of_section`).
Together with exactness at `π_n(E, e)` (`TauCeti.TopCat.mem_range_homotopyGroupMap_fiberι_iff`),
the long exact sequence thus breaks into split short exact sequences of groups

`1 → π_n(F, e) → π_n(E, e) → π_n(B, b) → 1`, `n ≥ 1`.

For example, evaluation of free loops at a point of the circle has the section by constant loops,
which splits the homotopy groups of the free loop space into those of the space and of its based
loop space.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {b : B} {e : p.fiber b} {N : Type*}
  {s : B ⟶ E}

/-- **A section makes the projection surjective on homotopy groups.** If `s` is a section of `p`
through `e`, then `p` induces a surjection `π_n(E, e) → π_n(B, b)`, split by the map induced by
`s`. -/
theorem surjective_homotopyGroupMap_of_section (hs : s ≫ p = 𝟙 B) (hsb : s b = e.1) :
    Function.Surjective
      (HomotopyGroup.map (N := N) p.hom (Set.mem_singleton_iff.1 e.2)) := by
  have hps : p.hom.comp s.hom = ContinuousMap.id B := congrArg _root_.TopCat.Hom.hom hs
  exact fun a ↦ ⟨HomotopyGroup.map s.hom hsb a,
    HomotopyGroup.map_map_of_comp_eq_id p.hom s.hom hsb _ hps a⟩

/-- **The boundary maps of a Serre fibration with a section vanish.** If `s` is a section of `p`
through `e`, every class of `π_{n+1}(B, b)` comes from `E`, so its boundary in `π_n(F, e)` is the
class of the constant loop. -/
theorem fibrationBoundary_eq_of_section (hp : serreFibrations p) [Finite N] (hs : s ≫ p = 𝟙 B)
    (hsb : s b = e.1) (a : HomotopyGroup (Option N) B b) :
    fibrationBoundary hp e a = (⟦GenLoop.const⟧ : HomotopyGroup N (p.fiber b) e) :=
  (mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).1
    (surjective_homotopyGroupMap_of_section hs hsb a)

/-- **The fibre of a Serre fibration with a section injects on homotopy groups.** If `s` is a
section of `p` through `e`, the fibre inclusion induces an injection `π_n(F, e) → π_n(E, e)` for
`n ≥ 1`: its kernel is the image of the boundary map, which is trivial. -/
theorem injective_homotopyGroupMap_fiberι_of_section (hp : serreFibrations p) [Finite N]
    [Nonempty N] (hs : s ≫ p = 𝟙 B) (hsb : s b = e.1) :
    Function.Injective
      (HomotopyGroup.map (N := N) (p.fiberι b).hom (_root_.TopCat.Hom.fiberι_apply p b e)) := by
  classical
  refine (injective_iff_map_eq_one
    (HomotopyGroup.mapHom (N := N) (p.fiberι b).hom (_root_.TopCat.Hom.fiberι_apply p b e))).2
    fun a ha ↦ ?_
  rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at ha
  obtain ⟨c, rfl⟩ := (mem_range_fibrationBoundary_iff hp).2 ha
  rw [fibrationBoundary_eq_of_section hp hs hsb, HomotopyGroup.mk_const_eq_one]

end TauCeti.TopCat
