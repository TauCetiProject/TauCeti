/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration.Fiber
import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# The homotopy-group criterion for trivial Kan fibrations

A connected Kan complex with trivial positive homotopy groups is intrinsically weakly
contractible. A Kan fibration over a Kan complex which induces bijections on connected
components and on all positive homotopy groups therefore lifts against every monomorphism.

The absolute boundary-filling argument contracts a horn using a simplex extending it. Endpoint
cylinder lifting extends that contraction to the boundary. The remaining face is a pointed
simplex, and its null class supplies a filler through `SSet.KanComplex.π.mk_eq_mk_iff`.
The relative criterion then uses the long exact sequence and the fibre criterion for trivial
fibrations. All spaces and homotopy groups here are native simplicial sets.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I, §§7–8.
-/

public section

universe u

open CategoryTheory Simplicial HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory

namespace SSet

open modelCategoryQuillen KanComplex

variable {X : SSet.{u}} [KanComplex X]

private lemma exists_boundary_homotopy_const_faces {n : ℕ} (a : (∂Δ[n + 1] : SSet) ⟶ X) :
    ∃ (x : X _⦋0⦌) (b : (∂Δ[n + 1] : SSet) ⟶ X), Nonempty (Homotopy b a) ∧
      ∀ j : Fin (n + 2), j ≠ 0 → boundary.ι j ≫ b = const x := by
  have hΛ : Λ[n + 1, 0] ≤ ∂Δ[n + 1] := by
    rw [horn_eq_iSup, boundary_eq_iSup]
    exact iSup_le fun j ↦ le_iSup (fun k : Fin (n + 2) ↦ stdSimplex.face {k}ᶜ) j.val
  let i := Subcomplex.homOfLE hΛ
  obtain ⟨g, hg⟩ := KanComplex.hornFilling (i ≫ a)
  let H := ((stdSimplex.contraction (n + 1)).postcomp g).precomp Λ[n + 1, 0].ι
  let p := stdSimplex.isTerminalObj₀.from X
  have : Fibration p := (isFibrant_iff_of_isTerminal p stdSimplex.isTerminalObj₀).1 inferInstance
  obtain ⟨L, hL₁, hLi, -⟩ := exists_lift_cylinder_ι₁_of_mono i p
    (stdSimplex.isTerminalObj₀.from _) a H.h
    (stdSimplex.isTerminalObj₀.hom_ext _ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)
    (by simpa [H] using hg)
  refine ⟨g.app _ (stdSimplex.obj₀Equiv.symm 0), ι₀ ≫ L,
    ⟨Homotopy.mk' L rfl hL₁⟩, fun j hj ↦ ?_⟩
  have hji : boundary.ι j = horn.ι 0 j hj ≫ i := by
    rw [← cancel_mono ∂Δ[n + 1].ι]
    simp [i]
  rw [hji, Category.assoc, ← ι₀_comp_assoc, hLi]
  simp [H]

private lemma exists_boundary_extension_const_faces {n : ℕ} {x : X _⦋0⦌}
    (h : Subsingleton (π n X x)) (a : (∂Δ[n + 1] : SSet) ⟶ X)
    (ha : ∀ j : Fin (n + 2), j ≠ 0 → boundary.ι j ≫ a = const x) :
    ∃ g : Δ[n + 1] ⟶ X, ∂Δ[n + 1].ι ≫ g = a := by
  let s : X.PtSimplex n x :=
    { map := boundary.ι 0 ≫ a
      comm := by
        obtain _ | n := n
        · exact boundary.hom_ext₀
        refine boundary.hom_ext fun j ↦ ?_
        have hc := (boundary.IsCompatible.of_hom a).δ_pred_comp 0 j.succ (by simp)
        simpa [ha _ (Fin.succ_ne_zero _)] using hc }
  obtain ⟨r⟩ := (π.mk_eq_mk_iff (p := s) (q := .const)).1 (h.elim _ _)
  refine ⟨r.map, boundary.hom_ext fun j ↦ ?_⟩
  obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
  · simpa [s] using r.δ_castSucc_map
  rw [boundary.ι_ι_assoc, ha _ (Fin.succ_ne_zero _)]
  obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
  · simpa using r.δ_succ_map
  · exact r.δ_map_of_gt _ (by simp [Fin.lt_def])

/-- A connected Kan complex with trivial positive homotopy groups lifts every boundary against
the map to a point, hence lifts against every monomorphism. -/
theorem rlp_monomorphisms_of_subsingleton_π (X : SSet.{u}) [KanComplex X]
    [X.IsConnected] (h : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (π (n + 1) X x)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (stdSimplex.isTerminalObj₀.from X) := by
  have hp (x : X _⦋0⦌) (n : ℕ) : Subsingleton (π n X x) := by
    obtain _ | n := n
    · exact (π.zeroEquiv X x).injective.subsingleton
    · exact h x n
  rw [SSet.rlp_monomorphisms]
  refine fun _ _ _ ⟨n⟩ ↦ ⟨fun {a b} sq ↦ ?_⟩
  obtain _ | n := n
  · obtain ⟨x⟩ : X.Nonempty := inferInstance
    exact ⟨⟨⟨const x, boundary.hom_ext₀, stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
  obtain ⟨x, a', ⟨H⟩, ha'⟩ := exists_boundary_homotopy_const_faces a
  obtain ⟨g, hg⟩ := exists_boundary_extension_const_faces (hp x n) a' ha'
  let p := stdSimplex.isTerminalObj₀.from X
  have : Fibration p := (isFibrant_iff_of_isTerminal p stdSimplex.isTerminalObj₀).1 inferInstance
  obtain ⟨L, -, hL, -⟩ := exists_lift_cylinder_ι₀_of_mono ∂Δ[n + 1].ι p
    (stdSimplex.isTerminalObj₀.from _) g H.h (stdSimplex.isTerminalObj₀.hom_ext _ _)
    (stdSimplex.isTerminalObj₀.hom_ext _ _) (hg.trans H.h₀.symm)
  exact ⟨⟨⟨ι₁ ≫ L, by rw [← ι₁_comp_assoc, hL, H.h₁],
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩

/-- A connected Kan complex whose positive homotopy groups are trivial is intrinsically weakly
contractible. -/
theorem isWeaklyContractible_of_subsingleton_π (X : SSet.{u}) [KanComplex X] [X.IsConnected]
    (h : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (π (n + 1) X x)) :
    IsWeaklyContractible X :=
  ((rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    stdSimplex.isTerminalObj₀ _).1 (rlp_monomorphisms_of_subsingleton_π X h)).2

omit [KanComplex X] in
/-- A Kan fibration over a Kan complex that induces bijections on connected components and all
positive homotopy groups has the right lifting property against every monomorphism. -/
theorem rlp_monomorphisms_of_bijective_mapπ₀_of_bijective_π_map {Y : SSet.{u}}
    (p : X ⟶ Y) [Fibration p] [KanComplex Y]
    (h₀ : Function.Bijective (mapπ₀ p))
    (hπ : ∀ (x : X _⦋0⦌) (n : ℕ),
      Function.Bijective (π.map (n := n + 1) p (y := p.app _ x) rfl)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  apply rlp_monomorphisms_of_isWeaklyContractible_fiber
  intro y
  have := isConnected_fiber_of_bijective_mapπ₀ p h₀ fun x ↦ (hπ x 0).2
  exact isWeaklyContractible_of_subsingleton_π (fiber p y : SSet)
    (subsingleton_π_fiber_of_bijective p hπ y)

end SSet
