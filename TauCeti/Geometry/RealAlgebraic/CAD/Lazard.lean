/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Analytic
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Semialgebraic

/-!
# Lifting cylindrical decompositions by Lazard delineations

A cylindrical algebraic decomposition of the base lifts through a family of Lazard
delineations, one over each base cell. The resulting sections and sectors are semialgebraic,
form a cylindrical algebraic decomposition of the cylinder, and remain analytic submanifolds
when the base cells are analytic submanifolds.

The Lazard valuation of every input is constant on each lifted cell when the new cylinder
coordinate is read last, as required by Lazard evaluation. In the ambient CAD convention the
new coordinate is coordinate zero. Rotating the input variables reconciles these conventions,
and the rotated inputs are sign-invariant on every lifted cell.

This is the CAD-level assembly step in Lazard's projection-and-lifting construction. The
separate analytic lifting theorem supplies the Lazard delineation over each base cell.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin (n + 1)) ℝ}

/-- **CAD lifting by Lazard delineations.** Suppose every cell of a cylindrical algebraic
decomposition of `ℝ ^ n` is an analytic submanifold and carries a Lazard delineation of a
fixed polynomial family. Then the stacks of those delineations form a cylindrical algebraic
decomposition of `ℝ ^ (n + 1)` with the original decomposition as its projection.

Every lifted cell is an analytic submanifold. The Lazard valuation of each family member is
constant there when the new coordinate is moved to the final position, and the corresponding
variable rotation of each member is sign-invariant in the ambient coordinate order. -/
theorem IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation
    {𝓓 : Set (Set (Fin n → ℝ))} (h𝓓 : IsCAD n 𝓓)
    (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C)
    (hD : ∀ C ∈ 𝓓, Nonempty (LazardDelineation F C)) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ k E, E ∈ 𝓒 → ∀ x ∈ E, ∀ y ∈ E,
        (F k).lazardValuation (Fin.snoc (Fin.tail x) (x 0)) =
          (F k).lazardValuation (Fin.snoc (Fin.tail y) (y 0))) ∧
      ∀ k E, E ∈ 𝓒 → SignInvariant
        (fun x ↦ eval x (rename (finRotate (n + 1)) (F k))) E := by
  classical
  have hstack (C : Set (Fin n → ℝ)) :
      ∃ (k : ℕ) (θ : Fin k → C → ℝ), C ∈ 𝓓 →
        IsSemialgebraicStack C θ ∧
          ∀ E ∈ stackCells C θ,
            (∃ d, IsAnalyticSubmanifold d E) ∧
            (∀ i, ∀ x ∈ E, ∀ y ∈ E,
              (F i).lazardValuation (Fin.snoc (Fin.tail x) (x 0)) =
                (F i).lazardValuation (Fin.snoc (Fin.tail y) (y 0))) ∧
            ∀ i, SignInvariant (fun x ↦ eval x (rename (finRotate (n + 1)) (F i))) E := by
    by_cases hC : C ∈ 𝓓
    · obtain ⟨D⟩ := hD C hC
      obtain ⟨d, hd⟩ := hanalytic C hC
      refine ⟨D.count, D.root, fun _ ↦ ⟨D.isSemialgebraicStack (h𝓓.isSemialgebraic hC),
        fun E hE ↦ ⟨(D.exists_isAnalyticSubmanifold_of_mem_stackCells hd hE).imp fun _ h ↦ h.2,
          ?_, fun i ↦ D.signInvariant_rename_finRotate_of_mem_stackCells
            (h𝓓.isConnected hC).isPreconnected i hE⟩⟩⟩
      exact fun i x hx y hy ↦ D.lazardValuation_snoc_eq_of_mem_stackCells i hE hx hy
    · exact ⟨0, Fin.elim0, fun h ↦ (hC h).elim⟩
  choose k θ hθ using hstack
  refine ⟨⋃ C ∈ 𝓓, stackCells C (θ C), IsCAD.succ k θ h𝓓 fun C hC ↦ (hθ C hC).1,
    image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).1.strictMono, ?_, ?_, ?_⟩
  · intro E hE
    obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.1 hE
    exact ((hθ C hC).2 E hEC).1
  · intro i E hE x hx y hy
    obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.1 hE
    exact ((hθ C hC).2 E hEC).2.1 i x hx y hy
  · intro i E hE
    obtain ⟨C, hC, hEC⟩ := mem_iUnion₂.1 hE
    exact ((hθ C hC).2 E hEC).2.2 i

end TauCeti
