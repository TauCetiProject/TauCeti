/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.Delineability
public import TauCeti.Geometry.RealAlgebraic.Stack.Semialgebraic

/-!
# Existence of adapted cylindrical algebraic decompositions

For every finite set `F` of real polynomials in `n` variables there is a cylindrical algebraic
decomposition of `ℝ ^ n` adapted to `F`: every member of `F` is sign-invariant on every cell
(`TauCeti.exists_isCAD_signInvariant`).

The proof is by induction on `n`. Single out the first variable with `MvPolynomial.finSuccEquiv`
and take an adapted CAD of `ℝ ^ n` for the Collins projection of the resulting family.
By Collins delineability, the family has a delineation over each cell. Its stacks give the CAD
of `ℝ ^ (n + 1)`.

These stacks are semialgebraic by `TauCeti.Delineation.isSemialgebraicStack`: their sections
and sectors are described by membership in the shared distinct root set and the number of
shared roots below the height. No derivatives need to be added to the input family.
Nullified members, repeated roots, the empty family and stacks without sections are included.

## Main results

* `TauCeti.exists_isCAD_signInvariant`: every finite set of polynomials has an adapted CAD.
* `TauCeti.IsSemialgebraic.image_tail`: **projection closure**. Forgetting the coordinate `0`
  maps semialgebraic subsets of `ℝ ^ (n + 1)` to semialgebraic subsets of `ℝ ^ n`. A
  semialgebraic set is a sign condition on finitely many polynomials, so it is a union of cells of
  an adapted CAD, and its projection is a union of cells of the projected CAD.
* `TauCeti.exists_finite_image_sign_eval_eq`: finitely many sample points realize every sign
  vector of a finite family of polynomials.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 and Chapter 11 (cylindrical decomposition).
-/

public section

open Function Set MvPolynomial
open scoped Polynomial

namespace TauCeti

variable {n : ℕ}

/-- **Existence of adapted cylindrical algebraic decompositions.** For every finite set `F` of
real polynomials in `n` variables there is a cylindrical algebraic decomposition of `ℝ ^ n` on
each cell of which every member of `F` is sign-invariant. -/
theorem exists_isCAD_signInvariant (F : Finset (MvPolynomial (Fin n) ℝ)) :
    ∃ 𝒞, IsCAD n 𝒞 ∧ ∀ f ∈ F, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x f) E := by
  induction n with
  | zero =>
    exact ⟨{univ}, .zero, fun f _ E hE ↦ by
      rw [mem_singleton_iff.1 hE]
      exact subsingleton_of_subsingleton.signInvariant⟩
  | succ n ih =>
    classical
    let G := F.image (finSuccEquiv ℝ n)
    have hFG {f} (hf : f ∈ F) : finSuccEquiv ℝ n f ∈ G :=
      Finset.mem_image_of_mem _ hf
    obtain ⟨𝒟, h𝒟, hproj⟩ := ih G.collinsProjection
    -- over each base cell, the stack of a delineation of the fibers of `G`
    have hstack (C : Set (Fin n → ℝ)) : ∃ (k : ℕ) (θ : Fin k → C → ℝ), C ∈ 𝒟 →
        IsSemialgebraicStack C θ ∧
          ∀ E ∈ stackCells C θ, ∀ f ∈ F, SignInvariant (fun y ↦ eval y f) E := by
      by_cases hC : C ∈ 𝒟
      · obtain ⟨D⟩ := nonempty_delineation_of_signInvariant_collinsProjection
          (φ := RingHom.id ℝ) (h𝒟.isConnected hC).isPreconnected fun q hq ↦ by
            simpa only [eval₂_id] using hproj q hq C hC
        refine ⟨D.count, D.root, fun _ ↦ ⟨D.isSemialgebraicStack (h𝒟.isSemialgebraic hC),
          fun E hE f hf ↦ ?_⟩⟩
        simpa only [eval₂_id] using D.signInvariant_eval₂_of_mem_stackCells (hFG hf) hE
      · exact ⟨0, Fin.elim0, fun h ↦ (hC h).elim⟩
    choose k θ hθ using hstack
    refine ⟨_, .succ k θ h𝒟 fun C hC ↦ (hθ C hC).1, fun f hf E hE ↦ ?_⟩
    obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    exact (hθ C hC).2 E hE f hf

/-- **Projection closure.** The projection of a semialgebraic subset of `ℝ ^ (n + 1)` forgetting
the coordinate `0` is semialgebraic. -/
theorem IsSemialgebraic.image_tail {s : Set (Fin (n + 1) → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (Fin.tail '' s) := by
  classical
  obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
  obtain ⟨𝒞, h𝒞, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
  exact h𝒞.isSemialgebraic_image_tail_setOf_sign_eval
    (fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) Φ

/-- **Sample points.** For finitely many real polynomials `p i` in `n` variables there is a
finite set of points of `ℝ ^ n` at which the `p i` take every sign vector that they take on
`ℝ ^ n`. -/
theorem exists_finite_image_sign_eval_eq {ι : Type*} [Finite ι]
    (p : ι → MvPolynomial (Fin n) ℝ) :
    ∃ T : Set (Fin n → ℝ), T.Finite ∧
      (fun x i ↦ SignType.sign (eval x (p i))) '' T =
        range fun x i ↦ SignType.sign (eval x (p i)) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨𝒞, h𝒞, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
  obtain ⟨T, hT, -, hTp⟩ := h𝒞.exists_finite_image_sign_eval_eq
    fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact ⟨T, hT, hTp⟩

end TauCeti
