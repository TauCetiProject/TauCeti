/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.Delineability

/-!
# Existence of adapted cylindrical algebraic decompositions

For every finite set `F` of real polynomials in `n` variables there is a cylindrical algebraic
decomposition of `ℝ ^ n` adapted to `F`: every member of `F` is sign-invariant on every cell
(`TauCeti.exists_isCAD_signInvariant`).

The proof is by induction on `n`. Single out the first variable with `MvPolynomial.finSuccEquiv`
and add all the derivatives in that variable of the members of `F`. Then take an adapted CAD of
`ℝ ^ n` for the Collins projection of the resulting family. By Collins delineability, this family
has a delineation over each cell. Its stacks give the CAD of `ℝ ^ (n + 1)`.

These stacks are semialgebraic because the family is closed under differentiation
(`TauCeti.Delineation.isSemialgebraicStack`). By Thom's lemma, two points of one fiber at which
all members of such a family have the same signs lie in the same cell of the stack
(`TauCeti.Delineation.mk_mem_sectionSet_iff_of_sign_eval_eq`,
`TauCeti.Delineation.mk_mem_sectorSet_iff_of_sign_eval_eq`). Each cell lies over the whole base
cell and the members are sign-invariant on it. So each cell is the set of points over the base
cell where the members of the family have one fixed sign vector. This set is semialgebraic
whenever the base cell is. No description of the roots by coefficient signs is needed.

## Main results

* `TauCeti.Delineation.isSemialgebraicStack`: over a semialgebraic base, a delineation of a family
  in which the derivative of every member is zero or a member is a semialgebraic stack.
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
second edition, Section 5.1 (cylindrical decomposition) and Proposition 2.27 (Thom's lemma).
-/

public section

open Function Set MvPolynomial
open scoped Polynomial

namespace TauCeti

variable {n : ℕ}

section Stack

variable {A : Type*} [CommRing A] {φ : A →+* ℝ} {F : Finset (MvPolynomial (Fin n) A)[X]}
  {C : Set (Fin n → ℝ)}

/-- A subset `B` of the cylinder over a semialgebraic set `C` is semialgebraic in `ℝ ^ (n + 1)`
if it lies over all of `C`, the fibers of the members of `F` are sign-invariant on it, and it
contains every point of a fiber at which these signs are those at some point of `B` in the same
fiber. -/
private theorem isSemialgebraic_image_cylinder (hC : IsSemialgebraic C) {B : Set (C × ℝ)}
    (hfst : Prod.fst '' B = univ)
    (hsign : ∀ p : F,
      SignInvariant (fun z : C × ℝ ↦ (p.1.map (eval₂Hom φ z.1.1)).eval z.2) B)
    (hmem : ∀ x t t', (x, t) ∈ B → (∀ p : F, SignType.sign ((p.1.map (eval₂Hom φ x.1)).eval t) =
      SignType.sign ((p.1.map (eval₂Hom φ x.1)).eval t')) → (x, t') ∈ B) :
    IsSemialgebraic (cylinder C '' B) := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simpa only [image_empty] using isSemialgebraic_empty
  -- the members of `F` as polynomials in `n + 1` variables
  have key (p : F) (y : Fin (n + 1) → ℝ) :
      eval y (map φ ((finSuccEquiv A n).symm p.1)) =
        (p.1.map (eval₂Hom φ (Fin.tail y))).eval (y 0) := by
    conv_lhs => rw [eval_map, ← Fin.cons_self_tail y, ← polynomial_eval_map_finSuccEquiv,
      AlgEquiv.apply_symm_apply]
  let σ (p : F) : SignType := SignType.sign ((p.1.map (eval₂Hom φ z₀.1.1)).eval z₀.2)
  suffices cylinder C '' B = {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C} ∩
      ⋂ p : F, {y | SignType.sign (eval y (map φ ((finSuccEquiv A n).symm p.1))) = σ p} by
    rw [this]
    exact hC.preimage_tail.inter (.iInter fun p ↦ isSemialgebraic_sign_eval_eq _ _)
  ext y
  simp only [mem_image_cylinder, mem_inter_iff, mem_iInter, mem_ofPred_eq, key]
  refine ⟨fun ⟨hy, hyB⟩ ↦ ⟨hy, fun p ↦ signInvariant_def.1 (hsign p) _ hyB _ hz₀⟩,
    fun ⟨hy, hyσ⟩ ↦ ⟨hy, ?_⟩⟩
  -- a point of `B` in the fiber of `y` has the signs of `z₀`, hence those of `y`
  obtain ⟨⟨x, t⟩, ht, hx⟩ := hfst.symm ▸ mem_univ (⟨Fin.tail y, hy⟩ : C)
  subst hx
  exact hmem _ t _ ht fun p ↦ (signInvariant_def.1 (hsign p) _ ht _ hz₀).trans (hyσ p).symm

/-- A delineation, over a semialgebraic set, of the fibers of a finite family of polynomials in
one distinguished variable, in which the derivative of every member is zero or a member, is a
semialgebraic stack. Each of its sections and sectors is the set of points over the base where the
members of the family have a given sign vector. -/
theorem Delineation.isSemialgebraicStack (hC : IsSemialgebraic C)
    (hF : ∀ p ∈ F, Polynomial.derivative p = 0 ∨ Polynomial.derivative p ∈ F)
    (D : Delineation fun (p : F) (x : C) ↦ p.1.map (eval₂Hom φ x.1)) :
    IsSemialgebraicStack C D.root := by
  have hder (x : C) (p : F) : Polynomial.derivative (p.1.map (eval₂Hom φ x.1)) = 0 ∨
      ∃ q : F, q.1.map (eval₂Hom φ x.1) = Polynomial.derivative (p.1.map (eval₂Hom φ x.1)) := by
    rw [Polynomial.derivative_map]
    obtain h0 | hmem := hF p.1 p.2
    · exact .inl (by rw [h0, Polynomial.map_zero])
    · exact .inr ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨D.continuous_root, D.strictMono_root, fun i ↦ ?_, fun j ↦ ?_⟩
  · exact isSemialgebraic_image_cylinder hC (fst_image_sectionSet _ i)
      (fun p ↦ D.signInvariant_sectionSet p i) fun x t t' ht h ↦
        (D.mk_mem_sectionSet_iff_of_sign_eval_eq (hder x) h i).1 ht
  · exact isSemialgebraic_image_cylinder hC (fst_image_sectorSet D.strictMono_root j)
      (fun p ↦ D.signInvariant_sectorSet p j) fun x t t' ht h ↦
        (D.mk_mem_sectorSet_iff_of_sign_eval_eq (hder x) h j).1 ht

end Stack

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
    -- the members of `F` in the distinguished variable, together with all their derivatives
    let G : Finset (MvPolynomial (Fin n) ℝ)[X] := (F.image (finSuccEquiv ℝ n)).biUnion
      fun p ↦ (Finset.range (p.natDegree + 2)).image fun m ↦ Polynomial.derivative^[m] p
    have hFG {f} (hf : f ∈ F) : finSuccEquiv ℝ n f ∈ G :=
      Finset.mem_biUnion.2 ⟨_, Finset.mem_image_of_mem _ hf,
        Finset.mem_image.2 ⟨0, by simp, rfl⟩⟩
    have hG : ∀ p ∈ G, Polynomial.derivative p ∈ G := by
      simp only [G, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
      rintro _ ⟨p, hp, m, hm, rfl⟩
      refine ⟨p, hp, min (m + 1) (p.natDegree + 1), by omega, ?_⟩
      rw [← iterate_succ_apply' Polynomial.derivative]
      rcases Nat.lt_or_ge m (p.natDegree + 1) with h | h
      · rw [min_eq_left h]
      · rw [Polynomial.iterate_derivative_eq_zero (by omega),
          Polynomial.iterate_derivative_eq_zero (by omega)]
    obtain ⟨𝒟, h𝒟, hproj⟩ := ih G.collinsProjection
    -- over each base cell, the stack of a delineation of the fibers of `G`
    have hstack (C : Set (Fin n → ℝ)) : ∃ (k : ℕ) (θ : Fin k → C → ℝ), C ∈ 𝒟 →
        IsSemialgebraicStack C θ ∧
          ∀ E ∈ stackCells C θ, ∀ f ∈ F, SignInvariant (fun y ↦ eval y f) E := by
      by_cases hC : C ∈ 𝒟
      · obtain ⟨D⟩ := nonempty_delineation_of_signInvariant_collinsProjection
          (φ := RingHom.id ℝ) (h𝒟.isConnected hC).isPreconnected fun q hq ↦ by
            simpa only [eval₂_id] using hproj q hq C hC
        refine ⟨D.count, D.root, fun _ ↦ ⟨D.isSemialgebraicStack (h𝒟.isSemialgebraic hC)
          fun p hp ↦ .inr (hG p hp),
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
