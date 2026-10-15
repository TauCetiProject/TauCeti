/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.DelineatingSet.Family
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.Lifting
public import TauCeti.Geometry.RealAlgebraic.Stack.Semialgebraic

/-!
# Order-invariant cylindrical algebraic decompositions by McCallum projection

McCallum's projection replaces the Collins projection by the contents, coefficients,
discriminants and pairwise resultants of an irreducible basis
(`Finset.mcCallumProjection`). It is correct under a well-orientedness assumption, and it then
produces a cylindrical algebraic decomposition whose cells are analytic submanifolds and on
whose cells every input polynomial is *order-invariant*: its ambient order of vanishing
`MvPolynomial.orderAt` is constant on each cell. Order-invariance implies sign-invariance on
connected cells (`IsPreconnected.signInvariant_eval_of_orderAt_eq`).

The lifting step takes a CAD of `ℝ ^ n` with analytic submanifold cells, on which the McCallum
projection of the family is order-invariant. Over a cell with more than one point, no basis
polynomial may be nullified; the cell then carries a common delineation of the basis
(`Finset.IsIrreducibleBasis.exists_delineation_orderAt_eq_of_mcCallumProjection`). Over a
single point, basis polynomials may be nullified, and the line over the point is refined by the
roots of the delineating polynomials of the inputs
(`Finset.exists_isSemialgebraicStack_orderAt_eq`). In both cases every input is order-invariant
on the resulting cells, which are again analytic submanifolds.

A finite family is *well-oriented* in McCallum's sense (`TauCeti.IsMcCallumWellOriented`) when,
at every level of the recursive projection, it has an irreducible basis each of whose members is
nullified at only finitely many points. On a cell where the projection is order-invariant, a
basis polynomial nullified at one point is nullified on the whole cell, because the projection
contains its coefficients. A connected cell inside a finite set is a point, so over a cell with
more than one point no basis polynomial is nullified, and the lifting step applies at every
level. Every family of polynomials in at most two variables is well-oriented.

## Main definitions and results

* `TauCeti.exists_isSemialgebraicStack_orderAt_eq_of_mcCallumProjection`: lifting over one cell.
* `TauCeti.IsCAD.exists_isCAD_orderAt_eq_of_mcCallumProjection`: lifting a CAD of `ℝ ^ n`
  adapted to the McCallum projection to a CAD of `ℝ ^ (n + 1)` adapted to the family.
* `TauCeti.IsMcCallumWellOriented`: McCallum's well-orientedness condition.
* `TauCeti.exists_isCAD_orderAt_eq_of_isMcCallumWellOriented`: **correctness of McCallum's
  projection**. A well-oriented family has a CAD into analytic submanifolds on whose cells every
  member is order-invariant.
* `TauCeti.isMcCallumWellOriented_one`, `TauCeti.isMcCallumWellOriented_two`: every family in
  one or two variables is well-oriented.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*, in
  *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998), 242–268,
  Section 5 (well-orientedness and the recursive algorithm).
* C. W. Brown, *The McCallum projection, lifting, and order-invariance*, technical report
  USNA-CS-TR-2005-02, U.S. Naval Academy (2005).
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti

variable {n : ℕ}

section Lifting

variable [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)} {B : Finset (MvPolynomial (Fin n) ℝ)[X]}

/-- **McCallum lifting over one cell.** Let `B` be an irreducible basis of a finite family `F` of
real polynomials in `n + 1` variables, with the distinguished variable `X 0` singled out, and let
`C ⊆ ℝ ^ n` be a semialgebraic, preconnected analytic submanifold on which every element of the
McCallum projection is order-invariant. If no member of `B` is nullified over `C` whenever `C` has
more than one point, then there is a semialgebraic stack over `C` whose cells are analytic
submanifolds, on each of which every member of `F` is order-invariant. -/
theorem exists_isSemialgebraicStack_orderAt_eq_of_mcCallumProjection
    (hB : (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B)
    {C : Set (Fin n → ℝ)} {d : ℕ} (hC : IsSemialgebraic C) (hCa : IsAnalyticSubmanifold d C)
    (hconn : IsPreconnected C)
    (hproj : ∀ q ∈ (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B,
      ∀ x ∈ C, ∀ y ∈ C, q.orderAt x = q.orderAt y)
    (hfiber : C.Nontrivial → ∀ b ∈ B, ∀ x ∈ C, b.map (MvPolynomial.eval x) ≠ 0) :
    ∃ (k : ℕ) (θ : Fin k → C → ℝ), IsSemialgebraicStack C θ ∧
      ∀ E ∈ stackCells C θ, (∃ e, IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F, ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  rcases C.subsingleton_or_nontrivial with hs | hnt
  · -- Over a point, refine the line by the roots of the delineating polynomials.
    obtain ⟨α, hα⟩ := hCa.nonempty
    obtain rfl := hs.eq_singleton_of_mem hα
    obtain ⟨k, c, hstack, -, -, hcells⟩ := F.exists_isSemialgebraicStack_orderAt_eq α
    exact ⟨k, _, hstack, fun E hE ↦
      ⟨(hcells E hE).1.imp fun _ h ↦ h.2, fun f hf ↦ ((hcells E hE).2 f hf).1⟩⟩
  · obtain ⟨D, hD⟩ :=
      hB.exists_delineation_orderAt_eq_of_mcCallumProjection hCa hconn (hfiber hnt) hproj
    refine ⟨D.count, D.root, D.isSemialgebraicStack (φ := RingHom.id ℝ) hC, fun E hE ↦
      ⟨(hD E hE).1.imp fun _ h ↦ h.2, fun f hf ↦ ?_⟩⟩
    simpa using ((hD E hE).2 (finSuccEquiv ℝ n f) (by simpa using hf)).1

/-- **McCallum lifting of a cylindrical algebraic decomposition.** Let `B` be an irreducible basis
of a finite family `F` of real polynomials in `n + 1` variables, with the distinguished variable
`X 0` singled out. Let `𝒟` be a CAD of `ℝ ^ n` into analytic submanifolds, on whose cells every
element of the McCallum projection is order-invariant, such that no member of `B` is nullified
over a cell with more than one point. Then `𝒟` lifts to a CAD of `ℝ ^ (n + 1)` into analytic
submanifolds, on whose cells every member of `F` is order-invariant. -/
theorem IsCAD.exists_isCAD_orderAt_eq_of_mcCallumProjection {𝒟 : Set (Set (Fin n → ℝ))}
    (h𝒟 : IsCAD n 𝒟) (hB : (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B)
    (hanalytic : ∀ C ∈ 𝒟, ∃ d, IsAnalyticSubmanifold d C)
    (hproj : ∀ q ∈ (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B,
      ∀ C ∈ 𝒟, ∀ x ∈ C, ∀ y ∈ C, q.orderAt x = q.orderAt y)
    (hfiber : ∀ C ∈ 𝒟, C.Nontrivial → ∀ b ∈ B, ∀ x ∈ C, b.map (MvPolynomial.eval x) ≠ 0) :
    ∃ 𝒞, IsCAD (n + 1) 𝒞 ∧ image Fin.tail '' 𝒞 = 𝒟 ∧
      (∀ E ∈ 𝒞, ∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ f ∈ F, ∀ E ∈ 𝒞, ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  have hstack (C : Set (Fin n → ℝ)) : ∃ (k : ℕ) (θ : Fin k → C → ℝ), C ∈ 𝒟 →
      IsSemialgebraicStack C θ ∧ ∀ E ∈ stackCells C θ, (∃ e, IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F, ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
    by_cases hC : C ∈ 𝒟
    · obtain ⟨d, hd⟩ := hanalytic C hC
      obtain ⟨k, θ, hθ⟩ := exists_isSemialgebraicStack_orderAt_eq_of_mcCallumProjection hB
        (h𝒟.isSemialgebraic hC) hd (h𝒟.isConnected hC).isPreconnected
        (fun q hq ↦ hproj q hq C hC) (hfiber C hC)
      exact ⟨k, θ, fun _ ↦ hθ⟩
    · exact ⟨0, Fin.elim0, fun h ↦ (hC h).elim⟩
  choose k θ hθ using hstack
  refine ⟨_, .succ k θ h𝒟 fun C hC ↦ (hθ C hC).1,
    image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).1.strictMono, fun E hE ↦ ?_,
    fun f hf E hE ↦ ?_⟩
  · obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    exact ((hθ C hC).2 E hE).1
  · obtain ⟨C, hC, hE⟩ := mem_iUnion₂.1 hE
    exact ((hθ C hC).2 E hE).2 f hf

end Lifting

/-! ### Well-oriented families -/

section WellOriented

variable [∀ m, NormalizedGCDMonoid (MvPolynomial (Fin m) ℝ)]

/-- A finite family `F` of real polynomials in `n` variables is *well-oriented* in McCallum's
sense if, when `n` is positive, singling out the distinguished variable `X 0` gives a family with
an irreducible basis `B` such that each member of `B` is nullified at only finitely many points of
`ℝ ^ (n - 1)`, and the McCallum projection of the family with respect to `B` is again
well-oriented. Every family of constants is well-oriented. -/
def IsMcCallumWellOriented : (n : ℕ) → Finset (MvPolynomial (Fin n) ℝ) → Prop
  | 0, _ => True
  | n + 1, F => ∃ B, (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B ∧
      (∀ b ∈ B, {x : Fin n → ℝ | b.map (MvPolynomial.eval x) = 0}.Finite) ∧
      IsMcCallumWellOriented n ((F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B)

/-- Every family of polynomials in no variables is well-oriented. -/
@[simp]
theorem isMcCallumWellOriented_zero (F : Finset (MvPolynomial (Fin 0) ℝ)) :
    IsMcCallumWellOriented 0 F :=
  trivial

/-- A family of polynomials in `n + 1` variables is well-oriented exactly when it has an
irreducible basis in the distinguished variable `X 0` whose members are nullified at finitely
many points, and whose McCallum projection is well-oriented. -/
theorem isMcCallumWellOriented_succ_iff {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)} :
    IsMcCallumWellOriented (n + 1) F ↔
      ∃ B, (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B ∧
        (∀ b ∈ B, {x : Fin n → ℝ | b.map (MvPolynomial.eval x) = 0}.Finite) ∧
        IsMcCallumWellOriented n
          ((F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B) :=
  Iff.rfl

/-- Every family of polynomials in one variable is well-oriented: its basis polynomials are
nullified at most at the single point of `ℝ ^ 0`. -/
@[simp]
theorem isMcCallumWellOriented_one (F : Finset (MvPolynomial (Fin 1) ℝ)) :
    IsMcCallumWellOriented 1 F := by
  obtain ⟨B, hB⟩ := (F.map (finSuccEquiv ℝ 0).toEquiv.toEmbedding).exists_isIrreducibleBasis
  exact ⟨B, hB, fun _ _ ↦ toFinite _, trivial⟩

/-- Every family of polynomials in two variables is well-oriented: a basis polynomial is nonzero,
so it has a nonzero coefficient, a polynomial in one variable with finitely many zeros. -/
@[simp]
theorem isMcCallumWellOriented_two (F : Finset (MvPolynomial (Fin 2) ℝ)) :
    IsMcCallumWellOriented 2 F := by
  obtain ⟨B, hB⟩ := (F.map (finSuccEquiv ℝ 1).toEquiv.toEmbedding).exists_isIrreducibleBasis
  refine ⟨B, hB, fun b hb ↦ ?_, isMcCallumWellOriented_one _⟩
  obtain ⟨i, hi⟩ : ∃ i, b.coeff i ≠ 0 := by
    by_contra! h
    exact (hB.irreducible b hb).ne_zero (Polynomial.ext h)
  -- The zeros of the coefficient are the roots of the corresponding univariate polynomial.
  let p := uniqueAlgEquiv ℝ (Fin 1) (b.coeff i)
  have hp : p ≠ 0 := (map_ne_zero_iff _ (uniqueAlgEquiv ℝ (Fin 1)).injective).2 hi
  refine (((finite_setOfPred_isRoot hp).image fun t (_ : Fin 1) ↦ t)).subset fun x hx ↦
    ⟨x 0, ?_, funext fun j ↦ by rw [Subsingleton.elim j 0]⟩
  have hx0 : MvPolynomial.eval x (b.coeff i) = 0 := by
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using congrArg (·.coeff i) hx
  have h := eval₂_uniqueAlgEquiv (f := b.coeff i) (φ := RingHom.id ℝ) (a := x)
  rw [Polynomial.eval₂_id, MvPolynomial.eval₂_id, hx0] at h
  exact IsRoot.def.2 h

/-- **Correctness of McCallum's projection.** A finite family of real polynomials that is
well-oriented in McCallum's sense has a cylindrical algebraic decomposition into analytic
submanifolds, on each cell of which every member of the family has constant ambient order. -/
theorem exists_isCAD_orderAt_eq_of_isMcCallumWellOriented {F : Finset (MvPolynomial (Fin n) ℝ)}
    (hF : IsMcCallumWellOriented n F) :
    ∃ 𝒞, IsCAD n 𝒞 ∧ (∀ E ∈ 𝒞, ∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ f ∈ F, ∀ E ∈ 𝒞, ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  induction n with
  | zero =>
    refine ⟨{univ}, .zero, fun E hE ↦ ⟨0, ?_⟩, fun f _ E _ y _ y' _ ↦ by
      rw [Subsingleton.elim y y']⟩
    rw [mem_singleton_iff.1 hE, univ_unique]
    exact isAnalyticSubmanifold_singleton _
  | succ n ih =>
    obtain ⟨B, hB, hfin, hP⟩ := hF
    obtain ⟨𝒟, h𝒟, hanalytic, hproj⟩ := ih hP
    -- A basis member nullified at one point of a cell is nullified on the whole cell, since the
    -- projection contains its coefficients; a connected cell inside a finite set is a point.
    have hfiber (C : Set (Fin n → ℝ)) (hC : C ∈ 𝒟) (hnt : C.Nontrivial) (b) (hb : b ∈ B)
        (x : Fin n → ℝ) (hx : x ∈ C) : b.map (MvPolynomial.eval x) ≠ 0 := by
      intro hbx
      refine hnt.not_subsingleton ((h𝒟.isConnected hC).isPreconnected.isDiscrete_iff_subsingleton.1
        ((hfin b hb).subset fun y hy ↦ ?_).isDiscrete)
      refine (Finset.map_eq_zero_iff_of_mcCallumProjection
        (F := F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding) (fun q hq ↦ ?_) hb).1 hbx
      rw [← MvPolynomial.orderAt_pos_iff, hproj q hq C hC x hx y hy, MvPolynomial.orderAt_pos_iff]
    obtain ⟨𝒞, h𝒞, -, h𝒞a, h𝒞o⟩ :=
      h𝒟.exists_isCAD_orderAt_eq_of_mcCallumProjection hB hanalytic hproj hfiber
    exact ⟨𝒞, h𝒞, h𝒞a, h𝒞o⟩

end WellOriented

end TauCeti
