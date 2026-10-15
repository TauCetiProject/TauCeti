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

import Mathlib.Algebra.MvPolynomial.Division

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

The hypothesis excluding nullification over cells with more than one point cannot be dropped
(`TauCeti.exists_nullified_mcCallumProjection_orderAt_ne`). Over the line `x₁ = x₂ = 0` of `ℝ ^ 3`,
the polynomial `X₂ (X₀ + 1) + X₃ X₁` is nullified, while its McCallum projection is
order-invariant. Above the line its order is one except at the single point `(-1, 0, 0, 0)`, where
it is at least two. Every cell of a stack lies over the whole line, so no stack over the line makes
it order-invariant. This is the failure condition of McCallum's lifting.

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
* `TauCeti.exists_nullified_mcCallumProjection_orderAt_ne`: lifting fails in general over a cell
  with more than one point on which a basis polynomial is nullified.
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

/-! ### Nullification over cells with more than one point -/

section Nullification

/-- The order of `X₂ (X₀ + 1) + X₃ X₁` is at least two at `(-1, 0, 0, 0)`, where all its first
partial derivatives vanish. -/
private lemma two_le_orderAt_nullificationExample {y : Fin 4 → ℝ} (h0 : y 0 = -1) (h1 : y 1 = 0)
    (h2 : y 2 = 0) (h3 : y 3 = 0) :
    2 ≤ (X 2 * (X 0 + 1) + X 3 * X 1 : MvPolynomial (Fin 4) ℝ).orderAt y := by
  rw [show (2 : ℕ∞) = 1 + 1 from rfl, succ_le_orderAt_iff]
  refine ⟨by simp [h0, h1, h2, h3], fun i ↦ ?_⟩
  rw [Order.one_le_iff_pos, orderAt_pos_iff]
  simp only [pderiv_X, Pi.single_apply, map_add, Derivation.leibniz]
  split_ifs <;> simp [h0, h1, h2, h3]

/-- The order of `X₂ (X₀ + 1) + X₃ X₁` is one at its zeros with `y₁ ≠ 0`, where its partial
derivative in `X₃` does not vanish. -/
private lemma orderAt_nullificationExample_eq_one {y : Fin 4 → ℝ} (h1 : y 1 ≠ 0) (h2 : y 2 = 0)
    (h3 : y 3 = 0) :
    (X 2 * (X 0 + 1) + X 3 * X 1 : MvPolynomial (Fin 4) ℝ).orderAt y = 1 :=
  orderAt_eq_one_of_eval_pderiv_ne_zero (by simp [h2, h3]) (i := 3) (by simpa [pderiv_X])

private lemma finSuccEquiv_nullificationExample :
    finSuccEquiv ℝ 3 (X 2 * (X 0 + 1) + X 3 * X 1) =
      Polynomial.C (X 1) * Polynomial.X + Polynomial.C (X 1 + X 2 * X 0) := by
  rw [show (2 : Fin 4) = (1 : Fin 3).succ from rfl, show (3 : Fin 4) = (2 : Fin 3).succ from rfl,
    show (1 : Fin 4) = (0 : Fin 3).succ from rfl]
  simp only [map_add, map_mul, finSuccEquiv_X_zero, finSuccEquiv_X_succ, map_one]
  ring

/-- The linear polynomial `X₁ T + (X₁ + X₂ X₀)` is irreducible, since its coefficients are
coprime, so it is its own irreducible basis. -/
private lemma isIrreducibleBasis_nullificationExample :
    ({Polynomial.C (X 1) * Polynomial.X + Polynomial.C (X 1 + X 2 * X 0)} :
      Finset (MvPolynomial (Fin 3) ℝ)[X]).IsIrreducibleBasis
      {Polynomial.C (X 1) * Polynomial.X + Polynomial.C (X 1 + X 2 * X 0)} := by
  have hirr : Irreducible (Polynomial.C (X 1 : MvPolynomial (Fin 3) ℝ) * Polynomial.X +
      Polynomial.C (X 1 + X 2 * X 0)) := by
    refine irreducible_C_mul_X_add_C (X_ne_zero _) <|
      (Irreducible.isRelPrime_iff_not_dvd (MvPolynomial.X_prime).irreducible).2 fun h ↦ ?_
    rw [dvd_add_right dvd_rfl, X_dvd_mul_iff] at h
    simp [X_dvd_X] at h
  refine ⟨by simpa using hirr, fun b hb ↦ ?_, by simp, fun f hf ↦ ⟨1, fun _ ↦ 1, by simp_all⟩,
    fun b hb ↦ ⟨b, hb, ?_, dvd_rfl⟩⟩
  · rw [Finset.mem_singleton.1 hb, natDegree_linear (X_ne_zero _)]
    exact one_pos
  · rw [Finset.mem_singleton.1 hb]
    exact hirr.ne_zero

variable [NormalizedGCDMonoid (MvPolynomial (Fin 3) ℝ)]

/-- **McCallum lifting fails over positive-dimensional nullifying cells.** The hypothesis of
`TauCeti.exists_isSemialgebraicStack_orderAt_eq_of_mcCallumProjection` that no basis member is
nullified over a cell with more than one point cannot be dropped, even over a connected
semialgebraic analytic submanifold on which the McCallum projection is order-invariant.

Explicitly, let `f = X₂ (X₀ + 1) + X₃ X₁`, a polynomial in the distinguished variable `X₀` and the
base coordinates `X₁, X₂, X₃`, and let `C ⊆ ℝ ^ 3` be the line of base points `x` with
`x₁ = x₂ = 0`. As a polynomial in `X₀`, `f` is linear with coprime coefficients `X₂` and
`X₂ + X₃ X₁`, each of which vanishes to order one at every point of `C`; its content and
discriminant are units. So for every irreducible basis `B` of `{f}`, every element of the McCallum
projection has constant order on `C`, while every member of `B` is nullified over `C`. But `f` has
order at least two at the point `(-1, 0, 0, 0)` above `C`, and order one at every point above
`C` where `X₀ ≠ -1` or `X₁ ≠ 0`. Since every cell of a stack over `C` lies over the whole of `C`,
no stack over `C`, given by pointwise strictly increasing functions, continuous or not, has `f`
order-invariant on each cell. -/
theorem exists_nullified_mcCallumProjection_orderAt_ne :
    ∃ (f : MvPolynomial (Fin 4) ℝ) (C : Set (Fin 3 → ℝ)), IsSemialgebraic C ∧
      IsAnalyticSubmanifold 1 C ∧ IsConnected C ∧
      ∀ B, (({f} : Finset _).map (finSuccEquiv ℝ 3).toEquiv.toEmbedding).IsIrreducibleBasis B →
        (∀ q ∈ (({f} : Finset _).map (finSuccEquiv ℝ 3).toEquiv.toEmbedding).mcCallumProjection B,
          ∀ x ∈ C, ∀ y ∈ C, q.orderAt x = q.orderAt y) ∧
        (∀ b ∈ B, ∀ x ∈ C, b.map (MvPolynomial.eval x) = 0) ∧
        ∀ (k : ℕ) (θ : Fin k → C → ℝ), (∀ x, StrictMono fun i ↦ θ i x) →
          ∃ E ∈ stackCells C θ, ∃ y ∈ E, ∃ y' ∈ E, f.orderAt y ≠ f.orderAt y' := by
  set C : Set (Fin 3 → ℝ) := {x | ∀ i : Fin 3, 1 ≤ i.val → x i = 0} with hC
  have hmem {x : Fin 3 → ℝ} : x ∈ C ↔ x 1 = 0 ∧ x 2 = 0 := by
    simp [hC, Fin.forall_fin_succ]
  have hCs : IsSemialgebraic C := by
    convert (isSemialgebraic_eval_eq_zero (X 1 : MvPolynomial (Fin 3) ℝ)).inter
      (isSemialgebraic_eval_eq_zero (X 2)) using 1
    ext x
    simp [hmem]
  have hCc : IsConnected C := by
    convert isConnected_range (firstCoords ℝ 1 3).continuous
    ext x
    refine ⟨fun hx ↦ ⟨firstCoords ℝ 3 1 x, firstCoords_firstCoords_of_forall hx⟩, ?_⟩
    rintro ⟨u, rfl⟩ i hi
    exact firstCoords_apply_of_le u hi
  set g : (MvPolynomial (Fin 3) ℝ)[X] :=
    Polynomial.C (X 1) * Polynomial.X + Polynomial.C (X 1 + X 2 * X 0) with hg
  have hF : (({X 2 * (X 0 + 1) + X 3 * X 1} : Finset (MvPolynomial (Fin 4) ℝ)).map
      (finSuccEquiv ℝ 3).toEquiv.toEmbedding) = {g} := by
    simp [finSuccEquiv_nullificationExample, hg]
  refine ⟨X 2 * (X 0 + 1) + X 3 * X 1, C, hCs, isAnalyticSubmanifold_coordSubspace (by norm_num),
    hCc, fun B hB ↦ ?_⟩
  rw [hF] at hB ⊢
  have h₀ : ({g} : Finset _).IsIrreducibleBasis {g} := isIrreducibleBasis_nullificationExample
  refine ⟨fun q hq x hx y hy ↦ ?_, fun b hb x hx ↦ ?_, fun k θ hθ ↦ ?_⟩
  · -- Every element of the projection is associated to one for the basis `{g}`: the content `1`,
    -- the two coefficients of `g`, each of order one along `C`, and the discriminant `1`.
    obtain ⟨q', hq', hqq'⟩ := h₀.exists_associated_mem_mcCallumProjection hB hq
    rw [orderAt_eq_of_associated hqq', orderAt_eq_of_associated hqq']
    have hX₁ {z : Fin 3 → ℝ} (hz : z ∈ C) : (X 1 : MvPolynomial (Fin 3) ℝ).orderAt z = 1 := by
      simpa [(hmem.1 hz).1] using orderAt_X_sub_C (R := ℝ) z 1
    have hcoeff {z : Fin 3 → ℝ} (hz : z ∈ C) :
        (X 1 + X 2 * X 0 : MvPolynomial (Fin 3) ℝ).orderAt z = 1 :=
      orderAt_eq_one_of_eval_pderiv_ne_zero (by simp [(hmem.1 hz).1, (hmem.1 hz).2]) (i := 1)
        (by simp [pderiv_X])
    rcases Finset.mem_mcCallumProjection.1 hq' with ⟨f, hf, rfl⟩ | ⟨b, hb, i, hi, rfl⟩ |
      ⟨b, hb, rfl⟩ | ⟨b, hb, b', hb', hne, -⟩
    · rw [(h₀.isPrimitive hf).content_eq_one, orderAt_one, orderAt_one]
    · obtain rfl := Finset.mem_singleton.1 hb
      rw [hg, natDegree_linear (X_ne_zero _)] at hi
      interval_cases i <;> simp [hg, hX₁ hx, hX₁ hy, hcoeff hx, hcoeff hy]
    · rw [Finset.mem_singleton.1 hb, discr_of_degree_eq_one (degree_linear (X_ne_zero _)),
        orderAt_one, orderAt_one]
    · exact (hne ((Finset.mem_singleton.1 hb).trans (Finset.mem_singleton.1 hb').symm)).elim
  · obtain ⟨b', hb', r, -, rfl⟩ := hB.exists_eq_C_mul h₀ hb
    simp [Finset.mem_singleton.1 hb', hg, (hmem.1 hx).1, (hmem.1 hx).2]
  · -- The point `(-1, 0, 0, 0)` lies in a cell, which also contains a point over `(1, 0, 0)`.
    obtain ⟨E, hE, hy₀E⟩ : ![-1, 0, 0, 0] ∈ ⋃₀ stackCells C θ := by
      rw [sUnion_stackCells fun x ↦ (hθ x).monotone]
      simp [hmem]
    obtain ⟨y, hyE, hy⟩ : ![(1 : ℝ), 0, 0] ∈ Fin.tail '' E := by
      rw [image_tail_of_mem_stackCells hθ hE]
      simp [hmem]
    have h₁ : y 1 = 1 := by simpa [Fin.tail] using congrFun hy 0
    have h₂ : y 2 = 0 := by simpa [Fin.tail] using congrFun hy 1
    have h₃ : y 3 = 0 := by simpa [Fin.tail] using congrFun hy 2
    refine ⟨E, hE, _, hy₀E, y, hyE, ne_of_gt ?_⟩
    rw [orderAt_nullificationExample_eq_one (by simp [h₁]) h₂ h₃]
    exact (show (1 : ℕ∞) < 2 by norm_num).trans_le
      (two_le_orderAt_nullificationExample rfl rfl rfl rfl)

end Nullification

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
