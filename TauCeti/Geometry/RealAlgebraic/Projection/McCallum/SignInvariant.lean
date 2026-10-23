/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.SquarefreeBasis
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.Lifting
public import TauCeti.Geometry.RealAlgebraic.Stack.Semialgebraic

/-!
# Sign-invariant McCallum lifting with nullified members

Over a connected semialgebraic analytic base on which the McCallum projection is
order-invariant, construct a sign-invariant semialgebraic stack for the original family.
No nonnullification hypothesis is required: coefficient orders make nullification constant
on the base, and only the nonnullified basis members participate in root lifting. The
remaining members vanish on the entire cylinder. Contents are retained when reconstructing
input signs.

This is suitable for the final lift of a sign-invariant CAD. It does not assert ambient
order-invariance on the lifted cells, which nullified members need not satisfy, and thus
cannot replace order-invariant lifting at intermediate levels.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Sections 2–3.
* C. W. Brown, *The McCallum projection, lifting, and order-invariance* (2005).
-/

public section

open MvPolynomial Polynomial Set

namespace Finset.IsSquarefreeBasis

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- **Final sign-invariant McCallum lifting.** Order-invariance of the projection on a
preconnected semialgebraic analytic submanifold gives a semialgebraic stack with analytic
cells on which every input is sign-invariant. Basis members may be nullified, even on a
positive-dimensional base; no ambient-order conclusion is asserted for the lifted inputs. -/
theorem exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection
    (hB : F.IsSquarefreeBasis B) (hS : TauCeti.IsAnalyticSubmanifold d S)
    (hconn : IsPreconnected S) (hsemi : TauCeti.IsSemialgebraic S)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.orderAt x = q.orderAt y) :
    ∃ k, ∃ θ : Fin k → S → ℝ, TauCeti.IsSemialgebraicStack S θ ∧
      ∀ E ∈ TauCeti.stackCells S θ,
        (∃ e, (e = d ∨ e = d + 1) ∧ TauCeti.IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F, TauCeti.SignInvariant
          (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ n).symm f)) E := by
  classical
  have hzero (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S)
      (q : MvPolynomial (Fin n) ℝ) (hq : q ∈ F.mcCallumProjection B) :
      MvPolynomial.eval x q = 0 ↔ MvPolynomial.eval y q = 0 :=
    TauCeti.eval_eq_zero_iff_of_orderAt_eq (hproj q hq x hx y hy)
  have hnull (b : Polynomial (MvPolynomial (Fin n) ℝ)) (hb : b ∈ B)
      (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      b.map (MvPolynomial.eval x) = 0 ↔ b.map (MvPolynomial.eval y) = 0 :=
    Finset.map_eq_zero_iff_of_mcCallumProjection (hzero x hx y hy) hb
  -- The active subfamily is fixed on the whole base, not chosen separately in each fiber.
  let A := B.filter fun b ↦ ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0
  have hAB : A ⊆ B := Finset.filter_subset _ _
  obtain ⟨D, -⟩ := TauCeti.exists_delineation_orderAt_prod_eq_of_mcCallumProjection hB hAB hS hconn
    (fun b hb ↦ (Finset.mem_filter.mp hb).2) hproj
  refine ⟨D.count, D.root, D.isSemialgebraicStack hsemi, fun E hE ↦
    ⟨D.exists_isAnalyticSubmanifold_of_mem_stackCells hS
      (fun (b : A) j ↦ hS.analyticOnSubmanifold_coeff_map_eval b.1 j) hE, fun f hf ↦ ?_⟩⟩
  have htail (y : Fin (n + 1) → ℝ) (hy : y ∈ E) : Fin.tail y ∈ S := by
    rw [← TauCeti.image_tail_of_mem_stackCells D.strictMono_root hE]
    exact Set.mem_image_of_mem Fin.tail hy
  apply hB.signInvariant_eval hf
  · have hc := hconn.signInvariant_eval_of_orderAt_eq
      (hproj f.content (Finset.content_mem_mcCallumProjection hf))
    rw [TauCeti.signInvariant_def] at hc ⊢
    exact fun y hy y' hy' ↦ hc _ (htail y hy) _ (htail y' hy')
  · intro b hb
    by_cases hbA : b ∈ A
    · simpa only [AlgEquiv.apply_symm_apply, MvPolynomial.eval₂_id] using
        D.signInvariant_eval₂_of_mem_stackCells (φ := RingHom.id ℝ)
          (f := (finSuccEquiv ℝ n).symm b) (by simpa using hbA) hE
    · have hvanish (x : Fin n → ℝ) (hx : x ∈ S) : b.map (MvPolynomial.eval x) = 0 := by
        by_contra hne
        apply hbA
        exact Finset.mem_filter.mpr ⟨hb, fun y hy ↦
          (hnull b hb y hy x hx).not.mpr hne⟩
      refine (TauCeti.signInvariant_const 0).congr fun y hy ↦ ?_
      symm
      conv_lhs => rw [← Fin.cons_self_tail y]
      rw [eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply, hvanish _ (htail y hy),
        Polynomial.eval_zero]

end Finset.IsSquarefreeBasis
