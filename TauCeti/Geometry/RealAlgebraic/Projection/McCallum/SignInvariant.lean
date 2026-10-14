/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.IrreducibleBasis
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

namespace Finset.IsIrreducibleBasis

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- Any nonnullified subfamily of an irreducible basis has a common delineation over a
preconnected analytic submanifold on which the original McCallum projection is
order-invariant. In particular, nullified members outside the subfamily cause no obstruction. -/
theorem nonempty_delineation_of_mcCallumProjection
    (hB : F.IsIrreducibleBasis B) {A : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hAB : A ⊆ B) (hS : TauCeti.IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hfiber : ∀ b ∈ A, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.orderAt x = q.orderAt y) :
    Nonempty (TauCeti.Delineation fun (b : A) (x : S) ↦ b.1.map (MvPolynomial.eval x.1)) := by
  classical
  have hdegree (b : A) (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      (b.1.map (MvPolynomial.eval x)).natDegree =
        (b.1.map (MvPolynomial.eval y)).natDegree := by
    apply Finset.natDegree_map_eq_of_mcCallumProjection (F := F) (hb := hAB b.2)
    intro q hq
    rw [← MvPolynomial.orderAt_pos_iff, hproj q hq x hx y hy,
      MvPolynomial.orderAt_pos_iff]
  let p : Polynomial (MvPolynomial (Fin n) ℝ) := ∏ b : A, b.1
  have hp_eq : p = ∏ b ∈ A, b := Finset.prod_coe_sort A fun b ↦ b
  have hp_discr_ne : p.discr ≠ 0 := by
    rw [hp_eq]
    exact hB.discr_prod_ne_zero hAB
  have hp_discr (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      p.discr.orderAt x = p.discr.orderAt y := by
    rw [hp_eq]
    exact hB.orderAt_discr_prod_eq_of_mcCallumProjection hAB x y
      (fun q hq ↦ hproj q hq x hx y hy)
  -- Glue chart-local delineations; no section invariant is needed for this conclusion.
  obtain ⟨D, -⟩ := TauCeti.exists_delineation_of_locally_chart
    (d := d) (P := fun (b : A) x ↦ b.1.map (MvPolynomial.eval x))
    (q := fun _ _ ↦ ()) hconn fun x hx ↦ by
      obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
      obtain ⟨V, hV, hxV, D, -⟩ := he.exists_delineation_orderAt_prod_eq
        (P := fun b : A ↦ b.1) hxe hx (fun b ↦ hfiber b b.2) hdegree hp_discr_ne hp_discr
      exact ⟨e, he, hxe, V, hV, hxV, D, fun _ _ _ ↦ rfl⟩
  exact ⟨D⟩

/-- **Final sign-invariant McCallum lifting.** Order-invariance of the projection on a
preconnected semialgebraic analytic submanifold gives a semialgebraic stack with analytic
cells on which every input is sign-invariant. Basis members may be nullified, even on a
positive-dimensional base; no ambient-order conclusion is asserted for the lifted inputs. -/
theorem exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection
    (hB : F.IsIrreducibleBasis B) (hS : TauCeti.IsAnalyticSubmanifold d S)
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
      MvPolynomial.eval x q = 0 ↔ MvPolynomial.eval y q = 0 := by
    rw [← MvPolynomial.orderAt_pos_iff, hproj q hq x hx y hy,
      MvPolynomial.orderAt_pos_iff]
  have hnull (b : Polynomial (MvPolynomial (Fin n) ℝ)) (hb : b ∈ B)
      (x : Fin n → ℝ) (hx : x ∈ S) (y : Fin n → ℝ) (hy : y ∈ S) :
      b.map (MvPolynomial.eval x) = 0 ↔ b.map (MvPolynomial.eval y) = 0 :=
    Finset.map_eq_zero_iff_of_mcCallumProjection (hzero x hx y hy) hb
  -- The active subfamily is fixed on the whole base, not chosen separately in each fiber.
  let A := B.filter fun b ↦ ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0
  have hAB : A ⊆ B := Finset.filter_subset _ _
  obtain ⟨D⟩ := hB.nonempty_delineation_of_mcCallumProjection hAB hS hconn
    (fun b hb ↦ (Finset.mem_filter.mp hb).2) hproj
  have hcoeff : ∀ (b : A) (j : ℕ), TauCeti.AnalyticOnSubmanifold d
      (fun x ↦ (b.1.map (MvPolynomial.eval x)).coeff j) S := by
    intro b j
    simp only [Polynomial.coeff_map]
    exact ((AnalyticOnNhd.eval_continuousLinearMap
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) (b.1.coeff j)).mono
        (Set.subset_univ S)).analyticOnSubmanifold hS
  refine ⟨D.count, D.root, D.isSemialgebraicStack hsemi, fun E hE ↦
    ⟨D.exists_isAnalyticSubmanifold_of_mem_stackCells hS hcoeff hE, fun f hf ↦ ?_⟩⟩
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
      have heval := MvPolynomial.polynomial_eval_map_finSuccEquiv
        (φ := RingHom.id ℝ) (s := Fin.tail y) (y := y 0)
        (f := (finSuccEquiv ℝ n).symm b)
      rw [← MvPolynomial.eval] at heval
      simpa only [AlgEquiv.apply_symm_apply, MvPolynomial.eval₂_id, Fin.cons_self_tail,
        hvanish _ (htail y hy), Polynomial.eval_zero] using heval

end Finset.IsIrreducibleBasis
