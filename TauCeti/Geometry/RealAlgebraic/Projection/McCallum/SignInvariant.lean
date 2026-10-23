/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.SquarefreeBasis
public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.Lifting
public import TauCeti.Geometry.RealAlgebraic.Stack.Semialgebraic

import TauCeti.Algebra.Squarefree
import TauCeti.RingTheory.Derivation.Basic

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

Nor can its hypothesis be weakened to sign-invariance of the projection. For the squarefree cubic
`(T - 1)² (T - 1 - x₀²) + x₁` over the line `x₁ = 0`, the McCallum projection is sign-invariant,
its discriminant vanishing identically there, but the two fibre roots `1` and `1 + x₀²` merge at
the origin, and no stack over the line makes the cubic sign-invariant
(`TauCeti.exists_signInvariant_mcCallumProjection_stackCells_not_signInvariant`). So on the lower
levels of a CAD built by McCallum projection, sign-invariance cannot replace order-invariance.

## Main results

* `Finset.IsSquarefreeBasis.exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection`:
  sign-invariant lifting over a base on which the McCallum projection is order-invariant.
* `TauCeti.exists_signInvariant_mcCallumProjection_stackCells_not_signInvariant`: sign-invariance
  of the McCallum projection does not suffice.

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

/-! ### Sign-invariance of the projection does not suffice -/

namespace TauCeti

section SignInvariantProjection

/-- The cubic `(T - 1)² (T - 1 - x₀²) + x₁` in the distinguished variable `T` over `ℝ[x₀, x₁]`.
Over the line `x₁ = 0` its fibre `(T - 1)² (T - 1 - x₀²)` has the two roots `1` and `1 + x₀²`,
which merge into a triple root at `x₀ = 0`. -/
private noncomputable def signInvariantExample : (MvPolynomial (Fin 2) ℝ)[X] :=
  (Polynomial.X - 1) ^ 2 * (Polynomial.X - Polynomial.C (1 + MvPolynomial.X 0 ^ 2)) +
    Polynomial.C (MvPolynomial.X 1)

private lemma signInvariantExample_eq :
    signInvariantExample = Polynomial.X ^ 3 - Polynomial.C (3 + MvPolynomial.X 0 ^ 2) *
      Polynomial.X ^ 2 + Polynomial.C (3 + 2 * MvPolynomial.X 0 ^ 2) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 1 - 1 - MvPolynomial.X 0 ^ 2) := by
  simp only [signInvariantExample, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

private lemma natDegree_signInvariantExample : signInvariantExample.natDegree = 3 := by
  rw [signInvariantExample_eq]
  compute_degree!

private lemma monic_signInvariantExample : signInvariantExample.Monic := by
  rw [signInvariantExample_eq]
  monicity!

private lemma map_eval_signInvariantExample (x : Fin 2 → ℝ) :
    signInvariantExample.map (MvPolynomial.eval x) =
      (Polynomial.X - 1) ^ 2 * (Polynomial.X - Polynomial.C (1 + x 0 ^ 2)) +
        Polynomial.C (x 1) := by
  simp [signInvariantExample, Polynomial.map_sub]

private lemma eval_cons_signInvariantExample (t : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval (Fin.cons t x) ((finSuccEquiv ℝ 2).symm signInvariantExample) =
      (t - 1) ^ 2 * (t - (1 + x 0 ^ 2)) + x 1 := by
  rw [eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply, map_eval_signInvariantExample]
  simp

/-- The example is `(X₀ - 1)² (X₀ - 1 - X₁²) + X₂` in the ambient variables, whose partial
derivative in `X₂` is `1`; so it is squarefree. -/
private lemma squarefree_signInvariantExample : Squarefree signInvariantExample := by
  have h : finSuccEquiv ℝ 2 ((MvPolynomial.X 0 - 1) ^ 2 *
      (MvPolynomial.X 0 - 1 - MvPolynomial.X 1 ^ 2) + MvPolynomial.X 2) =
      signInvariantExample := by
    rw [← Fin.succ_one_eq_two' (n := 1), ← Fin.succ_zero_eq_one' (n := 2)]
    simp only [signInvariantExample, map_add, map_sub, map_mul, map_pow, map_one,
      finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    ring
  rw [← h, squarefree_map_iff]
  refine (pderiv 2).squarefree_of_isUnit ?_
  simp [pderiv_X]

/-- The line `x₁ = 0` in `ℝ ^ 2`, written as the coordinate subspace of the first coordinate. -/
private def signInvariantExampleLine : Set (Fin 2 → ℝ) :=
  {x | ∀ i : Fin 2, 1 ≤ i.val → x i = 0}

private lemma mem_signInvariantExampleLine {x : Fin 2 → ℝ} :
    x ∈ signInvariantExampleLine ↔ x 1 = 0 := by
  simp [signInvariantExampleLine, Fin.forall_fin_two]

private lemma isSquarefreeBasis_signInvariantExample :
    ({signInvariantExample} : Finset _).IsSquarefreeBasis {signInvariantExample} := by
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_, fun b hb ↦ ?_, fun b hb b' hb' hne ↦ ?_,
    fun b hb ↦ ⟨1, fun _ ↦ 1, ?_⟩⟩ <;> rw [Finset.mem_singleton] at hb <;> subst hb
  · exact monic_signInvariantExample.isPrimitive
  · rw [natDegree_signInvariantExample]
    norm_num
  · exact squarefree_signInvariantExample
  · exact (hne (Finset.mem_singleton.1 hb').symm).elim
  · simp

/-- The coefficients `-(1 + x₀²)`, `3 + 2 x₀²`, `-(3 + x₀²)` and `1` of the example have
constant signs on the line `x₁ = 0`. -/
private lemma exists_sign_eval_coeff_signInvariantExample {i : ℕ} (hi : i ≤ 3) :
    ∃ σ : SignType, ∀ y ∈ signInvariantExampleLine,
      SignType.sign (MvPolynomial.eval y (signInvariantExample.coeff i)) = σ := by
  interval_cases i <;>
    simp only [signInvariantExample_eq, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  · refine ⟨-1, fun y hy ↦ sign_neg ?_⟩
    norm_num [mem_signInvariantExampleLine.1 hy]
    nlinarith [sq_nonneg (y 0)]
  · refine ⟨1, fun y _ ↦ sign_pos ?_⟩
    norm_num
    positivity
  · refine ⟨-1, fun y _ ↦ sign_neg ?_⟩
    norm_num
    nlinarith [sq_nonneg (y 0)]
  · exact ⟨1, fun y _ ↦ sign_pos (by norm_num)⟩

/-- The discriminant of the example vanishes on the line `x₁ = 0`, where each fibre
`(T - 1)² (T - 1 - x₀²)` has a double root. -/
private lemma eval_discr_signInvariantExample {x : Fin 2 → ℝ}
    (hx : x ∈ signInvariantExampleLine) :
    MvPolynomial.eval x signInvariantExample.discr = 0 := by
  rw [← monic_signInvariantExample.discr_map, ← not_ne_iff,
    (monic_signInvariantExample.map _).discr_ne_zero_iff, map_eval_signInvariantExample,
    mem_signInvariantExampleLine.1 hx, map_zero, add_zero]
  intro hsep
  exact not_isUnit_X_sub_C (1 : ℝ) (hsep.squarefree _ ⟨_, by rw [map_one, sq, mul_assoc]⟩)

/-- Over a point of the line `x₁ = 0`, a cell of a stack containing a zero of the example contains
its only zero `(T, x₀, x₁) = (1, 0, 0)` over the origin, since every cell lies over the whole
line. -/
private lemma cons_mem_of_mem_stackCells_signInvariantExample {k : ℕ}
    {θ : Fin k → signInvariantExampleLine → ℝ} (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    {E : Set (Fin 3 → ℝ)} (hE : E ∈ stackCells signInvariantExampleLine θ)
    (hsign : SignInvariant
      (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ 2).symm signInvariantExample)) E)
    {p : Fin 3 → ℝ} (hp : p ∈ E)
    (hv : MvPolynomial.eval p ((finSuccEquiv ℝ 2).symm signInvariantExample) = 0) :
    (Fin.cons 1 ![0, 0] : Fin 3 → ℝ) ∈ E := by
  obtain ⟨y, hyE, hy⟩ : ![(0 : ℝ), 0] ∈ Fin.tail '' E := by
    rw [image_tail_of_mem_stackCells hθ hE]
    simp [mem_signInvariantExampleLine]
  have hyc : Fin.cons (y 0) ![0, 0] = y := by rw [← hy, Fin.cons_self_tail]
  have h := signInvariant_def.1 hsign y hyE p hp
  rw [hv, sign_zero, sign_eq_zero_iff, ← hyc, eval_cons_signInvariantExample] at h
  have h1 : y 0 = 1 := by
    have : (y 0 - 1) ^ 3 = 0 := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      linear_combination h
    linarith [pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this]
  rwa [← h1, hyc]

/-- No stack over the line `x₁ = 0` has the example sign-invariant on each of its cells. The
cells through the zeros `(1, 1, 0)` and `(2, 1, 0)` both contain `(1, 0, 0)`, so they coincide,
and then contain `(3 / 2, 1, 0)`, where the example is negative. -/
private lemma exists_not_signInvariant_stackCells_signInvariantExample (k : ℕ)
    (θ : Fin k → signInvariantExampleLine → ℝ) (hθ : ∀ x, StrictMono fun i ↦ θ i x) :
    ∃ E ∈ stackCells signInvariantExampleLine θ, ¬ SignInvariant
      (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ 2).symm signInvariantExample)) E := by
  by_contra! hsign
  have hmem (t : ℝ) :
      (Fin.cons t ![1, 0] : Fin 3 → ℝ) ∈ ⋃₀ stackCells signInvariantExampleLine θ := by
    rw [sUnion_stackCells fun x ↦ (hθ x).monotone]
    simp [mem_signInvariantExampleLine]
  have hv (t : ℝ) : MvPolynomial.eval (Fin.cons t ![1, 0])
      ((finSuccEquiv ℝ 2).symm signInvariantExample) = (t - 1) ^ 2 * (t - 2) := by
    rw [eval_cons_signInvariantExample]
    norm_num
  obtain ⟨E, hE, h₁⟩ := hmem 1
  obtain ⟨E', hE', h₂⟩ := hmem 2
  obtain rfl : E = E' := (pairwiseDisjoint_stackCells fun x ↦ (hθ x).injective).elim_set hE hE' _
    (cons_mem_of_mem_stackCells_signInvariantExample hθ hE (hsign E hE) h₁ (by rw [hv]; norm_num))
    (cons_mem_of_mem_stackCells_signInvariantExample hθ hE' (hsign E' hE') h₂
      (by rw [hv]; norm_num))
  have h₃ : (Fin.cons (3 / 2) ![1, 0] : Fin 3 → ℝ) ∈ E :=
    (ordConnected_setOf_cons_mem_of_mem_stackCells hE ![1, 0]).out h₁ h₂ ⟨by norm_num, by norm_num⟩
  have h := signInvariant_def.1 (hsign E hE) _ h₃ _ h₁
  rw [hv, hv] at h
  norm_num at h

variable [NormalizedGCDMonoid (MvPolynomial (Fin 2) ℝ)]

/-- The McCallum projection of the example, its content `1`, its coefficients and its
discriminant, is sign-invariant on the line `x₁ = 0`. -/
private lemma signInvariant_mcCallumProjection_signInvariantExample {q : MvPolynomial (Fin 2) ℝ}
    (hq : q ∈ ({signInvariantExample} : Finset _).mcCallumProjection {signInvariantExample}) :
    SignInvariant (fun x ↦ MvPolynomial.eval x q) signInvariantExampleLine := by
  rw [signInvariant_iff_exists]
  rcases Finset.mem_mcCallumProjection.1 hq with ⟨b, hb, rfl⟩ | ⟨b, hb, i, hi, rfl⟩ |
    ⟨b, hb, rfl⟩ | ⟨b, hb, b', hb', hne, -⟩ <;> rw [Finset.mem_singleton] at hb <;> subst hb
  · refine ⟨1, fun y _ ↦ ?_⟩
    rw [monic_signInvariantExample.isPrimitive.content_eq_one, map_one, sign_one]
  · exact exists_sign_eval_coeff_signInvariantExample (natDegree_signInvariantExample ▸ hi)
  · exact ⟨0, fun y hy ↦ by simp [eval_discr_signInvariantExample hy]⟩
  · exact (hne (Finset.mem_singleton.1 hb').symm).elim

/-- **Sign-invariance of the McCallum projection does not suffice for lifting.** In
`Finset.IsSquarefreeBasis.exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection`, the
hypothesis that the McCallum projection is order-invariant on the base cannot be weakened to
sign-invariance, even for a nonnullified squarefree basis over a connected semialgebraic
analytic submanifold. So a lower level of a CAD that is merely sign-invariant for the projection
cannot replace an order-invariant one.

Explicitly, let `f = (T - 1)² (T - 1 - x₀²) + x₁`, a monic cubic in the distinguished variable
`T` over `ℝ[x₀, x₁]`, and let `S ⊆ ℝ ^ 2` be the line `x₁ = 0`. As `f` is squarefree, it is its
own squarefree basis. Over `S` its coefficients `1`, `-(3 + x₀²)`, `3 + 2 x₀²` and `-(1 + x₀²)`
have constant signs, its content is `1`, and its discriminant vanishes, because each fibre
`(T - 1)² (T - 1 - x₀²)` has a double root. So the McCallum projection of `{f}` is sign-invariant
on `S`, and some member of it has nonconstant order on `S`; since the other members do not vanish
on `S`, this is the discriminant. But the fibre has the two roots `1` and `2` over `(1, 0)` and
the single root `1` over the origin. In the coordinates `(T, x₀, x₁)`, every cell of a stack over
`S` lies over all of `S`, so the cells through the zeros `(1, 1, 0)` and `(2, 1, 0)` of `f` would
both contain its only zero `(1, 0, 0)` over the origin, hence coincide, and then also contain
`(3 / 2, 1, 0)`, where `f` is negative. So no stack over `S`, given by pointwise strictly
increasing functions, continuous or not, has `f` sign-invariant on each cell. -/
theorem exists_signInvariant_mcCallumProjection_stackCells_not_signInvariant :
    ∃ (f : (MvPolynomial (Fin 2) ℝ)[X]) (S : Set (Fin 2 → ℝ)),
      ({f} : Finset _).IsSquarefreeBasis {f} ∧ IsSemialgebraic S ∧
      IsAnalyticSubmanifold 1 S ∧ IsConnected S ∧
      (∀ x ∈ S, f.map (MvPolynomial.eval x) ≠ 0) ∧
      (∀ q ∈ ({f} : Finset _).mcCallumProjection {f},
        SignInvariant (fun x ↦ MvPolynomial.eval x q) S) ∧
      (∃ q ∈ ({f} : Finset _).mcCallumProjection {f}, ∃ x ∈ S, ∃ y ∈ S,
        q.orderAt x ≠ q.orderAt y) ∧
      ∀ (k : ℕ) (θ : Fin k → S → ℝ), (∀ x, StrictMono fun i ↦ θ i x) →
        ∃ E ∈ stackCells S θ,
          ¬ SignInvariant (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ 2).symm f)) E := by
  have hSs : IsSemialgebraic signInvariantExampleLine := by
    convert isSemialgebraic_eval_eq_zero (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) using 1
    ext x
    simp [mem_signInvariantExampleLine]
  have hSc : IsConnected signInvariantExampleLine := by
    convert isConnected_range (firstCoords ℝ 1 2).continuous
    ext x
    refine ⟨fun hx ↦ ⟨firstCoords ℝ 2 1 x, firstCoords_firstCoords_of_forall hx⟩, ?_⟩
    rintro ⟨u, rfl⟩ i hi
    exact firstCoords_apply_of_le u hi
  have hSa : IsAnalyticSubmanifold 1 signInvariantExampleLine :=
    isAnalyticSubmanifold_coordSubspace (by norm_num)
  refine ⟨signInvariantExample, signInvariantExampleLine, isSquarefreeBasis_signInvariantExample,
    hSs, hSa, hSc, fun x _ ↦ (monic_signInvariantExample.map _).ne_zero,
    fun q hq ↦ signInvariant_mcCallumProjection_signInvariantExample hq, ?_,
    exists_not_signInvariant_stackCells_signInvariantExample⟩
  -- Order-invariance of the projection would give, by the order-invariant lifting theorem, a
  -- stack on which the example is sign-invariant.
  by_contra! hord
  obtain ⟨k, θ, hθ, hsign⟩ :=
    Finset.IsSquarefreeBasis.exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection
      isSquarefreeBasis_signInvariantExample hSa hSc.isPreconnected hSs hord
  obtain ⟨E, hE, hnot⟩ := exists_not_signInvariant_stackCells_signInvariantExample k θ hθ.strictMono
  exact hnot ((hsign E hE).2 _ (Finset.mem_singleton_self _))

end SignInvariantProjection

end TauCeti
