/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
-- Proof-only: the pure-power coefficients of a formal group law, the symmetric 2-cocycle lemma,
-- lowest-degree parts of substitutions, two-variable substitution identities, and the
-- permutations of `Fin 2`.
import TauCeti.Data.Fin.Basic
import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The obstruction to extending a homomorphism of formal group laws

Let `F` and `G` be commutative formal group laws over a commutative ring `R`, and let `f` be a
power series without constant term which is a homomorphism from `F` to `G` up to degree `n`: the
**homomorphism defect** `f(F(X, Y)) - G(f(X), f(Y))` (`FormalGroup.homDefect`) vanishes below
degree `n`. Its degree-`n` part is the obstruction to improving `f` to a homomorphism up to degree
`n + 1`. This file shows that the obstruction is a multiple `c C_n` of the Lazard cocycle
`C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`, and that when `n = pᵏ` and `p = 0` in `R`, the scalar `c` is the
coefficient of `Xⁿ` in `[p]_G(f(X)) - f([p]_F(X))`. Since `d_n` is a unit in `R` unless `n` is a
power of `p`, only the degrees `pᵏ` carry a genuine obstruction, and it is read off the
`p`-series: this is the degree-by-degree mechanism behind Lazard's classification of formal group
laws over separably closed fields by their height.

The argument takes place in the group `G.Point σ` of power-series points of `G`. The defect
`δ(x, y) = f(x + y) - f(x) - f(y)`, computed there, satisfies the cocycle identity, the symmetry
and the telescoping `f(p x) - p f(x) = ∑_{j < p} δ(j x, x)` exactly, as identities in an abelian
group. The points vanishing to order `N ≥ 1` form a subgroup on which the degree-`N` part is
additive (`FormalGroup.le_order_subst_sub_sub`: `G(w, v) = w + v` up to degree `N + 1` when `w`
vanishes to order `N`), so these identities pass to the degree-`n` part of the defect, which is
then a symmetric additive 2-cocycle, hence a multiple of `C_n` by the symmetric 2-cocycle lemma
`TauCeti.exists_eq_smul_lazardCocycle`; its value in degree `pᵏ` comes from the identity
`∑_{j < p} C_{pᵏ}(j, 1) = -1` in characteristic `p`.

## Main definitions

* `FormalGroup.homDefect`: the homomorphism defect `f(F(X, Y)) - G(f(X), f(Y))`.
* `FormalGroup.substPointHom`: substitution into power-series points, as an additive map.

## Main results

* `FormalGroup.le_order_subst_sub_sub`: if `w` vanishes to order `N ≥ 1` and `v` has no constant
  term, then `G(w, v) - w - v` vanishes to order `N + 1`.
* `FormalGroup.homogeneousComponent_val_sub`: on points vanishing to order `N`, subtraction in
  `G` agrees with ordinary subtraction in degree `N`.
* `FormalGroup.exists_homogeneousComponent_eq_smul_lazardCocycle`: the leading term of a symmetric
  series satisfying the 2-cocycle identity along a formal group law up to higher-order terms is a
  multiple of the Lazard cocycle.
* `FormalGroup.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle`: the leading term of
  the homomorphism defect is a multiple `c C_n` of the Lazard cocycle.
* `FormalGroup.homogeneousComponent_homDefect_eq_smul_lazardCocycle`: in degree `pᵏ` and
  characteristic `p`, the multiple is the coefficient of `X^(pᵏ)` in `[p]_G ∘ f - f ∘ [p]_F`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Springer (1968), Chapter III.
* J. Lurie, *Chromatic Homotopy Theory* (Harvard lecture notes, 2010), Lecture 13.
-/

public section

open MvPowerSeries

namespace FormalGroup
variable {R : Type*} [CommRing R]

section Order
variable (G : FormalGroup R) {σ : Type*}

/-- **A formal group law is additive to first order.** If `w` vanishes to order `N ≥ 1` and `v`
has no constant term, then `G(w, v) - w - v` vanishes to order `N + 1`: the monomials of
`G(X, Y) - X - Y` have degree at least two and are divisible by `X`, since `G(0, Y) = Y`. -/
theorem le_order_subst_sub_sub {N : ℕ} (hN : N ≠ 0) {w v : MvPowerSeries σ R}
    (hw : (N : ℕ∞) ≤ w.order) (hv : constantCoeff v = 0) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (G.toPowerSeries.subst ![w, v] - w - v).order := by
  have hw₀ : constantCoeff w = 0 :=
    order_ne_zero_iff_constCoeff_eq_zero.mp (by intro h; rw [h] at hw; simp_all)
  have hwv : HasSubst ![w, v] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hw₀, hv]
  have hD : G.toPowerSeries.subst ![w, v] - w - v =
      (G.toPowerSeries - (X 0 + X 1)).subst ![w, v] := by
    rw [subst_sub hwv, subst_add hwv, subst_X hwv, subst_X hwv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [hD]
  refine le_trans ?_ (le_weightedOrder_subst (fun _ ↦ 1) hwv _)
  simp only [ne_eq, le_iInf_iff]
  intro d hd
  have hG := two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y
  -- the monomials of `G - X - Y` have degree at least two
  have hdeg : 2 ≤ d.degree := by
    by_contra h
    exact hd (coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast not_le.mp h) hG))
  -- and are not pure powers of `Y`, since `G(0, Y) = Y`
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have hd' : d = Finsupp.single 1 (d 1) := by
      ext i; fin_cases i <;> simp [h0]
    have h1 : d 1 ≠ 1 := by
      intro h1
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, h0, h1] at hdeg
      omega
    apply hd
    rw [hd', map_sub, map_add, coeff_single_one, ite_eq_right_iff.mpr (fun h ↦ (h1 h).elim),
      coeff_X, coeff_X]
    simp [Finsupp.single_eq_single_iff, h1]
  have hv' : (1 : ℕ∞) ≤ v.order :=
    Order.one_le_iff_ne_zero.mpr (order_ne_zero_iff_constCoeff_eq_zero.mpr hv)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, nsmul_eq_mul]
  -- `order` is by definition `weightedOrder` for the weight `1`
  change ((N + 1 : ℕ) : ℕ∞) ≤ (d 0 : ℕ∞) * w.order + (d 1 : ℕ∞) * v.order
  have hdeg' : 2 ≤ d 0 + d 1 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
  have key : N + 1 ≤ d 0 * N + d 1 := by
    rcases Nat.lt_or_ge (d 0) 2 with h | h
    · have : d 0 = 1 := by omega
      rw [this]; omega
    · have := Nat.mul_le_mul_right N h
      omega
  calc ((N + 1 : ℕ) : ℕ∞) ≤ ((d 0 * N + d 1 : ℕ) : ℕ∞) := by exact_mod_cast key
    _ = (d 0 : ℕ∞) * N + (d 1 : ℕ∞) * 1 := by push_cast; ring
    _ ≤ _ := by gcongr

/-- The points of `G` vanishing to order `N` are closed under addition. -/
theorem le_order_val_add {N : ℕ∞} {x y : G.Point σ} (hx : N ≤ x.val.order)
    (hy : N ≤ y.val.order) : N ≤ (x + y).val.order := by
  rw [add_apply]
  refine le_trans ?_ (le_order_subst (hasSubst_finTwo x.prop y.prop) _)
  have hG : (1 : ℕ∞) ≤ G.toPowerSeries.order :=
    Order.one_le_iff_ne_zero.mpr (order_ne_zero_iff_constCoeff_eq_zero.mpr G.zero_constantCoeff)
  calc N = N * 1 := (mul_one N).symm
    _ ≤ _ := mul_le_mul' (le_iInf fun i ↦ by fin_cases i <;> simpa) hG

/-- The points of `G` vanishing to order `N` are closed under negation. -/
theorem le_order_val_neg {N : ℕ∞} {x : G.Point σ} (hx : N ≤ x.val.order) :
    N ≤ (-x).val.order := by
  rw [neg_apply]
  refine le_trans ?_ (PowerSeries.le_order_subst _ x.prop _)
  have hi : (1 : ℕ∞) ≤ G.addInvX.order := by
    rw [PowerSeries.order_eq_order]
    exact Order.one_le_iff_ne_zero.mpr
      (order_ne_zero_iff_constCoeff_eq_zero.mpr G.constantCoeff_addInvX)
  calc N = N * 1 := (mul_one N).symm
    _ ≤ _ := mul_le_mul' hx hi

/-- The points of `G` vanishing to order `N` are closed under subtraction. -/
theorem le_order_val_sub {N : ℕ∞} {x y : G.Point σ} (hx : N ≤ x.val.order)
    (hy : N ≤ y.val.order) : N ≤ (x - y).val.order := by
  rw [sub_eq_add_neg]
  exact G.le_order_val_add hx (G.le_order_val_neg hy)

/-- If `x - y` vanishes to order `N ≥ 1` in the points of `G` and `y` has no constant term, then
subtraction in `G` agrees with ordinary subtraction up to degree `N + 1`. -/
theorem le_order_val_sub_val_sub {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hy : constantCoeff y.val = 0) (h : (N : ℕ∞) ≤ (x - y).val.order) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (x.val - y.val - (x - y).val).order := by
  have hx : x.val = G.toPowerSeries.subst ![(x - y).val, y.val] := by
    rw [← add_apply, sub_add_cancel]
  have := G.le_order_subst_sub_sub hN h hy
  rw [hx]
  convert this using 2
  ring

/-- On points whose difference in `G` vanishes to order `N ≥ 1`, the degree-`N` part of the
difference in `G` is the degree-`N` part of the ordinary difference. -/
theorem homogeneousComponent_val_sub {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hy : constantCoeff y.val = 0) (h : (N : ℕ∞) ≤ (x - y).val.order) :
    homogeneousComponent N (x - y).val = homogeneousComponent N (x.val - y.val) := by
  have h' := G.le_order_val_sub_val_sub hN hy h
  rw [← sub_eq_zero, ← map_sub]
  ext d
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hd
  · have hlt : (d.degree : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by
      rw [hd]; exact_mod_cast Nat.lt_succ_self N
    exact coeff_of_lt_order (hlt.trans_le (by rwa [← neg_sub, order_neg]))
  · rfl

/-- If `x` and `y` have no constant term and `x - y` vanishes to order `N` as power series, then
the difference `x - y` in the points of `G` vanishes to order `N` too. -/
theorem le_order_val_sub_of_le_order_sub {N : ℕ} {x y : G.Point σ}
    (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0)
    (h : (N : ℕ∞) ≤ (x.val - y.val).order) : (N : ℕ∞) ≤ (x - y).val.order := by
  have one_le {z : MvPowerSeries σ R} (hz : constantCoeff z = 0) : (1 : ℕ∞) ≤ z.order :=
    Order.one_le_iff_ne_zero.mpr (order_ne_zero_iff_constCoeff_eq_zero.mpr hz)
  induction N with
  | zero => simp
  | succ m ih =>
    have ih := ih (le_trans (by exact_mod_cast Nat.le_succ m) h)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact G.le_order_val_sub (one_le hx) (one_le hy)
    · have h' := G.le_order_val_sub_val_sub hm.ne' hy ih
      have := le_order_sub h h'
      rwa [sub_sub_cancel] at this

/-- Sums of points without constant term have no constant term. -/
private theorem constantCoeff_val_add {x y : G.Point σ}
    (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0) :
    constantCoeff (x + y).val = 0 := by
  rw [add_apply, constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo x.prop y.prop)
    (fun i ↦ by fin_cases i <;> assumption), G.zero_constantCoeff, map_zero]

end Order

section Subst

variable (G : FormalGroup R) {σ τ : Type*}

/-- Substituting a family `a` of series into the power-series points of `G` is additive: the
points of a formal group law are functorial along substitutions. -/
noncomputable def substPointHom {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    G.Point σ →+ G.Point τ :=
  AddMonoidHom.mk' (fun x ↦ ⟨x.val.subst a, IsNilpotent_subst ha x.prop⟩) fun x y ↦
    Subtype.ext <| by
      simp only [add_apply]
      rw [subst_comp_subst_apply (hasSubst_finTwo x.prop y.prop) ha]
      congr 1
      funext i
      fin_cases i <;> rfl

@[simp]
theorem val_substPointHom {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (x : G.Point σ) :
    (G.substPointHom ha x).val = x.val.subst a := (rfl)

end Subst

section Cocycle

/-- The degree-`n` part of a two-variable series, as a polynomial. -/
private noncomputable def leadingPoly (n : ℕ) (Φ : MvPowerSeries (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.homogeneousComponent n (truncTotal (n + 1) Φ)

private theorem coe_leadingPoly (n : ℕ) (Φ : MvPowerSeries (Fin 2) R) :
    (leadingPoly n Φ : MvPowerSeries (Fin 2) R) = homogeneousComponent n Φ := by
  ext d
  rw [MvPolynomial.coeff_coe, leadingPoly, MvPolynomial.coeff_homogeneousComponent,
    coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_truncTotal _ (by omega)
  · rfl

/-- If `Φ` vanishes below degree `n`, the degree-`n` part of `Φ(x)` for a family `x` of series
without constant term is the degree-`n` part of `Φ` evaluated at the linear parts of `x`. -/
private theorem homogeneousComponent_subst_eq_aeval {τ : Type*} {n : ℕ}
    {Φ : MvPowerSeries (Fin 2) R} (hn : n ≤ Φ.order) {x : Fin 2 → MvPowerSeries τ R}
    (hx : HasSubst x) (hx₀ : ∀ i, constantCoeff (x i) = 0) {l : Fin 2 → MvPolynomial τ R}
    (hl : ∀ i, homogeneousComponent 1 (x i) = l i) :
    homogeneousComponent n (Φ.subst x) =
      (MvPolynomial.aeval l (leadingPoly n Φ) : MvPowerSeries τ R) := by
  rw [homogeneousComponent_subst_of_le_order hn hx hx₀, ← coe_leadingPoly, subst_coe]
  simp_rw [hl]
  simpa using (MvPolynomial.comp_aeval_apply (MvPolynomial.coeToMvPowerSeries.algHom R)
    (leadingPoly n Φ) (f := l)).symm

/-- **Leading terms of symmetric 2-cocycles.** Let `F` be a formal group law and let
`Φ(X, Y)` be a symmetric series vanishing below degree `n ≠ 0` that satisfies the 2-cocycle
identity `Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)` up to terms of degree above `n`.
Then the degree-`n` part of `Φ` is a multiple of the Lazard cocycle `C_n`. -/
theorem exists_homogeneousComponent_eq_smul_lazardCocycle (F : FormalGroup R) {n : ℕ}
    (hn : n ≠ 0) {Φ : MvPowerSeries (Fin 2) R} (hΦ : n ≤ Φ.order)
    (hsymm : Φ.subst ![X 1, X 0] = Φ)
    (hcocycle : ((n + 1 : ℕ) : ℕ∞) ≤ (Φ.subst ![X 0, X 1] +
      Φ.subst ![F.toPowerSeries.subst ![X 0, X 1], (X 2 : MvPowerSeries (Fin 3) R)] -
      Φ.subst ![X 0, F.toPowerSeries.subst ![X 1, X 2]] -
      Φ.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]).order) :
    ∃ c : R, homogeneousComponent n Φ = ↑(c • TauCeti.lazardCocycle n R) := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hF₀ (i j : Fin 3) :
      constantCoeff (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo (hX i) (hX j))
      (fun s ↦ by fin_cases s <;> simp) F.toPowerSeries, F.zero_constantCoeff, map_zero]
  -- the leading polynomial is an additive 2-cocycle
  have hcoc : (leadingPoly n Φ).IsAddCocycle₂ := by
    have h := homogeneousComponent_of_lt_order_eq_zero
      (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hcocycle)
    rw [map_sub, map_sub, map_add,
      homogeneousComponent_subst_eq_aeval hΦ (hasSubst_finTwo (hX 0) (hX 1))
        (l := ![MvPolynomial.X 0, MvPolynomial.X 1]) (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_aeval hΦ
        (hasSubst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2))
        (l := ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 2])
        (fun i ↦ by fin_cases i <;> simp [hF₀])
        (fun i ↦ by
          fin_cases i <;>
            simp [homogeneousComponent_one_subst_pair F.zero_constantCoeff F.lin_coeff_X
              F.lin_coeff_Y (hX₀ 0) (hX₀ 1), homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_aeval hΦ
        (hasSubst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)))
        (l := ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 2])
        (fun i ↦ by fin_cases i <;> simp [hF₀])
        (fun i ↦ by
          fin_cases i <;>
            simp [homogeneousComponent_one_subst_pair F.zero_constantCoeff F.lin_coeff_X
              F.lin_coeff_Y (hX₀ 1) (hX₀ 2), homogeneousComponent_one_X]),
      homogeneousComponent_subst_eq_aeval hΦ (hasSubst_finTwo (hX 1) (hX 2))
        (l := ![MvPolynomial.X 1, MvPolynomial.X 2]) (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X])] at h
    rw [MvPolynomial.isAddCocycle₂_iff]
    refine MvPolynomial.coe_inj.mp ?_
    rw [MvPolynomial.coe_add, MvPolynomial.coe_add]
    linear_combination h
  -- the leading polynomial is symmetric
  have hsym : (leadingPoly n Φ).IsSymmetric := by
    have hX2 (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    have h : MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 0] (leadingPoly n Φ) =
        leadingPoly n Φ := by
      refine MvPolynomial.coe_inj.mp ?_
      rw [← homogeneousComponent_subst_eq_aeval hΦ (hasSubst_finTwo (hX2 1) (hX2 0))
        (fun i ↦ by fin_cases i <;> simp)
        (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]), hsymm, coe_leadingPoly]
    intro e
    rcases Equiv.Perm.eq_one_or_swap_fin_two e with rfl | rfl
    · simp
    · have hswap : (MvPolynomial.X ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → MvPolynomial (Fin 2) R) =
          ![MvPolynomial.X 1, MvPolynomial.X 0] := by
        funext i
        fin_cases i <;> simp
      rw [MvPolynomial.rename_eq_aeval, hswap]
      exact h
  obtain ⟨c, hc⟩ := TauCeti.exists_eq_smul_lazardCocycle hn
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _) hsym hcoc
  exact ⟨c, by rw [← coe_leadingPoly]; exact congrArg _ hc⟩

end Cocycle

section Defect

variable (F G : FormalGroup R)

/-- The **homomorphism defect** `f(F(X, Y)) - G(f(X), f(Y))` of a power series `f` with respect to
formal group laws `F` and `G`. It vanishes exactly when `f` satisfies the homomorphism equation
(`FormalGroup.homDefect_eq_zero_iff`), and its order measures to which degree `f` is a
homomorphism from `F` to `G`. -/
noncomputable def homDefect (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst F.toPowerSeries f - subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries

/-- Unfold the homomorphism defect. -/
theorem homDefect_def (f : PowerSeries R) :
    F.homDefect G f =
      PowerSeries.subst F.toPowerSeries f - subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries :=
  (rfl)

/-- The homomorphism defect vanishes exactly when `f` satisfies the homomorphism equation. -/
theorem homDefect_eq_zero_iff {f : PowerSeries R} :
    F.homDefect G f = 0 ↔
      PowerSeries.subst F.toPowerSeries f = subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries :=
  sub_eq_zero

variable {F G} {f : PowerSeries R} {σ : Type*}

/-- The point `f(x)` of `G`, for a series `f` without constant term and a point `x` of `F`. -/
private noncomputable def evalPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val f, by
    simpa only [PowerSeries.coe_substAlgHom] using
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf).comp x.prop⟩

private theorem val_evalPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) : (evalPoint G hf x).val = PowerSeries.subst x.val f := (rfl)

/-- The defect `f(x + y) - f(x) - f(y)` in the points of `G`. -/
private noncomputable def defectPoint (G : FormalGroup R) (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) : G.Point σ :=
  evalPoint G hf (x + y) - evalPoint G hf x - evalPoint G hf y

/-- The coordinate point `X i` of `F`. -/
private noncomputable def coordPoint (F : FormalGroup R) (i : σ) : F.Point σ :=
  ⟨X i, PowerSeries.HasSubst.X i⟩

/-- The defect at the coordinate points `X` and `Y` of `F`. -/
private noncomputable def coordDefect (F G : FormalGroup R)
    (hf : PowerSeries.constantCoeff f = 0) : G.Point (Fin 2) :=
  defectPoint G hf (coordPoint F 0) (coordPoint F 1)

private theorem constantCoeff_evalPoint (hf : PowerSeries.constantCoeff f = 0) {x : F.Point σ}
    (hx : constantCoeff x.val = 0) : constantCoeff (evalPoint G hf x).val = 0 := by
  change constantCoeff (PowerSeries.subst x.val f) = 0
  rw [PowerSeries.subst, constantCoeff_subst_of_constantCoeff_zero x.prop.const (fun _ ↦ hx)]
  exact (congrArg _ hf).trans (map_zero _)

private theorem substPointHom_evalPoint (hf : PowerSeries.constantCoeff f = 0) {τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (x : F.Point σ) :
    G.substPointHom ha (evalPoint G hf x) = evalPoint G hf (F.substPointHom ha x) :=
  Subtype.ext (subst_powerSeriesSubst ha x.prop f)

/-- The defect at any pair of points is obtained from the defect at the coordinate points by
substitution. -/
private theorem defectPoint_eq_substPointHom (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) :
    defectPoint G hf x y = G.substPointHom (hasSubst_finTwo x.prop y.prop)
      (coordDefect F G hf) := by
  have h0 : F.substPointHom (hasSubst_finTwo x.prop y.prop) (coordPoint F 0) = x :=
    Subtype.ext (subst_X (hasSubst_finTwo x.prop y.prop) 0)
  have h1 : F.substPointHom (hasSubst_finTwo x.prop y.prop) (coordPoint F 1) = y :=
    Subtype.ext (subst_X (hasSubst_finTwo x.prop y.prop) 1)
  simp only [coordDefect, defectPoint, map_sub, substPointHom_evalPoint, map_add, h0, h1]

/-- The defect is a 2-cocycle, by associativity of `F`. -/
private theorem defectPoint_add_defectPoint [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x y z : F.Point σ) :
    defectPoint G hf x y + defectPoint G hf (x + y) z =
      defectPoint G hf y z + defectPoint G hf x (y + z) := by
  simp only [defectPoint, add_assoc]
  abel

/-- The defect is symmetric when `F` and `G` are commutative. -/
private theorem defectPoint_comm [F.IsComm] [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x y : F.Point σ) : defectPoint G hf y x = defectPoint G hf x y := by
  simp only [defectPoint, add_comm y x]
  abel

/-- **The defect along multiples**: `f(m x) - m f(x)` telescopes to the sum of the defects
`f(j x + x) - f(j x) - f(x)` over `j < m`. -/
private theorem evalPoint_nsmul_sub_nsmul [G.IsComm] (hf : PowerSeries.constantCoeff f = 0)
    (x : F.Point σ) (m : ℕ) :
    evalPoint G hf (m • x) - m • evalPoint G hf x =
      ∑ j ∈ Finset.range m, defectPoint G hf (j • x) x := by
  induction m with
  | zero =>
    rw [zero_nsmul, zero_nsmul, Finset.sum_range_zero, sub_zero]
    exact Subtype.ext (PowerSeries.subst_zero_of_constantCoeff_zero hf)
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, defectPoint, succ_nsmul, succ_nsmul]
    abel

end Defect

section Obstruction

variable {F G : FormalGroup R} {f : PowerSeries R} {σ : Type*}

private theorem homogeneousComponent_val_add {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hx : (N : ℕ∞) ≤ x.val.order) (hy : constantCoeff y.val = 0) :
    homogeneousComponent N (x + y).val =
      homogeneousComponent N x.val + homogeneousComponent N y.val := by
  have h := G.homogeneousComponent_val_sub hN hy (x := x + y) (by rwa [add_sub_cancel_right])
  rw [add_sub_cancel_right, map_sub] at h
  rw [h, sub_add_cancel]

private theorem homogeneousComponent_val_sum [G.IsComm] {N : ℕ} (hN : N ≠ 0) (t : ℕ → G.Point σ)
    (ht : ∀ j, (N : ℕ∞) ≤ (t j).val.order) (m : ℕ) :
    homogeneousComponent N (∑ j ∈ Finset.range m, t j).val =
        ∑ j ∈ Finset.range m, homogeneousComponent N (t j).val ∧
      (N : ℕ∞) ≤ (∑ j ∈ Finset.range m, t j).val.order := by
  induction m with
  | zero => simp [zero_apply]
  | succ m ih =>
    have ht₀ : constantCoeff (t m).val = 0 := order_ne_zero_iff_constCoeff_eq_zero.mp
      fun h ↦ hN (by simpa [h] using ht m)
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      homogeneousComponent_val_add hN ih.2 ht₀, ih.1]
    exact ⟨rfl, G.le_order_val_add ih.2 (ht m)⟩

private theorem val_coordPoint (i : σ) : (coordPoint F i).val = X i := (rfl)

private theorem constantCoeff_coordPoint (i : σ) :
    constantCoeff (coordPoint F i).val = 0 :=
  constantCoeff_X i

private theorem coordDefect_eq (hf : PowerSeries.constantCoeff f = 0) :
    coordDefect F G hf = defectPoint G hf (coordPoint F 0) (coordPoint F 1) := (rfl)

/-- The defect at the coordinate points is the homomorphism defect, up to terms of degree above
its order. -/
private theorem homDefect_eq_val_sub (hf : PowerSeries.constantCoeff f = 0) :
    F.homDefect G f = (evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1)).val -
      (evalPoint G hf (coordPoint F (0 : Fin 2)) + evalPoint G hf (coordPoint F 1)).val := by
  simp only [homDefect, val_evalPoint, add_apply, val_coordPoint]
  congr 1
  · rw [finTwo_X_eq_X, subst_self, id]
  · congr 1
    funext i
    fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]

private theorem constantCoeff_evalPoint_add_evalPoint (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (evalPoint G hf (coordPoint F (0 : Fin 2)) +
      evalPoint G hf (coordPoint F 1)).val = 0 := by
  have h (i : Fin 2) := constantCoeff_evalPoint (G := G) hf (constantCoeff_coordPoint (F := F) i)
  exact G.constantCoeff_val_add (h 0) (h 1)

/-- If the defect at the coordinate points vanishes below degree `n`, so does the defect at any
pair of points without constant term. -/
private theorem le_order_defectPoint (hf : PowerSeries.constantCoeff f = 0) {n : ℕ}
    (hΨ : (n : ℕ∞) ≤ (coordDefect F G hf).val.order)
    {x y : F.Point σ} (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0) :
    (n : ℕ∞) ≤ (defectPoint G hf x y).val.order := by
  rw [defectPoint_eq_substPointHom, val_substPointHom]
  refine le_trans ?_ (le_order_subst (hasSubst_finTwo x.prop y.prop) _)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (![x.val, y.val] i).order :=
    le_iInf fun i ↦ by
      fin_cases i <;>
        exact Order.one_le_iff_ne_zero.mpr (order_ne_zero_iff_constCoeff_eq_zero.mpr (by simpa))
  calc (n : ℕ∞) = 1 * n := (one_mul _).symm
    _ ≤ _ := mul_le_mul' h1 hΨ

variable [G.IsComm]

private theorem defectPoint_coord_eq_sub (hf : PowerSeries.constantCoeff f = 0) :
    coordDefect F G hf =
      evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1) -
        (evalPoint G hf (coordPoint F (0 : Fin 2)) + evalPoint G hf (coordPoint F 1)) := by
  rw [coordDefect, defectPoint, sub_sub]

/-- The defect at the coordinate points vanishes below degree `n` when the homomorphism defect
does, and their degree-`n` parts agree. -/
private theorem le_order_defectPoint_coord (hf : PowerSeries.constantCoeff f = 0) {n : ℕ}
    (hn : n ≠ 0) (h : (n : ℕ∞) ≤ (F.homDefect G f).order) :
    (n : ℕ∞) ≤ (coordDefect F G hf).val.order ∧
      homogeneousComponent n (coordDefect F G hf).val =
        homogeneousComponent n (F.homDefect G f) := by
  have hv := constantCoeff_evalPoint_add_evalPoint (F := F) (G := G) hf
  have hu : constantCoeff (evalPoint G hf (coordPoint F (0 : Fin 2) + coordPoint F 1)).val =
      0 :=
    constantCoeff_evalPoint hf
      (F.constantCoeff_val_add (constantCoeff_coordPoint _) (constantCoeff_coordPoint _))
  rw [homDefect_eq_val_sub hf] at h ⊢
  have hΨ := G.le_order_val_sub_of_le_order_sub hu hv h
  rw [defectPoint_coord_eq_sub]
  exact ⟨hΨ, G.homogeneousComponent_val_sub hn hv hΨ⟩

variable [F.IsComm]

/-- The leading term of the defect at the coordinate points is a multiple of `C_n`. -/
private theorem exists_homogeneousComponent_defectPoint (hf : PowerSeries.constantCoeff f = 0)
    {n : ℕ} (hn : n ≠ 0)
    (hΨ : (n : ℕ∞) ≤ (coordDefect F G hf).val.order) :
    ∃ c : R, homogeneousComponent n (coordDefect F G hf).val =
      ↑(c • TauCeti.lazardCocycle n R) := by
  refine exists_homogeneousComponent_eq_smul_lazardCocycle F hn hΨ ?_ ?_
  · -- symmetry
    have h := congrArg Subtype.val (defectPoint_eq_substPointHom (G := G) hf
      (coordPoint F (1 : Fin 2)) (coordPoint F 0))
    rw [defectPoint_comm, val_substPointHom, val_coordPoint, val_coordPoint] at h
    exact h.symm.trans (congrArg Subtype.val (coordDefect_eq hf).symm)
  · -- the cocycle identity, up to terms of degree above `n`
    let x (i : Fin 3) : F.Point (Fin 3) := coordPoint F i
    have hx (i : Fin 3) : constantCoeff (x i).val = 0 := constantCoeff_coordPoint i
    have hx01 : constantCoeff (x 0 + x 1).val = 0 := F.constantCoeff_val_add (hx 0) (hx 1)
    have hx12 : constantCoeff (x 1 + x 2).val = 0 := F.constantCoeff_val_add (hx 1) (hx 2)
    have hval (y z : F.Point (Fin 3)) : (defectPoint G hf y z).val =
        (coordDefect F G hf).val.subst ![y.val, z.val] := by
      rw [defectPoint_eq_substPointHom, val_substPointHom]
    have hn' : ((1 : ℕ) : ℕ∞) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h0 {y z : F.Point (Fin 3)} (hy : constantCoeff y.val = 0)
        (hz : constantCoeff z.val = 0) : constantCoeff (defectPoint G hf y z).val = 0 :=
      order_ne_zero_iff_constCoeff_eq_zero.mp fun h ↦ by
        have := (le_order_defectPoint hf hΨ hy hz).trans_eq h
        exact hn (by exact_mod_cast le_zero_iff.mp this)
    have hA := G.le_order_subst_sub_sub hn (le_order_defectPoint hf hΨ (hx 0) (hx 1))
      (h0 hx01 (hx 2))
    have hC := G.le_order_subst_sub_sub hn (le_order_defectPoint hf hΨ (hx 1) (hx 2))
      (h0 (hx 0) hx12)
    rw [← add_apply, defectPoint_add_defectPoint] at hA
    rw [← add_apply] at hC
    have := le_order_sub hC hA
    have ex (i : Fin 3) : (x i).val = X i := (rfl)
    have e01 : (x 0 + x 1).val = F.toPowerSeries.subst ![X 0, X 1] := by
      rw [FormalGroup.add_apply, ex, ex]
    have e12 : (x 1 + x 2).val = F.toPowerSeries.subst ![X 1, X 2] := by
      rw [FormalGroup.add_apply, ex, ex]
    rw [hval, hval, hval, hval, e01, e12] at this
    simp only [ex] at this
    convert this using 2
    ring

/-- **The leading defect of an approximate homomorphism is a multiple of the Lazard cocycle.**
Let `F` and `G` be commutative formal group laws and let `f` be a power series without constant
term which is a homomorphism from `F` to `G` up to degree `n ≠ 0`: the homomorphism defect
`f(F(X, Y)) - G(f(X), f(Y))` vanishes below degree `n`. Then its degree-`n` part is `c C_n` for
some `c`, where `C_n` is the Lazard cocycle. -/
theorem exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle
    (hf : PowerSeries.constantCoeff f = 0) {n : ℕ} (hn : n ≠ 0)
    (h : (n : ℕ∞) ≤ (F.homDefect G f).order) :
    ∃ c : R, homogeneousComponent n (F.homDefect G f) = ↑(c • TauCeti.lazardCocycle n R) := by
  obtain ⟨hΨ, he⟩ := le_order_defectPoint_coord hf hn h
  obtain ⟨c, hc⟩ := exists_homogeneousComponent_defectPoint hf hn hΨ
  exact ⟨c, he ▸ hc⟩

/-- **The obstruction in degree `pᵏ` is read off the `p`-series.** Let `p` be a prime with
`p = 0` in `R`, let `F` and `G` be commutative formal group laws over `R`, and let `f` be a power
series without constant term whose homomorphism defect `f(F(X, Y)) - G(f(X), f(Y))` vanishes below
degree `n = pᵏ`, `k ≥ 1`. Then the degree-`n` part of the defect is `c C_n`, where `c` is the
coefficient of `Xⁿ` in `[p]_G(f(X)) - f([p]_F(X))`. In particular the defect vanishes in degree
`n` exactly when `f` commutes with multiplication by `p` up to degree `n`. -/
theorem homogeneousComponent_homDefect_eq_smul_lazardCocycle
    (hf : PowerSeries.constantCoeff f = 0) {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) {k : ℕ}
    (hk : k ≠ 0) (h : ((p ^ k : ℕ) : ℕ∞) ≤ (F.homDefect G f).order) :
    homogeneousComponent (p ^ k) (F.homDefect G f) =
      ↑(PowerSeries.coeff (p ^ k) (PowerSeries.subst f (G.nsmulSeries p) -
          PowerSeries.subst (F.nsmulSeries p) f) • TauCeti.lazardCocycle (p ^ k) R) := by
  have hn : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  obtain ⟨hΨ, he⟩ := le_order_defectPoint_coord hf hn h
  obtain ⟨c, hc⟩ := exists_homogeneousComponent_defectPoint hf hn hΨ
  rw [← he, hc]
  congr 2
  -- compare the degree-`pᵏ` parts of `f([p]_F(X)) - [p]_G(f(X))` and of the sum of the
  -- defects `f(j X + X) - f(j X) - f(X)` over `j < p`
  set x := F.tautologicalPoint
  have hx : constantCoeff x.val = 0 := by
    rw [val_tautologicalPoint]; exact PowerSeries.constantCoeff_X
  have hjx (j : ℕ) : (j • x).val = F.nsmulSeries j := by
    rw [← subst_nsmulSeries, val_tautologicalPoint, PowerSeries.X_subst]
  have hjx₀ (j : ℕ) : constantCoeff (j • x).val = 0 := by
    rw [hjx]; exact F.constantCoeff_nsmulSeries j
  have ht (j : ℕ) := le_order_defectPoint hf hΨ (hjx₀ j) hx
  have hsum := homogeneousComponent_val_sum hn (fun j ↦ defectPoint G hf (j • x) x) ht p
  rw [← evalPoint_nsmul_sub_nsmul] at hsum
  -- the left side
  have hfx : (evalPoint G hf x).val = f := by rw [val_evalPoint, val_tautologicalPoint,
    PowerSeries.X_subst]
  have hpx₀ : constantCoeff (p • evalPoint G hf x).val = 0 := by
    rw [← subst_nsmulSeries, hfx, PowerSeries.subst, constantCoeff_subst_of_constantCoeff_zero
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf).const (fun _ ↦ hf)]
    exact (congrArg _ (G.constantCoeff_nsmulSeries p)).trans (map_zero _)
  have hlhs := G.homogeneousComponent_val_sub hn hpx₀ hsum.2
  rw [val_evalPoint, hjx, ← subst_nsmulSeries, hfx] at hlhs
  -- the right side: the degree-`pᵏ` part of `f(j X + X) - f(j X) - f(X)` is `c C_n(j X, X)`
  have hterm (j : ℕ) : homogeneousComponent (p ^ k) (defectPoint G hf (j • x) x).val =
      MvPolynomial.coeToMvPowerSeries.ringHom (c • MvPolynomial.aeval
        ![(j : MvPolynomial Unit R) * MvPolynomial.X (), MvPolynomial.X ()]
        (TauCeti.lazardCocycle (p ^ k) R)) := by
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← _root_.map_smul,
      defectPoint_eq_substPointHom, val_substPointHom, homogeneousComponent_subst_of_le_order
      hΨ (hasSubst_finTwo (j • x).prop x.prop)
      (fun i ↦ by fin_cases i; exacts [hjx₀ j, hx]), hc, ← subst_coe_pair_eq_coe_aeval]
    congr 1
    funext i
    fin_cases i
    · -- the linear part of `[j]_F` is `j X`
      have hj : ((j : MvPolynomial Unit R) : MvPowerSeries Unit R) = j :=
        map_natCast MvPolynomial.coeToMvPowerSeries.ringHom j
      simp [hjx, homogeneousComponent_one_eq_C_mul_X, ← PowerSeries.coeff_def, hj]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, x,
        val_tautologicalPoint, MvPolynomial.coe_X]
      exact homogeneousComponent_one_X (R := R) ()
  have hpX : (p : MvPolynomial Unit R) = 0 := by
    rw [← map_natCast (MvPolynomial.C (σ := Unit)), hpR, map_zero]
  have hs := hsum.1
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← map_sum, ← Finset.smul_sum,
    TauCeti.sum_aeval_natCast_mul_lazardCocycle hp hpX hk, hlhs] at hs
  have hco := congrArg (coeff (Finsupp.single () (p ^ k))) hs
  simp only [coeff_homogeneousComponent, Finsupp.degree_single, ↓reduceIte,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_neg, MvPolynomial.coeff_X_pow] at hco
  rw [← PowerSeries.coeff_def Finsupp.single_eq_same] at hco
  rw [← neg_sub, map_neg, hco]
  simp

end Obstruction

end FormalGroup
