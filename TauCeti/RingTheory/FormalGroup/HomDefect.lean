/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
public import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.Data.Fin.Basic
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification

/-!
# Homomorphisms of formal group laws modulo a degree

Let `F` and `G` be formal group laws over a commutative ring `R`. The **homomorphism defect** of a
power series `g` with zero constant term is

  `Φ(X, Y) = g(F(X, Y)) - G(g(X), g(Y))` (`FormalGroup.homDefect`),

which vanishes exactly when `g` is a homomorphism from `F` to `G`. When `Φ` has order at least
`n`, the series `g` is a homomorphism up to terms of degree `n`. This file builds such
approximate homomorphisms degree by degree, following Lazard's proof that formal group laws over
a separably closed field are classified by their height.

Suppose that `F` and `G` are commutative and that `Φ` vanishes below degree `n ≥ 2`. Then the
degree-`n` part of `Φ` is a homogeneous symmetric additive 2-cocycle, so by the symmetric
2-cocycle lemma (`TauCeti.exists_eq_smul_lazardCocycle`) it is `r C_n` for the Lazard cocycle
`C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`.

* If `d_n` is a unit in `R`, replacing `g` by `g - r d_n⁻¹ Xⁿ` makes the defect vanish below
  degree `n + 1` (`FormalGroup.exists_succ_le_order_homDefect_sub_smul_X_pow`). This applies to
  every `n` that is not a power of `p` when `p = 0` in `R`.
* If `n = pᵏ` with `k ≥ 1` and `g = X + ⋯`, the coefficient `r` is measured by the `p`-series:
  summing `Φ([j]_F(X), X)` over `j < p` gives `g([p]_F(X)) - [p]_G(g(X))` to lowest order, whose
  degree-`n` part is `r ∑_{j < p} C_n(j, 1) Xⁿ = -r Xⁿ`. So if `[p]_F` and `[p]_G` have order at
  least `n` and the same coefficient of `Xⁿ`, then `r = 0`
  (`FormalGroup.succ_le_order_homDefect_of_coeff_nsmulSeries_eq`).

Starting from `g = X`, these two steps reach every degree up to `pʰ` when the `p`-series of `F`
and `G` have order at least `pʰ` and the same coefficient of `X^(pʰ)`: then some `g = X + ⋯` is a
homomorphism from `F` to `G` up to terms of degree greater than `pʰ`
(`FormalGroup.exists_le_order_homDefect_of_coeff_nsmulSeries_eq`). Over a field of
characteristic `p` this applies to two formal group laws of height `h` whose `p`-series have the
same leading coefficient. In the degrees `pᵏ` with `k > h` the obstruction no longer vanishes
automatically; over a separably closed field it is removed by solving an Artin–Schreier type
equation. Those degrees are not treated in this file.

## Main definitions

* `FormalGroup.homDefect`: the homomorphism defect `g(F(X, Y)) - G(g(X), g(Y))`.

## Main results

* `FormalGroup.exists_succ_le_order_homDefect_sub_smul_X_pow`: in a degree `n` with `d_n` a unit,
  the defect can be removed by subtracting a multiple of `Xⁿ`.
* `FormalGroup.succ_le_order_homDefect_of_coeff_nsmulSeries_eq`: in a degree `pᵏ` where the
  `p`-series agree, the defect vanishes automatically.
* `FormalGroup.exists_le_order_homDefect_of_coeff_nsmulSeries_eq`: commutative formal group laws
  whose `p`-series agree up to degree `pʰ` are isomorphic up to degree `pʰ`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74 (1968).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.2.
-/

public section

namespace FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R]

section HomDefect

variable (F G : FormalGroup R)

/-- The **homomorphism defect** `g(F(X, Y)) - G(g(X), g(Y))` of a one-variable power series `g`
from the formal group law `F` to `G`. It vanishes exactly when `g` is a homomorphism from `F` to
`G`; when it has order at least `n`, the series `g` is a homomorphism up to terms of degree `n`. -/
noncomputable def homDefect (g : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst F.toPowerSeries g - subst (fun i ↦ g.toMvPowerSeries i) G.toPowerSeries

/-- The homomorphism defect of `g` vanishes exactly when `g` satisfies the homomorphism equation
`g(F(X, Y)) = G(g(X), g(Y))` of `TauCeti.FormalGroupHom`. -/
theorem homDefect_eq_zero_iff {g : PowerSeries R} :
    homDefect F G g = 0 ↔
      PowerSeries.subst F.toPowerSeries g = subst (fun i ↦ g.toMvPowerSeries i) G.toPowerSeries :=
  sub_eq_zero

variable {F G} in
/-- A homomorphism of formal group laws has no homomorphism defect. -/
@[simp]
theorem _root_.TauCeti.FormalGroupHom.homDefect_eq_zero (f : TauCeti.FormalGroupHom F G) :
    homDefect F G f.toPowerSeries = 0 :=
  (homDefect_eq_zero_iff F G).mpr f.hom

/-- The homomorphism defect at substitutable `x, y` is `g(F(x, y)) - G(g(x), g(y))`. -/
theorem subst_homDefect {σ : Type*} {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    {x y : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    (homDefect F G g).subst ![x, y] = PowerSeries.subst (F.toPowerSeries.subst ![x, y]) g -
      G.toPowerSeries.subst ![PowerSeries.subst x g, PowerSeries.subst y g] := by
  have hxy := hasSubst_finTwo hx hy
  rw [homDefect, subst_sub hxy,
    subst_powerSeriesSubst hxy (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_comp_subst_apply (HasSubst.toMvPowerSeries hg) hxy]
  congr 2
  funext i
  rw [PowerSeries.subst_toMvPowerSeries hxy]
  fin_cases i <;> rfl

/-- The homomorphism defect is `g(F(X, Y)) - G(g(X), g(Y))`. -/
theorem homDefect_eq {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0) :
    homDefect F G g = PowerSeries.subst F.toPowerSeries g -
      G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) g,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) g] := by
  have h := subst_homDefect F G hg (PowerSeries.HasSubst.X (S := R) (0 : Fin 2))
    (PowerSeries.HasSubst.X (S := R) (1 : Fin 2))
  simpa only [finTwo_X_eq_X, subst_self, id] using h

end HomDefect

section Perturbation

variable (G : FormalGroup R) {σ : Type*} {x y e : MvPowerSeries σ R}

/-- Perturbing the first argument of `G` by a series `e` of order at least `n ≥ 1` adds `e` to
`G(x, y)`, up to terms of degree greater than `n`. -/
private theorem le_order_subst_add_left_sub (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      (G.toPowerSeries.subst ![x + e, y] - G.toPowerSeries.subst ![x, y] - e).order := by
  have hxy₀ : ∀ i, constantCoeff (![x, y] i) = 0 := fun i ↦ by fin_cases i <;> simp [hx, hy]
  have h := le_order_subst_update_add_sub G.toPowerSeries
    (hasSubst_of_constantCoeff_zero hxy₀) hxy₀ 0 hn he
  have hu : Function.update ![x, y] 0 (![x, y] 0 + e) = ![x + e, y] := by
    funext i
    fin_cases i <;> simp
  rwa [hu, G.lin_coeff_X, map_one, one_smul] at h

/-- Perturbing the second argument of `G` by a series `e` of order at least `n ≥ 1` adds `e` to
`G(x, y)`, up to terms of degree greater than `n`. -/
private theorem le_order_subst_add_right_sub (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      (G.toPowerSeries.subst ![x, y + e] - G.toPowerSeries.subst ![x, y] - e).order := by
  have hxy₀ : ∀ i, constantCoeff (![x, y] i) = 0 := fun i ↦ by fin_cases i <;> simp [hx, hy]
  have h := le_order_subst_update_add_sub G.toPowerSeries
    (hasSubst_of_constantCoeff_zero hxy₀) hxy₀ 1 hn he
  have hu : Function.update ![x, y] 1 (![x, y] 1 + e) = ![x, y + e] := by
    funext i
    fin_cases i <;> simp
  rwa [hu, G.lin_coeff_Y, map_one, one_smul] at h

/-- `G(x, y)` has no constant term when `x` and `y` have none. -/
private theorem constantCoeff_subst_pair (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (G.toPowerSeries.subst ![x, y]) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hx, hy]) (fun i ↦ by fin_cases i <;> simp [hx, hy]) G.zero_constantCoeff

/-- A series of order at least `n` keeps order at least `n` after substituting `x, y` without
constant terms. -/
private theorem le_order_subst_pair {f : MvPowerSeries (Fin 2) R} {n : ℕ∞} (hf : n ≤ f.order)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) : n ≤ (f.subst ![x, y]).order :=
  hf.trans (order_le_order_subst (hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hx, hy]) (fun i ↦ by fin_cases i <;> simp [hx, hy]) f)

end Perturbation

section Leading

variable {F G : FormalGroup R}

/-- **The homomorphism defect is a 2-cocycle to lowest order.** If the defect `Φ` of `g` vanishes
below degree `n`, then `Φ(X, Y) + Φ(F(X, Y), Z) - Φ(X, F(Y, Z)) - Φ(Y, Z)` vanishes below degree
`n + 1`, by associativity of `F` and `G`. -/
private theorem le_order_homDefect_cocycle {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ((homDefect F G g).subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1] +
      (homDefect F G g).subst
        ![F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2] -
      (homDefect F G g).subst
        ![X 0, F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]] -
      (homDefect F G g).subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]).order := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hgX (x : MvPowerSeries (Fin 3) R) (hx : constantCoeff x = 0) :
      constantCoeff (PowerSeries.subst x g) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx g hg
  have hS (x : MvPowerSeries (Fin 3) R) (hx : constantCoeff x = 0) :
      PowerSeries.HasSubst (PowerSeries.subst x g) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (hgX x hx)
  set A := F.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1]
  set B := F.toPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2]
  set u := G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 3) R) g,
    PowerSeries.subst (X 1 : MvPowerSeries (Fin 3) R) g]
  set v := G.toPowerSeries.subst ![PowerSeries.subst (X 1 : MvPowerSeries (Fin 3) R) g,
    PowerSeries.subst (X 2 : MvPowerSeries (Fin 3) R) g]
  -- `g(F(X, Y)) = u + Φ(X, Y)` and `g(F(Y, Z)) = v + Φ(Y, Z)` perturb the arguments of `G`
  have h₁ := G.le_order_subst_add_left_sub
    (e := PowerSeries.subst A g - u) (G.constantCoeff_subst_pair (hgX _ (hX₀ 0))
      (hgX _ (hX₀ 1))) (hgX _ (hX₀ 2)) hn₀ (by
        rw [← subst_homDefect F G hg (hX 0) (hX 1)]
        exact le_order_subst_pair hn (hX₀ 0) (hX₀ 1))
  have h₂ := G.le_order_subst_add_right_sub
    (e := PowerSeries.subst B g - v) (hgX _ (hX₀ 0)) (G.constantCoeff_subst_pair
      (hgX _ (hX₀ 1)) (hgX _ (hX₀ 2))) hn₀ (by
        rw [← subst_homDefect F G hg (hX 1) (hX 2)]
        exact le_order_subst_pair hn (hX₀ 1) (hX₀ 2))
  rw [add_sub_cancel] at h₁ h₂
  have heq : (homDefect F G g).subst ![X 0, X 1] + (homDefect F G g).subst ![A, X 2] -
      (homDefect F G g).subst ![X 0, B] - (homDefect F G g).subst ![X 1, X 2] =
      -(G.toPowerSeries.subst ![PowerSeries.subst A g, PowerSeries.subst (X 2) g] -
        G.toPowerSeries.subst ![u, PowerSeries.subst (X 2) g] - (PowerSeries.subst A g - u)) +
      (G.toPowerSeries.subst ![PowerSeries.subst (X 0) g, PowerSeries.subst B g] -
        G.toPowerSeries.subst ![PowerSeries.subst (X 0) g, v] - (PowerSeries.subst B g - v)) := by
    rw [subst_homDefect F G hg (hX 0) (hX 1),
      subst_homDefect F G hg (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2),
      subst_homDefect F G hg (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)),
      subst_homDefect F G hg (hX 1) (hX 2), F.assoc' (hX 0) (hX 1) (hX 2),
      G.assoc' (hS _ (hX₀ 0)) (hS _ (hX₀ 1)) (hS _ (hX₀ 2))]
    ring
  rw [heq]
  exact le_order_add (by rwa [order_neg]) h₂

/-- **The leading part of the homomorphism defect is an additive 2-cocycle**, read off from
`FormalGroup.le_order_homDefect_cocycle` in degree `n`. -/
private theorem isAddCocycle₂_homogeneousComponent_homDefect {n : ℕ} (hn₀ : n ≠ 0)
    {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hn : n ≤ (homDefect F G g).order) :
    (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homDefect F G g))).IsAddCocycle₂ := by
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hlin (i j : Fin 3) : homogeneousComponent 1
      (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = X i + X j :=
    (homogeneousComponent_one_subst_pair F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
      (hX₀ i) (hX₀ j)).trans (by simp)
  have hcomp (x y : MvPowerSeries (Fin 3) R) (hx : constantCoeff x = 0)
      (hy : constantCoeff y = 0) (l : Fin 2 → MvPolynomial (Fin 3) R)
      (hl : ∀ i, homogeneousComponent 1 (![x, y] i) = l i) :
      homogeneousComponent n ((homDefect F G g).subst ![x, y]) =
        (MvPolynomial.aeval l (MvPolynomial.homogeneousComponent n
          (truncTotal (n + 1) (homDefect F G g))) : MvPowerSeries (Fin 3) R) :=
    homogeneousComponent_subst_eq_aeval hn (hasSubst_of_constantCoeff_zero fun i ↦ by
      fin_cases i <;> simp [hx, hy]) (fun i ↦ by fin_cases i <;> simp [hx, hy]) hl
  have h := homogeneousComponent_of_lt_order_eq_zero
    ((Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le (le_order_homDefect_cocycle hn₀ hg hn))
  rw [map_sub, map_sub, map_add,
    hcomp _ _ (hX₀ 0) (hX₀ 1) ![MvPolynomial.X 0, MvPolynomial.X 1]
      (fun i ↦ by fin_cases i <;> simp),
    hcomp _ _ (F.constantCoeff_subst_pair (hX₀ 0) (hX₀ 1)) (hX₀ 2)
      ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 2]
      (fun i ↦ by fin_cases i <;> simp [hlin]),
    hcomp _ _ (hX₀ 0) (F.constantCoeff_subst_pair (hX₀ 1) (hX₀ 2))
      ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 2]
      (fun i ↦ by fin_cases i <;> simp [hlin]),
    hcomp _ _ (hX₀ 1) (hX₀ 2) ![MvPolynomial.X 1, MvPolynomial.X 2]
      (fun i ↦ by fin_cases i <;> simp)] at h
  rw [MvPolynomial.isAddCocycle₂_iff]
  refine MvPolynomial.coe_inj.mp ?_
  rw [MvPolynomial.coe_add, MvPolynomial.coe_add]
  linear_combination h

/-- **The leading part of the homomorphism defect is symmetric** when `F` and `G` are
commutative, since then the defect itself is symmetric. -/
private theorem isSymmetric_homogeneousComponent_homDefect [F.IsComm] [G.IsComm] {n : ℕ}
    {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hn : n ≤ (homDefect F G g).order) :
    (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homDefect F G g))).IsSymmetric := by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have hS (i : Fin 2) :
      PowerSeries.HasSubst (PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) g) :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) g hg)
  have hswap : (homDefect F G g).subst ![X 1, X 0] = homDefect F G g := by
    rw [subst_homDefect F G hg (hX 1) (hX 0), F.comm' (hX 1) (hX 0), G.comm' (hS 1) (hS 0),
      ← subst_homDefect F G hg (hX 0) (hX 1), finTwo_X_eq_X, subst_self, id]
  have h : MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 0]
      (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homDefect F G g))) =
      MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homDefect F G g)) := by
    refine MvPolynomial.coe_inj.mp ?_
    rw [← homogeneousComponent_subst_eq_aeval hn (hasSubst_finTwo (hX 1) (hX 0))
      (fun i ↦ by fin_cases i <;> simp) (fun i ↦ by fin_cases i <;> simp), hswap,
      coe_homogeneousComponent_truncTotal]
  intro e
  rcases Equiv.Perm.eq_one_or_swap_fin_two e with rfl | rfl
  · simp
  · have hsw : (MvPolynomial.X ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → MvPolynomial (Fin 2) R) =
        ![MvPolynomial.X 1, MvPolynomial.X 0] := by
      funext i
      fin_cases i <;> simp
    rw [MvPolynomial.rename_eq_aeval, hsw]
    exact h

/-- The lowest-degree part of `c Xⁿ` evaluated at `F(X, Y)`, minus its values at `X` and `Y`, is
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
private theorem homogeneousComponent_subst_smul_X_pow_sub (F : FormalGroup R) (c : R) (n : ℕ) :
    homogeneousComponent n
      (PowerSeries.subst F.toPowerSeries (c • PowerSeries.X ^ n : PowerSeries R) -
        PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) (c • PowerSeries.X ^ n : PowerSeries R) -
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) (c • PowerSeries.X ^ n : PowerSeries R)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  simp only [PowerSeries.subst_smul hF, PowerSeries.subst_smul (hX _),
    PowerSeries.subst_pow hF, PowerSeries.subst_pow (hX _), PowerSeries.subst_X hF,
    PowerSeries.subst_X (hX _), map_sub, _root_.map_smul,
    homogeneousComponent_pow_of_constantCoeff_eq_zero F.zero_constantCoeff,
    homogeneousComponent_pow_of_constantCoeff_eq_zero (constantCoeff_X _),
    homogeneousComponent_one_X,
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y]
  rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_mul, map_sub, map_pow, map_add, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, MvPolynomial.coe_C, MvPowerSeries.smul_eq_C_mul, mul_sub]

/-- **Correcting the leading defect.** Subtracting `c Xⁿ` from `g` subtracts
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)` from the degree-`n` part of the homomorphism defect, and keeps the defect
zero below degree `n`. -/
private theorem homDefect_sub_smul_X_pow {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) (c : R) :
    (n : ℕ∞) ≤ (homDefect F G (g - c • PowerSeries.X ^ n)).order ∧
      homogeneousComponent n (homDefect F G (g - c • PowerSeries.X ^ n)) =
        homogeneousComponent n (homDefect F G g) -
          ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
            MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  set e : PowerSeries R := c • PowerSeries.X ^ n
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have he₀ : PowerSeries.constantCoeff e = 0 := by simp [e, hn₀]
  have hen : (n : ℕ∞) ≤ e.order :=
    PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [e, PowerSeries.coeff_X_pow, hi.ne]
  have hsub (i : Fin 2) : constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) g) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) g hg
  have hsube (x : MvPowerSeries (Fin 2) R) (hx : constantCoeff x = 0) :
      (n : ℕ∞) ≤ (PowerSeries.subst x e).order :=
    hen.trans (PowerSeries.le_order_subst_left hx)
  set g₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) g
  set g₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) g
  set e₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) e
  set e₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) e
  -- subtracting `e₀` and `e₁` from the arguments of `G` subtracts them from `G(g₀, g₁)`
  have h₀ := G.le_order_subst_add_left_sub (x := g₀) (y := g₁ - e₁) (e := -e₀) (hsub 0)
    (by rw [map_sub, hsub 1, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) e he₀,
      sub_zero]) hn₀ (by rw [order_neg]; exact hsube _ (constantCoeff_X 0))
  have h₁ := G.le_order_subst_add_right_sub (x := g₀) (y := g₁) (e := -e₁) (hsub 0) (hsub 1) hn₀
    (by rw [order_neg]; exact hsube _ (constantCoeff_X 1))
  rw [← sub_eq_add_neg] at h₀ h₁
  -- the remaining change is the additivity defect `Q` of `e` along `F`
  set Q := PowerSeries.subst F.toPowerSeries e - e₀ - e₁
  have hQ : (n : ℕ∞) ≤ Q.order :=
    le_order_sub (le_order_sub (hsube _ F.zero_constantCoeff) (hsube _ (constantCoeff_X 0)))
      (hsube _ (constantCoeff_X 1))
  have heq : homDefect F G (g - e) = homDefect F G g - Q -
      (G.toPowerSeries.subst ![g₀ - e₀, g₁ - e₁] - G.toPowerSeries.subst ![g₀, g₁ - e₁] - -e₀) -
      (G.toPowerSeries.subst ![g₀, g₁ - e₁] - G.toPowerSeries.subst ![g₀, g₁] - -e₁) := by
    rw [homDefect_eq F G (by rw [map_sub, hg, he₀, sub_zero]), homDefect_eq F G hg,
      PowerSeries.subst_sub hF, PowerSeries.subst_sub (hX 0), PowerSeries.subst_sub (hX 1)]
    ring
  have hlt (f : MvPowerSeries (Fin 2) R) (hf : ((n + 1 : ℕ) : ℕ∞) ≤ f.order) :
      (n : ℕ∞) ≤ f.order :=
    (Nat.cast_le.mpr (Nat.le_succ n)).trans hf
  have hzero (f : MvPowerSeries (Fin 2) R) (hf : ((n + 1 : ℕ) : ℕ∞) ≤ f.order) :
      homogeneousComponent n f = 0 :=
    homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le hf)
  rw [heq]
  refine ⟨le_order_sub (le_order_sub (le_order_sub hn hQ) (hlt _ h₀)) (hlt _ h₁), ?_⟩
  rw [map_sub, map_sub, map_sub, hzero _ h₀, hzero _ h₁, homogeneousComponent_subst_smul_X_pow_sub,
    sub_zero, sub_zero]

/-- **The defect along the `m`-series.** Up to terms of degree greater than `n`, the difference
`g([m]_F(X)) - [m]_G(g(X))` is the sum of the defects `Φ([j]_F(X), X)` over `j < m`, where `Φ` is
the homomorphism defect of `g`, assumed to vanish below degree `n`. -/
private theorem le_order_subst_nsmulSeries_sub_sum {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) (m : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (PowerSeries.subst (F.nsmulSeries m) g -
      PowerSeries.subst g (G.nsmulSeries m) -
      ∑ j ∈ Finset.range m, (homDefect F G g).subst ![F.nsmulSeries j, PowerSeries.X]).order := by
  induction m with
  | zero => simp [PowerSeries.subst_zero_of_constantCoeff_zero hg]
  | succ m ih =>
    set E := PowerSeries.subst (F.nsmulSeries m) g - PowerSeries.subst g (G.nsmulSeries m)
    -- `E` has order at least `n`, as each `Φ([j]_F(X), X)` does
    have hE : (n : ℕ∞) ≤ E.order := by
      have h := le_order_add ((Nat.cast_le.mpr (Nat.le_succ n)).trans ih)
        (Finset.sum_induction (s := Finset.range m) _
          (fun x : MvPowerSeries Unit R ↦ (n : ℕ∞) ≤ x.order) (fun _ _ ↦ le_order_add) (by simp)
          (fun j _ ↦ le_order_subst_pair hn (F.constantCoeff_nsmulSeries j)
            PowerSeries.constantCoeff_X))
      rwa [sub_add_cancel] at h
    -- `g([m]_F(X)) = [m]_G(g(X)) + E` perturbs the first argument of `G`
    have hP := G.le_order_subst_add_left_sub (x := PowerSeries.subst g (G.nsmulSeries m))
      (y := g) (e := E) (PowerSeries.constantCoeff_subst_eq_zero hg _
        (G.constantCoeff_nsmulSeries m)) hg hn₀ hE
    rw [add_sub_cancel] at hP
    have hF₁ : PowerSeries.subst (F.nsmulSeries (m + 1)) g =
        (homDefect F G g).subst ![F.nsmulSeries m, PowerSeries.X] +
          G.toPowerSeries.subst ![PowerSeries.subst (F.nsmulSeries m) g, g] := by
      rw [subst_homDefect F G hg
        (PowerSeries.HasSubst.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries m))
        PowerSeries.HasSubst.X', F.nsmulSeries_succ, PowerSeries.X_subst, sub_add_cancel]
    have hG₁ : PowerSeries.subst g (G.nsmulSeries (m + 1)) =
        G.toPowerSeries.subst ![PowerSeries.subst g (G.nsmulSeries m), g] := by
      let x : G.Point Unit := ⟨g, .of_constantCoeff_zero' hg⟩
      rw [G.subst_nsmulSeries x (m + 1), succ_nsmul, add_apply, ← G.subst_nsmulSeries x m]
    have heq : PowerSeries.subst (F.nsmulSeries (m + 1)) g -
        PowerSeries.subst g (G.nsmulSeries (m + 1)) - ∑ j ∈ Finset.range (m + 1),
          (homDefect F G g).subst ![F.nsmulSeries j, PowerSeries.X] =
        (G.toPowerSeries.subst ![PowerSeries.subst (F.nsmulSeries m) g, g] -
          G.toPowerSeries.subst ![PowerSeries.subst g (G.nsmulSeries m), g] - E) +
        (E - ∑ j ∈ Finset.range m,
          (homDefect F G g).subst ![F.nsmulSeries j, PowerSeries.X]) := by
      rw [hF₁, hG₁, Finset.sum_range_succ]
      ring
    rw [heq]
    exact le_order_add hP ih

/-- The degree-`n` part of `f(φ(X))` is `a Xⁿ` when `f` has order at least `n` and coefficient `a`
of `Xⁿ`, and `φ = X + ⋯`. -/
private theorem homogeneousComponent_subst_eq_C_mul_X_pow {f φ : PowerSeries R} {n : ℕ}
    (hn : n ≤ f.order) (hφ : PowerSeries.constantCoeff φ = 0) (hφ₁ : PowerSeries.coeff 1 φ = 1) :
    homogeneousComponent n (PowerSeries.subst φ f) = C (PowerSeries.coeff n f) * X () ^ n := by
  rw [PowerSeries.homogeneousComponent_subst_of_le_order hφ hn,
    homogeneousComponent_one_eq_C_mul_X]
  simp [← PowerSeries.coeff_def, hφ₁]

/-- The degree-`n` part of `φ(f(X))` is `a Xⁿ` when `f` has order at least `n ≥ 1` and coefficient
`a` of `Xⁿ`, and `φ = X + ⋯`: the terms of `φ` of degree at least two contribute in degree at
least `2 n`. -/
private theorem homogeneousComponent_subst_eq_C_mul_X_pow' {f φ : PowerSeries R} {n : ℕ}
    (hn₀ : n ≠ 0) (hn : n ≤ f.order) (hφ : PowerSeries.constantCoeff φ = 0)
    (hφ₁ : PowerSeries.coeff 1 φ = 1) :
    homogeneousComponent n (PowerSeries.subst f φ) = C (PowerSeries.coeff n f) * X () ^ n := by
  have hf₀ : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_of_lt_order 0 ((Nat.cast_lt.mpr (Nat.pos_of_ne_zero hn₀)).trans_le hn)
  have hS : PowerSeries.HasSubst f := .of_constantCoeff_zero' hf₀
  have h₂ : (2 : ℕ∞) ≤ (φ - PowerSeries.X).order := PowerSeries.nat_le_order _ 2 fun i hi ↦ by
    interval_cases i <;> simp [hφ, hφ₁]
  have hrest : ((n + 1 : ℕ) : ℕ∞) ≤ (PowerSeries.subst f (φ - PowerSeries.X)).order := by
    refine le_trans ?_ (PowerSeries.le_order_subst _ hS _)
    rw [← PowerSeries.order_eq_order]
    calc ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) * 2 := by exact_mod_cast (by omega : n + 1 ≤ n * 2)
      _ ≤ _ := mul_le_mul' hn h₂
  have hsplit : PowerSeries.subst f φ =
      PowerSeries.subst PowerSeries.X f + PowerSeries.subst f (φ - PowerSeries.X) := by
    rw [PowerSeries.subst_sub hS, PowerSeries.subst_X hS, PowerSeries.X_subst, add_sub_cancel]
  rw [hsplit, map_add, homogeneousComponent_of_lt_order_eq_zero
    ((Nat.cast_lt.mpr (Nat.lt_succ_self _)).trans_le hrest), _root_.add_zero,
    homogeneousComponent_subst_eq_C_mul_X_pow hn PowerSeries.constantCoeff_X
      PowerSeries.coeff_one_X]

/-- **The obstruction in degree `pᵏ`.** Let `p = 0` in `R`, and let the homomorphism defect of
`g = X + ⋯` vanish below degree `n = pᵏ`, `k ≥ 1`, with degree-`n` part `r C_n`. If the `p`-series
of `F` and `G` have order at least `n`, their coefficients of `Xⁿ` differ by `r`: the degree-`n`
part of `g([p]_F(X)) - [p]_G(g(X))` is `r ∑_{j < p} C_n(j X, X) = -r Xⁿ`. -/
private theorem coeff_nsmulSeries_add_eq {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) {k : ℕ}
    (hk : k ≠ 0) {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hg₁ : PowerSeries.coeff 1 g = 1) (hn : ((p ^ k : ℕ) : ℕ∞) ≤ (homDefect F G g).order)
    (hF : ((p ^ k : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ k : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order) {r : R}
    (hr : MvPolynomial.homogeneousComponent (p ^ k) (truncTotal (p ^ k + 1) (homDefect F G g)) =
      r • TauCeti.lazardCocycle (p ^ k) R) :
    PowerSeries.coeff (p ^ k) (F.nsmulSeries p) + r =
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p) := by
  have hn₀ : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have h := homogeneousComponent_of_lt_order_eq_zero
    ((Nat.cast_lt.mpr (Nat.lt_succ_self _)).trans_le
      (le_order_subst_nsmulSeries_sub_sum hn₀ hg hn p))
  -- the degree-`pᵏ` part of `Φ([j]_F(X), X)` is `r C_n(j X, X)`
  have hterm (j : ℕ) : homogeneousComponent (p ^ k)
      ((homDefect F G g).subst ![F.nsmulSeries j, PowerSeries.X]) =
        MvPolynomial.coeToMvPowerSeries.ringHom (r • MvPolynomial.aeval
          ![(j : MvPolynomial Unit R) * MvPolynomial.X (), MvPolynomial.X ()]
          (TauCeti.lazardCocycle (p ^ k) R)) := by
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      homogeneousComponent_subst_eq_aeval hn (F.hasSubst_nsmulSeries_X j)
      (fun i ↦ by fin_cases i; exacts [F.constantCoeff_nsmulSeries j, PowerSeries.constantCoeff_X])
      (fun i ↦ ?_), hr, _root_.map_smul]
    fin_cases i
    · -- the linear part of `[j]_F` is `j X`
      have hj : ((j : MvPolynomial Unit R) : MvPowerSeries Unit R) = j :=
        map_natCast MvPolynomial.coeToMvPowerSeries.ringHom j
      simp [homogeneousComponent_one_eq_C_mul_X, ← PowerSeries.coeff_def, hj]
    · exact (homogeneousComponent_one_X (R := R) ()).trans (MvPolynomial.coe_X _).symm
  rw [map_sub, map_sub, map_sum, Finset.sum_congr rfl fun j _ ↦ hterm j,
    homogeneousComponent_subst_eq_C_mul_X_pow' hn₀ hF hg hg₁,
    homogeneousComponent_subst_eq_C_mul_X_pow hG hg hg₁, ← map_sum, ← Finset.smul_sum,
    TauCeti.sum_aeval_natCast_mul_lazardCocycle hp
      (by rw [← map_natCast (MvPolynomial.C (σ := Unit)), hpR, map_zero]) hk] at h
  -- compare the coefficients of `X^(pᵏ)`
  have hpoly : MvPolynomial.coeToMvPowerSeries.ringHom
      (r • -MvPolynomial.X () ^ (p ^ k) : MvPolynomial Unit R) = -(C r * X () ^ (p ^ k)) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_neg, map_pow,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X,
      mul_neg]
  have h' : C (PowerSeries.coeff (p ^ k) (F.nsmulSeries p) + r -
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p)) * X () ^ (p ^ k) = 0 := by
    rw [← h, hpoly, map_sub, map_add]
    ring
  have hc := congrArg (coeff (Finsupp.single () (p ^ k))) h'
  simp only [coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one, map_zero] at hc
  linear_combination hc

end Leading

section Step

variable {F G : FormalGroup R} [F.IsComm] [G.IsComm]

/-- **Correcting the defect in degrees with invertible `d_n`.** Let `F` and `G` be commutative and
let the homomorphism defect of `g` vanish below degree `n ≥ 2`. If `d_n = TauCeti.lazardGcd n` is a
unit in `R`, for instance if `n` is not a power of a prime `p` with `p = 0` in `R`, then for some
`c` the defect of `g - c Xⁿ` vanishes below degree `n + 1`. -/
theorem exists_succ_le_order_homDefect_sub_smul_X_pow {n : ℕ} (hn₂ : 2 ≤ n)
    (hd : IsUnit (TauCeti.lazardGcd n : R)) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) :
    ∃ c : R, ((n + 1 : ℕ) : ℕ∞) ≤ (homDefect F G (g - c • PowerSeries.X ^ n)).order := by
  obtain ⟨r, hr⟩ := TauCeti.exists_eq_smul_lazardCocycle (by omega)
    (MvPolynomial.homogeneousComponent_isHomogeneous n (truncTotal (n + 1) (homDefect F G g)))
    (isSymmetric_homogeneousComponent_homDefect hg hn)
    (isAddCocycle₂_homogeneousComponent_homDefect (by omega) hg hn)
  -- `r C_n = (r d_n⁻¹) ((X + Y)ⁿ - Xⁿ - Yⁿ)`
  have hc : MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homDefect F G g)) =
      (r * ↑hd.unit⁻¹) • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) := by
    rw [hr, ← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega), ← Nat.cast_smul_eq_nsmul R,
      smul_smul, mul_assoc, hd.val_inv_mul, mul_one]
  obtain ⟨h₁, h₂⟩ := homDefect_sub_smul_X_pow (by omega) hg hn (r * ↑hd.unit⁻¹)
  refine ⟨_, succ_le_order_of_homogeneousComponent_eq_zero h₁ ?_⟩
  rw [h₂, ← coe_homogeneousComponent_truncTotal, hc, sub_self]

/-- **No defect in degree `pᵏ` when the `p`-series agree.** Let `F` and `G` be commutative and let
the homomorphism defect of `g = X + ⋯` vanish below degree `n = pᵏ`, `k ≥ 1`. If the `p`-series of
`F` and `G` both have order at least `n` and the same coefficient of `Xⁿ`, the defect of `g`
vanishes below degree `n + 1`. -/
theorem succ_le_order_homDefect_of_coeff_nsmulSeries_eq {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ≠ 0) {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hg₁ : PowerSeries.coeff 1 g = 1) (hn : ((p ^ k : ℕ) : ℕ∞) ≤ (homDefect F G g).order)
    (hF : ((p ^ k : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ k : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p)) :
    ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g).order := by
  have hn₂ : 2 ≤ p ^ k := Nat.one_lt_pow hk hp.one_lt
  -- `p` is the linear coefficient of `[p]_F`, which vanishes
  have hpR : (p : R) = 0 := by
    rw [← F.coeff_one_nsmulSeries p]
    exact PowerSeries.coeff_of_lt_order 1 ((Nat.cast_lt.mpr (by omega)).trans_le hF)
  obtain ⟨r, hr⟩ := TauCeti.exists_eq_smul_lazardCocycle (by omega)
    (MvPolynomial.homogeneousComponent_isHomogeneous (p ^ k)
      (truncTotal (p ^ k + 1) (homDefect F G g)))
    (isSymmetric_homogeneousComponent_homDefect hg hn)
    (isAddCocycle₂_homogeneousComponent_homDefect (by omega) hg hn)
  have hr₀ : r = 0 := by
    have h := coeff_nsmulSeries_add_eq hp hpR hk hg hg₁ hn hF hG hr
    rwa [hFG, add_eq_left] at h
  refine succ_le_order_of_homogeneousComponent_eq_zero hn ?_
  rw [← coe_homogeneousComponent_truncTotal, hr, hr₀, zero_smul, MvPolynomial.coe_zero]

/-- The inductive step: a normalised `g` whose homomorphism defect vanishes below a degree
`2 ≤ n ≤ pʰ` can be modified in degree `n` so that its defect vanishes below degree `n + 1`. -/
private theorem exists_succ_le_order_homDefect {p : ℕ} (hp : p.Prime) {h : ℕ}
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ h : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ h) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ h) (G.nsmulSeries p))
    {n : ℕ} (hn₂ : 2 ≤ n) (hnh : n ≤ p ^ h) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hg₁ : PowerSeries.coeff 1 g = 1)
    (hn : n ≤ (homDefect F G g).order) :
    ∃ g' : PowerSeries R, PowerSeries.constantCoeff g' = 0 ∧ PowerSeries.coeff 1 g' = 1 ∧
      ((n + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g').order := by
  by_cases hpow : ∃ k, n = p ^ k
  · -- in degree `pᵏ` the defect vanishes, as both coefficients of `X^(pᵏ)` vanish below the height
    obtain ⟨k, rfl⟩ := hpow
    have hk₀ : k ≠ 0 := by
      rintro rfl
      simp at hn₂
    have hkh : k ≤ h := (Nat.pow_le_pow_iff_right hp.one_lt).mp hnh
    have hle (f : PowerSeries R) (hf : ((p ^ h : ℕ) : ℕ∞) ≤ f.order) :
        ((p ^ k : ℕ) : ℕ∞) ≤ f.order :=
      (Nat.cast_le.mpr hnh).trans hf
    have hcoeff : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
        PowerSeries.coeff (p ^ k) (G.nsmulSeries p) := by
      rcases hkh.lt_or_eq with hlt | rfl
      · have hlt' : ((p ^ k : ℕ) : ℕ∞) < ((p ^ h : ℕ) : ℕ∞) :=
          Nat.cast_lt.mpr (Nat.pow_lt_pow_right hp.one_lt hlt)
        rw [PowerSeries.coeff_of_lt_order _ (hlt'.trans_le hF),
          PowerSeries.coeff_of_lt_order _ (hlt'.trans_le hG)]
      · exact hFG
    exact ⟨g, hg, hg₁, succ_le_order_homDefect_of_coeff_nsmulSeries_eq hp hk₀ hg hg₁ hn
      (hle _ hF) (hle _ hG) hcoeff⟩
  · -- otherwise `d_n` is prime to `p`, and `p = 0` in `R`, so `d_n` is a unit
    have hpR : (p : R) = 0 := by
      rw [← F.coeff_one_nsmulSeries p]
      exact PowerSeries.coeff_of_lt_order 1 ((Nat.cast_lt.mpr (by omega)).trans_le hF)
    have hd : IsUnit ((TauCeti.lazardGcd n : ℕ) : R) := by
      have hcop : (TauCeti.lazardGcd n).Coprime p := Nat.Coprime.symm <|
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd ↦
          hpow ((TauCeti.prime_dvd_lazardGcd_iff hp (by omega)).mp hdvd)
      have : IsCoprime ((TauCeti.lazardGcd n : ℕ) : R) (p : R) := by
        simpa using (Nat.isCoprime_iff_coprime.mpr hcop).intCast (R := R)
      rwa [hpR, isCoprime_zero_right] at this
    obtain ⟨c, hc⟩ := exists_succ_le_order_homDefect_sub_smul_X_pow hn₂ hd hg hn
    exact ⟨g - c • PowerSeries.X ^ n, by simp [hg, show n ≠ 0 by omega],
      by simp [hg₁, PowerSeries.coeff_X_pow, show 1 ≠ n by omega], hc⟩

/-- **Formal group laws with matching `p`-series agree up to degree `pʰ`.** Let `p` be a prime and
let `F` and `G` be commutative formal group laws over a commutative ring `R` whose `p`-series both
have order at least `pʰ` and the same coefficient of `X^(pʰ)`. Then some power series
`g = X + ⋯` is a homomorphism from `F` to `G` up to terms of degree greater than `pʰ`:
`g(F(X, Y)) - G(g(X), g(Y))` has order at least `pʰ + 1`.

Over a field of characteristic `p`, this applies to two formal group laws of height `h` whose
`p`-series have the same leading coefficient. -/
theorem exists_le_order_homDefect_of_coeff_nsmulSeries_eq {p : ℕ} (hp : p.Prime) {h : ℕ}
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ h : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ h) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ h) (G.nsmulSeries p)) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      ((p ^ h + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g).order := by
  have hph : 1 ≤ p ^ h := Nat.one_le_pow _ _ hp.pos
  -- by induction on `m`, the defect can be made to vanish below each degree `m + 2 ≤ pʰ + 1`
  suffices key : ∀ m, m + 1 ≤ p ^ h → ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧
      PowerSeries.coeff 1 g = 1 ∧ ((m + 2 : ℕ) : ℕ∞) ≤ (homDefect F G g).order by
    obtain ⟨g, hg⟩ := key (p ^ h - 1) (by omega)
    exact ⟨g, by rwa [show p ^ h - 1 + 2 = p ^ h + 1 by omega] at hg⟩
  intro m
  induction m with
  | zero =>
    -- the defect of `X` is `F(X, Y) - G(X, Y)`
    refine fun _ ↦ ⟨PowerSeries.X, PowerSeries.constantCoeff_X, PowerSeries.coeff_one_X, ?_⟩
    have hF' := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    rw [homDefect_eq F G PowerSeries.constantCoeff_X, PowerSeries.subst_X hF',
      PowerSeries.subst_X (hX 0), PowerSeries.subst_X (hX 1), finTwo_X_eq_X, subst_self, id,
      ← sub_sub_sub_cancel_right _ _ (X 0 + X 1)]
    exact le_order_sub (two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y)
      (two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y)
  | succ m ih =>
    intro hm
    obtain ⟨g, hg, hg₁, hgo⟩ := ih (by omega)
    exact exists_succ_le_order_homDefect hp hF hG hFG (by omega) (by omega) hg hg₁ hgo

end Step

end FormalGroup
