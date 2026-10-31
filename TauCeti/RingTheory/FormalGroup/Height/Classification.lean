/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.FormalGroup.Frobenius.Factorization
public import TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight
import TauCeti.Data.Fin.Basic
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Classification of formal group laws by height

Let `K` be a separably closed field of characteristic `p`. Lazard's theorem: two commutative
formal group laws `F` and `G` over `K` are isomorphic exactly when they have the same height
(`FormalGroup.height_eq_height_iff_nonempty_formalGroupIso`). Isomorphic laws have the same height
by `TauCeti.FormalGroupIso.height_eq`, and in height `⊤` both are isomorphic to the additive law by
`FormalGroup.height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ`. This file treats finite height `h`,
writing `q = p ^ h`.

An isomorphism `f : F → G` is built degree by degree. Suppose the defect
`Φ(X, Y) = f(F(X, Y)) - G(f(X), f(Y))` vanishes below degree `n ≥ 2`. Its degree-`n` part is a
symmetric additive 2-cocycle, because `F` and `G` are associative and commutative and `G` is linear
on terms of degree `n`. By the symmetric 2-cocycle lemma (`TauCeti.exists_eq_smul_lazardCocycle`) it
is `r C_n` for the Lazard cocycle `C_n`, and replacing `f` by `f + c Xⁿ` adds
`c ((X + Y)ⁿ - Xⁿ - Yⁿ) = c d_n C_n` to it.

* If `n` is not a power of `p`, then `d_n` is a unit in `K` and a unique `c` cancels the defect.
* If `n = pᵏ`, then `d_n = p = 0` and adding `c Xⁿ` does not change the degree-`n` defect. Instead
  `r` is forced: summing `Φ([j]_F(X), X)` over `j < p` shows that `-r` is the coefficient of `Xⁿ`
  in `f([p]_F(X)) - [p]_G(f(X))`. This series vanishes below degree `q`, and its coefficient of
  `X^(m q)` only involves the coefficients of `f` up to degree `m`. Since `[p]_G(X) = ψ(X^q)` for
  an isomorphism `ψ` (`FormalGroup.heightFrobeniusIso`), that coefficient changes by
  `c uᵐ - v c^q` when `f` is replaced by `f + c Xᵐ`, where `u`, `v` are the coefficients of `X^q`
  in `[p]_F`, `[p]_G`. So the free coefficient of `f` in degree `m = pʲ` can be chosen, as a root
  of a separable polynomial `-v x^q + uᵐ x + a`, to make the coefficient of `X^(m q)` vanish, and
  then `r = 0` in degree `pʲ q`. This is where separable closedness is used; the linear coefficient
  of `f` is a nonzero root of `x^(q - 1) = u / v`.

The defect is then zero in the limit, and `f` is an isomorphism since its linear coefficient is
nonzero. The case `G = 𝔾ₐ`, `[p]_F = 0` of the same obstruction argument constructs the normalised
logarithm in `TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight`.

## Main results

* `FormalGroup.height_eq_height_iff_nonempty_formalGroupIso`: over a separably closed field of
  characteristic `p`, commutative formal group laws are isomorphic exactly when their heights
  agree.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Chapter III, §2.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Theorem A2.2.11.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F G : FormalGroup R)

section HomError

/-- The failure `f(F(X, Y)) - G(f(X), f(Y))` of `f` to be a homomorphism from `F` to `G`. -/
private noncomputable def homError (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst F.toPowerSeries f -
    G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) f,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) f]

variable {F G}

/-- Substituting a series without constant term at two points without constant term gives a
substitutable pair. -/
private theorem hasSubst_pair_subst {σ : Type*} {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) {x y : MvPowerSeries σ R} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : HasSubst ![PowerSeries.subst x f, PowerSeries.subst y f] :=
  hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i
    exacts [PowerSeries.constantCoeff_subst_eq_zero hx f hf,
      PowerSeries.constantCoeff_subst_eq_zero hy f hf]

/-- The homomorphism defect of `f` at points `x, y` is `f(F(x, y)) - G(f(x), f(y))`. -/
private theorem subst_homError {σ : Type*} {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) {x y : MvPowerSeries σ R} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    (homError F G f).subst ![x, y] = PowerSeries.subst (F.toPowerSeries.subst ![x, y]) f -
      G.toPowerSeries.subst ![PowerSeries.subst x f, PowerSeries.subst y f] := by
  have hxy : HasSubst ![x, y] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i
    exacts [hx, hy]
  rw [homError, subst_sub hxy,
    subst_powerSeriesSubst hxy (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_comp_subst_apply (hasSubst_pair_subst hf (constantCoeff_X 0) (constantCoeff_X 1)) hxy]
  congr 3
  funext i
  fin_cases i <;>
    simp [subst_powerSeriesSubst hxy (PowerSeries.HasSubst.X _), subst_X hxy]

/-- The homomorphism defect vanishes exactly for homomorphisms. -/
private theorem homError_eq_zero_iff {f : PowerSeries R} :
    homError F G f = 0 ↔ PowerSeries.subst F.toPowerSeries f =
      subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries := by
  have h : (fun i ↦ f.toMvPowerSeries i) = ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) f,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) f] := by
    funext i
    fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]
  rw [homError, sub_eq_zero, h]

/-- The homomorphism defect of zero vanishes. -/
private theorem homError_zero : homError F G 0 = 0 := by
  have h₀ : ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) (0 : PowerSeries R),
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) (0 : PowerSeries R)] = 0 := by
    funext i
    fin_cases i <;> simp [PowerSeries.subst_zero]
  rw [homError, PowerSeries.subst_zero, h₀,
    MvPowerSeries.subst_zero_of_constantCoeff_zero G.zero_constantCoeff, sub_zero]

/-- The coefficients of `G(x, z) - G(y, w)` in degrees at most `n` are those of
`(x - y) + (z - w)`, when `x - y` and `z - w` have order at least `n`. -/
private theorem coeff_subst_sub_subst_of_degree_le {τ : Type*} {x y z w : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (hz : constantCoeff z = 0)
    (hw : constantCoeff w = 0) {n : ℕ} (hxy : (n : ℕ∞) ≤ (x - y).order)
    (hzw : (n : ℕ∞) ≤ (z - w).order) {e : τ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (G.toPowerSeries.subst ![x, z] - G.toPowerSeries.subst ![y, w]) =
      coeff e (x - y) + coeff e (z - w) := by
  have ha₀ : ∀ i, constantCoeff (![x, z] i) = 0 := fun i ↦ by fin_cases i; exacts [hx, hz]
  have hb₀ : ∀ i, constantCoeff (![y, w] i) = 0 := fun i ↦ by fin_cases i; exacts [hy, hw]
  rw [MvPowerSeries.coeff_subst_sub_subst_of_degree_le _ (hasSubst_of_constantCoeff_zero ha₀)
    (hasSubst_of_constantCoeff_zero hb₀) ha₀ hb₀ (fun i ↦ by fin_cases i; exacts [hxy, hzw]) he,
    Fin.sum_univ_two, G.lin_coeff_X, G.lin_coeff_Y, one_mul, one_mul]
  rfl

/-- The degree-`n` part of `G(x, z) - G(y, w)` is that of `(x - y) + (z - w)`, when `x - y` and
`z - w` have order at least `n`. -/
private theorem homogeneousComponent_subst_sub_subst {τ : Type*} {x y z w : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (hz : constantCoeff z = 0)
    (hw : constantCoeff w = 0) {n : ℕ} (hxy : (n : ℕ∞) ≤ (x - y).order)
    (hzw : (n : ℕ∞) ≤ (z - w).order) :
    homogeneousComponent n (G.toPowerSeries.subst ![x, z] - G.toPowerSeries.subst ![y, w]) =
      homogeneousComponent n (x - y) + homogeneousComponent n (z - w) := by
  ext e
  simp only [map_add, coeff_homogeneousComponent]
  split_ifs with he
  · exact coeff_subst_sub_subst_of_degree_le hx hy hz hw hxy hzw he.le
  · rw [_root_.add_zero]

/-- The homomorphism defects of two series agreeing below degree `n` agree below degree `n`. -/
private theorem le_order_homError_sub {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) {n : ℕ} (hfg : (n : ℕ∞) ≤ (f - g).order) :
    (n : ℕ∞) ≤ (homError F G f - homError F G g).order := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) : (n : ℕ∞) ≤ (PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) f -
      PowerSeries.subst (X i) g).order := by
    rw [← PowerSeries.subst_sub (PowerSeries.HasSubst.X i)]
    exact hfg.trans (PowerSeries.le_order_subst_left (constantCoeff_X i))
  have hG := le_order_subst_sub_subst (H := G.toPowerSeries) (k := 1)
    (one_le_order_iff_constCoeff_eq_zero.mpr G.zero_constantCoeff)
    (hasSubst_pair_subst hf (constantCoeff_X (R := R) (0 : Fin 2)) (constantCoeff_X 1))
    (hasSubst_pair_subst hg (constantCoeff_X (R := R) (0 : Fin 2)) (constantCoeff_X 1))
    (fun i ↦ by
      fin_cases i <;> exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) f hf)
    (fun i ↦ by
      fin_cases i <;> exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) g hg)
    (n := n) (fun i ↦ by fin_cases i; exacts [hX 0, hX 1])
  rw [Nat.add_sub_cancel] at hG
  have h : homError F G f - homError F G g = PowerSeries.subst F.toPowerSeries (f - g) -
      (G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) f,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) f] -
      G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) g,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) g]) := by
    rw [homError, homError, PowerSeries.subst_sub hF]
    ring
  rw [h]
  exact le_order_sub (hfg.trans (PowerSeries.le_order_subst_left F.zero_constantCoeff)) hG

/-- The lowest-degree part of the change of the homomorphism defect under `f ↦ f + c Xⁿ` is
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
private theorem homogeneousComponent_homError_add_sub {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) {n : ℕ} (hn : n ≠ 0) (c : R) :
    homogeneousComponent n (homError F G (f + c • PowerSeries.X ^ n) - homError F G f) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  set g : PowerSeries R := c • PowerSeries.X ^ n
  have hg₀ : PowerSeries.constantCoeff g = 0 := by simp [g, hn]
  have hfg₀ : PowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg₀, _root_.add_zero]
  have hgn : (n : ℕ∞) ≤ g.order :=
    PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [g, PowerSeries.coeff_X_pow, hi.ne]
  -- the degree-`n` part of `g(X)` and `g(F(X, Y))`
  have hgX (x : MvPowerSeries (Fin 2) R) (hx₀ : constantCoeff x = 0) :
      homogeneousComponent n (PowerSeries.subst x g) = C c * homogeneousComponent 1 x ^ n := by
    rw [PowerSeries.homogeneousComponent_subst_of_le_order hx₀ hgn]
    simp [g, PowerSeries.coeff_X_pow]
  have hdiff (i : Fin 2) : PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) (f + g) -
      PowerSeries.subst (X i) f = PowerSeries.subst (X i) g := by
    rw [PowerSeries.subst_add (hX i), add_sub_cancel_left]
  have hfX (i : Fin 2) :=
    PowerSeries.constantCoeff_subst_eq_zero (S := R) (constantCoeff_X (R := R) i) _ hf
  have hfgX (i : Fin 2) :=
    PowerSeries.constantCoeff_subst_eq_zero (S := R) (constantCoeff_X (R := R) i) _ hfg₀
  have hgX' (i : Fin 2) : (n : ℕ∞) ≤ (PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) (f + g) -
      PowerSeries.subst (X i) f).order := by
    rw [hdiff]
    exact hgn.trans (PowerSeries.le_order_subst_left (constantCoeff_X _))
  have hG := homogeneousComponent_subst_sub_subst (G := G) (hfgX 0) (hfX 0) (hfgX 1) (hfX 1)
    (hgX' 0) (hgX' 1)
  have h : homError F G (f + g) - homError F G f = PowerSeries.subst F.toPowerSeries g -
      (G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) (f + g),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) (f + g)] -
      G.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) f,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) f]) := by
    rw [homError, homError, PowerSeries.subst_add hF]
    ring
  rw [h, map_sub, hG, hdiff, hdiff]
  rw [hgX _ F.zero_constantCoeff, hgX _ (constantCoeff_X 0), hgX _ (constantCoeff_X 1),
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y, homogeneousComponent_one_X,
    homogeneousComponent_one_X, MvPolynomial.smul_eq_C_mul,
    ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_mul, map_sub, map_pow, map_add, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, MvPolynomial.coe_C]
  ring

end HomError

section Leading

variable {F G}

/-- The degree-`n` part of the homomorphism defect is an additive 2-cocycle: comparing
`f(F(F(X, Y), Z)) = f(F(X, F(Y, Z)))` with the associativity of `G` in degree `n`, where `G` is
linear on the defects, gives `Φₙ(X, Y) + Φₙ(X + Y, Z) = Φₙ(X, Y + Z) + Φₙ(Y, Z)`. -/
private theorem isAddCocycle₂_homError {n : ℕ} {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hn : n ≤ (homError F G f).order) :
    (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homError F G f))).IsAddCocycle₂ := by
  set Φ := homError F G f
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hF₀ (i j : Fin 3) :
      constantCoeff (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_finTwo (hX i) (hX j))
      (fun s ↦ by fin_cases s <;> simp) F.zero_constantCoeff
  have hf₀ {x : MvPowerSeries (Fin 3) R} (hx : constantCoeff x = 0) :
      constantCoeff (PowerSeries.subst x f) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx f hf
  have hG₀ {x y : MvPowerSeries (Fin 3) R} (hx : constantCoeff x = 0)
      (hy : constantCoeff y = 0) : constantCoeff (G.toPowerSeries.subst ![x, y]) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s ↦ by
      fin_cases s
      exacts [hx, hy]) (fun s ↦ by fin_cases s; exacts [hx, hy]) G.zero_constantCoeff
  have hΦ {x y : MvPowerSeries (Fin 3) R} (hx : constantCoeff x = 0)
      (hy : constantCoeff y = 0) : (n : ℕ∞) ≤ (Φ.subst ![x, y]).order :=
    le_order_subst_of_constantCoeff_zero hn (hasSubst_of_constantCoeff_zero fun s ↦ by
      fin_cases s
      exacts [hx, hy]) fun s ↦ by fin_cases s; exacts [hx, hy]
  -- `G` is linear on the defects in degree `n`
  have hlin {x y z w : MvPowerSeries (Fin 3) R} (hx : constantCoeff x = 0)
      (hy : constantCoeff y = 0) (hz : constantCoeff z = 0) (hw : constantCoeff w = 0)
      (hxy : (n : ℕ∞) ≤ (x - y).order) (hzw : (n : ℕ∞) ≤ (z - w).order) :
      homogeneousComponent n (G.toPowerSeries.subst ![x, z]) =
        homogeneousComponent n (G.toPowerSeries.subst ![y, w]) +
          homogeneousComponent n (x - y) + homogeneousComponent n (z - w) := by
    rw [add_assoc, ← homogeneousComponent_subst_sub_subst hx hy hz hw hxy hzw, map_sub,
      add_sub_cancel]
  set x : MvPowerSeries (Fin 3) R := X 0 with hx
  set y : MvPowerSeries (Fin 3) R := X 1 with hy
  set z : MvPowerSeries (Fin 3) R := X 2 with hz
  set Fxy := F.toPowerSeries.subst ![x, y] with hFxy
  set Fyz := F.toPowerSeries.subst ![y, z] with hFyz
  -- the defect relations at `(F(X, Y), Z)`, `(X, Y)`, `(X, F(Y, Z))` and `(Y, Z)`
  have h₁ := subst_homError (F := F) (G := G) hf (hF₀ 0 1) (hX₀ 2)
  have h₂ := subst_homError (F := F) (G := G) hf (hX₀ 0) (hX₀ 1)
  have h₃ := subst_homError (F := F) (G := G) hf (hX₀ 0) (hF₀ 1 2)
  have h₄ := subst_homError (F := F) (G := G) hf (hX₀ 1) (hX₀ 2)
  rw [F.assoc' (hX 0) (hX 1) (hX 2)] at h₁
  have key : Φ.subst ![Fxy, z] + G.toPowerSeries.subst ![PowerSeries.subst Fxy f,
      PowerSeries.subst z f] = Φ.subst ![x, Fyz] + G.toPowerSeries.subst
        ![PowerSeries.subst x f, PowerSeries.subst Fyz f] := by
    rw [h₁, h₃]
    ring
  have hGa := G.assoc' (PowerSeries.HasSubst.of_constantCoeff_zero (hf₀ (hX₀ 0)))
    (PowerSeries.HasSubst.of_constantCoeff_zero (hf₀ (hX₀ 1)))
    (PowerSeries.HasSubst.of_constantCoeff_zero (hf₀ (hX₀ 2)))
  have hL := hlin (hf₀ (hF₀ 0 1)) (hG₀ (hf₀ (hX₀ 0)) (hf₀ (hX₀ 1))) (hf₀ (hX₀ 2))
    (hf₀ (hX₀ 2)) (by rw [← h₂]; exact hΦ (hX₀ 0) (hX₀ 1)) (by simp)
  have hR := hlin (hf₀ (hX₀ 0)) (hf₀ (hX₀ 0)) (hf₀ (hF₀ 1 2))
    (hG₀ (hf₀ (hX₀ 1)) (hf₀ (hX₀ 2))) (by simp) (by rw [← h₄]; exact hΦ (hX₀ 1) (hX₀ 2))
  rw [← h₂, sub_self, map_zero, _root_.add_zero] at hL
  rw [← h₄, sub_self, map_zero, _root_.add_zero] at hR
  have h := congrArg (homogeneousComponent n) key
  rw [map_add, map_add, hL, hR, hGa] at h
  -- read off the polynomial cocycle identity
  have hlx := homogeneousComponent_one_X (R := R) (0 : Fin 3)
  have hly := homogeneousComponent_one_X (R := R) (1 : Fin 3)
  have hlz := homogeneousComponent_one_X (R := R) (2 : Fin 3)
  have hlxy := homogeneousComponent_one_subst_pair (S := R) F.zero_constantCoeff F.lin_coeff_X
    F.lin_coeff_Y (hX₀ 0) (hX₀ 1)
  have hlyz := homogeneousComponent_one_subst_pair (S := R) F.zero_constantCoeff F.lin_coeff_X
    F.lin_coeff_Y (hX₀ 1) (hX₀ 2)
  rw [homogeneousComponent_subst_eq_coe_aeval hn (a := ![Fxy, z]) (l := ![MvPolynomial.X 0 +
      MvPolynomial.X 1, MvPolynomial.X 2]) (fun s ↦ by fin_cases s; exacts [hF₀ 0 1, hX₀ 2])
      (fun s ↦ by fin_cases s <;> simp [x, y, z, Fxy, hlxy, hlx, hly, hlz]),
    homogeneousComponent_subst_eq_coe_aeval hn (a := ![x, Fyz]) (l := ![MvPolynomial.X 0,
      MvPolynomial.X 1 + MvPolynomial.X 2]) (fun s ↦ by fin_cases s; exacts [hX₀ 0, hF₀ 1 2])
      (fun s ↦ by fin_cases s <;> simp [x, y, z, Fyz, hlyz, hlx, hly, hlz]),
    homogeneousComponent_subst_eq_coe_aeval hn (a := ![x, y]) (l := ![MvPolynomial.X 0,
      MvPolynomial.X 1]) (fun s ↦ by fin_cases s; exacts [hX₀ 0, hX₀ 1])
      (fun s ↦ by fin_cases s <;> simp [x, y, hlx, hly]),
    homogeneousComponent_subst_eq_coe_aeval hn (a := ![y, z]) (l := ![MvPolynomial.X 1,
      MvPolynomial.X 2]) (fun s ↦ by fin_cases s; exacts [hX₀ 1, hX₀ 2])
      (fun s ↦ by fin_cases s <;> simp [y, z, hly, hlz])] at h
  rw [MvPolynomial.isAddCocycle₂_iff]
  refine MvPolynomial.coe_inj.mp ?_
  rw [MvPolynomial.coe_add, MvPolynomial.coe_add]
  linear_combination h

/-- The degree-`n` part of the homomorphism defect is symmetric when `F` and `G` are
commutative. -/
private theorem isSymmetric_homError [F.IsComm] [G.IsComm] {n : ℕ}
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hn : n ≤ (homError F G f).order) :
    (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homError F G f))).IsSymmetric := by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have hswap : (homError F G f).subst ![X 1, X 0] = homError F G f := by
    rw [subst_homError hf (constantCoeff_X 1) (constantCoeff_X 0), F.comm' (hX 1) (hX 0),
      G.comm' (PowerSeries.HasSubst.of_constantCoeff_zero
        (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) f hf))
      (PowerSeries.HasSubst.of_constantCoeff_zero
        (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) f hf)),
      finTwo_X_eq_X, subst_self, id, homError]
  have h : MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 0]
      (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homError F G f))) =
        MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (homError F G f)) := by
    refine MvPolynomial.coe_inj.mp ?_
    rw [← homogeneousComponent_subst_eq_coe_aeval hn (a := ![X 1, X 0])
      (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]), hswap,
      coe_homogeneousComponent_truncTotal]
  intro e
  rcases Equiv.Perm.eq_one_or_swap_fin_two e with rfl | rfl
  · simp
  · have hswap' : (MvPolynomial.X ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → MvPolynomial (Fin 2) R) =
        ![MvPolynomial.X 1, MvPolynomial.X 0] := by
      funext i
      fin_cases i <;> simp
    rw [MvPolynomial.rename_eq_aeval, hswap']
    exact h

end Leading

section PSeries

variable {F G}

/-- Substituting a power series into `G(a, X)`. -/
private theorem subst_subst_pair_X (a : PowerSeries R) {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.subst f (G.toPowerSeries.subst ![a, PowerSeries.X]) =
      G.toPowerSeries.subst ![PowerSeries.subst f a, f] := by
  have hf' := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  rw [PowerSeries.subst_def _ (subst _ _), subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero fun s ↦ by
      fin_cases s; exacts [ha, PowerSeries.constantCoeff_X]) hf'.const]
  congr 2
  funext s
  fin_cases s
  · simp [PowerSeries.subst_def]
  · simpa [PowerSeries.subst_def] using PowerSeries.subst_X hf'

/-- **The homomorphism defect along the multiplication series.** If the defect `Φ` of `f`
vanishes below degree `n`, then so does `f([m]_F(X)) - [m]_G(f(X))`, whose coefficient of `Xⁿ`
is that of `∑_{j < m} Φ([j]_F(X), X)`. -/
private theorem subst_nsmulSeries_sub {n : ℕ} {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hn : n ≤ (homError F G f).order) (m : ℕ) :
    (n : ℕ∞) ≤ MvPowerSeries.order (PowerSeries.subst (F.nsmulSeries m) f -
      PowerSeries.subst f (G.nsmulSeries m)) ∧
    PowerSeries.coeff n (PowerSeries.subst (F.nsmulSeries m) f -
      PowerSeries.subst f (G.nsmulSeries m)) = ∑ j ∈ Finset.range m,
        PowerSeries.coeff n ((homError F G f).subst ![F.nsmulSeries j, PowerSeries.X]) := by
  induction m with
  | zero =>
    simp [nsmulSeries_zero, PowerSeries.subst_zero_of_constantCoeff_zero hf, PowerSeries.subst_zero]
  | succ m ih =>
    obtain ⟨ihord, ihcoeff⟩ := ih
    have hFm := F.constantCoeff_nsmulSeries m
    have hGm := G.constantCoeff_nsmulSeries m
    have hfm : PowerSeries.constantCoeff (PowerSeries.subst (F.nsmulSeries m) f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hFm f hf
    have hgm : PowerSeries.constantCoeff (PowerSeries.subst f (G.nsmulSeries m)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hf _ hGm
    have hΦ := subst_homError (F := F) (G := G) hf hFm PowerSeries.constantCoeff_X
    rw [← nsmulSeries_succ, PowerSeries.X_subst] at hΦ
    -- `f([m + 1]_F) - [m + 1]_G(f)` is the defect at `([m]_F, X)` plus a difference of values
    -- of `G`
    have hsplit : PowerSeries.subst (F.nsmulSeries (m + 1)) f -
        PowerSeries.subst f (G.nsmulSeries (m + 1)) =
          (homError F G f).subst ![F.nsmulSeries m, PowerSeries.X] +
            (G.toPowerSeries.subst ![PowerSeries.subst (F.nsmulSeries m) f, f] -
              G.toPowerSeries.subst ![PowerSeries.subst f (G.nsmulSeries m), f]) := by
      rw [hΦ, nsmulSeries_succ G, subst_subst_pair_X _ hf hGm]
      ring
    have hab : (n : ℕ∞) ≤ MvPowerSeries.order (f - f) := by simp
    rw [hsplit]
    refine ⟨le_order_add (le_order_subst_of_constantCoeff_zero hn (F.hasSubst_nsmulSeries_X m)
      fun s ↦ by fin_cases s; exacts [hFm, PowerSeries.constantCoeff_X]) ?_, ?_⟩
    · have ha₀ : ∀ i, constantCoeff (![PowerSeries.subst (F.nsmulSeries m) f, f] i) = 0 :=
        fun i ↦ by fin_cases i; exacts [hfm, hf]
      have hb₀ : ∀ i, constantCoeff (![PowerSeries.subst f (G.nsmulSeries m), f] i) = 0 :=
        fun i ↦ by fin_cases i; exacts [hgm, hf]
      simpa using le_order_subst_sub_subst (H := G.toPowerSeries) (k := 1)
        (one_le_order_iff_constCoeff_eq_zero.mpr G.zero_constantCoeff)
        (hasSubst_of_constantCoeff_zero ha₀) (hasSubst_of_constantCoeff_zero hb₀) ha₀ hb₀
        (n := n) fun i ↦ by fin_cases i; exacts [ihord, hab]
    · have hc := coeff_subst_sub_subst_of_degree_le (G := G) hfm hgm hf hf ihord hab
        (e := Finsupp.single () n) (by simp)
      rw [sub_self, map_zero, _root_.add_zero] at hc
      rw [map_add, Finset.sum_range_succ, ← ihcoeff, add_comm,
        PowerSeries.coeff_def (by simp : Finsupp.single () n () = n), hc]

/-- **The defect in degree `pᵏ` is read off from the `p`-series.** Let `p` be a prime with
`p = 0` in `R`, and suppose the homomorphism defect of `f` vanishes below degree `n = pᵏ`,
`k ≥ 1`, with degree-`n` part `r C_n`. Then the coefficient of `Xⁿ` in
`f([p]_F(X)) - [p]_G(f(X))` is `-r`, because `∑_{j < p} C_n(j, 1) = -1`. -/
private theorem coeff_subst_nsmulSeries_sub {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) {k : ℕ}
    (hk : k ≠ 0) {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hn : p ^ k ≤ (homError F G f).order) {r : R}
    (hr : MvPolynomial.homogeneousComponent (p ^ k) (truncTotal (p ^ k + 1) (homError F G f)) =
      r • TauCeti.lazardCocycle (p ^ k) R) :
    PowerSeries.coeff (p ^ k) (PowerSeries.subst (F.nsmulSeries p) f -
      PowerSeries.subst f (G.nsmulSeries p)) = -r := by
  rw [(subst_nsmulSeries_sub hf hn p).2]
  -- the degree-`pᵏ` part of `Φ([j]_F(X), X)` is `r C_n(j X, X)`
  have hterm (j : ℕ) : homogeneousComponent (p ^ k)
      ((homError F G f).subst ![F.nsmulSeries j, PowerSeries.X]) =
        MvPolynomial.coeToMvPowerSeries.ringHom (r • MvPolynomial.aeval
          ![(j : MvPolynomial Unit R) * MvPolynomial.X (), MvPolynomial.X ()]
          (TauCeti.lazardCocycle (p ^ k) R)) := by
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      homogeneousComponent_subst_eq_coe_aeval hn
      (fun i ↦ by fin_cases i; exacts [F.constantCoeff_nsmulSeries j, PowerSeries.constantCoeff_X])
      (fun i ↦ ?_), hr, _root_.map_smul]
    fin_cases i
    · -- the linear part of `[j]_F` is `j X`
      have hj : ((j : MvPolynomial Unit R) : MvPowerSeries Unit R) = j :=
        map_natCast MvPolynomial.coeToMvPowerSeries.ringHom j
      simp [homogeneousComponent_one_eq_C_mul_X, ← PowerSeries.coeff_def, hj]
    · exact (homogeneousComponent_one_X (R := R) ()).trans (MvPolynomial.coe_X _).symm
  have hcoeff (x : PowerSeries R) : PowerSeries.coeff (p ^ k) x =
      MvPowerSeries.coeff (Finsupp.single () (p ^ k)) (homogeneousComponent (p ^ k) x) := by
    rw [coeff_homogeneousComponent, ite_eq_left (by simp),
      PowerSeries.coeff_def (by simp : Finsupp.single () (p ^ k) () = p ^ k)]
  rw [Finset.sum_congr rfl fun j _ ↦ by rw [hcoeff, hterm], ← map_sum, ← map_sum,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe, ← Finset.smul_sum,
    TauCeti.sum_aeval_natCast_mul_lazardCocycle hp
      (by rw [← map_natCast (MvPolynomial.C (σ := Unit)), hpR, map_zero]) hk]
  simp [MvPolynomial.coeff_X_pow]

end PSeries

section Field

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] {F G : FormalGroup K}
  [F.IsComm] [G.IsComm] {h : ℕ}

/-- The failure `f([p]_F(X)) - [p]_G(f(X))` of `f` to commute with multiplication by `p`. -/
private noncomputable def pSeriesError (F G : FormalGroup K) (p : ℕ) (f : PowerSeries K) :
    PowerSeries K :=
  PowerSeries.subst (F.nsmulSeries p) f - PowerSeries.subst f (G.nsmulSeries p)

omit hp [CharP K p] [F.IsComm] [G.IsComm] in
/-- The `p`-series failure of zero vanishes. -/
private theorem pSeriesError_zero : pSeriesError F G p 0 = 0 := by
  rw [pSeriesError, PowerSeries.subst_zero, PowerSeries.subst_zero_of_constantCoeff_zero
    (G.constantCoeff_nsmulSeries p), sub_zero]

/-- Over a field of characteristic `p`, `[p]_G(f) = ψ(f^(p^h))` where `ψ` is the isomorphism
from the `h`-fold Frobenius twist of `G` back to `G`, `h` being the height of `G`. -/
private theorem subst_nsmulSeries_eq_subst_pow (hG : G.height p = h) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (G.nsmulSeries p) =
      PowerSeries.subst (f ^ p ^ h) (G.heightFrobeniusIso hG).toHom.toPowerSeries := by
  have h₁ := congrArg TauCeti.FormalGroupHom.toPowerSeries
    (G.heightFrobeniusIso_comp_iterateFrobeniusHom hG)
  rw [TauCeti.FormalGroupHom.comp_toPowerSeries, iterateFrobeniusHom_toPowerSeries,
    nsmulHom_toPowerSeries] at h₁
  have hf' := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  rw [← h₁, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero'
    (by simp [hp.out.ne_zero])) hf', PowerSeries.subst_pow hf', PowerSeries.subst_X hf']

/-- The coefficients of `f([p]_F(X)) - [p]_G(f(X))` in degrees below `(M + 1) p ^ h` only depend
on the coefficients of `f` in degrees at most `M`. -/
private theorem le_order_pSeriesError_sub (hF : F.height p = h) (hG : G.height p = h)
    {f g : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) {M : ℕ} (hfg : (M : ℕ∞) ≤ (f - g).order) :
    ((M * p ^ h : ℕ) : ℕ∞) ≤ (pSeriesError F G p f - pSeriesError F G p g).order := by
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set ψ := (G.heightFrobeniusIso hG).toHom.toPowerSeries
  have hψ : constantCoeff (ψ : MvPowerSeries Unit K) = 0 :=
    (G.heightFrobeniusIso hG).toHom.zero_constantCoeff
  have hq₀ (x : PowerSeries K) (hx : PowerSeries.constantCoeff x = 0) :
      constantCoeff (x ^ p ^ h : MvPowerSeries Unit K) = 0 := by
    rw [map_pow, ← PowerSeries.constantCoeff_eq, hx, zero_pow (pow_ne_zero h hp.out.ne_zero)]
  -- `f(X) - g(X)` composed with `[p]_F`, of order `p ^ h`
  have h₁ : ((M * p ^ h : ℕ) : ℕ∞) ≤
      MvPowerSeries.order (PowerSeries.subst (F.nsmulSeries p) (f - g)) := by
    rw [← PowerSeries.order_eq_order, PowerSeries.order_subst (F.constantCoeff_nsmulSeries p),
      F.height_eq_natCast_iff.mp hF, mul_comm M]
    push_cast
    gcongr
  -- `ψ(f ^ (p ^ h)) - ψ(g ^ (p ^ h))`, where `f ^ (p ^ h) - g ^ (p ^ h) = (f - g) ^ (p ^ h)`
  have h₂ : ((M * p ^ h : ℕ) : ℕ∞) ≤ MvPowerSeries.order
      (PowerSeries.subst (f ^ p ^ h) ψ - PowerSeries.subst (g ^ p ^ h) ψ) := by
    have hpow : ((M * p ^ h : ℕ) : ℕ∞) ≤
        MvPowerSeries.order ((f ^ p ^ h - g ^ p ^ h : PowerSeries K)) := by
      rw [← sub_pow_char_pow, ← PowerSeries.order_eq_order]
      refine (PowerSeries.le_order_pow _ _).trans' ?_
      rw [nsmul_eq_mul, mul_comm M]
      push_cast
      gcongr
    simpa [PowerSeries.subst_def] using MvPowerSeries.le_order_subst_sub_subst (H := ψ) (k := 1)
      (one_le_order_iff_constCoeff_eq_zero.mpr hψ)
      (a := fun _ ↦ (f ^ p ^ h : PowerSeries K)) (b := fun _ ↦ (g ^ p ^ h : PowerSeries K))
      (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ f hf)
      (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ g hg) (fun _ ↦ hq₀ f hf) (fun _ ↦ hq₀ g hg)
      fun _ ↦ hpow
  have hsplit : pSeriesError F G p f - pSeriesError F G p g =
      PowerSeries.subst (F.nsmulSeries p) (f - g) -
        (PowerSeries.subst (f ^ p ^ h) ψ - PowerSeries.subst (g ^ p ^ h) ψ) := by
    rw [pSeriesError, pSeriesError, subst_nsmulSeries_eq_subst_pow hG hf,
      subst_nsmulSeries_eq_subst_pow hG hg,
      PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero'
        (F.constantCoeff_nsmulSeries p))]
    ring
  rw [hsplit, PowerSeries.order_eq_order]
  exact le_order_sub h₁ h₂

/-- **The `p`-series failure under a perturbation in degree `M`.** Replacing `f` by `f + c Xᴹ`
changes the coefficient of `X^(M p ^ h)` in `f([p]_F(X)) - [p]_G(f(X))` by `c uᴹ - v c^(p ^ h)`,
where `u` and `v` are the coefficients of `X^(p ^ h)` in `[p]_F` and `[p]_G`. -/
private theorem coeff_pSeriesError_add (hF : F.height p = h) (hG : G.height p = h)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {M : ℕ} (hM : M ≠ 0) (c : K) :
    PowerSeries.coeff (M * p ^ h) (pSeriesError F G p (f + c • PowerSeries.X ^ M)) =
      PowerSeries.coeff (M * p ^ h) (pSeriesError F G p f) +
        c * PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ M -
          PowerSeries.coeff (p ^ h) (G.nsmulSeries p) * c ^ p ^ h := by
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set q := p ^ h
  set ψ := (G.heightFrobeniusIso hG).toHom.toPowerSeries
  have hψ : constantCoeff (ψ : MvPowerSeries Unit K) = 0 :=
    (G.heightFrobeniusIso hG).toHom.zero_constantCoeff
  have hcX : PowerSeries.constantCoeff (c • PowerSeries.X ^ M : PowerSeries K) = 0 := by
    simp [hM]
  have hfc : PowerSeries.constantCoeff (f + c • PowerSeries.X ^ M) = 0 := by
    rw [map_add, hf, hcX, _root_.add_zero]
  have hFp := F.constantCoeff_nsmulSeries p
  have hFp' := PowerSeries.HasSubst.of_constantCoeff_zero' hFp
  -- the perturbation composed with `[p]_F`: `c [p]_F ^ M`, whose coefficient is `c uᴹ`
  have hF₁ : PowerSeries.coeff (M * q) (PowerSeries.subst (F.nsmulSeries p)
      (c • PowerSeries.X ^ M : PowerSeries K)) = c * PowerSeries.coeff q (F.nsmulSeries p) ^ M := by
    obtain ⟨w, hw⟩ := PowerSeries.X_pow_dvd_iff.mpr fun m hm ↦ PowerSeries.coeff_of_lt_order m
      (by rw [F.height_eq_natCast_iff.mp hF]; exact_mod_cast hm)
    rw [PowerSeries.subst_smul hFp', PowerSeries.subst_pow hFp', PowerSeries.subst_X hFp', hw,
      mul_pow, ← pow_mul, PowerSeries.coeff_smul, mul_comm q M]
    simp [q, PowerSeries.coeff_X_pow_mul']
  -- `ψ((f + c Xᴹ) ^ q) - ψ(f ^ q) = ψ(f ^ q + c ^ q X^(M q)) - ψ(f ^ q)`, of coefficient `v c ^ q`
  have hq₀ (x : PowerSeries K) (hx : PowerSeries.constantCoeff x = 0) :
      constantCoeff (x ^ q : MvPowerSeries Unit K) = 0 := by
    rw [map_pow, ← PowerSeries.constantCoeff_eq, hx, zero_pow (pow_ne_zero h hp.out.ne_zero)]
  have hdiff : (f + c • PowerSeries.X ^ M) ^ q - f ^ q =
      (c ^ q • PowerSeries.X ^ (M * q) : PowerSeries K) := by
    rw [add_pow_char_pow, smul_pow, ← pow_mul, add_sub_cancel_left]
  have hord : ((M * q : ℕ) : ℕ∞) ≤ MvPowerSeries.order
      ((f + c • PowerSeries.X ^ M) ^ q - f ^ q : PowerSeries K) := by
    rw [hdiff, ← PowerSeries.order_eq_order]
    exact PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
  have hG₁ := MvPowerSeries.coeff_subst_sub_subst_of_degree_le ψ
    (a := fun _ ↦ ((f + c • PowerSeries.X ^ M) ^ q : PowerSeries K))
    (b := fun _ ↦ (f ^ q : PowerSeries K))
    (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ _ hfc)
    (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ f hf) (fun _ ↦ hq₀ _ hfc) (fun _ ↦ hq₀ f hf)
    (fun _ ↦ hord) (e := Finsupp.single () (M * q)) (by simp)
  have hG₁' : PowerSeries.coeff (M * q) (PowerSeries.subst ((f + c • PowerSeries.X ^ M) ^ q) ψ -
      PowerSeries.subst (f ^ q) ψ) = PowerSeries.coeff 1 ψ * c ^ q := by
    rw [PowerSeries.coeff_def (by simp : Finsupp.single () (M * q) () = M * q),
      PowerSeries.subst_def, PowerSeries.subst_def, hG₁, Fintype.sum_unique, hdiff,
      ← PowerSeries.coeff_def (by simp : Finsupp.single () (M * q) () = M * q),
      ← PowerSeries.coeff_def (by simp : Finsupp.single (default : Unit) 1 () = 1)]
    simp
  have hv : PowerSeries.coeff 1 ψ = PowerSeries.coeff q (G.nsmulSeries p) := by
    rw [coeff_heightFrobeniusIso, mul_one]
  have hsplit : pSeriesError F G p (f + c • PowerSeries.X ^ M) - pSeriesError F G p f =
      PowerSeries.subst (F.nsmulSeries p) (c • PowerSeries.X ^ M : PowerSeries K) -
        (PowerSeries.subst ((f + c • PowerSeries.X ^ M) ^ q) ψ - PowerSeries.subst (f ^ q) ψ) := by
    rw [pSeriesError, pSeriesError, subst_nsmulSeries_eq_subst_pow hG hf,
      subst_nsmulSeries_eq_subst_pow hG hfc, PowerSeries.subst_add hFp']
    ring
  have h := congrArg (PowerSeries.coeff (M * q)) hsplit
  rw [map_sub, map_sub, hF₁, hG₁', hv] at h
  linear_combination h

/-- Below degree `p ^ h`, the `p`-series failure vanishes. -/
private theorem coeff_pSeriesError_of_lt (hF : F.height p = h) (hG : G.height p = h)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {n : ℕ} (hn : n < p ^ h) :
    PowerSeries.coeff n (pSeriesError F G p f) = 0 := by
  have hf₁ : (1 : ℕ∞) ≤ f.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf
  rw [pSeriesError, map_sub, PowerSeries.coeff_of_lt_order, PowerSeries.coeff_of_lt_order,
    sub_zero]
  · rw [PowerSeries.order_subst hf, G.height_eq_natCast_iff.mp hG]
    calc (n : ℕ∞) < (p ^ h : ℕ) := by exact_mod_cast hn
      _ = 1 * (p ^ h : ℕ) := (one_mul _).symm
      _ ≤ f.order * (p ^ h : ℕ) := by gcongr
  · rw [PowerSeries.order_subst (F.constantCoeff_nsmulSeries p), F.height_eq_natCast_iff.mp hF]
    calc (n : ℕ∞) < (p ^ h : ℕ) := by exact_mod_cast hn
      _ = (p ^ h : ℕ) * 1 := (mul_one _).symm
      _ ≤ (p ^ h : ℕ) * f.order := by gcongr

/-- **The inductive step.** Let `F` and `G` have the same finite height `h` over a separably
closed field, and let `f` be a homomorphism from `F` to `G` up to degree `N ≥ 1`, whose `p`-series
failure vanishes in the degrees `pʲ p ^ h` with `pʲ ≤ N`. Then for a suitable `c`, `f + c X^(N + 1)`
has the same properties with `N + 1` in place of `N`.

In degree `M = N + 1` the defect is `r C_M`. If `M` is not a power of `p`, then `C_M` is a unit
multiple of `(X + Y)ᴹ - Xᴹ - Yᴹ` and `c` is chosen to cancel it. If `M = pᵏ`, then `r = 0`, since
`-r` is the coefficient of `Xᴹ` in the `p`-series failure, which vanishes below degree `p ^ h` and
by assumption at `M = p^(k - h) p ^ h` otherwise; now `c` is a root of the separable polynomial
`-v x^(p ^ h) + uᴹ x + a` that makes the `p`-series failure vanish in degree `M p ^ h`. -/
private theorem exists_le_order_homError_add [IsSepClosed K] (hF : F.height p = h)
    (hG : G.height p = h) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {N : ℕ}
    (hN : N ≠ 0) (hΦ : ((N + 1 : ℕ) : ℕ∞) ≤ (homError F G f).order)
    (hP : ∀ j, p ^ j ≤ N → PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p f) = 0) :
    ∃ c : K, ((N + 2 : ℕ) : ℕ∞) ≤ (homError F G (f + c • PowerSeries.X ^ (N + 1))).order ∧
      ∀ j, p ^ j ≤ N + 1 → PowerSeries.coeff (p ^ j * p ^ h)
        (pSeriesError F G p (f + c • PowerSeries.X ^ (N + 1))) = 0 := by
  have hp' := hp.out
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hh : h ≠ 0 := by
    have := F.one_le_height (p := p)
    rw [hF] at this
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (by exact_mod_cast this))
  set M := N + 1 with hM
  have hcX (c : K) : PowerSeries.constantCoeff (c • PowerSeries.X ^ M : PowerSeries K) = 0 := by
    simp [M]
  have hXM (c : K) : (M : ℕ∞) ≤ (f + c • PowerSeries.X ^ M - f).order := by
    rw [add_sub_cancel_left]
    exact PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
  have hfc (c : K) : PowerSeries.constantCoeff (f + c • PowerSeries.X ^ M) = 0 := by
    rw [map_add, hf, hcX, _root_.add_zero]
  -- the defect in degree `M` is a multiple `r C_M` of the Lazard cocycle
  obtain ⟨r, hr⟩ : ∃ r : K, MvPolynomial.homogeneousComponent M (truncTotal (M + 1)
      (homError F G f)) = r • TauCeti.lazardCocycle M K :=
    TauCeti.exists_eq_smul_lazardCocycle (by omega)
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _) (isSymmetric_homError hf hΦ)
    (isAddCocycle₂_homError hf hΦ)
  -- after adding `c Xᴹ`, the defect in degree `M` is `c ((X + Y)ᴹ - Xᴹ - Yᴹ) + r C_M`
  have hcomp (c : K) : homogeneousComponent M (homError F G (f + c • PowerSeries.X ^ M)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ M - MvPolynomial.X 0 ^ M -
        MvPolynomial.X 1 ^ M) + r • TauCeti.lazardCocycle M K : MvPolynomial (Fin 2) K) :
          MvPowerSeries (Fin 2) K) := by
    rw [← sub_add_cancel (homError F G (f + c • PowerSeries.X ^ M)) (homError F G f), map_add,
      homogeneousComponent_homError_add_sub hf (by omega), ← coe_homogeneousComponent_truncTotal,
      hr, MvPolynomial.coe_add]
  have hord (c : K) (hc : c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ M - MvPolynomial.X 0 ^ M -
      MvPolynomial.X 1 ^ M) + r • TauCeti.lazardCocycle M K = 0) :
      ((N + 2 : ℕ) : ℕ∞) ≤ (homError F G (f + c • PowerSeries.X ^ M)).order := by
    have hM' : (M : ℕ∞) ≤ (homError F G (f + c • PowerSeries.X ^ M)).order := by
      rw [← sub_add_cancel (homError F G (f + c • PowerSeries.X ^ M)) (homError F G f)]
      exact le_order_add (le_order_homError_sub (hfc c) hf (hXM c))
        (hΦ.trans' (by exact_mod_cast le_rfl))
    exact succ_le_order_of_homogeneousComponent_eq_zero hM'
      (by rw [hcomp, hc, MvPolynomial.coe_zero])
  -- the `p`-series failure is unchanged in degrees `pʲ p ^ h` with `pʲ < M`
  have hlow (c : K) {j : ℕ} (hj : p ^ j < M) : PowerSeries.coeff (p ^ j * p ^ h)
      (pSeriesError F G p (f + c • PowerSeries.X ^ M)) = 0 := by
    rw [← sub_add_cancel (pSeriesError F G p (f + c • PowerSeries.X ^ M)) (pSeriesError F G p f),
      map_add, hP j (by omega), _root_.add_zero, PowerSeries.coeff_of_lt_order]
    exact (le_order_pSeriesError_sub hF hG (hfc c) hf (hXM c)).trans_lt' (by
      exact_mod_cast Nat.mul_lt_mul_of_pos_right hj (pow_pos hp'.pos h))
  by_cases hpow : ∃ k, M = p ^ k
  · obtain ⟨k, hk⟩ := hpow
    have hk₀ : k ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at hk
      omega
    -- the defect vanishes in degree `M = pᵏ`
    have hr₀ : r = 0 := by
      have hc := coeff_subst_nsmulSeries_sub hp' hpK hk₀ hf (hk ▸ hΦ) (hk ▸ hr)
      rw [← pSeriesError, ← hk] at hc
      rw [← neg_eq_zero, ← hc]
      rcases lt_or_ge k h with hkh | hkh
      · exact coeff_pSeriesError_of_lt hF hG hf (hk ▸ Nat.pow_lt_pow_right hp'.one_lt hkh)
      · rw [hk, ← Nat.pow_sub_mul_pow p hkh]
        refine hP (k - h) ?_
        have := Nat.pow_lt_pow_right hp'.one_lt (show k - h < k by omega)
        omega
    -- choose `c` to make the `p`-series failure vanish in degree `M p ^ h`
    have hu : PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ≠ 0 := by
      have := (F.heightFrobeniusIso hF).isUnit_coeff_one
      rwa [coeff_heightFrobeniusIso, mul_one, isUnit_iff_ne_zero] at this
    obtain ⟨c, hc⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
      (-PowerSeries.coeff (p ^ h) (G.nsmulSeries p))
      (PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ M)
      (PowerSeries.coeff (M * p ^ h) (pSeriesError F G p f))
      (by rw [Nat.cast_pow, hpK, zero_pow hh])
      (by have := Nat.one_lt_pow hh hp'.one_lt; omega) (pow_ne_zero _ hu)
    refine ⟨c, hord c ?_, fun j hj ↦ ?_⟩
    · -- `(X + Y) ^ pᵏ = X ^ pᵏ + Y ^ pᵏ` in characteristic `p`
      rw [hr₀, zero_smul, _root_.add_zero, hk, add_pow_char_pow]
      simp
    · rcases hj.lt_or_eq with hj | hj
      · exact hlow c hj
      · rw [hj, coeff_pSeriesError_add hF hG hf (by omega)]
        linear_combination hc
  · -- `d_M` is prime to `p`, hence a unit, and `r C_M = (r d_M⁻¹) ((X + Y)ᴹ - Xᴹ - Yᴹ)`
    have hd : IsUnit ((TauCeti.lazardGcd M : ℕ) : K) := by
      have hcop : (TauCeti.lazardGcd M).Coprime p := Nat.Coprime.symm <|
        (Nat.Prime.coprime_iff_not_dvd hp').mpr fun h ↦
          hpow ((TauCeti.prime_dvd_lazardGcd_iff hp' (by omega)).mp h)
      have : IsCoprime ((TauCeti.lazardGcd M : ℕ) : K) (p : K) := by
        simpa using (Nat.isCoprime_iff_coprime.mpr hcop).intCast (R := K)
      rwa [hpK, isCoprime_zero_right] at this
    refine ⟨-r * ↑hd.unit⁻¹, hord _ ?_, fun j hj ↦
      hlow _ (hj.lt_of_ne fun h ↦ hpow ⟨j, h.symm⟩)⟩
    rw [← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega), ← Nat.cast_smul_eq_nsmul K, smul_smul,
      mul_assoc, hd.val_inv_mul, mul_one, ← add_smul, neg_add_cancel, zero_smul]

section Construction

/-- The approximations to an isomorphism: starting from `c₁ X`, step `n` adds the multiple
`c n g • X ^ (n + 2)` of the current approximation `g`. -/
private noncomputable def approx (c₁ : K) (c : ℕ → PowerSeries K → K) : ℕ → PowerSeries K
  | 0 => c₁ • PowerSeries.X ^ 1
  | n + 1 => approx c₁ c n + c n (approx c₁ c n) • PowerSeries.X ^ (n + 2)

/-- **Existence of an isomorphism.** Two commutative formal group laws of the same finite height
over a separably closed field of characteristic `p` are related by a homomorphism with nonzero
linear coefficient. It is the limit of the approximations built by
`exists_le_order_homError_add`, starting from `c₁ X` with `c₁ ^ (p ^ h - 1) = u / v`, where `u` and
`v` are the coefficients of `X^(p ^ h)` in `[p]_F` and `[p]_G`. -/
private theorem exists_formalGroupHom_coeff_one_ne_zero [IsSepClosed K] (hF : F.height p = h)
    (hG : G.height p = h) :
    ∃ f : TauCeti.FormalGroupHom F G, PowerSeries.coeff 1 f.toPowerSeries ≠ 0 := by
  have hp' := hp.out
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hh : h ≠ 0 := by
    have := F.one_le_height (p := p)
    rw [hF] at this
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (by exact_mod_cast this))
  have hq : 2 ≤ p ^ h := by have := Nat.one_lt_pow hh hp'.one_lt; omega
  set u := PowerSeries.coeff (p ^ h) (F.nsmulSeries p)
  set v := PowerSeries.coeff (p ^ h) (G.nsmulSeries p)
  have hu : u ≠ 0 := by
    have := (F.heightFrobeniusIso hF).isUnit_coeff_one
    rwa [coeff_heightFrobeniusIso, mul_one, isUnit_iff_ne_zero] at this
  have hv : v ≠ 0 := by
    have := (G.heightFrobeniusIso hG).isUnit_coeff_one
    rwa [coeff_heightFrobeniusIso, mul_one, isUnit_iff_ne_zero] at this
  -- the linear coefficient: a root of `x ^ (p ^ h - 1) = u / v`
  have : NeZero ((p ^ h - 1 : ℕ) : K) := ⟨by
    rw [Nat.cast_sub (by omega), Nat.cast_pow, hpK, zero_pow hh, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero⟩
  obtain ⟨c₁, hc₁⟩ := IsSepClosed.exists_pow_nat_eq (u / v) (p ^ h - 1)
  have hc₁₀ : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc₁
    exact div_ne_zero hu hv hc₁.symm
  choose! c hc using fun (n : ℕ) (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = 0)
    (hΦ : ((n + 2 : ℕ) : ℕ∞) ≤ (homError F G g).order)
    (hP : ∀ j, p ^ j ≤ n + 1 → PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p g) = 0) ↦
    exists_le_order_homError_add hF hG hg (N := n + 1) (by omega) hΦ hP
  -- `approx c₁ c n` is a homomorphism up to degree `n + 2` with the required `p`-series property
  have key (n : ℕ) : PowerSeries.constantCoeff (approx c₁ c n) = 0 ∧
      PowerSeries.coeff 1 (approx c₁ c n) = c₁ ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ (homError F G (approx c₁ c n)).order ∧
      ∀ j, p ^ j ≤ n + 1 →
        PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p (approx c₁ c n)) = 0 := by
    induction n with
    | zero =>
      have h₀ : approx c₁ c 0 = 0 + c₁ • PowerSeries.X ^ 1 := by rw [approx, _root_.zero_add]
      refine ⟨by simp [approx], by simp [approx], ?_, fun j hj ↦ ?_⟩
      · have h₁ : ((1 : ℕ) : ℕ∞) ≤ (homError F G (approx c₁ c 0)).order := by
          rw [← sub_zero (homError F G _), ← homError_zero (F := F) (G := G)]
          refine le_order_homError_sub (by simp [approx]) (map_zero _) ?_
          rw [sub_zero, Nat.cast_one]
          exact PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by simp [approx])
        refine succ_le_order_of_homogeneousComponent_eq_zero h₁ ?_
        have := homogeneousComponent_homError_add_sub (F := F) (G := G) (map_zero _)
          one_ne_zero c₁
        rw [← h₀, homError_zero, sub_zero] at this
        rw [this]
        simp
      · obtain rfl : j = 0 := by
          by_contra hj₀
          have := Nat.one_lt_pow hj₀ hp'.one_lt
          omega
        have hc₁q : c₁ ^ p ^ h = c₁ * (u / v) := by
          rw [← hc₁, ← pow_succ']
          congr 1
          omega
        rw [h₀, pow_zero, one_mul, ← one_mul (p ^ h),
          coeff_pSeriesError_add hF hG (map_zero _) one_ne_zero, pSeriesError_zero, map_zero,
          _root_.zero_add, pow_one, hc₁q]
        field_simp
        ring
    | succ n ih =>
      obtain ⟨h₀, h₁, hord, hP⟩ := ih
      obtain ⟨hord', hP'⟩ := hc n (approx c₁ c n) h₀ hord hP
      refine ⟨by simp [approx, h₀], ?_, hord', hP'⟩
      rw [approx, map_add, h₁, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
      simp
  -- the limit of the approximations is a homomorphism
  obtain ⟨f, hlim⟩ := PowerSeries.exists_forall_le_order_sub (f := approx c₁ c) fun n ↦ by
    rw [approx, add_sub_cancel_left]
    refine PowerSeries.nat_le_order _ _ fun i hi ↦ ?_
    simp [PowerSeries.coeff_X_pow, show i ≠ n + 2 by omega]
  have hcoeff {m n : ℕ} (hm : m < n) :
      PowerSeries.coeff m f = PowerSeries.coeff m (approx c₁ c n) := by
    rw [← sub_eq_zero, ← map_sub]
    exact PowerSeries.coeff_of_lt_order m ((hlim n).trans_lt' (by exact_mod_cast hm))
  have hf₀ : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff (n := 1) one_pos,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (key 1).1]
  have hΦ : homError F G f = 0 := by
    refine order_eq_top_iff.mp (top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun m _ ↦ ?_))
    have h := le_order_add ((key m).2.2.1.trans' (by exact_mod_cast (by omega : m ≤ m + 2)))
      (le_order_homError_sub (F := F) (G := G) hf₀ (key m).1 (hlim m))
    rwa [add_sub_cancel] at h
  refine ⟨⟨f, hf₀, homError_eq_zero_iff.mp hΦ⟩, ?_⟩
  rw [hcoeff (n := 2) one_lt_two, (key 2).2.1]
  exact hc₁₀

end Construction

end Field

/-- **Lazard's classification of formal group laws by height.** Over a separably closed field `K`
of characteristic `p`, two commutative formal group laws are isomorphic exactly when they have the
same height. In height `⊤` both are isomorphic to the additive formal group law. -/
theorem height_eq_height_iff_nonempty_formalGroupIso {K : Type*} [Field K] [IsSepClosed K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (F G : FormalGroup K) [F.IsComm] [G.IsComm] :
    F.height p = G.height p ↔ Nonempty (TauCeti.FormalGroupIso F G) := by
  refine ⟨fun hFG ↦ ?_, fun ⟨e⟩ ↦ e.height_eq p⟩
  cases hG : G.height p with
  | top =>
    obtain ⟨e⟩ := (height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ F).mp (hFG.trans hG)
    obtain ⟨e'⟩ := (height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ G).mp hG
    exact ⟨e.trans e'.symm⟩
  | coe h =>
    obtain ⟨f, hf⟩ := exists_formalGroupHom_coeff_one_ne_zero (hFG.trans hG) hG
    exact ⟨f.toIso (isUnit_iff_ne_zero.mpr hf)⟩

end FormalGroup
