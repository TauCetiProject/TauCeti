/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
import TauCeti.RingTheory.FormalGroup.AddInv
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.CharTwo
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The logarithm of a formal group law of exponent two

Let `F` be a commutative formal group law over a commutative ring `R` with `[2]_F(X) = F(X, X) = 0`.
Then `2 = 0` in `R`, since `2` is the linear coefficient of `[2]_F`, so no logarithm in the sense of
`FormalGroup.log` is available. Nevertheless `F` is strictly isomorphic to the additive formal group
law, and there is a canonical choice of isomorphism: there is a unique power series

  `g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{2ᵏ} = 0` for every `k ≥ 1`

such that `g(F(X, Y)) = g(X) + g(Y)`. Formal group laws with `[2]_F = 0` arise in Quillen's
description of unoriented bordism. No coefficient field and no further hypothesis on `R` is used: it
may have nilpotents or be the zero ring.

The power series `g` is constructed degree by degree. If `g` is additive along `F` up to degree
`n`, the degree-`n` part of the error `g(F(X, Y)) - g(X) - g(Y)` is a homogeneous symmetric
additive 2-cocycle, by associativity and commutativity of `F`, and it vanishes on the diagonal,
because `F(X, X) = 0` and `2 = 0`. By the classification of such cocycles over rings with `2 = 0`
(`TauCeti.existsUnique_eq_smul_add_pow_sub_pow_sub_pow_of_two_eq_zero` and
`TauCeti.eq_zero_of_two_eq_zero_of_aeval_X_X_eq_zero`), it is `c ((X + Y)ⁿ - Xⁿ - Yⁿ)` when `n` is
not a power of two, and it is zero when `n` is a power of two. Replacing `g` by `g - c Xⁿ` in the
first case, and keeping `g` in the second, makes `g` additive up to degree `n + 1` without changing
its coefficients in lower degrees, nor its coefficients in degrees `2ᵏ`. The power series
`g` is the limit of these approximations. The same comparison of lowest-degree terms shows that
two normalised additive series agree.

The lowest-degree part of a substitution is computed by
`MvPowerSeries.homogeneousComponent_subst_of_le_order`.

## Main results

* `FormalGroup.existsUnique_logarithm_of_nsmulSeries_two_eq_zero`: for a commutative formal group
  law `F` with `[2]_F = 0` there is a unique power series `g = X + ⋯` without terms of degree `2ᵏ`,
  `k ≥ 1`, such that `g(F(X, Y)) = g(X) + g(Y)`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

section AddError

/-- The failure `g(F(X, Y)) - g(X) - g(Y)` of `g` to be additive along `F`. -/
private noncomputable def addError (g : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst F.toPowerSeries g - PowerSeries.subst (X 0) g - PowerSeries.subst (X 1) g

private theorem addError_sub (g h : PowerSeries R) :
    addError F (g - h) = addError F g - addError F h := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  simp only [addError, PowerSeries.subst_sub hF, PowerSeries.subst_sub (PowerSeries.HasSubst.X _)]
  ring

private theorem addError_eq_zero_iff {g : PowerSeries R} :
    addError F g = 0 ↔
      PowerSeries.subst F.toPowerSeries g = PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g :=
  by rw [addError, sub_sub, sub_eq_zero]

/-- The additivity defect of `g` vanishes to the order of `g`. -/
private theorem le_order_addError {g : PowerSeries R} {n : ℕ} (hg : n ≤ g.order) :
    (n : ℕ∞) ≤ (addError F g).order := by
  have h {x : MvPowerSeries (Fin 2) R} (hx : constantCoeff x = 0) :
      (n : ℕ∞) ≤ (PowerSeries.subst x g).order :=
    hg.trans (PowerSeries.le_order_subst_left hx)
  have hsub {a b : MvPowerSeries (Fin 2) R} (ha : (n : ℕ∞) ≤ a.order) (hb : (n : ℕ∞) ≤ b.order) :
      (n : ℕ∞) ≤ (a - b).order := by
    rw [sub_eq_add_neg]
    exact (le_min ha (by rwa [order_neg])).trans min_order_le_add
  exact hsub (hsub (h F.zero_constantCoeff) (h (constantCoeff_X 0))) (h (constantCoeff_X 1))

/-- The lowest-degree part of the additivity defect of `c Xⁿ` is `c ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
private theorem homogeneousComponent_addError_smul_X_pow (c : R) (n : ℕ) :
    homogeneousComponent n (addError F (c • PowerSeries.X ^ n)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  -- the degree-`n` part of `xⁿ` is the `n`-th power of the linear part of `x`
  have hpow {x : MvPowerSeries (Fin 2) R} (hx : constantCoeff x = 0) :
      homogeneousComponent n (x ^ n) = homogeneousComponent 1 x ^ n := by
    simpa using homogeneousComponent_pow_of_le_order (p := 1)
      (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hx) n
  simp only [addError, PowerSeries.subst_smul hF, PowerSeries.subst_smul (hX _),
    PowerSeries.subst_pow hF, PowerSeries.subst_pow (hX _), PowerSeries.subst_X hF,
    PowerSeries.subst_X (hX _), map_sub, map_smul, hpow F.zero_constantCoeff,
    hpow (constantCoeff_X _), homogeneousComponent_one_X,
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y]
  rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_mul, map_sub, map_pow, map_add, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, MvPolynomial.coe_C, MvPowerSeries.smul_eq_C_mul, mul_sub]

/-- The additivity defect of `g` at substitutable `x, y` is `g(F(x, y)) - g(x) - g(y)`. -/
private theorem subst_addError {σ : Type*} {x y : MvPowerSeries σ R}
    (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) (g : PowerSeries R) :
    (addError F g).subst ![x, y] = PowerSeries.subst (F.toPowerSeries.subst ![x, y]) g -
      PowerSeries.subst x g - PowerSeries.subst y g := by
  have hxy := hasSubst_finTwo hx hy
  rw [addError, subst_sub hxy, subst_sub hxy,
    subst_powerSeriesSubst hxy (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_powerSeriesSubst hxy (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst hxy (PowerSeries.HasSubst.X _), subst_X hxy, subst_X hxy]
  simp

/-- **The additivity defect is a 2-cocycle**:
`Φ(X, Y) + Φ(F(X, Y), Z) = Φ(X, F(Y, Z)) + Φ(Y, Z)`, by associativity of `F`. -/
private theorem addError_cocycle (g : PowerSeries R) :
    (addError F g).subst ![X 0, X 1] +
        (addError F g).subst ![F.toPowerSeries.subst ![X 0, X 1], (X 2 : MvPowerSeries (Fin 3) R)] =
      (addError F g).subst ![X 0, F.toPowerSeries.subst ![X 1, X 2]] +
        (addError F g).subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2] := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  rw [subst_addError F (hX 0) (hX 1), subst_addError F (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2),
    subst_addError F (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)), subst_addError F (hX 1) (hX 2),
    F.assoc' (hX 0) (hX 1) (hX 2)]
  ring

/-- **The additivity defect is symmetric** when `F` is commutative. -/
private theorem subst_addError_X_one_X_zero [F.IsComm] (g : PowerSeries R) :
    (addError F g).subst ![X 1, X 0] = addError F g := by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  rw [subst_addError F (hX 1) (hX 0), F.comm' (hX 1) (hX 0), finTwo_X_eq_X, subst_self, id,
    addError]
  ring

/-- **The additivity defect vanishes on the diagonal** when `[2]_F = 0`: `F(X, X) = 0` and
`g(X) + g(X) = 0`. -/
private theorem subst_addError_X_X (hF : F.nsmulSeries 2 = 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) :
    (addError F g).subst ![(PowerSeries.X : PowerSeries R), PowerSeries.X] = 0 := by
  have hX := PowerSeries.HasSubst.X' (R := R)
  have hFX : F.toPowerSeries.subst ![(PowerSeries.X : PowerSeries R), PowerSeries.X] = 0 := by
    rw [← hF, nsmulSeries_succ, nsmulSeries_one]
  have h2 : (2 : R) = 0 := by exact_mod_cast F.natCast_eq_zero_of_nsmulSeries_eq_zero hF
  have hgg : g + g = 0 := by
    rw [← two_smul R g, h2, zero_smul]
  rw [subst_addError F hX hX, hFX, PowerSeries.subst_zero_of_constantCoeff_zero hg,
    PowerSeries.X_subst]
  linear_combination -hgg

end AddError

section Leading

/-- The degree-`n` part of the additivity defect of `g`, as a polynomial. -/
private noncomputable def leadingError (n : ℕ) (g : PowerSeries R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.homogeneousComponent n (truncTotal (n + 1) (addError F g))

private theorem coe_leadingError (n : ℕ) (g : PowerSeries R) :
    (leadingError F n g : MvPowerSeries (Fin 2) R) = homogeneousComponent n (addError F g) := by
  ext d
  rw [MvPolynomial.coeff_coe, leadingError, MvPolynomial.coeff_homogeneousComponent,
    coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_truncTotal _ (by omega)
  · rfl

/-- If the additivity defect of `g` vanishes below degree `n`, its degree-`n` part at a family `x`
of series without constant term is the polynomial `leadingError F n g` evaluated at the linear
parts of `x`. -/
private theorem homogeneousComponent_subst_addError {τ : Type*} {n : ℕ} {g : PowerSeries R}
    (hn : n ≤ (addError F g).order) {x : Fin 2 → MvPowerSeries τ R} (hx : HasSubst x)
    (hx₀ : ∀ i, constantCoeff (x i) = 0) {l : Fin 2 → MvPolynomial τ R}
    (hl : ∀ i, homogeneousComponent 1 (x i) = l i) :
    homogeneousComponent n ((addError F g).subst x) =
      (MvPolynomial.aeval l (leadingError F n g) : MvPowerSeries τ R) := by
  rw [homogeneousComponent_subst_of_le_order hn hx hx₀, ← coe_leadingError, subst_coe]
  simp_rw [hl]
  simpa using (MvPolynomial.comp_aeval_apply (MvPolynomial.coeToMvPowerSeries.algHom R)
    (leadingError F n g) (f := l)).symm

/-- The linear part of `F(x, y)` is the sum of the linear parts of `x` and `y`. -/
private theorem homogeneousComponent_one_subst_pair {τ : Type*} {x y : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    homogeneousComponent 1 (F.toPowerSeries.subst ![x, y]) =
      homogeneousComponent 1 x + homogeneousComponent 1 y := by
  have hc (z : MvPowerSeries τ R) : constantCoeff (homogeneousComponent 1 z) = 0 := by
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_homogeneousComponent]
  have hl : HasSubst ![homogeneousComponent 1 x, homogeneousComponent 1 y] :=
    hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> simp [hc]
  have hfun : (fun i ↦ homogeneousComponent 1 (![x, y] i)) =
      ![homogeneousComponent 1 x, homogeneousComponent 1 y] := by
    funext i
    fin_cases i <;> rfl
  rw [homogeneousComponent_subst_of_le_order
      (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr F.zero_constantCoeff)
      (hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> simp [hx, hy])
      (fun i ↦ by fin_cases i <;> simp [hx, hy]), hfun,
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y, subst_add hl, subst_X hl,
    subst_X hl]
  simp

variable {F}

/-- The degree-`n` part of the additivity defect is an additive 2-cocycle. -/
private theorem isAddCocycle₂_leadingError {n : ℕ} {g : PowerSeries R}
    (hn : n ≤ (addError F g).order) : (leadingError F n g).IsAddCocycle₂ := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hF₀ (i j : Fin 3) :
      constantCoeff (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo (hX i) (hX j))
      (fun s ↦ by fin_cases s <;> simp) F.toPowerSeries, F.zero_constantCoeff, map_zero]
  have h := congrArg (homogeneousComponent n) (addError_cocycle F g)
  rw [map_add, map_add,
    homogeneousComponent_subst_addError F hn (hasSubst_finTwo (hX 0) (hX 1))
      (l := ![MvPolynomial.X 0, MvPolynomial.X 1]) (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]),
    homogeneousComponent_subst_addError F hn
      (hasSubst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2))
      (l := ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 2])
      (fun i ↦ by fin_cases i <;> simp [hF₀])
      (fun i ↦ by
        fin_cases i <;>
          simp [homogeneousComponent_one_subst_pair F (hX₀ 0) (hX₀ 1), homogeneousComponent_one_X]),
    homogeneousComponent_subst_addError F hn
      (hasSubst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)))
      (l := ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 2])
      (fun i ↦ by fin_cases i <;> simp [hF₀])
      (fun i ↦ by
        fin_cases i <;>
          simp [homogeneousComponent_one_subst_pair F (hX₀ 1) (hX₀ 2), homogeneousComponent_one_X]),
    homogeneousComponent_subst_addError F hn (hasSubst_finTwo (hX 1) (hX 2))
      (l := ![MvPolynomial.X 1, MvPolynomial.X 2]) (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X])] at h
  rw [MvPolynomial.isAddCocycle₂_iff]
  exact MvPolynomial.coe_inj.mp (by rw [MvPolynomial.coe_add, MvPolynomial.coe_add]; exact h)

/-- The degree-`n` part of the additivity defect is symmetric when `F` is commutative. -/
private theorem isSymmetric_leadingError [F.IsComm] {n : ℕ} {g : PowerSeries R}
    (hn : n ≤ (addError F g).order) : (leadingError F n g).IsSymmetric := by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have h : MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 0] (leadingError F n g) =
      leadingError F n g := by
    refine MvPolynomial.coe_inj.mp ?_
    rw [← homogeneousComponent_subst_addError F hn (hasSubst_finTwo (hX 1) (hX 0))
      (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]),
      subst_addError_X_one_X_zero, coe_leadingError]
  intro e
  rcases (by decide : ∀ e : Equiv.Perm (Fin 2), e = 1 ∨ e = Equiv.swap 0 1) e with rfl | rfl
  · simp
  · rw [MvPolynomial.rename_eq_aeval]
    convert h using 3
    funext i
    fin_cases i <;> rfl

/-- The degree-`n` part of the additivity defect vanishes on the diagonal when `[2]_F = 0`. -/
private theorem aeval_X_X_leadingError (hF : F.nsmulSeries 2 = 0) {n : ℕ} {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (addError F g).order) :
    MvPolynomial.aeval ![(Polynomial.X : Polynomial R), Polynomial.X] (leadingError F n g) = 0 := by
  have hX := PowerSeries.HasSubst.X' (R := R)
  have h : MvPolynomial.aeval ![(MvPolynomial.X () : MvPolynomial Unit R), MvPolynomial.X ()]
      (leadingError F n g) = 0 := by
    refine MvPolynomial.coe_inj.mp ?_
    -- `PowerSeries.X` is by definition the variable `X ()`
    rw [← homogeneousComponent_subst_addError F hn (hasSubst_finTwo hX hX)
      (fun i ↦ by fin_cases i <;> exact constantCoeff_X ())
      (fun i ↦ by
        fin_cases i <;>
          exact (homogeneousComponent_one_X (R := R) ()).trans (MvPolynomial.coe_X _).symm),
      subst_addError_X_X F hF hg, map_zero, MvPolynomial.coe_zero]
  have h' := congrArg (MvPolynomial.uniqueAlgEquiv R Unit) h
  rw [map_zero, ← AlgEquiv.coe_toAlgHom, MvPolynomial.comp_aeval_apply] at h'
  convert h' using 3
  funext i
  fin_cases i <;> simp

variable (F)

/-- **The inductive step.** If the additivity defect of `g` vanishes below degree `n ≥ 1`,
subtracting a suitable multiple `c Xⁿ` makes it vanish below degree `n + 1`, and `c = 0` when `n` is
a power of two. -/
private theorem exists_le_order_addError_sub_smul_X_pow [F.IsComm] (hF : F.nsmulSeries 2 = 0)
    {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hn : n ≤ (addError F g).order) :
    ∃ c : R, ((n + 1 : ℕ) : ℕ∞) ≤ (addError F (g - c • PowerSeries.X ^ n)).order ∧
      ∀ k, n = 2 ^ k → c = 0 := by
  have h2 : (2 : R) = 0 := by exact_mod_cast F.natCast_eq_zero_of_nsmulSeries_eq_zero hF
  have hh := MvPolynomial.homogeneousComponent_isHomogeneous n (truncTotal (n + 1) (addError F g))
  by_cases hpow : ∃ k, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hP := TauCeti.eq_zero_of_two_eq_zero_of_aeval_X_X_eq_zero h2 hh
      (isSymmetric_leadingError hn) (isAddCocycle₂_leadingError hn)
      (aeval_X_X_leadingError hF hg hn)
    refine ⟨0, ?_, fun _ _ ↦ rfl⟩
    rw [zero_smul, sub_zero]
    refine succ_le_order_of_homogeneousComponent_eq_zero hn ?_
    rw [← coe_leadingError, leadingError, hP, MvPolynomial.coe_zero]
  · simp only [not_exists] at hpow
    obtain ⟨c, hc, -⟩ := TauCeti.existsUnique_eq_smul_add_pow_sub_pow_sub_pow_of_two_eq_zero h2
      hn₀ hpow hh (isSymmetric_leadingError hn) (isAddCocycle₂_leadingError hn)
    refine ⟨c, ?_, fun k hk ↦ (hpow k hk).elim⟩
    have hXn : (n : ℕ∞) ≤ (c • PowerSeries.X ^ n : PowerSeries R).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
    have hn' : (n : ℕ∞) ≤ (addError F (g - c • PowerSeries.X ^ n)).order := by
      rw [addError_sub, sub_eq_add_neg]
      exact (le_min hn (by rw [order_neg]; exact le_order_addError F hXn)).trans
        min_order_le_add
    refine succ_le_order_of_homogeneousComponent_eq_zero hn' ?_
    rw [addError_sub, map_sub, homogeneousComponent_addError_smul_X_pow, ← coe_leadingError,
      leadingError, hc, sub_self]

end Leading

section Construction

/-- The approximations to the logarithm: starting from `X`, step `n` subtracts the multiple
`c (n + 2) g • X ^ (n + 2)` of the current approximation `g`. -/
private noncomputable def approx (c : ℕ → PowerSeries R → R) : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | n + 1 => approx c n - c (n + 2) (approx c n) • PowerSeries.X ^ (n + 2)

/-- The approximations stabilise: `approx c n` and `approx c n'` agree below degree
`min n n' + 2`. -/
private theorem coeff_approx_eq_coeff_approx (c : ℕ → PowerSeries R → R) {m n n' : ℕ}
    (hm : m < n + 2) (hm' : m < n' + 2) :
    PowerSeries.coeff m (approx c n) = PowerSeries.coeff m (approx c n') := by
  wlog h : n ≤ n' generalizing n n'
  · exact (this hm' hm (by omega)).symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ih (by omega) (by omega), ← add_assoc, approx, map_sub, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow]
    simp [show m ≠ n + j + 2 by omega]

/-- The limit of the approximations. -/
private noncomputable def approxLimit (c : ℕ → PowerSeries R → R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m (approx c m)

/-- The limit agrees with `approx c n` below degree `n + 2`. -/
private theorem coeff_approxLimit (c : ℕ → PowerSeries R → R) {m n : ℕ} (hm : m < n + 2) :
    PowerSeries.coeff m (approxLimit c) = PowerSeries.coeff m (approx c n) := by
  rw [approxLimit, PowerSeries.coeff_mk]
  exact coeff_approx_eq_coeff_approx c (by omega) hm

/-- **Existence of the normalised logarithm**, by passing to the limit of the approximations. -/
private theorem exists_logarithm [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0) ∧ addError F g = 0 := by
  choose! c hc using fun (n : ℕ) (g : PowerSeries R) (hn₀ : n ≠ 0)
    (hg : PowerSeries.constantCoeff g = 0) (hn : (n : ℕ∞) ≤ (addError F g).order) ↦
    exists_le_order_addError_sub_smul_X_pow F hF hn₀ hg hn
  -- `approx c n` is normalised and additive along `F` below degree `n + 2`
  have key (n : ℕ) : PowerSeries.constantCoeff (approx c n) = 0 ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ (addError F (approx c n)).order ∧
      ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) (approx c n) = 0 := by
    induction n with
    | zero =>
      have hF' := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
      refine ⟨PowerSeries.constantCoeff_X, ?_, fun k hk ↦ ?_⟩
      · rw [approx, addError, PowerSeries.subst_X hF',
          PowerSeries.subst_X (PowerSeries.HasSubst.X _),
          PowerSeries.subst_X (PowerSeries.HasSubst.X _), sub_sub]
        exact two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
      · simp [approx, PowerSeries.coeff_X, hk.ne']
    | succ n ih =>
      obtain ⟨h₀, hord, hpow⟩ := ih
      obtain ⟨hord', hc₀⟩ := hc (n + 2) (approx c n) (by omega) h₀ hord
      refine ⟨by simp [approx, h₀], hord', fun k hk ↦ ?_⟩
      rw [approx, map_sub, hpow k hk, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
      split_ifs with h
      · simp [hc₀ k h.symm]
      · simp
  refine ⟨approxLimit c, ?_, ?_, fun k hk ↦ ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_approxLimit c (n := 0) (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (key 0).1]
  · rw [coeff_approxLimit c (n := 0) (by omega)]
    simp [approx]
  · rw [coeff_approxLimit c (n := 2 ^ k) (by omega), (key _).2.2 k hk]
  · -- the additivity defect of the limit vanishes below every degree
    refine order_eq_top_iff.mp (top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun m _ ↦ ?_))
    have hlim : ((m + 2 : ℕ) : ℕ∞) ≤ (approxLimit c - approx c m).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ by rw [map_sub, coeff_approxLimit c hi, sub_self]
    have hdiff := le_order_addError F hlim
    rw [addError_sub] at hdiff
    calc (m : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : m ≤ m + 2)
      _ ≤ min (addError F (approx c m)).order
          (addError F (approxLimit c) - addError F (approx c m)).order := le_min (key m).2.1 hdiff
      _ ≤ (addError F (approx c m) +
          (addError F (approxLimit c) - addError F (approx c m))).order := min_order_le_add
      _ = (addError F (approxLimit c)).order := by rw [add_sub_cancel]

/-- **Uniqueness of the normalised logarithm.** The lowest-degree term `c Xⁿ` of the difference of
two normalised additive series contributes `c ((X + Y)ⁿ - Xⁿ - Yⁿ) = 0` to the additivity defect,
which forces `c = 0` unless `n` is a power of two, where the normalisation does. -/
private theorem eq_of_logarithm (hF : F.nsmulSeries 2 = 0) {g g' : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0) ∧ addError F g = 0)
    (hg' : PowerSeries.constantCoeff g' = 0 ∧ PowerSeries.coeff 1 g' = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g' = 0) ∧ addError F g' = 0) :
    g = g' := by
  obtain ⟨h₀, h₁, hp, ha⟩ := hg
  obtain ⟨h₀', h₁', hp', ha'⟩ := hg'
  suffices h : ∀ n, PowerSeries.coeff n (g - g') = 0 by
    rw [← sub_eq_zero]
    ext n
    simpa using h n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  set c := PowerSeries.coeff n (g - g')
  have hD : ((n + 1 : ℕ) : ℕ∞) ≤ (g - g' - c • PowerSeries.X ^ n).order :=
    PowerSeries.nat_le_order _ _ fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · simp [ih i hi, PowerSeries.coeff_X_pow, hi.ne]
      · simp [c]
  -- the degree-`n` part of the additivity defect of `c Xⁿ` is `c ((X + Y)ⁿ - Xⁿ - Yⁿ)`, while
  -- that of `g - g'` vanishes
  have hc : c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
      MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) = 0 := by
    refine MvPolynomial.coe_inj.mp ?_
    rw [MvPolynomial.coe_zero, ← homogeneousComponent_addError_smul_X_pow F c n]
    have h := homogeneousComponent_of_lt_order_eq_zero
      ((Nat.cast_lt.mpr n.lt_succ_self).trans_le (le_order_addError F hD))
    rwa [addError_sub, addError_sub, ha, ha', sub_zero, zero_sub, map_neg, neg_eq_zero] at h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [c, h₀, h₀']
  by_cases hpow : ∃ k, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [c, h₁, h₁']
    · simp [c, hp k hk, hp' k hk]
  · simp only [not_exists] at hpow
    obtain ⟨r, -, hr⟩ := TauCeti.existsUnique_eq_smul_add_pow_sub_pow_sub_pow_of_two_eq_zero
      (by exact_mod_cast F.natCast_eq_zero_of_nsmulSeries_eq_zero hF) hn.ne' hpow
      (MvPolynomial.isHomogeneous_zero _ _ _) MvPolynomial.IsSymmetric.zero
      MvPolynomial.IsAddCocycle₂.zero
    exact (hr c hc.symm).trans (hr 0 (by simp)).symm

end Construction

/-- **The normalised logarithm of a formal group law of exponent two** (Quillen). Let `F` be a
commutative formal group law over a commutative ring `R` with `[2]_F = 0`. There is a unique power
series `g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{2ᵏ} = 0` for every `k ≥ 1` such that
`g(F(X, Y)) = g(X) + g(Y)`. -/
theorem existsUnique_logarithm_of_nsmulSeries_two_eq_zero [F.IsComm] (hF : F.nsmulSeries 2 = 0) :
    ∃! g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0) ∧
      PowerSeries.subst F.toPowerSeries g =
        PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g := by
  simp only [← addError_eq_zero_iff]
  obtain ⟨g, hg⟩ := exists_logarithm F hF
  exact ⟨g, hg, fun g' hg' ↦ eq_of_logarithm F hF hg' hg⟩

end FormalGroup
