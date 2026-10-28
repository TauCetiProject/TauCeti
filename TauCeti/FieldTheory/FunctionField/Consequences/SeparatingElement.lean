/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.Clifford
public import TauCeti.FieldTheory.FunctionField.Frobenius

/-!
# Separating elements in Riemann–Roch spaces of small degree

Let `F / k` be an algebraic function field of exponential characteristic `p`. A Riemann–Roch
space `L(D)` of small degree cannot consist of `p`-th powers alone once its dimension is large
compared with `deg D / p`. Taking `p`-th roots is injective, additive and semilinear for the
Frobenius of `k`, and the `p`-th root of a function whose poles are bounded by `D` has poles
bounded by `⌊D / p⌋`. So a `k`-subspace `V ⊆ L(D)` of `p`-th powers has dimension at most
`ℓ(⌊D / p⌋)`, and Clifford's theorem bounds this by `deg D / (2p) + 1`.

Over a perfect field the elements outside `F^p` are exactly the separating elements. For a
function field of genus `g ≥ 2` with exact constant field, applied to the Riemann–Roch space
`L(W)` of an effective canonical divisor, of dimension `g` and degree `2g - 2`, this produces a
separating element `x` with `[F : k(x)] ≤ 2g - 2`, exhibiting `F` as a separable cover of the
projective line of degree at most `2g - 2`.

The first two results make no assumption on `k`, so that they also apply to a constant field
extension `F · k' / k'` of a function field over an imperfect field `k`, with `k'` perfect, and to
the `k'`-span of a Riemann–Roch space of `F / k`. A separating element `x` of small degree is
what produces places of small degree with separable residue field: those above the rational
places of `k(x)` at which `F / k(x)` is unramified.

## Main results

* `TauCeti.Divisor.finrank_le_dim_of_forall_mem_fieldRange_frobenius`: a subspace of `L(D)`
  consisting of `p`-th powers has dimension at most `ℓ(E)` whenever `D < p (E + 1)`.
* `TauCeti.Divisor.exists_mem_notMem_fieldRange_frobenius`: if `0 ≤ deg D ≤ 2g - 2` and
  `deg D < p (2 dim V - 2)`, then a subspace `V ⊆ L(D)` contains an element which is not a
  `p`-th power.
* `TauCeti.Divisor.exists_mem_transcendental_and_isSeparable_adjoin`: over a perfect field, such
  a `V` contains a separating element.
* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_and_finrank_le`: over a
  perfect field, a function field of genus `g ≥ 2` with exact constant field has a separating
  element `x` with `[F : k(x)] ≤ 2g - 2`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.13 (Clifford's theorem) and Proposition 3.10.2 (separating elements).
* The Stacks Project, Section 55.18, [Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL),
  Theorem [0CDM](https://stacks.math.columbia.edu/tag/0CDM), whose degree bound uses a point of
  the curve over a separable extension of degree at most `2g - 2`; the separating element above
  is the function field input to that point.
-/

public section

open Module

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- **Riemann–Roch spaces of `p`-th powers.** A `k`-subspace `V ⊆ L(D)` consisting of `p`-th
powers has dimension at most `ℓ(E)` for every divisor `E` with `D < p (E + 1)`, for instance
`E = ⌊D / p⌋`. No hypothesis on the constant field `k` is needed. -/
theorem finrank_le_dim_of_forall_mem_fieldRange_frobenius (hF : IsFunctionField k F) (p : ℕ)
    [ExpChar F p] {D E : Divisor k F} (hDE : ∀ P : Place k F, D.coeff P < p * (E.coeff P + 1))
    {V : Submodule k F} (hV : V ≤ riemannRochSpace D)
    (hVp : ∀ v ∈ V, v ∈ (frobenius F p).fieldRange) :
    finrank k V ≤ dim E := by
  -- Taking `p`-th roots embeds `V` into `L(E)`, semilinearly for the Frobenius of `k`.
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  have hp : 0 < (p : ℤ) := by exact_mod_cast expChar_pos F p
  have : FiniteDimensional k (riemannRochSpace E) := finiteDimensional_riemannRochSpace hF E
  -- The `p`-th root of an element of `V`.
  let root : V → F := fun v ↦ (frobenius F p).rangeRestrictFieldEquiv.symm ⟨v, hVp v v.2⟩
  have hroot (v : V) : root v ^ p = v := by
    have h := (frobenius F p).rangeRestrictFieldEquiv_apply_symm_apply ⟨v, hVp v v.2⟩
    rwa [frobenius_def] at h
  have hrootE (v : V) : root v ∈ riemannRochSpace E := by
    rcases eq_or_ne (root v) 0 with h0 | h0
    · rw [h0]
      exact zero_mem _
    rw [mem_riemannRochSpace_iff_neg_le_ord h0]
    intro P
    -- `p · ord_P (root v) = ord_P v ≥ -D(P) > -p (E(P) + 1)`.
    have hv : (v : F) ≠ 0 := by rw [← hroot v]; exact pow_ne_zero p h0
    have hord := (mem_riemannRochSpace_iff_neg_le_ord hv).mp (hV v.2) P
    rw [← hroot v, P.ord_pow] at hord
    have := hDE P
    nlinarith
  -- Taking `p`-th roots is additive and injective.
  let j : V →+ riemannRochSpace E :=
    { toFun v := ⟨root v, hrootE v⟩
      map_zero' := by
        ext
        refine (frobenius_inj F p) ?_
        rw [ZeroMemClass.coe_zero, map_zero, frobenius_def]
        exact hroot 0
      map_add' a b := by
        ext
        refine (frobenius_inj F p) ?_
        simp only [frobenius_def, Submodule.coe_add, add_pow_expChar, hroot] }
  have hj : Function.Injective j := fun a b hab ↦ by
    have h := congrArg (fun y : riemannRochSpace E ↦ (y : F) ^ p) hab
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hroot] at h
    exact Subtype.ext h
  have hc (r : k) (v : V) : j (frobenius k p r • v) = r • j v := by
    ext
    refine (frobenius_inj F p) ?_
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, frobenius_def, SetLike.val_smul, hroot,
      Algebra.smul_def, mul_pow, map_pow]
  rw [dim_def]
  exact finrank_le_finrank_of_rank_le_rank
    (lift_rank_le_of_injective_injectiveₛ (frobenius k p) j (frobenius_inj k p) hj hc)
    (Module.rank_lt_aleph0 k _)

/-- **A Riemann–Roch space of small degree is not made of `p`-th powers.** Let `F / k` have exact
constant field and genus `g`, and let `D` be a divisor with `0 ≤ deg D ≤ 2g - 2`. A `k`-subspace
`V ⊆ L(D)` with `deg D < p (2 dim V - 2)` contains an element which is not a `p`-th power. No
hypothesis on `k` is needed. In characteristic zero, where `p = 1`, the hypotheses are
contradictory. -/
theorem exists_mem_notMem_fieldRange_frobenius (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (p : ℕ) [ExpChar F p] {D : Divisor k F}
    (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k F : ℤ) - 2) {V : Submodule k F}
    (hV : V ≤ riemannRochSpace D) (hlt : degree D < p * (2 * (finrank k V : ℤ) - 2)) :
    ∃ x ∈ V, x ∉ (frobenius F p).fieldRange := by
  -- Otherwise `dim V ≤ ℓ(⌊D / p⌋)`, and Clifford's theorem for `⌊D / p⌋`, whose degree is at
  -- most `deg D / p`, gives `p (2 dim V - 2) ≤ deg D`.
  by_contra! hVp
  have hp : 0 < (p : ℤ) := by exact_mod_cast expChar_pos F p
  -- The divisor `E = ⌊D / p⌋`.
  let E : Divisor k F := Finsupp.mapRange (· / (p : ℤ)) (Int.zero_ediv _) D
  have hE (P : Place k F) : E.coeff P = D.coeff P / p := Finsupp.mapRange_apply ..
  have hdim : finrank k V ≤ dim E :=
    finrank_le_dim_of_forall_mem_fieldRange_frobenius hF p
      (fun P ↦ by rw [hE, mul_add, mul_one]; exact Int.lt_mul_ediv_self_add hp) hV hVp
  -- `p • E ≤ D`, so `p deg E ≤ deg D`.
  have hpE : (p : ℤ) • E ≤ D := WeilDivisor.le_iff.mpr fun P ↦ by
    rw [WeilDivisor.coeff_zsmul, hE]
    exact Int.mul_ediv_self_le hp.ne'
  have hdegE : (p : ℤ) * degree E ≤ degree D := by
    simpa using degree_le_of_le hpE
  rcases lt_or_ge (degree E) 0 with hneg | hnonneg
  · -- `L(E) = 0`, so `V = 0`, against `0 ≤ deg D`.
    rw [dim_eq_zero_of_degree_neg hF hneg] at hdim
    have hV0 : finrank k V = 0 := by omega
    rw [hV0] at hlt
    push_cast at hlt
    nlinarith
  · -- Clifford's theorem for `E`.
    have hcl := two_mul_dim_le_degree_add_two hF hex hnonneg (by nlinarith)
    have : 2 * (finrank k V : ℤ) - 2 ≤ degree E := by
      have : (finrank k V : ℤ) ≤ dim E := by exact_mod_cast hdim
      omega
    nlinarith

/-- **A separating element in a Riemann–Roch space of small degree.** Over a perfect field `k`,
let `F / k` have exact constant field and genus `g`, and let `D` be a divisor with
`0 ≤ deg D ≤ 2g - 2`. A `k`-subspace `V ⊆ L(D)` with `deg D < p (2 dim V - 2)` contains a
separating element: an `x` transcendental over `k` with `F / k(x)` separable. -/
theorem exists_mem_transcendental_and_isSeparable_adjoin [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (p : ℕ) [ExpChar F p]
    {D : Divisor k F} (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k F : ℤ) - 2)
    {V : Submodule k F} (hV : V ≤ riemannRochSpace D)
    (hlt : degree D < p * (2 * (finrank k V : ℤ) - 2)) :
    ∃ x ∈ V, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  obtain ⟨x, hxV, hx⟩ := exists_mem_notMem_fieldRange_frobenius hF hex p hD₀ hDg hV hlt
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx ⟨x, by rw [frobenius_def, pow_one]⟩).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    exact ⟨x, hxV, hF.transcendental_and_isSeparable_adjoin_of_notMem_fieldRange_frobenius p hx⟩

end Divisor

namespace IsFunctionField

/-- **A separating element of degree at most `2g - 2`.** Over a perfect field `k`, a function
field `F / k` of genus `g ≥ 2` with exact constant field has a separating element `x`, that is
transcendental over `k` with `F / k(x)` separable, of degree `[F : k(x)] ≤ 2g - 2`. -/
theorem exists_transcendental_and_isSeparable_adjoin_and_finrank_le [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F ∧
      finrank k⟮x⟯ F ≤ 2 * genus k F - 2 := by
  -- An effective canonical divisor `W'`.
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  obtain ⟨W', hW'eff, hlin⟩ := (riemannRochSpace_ne_bot_iff hF).mp
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF W).mp (by rw [hW.dim_eq hF hex]; omega))
  have hRR : W'.IsRiemannRochDivisor (genus k F) := hW.of_linearlyEquivalent hF hlin
  have hdimW' : Divisor.dim W' = genus k F := hRR.dim_eq hF hex
  have hdegW' : Divisor.degree W' = 2 * (genus k F : ℤ) - 2 := hRR.degree_eq hF hex
  -- A separating element of `L(W')`.
  obtain ⟨x, hxW', hxt, hxs⟩ : ∃ x ∈ riemannRochSpace W', Transcendental k x ∧
      Algebra.IsSeparable k⟮x⟯ F := by
    obtain ⟨p, hp⟩ := ExpChar.exists F
    cases hp with
    | zero =>
      -- In characteristic zero every transcendental `x ∈ L(W')` is separating.
      obtain ⟨x, hxW', hx⟩ :=
        Divisor.exists_mem_riemannRochSpace_transcendental hF hex (D := W') (by omega)
      have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
      exact ⟨x, hxW', hx, inferInstance⟩
    | prime hp =>
      have : ExpChar F p := .prime hp
      refine Divisor.exists_mem_transcendental_and_isSeparable_adjoin hF hex p
        (hdegW' ▸ by omega) hdegW'.le le_rfl ?_
      rw [hdegW', ← Divisor.dim_def, hdimW']
      have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      have : (2 : ℤ) ≤ genus k F := by exact_mod_cast hg
      nlinarith
  -- Its pole divisor lies below `W'`, so `[F : k(x)] = deg (x)_∞ ≤ deg W' = 2g - 2`.
  have hx0 : x ≠ 0 := hxt.ne_zero
  have hdeg := Divisor.degree_le_of_le ((poles_le_iff_mem_riemannRochSpace hF
    (WeilDivisor.isEffective_iff_zero_le.mpr hW'eff) (Units.mk0 x hx0)).mpr hxW')
  rw [Divisor.degree_poles hF (Units.mk0 x hx0) hxt, Units.val_mk0, hdegW'] at hdeg
  refine ⟨x, hxt, hxs, ?_⟩
  omega

end IsFunctionField

end TauCeti
