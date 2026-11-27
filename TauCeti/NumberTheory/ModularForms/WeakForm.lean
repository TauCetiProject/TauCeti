/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel
public import TauCeti.NumberTheory.ModularForms.MulDiscriminant
public import TauCeti.NumberTheory.ModularForms.QExpansion.Growth

/-!
# Weak forms on subgroups of `SL₂(ℤ)`

A **weak form** of integral weight `k` on a subgroup `Γ ≤ SL₂(ℤ)` (`TauCeti.IsWeakForm Γ k f`) is
a holomorphic function `f` on the upper half-plane with `f ∣[k] γ = f` for every `γ ∈ Γ`, such that
for every `g ∈ SL₂(ℤ)` the translate `f ∣[k] g` grows at most exponentially,
`O(exp (C · Im τ))` for some real `C`, as `Im τ → ∞`. Unlike a modular form, a weak form may have
poles at the cusps, but it has no poles in the upper half-plane. A weak form of weight `0` is a
weakly holomorphic modular function. These are the objects of the unbounded denominators theorem of
Calegari, Dimitrov and Tang, which concerns arbitrary finite-index subgroups `Γ`, congruence or
not.

For finite-index `Γ`, the growth condition is the familiar condition that each cusp germ is
meromorphic: every `f ∣[k] g` is periodic with period the strict level of `Γ`
(`TauCeti.periodic_slash_comp_ofComplex`), and a weak form is a holomorphic `Γ`-invariant
function such that for every `g` the cusp function of `f ∣[k] g` in `exp (2 π i τ / h)`, for some
period `h ≥ 1`, is meromorphic at `0` (`TauCeti.isWeakForm_iff_meromorphicAt_cuspFunction`). So
its Laurent expansion at every cusp has finite principal part.

Weak forms are stable under restriction to a subgroup, sums, scalar multiples, products (adding
the weights) and powers, and slashing by `g ∈ SL₂(ℤ)` takes a weak form on `Γ` to one on
`g⁻¹ Γ g`. For finite-index `Γ` the modular forms are exactly the weak forms bounded at every cusp
(`TauCeti.exists_modularForm_coe_eq_iff`). The inverse `Δ⁻¹` of the discriminant is a weak form of
weight `-12` on `SL₂(ℤ)` that is unbounded at `i∞`, hence not a modular form. In odd weight a weak
form on a subgroup containing `-1` vanishes.

Conversely, the poles of a weak form at the cusps can be cleared with a power of `Δ`: on a
finite-index `Γ`, `f` is a weak form of weight `k` exactly when `f Δᵐ` is a modular form of weight
`k + 12 m` for some `m` (`TauCeti.isWeakForm_iff_exists_modularForm_coe_eq_mul_discriminant_pow`),
and then every sufficiently large `m` works. Since `Δ` vanishes nowhere on `ℍ`, `f` is recovered as
`f Δᵐ · Δ⁻ᵐ`. The exponent is uniform over the cusps because the growth rates of a weak form at the
cusps are bounded by a single constant (`TauCeti.IsWeakForm.exists_forall_isBigO_exp`): the
translate `f ∣[k] g` depends only on the coset `Γ g`, of which there are finitely many. No
hypothesis on `-1 ∈ Γ` or on the regularity of the cusps is needed.

## Main declarations

* `TauCeti.IsWeakForm`: the predicate.
* `TauCeti.IsWeakForm.mono`, `TauCeti.IsWeakForm.add`, `TauCeti.IsWeakForm.smul`,
  `TauCeti.IsWeakForm.mul`, `TauCeti.IsWeakForm.pow`: closure properties.
* `TauCeti.IsWeakForm.slash`: slashing by `g` gives a weak form on the conjugate `g⁻¹ Γ g`.
* `ModularFormClass.isWeakForm`, `TauCeti.exists_modularForm_coe_eq_iff`: modular forms are the
  weak forms bounded at every cusp.
* `TauCeti.IsWeakForm.meromorphicAt_cuspFunction_slash`,
  `TauCeti.isWeakForm_iff_meromorphicAt_cuspFunction`: weak forms are the holomorphic invariant
  functions with meromorphic cusp germs.
* `TauCeti.IsWeakForm.eq_zero_of_neg_one_mem`: in odd weight, a weak form on a subgroup containing
  `-1` vanishes.
* `TauCeti.isWeakForm_inv_discriminant`, `TauCeti.not_exists_modularForm_coe_eq_inv_discriminant`:
  `Δ⁻¹` is a weak form and not a modular form.
* `TauCeti.IsWeakForm.exists_forall_isBigO_exp`: on a finite-index subgroup, one exponential
  growth rate bounds a weak form at every cusp.
* `TauCeti.IsWeakForm.eventually_exists_modularForm_coe_eq_mul_discriminant_pow`,
  `TauCeti.isWeakForm_iff_exists_modularForm_coe_eq_mul_discriminant_pow`: multiplying by a
  power of `Δ` clears the poles of a weak form at the cusps, and the weak forms are exactly the
  quotients of modular forms by powers of `Δ`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math.
  Soc. 38 (2025), 627–702, Theorem 1.0.1, Lemma 4.2.2, Definition 7.4.3 and Lemma 7.4.4.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.2 and §2.4.
-/

public section

open UpperHalfPlane ModularForm Filter Asymptotics Function Matrix.SpecialLinearGroup
open scoped Manifold MatrixGroups Pointwise

namespace TauCeti

variable {Γ Γ' : Subgroup SL(2, ℤ)} {k l : ℤ} {f f' : ℍ → ℂ}

/-- A **weak form** of weight `k` on a subgroup `Γ` of `SL₂(ℤ)`: a holomorphic function on the
upper half-plane, invariant under the weight-`k` slash action of `Γ`, such that its slash by every
`g ∈ SL₂(ℤ)` grows at most exponentially, `O(exp (C · Im τ))` for some real `C`, as
`Im τ → ∞`. For finite-index `Γ` this says that every cusp germ is meromorphic
(`TauCeti.isWeakForm_iff_meromorphicAt_cuspFunction`); poles at the cusps are allowed, poles in
the upper half-plane are not. -/
structure IsWeakForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop where
  /-- A weak form is holomorphic on the upper half-plane. -/
  mdifferentiable : MDiff f
  /-- A weak form is invariant under the weight-`k` slash action of `Γ`. -/
  slash_eq : ∀ γ ∈ Γ, f ∣[k] γ = f
  /-- A weak form grows at most exponentially at every cusp. -/
  exists_isBigO_exp : ∀ g : SL(2, ℤ), ∃ C : ℝ,
    (f ∣[k] g) =O[atImInfty] fun τ ↦ Real.exp (C * τ.im)

/-! ### Closure properties -/

namespace IsWeakForm

/-- A weak form on `Γ` is a weak form on every subgroup of `Γ`, in the same weight. -/
theorem mono (hf : IsWeakForm Γ k f) (h : Γ' ≤ Γ) : IsWeakForm Γ' k f :=
  ⟨hf.mdifferentiable, fun γ hγ ↦ hf.slash_eq γ (h hγ), hf.exists_isBigO_exp⟩

/-- The sum of two weak forms of the same weight is a weak form. -/
theorem add (hf : IsWeakForm Γ k f) (hf' : IsWeakForm Γ k f') : IsWeakForm Γ k (f + f') where
  mdifferentiable := hf.mdifferentiable.add hf'.mdifferentiable
  slash_eq γ hγ := by rw [SlashAction.add_slash, hf.slash_eq γ hγ, hf'.slash_eq γ hγ]
  exists_isBigO_exp g := by
    obtain ⟨C, hC⟩ := hf.exists_isBigO_exp g
    obtain ⟨C', hC'⟩ := hf'.exists_isBigO_exp g
    refine ⟨max C C', ?_⟩
    rw [SlashAction.add_slash]
    exact (UpperHalfPlane.isBigO_exp_mul_im_of_le (le_max_left C C') hC).add
      (UpperHalfPlane.isBigO_exp_mul_im_of_le (le_max_right C C') hC')

/-- A scalar multiple of a weak form is a weak form. -/
theorem smul (hf : IsWeakForm Γ k f) (c : ℂ) : IsWeakForm Γ k (c • f) where
  mdifferentiable := hf.mdifferentiable.const_smul c
  slash_eq γ hγ := by rw [SL_smul_slash, hf.slash_eq γ hγ]
  exists_isBigO_exp g := by
    obtain ⟨C, hC⟩ := hf.exists_isBigO_exp g
    exact ⟨C, by rw [SL_smul_slash]; exact hC.const_smul_left c⟩

/-- The negative of a weak form is a weak form. -/
theorem neg (hf : IsWeakForm Γ k f) : IsWeakForm Γ k (-f) := by
  simpa using hf.smul (-1)

/-- The difference of two weak forms of the same weight is a weak form. -/
theorem sub (hf : IsWeakForm Γ k f) (hf' : IsWeakForm Γ k f') : IsWeakForm Γ k (f - f') := by
  simpa [sub_eq_add_neg] using hf.add hf'.neg

/-- The product of weak forms of weights `k` and `l` is a weak form of weight `k + l`. -/
theorem mul (hf : IsWeakForm Γ k f) (hf' : IsWeakForm Γ l f') : IsWeakForm Γ (k + l) (f * f')
    where
  mdifferentiable := hf.mdifferentiable.mul hf'.mdifferentiable
  slash_eq γ hγ := by rw [mul_slash_SL2, hf.slash_eq γ hγ, hf'.slash_eq γ hγ]
  exists_isBigO_exp g := by
    obtain ⟨C, hC⟩ := hf.exists_isBigO_exp g
    obtain ⟨C', hC'⟩ := hf'.exists_isBigO_exp g
    refine ⟨C + C', ?_⟩
    rw [mul_slash_SL2]
    exact (hC.mul hC').congr_right fun τ ↦ by rw [← Real.exp_add, add_mul]

end IsWeakForm

/-- A constant function is a weak form of weight `0`. -/
theorem isWeakForm_const (c : ℂ) : IsWeakForm Γ 0 (fun _ ↦ c) where
  mdifferentiable := mdifferentiable_const
  slash_eq γ _ := is_invariant_const γ c
  exists_isBigO_exp g := ⟨0, by
    -- `is_invariant_const` is stated for `Function.const ℍ c`, which is `fun _ ↦ c`
    rw [show (fun _ : ℍ ↦ c) = Function.const ℍ c from rfl, is_invariant_const]
    exact (isBigO_const_const c (one_ne_zero (α := ℝ)) atImInfty).congr_right fun τ ↦ by simp⟩

/-- The zero function is a weak form of every weight. -/
theorem isWeakForm_zero : IsWeakForm Γ k 0 where
  mdifferentiable := mdifferentiable_const
  slash_eq _ _ := SlashAction.zero_slash _ _
  exists_isBigO_exp _ := ⟨0, by rw [SlashAction.zero_slash]; exact isBigO_zero _ _⟩

namespace IsWeakForm

/-- The `n`-th power of a weak form of weight `k` is a weak form of weight `n * k`. -/
theorem pow (hf : IsWeakForm Γ k f) (n : ℕ) : IsWeakForm Γ (n * k) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact isWeakForm_const 1
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hf using 1
    push_cast
    ring

end IsWeakForm

/-! ### Translates by `SL₂(ℤ)` and periodicity -/

/-- If `f` is invariant under the weight-`k` slash action of `Γ`, then every translate
`f ∣[k] g`, `g ∈ SL₂(ℤ)`, is periodic with period the strict level of `Γ`. -/
theorem periodic_slash_comp_ofComplex (hf : ∀ γ ∈ Γ, f ∣[k] γ = f) (g : SL(2, ℤ)) :
    Periodic ((f ∣[k] g) ∘ ofComplex) Γ.strictLevel :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
    have hT := ModularForm.slash_T_zpow_apply k Γ.strictLevel (f ∣[k] g) τ
    rw [zpow_natCast, Int.cast_natCast] at hT
    rw [← hT, ← SlashAction.slash_mul,
      show g * ModularGroup.T ^ Γ.strictLevel =
        g * ModularGroup.T ^ Γ.strictLevel * g⁻¹ * g by group,
      SlashAction.slash_mul, hf _ (Γ.conj_T_pow_strictLevel_mem g)]

namespace IsWeakForm

/-- Slashing a weak form on `Γ` by `g ∈ SL₂(ℤ)` gives a weak form on the conjugate
`g⁻¹ Γ g`, in the same weight. -/
theorem slash (hf : IsWeakForm Γ k f) (g : SL(2, ℤ)) :
    IsWeakForm (ConjAct.toConjAct g⁻¹ • Γ) k (f ∣[k] g) where
  mdifferentiable := by
    rw [SL_slash]
    exact hf.mdifferentiable.slash k _
  slash_eq γ hγ := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv,
      ConjAct.toConjAct_smul] at hγ
    rw [← SlashAction.slash_mul, show g * γ = g * γ * g⁻¹ * g by group, SlashAction.slash_mul,
      hf.slash_eq _ hγ]
  exists_isBigO_exp g' := by
    rw [← SlashAction.slash_mul]
    exact hf.exists_isBigO_exp (g * g')

/-- On a finite-index subgroup, the cusp germ of a weak form at every cusp is meromorphic: the
cusp function of `f ∣[k] g` in `exp (2 π i τ / N)`, for `N` the strict level of `Γ`, is
meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_slash [Γ.FiniteIndex] (hf : IsWeakForm Γ k f)
    (g : SL(2, ℤ)) : MeromorphicAt (cuspFunction Γ.strictLevel (f ∣[k] g)) 0 := by
  obtain ⟨C, hC⟩ := hf.exists_isBigO_exp g
  refine UpperHalfPlane.meromorphicAt_cuspFunction_of_isBigO_exp
    (by exact_mod_cast Γ.strictLevel_pos) (periodic_slash_comp_ofComplex hf.slash_eq g)
    (.of_forall fun τ ↦ ?_) hC
  rw [SL_slash]
  exact hf.mdifferentiable.slash k _ τ

end IsWeakForm

/-- **Weak forms have meromorphic cusp germs.** On a finite-index subgroup `Γ`, a function `f` is a
weak form of weight `k` exactly when it is holomorphic and `Γ`-invariant in weight `k`, and for
every `g ∈ SL₂(ℤ)` the translate `f ∣[k] g` has a period `h ≥ 1` for which its cusp function in
`exp (2 π i τ / h)` is meromorphic at `0`. -/
theorem isWeakForm_iff_meromorphicAt_cuspFunction [Γ.FiniteIndex] :
    IsWeakForm Γ k f ↔ MDiff f ∧ (∀ γ ∈ Γ, f ∣[k] γ = f) ∧
      ∀ g : SL(2, ℤ), ∃ h : ℕ, 0 < h ∧ Periodic ((f ∣[k] g) ∘ ofComplex) h ∧
        MeromorphicAt (cuspFunction h (f ∣[k] g)) 0 := by
  refine ⟨fun hf ↦ ⟨hf.mdifferentiable, hf.slash_eq, fun g ↦ ⟨Γ.strictLevel, Γ.strictLevel_pos,
    periodic_slash_comp_ofComplex hf.slash_eq g, hf.meromorphicAt_cuspFunction_slash g⟩⟩,
    fun ⟨hhol, hinv, hmero⟩ ↦ ⟨hhol, hinv, fun g ↦ ?_⟩⟩
  obtain ⟨h, hh, hper, hm⟩ := hmero g
  exact UpperHalfPlane.exists_isBigO_exp_of_meromorphicAt_cuspFunction (by exact_mod_cast hh)
    hper hm

/-! ### Odd weight -/

/-- In odd weight, a weak form on a subgroup containing `-1` vanishes. -/
theorem IsWeakForm.eq_zero_of_neg_one_mem (hf : IsWeakForm Γ k f) (hΓ : -1 ∈ Γ) (hk : Odd k) :
    f = 0 :=
  ModularForm.eq_zero_of_slash_neg_one_eq (hf.slash_eq _ hΓ) hk

/-! ### Modular forms -/

/-- The function underlying a modular form on a finite-index subgroup `Γ`, or more generally an
element of any `ModularFormClass` such as a cusp form, is a weak form on `Γ` of the same weight. -/
theorem _root_.ModularFormClass.isWeakForm {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Γ.map (mapGL ℝ)) k] [Γ.FiniteIndex] (f : F) : IsWeakForm Γ k f where
  mdifferentiable := ModularFormClass.holo f
  slash_eq γ hγ := by
    rw [SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  exists_isBigO_exp g :=
    ⟨0, (ModularFormClass.bdd_at_infty_slash f g).trans (isBigO_of_le _ fun _ ↦ by simp)⟩

/-- **Modular forms are the weak forms bounded at every cusp.** On a finite-index subgroup `Γ`, a
function is the function of a modular form of weight `k` on `Γ` exactly when it is a weak form of
weight `k` on `Γ` whose translates `f ∣[k] g`, `g ∈ SL₂(ℤ)`, are all bounded at `i∞`. The modular
form is then unique, since a modular form is determined by its function. -/
theorem exists_modularForm_coe_eq_iff [Γ.FiniteIndex] :
    (∃ F : ModularForm Γ k, ⇑F = f) ↔
      IsWeakForm Γ k f ∧ ∀ g : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] g) := by
  refine ⟨?_, fun ⟨hf, hbdd⟩ ↦ ?_⟩
  · rintro ⟨F, rfl⟩
    exact ⟨ModularFormClass.isWeakForm F, fun g ↦ ModularFormClass.bdd_at_infty_slash F g⟩
  refine ⟨{ toFun := f
            slash_action_eq' := ?_
            holo' := hf.mdifferentiable
            bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hf.slash_eq γ hγ
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ hbdd γ

/-! ### The inverse of the discriminant -/

/-- The inverse `Δ⁻¹` of the discriminant is a weak form of weight `-12` on `SL₂(ℤ)`: it is
holomorphic since `Δ` has no zeros on `ℍ`, and it grows like `exp (2 π Im τ)` at `i∞`. -/
theorem isWeakForm_inv_discriminant : IsWeakForm ⊤ (-12) discriminant⁻¹ := by
  have hslash (γ : SL(2, ℤ)) : discriminant⁻¹ ∣[(-12 : ℤ)] γ = discriminant⁻¹ := by
    have h := div_discriminant_slash (k := -12) 1 γ
    rwa [show (-12 : ℤ) + 12 = 0 by norm_num, is_invariant_one, one_div] at h
  refine ⟨CuspForm.discriminant.holo'.inv discriminant_ne_zero, fun γ _ ↦ hslash γ,
    fun g ↦ ⟨2 * Real.pi, ?_⟩⟩
  rw [hslash]
  refine (exp_isBigO_discriminant.inv_rev (.of_forall fun τ h ↦ ?_)).congr_right fun τ ↦ ?_
  · exact absurd h (Real.exp_pos _).ne'
  · rw [← Real.exp_neg, neg_mul, neg_mul, neg_neg]

/-- The inverse `Δ⁻¹` of the discriminant is unbounded at `i∞`, since `Δ` tends to `0` there. -/
theorem not_isBoundedAtImInfty_inv_discriminant : ¬ IsBoundedAtImInfty discriminant⁻¹ := by
  intro h
  have h0 : Tendsto (discriminant * discriminant⁻¹) atImInfty (nhds 0) :=
    discriminant_isZeroAtImInfty.mul_boundedAtFilter h
  have h1 : discriminant * discriminant⁻¹ = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (discriminant_ne_zero τ)
  rw [h1] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- The inverse `Δ⁻¹` of the discriminant, a weak form of weight `-12` on `SL₂(ℤ)`, is not the
function of a modular form. -/
theorem not_exists_modularForm_coe_eq_inv_discriminant :
    ¬ ∃ F : ModularForm (⊤ : Subgroup SL(2, ℤ)) (-12), ⇑F = discriminant⁻¹ := by
  intro h
  have := (exists_modularForm_coe_eq_iff.mp h).2 1
  rw [SlashAction.slash_one] at this
  exact not_isBoundedAtImInfty_inv_discriminant this

/-! ### Clearing the poles at the cusps with `Δ` -/

/-- The discriminant `Δ` is a weak form of weight `12` on `SL₂(ℤ)`. -/
theorem isWeakForm_discriminant : IsWeakForm ⊤ 12 discriminant where
  mdifferentiable := CuspForm.discriminant.holo'
  slash_eq γ _ := discriminant_slash γ
  exists_isBigO_exp g := ⟨0, by
    rw [discriminant_slash]
    exact discriminant_isZeroAtImInfty.isBoundedAtImInfty.trans
      (isBigO_of_le _ fun _ ↦ by simp)⟩

/-- **Uniform growth at the cusps.** On a finite-index subgroup `Γ`, a single real `C` bounds the
growth of a weak form at every cusp: `f ∣[k] g = O(exp (C · Im τ))` as `Im τ → ∞` for every
`g ∈ SL₂(ℤ)`. Indeed `f ∣[k] g` depends only on the coset `Γ g`, and there are finitely many. -/
theorem IsWeakForm.exists_forall_isBigO_exp [Γ.FiniteIndex] (hf : IsWeakForm Γ k f) :
    ∃ C : ℝ, ∀ g : SL(2, ℤ), (f ∣[k] g) =O[atImInfty] fun τ ↦ Real.exp (C * τ.im) := by
  choose C hC using hf.exists_isBigO_exp
  obtain ⟨M, hM⟩ := (Set.finite_range fun q : SL(2, ℤ) ⧸ Γ ↦ C q.out⁻¹).bddAbove
  refine ⟨M, fun g ↦ ?_⟩
  -- the representative `r` of the coset `g⁻¹ Γ` has `r⁻¹ = γ g` with `γ ∈ Γ`
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ g⁻¹
  have hg : f ∣[k] g = f ∣[k] (QuotientGroup.mk g⁻¹ : SL(2, ℤ) ⧸ Γ).out⁻¹ := by
    rw [hγ, mul_inv_rev, inv_inv, SlashAction.slash_mul, hf.slash_eq _ (inv_mem γ.property)]
  rw [hg]
  exact UpperHalfPlane.isBigO_exp_mul_im_of_le (hM ⟨_, rfl⟩) (hC _)

/-- **Clearing the poles at the cusps with `Δ`.** If `f` is a weak form of weight `k` on a
finite-index subgroup `Γ`, then for every sufficiently large `m` the product `f Δᵐ` is the function
of a modular form of weight `k + 12 m` on `Γ`. This needs neither `-1 ∈ Γ` nor regularity of the
cusps. -/
theorem IsWeakForm.eventually_exists_modularForm_coe_eq_mul_discriminant_pow [Γ.FiniteIndex]
    (hf : IsWeakForm Γ k f) :
    ∀ᶠ m : ℕ in atTop, ∃ F : ModularForm Γ (k + 12 * m), ⇑F = f * discriminant ^ m := by
  obtain ⟨C, hC⟩ := hf.exists_forall_isBigO_exp
  have hΔ : discriminant =O[atImInfty] fun τ ↦ Real.exp (-(2 * Real.pi) * τ.im) := by
    simpa [neg_mul] using CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant
      one_pos one_mem_strictPeriods_SL
  filter_upwards [eventually_ge_atTop ⌈C / (2 * Real.pi)⌉₊] with m hm
  have hCm : C ≤ 2 * Real.pi * m :=
    (div_le_iff₀' Real.two_pi_pos).mp ((Nat.le_ceil _).trans (by exact_mod_cast hm))
  have hweight : k + 12 * (m : ℤ) = k + m * 12 := by ring
  have hΔm := isWeakForm_discriminant.pow m
  refine exists_modularForm_coe_eq_iff.mpr
    ⟨hweight ▸ hf.mul (hΔm.mono (le_top : Γ ≤ ⊤)), fun g ↦ ?_⟩
  rw [hweight, mul_slash_SL2, hΔm.slash_eq g (Subgroup.mem_top g)]
  refine ((hC g).mul (hΔ.pow m)).trans (isBigO_of_le _ fun τ ↦ ?_)
  simp [← Real.exp_natCast_mul, ← Real.exp_add, Real.exp_le_one_iff]
  nlinarith [τ.im_pos]

/-- **Weak forms are quotients of modular forms by powers of `Δ`.** On a finite-index subgroup
`Γ`, a function `f` is a weak form of weight `k` exactly when `f Δᵐ` is the function of a modular
form of weight `k + 12 m` on `Γ` for some `m`. -/
theorem isWeakForm_iff_exists_modularForm_coe_eq_mul_discriminant_pow [Γ.FiniteIndex] :
    IsWeakForm Γ k f ↔ ∃ m : ℕ, ∃ F : ModularForm Γ (k + 12 * m), ⇑F = f * discriminant ^ m := by
  refine ⟨fun hf ↦ hf.eventually_exists_modularForm_coe_eq_mul_discriminant_pow.exists, ?_⟩
  rintro ⟨m, F, hF⟩
  have hfF : f = ⇑F * discriminant⁻¹ ^ m := by
    funext τ
    simp [hF, discriminant_ne_zero τ]
  rw [hfF]
  convert (ModularFormClass.isWeakForm F).mul
    ((isWeakForm_inv_discriminant.mono (le_top : Γ ≤ ⊤)).pow m) using 1
  ring

end TauCeti
