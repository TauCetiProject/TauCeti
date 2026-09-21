/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.NumberTheory.ModularForms.Bounds
public import TauCeti.NumberTheory.Modular
-- proof-only: `CuspForm.coe_translate_gl`
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The Petersson inner product

The **Petersson inner product**
$$\langle f, g \rangle = \int_D \overline{f(\tau)} \, g(\tau) \, (\operatorname{Im}\tau)^k
\, d\mu(\tau)$$
of two functions on the upper half-plane, integrated over a set `D` — in applications a
fundamental domain — against
Mathlib's invariant measure `volume : Measure ℍ` (`dx dy / y²`,
`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`), with the integrand
`petersson k f g` from `Mathlib/NumberTheory/ModularForms/Petersson.lean`.

## Main definitions

* `UpperHalfPlane.peterssonInner`: the set integral of the Petersson integrand over an
  arbitrary `D : Set ℍ` — a sesquilinear pairing on classes of functions whose integrands
  are integrable over `D`; positive definiteness is a separate result of the
  level-one-domain specialization (`CuspForm.peterssonInnerFd_definite`).
* `CuspForm.peterssonInnerFd`: the level-one-domain pairing of two cusp forms (over `𝒟`,
  whatever the level).
* `CuspForm.peterssonInnerCore`: for arithmetic levels, the pairing bundled as an
  `InnerProductSpace.Core` on `S_k(Γ)`.

## Main results

* `UpperHalfPlane.peterssonInner_conj_symm`: Hermitian symmetry.
* `UpperHalfPlane.petersson_smul_of_mem` and `UpperHalfPlane.petersson_psl_smul_of_mem`: the
  integrand is invariant under `Γ`, and under the image of `Γ` in `PSL(2, ℤ)` that actually acts.
* `UpperHalfPlane.peterssonInner_eq_of_isFundamentalDomain`: the pairing is the same over any two
  fundamental domains for that image — "the" Petersson product does not depend on the domain.
* `UpperHalfPlane.integrableOn_petersson_fd_left`: integrability of the Petersson integrand of a
  cusp form against a modular form over the standard fundamental domain.
* `UpperHalfPlane.integrableOn_petersson_slash_left` and
  `UpperHalfPlane.integrableOn_petersson_slash_right`: the same for forms slashed by `SL₂(ℤ)`
  when either argument is cuspidal.
* `UpperHalfPlane.integrableOn_petersson_sl_smul_fd_left` and
  `UpperHalfPlane.integrableOn_petersson_sl_smul_fd_right`: integrability over every
  `SL(2, ℤ)`-translate of the standard fundamental domain when either argument is cuspidal.
* `UpperHalfPlane.integrableOn_petersson_of_measure_lt_top`: integrability over any set of finite
  measure, for any measure, for two cusp forms of *unrelated* arithmetic groups. This is the shape
  a Hecke operator's summands present, where no single bound covers the pair.
* `UpperHalfPlane.integrableOn_petersson_slash_left_of_measure_lt_top` and
  `UpperHalfPlane.integrableOn_petersson_slash_right_of_measure_lt_top`: its specializations to
  one argument slashed by a `GL(2, ℝ)` element whose conjugate of the group is again arithmetic.
* `UpperHalfPlane.peterssonInner_self_eq_ofReal`, `peterssonInner_self_re_nonneg`: the
  self-pairing of any function is the real integral of `‖h τ‖² (Im τ)^k`, hence nonnegative
  over any domain.
* `UpperHalfPlane.eq_zero_on_fd_of_peterssonInner_self_eq_zero`: definiteness on the
  fundamental domain, for any continuous function with integrable self-integrand.

The pairing is parameterized by an arbitrary `D : Set ℍ` rather than fixing a subgroup;
for `SL₂(ℤ)` use `D = ModularGroup.fd`, and for a congruence subgroup a union of
translates of `𝒟`. The topology of `𝒟`/`𝒟ᵒ` comes from
`Mathlib/NumberTheory/Modular.lean`, and its measure theory (finite volume, null frontier,
`𝒟`-vs-`𝒟ᵒ` integration) from `TauCeti/NumberTheory/Modular.lean`.

Ported from the AINTLIB `LeanModularForms` project's
`LeanModularForms/Modularforms/PeterssonInnerProduct.lean` (Chris Birkbeck), rewritten to
consume Mathlib's `MeasureSpace ℍ` instance instead of constructing the hyperbolic measure.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.4
* Miyake, *Modular forms*, §2.5
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/PeterssonInnerProduct.lean`)
* AINTLIB again, at commit `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, Apache-2.0, for
  `peterssonInner_sum_left` and `peterssonInner_sum_right`:
  `HeckeRIngs/GL2/AdjointTheory/SummandAdjoint.lean` (`peterssonInner_add_left`, :222;
  `peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable`, :620); and for the
  finite-measure integrability results `integrableOn_petersson_of_measure_lt_top` and its two
  slash specializations: `HeckeRIngs/GL2/AdjointTheory/DeltaBSystem.lean`
  (`integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure`, :397).
-/

public section

noncomputable section

open MeasureTheory Measure UpperHalfPlane ModularGroup Complex Set ENNReal
open Matrix.SpecialLinearGroup

open scoped ComplexConjugate MatrixGroups ModularForm NNReal Pointwise

namespace UpperHalfPlane

/-- The Petersson pairing of two functions `f, g : ℍ → ℂ` of weight `k`, integrated over
an arbitrary set `D` (in applications, a fundamental domain) with respect to the
invariant measure.

The integrand is `conj(f(τ)) · g(τ) · (Im τ)^k`, which equals
`petersson k f g τ` from `Mathlib.NumberTheory.ModularForms.Petersson`. -/
def peterssonInner (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) : ℂ :=
  ∫ τ in D, petersson k f g τ

/-- The pairing depends on the domain only up to null sets: congruent domains give equal
pairings, with no unfolding to the underlying set integral. -/
theorem peterssonInner_congr_set {k : ℤ} {D D' : Set ℍ} (h : D =ᶠ[MeasureTheory.ae volume] D')
    (f g : ℍ → ℂ) : peterssonInner k D f g = peterssonInner k D' f g :=
  MeasureTheory.setIntegral_congr_set h

/-- Over the standard fundamental domain the pairing may be computed on its interior. -/
theorem peterssonInner_fd_eq_fdo (k : ℤ) (f g : ℍ → ℂ) :
    peterssonInner k ModularGroup.fd f g = peterssonInner k ModularGroup.fdo f g :=
  peterssonInner_congr_set ModularGroup.fd_ae_eq_fdo f g

/-- **The Petersson integrand is invariant under the group its arguments are modular for.**
This is pointwise, and no change of variables is involved: `conj (f τ)` and `f' τ` each pick up
the automorphy factor of `γ`, and their product cancels against the transformation of the weight
`im τ ^ k`, which `UpperHalfPlane.petersson_slash_SL` records. So `petersson k f f'` is a genuine
function on the quotient `Γ \ ℍ`.

Not `@[simp]`: the left-hand side is not in simp normal form, since `ModularGroup.sl_moeb`
rewrites `γ • τ` into the `GL(2, ℝ)` action of `γ`'s image. The `PSL(2, ℤ)` form below carries the
attribute instead, and it is the one simp can use. -/
theorem petersson_smul_of_mem {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] (k : ℤ)
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k]
    [SlashInvariantFormClass F' (Γ.map (mapGL ℝ)) k] (f : F) (f' : F') {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) (τ : ℍ) :
    petersson k ⇑f ⇑f' (γ • τ) = petersson k ⇑f ⇑f' τ := by
  -- `ModularForm.SL_slash` is `rfl`, so the `SL(2, ℤ)`-slash *is* the `GL(2, ℝ)`-slash of the
  -- image; the two are defeq but not syntactically equal, so these are `exact`s and not `rw`s.
  have hf : ⇑f ∣[k] γ = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  have hf' : ⇑f' ∣[k] γ = ⇑f' :=
    SlashInvariantFormClass.slash_action_eq f' _ (Subgroup.mem_map_of_mem _ hγ)
  rw [← petersson_slash_SL k ⇑f ⇑f' γ τ, hf, hf']

/-- **The Petersson integrand is invariant under the image of `Γ` in `PSL(2, ℤ)`**, which is
the group that actually acts: `±I` acts trivially on `ℍ`. This is the hypothesis
`MeasureTheory.IsFundamentalDomain.setIntegral_eq` asks for. -/
@[simp]
theorem petersson_psl_smul_of_mem {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ] (k : ℤ)
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k]
    [SlashInvariantFormClass F' (Γ.map (mapGL ℝ)) k] (f : F) (f' : F')
    (g : Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (τ : ℍ) :
    petersson k ⇑f ⇑f' ((g : PSL(2, ℤ)) • τ) = petersson k ⇑f ⇑f' τ := by
  obtain ⟨γ, hγ, hg⟩ := g.2
  rw [← hg]
  exact petersson_smul_of_mem k f f' hγ τ

/-- **The Petersson pairing does not depend on the fundamental domain.** Any two fundamental
domains for the image of `Γ` in `PSL(2, ℤ)` give the same pairing of two forms modular for `Γ`,
because the integrand is constant on `Γ`-orbits (`petersson_psl_smul_of_mem`).

Together with a proof that a particular set *is* a fundamental domain — for the union of
translates of `𝒟ᵒ` that the coset sum produces, `ModularGroup.isFundamentalDomain_fdo` and its
subgroup form — this is what makes "the" Petersson product well defined. -/
theorem peterssonInner_eq_of_isFundamentalDomain {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k]
    [SlashInvariantFormClass F' (Γ.map (mapGL ℝ)) k] (f : F) (f' : F') {S T : Set ℍ}
    (hS : MeasureTheory.IsFundamentalDomain
      (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) S volume)
    (hT : MeasureTheory.IsFundamentalDomain
      (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) T volume) :
    peterssonInner k S ⇑f ⇑f' = peterssonInner k T ⇑f ⇑f' :=
  hS.setIntegral_eq hT fun g τ ↦ petersson_psl_smul_of_mem k f f' g τ

/-- Unfolding: the pairing over `D` is the integral of the Petersson integrand over `D`. -/
theorem peterssonInner_def (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f g = ∫ τ in D, petersson k f g τ := (rfl)

/-- Hermitian symmetry: `conj ⟨g, f⟩ = ⟨f, g⟩`. -/
@[simp]
theorem peterssonInner_conj_symm (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    conj (peterssonInner k D g f) = peterssonInner k D f g := by
  simp only [peterssonInner, ← integral_conj, petersson_symm k g f]

/-- The pairing with zero on the right vanishes. -/
@[simp]
theorem peterssonInner_zero_right (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    peterssonInner k D f 0 = 0 := by
  simp [peterssonInner, petersson]

/-- The pairing with zero on the left vanishes. -/
@[simp]
theorem peterssonInner_zero_left (k : ℤ) (D : Set ℍ) (g : ℍ → ℂ) :
    peterssonInner k D 0 g = 0 := by
  simp [peterssonInner, petersson]

/-- Negation in the right argument. -/
@[simp]
theorem peterssonInner_neg_right (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f (-g) = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, mul_neg, neg_mul, integral_neg]

/-- Negation in the left argument. -/
@[simp]
theorem peterssonInner_neg_left (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D (-f) g = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, map_neg, neg_mul, integral_neg]

/-- The Petersson integrand of a cusp form against a modular form is integrable over the
standard fundamental domain. -/
theorem integrableOn_petersson_fd_left {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') :
    IntegrableOn (fun τ ↦ petersson k f f' τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable.restrict) C
    (ae_of_all _ fun τ ↦ hC τ)

/-- The Petersson integrand of a modular form against a cusp form is integrable over the
standard fundamental domain. -/
theorem integrableOn_petersson_fd_right {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [ModularFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (f' : F') :
    IntegrableOn (fun τ ↦ petersson k f f' τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_right k Γ f f'
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable.restrict) C
    (ae_of_all _ fun τ ↦ hC τ)

/-- The Petersson self-integrand of any function is a nonnegative real:
`petersson k h h τ = ‖h τ‖² (Im τ)^k`. -/
@[simp]
theorem petersson_self_eq_ofReal (k : ℤ) (h : ℍ → ℂ) (τ : ℍ) :
    petersson k h h τ = ((normSq (h τ) * τ.im ^ k : ℝ) : ℂ) := by
  simp only [petersson, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

/-- The Petersson self-pairing of any function over any domain is the real integral of
`‖h τ‖² (Im τ)^k`. -/
theorem peterssonInner_self_eq_ofReal (k : ℤ) (D : Set ℍ) (h : ℍ → ℂ) :
    peterssonInner k D h h = ((∫ τ in D, normSq (h τ) * τ.im ^ k : ℝ) : ℂ) := by
  rw [peterssonInner_def]
  simp_rw [petersson_self_eq_ofReal]
  exact integral_ofReal

/-- The Petersson self-pairing over any domain is nonnegative, for any function:
the integrand `‖h τ‖² (Im τ)^k` is. -/
theorem peterssonInner_self_re_nonneg (k : ℤ) (D : Set ℍ)
    (h : ℍ → ℂ) : 0 ≤ (peterssonInner k D h h).re := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_re]
  exact setIntegral_nonneg_of_ae_restrict <| ae_of_all _ fun τ ↦
    mul_nonneg (normSq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos τ).le _)

/-! ### Integrability of a one-sided slash, over any set of finite measure -/

/-- **The Petersson integrand of two cusp forms for *unrelated* arithmetic groups is integrable
over any set of finite measure.**

The lemmas above need a single group: they slash *both* arguments by the same `SL(2, ℤ)` element,
so one cusp-form bound covers the pair. A Hecke operator does not do that — its summands pair
forms cuspidal for different groups, which is the situation this covers and
`CuspFormClass.petersson_bounded_left` does not. -/
theorem integrableOn_petersson_of_measure_lt_top {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ Γ' : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ'.IsArithmetic]
    [CuspFormClass F Γ k] [CuspFormClass F' Γ' k] (f : F) (g : F') (μ : Measure ℍ) {S : Set ℍ}
    (hS : μ S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ) S μ := by
  obtain ⟨Cf, hCf⟩ := CuspFormClass.petersson_bounded_left k Γ f f
  obtain ⟨Cg, hCg⟩ := CuspFormClass.petersson_bounded_left k Γ' g g
  refine IntegrableOn.of_bound hS ((petersson_continuous k (ModularFormClass.continuous f)
    (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    ((Cf + Cg) / 2) (ae_of_all _ fun τ ↦ ?_)
  -- each argument is bounded against *itself*, which needs no group common to both; `2ab ≤ a²+b²`
  -- scaled by the positive `(Im τ) ^ k` combines the two bounds
  have him : (0 : ℝ) < τ.im ^ k := zpow_pos (UpperHalfPlane.im_pos τ) k
  have hnorm : ∀ a b : ℍ → ℂ, ‖petersson k a b τ‖ = ‖a τ‖ * ‖b τ‖ * τ.im ^ k := fun a b ↦ by
    simp [petersson, abs_of_pos (UpperHalfPlane.im_pos τ)]
  rw [hnorm]
  have hf := hCf τ
  have hg := hCg τ
  rw [hnorm] at hf hg
  nlinarith [mul_le_mul_of_nonneg_right (two_mul_le_add_sq ‖f τ‖ ‖g τ‖) him.le]

open ConjAct in
/-- **The Petersson integrand of a *singly* slashed cusp form against a cusp form is integrable
over any set of finite measure** — the orientation
`peterssonInner_sum_slash_left_adjugateGL` asks its caller for.

Arithmeticity of the conjugate is taken as an instance rather than derived, so that a caller with
a rational `σ` supplies it from `Subgroup.IsArithmetic.conj` and one with any other source of it
is not shut out. -/
theorem integrableOn_petersson_slash_left_of_measure_lt_top {F F' : Type*} [FunLike F ℍ ℂ]
    [FunLike F' ℍ ℂ] (k : ℤ) (Γ Γ' : Subgroup (GL (Fin 2) ℝ)) [Γ'.IsArithmetic]
    [CuspFormClass F Γ k] [CuspFormClass F' Γ' k] (f : F) (g : F') (σ : GL (Fin 2) ℝ)
    [((toConjAct σ)⁻¹ • Γ).IsArithmetic] (μ : Measure ℍ) {S : Set ℍ} (hS : μ S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] σ) ⇑g τ) S μ := by
  have := integrableOn_petersson_of_measure_lt_top k ((toConjAct σ)⁻¹ • Γ) Γ'
    (CuspForm.translate f σ) g μ hS
  rwa [CuspForm.coe_translate_gl] at this

open ConjAct in
/-- The mirror of `integrableOn_petersson_slash_left_of_measure_lt_top`, with the *second*
argument slashed. -/
theorem integrableOn_petersson_slash_right_of_measure_lt_top {F F' : Type*} [FunLike F ℍ ℂ]
    [FunLike F' ℍ ℂ] (k : ℤ) (Γ Γ' : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [CuspFormClass F' Γ' k] (f : F) (g : F') (σ : GL (Fin 2) ℝ)
    [((toConjAct σ)⁻¹ • Γ').IsArithmetic] (μ : Measure ℍ) {S : Set ℍ} (hS : μ S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f (⇑g ∣[k] σ) τ) S μ := by
  have := integrableOn_petersson_of_measure_lt_top k Γ ((toConjAct σ)⁻¹ • Γ')
    f (CuspForm.translate g σ) μ hS
  rwa [CuspForm.coe_translate_gl] at this

/-- The Petersson integrand of a slashed cusp form and modular form is integrable over `𝒟`:
slashing by an element of `SL₂(ℤ)` moves the integrand along the action, where the cusp-form
bound still applies. -/
theorem integrableOn_petersson_slash_left {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) fd (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  have hslash : (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) =
      fun τ ↦ petersson k (⇑f) (⇑f') (δ • τ) :=
    funext fun τ ↦ petersson_slash_SL k _ _ δ τ
  rw [hslash]
  -- the `SL(2, ℤ)` action on `ℍ` is the `GL(2, ℝ)` action along `mapGL`, where the
  -- continuity instance lives
  have hsmul : Continuous fun τ : ℍ ↦ δ • τ := by
    simp only [MulAction.compHom_smul_def]
    exact continuous_const_smul (mapGL ℝ δ)
  exact IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).comp hsmul |>.aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC (δ • τ))

/-- The Petersson integrand of a slashed modular form and cusp form is integrable over `𝒟`:
the mirror of `integrableOn_petersson_slash_left`, obtained from it by the conjugate symmetry
`UpperHalfPlane.petersson_symm` of the integrand, complex conjugation being an `ℝ`-linear
isometry of `ℂ`. -/
theorem integrableOn_petersson_slash_right {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [ModularFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (f' : F') (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) fd (volume : Measure ℍ) := by
  have h : IntegrableOn (fun τ ↦ conj (petersson k (⇑f' ∣[k] δ) (⇑f ∣[k] δ) τ)) fd
      (volume : Measure ℍ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
      (integrableOn_petersson_slash_left k Γ f' f δ)
  simpa only [← petersson_symm] using h

/-- **The Petersson integrand of a cusp form and a modular form is integrable over every
`SL(2, ℤ)`-translate of `𝒟`.** Transporting the integral back to `𝒟` turns the integrand into
that of the simultaneously slashed pair, where the cusp-form bound applies. -/
theorem integrableOn_petersson_sl_smul_fd_left {F F' : Type*} [FunLike F ℍ ℂ]
    [FunLike F' ℍ ℂ] (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') (γ : SL(2, ℤ)) :
    IntegrableOn (petersson k ⇑f ⇑f') (γ • fd) volume := by
  rw [ModularGroup.sl_smul_set, ← Set.image_smul,
    (measurePreserving_smul (γ : GL (Fin 2) ℝ) volume).integrableOn_image
      (measurableEmbedding_const_smul (γ : GL (Fin 2) ℝ))]
  refine (integrableOn_petersson_slash_left k Γ f f' γ).congr_fun (fun τ _ ↦ ?_)
    isClosed_fd.measurableSet
  simp only [Function.comp_apply, petersson_slash_SL, ModularGroup.sl_moeb]

/-- **The Petersson integrand of a modular form and a cusp form is integrable over every
`SL(2, ℤ)`-translate of `𝒟`.** This is the right-cuspidal counterpart of
`integrableOn_petersson_sl_smul_fd_left`, obtained from it by the same conjugate symmetry of the
integrand as `integrableOn_petersson_slash_right`. -/
theorem integrableOn_petersson_sl_smul_fd_right {F F' : Type*} [FunLike F ℍ ℂ]
    [FunLike F' ℍ ℂ] (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [ModularFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (f' : F') (γ : SL(2, ℤ)) :
    IntegrableOn (petersson k ⇑f ⇑f') (γ • fd) volume := by
  have h : IntegrableOn (fun τ ↦ conj (petersson k ⇑f' ⇑f τ)) (γ • fd) (volume : Measure ℍ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
      (integrableOn_petersson_sl_smul_fd_left k Γ f' f γ)
  simpa only [← petersson_symm] using h

/-- Additivity in the second argument. -/
theorem peterssonInner_add_right (k : ℤ) (D : Set ℍ) (f g₁ g₂ : ℍ → ℂ)
    (hg₁ : IntegrableOn (fun τ ↦ petersson k f g₁ τ) D (volume : Measure ℍ))
    (hg₂ : IntegrableOn (fun τ ↦ petersson k f g₂ τ) D (volume : Measure ℍ)) :
    peterssonInner k D f (g₁ + g₂) = peterssonInner k D f g₁ + peterssonInner k D f g₂ := by
  simp only [peterssonInner]
  rw [← integral_add hg₁ hg₂]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.add_apply]
    ring)

/-- Additivity in the first argument, given integrability of both summands. -/
theorem peterssonInner_add_left (k : ℤ) (D : Set ℍ) (f₁ f₂ g : ℍ → ℂ)
    (hf₁ : IntegrableOn (fun τ ↦ petersson k f₁ g τ) D (volume : Measure ℍ))
    (hf₂ : IntegrableOn (fun τ ↦ petersson k f₂ g τ) D (volume : Measure ℍ)) :
    peterssonInner k D (f₁ + f₂) g = peterssonInner k D f₁ g + peterssonInner k D f₂ g := by
  simp only [peterssonInner]
  rw [← integral_add hf₁ hf₂]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.add_apply, map_add]
    ring)

/-- **Additivity over a finite family in the first argument.** The `add_left` case iterated;
the hypothesis is integrability of each summand's integrand, exactly as there. -/
theorem peterssonInner_sum_left (k : ℤ) (D : Set ℍ) {ι : Type*} (s : Finset ι)
    (f : ι → ℍ → ℂ) (g : ℍ → ℂ)
    (hf : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k (f i) g τ) D (volume : Measure ℍ)) :
    peterssonInner k D (∑ i ∈ s, f i) g = ∑ i ∈ s, peterssonInner k D (f i) g := by
  simp only [peterssonInner]
  rw [← integral_finsetSum s hf]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Finset.sum_apply, _root_.map_sum, Finset.sum_mul])

/-- **Additivity over a finite family in the second argument**, the mirror of
`peterssonInner_sum_left`. -/
theorem peterssonInner_sum_right (k : ℤ) (D : Set ℍ) {ι : Type*} (s : Finset ι)
    (f : ℍ → ℂ) (g : ι → ℍ → ℂ)
    (hg : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k f (g i) τ) D (volume : Measure ℍ)) :
    peterssonInner k D f (∑ i ∈ s, g i) = ∑ i ∈ s, peterssonInner k D f (g i) := by
  simp only [peterssonInner]
  rw [← integral_finsetSum s hg]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul])

/-- Scalar multiplication in the second argument. -/
@[simp]
theorem peterssonInner_smul_right (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D f (c • g) = c * peterssonInner k D f g := by
  simp only [peterssonInner]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.smul_apply, smul_eq_mul]
    ring)

/-- Conjugate-scalar multiplication in the left argument. -/
@[simp]
theorem peterssonInner_smul_left (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D (c • f) g = conj c * peterssonInner k D f g := by
  simp only [peterssonInner]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ by
    simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul]
    ring)

/-- **Definiteness of the Petersson pairing on the fundamental domain**: a continuous
function whose Petersson self-integrand is integrable on `𝒟` and whose self-pairing over
`𝒟` vanishes is zero everywhere on `𝒟`.

The nonnegative continuous integrand `normSq (f τ) · (Im τ)^k` is a.e. zero, hence zero on
the open domain `𝒟ᵒ`, hence zero on `𝒟 = closure 𝒟ᵒ` by continuity. -/
theorem eq_zero_on_fd_of_peterssonInner_self_eq_zero {k : ℤ} {f : ℍ → ℂ}
    (hf : Continuous f) (hint : IntegrableOn (petersson k f f) fd volume)
    (hpet : peterssonInner k fd f f = 0) {τ : ℍ} (hτ : τ ∈ fd) : f τ = 0 := by
  set g : ℍ → ℝ := fun z ↦ (petersson k f f z).re
  have hg_zero : ∫ z in fd, g z = 0 := by
    trans RCLike.re (∫ z in fd, petersson k f f z)
    · exact integral_re hint
    · simp only [peterssonInner] at hpet; rw [hpet]; simp
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z ↦ by
    simp only [g, petersson_self_eq_ofReal, Complex.ofReal_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hg_ae : g =ᶠ[ae ((volume : Measure ℍ).restrict fd)] 0 := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hg_nonneg) hint.re]
  have hg_cont : Continuous g :=
    Complex.continuous_re.comp (petersson_continuous k hf hf)
  have hgτ : g τ = 0 :=
    Measure.eqOn_of_ae_eq hg_ae hg_cont.continuousOn continuousOn_const
      (by rw [← fdo_eq_interior_fd, ← fd_eq_closure_fdo]) hτ
  simp only [g, petersson_self_eq_ofReal, Complex.ofReal_re] at hgτ
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hgτ).elim id
    (fun h ↦ absurd h (ne_of_gt (zpow_pos τ.im_pos k))))

end UpperHalfPlane

namespace CuspForm

open UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The **level-one-domain Petersson pairing** of two cusp forms: the integral over the
standard fundamental domain `𝒟` for `SL₂(ℤ)`, whatever the level `Γ` — the `Fd` in the
name marks that the integration domain is `𝒟`, not a `Γ`-fundamental domain.

This is **not** the `Γ \ ℍ`-normalized Petersson inner product, which integrates over a
`Γ`-fundamental domain. Its structure accrues by hypothesis: Hermitian symmetry and the
zero/negation laws, reality, and nonnegativity of the self-pairing are unconditional,
the scalar laws (`peterssonInnerFd_smul_left`/`_right`) require `[Γ.HasDetOne]`, and
additivity (`peterssonInnerFd_add_left`/`_right`) and positive definiteness
(`peterssonInnerFd_definite`) require `[Γ.IsArithmetic]`. -/
def peterssonInnerFd (f g : CuspForm Γ k) : ℂ :=
  UpperHalfPlane.peterssonInner k ModularGroup.fd f g

/-- Unfolding: the cusp-form pairing is `peterssonInner` over the standard domain `𝒟`. -/
theorem peterssonInnerFd_def (f g : CuspForm Γ k) :
    peterssonInnerFd f g = UpperHalfPlane.peterssonInner k ModularGroup.fd f g := (rfl)

/-- Hermitian symmetry of the level-one-domain pairing. -/
@[simp]
theorem peterssonInnerFd_conj_symm (f g : CuspForm Γ k) :
    conj (peterssonInnerFd g f) = peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def]
  exact UpperHalfPlane.peterssonInner_conj_symm k ModularGroup.fd f g

/-- The self-pairing is real: its imaginary part vanishes, by Hermitian symmetry. -/
@[simp]
theorem peterssonInnerFd_self_im (f : CuspForm Γ k) : (peterssonInnerFd f f).im = 0 :=
  Complex.conj_eq_iff_im.mp (peterssonInnerFd_conj_symm f f)

/-- The self-pairing is nonnegative: its real part is the integral of
`|f τ|² (Im τ)ᵏ ≥ 0` over the fundamental domain. -/
theorem peterssonInnerFd_self_re_nonneg (f : CuspForm Γ k) :
    0 ≤ (peterssonInnerFd f f).re := by
  rw [peterssonInnerFd_def]
  exact UpperHalfPlane.peterssonInner_self_re_nonneg k _ _

/-- The pairing vanishes when its right argument is zero. -/
@[simp]
theorem peterssonInnerFd_zero_right (f : CuspForm Γ k) : peterssonInnerFd f 0 = 0 := by
  simp [peterssonInnerFd_def]

/-- The pairing vanishes when its left argument is zero. -/
@[simp]
theorem peterssonInnerFd_zero_left (g : CuspForm Γ k) : peterssonInnerFd 0 g = 0 := by
  simp [peterssonInnerFd_def]

/-- Negating the right argument negates the pairing. -/
@[simp]
theorem peterssonInnerFd_neg_right (f g : CuspForm Γ k) :
    peterssonInnerFd f (-g) = -peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, FunLike.coe_neg]
  exact UpperHalfPlane.peterssonInner_neg_right k ModularGroup.fd f g

/-- Negating the left argument negates the pairing: the first slot is conjugate-linear,
and conjugation fixes `-1`. -/
@[simp]
theorem peterssonInnerFd_neg_left (f g : CuspForm Γ k) :
    peterssonInnerFd (-f) g = -peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, FunLike.coe_neg]
  exact UpperHalfPlane.peterssonInner_neg_left k ModularGroup.fd f g

section HasDetOne

variable [Γ.HasDetOne]

/-- The level-one-domain pairing is ℂ-linear in the second argument. -/
@[simp]
theorem peterssonInnerFd_smul_right (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInnerFd f (c • g) = c * peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, FunLike.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_right k ModularGroup.fd c f g

/-- The level-one-domain pairing is conjugate-linear in the first argument. -/
@[simp]
theorem peterssonInnerFd_smul_left (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInnerFd (c • f) g = conj c * peterssonInnerFd f g := by
  simp only [peterssonInnerFd_def, FunLike.coe_smul]
  exact UpperHalfPlane.peterssonInner_smul_left k ModularGroup.fd c f g

end HasDetOne

/-- **Positive definiteness from integrability**, at arbitrary level: a cusp form with
integrable Petersson self-integrand over `𝒟` and vanishing self-pairing is zero.

The self-pairing vanishing forces `f = 0` on the open fundamental domain `𝒟ᵒ`
(`eq_zero_on_fd_of_peterssonInner_self_eq_zero`), and a holomorphic function on `ℍ`
vanishing on a nonempty open set vanishes identically
(`UpperHalfPlane.eq_zero_of_frequently`). -/
theorem peterssonInnerFd_definite_of_integrable (f : CuspForm Γ k)
    (hint : MeasureTheory.IntegrableOn (petersson k (⇑f) (⇑f)) ModularGroup.fd
      MeasureTheory.volume)
    (hpet : peterssonInnerFd f f = 0) :
    f = 0 := by
  rw [peterssonInnerFd_def] at hpet
  have hfdo : ∀ τ ∈ ModularGroup.fdo, f τ = 0 := fun τ hτ ↦
    eq_zero_on_fd_of_peterssonInner_self_eq_zero (ModularFormClass.continuous f)
      hint hpet (ModularGroup.fdo_subset_fd hτ)
  set τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩ with hτ₀_def
  have hτ₀ : τ₀ ∈ ModularGroup.fdo := by
    constructor
    · norm_num [hτ₀_def, Complex.normSq_apply]
    · norm_num [hτ₀_def]
  have hev := Filter.eventually_of_mem (ModularGroup.isOpen_fdo.mem_nhds hτ₀) hfdo
  have h := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun h τ

section IsArithmetic

variable [Γ.IsArithmetic]

/-- Additivity of the level-one-domain pairing in the second argument. -/
@[simp]
theorem peterssonInnerFd_add_right (f g₁ g₂ : CuspForm Γ k) :
    peterssonInnerFd f (g₁ + g₂) = peterssonInnerFd f g₁ + peterssonInnerFd f g₂ := by
  simp only [peterssonInnerFd_def, FunLike.coe_add]
  exact UpperHalfPlane.peterssonInner_add_right k ModularGroup.fd f g₁ g₂
    (integrableOn_petersson_fd_left k Γ f g₁) (integrableOn_petersson_fd_left k Γ f g₂)

/-- Additivity of the level-one-domain pairing in the first argument. -/
@[simp]
theorem peterssonInnerFd_add_left (f₁ f₂ g : CuspForm Γ k) :
    peterssonInnerFd (f₁ + f₂) g = peterssonInnerFd f₁ g + peterssonInnerFd f₂ g := by
  calc peterssonInnerFd (f₁ + f₂) g
      = conj (peterssonInnerFd g (f₁ + f₂)) := (peterssonInnerFd_conj_symm _ _).symm
    _ = conj (peterssonInnerFd g f₁) + conj (peterssonInnerFd g f₂) := by
        simp [peterssonInnerFd_add_right]
    _ = peterssonInnerFd f₁ g + peterssonInnerFd f₂ g := by
        simp [peterssonInnerFd_conj_symm]

/-- **Positive definiteness of the level-one-domain pairing**: a cusp form of any
arithmetic level with vanishing self-pairing is zero — the integrability hypothesis of
`peterssonInnerFd_definite_of_integrable` is automatic. -/
theorem peterssonInnerFd_definite (f : CuspForm Γ k) (hpet : peterssonInnerFd f f = 0) :
    f = 0 :=
  peterssonInnerFd_definite_of_integrable f (integrableOn_petersson_fd_left k Γ f f) hpet

/-- The self-pairing vanishes exactly on the zero form: nondegeneracy packaged with the
zero law. -/
@[simp]
theorem peterssonInnerFd_self_eq_zero (f : CuspForm Γ k) :
    peterssonInnerFd f f = 0 ↔ f = 0 :=
  ⟨peterssonInnerFd_definite f, fun h ↦ by rw [h]; exact peterssonInnerFd_zero_left 0⟩

/-- The `𝒟`-domain Petersson pairing bundled as an `InnerProductSpace.Core` on
`S_k(Γ)` for an arithmetic level: the Hermitian interface behind Mathlib's standard
inner-product, norm, and orthogonality APIs. Evaluation is `peterssonInnerCore_inner`.

Deliberately **not** an instance: the pairing integrates over the level-one domain `𝒟`, not
over a fundamental domain for `Γ`, so for general `Γ` it is not the genuine level-`Γ`
Petersson product, and making it canonical would silently give downstream orthogonality and
adjoint APIs the wrong domain. It is a plain `def` that consumers must name explicitly; no
`InnerProductSpace` instance is derived from it. The `@[instance_reducible]` attribute is
required by Lean's class-definition reducibility linter for any `def` of class type — it
governs unfolding during instance search and registers nothing on its own. -/
@[instance_reducible]
noncomputable def peterssonInnerCore [Γ.HasDetOne] :
    InnerProductSpace.Core ℂ (CuspForm Γ k) where
  inner := peterssonInnerFd
  conj_inner_symm := peterssonInnerFd_conj_symm
  re_inner_nonneg := peterssonInnerFd_self_re_nonneg
  add_left := peterssonInnerFd_add_left
  smul_left f g c := peterssonInnerFd_smul_left c f g
  definite := peterssonInnerFd_definite

/-- Evaluation of the bundled core: its inner product is `peterssonInnerFd`. -/
@[simp]
theorem peterssonInnerCore_inner [Γ.HasDetOne] (f g : CuspForm Γ k) :
    (peterssonInnerCore : InnerProductSpace.Core ℂ (CuspForm Γ k)).inner f g =
      peterssonInnerFd f g := (rfl)

end IsArithmetic

end CuspForm
