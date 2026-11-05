/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Separated
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Complex.Weierstrass

/-!
# Weierstrass preparation and division in holomorphic stalks

Let `E` be a complex normed space, `x₀ : E`, and `w₀ : ℂ`. Write `𝒪_{E, x₀}` and
`𝒪_{E × ℂ, (x₀, w₀)}` for the stalks of `holomorphicStructureSheaf` at `x₀` and `(x₀, w₀)`. This
file connects the local analytic Weierstrass preparation and division theorems on `E × ℂ`
(`AnalyticAt.exists_weierstrassPreparation`, `AnalyticAt.exists_weierstrassDivision`) with
Mathlib's formal power series Weierstrass API (`PowerSeries.IsWeierstrassFactorization`,
`PowerSeries.IsWeierstrassDivision`) and deduces uniqueness, polynomial divisibility reflection,
polynomial quotient isomorphisms, and flatness and finiteness of local hypersurface quotients over
the base stalk.

## Main definitions

* `TauCeti.holomorphicStructureSheaf.evalVertical`: evaluates a polynomial over `𝒪_{E, x₀}` as a
  holomorphic germ at `(x₀, w₀)` by pulling coefficients back along `Prod.fst` and substituting the
  centered vertical coordinate germ `p ↦ p.2 - w₀`.
* `TauCeti.holomorphicStructureSheaf.verticalPowerSeries`: expands a holomorphic germ at `(x₀, w₀)`
  as a formal power series over `𝒪_{E, x₀}` in `w - w₀` via iterated vertical derivatives.
* `TauCeti.holomorphicStructureSheaf.quotientEquivOfIsDistinguishedAt`: for
  `[FiniteDimensional ℂ E]` and a distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]`, the canonical
  ring isomorphism
  `(𝒪_{E, x₀})[X] ⧸ Ideal.span {P} ≃+* 𝒪_{E × ℂ, (x₀, w₀)} ⧸ Ideal.span {evalVertical x₀ w₀ P}`.
* `TauCeti.holomorphicStructureSheaf.weierstrassQuotientEquiv`: the induced ring isomorphism
  `(𝒪_{E, x₀})[X] ⧸ Ideal.span {P} ≃+* 𝒪_{E × ℂ, (x₀, w₀)} ⧸ Ideal.span {f}` for a Weierstrass
  factorization `f = evalVertical x₀ w₀ P * u`.

## Main results

* `TauCeti.holomorphicStructureSheaf.verticalPowerSeries_injective`: vertical Taylor expansion is
  injective (with no finite-dimensionality assumption on `E`).
* `TauCeti.holomorphicStructureSheaf.order_map_residue_verticalPowerSeries`: the formal order of
  the residue-field reduction of `verticalPowerSeries x₀ w₀ g` equals the analytic order of the
  vertical slice `w ↦ G (x₀, w)` at `w₀`.
* `TauCeti.holomorphicStructureSheaf.isWeierstrassFactorization_verticalPowerSeries_iff`,
  `TauCeti.holomorphicStructureSheaf.isWeierstrassDivision_verticalPowerSeries_iff`: alignment of
  holomorphic germ factorizations and divisions with `PowerSeries.IsWeierstrassFactorization` and
  `PowerSeries.IsWeierstrassDivision`.
* `TauCeti.holomorphicStructureSheaf.weierstrassPreparation_unique`,
  `TauCeti.holomorphicStructureSheaf.weierstrassDivision_unique`: uniqueness of Weierstrass
  preparation and division in `𝒪_{E × ℂ, (x₀, w₀)}` (without `FiniteDimensional ℂ E`, deduced from
  maximal-ideal Hausdorffness via `PowerSeries.IsWeierstrassFactorization.elim` and
  `PowerSeries.IsWeierstrassDivision.elim`).
* `TauCeti.holomorphicStructureSheaf.evalVertical_dvd_iff_of_isDistinguishedAt`: divisibility by a
  distinguished polynomial `P` in `(𝒪_{E, x₀})[X]` agrees with divisibility by
  `evalVertical x₀ w₀ P` in `𝒪_{E × ℂ, (x₀, w₀)}`.
* `TauCeti.holomorphicStructureSheaf.existsUnique_weierstrassPreparation`,
  `TauCeti.holomorphicStructureSheaf.existsUnique_weierstrassPreparation_of_analyticOrderAt`,
  `TauCeti.holomorphicStructureSheaf.existsUnique_weierstrassDivision_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.existsUnique_weierstrassDivision`: existence and uniqueness of
  Weierstrass preparation and division on finite-dimensional holomorphic stalks.
* `TauCeti.holomorphicStructureSheaf.flat_quotientMk_comp_stalkPrecomp_fst`,
  `TauCeti.holomorphicStructureSheaf.finite_quotientMk_comp_stalkPrecomp_fst`: any hypersurface
  germ whose vertical slice does not vanish identically defines a flat and finite algebra over the
  base stalk `𝒪_{E, x₀}`.

## Attribution

The alignment with formal power series and polynomial quotient comparison builds on Jz Pan's
formalization of formal Weierstrass preparation and division
(`Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`), in particular its `IsHausdorff`
uniqueness theorems and `Polynomial.IsDistinguishedAt.algEquivQuotient`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §1.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
-/

public noncomputable section

open CategoryTheory Filter Function Metric Polynomial Topology
open scoped ContDiff Manifold PowerSeries

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Vertical polynomial evaluation -/

/-- Evaluates a polynomial over `(holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀` as a
holomorphic germ on `E × ℂ` at `(x₀, w₀)`, pulling coefficients back along `Prod.fst` and
sending `X` to the centered vertical coordinate germ `p ↦ p.2 - w₀`. -/
def evalVertical (x₀ : E) (w₀ : ℂ) :
    ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] →+*
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) :=
  Polynomial.eval₂RingHom
    (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst (contMDiff_iff_contDiff.2 contDiff_fst) (x₀, w₀))
    (germOfContMDiff (fun p : E × ℂ ↦ p.2 - w₀)
      (contMDiff_iff_contDiff.2 (contDiff_snd.sub contDiff_const)) (x₀, w₀))

@[simp]
theorem evalVertical_C (x₀ : E) (w₀ : ℂ)
    (a : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) :
    evalVertical x₀ w₀ (Polynomial.C a) =
      stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst
        (contMDiff_iff_contDiff.2 contDiff_fst) (x₀, w₀) a :=
  Polynomial.eval₂_C _ _

@[simp]
theorem evalVertical_X (x₀ : E) (w₀ : ℂ) :
    evalVertical x₀ w₀ Polynomial.X =
      germOfContMDiff (fun p : E × ℂ ↦ p.2 - w₀)
        (contMDiff_iff_contDiff.2 (contDiff_snd.sub contDiff_const)) (x₀, w₀) :=
  Polynomial.eval₂_X _ _

theorem evalVertical_monomial (x₀ : E) (w₀ : ℂ) (n : ℕ)
    (a : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) :
    evalVertical x₀ w₀ (Polynomial.monomial n a) =
      stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst
          (contMDiff_iff_contDiff.2 contDiff_fst) (x₀, w₀) a *
        germOfContMDiff (fun p : E × ℂ ↦ p.2 - w₀)
          (contMDiff_iff_contDiff.2 (contDiff_snd.sub contDiff_const)) (x₀, w₀) ^ n :=
  Polynomial.eval₂_monomial _ _

/-- Evaluating `evalVertical x₀ w₀ P` at `(x₀, w₀)` evaluates the constant term of `P` at `x₀`. -/
@[simp]
theorem eval_evalVertical (x₀ : E) (w₀ : ℂ)
    (P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    eval 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (evalVertical x₀ w₀ P) =
      eval 𝓘(ℂ, E) E x₀ (P.coeff 0) := by
  have heq : (eval 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀)).comp (evalVertical x₀ w₀) =
      (eval 𝓘(ℂ, E) E x₀).comp Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext'
    · ext a
      simp [eval_stalkPrecomp]
    · simp
  exact RingHom.congr_fun heq P

/-- If `C i` represents `c i` near `x₀`, then `(x, w) ↦ ∑ i, C i x * (w - w₀) ^ i` represents
`evalVertical x₀ w₀ (∑ i, monomial i (c i))` near `(x₀, w₀)`. -/
theorem toFilterGerm_evalVertical_sum_monomial {x₀ : E} {w₀ : ℂ} {d : ℕ}
    {c : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀}
    {C : Fin d → E → ℂ}
    (hC : ∀ i, toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl (c i) = C i) :
    toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
        (evalVertical x₀ w₀ (∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i))) =
      (fun p : E × ℂ ↦ ∑ i : Fin d, C i p.1 * (p.2 - w₀) ^ (i : ℕ)) := by
  simp only [map_sum, evalVertical_monomial, map_mul, map_pow, toFilterGerm_stalkPrecomp, hC,
    toFilterGerm_germOfContMDiff, Germ.coe_compTendsto, ← Germ.coe_pow, ← Germ.coe_mul]
  exact (map_sum (Germ.coeAddHom (M := ℂ) (𝓝 (x₀, w₀))) _ Finset.univ).symm.trans
    (congrArg _ (funext fun _ ↦ by simp [Function.comp_apply]))

/-- If `C i` represents `c i` near `x₀`, then `(x, w) ↦ (monicOfCoeff (C · x)).eval (w - w₀)`
represents `evalVertical x₀ w₀ (monicOfCoeff c)` near `(x₀, w₀)`. -/
theorem toFilterGerm_evalVertical_monicOfCoeff {x₀ : E} {w₀ : ℂ} {d : ℕ}
    {c : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀}
    {C : Fin d → E → ℂ}
    (hC : ∀ i, toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl (c i) = C i) :
    toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
        (evalVertical x₀ w₀ (TauCeti.Polynomial.monicOfCoeff c)) =
      (fun p : E × ℂ ↦ (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C i p.1)).eval (p.2 - w₀)) := by
  have heval : evalVertical x₀ w₀ (TauCeti.Polynomial.monicOfCoeff c) =
      evalVertical x₀ w₀ Polynomial.X ^ d +
        evalVertical x₀ w₀ (∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i)) := by
    simp [evalVertical, Polynomial.eval₂_eq_eval_map, TauCeti.Polynomial.eval_monicOfCoeff]
  rw [heval, map_add, map_pow, evalVertical_X, toFilterGerm_germOfContMDiff,
    toFilterGerm_evalVertical_sum_monomial hC, ← Germ.coe_pow, ← Germ.coe_add]
  exact congrArg _ (funext fun _ ↦ (TauCeti.Polynomial.eval_monicOfCoeff _ _).symm)

/-- A monic polynomial `monicOfCoeff c` over `𝒪_{E, x₀}` is distinguished at the maximal ideal if
and only if all lower coefficient germs `c i` vanish at `x₀`. -/
theorem isDistinguishedAt_monicOfCoeff_iff {x₀ : E} {d : ℕ}
    (c : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) :
    (TauCeti.Polynomial.monicOfCoeff c).IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ↔
      ∀ i, eval 𝓘(ℂ, E) E x₀ (c i) = 0 := by
  refine ⟨fun h i ↦ ?_, fun hc ↦ ⟨⟨fun {n} hn ↦ ?_⟩, TauCeti.Polynomial.monic_monicOfCoeff c⟩⟩
  · have hmem := h.mem (n := (i : ℕ)) (by simp [i.2])
    rwa [TauCeti.Polynomial.coeff_monicOfCoeff, maximalIdeal_stalk, RingHom.mem_ker] at hmem
  · rw [TauCeti.Polynomial.natDegree_monicOfCoeff] at hn
    rw [maximalIdeal_stalk, RingHom.mem_ker, ← Fin.val_mk hn,
      TauCeti.Polynomial.coeff_monicOfCoeff]
    exact hc ⟨n, hn⟩

/-! ### Vertical Taylor expansion -/

private theorem exists_verticalCoeffFun (x₀ : E) (w₀ : ℂ) (n : ℕ)
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    ∃ c : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀,
      toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl c =
        (fun x : E ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n
          (fun w ↦ Classical.choose (exists_analyticAt_toFilterGerm_eq (x₀, w₀) g) (x, w)) w₀) :=
  exists_toFilterGerm_nhds_eq_iff_analyticAt.2 <|
    (analyticAt_const : AnalyticAt ℂ (fun _ : E ↦ (n.factorial : ℂ)⁻¹) x₀).fun_mul <|
      (Classical.choose_spec (exists_analyticAt_toFilterGerm_eq (x₀, w₀) g)).1
        |>.curry_left_iteratedDeriv_snd n

private def verticalCoeffFun (x₀ : E) (w₀ : ℂ) (n : ℕ)
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀ :=
  Classical.choose (exists_verticalCoeffFun x₀ w₀ n g)

private theorem toFilterGerm_verticalCoeffFun {x₀ : E} {w₀ : ℂ}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {G : E × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl g = G) (n : ℕ) :
    toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl (verticalCoeffFun x₀ w₀ n g) =
      (fun x : E ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ G (x, w)) w₀) := by
  have hspec := Classical.choose_spec (exists_verticalCoeffFun x₀ w₀ n g)
  have hG₀ := (Classical.choose_spec (exists_analyticAt_toFilterGerm_eq (x₀, w₀) g)).2 _ le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Germ.coe_eq.1 (hG₀.symm.trans hgG))
  refine hspec.trans (Germ.coe_eq.2 ?_)
  filter_upwards [ball_mem_nhds x₀ hδ] with x hx
  have hslice : (fun w ↦ Classical.choose (exists_analyticAt_toFilterGerm_eq (x₀, w₀) g) (x, w))
      =ᶠ[𝓝 w₀] fun w ↦ G (x, w) := by
    filter_upwards [ball_mem_nhds w₀ hδ] with w hw
    exact hball (ball_prod_same x₀ w₀ δ ▸ ⟨hx, hw⟩)
  rw [hslice.iteratedDeriv_eq n]

/-- Expands a holomorphic germ at `(x₀, w₀)` on `E × ℂ` as a formal power series in `w - w₀` over
the base stalk `(holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀`, sending `g` to
`∑ n, ((n!)⁻¹ · ∂_w^n g(·, w₀)) X ^ n`. -/
def verticalPowerSeries (x₀ : E) (w₀ : ℂ) :
    (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) →+*
      ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)⟦X⟧ where
  toFun g := PowerSeries.mk fun n ↦ verticalCoeffFun x₀ w₀ n g
  map_one' := by
    ext n; apply toFilterGerm_nhds_injective x₀
    rw [PowerSeries.coeff_mk,
      toFilterGerm_verticalCoeffFun (G := fun _ ↦ 1) (by rw [map_one]; rfl) n]
    rcases n with _ | n <;> simp [iteratedDeriv_const] <;> rfl
  map_mul' g₁ g₂ := by
    obtain ⟨G₁, hG₁_an, hG₁⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g₁
    obtain ⟨G₂, hG₂_an, hG₂⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g₂
    ext n; apply toFilterGerm_nhds_injective x₀
    rw [PowerSeries.coeff_mk,
      toFilterGerm_verticalCoeffFun (by rw [map_mul, hG₁, hG₂, ← Germ.coe_mul]) n,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i _ * PowerSeries.coeff j _) n, map_sum]
    simp only [PowerSeries.coeff_mk, map_mul, toFilterGerm_verticalCoeffFun (hG₁ _ le_rfl),
      toFilterGerm_verticalCoeffFun (hG₂ _ le_rfl), ← Germ.coe_mul]
    refine (Germ.coe_eq.2 ?_).trans
      (map_sum (Germ.coeAddHom (M := ℂ) (𝓝 x₀)) _ (Finset.range n.succ))
    filter_upwards [((by fun_prop : Continuous fun x : E ↦ (x, w₀)).tendsto x₀).eventually
      (hG₁_an.eventually_analyticAt.and hG₂_an.eventually_analyticAt)] with x ⟨h₁, h₂⟩
    simp only [Pi.mul_apply, Finset.sum_apply]
    rw [iteratedDeriv_fun_mul (h₁.curry_right.contDiffAt.of_le le_top)
      (h₂.curry_right.contDiffAt.of_le le_top), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hle := Finset.mem_range_succ_iff.1 hi
    have hfac : (n.factorial : ℂ) =
        (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hle).symm
    rw [hfac, mul_inv, mul_inv]
    linear_combination
      (iteratedDeriv i (fun w ↦ G₁ (x, w)) w₀ * iteratedDeriv (n - i) (fun w ↦ G₂ (x, w)) w₀ *
        (i.factorial : ℂ)⁻¹ * ((n - i).factorial : ℂ)⁻¹) *
        inv_mul_cancel₀ (a := (n.choose i : ℂ)) (Nat.cast_ne_zero.2 (Nat.choose_pos hle).ne')
  map_zero' := by
    ext n; apply toFilterGerm_nhds_injective x₀
    rw [PowerSeries.coeff_mk,
      toFilterGerm_verticalCoeffFun (G := fun _ ↦ 0) (by rw [map_zero]; rfl) n, map_zero]
    simp; rfl
  map_add' g₁ g₂ := by
    obtain ⟨G₁, hG₁_an, hG₁⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g₁
    obtain ⟨G₂, hG₂_an, hG₂⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g₂
    ext n; apply toFilterGerm_nhds_injective x₀
    rw [PowerSeries.coeff_mk,
      toFilterGerm_verticalCoeffFun (by rw [map_add, hG₁, hG₂, ← Germ.coe_add]) n,
      map_add, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      toFilterGerm_verticalCoeffFun (hG₁ _ le_rfl) n,
      toFilterGerm_verticalCoeffFun (hG₂ _ le_rfl) n, ← Germ.coe_add, Germ.coe_eq]
    filter_upwards [((by fun_prop : Continuous fun x : E ↦ (x, w₀)).tendsto x₀).eventually
      (hG₁_an.eventually_analyticAt.and hG₂_an.eventually_analyticAt)] with x ⟨h₁, h₂⟩
    simp only [Pi.add_apply]
    rw [iteratedDeriv_fun_add (h₁.curry_right.contDiffAt.of_le le_top)
      (h₂.curry_right.contDiffAt.of_le le_top), mul_add]

/-- If `G` represents `g` near `(x₀, w₀)`, then `x ↦ (n!)⁻¹ * iteratedDeriv n (G (x, ·)) w₀`
represents the `n`-th coefficient of `verticalPowerSeries x₀ w₀ g` near `x₀`. -/
theorem toFilterGerm_coeff_verticalPowerSeries {x₀ : E} {w₀ : ℂ}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {G : E × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl g = G) (n : ℕ) :
    toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl
        (PowerSeries.coeff n (verticalPowerSeries x₀ w₀ g)) =
      (fun x : E ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ G (x, w)) w₀) := by
  simpa [verticalPowerSeries] using toFilterGerm_verticalCoeffFun hgG n

/-- Evaluating the constant coefficient of `verticalPowerSeries x₀ w₀ g` at `x₀` recovers the
value of `g` at `(x₀, w₀)`. -/
@[simp]
theorem eval_constantCoeff_verticalPowerSeries (x₀ : E) (w₀ : ℂ)
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    eval 𝓘(ℂ, E) E x₀ (PowerSeries.constantCoeff (verticalPowerSeries x₀ w₀ g)) =
      eval 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) g := by
  obtain ⟨G, -, hG⟩ := exists_toFilterGerm_eq (x₀, w₀) g
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    eval_eq_of_toFilterGerm_eq (toFilterGerm_coeff_verticalPowerSeries (hG _ le_rfl) 0),
    eval_eq_of_toFilterGerm_eq (hG _ le_rfl)]
  simp [iteratedDeriv_zero]

/-- Pulling a base germ back along `Prod.fst` sends it to a constant vertical power series. -/
@[simp]
theorem verticalPowerSeries_stalkPrecomp_fst (x₀ : E) (w₀ : ℂ)
    (hf : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    (a : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) :
    verticalPowerSeries x₀ w₀ (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hf (x₀, w₀) a) =
      PowerSeries.C a := by
  obtain ⟨A, -, hA⟩ := exists_toFilterGerm_eq x₀ a
  have hpre : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hf (x₀, w₀) a) = (fun p : E × ℂ ↦ A p.1) := by
    rw [toFilterGerm_stalkPrecomp, hA _ le_rfl, Germ.coe_compTendsto]; rfl
  ext n; apply toFilterGerm_nhds_injective x₀
  rw [toFilterGerm_coeff_verticalPowerSeries hpre n]
  rcases n with _ | n
  · simp [iteratedDeriv_zero, hA _ le_rfl]
  · simp [iteratedDeriv_const]; rfl

/-- The vertical power series of `evalVertical x₀ w₀ P` is `P` viewed as a power series. -/
@[simp]
theorem verticalPowerSeries_evalVertical (x₀ : E) (w₀ : ℂ)
    (P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P) = P := by
  have heq : (verticalPowerSeries x₀ w₀).comp (evalVertical x₀ w₀) =
      Polynomial.coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext fun a ↦ ?_) ?_
    · simpa only [RingHom.comp_apply, evalVertical_C, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C] using verticalPowerSeries_stalkPrecomp_fst x₀ w₀ _ a
    · simp only [RingHom.comp_apply, evalVertical_X, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_X]
      ext n; apply toFilterGerm_nhds_injective x₀
      rw [toFilterGerm_coeff_verticalPowerSeries (toFilterGerm_germOfContMDiff _ _ le_rfl) n,
        PowerSeries.coeff_X]
      rcases n with _ | _ | n
      · simp [iteratedDeriv_zero]; rfl
      · simp [iteratedDeriv_succ', iteratedDeriv_zero]; rfl
      · simp [iteratedDeriv_succ', deriv_sub_const_fun, deriv_id'', iteratedDeriv_const]; rfl
  exact RingHom.congr_fun heq P

/-- Vertical Taylor expansion at `(x₀, w₀)` is injective (without assuming finite-dimensionality
of `E`). -/
theorem verticalPowerSeries_injective (x₀ : E) (w₀ : ℂ) :
    Injective (verticalPowerSeries x₀ w₀) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨G, hG_an, hG⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℂ G) (x₀, w₀) hG_an
  have hmem {x : E} {w : ℂ} (hx : x ∈ ball x₀ r) (hw : w ∈ ball w₀ r) :
      (x, w) ∈ ball (x₀, w₀) r := ball_prod_same x₀ w₀ r ▸ ⟨hx, hw⟩
  have hcoeff_zero (n : ℕ) {x : E} (hx : x ∈ ball x₀ r) :
      iteratedDeriv n (fun w ↦ G (x, w)) w₀ = 0 := by
    have han_n : AnalyticOnNhd ℂ
        (fun x : E ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ G (x, w)) w₀) (ball x₀ r) :=
      fun x hx ↦ analyticAt_const.fun_mul
        ((hball (hmem hx (mem_ball_self hr))).curry_left_iteratedDeriv_snd n)
    have hev_n : (fun x : E ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ G (x, w)) w₀)
        =ᶠ[𝓝 x₀] 0 := Germ.coe_eq.1
      ((toFilterGerm_coeff_verticalPowerSeries (hG _ le_rfl) n).symm.trans
        (by rw [hg, map_zero, map_zero]; rfl))
    exact (mul_eq_zero.1 (han_n.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x₀ r).isPreconnected (mem_ball_self hr) hev_n hx)).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero))
  apply toFilterGerm_nhds_injective (x₀, w₀)
  rw [hG, map_zero, ← Germ.coe_zero, Germ.coe_eq]
  filter_upwards [ball_mem_nhds (x₀, w₀) hr] with ⟨x, w⟩ hxw
  obtain ⟨hx, hw⟩ : x ∈ ball x₀ r ∧ w ∈ ball w₀ r := by rwa [← ball_prod_same] at hxw
  have hslice_an : AnalyticOnNhd ℂ (fun ζ ↦ G (x, ζ)) (ball w₀ r) :=
    fun ζ hζ ↦ (hball (hmem hx hζ)).curry_right
  have hslice_ev : ∀ᶠ ζ in 𝓝 w₀, G (x, ζ) = 0 := by
    rw [← analyticOrderAt_eq_top]
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
    exact (Nat.lt_succ_self m).not_ge <| ENat.natCast_le_natCast.1 <| hm ▸
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (hslice_an w₀ (mem_ball_self hr))).2 fun i _ ↦ hcoeff_zero i hx
  exact hslice_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball w₀ r).isPreconnected (mem_ball_self hr) hslice_ev hw

/-- Polynomial evaluation `evalVertical x₀ w₀` is injective. -/
theorem evalVertical_injective (x₀ : E) (w₀ : ℂ) : Injective (evalVertical x₀ w₀) :=
  fun P Q hPQ ↦ Polynomial.coe_inj.1 <|
    (verticalPowerSeries_evalVertical x₀ w₀ P).symm.trans <|
      (congrArg (verticalPowerSeries x₀ w₀) hPQ).trans (verticalPowerSeries_evalVertical x₀ w₀ Q)

/-- A holomorphic germ is a unit if and only if its vertical power series is a unit. -/
@[simp]
theorem isUnit_verticalPowerSeries_iff (x₀ : E) (w₀ : ℂ)
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    IsUnit (verticalPowerSeries x₀ w₀ g) ↔ IsUnit g := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_stalk_iff, isUnit_stalk_iff,
    eval_constantCoeff_verticalPowerSeries]

/-- The formal order of the residue-field reduction of `verticalPowerSeries x₀ w₀ g` equals the
analytic order of the vertical slice `w ↦ G (x₀, w)` at `w₀` for any representative `G` of `g`. -/
theorem order_map_residue_verticalPowerSeries {x₀ : E} {w₀ : ℂ}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {G : E × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl g = G) :
    ((verticalPowerSeries x₀ w₀ g).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))).order =
      analyticOrderAt (fun w ↦ G (x₀, w)) w₀ := by
  have hslice_an : AnalyticAt ℂ (fun w ↦ G (x₀, w)) w₀ :=
    (exists_toFilterGerm_nhds_eq_iff_analyticAt.1 ⟨g, hgG⟩).curry_right
  have hle_iff (n : ℕ) :
      (n : ℕ∞) ≤ ((verticalPowerSeries x₀ w₀ g).map (IsLocalRing.residue _)).order ↔
        (n : ℕ∞) ≤ analyticOrderAt (fun w ↦ G (x₀, w)) w₀ := by
    rw [PowerSeries.nat_le_order_iff,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hslice_an]
    refine forall₂_congr fun i _ ↦ ?_
    rw [PowerSeries.coeff_map, ← (residueFieldEquiv 𝓘(ℂ, E) E x₀).injective.eq_iff, map_zero,
      residueFieldEquiv_residue,
      eval_eq_of_toFilterGerm_eq (toFilterGerm_coeff_verticalPowerSeries hgG i), mul_eq_zero,
      or_iff_right (inv_ne_zero (Nat.cast_ne_zero.2 i.factorial_ne_zero))]
  exact ENat.eq_of_forall_natCast_le_iff hle_iff

/-- The residue-field reduction of `verticalPowerSeries x₀ w₀ g` is nonzero if and only if the
vertical slice `w ↦ G (x₀, w)` has finite analytic order at `w₀`. -/
theorem map_residue_verticalPowerSeries_ne_zero_iff {x₀ : E} {w₀ : ℂ}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {G : E × ℂ → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl g = G) :
    (verticalPowerSeries x₀ w₀ g).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 ↔
      analyticOrderAt (fun w ↦ G (x₀, w)) w₀ ≠ ⊤ := by
  rw [← PowerSeries.order_finite_iff_ne_zero, lt_top_iff_ne_top,
    order_map_residue_verticalPowerSeries hgG]

/-! ### Alignment with `PowerSeries` and uniqueness -/

/-- A holomorphic germ factorization `g = evalVertical x₀ w₀ P * u` is a Weierstrass factorization
in the formal power series sense if and only if `P` is distinguished at the maximal ideal of
`𝒪_{E, x₀}` and `u` is a unit of `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem isWeierstrassFactorization_verticalPowerSeries_iff {x₀ : E} {w₀ : ℂ}
    {g u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]} :
    (verticalPowerSeries x₀ w₀ g).IsWeierstrassFactorization P (verticalPowerSeries x₀ w₀ u) ↔
      P.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        IsUnit u ∧ g = evalVertical x₀ w₀ P * u := by
  rw [PowerSeries.IsWeierstrassFactorization, PowerSeries.isWeierstrassFactorizationAt_iff,
    isUnit_verticalPowerSeries_iff, ← verticalPowerSeries_evalVertical x₀ w₀ P, ← map_mul,
    (verticalPowerSeries_injective x₀ w₀).eq_iff]

/-- A holomorphic germ division `g = f * q + evalVertical x₀ w₀ r` is a Weierstrass division in the
formal power series sense if and only if `r` has degree strictly less than the residue-field order
of `verticalPowerSeries x₀ w₀ f`. -/
theorem isWeierstrassDivision_verticalPowerSeries_iff {x₀ : E} {w₀ : ℂ}
    {f g q : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {r : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]} :
    (verticalPowerSeries x₀ w₀ g).IsWeierstrassDivision
        (verticalPowerSeries x₀ w₀ f) (verticalPowerSeries x₀ w₀ q) r ↔
      r.degree <
          (((verticalPowerSeries x₀ w₀ f).map
            (IsLocalRing.residue _)).order.toNat : WithBot ℕ) ∧
        g = f * q + evalVertical x₀ w₀ r := by
  rw [PowerSeries.IsWeierstrassDivision, PowerSeries.isWeierstrassDivisionAt_iff,
    ← verticalPowerSeries_evalVertical x₀ w₀ r, ← map_mul, ← map_add,
    (verticalPowerSeries_injective x₀ w₀).eq_iff]
  rfl

/-- **Uniqueness of Weierstrass preparation in holomorphic stalks** (without assuming
finite-dimensionality of `E`). -/
theorem weierstrassPreparation_unique {x₀ : E} {w₀ : ℂ}
    {g u u' : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P P' : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hg : g = evalVertical x₀ w₀ P * u)
    (hP' : P'.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu' : IsUnit u') (hg' : g = evalVertical x₀ w₀ P' * u') :
    P = P' ∧ u = u' := by
  have H₁ := isWeierstrassFactorization_verticalPowerSeries_iff.2 ⟨hP, hu, hg⟩
  have H₂ := isWeierstrassFactorization_verticalPowerSeries_iff.2 ⟨hP', hu', hg'⟩
  obtain ⟨hPP', huu'⟩ := H₁.elim H₂
  exact ⟨hPP', verticalPowerSeries_injective x₀ w₀ huu'⟩

/-- **Uniqueness of Weierstrass division in holomorphic stalks** (without assuming
finite-dimensionality of `E`). -/
theorem weierstrassDivision_unique {x₀ : E} {w₀ : ℂ}
    {f g q q' : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {r r' : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0)
    (hr : r.degree < (((verticalPowerSeries x₀ w₀ f).map (IsLocalRing.residue _)).order.toNat :
      WithBot ℕ))
    (hg : g = f * q + evalVertical x₀ w₀ r)
    (hr' : r'.degree < (((verticalPowerSeries x₀ w₀ f).map (IsLocalRing.residue _)).order.toNat :
      WithBot ℕ))
    (hg' : g = f * q' + evalVertical x₀ w₀ r') :
    q = q' ∧ r = r' := by
  have H₁ := isWeierstrassDivision_verticalPowerSeries_iff.2 ⟨hr, hg⟩
  have H₂ := isWeierstrassDivision_verticalPowerSeries_iff.2 ⟨hr', hg'⟩
  obtain ⟨hqq', hrr'⟩ := H₁.elim hf H₂
  exact ⟨verticalPowerSeries_injective x₀ w₀ hqq', hrr'⟩

/-- For a distinguished polynomial `P` over `𝒪_{E, x₀}`, the residue-field reduction of
`verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)` has formal order `P.natDegree`. -/
theorem order_map_residue_verticalPowerSeries_evalVertical_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    ((verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))).order =
      P.natDegree := by
  have h1 : (verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)).IsWeierstrassFactorization P 1 := by
    refine ⟨hP, isUnit_one, ?_⟩
    rw [verticalPowerSeries_evalVertical, mul_one]
  exact (hP.coe_natDegree_eq_order_map _ 1 (by simp) h1.eq_mul).symm

/-- For a distinguished polynomial `P` over `𝒪_{E, x₀}`, the residue-field reduction of
`verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)` is nonzero. -/
theorem map_residue_verticalPowerSeries_evalVertical_ne_zero_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  have h1 : (verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)).IsWeierstrassFactorization P 1 :=
    ⟨hP, isUnit_one, by rw [verticalPowerSeries_evalVertical, mul_one]⟩
  exact h1.map_ne_zero

/-- Uniqueness of Weierstrass division by `evalVertical x₀ w₀ P` for a distinguished polynomial
`P` (without assuming finite-dimensionality of `E`). -/
theorem weierstrassDivision_unique_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    {g q q' : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {r r' : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hr : r.degree < P.natDegree) (hg : g = evalVertical x₀ w₀ P * q + evalVertical x₀ w₀ r)
    (hr' : r'.degree < P.natDegree) (hg' : g = evalVertical x₀ w₀ P * q' + evalVertical x₀ w₀ r') :
    q = q' ∧ r = r' := by
  have hord : ((verticalPowerSeries x₀ w₀ (evalVertical x₀ w₀ P)).map
      (IsLocalRing.residue _)).order.toNat = P.natDegree := by
    rw [order_map_residue_verticalPowerSeries_evalVertical_of_isDistinguishedAt hP,
      ENat.toNat_natCast]
  exact weierstrassDivision_unique
    (map_residue_verticalPowerSeries_evalVertical_ne_zero_of_isDistinguishedAt hP)
    (by rwa [hord]) hg (by rwa [hord]) hg'

/-- A distinguished polynomial `P` over `𝒪_{E, x₀}` divides a polynomial `Q` in `(𝒪_{E, x₀})[X]`
if and only if `evalVertical x₀ w₀ P` divides `evalVertical x₀ w₀ Q` in `𝒪_{E × ℂ, (x₀, w₀)}`
(without assuming finite-dimensionality of `E`). -/
theorem evalVertical_dvd_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    P ∣ Q ↔ evalVertical x₀ w₀ P ∣ evalVertical x₀ w₀ Q := by
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨evalVertical x₀ w₀ S, by rw [hS, map_mul]⟩, fun ⟨q, hq⟩ ↦ ?_⟩
  have hr0 : Q %ₘ P = 0 := (weierstrassDivision_unique_of_isDistinguishedAt hP
    (by simpa only [degree_eq_natDegree hP.monic.ne_zero] using
      Polynomial.degree_modByMonic_lt Q hP.monic)
    (by rw [← map_mul, ← map_add, add_comm, Polynomial.modByMonic_add_div Q])
    (by simp) (by rw [map_zero, add_zero, hq])).2
  exact ⟨Q /ₘ P, by simpa [hr0] using (Polynomial.modByMonic_add_div Q P).symm⟩

/-! ### Existence, uniqueness, quotients, and flatness in finite dimension -/

section FiniteDimensional

variable [FiniteDimensional ℂ E]

/-- **Weierstrass preparation in holomorphic stalks (explicit degree form).** When a representative
`F` of `f` has vertical slice `w ↦ F (x₀, w)` of analytic order `d` at `w₀`, there exist unique
coefficient germs `c : Fin d → 𝒪_{E, x₀}` vanishing at `x₀` and unit germ `u ∈ 𝒪_{E × ℂ, (x₀, w₀)}`
such that `f = evalVertical x₀ w₀ (monicOfCoeff c) * u`. -/
theorem existsUnique_weierstrassPreparation_of_analyticOrderAt {x₀ : E} {w₀ : ℂ} {d : ℕ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {F : E × ℂ → ℂ}
    (hfF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl f = F)
    (hd : analyticOrderAt (fun w ↦ F (x₀, w)) w₀ = d) :
    ∃! cu : (Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) ×
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      (∀ i, eval 𝓘(ℂ, E) E x₀ (cu.1 i) = 0) ∧ IsUnit cu.2 ∧
        f = evalVertical x₀ w₀ (TauCeti.Polynomial.monicOfCoeff cu.1) * cu.2 := by
  have hF_an : AnalyticAt ℂ F (x₀, w₀) :=
    exists_toFilterGerm_nhds_eq_iff_analyticAt.1 ⟨f, hfF⟩
  obtain ⟨C, U, hC_an, hC0, hU_an, hU0, hfac⟩ := hF_an.exists_weierstrassPreparation hd
  let c : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀ :=
    fun i ↦ Classical.choose (exists_toFilterGerm_eq_of_analyticAt (hC_an i))
  have hc_germ (i : Fin d) : toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl (c i) = C i :=
    Classical.choose_spec (exists_toFilterGerm_eq_of_analyticAt (hC_an i)) _ le_rfl
  obtain ⟨u, hu_germ⟩ := exists_toFilterGerm_eq_of_analyticAt hU_an
  have hc_eval (i : Fin d) : eval 𝓘(ℂ, E) E x₀ (c i) = 0 :=
    (eval_eq_of_toFilterGerm_eq (hc_germ i)).trans (hC0 i)
  have hu_unit : IsUnit u :=
    (isUnit_stalk_iff 𝓘(ℂ, E × ℂ) (E × ℂ) u).2
      ((eval_eq_of_toFilterGerm_eq (hu_germ _ le_rfl)).symm ▸ hU0)
  have hf_eq : f = evalVertical x₀ w₀ (TauCeti.Polynomial.monicOfCoeff c) * u :=
    toFilterGerm_nhds_injective (x₀, w₀) <| by
      rw [hfF, map_mul, toFilterGerm_evalVertical_monicOfCoeff hc_germ, hu_germ, ← Germ.coe_mul,
        Germ.coe_eq]
      exact hfac
  refine ⟨(c, u), ⟨hc_eval, hu_unit, hf_eq⟩, fun ⟨c', u'⟩ ⟨hc'_eval, hu'_unit, hf'_eq⟩ ↦ ?_⟩
  obtain ⟨hP, hu⟩ := weierstrassPreparation_unique
    ((isDistinguishedAt_monicOfCoeff_iff c').2 hc'_eval) hu'_unit hf'_eq
    ((isDistinguishedAt_monicOfCoeff_iff c).2 hc_eval) hu_unit hf_eq
  exact Prod.ext ((TauCeti.Polynomial.monicOfCoeff_inj c' c).1 hP) hu

/-- **Weierstrass preparation theorem in holomorphic stalks.** Every holomorphic germ `f` at
`(x₀, w₀)` whose vertical power series has nonzero image in `(𝒪_{E, x₀} ⧸ 𝔪_{x₀})⟦X⟧` admits a
unique factorization `f = evalVertical x₀ w₀ P * u` into a distinguished polynomial `P` over
`𝒪_{E, x₀}` and a unit germ `u` at `(x₀, w₀)`. -/
theorem existsUnique_weierstrassPreparation {x₀ : E} {w₀ : ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0) :
    ∃! pu : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ×
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      pu.1.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        IsUnit pu.2 ∧ f = evalVertical x₀ w₀ pu.1 * pu.2 := by
  obtain ⟨F, -, hfF⟩ := exists_toFilterGerm_eq (x₀, w₀) f
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1
    ((map_residue_verticalPowerSeries_ne_zero_iff (hfF _ le_rfl)).1 hf)
  obtain ⟨⟨c, u⟩, ⟨hc0, hu, hfac⟩, _⟩ :=
    existsUnique_weierstrassPreparation_of_analyticOrderAt (hfF _ le_rfl) hd.symm
  refine ⟨(TauCeti.Polynomial.monicOfCoeff c, u),
    ⟨(isDistinguishedAt_monicOfCoeff_iff c).2 hc0, hu, hfac⟩,
    fun ⟨P', u'⟩ ⟨hP', hu', hfac'⟩ ↦ ?_⟩
  obtain ⟨hPP', huu'⟩ := weierstrassPreparation_unique hP' hu' hfac'
    ((isDistinguishedAt_monicOfCoeff_iff c).2 hc0) hu hfac
  exact Prod.ext hPP' huu'

/-- **Weierstrass division by a distinguished polynomial in holomorphic stalks.** Given a
distinguished polynomial `P` over `𝒪_{E, x₀}` and any germ `g` at `(x₀, w₀)`, there exist unique
`q ∈ 𝒪_{E × ℂ, (x₀, w₀)}` and `r ∈ (𝒪_{E, x₀})[X]` of degree `< P.natDegree` such that
`g = evalVertical x₀ w₀ P * q + evalVertical x₀ w₀ r`. -/
theorem existsUnique_weierstrassDivision_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    ∃! qr : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ×
        ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X],
      qr.2.degree < P.natDegree ∧ g = evalVertical x₀ w₀ P * qr.1 + evalVertical x₀ w₀ qr.2 := by
  set d := P.natDegree
  let c : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀ := fun i ↦ P.coeff i
  have hP_eq : TauCeti.Polynomial.monicOfCoeff c = P :=
    TauCeti.Polynomial.monicOfCoeff_coeff hP.monic rfl
  have hc0_germ : ∀ i : Fin d, eval 𝓘(ℂ, E) E x₀ (c i) = 0 :=
    (isDistinguishedAt_monicOfCoeff_iff c).1 (hP_eq.symm ▸ hP)
  let C : Fin d → E → ℂ := fun i ↦ Classical.choose (exists_analyticAt_toFilterGerm_eq x₀ (c i))
  have hC_spec := fun i : Fin d ↦ Classical.choose_spec (exists_analyticAt_toFilterGerm_eq x₀ (c i))
  obtain ⟨G, hG_an, hgG⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) g
  obtain ⟨Q, R, hQ_an, hR_an, hdiv⟩ := hG_an.exists_weierstrassDivision_monicOfCoeff
    (fun i ↦ (hC_spec i).1)
    (fun i ↦ (eval_eq_of_toFilterGerm_eq ((hC_spec i).2 _ le_rfl)).symm.trans (hc0_germ i))
  obtain ⟨q, hq_germ⟩ := exists_toFilterGerm_eq_of_analyticAt hQ_an
  let r_coeff : Fin d → (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀ :=
    fun i ↦ Classical.choose (exists_toFilterGerm_eq_of_analyticAt (hR_an i))
  have hr_germ (i : Fin d) : toFilterGerm 𝓘(ℂ, E) E x₀ (𝓝 x₀) le_rfl (r_coeff i) = R i :=
    Classical.choose_spec (exists_toFilterGerm_eq_of_analyticAt (hR_an i)) _ le_rfl
  let r : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] :=
    ∑ i : Fin d, Polynomial.monomial (i : ℕ) (r_coeff i)
  have hr_deg : r.degree < d := by
    simpa only [r, C_mul_X_pow_eq_monomial] using Polynomial.degree_sum_fin_lt r_coeff
  have hg_eq : g = evalVertical x₀ w₀ P * q + evalVertical x₀ w₀ r :=
    toFilterGerm_nhds_injective (x₀, w₀) <| by
      rw [hgG, ← hP_eq, map_add, map_mul,
        toFilterGerm_evalVertical_monicOfCoeff (fun i ↦ (hC_spec i).2 _ le_rfl), hq_germ,
        toFilterGerm_evalVertical_sum_monomial hr_germ, ← Germ.coe_mul, ← Germ.coe_add, Germ.coe_eq]
      exact hdiv
  refine ⟨(q, r), ⟨hr_deg, hg_eq⟩, fun ⟨q', r'⟩ ⟨hr'_deg, hg'_eq⟩ ↦ ?_⟩
  obtain ⟨hqq', hrr'⟩ := weierstrassDivision_unique_of_isDistinguishedAt hP hr'_deg hg'_eq
    hr_deg hg_eq
  exact Prod.ext hqq' hrr'

/-- **Weierstrass division theorem in holomorphic stalks.** Given germs `f` and `g` at `(x₀, w₀)`
such that the vertical power series of `f` has nonzero image in `(𝒪_{E, x₀} ⧸ 𝔪_{x₀})⟦X⟧`, there
exist unique `q ∈ 𝒪_{E × ℂ, (x₀, w₀)}` and `r ∈ (𝒪_{E, x₀})[X]` forming a Weierstrass division of
`g` by `f`. -/
theorem existsUnique_weierstrassDivision {x₀ : E} {w₀ : ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0)
    (g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
    ∃! qr : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ×
        ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X],
      (verticalPowerSeries x₀ w₀ g).IsWeierstrassDivision
        (verticalPowerSeries x₀ w₀ f) (verticalPowerSeries x₀ w₀ qr.1) qr.2 := by
  obtain ⟨⟨P, u⟩, ⟨hP, hu, hf_eq⟩, _⟩ := existsUnique_weierstrassPreparation hf
  have hH := isWeierstrassFactorization_verticalPowerSeries_iff.2 ⟨hP, hu, hf_eq⟩
  obtain ⟨⟨q₀, r⟩, ⟨hr_deg, hg_eq⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hP g
  obtain ⟨u_inv, hu_inv⟩ := hu.exists_right_inv
  have hdiv : (verticalPowerSeries x₀ w₀ g).IsWeierstrassDivision
      (verticalPowerSeries x₀ w₀ f) (verticalPowerSeries x₀ w₀ (u_inv * q₀)) r := by
    rw [isWeierstrassDivision_verticalPowerSeries_iff, ← hH.natDegree_eq_toNat_order_map]
    refine ⟨hr_deg, ?_⟩
    rw [hf_eq]
    linear_combination hg_eq - evalVertical x₀ w₀ P * q₀ * hu_inv
  refine ⟨(u_inv * q₀, r), hdiv, fun ⟨q', r'⟩ hdiv' ↦ ?_⟩
  obtain ⟨hr', hg'⟩ := isWeierstrassDivision_verticalPowerSeries_iff.1 hdiv'
  obtain ⟨hr₀, hg₀⟩ := isWeierstrassDivision_verticalPowerSeries_iff.1 hdiv
  obtain ⟨hqq', hrr'⟩ := weierstrassDivision_unique hf hr' hg' hr₀ hg₀
  exact Prod.ext hqq' hrr'

/-! ### Polynomial quotient isomorphism, flatness, and finiteness -/

/-- For a distinguished polynomial `P` over `𝒪_{E, x₀}`, evaluating polynomials vertically induces
a canonical ring isomorphism `(𝒪_{E, x₀})[X] ⧸ (P) ≃+* 𝒪_{E × ℂ, (x₀, w₀)} ⧸ (evalVertical P)`. -/
def quotientEquivOfIsDistinguishedAt (x₀ : E) (w₀ : ℂ)
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P}) ≃+*
      ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ⧸
        Ideal.span {evalVertical x₀ w₀ P}) := by
  refine RingEquiv.ofBijective (Ideal.Quotient.lift (Ideal.span {P})
    ((Ideal.Quotient.mk (Ideal.span {evalVertical x₀ w₀ P})).comp (evalVertical x₀ w₀))
    fun Q hQ ↦ Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <|
      (evalVertical_dvd_iff_of_isDistinguishedAt hP).1 (Ideal.mem_span_singleton.1 hQ)) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <|
      (evalVertical_dvd_iff_of_isDistinguishedAt hP).2 <| Ideal.mem_span_singleton.1 <|
        Ideal.Quotient.eq_zero_iff_mem.1 hx
  · intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨q, r⟩, ⟨_, hg_eq⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hP g
    exact ⟨Ideal.Quotient.mk _ r, by
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, hg_eq, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨q, rfl⟩), zero_add]⟩

@[simp]
theorem quotientEquivOfIsDistinguishedAt_mk (x₀ : E) (w₀ : ℂ)
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    quotientEquivOfIsDistinguishedAt x₀ w₀ hP (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (evalVertical x₀ w₀ Q) :=
  (rfl)

/-- If `g = evalVertical x₀ w₀ P * q + evalVertical x₀ w₀ r`, then the inverse of
`quotientEquivOfIsDistinguishedAt` maps the residue class of `g` to the residue class of `r`. -/
theorem quotientEquivOfIsDistinguishedAt_symm_mk_of_eq {x₀ : E} {w₀ : ℂ}
    {P r : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    {g q : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hg : g = evalVertical x₀ w₀ P * q + evalVertical x₀ w₀ r) :
    (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).symm (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ r :=
  (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).injective <| by
    rw [RingEquiv.apply_symm_apply, quotientEquivOfIsDistinguishedAt_mk, hg, map_add,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨q, rfl⟩), zero_add]

/-- Composing `quotientEquivOfIsDistinguishedAt` with the canonical `𝒪_{E, x₀}`-algebra map into
`(𝒪_{E, x₀})[X] ⧸ (P)` recovers pullback along `Prod.fst` followed by the quotient map. -/
theorem quotientEquivOfIsDistinguishedAt_comp_algebraMap {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (quotientEquivOfIsDistinguishedAt x₀ w₀ hP : _ →+* _).comp
        (algebraMap ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)
          (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P})) =
      (Ideal.Quotient.mk (Ideal.span {evalVertical x₀ w₀ P})).comp
        (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀)) := by
  ext a
  rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← Ideal.Quotient.mk_algebraMap,
    Polynomial.algebraMap_eq, quotientEquivOfIsDistinguishedAt_mk, evalVertical_C,
    RingHom.comp_apply]

/-- For a Weierstrass factorization `f = evalVertical x₀ w₀ P * u`, evaluating polynomials
vertically induces a canonical ring isomorphism
`(𝒪_{E, x₀})[X] ⧸ (P) ≃+* 𝒪_{E × ℂ, (x₀, w₀)} ⧸ (f)`. -/
def weierstrassQuotientEquiv {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P}) ≃+*
      ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ⧸
        Ideal.span {f}) :=
  (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).trans <|
    Ideal.quotEquivOfEq (by rw [hf, Ideal.span_singleton_mul_right_unit hu])

@[simp]
theorem weierstrassQuotientEquiv_mk {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u)
    (Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    weierstrassQuotientEquiv hP hu hf (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (evalVertical x₀ w₀ Q) :=
  (rfl)

/-- If `f = evalVertical x₀ w₀ P * u` is a Weierstrass factorization and
`g = f * q + evalVertical x₀ w₀ r`, then the inverse of `weierstrassQuotientEquiv` maps the residue
class of `g` to the residue class of `r`. -/
theorem weierstrassQuotientEquiv_symm_mk_of_eq {x₀ : E} {w₀ : ℂ}
    {f u g q : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P r : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u)
    (hg : g = f * q + evalVertical x₀ w₀ r) :
    (weierstrassQuotientEquiv hP hu hf).symm (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ r :=
  (weierstrassQuotientEquiv hP hu hf).injective <| by
    rw [RingEquiv.apply_symm_apply, weierstrassQuotientEquiv_mk, hg, map_add,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨q, rfl⟩), zero_add]

/-- Composing `weierstrassQuotientEquiv` with the canonical `𝒪_{E, x₀}`-algebra map into
`(𝒪_{E, x₀})[X] ⧸ (P)` recovers pullback along `Prod.fst` followed by the quotient map modulo
`f`. -/
theorem weierstrassQuotientEquiv_comp_algebraMap {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    (weierstrassQuotientEquiv hP hu hf : _ →+* _).comp
        (algebraMap ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)
          (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P})) =
      (Ideal.Quotient.mk (Ideal.span {f})).comp
        (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀)) := by
  ext a
  rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← Ideal.Quotient.mk_algebraMap,
    Polynomial.algebraMap_eq, weierstrassQuotientEquiv_mk, evalVertical_C, RingHom.comp_apply]

/-- Pullback along `Prod.fst` makes the local quotient `𝒪_{E × ℂ, (x₀, w₀)} ⧸ (evalVertical P)`
flat over the base stalk `𝒪_{E, x₀}` for every distinguished polynomial `P`. -/
theorem flat_quotientMk_comp_stalkPrecomp_fst_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    ((Ideal.Quotient.mk (Ideal.span {evalVertical x₀ w₀ P})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀))).Flat := by
  have : Module.Free ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)
      (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P}) :=
    hP.monic.free_quotient
  rw [← quotientEquivOfIsDistinguishedAt_comp_algebraMap hπ hP]
  exact (RingHom.flat_algebraMap_iff.2 inferInstance).comp
    (RingHom.Flat.of_bijective (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).bijective)

/-- Pullback along `Prod.fst` makes the local quotient `𝒪_{E × ℂ, (x₀, w₀)} ⧸ (evalVertical P)`
finite over the base stalk `𝒪_{E, x₀}` for every distinguished polynomial `P`. -/
theorem finite_quotientMk_comp_stalkPrecomp_fst_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    ((Ideal.Quotient.mk (Ideal.span {evalVertical x₀ w₀ P})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀))).Finite := by
  have : Module.Finite ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)
      (((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ⧸ Ideal.span {P}) :=
    hP.monic.finite_quotient
  rw [← quotientEquivOfIsDistinguishedAt_comp_algebraMap hπ hP]
  exact RingHom.Finite.comp
    (RingHom.Finite.of_surjective _ (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).surjective)
    (RingHom.finite_algebraMap.2 inferInstance)

/-- **Local hypersurface flatness via Weierstrass preparation.** If `f ∈ 𝒪_{E × ℂ, (x₀, w₀)}` has
vertical power series with nonzero residue-field reduction (equivalently, its vertical slice at `x₀`
does not vanish identically near `w₀`), then `𝒪_{E × ℂ, (x₀, w₀)} ⧸ (f)` is flat over the base stalk
`𝒪_{E, x₀}` via pullback along `Prod.fst`. -/
theorem flat_quotientMk_comp_stalkPrecomp_fst {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0) :
    ((Ideal.Quotient.mk (Ideal.span {f})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀))).Flat := by
  obtain ⟨⟨P, u⟩, ⟨hP, hu, hf_eq⟩, _⟩ := existsUnique_weierstrassPreparation hf
  have hspan : Ideal.span {f} = Ideal.span {evalVertical x₀ w₀ P} := by
    rw [hf_eq, Ideal.span_singleton_mul_right_unit hu]
  exact hspan ▸ flat_quotientMk_comp_stalkPrecomp_fst_of_isDistinguishedAt hπ hP

/-- **Local hypersurface finiteness via Weierstrass preparation.** If `f ∈ 𝒪_{E × ℂ, (x₀, w₀)}` has
vertical power series with nonzero residue-field reduction, then `𝒪_{E × ℂ, (x₀, w₀)} ⧸ (f)` is a
finite algebra over the base stalk `𝒪_{E, x₀}` via pullback along `Prod.fst`. -/
theorem finite_quotientMk_comp_stalkPrecomp_fst {x₀ : E} {w₀ : ℂ}
    (hπ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E) ω Prod.fst)
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0) :
    ((Ideal.Quotient.mk (Ideal.span {f})).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst hπ (x₀, w₀))).Finite := by
  obtain ⟨⟨P, u⟩, ⟨hP, hu, hf_eq⟩, _⟩ := existsUnique_weierstrassPreparation hf
  have hspan : Ideal.span {f} = Ideal.span {evalVertical x₀ w₀ P} := by
    rw [hf_eq, Ideal.span_singleton_mul_right_unit hu]
  exact hspan ▸ finite_quotientMk_comp_stalkPrecomp_fst_of_isDistinguishedAt hπ hP

end FiniteDimensional

end TauCeti.holomorphicStructureSheaf
