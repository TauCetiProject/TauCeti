/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Normed.Operator.Holder
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Extending a uniformly elliptic field to the whole space

Results about a divergence-form operator on the whole space or on a half-space, such as global
`H²` regularity, ask for a coefficient field that is uniformly elliptic and Lipschitz there. A field
`a` that is uniformly elliptic and Lipschitz only on a set `S`, possibly up to part of its
boundary, can be brought into that form near a compact set `C` without changing it on `S` near
`C`. Extend `a` from `S` entrywise by McShane's extension to a Lipschitz field `ā` on the whole
space, and take a smooth cutoff `χ` equal to one near `C` and supported in an open `U ⊇ C`. The
field `χ ā + (1 - χ) λ I` is bounded and Lipschitz on the whole space, it agrees with `a` on
`S ∩ W` for an open `W` with `C ⊆ W ⊆ U`, and it is uniformly elliptic with the same constants
`λ, Λ` on any prescribed set `T` with `T ∩ U ⊆ S`, such as a half-space that coincides with `S`
near `C`.

When `a` has smooth entries near `C`, the same cutoff gives a field `a'` whose entries are smooth,
with Lipschitz first derivatives, since `a' - λ I` has compact support. This is the form needed by
the higher regularity theorems on a half-space.

The case of a field that is locally Lipschitz and uniformly elliptic on an open set `Ω`, with
`C ⊆ Ω` and `T` the whole space, is a corollary: apply the construction with `S` a compact
neighbourhood of `C` in `Ω`, on which `a` is Lipschitz.

Without any regularity there is a simpler extension: a measurable field that is uniformly elliptic
on an open set `Ω`, extended by `λ I` off `Ω`, is a measurable field that is uniformly elliptic with
the same constants on the whole space. The boundary De Giorgi estimates use it to pass from a
subsolution on `Ω` to its zero extension on the whole space.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`: a field uniformly elliptic
  and Lipschitz on a set `S` agrees, near a compact set `C` that may meet the boundary of `S`,
  with a bounded Lipschitz field on the whole space that is uniformly elliptic on a prescribed
  set `T`, such as a half-space that coincides with `S` near `C`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_contDiff_eqOn_inter`: the same for a field with smooth
  entries near `C`, giving a field with smooth entries and Lipschitz first derivatives.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn`: near a compact subset of `Ω`, a
  locally Lipschitz uniformly elliptic field agrees with a Lipschitz uniformly elliptic field on
  the whole space.
* `TauCeti.PDE.UniformlyEllipticOn.exists_aestronglyMeasurable_eqOn`: a measurable field uniformly
  elliptic on `Ω`, extended by `λ I` off `Ω`, is measurable and uniformly elliptic on the whole
  space.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §8.3
  (localization of the coefficients in the proof of Theorem 8.8).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- **Blending a Lipschitz field with a constant one by a smooth cutoff is bounded and Lipschitz.**
If `x ↦ matrixBilinearForm (abar x)` is Lipschitz and `χ` is a `C¹` compactly supported weight with
values in `[0, 1]`, then the bilinear forms of `χ abar + (1 - χ) c` are Lipschitz and bounded, for
every constant matrix `c`. -/
private theorem exists_lipschitzWith_and_norm_le_matrixBilinearForm_smul_add_one_sub_smul
    {L : ℝ≥0} {abar : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hLbar : LipschitzWith L (fun x => matrixBilinearForm (abar x)))
    {χ : EuclideanSpace ℝ ι → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (c : Matrix ι ι ℝ) :
    ∃ (K' : ℝ≥0) (M : ℝ),
      LipschitzWith K' (fun x => matrixBilinearForm (χ x • abar x + (1 - χ x) • c)) ∧
        ∀ x, ‖matrixBilinearForm (χ x • abar x + (1 - χ x) • c)‖ ≤ M := by
  have hχ0 : ∀ x ∉ tsupport χ, χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C0, hC0⟩ : ∃ C0, matrixBilinearForm c = C0 := ⟨_, rfl⟩
  -- On the compact set `tsupport χ`, `F = B(ā) - C0` is Lipschitz and bounded.
  set F := fun x => matrixBilinearForm (abar x) + -C0
  have hF : LipschitzWith (_ + 0) F := hLbar.add (LipschitzWith.const (-C0))
  obtain ⟨B, hB⟩ := hχc.bddAbove_image (Continuous.norm
    (E := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) hF.continuous).continuousOn
  have hFb : ∀ x ∈ tsupport χ, ‖F x‖ ≤ B.toNNReal := fun x hx =>
    (hB ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal _)
  obtain ⟨Lχ, hLχ⟩ := hχ.lipschitzWith_of_hasCompactSupport hχc (by simp)
  have hχF := (holderWith_one.2 hLχ).smul_of_eq_zero (holderOnWith_one.2 hF.lipschitzOnWith)
    (Mc := 1) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχI x).1, NNReal.coe_one]
      exact (hχI x).2) hFb hχ0
  -- The bilinear forms of `χ ā + (1 - χ) λ I` are `C0 + χ F`.
  have hBform : (fun x => matrixBilinearForm (χ x • abar x + (1 - χ x) • c)) =
      fun x => C0 + χ x • F x := by
    ext x η ξ
    simp only [F, ← hC0, matrixBilinearForm_add_apply, matrixBilinearForm_smul_apply, add_apply,
      FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  obtain ⟨K', hK'⟩ : ∃ K', LipschitzWith K' fun x =>
      matrixBilinearForm (χ x • abar x + (1 - χ x) • c) :=
    ⟨_, by rw [hBform]; exact (LipschitzWith.const C0).add (holderWith_one.1 hχF)⟩
  refine ⟨K', ‖C0‖ + B.toNNReal, hK', fun x => ?_⟩
  rw [show matrixBilinearForm (χ x • abar x + (1 - χ x) • c) = C0 + χ x • F x from
    congrFun hBform x]
  have hχFx : ‖χ x • F x‖ ≤ B.toNNReal := by
    refine (ContinuousLinearMap.opNorm_smul_le (χ x) (F x)).trans ?_
    by_cases hx : x ∈ tsupport χ
    · rw [Real.norm_eq_abs, abs_of_nonneg (hχI x).1]
      exact (mul_le_of_le_one_left (norm_nonneg (F x)) (hχI x).2).trans (hFb x hx)
    · rw [hχ0 x hx, norm_zero, zero_mul]
      exact NNReal.coe_nonneg _
  linarith [norm_add_le C0 (χ x • F x)]

/-- **Blending a uniformly elliptic field with `λ I` by a cutoff that is one near `C`.** Let `a`
be uniformly elliptic on `S` with constants `λ, Λ`, and let `T ∩ U ⊆ S`. If `χ` takes values in
`[0, 1]`, is supported in `U` and equals one near `C`, then `χ a + (1 - χ) λ I` is uniformly
elliptic on `T`, and `χ = 1` on an open `W` with `C ⊆ W ⊆ U`. -/
private theorem exists_uniformlyEllipticOn_smul_add_one_sub_smul [DecidableEq ι] {lam Lam : ℝ}
    {S T C : Set (EuclideanSpace ℝ ι)} {U : Opens (EuclideanSpace ℝ ι)}
    (ha : UniformlyEllipticOn S a lam Lam) (hTU : T ∩ U ⊆ S) {χ : EuclideanSpace ℝ ι → ℝ}
    (hχr : range χ ⊆ Icc 0 1) (hχ1 : C ⊆ interior (χ ⁻¹' {1})) (hχs : tsupport χ ⊆ U) :
    ∃ W : Opens (EuclideanSpace ℝ ι), C ⊆ W ∧ W ≤ U ∧
      UniformlyEllipticOn T (fun x => χ x • a x + (1 - χ x) • (lam • 1)) lam Lam ∧
        ∀ x ∈ W, χ x = 1 := by
  classical
  have hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := fun x => hχr (mem_range_self x)
  have hχ0 : ∀ x ∉ tsupport χ, χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  refine ⟨⟨interior (χ ⁻¹' {1}), isOpen_interior⟩, hχ1, fun x hx => ?_, ?_,
    fun x hx => interior_subset hx⟩
  · have hχx : χ x = 1 := interior_subset hx
    exact hχs (subset_tsupport _ (by simp [hχx]))
  · -- On `T`, the weight vanishes off `S`, since `T ∩ U ⊆ S` and `tsupport χ ⊆ U`.
    have hT := ha.smul_add_one_sub_smul
      (uniformlyEllipticOn_const_smul_one univ ha.pos le_rfl ha.le)
      (χ := fun x => if x ∈ T then χ x else 0)
      (fun x => by split_ifs <;> simp [hχI x])
      (fun x hx => by
        split_ifs with hxT
        · exact hχ0 x fun h => hx (hTU ⟨hxT, hχs h⟩)
        · rfl)
    refine (hT.mono_set (subset_univ T)).congr fun x hx => ?_
    simp only [hx, ite_true]

/-- **A uniformly elliptic field, Lipschitz up to part of the boundary, agrees near a compact set
with a Lipschitz field on the whole space.** Let `a` be uniformly elliptic on a set `S` with
constants `λ, Λ`, with `x ↦ a(x)` Lipschitz on `S` in the operator norm of its bilinear forms. Let
`U` be open, let `T` be a set with `T ∩ U ⊆ S`, and let `C ⊆ U` be compact. Then there is a bounded
field `a'` on the whole space, Lipschitz there and uniformly elliptic on `T` with the same
constants, that agrees with `a` on `S ∩ W` for an open `W` with `C ⊆ W ⊆ U`.

Here `C` need not lie in `S`: typically `S = Ω ∩ U` for a domain `Ω` and a half-space `T` with
`Ω ∩ U = T ∩ U`, and `C` meets the flat part of `∂Ω`. One may take
`a' = χ ā + (1 - χ) λ I`, where `ā` extends `a` from `S` entrywise by McShane's extension
(`LipschitzOnWith.extend_real`) and `χ` is a smooth cutoff equal to one near `C` and supported
in `U`. -/
theorem UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter [DecidableEq ι] {lam Lam : ℝ}
    {K : ℝ≥0} {S T C : Set (EuclideanSpace ℝ ι)} {U : Opens (EuclideanSpace ℝ ι)}
    (ha : UniformlyEllipticOn S a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) S)
    (hTU : T ∩ U ⊆ S) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ, ∃ K' : ℝ≥0, ∃ M : ℝ,
      ∃ W : Opens (EuclideanSpace ℝ ι), C ⊆ W ∧ W ≤ U ∧ UniformlyEllipticOn T a' lam Lam ∧
        LipschitzWith K' (fun x => matrixBilinearForm (a' x)) ∧
          (∀ x, ‖matrixBilinearForm (a' x)‖ ≤ M) ∧ EqOn a' a (S ∩ W) := by
  classical
  obtain ⟨abar, _, habar, hLbar⟩ := exists_lipschitzWith_matrixBilinearForm_eqOn hK
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχs⟩ := hC.exists_contDiff_cutoff U.isOpen hCU
  obtain ⟨W, hCW, hWU, hT, hW1⟩ :=
    exists_uniformlyEllipticOn_smul_add_one_sub_smul (ha.congr habar) hTU hχr hχ1 hχs
  obtain ⟨K', M, hK', hM⟩ :=
    exists_lipschitzWith_and_norm_le_matrixBilinearForm_smul_add_one_sub_smul hLbar
    (hχ.of_le (by simp)) hχc (fun x => hχr (mem_range_self x)) (lam • 1)
  exact ⟨_, K', M, W, hCW, hWU, hT, hK', hM, fun x hx => by simp [hW1 x hx.2, habar hx.1]⟩

/-- **A locally Lipschitz uniformly elliptic field agrees near a compact set with a Lipschitz
uniformly elliptic field on the whole space.** Let `a` be uniformly elliptic on `Ω` with
constants `λ, Λ`, with `x ↦ a(x)` locally Lipschitz on `Ω` in the operator norm of its bilinear
forms, and let `S ⊆ Ω` be compact. Then there is a field `a'` on the whole space, uniformly
elliptic there with the same constants and Lipschitz, that agrees with `a` on an open `U` with
`S ⊆ U ⊆ Ω`.

One may take `a' = χ a + (1 - χ) λ I` for a smooth cutoff `χ` equal to one near `S` and supported
in `Ω`. This is the case `T = ℝⁿ` of
`TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`, applied on a compact
neighbourhood of `S` in `Ω`. -/
theorem UniformlyEllipticOn.exists_lipschitzWith_eqOn [DecidableEq ι] {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LocallyLipschitzOn (Omega : Set (EuclideanSpace ℝ ι))
      fun x => matrixBilinearForm (a x))
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S)
    (hSΩ : S ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ, ∃ K' : ℝ≥0, ∃ U : Opens (EuclideanSpace ℝ ι),
      S ⊆ U ∧ U ≤ Omega ∧ UniformlyEllipticOn univ a' lam Lam ∧
        LipschitzWith K' (fun x => matrixBilinearForm (a' x)) ∧
          EqOn a' a (U : Set (EuclideanSpace ℝ ι)) := by
  -- On a compact neighbourhood `L ⊆ Ω` of `S`, the field is Lipschitz.
  obtain ⟨L, hL, hSL, hLΩ⟩ := exists_compact_between hS Omega.isOpen hSΩ
  obtain ⟨K0, hK0⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hL (hK.mono hLΩ)
  obtain ⟨a', K', -, W, hSW, hWL, ha', hK', -, haa'⟩ :=
    (ha.mono_set hLΩ).exists_lipschitzWith_eqOn_inter (T := univ)
      (U := ⟨interior L, isOpen_interior⟩) hK0 (fun x hx => interior_subset hx.2) hS hSL
  have hWL' : (W : Set (EuclideanSpace ℝ ι)) ⊆ L := fun x hx => interior_subset (hWL hx)
  exact ⟨a', K', W, hSW, fun x hx => hLΩ (hWL' hx), ha', hK',
    fun x hx => haa' ⟨hWL' hx, hx⟩⟩

/-- **Blending a field smooth on `U` with a constant one by a cutoff supported in `U`.** If the
entries of `a` are smooth on an open `U` and `χ` is smooth with compact support in `U`, then
`χ a + (1 - χ) c` has smooth entries with Lipschitz first derivatives, and its bilinear forms are
bounded and Lipschitz, for every constant matrix `c`. -/
private theorem exists_lipschitzWith_contDiff_smul_add_one_sub_smul
    {U : Opens (EuclideanSpace ℝ ι)} (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
    {χ : EuclideanSpace ℝ ι → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ U) (c : Matrix ι ι ℝ) :
    ∃ K K' : ℝ≥0, ∃ M : ℝ, (∀ i j, ContDiff ℝ ∞ fun x => (χ x • a x + (1 - χ x) • c) i j) ∧
      LipschitzWith K (fun x => matrixBilinearForm (χ x • a x + (1 - χ x) • c)) ∧
      (∀ i j, LipschitzWith K' fun x => fderiv ℝ (fun y => (χ y • a y + (1 - χ y) • c) i j) x) ∧
      ∀ x, ‖matrixBilinearForm (χ x • a x + (1 - χ x) • c)‖ ≤ M := by
  set a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ := fun x => χ x • a x + (1 - χ x) • c
  -- Each entry of `a'` is a constant plus the smooth compactly supported `χ (aᵢⱼ - cᵢⱼ)`.
  set g : ι → ι → EuclideanSpace ℝ ι → ℝ := fun i j x => χ x • (a x i j - c i j)
  have hg : ∀ i j, ContDiff ℝ ∞ (g i j) := fun i j =>
    ((hsmooth i j).sub contDiffOn_const).contDiff_smul_of_tsupport_subset U.isOpen hχ.contDiffOn
      hχs
  have hgc : ∀ i j, HasCompactSupport (g i j) := fun i j => hχc.smul_right
  have ha'g : ∀ i j, (fun x => a' x i j) = fun x => g i j x + c i j := fun i j => by
    funext x
    simp only [a', g, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  -- Lipschitz bounds for the entries and their first derivatives, and bounds for the entries.
  choose L hL using fun i j =>
    (hg i j).lipschitzWith_of_hasCompactSupport (hgc i j) (by simp)
  choose L' hL' using fun i j =>
    ((hg i j).fderiv_right (m := 1) (by simp)).lipschitzWith_of_hasCompactSupport
      ((hgc i j).fderiv ℝ) (by simp)
  choose B hB using fun i j => (hgc i j).exists_bound_of_continuous (hg i j).continuous
  have hLa : ∀ i j, LipschitzWith (L i j) fun x => a' x i j := fun i j => by
    rw [ha'g]
    simpa using (hL i j).add (LipschitzWith.const (c i j))
  refine ⟨∑ i, ∑ j, L i j, ∑ i, ∑ j, L' i j, ∑ i, ∑ j, (B i j + |c i j|), fun i j => ?_,
    lipschitzOnWith_univ.1 (holderOnWith_one.1 (holderOnWith_matrixBilinearForm_of_forall
      fun i j => (holderWith_one.2 (hLa i j)).holderOnWith univ)), fun i j => ?_, fun x => ?_⟩
  · rw [ha'g]
    exact (hg i j).add contDiff_const
  · rw [show (fun x => fderiv ℝ (fun y => a' y i j) x) = fderiv ℝ (g i j) from funext fun x => by
      rw [ha'g, fderiv_add_const]]
    exact (hL' i j).weaken ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, L' i j) (fun _ _ => zero_le)
        (Finset.mem_univ i)))
  · refine (norm_matrixBilinearForm_le_sum_abs (a' x)).trans
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    rw [show a' x i j = g i j x + c i j from congrFun (ha'g i j) x]
    exact (abs_add_le _ _).trans (add_le_add_left (hB i j x) _)

/-- **A uniformly elliptic field, smooth near part of the boundary, agrees near a compact set with
a smooth field on the whole space.** Let `a` be uniformly elliptic on a set `S` with constants
`λ, Λ`, with entries smooth on an open set `U`. Let `T` be a set with `T ∩ U ⊆ S`, and let
`C ⊆ U` be compact. Then there is a field `a'` on the whole space, uniformly elliptic on `T` with
the same constants, that agrees with `a` on an open `W` with `C ⊆ W ⊆ U`; its entries are smooth
with Lipschitz first derivatives, and its bilinear forms are bounded and Lipschitz.
It equals `λ I` off a compact set `K₀ ⊆ U`.

As in `TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`, `C` need not lie in `S`:
typically `S = Ω ∩ U` for a domain `Ω` and a half-space `T` with `Ω ∩ U = T ∩ U`. One may take
`a' = χ a + (1 - χ) λ I` for a smooth cutoff `χ` equal to one near `C` and supported in `U`; then
`a' - λ I` has compact support, which bounds every derivative. -/
theorem UniformlyEllipticOn.exists_contDiff_eqOn_inter [DecidableEq ι] {lam Lam : ℝ}
    {S T C : Set (EuclideanSpace ℝ ι)} {U : Opens (EuclideanSpace ℝ ι)}
    (ha : UniformlyEllipticOn S a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
    (hTU : T ∩ U ⊆ S) (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ, ∃ K K' : ℝ≥0, ∃ M : ℝ,
      ∃ W : Opens (EuclideanSpace ℝ ι), C ⊆ W ∧ W ≤ U ∧ UniformlyEllipticOn T a' lam Lam ∧
        (∀ i j, ContDiff ℝ ∞ fun x => a' x i j) ∧
        LipschitzWith K (fun x => matrixBilinearForm (a' x)) ∧
        (∀ i j, LipschitzWith K' fun x => fderiv ℝ (fun y => a' y i j) x) ∧
        (∀ x, ‖matrixBilinearForm (a' x)‖ ≤ M) ∧ EqOn a' a (W : Set (EuclideanSpace ℝ ι)) ∧
        ∃ K₀ : Set (EuclideanSpace ℝ ι), IsCompact K₀ ∧ K₀ ⊆ U ∧
          EqOn a' (fun _ ↦ lam • (1 : Matrix ι ι ℝ)) K₀ᶜ := by
  classical
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχs⟩ := hC.exists_contDiff_cutoff U.isOpen hCU
  obtain ⟨W, hCW, hWU, hT, hW1⟩ :=
    exists_uniformlyEllipticOn_smul_add_one_sub_smul ha hTU hχr hχ1 hχs
  obtain ⟨K, K', M, hsm, hK, hK', hM⟩ :=
    exists_lipschitzWith_contDiff_smul_add_one_sub_smul hsmooth hχ hχc hχs (lam • 1)
  refine ⟨_, K, K', M, W, hCW, hWU, hT, hsm, hK, hK', hM, ?_,
    tsupport χ, hχc.isCompact, hχs, ?_⟩
  · intro x hx
    simp only [hW1 x hx, one_smul, sub_self, zero_smul, add_zero]
  · intro x hx
    simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul, zero_add, sub_zero, one_smul]

/-- **Extending a measurable uniformly elliptic field by `λ I`.** A field `a`, measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, agrees on `Ω` with a field that is measurable and
uniformly elliptic with the same constants on the whole space, namely `a` extended by `λ I` off
`Ω`. -/
theorem UniformlyEllipticOn.exists_aestronglyMeasurable_eqOn [DecidableEq ι]
    {mu : Measure (EuclideanSpace ℝ ι)} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (univ : Set (EuclideanSpace ℝ ι)) a' lam Lam ∧
        AEStronglyMeasurable a' mu ∧ EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)) := by
  classical
  have hI := uniformlyEllipticOn_const_smul_one (n := ι) (univ : Set (EuclideanSpace ℝ ι))
    h.pos le_rfl h.le
  refine ⟨(Omega : Set (EuclideanSpace ℝ ι)).piecewise a fun _ => lam • (1 : Matrix ι ι ℝ),
    UniformlyEllipticOn.of_bounds h.pos h.le (fun x _ ξ => ?_) (fun x _ η ξ => ?_),
    ha.piecewise Omega.isOpen.measurableSet.nullMeasurableSet aestronglyMeasurable_const,
    piecewise_eqOn _ _ _⟩
  · by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [piecewise_eq_of_mem _ _ _ hx]
      exact h.lower_bound hx ξ
    · rw [piecewise_eq_of_notMem _ _ _ hx]
      exact hI.lower_bound (mem_univ x) ξ
  · by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [piecewise_eq_of_mem _ _ _ hx]
      exact h.upper_bound hx η ξ
    · rw [piecewise_eq_of_notMem _ _ _ hx]
      exact hI.upper_bound (mem_univ x) η ξ

section CompactPerturbation
open scoped BigOperators
variable {K : Set (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}
local notation "E" => EuclideanSpace ℝ ι

/-- A smooth matrix field constant off a compact set has a common bound for its derivatives
of orders two through any fixed order. -/
theorem exists_coefficient_derivative_bound
    (hK : IsCompact K) (hconst : EqOn a (fun _ ↦ A) Kᶜ)
    (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) (k : ℕ) :
    ∃ C : ℝ, ∀ i j, ∀ r, 2 ≤ r → r ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ r (fun y ↦ a y i j) x‖ ≤ C := by
  classical
  choose C hC using fun (i j : ι) (r : Fin (k + 1)) ↦
    ContDiff.exists_bound_iteratedFDeriv_of_eqOn_compl (i := r.val + 1)
      ((hsm i j).of_le (by simp) : ContDiff ℝ (r.val + 1) (fun x ↦ a x i j))
      (by omega) hK (b := A i j) (L := 0) (fun x hx ↦ by
        simpa using congrArg (fun B ↦ B i j) (hconst hx))
  refine ⟨∑ i, ∑ j, ∑ s : Fin (k + 1), |C i j s|, fun i j r hr hrk x ↦ ?_⟩
  have hs : r - 1 < k + 1 := by omega
  have h := hC i j ⟨r - 1, hs⟩ x
  -- Expose the finite index in the chosen bound so the natural-number rewrite applies.
  change ‖iteratedFDeriv ℝ (r - 1 + 1) (fun y ↦ a y i j) x‖ ≤ C i j ⟨r - 1, hs⟩ at h
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h
  apply (h.trans (le_abs_self _)).trans
  calc
    |C i j ⟨r - 1, hs⟩| ≤ ∑ s : Fin (k + 1), |C i j s| :=
      Finset.single_le_sum (f := fun s : Fin (k + 1) ↦ |C i j s|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ (⟨r - 1, hs⟩ : Fin (k + 1)))
    _ ≤ ∑ t : ι, ∑ s : Fin (k + 1), |C i t s| :=
      Finset.single_le_sum (f := fun t : ι ↦ ∑ s : Fin (k + 1), |C i t s|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ t : ι, ∑ v : ι, ∑ s : Fin (k + 1), |C t v s| :=
      Finset.single_le_sum (f := fun t : ι ↦ ∑ v : ι, ∑ s : Fin (k + 1), |C t v s|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)

end CompactPerturbation

end PDE

end TauCeti
