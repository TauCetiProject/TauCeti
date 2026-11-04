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
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Extending a Lipschitz uniformly elliptic field to the whole space

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

The case of a field that is locally Lipschitz and uniformly elliptic on an open set `Ω`, with
`C ⊆ Ω` and `T` the whole space, is a corollary: apply the construction with `S` a compact
neighbourhood of `C` in `Ω`, on which `a` is Lipschitz.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`: a field uniformly elliptic
  and Lipschitz on a set `S` agrees, near a compact set `C` that may meet the boundary of `S`,
  with a bounded Lipschitz field on the whole space that is uniformly elliptic on a prescribed
  set `T`, such as a half-space that coincides with `S` near `C`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn`: near a compact subset of `Ω`, a
  locally Lipschitz uniformly elliptic field agrees with a Lipschitz uniformly elliptic field on
  the whole space.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §8.3
  (localization of the coefficients in the proof of Theorem 8.8).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

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
  -- Extend the entries of `a` from `S` to Lipschitz functions on the whole space.
  have hent : ∀ i j, LipschitzOnWith (K * ‖EuclideanSpace.single i (1 : ℝ)‖₊ *
      ‖EuclideanSpace.single j (1 : ℝ)‖₊) (fun x => a x i j) S := fun i j => by
    simpa [matrixBilinearForm_apply] using lipschitzOnWith_matrixBilinearForm_apply_apply hK
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
  choose g hgL hgS using fun i j => (hent i j).extend_real
  set abar : EuclideanSpace ℝ ι → Matrix ι ι ℝ := fun x => Matrix.of fun i j => g i j x
  have habar : EqOn abar a S := fun x hx => by
    ext i j
    exact (hgS i j hx).symm
  -- The bilinear forms of `ā` are Lipschitz, with the sum of the entrywise constants.
  have hLbar : LipschitzWith (∑ i : ι, ∑ j : ι, K * ‖EuclideanSpace.single i (1 : ℝ)‖₊ *
      ‖EuclideanSpace.single j (1 : ℝ)‖₊) (fun x => matrixBilinearForm (abar x)) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, ← matrixBilinearForm_sub]
    refine (norm_matrixBilinearForm_le_sum_abs _).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.sub_apply, ← Real.dist_eq]
    exact (hgL i j).dist_le_mul y z
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχs⟩ := hC.exists_contDiff_cutoff U.isOpen hCU
  have hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := fun x => hχr (mem_range_self x)
  have hχ0 : ∀ x ∉ tsupport χ, χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C0, hC0⟩ : ∃ C0, matrixBilinearForm (lam • (1 : Matrix ι ι ℝ)) = C0 := ⟨_, rfl⟩
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
  have hBform : (fun x => matrixBilinearForm (χ x • abar x + (1 - χ x) • (lam • 1))) =
      fun x => C0 + χ x • F x := by
    ext x η ξ
    simp only [F, ← hC0, matrixBilinearForm_add_apply, matrixBilinearForm_smul_apply, add_apply,
      FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  obtain ⟨K', hK'⟩ : ∃ K', LipschitzWith K' fun x =>
      matrixBilinearForm (χ x • abar x + (1 - χ x) • (lam • (1 : Matrix ι ι ℝ))) :=
    ⟨_, by rw [hBform]; exact (LipschitzWith.const C0).add (holderWith_one.1 hχF)⟩
  refine ⟨fun x => χ x • abar x + (1 - χ x) • (lam • 1), K', ‖C0‖ + B.toNNReal,
    ⟨interior (χ ⁻¹' {1}), isOpen_interior⟩, hχ1, fun x hx => ?_, ?_, hK', fun x => ?_,
    fun x hx => ?_⟩
  · have hχx : χ x = 1 := interior_subset hx
    exact hχs (subset_tsupport _ (by simp [hχx]))
  · -- On `T`, the weight vanishes off `S`, since `T ∩ U ⊆ S` and `tsupport χ ⊆ U`.
    have hT := (ha.congr habar).smul_add_one_sub_smul
      (uniformlyEllipticOn_const_smul_one univ ha.pos le_rfl ha.le)
      (χ := fun x => if x ∈ T then χ x else 0)
      (fun x => by split_ifs <;> simp [hχI x])
      (fun x hx => by
        split_ifs with hxT
        · exact hχ0 x fun h => hx (hTU ⟨hxT, hχs h⟩)
        · rfl)
    refine (hT.mono_set (subset_univ T)).congr fun x hx => ?_
    simp [hx]
  · rw [show matrixBilinearForm (χ x • abar x + (1 - χ x) • (lam • 1)) = C0 + χ x • F x from
      congrFun hBform x]
    have hχFx : ‖χ x • F x‖ ≤ B.toNNReal := by
      refine (ContinuousLinearMap.opNorm_smul_le (χ x) (F x)).trans ?_
      by_cases hx : x ∈ tsupport χ
      · rw [Real.norm_eq_abs, abs_of_nonneg (hχI x).1]
        exact (mul_le_of_le_one_left (norm_nonneg (F x)) (hχI x).2).trans (hFb x hx)
      · rw [hχ0 x hx, norm_zero, zero_mul]
        exact NNReal.coe_nonneg _
    linarith [norm_add_le C0 (χ x • F x)]
  · have hχx : χ x = 1 := interior_subset hx.2
    simp [hχx, habar hx.1]

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

end PDE

end TauCeti
