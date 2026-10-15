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
# Extending a locally Lipschitz uniformly elliptic field to the whole space

Results about a divergence-form operator on the whole space, such as global `H²` regularity, ask
for a coefficient field that is uniformly elliptic and Lipschitz everywhere. A field that is only
uniformly elliptic and locally Lipschitz on an open set `Ω` can be brought into that form near any
compact `S ⊆ Ω` without changing it there: for a smooth cutoff `χ` equal to one near `S` and
supported in `Ω`, the field `χ a + (1 - χ) λ I` is uniformly elliptic on the whole space with the
same constants `λ, Λ`, it is Lipschitz because `χ` vanishes off the compact set where `a` is
Lipschitz and bounded, and it agrees with `a` where `χ = 1`.

## Main declarations

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

/-- **A locally Lipschitz uniformly elliptic field agrees near a compact set with a Lipschitz
uniformly elliptic field on the whole space.** Let `a` be uniformly elliptic on `Ω` with
constants `λ, Λ`, with `x ↦ a(x)` locally Lipschitz on `Ω` in the operator norm of its bilinear
forms, and let `S ⊆ Ω` be compact. Then there is a field `a'` on the whole space, uniformly
elliptic there with the same constants and Lipschitz, that agrees with `a` on an open `U` with
`S ⊆ U ⊆ Ω`.

One may take `a' = χ a + (1 - χ) λ I` for a smooth cutoff `χ` equal to one near `S` and supported
in `Ω`. -/
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
  classical
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχs⟩ := hS.exists_contDiff_cutoff Omega.isOpen hSΩ
  have hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := fun x => hχr (mem_range_self x)
  have hχ0 : ∀ x ∉ tsupport χ, χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C0, hC0⟩ : ∃ C0, matrixBilinearForm (lam • (1 : Matrix ι ι ℝ)) = C0 := ⟨_, rfl⟩
  -- On the compact set `tsupport χ`, the field is Lipschitz and bounded.
  obtain ⟨K0, hK0⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hχc (hK.mono hχs)
  set F := fun x => matrixBilinearForm (a x) + -C0
  have hF : LipschitzOnWith (K0 + 0) F (tsupport χ) :=
    hK0.add (LipschitzWith.const (-C0)).lipschitzOnWith
  have hFb : ∀ x ∈ tsupport χ, ‖F x‖ ≤ (Lam + ‖C0‖).toNNReal := fun x hx => by
    have h1 := ha.opNorm_matrixBilinearForm_le (hχs hx)
    calc ‖F x‖ ≤ ‖matrixBilinearForm (a x)‖ + ‖-C0‖ := norm_add_le (matrixBilinearForm (a x)) _
      _ ≤ Lam + ‖C0‖ := add_le_add h1 (norm_neg C0).le
      _ ≤ _ := Real.le_coe_toNNReal _
  obtain ⟨Lχ, hLχ⟩ := hχ.lipschitzWith_of_hasCompactSupport hχc (by simp)
  -- The bilinear forms of `χ a + (1 - χ) λ I` are `C0 + χ F`, Lipschitz because `χ` vanishes off
  -- the set where `F` is controlled.
  have hχF := (holderWith_one.2 hLχ).smul_of_eq_zero (holderOnWith_one.2 hF) (Mc := 1)
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχI x).1, NNReal.coe_one]
      exact (hχI x).2) hFb hχ0
  have hB : (fun x => matrixBilinearForm (χ x • a x + (1 - χ x) • (lam • (1 : Matrix ι ι ℝ))))
      = fun x => C0 + χ x • F x := by
    ext x η ξ
    simp only [F, ← hC0, matrixBilinearForm_add_apply, matrixBilinearForm_smul_apply, add_apply,
      FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    ring
  obtain ⟨K', hK'⟩ : ∃ K', LipschitzWith K' fun x =>
      matrixBilinearForm (χ x • a x + (1 - χ x) • (lam • (1 : Matrix ι ι ℝ))) :=
    ⟨_, by rw [hB]; exact (LipschitzWith.const C0).add (holderWith_one.1 hχF)⟩
  refine ⟨fun x => χ x • a x + (1 - χ x) • (lam • 1), K',
    ⟨interior (χ ⁻¹' {1}), isOpen_interior⟩, hχ1, fun x hx => ?_,
    ha.smul_add_one_sub_smul (uniformlyEllipticOn_const_smul_one univ ha.pos le_rfl ha.le) hχI
      (fun x hx => hχ0 x fun h => hx (hχs h)), hK', fun x hx => ?_⟩
  · have hx1 : x ∈ χ ⁻¹' {1} := interior_subset hx
    have hχx : χ x = 1 := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx1)
    exact hχs (subset_tsupport _ (by simp [hχx]))
  · have hx1 : x ∈ χ ⁻¹' {1} := interior_subset hx
    have hχx : χ x = 1 := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx1)
    simp [hχx]

end PDE

end TauCeti
