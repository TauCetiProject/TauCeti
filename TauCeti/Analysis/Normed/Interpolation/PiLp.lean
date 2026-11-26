/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Finite `ℓ^q` sums of a compatible couple

For a compatible couple `(X₀, X₁)` in an ambient space `V`, a finite index type `ι` and exponents
`1 ≤ q₀, q₁ ≤ ∞`, the spaces `ℓ^{q₀}(ι; X₀) = PiLp q₀ (fun _ : ι => X₀)` and
`ℓ^{q₁}(ι; X₁) = PiLp q₁ (fun _ : ι => X₁)` form a compatible couple
`TauCeti.CompatibleCouple.piLp C ι q₀ q₁` in the ambient space `ι → V`, embedded coordinatewise.
Its intersection consists of the families whose coordinates lie in `X₀ ∩ X₁`
(`TauCeti.CompatibleCouple.mem_piLp_inter_iff`).

Its sum space is the finite product of copies of `X₀ + X₁`: the coordinate inclusions
`TauCeti.CompatibleCouple.sumSingle` and projections `TauCeti.CompatibleCouple.sumProj` of the sum
spaces satisfy `sumProj k (sumSingle j u) = Pi.single j u k`
(`TauCeti.CompatibleCouple.sumProj_sumSingle`) and `∑ k, sumSingle k (sumProj k u) = u`
(`TauCeti.CompatibleCouple.sum_sumSingle_sumProj`), and both lie over the coordinate maps of
`ι → V`.

These couples are the vector-valued sequence spaces of interpolation theory: Bergh–Löfström,
Theorem 5.1.2, computes their complex interpolation spaces as
`[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ = ℓ^q([X₀, X₁]_θ)` with `1 / q = (1 - θ) / q₀ + θ / q₁`, which for two
coordinates interpolates two-term maps such as `(x, y) ↦ (x + y, x - y)` in Clarkson's
inequalities.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.2).
-/

public noncomputable section

open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V) (ι : Type*) [Fintype ι] (q₀ q₁ : ℝ≥0∞)
  [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

/-- The couple `(ℓ^{q₀}(ι; X₀), ℓ^{q₁}(ι; X₁))` of finite `ℓ^q` sums of the spaces of a compatible
couple `(X₀, X₁)`, embedded coordinatewise into `ι → V`. -/
def piLp : CompatibleCouple 𝕜 (PiLp q₀ fun _ : ι => X₀) (PiLp q₁ fun _ : ι => X₁) (ι → V) where
  embed₀ := .pi fun k => C.embed₀.comp (PiLp.proj q₀ (fun _ : ι => X₀) k)
  embed₁ := .pi fun k => C.embed₁.comp (PiLp.proj q₁ (fun _ : ι => X₁) k)
  embed₀_injective _ _ h :=
    WithLp.ofLp_injective q₀ <| funext fun k => C.embed₀_injective (by simpa using congrFun h k)
  embed₁_injective _ _ h :=
    WithLp.ofLp_injective q₁ <| funext fun k => C.embed₁_injective (by simpa using congrFun h k)

variable {C ι q₀ q₁}

omit [Fintype ι] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] in
@[simp]
theorem piLp_embed₀_apply (x : PiLp q₀ fun _ : ι => X₀) (k : ι) :
    (C.piLp ι q₀ q₁).embed₀ x k = C.embed₀ (x k) :=
  (rfl)

omit [Fintype ι] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] in
@[simp]
theorem piLp_embed₁_apply (x : PiLp q₁ fun _ : ι => X₁) (k : ι) :
    (C.piLp ι q₀ q₁).embed₁ x k = C.embed₁ (x k) :=
  (rfl)

/-- A pair of families lies in the intersection `ℓ^{q₀}(X₀) ∩ ℓ^{q₁}(X₁)` exactly when each pair
of coordinates lies in `X₀ ∩ X₁`. -/
theorem mem_piLp_inter_iff {x : (PiLp q₀ fun _ : ι => X₀) × PiLp q₁ fun _ : ι => X₁} :
    x ∈ (C.piLp ι q₀ q₁).inter ↔ ∀ k, (x.1 k, x.2 k) ∈ C.inter := by
  simp [funext_iff]

/-! ### The coordinate maps of the sum spaces -/

section Coordinate

omit [Fintype ι] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] in
/-- The family `(C.embed₀ (Pi.single k x j))_j` is `Pi.single k (C.embed₀ x)`. -/
private theorem embed₀_single [DecidableEq ι] (k : ι) (x : X₀) :
    (C.piLp ι q₀ q₁).embed₀ (PiLp.single q₀ k x) = Pi.single k (C.embed₀ x) := by
  ext j
  rcases eq_or_ne j k with rfl | hj <;> simp [*]

omit [Fintype ι] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] in
private theorem embed₁_single [DecidableEq ι] (k : ι) (x : X₁) :
    (C.piLp ι q₀ q₁).embed₁ (PiLp.single q₁ k x) = Pi.single k (C.embed₁ x) := by
  ext j
  rcases eq_or_ne j k with rfl | hj <;> simp [*]

variable [ContinuousAdd V]


variable (C q₀ q₁) in
/-- The inclusion `X₀ + X₁ → ℓ^{q₀}(X₀) + ℓ^{q₁}(X₁)` of the `k`-th coordinate of the sum spaces:
`x₀ + x₁ ↦ single k x₀ + single k x₁`. It lies over `Pi.single k` (`sumSpaceEmbed_sumSingle`). -/
def sumSingle [DecidableEq ι] (k : ι) : C.SumSpace →L[𝕜] (C.piLp ι q₀ q₁).SumSpace :=
  C.sumLift ((C.piLp ι q₀ q₁).fstToSum.comp (PiLp.singleCLM q₀ 𝕜 (fun _ : ι => X₀) k))
    ((C.piLp ι q₀ q₁).sndToSum.comp (PiLp.singleCLM q₁ 𝕜 (fun _ : ι => X₁) k)) fun x =>
      sumSpace_ext _ <| by
        simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, ContinuousLinearMap.comp_apply,
          PiLp.singleCLM_apply, embed₀_single, embed₁_single]
        exact congrArg _ (C.embed₀_interFst x)

@[simp]
theorem sumSingle_fstToSum [DecidableEq ι] (k : ι) (x : X₀) :
    C.sumSingle q₀ q₁ k (C.fstToSum x) = (C.piLp ι q₀ q₁).fstToSum (PiLp.single q₀ k x) := by
  simp [sumSingle]

@[simp]
theorem sumSingle_sndToSum [DecidableEq ι] (k : ι) (x : X₁) :
    C.sumSingle q₀ q₁ k (C.sndToSum x) = (C.piLp ι q₀ q₁).sndToSum (PiLp.single q₁ k x) := by
  simp [sumSingle]

/-- The coordinate inclusion of the sum spaces lies over `Pi.single k : V → (ι → V)`. -/
@[simp]
theorem sumSpaceEmbed_sumSingle [DecidableEq ι] (k : ι) (u : C.SumSpace) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (C.sumSingle q₀ q₁ k u) = Pi.single k (C.sumSpaceEmbed u) := by
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  simp [embed₀_single, embed₁_single, Pi.single_add]

variable (C q₀ q₁) in
/-- The projection `ℓ^{q₀}(X₀) + ℓ^{q₁}(X₁) → X₀ + X₁` onto the `k`-th coordinate of the sum
spaces: `x₀ + x₁ ↦ x₀ k + x₁ k`. It lies over the evaluation at `k` (`sumSpaceEmbed_sumProj`). -/
def sumProj (k : ι) : (C.piLp ι q₀ q₁).SumSpace →L[𝕜] C.SumSpace :=
  (C.piLp ι q₀ q₁).sumLift (C.fstToSum.comp (PiLp.proj q₀ (fun _ : ι => X₀) k))
    (C.sndToSum.comp (PiLp.proj q₁ (fun _ : ι => X₁) k)) fun x =>
      sumSpace_ext _ <| by simpa using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) k

@[simp]
theorem sumProj_fstToSum (k : ι) (x : PiLp q₀ fun _ : ι => X₀) :
    C.sumProj q₀ q₁ k ((C.piLp ι q₀ q₁).fstToSum x) = C.fstToSum (x k) := by
  simp [sumProj]

@[simp]
theorem sumProj_sndToSum (k : ι) (x : PiLp q₁ fun _ : ι => X₁) :
    C.sumProj q₀ q₁ k ((C.piLp ι q₀ q₁).sndToSum x) = C.sndToSum (x k) := by
  simp [sumProj]

/-- The coordinate projection of the sum spaces lies over the evaluation at `k`. -/
@[simp]
theorem sumSpaceEmbed_sumProj (k : ι) (u : (C.piLp ι q₀ q₁).SumSpace) :
    C.sumSpaceEmbed (C.sumProj q₀ q₁ k u) = (C.piLp ι q₀ q₁).sumSpaceEmbed u k := by
  obtain ⟨x₀, x₁, rfl⟩ := (C.piLp ι q₀ q₁).exists_fstToSum_add_sndToSum_eq u
  simp

@[simp]
theorem sumProj_sumSingle [DecidableEq ι] (k j : ι) (u : C.SumSpace) :
    C.sumProj q₀ q₁ k (C.sumSingle q₀ q₁ j u) = Pi.single (M := fun _ : ι => C.SumSpace) j u k := by
  refine sumSpace_ext _ ?_
  rcases eq_or_ne k j with rfl | hk <;> simp [*]

/-- The sum space of `(ℓ^{q₀}(X₀), ℓ^{q₁}(X₁))` is the product of copies of `X₀ + X₁`: every
element is the sum of the coordinate inclusions of its coordinate projections. -/
theorem sum_sumSingle_sumProj [DecidableEq ι] (u : (C.piLp ι q₀ q₁).SumSpace) :
    ∑ k, C.sumSingle q₀ q₁ k (C.sumProj q₀ q₁ k u) = u := by
  refine sumSpace_ext _ ?_
  simp [map_sum, Finset.univ_sum_single]

end Coordinate

end TauCeti.CompatibleCouple
