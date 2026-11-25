/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Flow.Diffeomorph

/-!
# Smooth retraction onto a regular zero level along a flow

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M` whose zero level
`N = f⁻¹(0)` is compact and contains no critical point. Then a neighbourhood of `N` retracts
smoothly onto `N` (`TauCeti.exists_contMDiff_retraction_zeroLevel`): there are a smooth map
`ρ : M → M` fixing `N` pointwise and an open neighbourhood `W` of `N` which `ρ` sends into `N`.

The retraction follows a flow. A smooth compactly supported field `X` with `df(X) = -1` near `N`
(`TauCeti.exists_vectorField_mvfderiv_eq_neg_one`) is complete, and its flow `φ` lowers `f` at unit
speed along every flow line while the line stays where `df(X) = -1`
(`TauCeti.apply_globalFlow_eq_sub_of_forall_mem`). Near the compact set `N` this holds for all
small times, so the flow carries a point `x` near `N` to the zero level at time `f x`, forward when
`f x ≥ 0` and backward when `f x ≤ 0`. The retraction is `ρ x = φ (f x) x`, smooth because the flow
is jointly smooth in time and space.

If `τ` is a smooth involution of `M` that reverses the sign of `f`, the field can be replaced by
its antisymmetrization `(X - τ^* X) / 2`, which `τ` carries to its negative. The flow then
satisfies `τ (φ t x) = φ (-t) (τ x)`, so the retraction commutes with `τ`
(`TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive`). When `τ` fixes `N` pointwise,
for instance when `N` is the fixed curve of the antiholomorphic involution of a Schottky double and
`f` a defining function odd under it, the retraction is `τ`-invariant on `W`
(`TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive_of_eqOn`). Such a retraction is a
collar projection whose fibres are preserved by the involution.

## Main results

* `TauCeti.exists_contMDiff_retraction_zeroLevel`: a smooth retraction of a neighbourhood onto a
  regular compact zero level.
* `TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive`: for a smooth involution reversing
  the sign of `f`, the retraction can be chosen to commute with it.
* `TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive_of_eqOn`: if the involution also
  fixes the zero level, the retraction is invariant under it on the neighbourhood.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Section 5.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1, for the flow of a normalized field.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ}

omit [FiniteDimensional ℝ E] in
/-- The retraction along a given field: a smooth complete field `X` with `df(X) = -1` on an open
neighbourhood of the compact zero level of `f` gives the retraction `x ↦ φ (f x) x` along its flow
`φ`. -/
private theorem exists_retraction_of_vectorField [CompleteSpace E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hK : IsCompact (f ⁻¹' {0}))
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hcomplete : IsCompleteVectorField X) {U : Set M} (hU : IsOpen U) (hKU : f ⁻¹' {0} ⊆ U)
    (hXU : ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (X y) = -1) :
    ∃ ρ : M → M, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ρ ∧
      (∀ x, ρ x = globalFlow X (hX.of_le (by simp)) hcomplete (f x) x) ∧
      (∀ x, f x = 0 → ρ x = x) ∧ ∃ W, IsOpen W ∧ f ⁻¹' {0} ⊆ W ∧ ∀ x ∈ W, f (ρ x) = 0 := by
  have hX1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hX.of_le (by simp)
  have hφ := contMDiff_globalFlow_uncurry hcomplete le_top hX
  -- By the tube lemma, the flow lines through a neighbourhood `V` of the zero level stay in `U`
  -- for all times in `(-ε, ε)`.
  obtain ⟨u, V, hu, hV, h0u, hKV, huV⟩ := generalized_tube_lemma (isCompact_singleton (x := 0))
    hK (hU.preimage hφ.continuous) fun p hp ↦ by
      obtain ⟨t, y⟩ := p
      obtain ⟨ht, hy⟩ := hp
      rw [mem_singleton_iff] at ht
      subst ht
      rw [mem_preimage, Flow.map_zero_apply]
      exact hKU hy
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu 0 (h0u rfl)
  refine ⟨fun x ↦ globalFlow X hX1 hcomplete (f x) x, hφ.comp (hf.prodMk contMDiff_id),
    fun _ ↦ rfl, fun x hx ↦ by simp only [hx, Flow.map_zero_apply],
    V ∩ f ⁻¹' Ioo (-ε) ε, hV.inter (isOpen_Ioo.preimage hf.continuous),
    fun x hx ↦ ⟨hKV hx, by simpa only [mem_preimage, mem_singleton_iff.1 (mem_preimage.1 hx),
      mem_Ioo, neg_lt_zero, and_self] using hε⟩, fun x hx ↦ ?_⟩
  have hxU : ∀ s ∈ Ioo (-ε) ε, globalFlow X hX1 hcomplete s x ∈ U := fun s hs ↦
    huV (mk_mem_prod (hεu (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt])) hx.1)
  have h := apply_globalFlow_eq_sub_of_forall_mem hX1 hcomplete hXU hxU hx.2
  rwa [sub_self] at h

/-- **Smooth retraction onto a regular zero level.** Let `f` be a smooth function on a boundaryless
finite-dimensional manifold whose zero level is compact and contains no critical point. Then there
are a smooth map `ρ` fixing the zero level pointwise and an open neighbourhood `W` of the zero level
which `ρ` sends into the zero level. -/
theorem exists_contMDiff_retraction_zeroLevel (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hK : IsCompact (f ⁻¹' {0})) (hreg : ∀ x, f x = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) :
    ∃ ρ : M → M, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ρ ∧ (∀ x, f x = 0 → ρ x = x) ∧
      ∃ W, IsOpen W ∧ f ⁻¹' {0} ⊆ W ∧ ∀ x ∈ W, f (ρ x) = 0 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨X, hX, -, ⟨U, hU, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one hf hK fun x hx ↦ hreg x hx
  obtain ⟨ρ, hρ, -, hρ0, hρW⟩ := exists_retraction_of_vectorField hf hK hX
    (isCompleteVectorField_of_isCompact_of_eq_zero_off (hX.of_le (by simp)) hC hXC) hU hKU hXU
  exact ⟨ρ, hρ, hρ0, hρW⟩

omit [T2Space M] in
/-- The antisymmetrization `X' = (X - τ^* X) / 2` of a smooth field `X` with `df(X) = -1` on `U`,
for a smooth involution `τ` reversing the sign of `f`: it is smooth, vanishes off a compact set
when `X` does, has `df(X') = -1` on `U ∩ τ⁻¹ U`, and `τ` carries `-X'` to `X'`. -/
private theorem exists_antisymmetrization (τ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)
    (hτ : ∀ x, τ (τ x) = x) (hfτ : ∀ x, f (τ x) = -f x) {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {C : Set M} (hC : IsCompact C) (hXC : ∀ x ∉ C, X x = 0) {U : Set M}
    (hXU : ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (X y) = -1) :
    ∃ X' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ C', IsCompact C' ∧ ∀ x ∉ C', X' x = 0) ∧
      (∀ y ∈ U ∩ τ ⁻¹' U, mvfderiv 𝓘(ℝ, E) f y (X' y) = -1) ∧
      ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ x ((-X') x) = X' (τ x) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The pullback `τ^* X` and the antisymmetrization `X' = (X - τ^* X) / 2`.
  set Xs := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) τ X with hXs_def
  set X' : (x : M) → TangentSpace 𝓘(ℝ, E) x := (1 / 2 : ℝ) • (X - Xs) with hX'
  have hsymm : ⇑τ.symm = ⇑τ := funext fun y ↦ τ.symm_apply_eq.2 (hτ y).symm
  have hXs : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ x (Xs x) = X (τ x) :=
    τ.mfderiv_apply_mpullback hn X
  -- Since `τ` is an involution, `(τ^* X) (τ x) = dτ_x (X x)`.
  have hXsτ : ∀ x, Xs (τ x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ x (X x) := fun x ↦ by
    have h := τ.mfderiv_symm_apply_mfderiv_apply hn (τ x) (Xs (τ x))
    rw [hXs (τ x), hsymm, hτ x] at h
    exact h.symm
  -- Since `f ∘ τ = -f`, `df_{τ y} ∘ dτ_y = -df_y`.
  have hdfτ : ∀ y w, mvfderiv 𝓘(ℝ, E) f (τ y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ y w) =
      -mvfderiv 𝓘(ℝ, E) f y w := fun y w ↦ by
    have h := congrArg (fun L ↦ L w) (τ.mvfderiv_comp_diffeomorph hn f y)
    have hfτ' : f ∘ τ = -f := funext hfτ
    simp only [hfτ', mvfderiv_neg, neg_apply,
      ContinuousLinearMap.comp_apply] at h
    exact h.symm
  -- The antisymmetrized field is smooth, vanishes off a compact set, lowers `f` at unit speed
  -- near the zero level and is carried by `τ` to its negative.
  have hX's : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun x ↦ (⟨x, X' x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    (hX.sub_section (hX.mpullback_vectorField τ.contMDiff
      (fun _ ↦ τ.isInvertible_mfderiv hn) le_rfl)).const_smul_section
  have hX'C : ∀ x ∉ C ∪ τ '' C, X' x = 0 := fun x hx ↦ by
    rw [mem_union, not_or] at hx
    have hτx : τ x ∉ C := fun h ↦ hx.2 ⟨τ x, h, hτ x⟩
    simp only [hX', hXs_def, Pi.smul_apply, Pi.sub_apply, VectorField.mpullback_apply, hXC x hx.1,
      hXC _ hτx, map_zero, sub_zero, smul_zero]
  have hX'U : ∀ y ∈ U ∩ τ ⁻¹' U, mvfderiv 𝓘(ℝ, E) f y (X' y) = -1 := fun y hy ↦ by
    have h := hdfτ y (Xs y)
    rw [hXs y, hXU _ hy.2] at h
    simp only [hX', Pi.smul_apply, Pi.sub_apply, map_smul, map_sub, hXU y hy.1, smul_eq_mul]
    linarith
  have hτX' : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) τ x ((-X') x) = X' (τ x) := fun x ↦ by
    simp only [hX', Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, map_smul, map_sub, hXs,
      ← hXsτ, ← smul_neg, neg_sub]
  exact ⟨X', hX's, ⟨_, hC.union (hC.image τ.continuous), hX'C⟩, hX'U, hτX'⟩

/-- **Equivariant smooth retraction onto a regular zero level.** In the setting of
`TauCeti.exists_contMDiff_retraction_zeroLevel`, let moreover `τ` be a smooth involution of the
manifold reversing the sign of `f`. Then the retraction `ρ` can be chosen to commute with `τ`. -/
theorem exists_contMDiff_retraction_zeroLevel_of_involutive (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hK : IsCompact (f ⁻¹' {0})) (hreg : ∀ x, f x = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0)
    (τ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (hτ : ∀ x, τ (τ x) = x) (hfτ : ∀ x, f (τ x) = -f x) :
    ∃ ρ : M → M, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ρ ∧ (∀ x, f x = 0 → ρ x = x) ∧
      (∀ x, ρ (τ x) = τ (ρ x)) ∧ ∃ W, IsOpen W ∧ f ⁻¹' {0} ⊆ W ∧ ∀ x ∈ W, f (ρ x) = 0 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨X, hX, -, ⟨U, hU, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one hf hK fun x hx ↦ hreg x hx
  obtain ⟨X', hX's, ⟨C', hC', hX'C⟩, hX'U, hτX'⟩ :=
    exists_antisymmetrization τ hτ hfτ hX hC hXC hXU
  have hX'1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X' x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hX's.of_le (by simp)
  have hcomplete : IsCompleteVectorField X' :=
    isCompleteVectorField_of_isCompact_of_eq_zero_off hX'1 hC' hX'C
  obtain ⟨ρ, hρ, hρφ, hρ0, hρW⟩ := exists_retraction_of_vectorField hf hK hX's hcomplete
    (hU.inter (hU.preimage τ.continuous))
    (fun x hx ↦ ⟨hKU hx, hKU (by rw [mem_preimage, mem_singleton_iff, hfτ,
      mem_singleton_iff.1 (mem_preimage.1 hx), neg_zero])⟩)
    hX'U
  refine ⟨ρ, hρ, hρ0, fun x ↦ ?_, hρW⟩
  -- `τ` carries the backward flow line of `x` to the forward flow line of `τ x`.
  have hcurve : IsMIntegralCurve (τ ∘ fun t ↦ globalFlow X' hX'1 hcomplete (-t) x) X' := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
    exact (τ.isMIntegralCurveOn_comp_iff hn hτX').2
      ((isMIntegralCurve_globalFlow hX'1 hcomplete x).comp_neg.isMIntegralCurveOn _)
  have h := globalFlow_eq_of_isMIntegralCurve hX'1 hcomplete hcurve (f (τ x))
  simp only [comp_apply, neg_zero, Flow.map_zero_apply, hfτ, neg_neg] at h
  rw [hρφ, hρφ, hfτ]
  exact h

/-- **Invariant smooth retraction onto a regular zero level.** In the setting of
`TauCeti.exists_contMDiff_retraction_zeroLevel_of_involutive`, if the involution `τ` moreover fixes
the zero level of `f` pointwise, then the retraction `ρ` is `τ`-invariant on the neighbourhood `W`
which it sends into the zero level. -/
theorem exists_contMDiff_retraction_zeroLevel_of_involutive_of_eqOn
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hK : IsCompact (f ⁻¹' {0}))
    (hreg : ∀ x, f x = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0)
    (τ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (hτ : ∀ x, τ (τ x) = x) (hfτ : ∀ x, f (τ x) = -f x)
    (hτN : ∀ x, f x = 0 → τ x = x) :
    ∃ ρ : M → M, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ρ ∧ (∀ x, f x = 0 → ρ x = x) ∧
      ∃ W, IsOpen W ∧ f ⁻¹' {0} ⊆ W ∧ ∀ x ∈ W, f (ρ x) = 0 ∧ ρ (τ x) = ρ x := by
  obtain ⟨ρ, hρ, hρ0, hρτ, W, hW, hKW, hρW⟩ :=
    exists_contMDiff_retraction_zeroLevel_of_involutive hf hK hreg τ hτ hfτ
  exact ⟨ρ, hρ, hρ0, W, hW, hKW, fun x hx ↦ ⟨hρW x hx, by rw [hρτ, hτN _ (hρW x hx)]⟩⟩

end TauCeti
