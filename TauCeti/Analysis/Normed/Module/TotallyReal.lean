/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Frame
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Stability of maximal totally real subspaces

If `range A` is maximal totally real and both `A` and `J ∘ A` are injective, the doubled
frame `(x, y) ↦ A x + J (A y)` is invertible. Openness of invertible operators makes maximal total
reality stable under simultaneous operator-norm perturbations of `A` and `J`. Compact
families admit a single positive perturbation radius.

The frame formulation allows the tangent image of an embedding to vary with the base point.
In particular it applies to derivatives of embeddings in local trivializations, and hence
to the stability of totally real boundary conditions. The perturbed endomorphism need not
square to minus the identity; only the original doubled frames must be invertible.

The doubled-frame argument is also the linear step in the adapted-coordinate construction
of McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
Exercise B.4.10.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A compact set of maximal totally real frames has a uniform positive perturbation radius.
Both the parametrization and the endomorphism may vary. Injectivity of the two original
halves is essential: complementarity alone does not make a doubled frame invertible. -/
theorem exists_pos_isMaximalTotallyReal_range_of_isCompact
    {s : Set ((F →L[𝕜] E) × (E →L[𝕜] E))} (hs : IsCompact s)
    (hA : ∀ p ∈ s, Function.Injective p.1)
    (hJA : ∀ p ∈ s, Function.Injective (p.2.comp p.1))
    (hL : ∀ p ∈ s, IsMaximalTotallyReal p.2.toLinearMap p.1.range) :
    ∃ ε > 0, ∀ p ∈ s, ∀ (B : F →L[𝕜] E) (K : E →L[𝕜] E),
      ‖B - p.1‖ < ε → ‖K - p.2‖ < ε →
        IsMaximalTotallyReal K.toLinearMap B.range := by
  let _ := FiniteDimensional.complete 𝕜 F
  let D : ((F →L[𝕜] E) × (E →L[𝕜] E)) → (F × F →L[𝕜] E) :=
    fun p => p.1.coprod (p.2.comp p.1)
  have hD : Continuous D := by
    simp only [D, ← ContinuousLinearMap.comp_fst_add_comp_snd]
    exact (continuous_fst.clm_comp_const _).add
      ((continuous_snd.clm_comp continuous_fst).clm_comp_const _)
  have ho : IsOpen {p | (D p).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hD
  have hsub : s ⊆ {p | (D p).IsInvertible} := by
    intro p hp
    have hb := (hL p hp).bijective_coprod (hA p hp) (hJA p hp)
    refine ⟨(LinearEquiv.ofBijective (D p).toLinearMap hb).toContinuousLinearEquiv, ?_⟩
    exact ContinuousLinearMap.ext fun x => LinearEquiv.ofBijective_apply _ (hf := hb) x
  obtain ⟨ε, hε, he⟩ := hs.exists_thickening_subset_open ho hsub
  refine ⟨ε, hε, fun p hp B K hB hK => ?_⟩
  have hd : dist (B, K) p < ε := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [dist_eq_norm] using hB)
      (by simpa only [dist_eq_norm] using hK)
  have hi : (D (B, K)).IsInvertible := he (Metric.mem_thickening_iff.mpr ⟨p, hp, hd⟩)
  exact isMaximalTotallyReal_range_of_bijective_coprod hi.bijective

/-- Along a continuous family of injective frames `A x` with maximal totally real image and
injective `J x ∘ A x` on a compact parameter set, one radius works at every parameter.
No continuity of the perturbed family is required. -/
theorem exists_pos_isMaximalTotallyReal_range_of_continuousOn
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {A : X → F →L[𝕜] E} {J : X → E →L[𝕜] E}
    (hAc : ContinuousOn A s) (hJc : ContinuousOn J s)
    (hA : ∀ x ∈ s, Function.Injective (A x))
    (hJA : ∀ x ∈ s, Function.Injective ((J x).comp (A x)))
    (hL : ∀ x ∈ s, IsMaximalTotallyReal (J x).toLinearMap (A x).range) :
    ∃ ε > 0, ∀ x ∈ s, ∀ (B : F →L[𝕜] E) (K : E →L[𝕜] E),
      ‖B - A x‖ < ε → ‖K - J x‖ < ε →
        IsMaximalTotallyReal K.toLinearMap B.range := by
  obtain ⟨ε, hε, he⟩ := exists_pos_isMaximalTotallyReal_range_of_isCompact
    (hs.image_of_continuousOn (hAc.prodMk hJc))
    (by rintro _ ⟨x, hx, rfl⟩; exact hA x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact hJA x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact hL x hx)
  exact ⟨ε, hε, fun x hx => he (A x, J x) ⟨x, hx, rfl⟩⟩

/-- A fixed maximal totally real subspace remains so under small perturbations of `J`.
Only injectivity of `J` on the subspace is needed, rather than a complex-structure identity. -/
theorem IsMaximalTotallyReal.exists_pos_of_injective_domRestrict
    [FiniteDimensional 𝕜 E] {J : E →L[𝕜] E} {L : Submodule 𝕜 E}
    (hL : IsMaximalTotallyReal J.toLinearMap L)
    (hJ : Function.Injective (J.domRestrict L)) :
    ∃ ε > 0, ∀ K : E →L[𝕜] E, ‖K - J‖ < ε →
      IsMaximalTotallyReal K.toLinearMap L := by
  have hLs : IsMaximalTotallyReal J.toLinearMap L.subtypeL.range := by
    simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using hL
  obtain ⟨ε, hε, he⟩ := exists_pos_isMaximalTotallyReal_range_of_isCompact
    (isCompact_singleton (x := (L.subtypeL, J)))
    (by rintro _ rfl; exact Subtype.val_injective)
    (by rintro _ rfl; exact hJ) (by simpa using hLs)
  refine ⟨ε, hε, fun K hK => ?_⟩
  simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using
    he (L.subtypeL, J) (mem_singleton _) L.subtypeL K (by simpa using hε) hK

/-- Maximal total reality for a complex structure persists under small operator-norm
perturbations. The new endomorphism is not required to satisfy the square identity. -/
theorem IsMaximalTotallyReal.exists_pos_of_comp_self_eq_neg_id
    [FiniteDimensional 𝕜 E] {J : E →L[𝕜] E} {L : Submodule 𝕜 E}
    (hL : IsMaximalTotallyReal J.toLinearMap L)
    (hJ : J.comp J = -ContinuousLinearMap.id 𝕜 E) :
    ∃ ε > 0, ∀ K : E →L[𝕜] E, ‖K - J‖ < ε →
      IsMaximalTotallyReal K.toLinearMap L := by
  have hJJ (x : E) : J (J x) = -x := by
    simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply] using congrArg (fun T : E →L[𝕜] E => T x) hJ
  apply hL.exists_pos_of_injective_domRestrict
  intro x y hxy
  apply Subtype.ext
  have h := congrArg J hxy
  simpa only [ContinuousLinearMap.domRestrict_apply, hJJ, neg_inj] using h

end TauCeti
