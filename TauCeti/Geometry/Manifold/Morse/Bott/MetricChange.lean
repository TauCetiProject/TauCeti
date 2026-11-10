/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.RelativeProjection
public import TauCeti.Geometry.Manifold.Morse.Bott.Coordinates
public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
public import TauCeti.LinearAlgebra.Projection.SplittingEquiv

/-!
# Changing the fibre metric of the negative and positive normal spaces

Let `i : S → M` be a nondegenerate critical submanifold of a function `f`. A fibre metric `g` on
its normal spaces splits each normal space into the negative normal space `ν⁻_g`, on which the
normal Hessian is negative definite, and the positive normal space `ν⁺_g`, on which it is positive
definite (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`). These subspaces
depend on `g`, but their isomorphism classes do not. For a second fibre metric `g'`, the space
`ν⁻_g` is also a complement of `ν⁺_{g'}`, since a vector in both is `0` by definiteness, and
likewise `ν⁺_g` is a complement of `ν⁻_{g'}` (`isCompl_negativeNormalSpace_positiveNormalSpace`,
in the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
So projecting `ν⁻_g` onto `ν⁻_{g'}` along `ν⁺_{g'}`, and `ν⁺_g` onto `ν⁺_{g'}` along `ν⁻_{g'}`,
defines a linear automorphism of the normal space (`normalMetricChange`, built from
`Submodule.splittingEquiv`), which carries `ν⁻_g` onto `ν⁻_{g'}` and `ν⁺_g` onto `ν⁺_{g'}`, and
is the identity when `g' = g`.

This automorphism is as smooth as the metrics and the function allow. In the preferred
normal-bundle trivialization at any point, with Euclidean fibre model `P`, write the two fibre
metrics as `C^k` families `G` and `G'` of forms on `P`, with `f` of class `C^{k+2}` along the
submanifold. If `p` and `p'` are the negative spectral projections of the normal Hessian relative
to `G` and to `G'` (`ContinuousLinearMap.negativeSpectralProjection`), the automorphism reads
`p' ∘ p + (1 - p') ∘ (1 - p)` in the trivialization, a `C^k` family of invertible operators whose
inverses form a `C^k` family as well (`exists_contMDiffOn_normalMetricChange`). Hence a change of
fibre metric is a `C^k` automorphism of the normal bundle carrying the negative and positive
normal spaces of one metric onto those of the other. No eigenbasis of the normal Hessian is
chosen.

## Main definitions

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `normalMetricChange`: the automorphism of the normal space carrying the negative and positive
  normal spaces for the fibre metric `g` onto those for `g'`.

## Main results

* `map_negativeNormalSpace_normalMetricChange` and `map_positiveNormalSpace_normalMetricChange`:
  the automorphism carries `ν⁻_g` onto `ν⁻_{g'}` and `ν⁺_g` onto `ν⁺_{g'}`.
* `normalMetricChange_self`: for `g' = g` it is the identity.
* `normalSpaceTrivialization_symm_negativeSpectralProjection_apply`: in a normal-bundle
  trivialization, the negative spectral projection of the normal Hessian relative to `g` reads the
  projection onto `ν⁻_g` along `ν⁺_g`.
* `exists_contMDiffOn_projection_negativeNormalSpace`: these projections form a `C^k` family in
  each normal-bundle trivialization.
* `exists_contMDiffOn_normalMetricChange`: in each normal-bundle trivialization the automorphism
  and its inverse are `C^k` families of operators.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Bundle Function Set InnerProductSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E]

section Pointwise

variable [IsManifold I 2 M] (h : i.IsNondegenerateCriticalSubmanifold f)
  (g g' : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The **change of fibre metric** on the normal space of a Morse–Bott submanifold at `s`: the
automorphism which projects the negative normal space for `g` onto the negative normal space for
`g'` along the positive normal space for `g'`, and the positive normal space for `g` onto the
positive normal space for `g'` along the negative normal space for `g'`. -/
def normalMetricChange (s : S) : i.NormalSpace s hn ≃ₗ[ℝ] i.NormalSpace s hn :=
  Submodule.splittingEquiv (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g' s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g s).symm

/-- The change of fibre metric projects the negative part of `v` for `g` onto the negative normal
space for `g'`, and its positive part onto the positive normal space for `g'`. -/
theorem normalMetricChange_apply (s : S) (v : i.NormalSpace s hn) :
    h.normalMetricChange hn g g' s v =
      (h.negativeNormalSpace hn g' s).projection (h.positiveNormalSpace hn g' s)
          (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s)
          ((h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
            (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s) v) +
        (h.positiveNormalSpace hn g' s).projection (h.negativeNormalSpace hn g' s)
          (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s).symm
          ((h.positiveNormalSpace hn g s).projection (h.negativeNormalSpace hn g s)
            (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s).symm v) :=
  Submodule.splittingEquiv_apply _ _ _ _ v

/-- On the negative normal space for `g`, the change of fibre metric is the projection onto the
negative normal space for `g'` along the positive normal space for `g'`. -/
theorem normalMetricChange_apply_of_mem_negativeNormalSpace {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.negativeNormalSpace hn g s) :
    h.normalMetricChange hn g g' s v =
      (h.negativeNormalSpace hn g' s).projection (h.positiveNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s) v :=
  Submodule.splittingEquiv_apply_of_mem_left _ _ _ _ hv

/-- On the positive normal space for `g`, the change of fibre metric is the projection onto the
positive normal space for `g'` along the negative normal space for `g'`. -/
theorem normalMetricChange_apply_of_mem_positiveNormalSpace {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.positiveNormalSpace hn g s) :
    h.normalMetricChange hn g g' s v =
      (h.positiveNormalSpace hn g' s).projection (h.negativeNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s).symm v :=
  Submodule.splittingEquiv_apply_of_mem_right _ _ _ _ hv

/-- **A change of fibre metric carries the negative normal space for `g` onto the negative normal
space for `g'`.** In particular the two negative normal spaces are isomorphic. -/
theorem map_negativeNormalSpace_normalMetricChange (s : S) :
    (h.negativeNormalSpace hn g s).map (h.normalMetricChange hn g g' s : _ →ₗ[ℝ] _) =
      h.negativeNormalSpace hn g' s :=
  Submodule.map_splittingEquiv_left _ _ _ _

/-- **A change of fibre metric carries the positive normal space for `g` onto the positive normal
space for `g'`.** In particular the two positive normal spaces are isomorphic. -/
theorem map_positiveNormalSpace_normalMetricChange (s : S) :
    (h.positiveNormalSpace hn g s).map (h.normalMetricChange hn g g' s : _ →ₗ[ℝ] _) =
      h.positiveNormalSpace hn g' s :=
  Submodule.map_splittingEquiv_right _ _ _ _

/-- Keeping the fibre metric is the identity. -/
@[simp]
theorem normalMetricChange_self (s : S) :
    h.normalMetricChange hn g g s = LinearEquiv.refl ℝ (i.NormalSpace s hn) :=
  Submodule.splittingEquiv_self _

end Pointwise

section Smooth

variable [FiniteDimensional ℝ E'] [IsManifold J 1 S]
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The negative spectral projection in a normal-bundle trivialization.** Let `Q` be the normal
Hessian of a Morse–Bott submanifold at `s`, read in the preferred normal-bundle trivialization `e`
at `s₀`, and let `G` be a fibre metric `g` read in `e`. Then the negative spectral projection of
`Q` relative to `G` reads, through `e`, the projection of the normal space onto the negative normal
space for `g` along the positive normal space for `g`. -/
theorem normalSpaceTrivialization_symm_negativeSpectralProjection_apply [IsManifold I 2 M]
    (h : i.IsNondegenerateCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') {s₀ s : S}
    (hs : s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet) {Q G : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
      ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q u v ∧ Q u v = Q v u)
    (hQinj : Injective Q) (hG : IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) G))
    (hGg : ∀ u v, G u v = g.inner s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
      ((i.normalSpaceTrivialization hn hdim s₀).symm s v)) (u : P) :
    (i.normalSpaceTrivialization hn hdim s₀).symm s (Q.negativeSpectralProjection G u) =
      (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)
        ((i.normalSpaceTrivialization hn hdim s₀).symm s u) := by
  set e := i.normalSpaceTrivialization hn hdim s₀
  set hc := h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s
  set pr := (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s) hc
  let L := e.linearEquivAt ℝ s hs
  have hL (w : P) : L.symm w = e.symm s w := Trivialization.linearEquivAt_symm_apply ..
  -- The projection read in the trivialization.
  let p : P →L[ℝ] P := LinearMap.toContinuousLinearMap (L.toLinearMap ∘ₗ pr ∘ₗ L.symm.toLinearMap)
  have hp (w : P) : L.symm (p w) = pr (L.symm w) := by simp [p]
  have hmem (w : P) : L.symm (p w) ∈ h.negativeNormalSpace hn g s := by
    rw [hp]; exact Submodule.projection_apply_mem hc _
  have hmem' (w : P) : L.symm (w - p w) ∈ h.positiveNormalSpace hn g s := by
    rw [map_sub, hp]; exact Submodule.sub_projection_mem hc _
  have hQ' (w w' : P) : Q w w' = h.normalHessian hn s (L.symm w) (L.symm w') := by
    rw [hL, hL, (hQ w w').1]
  have hG' (w w' : P) : G w w' = g.inner s (L.symm w) (L.symm w') := by rw [hL, hL, hGg]
  have hne {w : P} (hw : w ≠ 0) : L.symm w ≠ 0 := (map_ne_zero_iff _ L.symm.injective).2 hw
  have heq : p = Q.negativeSpectralProjection G := by
    refine (ContinuousLinearMap.eq_negativeSpectralProjection_iff hG (fun w w' ↦ (hQ w w').2)
      hQinj).2 ⟨?_, fun w w' ↦ ?_, fun w w' ↦ ?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · ext w
      apply L.symm.injective
      rw [mul_apply_eq_comp, hp, hp,
        Submodule.projection_apply_of_mem_left hc (Submodule.projection_apply_mem hc _)]
    · rw [hG']
      exact h.inner_eq_zero_of_mem_negativeNormalSpace hn g (hmem w) (hmem' w')
    · rw [hQ']
      exact h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g (hmem w) (hmem' w')
    · rw [hQ']
      exact h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g (hmem w) (hne hw)
    · rw [hQ']
      exact h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g (hmem' w) (hne hw)
  rw [← heq, ← hL, ← hL, hp]

/-- **The projections onto the negative normal spaces are `C^k` in a normal-bundle
trivialization.** Let `i` be a nondegenerate critical submanifold of `f`, with `f` of class
`C^{k+2}` along it and `k ≤ n`, and let `g` be a fibre metric on its normal spaces, read in the
preferred normal-bundle trivialization `e` at `s₀` as a `C^k` family `G` of bilinear forms on the
Euclidean fibre model `P` over a set `U`. Then over the intersection of `U` with the base set of
`e`, the projections of the normal spaces onto the negative normal spaces for `g` along the
positive normal spaces for `g` are read in `e` by a `C^k` family of operators on `P`. -/
theorem exists_contMDiffOn_projection_negativeNormalSpace {k : ℕ∞ω} [IsManifold I (k + 2) M]
    (h : i.IsNondegenerateCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
    (hk : k ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S)
    {U : Set S} {G : S → P →L[ℝ] P →L[ℝ] ℝ}
    (hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G U)
    (hGg : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v,
      G s u v = g.inner s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
        ((i.normalSpaceTrivialization hn hdim s₀).symm s v)) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ p : S → P →L[ℝ] P,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p (U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet) ∧
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u,
        (i.normalSpaceTrivialization hn hdim s₀).symm s (p s u) =
          (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
            (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)
            ((i.normalSpaceTrivialization hn hdim s₀).symm s u) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  set e := i.normalSpaceTrivialization hn hdim s₀
  set V := U ∩ e.baseSet
  obtain ⟨Q, hQ, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  -- The metric read in the trivialization is positive definite.
  have hpos (s : S) (hs : s ∈ V) :
      IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (G s)) := by
    refine isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr
      ⟨fun u v ↦ by rw [hGg s hs, hGg s hs, g.symm], fun u hu ↦ ?_⟩
    rw [hGg s hs]
    refine g.pos s _ ?_
    rw [← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2]
    exact (map_ne_zero_iff _ (e.linearEquivAt ℝ s hs.2).symm.injective).2 hu
  have hmaps (s : S) (hs : s ∈ V) :
      (Q s, G s) ∈ {p : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) |
        (∀ u v, p.1 u v = p.1 v u) ∧ Injective p.1 ∧
          IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) p.2)} :=
    ⟨fun u v ↦ ((hrep s hs.2).1 u v).2, (hrep s hs.2).2, hpos s hs⟩
  refine ⟨fun s ↦ (Q s).negativeSpectralProjection (G s), fun s hs ↦ ?_, fun s hs u ↦
    h.normalSpaceTrivialization_symm_negativeSpectralProjection_apply hn g hdim hs.2
      (hrep s hs.2).1 (hrep s hs.2).2 (hpos s hs) (hGg s hs) u⟩
  -- Smoothness: compose the smooth dependence on the pair of forms with the pair of families.
  have hpair := ((hQ s hs.2).mono inter_subset_right).prodMk_space
    ((hG s hs.1).mono inter_subset_left)
  exact (ContinuousLinearMap.contDiffOn_negativeSpectralProjection.contDiffWithinAt
    (hmaps s hs)).comp_contMDiffWithinAt (f := fun s' ↦ (Q s', G s')) hpair
      fun s' hs' ↦ hmaps s' hs'

/-- **A change of fibre metric is a `C^k` automorphism of the normal bundle.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `k ≤ n`, and
let `g` and `g'` be fibre metrics on its normal spaces. In the preferred normal-bundle
trivialization `e` at `s₀`, with Euclidean fibre model `P`, suppose `g` and `g'` are read as `C^k`
families `G` and `G'` of bilinear forms on `P` over a set `U`. Then over the intersection of `U`
with the base set of `e`, the change of fibre metric `normalMetricChange g g'` and its inverse are
given by `C^k` families `A` and `B` of operators on `P`. The automorphism carries the negative and
positive normal spaces for `g` onto those for `g'`
(`map_negativeNormalSpace_normalMetricChange`, `map_positiveNormalSpace_normalMetricChange`). -/
theorem exists_contMDiffOn_normalMetricChange {k : ℕ∞ω} [IsManifold I (k + 2) M]
    (h : i.IsNondegenerateCriticalSubmanifold f)
    (g g' : RiemannianMetric fun s ↦ i.NormalSpace s hn)
    (hk : k ≤ n) (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S)
    {U : Set S} {G G' : S → P →L[ℝ] P →L[ℝ] ℝ}
    (hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G U)
    (hG' : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G' U)
    (hGg : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v,
      G s u v = g.inner s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
        ((i.normalSpaceTrivialization hn hdim s₀).symm s v))
    (hGg' : haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v,
      G' s u v = g'.inner s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
        ((i.normalSpaceTrivialization hn hdim s₀).symm s v)) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ A B : S → P →L[ℝ] P,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k A (U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet) ∧
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k B (U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet) ∧
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u,
        (i.normalSpaceTrivialization hn hdim s₀).symm s (A s u) =
            h.normalMetricChange hn g g' s ((i.normalSpaceTrivialization hn hdim s₀).symm s u) ∧
          (i.normalSpaceTrivialization hn hdim s₀).symm s (B s u) =
            (h.normalMetricChange hn g g' s).symm
              ((i.normalSpaceTrivialization hn hdim s₀).symm s u) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  set e := i.normalSpaceTrivialization hn hdim s₀
  set V := U ∩ e.baseSet
  obtain ⟨p, hp, hpe⟩ :=
    h.exists_contMDiffOn_projection_negativeNormalSpace hn g hk hf hdim s₀ hG hGg
  obtain ⟨p', hp', hpe'⟩ :=
    h.exists_contMDiffOn_projection_negativeNormalSpace hn g' hk hf hdim s₀ hG' hGg'
  -- In the trivialization, the change of metric is `p' ∘ p + (1 - p') ∘ (1 - p)`.
  set A : S → P →L[ℝ] P := fun s ↦ (p' s).comp (p s) + (1 - p' s).comp (1 - p s)
  have hsub {q : S → P →L[ℝ] P} (hq : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k q V) :
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k (fun s ↦ 1 - q s) V :=
    fun s hs ↦ ContDiff.comp_contMDiffWithinAt (f := q) (g := fun T : P →L[ℝ] P ↦ 1 - T)
      (contDiff_const.sub contDiff_id) (hq s hs)
  have hA : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k A V :=
    (hp'.clm_comp hp).add ((hsub hp').clm_comp (hsub hp))
  have hAe (s : S) (hs : s ∈ V) (u : P) :
      e.symm s (A s u) = h.normalMetricChange hn g g' s (e.symm s u) := by
    have hlin (w w' : P) : e.symm s (w - w') = e.symm s w - e.symm s w' := by
      simp only [← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2, map_sub]
    have hlin' (w w' : P) : e.symm s (w + w') = e.symm s w + e.symm s w' := by
      simp only [← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2, map_add]
    have hA' : A s u = p' s (p s u) + ((u - p s u) - p' s (u - p s u)) := by
      simp [A]
      abel
    rw [hA', hlin', hlin, hlin, hpe s hs, hpe' s hs, hpe' s hs, hlin, hpe s hs,
      normalMetricChange_apply,
      Submodule.projection_eq_self_sub_projection
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s),
      Submodule.projection_eq_self_sub_projection
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s)]
  -- The change of metric is invertible, so its inverse is `C^k` as well.
  let Φ (s : S) (hs : s ∈ V) : P ≃L[ℝ] P :=
    (((e.linearEquivAt ℝ s hs.2).symm.trans (h.normalMetricChange hn g g' s)).trans
      (e.linearEquivAt ℝ s hs.2)).toContinuousLinearEquiv
  have hΦ (s : S) (hs : s ∈ V) : A s = Φ s hs := by
    ext u
    apply (e.linearEquivAt ℝ s hs.2).symm.injective
    simp only [Φ, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Trivialization.linearEquivAt_symm_apply, hAe s hs]
  refine ⟨A, fun s ↦ Ring.inverse (A s), hA, fun s hs ↦ ?_, fun s hs u ↦ ⟨hAe s hs u, ?_⟩⟩
  · have hinv := contDiffAt_ringInverse ℝ (n := k) (Φ s hs).toUnit
    -- The unit `toUnit` has underlying operator `Φ s hs` by definition.
    rw [show ((Φ s hs).toUnit : P →L[ℝ] P) = A s from (hΦ s hs).symm] at hinv
    exact hinv.comp_contMDiffWithinAt (hA s hs)
  · dsimp only
    rw [hΦ s hs, ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.inverse_equiv,
      ← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2,
      ← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2]
    simpa [Φ] using e.symm_apply_apply_mk hs.2 _

end Smooth

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
