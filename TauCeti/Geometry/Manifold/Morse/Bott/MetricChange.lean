/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.NegativeNormal
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
inverses form a `C^k` family as well (`exists_contMDiffOn_normalMetricChange`). The projections
`p` and `p'` come from `exists_contMDiffOn_projection_negativeNormalSpace`. Hence a change of
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
* `normalMetricChange_symm_apply`: the inverse projects `ν⁻_{g'}` onto `ν⁻_g` along `ν⁺_{g'}`, and
  `ν⁺_{g'}` onto `ν⁺_g` along `ν⁻_{g'}`.
* `normalMetricChange_self`: for `g' = g` it is the identity.
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

/-- The inverse change of fibre metric projects the negative part of `v` for `g'` onto the negative
normal space for `g` along the positive normal space for `g'`, and its positive part onto the
positive normal space for `g` along the negative normal space for `g'`. -/
theorem normalMetricChange_symm_apply (s : S) (v : i.NormalSpace s hn) :
    (h.normalMetricChange hn g g' s).symm v =
      (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g' s)
          (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g' s)
          ((h.negativeNormalSpace hn g' s).projection (h.positiveNormalSpace hn g' s)
            (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s) v) +
        (h.positiveNormalSpace hn g s).projection (h.negativeNormalSpace hn g' s)
          (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g s).symm
          ((h.positiveNormalSpace hn g' s).projection (h.negativeNormalSpace hn g' s)
            (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s).symm v) :=
  Submodule.splittingEquiv_symm_apply _ _ _ _ v

/-- On the negative normal space for `g'`, the inverse change of fibre metric is the projection
onto the negative normal space for `g` along the positive normal space for `g'`. -/
theorem normalMetricChange_symm_apply_of_mem_negativeNormalSpace {s : S}
    {v : i.NormalSpace s hn} (hv : v ∈ h.negativeNormalSpace hn g' s) :
    (h.normalMetricChange hn g g' s).symm v =
      (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g' s) v :=
  Submodule.splittingEquiv_symm_apply_of_mem_left _ _ _ _ hv

/-- On the positive normal space for `g'`, the inverse change of fibre metric is the projection
onto the positive normal space for `g` along the negative normal space for `g'`. -/
theorem normalMetricChange_symm_apply_of_mem_positiveNormalSpace {s : S}
    {v : i.NormalSpace s hn} (hv : v ∈ h.positiveNormalSpace hn g' s) :
    (h.normalMetricChange hn g g' s).symm v =
      (h.positiveNormalSpace hn g s).projection (h.negativeNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g s).symm v :=
  Submodule.splittingEquiv_symm_apply_of_mem_right _ _ _ _ hv

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
  -- An endomorphism `T` of the normal space at `s`, read in the trivialization.
  let C (s : S) (hs : s ∈ V) (T : Module.End ℝ (i.NormalSpace s hn)) : P →L[ℝ] P :=
    LinearMap.toContinuousLinearMap ((e.linearEquivAt ℝ s hs.2).conj T)
  have hC (s : S) (hs : s ∈ V) (T : Module.End ℝ (i.NormalSpace s hn)) (u : P) :
      e.symm s (C s hs T u) = T (e.symm s u) := by
    simp only [C, LinearMap.coe_toContinuousLinearMap', LinearEquiv.conj_apply_apply,
      ← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2, LinearEquiv.symm_apply_apply]
  have hAC (s : S) (hs : s ∈ V) : A s = C s hs (h.normalMetricChange hn g g' s) := by
    set L := e.linearEquivAt ℝ s hs.2
    have hL (w : P) : L.symm w = e.symm s w := Trivialization.linearEquivAt_symm_apply ..
    have hpL (w : P) : L.symm (p s w) = (h.negativeNormalSpace hn g s).projection
        (h.positiveNormalSpace hn g s) (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)
        (L.symm w) := by rw [hL, hL, hpe s hs]
    have hpL' (w : P) : L.symm (p' s w) = (h.negativeNormalSpace hn g' s).projection
        (h.positiveNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s) (L.symm w) := by
      rw [hL, hL, hpe' s hs]
    ext u
    apply L.symm.injective
    rw [hL (C s hs _ u), hC s hs, ← hL, LinearEquiv.coe_coe]
    simp only [A, add_apply, ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_add,
      map_sub, hpL, hpL', normalMetricChange_apply, Submodule.projection_eq_self_sub_projection
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s),
      Submodule.projection_eq_self_sub_projection
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s)]
    abel
  -- The change of metric read in the trivialization is a bijection, hence invertible, so its
  -- inverse is `C^k` as well and is the inverse change of metric read in the trivialization.
  have hAu (s : S) (hs : s ∈ V) : IsUnit (A s) := by
    rw [hAC s hs, ContinuousLinearMap.isUnit_iff_bijective]
    convert ((e.linearEquivAt ℝ s hs.2).symm ≪≫ₗ h.normalMetricChange hn g g' s ≪≫ₗ
      e.linearEquivAt ℝ s hs.2).bijective using 1
    ext u
    simp only [C, LinearMap.coe_toContinuousLinearMap', LinearEquiv.conj_apply_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  refine ⟨A, fun s ↦ Ring.inverse (A s), hA, fun s hs ↦ ?_, fun s hs u ↦ ⟨?_, ?_⟩⟩
  · have hinv := contDiffAt_ringInverse ℝ (n := k) (hAu s hs).unit
    rw [IsUnit.unit_spec] at hinv
    exact hinv.comp_contMDiffWithinAt (hA s hs)
  · rw [hAC s hs, hC s hs, LinearEquiv.coe_coe]
  · beta_reduce
    rw [LinearEquiv.eq_symm_apply, ← LinearEquiv.coe_coe, ← hC s hs, ← hAC s hs,
      ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ (hAu s hs), one_apply_eq_self]

end Smooth

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
