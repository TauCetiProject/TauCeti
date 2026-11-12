/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.RelativeProjection
public import TauCeti.Geometry.Manifold.Morse.Bott.Coordinates
public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Local negative normal projections of a Morse–Bott submanifold

Let `i : S → M` be a nondegenerate critical submanifold of a function `f`. At each point of `S`
the normal Hessian is a nondegenerate symmetric bilinear form on the normal space, whose negative
index of inertia is the Morse index of `f` at `i s`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.sigNeg_normalHessian`). Given a fibre
metric on the normal bundle, the normal space therefore splits, orthogonally for the metric and for
the normal Hessian, into a **negative normal space**, on which the normal Hessian is negative
definite, and a positive normal space, on which it is positive definite. The negative normal
spaces are the fibres of the negative normal bundle along which the negative disc bundle of the
critical submanifold is attached.

This file shows that these splittings vary smoothly. In the preferred normal-bundle trivialization
at any point `s₀`, with fibre model `P`, write the fibre metric as a `C^k` family `G` of positive
definite bilinear forms on `P`. Then the projections onto the negative normal spaces along the
positive ones form a `C^k` family of operators on `P` over the base set of the trivialization (or
the part of it where `G` is given). Their ranges and kernels are the negative and positive
relative spectral subspaces of the normal Hessian, read in the trivialization, with respect to `G`
(`LinearMap.BilinForm.relativeSpectralSubspace`); their ranks are the Morse indices of `f` and
their nullities those of `-f`. The projections come from the real-analytic family of relative
spectral projections `TauCeti.exists_contDiffOn_range_eq_relativeSpectralSubspace`, applied to the
normal Hessian, which is a `C^k` family of nondegenerate forms in these coordinates
(`exists_contMDiffOn_normalHessian_normalSpaceTrivialization`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
No eigenbasis of the normal Hessian is chosen, so no smoothly varying eigenvectors are needed, and
`P` needs no inner product.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_contMDiffOn_negativeNormalProjection`: in each normal-bundle trivialization, the
  projections onto the negative normal spaces of a Morse–Bott submanifold relative to a `C^k` fibre
  metric form a `C^k` family, of rank the Morse index; their ranges and kernels are the negative
  and positive relative spectral subspaces.
* `normalSpaceTrivialization_symm_negativeSpectralProjection_apply`: in a normal-bundle
  trivialization, the negative spectral projection of the normal Hessian relative to a fibre
  metric `g` reads the projection onto the negative normal space for `g`
  (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`) along the positive normal
  space for `g`.
* `exists_contMDiffOn_projection_negativeNormalSpace`: these projections form a `C^k` family in
  each normal-bundle trivialization.

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
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]

section NormedSpace

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The negative normal projections of a Morse–Bott submanifold are smooth.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `k ≤ n`, and
let `G` be a `C^k` family of symmetric positive definite bilinear forms on the fibre model `P` over
a set `U`, for instance a fibre metric on the normal bundle read in the preferred normal-bundle
trivialization `e` at `s₀`. Write `N s u v` for the normal Hessian at `s` of the normal vectors
with coordinates `u` and `v`. Then there is a `C^k` family `p` of operators on `P` over the
intersection of `U` with the base set of `e` such that each `p s` is a projection whose range and
kernel are the negative and positive relative spectral subspaces of `N s` with respect to `G s`.
They are orthogonal for both `G s` and `N s`, with `N s` negative definite on the range and
positive definite on the kernel. The rank of `p s` is the Morse index of `f` at `i s`, and its
nullity is the Morse index of `-f`. -/
theorem exists_contMDiffOn_negativeNormalProjection {k : ℕ∞ω} [IsManifold I (k + 2) M]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S)
    {U : Set S} {G : S → P →L[ℝ] P →L[ℝ] ℝ} (hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G U)
    (hGsymm : ∀ s ∈ U, ∀ u v, G s u v = G s v u) (hGpos : ∀ s ∈ U, ∀ u, u ≠ 0 → 0 < G s u u) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ p : S → P →L[ℝ] P,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p (U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet) ∧
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet,
        let e := i.normalSpaceTrivialization hn hdim s₀
        IsIdempotentElem (p s) ∧
        (p s).range = (G s).toBilinForm.relativeSpectralSubspace
          ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Iio 0) ∧
        (p s).ker = (G s).toBilinForm.relativeSpectralSubspace
          ((h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)) (Ioi 0) ∧
        (∀ u v, G s (p s u) (v - p s v) = 0) ∧
        (∀ u v, h.normalHessian hn s (e.symm s (p s u)) (e.symm s (v - p s v)) = 0) ∧
        (∀ u, p s u ≠ 0 → h.normalHessian hn s (e.symm s (p s u)) (e.symm s (p s u)) < 0) ∧
        (∀ u, u - p s u ≠ 0 →
          0 < h.normalHessian hn s (e.symm s (u - p s u)) (e.symm s (u - p s u))) ∧
        Module.finrank ℝ (p s).range = manifoldMorseIndex I f (i s) ∧
        Module.finrank ℝ (p s).ker = manifoldMorseIndex I (-f) (i s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  set e := i.normalSpaceTrivialization hn hdim s₀
  obtain ⟨Q, hQ, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  have hmaps (s : S) (hs : s ∈ U ∩ e.baseSet) :
      (Q s, G s) ∈ {x : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) |
        (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧
          (∀ u v, x.2 u v = x.2 v u) ∧ ∀ u, u ≠ 0 → 0 < x.2 u u} :=
    ⟨fun u v ↦ ((hrep s hs.2).1 u v).2, (hrep s hs.2).2, hGsymm s hs.1, hGpos s hs.1⟩
  obtain ⟨Φ, hΦ, hΦp⟩ := exists_contDiffOn_range_eq_relativeSpectralSubspace (P := P)
  refine ⟨fun s ↦ Φ (Q s, G s), fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · -- Smoothness: compose the smooth dependence on the pair of forms with the pair of families.
    have hpair := ((hQ s hs.2).mono inter_subset_right).prodMk_space
      ((hG s hs.1).mono inter_subset_left)
    exact ((hΦ.of_le le_top).contDiffWithinAt (hmaps s hs)).comp_contMDiffWithinAt
      (f := fun s' ↦ (Q s', G s')) hpair fun s' hs' ↦ hmaps s' hs'
  -- In the trivialization the normal Hessian is `Q s`.
  obtain ⟨hsymm, hinj, -, -⟩ := hmaps s hs
  have hN (u v : P) : h.normalHessian hn s (e.symm s u) (e.symm s v) = Q s u v :=
    ((hrep s hs.2).1 u v).1
  have hQN : (Q s).toBilinForm =
      (h.normalHessian hn s).compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s) := by
    ext u v
    rw [ContinuousLinearMap.toBilinForm_apply, LinearMap.compl₁₂_apply, e.symmₗ_apply hs.2,
      e.symmₗ_apply hs.2, hN]
  obtain ⟨hidem, hrange, hker⟩ := hΦp (Q s) (G s) hsymm hinj (hGsymm s hs.1) (hGpos s hs.1)
  have hGs : (G s).toBilinForm.IsSymm :=
    ContinuousLinearMap.isSymm_toBilinForm_iff.mpr (hGsymm s hs.1)
  have hGp (v : P) (hv : v ≠ 0) : 0 < (G s).toBilinForm v v := hGpos s hs.1 v hv
  have hQs : (Q s).toBilinForm.IsSymm := ContinuousLinearMap.isSymm_toBilinForm_iff.mpr hsymm
  -- The range of `p s` is the negative relative spectral subspace, and the complement `v - p s v`
  -- of its value lies in its kernel, the positive one.
  have hmem (u : P) := hrange ▸ LinearMap.mem_range_self (Φ (Q s, G s) : P →ₗ[ℝ] P) u
  have hsub (v : P) : v - Φ (Q s, G s) v ∈
      (G s).toBilinForm.relativeSpectralSubspace (Q s).toBilinForm (Ioi 0) := by
    rw [← hker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero]
    exact congr($(hidem.eq) v).symm
  -- The inverse trivialization at `s` is an isometry from `Q s` to the normal Hessian.
  let L : QuadraticMap.IsometryEquiv (Q s).toBilinForm.toQuadraticMap
      (h.normalHessian hn s).toQuadraticMap :=
    { (e.linearEquivAt ℝ s hs.2).symm with
      map_app' := fun u ↦ by
        simp only [LinearEquiv.toFun_eq_coe, Trivialization.linearEquivAt_symm_apply,
          LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply, hN] }
  refine ⟨hidem, hrange.trans (by rw [hQN]), hker.trans (by rw [hQN]),
    fun u v ↦ (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace hGs hQs
      Iio_disjoint_Ioi_same (hmem u) (hsub v)).1, fun u v ↦ ?_, fun u hu ↦ ?_, fun u hu ↦ ?_,
    ?_, ?_⟩
  · rw [hN]
    exact (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace hGs hQs
      Iio_disjoint_Ioi_same (hmem u) (hsub v)).2
  · rw [hN]
    exact LinearMap.BilinForm.apply_self_neg_of_mem_relativeSpectralSubspace_Iio hGs hGp hQs
      (hmem u) hu
  · rw [hN]
    exact LinearMap.BilinForm.apply_self_pos_of_mem_relativeSpectralSubspace_Ioi hGs hGp hQs
      (hsub u) hu
  · rw [hrange, LinearMap.BilinForm.finrank_relativeSpectralSubspace_Iio hGs hGp hQs,
      QuadraticMap.Equivalent.sigNeg_eq ⟨L⟩, h.sigNeg_normalHessian hn s]
  · rw [hker, LinearMap.BilinForm.finrank_relativeSpectralSubspace_Ioi hGs hGp hQs,
      QuadraticMap.Equivalent.sigPos_eq ⟨L⟩, h.sigPos_normalHessian hn s]

end NormedSpace

section InnerProductSpace

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

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
      ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q u v)
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
  have hQ' (w w' : P) : Q w w' = h.normalHessian hn s (L.symm w) (L.symm w') := by
    rw [hL, hL, hQ]
  have hG' (w w' : P) : G w w' = g.inner s (L.symm w) (L.symm w') := by rw [hL, hL, hGg]
  have hne {w : P} (hw : w ≠ 0) : L.symm w ≠ 0 := (map_ne_zero_iff _ L.symm.injective).2 hw
  -- `Q` is symmetric and nondegenerate, and `G` is positive definite, as the normal Hessian and
  -- the fibre metric are.
  have hQsymm (w w' : P) : Q w w' = Q w' w := by
    rw [hQ', hQ', (h.isSymm_normalHessian hn s).eq]
  have hQinj : Injective Q := fun w w' hww' ↦ by
    have hker : L.symm (w - w') ∈ LinearMap.ker (h.normalHessian hn s) := by
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨v, rfl⟩ := L.symm.surjective x
      rw [map_sub, LinearMap.map_sub₂, LinearMap.zero_apply, ← hQ', ← hQ', hww', sub_self]
    rwa [h.ker_normalHessian hn s, Submodule.mem_bot, map_eq_zero_iff _ L.symm.injective,
      sub_eq_zero] at hker
  have hG : IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) G) :=
    isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr
      ⟨fun w w' ↦ by rw [hG', hG', g.symm], fun w hw ↦ by rw [hG']; exact g.pos s _ (hne hw)⟩
  -- The projection read in the trivialization.
  let p : P →L[ℝ] P := LinearMap.toContinuousLinearMap (L.conj pr)
  have hp (w : P) : L.symm (p w) = pr (L.symm w) := by
    simp only [p, LinearMap.coe_toContinuousLinearMap', LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]
  have hmem (w : P) : L.symm (p w) ∈ h.negativeNormalSpace hn g s := by
    rw [hp]; exact Submodule.projection_apply_mem hc _
  have hmem' (w : P) : L.symm (w - p w) ∈ h.positiveNormalSpace hn g s := by
    rw [map_sub, hp]; exact Submodule.sub_projection_mem hc _
  have heq : p = Q.negativeSpectralProjection G := by
    refine (ContinuousLinearMap.eq_negativeSpectralProjection_iff hG hQsymm hQinj).2
      ⟨?_, fun w w' ↦ ?_, fun w w' ↦ ?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
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
positive normal spaces for `g` are read in `e` by a `C^k` family of operators on `P`. This
identifies the family of `exists_contMDiffOn_negativeNormalProjection` for the fibre metric `g`. -/
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
  -- Over `V`, the family `G` is symmetric and positive definite, as the fibre metric is.
  have hGsymm (s : S) (hs : s ∈ V) (u v : P) : G s u v = G s v u := by
    rw [hGg s hs, hGg s hs, g.symm]
  have hGpos (s : S) (hs : s ∈ V) (u : P) (hu : u ≠ 0) : 0 < G s u u := by
    rw [hGg s hs, ← Trivialization.linearEquivAt_symm_apply (R := ℝ) e s hs.2]
    exact g.pos s _ ((map_ne_zero_iff _ (e.linearEquivAt ℝ s hs.2).symm.injective).2 hu)
  obtain ⟨p, hp, hprop⟩ := h.exists_contMDiffOn_negativeNormalProjection hn hk hf hdim s₀
    (hG.mono inter_subset_left) hGsymm hGpos
  rw [inter_assoc, inter_self] at hp hprop
  obtain ⟨Q, -, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  refine ⟨p, hp, fun s hs u ↦ ?_⟩
  -- The properties of `p s` characterize the negative spectral projection of `Q s`.
  obtain ⟨hQ, hQinj⟩ := hrep s hs.2
  obtain ⟨hidem, -, -, hpG, hpN, hneg, hpos, -, -⟩ := hprop s hs
  have hN (u v : P) := (hQ u v).1
  simp only [hN] at hpN hneg hpos
  have hGH : IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (G s)) :=
    isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr ⟨hGsymm s hs, hGpos s hs⟩
  rw [(ContinuousLinearMap.eq_negativeSpectralProjection_iff hGH (fun u v ↦ (hQ u v).2)
    hQinj).2 ⟨hidem, hpG, hpN, hneg, hpos⟩]
  exact h.normalSpaceTrivialization_symm_negativeSpectralProjection_apply hn g hdim hs.2 hN
    (hGg s hs) u

end InnerProductSpace

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
