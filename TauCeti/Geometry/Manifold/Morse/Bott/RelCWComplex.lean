/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Adjunction
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.ThomPair
public import TauCeti.Topology.CWComplex.Classical.Image
public import TauCeti.Topology.CWComplex.Classical.ThomSpace

/-!
# The cells of a Morse–Bott critical level form a relative CW complex

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on the
level `f = c`, with Morse index `r` along it, and let `g` be a smooth fibre metric on its normal
bundle. For small `ε > 0` the sublevel `M_{c+ε} = {f ≤ c + ε}` strong deformation retracts onto
the lower sublevel `M_{c-ε} = {f ≤ c - ε}` with the negative disc bundle
`D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}` attached along its sphere bundle through a Morse–Bott normal
form `Θ` (`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`
and `IsCriticalSubmanifold.isPushout_negativeDiscBundle`, in the namespace
`TauCeti.SmoothEmbedding`). This file reads that attachment cell by cell: if `S` is a CW complex,
then `M_{c-ε} ∪ Θ(D_ε)` is a CW complex relative to `M_{c-ε}` with one `(m + r)`-cell for each
`m`-cell of `S`. This is Bott's form of Milnor's cell attachment theorem: when `S` is a point it has
a single `0`-cell, and the level contributes one `r`-cell, as for a nondegenerate critical point of
index `r` (`TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation`).

The cells come from those of the disc bundle of a vector bundle over a CW complex relative to its
sphere bundle (`TauCeti.relCWComplexDiscBundleSphereBundle`), glued along the attaching map
(`TauCeti.discBundleAttachmentCellEquiv`). The negative normal spaces form a vector bundle `ν⁻` of
rank `r`, and with the inner product `-(2ε)⁻¹ Hessₛ`
(`IsCriticalSubmanifold.negativeNormalInnerProductSpace`) its unit disc and sphere bundles are
`D_ε` and `S_ε` read through the inclusion of `ν⁻` in the normal bundle. So `Θ` attaches the unit
disc bundle of `ν⁻` to `M_{c-ε}`, and the resulting relative CW structure on the adjunction space
is carried into `M` by the inclusion of the closed set `M_{c-ε} ∪ Θ(D_ε)`.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.exists_relCWComplex_union_negativeDiscBundle`: if the negative normal
  spaces form a vector bundle of rank `r`, `D_ε` is compact and `Θ` is continuous, injective and in
  Morse–Bott normal form on it, then `M_{c-ε} ∪ Θ(D_ε)` is a CW complex relative to `M_{c-ε}` whose
  `k`-cells are the `m`-cells of `S` with `m + r = k`.
* `IsNondegenerateCriticalSubmanifold.exists_relCWComplex_sublevel_deformation`: **the cell
  attachment theorem of a compact Morse–Bott submanifold.** If the band `f⁻¹[c - δ, c + δ]` is
  compact and its critical points lie on `i`, then for some `0 < ε ≤ δ` the sublevel `M_{c+ε}`
  strong deformation retracts onto a CW complex relative to `M_{c-ε}` with one `(m + r)`-cell for
  each `m`-cell of `S`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cells of the disc bundle of a vector bundle over a CW
  complex).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Set Topology Topology.RelCWComplex
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

universe u

section Attachment

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {E' H' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {f : M → ℝ} {n : ℕ∞ω}
  {i : SmoothEmbedding J I n S M} {hn : n ≠ 0} {P : Type*} {h : i.IsCriticalSubmanifold f}
  {g : RiemannianMetric fun s ↦ i.NormalSpace s hn}
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ} {r : ℕ}

namespace IsCriticalSubmanifold

/-- A set `A` of vectors of the negative normal bundle `ν⁻`, whose total space carries the topology
of a subspace of the normal bundle, is homeomorphic to the set `A'` of normal vectors it consists
of. -/
private def negativeNormalSpaceHomeomorph
    (A : Set (TotalSpace (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s))
    (A' : Set (TotalSpace P fun s ↦ i.NormalSpace s hn))
    (hA : ∀ v, v ∈ A ↔ (⟨v.proj, v.snd⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) ∈ A')
    (hA' : ∀ x ∈ A', x.snd ∈ h.negativeNormalSpace hn g x.proj) :
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    A ≃ₜ A' :=
  letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  have hι := isEmbedding_totalSpace_subbundle P (Fin r → ℝ) (h.negativeNormalSpace hn g)
  -- Unlike `Topology.IsEmbedding.homeomorphImage`, the inverse is explicit, so that these
  -- homeomorphisms commute with the inclusions of sphere bundles in disc bundles by `rfl`.
  { toFun v := ⟨⟨v.val.proj, v.val.snd⟩, (hA v.val).1 v.property⟩
    invFun x := ⟨⟨x.val.proj, ⟨x.val.snd, hA' x.val x.property⟩⟩, (hA _).2 x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := (hι.continuous.comp continuous_subtypeVal).subtype_mk _
    continuous_invFun := (hι.continuous_iff.2 continuous_subtypeVal).subtype_mk _ }

variable [T2Space M] [FiniteDimensional ℝ E'] [IsManifold J 1 S] [T2Space S]
  [CWComplex (univ : Set S)] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The lower sublevel with the negative disc bundle attached is a relative CW complex.** Let
`i : S → M` be a critical submanifold of a continuous function `f` on a Hausdorff manifold, with a
fibre metric `g` on its normal bundle, such that the negative normal spaces have continuous local
frames of size `r`, so that they form a vector bundle `ν⁻` of rank `r`. Suppose that `S` is a CW
complex, that for some `ε > 0` the negative disc bundle `D_ε` is compact, and that `Θ` is continuous
and injective on `D_ε` and puts `f` there in the Morse–Bott normal form
`f (Θ v) = c + ½ Hessₛ (v, v)`.

Then `{f ≤ c - ε} ∪ Θ(D_ε)` is a CW complex relative to `{f ≤ c - ε}` whose `k`-cells correspond
to the `m`-cells of `S` with `m + r = k`. -/
theorem exists_relCWComplex_union_negativeDiscBundle
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) (hf : Continuous f) (hD : IsCompact (h.negativeDiscBundle hn P g ε))
    (hΘc : ContinuousOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘi : InjOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) :
    ∃ _ : RelCWComplex ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g ε)
        {y | f y ≤ c - ε},
      ∀ k, Nonempty (cell ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g ε) k ≃
        Σ m : {m : ℕ // m + r = k}, cell (univ : Set S) m) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  let := h.negativeNormalNorm hn g hε
  let := h.negativeNormalInnerProductSpace hn g hε
  have : ContinuousFiberNorm (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) :=
    ⟨h.continuous_norm_negativeNormalNorm hn g r hdim hε⟩
  set D := h.negativeDiscBundle hn P g ε
  set L : Set M := {y | f y ≤ c - ε}
  -- `{f ≤ c - ε} ∪ Θ(D_ε)` is obtained by attaching `D_ε` along `S_ε`, and these are the unit disc
  -- and sphere bundles of `ν⁻` for the norm `-(2ε)⁻¹ Hessₛ`.
  obtain ⟨α, χ, -, -, hsq⟩ := isPushout_negativeDiscBundle hf hD hΘc hΘi hΘ
  let eD := negativeNormalSpaceHomeomorph (r := r)
    (discBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s)) D
    (h.mem_discBundle_iff_mem_negativeDiscBundle hn P g r hε)
    fun _ hx ↦ mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx
  let eS := negativeNormalSpaceHomeomorph (r := r)
    (sphereBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s))
    (h.negativeSphereBundle hn P g ε)
    (h.mem_sphereBundle_iff_mem_negativeSphereBundle hn P g r hε)
    fun _ hx ↦ ((mem_negativeSphereBundle hn).1 hx).1
  have hpush : IsPushout (TopCat.ofHom (ContinuousMap.inclusion
        (sphereBundle_subset_discBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s))))
      ((TopCat.isoOfHomeo eS).hom ≫ TopCat.ofHom α) ((TopCat.isoOfHomeo eD).hom ≫ TopCat.ofHom χ)
      (TopCat.ofHom (ContinuousMap.inclusion (subset_union_left : L ⊆ L ∪ Θ '' D))) :=
    hsq.flip.of_iso (TopCat.isoOfHomeo eS).symm (TopCat.isoOfHomeo eD).symm (Iso.refl _)
      (Iso.refl _) rfl
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  let := relCWComplexDiscBundleSphereBundle (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s)
  let := hpush.relCWComplex
  -- Carry the relative CW structure of the adjunction space into `M`.
  have hcl : IsClosedEmbedding (Subtype.val : ↥(L ∪ Θ '' D) → M) :=
    ((isClosed_le hf continuous_const).union
      (hD.image_of_continuousOn hΘc).isClosed).isClosedEmbedding_subtypeVal
  refine ⟨hcl.relCWComplex (C := (univ : Set (TopCat.of ↥(L ∪ Θ '' D))))
    (Subtype.coe_image_univ _) ?_, fun k ↦ ⟨(hcl.relCWComplexCellEquiv _ _ k).trans
      ((discBundleAttachmentCellEquiv _ _ hpush k).trans ?_)⟩⟩
  · ext y
    simp only [mem_image, mem_range]
    exact ⟨fun ⟨_, ⟨x, hx⟩, hxy⟩ ↦ hxy ▸ hx ▸ x.property,
      fun hy ↦ ⟨⟨y, Or.inl hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩⟩
  · exact Equiv.cast (by rw [Module.finrank_fin_fun])

end IsCriticalSubmanifold

end Attachment

section Deformation

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {E' H' P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **The cell attachment theorem of a compact Morse–Bott submanifold.** Let `i : S → M` be a
nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `S` compact, nonempty and a CW complex, `f = c` and
Morse index `r` along `i`, and let `g` be a smooth fibre metric on the normal bundle of `i`. Let
`δ > 0` be such that the band `f⁻¹[c - δ, c + δ]` is compact and all its critical points lie on
`i`.

Then for some `0 < ε ≤ δ` the sublevel `{f ≤ c + ε}` strong deformation retracts onto a CW complex
`C ⊆ {f ≤ c + ε}` relative to the lower sublevel `{f ≤ c - ε}`, whose `k`-cells correspond to the
`m`-cells of `S` with `m + r = k`. The complex is `{f ≤ c - ε}` with the negative disc bundle of
`i` attached through a Morse–Bott normal form
(`IsCriticalSubmanifold.exists_relCWComplex_union_negativeDiscBundle`). -/
theorem exists_relCWComplex_sublevel_deformation [T2Space M] [SecondCountableTopology M]
    [J.Boundaryless] [CompactSpace S] [Nonempty S] [CWComplex (univ : Set S)]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
    {δ : ℝ} (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ range i) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ ∃ (C : Set M) (_ : RelCWComplex C {x | f x ≤ c - ε})
      (hC : C ⊆ {x | f x ≤ c + ε}),
      (∀ k, Nonempty (cell C k ≃ Σ m : {m : ℕ // m + r = k}, cell (univ : Set S) m)) ∧
      ∃ ρ : C({x | f x ≤ c + ε}, C), (∀ x, ρ (ContinuousMap.inclusion hC x) = x) ∧
        Nonempty (((ContinuousMap.inclusion hC).comp ρ).HomotopyRel (ContinuousMap.id _)
          {x | (x : M) ∈ C}) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  have : T2Space S := i.isEmbedding.t2Space
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  set ε := min δ (ε₀ / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hε₀)
  have hband : f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' Icc (c - δ) (c + δ) :=
    preimage_mono (Icc_subset_Icc (by linarith [min_le_left δ (ε₀ / 2)])
      (by linarith [min_le_left δ (ε₀ / 2)]))
  obtain ⟨hsrc, ρ, hρ, ⟨G⟩⟩ := hmain ε ⟨hε, (min_le_right _ _).trans_lt (half_lt_self hε₀)⟩
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) hband)
    ((inter_subset_inter_right _ hband).trans hcrit)
  have hΘ (x) (hx : x ∈ h.negativeDiscBundle hn P g.toRiemannianMetric ε) :=
    hΘf x (hsrc hx)
  -- The negative normal spaces form a smooth vector bundle of rank `r`; `∞ + 2 = ∞` in `ℕ∞ω`.
  have : IsManifold I (∞ + 2) M := inferInstanceAs (IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) S := inferInstanceAs (IsManifold J ∞ S)
  have hV := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) le_rfl
    (fun s ↦ hfs.contMDiffAt) hdim g hr).hasLocalSubbundleFrames
  obtain ⟨hcw, hcells⟩ := h.exists_relCWComplex_union_negativeDiscBundle hdim hV hε
    hfs.continuous (h.isCompact_negativeDiscBundle hn hfs hdim g ε)
    (Θ.contMDiffOn.continuousOn.mono hsrc) (Θ.toPartialEquiv.injOn.mono hsrc) hΘ
  -- The lower sublevel and the image of the negative disc bundle lie in `{f ≤ c}`.
  have hC : {x | f x ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆
      {x | f x ≤ c + ε} := by
    rintro _ (hx | ⟨x, hx, rfl⟩)
    · simp only [mem_ofPred_eq] at hx ⊢
      linarith
    · exact (IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle hΘ hx).trans (by linarith)
  refine ⟨ε, hε, min_le_left _ _, _, hcw, hC, hcells,
    (ContinuousMap.inclusion inter_subset_right).comp ρ, fun x ↦ ?_, ⟨G.cast (by ext; rfl) rfl⟩⟩
  exact congrArg (ContinuousMap.inclusion inter_subset_right) (hρ ⟨x, hC x.property, x.property⟩)

end IsNondegenerateCriticalSubmanifold

end Deformation

end TauCeti.SmoothEmbedding
