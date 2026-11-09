/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Topology.CWComplex.Classical.Disk
public import TauCeti.Topology.Homotopy.Extension.CWComplex
public import TauCeti.Topology.Homotopy.Extension.Pushout

/-!
# Crossing a critical value between regular levels attaches cells

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, write
`M_t = {f ≤ t}`, and let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and `c` is its
only critical value. This file shows that `M_b` is homotopy equivalent to `M_a` with one cell of
dimension `λ p` attached for each critical point `p` of index `λ p` on the level `c`, by a homotopy
equivalence which is the inclusion `M_a → M_b` on `M_a`
(`TauCeti.IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace`). This is Milnor's Theorem 3.2
between arbitrary regular levels around `c`, in the form of a cell attachment
`M_a ∪_α ⨆ₚ D^{λ p}`: the adjunction space `TauCeti.relCWAdjunctionSpace` of the disjoint union of
disks `TauCeti.sigmaDiskRelCWComplex` along `TauCeti.sigmaDiskAttachingMap α`. Its cells are
the critical points of the level, labelled by their indices
(`TauCeti.sigmaDiskAdjunctionSpaceCellEquiv`).

The attaching maps are explicit. For a small width `ε > 0`, normalized Morse charts `ψ p` at the
critical points give attaching maps `∂D^{λ p} → M_{c-ε}`,
`OpenPartialHomeomorph.morseAttachingMap`, the restriction of `w ↦ ψ p⁻¹(√ε • (w, 0))` to the
boundary sphere. The attaching map `α p` into `M_a` is this map followed by a retraction `r` of
`M_{c-ε}` onto `M_a` along the band `f⁻¹[a, c - ε]`, which contains no critical point.

The homotopy equivalence is the composite of three. First, the cells attached to `M_{c-ε}` along
the attaching maps of the charts give the same space as Milnor's
`TauCeti.morseCellAttachment`, the pushout of the coproduct of these maps along the coproduct
of the boundary inclusions of the disks (`TauCeti.isPushout_sigmaDiskAdjunctionSpace`); Milnor's
cell attachment theorem makes its comparison map to `M_{c+ε}` a homotopy equivalence which is the
inclusion on `M_{c-ε}` (`TauCeti.IsMorse.exists_morseCellAttachment_deformation`). Second, the
inclusion `M_{c+ε} → M_b` is a homotopy equivalence across the band `f⁻¹[c + ε, b]`
(`TauCeti.exists_sublevelHomotopyEquiv`). Third, the retraction `r` is a homotopy equivalence with
homotopy inverse the inclusion, and attaching along a cofibration is homotopy invariant under a
change of base (`CategoryTheory.IsPushout.exists_homotopic_id_of_homotopic_id`): attaching the
cells to `M_a` along `r ∘ α` is homotopy equivalent to attaching them to `M_{c-ε}` along `α`, by a
map which is the inclusion on `M_a`.

This is the step by which the sublevels of a Morse function are built cell by cell along a
sequence of regular levels separating its critical values.

## Main results

* `TauCeti.IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace`: if `a < c < b`, the band
  `f⁻¹[a, b]` is compact and `c` is its only critical value, then `M_b` is homotopy equivalent to
  `M_a` with one `λ p`-cell attached at each critical point `p` of index `λ p` on the level `c`, by
  a homotopy equivalence which is the inclusion on `M_a`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2, Remark 3.3 and Theorem 3.5.
-/

public section

noncomputable section

open Function Set Metric Topology CategoryTheory Limits Topology.RelCWComplex
open scoped ContDiff Manifold ContinuousMap

universe u

namespace TauCeti

section Comparison

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type u} {f : M → ℝ} {c ε : ℝ}

/-- If the handle-to-cell comparison `Φ : M_{c-ε} ∪_α ⨆ᵢ D^{k i} → M_{c+ε}` of
`TauCeti.morseCellAttachment` has a left inverse `g` with `Φ ∘ g` homotopic to the identity, then
attaching the cells to `M_{c-ε}` along the same attaching maps, as
`TauCeti.relCWAdjunctionSpace` of `TauCeti.sigmaDiskRelCWComplex k`, gives a space homotopy
equivalent to `M_{c+ε}` by a homotopy equivalence which is the inclusion on `M_{c-ε}`. -/
private theorem exists_homotopyEquiv_sigmaDiskAdjunctionSpace_of_leftInverse
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hε : 0 ≤ ε) (hball : ∀ i, closedBall 0 √ε ⊆ (φ i).target)
    (hf : ∀ i, ∀ y ∈ (φ i).source, f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i y j ^ 2)
    {g : C({x | f x ≤ c + ε}, morseCellAttachment φ k hk hε hball hf)}
    (hg : LeftInverse g (morseCellComparison φ k hk hε hball hf))
    (hΦ : ((morseCellComparison φ k hk hε hball hf).hom.comp g).Homotopic (ContinuousMap.id _)) :
    letI := sigmaDiskRelCWComplex k
    ∃ e : relCWAdjunctionSpace (univ.sigma fun i ↦ (univ : Set (TopCat.disk.{u} (k i))))
        (sigmaDiskAttachingMap fun i ↦ ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i)).hom) ≃ₕ
        {x | f x ≤ c + ε},
      ∀ z, (e (pushout.inr (relCWBaseInclusion _) (TopCat.ofHom (sigmaDiskAttachingMap
        fun i ↦ ((φ i).morseAttachingMap (hk i) hε (hball i) (hf i)).hom)) z) : M) = z := by
  let := sigmaDiskRelCWComplex k
  set Φ := morseCellComparison φ k hk hε hball hf
  -- The two pushouts of the same span are isomorphic, compatibly with the inclusions of
  -- `M_{c-ε}`.
  let iso := (isPushout_sigmaDiskAdjunctionSpace _).isoIsPushout _ _
    (isPushout_morseCellAttachment φ k hk hball hf hε)
  have hiso : pushout.inr _ _ ≫ iso.hom = morseCellAttachmentIncl φ k hk hε hball hf :=
    IsPushout.inl_isoIsPushout_hom _ _ _ _
  refine ⟨⟨(iso.hom ≫ Φ).hom, iso.inv.hom.comp g, ?_, ?_⟩, fun z ↦ ?_⟩
  · have : (iso.inv.hom.comp g).comp (iso.hom ≫ Φ).hom = ContinuousMap.id _ := by
      ext x
      simp [hg _]
    rw [this]
  · have : (iso.hom ≫ Φ).hom.comp (iso.inv.hom.comp g) = Φ.hom.comp g := by
      ext x
      simp
    rw [this]
    exact hΦ
  · rw [← ConcreteCategory.comp_apply, ← Category.assoc, hiso, ConcreteCategory.comp_apply]
    exact coe_morseCellComparison_morseCellAttachmentIncl φ k hk hball hf hε z

end Comparison

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b c : ℝ}

/-- **Crossing a critical value between regular levels attaches cells.** Let `f` be a Morse
function, and let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and `c` is the only
critical value of `f` in `[a, b]`. Then for some width `ε > 0` with `a ≤ c - ε` and
`c + ε ≤ b` there are normalized Morse charts `ψ p` at the critical points `p` on the level `c`,
with pairwise disjoint sources, and a retraction `r` of `M_{c-ε} = {f ≤ c - ε}` onto
`M_a = {f ≤ a}`, such that `M_b = {f ≤ b}` is homotopy equivalent to `M_a` with one cell of
dimension the Morse index `λ p` attached at each `p` along `r ∘ α p`, where `α p` is the attaching
map of the chart `ψ p`. The homotopy equivalence is the inclusion `M_a → M_b` on `M_a`. -/
theorem IsMorse.exists_homotopyEquiv_sigmaDiskAdjunctionSpace (hf : IsMorse I f) (hac : a < c)
    (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) :
    ∃ ε, ∃ hε : 0 < ε, a ≤ c - ε ∧ c + ε ≤ b ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧ (∀ p, ↑p ∈ (ψ p).source ∧ ψ p p = 0) ∧
        ∃ (hball : ∀ p, closedBall 0 √ε ⊆ (ψ p).target)
          (hψ : ∀ p, ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2),
          ∃ r : C({x | f x ≤ c - ε}, {x | f x ≤ a}),
            (∀ x : {x | f x ≤ c - ε}, f x ≤ a → (r x : M) = x) ∧
            letI := sigmaDiskRelCWComplex fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
              manifoldMorseIndex I f p
            ∃ e : relCWAdjunctionSpace (univ.sigma fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
                  (univ : Set (TopCat.disk.{u} (manifoldMorseIndex I f p))))
                (sigmaDiskAttachingMap fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦ r.comp
                  ((ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank
                    hε.le (hball p) (hψ p)).hom) ≃ₕ {x | f x ≤ b},
              ∀ z, (e (pushout.inr (relCWBaseInclusion _) (TopCat.ofHom (sigmaDiskAttachingMap
                fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦ r.comp
                  ((ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank
                    hε.le (hball p) (hψ p)).hom)) z) : M) = z := by
  set k := fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦ manifoldMorseIndex I f p
  have hδ : 0 < min (c - a) (b - c) := lt_min (by linarith) (by linarith)
  have hsub {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) : IsCompact (f ⁻¹' Icc s t) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc hs ht))
  have hδa := min_le_left (c - a) (b - c)
  have hδb := min_le_right (c - a) (b - c)
  obtain ⟨ε, hε, hεδ, ψ, hψd, hψp, hball, hψ, g, hg, hΦ⟩ :=
    hf.exists_morseCellAttachment_deformation (c := c) hδ (hsub (by linarith) (by linarith))
  have hεa : a ≤ c - ε := by linarith
  have hεb : c + ε ≤ b := by linarith
  -- Points of the two collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` are not critical.
  have hreg {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) (hst : t < c ∨ c < s) :
      ∀ x, s ≤ f x → f x ≤ t → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x hsx hxt h0 ↦ by
    have := hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) ⟨by linarith, by linarith⟩
    rcases hst with hst | hst <;> linarith
  obtain ⟨r, hr, ⟨R⟩⟩ := exists_sublevelDeformation hf.contMDiff hεa (hsub le_rfl (by linarith))
    (hreg le_rfl (by linarith) (Or.inl (by linarith)))
  obtain ⟨e₂, he₂⟩ := exists_sublevelHomotopyEquiv hf.contMDiff hεb (hsub (by linarith) le_rfl)
    (hreg (by linarith) le_rfl (Or.inr (by linarith)))
  refine ⟨ε, hε, hεa, hεb, ψ, hψd, hψp, hball, hψ, r, fun x hx ↦ ?_, ?_⟩
  · have h := hr ⟨x, hx⟩
    rw [show sublevelInclusion f a (c - ε) hεa ⟨x, hx⟩ = x from
      Subtype.ext (coe_sublevelInclusion_apply f hεa _)] at h
    rw [h]
  let := sigmaDiskRelCWComplex k
  set α := fun p ↦ ((ψ p).toOpenPartialHomeomorph.morseAttachingMap manifoldMorseIndex_le_finrank
    hε.le (hball p) (hψ p)).hom
  -- Attaching the cells to `M_{c-ε}` gives a space homotopy equivalent to `M_{c+ε}`.
  obtain ⟨e₁, he₁⟩ := exists_homotopyEquiv_sigmaDiskAdjunctionSpace_of_leftInverse
    (fun p ↦ (ψ p).toOpenPartialHomeomorph) k _ hε.le hball hψ hg hΦ.homotopic.symm
  -- Change the base of the attachment from `M_{c-ε}` to `M_a` along `r`, a homotopy equivalence
  -- with homotopy inverse the inclusion.
  let er : {x | f x ≤ c - ε} ≃ₕ {x | f x ≤ a} :=
    { toFun := r
      invFun := sublevelInclusion f a (c - ε) hεa
      left_inv := ⟨R.toHomotopy⟩
      right_inv := by
        rw [show r.comp (sublevelInclusion f a (c - ε) hεa) = ContinuousMap.id _ from
          ContinuousMap.ext hr] }
  obtain ⟨E, -, hE⟩ := er.exists_homotopyEquiv_relCWAdjunctionSpace
    (univ.sigma fun p ↦ (univ : Set (TopCat.disk.{u} (k p)))) (sigmaDiskAttachingMap α)
  have hcomp : sigmaDiskAttachingMap (fun p ↦ r.comp (α p)) = r.comp (sigmaDiskAttachingMap α) := by
    refine ContinuousMap.ext fun x ↦ ?_
    obtain ⟨⟨p, s⟩, rfl⟩ := (sigmaDiskBoundaryHomeomorph k).symm.surjective x
    rw [ContinuousMap.comp_apply, sigmaDiskAttachingMap_apply (n := k),
      sigmaDiskAttachingMap_apply (n := k), ContinuousMap.comp_apply]
  rw [hcomp]
  refine ⟨E.symm.trans (e₁.trans e₂), fun z ↦ ?_⟩
  rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.HomotopyEquiv.trans_apply, hE, he₂,
    he₁]
  exact coe_sublevelInclusion_apply f hεa z

end TauCeti
