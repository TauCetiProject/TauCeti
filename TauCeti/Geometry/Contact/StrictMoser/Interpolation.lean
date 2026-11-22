/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.StrictMoser
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Contact.Interpolation
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.Flow.Transport
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Strict relative Moser stability for contact forms agreeing along a transverse slice

Let `α₀` and `α₁` be one-forms on a boundaryless finite-dimensional σ-compact manifold `M`, let
`ι : S → M` be a closed embedded hypersurface, and let `K` be a subset of its image at whose points
`α₀` is contact. If `α₁` and `α₀` agree at the points of `K` together with their exterior
derivatives, and the Reeb vector of `α₀` is transverse to the hypersurface at the points of `K`,
then there is a partial diffeomorphism `φ` of `M`, defined on open neighbourhoods of `K` and fixing
every point of `K`, with

`φ^* α₁ = α₀`

exactly, on the whole source of `φ`. This is the strict counterpart of the relative Gray theorem
for forms agreeing to first order
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`), which only gives
`φ^* α₁ = g α₀` for a positive function `g`.

The proof is the strict Moser method for the linear interpolation `α_t = α₀ + c(t) (α₁ - α₀)`,
reparametrized by a smooth step function `c`. Along `K` every `α_t` has the value and exterior
derivative of `α₀`, so it is contact there with the Reeb vector of `α₀`; by openness of the contact
condition and of transversality, and compactness of the parameter interval, every `α_t` is contact
on an open neighbourhood of `K` and its Reeb field is transverse to the part of the hypersurface
lying in that neighbourhood. There the Reeb-direction equation `R_(α_t) h_t = -(∂_t α_t)(R_(α_t))`
has a smooth solution `h` vanishing on the hypersurface
(`TauCeti.SmoothForm.exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong`). Since
`∂_t α_t = c'(t) (α₁ - α₀)` vanishes on `K`, the strict Moser vector field of `(α_t, h_t)` vanishes
there (`TauCeti.SmoothForm.strictMoserVectorField_eq_zero_of_comp_eventuallyEq_zero`), and the
relative strict Moser theorem (`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq`) gives
`φ`. Neither `K` nor `M` need be compact.

This is the Moser step of the neighbourhood theorem for Legendrian submanifolds in the form of
Kriegl and Michor: once a first-order identification of a neighbourhood of a closed Legendrian
submanifold `Λ` with a neighbourhood of the zero section of `J¹Λ = T^* Λ × ℝ` makes the model form
`dz - λ_Λ` and the pulled-back contact form agree with their exterior derivatives along the zero
section, the hypersurface `T^* Λ × {0}`, transverse to the Reeb field `∂_z` of the model form, is
the slice of this file.

## Main results

* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt`: strict
  relative Moser stability for two forms joined by a segment of contact forms whose Reeb fields
  are transverse to a closed hypersurface containing `K`.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_apply_eq`: strict relative Moser
  stability for contact forms agreeing to first order along a set `K` contained in a closed
  hypersurface transverse to the Reeb field of `α₀` at the points of `K`.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5.
-/

public section

noncomputable section

open Set Module
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [BoundarylessManifold J S] [TopologicalSpace.PseudoMetrizableSpace S]
  {α₀ α₁ : SmoothForm I M ℝ 1} {ι : S → M}

/-! ### Strict relative Moser stability along a segment of contact forms -/

/-- **Strict relative Moser stability along a segment of contact forms.** Let every interpolation
`α₀ + u (α₁ - α₀)`, `u ∈ [0, 1]`, be a contact form on a boundaryless σ-compact manifold `M`, with
Reeb vector field transverse to a closed embedded hypersurface `ι : S → M`, and let `α₁` agree with
`α₀` at the points of a set `K` contained in the hypersurface. Then there is a smooth partial
diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which fixes every
point of `K` and pulls `α₁` back to `α₀` on its source. Neither `K` nor `M` need be compact. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt
    [TopologicalSpace.PseudoMetrizableSpace M] [SigmaCompactSpace M]
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hc : ∀ x, ∀ u ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + u • (α₁ - α₀)).val x)
    (htr : ∀ u ∈ Icc (0 : ℝ) 1, IsTransverseAlong J (α₀ + u • (α₁ - α₀)).reebVectorField ι)
    {K : Set M} (hKι : K ⊆ range ι) (hval : ∀ x ∈ K, α₁.val x = α₀.val x) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ α₁.val x = α₀.val x := by
  -- The segment, reparametrized by the smooth step function, is a smooth family `α_t` of contact
  -- forms whose Reeb fields are transverse to the hypersurface.
  set α := lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤))
  have hχ (t : ℝ) : Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hcα (t : ℝ) :
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm := by
    rw [mpullback_prodMk_lineMapFamily, isContactForm_iff_forall_isContactFormAt]
    exact fun x ↦ hc x _ (hχ t)
  have htrα (t : ℝ) : IsTransverseAlong J
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField ι := by
    rw [mpullback_prodMk_lineMapFamily]
    exact htr _ (hχ t)
  obtain ⟨U, hU, hιU, h, hh, h0, hR⟩ :=
    exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong hcα hι himm hind hclosed
      htrα hdim
  -- The velocity `∂_t α_t = c'(t) (α₁ - α₀)` vanishes on `K`, so the strict Moser field does too.
  have hK (x : M) (hx : x ∈ K) (u : ℝ) : α.strictMoserVectorField h u x = 0 := by
    obtain ⟨s, rfl⟩ := hKι hx
    refine strictMoserVectorField_eq_zero_of_comp_eventuallyEq_zero (hcα u) hdim (himm s)
      (isTransverseAlong_iff.1 (htrα u) s) (.of_forall fun s' ↦ h0 u s') (hR (u, ι s) (hιU u s)) ?_
    rw [mpullback_prodMk_timeDeriv_lineMapFamily, Submodule.coe_smul, Pi.smul_apply,
      Submodule.coe_sub, Pi.sub_apply, hval _ hx, sub_self, smul_zero]
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ := exists_partialDiffeomorph_mpullback_eq hcα hh hK hU
    (s := 0) (t := 1) (fun x hx u _ ↦ by obtain ⟨s, rfl⟩ := hKι hx; exact hιU u s) hR
  refine ⟨φ, hsrc, htgt, hfix, fun x hx ↦ ?_⟩
  -- The slices of the family at times `1` and `0` are `α₁` and `α₀`.
  have h1 := hφ x hx
  rw [mpullback_prodMk_lineMapFamily, mpullback_prodMk_lineMapFamily, Real.smoothTransition.one,
    Real.smoothTransition.zero, one_smul, zero_smul, add_zero, add_sub_cancel] at h1
  exact h1

/-! ### Forms agreeing to first order along a transverse slice -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- Along a set where `α₁` agrees with `α₀` together with its exterior derivative, every
interpolation `α₀ + u (α₁ - α₀)` has the Reeb vector of `α₀`. -/
private theorem reebVectorField_add_smul_sub_eq {x : M} (hval : α₁.val x = α₀.val x)
    (hd : mextDeriv α₁.val x = mextDeriv α₀.val x) (u : ℝ) :
    (α₀ + u • (α₁ - α₀)).reebVectorField x = α₀.reebVectorField x := by
  refine reebVectorField_congr ?_ ?_
  · rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, hval, sub_self, smul_zero, add_zero]
  · rw [← mextDerivₗ_apply, ← mextDerivₗ_apply, map_add, map_smul, map_sub, Submodule.coe_add,
      Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      mextDerivₗ_apply, mextDerivₗ_apply, hd, sub_self, smul_zero, add_zero]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [IsManifold J ∞ S]
  [BoundarylessManifold J S] [TopologicalSpace.PseudoMetrizableSpace S] in
/-- The part of the hypersurface `ι` over an open subset `U` of `M`, as a map from the open subset
`ι⁻¹(U)` of `S` into `U`, is again a smooth immersion and an inducing map, with the same
differential, whose image is the trace of the image of `ι` in `U`. -/
private theorem exists_restrict_preimage (hι : ContMDiff J I ∞ ι)
    (hind : Topology.IsInducing ι) (U : TopologicalSpace.Opens M) :
    ∃ ι' : (⟨ι ⁻¹' U, U.isOpen.preimage hι.continuous⟩ : TopologicalSpace.Opens S) → U,
      ContMDiff J I ∞ ι' ∧ (∀ s, (ι' s : M) = ι s) ∧
      (∀ s (v : TangentSpace J s), mfderiv J I ι' s v = mfderiv J I ι s v) ∧
      Topology.IsInducing ι' ∧ ∀ y : U, y ∈ range ι' ↔ (y : M) ∈ range ι := by
  set ι' : (⟨ι ⁻¹' U, U.isOpen.preimage hι.continuous⟩ : TopologicalSpace.Opens S) → U :=
    fun s ↦ ⟨ι s, s.property⟩
  -- Composed with the inclusion of `U`, `ι'` is `ι` composed with the inclusion of `ι⁻¹(U)`.
  have hcomp : Subtype.val ∘ ι' = ι ∘ Subtype.val := rfl
  refine ⟨ι', (ContMDiff.subtypeVal_comp_iff U ι').1 (hcomp ▸ hι.comp contMDiff_subtypeVal),
    fun _ ↦ rfl, fun s v ↦ ?_, ?_, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [← Manifold.mfderiv_subtype_val_comp_apply, hcomp, Manifold.mfderiv_comp_subtype_val_apply]
  · exact Topology.IsInducing.subtypeVal.of_comp_iff.1 (hcomp ▸ hind.comp .subtypeVal)
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨s, show ι s ∈ U from hs ▸ y.property⟩, Subtype.ext hs⟩

omit [TopologicalSpace.PseudoMetrizableSpace S] in
/-- Let every interpolation `α₀ + u (α₁ - α₀)`, `u ∈ [0, 1]`, be contact on an open set `N`, and
let `c` be the smooth step function. The pairs `(t, s)`, with `ι s ∈ N`, at which the Reeb field of
`α₀ + c(t) (α₁ - α₀)` is transverse to the hypersurface `ι` form an open set. -/
private theorem exists_isOpen_iff_notMem_range_mfderiv (hι : ContMDiff J I ∞ ι)
    (himm : ∀ s, Function.Injective (mfderiv J I ι s)) (hind : Topology.IsInducing ι)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {N : Set M} (hN : IsOpen N)
    (hcN : ∀ x ∈ N, ∀ u ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + u • (α₁ - α₀)).val x) :
    ∃ O : Set (ℝ × (⟨ι ⁻¹' N, hN.preimage hι.continuous⟩ : TopologicalSpace.Opens S)),
      IsOpen O ∧ ∀ t s, (t, s) ∈ O ↔
        (α₀ + Real.smoothTransition t • (α₁ - α₀)).reebVectorField (ι s) ∉
          (mfderiv J I ι s).range := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨∅, isOpen_empty, fun _ s ↦ isEmptyElim (s : S)⟩
  have : FiniteDimensional ℝ E' := by
    have : FiniteDimensional ℝ (TangentSpace I (ι s₀)) := inferInstanceAs (FiniteDimensional ℝ E)
    exact FiniteDimensional.of_injective (mfderiv J I ι s₀).toLinearMap (himm s₀)
  -- On `W = N`, the restricted segment reparametrized by the smooth step function is a smooth
  -- family `β_t` of contact forms, so its vertical Reeb field on `ℝ × W` is smooth.
  set W : TopologicalSpace.Opens M := ⟨N, hN⟩
  set β := lineMapFamily (mpullback (Subtype.val : W → M) contMDiff_subtypeVal α₀)
    (mpullback (Subtype.val : W → M) contMDiff_subtypeVal α₁)
    (Real.smoothTransition.contDiff (n := ⊤))
  have hslice (t : ℝ) : mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β =
      mpullback (Subtype.val : W → M) contMDiff_subtypeVal
        (α₀ + Real.smoothTransition t • (α₁ - α₀)) := by
    rw [mpullback_prodMk_lineMapFamily, map_add, map_smul, map_sub]
  have hcβ (t : ℝ) :
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).IsContactForm := by
    rw [hslice, isContactForm_iff_forall_isContactFormAt]
    exact fun y ↦ (isContactFormAt_mpullback_subtype_val_iff _ y).2 (hcN y y.property _
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  obtain ⟨ι₀, hι₀, hι₀ι, hdι₀, -, -⟩ := exists_restrict_preimage hι hind W
  have himm₀ (s) : Function.Injective (mfderiv J I ι₀ s) := fun v v' hv ↦
    himm s (by rw [← hdι₀, ← hdι₀]; exact hv)
  -- The pairs `(t, s)` at which the vertical Reeb field of `β` is transverse to `id × ι₀` form an
  -- open set.
  refine ⟨_, isOpen_setOf_notMem_range_mfderiv (Z := verticalField 𝓘(ℝ, ℝ) fun t ↦
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).reebVectorField)
    (contMDiff_verticalField (contMDiff_reebVectorField_mpullback_prodMk β hcβ))
    (contMDiff_id.prodMap hι₀) (fun q ↦ ?_)
    (by rw [Module.finrank_prod, Module.finrank_prod, ← hdim]; ring), fun t s ↦ ?_⟩
  · rw [mfderiv_prodMap mdifferentiableAt_id (hι₀.mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.Injective.prodMap (fun _ _ h ↦ h) (himm₀ q.2)
  -- At `(t, s)`, transversality to `id × ι₀` is transversality of the Reeb field of `β_t` to `ι₀`,
  -- and that Reeb field is the one of `α₀ + c(t) (α₁ - α₀)`.
  rw [mem_ofPred_eq, mfderiv_prodMap mdifferentiableAt_id (hι₀.mdifferentiableAt (by simp)),
    mfderiv_id, not_iff_not, Prod.map_apply, verticalField_apply, hslice,
    reebVectorField_mpullback_subtype_val]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.2, (hdι₀ s w.2).symm.trans ((congrArg Prod.snd hw).trans (by rw [hι₀ι]; rfl))⟩
  · rintro ⟨w, hw⟩
    exact ⟨((0 : ℝ), w), Prod.ext rfl ((hdι₀ s w).trans (hw.trans (by rw [hι₀ι]; rfl)))⟩

omit [TopologicalSpace.PseudoMetrizableSpace S] in
/-- **Transversality persists near a transverse slice.** Let every interpolation
`α₀ + u (α₁ - α₀)`, `u ∈ [0, 1]`, be contact on an open set `N`, and let `K ⊆ N` be a set on the
hypersurface along which `α₁` agrees to first order with `α₀`, whose Reeb field is transverse to
the hypersurface there. Then there is an open neighbourhood `V` of `K` such that the Reeb field of
every interpolation is transverse to the hypersurface at its points in `N ∩ V`. -/
private theorem exists_isOpen_forall_notMem_range_mfderiv (hι : ContMDiff J I ∞ ι)
    (himm : ∀ s, Function.Injective (mfderiv J I ι s)) (hind : Topology.IsInducing ι)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {N : Set M} (hN : IsOpen N)
    (hcN : ∀ x ∈ N, ∀ u ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + u • (α₁ - α₀)).val x)
    {K : Set M} (hKN : K ⊆ N) (hKι : K ⊆ range ι) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, mextDeriv α₁.val x = mextDeriv α₀.val x)
    (htr : ∀ s, ι s ∈ K → α₀.reebVectorField (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ ∀ s, ι s ∈ N → ι s ∈ V → ∀ u ∈ Icc (0 : ℝ) 1,
      (α₀ + u • (α₁ - α₀)).reebVectorField (ι s) ∉ (mfderiv J I ι s).range := by
  obtain ⟨O, hOo, hOmem⟩ := exists_isOpen_iff_notMem_range_mfderiv hι himm hind hdim hN hcN
  -- Since `[0, 1]` is compact, the points `s` with `[0, 1] × {s} ⊆ O` form an open set `S₁`, which
  -- is the trace on the hypersurface of an open set `V` of `M`.
  set S₁ := {s | ∀ t ∈ Icc (0 : ℝ) 1, (t, s) ∈ O}
  have hS₁ : IsOpen S₁ := isOpen_iff_mem_nhds.2 fun s hs ↦
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
      (hOo.preimage continuous_swap).mem_nhds (hs t ht)
  obtain ⟨V, hV, hVS⟩ := hind.isOpen_iff.1
    ((TopologicalSpace.Opens.isOpenEmbedding' _).isOpenMap S₁ hS₁)
  refine ⟨V, hV, fun x hx ↦ ?_, fun s hsN hsV u hu ↦ ?_⟩
  · -- Along `K`, every interpolation has the Reeb field of `α₀`, transverse by hypothesis.
    obtain ⟨s, rfl⟩ := hKι hx
    have hs : s ∈ ι ⁻¹' V := by
      rw [hVS]
      refine ⟨⟨s, hKN hx⟩, fun t _ ↦ (hOmem t _).2 ?_, rfl⟩
      rw [reebVectorField_add_smul_sub_eq (hval _ hx) (hd _ hx)]
      exact htr s hx
    exact hs
  · -- The step function takes every value `u ∈ [0, 1]` on `[0, 1]`.
    rw [← mem_preimage, hVS] at hsV
    obtain ⟨s', hs', rfl⟩ := hsV
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc zero_le_one
      Real.smoothTransition.continuous.continuousOn
      (by rwa [Real.smoothTransition.zero, Real.smoothTransition.one])
    exact (hOmem t s').1 (hs' t ht)

/-- **Strict relative Moser stability for contact forms agreeing to first order along a transverse
slice.** Let `ι : S → M` be a closed embedded hypersurface of a boundaryless σ-compact manifold
`M`, and let `K` be a subset of its image. Let `α₀` be contact at the points of `K`, with Reeb
vector transverse to the hypersurface there, and let `α₁` agree with `α₀` at the points of `K`,
together with its exterior derivative. Then there is a smooth partial diffeomorphism `φ` of `M`,
whose source and target are open neighbourhoods of `K`, which fixes every point of `K` and pulls
`α₁` back to `α₀` on its source. Neither `K` nor `M` need be compact, and the forms are only
assumed contact at the points of `K`. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_apply_eq [SigmaCompactSpace M]
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) {K : Set M} (hKι : K ⊆ range ι)
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, mextDeriv α₁.val x = mextDeriv α₀.val x)
    (htr : ∀ s, ι s ∈ K → α₀.reebVectorField (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ α₁.val x = α₀.val x := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · -- For empty `K`, the partial diffeomorphism with empty source will do.
    refine ⟨(Diffeomorph.refl I M ∞).toPartialDiffeomorph.restrOpen ∅ isOpen_empty, by simp,
      by simp, by simp, fun x hx ↦ ?_⟩
    simp at hx
  -- Restrict to an open neighbourhood `W` of `K` on which the segment is contact and transverse.
  obtain ⟨N, hN, hKN, hcN⟩ := exists_isOpen_forall_isContactFormAt_add_smul_sub hc hval
    fun x hx v _ w _ ↦ by rw [hd x hx]
  obtain ⟨V, hV, hKV, htrV⟩ :=
    exists_isOpen_forall_notMem_range_mfderiv hι himm hind hdim hN hcN hKN hKι hval hd htr
  set W : TopologicalSpace.Opens M := ⟨N ∩ V, hN.inter hV⟩
  have hW : Nonempty W := ⟨⟨x₀, hKN hx₀, hKV hx₀⟩⟩
  have := Manifold.sigmaCompactSpace_opens I W
  have := Manifold.metrizableSpace I W
  set res : SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I W ℝ 1 :=
    mpullback (Subtype.val : W → M) contMDiff_subtypeVal
  have hres (u : ℝ) : res α₀ + u • (res α₁ - res α₀) = res (α₀ + u • (α₁ - α₀)) := by
    rw [map_add, map_smul, map_sub]
  obtain ⟨ι₂, hι₂, hι₂ι, hdι₂, hind₂, hrange₂⟩ := exists_restrict_preimage hι hind W
  have : TopologicalSpace.PseudoMetrizableSpace
      (⟨ι ⁻¹' W, W.isOpen.preimage hι.continuous⟩ : TopologicalSpace.Opens S) :=
    Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  have htrW (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      IsTransverseAlong J (res α₀ + u • (res α₁ - res α₀)).reebVectorField ι₂ := by
    refine isTransverseAlong_iff.2 fun s ⟨w, hw⟩ ↦ htrV s (hι₂ι s ▸ (ι₂ s).property.1)
      (hι₂ι s ▸ (ι₂ s).property.2) u hu ⟨w, ?_⟩
    rw [hres, reebVectorField_mpullback_subtype_val, ContinuousLinearMap.coe_coe, hdι₂] at hw
    rw [ContinuousLinearMap.coe_coe, hw, hι₂ι]
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ :=
    exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt hι₂
      (fun s v v' hv ↦ himm s (by rw [← hdι₂, ← hdι₂]; exact hv)) hind₂
      (by rw [show range ι₂ = Subtype.val ⁻¹' range ι from ext hrange₂]
          exact hclosed.preimage continuous_subtypeVal)
      hdim (fun y u hu ↦ hres u ▸ (isContactFormAt_mpullback_subtype_val_iff _ y).2
        (hcN y y.property.1 u hu)) htrW (K := Subtype.val ⁻¹' K)
      (fun y hy ↦ (hrange₂ y).2 (hKι hy))
      fun y hy ↦ (coe_mpullback_subtype_val_apply α₁ y).trans
        ((hval y hy).trans (coe_mpullback_subtype_val_apply α₀ y).symm)
  -- Read `φ` in `M`.
  refine ⟨φ.liftOpens hW hW, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · exact (PartialDiffeomorph.liftOpens_source φ hW hW).symm ▸ ⟨⟨x, hKN hx, hKV hx⟩, hsrc hx, rfl⟩
  · exact (PartialDiffeomorph.liftOpens_target φ hW hW).symm ▸ ⟨⟨x, hKN hx, hKV hx⟩, htgt hx, rfl⟩
  · exact (φ.liftOpens_apply_coe hW hW ⟨x, hKN hx, hKV hx⟩).trans
      (congrArg Subtype.val (hfix ⟨x, hKN hx, hKV hx⟩ hx))
  rw [PartialDiffeomorph.liftOpens_source] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mpullback_liftOpens_apply_coe φ (by simp) hW hW α₁.val hy, ← coe_mpullback]
  exact (hφ y hy).trans (coe_mpullback_subtype_val_apply α₀ y)

end TauCeti.SmoothForm
