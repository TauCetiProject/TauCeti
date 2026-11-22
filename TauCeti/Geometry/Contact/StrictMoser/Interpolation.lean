/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Interpolation
public import TauCeti.Geometry.Contact.StrictMoser
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Strict interpolation of contact forms agreeing along a transverse slice

Two contact forms on a manifold `M` that agree to first order along a set `K` are related near `K`
by a contactomorphism fixing `K` which preserves the contact structures
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`): it pulls `α₁` back
to a positive multiple of `α₀`. This file proves the **strict** version, with `φ^* α₁ = α₀`
exactly, when `K` lies in a hypersurface which is tangent to the contact hyperplanes along `K`.

The proof is the strict Moser method for the interpolation `α_t = α₀ + t (α₁ - α₀)`. The strict
Moser vector field `X_t` solves `L_(X_t) α_t = -∂_t α_t = α₀ - α₁` once a function `h_t = α_t(X_t)`
solving the Reeb-direction equation `R_(α_t) h_t = (α₀ - α₁)(R_(α_t))` is given. Such an `h` exists
near a closed embedded hypersurface `ι : S → M` transverse to every Reeb field `R_(α_t)`, with zero
values on the hypersurface
(`TauCeti.SmoothForm.exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong`), and then
`X_t` vanishes at the points of the hypersurface where `α₀` and `α₁` agree. So the time-one map of
the strict Moser isotopy fixes `K` and pulls `α₁` back to `α₀` on a neighbourhood of `K`:

* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_isTransverseAlong`: for any smooth
  family of contact forms, with a closed hypersurface transverse to all its Reeb fields, the strict
  Moser isotopy fixes the points of the hypersurface where the family does not move;
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt`: the case
  of the segment from `α₀` to `α₁`, when all its forms are contact.

In the main theorem the interpolations are only contact near `K`, and the hypersurface is only
transverse to their Reeb fields near `K`. Transversality is propagated from `K` by a one-form `β`
which vanishes on the tangent spaces of the hypersurface and equals `α₀` at the points of `K`: at
those points `β(R_(α_t)) = α_t(R_(α_t)) = 1`, and positivity of `β(R_(α_t))` for all `t ∈ [0, 1]`
is an open condition which excludes tangency to the hypersurface. Restricting to the open set
where it holds gives

* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_apply_eq`: if `α₀` is contact
  along `K`, `α₁ = α₀` and `dα₁ = dα₀` on `ker α₀` at the points of `K`, and `K` lies in such a
  hypersurface, there is a partial diffeomorphism fixing `K`, defined on open neighbourhoods of
  `K`, which pulls `α₁` back to `α₀`.

Neither `K` nor `M` need be compact. The hypersurface hypothesis is met by the zero section of the
one-jet bundle `T^* L × ℝ` with its contact form `dz - λ`, inside the slice `z = 0`, with `β = dz`.
This is the Moser step of the neighbourhood theorem for Legendrian submanifolds, in which the
pullback of a contact form along a tubular map is compared with `dz - λ` near the zero section.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS, 1997, Proposition 43.18.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109,
  Cambridge University Press, 2008, Section 2.5.
-/

public section

noncomputable section

open Bundle Set Module Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [BoundarylessManifold J S] {ι : S → M}

/-! ### The strict Moser isotopy fixing a transverse slice -/

section Family

variable [TopologicalSpace.PseudoMetrizableSpace M] [SigmaCompactSpace M]

/-- **The relative strict Moser theorem along a transverse slice.** Let `α_t` be a smooth family
of contact forms on a boundaryless σ-compact manifold `M`, and let `ι : S → M` be a smooth
embedding with closed image of a boundaryless manifold of one dimension less, to which every Reeb
vector field `R_(α_t)` is transverse. Let `K` be a set of points of the image of `ι` at which the
family does not move: `∂_t α_t` vanishes there at all times. Then for any two times `s` and `t`
there is a smooth partial diffeomorphism `φ` of `M`, whose source and target are open
neighbourhoods of `K`, which fixes every point of `K` and pulls `α_t` back to `α_s` exactly. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_isTransverseAlong
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (htr : ∀ t, IsTransverseAlong J
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField ι)
    {K : Set M} (hKι : K ⊆ range ι)
    (hK : ∀ x ∈ K, ∀ t,
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val x = 0)
    (s t : ℝ) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x =
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  -- The slice is metrizable, as a subspace of `M`.
  have := hind.pseudoMetrizableSpace
  obtain ⟨U, hU, hιU, h, hh, h0, hR⟩ :=
    exists_contMDiff_mvfderiv_reebVectorField_eq_of_isTransverseAlong hc hι himm hind hclosed htr
      hdim
  -- The strict Moser vector field vanishes on `K` at all times.
  have hX (x : M) (hx : x ∈ K) (u : ℝ) : α.strictMoserVectorField h u x = 0 := by
    obtain ⟨σ, rfl⟩ := hKι hx
    exact strictMoserVectorField_eq_zero_of_comp_eventuallyEq_zero (hc u) hdim (himm σ)
      (isTransverseAlong_iff.1 (htr u) σ)
      (.of_forall fun σ' ↦ h0 u σ') (hR (u, ι σ) (hιU u σ)) (hK _ hx u)
  exact exists_partialDiffeomorph_mpullback_eq hc hh hX hU
    (fun x hx u _ ↦ by obtain ⟨σ, rfl⟩ := hKι hx; exact hιU u σ) hR

/-- **Strict interpolation along a segment of contact forms.** Let every interpolation
`α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, be a contact form on a boundaryless σ-compact manifold `M`, and
let `ι : S → M` be a smooth embedding with closed image of a boundaryless manifold of one dimension
less, to which the Reeb vector field of every interpolation is transverse. If `α₁` agrees with
`α₀` at the points of a subset `K` of the image of `ι`, there is a smooth partial diffeomorphism
`φ` of `M`, whose source and target are open neighbourhoods of `K`, which fixes every point of `K`
and pulls `α₁` back to `α₀` exactly on its source. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt
    {α₀ α₁ : SmoothForm I M ℝ 1}
    (hc : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x)
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (htr : ∀ s ∈ Icc (0 : ℝ) 1, IsTransverseAlong J (α₀ + s • (α₁ - α₀)).reebVectorField ι)
    {K : Set M} (hKι : K ⊆ range ι) (hval : ∀ x ∈ K, α₁.val x = α₀.val x) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ α₁.val x = α₀.val x := by
  -- The segment, reparametrized by the smooth step function, is a smooth family of contact forms.
  have hst (t : ℝ) : Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hcα (t : ℝ) : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).IsContactForm := by
    rw [mpullback_prodMk_lineMapFamily, isContactForm_iff_forall_isContactFormAt]
    exact fun x ↦ hc x _ (hst t)
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ := exists_partialDiffeomorph_mpullback_eq_of_isTransverseAlong
    hcα hι himm hind hclosed hdim
    (fun t ↦ by rw [mpullback_prodMk_lineMapFamily]; exact htr _ (hst t)) hKι
    (fun x hx t ↦ mpullback_prodMk_timeDeriv_lineMapFamily_apply_eq_zero _ (hval x hx) t) 0 1
  refine ⟨φ, hsrc, htgt, hfix, fun x hx ↦ ?_⟩
  simpa [Real.smoothTransition.one, Real.smoothTransition.zero] using hφ x hx

end Family

omit [I.Boundaryless] [T2Space M] in
/-- At the points of an open set `N` on which all interpolations `α₀ + s (α₁ - α₀)`,
`s ∈ [0, 1]`, are contact, positivity of a one-form `β` on their Reeb vectors is an open
condition. The interpolations are indexed by `c(t)`, `t ∈ [0, 1]`, for the smooth step function
`c`. -/
private theorem isOpen_setOf_forall_pos_apply_reebVectorField {α₀ α₁ β : SmoothForm I M ℝ 1}
    {N : Set M} (hN : IsOpen N)
    (hcN : ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x) :
    IsOpen {x | x ∈ N ∧ ∀ t ∈ Icc (0 : ℝ) 1, 0 < β.val x
      ![(α₀ + Real.smoothTransition t • (α₁ - α₀)).reebVectorField x]} := by
  set A := lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤))
  set g : ℝ × M → ℝ := fun q ↦ β.val q.2
    ![(mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) A).reebVectorField q.2]
  -- `g` is continuous at the points over `N`, where all slices of `A` are contact.
  have hg (p : ℝ × M) (hp : p.2 ∈ N) : ContinuousAt g p := by
    have hc : ∀ᶠ q in 𝓝 p, IsContactFormAt
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) A).val q.2 :=
      mem_of_superset ((hN.preimage continuous_snd).mem_nhds hp) fun q hq ↦ by
        simp only [mem_ofPred_eq, A, mpullback_prodMk_lineMapFamily]
        exact hcN q.2 hq _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hβ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
          q.2 (degreeOneEquiv β q.2)) p :=
      (contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
        (α := fun _ : ℝ × M ↦ β) (m₀ := p) (n := ∞)).2
        ((β.contMDiff.comp (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I))) p)
    have hR := contMDiffAt_sectionAlong_reebVectorField (b := Prod.snd)
      (α := fun q : ℝ × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) A) hc
      (contMDiff_mpullback_prodMk A p) (contMDiff_mextDeriv_mpullback_prodMk A p)
    have hgp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ g p := by
      simpa [degreeOneEquiv_apply_apply_vec] using hβ.clm_bundle_apply_scalar hR
    exact hgp.continuousAt
  refine isOpen_iff_mem_nhds.2 fun x ⟨hxN, hx⟩ ↦ ?_
  have hev : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, 0 < g (t, y) :=
    isCompact_Icc.eventually_forall_of_forall_eventually (P := fun y t ↦ 0 < g (t, y))
      fun t ht ↦ by
        have hgs : ContinuousAt (fun z : M × ℝ ↦ g (z.2, z.1)) (x, t) :=
          (hg (t, x) hxN).comp_of_eq continuous_swap.continuousAt rfl
        exact hgs.eventually (lt_mem_nhds (by simpa [g, A] using hx t ht))
  filter_upwards [hN.mem_nhds hxN, hev] with y hyN hy
  exact ⟨hyN, fun t ht ↦ by simpa [g, A] using hy t ht⟩

variable [SecondCountableTopology M]

/-- The restriction step of
`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_apply_eq`. On an open set `V` on
which all interpolations are contact, and on which a one-form `β` vanishing on the tangent images
of the slice is positive on all their Reeb vectors, the slice meets `V` in a hypersurface
transverse to these Reeb vectors, and the strict interpolation applies on `V`. -/
private theorem exists_partialDiffeomorph_mpullback_eq_of_forall_pos
    {α₀ α₁ β : SmoothForm I M ℝ 1} {V : Set M} (hV : IsOpen V)
    (hcV : ∀ x ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x)
    (hpos : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      0 < β.val x ![(α₀ + Real.smoothTransition t • (α₁ - α₀)).reebVectorField x])
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hβι : ∀ s w, β.val (ι s) ![mfderiv J I ι s w] = 0)
    {K : Set M} (hKV : K ⊆ V) (hKι : K ⊆ range ι) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (x₀ : M) (hx₀ : x₀ ∈ K) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ α₁.val x = α₀.val x := by
  set W : TopologicalSpace.Opens M := ⟨V, hV⟩
  have hW : Nonempty W := ⟨⟨x₀, hKV hx₀⟩⟩
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace H W
  have : TopologicalSpace.MetrizableSpace W :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable W
  set res : SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I W ℝ 1 :=
    mpullback (Subtype.val : W → M) contMDiff_subtypeVal
  have hbij (y : W) : Function.Bijective (mfderiv I I (Subtype.val : W → M) y) := by
    rw [Manifold.mfderiv_subtype_val]; exact ContinuousLinearEquiv.bijective _
  -- The part of the slice over `V`.
  set T : TopologicalSpace.Opens S := ⟨ι ⁻¹' V, hV.preimage hι.continuous⟩
  let ιW : T → W := fun σ ↦ ⟨ι σ, σ.property⟩
  have hdιW (σ : T) (w : TangentSpace J σ) : mfderiv J I ιW σ w = mfderiv J I ι σ w :=
    Manifold.mfderiv_apply_of_subtype_val_comp_eq (f := ιW) (A := ι) rfl w
  have hrange : range ιW = Subtype.val ⁻¹' range ι := by
    ext y
    exact ⟨fun ⟨σ, hσ⟩ ↦ ⟨σ, congrArg Subtype.val hσ⟩,
      fun ⟨σ, hσ⟩ ↦ ⟨⟨σ, mem_preimage.2 (hσ ▸ y.property)⟩, Subtype.ext hσ⟩⟩
  -- Transversality: `β` kills the tangent images of the slice but not the Reeb vectors.
  have htr (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IsTransverseAlong J (res α₀ + s • (res α₁ - res α₀)).reebVectorField ιW := by
    refine isTransverseAlong_iff.2 fun σ ⟨w, hw⟩ ↦ ?_
    obtain ⟨t, ht, rfl⟩ : s ∈ Real.smoothTransition '' Icc (0 : ℝ) 1 :=
      intermediate_value_Icc zero_le_one Real.smoothTransition.continuous.continuousOn
        (by simpa [Real.smoothTransition.zero, Real.smoothTransition.one] using hs)
    have hR := mfderiv_reebVectorField_mpullback_of_isContactFormAt (Subtype.val : W → M)
      contMDiff_subtypeVal (hbij (ιW σ)) (hcV (ι σ) σ.property _ hs)
    rw [Manifold.mfderiv_subtype_val_apply, map_add, map_smul, map_sub] at hR
    rw [hR, ContinuousLinearMap.coe_coe, hdιW] at hw
    have h0 := hβι σ w
    rw [hw] at h0
    exact (hpos (ι σ) σ.property t ht).ne' h0
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ :=
    exists_partialDiffeomorph_mpullback_eq_of_forall_isContactFormAt (K := Subtype.val ⁻¹' K)
      (fun y s hs ↦ isContactFormAt_mpullback_subtypeVal_add_smul_sub (hcV y y.property s hs))
      ((ContMDiff.subtypeVal_comp_iff W ιW).1 (hι.comp contMDiff_subtypeVal))
      (fun σ v w h ↦ himm σ (by rwa [hdιW, hdιW] at h))
      ((Topology.IsInducing.subtypeVal.of_comp_iff).1 (hind.comp Topology.IsInducing.subtypeVal))
      (hrange ▸ hclosed.preimage continuous_subtypeVal) hdim htr
      (fun y hy ↦ hrange ▸ hKι hy)
      (fun y hy ↦ (coe_mpullback_subtype_val_apply α₁ y).trans
        ((hval y hy).trans (coe_mpullback_subtype_val_apply α₀ y).symm))
  refine exists_partialDiffeomorph_forall_mpullback_of_opens (by simp) hW hKV hsrc htgt hfix α₁.val
    (P := fun x v ↦ v = α₀.val x) fun y hy ↦ ?_
  have hφy := hφ y hy
  rw [coe_mpullback] at hφy
  exact hφy.trans (coe_mpullback_subtype_val_apply α₀ y)

/-- **Strict interpolation of contact forms agreeing to first order along a slice.** Let `α₀` be
a contact form at the points of a set `K`, and let `α₁` agree with `α₀` at the points of `K`, with
`dα₁` agreeing with `dα₀` on the hyperplanes `ker α₀` there. Let `K` lie in the image of a smooth
embedding `ι : S → M`, with closed image, of a boundaryless manifold of one dimension less, which
is tangent to the hyperplanes `ker α₀` along `K` in the following sense: some one-form `β` vanishes
on the tangent images of `ι` and agrees with `α₀` at the points of `K`. Then there is a smooth
partial diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which
fixes every point of `K` and pulls `α₁` back to `α₀` exactly on its source. Neither `K` nor `M`
need be compact.

For instance, along the zero section of the one-jet bundle `T^* L × ℝ` with its contact form
`dz - λ`, the slice `z = 0` and `β = dz` satisfy these hypotheses. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_apply_eq {α₀ α₁ β : SmoothForm I M ℝ 1}
    {K : Set M} (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w])
    (hι : ContMDiff J I ∞ ι) (himm : ∀ s, Function.Injective (mfderiv J I ι s))
    (hind : Topology.IsInducing ι) (hclosed : _root_.IsClosed (range ι))
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) (hKι : K ⊆ range ι)
    (hβι : ∀ s w, β.val (ι s) ![mfderiv J I ι s w] = 0) (hβK : ∀ x ∈ K, β.val x = α₀.val x) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback I I φ α₁.val x = α₀.val x := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · -- For empty `K`, the partial diffeomorphism with empty source will do.
    refine ⟨(Diffeomorph.refl I M ∞).toPartialDiffeomorph.restrOpen ∅ isOpen_empty, by simp,
      by simp, by simp, fun x hx ↦ ?_⟩
    simp at hx
  -- The interpolations are contact on an open neighbourhood `N` of `K`, and `β` is positive on
  -- their Reeb vectors on a smaller one, `V`: at the points of `K`, `β = α₀ = α_t` there.
  obtain ⟨N, hN, hKN, hcN⟩ := exists_isOpen_forall_isContactFormAt_add_smul_sub hc hval hd
  have hKV (x : M) (hx : x ∈ K) (t : ℝ) :
      0 < β.val x ![(α₀ + Real.smoothTransition t • (α₁ - α₀)).reebVectorField x] := by
    have h1 := apply_reebVectorField_of_isContactFormAt (hcN x (hKN hx) _
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)
    rw [show (α₀ + Real.smoothTransition t • (α₁ - α₀)).val x = α₀.val x by simp [hval x hx]]
      at h1
    rw [hβK x hx, h1]
    exact one_pos
  exact exists_partialDiffeomorph_mpullback_eq_of_forall_pos
    (isOpen_setOf_forall_pos_apply_reebVectorField hN hcN) (fun x hx ↦ hcN x hx.1)
    (fun x hx ↦ hx.2) hι himm hind hclosed hdim hβι (fun x hx ↦ ⟨hKN hx, fun t _ ↦ hKV x hx t⟩)
    hKι hval x₀ hx₀

end TauCeti.SmoothForm
