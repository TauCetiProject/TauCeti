/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Topology.VectorBundle.Hom

/-!
# Interpolating contact forms which agree along a set

Let `α₀` and `α₁` be one-forms on a finite-dimensional manifold `M` and let `K ⊆ M` be a set along
which they agree to first order on the contact hyperplanes: at each `x ∈ K`, `α₀` is contact,
`α₁ x = α₀ x`, and `dα₁ x` agrees with `dα₀ x` on `ker α₀ x × ker α₀ x`. Then every form of the
linear interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, takes the value `α₀ x` at `x ∈ K`, and its
exterior derivative agrees with `dα₀ x` on `ker α₀ x`, so it is contact at `x`
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub`). The contact condition is open, and `[0, 1]` is
compact, so the whole interpolation is contact on an open neighbourhood of `K`
(`TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`). Openness is read off the
contact flat map `v ↦ ι_v dα + α(v) α`: its invertibility is an open condition, and in odd
dimension it is equivalent to contactness
(`TauCeti.SmoothForm.isContactFormAt_iff_isInvertible_contactFlat`). No compactness of `K` is
needed, since only the parameter interval is compact.

On this neighbourhood the interpolation, reparametrized by a smooth step function, is a smooth
family of contact forms whose hyperplanes do not move along `K`. Relative Gray stability
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul`) on the open submanifold then
gives a partial diffeomorphism of `M`, defined on open neighbourhoods of `K`, which fixes every
point of `K` and pulls `α₁` back to a positive multiple of `α₀`
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`). So contact
structures whose defining forms have the same values and the same Levi forms along `K` agree near
`K` up to a contactomorphism fixing `K`. This is the step of the isotropic and Legendrian
neighbourhood theorems which compares two contact structures after their first-order data along
the submanifold have been identified.

## Main results

* `TauCeti.SmoothForm.isContactFormAt_add_smul_sub`: the interpolations are contact along `K`.
* `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`: the interpolations
  `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, are contact on an open neighbourhood of `K`.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt`:
  relative Gray stability for two forms joined by a segment of contact forms.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`: relative Gray
  stability for two contact forms agreeing to first order along `K`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and Section 2.5 (the isotropic neighbourhood theorem, whose
  proof interpolates two contact forms agreeing along the submanifold).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α₀ α₁ : SmoothForm I M ℝ 1}

/-! ### Contact flat maps along the segment -/

/-- The contact flat maps of the interpolations `α₀ + s (α₁ - α₀)` form a smooth section along the
projection `ℝ × M → M`. -/
private theorem contMDiff_contactFlat_add_smul_sub (α₀ α₁ : SmoothForm I M ℝ 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((α₀ + p.1 • (α₁ - α₀)).contactFlat p.2)) := by
  intro p
  have hα := contMDiff_mpullback_prodMk (lineMapFamily α₀ α₁ contDiff_id) p
  have hdα := contMDiff_mextDeriv_mpullback_prodMk (lineMapFamily α₀ α₁ contDiff_id) p
  simp only [mpullback_prodMk_lineMapFamily, id] at hα hdα
  exact contMDiffAt_sectionAlong_contactFlat (b := Prod.snd)
    (α := fun p : ℝ × M ↦ α₀ + p.1 • (α₁ - α₀)) hα hdα

/-! ### The interpolation is contact near the set of agreement -/

/-- **Interpolations of forms agreeing to first order at a contact point are contact there.** If
`α₀` is contact at `x`, `α₁ x = α₀ x`, and `dα₁ x` agrees with `dα₀ x` on the hyperplane
`ker α₀ x`, then every form `α₀ + s (α₁ - α₀)` is contact at `x`. -/
theorem isContactFormAt_add_smul_sub {x : M} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = α₀.val x)
    (hd : ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) (s : ℝ) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  refine (isContactFormAt_congr ?_ fun v hv w hw ↦ ?_).2 hc
  · simp [hval]
  · rw [← mextDerivₗ_apply I 1 (α₀ + s • (α₁ - α₀)), map_add, map_smul, map_sub]
    simp [hd v hv w hw]

variable [FiniteDimensional ℝ E]

/-- **The interpolation is contact near the set of first-order agreement.** Let `α₀` be contact at
every point of `K`, and let `α₁` agree with `α₀` at the points of `K`, with `dα₁` agreeing with
`dα₀` on the hyperplanes `ker α₀`. Then there is an open neighbourhood of `K` on which every
interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact. The set `K` need not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub {K : Set M}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, isOpen_empty, empty_subset _, by simp⟩
  -- A contact point makes the model space odd-dimensional.
  have hodd : Odd (finrank ℝ E) :=
    (isContactFormAt_iff_isContact.1 (hc x₀ hx₀)).odd_finrank (isAlt_bilinFormAt _ x₀)
  -- The contact flat maps of the interpolations are invertible on an open set `O ⊆ ℝ × M`.
  set O := {p : ℝ × M | ((α₀ + p.1 • (α₁ - α₀)).contactFlat p.2).IsInvertible}
  -- The bundles and the base map are given explicitly: unification would otherwise read the
  -- section along the identity of `M`.
  have hO : IsOpen O := Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E)
    (F₂ := E →L[ℝ] ℝ) (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    (b := Prod.snd) (ϕ := fun p : ℝ × M ↦ (α₀ + p.1 • (α₁ - α₀)).contactFlat p.2)
    (contMDiff_contactFlat_add_smul_sub α₀ α₁).continuous
  -- Since `[0, 1]` is compact, the points `x` with `[0, 1] × {x} ⊆ O` form an open set.
  refine ⟨{x | ∀ s ∈ Icc (0 : ℝ) 1, (s, x) ∈ O},
    isOpen_iff_mem_nhds.2 fun x hx ↦ isCompact_Icc.eventually_forall_of_forall_eventually
      fun s hs ↦ (hO.preimage continuous_swap).mem_nhds (hx s hs),
    fun x hx s _ ↦ isInvertible_contactFlat_of_isContactFormAt
      (isContactFormAt_add_smul_sub (hc x hx) (hval x hx) (hd x hx) s),
    fun x hx s hs ↦ isContactFormAt_of_isInvertible_contactFlat hodd (hx s hs)⟩

/-! ### Relative Gray stability for two contact forms -/

variable [I.Boundaryless] [T2Space M]

/-- **Relative Gray stability along a segment of contact forms.** Let every interpolation
`α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, be a contact form, and let `α₁` agree with `α₀` at the points of
a set `K`. Then there is a smooth partial diffeomorphism `φ` of `M`, whose source and target are
open neighbourhoods of `K`, which fixes every point of `K` and pulls `α₁` back to a positive
multiple of `α₀` on its source. Neither `K` nor `M` need be compact. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt {K : Set M}
    (hc : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x)
    (hval : ∀ x ∈ K, α₁.val x = α₀.val x) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧ TauCeti.mpullback I I φ α₁.val x = g • α₀.val x := by
  -- The segment, reparametrized by the smooth step function, is a smooth family of contact forms.
  have hcα (t : ℝ) : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).IsContactForm := by
    rw [mpullback_prodMk_lineMapFamily, isContactForm_iff_forall_isContactFormAt]
    exact fun x ↦ hc x _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- Along `K`, every form of the segment takes the value `α₀`, so its kernel does not move.
  have hK (x : M) (hx : x ∈ K) (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id)
        (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id)
        (lineMapFamily α₀ α₁ (Real.smoothTransition.contDiff (n := ⊤)))).kerDistribution x := by
    ext v
    simp [mem_kerDistribution, hval x hx]
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ := exists_partialDiffeomorph_mpullback_eq_smul hcα hK 0 1
  refine ⟨φ, hsrc, htgt, hfix, fun x hx ↦ ?_⟩
  simpa [Real.smoothTransition.one, Real.smoothTransition.zero] using hφ x hx

/-- **Relative Gray stability for contact forms agreeing to first order along a set.** Let `α₀` be
contact at every point of a set `K`, and let `α₁` agree with `α₀` at the points of `K`, with `dα₁`
agreeing with `dα₀` on the hyperplanes `ker α₀`. Then there is a smooth partial diffeomorphism `φ`
of `M`, whose source and target are open neighbourhoods of `K`, which fixes every point of `K` and
pulls `α₁` back to a positive multiple of `α₀` on its source. Neither `K` nor `M` need be compact.
Only `α₀` is assumed contact, and only at the points of `K`. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq {K : Set M}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧ TauCeti.mpullback I I φ α₁.val x = g • α₀.val x := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · -- For empty `K`, the partial diffeomorphism with empty source will do.
    refine ⟨(Diffeomorph.refl I M ∞).toPartialDiffeomorph.restrOpen ∅ isOpen_empty, by simp,
      by simp, by simp, fun x hx ↦ ?_⟩
    simp at hx
  -- Restrict both forms to an open neighbourhood `W` of `K` on which the segment is contact.
  obtain ⟨N, hN, hKN, hcN⟩ := exists_isOpen_forall_isContactFormAt_add_smul_sub hc hval hd
  set W : TopologicalSpace.Opens M := ⟨N, hN⟩
  have hW : Nonempty W := ⟨⟨x₀, hKN hx₀⟩⟩
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ :=
    exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt (K := Subtype.val ⁻¹' K)
      (fun (y : W) s hs ↦ by
        rw [← map_sub, ← map_smul, ← map_add, isContactFormAt_mpullback_subtypeVal_iff]
        exact hcN y y.property s hs)
      fun y hy ↦ (coe_mpullback_subtype_val_apply α₁ y).trans
        ((hval y hy).trans (coe_mpullback_subtype_val_apply α₀ y).symm)
  -- Read `φ` in `M`.
  refine exists_partialDiffeomorph_forall_mpullback_of_opens (by simp) hW hKN hsrc htgt hfix α₁.val
    (P := fun x v ↦ ∃ g : ℝ, 0 < g ∧ v = g • α₀.val x) fun y hy ↦ ?_
  obtain ⟨g, hg, hφy⟩ := hφ y hy
  rw [coe_mpullback, coe_mpullback] at hφy
  exact ⟨g, hg, hφy.trans (congrArg (g • ·) (mpullback_subtype_val_apply α₀.val y))⟩

end TauCeti.SmoothForm
