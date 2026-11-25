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
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub`). This persists when the exterior derivatives
agree only on pairs with one vector in a subspace `W ⊆ ker α₀ x` containing its own
`dα₀ x`-orthogonal in `ker α₀ x`, such as the tangent space of a Legendrian submanifold
(`TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on`). The contact condition is
open, and `[0, 1]` is compact, so the whole interpolation is contact on an open neighbourhood of `K`
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
* `TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on`: the same when the exterior
  derivatives only agree on pairs with one vector in a coisotropic subspace of `ker α₀`, such as the
  tangent space of a Legendrian submanifold.
* `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt`: if
  the interpolations `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, are contact along `K`, they are contact on an
  open neighbourhood of `K`.
* `TauCeti.SmoothForm.exists_isOpen_forall_isContactFormAt_add_smul_sub`: this holds for forms
  agreeing to first order along `K`.
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

/-- **Interpolations of forms agreeing along a coisotropic subspace are contact.** Let `α₀` be
contact at `x` and `α₁ x = α₀ x`, and let `W ⊆ ker α₀ x` be a subspace containing every vector of
`ker α₀ x` that is `dα₀ x`-orthogonal to `W`. If `dα₁ x (w, v) = dα₀ x (w, v)` for `w ∈ W` and
`v ∈ ker α₀ x`, then every form `α₀ + s (α₁ - α₀)` is contact at `x`. The exterior derivatives may
differ on pairs of vectors outside `W`; for the tangent space `W` of a Legendrian submanifold
through `x` this asks only for agreement on pairs with one vector tangent to the submanifold. -/
theorem isContactFormAt_add_smul_sub_of_mextDeriv_eq_on {x : M} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = α₀.val x) {W : Submodule ℝ (TangentSpace I x)}
    (hWk : ∀ w ∈ W, w ∈ RoughForm.ker α₀.val x)
    (hW : ∀ v ∈ RoughForm.ker α₀.val x, (∀ w ∈ W, mextDeriv α₀.val x ![w, v] = 0) → v ∈ W)
    (hd : ∀ w ∈ W, ∀ v ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![w, v] = mextDeriv α₀.val x ![w, v]) (s : ℝ) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  have hval' : (α₀ + s • (α₁ - α₀)).val x = α₀.val x := by simp [hval]
  -- On `W × ker α₀ x`, the exterior derivative of the interpolation is that of `α₀`.
  have hdW (w : TangentSpace I x) (hw : w ∈ W) (v : TangentSpace I x)
      (hv : v ∈ RoughForm.ker α₀.val x) :
      mextDeriv (α₀ + s • (α₁ - α₀)).val x ![w, v] = mextDeriv α₀.val x ![w, v] := by
    rw [← mextDerivₗ_apply I 1 (α₀ + s • (α₁ - α₀)), map_add, map_smul, map_sub]
    simp [hd w hw v hv]
  have hswap (β : RoughForm I M ℝ 1) (v w : TangentSpace I x) :
      mextDeriv β x ![v, w] = -mextDeriv β x ![w, v] := by
    simpa using (mextDeriv β x).apply_vecCons_swap w v
  have hker {u : TangentSpace I x} :
      u ∈ RoughForm.ker (α₀ + s • (α₁ - α₀)).val x ↔ u ∈ RoughForm.ker α₀.val x := by
    rw [RoughForm.mem_ker, RoughForm.mem_ker, hval']
  refine ⟨hval'.symm ▸ hc.ne_zero, fun v hv hvw ↦ ?_⟩
  rw [hker] at hv
  -- A vector of `ker α₀ x` in the kernel of the interpolated form is orthogonal to `W`, so it
  -- lies in `W`; there its pairings are those of `dα₀ x`, so it vanishes.
  have hvW : v ∈ W := hW v hv fun w hw ↦ by
    rw [← hdW w hw v hv, hswap, hvw w (hker.2 (hWk w hw)), neg_zero]
  exact hc.nondegenerate v hv fun w hw ↦ by rw [← hdW v hvW w hw, hvw w (hker.2 hw)]

/-- **Interpolations of forms agreeing to first order at a contact point are contact there.** If
`α₀` is contact at `x`, `α₁ x = α₀ x`, and `dα₁ x` agrees with `dα₀ x` on the hyperplane
`ker α₀ x`, then every form `α₀ + s (α₁ - α₀)` is contact at `x`. -/
theorem isContactFormAt_add_smul_sub {x : M} (hc : IsContactFormAt α₀.val x)
    (hval : α₁.val x = α₀.val x)
    (hd : ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) (s : ℝ) :
    IsContactFormAt (α₀ + s • (α₁ - α₀)).val x :=
  isContactFormAt_add_smul_sub_of_mextDeriv_eq_on (W := RoughForm.ker α₀.val x) hc hval
    (fun _ h ↦ h) (fun _ hv _ ↦ hv) hd s

variable [FiniteDimensional ℝ E]

/-- **The interpolation is contact near a set where it is contact.** If every interpolation
`α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact at the points of `K`, then there is an open
neighbourhood of `K` on which all of them are contact. The set `K` need not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt {K : Set M}
    (hcK : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, IsContactFormAt (α₀ + s • (α₁ - α₀)).val x) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, isOpen_empty, empty_subset _, by simp⟩
  -- A contact point makes the model space odd-dimensional.
  have hodd : Odd (finrank ℝ E) :=
    (isContactFormAt_iff_isContact.1 (hcK x₀ hx₀ 0 ⟨le_rfl, zero_le_one⟩)).odd_finrank
      (isAlt_bilinFormAt _ x₀)
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
    fun x hx s hs ↦ isInvertible_contactFlat_of_isContactFormAt (hcK x hx s hs),
    fun x hx s hs ↦ isContactFormAt_of_isInvertible_contactFlat hodd (hx s hs)⟩

/-- **The interpolation is contact near the set of first-order agreement.** Let `α₀` be contact at
every point of `K`, and let `α₁` agree with `α₀` at the points of `K`, with `dα₁` agreeing with
`dα₀` on the hyperplanes `ker α₀`. Then there is an open neighbourhood of `K` on which every
interpolation `α₀ + s (α₁ - α₀)`, `s ∈ [0, 1]`, is contact. The set `K` need not be compact. -/
theorem exists_isOpen_forall_isContactFormAt_add_smul_sub {K : Set M}
    (hc : ∀ x ∈ K, IsContactFormAt α₀.val x) (hval : ∀ x ∈ K, α₁.val x = α₀.val x)
    (hd : ∀ x ∈ K, ∀ v ∈ RoughForm.ker α₀.val x, ∀ w ∈ RoughForm.ker α₀.val x,
      mextDeriv α₁.val x ![v, w] = mextDeriv α₀.val x ![v, w]) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + s • (α₁ - α₀)).val x :=
  exists_isOpen_forall_isContactFormAt_add_smul_sub_of_isContactFormAt fun x hx s _ ↦
    isContactFormAt_add_smul_sub (hc x hx) (hval x hx) (hd x hx) s

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
  -- Restrict both forms to an open neighbourhood `W` of `K` on which the segment is contact.
  obtain ⟨N, hN, hKN, hcN⟩ := exists_isOpen_forall_isContactFormAt_add_smul_sub hc hval hd
  set W : TopologicalSpace.Opens M := ⟨N, hN⟩
  set res : SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I W ℝ 1 :=
    mpullback (Subtype.val : W → M) contMDiff_subtypeVal
  have hcW (y : W) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IsContactFormAt (res α₀ + s • (res α₁ - res α₀)).val y := by
    rw [← map_sub, ← map_smul, ← map_add]
    exact (isContactFormAt_mpullback_subtype_val_iff _ y).2 (hcN y y.property s hs)
  obtain ⟨φ, hsrc, htgt, hfix, hφ⟩ :=
    exists_partialDiffeomorph_mpullback_eq_smul_of_forall_isContactFormAt (K := Subtype.val ⁻¹' K)
      hcW fun y hy ↦ (coe_mpullback_subtype_val_apply α₁ y).trans
        ((hval y hy).trans (coe_mpullback_subtype_val_apply α₀ y).symm)
  -- Read `φ` in `M`.
  obtain ⟨Φ, hsrcΦ, htgtΦ, hfixΦ, hΦ⟩ :=
    exists_partialDiffeomorph_mpullback_apply_eq_of_opens (by simp) hKN φ hsrc htgt hfix
  refine ⟨Φ, hsrcΦ, htgtΦ, hfixΦ, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl, hΦy⟩ := hΦ x hx
  obtain ⟨g, hg, hφy⟩ := hφ y hy
  refine ⟨g, hg, (hΦy α₁.val).trans ?_⟩
  rw [coe_mpullback, coe_mpullback] at hφy
  exact hφy.trans (congrArg (g • ·) (mpullback_subtype_val_apply α₀.val y))

end TauCeti.SmoothForm
