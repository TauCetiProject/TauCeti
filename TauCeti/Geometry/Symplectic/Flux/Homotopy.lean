/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux

/-!
# Homotopy invariance of the flux

Let `σ` be a closed two-form on a manifold `M` and let `φ_t` and `ψ_t`, `t ∈ [0, 1]`, be smooth
diffeotopies of `M` with the same final diffeomorphism `φ₁ = ψ₁`. Suppose they are joined by a
smooth homotopy fixing both time ends: a smooth map

`G : (M × [0, 1]) × [0, 1] → M`, `((x, t), s) ↦ G_s(x, t)`,

with `G_0(x, t) = φ_t x`, `G_1(x, t) = ψ_t x`, `G_s(x, 0) = x` and `G_s(x, 1) = φ₁ x` for every
`s`. Then the flux forms of `φ` and `ψ` differ by an exact form
(`TauCeti.Diffeotopy.fluxForm_sub_mem_exactForms_of_homotopy`), so when `φ₁` preserves `σ` the
two diffeotopies have the same flux in `H¹_dR(M)` (`TauCeti.Diffeotopy.flux_eq_of_homotopy`).
In particular a diffeotopy whose final diffeomorphism is the identity, and which is homotopic to the
constant diffeotopy through such a homotopy, has zero flux
(`TauCeti.Diffeotopy.flux_eq_zero_of_homotopy_refl`). Thus the flux of a symplectic isotopy only
depends on its class modulo smooth homotopies fixing both time ends.

The intermediate maps `G_s` need not be diffeotopies, nor preserve `σ`, and `σ` need not be
nondegenerate. The homotopy only has to be smooth and to fix the two time ends.

## Implementation notes

The two-parameter identity `∂_s β_t - ∂_t β_s = d (σ(X, Y) ∘ G)` of the classical argument is
replaced by two applications of the cochain-homotopy identity of the homotopy operator
(`TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`). The pullback `τ = G^* σ` is
a closed two-form on `(M × [0, 1]) × [0, 1]`, so the homotopy operator `L = h_s τ` in `s` is a
one-form on the cylinder `M × [0, 1]` with `d L = ψ^* σ - φ^* σ`, where `φ` and `ψ` here denote
the motions `(x, t) ↦ φ_t x` and `(x, t) ↦ ψ_t x`. The homotopy operator in `t` then gives

`Flux(ψ) - Flux(φ) = h_t (d L) = ι₁^* L - ι₀^* L - d (h_t L)`.

Over the time ends `t = 0` and `t = 1` the homotopy is stationary in `s`, so the restrictions
`ι₀^* L` and `ι₁^* L` are homotopy operators of forms pulled back along the projection to `M`,
which vanish (`TauCeti.homotopyOperator_mpullback_fst`). Hence `Flux(ψ) - Flux(φ) = -d (h_t L)`.

## Main results

* `TauCeti.Diffeotopy.fluxForm_sub_mem_exactForms_of_homotopy`: diffeotopies joined by a smooth
  homotopy fixing both time ends have flux forms differing by an exact form.
* `TauCeti.Diffeotopy.flux_eq_of_homotopy`: such diffeotopies have the same flux.
* `TauCeti.Diffeotopy.flux_eq_zero_of_homotopy_refl`: a diffeotopy joined to the constant
  diffeotopy by such a homotopy has zero flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism on the universal cover of the
  identity component of the symplectomorphism group).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] (Φ Ψ : Diffeotopy J ∞ M)

/-- Pulling a form on `M` back along a smooth map `(M × [0, 1]) × [0, 1] → M` and then
restricting to the slice at time `c` is pulling it back along the slice of the map. -/
private theorem mpullback_slice_mpullback {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G) {f : M × unitInterval → M}
    (c : unitInterval) (hf : ∀ p, G (p, c) = f p) (σ : SmoothForm J M ℝ 2) :
    mpullback (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, c))
        (SmoothForm.mpullback G hG σ).1 =
      mpullback (J.prod (𝓡∂ 1)) J f σ.1 := by
  have hslice : MDifferentiable (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      fun p : M × unitInterval ↦ (p, c) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  rw [SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp hslice (hG.mdifferentiable (by simp))]
  exact congrArg (mpullback _ J · σ.1) (funext hf)

/-- If a smooth map `(M × [0, 1]) × [0, 1] → M` is stationary in the last variable over the time
`c` of the cylinder, then the homotopy operator in that variable of the pullback of a form,
restricted to time `c`, vanishes. -/
private theorem mpullback_slice_homotopyOperator_mpullback_eq_zero
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G) {f : M → M} (hf : ContMDiff J J ∞ f)
    (c : unitInterval) (hGc : ∀ x s, G ((x, c), s) = f x) (σ : SmoothForm J M ℝ 2) :
    mpullback J (J.prod (𝓡∂ 1)) (fun x ↦ (x, c))
        (homotopyOperator (SmoothForm.mpullback G hG σ).1) = 0 := by
  have : IsManifold (J.prod (𝓡∂ 1)) 1 (M × unitInterval) := IsManifold.of_le (n := ∞) (by simp)
  have hslice : MDifferentiable J (J.prod (𝓡∂ 1)) fun x : M ↦ (x, c) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have hprod : MDifferentiable (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      (Prod.map (fun x : M ↦ (x, c)) (id : unitInterval → unitInterval)) :=
    hslice.prodMap mdifferentiable_id
  -- Over time `c` the map is `f ∘ Prod.fst`, so the pulled back form comes from `M`.
  have hcomp : G ∘ Prod.map (fun x : M ↦ (x, c)) id = f ∘ Prod.fst :=
    funext fun q ↦ hGc q.1 q.2
  rw [← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm hslice
      ((SmoothForm.mpullback G hG σ).isSmoothForm.of_le (by simp)),
    SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp hprod (hG.mdifferentiable (by simp)),
    hcomp, TauCeti.mpullback_comp mdifferentiable_fst (hf.mdifferentiable (by simp)),
    homotopyOperator_mpullback_fst]

/-- **Homotopy invariance of the flux form.** Let `σ` be a closed two-form and let `G` be a smooth
homotopy from the motion `(x, t) ↦ φ_t x` of a diffeotopy `φ` to the motion `(x, t) ↦ ψ_t x` of a
diffeotopy `ψ` which fixes both time ends: `G_s(x, 0) = x` and `G_s(x, 1) = φ₁ x` for every `s`.
Then the flux forms of `φ` and `ψ` differ by an exact form. -/
theorem fluxForm_sub_mem_exactForms_of_homotopy {σ : SmoothForm J M ℝ 2}
    (hσ : SmoothForm.IsClosed σ) {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (hstart : ∀ x s, G ((x, 0), s) = x) (hfinal : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Ψ.fluxForm σ - Φ.fluxForm σ ∈ exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold (J.prod (𝓡∂ 1)) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (M × unitInterval) :=
    IsManifold.of_le (n := ∞) (by simp)
  -- `τ = G^* σ` is closed on `(M × [0, 1]) × [0, 1]`, and `L = h_s τ` has `d L = ψ^* σ - φ^* σ`.
  set τ := SmoothForm.mpullback G hG σ
  set L := homotopyOperator τ.1
  have hdL : mextDeriv L =
      (SmoothForm.mpullback Ψ.cylinderMap Ψ.contMDiff_cylinderMap σ).1 -
        (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).1 := by
    funext p
    rw [mextDeriv_homotopyOperator (τ.isSmoothForm.of_le (by simp))
      ((SmoothForm.isClosed_def _).mp (hσ.mpullback G hG)) p,
      mpullback_slice_mpullback hG 1 hG₁, mpullback_slice_mpullback hG 0 hG₀,
      SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, Pi.sub_apply]
  -- The homotopy is stationary over the two time ends, where `L` restricts to zero.
  have hL₁ := mpullback_slice_homotopyOperator_mpullback_eq_zero hG Φ.final.contMDiff 1 hfinal σ
  have hL₀ := mpullback_slice_homotopyOperator_mpullback_eq_zero hG contMDiff_id 0 hstart σ
  -- The cochain-homotopy identity in `t` for `L` concludes: `Flux(ψ) - Flux(φ) = -d (h_t L)`.
  have hLs : IsSmoothForm (J.prod (𝓡∂ 1)) ∞ L := IsSmoothForm.homotopyOperator τ.isSmoothForm
  rw [exactForms_succ]
  refine ⟨-⟨homotopyOperator L, (IsSmoothForm.homotopyOperator hLs).mem_smoothBundleForms⟩,
    Subtype.ext (funext fun x ↦ ?_)⟩
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv (hLs.of_le (by simp)) x
  -- The homotopy operator in `t` is additive on the continuous forms `ψ^* σ - φ^* σ` and `φ^* σ`.
  have hadd := homotopyOperator_add
    ((SmoothForm.mpullback Ψ.cylinderMap Ψ.contMDiff_cylinderMap σ -
      SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).isSmoothForm.of_le (by simp))
    ((SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).isSmoothForm.of_le (by simp))
  rw [Submodule.coe_sub, sub_add_cancel] at hadd
  rw [hdL, hL₁, hL₀, Pi.zero_apply, sub_zero] at key
  rw [map_neg, Submodule.coe_neg, Pi.neg_apply, mextDerivₗ_apply, Submodule.coe_sub, Pi.sub_apply,
    coe_fluxForm, coe_fluxForm, hadd, Pi.add_apply, add_sub_cancel_right,
    eq_neg_of_add_eq_zero_right key]

/-- **Homotopy invariance of the flux.** For a closed two-form `σ`, two diffeotopies `φ` and `ψ`
whose final diffeomorphism preserves `σ` and which are joined by a smooth homotopy fixing both time
ends (`G_s(x, 0) = x` and `G_s(x, 1) = φ₁ x` for every `s`) have the same flux. -/
theorem flux_eq_of_homotopy (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (hstart : ∀ x s, G ((x, 0), s) = x) (hfinal : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Φ.flux σ hΦ = Ψ.flux σ hΨ := by
  rw [flux_def, flux_def, eq_comm, ← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff]
  exact Φ.fluxForm_sub_mem_exactForms_of_homotopy Ψ
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2)) hG hG₀ hG₁ hstart hfinal

/-- **Contractible loops have zero flux.** For a closed two-form `σ`, a diffeotopy `φ` joined to
the constant diffeotopy by a smooth homotopy fixing both time ends (`G_s(x, 0) = x` and
`G_s(x, 1) = x` for every `s`) has zero flux. These hypotheses force the final diffeomorphism of
`φ` to be the identity, so `φ` is a loop of diffeomorphisms. -/
theorem flux_eq_zero_of_homotopy_refl (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    {G : (M × unitInterval) × unitInterval → M}
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = p.1)
    (hstart : ∀ x s, G ((x, 0), s) = x) (hfinal : ∀ x s, G ((x, 1), s) = x) :
    Φ.flux σ hΦ = 0 := by
  have hrefl : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.1 := by
    rw [final_refl]
    exact (SmoothForm.diffeomorphStabilizer σ.1).one_mem
  -- The final diffeomorphism of `φ` is the identity: it is the end of the homotopy at `s = 0`.
  have hΦfinal (x : M) : G ((x, 1), 0) = Φ.final x := by
    rw [hG₀, cylinderMap_apply, final_apply]
  rw [Φ.flux_eq_of_homotopy (refl J ∞ M) σ hΦ hrefl hG hG₀ (fun p ↦ by simp [hG₁]) hstart
    fun x s ↦ by rw [hfinal, ← hΦfinal, hfinal], flux_refl]

end Diffeotopy

end TauCeti
