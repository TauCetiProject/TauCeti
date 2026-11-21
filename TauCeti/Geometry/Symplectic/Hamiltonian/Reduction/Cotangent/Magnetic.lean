/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
public import TauCeti.Geometry.Manifold.GroupAction.Quotient.Form
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LevelShift
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent

/-!
# Magnetic cotangent reduction at a coadjoint-fixed value

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, with orbit projection
`ρ : Q → Q ⧸ G`, and let `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))` be the moment map of the cotangent-lifted
action on `T*Q` (`TauCeti.CotangentBundle.momentMap`). At the value `0`, the reduction map
`Ψ : (q, p) ↦ (ρ q, p')`, where `p = p' ∘ dρ_q`, identifies the level `μ⁻¹(0)` modulo `G` with
`T*(Q ⧸ G)` and pulls back its canonical symplectic form
(`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent`). This file treats a nonzero value
`ν ∈ 𝔤*`, after choosing a one-form `α` on `Q` that is invariant under `G` and pairs the fundamental
vector fields with the constant `-ν`:

`α(ξ_Q) = -ν(ξ)`.

For a principal connection `A` of the free action, with `A(ξ_Q) = -ξ`, and a coadjoint-fixed
value `ν`, this is `α = ⟨ν, A⟩`. On a nonempty `Q` such an `α` forces `ν` to be coadjoint-fixed
(`TauCeti.CotangentBundle.coadjointRepresentation_apply_eq_self_of_forall_eval_eq`), so the
stabilizer `G_ν` is all of `G`.

Translating the fibres by `α`, `τ_α(q, p) = (q, p + α_q)`, carries the level `μ⁻¹(ν)` onto the
horizontal covectors `μ⁻¹(0)`. The **magnetic reduction map**
(`TauCeti.CotangentBundle.magneticReductionMap`) is `Φ = Ψ ∘ τ_α`: it sends a covector `p` at `q`
in `μ⁻¹(ν)` to the unique covector `p'` at `ρ q` with `p + α_q = p' ∘ dρ_q`. Most statements are
made for a map `ρ : Q → B` with the properties of the orbit projection that they use.

* **Levels.** A covector `p` at `q` lies in `μ⁻¹(ν)` exactly when `p + α_q` vanishes on the orbit
  directions (`TauCeti.CotangentBundle.momentMap_eq_iff_of_ker_eq`).
* **Fibres and image.** On `μ⁻¹(ν)` the map `Φ` is invariant under `G`, its fibres are exactly the
  `G`-orbits (`TauCeti.CotangentBundle.magneticReductionMap_eq_magneticReductionMap_iff`), and it
  is onto `T*B` (`TauCeti.CotangentBundle.exists_momentMap_eq_and_magneticReductionMap_eq`).
* **The reduced form.** The fibre translation pulls the canonical symplectic form `ω_Q` back to
  `ω_Q - π^* dα`, so along a smooth family `f` in `μ⁻¹(ν)`,
  `(Φ ∘ f)^* ω_B = f^* ω_Q - (π ∘ f)^* dα`
  (`TauCeti.CotangentBundle.mpullback_magneticReductionMap_comp_symplecticForm`). The **magnetic
  term** `dα` is invariant and vanishes on the orbit directions, so it is the pullback `ρ^* β` of a
  unique closed two-form `β` on `Q ⧸ G`
  (`ProperSMul.existsUnique_mpullback_quotientMk_eq_mextDerivₗ`,
  `ProperSMul.isClosed_of_mpullback_quotientMk_eq_mextDerivₗ`). For `α = ⟨ν, A⟩` it is the
  `ν`-component of the curvature of `A`, since `ν` vanishes on brackets. Then
  `(Φ ∘ f)^* (ω_B + π_B^* β) = f^* ω_Q`
  (`TauCeti.CotangentBundle.mpullback_magneticReductionMap_comp_add_symplecticForm`): the form
  that descends to the reduced space `μ⁻¹(ν) ⧸ G` is the pullback along `Φ` of the twisted form
  `ω_B + π_B^* β` of `T*(Q ⧸ G)`.
* **Change of connection.** If `α'` is a second such one-form, then `α' - α` descends to a
  one-form `γ` on `Q ⧸ G`, and on `μ⁻¹(ν)` the magnetic reduction maps differ by the fibre
  translation by `γ`, `Φ' = τ_γ ∘ Φ`
  (`ProperSMul.exists_mpullback_quotientMk_eq_sub_and_magneticReductionMap_eq`). Accordingly
  `dα' = dα + ρ^* dγ`, so the magnetic term changes from `β` to `β + dγ`, while the translation
  pulls `ω_B` back to `ω_B - π_B^* dγ`
  (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm`).

For the orbit projection of a free proper action all the hypotheses on `ρ` hold, and the results
are restated in the namespace `ProperSMul`. The construction of a principal connection and of the
reduced space `μ⁻¹(ν) ⧸ G` as a manifold are not part of this file.

## Main definitions

* `TauCeti.CotangentBundle.magneticReductionMap I IB ρ α`: the map `(q, p) ↦ (ρ q, p')` with
  `p + α_q = p' ∘ dρ_q`.

## References

* Jerrold E. Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor S. Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, §2.2
  (cotangent bundle reduction at a value fixed by the coadjoint action: the shift map and the
  magnetic term).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Springer, 1999, Sections 6.6 and 12.1 (magnetic terms and momentum maps of cotangent lifts).
-/

public section

noncomputable section

open Bundle Function Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {ρ : Q → B}

/-! ### The magnetic reduction map -/

section Descent

variable [IsManifold I 1 Q]

variable (I IB ρ) in
/-- The **magnetic reduction map** of a one-form `α` on `Q`: the fibre translation
`(q, p) ↦ (q, p + α_q)` followed by the reduction map `TauCeti.CotangentBundle.reductionMap` along
`ρ`. On a covector `p` at `q` for which `p + α_q` vanishes on `ker dρ_q` it is the unique covector
`p'` at `ρ q` with `p + α_q = p' ∘ dρ_q`
(`TauCeti.CotangentBundle.magneticReductionMap_snd_apply_mfderiv`,
`TauCeti.CotangentBundle.eq_magneticReductionMap_of_snd_apply_mfderiv`). Elsewhere its value
carries no meaning. -/
def magneticReductionMap (α : SmoothForm I Q ℝ 1) (z : CotangentBundle I Q) :
    CotangentBundle IB B :=
  reductionMap I IB ρ ⟨z.proj, z.snd + SmoothForm.degreeOneEquiv α z.proj⟩

variable {α : SmoothForm I Q ℝ 1}

/-- The covector `p` at `q` translated by `α` takes the value `p v + α_q(v)` at `v`. -/
private theorem add_degreeOneEquiv_apply (α : SmoothForm I Q ℝ 1) (z : CotangentBundle I Q)
    (v : TangentSpace I z.proj) :
    (z.snd + SmoothForm.degreeOneEquiv α z.proj) v = z.snd v + α.val z.proj ![v] := by
  rw [add_apply, SmoothForm.degreeOneEquiv_apply_apply_vec]

/-- The magnetic reduction map reduces the translated covector `p + α_q`. -/
theorem magneticReductionMap_def (α : SmoothForm I Q ℝ 1) (z : CotangentBundle I Q) :
    magneticReductionMap I IB ρ α z =
      reductionMap I IB ρ ⟨z.proj, z.snd + SmoothForm.degreeOneEquiv α z.proj⟩ :=
  (rfl)

/-- The magnetic reduction map is the reduction map after the fibre translation by `α`. -/
theorem reductionMap_vectorBundleTranslateDiffeomorph (α : SmoothForm I Q ℝ 1)
    (z : CotangentBundle I Q) :
    reductionMap I IB ρ (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) =
      magneticReductionMap I IB ρ α z := by
  rw [vectorBundleTranslateDiffeomorph_apply, magneticReductionMap_def]

/-- The magnetic reduction map lies over `ρ`. -/
@[simp]
theorem proj_magneticReductionMap (z : CotangentBundle I Q) :
    (magneticReductionMap I IB ρ α z).proj = ρ z.proj :=
  proj_reductionMap _

/-- On a covector `p` at `q` such that `p + α_q` vanishes on `ker dρ_q`, the magnetic reduced
covector `p'` satisfies `p'(dρ_q v) = p v + α_q(v)`. -/
theorem magneticReductionMap_snd_apply_mfderiv {z : CotangentBundle I Q}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hz : ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v + α.val z.proj ![v] = 0)
    (v : TangentSpace I z.proj) :
    (magneticReductionMap I IB ρ α z).snd (mfderiv I IB ρ z.proj v) =
      z.snd v + α.val z.proj ![v] := by
  have h := reductionMap_snd_apply_mfderiv (IB := IB)
    (z := ⟨z.proj, z.snd + SmoothForm.degreeOneEquiv α z.proj⟩) hρ
    (fun v hv ↦ (add_degreeOneEquiv_apply α z v).trans (hz v hv)) v
  rwa [add_degreeOneEquiv_apply] at h

/-- **Uniqueness of the magnetic reduced covector.** If `dρ_q` has a continuous right inverse,
every covector `p'` at `ρ q` with `p'(dρ_q v) = p v + α_q(v)` for all `v` is the magnetic reduced
covector of the covector `p` at `q`. -/
theorem eq_magneticReductionMap_of_snd_apply_mfderiv {z : CotangentBundle I Q}
    {w : CotangentBundle IB B} (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hw : w.proj = ρ z.proj)
    (h : ∀ v, w.snd (mfderiv I IB ρ z.proj v) = z.snd v + α.val z.proj ![v]) :
    w = magneticReductionMap I IB ρ α z :=
  eq_reductionMap_of_cotangentRel hρ ((cotangentRel_iff I IB ρ _ _).2
    ⟨hw.symm, ContinuousLinearMap.ext fun v ↦ (add_degreeOneEquiv_apply α z v).trans (h v).symm⟩)

/-- If `dρ_q` has a continuous right inverse, a covector `p'` at `ρ q` satisfies
`p'(dρ_q v) = p v + α_q(v)` for all `v` exactly when `p + α_q` vanishes on `ker dρ_q` and `p'` is
the magnetic reduced covector of `p`. -/
theorem snd_apply_mfderiv_iff_eq_magneticReductionMap {z : CotangentBundle I Q}
    {w : CotangentBundle IB B} (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hw : w.proj = ρ z.proj) :
    (∀ v, w.snd (mfderiv I IB ρ z.proj v) = z.snd v + α.val z.proj ![v]) ↔
      (∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v + α.val z.proj ![v] = 0) ∧
        w = magneticReductionMap I IB ρ α z := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, eq_magneticReductionMap_of_snd_apply_mfderiv hρ hw h⟩, ?_⟩
  · rw [← h v, hv]
    exact map_zero w.snd
  · rintro ⟨hz, rfl⟩
    exact magneticReductionMap_snd_apply_mfderiv hρ hz

/-- **Change of connection.** Let `α'` be a second one-form whose difference with `α` is the
pullback along `ρ` of a one-form `γ` on `B`. On a covector `p` at `q` such that `p + α_q` vanishes
on `ker dρ_q`, the magnetic reduction map of `α'` is that of `α` followed by the fibre translation
by `γ`. -/
theorem magneticReductionMap_eq_vectorBundleTranslateDiffeomorph [IsManifold IB 1 B]
    {α' : SmoothForm I Q ℝ 1} {γ : SmoothForm IB B ℝ 1}
    (hγ : ∀ q v, α'.val q ![v] - α.val q ![v] = γ.val (ρ q) ![mfderiv I IB ρ q v])
    {z : CotangentBundle I Q} (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hz : ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v + α.val z.proj ![v] = 0) :
    magneticReductionMap I IB ρ α' z =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
        (SmoothForm.degreeOneEquiv γ).contMDiff (magneticReductionMap I IB ρ α z) := by
  have h := magneticReductionMap_snd_apply_mfderiv hρ hz
  have hp := proj_magneticReductionMap (IB := IB) (ρ := ρ) (α := α) z
  generalize magneticReductionMap I IB ρ α z = w at h hp ⊢
  obtain ⟨y, p⟩ := w
  obtain rfl : y = ρ z.proj := hp
  -- The translated covector pulls back along `dρ_q` to `p + α'_q`.
  rw [vectorBundleTranslateDiffeomorph_apply]
  refine (eq_magneticReductionMap_of_snd_apply_mfderiv hρ rfl fun v ↦ ?_).symm
  simp only [add_apply, SmoothForm.degreeOneEquiv_apply_apply_vec]
  rw [h v, ← hγ]
  ring

end Descent

/-! ### Smoothness and the reduced form -/

section Smooth

variable [IsManifold I ∞ Q] [IsManifold IB ∞ B] [I.Boundaryless] {α : SmoothForm I Q ℝ 1}
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {m : WithTop ℕ∞}

/-- **The magnetic reduction map is smooth along smooth families.** If `ρ` is a smooth submersion
with boundaryless source, and `f` is a `C^m` family of covectors `p` at `q` such that `p + α_q`
vanishes on the vertical tangent vectors of `ρ`, then the family of magnetic reduced covectors of
`f x` is `C^m`. -/
theorem contMDiff_magneticReductionMap_comp (hρ : IsSubmersion I IB ∞ ρ)
    {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v + α.val (f x).proj ![v] = 0)
    (hm : m ≤ ∞) :
    ContMDiff IX (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) m (magneticReductionMap I IB ρ α ∘ f) := by
  -- The translated family `x ↦ f x + α` is smooth, as the fibre translation is.
  have hτ : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m fun x ↦
      (⟨(f x).proj, (f x).snd + SmoothForm.degreeOneEquiv α (f x).proj⟩ : CotangentBundle I Q) :=
    (((vectorBundleTranslateDiffeomorph _ (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff.of_le
      hm).comp hf).congr fun x ↦ (vectorBundleTranslateDiffeomorph_apply _ _ (f x)).symm
  exact contMDiff_reductionMap_comp hρ hτ
    (fun x v hv ↦ (add_degreeOneEquiv_apply α (f x) v).trans (hz x v hv)) hm

/-- **The magnetic reduction map and the canonical symplectic forms.** For a smooth submersion `ρ`
with boundaryless source and a smooth family `f` of covectors `p` at `q` such that `p + α_q`
vanishes on the vertical tangent vectors of `ρ`, the magnetic reduction map pulls the canonical
symplectic form of `T*B` back along `f` to `f^* ω_Q - (π ∘ f)^* dα`. -/
theorem mpullback_magneticReductionMap_comp_symplecticForm [IsManifold IX ∞ X]
    (hρ : IsSubmersion I IB ∞ ρ) {f : X → CotangentBundle I Q}
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v + α.val (f x).proj ![v] = 0) :
    SmoothForm.mpullback (magneticReductionMap I IB ρ α ∘ f)
        (contMDiff_magneticReductionMap_comp hρ hf hz le_rfl) (symplecticForm IB B) =
      SmoothForm.mpullback f hf (symplecticForm I Q) -
        SmoothForm.mpullback (fun x ↦ (f x).proj) ((contMDiff_proj _).comp hf)
          (mextDerivₗ I 1 α) := by
  have hτ := (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff
  have hzτ (x : X) : ∀ v, mfderiv I IB ρ ((vectorBundleTranslateDiffeomorph
      (SmoothForm.degreeOneEquiv α) (SmoothForm.degreeOneEquiv α).contMDiff ∘ f) x).proj v = 0 →
      ((vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff ∘ f) x).snd v = 0 := by
    rw [comp_apply, vectorBundleTranslateDiffeomorph_apply]
    exact fun v hv ↦ (add_degreeOneEquiv_apply α (f x) v).trans (hz x v hv)
  -- The magnetic reduction map along `f` is the reduction map along the translated family.
  have hΦ : magneticReductionMap I IB ρ α ∘ f = reductionMap I IB ρ ∘
      (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff ∘ f) :=
    funext fun x ↦ (reductionMap_vectorBundleTranslateDiffeomorph α (f x)).symm
  rw [SmoothForm.mpullback_congr _ (contMDiff_reductionMap_comp hρ (hτ.comp hf) hzτ le_rfl) hΦ,
    mpullback_reductionMap_comp_symplecticForm hρ (hτ.comp hf) hzτ,
    ← SmoothForm.mpullback_mpullback f _ hf hτ,
    mpullback_vectorBundleTranslateDiffeomorph_symplecticForm, map_sub,
    SmoothForm.mpullback_mpullback]
  -- `π ∘ f` is the family of base points `x ↦ (f x).proj`.
  exact congrArg _ (SmoothForm.mpullback_congr _ _ rfl _)

/-- **The reduced form of magnetic cotangent reduction.** Let `ρ` be a smooth submersion with
boundaryless source and let `β` be a two-form on `B` with `ρ^* β = dα`. Along a smooth family `f`
of covectors `p` at `q` such that `p + α_q` vanishes on the vertical tangent vectors of `ρ`, the
magnetic reduction map pulls the twisted form `ω_B + π_B^* β` of `T*B` back to the canonical
symplectic form of `T*Q`. -/
theorem mpullback_magneticReductionMap_comp_add_symplecticForm [IsManifold IX ∞ X]
    (hρ : IsSubmersion I IB ∞ ρ) {β : SmoothForm IB B ℝ 2}
    (hβ : SmoothForm.mpullback ρ hρ.contMDiff β = mextDerivₗ I 1 α)
    {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v + α.val (f x).proj ![v] = 0) :
    SmoothForm.mpullback (magneticReductionMap I IB ρ α ∘ f)
        (contMDiff_magneticReductionMap_comp hρ hf hz le_rfl)
        (symplecticForm IB B +
          SmoothForm.mpullback (TotalSpace.proj : CotangentBundle IB B → B) (contMDiff_proj _) β) =
      SmoothForm.mpullback f hf (symplecticForm I Q) := by
  rw [map_add, mpullback_magneticReductionMap_comp_symplecticForm hρ hf hz,
    SmoothForm.mpullback_mpullback_of_comp_eq (contMDiff_magneticReductionMap_comp hρ hf hz le_rfl)
      (contMDiff_proj _) ((contMDiff_proj _).comp hf) hρ.contMDiff
      (funext fun x ↦ proj_magneticReductionMap (f x)), hβ]
  -- The twisted term `(π ∘ f)^* dα` cancels the magnetic correction.
  exact sub_add_cancel _ _

end Smooth

/-! ### Levels of the cotangent moment map -/

section MomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [CompleteSpace E] [IsManifold I ∞ Q]
  [MulAction G Q] [ContMDiffSMul IG I ∞ G Q] {α : SmoothForm I Q ℝ 1}
  {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

omit [CompleteSpace EG] [LieGroup IG ∞ G] [CompleteSpace E] [ContMDiffSMul IG I ∞ G Q] in
/-- If `α` pairs every fundamental vector field with `-ν`, the fibre translation by `α` lowers
the cotangent moment map by `ν`. -/
private theorem momentMap_vectorBundleTranslateDiffeomorph_of_eq_neg
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) (z : CotangentBundle I Q) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) = momentMap IG G z - ν := by
  rw [momentMap_vectorBundleTranslateDiffeomorph (c := -ν) fun x ξ ↦ hα x ξ, sub_eq_add_neg]

omit [CompleteSpace EG] [LieGroup IG ∞ G] [CompleteSpace E] [ContMDiffSMul IG I ∞ G Q] in
/-- If `α` pairs every fundamental vector field with `-ν`, the fibre translation by `α` sends the
level `μ⁻¹(ν)` to the zero level. -/
private theorem momentMap_vectorBundleTranslateDiffeomorph_eq_zero_of_eq
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) = 0 := by
  rw [momentMap_vectorBundleTranslateDiffeomorph_of_eq_neg hα, hz, sub_self]

/-- **The level `μ⁻¹(ν)`.** Let the vertical tangent vectors of `ρ` at `q` be the orbit directions
`𝔤 · q`, and let `α` pair every fundamental vector field with `-ν`. A covector `p` at `q` lies in
the level `μ⁻¹(ν)` of the cotangent moment map exactly when `p + α_q` vanishes on the vertical
tangent vectors of `ρ`. -/
theorem momentMap_eq_iff_of_ker_eq {z : CotangentBundle I Q}
    (hker : (mfderiv I IB ρ z.proj).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent z.proj)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    momentMap IG G z = ν ↔ ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v + α.val z.proj ![v] = 0 := by
  have h := momentMap_vectorBundleTranslateDiffeomorph_of_eq_neg hα z
  rw [vectorBundleTranslateDiffeomorph_apply] at h
  rw [← sub_eq_zero, ← h,
    momentMap_eq_zero_iff_of_ker_eq (z := ⟨z.proj, z.snd + SmoothForm.degreeOneEquiv α z.proj⟩)
      hker]
  exact forall_congr' fun v ↦ by rw [add_degreeOneEquiv_apply]

/-- **The magnetic reduction map is onto.** If `ρ` is surjective, its differentials have continuous
right inverses and its vertical tangent vectors are the orbit directions, every covector on `B` is
the magnetic reduced covector of a covector in the level `μ⁻¹(ν)`. -/
theorem exists_momentMap_eq_and_magneticReductionMap_eq
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hsurj : Surjective ρ) (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) (w : CotangentBundle IB B) :
    ∃ z : CotangentBundle I Q, momentMap IG G z = ν ∧ magneticReductionMap I IB ρ α z = w := by
  obtain ⟨z, hz, rfl⟩ := exists_momentMap_eq_zero_and_reductionMap_eq hker hsurj hρ w
  -- Translate the horizontal covector back by `α`.
  set τ := vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff with hτ
  refine ⟨τ.symm z, ?_, ?_⟩
  · have h := momentMap_vectorBundleTranslateDiffeomorph_of_eq_neg hα (τ.symm z)
    rwa [← hτ, τ.apply_symm_apply, hz, eq_comm, sub_eq_zero] at h
  · rw [← reductionMap_vectorBundleTranslateDiffeomorph, ← hτ, τ.apply_symm_apply]

variable [ContMDiffConstSMul I ∞ G Q]

/-- **The magnetic reduction map is invariant on the level.** For a `G`-invariant map `ρ` whose
differentials have continuous right inverses and whose vertical tangent vectors are the orbit
directions, and a `G`-invariant one-form `α` pairing every fundamental vector field with `-ν`, the
magnetic reduced covector of `g • (q, p)` is that of `(q, p)` whenever `μ(q, p) = ν`. -/
theorem magneticReductionMap_smul
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hinv : ∀ (g : G) q, ρ (g • q) = ρ q) (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (g : G) :
    magneticReductionMap I IB ρ α (g • z) = magneticReductionMap I IB ρ α z := by
  rw [← reductionMap_vectorBundleTranslateDiffeomorph α (g • z),
    ← reductionMap_vectorBundleTranslateDiffeomorph α z,
    vectorBundleTranslateDiffeomorph_smul hαinv]
  exact reductionMap_smul hker hinv hρd hρ
    (momentMap_vectorBundleTranslateDiffeomorph_eq_zero_of_eq hα hz) g

/-- **The fibres of the magnetic reduction map on the level are the orbits.** Let the differentials
of `ρ` have continuous right inverses, its vertical tangent vectors be the orbit directions and its
fibres be the `G`-orbits, and let `α` be a `G`-invariant one-form pairing every fundamental vector
field with `-ν`. Two covectors in `μ⁻¹(ν)` have the same magnetic reduced covector exactly when they
lie in one `G`-orbit. -/
theorem magneticReductionMap_eq_magneticReductionMap_iff
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hfib : ∀ q q', ρ q = ρ q' ↔ ∃ g : G, g • q = q') (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z z' : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (hz' : momentMap IG G z' = ν) :
    magneticReductionMap I IB ρ α z = magneticReductionMap I IB ρ α z' ↔
      ∃ g : G, g • z = z' := by
  rw [← reductionMap_vectorBundleTranslateDiffeomorph α z,
    ← reductionMap_vectorBundleTranslateDiffeomorph α z',
    reductionMap_eq_reductionMap_iff hker hfib hρd hρ
      (momentMap_vectorBundleTranslateDiffeomorph_eq_zero_of_eq hα hz)
      (momentMap_vectorBundleTranslateDiffeomorph_eq_zero_of_eq hα hz')]
  -- The translation commutes with the action and is injective.
  simp only [← vectorBundleTranslateDiffeomorph_smul hαinv]
  exact exists_congr fun g ↦ (vectorBundleTranslateDiffeomorph _ _).injective.eq_iff

end MomentMap

end TauCeti.CotangentBundle

/-! ### Magnetic cotangent reduction for a free proper action -/

namespace ProperSMul

open TauCeti TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ProperSMul G Q] [IsCancelSMul G Q]
  {α : SmoothForm I Q ℝ 1} {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

/-- **The magnetic term descends.** For a free proper action, the exterior derivative of a
`G`-invariant one-form `α` pairing every fundamental vector field with a constant `c(ξ)` is the
pullback along the orbit projection of a unique two-form on `Q ⧸ G`. -/
theorem existsUnique_mpullback_quotientMk_eq_mextDerivₗ {c : Module.Dual ℝ (GroupLieAlgebra IG G)}
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = c ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∃! β : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 2,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
        (contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) β = mextDerivₗ I 1 α := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  refine existsUnique_mpullback_quotientMk_eq (fun g ↦ ?_) fun x v j hj ↦ ?_
  · rw [← SmoothForm.mextDerivₗ_mpullback, hαinv]
  -- `dα(ξ_Q, w) = 0` by Cartan's formula, since `α(ξ_Q)` is constant.
  obtain ⟨ξ, hξ⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hj
  rw [InfinitesimalAction.fundamental_apply] at hξ
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, ← SmoothBundleForm.eval₂_apply]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [← hξ, SmoothBundleForm.eval₂_apply]
    exact mextDerivₗ_apply_fundamentalVectorField_eq_zero hαinv hα ξ x (v 1)
  · rw [SmoothBundleForm.eval₂_swap, ← hξ, SmoothBundleForm.eval₂_apply,
      mextDerivₗ_apply_fundamentalVectorField_eq_zero hαinv hα ξ x (v 0), neg_zero]

/-- **The magnetic term is closed.** A two-form on `Q ⧸ G` whose pullback along the orbit
projection is the exact form `dα` is closed. -/
theorem isClosed_of_mpullback_quotientMk_eq_mextDerivₗ :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ {β : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 2},
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
        (contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) β = mextDerivₗ I 1 α →
      β.IsClosed := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  intro β hβ
  rw [← (isSubmersion_quotientMk (I := IG) (G := G) (I' := I) (M := Q)).isClosed_mpullback_iff
    Quotient.mk_surjective, hβ]
  exact SmoothForm.isClosed_mextDerivₗ α

/-- **Magnetic cotangent reduction: surjectivity.** For a free proper action and a one-form `α`
pairing every fundamental vector field with `-ν`, every covector on the orbit space `Q ⧸ G` is the
magnetic reduced covector of a covector in the level `μ⁻¹(ν)` of the cotangent moment map. -/
theorem exists_momentMap_eq_and_magneticReductionMap_eq_quotientMk
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ w : CotangentBundle 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q),
      ∃ z : CotangentBundle I Q, momentMap IG G z = ν ∧
        magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G Q)) α z = w := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact CotangentBundle.exists_momentMap_eq_and_magneticReductionMap_eq ker_mfderiv_quotientMk
    Quotient.mk_surjective (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp)) hα

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X]

/-- **Magnetic cotangent reduction: the reduced form.** For a free proper action, a one-form `α`
pairing every fundamental vector field with `-ν`, and a two-form `β` on `Q ⧸ G` whose pullback
along the orbit projection is `dα`, the magnetic reduction map to `T*(Q ⧸ G)` is smooth along every
smooth family `f` of covectors in the level `μ⁻¹(ν)`, and pulls the twisted form `ω + π^* β` of
`T*(Q ⧸ G)` back to the canonical symplectic form of `T*Q`. -/
theorem mpullback_magneticReductionMap_comp_add_symplecticForm_quotientMk
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ {β : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 2},
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
        (contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) β = mextDerivₗ I 1 α →
      ∀ {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
        (hz : ∀ x, momentMap IG G (f x) = ν),
        SmoothForm.mpullback
            (magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
              (Quotient.mk (MulAction.orbitRel G Q)) α ∘ f)
            (contMDiff_magneticReductionMap_comp isSubmersion_quotientMk hf
              (fun x ↦ (momentMap_eq_iff_of_ker_eq (ker_mfderiv_quotientMk _) hα).1 (hz x))
              le_rfl)
            (symplecticForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) +
              SmoothForm.mpullback TotalSpace.proj (contMDiff_proj _) β) =
          SmoothForm.mpullback f hf (symplecticForm I Q) := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  intro β hβ f hf hz
  exact CotangentBundle.mpullback_magneticReductionMap_comp_add_symplecticForm
    isSubmersion_quotientMk hβ hf
    fun x ↦ (momentMap_eq_iff_of_ker_eq (ker_mfderiv_quotientMk _) hα).1 (hz x)

variable [ContMDiffConstSMul I ∞ G Q]

/-- **Magnetic cotangent reduction: the fibres.** For a free proper action and a `G`-invariant
one-form `α` pairing every fundamental vector field with `-ν`, two covectors in the level `μ⁻¹(ν)`
of the cotangent moment map have the same magnetic reduced covector on `Q ⧸ G` exactly when they
lie in one `G`-orbit. -/
theorem magneticReductionMap_eq_magneticReductionMap_iff_quotientMk
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z z' : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (hz' : momentMap IG G z' = ν) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E) (Quotient.mk (MulAction.orbitRel G Q))
        α z =
        magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G Q)) α z' ↔
      ∃ g : G, g • z = z' := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact CotangentBundle.magneticReductionMap_eq_magneticReductionMap_iff ker_mfderiv_quotientMk
    (fun q q' ↦ by rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff])
    (fun q ↦ (contMDiff_quotientMk q).mdifferentiableAt (by simp))
    (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp)) hαinv hα hz hz'

/-- **Magnetic cotangent reduction: change of connection.** For a free proper action, let `α` and
`α'` be `G`-invariant one-forms that both pair every fundamental vector field with `-ν`. Their
difference is the pullback along the orbit projection of a one-form `γ` on `Q ⧸ G`, and on the
level `μ⁻¹(ν)` the magnetic reduction map of `α'` is that of `α` followed by the fibre translation
of `T*(Q ⧸ G)` by `γ`. -/
theorem exists_mpullback_quotientMk_eq_sub_and_magneticReductionMap_eq
    {α' : SmoothForm I Q ℝ 1}
    (hαinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα'inv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α' = α')
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ)
    (hα' : ∀ x ξ, α'.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∃ γ : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 1,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q))
          (contMDiff_quotientMk (I := IG) (G := G) (I' := I) (M := Q)) γ = α' - α ∧
        ∀ z : CotangentBundle I Q, momentMap IG G z = ν →
          magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
              (Quotient.mk (MulAction.orbitRel G Q)) α' z =
            vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
              (SmoothForm.degreeOneEquiv γ).contMDiff
              (magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
                (Quotient.mk (MulAction.orbitRel G Q)) α z) := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  -- The difference `α' - α` is invariant and annihilates the orbit directions.
  obtain ⟨γ, hγ, -⟩ := existsUnique_mpullback_quotientMk_eq (I := IG) (G := G) (α := α' - α)
    (fun g ↦ by rw [map_sub, hα'inv, hαinv]) fun x v j hj ↦ by
      obtain ⟨ξ, hξ⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hj
      rw [InfinitesimalAction.fundamental_apply] at hξ
      obtain rfl : j = 0 := Subsingleton.elim j 0
      have hv : v = ![fundamentalVectorField I ξ x] := by
        ext i
        rw [Subsingleton.elim i 0, ← hξ]
        rfl
      simp [hv, hα, hα']
  refine ⟨γ, hγ, fun z hz ↦ CotangentBundle.magneticReductionMap_eq_vectorBundleTranslateDiffeomorph
    (fun q v ↦ ?_) (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp) _)
    ((momentMap_eq_iff_of_ker_eq (ker_mfderiv_quotientMk _) hα).1 hz)⟩
  -- Evaluate `π^* γ = α' - α` on the single vector `v`.
  have h := congrArg (fun φ ↦ φ.val q ![v]) hγ
  rw [SmoothForm.mpullback_apply_one] at h
  simpa using h.symm

end ProperSMul
