/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap

import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
import TauCeti.Geometry.Lie.Subgroup.Differential

/-!
# Cotangent reduction at zero

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, so that the orbit
projection `Q → Q ⧸ G` is a smooth submersion whose vertical tangent vectors are the orbit
directions `𝔤 · q` (`ProperSMul.isSubmersion_quotientMk`, `ProperSMul.ker_mfderiv_quotientMk`). The
cotangent-lifted action of `G` on `T*Q` has the moment map `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))`
(`TauCeti.CotangentBundle.momentMap`). This file proves the ingredients of the model case
`T*Q //₀ G ≅ T*(Q ⧸ G)` of cotangent bundle reduction: a reduction map `Ψ` from the zero level
`μ⁻¹(0)` onto `T*(Q ⧸ G)` whose fibres are exactly the `G`-orbits, and which pulls the canonical
symplectic form of `T*(Q ⧸ G)` back to that of `T*Q` along smooth families in `μ⁻¹(0)`. The map
descended to the reduced space `μ⁻¹(0) ⧸ G`, and the symplectomorphism with `T*(Q ⧸ G)`, are in
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.ReducedSpace`.

Most statements are made for a map `ρ : Q → B` with the properties of the orbit projection that
they use, and the final section applies them to the orbit projection itself. Write `Ψ` for the
reduction map below.

* **Horizontal covectors.** A covector `p` at `q` lies in `μ⁻¹(0)` exactly when it vanishes on the
  orbit directions, that is on `ker dρ_q`
  (`TauCeti.CotangentBundle.momentMap_eq_zero_iff_of_ker_eq`). Such a covector is the pullback
  `p = p' ∘ dρ_q` of a covector `p'` at `ρ q`
  (`TauCeti.CotangentBundle.momentMap_eq_zero_iff_exists_cotangentRel`), and of only one
  (`TauCeti.CotangentBundle.eq_reductionMap_of_cotangentRel`); in terms of the cotangent
  relation of `ρ`, `(q, p)` is related to `(ρ q, p')`.
* **The reduction map.** The map `(q, p) ↦ (ρ q, p ∘ R)`, for a right inverse `R` of `dρ_q`
  (`TauCeti.CotangentBundle.reductionMap`), sends a horizontal covector to that `p'`
  (`TauCeti.CotangentBundle.cotangentRel_reductionMap`); off the horizontal covectors its value
  depends on the choice of `R` and carries no meaning. On `μ⁻¹(0)` it is invariant under `G`
  (`TauCeti.CotangentBundle.reductionMap_smul`), its fibres are exactly the `G`-orbits
  (`TauCeti.CotangentBundle.reductionMap_eq_reductionMap_iff`), and it is onto `T*B`
  (`TauCeti.CotangentBundle.exists_momentMap_eq_zero_and_reductionMap_eq`).
* **Smoothness.** If `ρ` is a smooth submersion with boundaryless source, the reduction map is
  smooth along every smooth family of horizontal covectors
  (`TauCeti.CotangentBundle.contMDiffAt_reductionMap_comp`): near any point it agrees with the
  pullback of covectors along a smooth family of local sections of `ρ`.
* **Descent of the tautological forms.** Along such a family `f`, the reduction map pulls the
  Liouville form `λ` of `T*B` back to that of `T*Q`, `(Ψ ∘ f)^* λ_B = f^* λ_Q`
  (`TauCeti.CotangentBundle.mpullback_reductionMap_comp_liouvilleForm`), and likewise the canonical
  symplectic forms `ω = -dλ`
  (`TauCeti.CotangentBundle.mpullback_reductionMap_comp_symplecticForm`). Applied to smooth
  parametrizations of pieces of `μ⁻¹(0)`, this says that the restriction of `ω_Q` to the zero level,
  the form that the reduced symplectic form of `μ⁻¹(0) ⧸ G` descends, is the pullback of
  `ω_(Q ⧸ G)` along `Ψ`.

For the orbit projection of a free proper action, all these hypotheses hold
(`ProperSMul.reductionMap_eq_reductionMap_iff_quotientMk`,
`ProperSMul.exists_momentMap_eq_zero_and_reductionMap_eq_quotientMk`,
`ProperSMul.mpullback_reductionMap_comp_symplecticForm_quotientMk`). The model space of
`T*(Q ⧸ G)` has dimension `2 (dim Q - dim G)`, and so does the model space of the
Marsden–Weinstein–Meyer reduced space of `T*Q` at any value `ν` fixed by `𝔤`, in particular at zero
(`TauCeti.CotangentBundle.finrank_quotientModelSpace_level`).

## References

* Jerrold Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 2
  (cotangent bundle reduction, in particular at zero).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Springer, 1999, Section 12.1 (momentum maps of cotangent lifts).
-/

public section

noncomputable section

open Bundle Function Filter Manifold Module
open scoped ContDiff Manifold Topology

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {ρ : Q → B}

/-! ### Descending covectors along a map -/

section Descent

open Classical in
variable (I IB ρ) in
/-- The **reduction map** `(q, p) ↦ (ρ q, p ∘ R)` from `T*Q` to `T*B`, where `R` is a chosen
continuous right inverse of `dρ_q` (and the covector is zero if there is none). On a covector `p`
vanishing on `ker dρ_q` it does not depend on `R`: it is the unique covector `p'` at `ρ q` with
`p = p' ∘ dρ_q` (`TauCeti.CotangentBundle.cotangentRel_reductionMap`). Elsewhere its value carries
no meaning. -/
def reductionMap (z : CotangentBundle I Q) : CotangentBundle IB B :=
  TotalSpace.mk' (EB →L[ℝ] ℝ) (ρ z.proj)
    (if h : (mfderiv I IB ρ z.proj).HasRightInverse then z.snd ∘L h.rightInverse else 0)

/-- The reduction map lies over `ρ`. -/
@[simp]
theorem proj_reductionMap (z : CotangentBundle I Q) : (reductionMap I IB ρ z).proj = ρ z.proj :=
  (rfl)

/-- Where `dρ_q` has a continuous right inverse, the reduction map composes the covector with the
chosen one. -/
theorem reductionMap_snd {z : CotangentBundle I Q} (hρ : (mfderiv I IB ρ z.proj).HasRightInverse) :
    (reductionMap I IB ρ z).snd = z.snd ∘L hρ.rightInverse :=
  dite_eq_left hρ

/-- Where `dρ_q` has a continuous right inverse `R`, the reduction map evaluates as `p ∘ R`. -/
theorem reductionMap_snd_apply {z : CotangentBundle I Q}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse) (w : TangentSpace IB (ρ z.proj)) :
    (reductionMap I IB ρ z).snd w = z.snd (hρ.rightInverse w) := by
  rw [reductionMap_snd hρ]
  rfl

/-- On a covector `p` at `q` vanishing on `ker dρ_q`, the reduced covector `p'` satisfies
`p' (dρ_q v) = p v`. -/
theorem reductionMap_snd_apply_mfderiv {z : CotangentBundle I Q}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hz : ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0) (v : TangentSpace I z.proj) :
    (reductionMap I IB ρ z).snd (mfderiv I IB ρ z.proj v) = z.snd v := by
  rw [reductionMap_snd_apply hρ, ← sub_eq_zero, ← map_sub]
  refine hz _ ?_
  rw [map_sub, hρ.rightInverse_rightInverse, sub_self]

/-- **The reduced covector is related to the original one.** A covector `p` at `q` vanishing on
`ker dρ_q` is the pullback of its reduced covector: `p = p' ∘ dρ_q`. -/
theorem cotangentRel_reductionMap {z : CotangentBundle I Q}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse)
    (hz : ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0) :
    cotangentRel I IB ρ z (reductionMap I IB ρ z) :=
  (cotangentRel_iff I IB ρ _ _).2
    ⟨rfl, ContinuousLinearMap.ext fun v ↦ (reductionMap_snd_apply_mfderiv hρ hz v).symm⟩

/-- **Uniqueness of the reduced covector.** If `dρ_q` has a continuous right inverse, every
covector at `ρ q` whose pullback is `p` is the reduced covector. -/
theorem eq_reductionMap_of_cotangentRel {z : CotangentBundle I Q} {w : CotangentBundle IB B}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse) (h : cotangentRel I IB ρ z w) :
    w = reductionMap I IB ρ z := by
  obtain ⟨y, p⟩ := w
  obtain rfl : ρ z.proj = y := cotangentRel_proj h
  refine ext rfl fun v ↦ ?_
  rw [reductionMap_snd_apply hρ, cotangentRel_snd_apply h, hρ.rightInverse_rightInverse]

/-- If `dρ_q` has a continuous right inverse, a covector `p` at `q` is related to a covector at
`ρ q` exactly when `p` vanishes on `ker dρ_q`, and that covector is then the reduced covector. -/
theorem cotangentRel_iff_eq_reductionMap {z : CotangentBundle I Q} {w : CotangentBundle IB B}
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse) :
    cotangentRel I IB ρ z w ↔
      (∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0) ∧ w = reductionMap I IB ρ z := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, eq_reductionMap_of_cotangentRel hρ h⟩, ?_⟩
  · obtain ⟨y, p⟩ := w
    obtain rfl : ρ z.proj = y := cotangentRel_proj h
    rw [cotangentRel_snd_apply h, hv]
    exact map_zero p
  · rintro ⟨hz, rfl⟩
    exact cotangentRel_reductionMap hρ hz

/-- **The reduced covector through a local section.** Let `σ` be a map through `q` that is a right
inverse of `ρ` near `ρ q`. For a covector `p` at `q` vanishing on `ker dρ_q`, the reduced covector
is the pullback `p ∘ dσ_(ρ q)`. -/
theorem reductionMap_eq_mk_comp_mfderiv {z : CotangentBundle I Q} {σ : B → Q}
    (hσ : σ (ρ z.proj) = z.proj) (hσd : MDifferentiableAt IB I σ (ρ z.proj))
    (hρd : MDifferentiableAt I IB ρ z.proj) (hρσ : ρ ∘ σ =ᶠ[𝓝 (ρ z.proj)] id)
    (hz : ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0) :
    reductionMap I IB ρ z =
      TotalSpace.mk' (EB →L[ℝ] ℝ) (ρ z.proj) (z.snd ∘L mfderiv IB I σ (ρ z.proj)) := by
  -- The differential of `σ` is a right inverse of `dρ_q`, by the chain rule for `ρ ∘ σ = id`.
  have hR : ∀ w, mfderiv I IB ρ z.proj (mfderiv IB I σ (ρ z.proj) w) = w := fun w ↦ by
    rw [← mfderiv_comp_apply_of_eq (ρ z.proj) hρd hσd hσ,
      ((hasMFDerivAt_id (ρ z.proj)).congr_of_eventuallyEq hρσ).mfderiv]
    rfl
  refine (eq_reductionMap_of_cotangentRel ⟨_, hR⟩
    ((cotangentRel_iff I IB ρ _ _).2 ⟨rfl, ContinuousLinearMap.ext fun v ↦ ?_⟩)).symm
  let u : TangentSpace I z.proj := mfderiv IB I σ (ρ z.proj) (mfderiv I IB ρ z.proj v)
  have h0 : z.snd (v - u) = 0 := hz _ (by rw [map_sub, hR, sub_self])
  rw [map_sub, sub_eq_zero] at h0
  -- The right-hand side is `z.2 (dσ (dρ v))`, the second component of `TotalSpace.mk'` applied.
  exact h0

end Descent

/-! ### Smoothness of the reduction map along a submersion -/

section Smooth

variable [IsManifold I ∞ Q] [IsManifold IB ∞ B] [I.Boundaryless]

/-- Near every covector, the reduction map agrees on horizontal covectors with a smooth map: the
pullback of covectors along a smooth family of local sections of `ρ`. -/
private theorem exists_contMDiffAt_eventuallyEq_reductionMap (hρ : IsSubmersion I IB ∞ ρ)
    (z₀ : CotangentBundle I Q) :
    ∃ Ψ : CotangentBundle I Q → CotangentBundle IB B,
      ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) ∞ Ψ z₀ ∧
      ∀ᶠ z in 𝓝 z₀, (∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0) →
        Ψ z = reductionMap I IB ρ z := by
  classical
  obtain ⟨W, hW, hW₀, s, hs, hρs, hs₀⟩ :=
    (hρ.isSubmersionAt z₀.proj).exists_contMDiffOn_uncurry_section
  have hproj : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ (fun z : CotangentBundle I Q ↦ z.proj) :=
    contMDiff_proj _
  -- The sections `s q`, replaced by a constant map wherever they miss the base point.
  set S : CotangentBundle I Q → B → Q := fun z ↦
    if s z.proj (ρ z.proj) = z.proj then s z.proj else fun _ ↦ z.proj with hS_def
  have hS : ∀ z, z.proj = S z (ρ z.proj) := fun z ↦ by
    by_cases h : s z.proj (ρ z.proj) = z.proj <;> simp [hS_def, h]
  have hSs : ∀ᶠ z in 𝓝 z₀, S z = s z.proj :=
    (hproj.continuous.continuousAt.eventually hs₀).mono fun z h ↦ by simp [hS_def, h]
  -- The covectors whose base point `q` has `(q, ρ q) ∈ W`.
  have hgraph : Continuous fun z : CotangentBundle I Q ↦ (z.proj, ρ z.proj) :=
    hproj.continuous.prodMk (hρ.contMDiff.continuous.comp hproj.continuous)
  have hW' : ∀ᶠ z in 𝓝 z₀, (z.proj, ρ z.proj) ∈ W :=
    hgraph.continuousAt.preimage_mem_nhds (hW.mem_nhds hW₀)
  refine ⟨fun z ↦ TotalSpace.mk' (EB →L[ℝ] ℝ) (ρ z.proj) (z.snd ∘L mfderiv IB I (S z) (ρ z.proj)),
    ?_, ?_⟩
  · -- Pull covectors back along the jointly smooth family `S`.
    refine contMDiffAt_mk_comp_mfderiv_uncurry (m := ∞) (n := ∞) (Ψ := id)
      (g := fun z ↦ ρ z.proj) hS contMDiffAt_id (hρ.contMDiff.comp hproj).contMDiffAt ?_ (by simp)
    have hsmooth : ContMDiffAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod IB) I ∞
        (fun p : CotangentBundle I Q × B ↦ uncurry s (p.1.proj, p.2)) (z₀, ρ z₀.proj) :=
      (hs.contMDiffAt (hW.mem_nhds hW₀)).comp (z₀, ρ z₀.proj)
        ((hproj.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_fst.eventually hSs] with p hp
    simp only [uncurry_apply_pair]
    exact congrFun hp p.2
  · filter_upwards [hSs, hW'] with z hz hzW hker
    rw [hz]
    refine (reductionMap_eq_mk_comp_mfderiv ?_ ?_ (hρ.contMDiff.mdifferentiableAt (by simp))
      ?_ hker).symm
    · rw [← hz]
      exact (hS z).symm
    · exact ((hs.contMDiffAt (hW.mem_nhds hzW)).comp (ρ z.proj)
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    · -- `ρ (s q w) = w` for `(q, w) ∈ W`, an open neighbourhood of `(q, ρ q)`.
      filter_upwards [(Continuous.prodMk_right z.proj).continuousAt.preimage_mem_nhds
        (hW.mem_nhds hzW)] with w hw
      exact hρs (z.proj, w) hw

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {m : WithTop ℕ∞}

/-- **The reduction map is smooth along smooth families of horizontal covectors.** If `ρ` is a
smooth submersion with boundaryless source, and a `C^m` family `f` of covectors on `Q` near `x₀`
vanishes on the vertical tangent vectors of `ρ`, then the family of reduced covectors of `f x` is
`C^m` at `x₀`. -/
theorem contMDiffAt_reductionMap_comp (hρ : IsSubmersion I IB ∞ ρ) {f : X → CotangentBundle I Q}
    {x₀ : X} (hf : ContMDiffAt IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m f x₀)
    (hz : ∀ᶠ x in 𝓝 x₀, ∀ v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v = 0) (hm : m ≤ ∞) :
    ContMDiffAt IX (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) m (reductionMap I IB ρ ∘ f) x₀ := by
  obtain ⟨Ψ, hΨ, hΨeq⟩ := exists_contMDiffAt_eventuallyEq_reductionMap hρ (f x₀)
  refine ((hΨ.of_le hm).comp x₀ hf).congr_of_eventuallyEq ?_
  filter_upwards [hf.continuousAt.eventually hΨeq, hz] with x hx hzx
  exact (hx hzx).symm

/-- **The reduction map is smooth along smooth families of horizontal covectors.** The global
version of `TauCeti.CotangentBundle.contMDiffAt_reductionMap_comp`. -/
theorem contMDiff_reductionMap_comp (hρ : IsSubmersion I IB ∞ ρ) {f : X → CotangentBundle I Q}
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v = 0) (hm : m ≤ ∞) :
    ContMDiff IX (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) m (reductionMap I IB ρ ∘ f) :=
  fun x ↦ contMDiffAt_reductionMap_comp hρ (hf x) (Eventually.of_forall (hz ·)) hm

/-- **Descent of the Liouville form.** For a smooth submersion `ρ` with boundaryless source and a
smooth family `f` of covectors on `Q` vanishing on the vertical tangent vectors of `ρ`, the
reduction map pulls the Liouville form of `T*B` back along `f` to the Liouville form of `T*Q`:
`(Ψ ∘ f)^* λ_B = f^* λ_Q`. -/
theorem mpullback_reductionMap_comp_liouvilleForm [IsManifold IX ∞ X] (hρ : IsSubmersion I IB ∞ ρ)
    {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v = 0) :
    SmoothForm.mpullback (reductionMap I IB ρ ∘ f) (contMDiff_reductionMap_comp hρ hf hz le_rfl)
        (liouvilleForm IB B) =
      SmoothForm.mpullback f hf (liouvilleForm I Q) := by
  apply Subtype.ext
  funext x
  ext v
  have hq : ContMDiff IX I ∞ fun x ↦ (f x).proj := (contMDiff_proj _).comp hf
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (g := ρ ∘ fun x ↦ (f x).proj) (fun _ ↦ rfl)
      ((contMDiff_reductionMap_comp hρ hf hz le_rfl x).mdifferentiableAt (by simp)),
    mpullback_liouvilleForm_apply_of_proj_comp_eq (g := fun x ↦ (f x).proj) (fun _ ↦ rfl)
      ((hf x).mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (hρ.contMDiff.mdifferentiableAt (by simp))
      ((hq x).mdifferentiableAt (by simp))]
  exact reductionMap_snd_apply_mfderiv (hρ.hasRightInverse_mfderiv (by simp) _) (hz x) _

/-- **Descent of the canonical symplectic form.** For a smooth submersion `ρ` with boundaryless
source and a smooth family `f` of covectors on `Q` vanishing on the vertical tangent vectors of `ρ`,
the reduction map pulls the canonical symplectic form `ω_B = -dλ_B` back along `f` to `ω_Q`:
`(Ψ ∘ f)^* ω_B = f^* ω_Q`. -/
theorem mpullback_reductionMap_comp_symplecticForm [IsManifold IX ∞ X] (hρ : IsSubmersion I IB ∞ ρ)
    {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
    (hz : ∀ x v, mfderiv I IB ρ (f x).proj v = 0 → (f x).snd v = 0) :
    SmoothForm.mpullback (reductionMap I IB ρ ∘ f) (contMDiff_reductionMap_comp hρ hf hz le_rfl)
        (symplecticForm IB B) =
      SmoothForm.mpullback f hf (symplecticForm I Q) := by
  rw [symplecticForm_eq_neg_mextDerivₗ, symplecticForm_eq_neg_mextDerivₗ, map_neg, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_reductionMap_comp_liouvilleForm hρ hf hz]

end Smooth

/-! ### The zero level of the cotangent moment map -/

section MomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [CompleteSpace E] [IsManifold I ∞ Q]
  [MulAction G Q] [ContMDiffSMul IG I ∞ G Q]

/-- **Horizontal covectors.** If the vertical tangent vectors of `ρ` at `q` are the orbit
directions `𝔤 · q`, a covector at `q` lies in the zero level of the cotangent moment map exactly
when it vanishes on the vertical tangent vectors. -/
theorem momentMap_eq_zero_iff_of_ker_eq {z : CotangentBundle I Q}
    (hker : (mfderiv I IB ρ z.proj).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent z.proj) :
    momentMap IG G z = 0 ↔ ∀ v, mfderiv I IB ρ z.proj v = 0 → z.snd v = 0 := by
  simp only [momentMap_eq_zero_iff, ← hker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- **The zero level consists of pullbacks.** If `dρ_q` has a continuous right inverse and the
vertical tangent vectors of `ρ` at `q` are the orbit directions, a covector at `q` lies in `μ⁻¹(0)`
exactly when it is the pullback of a covector at `ρ q`. -/
theorem momentMap_eq_zero_iff_exists_cotangentRel {z : CotangentBundle I Q}
    (hker : (mfderiv I IB ρ z.proj).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent z.proj)
    (hρ : (mfderiv I IB ρ z.proj).HasRightInverse) :
    momentMap IG G z = 0 ↔ ∃ w, cotangentRel I IB ρ z w := by
  rw [momentMap_eq_zero_iff_of_ker_eq hker]
  exact ⟨fun hz ↦ ⟨_, cotangentRel_reductionMap hρ hz⟩,
    fun ⟨_, h⟩ ↦ ((cotangentRel_iff_eq_reductionMap hρ).1 h).1⟩

/-- **The reduction map is onto.** If `ρ` is surjective and its differentials have continuous
right inverses, every covector on `B` is the reduced covector of a covector in `μ⁻¹(0)`, namely
of its pullback. -/
theorem exists_momentMap_eq_zero_and_reductionMap_eq
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hsurj : Surjective ρ) (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (w : CotangentBundle IB B) :
    ∃ z : CotangentBundle I Q, momentMap IG G z = 0 ∧ reductionMap I IB ρ z = w := by
  obtain ⟨y, p⟩ := w
  obtain ⟨q, rfl⟩ := hsurj y
  set z : CotangentBundle I Q := TotalSpace.mk' (E →L[ℝ] ℝ) q (p ∘L mfderiv I IB ρ q)
  have h : cotangentRel I IB ρ z (TotalSpace.mk' (EB →L[ℝ] ℝ) (ρ q) p) :=
    (cotangentRel_mk_iff I IB ρ q _ p).2 rfl
  exact ⟨z, (momentMap_eq_zero_iff_exists_cotangentRel (hker q) (hρ q)).2 ⟨_, h⟩,
    (eq_reductionMap_of_cotangentRel (hρ q) h).symm⟩

variable [ContMDiffConstSMul I ∞ G Q]

/-- **The reduction map is invariant on the zero level.** For a `G`-invariant map `ρ` whose
differentials have continuous right inverses and whose vertical tangent vectors are the orbit
directions, the reduced covector of `g • (q, p)` is that of `(q, p)` whenever `μ(q, p) = 0`. -/
theorem reductionMap_smul
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hinv : ∀ (g : G) q, ρ (g • q) = ρ q) (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = 0) (g : G) :
    reductionMap I IB ρ (g • z) = reductionMap I IB ρ z :=
  (eq_reductionMap_of_cotangentRel (hρ _) ((cotangentRel_smul_iff g (hinv g) z (hρd _) _).2
    (cotangentRel_reductionMap (hρ _) ((momentMap_eq_zero_iff_of_ker_eq (hker z.proj)).1 hz)))).symm

/-- **The fibres of the reduction map on the zero level are the orbits.** Let the differentials
of `ρ` have continuous right inverses, its vertical tangent vectors be the orbit directions, and
its fibres be the `G`-orbits. Two covectors in `μ⁻¹(0)` have the same reduced covector exactly
when they lie in one `G`-orbit. -/
theorem reductionMap_eq_reductionMap_iff
    (hker : ∀ q, (mfderiv I IB ρ q).ker = (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hfib : ∀ q q', ρ q = ρ q' ↔ ∃ g : G, g • q = q') (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse) {z z' : CotangentBundle I Q}
    (hz : momentMap IG G z = 0) (hz' : momentMap IG G z' = 0) :
    reductionMap I IB ρ z = reductionMap I IB ρ z' ↔ ∃ g : G, g • z = z' := by
  have hinv : ∀ (g : G) q, ρ (g • q) = ρ q := fun g q ↦ ((hfib _ _).2 ⟨g, rfl⟩).symm
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ (reductionMap_smul hker hinv hρd hρ hz g).symm⟩
  obtain ⟨g, hg⟩ := (hfib z.proj z'.proj).1 (congrArg TotalSpace.proj h)
  refine ⟨g, ?_⟩
  -- Both `g • z` and `z'` are pullbacks of the same covector at `ρ q'`, with base point `q'`.
  have h₁ : cotangentRel I IB ρ (g • z) (reductionMap I IB ρ z') :=
    (cotangentRel_smul_iff g (hinv g) z (hρd _) _).2
      (h ▸ cotangentRel_reductionMap (hρ _) ((momentMap_eq_zero_iff_of_ker_eq (hker z.proj)).1 hz))
  have h₂ : cotangentRel I IB ρ z' (reductionMap I IB ρ z') :=
    cotangentRel_reductionMap (hρ _) ((momentMap_eq_zero_iff_of_ker_eq (hker z'.proj)).1 hz')
  exact eq_of_cotangentRel_of_proj_eq h₁ h₂ ((proj_smul g z).trans hg)

end MomentMap

end TauCeti.CotangentBundle

/-! ### Cotangent reduction at zero for a free proper action -/

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
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q] [ProperSMul G Q] [IsCancelSMul G Q]

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ E] in
/-- The model space `ℝ^(dim Q - dim G) × (ℝ^(dim Q - dim G))*` of the cotangent bundle of the orbit
space `Q ⧸ G` has dimension `2 (dim Q - dim G)`. -/
theorem finrank_quotientModelSpace_prod_dual :
    finrank ℝ (QuotientModelSpace EG E × (QuotientModelSpace EG E →L[ℝ] ℝ)) =
      2 * (finrank ℝ E - finrank ℝ EG) := by
  rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, finrank_quotientModelSpace, two_mul]

/-- **Cotangent reduction at zero: the fibres.** For a free proper action, two covectors in the zero
level of the cotangent moment map have the same reduced covector on `Q ⧸ G` exactly when they lie in
one `G`-orbit. -/
theorem reductionMap_eq_reductionMap_iff_quotientMk {z z' : CotangentBundle I Q}
    (hz : momentMap IG G z = 0) (hz' : momentMap IG G z' = 0) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    reductionMap I 𝓘(ℝ, QuotientModelSpace EG E) (Quotient.mk (MulAction.orbitRel G Q)) z =
        reductionMap I 𝓘(ℝ, QuotientModelSpace EG E) (Quotient.mk (MulAction.orbitRel G Q)) z' ↔
      ∃ g : G, g • z = z' := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact CotangentBundle.reductionMap_eq_reductionMap_iff ker_mfderiv_quotientMk
    (fun _ _ ↦ MulAction.quotientMk_eq_quotientMk_iff_exists_smul_eq)
    (fun q ↦ (contMDiff_quotientMk q).mdifferentiableAt (by simp))
    (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp)) hz hz'

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Cotangent reduction at zero: surjectivity.** For a free proper action, every covector on the
orbit space `Q ⧸ G` is the reduced covector of a covector in the zero level of the cotangent moment
map. -/
theorem exists_momentMap_eq_zero_and_reductionMap_eq_quotientMk :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ w : CotangentBundle 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q),
      ∃ z : CotangentBundle I Q, momentMap IG G z = 0 ∧
        reductionMap I 𝓘(ℝ, QuotientModelSpace EG E) (Quotient.mk (MulAction.orbitRel G Q)) z =
          w := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact CotangentBundle.exists_momentMap_eq_zero_and_reductionMap_eq ker_mfderiv_quotientMk
    Quotient.mk_surjective (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp))

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X]

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Cotangent reduction at zero: descent of the symplectic form.** For a free proper action and a
smooth family `f` of covectors in the zero level of the cotangent moment map, the reduction map to
`T*(Q ⧸ G)` is smooth along `f` and pulls the canonical symplectic form of `T*(Q ⧸ G)` back to that
of `T*Q`. -/
theorem mpullback_reductionMap_comp_symplecticForm_quotientMk {f : X → CotangentBundle I Q}
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f) (hz : ∀ x, momentMap IG G (f x) = 0) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    SmoothForm.mpullback
        (reductionMap I 𝓘(ℝ, QuotientModelSpace EG E) (Quotient.mk (MulAction.orbitRel G Q)) ∘ f)
        (contMDiff_reductionMap_comp isSubmersion_quotientMk hf
          (fun x ↦ (momentMap_eq_zero_iff_of_ker_eq (ker_mfderiv_quotientMk _)).1 (hz x)) le_rfl)
        (symplecticForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q)) =
      SmoothForm.mpullback f hf (symplecticForm I Q) := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact CotangentBundle.mpullback_reductionMap_comp_symplecticForm isSubmersion_quotientMk hf
    fun x ↦ (momentMap_eq_zero_iff_of_ker_eq (ker_mfderiv_quotientMk _)).1 (hz x)

end ProperSMul

/-! ### The dimension of the reduced space at a coadjoint-fixed value -/

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}
  {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

/-- **The dimension of the reduced space at an infinitesimally coadjoint-fixed value.** If every
element of `𝔤` annihilates `ν`, `ν ⁅ξ, ·⁆ = 0`, as for a coadjoint-fixed `ν` such as `0`, the model
space `ℝ^(n - dim G_ν)` of the reduced space `μ⁻¹(ν) / G_ν` of `T*Q`, where `n = 2 dim Q - dim G`
is the dimension of the level `μ⁻¹(ν)` and `G_ν` carries the Lie group structure `d`, has dimension
`2 (dim Q - dim G)`, that of `T*(Q ⧸ G)`: the coadjoint stabilizer of `ν` has the dimension of `G`.
-/
theorem finrank_quotientModelSpace_level
    (hν : lieAnnihilator ℝ (GroupLieAlgebra IG G) ν = ⊤)
    (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
    (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer ν) F) :
    finrank ℝ (ProperSMul.QuotientModelSpace F (Fin n → ℝ)) = 2 * (finrank ℝ E - finrank ℝ EG) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have hF : finrank ℝ F = finrank ℝ EG := by
    rw [d.finrank_eq_finrank_lieSubalgebraOfSubgroup,
      Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
        BoundarylessManifold.isInteriorPoint, hν]
    exact LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq
  -- The Lie algebra `GroupLieAlgebra IG G` is by definition the tangent space `EG` at `1`.
  have hG : finrank ℝ (GroupLieAlgebra IG G) = finrank ℝ EG := rfl
  rw [ProperSMul.finrank_quotientModelSpace, Module.finrank_fin_fun, hF, ← hn, finrank_prod,
    ContinuousLinearMap.dual_finrank_eq, hG]
  omega

end TauCeti.CotangentBundle
