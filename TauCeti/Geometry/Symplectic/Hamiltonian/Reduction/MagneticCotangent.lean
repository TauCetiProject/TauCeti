/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient.ProperAction
public import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Translate
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LevelShift
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent

/-!
# Cotangent reduction at a nonzero value: the magnetic term

Let a Lie group `G` act smoothly on a manifold `Q`, and let `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))` be the
moment map of the cotangent-lifted action on `T*Q` (`TauCeti.CotangentBundle.momentMap`). At the
value `0`, the reduction map `(q, p) ↦ (ρ q, p ∘ (dρ_q)⁻¹)` along the orbit projection
`ρ : Q → Q ⧸ G` of a free proper action identifies `μ⁻¹(0) ⧸ G` with `T*(Q ⧸ G)`, carrying the
canonical symplectic form (`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent`). This
file treats a nonzero value `ν ∈ 𝔤*`.

Fix a `G`-invariant one-form `α` on `Q` that pairs every fundamental vector field with `-ν`:
`α(ξ_Q) = -ν(ξ)`. For a principal connection `A` of the free action, normalized by `A(ξ_Q) = -ξ`
on the fundamental vector fields of the left action, the form `α = ⟨ν, A⟩` is such a form when `ν`
is coadjoint-invariant; conversely, the existence of an invariant `α` forces `ν` to be
coadjoint-invariant
(`TauCeti.CotangentBundle.coadjointRepresentation_apply_eq_self_of_forall_eval_eq`). Translating
the fibres by `α`, `τ_α (q, p) = (q, p + α_q)`, carries the level `μ⁻¹(ν)` onto `μ⁻¹(0)`. The
**magnetic reduction map** (`TauCeti.CotangentBundle.magneticReductionMap`) is the composite

`Ψ_α (q, p) = (ρ q, (p + α_q) ∘ (dρ_q)⁻¹)`

of this translation with the reduction map at zero. On the level `μ⁻¹(ν)`:

* `Ψ_α` is invariant under `G` (`TauCeti.CotangentBundle.magneticReductionMap_smul`), its fibres
  are exactly the `G`-orbits
  (`TauCeti.CotangentBundle.magneticReductionMap_eq_magneticReductionMap_iff`), and it is onto
  `T*B` (`TauCeti.CotangentBundle.exists_momentMap_eq_and_magneticReductionMap_eq`). So it
  identifies the reduced space `μ⁻¹(ν) ⧸ G` with `T*(Q ⧸ G)` as a set.
* **The magnetic term.** The exterior derivative `dα` is invariant and kills the orbit
  directions, so it is the pullback `ρ^* β` of a unique two-form `β` on `Q ⧸ G`, which is closed
  (`ProperSMul.existsUnique_isClosed_and_mpullback_quotientMk_eq_mextDerivₗ`). For `α = ⟨ν, A⟩`
  it is `⟨ν, F_A⟩`, the `ν`-component of the curvature, since `ν` vanishes on brackets.
* **The reduced form.** Along every smooth family `f` of covectors in `μ⁻¹(ν)`, `Ψ_α` pulls the
  magnetic symplectic form `ω_B + π_B^* β` of `T*B` back to the canonical form of `T*Q`:
  `(Ψ_α ∘ f)^* (ω_B + π_B^* β) = f^* ω_Q`
  (`TauCeti.CotangentBundle.mpullback_magneticReductionMap_comp_symplecticForm_add`). Indeed,
  `τ_α` pulls `ω_Q` back to `ω_Q - π_Q^* dα`, the reduction map at zero carries `ω_B` to the first
  term, and `π_B ∘ Ψ_α = ρ ∘ π_Q` carries `π_B^* β` to `π_Q^* dα`. This is the form-level content
  of the symplectomorphism `μ⁻¹(ν) ⧸ G ≅ (T*(Q ⧸ G), ω_B + π_B^* β)`, with the sign
  `ω_red = ω_can + pr^* β` for the convention `ω = -dλ`.
* **Change of connection.** If a second invariant one-form `α'` pairs the fundamental vector
  fields with the same `-ν`, its difference with `α` is the pullback `ρ^* γ` of a one-form `γ` on
  `Q ⧸ G` (`ProperSMul.existsUnique_mpullback_quotientMk_eq_sub`), and on `μ⁻¹(ν)` the two
  reduction maps differ by the fibre translation by `γ`: `Ψ_α' = τ_γ ∘ Ψ_α`
  (`TauCeti.CotangentBundle.magneticReductionMap_eq_vectorBundleTranslateDiffeomorph`). The two
  magnetic terms differ by the exact form `dγ`, which is the change of the canonical form under
  `τ_γ` (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm`).

As in the reduction at zero, the statements in the namespace `TauCeti.CotangentBundle` are made for
a map `ρ : Q → B` with the properties of an orbit projection that they use, and those in the
namespace `ProperSMul` apply them to the orbit projection of a free proper action. The
construction of principal connections, which supply the forms `α`, is not part of this file, and
no quotient manifold structure on `μ⁻¹(ν) ⧸ G` is built here.

## Main definitions

* `TauCeti.CotangentBundle.magneticReductionMap`: the map
  `Ψ_α (q, p) = (ρ q, (p + α_q) ∘ (dρ_q)⁻¹)`.

## Main results

* `TauCeti.CotangentBundle.magneticReductionMap_eq_magneticReductionMap_iff`: on `μ⁻¹(ν)`, the
  fibres of `Ψ_α` are the `G`-orbits.
* `TauCeti.CotangentBundle.exists_momentMap_eq_and_magneticReductionMap_eq`: `Ψ_α` maps `μ⁻¹(ν)`
  onto `T*B`.
* `TauCeti.CotangentBundle.mpullback_magneticReductionMap_comp_symplecticForm_add`: `Ψ_α` pulls
  `ω_B + π_B^* β` back to `ω_Q` along smooth families in `μ⁻¹(ν)`.
* `TauCeti.CotangentBundle.magneticReductionMap_eq_vectorBundleTranslateDiffeomorph`: change of
  connection.
* `ProperSMul.existsUnique_isClosed_and_mpullback_quotientMk_eq_mextDerivₗ`: the magnetic term on
  `Q ⧸ G`.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Springer, 1999, §§6.6 and 12.1 (magnetic terms and cotangent momentum maps).
* Jerrold E. Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor S. Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, §2.2
  (cotangent bundle reduction at a coadjoint-invariant value, the magnetic term `⟨ν, F_A⟩`).
* Shlomo Sternberg, *Minimal coupling and the symplectic mechanics of a classical particle in the
  presence of a Yang–Mills field*, Proceedings of the National Academy of Sciences 74 (1977),
  5253–5254.
-/

public section

noncomputable section

open Bundle Function Manifold Module
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {ρ : Q → B}

/-! ### The magnetic reduction map -/

section Map

variable [IsManifold I ∞ Q]

variable (I IB ρ) in
/-- The **magnetic reduction map** of a one-form `α` on `Q`: translate the fibres of `T*Q` by `α`,
then reduce along `ρ`, `Ψ_α (q, p) = (ρ q, (p + α_q) ∘ (dρ_q)⁻¹)`. On a level `μ⁻¹(ν)` of the
cotangent moment map, for an invariant `α` pairing every fundamental vector field with `-ν`, the
translated covectors vanish on the orbit directions, and `Ψ_α` identifies `μ⁻¹(ν) ⧸ G` with
`T*B`. -/
def magneticReductionMap (α : SmoothForm I Q ℝ 1) (z : CotangentBundle I Q) :
    CotangentBundle IB B :=
  reductionMap I IB ρ (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff z)

variable (α : SmoothForm I Q ℝ 1)

/-- The magnetic reduction map is the reduction map applied to the translated covector. -/
theorem magneticReductionMap_def (z : CotangentBundle I Q) :
    magneticReductionMap I IB ρ α z =
      reductionMap I IB ρ (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) :=
  (rfl)

/-- The magnetic reduction map lies over `ρ`. -/
@[simp]
theorem proj_magneticReductionMap (z : CotangentBundle I Q) :
    (magneticReductionMap I IB ρ α z).proj = ρ z.proj := by
  rw [magneticReductionMap_def, proj_reductionMap, vectorBundleTranslateDiffeomorph_apply]

/-- The magnetic reduction map lies over `ρ`, as an identity of maps. -/
theorem proj_comp_magneticReductionMap :
    TotalSpace.proj ∘ magneticReductionMap I IB ρ α = ρ ∘ TotalSpace.proj :=
  funext (proj_magneticReductionMap α)

/-- For the zero form, the magnetic reduction map is the reduction map. -/
@[simp]
theorem magneticReductionMap_zero : magneticReductionMap I IB ρ 0 = reductionMap I IB ρ :=
  funext fun z ↦ by simp [magneticReductionMap_def]

end Map

/-! ### Levels of the cotangent moment map -/

section MomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [CompleteSpace E] [IsManifold I ∞ Q]
  [MulAction G Q] [ContMDiffSMul IG I ∞ G Q] {α : SmoothForm I Q ℝ 1}
  {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

/-- On the level `μ⁻¹(ν)`, the covectors translated by `α` vanish on the vertical tangent vectors
of `ρ`, when these are the orbit directions. -/
theorem vectorBundleTranslateDiffeomorph_snd_eq_zero_of_momentMap_eq
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) :
    ∀ v, mfderiv I IB ρ (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z).proj v = 0 →
      (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z).snd v = 0 :=
  (momentMap_eq_zero_iff_of_ker_eq (hker _)).1
    ((momentMap_vectorBundleTranslateDiffeomorph_eq_zero_iff hα z).2 hz)

/-- On the level `μ⁻¹(ν)`, the covector translated by `α` is the pullback of its image under the
magnetic reduction map: `p + α_q = (Ψ_α (q, p)).snd ∘ dρ_q`, when the vertical tangent vectors of
`ρ` are the orbit directions and `dρ_q` has a continuous right inverse. -/
theorem cotangentRel_magneticReductionMap
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) :
    cotangentRel I IB ρ
      (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z)
      (magneticReductionMap I IB ρ α z) :=
  cotangentRel_reductionMap (hρ _)
    (vectorBundleTranslateDiffeomorph_snd_eq_zero_of_momentMap_eq hker hα hz)

/-- **The value of the magnetic reduction map.** On the level `μ⁻¹(ν)`, when the vertical tangent
vectors of `ρ` are the orbit directions and `dρ_q` has a continuous right inverse, the reduced
covector evaluates on `dρ_q v` as `p + α_q` on `v`:
`(Ψ_α (q, p)).snd (dρ_q v) = p v + α_q v`. -/
theorem magneticReductionMap_snd_apply_mfderiv
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (v : TangentSpace I z.proj) :
    (magneticReductionMap I IB ρ α z).snd (mfderiv I IB ρ z.proj v) =
      z.snd v + α.val z.proj ![v] := by
  have h := cotangentRel_magneticReductionMap hker hρ hα hz
  rw [vectorBundleTranslateDiffeomorph_apply] at h
  exact (cotangentRel_snd_apply h v).symm.trans (by simp)

/-- **The magnetic reduction map is onto.** If `ρ` is surjective, its differentials have
continuous right inverses and its vertical tangent vectors are the orbit directions, every
covector on `B` is the image under `Ψ_α` of a covector in the level `μ⁻¹(ν)`. -/
theorem exists_momentMap_eq_and_magneticReductionMap_eq
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hsurj : Surjective ρ) (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) (w : CotangentBundle IB B) :
    ∃ z : CotangentBundle I Q, momentMap IG G z = ν ∧ magneticReductionMap I IB ρ α z = w := by
  obtain ⟨z₀, hz₀, rfl⟩ := exists_momentMap_eq_zero_and_reductionMap_eq hker hsurj hρ w
  -- The preimage of `z₀` under the translation lies in `μ⁻¹(ν)`.
  refine ⟨(vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff).symm z₀, ?_, ?_⟩
  · rw [← momentMap_vectorBundleTranslateDiffeomorph_eq_zero_iff hα, Diffeomorph.apply_symm_apply]
    exact hz₀
  · rw [magneticReductionMap_def, Diffeomorph.apply_symm_apply]

/-- **Change of connection.** Let `ρ` be a smooth map whose differentials have continuous right
inverses and whose vertical tangent vectors are the orbit directions, and let `α` pair the
fundamental vector fields with `-ν`. If `α' = α + ρ^* γ` for a one-form `γ` on `B`, so that `α'`
pairs them with `-ν` as well, then on the level `μ⁻¹(ν)` the magnetic reduction map of `α'` is that
of `α` followed by the fibre translation by `γ`: `Ψ_α' = τ_γ ∘ Ψ_α`. -/
theorem magneticReductionMap_eq_vectorBundleTranslateDiffeomorph [IsManifold IB ∞ B]
    (hρs : ContMDiff I IB ∞ ρ) (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {α' : SmoothForm I Q ℝ 1}
    {γ : SmoothForm IB B ℝ 1} (hγ : SmoothForm.mpullback ρ hρs γ = α' - α)
    {z : CotangentBundle I Q} (hz : momentMap IG G z = ν) :
    magneticReductionMap I IB ρ α' z =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
        (SmoothForm.degreeOneEquiv γ).contMDiff (magneticReductionMap I IB ρ α z) := by
  -- `Ψ_α' z` is the reduction of `τ_(α' - α) (τ_α z)`, which is related to `τ_γ (Ψ_α z)`.
  have h := cotangentRel_vectorBundleTranslateDiffeomorph_mpullback hρs γ
    (cotangentRel_magneticReductionMap hker hρ hα hz)
  rw [hγ] at h
  rw [magneticReductionMap_def, magneticReductionMap_def,
    ← vectorBundleTranslateDiffeomorph_trans_sub (α := α) α', Diffeomorph.coe_trans, comp_apply]
  exact (eq_reductionMap_of_cotangentRel (hρ _) h).symm

variable [ContMDiffConstSMul I ∞ G Q]

/-- **The magnetic reduction map is invariant on the level.** For a `G`-invariant map `ρ` whose
differentials have continuous right inverses and whose vertical tangent vectors are the orbit
directions, and for a `G`-invariant one-form `α` pairing the fundamental vector fields with `-ν`,
`Ψ_α (g • z) = Ψ_α z` whenever `μ(z) = ν`. -/
theorem magneticReductionMap_smul
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hinvρ : ∀ (g : G) q, ρ (g • q) = ρ q) (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (g : G) :
    magneticReductionMap I IB ρ α (g • z) = magneticReductionMap I IB ρ α z := by
  rw [magneticReductionMap_def, magneticReductionMap_def,
    vectorBundleTranslateDiffeomorph_smul hinv]
  exact reductionMap_smul hker hinvρ hρd hρ
    ((momentMap_vectorBundleTranslateDiffeomorph_eq_zero_iff hα z).2 hz) g

/-- **The fibres of the magnetic reduction map on the level are the orbits.** Let the differentials
of `ρ` have continuous right inverses, its vertical tangent vectors be the orbit directions and
its fibres be the `G`-orbits, and let `α` be a `G`-invariant one-form pairing the fundamental
vector fields with `-ν`. Two covectors in `μ⁻¹(ν)` have the same image under `Ψ_α` exactly when
they lie in one `G`-orbit. -/
theorem magneticReductionMap_eq_magneticReductionMap_iff
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hfib : ∀ q q', ρ q = ρ q' ↔ ∃ g : G, g • q = q') (hρd : ∀ q, MDifferentiableAt I IB ρ q)
    (hρ : ∀ q, (mfderiv I IB ρ q).HasRightInverse)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z z' : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) (hz' : momentMap IG G z' = ν) :
    magneticReductionMap I IB ρ α z = magneticReductionMap I IB ρ α z' ↔
      ∃ g : G, g • z = z' := by
  rw [magneticReductionMap_def, magneticReductionMap_def,
    reductionMap_eq_reductionMap_iff hker hfib hρd hρ
      ((momentMap_vectorBundleTranslateDiffeomorph_eq_zero_iff hα z).2 hz)
      ((momentMap_vectorBundleTranslateDiffeomorph_eq_zero_iff hα z').2 hz')]
  simp only [← vectorBundleTranslateDiffeomorph_smul hinv, (EquivLike.injective _).eq_iff]

end MomentMap

/-! ### The magnetic term and change of connection -/

section Smooth

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G] [CompleteSpace E] [IsManifold I ∞ Q]
  [IsManifold IB ∞ B] [I.Boundaryless] [MulAction G Q] [ContMDiffSMul IG I ∞ G Q]
  {α : SmoothForm I Q ℝ 1} {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {m : WithTop ℕ∞}

/-- **The magnetic reduction map is smooth along smooth families in a level.** For a smooth
submersion `ρ` with boundaryless source whose vertical tangent vectors are the orbit directions,
and a one-form `α` pairing the fundamental vector fields with `-ν`, the image under `Ψ_α` of a
`C^m` family of covectors in `μ⁻¹(ν)` is `C^m`. -/
theorem contMDiff_magneticReductionMap_comp (hρ : IsSubmersion I IB ∞ ρ)
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {f : X → CotangentBundle I Q}
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m f) (hz : ∀ x, momentMap IG G (f x) = ν)
    (hm : m ≤ ∞) :
    ContMDiff IX (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) m (magneticReductionMap I IB ρ α ∘ f) :=
  contMDiff_reductionMap_comp hρ
    (((vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
      (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff.of_le hm).comp hf)
    (fun x ↦ vectorBundleTranslateDiffeomorph_snd_eq_zero_of_momentMap_eq hker hα (hz x)) hm

variable [IsManifold IX ∞ X]

/-- **The reduced form at a nonzero value.** Let `ρ` be a smooth submersion with boundaryless
source whose vertical tangent vectors are the orbit directions, let `α` pair the fundamental
vector fields with `-ν`, and let `β` be a two-form on `B` with `ρ^* β = dα`, the magnetic term.
Along a smooth family `f` of covectors in the level `μ⁻¹(ν)`, the magnetic reduction map pulls
the magnetic symplectic form `ω_B + π_B^* β` of `T*B` back to the canonical symplectic form of
`T*Q`: `(Ψ_α ∘ f)^* (ω_B + π_B^* β) = f^* ω_Q`. -/
theorem mpullback_magneticReductionMap_comp_symplecticForm_add (hρ : IsSubmersion I IB ∞ ρ)
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {β : SmoothForm IB B ℝ 2}
    (hβ : SmoothForm.mpullback ρ hρ.contMDiff β = mextDerivₗ I 1 α) {f : X → CotangentBundle I Q}
    (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f) (hz : ∀ x, momentMap IG G (f x) = ν) :
    SmoothForm.mpullback (magneticReductionMap I IB ρ α ∘ f)
        (contMDiff_magneticReductionMap_comp hρ hker hα hf hz le_rfl)
        (symplecticForm IB B +
          SmoothForm.mpullback (TotalSpace.proj : CotangentBundle IB B → B) (contMDiff_proj _) β) =
      SmoothForm.mpullback f hf (symplecticForm I Q) := by
  set τ := vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff
  have hproj : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞
      (TotalSpace.proj : CotangentBundle I Q → Q) := contMDiff_proj _
  -- The reduction map at zero carries `ω_B` to `(τ ∘ f)^* ω_Q = f^* (ω_Q - π_Q^* dα)`.
  have h₁ : SmoothForm.mpullback (magneticReductionMap I IB ρ α ∘ f)
      (contMDiff_magneticReductionMap_comp hρ hker hα hf hz le_rfl) (symplecticForm IB B) =
      SmoothForm.mpullback f hf (symplecticForm I Q -
        SmoothForm.mpullback TotalSpace.proj hproj (mextDerivₗ I 1 α)) := by
    rw [← mpullback_vectorBundleTranslateDiffeomorph_symplecticForm,
      SmoothForm.mpullback_mpullback]
    exact mpullback_reductionMap_comp_symplecticForm hρ (τ.contMDiff.comp hf)
      fun x ↦ vectorBundleTranslateDiffeomorph_snd_eq_zero_of_momentMap_eq hker hα (hz x)
  -- Since `π_B ∘ Ψ_α = ρ ∘ π_Q`, the magnetic term pulls back to `f^* π_Q^* dα`.
  have h₂ : SmoothForm.mpullback (magneticReductionMap I IB ρ α ∘ f)
      (contMDiff_magneticReductionMap_comp hρ hker hα hf hz le_rfl)
      (SmoothForm.mpullback (TotalSpace.proj : CotangentBundle IB B → B) (contMDiff_proj _) β) =
      SmoothForm.mpullback f hf
        (SmoothForm.mpullback TotalSpace.proj hproj (mextDerivₗ I 1 α)) := by
    rw [← hβ, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_mpullback]
    simp only [← comp_assoc, proj_comp_magneticReductionMap]
  rw [map_add, h₁, h₂, ← map_add, sub_add_cancel]

end Smooth

end TauCeti.CotangentBundle

/-! ### Cotangent reduction at a nonzero value for a free proper action -/

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
  {α α' : SmoothForm I Q ℝ 1} {ν : Module.Dual ℝ (GroupLieAlgebra IG G)}

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **The magnetic term.** For a free proper action and a `G`-invariant one-form `α` pairing
every fundamental vector field with `-ν`, the exterior derivative `dα` is the pullback along the
orbit projection of a unique two-form `β` on `Q ⧸ G`, and `β` is closed. -/
theorem existsUnique_isClosed_and_mpullback_quotientMk_eq_mextDerivₗ
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∃! β : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 2,
      β.IsClosed ∧
        SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q)) contMDiff_quotientMk β =
          mextDerivₗ I 1 α := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  have hsub := isSubmersion_quotientMk (I := IG) (G := G) (I' := I) (M := Q)
  -- `dα` kills the orbit directions in its first argument, hence in both by antisymmetry.
  have h₀ : ∀ x (v : Fin 2 → TangentSpace I x) (ξ : GroupLieAlgebra IG G),
      v 0 = fundamentalVectorField I ξ x → (mextDerivₗ I 1 α).val x v = 0 := fun x v ξ hv ↦ by
    have hv' : v = ![fundamentalVectorField I ξ x, v 1] := by
      ext i; fin_cases i
      · exact hv
      · rfl
    rw [hv']
    exact mextDerivₗ_apply_fundamentalVectorField_eq_zero hinv
      (c := -ν) (fun x ξ ↦ (hα x ξ).trans (LinearMap.neg_apply ν ξ).symm) ξ x (v 1)
  have hbasic := isBasic_quotientMk (IG := IG) (G := G) (φ := mextDerivₗ I 1 α)
    (fun g ↦ by rw [← SmoothForm.mextDerivₗ_mpullback, hinv]) fun x v j ξ hv ↦ by
      fin_cases j
      · exact h₀ x v ξ hv
      · have hswap : (mextDerivₗ I 1 α).val x (v ∘ Equiv.swap 0 1) =
            -(mextDerivₗ I 1 α).val x v :=
          ((mextDerivₗ I 1 α).val x).toAlternatingMap.map_swap v (show (0 : Fin 2) ≠ 1 by decide)
        rw [← neg_eq_zero, ← hswap]
        exact h₀ x _ ξ (by simpa using hv)
  refine ⟨SmoothForm.descendedForm hsub Quotient.mk_surjective _ hbasic,
    ⟨?_, SmoothForm.mpullback_descendedForm⟩, fun β hβ ↦ SmoothForm.eq_descendedForm_iff.2 hβ.2⟩
  rw [SmoothForm.isClosed_descendedForm_iff]
  exact SmoothForm.isClosed_mextDerivₗ _

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Change of connection on the base.** For a free proper action, if two `G`-invariant one-forms
`α` and `α'` pair every fundamental vector field with the same `-ν`, their difference is the
pullback along the orbit projection of a unique one-form `γ` on `Q ⧸ G`. -/
theorem existsUnique_mpullback_quotientMk_eq_sub
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) α = α)
    (hinv' : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g) α' = α')
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ)
    (hα' : ∀ x ξ, α'.val x ![fundamentalVectorField I ξ x] = -ν ξ) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∃! γ : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 1,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q)) contMDiff_quotientMk γ =
        α' - α := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have hsub := isSubmersion_quotientMk (I := IG) (G := G) (I' := I) (M := Q)
  have hbasic := isBasic_quotientMk (IG := IG) (G := G) (φ := α' - α)
    (fun g ↦ by rw [map_sub, hinv, hinv']) fun x v j ξ hv ↦ by
      have hv' : v = ![fundamentalVectorField I ξ x] := by
        ext i; fin_cases i; fin_cases j; exact hv
      simp [hv', hα, hα']
  exact ⟨SmoothForm.descendedForm hsub Quotient.mk_surjective _ hbasic,
    SmoothForm.mpullback_descendedForm, fun γ hγ ↦ SmoothForm.eq_descendedForm_iff.2 hγ⟩

/-- **Cotangent reduction at a nonzero value: the fibres.** For a free proper action and a
`G`-invariant one-form `α` pairing every fundamental vector field with `-ν`, two covectors in the
level `μ⁻¹(ν)` of the cotangent moment map have the same image under the magnetic reduction map to
`T*(Q ⧸ G)` exactly when they lie in one `G`-orbit. -/
theorem magneticReductionMap_eq_magneticReductionMap_iff_quotientMk
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : Q ↦ g • x) (contMDiff_const_smul g) α = α)
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
    (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp)) hinv hα hz hz'

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Cotangent reduction at a nonzero value: surjectivity.** For a free proper action and a
one-form `α` pairing every fundamental vector field with `-ν`, every covector on the orbit space
`Q ⧸ G` is the image under the magnetic reduction map of a covector in the level `μ⁻¹(ν)` of the
cotangent moment map. -/
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

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Cotangent reduction at a nonzero value: the reduced form.** For a free proper action, a
one-form `α` pairing every fundamental vector field with `-ν`, and the magnetic term `β` on
`Q ⧸ G` with `ρ^* β = dα`, the magnetic reduction map pulls the magnetic symplectic form
`ω + π^* β` of `T*(Q ⧸ G)` back to the canonical symplectic form of `T*Q` along every smooth
family `f` of covectors in the level `μ⁻¹(ν)`. -/
theorem mpullback_magneticReductionMap_comp_symplecticForm_add_quotientMk
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ)
    {f : X → CotangentBundle I Q} (hf : ContMDiff IX (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f)
    (hz : ∀ x, momentMap IG G (f x) = ν) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ β : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 2,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q)) contMDiff_quotientMk β =
        mextDerivₗ I 1 α →
      SmoothForm.mpullback
          (magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
            (Quotient.mk (MulAction.orbitRel G Q)) α ∘ f)
          (contMDiff_magneticReductionMap_comp isSubmersion_quotientMk ker_mfderiv_quotientMk hα
            hf hz le_rfl)
          (symplecticForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) +
            SmoothForm.mpullback TotalSpace.proj (contMDiff_proj _) β) =
        SmoothForm.mpullback f hf (symplecticForm I Q) := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact fun β hβ ↦ CotangentBundle.mpullback_magneticReductionMap_comp_symplecticForm_add
    isSubmersion_quotientMk ker_mfderiv_quotientMk hα hβ hf hz

omit [ContMDiffConstSMul I ∞ G Q] in
/-- **Cotangent reduction at a nonzero value: change of connection.** For a free proper action, if
a one-form `α` pairs every fundamental vector field with `-ν` and `α' - α = ρ^* γ` for a one-form
`γ` on `Q ⧸ G`, then on the level `μ⁻¹(ν)` the magnetic reduction map of `α'` is that of `α`
followed by the fibre translation by `γ`. Such a `γ` exists for every second invariant one-form
`α'` pairing the fundamental vector fields with `-ν`
(`ProperSMul.existsUnique_mpullback_quotientMk_eq_sub`). -/
theorem magneticReductionMap_eq_vectorBundleTranslateDiffeomorph_quotientMk
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I ξ x] = -ν ξ) {z : CotangentBundle I Q}
    (hz : momentMap IG G z = ν) :
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∀ γ : SmoothForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) ℝ 1,
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G Q)) contMDiff_quotientMk γ =
        α' - α →
      magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G Q)) α' z =
        vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv γ)
          (SmoothForm.degreeOneEquiv γ).contMDiff
          (magneticReductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
            (Quotient.mk (MulAction.orbitRel G Q)) α z) := by
  let _ := orbitRelQuotientChartedSpace IG G I Q
  exact fun γ hγ ↦ CotangentBundle.magneticReductionMap_eq_vectorBundleTranslateDiffeomorph
    contMDiff_quotientMk (isSubmersion_quotientMk.hasRightInverse_mfderiv (by simp))
    ker_mfderiv_quotientMk hα hγ hz

end ProperSMul
