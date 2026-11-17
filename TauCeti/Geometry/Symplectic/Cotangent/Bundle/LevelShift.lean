/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap

/-!
# Magnetic shifts between levels of the cotangent moment map

Let a Lie group `G`, with Lie algebra `𝔤`, act smoothly on a manifold `Q`, and let
`⟨μ(q, p), ξ⟩ = p(ξ_Q(q))` be the moment map of the cotangent-lifted action on `T*Q`
(`TauCeti.CotangentBundle.momentMap`). Translating the fibres of `T*Q` by a one-form `α`,
`τ_α (q, p) = (q, p + α_q)`, changes the canonical form `ω = -dλ` to `ω - π^* dα`
(`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm`). This file
records how it moves the moment map:

`μ(τ_α (q, p)) (ξ) = μ(q, p) (ξ) + α(ξ_Q(q))`

(`TauCeti.CotangentBundle.momentMap_vectorBundleTranslateDiffeomorph_apply`).

In cotangent bundle reduction at a nonzero value `c ∈ 𝔤*`, the one-form is `α = ⟨c, A⟩` for a
principal connection `A` of the free action, which pairs every fundamental vector field with a
constant: `α(ξ_Q) = ⟨c, A(ξ_Q)⟩ = -c(ξ)` for the convention `A(ξ_Q) = -ξ` of a left action.
This file works with the real one-form `α` alone, under the hypothesis that `α(ξ_Q(q)) = c(ξ)` for
every point `q` and every `ξ`, for some `c ∈ 𝔤*`. Then:

* `τ_α` adds `c` to the moment map, `μ ∘ τ_α = μ + c`
  (`TauCeti.CotangentBundle.momentMap_vectorBundleTranslateDiffeomorph`), so it carries each level
  `μ⁻¹(ν)` onto the level `μ⁻¹(ν + c)`
  (`TauCeti.CotangentBundle.image_vectorBundleTranslateDiffeomorph_preimage_momentMap`). For the
  connection form this is the shift of `μ⁻¹(c)` onto the horizontal covectors `μ⁻¹(0)`.
* If `α` is moreover `G`-invariant, `τ_α` commutes with the cotangent-lifted action
  (`TauCeti.CotangentBundle.vectorBundleTranslateDiffeomorph_smul`). Comparing the equivariance of
  `μ` on both sides then shows that the value `c` is necessarily fixed by the coadjoint action,
  `Ad*_g c = c`, as soon as `Q` is nonempty
  (`TauCeti.CotangentBundle.coadjointRepresentation_apply_eq_self_of_forall_eval_eq`).
* The **magnetic term** `dα` of the shifted symplectic form is `G`-invariant
  (`TauCeti.CotangentBundle.mpullback_smul_mextDerivₗ_of_mpullback_smul_eq`) and horizontal:
  `dα(ξ_Q, v) = 0` for every fundamental vector field `ξ_Q` and every tangent vector `v`
  (`TauCeti.CotangentBundle.mextDerivₗ_apply_fundamentalVectorField_eq_zero`). This is Cartan's
  formula `0 = L_{ξ_Q} α = ι_{ξ_Q} dα + d(α(ξ_Q))`, in which `α(ξ_Q) = c(ξ)` is constant. An
  invariant horizontal form is basic: it is the form that descends to the quotient `Q / G` as the
  magnetic term of the reduced form. For `α = ⟨c, A⟩` with `c` coadjoint-invariant it is
  `⟨c, F_A⟩`, the `c`-component of the curvature, since `c` vanishes on brackets.
* **Change of connection.** If two one-forms `α` and `α'` pair the fundamental vector fields with
  the same `c`, their difference `β = α' - α` annihilates them, and `τ_α'` is `τ_α` followed by
  `τ_β` (`TauCeti.CotangentBundle.vectorBundleTranslateDiffeomorph_trans_sub`),
  a fibre translation by a horizontal one-form which preserves every level of `μ`
  (`TauCeti.CotangentBundle.momentMap_vectorBundleTranslateDiffeomorph_sub`).

The construction of principal connections, the descent of `dα` to `Q / G` and the identification
of the reduced space at `c` with `T*(Q / G)` carrying `ω_can + pr^* β_c` belong to the quotient
theory and are not part of this file.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §12.1 (momentum maps of cotangent lifts and their shifts by one-forms).
* Jerrold E. Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor S. Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, §2.2
  (cotangent bundle reduction: the magnetic term).
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M]

/-! ### The moment map of a translated covector -/

section Translate

variable [IsManifold I 1 M] (α : SmoothForm I M ℝ 1)

/-- **Fibre translation shifts the cotangent moment map.** Translating a covector `p` at `x` by
the value of a one-form `α` adds `α(ξ_M(x))` to its moment map: `μ(x, p + α_x)(ξ) = μ(x, p)(ξ) +
α(ξ_M(x))`. -/
theorem momentMap_vectorBundleTranslateDiffeomorph_apply (z : CotangentBundle I M)
    (ξ : GroupLieAlgebra IG G) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) ξ =
      momentMap IG G z ξ + α.1 z.proj ![fundamentalVectorField I ξ z.proj] := by
  simp [momentMap_apply]

variable {α} {c : Module.Dual ℝ (GroupLieAlgebra IG G)}

/-- If a one-form `α` pairs every fundamental vector field with the constant `c(ξ)`, translating
the fibres by `α` adds `c` to the cotangent moment map: `μ ∘ τ_α = μ + c`. -/
theorem momentMap_vectorBundleTranslateDiffeomorph
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ) (z : CotangentBundle I M) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z) = momentMap IG G z + c := by
  ext ξ
  rw [momentMap_vectorBundleTranslateDiffeomorph_apply, hα, LinearMap.add_apply]

/-- If a one-form `α` pairs every fundamental vector field with the constant `c(ξ)`, the
covectors translated by `α` into the level `μ⁻¹(ν + c)` are exactly those of the level
`μ⁻¹(ν)`. -/
theorem preimage_vectorBundleTranslateDiffeomorph_preimage_momentMap
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ)
    (ν : Module.Dual ℝ (GroupLieAlgebra IG G)) :
    vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff ⁻¹' (momentMap IG G ⁻¹' {ν + c}) =
      momentMap IG G ⁻¹' {ν} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff, momentMap_vectorBundleTranslateDiffeomorph hα,
    add_left_inj]

/-- **The magnetic shift between moment levels.** If a one-form `α` pairs every fundamental vector
field with the constant `c(ξ)`, translating the fibres by `α` carries the level `μ⁻¹(ν)` of the
cotangent moment map onto the level `μ⁻¹(ν + c)`. -/
theorem image_vectorBundleTranslateDiffeomorph_preimage_momentMap
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ)
    (ν : Module.Dual ℝ (GroupLieAlgebra IG G)) :
    vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff '' (momentMap IG G ⁻¹' {ν}) =
      momentMap IG G ⁻¹' {ν + c} := by
  rw [← preimage_vectorBundleTranslateDiffeomorph_preimage_momentMap hα ν,
    image_preimage_eq _ fun y ↦ ⟨_, Diffeomorph.apply_symm_apply _ y⟩]

/-- A one-form annihilating every fundamental vector field translates the fibres without moving
the cotangent moment map: `μ ∘ τ_β = μ`. -/
theorem momentMap_vectorBundleTranslateDiffeomorph_of_forall_eq_zero {β : SmoothForm I M ℝ 1}
    (hβ : ∀ x (ξ : GroupLieAlgebra IG G), β.1 x ![fundamentalVectorField I ξ x] = 0)
    (z : CotangentBundle I M) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv β)
        (SmoothForm.degreeOneEquiv β).contMDiff z) = momentMap IG G z := by
  rw [momentMap_vectorBundleTranslateDiffeomorph (c := 0) (fun x ξ ↦ by rw [hβ]; rfl), add_zero]

/-- **Change of connection.** If two one-forms `α` and `α'` pair every fundamental vector field
with the same constant `c(ξ)`, their difference annihilates the fundamental vector fields, so
translation by `α' - α` preserves the cotangent moment map. -/
theorem momentMap_vectorBundleTranslateDiffeomorph_sub {α' : SmoothForm I M ℝ 1}
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ)
    (hα' : ∀ x ξ, α'.1 x ![fundamentalVectorField I ξ x] = c ξ) (z : CotangentBundle I M) :
    momentMap IG G (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (α' - α))
        (SmoothForm.degreeOneEquiv (α' - α)).contMDiff z) = momentMap IG G z :=
  momentMap_vectorBundleTranslateDiffeomorph_of_forall_eq_zero
    (fun x ξ ↦ by simp [hα, hα']) z

/-- **Change of connection.** Translation by `α'` is translation by `α` followed by translation by
the difference `α' - α`. When `α` and `α'` pair the fundamental vector fields with the same
constant, this difference annihilates them
(`TauCeti.CotangentBundle.momentMap_vectorBundleTranslateDiffeomorph_sub`). -/
theorem vectorBundleTranslateDiffeomorph_trans_sub (α' : SmoothForm I M ℝ 1) :
    (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff).trans
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (α' - α))
          (SmoothForm.degreeOneEquiv (α' - α)).contMDiff) =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α')
        (SmoothForm.degreeOneEquiv α').contMDiff := by
  rw [vectorBundleTranslateDiffeomorph_trans]
  exact Diffeomorph.ext fun z ↦ by
    simp only [vectorBundleTranslateDiffeomorph_apply, map_sub, ContMDiffSection.coe_sub,
      add_sub_cancel]

end Translate

/-! ### Invariant one-forms -/

section Invariant

variable [IsManifold I 2 M] [ContMDiffConstSMul I ∞ G M] {α : SmoothForm I M ℝ 1}

omit [TopologicalSpace G] in
/-- **Translation by an invariant one-form is equivariant.** If a one-form `α` is invariant under
the action of `G`, translating the fibres by `α` commutes with the cotangent-lifted action. -/
theorem vectorBundleTranslateDiffeomorph_smul
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) α = α)
    (g : G) (z : CotangentBundle I M) :
    vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff (g • z) =
      g • vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z := by
  -- Invariance under `g⁻¹` at `g • x`: `α_{g x}(w) = α_x((dg_x)⁻¹ w)`.
  have h (w : TangentSpace I (g • z.proj)) :
      α.1 (g • z.proj) (fun _ ↦ w) =
        α.1 z.proj (fun _ ↦ mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj) w) := by
    have h := SmoothForm.mpullback_apply (fun x : M ↦ g⁻¹ • x) (contMDiff_const_smul g⁻¹) α
      (g • z.proj) (fun _ ↦ w)
    rw [hinv g⁻¹] at h
    exact h.trans (congrArg (fun A : E [⋀^Fin 1]→L[ℝ] ℝ ↦
      A (fun _ ↦ mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj) w))
      (show α.1 (g⁻¹ • g • z.proj) = α.1 z.proj by rw [inv_smul_smul]))
  rw [smul_eq_mk g z, smul_eq_mk g, vectorBundleTranslateDiffeomorph_apply,
    vectorBundleTranslateDiffeomorph_apply]
  -- Both covectors lie over `g • x`. Their values are compared by evaluating the sum and the
  -- composite pointwise: `rw` cannot see these evaluations, because the differential of
  -- `x ↦ g⁻¹ • x` lands in the tangent space at `g⁻¹ • g • x`, only definitionally that at `x`.
  refine CotangentBundle.ext rfl fun w ↦ ?_
  have h' : SmoothForm.degreeOneEquiv α (g • z.proj) w =
      SmoothForm.degreeOneEquiv α z.proj (mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj) w) :=
    (SmoothForm.degreeOneEquiv_apply_apply α _ w).trans
      ((h w).trans (SmoothForm.degreeOneEquiv_apply_apply α _ _).symm)
  exact congrArg (z.2 (mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj) w) + ·) h'

omit [TopologicalSpace G] in
/-- The **magnetic term** `dα` of an invariant one-form is invariant. -/
theorem mpullback_smul_mextDerivₗ_of_mpullback_smul_eq
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) α = α)
    (g : G) :
    SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) (mextDerivₗ I 1 α) =
      mextDerivₗ I 1 α := by
  rw [← SmoothForm.mextDerivₗ_mpullback, hinv]

end Invariant

section Coadjoint

variable [LieGroup IG ∞ G] [IsManifold I ∞ M] [ContMDiffSMul IG I ∞ G M]
  [ContMDiffConstSMul I ∞ G M] {α : SmoothForm I M ℝ 1}

/-- **The shift value is coadjoint-invariant.** If an invariant one-form `α` on a nonempty manifold
pairs every fundamental vector field with the constant `c(ξ)`, then `c` is fixed by the coadjoint
action, `Ad*_g c = c`. Equivalently, magnetic shifts by invariant one-forms only connect levels
whose difference is a coadjoint-invariant value. -/
theorem coadjointRepresentation_apply_eq_self_of_forall_eval_eq [Nonempty M]
    {c : Module.Dual ℝ (GroupLieAlgebra IG G)}
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) α = α)
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ) (g : G) :
    Lie.coadjointRepresentation ℝ IG G g c = c := by
  let z : CotangentBundle I M := zeroSection (E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (Classical.arbitrary M)
  -- Compute `μ(τ_α (g • z))` along both sides of the equivariance of `τ_α`.
  have h := congrArg (momentMap IG G) (vectorBundleTranslateDiffeomorph_smul hinv g z)
  rw [momentMap_vectorBundleTranslateDiffeomorph hα, momentMap_smul, momentMap_smul,
    momentMap_vectorBundleTranslateDiffeomorph hα, map_add, add_right_inj] at h
  exact h.symm

end Coadjoint

/-! ### The magnetic term is horizontal -/

section Horizontal

variable [CompleteSpace EG] [LieGroup IG ∞ G] [T2Space G] [BoundarylessManifold IG G]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffSMul IG I ∞ G M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The magnetic term is horizontal.** If a one-form `α` is invariant under a smooth Lie group
action and pairs every fundamental vector field with a constant, its exterior derivative vanishes
on every fundamental vector field: `dα(ξ_M, v) = 0`. By Cartan's formula,
`0 = L_{ξ_M} α = ι_{ξ_M} dα + d(α(ξ_M))`, and `α(ξ_M) = c(ξ)` is constant. -/
theorem mextDerivₗ_apply_fundamentalVectorField_eq_zero {α : SmoothForm I M ℝ 1}
    {c : Module.Dual ℝ (GroupLieAlgebra IG G)}
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) α = α)
    (hα : ∀ x ξ, α.1 x ![fundamentalVectorField I ξ x] = c ξ) (ξ : GroupLieAlgebra IG G) (x : M)
    (v : TangentSpace I x) :
    (mextDerivₗ I 1 α).1 x ![fundamentalVectorField I ξ x, v] = 0 := by
  have hX : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, fundamentalVectorField I ξ y⟩ : TangentBundle I M)) x :=
    ((contMDiff_fundamentalVectorField (m := 1) (n := ∞) (by simp) ξ).mdifferentiable
      one_ne_zero) x
  have h := mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ c ξ) (fun y ↦ hα y ξ)
    (α.mdifferentiableAt x) hX v
  rw [mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ, mvfderiv_const] at h
  rw [mextDerivₗ_apply]
  simpa [eq_comm] using h

end Horizontal

end TauCeti.CotangentBundle
