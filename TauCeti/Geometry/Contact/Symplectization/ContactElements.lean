/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ContactElements
public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Cosphere.Symplectization
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# The symplectization of the space of contact elements of the plane

The space of contact elements of the plane is `M = ℝ² × ℝP¹`, modelled as `ℝ² × AddCircle π`,
with the contact structure `ξ` of tangent vectors whose `ℝ²`-component lies on the contact
element at their base point (`TauCeti.contactElementDistribution`). This contact structure is not
coorientable, so its symplectization is not a product `ℝ × M` trivialized by a contact form: it is
the complement `ξ⁰ ∖ 0` of the zero section in the annihilator line of `ξ`
(`TauCeti.IsContactDistribution.annihilatorPunctured`), with the tautological one-form `θ`. This
file identifies it with the punctured cotangent bundle `T*ℝ² ∖ 0` of the plane, carrying `θ` to the
Liouville form `p₁ dx + p₂ dy`.

A nonzero covector `p` of `ℝ²` determines the line `ker p`, a contact element of the plane. Its
angle class `contactElementOfCovector p ∈ ℝ / πℤ` is the class of the argument of
`(p(1, 0), p(0, 1))`, so that `contactElementLine (contactElementOfCovector p) = ker p`
(`TauCeti.contactElementLine_contactElementOfCovector`). It depends smoothly on `p ≠ 0`
(`TauCeti.contMDiffAt_contactElementOfCovector`): near a covector the class is that of a local
smooth branch of the argument of either `(p(1, 0), p(0, 1))` or its negative, and the two branches
differ by `π`, which is zero in `ℝ / πℤ`.

The map `Φ` (`TauCeti.cotangentToContactElementAnnihilator`) sends a nonzero covector `p` at `q` to
the covector `(u, w) ↦ p(u)` at the contact element `(q, ker p)`. This covector vanishes on `ξ`,
since `ξ` consists of the vectors whose `ℝ²`-component lies on `ker p`; it is the pullback of `p`
along the projection `M → ℝ²`. The map `Φ` is smooth, and it pulls `θ` back to the Liouville form
`λ` of `T*ℝ²` (`TauCeti.mpullback_cotangentToContactElementAnnihilator_annihilatorLiouvilleForm`):
`θ` evaluates a covector on the projection of a tangent vector to `M`, and the projection of `Φ`
followed by the projection `M → ℝ²` is the projection of `T*ℝ²`. So `Φ` pulls `dθ` back to `dλ`,
which is nondegenerate, and its differential is injective, hence bijective between these
four-dimensional spaces. The map is injective, and its image is all of `ξ⁰ ∖ 0`
(`TauCeti.range_cotangentToContactElementAnnihilator`): a nonzero covector `z` annihilating `ξ` at
`(q, θ)` vanishes on the fibre direction, so it is the pullback of the covector `p = z(·, 0)` of
`ℝ²`, and `ker p` contains, hence is, the contact element `θ`. Therefore `Φ` is a diffeomorphism
`T*ℝ² ∖ 0 ≃ ξ⁰ ∖ 0` (`TauCeti.contactElementSymplectizationDiffeomorph`) carrying `θ` to the
Liouville form and `dθ` to `dλ = -ω`.

## Main definitions

* `TauCeti.contactElementOfCovector`: the contact element `ker p` of a covector `p` of `ℝ²`, as
  an angle class.
* `TauCeti.cotangentToContactElementAnnihilator`: the map `T*ℝ² ∖ 0 → ξ⁰`,
  `p_q ↦ (p ∘ dπ)_(q, ker p)`.
* `TauCeti.contactElementSymplectizationDiffeomorph`: the diffeomorphism `T*ℝ² ∖ 0 ≃ ξ⁰ ∖ 0`.

## Main results

* `TauCeti.contactElementLine_contactElementOfCovector`: the contact element of `p` is `ker p`.
* `TauCeti.contMDiffAt_contactElementOfCovector`: it depends smoothly on `p ≠ 0`.
* `TauCeti.contMDiff_cotangentToContactElementAnnihilator`,
  `TauCeti.cotangentToContactElementAnnihilator_injective`: `Φ` is smooth and injective.
* `TauCeti.coe_contactElementSymplectizationDiffeomorph_symm_apply`: the inverse diffeomorphism
  sends a covector `w` of `ξ⁰ ∖ 0` over `(q, θ)` to the covector `u ↦ w(u, 0)` at `q`.
* `TauCeti.mpullback_cotangentToContactElementAnnihilator_annihilatorLiouvilleForm`: `Φ^* θ = λ`.
* `TauCeti.range_cotangentToContactElementAnnihilator`: the image of `Φ` is `ξ⁰ ∖ 0`.
* `TauCeti.mpullback_contactElementSymplectizationDiffeomorph_annihilatorLiouvilleForm`,
  `TauCeti.mpullback_contactElementSymplectizationDiffeomorph_mextDerivₗ_annihilatorLiouvilleForm`:
  the diffeomorphism carries `θ` to the Liouville form of `T*ℝ²` and `dθ` to `dλ = -ω`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Springer GTM 60 (1989),
  Appendix 4 (the symplectification of the manifold of contact elements as the cotangent bundle
  with the zero section removed).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.2 (the space of contact elements).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle Real

local instance : Fact (0 < π) := ⟨pi_pos⟩

/-! ### The contact element of a covector -/

/-- The **contact element of a covector** `p` of the plane, as an angle class: the class in
`ℝ / πℤ` of the argument of `(p(1, 0), p(0, 1))`. For `p ≠ 0` it is the class of the contact
element `ker p` (`TauCeti.contactElementLine_contactElementOfCovector`), and this characterizes
it (`TauCeti.contactElementOfCovector_eq_iff`). The zero covector gets the junk value `0`. -/
def contactElementOfCovector (p : (ℝ × ℝ) →L[ℝ] ℝ) : AddCircle π :=
  (Complex.arg ⟨p (1, 0), p (0, 1)⟩ : ℝ)

/-- **The contact element of a nonzero covector is its kernel.** -/
theorem contactElementLine_contactElementOfCovector {p : (ℝ × ℝ) →L[ℝ] ℝ} (hp : p ≠ 0) :
    contactElementLine (contactElementOfCovector p) = LinearMap.ker (p : (ℝ × ℝ) →ₗ[ℝ] ℝ) := by
  set c : ℂ := ⟨p (1, 0), p (0, 1)⟩
  have hc₀ : c ≠ 0 := fun h ↦ hp <| p.eq_zero_of_apply_one_zero_of_apply_zero_one
    (congrArg Complex.re h) (congrArg Complex.im h)
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc₀
  ext ⟨a, b⟩
  rw [contactElementOfCovector, mem_contactElementLine_coe, Complex.cos_arg hc₀, Complex.sin_arg,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, p.apply_mk_eq_smul_add_smul a b, smul_eq_mul,
    smul_eq_mul]
  dsimp only
  -- `(cos τ, sin τ)` is `(p(1, 0), p(0, 1))` divided by its norm.
  have key : c.re / ‖c‖ * a + c.im / ‖c‖ * b = (a * p (1, 0) + b * p (0, 1)) / ‖c‖ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, mul_comm c.re, mul_comm c.im]
  rw [key, div_eq_zero_iff, or_iff_left hn]

/-- The contact element of a nonzero covector `p` is the angle class `θ` exactly when the contact
element `contactElementLine θ` is the kernel of `p`. -/
theorem contactElementOfCovector_eq_iff {p : (ℝ × ℝ) →L[ℝ] ℝ} (hp : p ≠ 0) {θ : AddCircle π} :
    contactElementOfCovector p = θ ↔
      contactElementLine θ = LinearMap.ker (p : (ℝ × ℝ) →ₗ[ℝ] ℝ) := by
  rw [← contactElementLine_contactElementOfCovector hp, contactElementLine_injective.eq_iff,
    eq_comm]

/-- **The contact element of a covector depends smoothly on the covector** away from zero. -/
theorem contMDiffAt_contactElementOfCovector {p : (ℝ × ℝ) →L[ℝ] ℝ} (hp : p ≠ 0)
    {n : WithTop ℕ∞} : ContMDiffAt 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ) 𝓘(ℝ) n contactElementOfCovector p := by
  -- The coordinates `(p(1, 0), p(0, 1))` of a covector, as a complex number.
  let C : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).prod
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)))
  have hC₀ : C p ≠ 0 := fun h ↦ hp <| p.eq_zero_of_apply_one_zero_of_apply_zero_one
    (congrArg Complex.re h) (congrArg Complex.im h)
  have hcoe := AddCircle.contMDiff_coe (p := π) n
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hC₀ with h | h
  · exact (hcoe _).comp p ((Complex.contDiffAt_arg h).comp p C.contDiff.contDiffAt).contMDiffAt
  · -- Off the slit plane, use the argument of `-C q`, which differs by `π`, zero in `ℝ / πℤ`.
    have h' : ContDiffAt ℝ n (fun q ↦ Complex.arg (-C q) + π) p :=
      ((Complex.contDiffAt_arg h).comp p C.contDiff.contDiffAt.neg).add contDiffAt_const
    have hper : Function.Periodic ((↑) : ℝ → AddCircle π) (2 * π) := fun x ↦ by
      rw [two_mul, ← add_assoc, AddCircle.coe_add_period, AddCircle.coe_add_period]
    refine ((hcoe _).comp p h'.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_ne.preimage C.continuous).mem_nhds hC₀] with q hq
    exact hper.apply_arg_eq_apply_arg_neg_add_pi hq

/-! ### The map from the punctured cotangent bundle of the plane -/

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ((∞ : WithTop ℕ∞) + 1)
    ((ℝ × ℝ) × AddCircle π) :=
  IsManifold.of_le (n := ∞) (by simp)

/-- The annihilator line `ξ⁰` of the contact structure of the space of contact elements, as a fibre
bundle of rank one (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`). -/
local instance instFiberBundleAnnihilatorSpaceContactElementDistribution :
    FiberBundle (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x :=
  (isContactDistribution_contactElementDistribution (n := ∞)).isContMDiffDistribution
    |>.annihilatorFiberBundle
      (isContactDistribution_contactElementDistribution (n := ∞)).finrank_sub_one_add_one

/-- The annihilator line `ξ⁰` of the contact structure of the space of contact elements is a
vector bundle (`TauCeti.IsContMDiffDistribution.annihilatorVectorBundle`). -/
local instance instVectorBundleAnnihilatorSpaceContactElementDistribution :
    VectorBundle ℝ (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x :=
  (isContactDistribution_contactElementDistribution (n := ∞)).isContMDiffDistribution
    |>.annihilatorVectorBundle
      (isContactDistribution_contactElementDistribution (n := ∞)).finrank_sub_one_add_one

/-- The annihilator line `ξ⁰` of the contact structure of the space of contact elements is a smooth
vector bundle (`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle`). -/
local instance instContMDiffVectorBundleAnnihilatorSpaceContactElementDistribution :
    ContMDiffVectorBundle ∞ (Fin 1 → ℝ) (fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x)
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) :=
  (isContactDistribution_contactElementDistribution (n := ∞)).isContMDiffDistribution
    |>.annihilatorContMDiffVectorBundle
      (isContactDistribution_contactElementDistribution (n := ∞)).finrank_sub_one_add_one

variable (z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))

/-- The covector `(u, w) ↦ p(u)` at the contact element `(q, ker p)` annihilates the contact
structure, for a nonzero covector `p` at `q`. -/
private theorem comp_fst_mem_annihilatorSpace :
    (z.val.snd ∘L ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ :
        TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ))
          ((z.val.proj, contactElementOfCovector z.val.snd) : (ℝ × ℝ) × AddCircle π) →L[ℝ] ℝ) ∈
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution
        (z.val.proj, contactElementOfCovector z.val.snd) := by
  rw [mem_annihilatorSpace_iff]
  intro v hv
  rw [mem_contactElementDistribution,
    contactElementLine_contactElementOfCovector (mem_punctured.1 z.property),
    LinearMap.mem_ker] at hv
  -- The covector `p ∘ fst` evaluates `v` to `p(v₁)`.
  exact (ContinuousLinearMap.comp_apply _ _ v).trans hv

/-- The map `T*ℝ² ∖ 0 → ξ⁰` from the punctured cotangent bundle of the plane to the annihilator line
of the contact structure of its space of contact elements: a nonzero covector `p` at `q` goes to
the covector `(u, w) ↦ p(u)` at the contact element `(q, ker p)`, the pullback of `p` along the
projection to `ℝ²`. It is a diffeomorphism onto the symplectization `ξ⁰ ∖ 0`
(`TauCeti.contactElementSymplectizationDiffeomorph`). -/
def cotangentToContactElementAnnihilator :
    TotalSpace (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x :=
  TotalSpace.mk' (Fin 1 → ℝ) (z.val.proj, contactElementOfCovector z.val.snd)
    ⟨_, comp_fst_mem_annihilatorSpace z⟩

/-- The image of a nonzero covector `p` at `q` lies over the contact element `(q, ker p)`. -/
@[simp]
theorem proj_cotangentToContactElementAnnihilator :
    (cotangentToContactElementAnnihilator z).proj =
      (z.val.proj, contactElementOfCovector z.val.snd) :=
  (rfl)

/-- The image of a nonzero covector `p` evaluates a tangent vector `(u, w)` to `p(u)`. -/
@[simp]
theorem cotangentToContactElementAnnihilator_snd_apply
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) (cotangentToContactElementAnnihilator z).proj) :
    ((cotangentToContactElementAnnihilator z).snd :
        TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) (cotangentToContactElementAnnihilator z).proj →L[ℝ] ℝ)
        v = z.val.snd v.1 :=
  (rfl)

/-- The base point `(q, ker p)` of the image of a nonzero covector `p` at `q` depends smoothly on
the covector. -/
private theorem contMDiff_proj_cotangentToContactElementAnnihilator :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ)) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) ∞
      fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦ (z.val.proj, contactElementOfCovector z.val.snd) := by
  intro z
  have hval : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ)) ∞
      (Subtype.val : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) → CotangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) :=
    contMDiff_subtypeVal
  -- The fibre coordinate of `T*ℝ² = ℝ² × (ℝ²)*` is smooth.
  have hsnd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ)) 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ) ∞
      fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦ (modelSpaceDiffeomorph (ℝ × ℝ) z.val).2 :=
    (contDiff_snd.contMDiff.comp (modelSpaceDiffeomorph (ℝ × ℝ)).contMDiff).comp hval
  simp only [modelSpaceDiffeomorph_apply] at hsnd
  have hθ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦ contactElementOfCovector z.val.snd) z :=
    ContMDiffAt.comp (g := contactElementOfCovector)
      (f := fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦ (z.val.snd : (ℝ × ℝ) →L[ℝ] ℝ)) z
      (contMDiffAt_contactElementOfCovector (mem_punctured.1 z.property)) (hsnd z)
  exact (((contMDiff_proj _).comp hval) z).prodMk hθ

/-- Followed by the inclusion `ξ⁰ → T*M`, the map is the pullback of covectors along the projection
`M → ℝ²`. -/
private theorem annihilatorInclusion_cotangentToContactElementAnnihilator :
    annihilatorInclusion (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution (Fin 1 → ℝ)
        (cotangentToContactElementAnnihilator z) =
      TotalSpace.mk' ((ℝ × ℝ) × ℝ →L[ℝ] ℝ) (z.val.proj, contactElementOfCovector z.val.snd)
        (z.val.snd ∘L mfderiv (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) Prod.fst
          (z.val.proj, contactElementOfCovector z.val.snd)) := by
  rw [cotangentToContactElementAnnihilator, annihilatorInclusion_mk', mfderiv_fst]
  -- Both covectors are `p ∘ fst`; they differ only in how the tangent space is written.
  rfl

/-- **The map is smooth.** -/
theorem contMDiff_cotangentToContactElementAnnihilator :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      ((𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ cotangentToContactElementAnnihilator :=
  fun z ↦ by
  have hξ := isContactDistribution_contactElementDistribution (n := ∞)
  -- The inclusion `ξ⁰ → T*M` is a smooth embedding, and its composite with the map is smooth.
  have hj := hξ.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
    hξ.finrank_sub_one_add_one
  have hκ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      ((𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, (ℝ × ℝ) × ℝ →L[ℝ] ℝ)) ∞
      (annihilatorInclusion (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution (Fin 1 → ℝ) ∘
        cotangentToContactElementAnnihilator) := by
    have h := contMDiff_mk_comp_mfderiv (f := Prod.fst) (Ψ := Subtype.val)
      (g := fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦
        (z.val.proj, contactElementOfCovector z.val.snd)) (fun _ ↦ rfl) contMDiff_subtypeVal
      contMDiff_proj_cotangentToContactElementAnnihilator contMDiff_fst (m := ∞) (n := ∞) (by simp)
    exact h.congr fun z ↦ annihilatorInclusion_cotangentToContactElementAnnihilator z
  rw [ContMDiffAt.iff_comp_isImmersionAt (hj.isImmersion.isImmersionAt _),
    hj.isEmbedding.isInducing.continuousAt_iff]
  exact ⟨hκ.continuous.continuousAt, hκ z⟩

/-- **The map is tautological.** It pulls the tautological one-form `θ` of the annihilator line
back to the Liouville form `λ` of the plane, `p₁ dx + p₂ dy`, restricted to `T*ℝ² ∖ 0`. -/
theorem mpullback_cotangentToContactElementAnnihilator_annihilatorLiouvilleForm :
    SmoothForm.mpullback cotangentToContactElementAnnihilator
        contMDiff_cotangentToContactElementAnnihilator
        (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorLiouvilleForm =
      SmoothForm.mpullback (Subtype.val : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) → _) contMDiff_subtypeVal
        (liouvilleForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) := by
  have hξ := isContactDistribution_contactElementDistribution (n := ∞)
  have hΦ := contMDiff_cotangentToContactElementAnnihilator
  have hg := contMDiff_proj_cotangentToContactElementAnnihilator
  apply Subtype.ext
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  have hval : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      (Subtype.val : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) → CotangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) z :=
    (contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero
  -- The projection of `ξ⁰` after the map is the base point map `p_q ↦ (q, ker p)`.
  have hproj := mfderiv_comp_apply z
    ((contMDiff_proj (n := 1) (fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x)
        (cotangentToContactElementAnnihilator z)).mdifferentiableAt one_ne_zero)
    ((hΦ z).mdifferentiableAt (by simp)) (v 0)
  -- Its first component is the derivative of the base point `q` of the covector.
  have hfst := mfderiv_comp_apply z mdifferentiableAt_fst ((hg z).mdifferentiableAt (by simp))
    (v 0)
  rw [mfderiv_fst] at hfst
  rw [hv, SmoothForm.mpullback_apply_one, hξ.annihilatorLiouvilleForm_apply, ← hproj,
    SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq
      (g := fun z : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ↦ z.val.proj) (fun _ ↦ rfl) hval,
    Matrix.cons_val_zero]
  exact (cotangentToContactElementAnnihilator_snd_apply z _).trans (congrArg z.val.snd hfst.symm)

/-- **The map is injective**: the image of a nonzero covector `p` at `q` determines `q` as its base
point and `p` by its values on the vectors `(u, 0)`. -/
theorem cotangentToContactElementAnnihilator_injective :
    Injective cotangentToContactElementAnnihilator := by
  intro z z' h
  refine Subtype.ext (CotangentBundle.ext (congrArg (fun w ↦ w.proj.1) h) fun u ↦ ?_)
  have hu := congrArg (fun w : TotalSpace (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
      annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x ↦
    (w.snd : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) w.proj →L[ℝ] ℝ) ((u, 0) : (ℝ × ℝ) × ℝ)) h
  -- The image of `p` takes the value `p(u)` on `(u, 0)`.
  exact (cotangentToContactElementAnnihilator_snd_apply z (u, 0)).symm.trans
    (hu.trans (cotangentToContactElementAnnihilator_snd_apply z' (u, 0)))

/-- **The image of the map is the symplectization.** The nonzero covectors annihilating the
contact structure of the space of contact elements are exactly the images of the nonzero
covectors of the plane. -/
theorem range_cotangentToContactElementAnnihilator :
    range cotangentToContactElementAnnihilator =
      ((isContactDistribution_contactElementDistribution (n := ∞)).annihilatorPunctured :
        Set (TotalSpace (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
          annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x)) := by
  ext w
  rw [SetLike.mem_coe, IsContactDistribution.mem_annihilatorPunctured]
  constructor
  · rintro ⟨z, rfl⟩ h₀
    refine mem_punctured.1 z.property (ContinuousLinearMap.ext fun u ↦ ?_)
    -- The image of `p` takes the value `p(u)` on `(u, 0)`.
    have hu : ((cotangentToContactElementAnnihilator z).snd :
        TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) (cotangentToContactElementAnnihilator z).proj →L[ℝ] ℝ)
          ((u, 0) : (ℝ × ℝ) × ℝ) = 0 := by
      rw [h₀, ZeroMemClass.coe_zero]
      exact zero_apply _
    exact (cotangentToContactElementAnnihilator_snd_apply z (u, 0)).symm.trans
      (hu.trans (zero_apply _).symm)
  · intro hw
    -- The covector `w` at `x`, read on `ℝ² × ℝ`, is the pullback of `P = w(·, 0)` on `ℝ²`.
    let W : (ℝ × ℝ) × ℝ →L[ℝ] ℝ :=
      (w.snd : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) w.proj →L[ℝ] ℝ)
    let P : (ℝ × ℝ) →L[ℝ] ℝ := W ∘L ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ
    have hann (v : (ℝ × ℝ) × ℝ) (hv : v.1 ∈ contactElementLine w.proj.2) : W v = 0 :=
      mem_annihilatorSpace_iff.1 w.snd.property v (mem_contactElementDistribution.2 hv)
    have hW (v : (ℝ × ℝ) × ℝ) : W v = P v.1 := by
      -- The vertical vector `(0, v₂)` lies in the contact structure.
      have hvert : W.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) v.2 = 0 :=
        hann (0, v.2) (Submodule.zero_mem _)
      rw [← W.comp_inl_add_comp_inr v, hvert, add_zero]
    have hP : P ≠ 0 := fun hP₀ ↦ hw <| Subtype.ext
      (ContinuousLinearMap.ext fun v ↦ by rw [hW v, hP₀, zero_apply, zero_apply] : W = 0)
    have hline : contactElementLine w.proj.2 = LinearMap.ker (P : (ℝ × ℝ) →ₗ[ℝ] ℝ) :=
      contactElementLine_eq_ker_of_le hP fun u hu ↦ by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        exact hann (u, 0) hu
    refine ⟨⟨TotalSpace.mk' ((ℝ × ℝ) →L[ℝ] ℝ) w.proj.1 P, mem_punctured.2 hP⟩, ?_⟩
    refine totalSpace_annihilatorSpace_ext ?_ fun v ↦ ?_
    · exact Prod.ext rfl ((contactElementOfCovector_eq_iff hP).2 hline)
    · -- The image of `P` takes the value `P(v₁)` on `v`.
      rw [cotangentToContactElementAnnihilator_snd_apply]
      exact (hW v).symm

/-- The differential of the map is injective: the map pulls `dθ` back to `dλ`, which is minus the
nondegenerate canonical symplectic form of `T*ℝ²`. -/
private theorem injective_mfderiv_cotangentToContactElementAnnihilator :
    Injective (mfderiv (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      ((𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, Fin 1 → ℝ)) cotangentToContactElementAnnihilator z) := by
  have hd := congrArg (mextDerivₗ _ 1)
    mpullback_cotangentToContactElementAnnihilator_annihilatorLiouvilleForm
  rw [SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback] at hd
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦
    (strongDualCotangentSymplecticForm (V := ℝ × ℝ)).nondegenerate.1 v
      fun (w : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ)) z) ↦ ?_
  -- Evaluate `Φ^* dθ = dλ` on `(v, w)`: the left side vanishes because `dΦ v = 0`.
  have h₁ := SmoothForm.eval₂_mpullback _ contMDiff_cotangentToContactElementAnnihilator
    (mextDerivₗ _ 1 (isContactDistribution_contactElementDistribution
      (n := ∞)).annihilatorLiouvilleForm) z v w
  rw [hv, SmoothBundleForm.eval₂_zero_left, hd, SmoothBundleForm.eval₂_apply,
    SmoothForm.coe_mpullback, mpullback_subtype_val_apply] at h₁
  -- The right side is `-ω(v, w)`.
  have hω := symplecticForm_apply (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) z.val ![v, w]
  rw [symplecticForm_eq_neg_mextDeriv, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    ← mextDerivₗ_apply] at hω
  -- `v` and `w` are tangent vectors at `z` of `T*ℝ² ∖ 0`, hence at `z` of `T*ℝ²`.
  have h₂ := (congrArg Neg.neg h₁).symm.trans hω
  rw [neg_zero] at h₂
  exact h₂.symm

/-- The map, with values in the symplectization `ξ⁰ ∖ 0`. -/
private def toAnnihilatorPunctured :
    (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorPunctured :=
  ⟨cotangentToContactElementAnnihilator z, by
    rw [← SetLike.mem_coe, ← range_cotangentToContactElementAnnihilator]
    exact mem_range_self z⟩

/-- The map into `ξ⁰ ∖ 0` is the map into `ξ⁰`, with its codomain restricted. -/
private theorem coe_toAnnihilatorPunctured :
    (toAnnihilatorPunctured z : TotalSpace (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
        annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x) =
      cotangentToContactElementAnnihilator z :=
  rfl

/-- The map into `ξ⁰ ∖ 0` is a local diffeomorphism, by the inverse function theorem. -/
private theorem isLocalDiffeomorph_toAnnihilatorPunctured :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      ((𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ toAnnihilatorPunctured := fun z ↦ by
  have hcont : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ))
      ((𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ toAnnihilatorPunctured :=
    (ContMDiff.subtypeVal_comp_iff _ _).1 contMDiff_cotangentToContactElementAnnihilator
  -- The differential of the map into `ξ⁰` factors through that of the map into `ξ⁰ ∖ 0`.
  have hinj := injective_mfderiv_cotangentToContactElementAnnihilator z
  have hcomp : cotangentToContactElementAnnihilator = Subtype.val ∘ toAnnihilatorPunctured :=
    funext fun y ↦ (coe_toAnnihilatorPunctured y).symm
  rw [hcomp, mfderiv_comp z ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)
      ((hcont z).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp] at hinj
  refine isLocalDiffeomorphAt_of_injective_mfderiv hcont.contMDiffOn isOpen_univ (mem_univ z)
    BoundarylessManifold.isInteriorPoint (by simp) hinj.of_comp ?_
  rw [finrank_prod, ← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ℝ × ℝ) (F' := ℝ)).finrank_eq]
  simp [finrank_prod]

/-- The map into `ξ⁰ ∖ 0` is bijective. -/
private theorem bijective_toAnnihilatorPunctured :
    Bijective toAnnihilatorPunctured :=
  ⟨fun _ _ h ↦ cotangentToContactElementAnnihilator_injective (congrArg Subtype.val h), fun w ↦ by
    obtain ⟨z, hz⟩ :
        (w : TotalSpace (Fin 1 → ℝ) _) ∈ range cotangentToContactElementAnnihilator := by
      rw [range_cotangentToContactElementAnnihilator]
      exact w.property
    exact ⟨z, Subtype.ext hz⟩⟩

/-- **The symplectization of the space of contact elements of the plane is the punctured cotangent
bundle of the plane.** The map sending a nonzero covector `p` at `q` to the covector
`(u, w) ↦ p(u)` at the contact element `(q, ker p)` is a diffeomorphism from `T*ℝ² ∖ 0` onto the
complement `ξ⁰ ∖ 0` of the zero section in the annihilator line of the contact structure. It
carries the tautological one-form `θ` to the Liouville form of `T*ℝ²`
(`TauCeti.mpullback_contactElementSymplectizationDiffeomorph_annihilatorLiouvilleForm`). -/
def contactElementSymplectizationDiffeomorph :
    punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] ℝ),
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)).prod 𝓘(ℝ, Fin 1 → ℝ)⟯
      (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorPunctured :=
  isLocalDiffeomorph_toAnnihilatorPunctured.diffeomorphOfBijective
    bijective_toAnnihilatorPunctured

/-- The diffeomorphism sends a nonzero covector `p` at `q` to the covector `(u, w) ↦ p(u)` at the
contact element `(q, ker p)`. -/
@[simp]
theorem coe_contactElementSymplectizationDiffeomorph_apply :
    (contactElementSymplectizationDiffeomorph z :
        TotalSpace (Fin 1 → ℝ) fun x : (ℝ × ℝ) × AddCircle π ↦
          annihilatorSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) contactElementDistribution x) =
      cotangentToContactElementAnnihilator z := by
  rw [contactElementSymplectizationDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective,
    coe_toAnnihilatorPunctured]

/-- The inverse of the diffeomorphism sends a nonzero covector `w` of `ξ⁰` over `(q, θ)` to the
covector `u ↦ w(u, 0)` at `q`. -/
@[simp]
theorem coe_contactElementSymplectizationDiffeomorph_symm_apply
    (w : (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorPunctured) :
    (contactElementSymplectizationDiffeomorph.symm w : CotangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) =
      TotalSpace.mk' ((ℝ × ℝ) →L[ℝ] ℝ) w.val.proj.1
        ((w.val.snd : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ)) w.val.proj →L[ℝ] ℝ) ∘L
          ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ) := by
  obtain ⟨z, rfl⟩ : ∃ z, contactElementSymplectizationDiffeomorph z = w :=
    contactElementSymplectizationDiffeomorph.surjective w
  rw [Diffeomorph.symm_apply_apply, coe_contactElementSymplectizationDiffeomorph_apply]
  refine CotangentBundle.ext rfl fun u ↦ ?_
  -- The image of `p` takes the value `p(u)` on `(u, 0)`.
  exact (cotangentToContactElementAnnihilator_snd_apply z (u, 0)).symm

/-- **The symplectization of the space of contact elements carries the Liouville form.** The
diffeomorphism `T*ℝ² ∖ 0 ≃ ξ⁰ ∖ 0` pulls the tautological one-form `θ`, restricted to `ξ⁰ ∖ 0`,
back to the Liouville form `p₁ dx + p₂ dy` of `T*ℝ²`, restricted to `T*ℝ² ∖ 0`. -/
theorem mpullback_contactElementSymplectizationDiffeomorph_annihilatorLiouvilleForm :
    SmoothForm.mpullback contactElementSymplectizationDiffeomorph
        contactElementSymplectizationDiffeomorph.contMDiff
        (SmoothForm.mpullback (Subtype.val : (isContactDistribution_contactElementDistribution
          (n := ∞)).annihilatorPunctured → _) contMDiff_subtypeVal
          (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorLiouvilleForm) =
      SmoothForm.mpullback (Subtype.val : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) → _) contMDiff_subtypeVal
        (liouvilleForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) := by
  rw [SmoothForm.mpullback_mpullback,
    ← mpullback_cotangentToContactElementAnnihilator_annihilatorLiouvilleForm]
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  exact congrArg (fun f ↦ TauCeti.mpullback _ _ f _)
    (funext coe_contactElementSymplectizationDiffeomorph_apply)

/-- **The diffeomorphism is symplectic for `dλ = -ω`.** The diffeomorphism `T*ℝ² ∖ 0 ≃ ξ⁰ ∖ 0`
pulls the symplectic form `dθ` of the symplectization back to the exterior derivative `dλ = -ω` of
the Liouville form of `T*ℝ²`, where `ω` is the canonical symplectic form: it is a symplectomorphism
from `(T*ℝ² ∖ 0, -ω)` to `(ξ⁰ ∖ 0, dθ)`. -/
theorem mpullback_contactElementSymplectizationDiffeomorph_mextDerivₗ_annihilatorLiouvilleForm :
    SmoothForm.mpullback contactElementSymplectizationDiffeomorph
        contactElementSymplectizationDiffeomorph.contMDiff
        (SmoothForm.mpullback (Subtype.val : (isContactDistribution_contactElementDistribution
          (n := ∞)).annihilatorPunctured → _) contMDiff_subtypeVal
          (mextDerivₗ _ 1
            (isContactDistribution_contactElementDistribution (n := ∞)).annihilatorLiouvilleForm)) =
      -SmoothForm.mpullback (Subtype.val : punctured 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) → _) contMDiff_subtypeVal
        (symplecticForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) := by
  rw [← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_contactElementSymplectizationDiffeomorph_annihilatorLiouvilleForm,
    SmoothForm.mextDerivₗ_mpullback, symplecticForm_eq_neg_mextDerivₗ, map_neg, neg_neg]

end TauCeti
