/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic

/-!
# The `(p,q)` type of paired wedges of complex-valued alternating forms

Let `J` be a continuous real-linear endomorphism of a real topological vector space `V`. The
derivation `J.alternatingDerivation` that `J` induces on alternating maps on `V` is a derivation
of the paired wedge for every continuous real-bilinear pairing `μ` of the coefficients:
`D_J (φ ∧ ψ) = D_J φ ∧ ψ + φ ∧ D_J ψ`. It has no sign, since `D_J` has degree `0`.

When `μ` is complex-bilinear, the paired wedge is complex-bilinear, so the eigenvalues of `D_J`
add. Since the type `(p,q)` of a form is defined by the eigenvalue `(p - q) * I` of `D_J`, the
paired wedge of forms of types `(p,q)` and `(p',q')` has type `(p + p', q + q')`. For `J² = -1`
it follows that the type-`(P,Q)` component of a paired wedge is the sum of the paired wedges of
the type components of the factors whose types add up to `(P,Q)`.

## Main declarations

* `ContinuousLinearMap.alternatingDerivation_pairedWedge`: the Leibniz rule for the derivation
  induced by `J`.
* `ContinuousAlternatingMap.IsOfType.pairedWedge`: types add under paired wedges with
  complex-bilinear pairings.
* `ContinuousLinearMap.typeProjection_pairedWedge`: the type components of a paired wedge.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

noncomputable section

open Complex Function

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {F₁ F₂ F₃ : Type*}
  [AddCommGroup F₁] [Module ℂ F₁] [Module ℝ F₁] [IsScalarTower ℝ ℂ F₁]
  [TopologicalSpace F₁] [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℂ F₁]
  [AddCommGroup F₂] [Module ℂ F₂] [Module ℝ F₂] [IsScalarTower ℝ ℂ F₂]
  [TopologicalSpace F₂] [IsTopologicalAddGroup F₂] [ContinuousConstSMul ℂ F₂]
  [AddCommGroup F₃] [Module ℂ F₃] [Module ℝ F₃] [IsScalarTower ℝ ℂ F₃]
  [TopologicalSpace F₃] [IsTopologicalAddGroup F₃] [ContinuousConstSMul ℂ F₃]
  [ContinuousConstSMul ℝ F₃]
  {k l : ℕ}

namespace ContinuousLinearMap

omit [Module ℂ F₃] [IsScalarTower ℝ ℂ F₃] [ContinuousConstSMul ℂ F₃] in
/-- Applying `J` to one argument at a time of the concatenation of the arguments of `φ` and `ψ`
and summing gives the pairing of `D_J φ` with `ψ` plus the pairing of `φ` with `D_J ψ`. -/
private lemma sum_pairing_update (J : V →L[ℝ] V) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : V [⋀^Fin k]→L[ℝ] F₁) (ψ : V [⋀^Fin l]→L[ℝ] F₂) (w : Fin (k + l) → V) :
    ∑ j, μ (φ fun a ↦ update w j (J (w j)) (Fin.castAdd l a))
        (ψ fun b ↦ update w j (J (w j)) (Fin.natAdd k b)) =
      μ (J.alternatingDerivation φ fun a ↦ w (Fin.castAdd l a)) (ψ fun b ↦ w (Fin.natAdd k b)) +
        μ (φ fun a ↦ w (Fin.castAdd l a))
          (J.alternatingDerivation ψ fun b ↦ w (Fin.natAdd k b)) := by
  rw [Fin.sum_univ_add, alternatingDerivation_apply, alternatingDerivation_apply, map_sum,
    _root_.sum_apply, map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
  · rw [update_comp_eq_of_injective' w (Fin.castAdd_injective k l),
      update_comp_eq_of_forall_ne' w _ fun b h ↦ by simp [Fin.ext_iff] at h; omega]
  · rw [update_comp_eq_of_injective' w (Fin.natAdd_injective l k),
      update_comp_eq_of_forall_ne' w _ fun a h ↦ by simp [Fin.ext_iff] at h; omega]

/-- The derivation induced by an endomorphism `J` is a derivation of the paired wedge:
`D_J (φ ∧ ψ) = D_J φ ∧ ψ + φ ∧ D_J ψ`. -/
theorem alternatingDerivation_pairedWedge (J : V →L[ℝ] V) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (uncurry fun x y ↦ μ x y)) (φ : V [⋀^Fin k]→L[ℝ] F₁)
    (ψ : V [⋀^Fin l]→L[ℝ] F₂) :
    J.alternatingDerivation (ContinuousAlternatingMap.pairedWedge μ hμ φ ψ) =
      ContinuousAlternatingMap.pairedWedge μ hμ (J.alternatingDerivation φ) ψ +
        ContinuousAlternatingMap.pairedWedge μ hμ φ (J.alternatingDerivation ψ) := by
  ext v
  rw [alternatingDerivation_apply, ContinuousAlternatingMap.add_apply]
  simp only [ContinuousAlternatingMap.pairedWedge_apply, ← smul_add, ← Finset.sum_add_distrib]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ ?_)
  rw [← Finset.smul_sum, ← sum_pairing_update J μ φ ψ fun m ↦ v (σ m), ← Equiv.sum_comp σ]
  simp only [update_apply, EmbeddingLike.apply_eq_iff_eq]

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable {μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃} {hμ : Continuous (uncurry fun x y ↦ μ x y)} {J : V →L[ℝ] V}
  {φ : V [⋀^Fin k]→L[ℝ] F₁} {ψ : V [⋀^Fin l]→L[ℝ] F₂}
  {p q p' q' : ℕ}

/-- For a complex-bilinear pairing, the paired wedge of forms of types `(p,q)` and `(p',q')` has
type `(p + p', q + q')`. -/
theorem IsOfType.pairedWedge (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
    (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b) (hφ : φ.IsOfType J p q)
    (hψ : ψ.IsOfType J p' q') : (pairedWedge μ hμ φ ψ).IsOfType J (p + p') (q + q') :=
  isOfType_iff.2 ⟨by rw [← hφ.add_eq, ← hψ.add_eq]; ring, by
    rw [ContinuousLinearMap.alternatingDerivation_pairedWedge, hφ.alternatingDerivation_eq,
      hψ.alternatingDerivation_eq,
      pairedWedge_smul_left_of_map_smul μ hμ (hμ₁ _), pairedWedge_smul_right_of_map_smul μ hμ
        (hμ₂ _), ← add_smul]
    congr 1
    push_cast
    ring⟩

end ContinuousAlternatingMap

namespace ContinuousLinearMap

variable [ContinuousConstSMul ℝ F₁] [ContinuousConstSMul ℝ F₂] {μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃}
  {hμ : Continuous (uncurry fun x y ↦ μ x y)} {J : V →L[ℝ] V}

/-- For `J² = -1` and a complex-bilinear pairing, the type-`(P,Q)` component of a paired wedge
is the sum of the paired wedges of the type-`(p,q)` component of the first factor with the
type-`(p',q')` component of the second, over the types with `(p + p', q + q') = (P,Q)`. -/
theorem typeProjection_pairedWedge (hJ : ∀ v, J (J v) = -v)
    (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b) (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b)
    (φ : V [⋀^Fin k]→L[ℝ] F₁) (ψ : V [⋀^Fin l]→L[ℝ] F₂) (P Q : ℕ) :
    J.typeProjection P Q (ContinuousAlternatingMap.pairedWedge μ hμ φ ψ) =
      ∑ x ∈ Finset.antidiagonal k ×ˢ Finset.antidiagonal l with x.1 + x.2 = (P, Q),
        ContinuousAlternatingMap.pairedWedge μ hμ (J.typeProjection x.1.1 x.1.2 φ)
          (J.typeProjection x.2.1 x.2.2 ψ) := by
  set S := Finset.antidiagonal k ×ˢ Finset.antidiagonal l
  set f : (ℕ × ℕ) × (ℕ × ℕ) → V [⋀^Fin (k + l)]→L[ℝ] F₃ := fun x ↦
    ContinuousAlternatingMap.pairedWedge μ hμ (J.typeProjection x.1.1 x.1.2 φ)
      (J.typeProjection x.2.1 x.2.2 ψ)
  have hS : ∀ x ∈ S, x.1 + x.2 ∈ Finset.antidiagonal (k + l) := fun x hx ↦ by
    simp only [S, Finset.mem_product, Finset.mem_antidiagonal] at hx ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hPQ : P + Q = k + l
  · refine typeProjection_eq_of_sum_eq (η := fun c ↦ ∑ x ∈ S with x.1 + x.2 = c, f x)
      (fun c hc ↦ ?_) ?_ hPQ
    · refine Finset.sum_induction _ (fun ω : V [⋀^Fin (k + l)]→L[ℝ] F₃ ↦ ω.IsOfType J c.1 c.2)
        (fun _ _ ↦ ContinuousAlternatingMap.IsOfType.add)
        (by simpa using hc) fun x hx ↦ ?_
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_antidiagonal] at hx
      obtain ⟨⟨h₁, h₂⟩, rfl⟩ := hx
      exact (isOfType_typeProjection hJ h₁ φ).pairedWedge hμ₁ hμ₂
        (isOfType_typeProjection hJ h₂ ψ)
    · rw [Finset.sum_fiberwise_of_maps_to hS, Finset.sum_product]
      conv_rhs => rw [← sum_typeProjection J φ, ← sum_typeProjection J ψ]
      simp only [f, ContinuousAlternatingMap.pairedWedge_sum_left,
        ContinuousAlternatingMap.pairedWedge_sum_right]
      exact Finset.sum_comm
  · rw [typeProjection_eq_zero hJ hPQ, LinearMap.zero_apply, eq_comm]
    refine Finset.sum_eq_zero fun x hx ↦ absurd ?_ hPQ
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_antidiagonal] at hx
    obtain ⟨⟨h₁, h₂⟩, h⟩ := hx
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h
    omega

end ContinuousLinearMap
