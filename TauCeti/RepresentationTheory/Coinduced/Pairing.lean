/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.ClassSum
public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.InvariantForm.Hermitian
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# The class-integral pairing of smooth coinduced functions

Let `φ : H →* G` be a homomorphism into a topological group, `σ` a representation of `H` on a
module `W` over a commutative star ring `R` that is a `ℚ`-vector space, and `B` a sesquilinear form
on `W` invariant under `σ`. For `f, f'` in the representation `coind φ σ` coinduced along `φ`
(the functions with `f (φ h * g) = σ h (f g)`), the function `g ↦ B (f g) (f' g)` on `G` is left
invariant under `Γ = φ(H)`; when `f` and `f'` are smooth (have open stabilizers) it is right
invariant under an open subgroup. For a compact open subgroup `K` of `G` with `(Γ, K)` of finite
type (`TauCeti.HasFiniteType`), its class integral `I_{Γ,K}` (`TauCeti.classIntegral`) is
therefore defined, and

  `⟨f, f'⟩_B = I_{Γ,K}(g ↦ B (f g) (f' g))`

is a sesquilinear form on the smooth vectors of `coind φ σ`, invariant under right translation by
`G`, and hermitian when `B` is. As for every class integral, it stands for the integral of
`B (f g) (f' g)` over `Γ \ G` for the Haar measure giving `K` mass one.

For `G` the finite adelic points of a unitary group compact at infinity, `Γ` its rational points
and `σ` a representation of the rational points through their archimedean components, the smooth
coinduced functions are the algebraic modular forms and this is Gross's invariant pairing of
algebraic modular forms.

## Main definitions

* `Representation.coindPairing hK B hB`: the pairing `⟨f, f'⟩_B` on the smooth vectors of
  `coind φ σ`, for `hK : TauCeti.HasFiniteType φ.range K` and `hB` the `σ`-invariance of `B`.

## Main results

* `Representation.coindPairing_apply`: `⟨f, f'⟩_B = I_{Γ,K}(g ↦ B (f g) (f' g))`.
* `Representation.isInvariantSesqForm_coindPairing`: the pairing is invariant under right
  translation by `G`.
* `Representation.isSymm_coindPairing`: the pairing is hermitian when `B` is.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.

## Attribution

The pairing follows `New.smoothPairing`, `New.smoothPairing_apply`,
`New.pairing_mem_smoothInvariants` and `New.smoothPairing_formTranslation` in
`src/Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), there stated for
algebraic modular forms on a definite unitary group; here it is stated for smooth vectors of any
coinduced representation.
-/

public section

namespace Representation

open TauCeti

section Pointwise

variable {R H G W : Type*} [CommSemiring R] [StarRing R] [Group H] [Group G]
  [AddCommMonoid W] [Module R W] {φ : H →* G} {σ : Representation R H W}
  {B : W →ₗ⋆[R] W →ₗ[R] R}

/-- For a `σ`-invariant sesquilinear form `B` and coinduced functions `f, f'`, the function
`g ↦ B (f g) (f' g)` is left invariant under the image `φ(H)`. -/
theorem IsInvariantSesqForm.apply_coindV_mul (hB : IsInvariantSesqForm σ B) (f f' : coindV φ σ)
    {γ : G} (hγ : γ ∈ φ.range) (g : G) :
    B (f.val (γ * g)) (f'.val (γ * g)) = B (f.val g) (f'.val g) := by
  obtain ⟨h, rfl⟩ := hγ
  rw [f.property h g, f'.property h g, hB.apply]

/-- For smooth coinduced functions `f, f'`, the function `g ↦ B (f g) (f' g)` has an open
right-translation stabilizer. -/
theorem isOpen_rightTranslationStabilizer_apply_coindV [TopologicalSpace G]
    [SeparatelyContinuousMul G] {f f' : coindV φ σ}
    (hf : f ∈ (coind φ σ).smoothVectors) (hf' : f' ∈ (coind φ σ).smoothVectors) :
    IsOpen (rightTranslationStabilizer (fun g ↦ B (f.val g) (f'.val g)) : Set G) := by
  rw [mem_smoothVectors_iff, stabilizer_coind_eq] at hf hf'
  -- every element fixing both `f` and `f'` fixes the pointwise pairing
  refine Subgroup.isOpen_mono
    (H₁ := rightTranslationStabilizer f.val ⊓ rightTranslationStabilizer f'.val)
    (fun u hu ↦ mem_rightTranslationStabilizer.2 fun x ↦ ?_) (hf.inter hf')
  rw [mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 hu).1 x,
    mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 hu).2 x]

end Pointwise

section Pairing

variable {R H G W : Type*} [CommRing R] [StarRing R] [Module ℚ R] [Group H] [Group G]
  [AddCommMonoid W] [Module R W] {φ : H →* G} {σ : Representation R H W}
  {B : W →ₗ⋆[R] W →ₗ[R] R} [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}

/-- Additivity of the class integral on two pointwise pairings of smooth coinduced functions, the
step shared by the additivity of `coindPairing` in each variable. -/
private theorem classIntegral_add_apply_coindV (hK : HasFiniteType φ.range K)
    (hB : IsInvariantSesqForm σ B) {f₁ f'₁ f₂ f'₂ : coindV φ σ}
    (h₁ : f₁ ∈ (coind φ σ).smoothVectors) (h'₁ : f'₁ ∈ (coind φ σ).smoothVectors)
    (h₂ : f₂ ∈ (coind φ σ).smoothVectors) (h'₂ : f'₂ ∈ (coind φ σ).smoothVectors) :
    classIntegral φ.range K (fun g ↦ B (f₁.val g) (f'₁.val g) + B (f₂.val g) (f'₂.val g)) =
      classIntegral φ.range K (fun g ↦ B (f₁.val g) (f'₁.val g)) +
        classIntegral φ.range K (fun g ↦ B (f₂.val g) (f'₂.val g)) :=
  classIntegral_add hK (fun _ hγ g ↦ hB.apply_coindV_mul _ _ hγ g)
    (fun _ hγ g ↦ hB.apply_coindV_mul _ _ hγ g)
    (isOpen_rightTranslationStabilizer_apply_coindV h₁ h'₁)
    (isOpen_rightTranslationStabilizer_apply_coindV h₂ h'₂)

/-- Multiplying a pointwise pairing of smooth coinduced functions by a scalar multiplies its class
integral, the step shared by the homogeneity of `coindPairing` in each variable. -/
private theorem classIntegral_mul_apply_coindV (hK : HasFiniteType φ.range K)
    (hB : IsInvariantSesqForm σ B) (c : R) {f f' : coindV φ σ}
    (hf : f ∈ (coind φ σ).smoothVectors) (hf' : f' ∈ (coind φ σ).smoothVectors) :
    classIntegral φ.range K (fun g ↦ c * B (f.val g) (f'.val g)) =
      c * classIntegral φ.range K (fun g ↦ B (f.val g) (f'.val g)) :=
  (map_classIntegral hK (AddMonoidHom.mulLeft c) (fun _ hγ g ↦ hB.apply_coindV_mul _ _ hγ g)
    (isOpen_rightTranslationStabilizer_apply_coindV hf hf')).symm

variable (S : Subrepresentation (coind φ σ)) (hS : S ≤ (coind φ σ).smoothVectors)

variable (B) in
/-- **The class-integral pairing** `⟨f, f'⟩_B = I_{Γ,K}(g ↦ B (f g) (f' g))` on a subrepresentation
`S` of smooth coinduced functions, for `Γ = φ(H)`, a subgroup `K` with `(Γ, K)` of finite type, and
a `σ`-invariant sesquilinear form `B` (`coindPairing_apply`). It is conjugate-linear in `f` and
linear in `f'`. For `S` all the smooth vectors, `hS` is `le_rfl`. -/
noncomputable def coindPairing (hK : HasFiniteType φ.range K) (hB : IsInvariantSesqForm σ B) :
    S.toSubmodule →ₗ⋆[R] S.toSubmodule →ₗ[R] R :=
  LinearMap.mk₂'ₛₗ (starRingEnd R) (RingHom.id R)
    (fun f f' ↦ classIntegral φ.range K fun g ↦
      B ((f : coindV φ σ).val g) ((f' : coindV φ σ).val g))
    (fun f₁ f₂ f' ↦ by
      simp only [Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply]
      exact classIntegral_add_apply_coindV hK hB (hS f₁.property) (hS f'.property)
        (hS f₂.property) (hS f'.property))
    (fun c f f' ↦ by
      simp only [SetLike.val_smul, Pi.smul_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      exact classIntegral_mul_apply_coindV hK hB _ (hS f.property) (hS f'.property))
    (fun f f'₁ f'₂ ↦ by
      simp only [Submodule.coe_add, Pi.add_apply, map_add]
      exact classIntegral_add_apply_coindV hK hB (hS f.property) (hS f'₁.property)
        (hS f.property) (hS f'₂.property))
    (fun c f f' ↦ by
      simp only [SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
      exact classIntegral_mul_apply_coindV hK hB _ (hS f.property) (hS f'.property))

/-- `⟨f, f'⟩_B = I_{Γ,K}(g ↦ B (f g) (f' g))`. -/
@[simp]
theorem coindPairing_apply (hK : HasFiniteType φ.range K) (hB : IsInvariantSesqForm σ B)
    (f f' : S.toSubmodule) :
    coindPairing B S hS hK hB f f' =
      classIntegral φ.range K fun g ↦ B ((f : coindV φ σ).val g) ((f' : coindV φ σ).val g) :=
  (rfl)

/-- **The pairing is invariant under right translation**:
`⟨f(· u), f'(· u)⟩_B = ⟨f, f'⟩_B` for every `u ∈ G`. -/
theorem isInvariantSesqForm_coindPairing (hK : HasFiniteType φ.range K)
    (hB : IsInvariantSesqForm σ B) :
    IsInvariantSesqForm S.toRepresentation (coindPairing B S hS hK hB) :=
  isInvariantSesqForm_iff.2 fun u f f' ↦ by
    simp only [coindPairing_apply, Subrepresentation.coe_toRepresentation_apply,
      coind_apply_coe_apply]
    exact classIntegral_comp_mul_right hK (fun _ hγ g ↦ hB.apply_coindV_mul _ _ hγ g)
      (isOpen_rightTranslationStabilizer_apply_coindV (hS f.property) (hS f'.property)) u

/-- **The pairing is hermitian when `B` is**: `star ⟨f, f'⟩_B = ⟨f', f⟩_B`. -/
theorem isSymm_coindPairing (hK : HasFiniteType φ.range K) (hB : IsInvariantSesqForm σ B)
    (hBs : B.IsSymm) : (coindPairing B S hS hK hB).IsSymm where
  eq f f' := by
    -- `star` is an additive map, so it commutes with the class integral.
    have h := map_classIntegral hK (starAddEquiv : R ≃+ R).toAddMonoidHom
      (fun _ hγ g ↦ hB.apply_coindV_mul _ _ hγ g)
      (isOpen_rightTranslationStabilizer_apply_coindV (hS f.property) (hS f'.property))
    rw [AddEquiv.coe_toAddMonoidHom, starAddEquiv_apply] at h
    rw [coindPairing_apply, coindPairing_apply, starRingEnd_apply, h]
    exact congrArg _ (funext fun g ↦ by
      rw [Function.comp_apply, starAddEquiv_apply, ← starRingEnd_apply, hBs.eq])

end Pairing

end Representation
