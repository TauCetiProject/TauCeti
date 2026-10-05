/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# Explicit inhomogeneous cochains with trivial `𝔽₂` coefficients

Explicit cohomological constructions with trivial `𝔽₂` coefficients, such as the two-point graph
cocycle of the Evens norm or a factor set pulled back along a homomorphism, are given by formulas
`G → ZMod 2` and `G × G → ZMod 2`. Continuous cohomology with these coefficients is computed by
Mathlib's homogeneous cochains of `TauCeti.trivialF2 G`, whose carrier is the universe lift
`ULift (ZMod 2)`. This file places continuous formulas in that complex, through the classical
passage `f ↦ ((g₀, g₁) ↦ f (g₀⁻¹ g₁))` and `f ↦ ((g₀, g₁, g₂) ↦ f (g₀⁻¹ g₁, g₁⁻¹ g₂))` from
inhomogeneous to homogeneous cochains, the action being trivial. These constructors are the only
place where the universe lift is crossed.

Under this passage the canonical differential becomes the inhomogeneous one: a formula is a cocycle
exactly when it satisfies the inhomogeneous cocycle identity, and the differential of the image of
a `1`-cochain `ψ` is the image of `(g, h) ↦ ψ h - ψ (g h) + ψ g`. Hence two continuous
inhomogeneous `2`-cocycles that differ by such an explicit coboundary have the same class in
`continuousCohomology 2 (trivialF2 G)`. This is how a coboundary witness written as a formula
crosses to the canonical object.

No local compactness is needed: the homogeneous cochains are obtained by currying a jointly
continuous function, which is always possible. For a general discrete module, the passage between
the two kinds of cochains is `TauCeti.ContCohomology.cochainEquiv1` and
`TauCeti.ContCohomology.cochainEquiv2`.

## Main definitions

* `TauCeti.ContCohomology.inhomogeneousCochain1`, `TauCeti.ContCohomology.inhomogeneousCochain2`:
  a continuous `ZMod 2`-valued function on `G`, respectively `G × G`, as a homogeneous cochain of
  `trivialF2 G`.

## Main results

* `TauCeti.ContCohomology.inhomogeneousCochain1_d_eq_zero_iff`: the image of `f : G → ZMod 2` is a
  cocycle exactly when `f` is additive, that is, a homomorphism.
* `TauCeti.ContCohomology.inhomogeneousCochain2_d_eq_zero_iff`: the image of `f : G × G → ZMod 2`
  is a cocycle exactly when `f` satisfies the inhomogeneous `2`-cocycle identity.
* `TauCeti.ContCohomology.d_inhomogeneousCochain1`: the differential of the image of a `1`-cochain
  is the image of its inhomogeneous coboundary.
* `TauCeti.ContCohomology.cochainClass_inhomogeneousCochain2_eq_of_coboundary`: cohomologous
  continuous inhomogeneous `2`-cocycles have the same class.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  inhomogeneous description of continuous cochains.
-/

public section

namespace TauCeti.ContCohomology

open TopRep

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous function `f : G → ZMod 2`, as the homogeneous `1`-cochain
`(g₀, g₁) ↦ f (g₀⁻¹ * g₁)` of the trivial `𝔽₂` coefficients `trivialF2 G`, lifted to their
carrier.

Source: this constructor is close to the degree-`1` constructor of Tau Ceti PR
[#11157](https://github.com/TauCetiProject/TauCeti/pull/11157); here it is stated on
`homogeneousCochains (trivialF2 G)` directly, without local compactness, with
`inhomogeneousCochain2` as its degree-`2` counterpart. -/
noncomputable def inhomogeneousCochain1 (f : G → ZMod 2) (hf : Continuous f) :
    (homogeneousCochains (trivialF2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦ (trivialF2Equiv G).symm (f (q.1⁻¹ * q.2)),
      continuous_of_discreteTopology.comp (hf.comp (continuous_fst.inv.mul continuous_snd))⟩,
    fun g ↦ by
      ext h₀ h₁
      simp only [ContRepresentation.coind₁_apply_apply, trivialF2_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]⟩

/-- The value of `inhomogeneousCochain1 f hf` at `(g₀, g₁)` is `f (g₀⁻¹ * g₁)`, lifted to the
carrier of `trivialF2 G`. -/
@[simp]
theorem inhomogeneousCochain1_apply (f : G → ZMod 2) (hf : Continuous f) (g₀ g₁ : G) :
    (inhomogeneousCochain1 f hf).val g₀ g₁ = (trivialF2Equiv G).symm (f (g₀⁻¹ * g₁)) :=
  (rfl)

/-- A continuous function `f : G × G → ZMod 2`, as the homogeneous `2`-cochain
`(g₀, g₁, g₂) ↦ f (g₀⁻¹ * g₁, g₁⁻¹ * g₂)` of the trivial `𝔽₂` coefficients `trivialF2 G`, lifted
to their carrier. -/
noncomputable def inhomogeneousCochain2 (f : G × G → ZMod 2) (hf : Continuous f) :
    (homogeneousCochains (trivialF2 G)).X 2 :=
  ⟨ContinuousMap.curry <| ContinuousMap.curry
      ⟨fun q : (G × G) × G ↦ (trivialF2Equiv G).symm (f (q.1.1⁻¹ * q.1.2, q.1.2⁻¹ * q.2)),
        continuous_of_discreteTopology.comp (hf.comp
          ((continuous_fst.comp continuous_fst).inv.mul (continuous_snd.comp continuous_fst)
            |>.prodMk ((continuous_snd.comp continuous_fst).inv.mul continuous_snd)))⟩,
    fun g ↦ by
      ext h₀ h₁ h₂
      simp only [ContRepresentation.coind₁_apply_apply, trivialF2_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]⟩

/-- The value of `inhomogeneousCochain2 f hf` at `(g₀, g₁, g₂)` is `f (g₀⁻¹ * g₁, g₁⁻¹ * g₂)`,
lifted to the carrier of `trivialF2 G`. -/
@[simp]
theorem inhomogeneousCochain2_apply (f : G × G → ZMod 2) (hf : Continuous f) (g₀ g₁ g₂ : G) :
    (inhomogeneousCochain2 f hf).val g₀ g₁ g₂ =
      (trivialF2Equiv G).symm (f (g₀⁻¹ * g₁, g₁⁻¹ * g₂)) :=
  (rfl)

/-- **The canonical differential of an inhomogeneous `1`-cochain is its inhomogeneous
coboundary**: the differential of the image of `ψ` is the image of
`(g, h) ↦ ψ h - ψ (g * h) + ψ g`. -/
theorem d_inhomogeneousCochain1 (ψ : G → ZMod 2) (hψ : Continuous ψ) :
    ((homogeneousCochains (trivialF2 G)).d 1 2).hom (inhomogeneousCochain1 ψ hψ) =
      inhomogeneousCochain2 (fun p ↦ ψ p.2 - ψ (p.1 * p.2) + ψ p.1)
        (((hψ.comp continuous_snd).sub (hψ.comp (continuous_fst.mul continuous_snd))).add
          (hψ.comp continuous_fst)) := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply, inhomogeneousCochain1_apply, inhomogeneousCochain1_apply,
    inhomogeneousCochain1_apply, inhomogeneousCochain2_apply]
  simp only [← map_sub, mul_assoc, mul_inv_cancel_left]
  congr 1
  abel

/-- **The image of `f : G → ZMod 2` is a cocycle exactly when `f` is additive.** With trivial
coefficients the inhomogeneous `1`-cocycles are the homomorphisms. -/
theorem inhomogeneousCochain1_d_eq_zero_iff (f : G → ZMod 2) (hf : Continuous f) :
    ((homogeneousCochains (trivialF2 G)).d 1 2).hom (inhomogeneousCochain1 f hf) = 0 ↔
      ∀ g h : G, f (g * h) = f g + f h := by
  constructor
  · intro hd g h
    have e := congrArg
      (fun z : (homogeneousCochains (trivialF2 G)).X 2 ↦ trivialF2Equiv G (z.val 1 g (g * h))) hd
    simp only at e
    rw [homogeneousCochains.d_one_apply, inhomogeneousCochain1_apply, inhomogeneousCochain1_apply,
      inhomogeneousCochain1_apply] at e
    simp only [Submodule.coe_zero, ContinuousMap.zero_apply, map_sub, map_zero,
      AddEquiv.apply_symm_apply, inv_one, one_mul, inv_mul_cancel_left] at e
    linear_combination -e
  · intro hc
    apply Subtype.ext
    ext g₀ g₁ g₂
    rw [homogeneousCochains.d_one_apply, inhomogeneousCochain1_apply, inhomogeneousCochain1_apply,
      inhomogeneousCochain1_apply]
    simp only [← map_sub, Submodule.coe_zero, ContinuousMap.zero_apply,
      ← map_zero (trivialF2Equiv G).symm]
    have h := hc (g₀⁻¹ * g₁) (g₁⁻¹ * g₂)
    simp only [mul_assoc, mul_inv_cancel_left] at h
    congr 1
    linear_combination -h

/-- **The image of a homomorphism is a cocycle.** -/
theorem inhomogeneousCochain1_d_eq_zero (f : G → ZMod 2) (hf : Continuous f)
    (hcocycle : ∀ g h : G, f (g * h) = f g + f h) :
    ((homogeneousCochains (trivialF2 G)).d 1 2).hom (inhomogeneousCochain1 f hf) = 0 :=
  (inhomogeneousCochain1_d_eq_zero_iff f hf).2 hcocycle

/-- **The image of `f : G × G → ZMod 2` is a cocycle exactly when `f` satisfies the inhomogeneous
`2`-cocycle identity** `f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)`. -/
theorem inhomogeneousCochain2_d_eq_zero_iff (f : G × G → ZMod 2) (hf : Continuous f) :
    ((homogeneousCochains (trivialF2 G)).d 2 3).hom (inhomogeneousCochain2 f hf) = 0 ↔
      ∀ g h j : G, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j) := by
  constructor
  · intro hd g h j
    have e := congrArg (fun z : (homogeneousCochains (trivialF2 G)).X 3 ↦
      trivialF2Equiv G (z.val 1 g (g * h) (g * h * j))) hd
    simp only at e
    rw [homogeneousCochains.d_two_apply, inhomogeneousCochain2_apply, inhomogeneousCochain2_apply,
      inhomogeneousCochain2_apply, inhomogeneousCochain2_apply] at e
    simp only [Submodule.coe_zero, ContinuousMap.zero_apply, map_sub, map_zero,
      AddEquiv.apply_symm_apply, inv_one, one_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left] at e
    linear_combination -e
  · intro hc
    apply Subtype.ext
    ext g₀ g₁ g₂ g₃
    rw [homogeneousCochains.d_two_apply, inhomogeneousCochain2_apply, inhomogeneousCochain2_apply,
      inhomogeneousCochain2_apply, inhomogeneousCochain2_apply]
    simp only [← map_sub, Submodule.coe_zero, ContinuousMap.zero_apply,
      ← map_zero (trivialF2Equiv G).symm]
    have h := hc (g₀⁻¹ * g₁) (g₁⁻¹ * g₂) (g₂⁻¹ * g₃)
    simp only [mul_assoc, mul_inv_cancel_left] at h
    congr 1
    linear_combination -h

/-- **The image of an inhomogeneous `2`-cocycle is a cocycle.** -/
theorem inhomogeneousCochain2_d_eq_zero (f : G × G → ZMod 2) (hf : Continuous f)
    (hcocycle : ∀ g h j : G, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) :
    ((homogeneousCochains (trivialF2 G)).d 2 3).hom (inhomogeneousCochain2 f hf) = 0 :=
  (inhomogeneousCochain2_d_eq_zero_iff f hf).2 hcocycle

/-- **Cohomologous inhomogeneous `2`-cocycles have the same class.** If two continuous functions
`f f' : G × G → ZMod 2` whose images are cocycles differ by the inhomogeneous coboundary
`(g, h) ↦ ψ h - ψ (g * h) + ψ g` of a continuous `ψ : G → ZMod 2`, their images have the same class
in `continuousCohomology 2 (trivialF2 G)`. The cocycle hypotheses are typically
`inhomogeneousCochain2_d_eq_zero f hf hcf` and its counterpart for `f'`. -/
theorem cochainClass_inhomogeneousCochain2_eq_of_coboundary (f f' : G × G → ZMod 2)
    (hf : Continuous f) (hf' : Continuous f') (ψ : G → ZMod 2) (hψ : Continuous ψ)
    (hfψ : ∀ g h : G, f (g, h) = f' (g, h) + (ψ h - ψ (g * h) + ψ g))
    (ha : ((homogeneousCochains (trivialF2 G)).d 2 3).hom (inhomogeneousCochain2 f hf) = 0)
    (hb : ((homogeneousCochains (trivialF2 G)).d 2 3).hom (inhomogeneousCochain2 f' hf') = 0) :
    (trivialF2 G).cochainClass 2 (inhomogeneousCochain2 f hf) ha =
      (trivialF2 G).cochainClass 2 (inhomogeneousCochain2 f' hf') hb := by
  refine cochainClass_eq_of_sub_eq_d (j := 1) rfl ha hb (inhomogeneousCochain1 ψ hψ) ?_
  rw [d_inhomogeneousCochain1]
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [Submodule.coe_sub, ContinuousMap.sub_apply, ContinuousMap.sub_apply,
    ContinuousMap.sub_apply, inhomogeneousCochain2_apply, inhomogeneousCochain2_apply,
    inhomogeneousCochain2_apply, ← map_sub, hfψ]
  simp only [mul_assoc, mul_inv_cancel_left, add_sub_cancel_left]

end TauCeti.ContCohomology
