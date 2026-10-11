/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character

/-!
# The mod-two cup product of inhomogeneous one-cochains

With trivial `𝔽₂` coefficients, the explicit formulas `f : G → ZMod 2` enter Mathlib's homogeneous
cochains through `TauCeti.ContCohomology.inhomogeneousCochain1` and
`TauCeti.ContCohomology.inhomogeneousCochain2`. This file computes the cup product along the
multiplication pairing `TauCeti.trivialF2TopPairing` in these terms: the Alexander–Whitney product
of the images of `f` and `f'` is the image of the product cochain `(g, h) ↦ f g * f' h`, already
at cochain level, so the cup product of the classes of two continuous homomorphisms `G → 𝔽₂` is
the class of that product cochain. The action being trivial, the factor `g • f' h` of the general
explicit `(1, 1)` cup product loses its action.

No local compactness is needed, unlike for the explicit comparison
`TauCeti.trivialF2TopPairing_cup_one_one_explicitH1` in degree two: both sides are canonical
cochain classes.

## Main results

* `TauCeti.ContCohomology.cupCochain_inhomogeneousCochain1`: at cochain level, the cup product of
  the images of `f` and `f'` is the image of `(g, h) ↦ f g * f' h`.
* `TauCeti.ContCohomology.cup_cochainClass_inhomogeneousCochain1`: the same statement on classes.
* `TauCeti.ContCohomology.cup11_homClass`: the cup product of the classes `homClass` of two
  continuous homomorphisms `χ ψ : G → 𝔽₂` is the class `f2CocycleClass` of the explicit cocycle
  `(g, h) ↦ χ g * ψ h`.
-/

public section

namespace TauCeti.ContCohomology

open TopRep

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The cup product of two inhomogeneous one-cochains is their product cochain.** Along the
multiplication pairing of the trivial `𝔽₂` coefficients, the Alexander–Whitney product of the
images of `f` and `f'` is the image of `(g, h) ↦ f g * f' h`. -/
theorem cupCochain_inhomogeneousCochain1 (f f' : G → ZMod 2) (hf : Continuous f)
    (hf' : Continuous f') :
    (trivialF2TopPairing G).cupCochain 1 1 (inhomogeneousCochain1 f hf)
        (inhomogeneousCochain1 f' hf') =
      inhomogeneousCochain2 (fun q ↦ f q.1 * f' q.2)
        ((hf.comp continuous_fst).mul (hf'.comp continuous_snd)) := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [TopPairing.cupCochain_one_one_apply, inhomogeneousCochain1_apply,
    inhomogeneousCochain1_apply, inhomogeneousCochain2_apply, trivialF2TopPairing_bil_apply,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **The cup product of the classes of two inhomogeneous one-cocycles is the class of their
product cochain.** For continuous `f f' : G → ZMod 2` whose images are cocycles, that is, continuous
homomorphisms, the cup product along `trivialF2TopPairing` of their classes is the class of
`(g, h) ↦ f g * f' h`. -/
theorem cup_cochainClass_inhomogeneousCochain1 (f f' : G → ZMod 2) (hf : Continuous f)
    (hf' : Continuous f')
    (hd : ((homogeneousCochains (trivialF2 G)).d 1 2).hom (inhomogeneousCochain1 f hf) = 0)
    (hd' : ((homogeneousCochains (trivialF2 G)).d 1 2).hom (inhomogeneousCochain1 f' hf') = 0)
    (hd'' : ((homogeneousCochains (trivialF2 G)).d 2 3).hom
      (inhomogeneousCochain2 (fun q ↦ f q.1 * f' q.2)
        ((hf.comp continuous_fst).mul (hf'.comp continuous_snd))) = 0) :
    (trivialF2TopPairing G).cup 1 1 ((trivialF2 G).cochainClass 1 (inhomogeneousCochain1 f hf) hd)
        ((trivialF2 G).cochainClass 1 (inhomogeneousCochain1 f' hf') hd') =
      (trivialF2 G).cochainClass 2
        (inhomogeneousCochain2 (fun q ↦ f q.1 * f' q.2)
          ((hf.comp continuous_fst).mul (hf'.comp continuous_snd))) hd'' := by
  rw [TopPairing.cup_cochainClass _ 1 1 _ hd _ hd'
    (by rw [cupCochain_inhomogeneousCochain1]; exact hd'')]
  simp only [cupCochain_inhomogeneousCochain1]

/-- **The cup product of the classes of two continuous homomorphisms to `𝔽₂`** is the class of the
product cocycle `(g, h) ↦ χ g * ψ h`: the cup product along `trivialF2TopPairing` of `homClass χ`
and `homClass ψ` is `f2CocycleClass` of that cocycle. -/
theorem cup11_homClass (χ ψ : G →* Multiplicative (ZMod 2)) (hχ : Continuous χ)
    (hψ : Continuous ψ) :
    (trivialF2TopPairing G).cup 1 1 (homClass G χ hχ) (homClass G ψ hψ) =
      f2CocycleClass (fun q ↦ Multiplicative.toAdd (χ q.1) * Multiplicative.toAdd (ψ q.2))
        (((continuous_toAdd.comp hχ).comp continuous_fst).mul
          ((continuous_toAdd.comp hψ).comp continuous_snd))
        (fun g h j ↦ by simp only [map_mul, toAdd_mul]; ring) := by
  rw [homClass_eq_cochainClass, homClass_eq_cochainClass, f2CocycleClass_def]
  exact cup_cochainClass_inhomogeneousCochain1 _ _ _ _ _ _ _

end TauCeti.ContCohomology
