/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Permutation
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Singular homology of a double cover and the sign local system

Let `p : E ⟶ B` be a covering map and `σ : E → E` a continuous involution over `B`. The singular
homology of `E` is the homology of `B` twisted by the permutation local system of `p`
(`IsCoveringMap.singularHomologyPermutationIso`), and under this identification `σ_*` is induced
by the endomorphism moving the sheets by `σ`
(`IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom`). Antisymmetrization from the
permutation local system to the sign local system of `σ`
(`IsCoveringMap.permutationLocalSystemToSign`) changes sign when precomposed with that
endomorphism. So the composite

`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`

satisfies `σ_* c ↦ -(image of c)`
(`IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`). When the fibres
are finite, reading functions on fibres as formal sums of sheets gives a morphism back
(`IsCoveringMap.signLocalSystemToPermutation`), and the round trip on `Hₖ(E; R)` is `1 - σ_*`
(`IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`).

Read back on the cover, a class of `Hₖ(B; sign)` gives a class of `Hₖ(E; R)`
(`IsCoveringMap.signHomologyToCover`) on which `σ_*` acts by `-1`
(`IsCoveringMap.signHomologyToCover_comp_homologyMap`), and antisymmetrizing it again gives twice
the original class (`IsCoveringMap.signHomologyToCover_comp_hom_comp_toSign`), since a function
`f` changing sign under `σ` has `f e - f (σ e) = 2 f e`. So when `2` is invertible in `R`, the
sign-twisted homology of the base is the anti-invariant part of the homology of the cover:
reading classes back is injective (`IsCoveringMap.injective_signHomologyToCover`), and its image
is the set of classes `c` with `σ_* c = -c` (`IsCoveringMap.range_signHomologyToCover`), since
such a class is `(1 - σ_*) (c / 2)`. This gives the linear equivalence
`Hₖ(B; sign) ≃ {c ∈ Hₖ(E; R) | σ_* c = -c}` (`IsCoveringMap.signHomologyLinearEquiv`). No
condition on the fibres beyond finiteness is needed. It is the sign counterpart of the
identification of `Hₖ(B; R)` with the invariant classes of the cover when the number of sheets is
invertible (`IsQuotientCoveringMap.isLimitHomologyMapConeTransferCone`). For the orientation
double cover of a vector bundle, with its deck involution, the sign local system is the
orientation local system, so over a field of characteristic other than `2` the homology of the
base twisted by the orientation local system is the part of the homology of the orientation cover
on which the deck involution acts by `-1`.

When every fibre is a pair `{e, σ e}` with `σ e ≠ e`, the short exact sequence
`0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` (`IsCoveringMap.shortExact_signPermutationShortComplex`) has a
coefficient long exact sequence. It shows that a class `c ∈ Hₖ(E; R)` with `p_* c = 0` comes from
`Hₖ(B; sign)`
(`IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq`), from a
unique class when `Hₖ₊₁(B; R) = 0`
(`IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`).

For the orientation double cover of a manifold with its deck involution, the sign local system is
the orientation local system, and the class of the fundamental class of the orientation cover is
the fundamental class of the manifold with orientation-twisted coefficients
(`TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass`).

## Main definitions

* `IsCoveringMap.signHomologyToCover`: the map `Hₖ(B; sign) ⟶ Hₖ(E; R)` reading functions on
  fibres as formal sums of sheets.
* `IsCoveringMap.signHomologyLinearEquiv`: when `2` is invertible, `Hₖ(B; sign)` is linearly
  equivalent to the classes `c ∈ Hₖ(E; R)` with `σ_* c = -c`.

## Main results

* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`: antisymmetrizing
  the image of `σ_* c` gives the negative of antisymmetrizing the image of `c`.
* `IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`: the round
  trip through the sign local system is `1 - σ_*`.
* `IsCoveringMap.signHomologyToCover_comp_homologyMap` and
  `IsCoveringMap.signHomologyToCover_comp_hom_comp_toSign`: a sign class read on the cover changes
  sign under `σ_*`, and antisymmetrizing it again doubles it.
* `IsCoveringMap.injective_signHomologyToCover` and `IsCoveringMap.range_signHomologyToCover`: when
  `2` is invertible, reading sign classes on the cover is injective, with image the classes
  changing sign under `σ_*`.
* `IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq` and
  `IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`: classes of
  a double cover killed by `p_*` come from the sign local system, uniquely when
  `Hₖ₊₁(B; R) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients, the local
  system of a covering space and the orientation local system of a manifold, and Section 3.G
  (Proposition 3G.1), for the transfer and the averaging argument with an invertible number of
  sheets.
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

universe u

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  {σ : C(E, E)} (hσ : ⇑p ∘ ⇑σ = ⇑p) (hσσ : Function.Involutive σ)

/-- **Antisymmetrizing anti-commutes with an involution over the base**: for the composite
`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`, the image of `σ_* c` is the negative of the image
of `c`. -/
theorem homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k ≫
        (hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k =
      -((hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k) := by
  rw [homologyMap_comp_singularHomologyPermutationIso_hom_assoc hp R σ hσ,
    ← twistedHomologyCoefficientMap_comp, permutationLocalSystemFiberMap_comp_toSign,
    twistedHomologyCoefficientMap_neg, Preadditive.comp_neg]

variable (hfin : ∀ b, Finite (p ⁻¹' {b}))

/-- **The round trip through the sign local system is `1 - σ_*`**: antisymmetrizing the image of
a class `c ∈ Hₖ(E; R)` in `Hₖ(B; R[p⁻¹ b])`, reading it back as a formal sum of sheets and
returning to `Hₖ(E; R)` gives `c - σ_* c`. -/
theorem singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k ≫
          twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k ≫
            (hp.singularHomologyPermutationIso R k).inv =
      𝟙 _ - SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k := by
  rw [← twistedHomologyCoefficientMap_comp_assoc,
    permutationLocalSystemToSign_comp_toPermutation, twistedHomologyCoefficientMap_sub,
    twistedHomologyCoefficientMap_id, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Iso.hom_inv_id, ← homologyMap_comp_singularHomologyPermutationIso_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! ### Sign classes as anti-invariant classes of the cover -/

/-- The map `Hₖ(B; sign) ⟶ Hₖ(E; R)` reading a class of `B` twisted by the sign local system of
`σ` as a class of the cover: a function on a fibre is read as the formal sum of the sheets with
these coefficients, and the homology of `B` twisted by the permutation local system is the
homology of `E`. -/
def signHomologyToCover (k : ℕ) :
    twistedHomology.{u, u, u} (hp.signLocalSystem R σ hσ) k ⟶
      (TopCat.toSSet.obj E).homology (ModuleCat.of R R) k :=
  twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k ≫
    (hp.singularHomologyPermutationIso R k).inv

/-- The map from the sign-twisted homology of the base to the homology of the cover is the map on
twisted homology of reading functions on fibres as formal sums of sheets, followed by the
identification of the permutation-twisted homology of the base with the homology of the cover. -/
theorem signHomologyToCover_def (k : ℕ) :
    hp.signHomologyToCover R hσ hfin k =
      twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k ≫
        (hp.singularHomologyPermutationIso R k).inv :=
  (rfl)

include hσσ in
/-- **Sign classes are anti-invariant on the cover**: a class of `Hₖ(B; sign)` read as a class
of the cover changes sign under `σ_*`. -/
@[reassoc (attr := simp)]
theorem signHomologyToCover_comp_homologyMap (k : ℕ) :
    hp.signHomologyToCover R hσ hfin k ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k =
      -hp.signHomologyToCover R hσ hfin k := by
  -- Under the identification with permutation-twisted homology, `σ_*` moves the sheets by `σ`.
  have h : (hp.singularHomologyPermutationIso R k).inv ≫
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k =
        twistedHomologyCoefficientMap (hp.permutationLocalSystemFiberMap R σ hσ) k ≫
          (hp.singularHomologyPermutationIso R k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← homologyMap_comp_singularHomologyPermutationIso_hom hp R σ hσ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [signHomologyToCover_def, Category.assoc, h, ← twistedHomologyCoefficientMap_comp_assoc,
    signLocalSystemToPermutation_comp_permutationLocalSystemFiberMap _ _ _ hσσ,
    twistedHomologyCoefficientMap_neg, Preadditive.neg_comp]

/-- **Antisymmetrizing a sign class read on the cover doubles it**: reading a class of
`Hₖ(B; sign)` as a class of the cover and antisymmetrizing its image in `Hₖ(B; R[p⁻¹ b])` gives
twice the class. -/
@[reassoc (attr := simp)]
theorem signHomologyToCover_comp_hom_comp_toSign (k : ℕ) :
    hp.signHomologyToCover R hσ hfin k ≫ (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k =
      𝟙 _ + 𝟙 _ := by
  rw [signHomologyToCover_def, Category.assoc, Iso.inv_hom_id_assoc,
    ← twistedHomologyCoefficientMap_comp, signLocalSystemToPermutation_comp_toSign,
    twistedHomologyCoefficientMap_add, twistedHomologyCoefficientMap_id]

section Invertible

variable [Invertible (2 : R)]

include hσσ in
/-- **Sign classes embed in the homology of the cover when `2` is invertible**: if `2` is
invertible in `R`, reading classes of `Hₖ(B; sign)` as classes of the cover is injective, since
antisymmetrizing again multiplies by `2`. -/
theorem injective_signHomologyToCover (k : ℕ) :
    Function.Injective (hp.signHomologyToCover R hσ hfin k).hom := by
  refine (injective_iff_map_eq_zero _).2 fun g hg ↦ ?_
  have h := congrArg (fun φ ↦ φ.hom g) (hp.signHomologyToCover_comp_hom_comp_toSign R hσ hσσ hfin k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hg, map_zero, ModuleCat.hom_add,
    ModuleCat.hom_id, LinearMap.add_apply, LinearMap.id_apply] at h
  -- `g + g = (2 : R) • g` vanishes, and `2` is invertible.
  rw [← two_smul R g] at h
  rw [← one_smul R g, ← invOf_mul_self (2 : R), mul_smul, ← h, smul_zero]

include hσσ in
/-- **The sign classes are the anti-invariant classes of the cover when `2` is invertible**: if
`2` is invertible in `R`, a class `c ∈ Hₖ(E; R)` is read from a class of `Hₖ(B; sign)` exactly
when `σ_* c = -c`. -/
theorem range_signHomologyToCover (k : ℕ) :
    LinearMap.range (hp.signHomologyToCover R hσ hfin k).hom =
      LinearMap.ker ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ))
        (ModuleCat.of R R) k).hom + LinearMap.id) := by
  refine le_antisymm ?_ fun c hc ↦ ?_
  · rintro _ ⟨g, rfl⟩
    have h := congrArg (fun φ ↦ φ.hom g) (hp.signHomologyToCover_comp_homologyMap R hσ hσσ hfin k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply] at h
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, h, neg_add_cancel]
  · -- An anti-invariant class `c` is `(1 - σ_*) (⅟2 • c)`, which is read from a sign class.
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg] at hc
    refine ⟨((hp.singularHomologyPermutationIso R k).hom ≫
      twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k).hom
        (⅟(2 : R) • c), ?_⟩
    have h := congrArg (fun φ ↦ φ.hom (⅟(2 : R) • c))
      (hp.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation R hσ hσσ hfin k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, ModuleCat.hom_id,
      LinearMap.sub_apply, LinearMap.id_apply] at h
    simp only [signHomologyToCover_def, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h, map_smul, hc, smul_neg, sub_neg_eq_add, ← add_smul, invOf_two_add_invOf_two, one_smul]

/-- **The sign-twisted homology of the base is the anti-invariant part of the homology of the
cover when `2` is invertible**: reading functions on fibres as formal sums of sheets identifies
`Hₖ(B; sign)` with the classes `c ∈ Hₖ(E; R)` with `σ_* c = -c`. -/
def signHomologyLinearEquiv (k : ℕ) :
    twistedHomology.{u, u, u} (hp.signLocalSystem R σ hσ) k ≃ₗ[R]
      LinearMap.ker ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ))
        (ModuleCat.of R R) k).hom + LinearMap.id) :=
  (LinearEquiv.ofInjective _ (hp.injective_signHomologyToCover R hσ hσσ hfin k)).trans
    (LinearEquiv.ofEq _ _ (hp.range_signHomologyToCover R hσ hσσ hfin k))

/-- The identification of sign classes with anti-invariant classes is
`IsCoveringMap.signHomologyToCover`. -/
@[simp]
theorem coe_signHomologyLinearEquiv_apply (k : ℕ)
    (g : twistedHomology.{u, u, u} (hp.signLocalSystem R σ hσ) k) :
    (hp.signHomologyLinearEquiv R hσ hσσ hfin k g :
      ((TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) =
        (hp.signHomologyToCover R hσ hfin k).hom g :=
  (rfl)

end Invertible

section DoubleCover

variable (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)
  (hsurj : Function.Surjective p)

include hσσ hfix hfib hsurj in
/-- **Reading sign classes as classes of the cover is injective below a vanishing degree**: for a
double cover, if `Hₖ₊₁(B; R) = 0` then the map `Hₖ(B; sign) ⟶ Hₖ(B; R[p⁻¹ b])` reading functions
on fibres as formal sums of sheets is injective, by the coefficient long exact sequence of
`0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0`. -/
theorem injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation (k : ℕ)
    (hk : Limits.IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj B)) :
    Function.Injective
      (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  have := (hS.twistedHomology_exact₁ (k + 1) k rfl).mono_g
    ((hk.of_iso (twistedHomologyConstantIso B (ModuleCat.of R R) (k + 1))).eq_of_src _ _)
  exact (ModuleCat.mono_iff_injective _).1 this

include hσσ hfix hfib hsurj in
/-- **Classes of the cover killed by the projection come from the sign local system**: for a
double cover, a class `c ∈ Hₖ(E; R)` with `p_* c = 0` is, as a class of `B` twisted by the
permutation local system, the image of a class of `Hₖ(B; sign)` read as formal sums of sheets.
This is exactness of the coefficient long exact sequence of `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` at
`Hₖ(B; R[p⁻¹ b])`. -/
theorem exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq (k : ℕ)
    (c : ((TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R))
    (hc : (SSet.homologyMap (TopCat.toSSet.map p) (ModuleCat.of R R) k).hom c = 0) :
    ∃ g, (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom g =
      (hp.singularHomologyPermutationIso R k).hom.hom c := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  refine (ShortComplex.moduleCat_exact_iff _).1 (hS.twistedHomology_exact₂ k) _ ?_
  -- The augmentation of the image of `c` is `p_* c = 0`.
  have h := congrArg (fun φ ↦ φ.hom c) (hp.singularHomologyPermutationIso_hom_comp_augmentation R k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine (ModuleCat.mono_iff_injective
    (twistedHomologyConstantIso B (ModuleCat.of R R) k).hom).1 inferInstance ?_
  exact h.trans (hc.trans (map_zero _).symm)

end DoubleCover

end IsCoveringMap
