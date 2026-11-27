/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum

/-!
# Čech cohomology of split bundles `⨁ₗ 𝒪(k l)` on complex projective space

For a finite family of integers `k : κ → ℤ`, the sheaf of holomorphic sections of the split bundle
`⨁ₗ 𝒪(k l)` (`Projectivization.twistSumCore k`) on `ℂℙⁿ` is the biproduct of the sheaves of
holomorphic sections of the line bundles `𝒪(k l)` (`Projectivization.twistCore`), with the
morphisms induced by the projections onto the summands and the inclusions of the summands
(`Projectivization.twistSumSheafBiconeIsBilimit`). Čech cohomology is an additive functor of the
sheaf, so it preserves this biproduct:
`Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) ≅ ⨁ₗ Hᵖ(ℂℙⁿ, 𝒪(k l))`
(`Projectivization.holomorphicSectionCechCohomologyTwistSumIso`).

On the projective line, `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le`), so
`H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` as soon as every `k l ≥ -1`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`). This
is the vanishing used for holomorphic spheres `u` whose pullback bundle `u* TX` splits in this
way, such as a line in `ℂℙⁿ`, along which `u* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹`.

The bicone, its bilimit and the cohomology isomorphism are the finite-family version of the binary
`TauCeti.holomorphicSectionSheaf.prodBicone`, `TauCeti.holomorphicSectionSheaf.prodBiconeIsBilimit`
and `TauCeti.holomorphicSectionCechCohomology.prodIso`, and follow their construction. A separate
version is needed because the model fibre of `⨁ₗ 𝒪(k l)` is `κ → ℂ` rather than an iterated `×ᵇ`.

## Main declarations

* `Projectivization.twistSumSheafProj k l`, `Projectivization.twistSumSheafSingle k l`: the
  projection of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` onto that of the summand
  `𝒪(k l)`, and the inclusion of the latter.
* `Projectivization.twistSumSheafBicone k`, `Projectivization.twistSumSheafBiconeIsBilimit k`: the
  sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` is the biproduct of those of the summands.
* `Projectivization.holomorphicSectionCechCohomologyTwistSumIso k p`:
  `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) ≅ ⨁ₗ Hᵖ(ℂℙⁿ, 𝒪(k l))`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore`: `Hᵖ` of a split bundle
  vanishes when it vanishes for every summand.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`:
  `H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` when every `k l ≥ -1`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the regularity of lines.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ} {κ : Type} [Fintype κ] (k : κ → ℤ)

/-! ### The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` -/

/-- The projection of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` onto the sheaf of
holomorphic sections of the summand `𝒪(k l)`, taking a section to its component `l`. -/
def twistSumSheafProj (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  -- The fibres of `⨁ₗ 𝒪(k l)` and of `𝒪(k l)` are `κ → ℂ` and `ℂ`, by definition.
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.proj (R := ℂ) (φ := fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_apply k l)

variable [DecidableEq κ] in
/-- The inclusion of the sheaf of holomorphic sections of the summand `𝒪(k l)` into the sheaf of
holomorphic sections of `⨁ₗ 𝒪(k l)`, placing a section in the component `l`. -/
def twistSumSheafSingle (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  -- The fibres of `𝒪(k l)` and of `⨁ₗ 𝒪(k l)` are `ℂ` and `κ → ℂ`, by definition.
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.single ℂ (fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_single k l)

variable {k}

/-- The projection onto the summand `l` takes a section to its component `l`. -/
@[simp]
theorem twistSumSheafProj_app_apply (l : κ) {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumSheafProj k l).hom.app U s x = (s x : κ → ℂ) l :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

section Single

variable [DecidableEq κ]

/-- The inclusion of the summand `l` places a section in the component `l`. -/
@[simp]
theorem twistSumSheafSingle_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber).obj.obj U) (x : ↥(unop U)) :
    ((twistSumSheafSingle k l).hom.app U s x : κ → ℂ) = Pi.single l (s x : ℂ) :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

/-- Projecting a section of the summand `l` placed in the component `l` gives it back. -/
@[reassoc (attr := simp)]
theorem twistSumSheafSingle_proj_self (l : κ) :
    twistSumSheafSingle (n := n) k l ≫ twistSumSheafProj k l = 𝟙 _ :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    -- the fibre of `𝒪(k l)` is `ℂ`, by definition
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply, twistSumSheafProj_app_apply, twistSumSheafSingle_app_apply]
    exact Pi.single_eq_same (M := fun _ : κ ↦ ℂ) l (s x : ℂ)

/-- Projecting a section of the summand `l` placed in the component `l` onto another component
`l'` gives `0`. -/
@[reassoc (attr := simp)]
theorem twistSumSheafSingle_proj_of_ne {l l' : κ} (h : l ≠ l') :
    twistSumSheafSingle (n := n) k l ≫ twistSumSheafProj k l' = 0 :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.zero_hom_app_apply]
    -- the fibre of `𝒪(k l')` is `ℂ`, by definition
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply, twistSumSheafProj_app_apply, twistSumSheafSingle_app_apply]
    exact Pi.single_eq_of_ne' (M := fun _ : κ ↦ ℂ) h (s x : ℂ)

variable (k)

/-- The components of a section of `⨁ₗ 𝒪(k l)`, placed back in their summands, add up to the
section: the projections and inclusions of the summands add up to the identity of the sheaf of
holomorphic sections of `⨁ₗ 𝒪(k l)`. -/
theorem sum_twistSumSheafProj_comp_twistSumSheafSingle :
    ∑ l, twistSumSheafProj (n := n) k l ≫ twistSumSheafSingle k l = 𝟙 _ :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.sum_hom_app_apply]
    -- the fibre of `⨁ₗ 𝒪(k l)` is `κ → ℂ`, by definition
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply, twistSumSheafProj_app_apply, twistSumSheafSingle_app_apply]
    exact Finset.univ_sum_single (s x : κ → ℂ)

/-- The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)`, with the projections onto the summands and
the inclusions of the summands, as a bicone over the sheaves of holomorphic sections of the
summands `𝒪(k l)`. -/
-- Exposed so that the cone point is visibly the sheaf of `⨁ₗ 𝒪(k l)`: otherwise the legs cannot
-- be stated as `twistSumSheafProj` and `twistSumSheafSingle` in the simp lemmas.
@[expose, simps]
def twistSumSheafBicone :
    Bicone fun l ↦
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber where
  pt := holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber
  «π» := twistSumSheafProj k
  ι := twistSumSheafSingle k
  ι_π l l' := by
    split_ifs with h
    · subst h
      simp
    · exact twistSumSheafSingle_proj_of_ne h

/-- **The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` is the biproduct of the sheaves of
holomorphic sections of the summands `𝒪(k l)`.** -/
def twistSumSheafBiconeIsBilimit : (twistSumSheafBicone (n := n) k).IsBilimit :=
  isBilimitOfTotal _ (sum_twistSumSheafProj_comp_twistSumSheafSingle k)

/-! ### Čech cohomology -/

variable (p : ℕ)

/-- **Additivity.** The Čech cohomology `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` of the sheaf of holomorphic sections
of `⨁ₗ 𝒪(k l)` is the biproduct of the cohomologies `Hᵖ(ℂℙⁿ, 𝒪(k l))` of the summands, since Čech
cohomology is an additive functor of the sheaf and so preserves the biproduct
`Projectivization.twistSumSheafBiconeIsBilimit`. -/
def holomorphicSectionCechCohomologyTwistSumIso :
    holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p ≅
      ⨁ fun l ↦ holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
        (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves
    (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of _) (ModuleCat.{0} ℂ) p)
    (twistSumSheafBiconeIsBilimit (n := n) k))

/-- The isomorphism with the biproduct is given by the maps induced by the projections onto the
summands. -/
@[simp]
theorem holomorphicSectionCechCohomologyTwistSumIso_hom :
    (holomorphicSectionCechCohomologyTwistSumIso (n := n) k p).hom =
      biproduct.lift fun l ↦
        (Topology.cechCohomology (TopCat.of _) (ModuleCat.{0} ℂ) p).map
          (twistSumSheafProj k l).hom := by
  rw [holomorphicSectionCechCohomologyTwistSumIso, biproduct.uniqueUpToIso_hom]
  rfl

/-- The inverse of the isomorphism with the biproduct is given by the maps induced by the
inclusions of the summands. -/
@[simp]
theorem holomorphicSectionCechCohomologyTwistSumIso_inv :
    (holomorphicSectionCechCohomologyTwistSumIso (n := n) k p).inv =
      biproduct.desc fun l ↦
        (Topology.cechCohomology (TopCat.of _) (ModuleCat.{0} ℂ) p).map
          (twistSumSheafSingle k l).hom := by
  rw [holomorphicSectionCechCohomologyTwistSumIso, biproduct.uniqueUpToIso_inv]
  rfl

end Single

/-- The Čech cohomology `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` vanishes when `Hᵖ(ℂℙⁿ, 𝒪(k l))` vanishes for every
summand. -/
theorem isZero_holomorphicSectionCechCohomology_twistSumCore {p : ℕ}
    (h : ∀ l, IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p)) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p) := by
  classical
  exact (isBilimitOfPreserves (sheafToPresheaf
    (Opens.grothendieckTopology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))) _ ⋙
    Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p)
      (twistSumSheafBiconeIsBilimit k)).isLimit.isZero_pt (Functor.isZero _ fun ⟨l⟩ ↦ h l)

/-- **`H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` when every `k l ≥ -1`.** The first Čech cohomology of the sheaf of
holomorphic sections of the split bundle `⨁ₗ 𝒪(k l)` on the complex projective line vanishes as
soon as every twist `k l` is at least `-1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    (hk : ∀ l, -1 ≤ k l) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := 1) k).Fiber 1) :=
  isZero_holomorphicSectionCechCohomology_twistSumCore fun l ↦
    isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le (k l) (hk l)

end Projectivization
