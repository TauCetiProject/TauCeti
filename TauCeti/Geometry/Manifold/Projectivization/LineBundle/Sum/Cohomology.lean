/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Cech
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum

/-!
# Sections and Čech cohomology of split bundles on projective space

On `ℂℙⁿ`, the sheaf of holomorphic sections of the split bundle `⨁ₗ 𝒪(k l)`
(`Projectivization.twistSumCore k`) is the biproduct of the sheaves of sections of its summands,
with the projections and inclusions of the summands
(`Projectivization.twistSumCoreSectionBiconeIsBilimit`). Čech cohomology is an additive functor of
the sheaf, so `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) ≅ ⨁ₗ Hᵖ(ℂℙⁿ, 𝒪(k l))` in every degree
(`Projectivization.twistSumCoreCechCohomologyIso`), and `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` vanishes when every
`Hᵖ(ℂℙⁿ, 𝒪(k l))` does (`Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore`).

The construction follows the binary direct sum (`TauCeti.holomorphicSectionSheaf.prodBicone`,
`TauCeti.holomorphicSectionCechCohomology.prodBicone`).
`Projectivization.twistSumCore` is glued directly from transition functions rather than as an
iterated `Bundle.Prod`, so the binary isomorphisms do not apply to it.

## Main declarations

* `Projectivization.twistSumCoreSectionBicone`: the sheaf of sections of `⨁ₗ 𝒪(k l)` with the
  projections `Projectivization.twistSumCoreSectionProj` and inclusions
  `Projectivization.twistSumCoreSectionSingle` of the summands, a bilimit bicone.
* `Projectivization.twistSumCoreCechCohomologyIso`: `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) ≅ ⨁ₗ Hᵖ(ℂℙⁿ, 𝒪(k l))`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore`: the vanishing of
  `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` when that of every summand vanishes.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ} {κ : Type} [Fintype κ] (k : κ → ℤ)

/-- The projection of `⨁ₗ 𝒪(k l)` onto its summand `𝒪(k l)`, on sheaves of holomorphic
sections. -/
def twistSumCoreSectionProj (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.proj l)
    (contMDiff_twistSumCore_apply k l)

/-- The projection onto the summand `l` takes a section of `⨁ₗ 𝒪(k l)` to its component `l`. -/
@[simp]
theorem twistSumCoreSectionProj_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumCoreSectionProj k l).hom.app U s x = s x l :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

section Single

variable [DecidableEq κ]

/-- The inclusion of the summand `𝒪(k l)` into `⨁ₗ 𝒪(k l)`, on sheaves of holomorphic
sections. -/
def twistSumCoreSectionSingle (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.single ℂ (fun _ ↦ ℂ) l)
    (contMDiff_twistSumCore_single k l)

/-- The inclusion of the summand `l` places a section of `𝒪(k l)` in the component `l`. -/
@[simp]
theorem twistSumCoreSectionSingle_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumCoreSectionSingle k l).hom.app U s x = Pi.single (M := fun _ ↦ ℂ) l (s x) :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

/-- The inclusion of a summand of `⨁ₗ 𝒪(k l)` followed by the projection onto the same summand is
the identity. -/
@[reassoc (attr := simp)]
theorem twistSumCoreSectionSingle_comp_twistSumCoreSectionProj_self (l : κ) :
    twistSumCoreSectionSingle (n := n) k l ≫ twistSumCoreSectionProj k l = 𝟙 _ :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.comp_hom_app_apply, twistSumCoreSectionProj_app_apply,
      twistSumCoreSectionSingle_app_apply, holomorphicSectionSheaf.id_hom_app_apply]
    exact Pi.single_eq_same (M := fun _ ↦ ℂ) l (s x)

/-- The inclusion of a summand of `⨁ₗ 𝒪(k l)` followed by the projection onto a different summand
is zero. -/
@[reassoc (attr := simp)]
theorem twistSumCoreSectionSingle_comp_twistSumCoreSectionProj_of_ne {l l' : κ} (h : l ≠ l') :
    twistSumCoreSectionSingle (n := n) k l ≫ twistSumCoreSectionProj k l' = 0 :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.comp_hom_app_apply, twistSumCoreSectionProj_app_apply,
      twistSumCoreSectionSingle_app_apply, holomorphicSectionSheaf.zero_hom_app_apply]
    exact Pi.single_eq_of_ne' (M := fun _ ↦ ℂ) h (s x)

/-- **The sheaf of sections of `⨁ₗ 𝒪(k l)`.** The sheaf of holomorphic sections of the split
bundle `⨁ₗ 𝒪(k l)` on `ℂℙⁿ` (`Projectivization.twistSumCore k`), with the projections
`Projectivization.twistSumCoreSectionProj` onto the sheaves of sections of the summands `𝒪(k l)`
and the inclusions `Projectivization.twistSumCoreSectionSingle`, as a bicone. -/
-- Exposed so that the cone point is visibly the sheaf of the split bundle: otherwise the
-- Čech cohomology of the bicone cannot be stated as that of `twistSumCore k`.
@[expose, simps]
def twistSumCoreSectionBicone :
    Bicone fun l ↦
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber where
  pt := holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber
  «π» := twistSumCoreSectionProj k
  ι := twistSumCoreSectionSingle k
  ι_π l l' := by
    split_ifs with h
    · subst h
      exact twistSumCoreSectionSingle_comp_twistSumCoreSectionProj_self k l
    · exact twistSumCoreSectionSingle_comp_twistSumCoreSectionProj_of_ne k h

/-- The projections of `⨁ₗ 𝒪(k l)` onto its summands followed by the inclusions of the summands
add up to the identity of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)`. -/
theorem sum_twistSumCoreSectionProj_comp_twistSumCoreSectionSingle :
    ∑ l, twistSumCoreSectionProj (n := n) k l ≫ twistSumCoreSectionSingle k l = 𝟙 _ :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.sum_hom_app_apply, holomorphicSectionSheaf.id_hom_app_apply]
    refine (Finset.sum_congr rfl fun l _ ↦ ?_).trans (Finset.univ_sum_single (s x))
    rw [holomorphicSectionSheaf.comp_hom_app_apply, twistSumCoreSectionSingle_app_apply,
      twistSumCoreSectionProj_app_apply]

/-- **The sheaf of sections of `⨁ₗ 𝒪(k l)` is the biproduct of the sheaves of sections of the
summands.** The projections followed by the inclusions add up to the identity. -/
def twistSumCoreSectionBiconeIsBilimit : (twistSumCoreSectionBicone (n := n) k).IsBilimit :=
  isBilimitOfTotal _ (sum_twistSumCoreSectionProj_comp_twistSumCoreSectionSingle k)

/-- **Čech cohomology of `⨁ₗ 𝒪(k l)`.** The Čech cohomology of the sheaf of holomorphic sections
of the split bundle `⨁ₗ 𝒪(k l)` on `ℂℙⁿ`, with the maps induced by the projections onto the
summands and the inclusions of the summands, as a bicone over the cohomologies of the summands:
the image of `Projectivization.twistSumCoreSectionBicone` under Čech cohomology. -/
-- Exposed so that the cone point is visibly the cohomology of the split bundle.
@[expose]
def twistSumCoreCechCohomologyBicone (p : ℕ) :
    Bicone fun l ↦
      holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
        (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p :=
  (sheafToPresheaf _ _ ⋙ Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))
    (ModuleCat.{0} ℂ) p).mapBicone (twistSumCoreSectionBicone k)

@[simp]
theorem twistSumCoreCechCohomologyBicone_pt (p : ℕ) :
    (twistSumCoreCechCohomologyBicone (n := n) k p).pt =
      holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p :=
  (rfl)

@[simp]
theorem twistSumCoreCechCohomologyBicone_π (p : ℕ) (l : κ) :
    (twistSumCoreCechCohomologyBicone (n := n) k p).π l =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p).map
        ((twistSumCoreSectionBicone k).π l).hom :=
  (rfl)

@[simp]
theorem twistSumCoreCechCohomologyBicone_ι (p : ℕ) (l : κ) :
    (twistSumCoreCechCohomologyBicone (n := n) k p).ι l =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p).map
        ((twistSumCoreSectionBicone k).ι l).hom :=
  (rfl)

/-- **Additivity.** The Čech cohomology of `⨁ₗ 𝒪(k l)` is the biproduct of the cohomologies of
the summands, since Čech cohomology is an additive functor of the sheaf. -/
def twistSumCoreCechCohomologyBiconeIsBilimit (p : ℕ) :
    (twistSumCoreCechCohomologyBicone (n := n) k p).IsBilimit :=
  isBilimitOfPreserves _ (twistSumCoreSectionBiconeIsBilimit k)

/-- **`Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) ≅ ⨁ₗ Hᵖ(ℂℙⁿ, 𝒪(k l))`.** The Čech cohomology of the split bundle is
isomorphic to the biproduct of the cohomologies of its summands. -/
def twistSumCoreCechCohomologyIso (p : ℕ) :
    holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p ≅
      ⨁ fun l ↦ holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
        (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p :=
  biproduct.uniqueUpToIso _ (twistSumCoreCechCohomologyBiconeIsBilimit k p)

/-- The isomorphism with the biproduct is given by the maps induced by the projections onto the
summands. -/
@[simp]
theorem twistSumCoreCechCohomologyIso_hom (p : ℕ) :
    (twistSumCoreCechCohomologyIso (n := n) k p).hom =
      biproduct.lift (twistSumCoreCechCohomologyBicone k p).π :=
  (rfl)

/-- The inverse of the isomorphism with the biproduct is given by the maps induced by the
inclusions of the summands. -/
@[simp]
theorem twistSumCoreCechCohomologyIso_inv (p : ℕ) :
    (twistSumCoreCechCohomologyIso (n := n) k p).inv =
      biproduct.desc (twistSumCoreCechCohomologyBicone k p).ι :=
  (rfl)

end Single

/-- The Čech cohomology of `⨁ₗ 𝒪(k l)` in degree `p` vanishes when that of every summand does. -/
theorem isZero_holomorphicSectionCechCohomology_twistSumCore {p : ℕ}
    (h : ∀ l, IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p)) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p) := by
  classical
  exact (twistSumCoreCechCohomologyBiconeIsBilimit k p).isLimit.isZero_pt
    (Functor.isZero _ fun j ↦ h j.as)

end Projectivization
