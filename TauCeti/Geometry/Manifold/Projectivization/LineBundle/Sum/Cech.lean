/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Cech
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum.Basic
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` and its Čech cohomology

On complex projective space `ℂℙⁿ`, the sheaf of holomorphic sections of a finite direct sum
`⨁ₗ 𝒪(k l)` (`Projectivization.twistSumCore k`) is the biproduct of the sheaves of holomorphic
sections of the summands (`Projectivization.twistSumBiconeIsBilimit`), by the projections onto the
summands and the inclusions of the summands. Čech cohomology is additive, so `Hᵐ(ℂℙⁿ, ⨁ₗ 𝒪(k l))`
vanishes exactly when every `Hᵐ(ℂℙⁿ, 𝒪(k l))` does
(`Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore_iff`).

This is the binary direct-sum API `TauCeti.holomorphicSectionSheaf.prodBicone` and
`TauCeti.holomorphicSectionSheaf.prodBiconeIsBilimit` for the single vector-bundle core
`twistSumCore k`, whose fibre is `κ → ℂ` rather than an iterated `×ᵇ`.

## Main declarations

* `Projectivization.twistSumSectionProj`, `Projectivization.twistSumSectionSingle` and
  `Projectivization.twistSumBicone`: the projections onto and inclusions of the summands of
  `⨁ₗ 𝒪(k l)` on sheaves of holomorphic sections; `Projectivization.twistSumBiconeIsBilimit`: the
  sheaf of `⨁ₗ 𝒪(k l)` is their biproduct.
* `Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore_iff`:
  `Hᵐ(ℂℙⁿ, ⨁ₗ 𝒪(k l)) = 0` if and only if every `Hᵐ(ℂℙⁿ, 𝒪(k l)) = 0`.

-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (k : κ → ℤ)

/-- The projection of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` onto the sheaf of
holomorphic sections of the summand `𝒪(k l)`, taking a section to its component `l`. -/
def twistSumSectionProj (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.proj l)
    (contMDiff_twistSumCore_apply k l)

/-- The inclusion of the sheaf of holomorphic sections of the summand `𝒪(k l)` into the sheaf of
holomorphic sections of `⨁ₗ 𝒪(k l)`, placing a section in the summand `l`. -/
def twistSumSectionSingle (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.single ℂ (fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_single k l)

variable {k}

omit [DecidableEq κ] in
@[simp]
theorem twistSumSectionProj_app_apply (l : κ) {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumSectionProj k l).hom.app U s x = s x l :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

@[simp]
theorem twistSumSectionSingle_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumSectionSingle k l).hom.app U s x = Pi.single (M := fun _ : κ ↦ ℂ) l (s x) :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

@[reassoc (attr := simp)]
theorem twistSumSectionSingle_comp_twistSumSectionProj_self (l : κ) :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l = 𝟙 _ :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.comp_app_apply, twistSumSectionProj_app_apply,
      twistSumSectionSingle_app_apply, holomorphicSectionSheaf.id_app_apply]
    -- the fibres of `twistCore` are `ℂ` only up to unfolding, so `Pi.single` is evaluated here
    exact Pi.single_eq_same (M := fun _ : κ ↦ ℂ) l (s x)

@[reassoc (attr := simp)]
theorem twistSumSectionSingle_comp_twistSumSectionProj_of_ne {l l' : κ} (h : l ≠ l') :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l' = 0 :=
  holomorphicSectionSheaf.hom_ext fun _ s x ↦ by
    rw [holomorphicSectionSheaf.comp_app_apply, twistSumSectionProj_app_apply,
      twistSumSectionSingle_app_apply, holomorphicSectionSheaf.zero_app_apply]
    -- the fibres of `twistCore` are `ℂ` only up to unfolding, so `Pi.single` is evaluated here
    exact Pi.single_eq_of_ne' (M := fun _ : κ ↦ ℂ) h (s x)

/-- The projections onto the summands followed by the inclusions of the summands add up to the
identity of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)`. -/
theorem sum_twistSumSectionProj_comp_twistSumSectionSingle :
    ∑ l, twistSumSectionProj (n := n) k l ≫ twistSumSectionSingle k l = 𝟙 _ := by
  refine holomorphicSectionSheaf.hom_ext fun U s x ↦ ?_
  rw [holomorphicSectionSheaf.sum_app_apply]
  refine (Finset.sum_congr rfl fun l _ ↦ ?_).trans (Finset.univ_sum_single (s x))
  -- the composite takes the component `l` of `s x` and places it in the summand `l`
  exact (twistSumSectionSingle_app_apply l _ x).trans
    (congrArg (Pi.single (M := fun _ : κ ↦ ℂ) l) (twistSumSectionProj_app_apply l s x))

variable (k)

/-- The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)`, with the morphisms induced by the
projections onto the summands and the inclusions of the summands, as a bicone over the sheaves
of holomorphic sections of the summands `𝒪(k l)`. -/
-- Exposed so that the cone point is visibly the sheaf of the split bundle: otherwise the legs
-- cannot be stated as `twistSumSectionProj` and `twistSumSectionSingle` in the simp lemmas.
@[expose, simps]
def twistSumBicone :
    Bicone fun l ↦
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  Bicone.mk
    (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber)
    (twistSumSectionProj k) (twistSumSectionSingle k) fun l l' ↦ by
      split_ifs with h
      · subst h
        simp
      · exact twistSumSectionSingle_comp_twistSumSectionProj_of_ne h

/-- **The sheaf of a split bundle is a biproduct.** The sheaf of holomorphic sections of
`⨁ₗ 𝒪(k l)` on `ℂℙⁿ` is the biproduct of the sheaves of holomorphic sections of the
summands `𝒪(k l)`. -/
def twistSumBiconeIsBilimit : (twistSumBicone (n := n) k).IsBilimit :=
  isBilimitOfTotal _ sum_twistSumSectionProj_comp_twistSumSectionSingle

omit [DecidableEq κ] in
/-- **The cohomology of a split bundle vanishes exactly when that of every summand does.** The
Čech cohomology `Hᵐ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` of the sheaf of holomorphic sections of a finite direct sum
of the line bundles `𝒪(k l)` is zero if and only if every `Hᵐ(ℂℙⁿ, 𝒪(k l))` is zero, since Čech
cohomology is additive and so carries the biproduct `Projectivization.twistSumBiconeIsBilimit`
to a biproduct. -/
theorem isZero_holomorphicSectionCechCohomology_twistSumCore_iff (m : ℕ) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber m) ↔
      ∀ l, IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
        (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber m) := by
  classical
  -- Čech cohomology of the sheaves carries the bilimit bicone to a bilimit bicone
  exact (isBilimitOfPreserves (sheafToPresheaf
    (Opens.grothendieckTopology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))) (ModuleCat.{0} ℂ) ⋙
      Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) m)
    (twistSumBiconeIsBilimit k)).isZero_pt_iff

end Projectivization
