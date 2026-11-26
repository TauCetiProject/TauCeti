/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum

/-!
# Čech cohomology of the split bundles `⨁ₗ 𝒪(k l)` on complex projective space

For a finite family of integers `k : κ → ℤ`, the split bundle `⨁ₗ 𝒪(k l)` on `ℂℙⁿ`
(`Projectivization.twistSumCore k`) is glued along diagonal transition functions, so its
holomorphic sections are families of holomorphic sections of the summands `𝒪(k l)`. This file
makes this precise on sheaves and passes it to Čech cohomology:

* the projections onto the summands and the inclusions of the summands
  (`Projectivization.twistSumSectionProj`, `Projectivization.twistSumSectionSingle`) exhibit the
  sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` as the biproduct of the sheaves of holomorphic
  sections of the `𝒪(k l)` (`Projectivization.twistSumSectionBiconeIsBilimit`);
* since Čech cohomology is an additive functor of the sheaf, in every degree `p` the cohomology
  `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` is the biproduct of the `Hᵖ(ℂℙⁿ, 𝒪(k l))`
  (`Projectivization.twistSumCechIso`), and it vanishes when every summand does
  (`Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore`).

On the projective line this gives `H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` as soon as every `k l ≥ -1`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`), from
the vanishing for a single line bundle
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le`). This is
the cohomological form of the regularity of a holomorphic sphere `u` whose pulled-back tangent
bundle splits as `u* TX ≅ ⨁ₗ 𝒪(aₗ)` with all `aₗ ≥ -1`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the vanishing of `H¹(ℙ¹, u* T_X)`.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ} {κ : Type} [Fintype κ] (k : κ → ℤ)

/-! ### Sheaves of holomorphic sections -/

/-- The projection of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` onto the sheaf of
holomorphic sections of the summand `𝒪(k l)`, taking the component `l` of a section. -/
def twistSumSectionProj (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.proj l)
    (contMDiff_twistSumCore_apply k l)

@[simp]
theorem twistSumSectionProj_app_apply (l : κ) {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumSectionProj k l).hom.app U s x = (s x : κ → ℂ) l :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

variable [DecidableEq κ]

/-- The inclusion of the sheaf of holomorphic sections of the summand `𝒪(k l)` into the sheaf of
holomorphic sections of `⨁ₗ 𝒪(k l)`, placing a section in the component `l`. -/
def twistSumSectionSingle (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.single ℂ (fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_single k l)

@[simp]
theorem twistSumSectionSingle_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber).obj.obj U) (x : ↥(unop U)) :
    ((twistSumSectionSingle k l).hom.app U s x : κ → ℂ) = Pi.single l (s x : ℂ) :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

/-- The inclusion of a summand followed by the projection onto the same summand is the
identity. -/
@[reassoc (attr := simp)]
theorem twistSumSectionSingle_twistSumSectionProj (l : κ) :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l = 𝟙 _ := by
  refine holomorphicSectionSheaf.hom_ext fun _ s x ↦ ?_
  simp only [holomorphicSectionSheaf.comp_hom_app_apply, twistSumSectionProj_app_apply,
    twistSumSectionSingle_app_apply, holomorphicSectionSheaf.id_hom_app_apply]
  exact Pi.single_eq_same (M := fun _ : κ ↦ ℂ) l (s x)

/-- The inclusion of a summand followed by the projection onto another summand is zero. -/
theorem twistSumSectionSingle_twistSumSectionProj_of_ne {l l' : κ} (h : l ≠ l') :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l' = 0 := by
  refine holomorphicSectionSheaf.hom_ext fun _ s x ↦ ?_
  simp only [holomorphicSectionSheaf.comp_hom_app_apply, twistSumSectionProj_app_apply,
    twistSumSectionSingle_app_apply]
  exact (Pi.single_eq_of_ne' (M := fun _ : κ ↦ ℂ) h (s x)).trans
    (holomorphicSectionSheaf.zero_apply (I := 𝓘(ℂ, Fin n → ℂ))
      (V := (twistCore (𝕜 := ℂ) (n := n) (k l')).Fiber) x).symm

/-- The projections onto the summands followed by the inclusions of the summands add up to the
identity of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)`. -/
theorem sum_twistSumSectionProj_twistSumSectionSingle :
    ∑ l, twistSumSectionProj (n := n) k l ≫ twistSumSectionSingle k l = 𝟙 _ := by
  refine holomorphicSectionSheaf.hom_ext fun _ s x ↦ ?_
  simp only [holomorphicSectionSheaf.sum_hom_app_apply, holomorphicSectionSheaf.comp_hom_app_apply,
    twistSumSectionProj_app_apply, twistSumSectionSingle_app_apply,
    holomorphicSectionSheaf.id_hom_app_apply]
  exact Finset.univ_sum_single (s x : κ → ℂ)

variable (n)

/-- The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` on `ℂℙⁿ`, with the projections onto and the
inclusions of the sheaves of holomorphic sections of the summands `𝒪(k l)`, as a bicone. -/
-- Exposed so that the cone point and the legs are visibly the sheaf of sections of the sum and the
-- maps `twistSumSectionProj` and `twistSumSectionSingle`, as stated by the lemmas below.
@[expose]
def twistSumSectionBicone :
    Bicone fun l ↦
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  Bicone.mk
    (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber)
    (twistSumSectionProj k) (twistSumSectionSingle k) fun l l' ↦ by
      split_ifs with h
      · subst h
        simp
      · exact twistSumSectionSingle_twistSumSectionProj_of_ne k h

@[simp]
theorem twistSumSectionBicone_pt :
    (twistSumSectionBicone n k).pt =
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  (rfl)

@[simp]
theorem twistSumSectionBicone_π (l : κ) :
    (twistSumSectionBicone n k).π l = twistSumSectionProj k l :=
  (rfl)

@[simp]
theorem twistSumSectionBicone_ι (l : κ) :
    (twistSumSectionBicone n k).ι l = twistSumSectionSingle k l :=
  (rfl)

/-- **Sections of a split bundle.** The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` is the
biproduct of the sheaves of holomorphic sections of the summands `𝒪(k l)`. -/
def twistSumSectionBiconeIsBilimit : (twistSumSectionBicone n k).IsBilimit :=
  isBilimitOfTotal _ (sum_twistSumSectionProj_twistSumSectionSingle k)

/-! ### Čech cohomology -/

/-- The Čech cohomology `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))`, with the maps induced by the projections onto and
the inclusions of the summands, as a bicone over the cohomologies `Hᵖ(ℂℙⁿ, 𝒪(k l))`: the image of
`Projectivization.twistSumSectionBicone` under Čech cohomology. -/
-- Exposed so that the cone point is visibly the cohomology of the split bundle: otherwise the legs
-- cannot be stated as the maps induced by the sheaf-level projections and inclusions below.
@[expose]
def twistSumCechBicone (p : ℕ) :
    Bicone fun l ↦ holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p :=
  (sheafToPresheaf _ _ ⋙
    Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p).mapBicone
      (twistSumSectionBicone n k)

@[simp]
theorem twistSumCechBicone_pt (p : ℕ) :
    (twistSumCechBicone n k p).pt = holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p :=
  (rfl)

@[simp]
theorem twistSumCechBicone_π (p : ℕ) (l : κ) :
    (twistSumCechBicone n k p).π l =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p).map
        (twistSumSectionProj k l).hom :=
  (rfl)

@[simp]
theorem twistSumCechBicone_ι (p : ℕ) (l : κ) :
    (twistSumCechBicone n k p).ι l =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) p).map
        (twistSumSectionSingle k l).hom :=
  (rfl)

/-- **Additivity.** In every degree, the Čech cohomology of `⨁ₗ 𝒪(k l)` is the biproduct of the
Čech cohomologies of the summands `𝒪(k l)`, since Čech cohomology is an additive functor of the
sheaf and so preserves the biproduct `Projectivization.twistSumSectionBiconeIsBilimit`. -/
def twistSumCechBiconeIsBilimit (p : ℕ) : (twistSumCechBicone n k p).IsBilimit :=
  isBilimitOfPreserves _ (twistSumSectionBiconeIsBilimit n k)

/-- The Čech cohomology `Hᵖ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` is isomorphic to the biproduct `⨁` of the
cohomologies `Hᵖ(ℂℙⁿ, 𝒪(k l))`. -/
def twistSumCechIso (p : ℕ) :
    holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p ≅
      ⨁ fun l ↦ holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
        (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p :=
  biproduct.uniqueUpToIso _ (twistSumCechBiconeIsBilimit n k p)

omit [DecidableEq κ]
variable {n k}

/-- The Čech cohomology of `⨁ₗ 𝒪(k l)` in degree `p` vanishes when the cohomology of every
summand `𝒪(k l)` in degree `p` does. -/
theorem isZero_holomorphicSectionCechCohomology_twistSumCore {p : ℕ}
    (h : ∀ l, IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber p)) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber p) := by
  classical
  -- The identity of the cohomology of the sum is the sum of maps factoring through the summands.
  have htotal := IsBilimit.total (twistSumCechBiconeIsBilimit n k p)
  refine (IsZero.iff_id_eq_zero _).2 (htotal.symm.trans (Finset.sum_eq_zero fun l _ ↦ ?_))
  rw [(h l).eq_of_tgt ((twistSumCechBicone n k p).π l) 0, zero_comp]

/-- **`H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` when every `k l ≥ -1`.** The first Čech cohomology of the sheaf
of holomorphic sections of the split bundle `⨁ₗ 𝒪(k l)` on the complex projective line vanishes
as soon as every twist `k l` is at least `-1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    (hk : ∀ l, -1 ≤ k l) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := 1) k).Fiber 1) :=
  isZero_holomorphicSectionCechCohomology_twistSumCore fun l ↦
    isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le (k l) (hk l)

end Projectivization
