/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.RingTheory.Flat.NonZeroDivisors

/-!
# Flatness of scheme-theoretic images over a Bezout domain

Let `R` be a Bezout domain, for instance a discrete valuation ring, with an injective map to a
field `K`, and let `X` be a scheme over `R`. If a quasi-compact morphism `f : Y ⟶ X` comes from a
scheme `Y` over `K`, then the scheme-theoretic image of `f` is flat over `R`.

On an affine open `U` of `X`, the sections of the image over `U` form the quotient of `Γ(X, U)`
by the kernel of `Γ(X, U) → Γ(Y, f⁻¹ U)`, so they embed into a `K`-algebra. Nonzero elements of
`R` are therefore nonzerodivisors on them, which over a Bezout domain is flatness
(`Module.Flat.flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout`).

Over a discrete valuation ring this is the flatness of the scheme-theoretic closure of the
generic fibre: closing up a subscheme of `X_K` inside `X` yields a flat model of it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_imageι_comp`: the scheme-theoretic image of a
  quasi-compact morphism from a scheme over `K` to a scheme over `R` is flat over `R`.

## References

* [The Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539), flatness over
  valuation rings, generalized in Mathlib to Bezout domains.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

/-- Let `R` be a Bezout domain with an injective map to a field `K`, let `g : X ⟶ Spec R`, and
let `f : Y ⟶ X` be quasi-compact with `f ≫ g` factoring through `Spec K`. Then the
scheme-theoretic image of `f` is flat over `R`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.flat_imageι_comp {R K : Type u} [CommRing R]
    [IsDomain R] [IsBezout R] [Field K] [Algebra R K] [FaithfulSMul R K]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] (g : X ⟶ Spec (.of R))
    (toK : Y ⟶ Spec (.of K))
    (h : f ≫ g = toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Flat (f.imageι ≫ g) := by
  -- The image is covered by the affine opens `imageι⁻¹ U` for `U` affine in `X`.
  let U : X.affineOpens → f.image.affineOpens := fun U ↦ ⟨f.imageι ⁻¹ᵁ U, U.2.preimage _⟩
  have hU : ⨆ V, (U V : f.image.Opens) = ⊤ := by
    simp only [U]
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine HasRingHomProperty.of_iSup_eq_top U hU fun V ↦ ?_
  rw [← RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]
  set φ := ((f.imageι ≫ g).appLE ⊤ (U V).1 le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  set ψ := (f.toImage.app (U V).1).hom
  have hψ : Function.Injective ψ := f.toImage_app_injective V
  -- Composed with the injection `ψ` into sections over `Y`, the map `φ` factors through `K`.
  have key : ψ.comp φ = (toK.appLE ⊤ (f.toImage ⁻¹ᵁ (U V).1) le_top).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap R K)) := by
    have hk : ∀ (k : Y ⟶ Spec (.of R)) (_ : k = toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (e : f.toImage ⁻¹ᵁ (U V).1 ≤ k ⁻¹ᵁ ⊤), k.appLE ⊤ _ e =
          (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫ toK.appLE ⊤ _ le_top := by
      rintro _ rfl e
      rw [Scheme.Hom.comp_appLE]
      -- `app ⊤` is `appTop`, and the preimage of `⊤` is `⊤` by definition.
      rfl
    have e1 : (f.imageι ≫ g).appLE ⊤ (U V).1 le_top ≫ f.toImage.app (U V).1 =
        (f.toImage ≫ f.imageι ≫ g).appLE ⊤ (f.toImage ⁻¹ᵁ (U V).1) le_top := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))
    ext x
    have h1 := congrArg (fun k ↦ k.hom ((Scheme.ΓSpecIso (.of R)).inv.hom x))
      (e1.trans (hk _ (by rw [f.toImage_imageι_assoc, h]) le_top))
    have h2 := congrArg (fun k ↦ (toK.appLE ⊤ (f.toImage ⁻¹ᵁ (U V).1) le_top).hom (k.hom x)) e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2 ⊢
    exact h1.trans h2.symm
  algebraize [φ]
  refine (Module.Flat.flat_iff_algebraMap_mem_nonZeroDivisors_of_isBezout).2 fun r hr ↦ ?_
  -- A nonzero `r` becomes a unit over `Y`, hence a nonzerodivisor on the image.
  have hunit : IsUnit (ψ (φ r)) := by
    rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.comp_apply]
    exact ((isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective R K)).mpr hr)).map _).map _
  rw [mem_nonZeroDivisors_iff_right]
  intro a ha
  apply hψ
  rw [map_zero, ← hunit.mul_left_eq_zero, ← map_mul]
  exact (congrArg ψ ha).trans (map_zero ψ)

end TauCeti
