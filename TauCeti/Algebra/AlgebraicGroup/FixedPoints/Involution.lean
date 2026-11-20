/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Antipode
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Product
public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Basic
public import TauCeti.Algebra.Bialgebra.TensorProduct
public import TauCeti.CategoryTheory.Aut.Involution

/-!
# Fixed-point closed subgroup schemes of involutions

Specializes `TauCeti.CommHopfAlgCat.fixedPoints` to `ℤ/2`-actions induced by involutions
(`TauCeti.involutionAction`), including the factor swap on `H ⊗[R] H` (diagonal `H`) and inversion
on cocommutative `H : CommHopfAlgCat R` (`[Coalgebra.IsCocomm R H]`).

## Main declarations

* `TauCeti.CommHopfAlgCat.range_mapDomain_mkFixedPoints_involutionAction`: `A`-points of
  `involutionAction f hf` are `{ g | BialgHom.mapDomain f.hom g = g }`.
* `CommHopfAlgCat.fixedPointsOfSwapIso`, `CommHopfAlgCat.swapAction`,
  `CommHopfAlgCat.fixedPointsSwapActionIso`: swap fixed points on `H ⊗[R] H` are isomorphic to `H`.
* `CommHopfAlgCat.antipodeAction`, `CommHopfAlgCat.range_mapDomain_mkFixedPoints_antipodeAction`:
  for `[Coalgebra.IsCocomm R H]`, inversion fixed `A`-points are `{ g | g⁻¹ = g }`.
-/

public section

open CategoryTheory TensorProduct WithConv TauCeti TauCeti.CommHopfAlgCat

universe u v w w'

namespace TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}

/-- On `A`-points, the fixed points of `involutionAction f hf` are the points fixed by `f`. -/
theorem range_mapDomain_mkFixedPoints_involutionAction (f : H ⟶ H) (hf : f ≫ f = 𝟙 H)
    (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A)
        (mkFixedPoints fun θ ↦ (involutionAction f hf θ).asIso.hom).hom) =
      {g | BialgHom.mapDomain (A := A) f.hom g = g} := by
  rw [range_mapDomain_mkFixedPoints]; ext g
  refine ⟨fun hg ↦ by simpa [involutionAction_ofAdd_one] using hg (.ofAdd 1), fun hg θ ↦ ?_⟩
  rcases involutionAction_hom_eq_id_or f hf θ with hθ | hθ
  · rw [hθ, TauCeti.CommHopfAlgCat.hom_id_eq_bialgHom_id, BialgHom.mapDomain_id, MonoidHom.id_apply]
  · rwa [hθ]

end TauCeti.CommHopfAlgCat

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

private theorem comp_mulBialgHom_of_eq_id_or_swapEnd (H : CommHopfAlgCat.{v} R) {ι : Type w}
    {f : ι → (CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H))}
    (hf : ∀ i, f i = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) ∨ f i = swapEnd H) (i : ι) :
    f i ≫ CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) =
      CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) := by
  rcases hf i with hi | hi <;> simp [hi]

/-- **Fixed points of the factor swap on `G × G` are the diagonal `G`.** -/
noncomputable def fixedPointsOfSwapIso (H : CommHopfAlgCat.{v} R) {ι : Type w}
    {f : ι → (CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H))}
    (hswap : ∃ i, f i = swapEnd H)
    (hf : ∀ i, f i = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) ∨ f i = swapEnd H) :
    fixedPoints f ≅ H where
  hom := liftFixedPoints (CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H))
    (comp_mulBialgHom_of_eq_id_or_swapEnd H hf)
  inv := CommHopfAlgCat.ofHom
    (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)) ≫ mkFixedPoints f
  hom_inv_id := by
    apply mkQuotient_hom_ext
    rw [← Category.assoc, mkFixedPoints_comp_liftFixedPoints, Category.comp_id]
    obtain ⟨i₀, hi₀⟩ := hswap
    have hmk_swap : swapEnd H ≫ mkFixedPoints f = mkFixedPoints f := by
      rw [← hi₀]; exact comp_mkFixedPoints f i₀
    refine CommHopfAlgCat.hom_ext (BialgHom.coe_toAlgHom_injective <|
      Algebra.TensorProduct.ext' fun x y ↦ ?_)
    have hswap_y :
        (Bialgebra.Quotient.mkBialgHom (R := R) (fixedPointsHopfIdeal f).toIdeal)
            ((1 : H) ⊗ₜ[R] y) =
          (Bialgebra.Quotient.mkBialgHom (R := R) (fixedPointsHopfIdeal f).toIdeal)
            (y ⊗ₜ[R] (1 : H)) := by
      have h := congrArg (fun m : _ ⟶ fixedPoints f ↦ m.hom (y ⊗ₜ[R] (1 : H))) hmk_swap
      rwa [CommHopfAlgCat.hom_comp, BialgHom.comp_apply, swapEnd_hom, hom_mkQuotient] at h
    have hxy : (x ⊗ₜ[R] y : H ⊗[R] H) = (x ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] y) := by simp
    have hl : ((x * y) ⊗ₜ[R] (1 : H) : H ⊗[R] H) = (x ⊗ₜ[R] (1 : H)) * (y ⊗ₜ[R] (1 : H)) := by simp
    simp only [CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom, CommHopfAlgCat.hom_ofHom, Bialgebra.coe_mulBialgHom,
      LinearMap.mul'_apply, TauCeti.Bialgebra.TensorProduct.includeLeft_apply]
    rw [hl, map_mul, hxy, map_mul, hswap_y]
  inv_hom_id := by
    rw [Category.assoc, mkFixedPoints_comp_liftFixedPoints]
    exact CommHopfAlgCat.hom_ext (by ext x; simp)

/-- Composing `mkFixedPoints f` with `(fixedPointsOfSwapIso H hswap hf).hom` is `mulBialgHom`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsOfSwapIso_hom (H : CommHopfAlgCat.{v} R) {ι : Type w}
    {f : ι → (CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H))}
    (hswap : ∃ i, f i = swapEnd H)
    (hf : ∀ i, f i = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) ∨ f i = swapEnd H) :
    mkFixedPoints f ≫ (fixedPointsOfSwapIso H hswap hf).hom =
      CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) := by
  rw [fixedPointsOfSwapIso, mkFixedPoints_comp_liftFixedPoints]

/-- The inverse of `fixedPointsOfSwapIso H hswap hf` is `includeLeft ≫ mkFixedPoints f`. -/
@[simp]
theorem fixedPointsOfSwapIso_inv (H : CommHopfAlgCat.{v} R) {ι : Type w}
    {f : ι → (CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H))}
    (hswap : ∃ i, f i = swapEnd H)
    (hf : ∀ i, f i = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) ∨ f i = swapEnd H) :
    (fixedPointsOfSwapIso H hswap hf).inv =
      CommHopfAlgCat.ofHom
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)) ≫
        mkFixedPoints f := by rfl

/-- The `ℤ/2`-action on `H ⊗[R] H` swapping the two tensor factors. -/
noncomputable def swapAction (H : CommHopfAlgCat.{v} R) :
    Multiplicative (ZMod 2) →* Aut (CommHopfAlgCat.of R (H ⊗[R] H)) :=
  involutionAction (swapEnd H) (swapEnd_comp_swapEnd H)

/-- The generator `ofAdd 1` acts under `swapAction H` as `swapEnd H`. -/
@[simp]
theorem swapAction_ofAdd_one (H : CommHopfAlgCat.{v} R) :
    (swapAction H (.ofAdd 1)).asIso.hom = swapEnd H := by
  rw [swapAction, involutionAction_ofAdd_one]

/-- The fixed-point Hopf algebra of `swapAction H` on `H ⊗[R] H` is isomorphic to `H`. -/
noncomputable def fixedPointsSwapActionIso (H : CommHopfAlgCat.{v} R) :
    fixedPoints (fun θ ↦ (swapAction H θ).asIso.hom) ≅ H :=
  fixedPointsOfSwapIso H ⟨.ofAdd 1, swapAction_ofAdd_one H⟩ fun θ ↦ by
    rw [swapAction]; exact involutionAction_hom_eq_id_or _ _ θ

/-- Precomposing `(fixedPointsSwapActionIso H).hom` with `mkFixedPoints` gives `mulBialgHom R H`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsSwapActionIso_hom (H : CommHopfAlgCat.{v} R) :
    mkFixedPoints (fun θ ↦ (swapAction H θ).asIso.hom) ≫ (fixedPointsSwapActionIso H).hom =
      CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) := by
  rw [fixedPointsSwapActionIso, mkFixedPoints_comp_fixedPointsOfSwapIso_hom]

/-- The inverse of `fixedPointsSwapActionIso H` is `includeLeft ≫ mkFixedPoints`. -/
@[simp]
theorem fixedPointsSwapActionIso_inv (H : CommHopfAlgCat.{v} R) :
    (fixedPointsSwapActionIso H).inv =
      CommHopfAlgCat.ofHom
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)) ≫
        mkFixedPoints (fun θ ↦ (swapAction H θ).asIso.hom) := by
  rw [fixedPointsSwapActionIso, fixedPointsOfSwapIso_inv]

/-- The `ℤ/2`-action by group-scheme inversion on cocommutative `H : CommHopfAlgCat R`
(`[Coalgebra.IsCocomm R H]`). -/
noncomputable def antipodeAction (H : CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    Multiplicative (ZMod 2) →* Aut H :=
  involutionAction (antipodeEnd H) (antipodeEnd_comp_antipodeEnd H)

/-- The generator `ofAdd 1` acts under `antipodeAction H` as `antipodeEnd H`. -/
@[simp]
theorem antipodeAction_ofAdd_one (H : CommHopfAlgCat.{v} R) [Coalgebra.IsCocomm R H] :
    (antipodeAction H (.ofAdd 1)).asIso.hom = antipodeEnd H := by
  rw [antipodeAction, involutionAction_ofAdd_one]

/-- On `A`-points of cocommutative `H`, `antipodeAction H` fixes `{g | g⁻¹ = g}`. -/
theorem range_mapDomain_mkFixedPoints_antipodeAction (H : CommHopfAlgCat.{v} R)
    [Coalgebra.IsCocomm R H] (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A)
        (mkFixedPoints fun θ ↦ (antipodeAction H θ).asIso.hom).hom) = {g | g⁻¹ = g} := by
  rw [antipodeAction, range_mapDomain_mkFixedPoints_involutionAction]; ext g
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩ <;>
  · apply ofConv_injective; ext x
    simpa only [WithConv.algHom_inv_apply, BialgHom.mapDomain_apply_apply, antipodeEnd_hom,
      HopfAlgebra.antipodeBialgHom_apply] using
      congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv x) hg

end CommHopfAlgCat
