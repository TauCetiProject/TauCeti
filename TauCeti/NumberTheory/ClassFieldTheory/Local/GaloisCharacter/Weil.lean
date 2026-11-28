/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Reciprocity
public import TauCeti.NumberTheory.GaloisRepresentation.Unramified.WeilCharacter
public import TauCeti.NumberTheory.LocalField.Unramified.Character
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Characters of `Kˣ` as Weil characters

By geometric local Weil reciprocity (`TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv K`),
for any nonarchimedean local field `K` of characteristic zero, every continuous character
`δ : Kˣ →ₜ* M` induces a continuous character `δ.toWeilCharacter : W_K →ₜ* M` of the local Weil
group. When the target `G` is a commutative `T1` topological group with continuous multiplication,
this yields a group isomorphism `(Kˣ →ₜ* G) ≃* (W_K →ₜ* G)`
(`TauCeti.ClassFieldTheory.localWeilCharacterEquiv K G`), with inverse
`ContinuousMonoidHom.ofWeilCharacter`. For unramified characters `μ_a`,
`μ_a.toWeilCharacter = GaloisRep.weilUnramifiedCharacter K a⁻¹`
(`ContinuousMonoidHom.toWeilCharacter_unramifiedCharacter`), so any continuous Galois extension is
trivial on inertia and evaluates to `a` on geometric Frobenius lifts (`a⁻¹` on arithmetic Frobenius
lifts).

Because `W_K` is dense in `G_K`, any continuous extension of a Weil character to `G_K` into a
Hausdorff target is unique (`TauCeti.ClassFieldTheory.galoisCharacter_eq_of_weilToAbsolute_eq`),
and this restriction respects trivial, pointwise product, and inverse characters
(`TauCeti.ClassFieldTheory.galoisCharacter_eq_mul_of_weilToAbsolute_eq`,
`TauCeti.ClassFieldTheory.galoisCharacter_eq_inv_of_weilToAbsolute_eq`,
`TauCeti.ClassFieldTheory.exists_galoisCharacter_one`,
`TauCeti.ClassFieldTheory.exists_galoisCharacter_mul`,
`TauCeti.ClassFieldTheory.exists_galoisCharacter_inv`).

## Main definitions

* `ContinuousMonoidHom.toWeilCharacter` and `ContinuousMonoidHom.ofWeilCharacter`: transport
  between continuous characters of `Kˣ` and of `WeilGroup K`.
* `TauCeti.ClassFieldTheory.localWeilCharacterEquiv`: the group isomorphism
  `(Kˣ →ₜ* G) ≃* (WeilGroup K →ₜ* G)` for a commutative `T1` topological group `G` with
  continuous multiplication.

## Main results

* `ContinuousMonoidHom.toWeilCharacter_apply`,
  `ContinuousMonoidHom.toWeilCharacter_unramifiedCharacter`,
  `ContinuousMonoidHom.ofWeilCharacter_toWeilCharacter`,
  `ContinuousMonoidHom.toWeilCharacter_ofWeilCharacter`: evaluation and round-trip cancellation
  laws for `toWeilCharacter` and `ofWeilCharacter`.
* `TauCeti.ClassFieldTheory.galoisCharacter_eq_of_weilToAbsolute_eq`,
  `TauCeti.ClassFieldTheory.galoisCharacter_eq_mul_of_weilToAbsolute_eq`,
  `TauCeti.ClassFieldTheory.galoisCharacter_eq_inv_of_weilToAbsolute_eq`: uniqueness and closure
  of continuous Galois extensions.
* `TauCeti.ClassFieldTheory.exists_galoisCharacter_one`,
  `TauCeti.ClassFieldTheory.exists_galoisCharacter_mul`,
  `TauCeti.ClassFieldTheory.exists_galoisCharacter_inv`: closure of extendability under `1`, `*`,
  and `⁻¹`.
* `TauCeti.ClassFieldTheory.lift_geometricArtinMap_eq_of_weilToAbsolute` and
  `TauCeti.ClassFieldTheory.lift_artinMap_eq_inv_of_weilToAbsolute`: compatibility of continuous
  extensions with the absolute local Artin maps.
* `TauCeti.ClassFieldTheory.inertiaSubgroup_le_ker_of_extends_unramifiedCharacter`,
  `TauCeti.ClassFieldTheory.apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv`,
  `TauCeti.ClassFieldTheory.apply_eq_inv_of_extends_unramifiedCharacter_of_isArithFrobeniusLift`:
  inertia and Frobenius values of extensions of unramified characters.

## References

* P. Colmez, *Représentations de GL₂(ℚ_p) et (φ, Γ)-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace ContinuousMonoidHom

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- The continuous character `W_K →ₜ* M` corresponding to `δ : Kˣ →ₜ* M` via geometric local Weil
reciprocity `Kˣ ≃ₜ* W_K^{ab}`. -/
def toWeilCharacter (δ : Kˣ →ₜ* M) : WeilGroup K →ₜ* M :=
  (δ.comp ((localWeilGeometricArtinEquiv K).symm :
      TopologicalAbelianization (WeilGroup K) →ₜ* Kˣ)).comp
    (Subgroup.quotientMkContinuousMonoidHom (commutator (WeilGroup K)).topologicalClosure)

/-- Evaluation of `δ.toWeilCharacter` at `w : WeilGroup K`. -/
theorem toWeilCharacter_apply (δ : Kˣ →ₜ* M) (w : WeilGroup K) :
    δ.toWeilCharacter w =
      δ ((localWeilGeometricArtinEquiv K).symm
        (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))) := by
  simp [toWeilCharacter]

/-- If `w ∈ W_K` represents `localWeilGeometricArtinEquiv K x`, then `δ.toWeilCharacter w = δ x`. -/
theorem toWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv (δ : Kˣ →ₜ* M) (x : Kˣ)
    (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    δ.toWeilCharacter w = δ x := by
  rw [toWeilCharacter_apply, hw, ContinuousMulEquiv.symm_apply_apply]

/-- The trivial character of `Kˣ` corresponds to the trivial Weil character. -/
@[simp]
theorem toWeilCharacter_one : (1 : Kˣ →ₜ* M).toWeilCharacter = 1 := by
  ext1 _
  rfl

end Monoid

section Group

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Transport of an unramified character `μ_a : Kˣ →ₜ* G` to `W_K` is the unramified Weil
character `GaloisRep.weilUnramifiedCharacter K a⁻¹` (`w ↦ a ^ (-deg w)`). -/
@[simp]
theorem toWeilCharacter_unramifiedCharacter (a : G) :
    (unramifiedCharacter K a).toWeilCharacter = GaloisRep.weilUnramifiedCharacter K a⁻¹ := by
  ext1 w
  rw [toWeilCharacter_apply, unramifiedCharacter_apply, GaloisRep.weilUnramifiedCharacter_apply]
  have hnv : (normalizedValuation K ((localWeilGeometricArtinEquiv K).symm
      (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))))⁻¹ =
      weilDegreeAbelianization K (QuotientGroup.mk w) := by
    rw [← weilDegreeAbelianization_localWeilGeometricArtinEquiv,
      ContinuousMulEquiv.apply_symm_apply]
  have hnv' : normalizedValuation K ((localWeilGeometricArtinEquiv K).symm
      (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))) =
      (weilDegree K w)⁻¹ := by
    rw [inv_eq_iff_eq_inv.mp hnv, weilDegreeAbelianization_mk]
  rw [hnv', toAdd_inv, zpow_neg, inv_zpow]

end Group

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

/-- `toWeilCharacter` preserves products of characters. -/
@[simp]
theorem toWeilCharacter_mul (δ₁ δ₂ : Kˣ →ₜ* M) :
    (δ₁ * δ₂).toWeilCharacter = δ₁.toWeilCharacter * δ₂.toWeilCharacter := by
  ext1 _
  rfl

end CommMonoid

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- `toWeilCharacter` preserves inverses of characters. -/
@[simp]
theorem toWeilCharacter_inv [IsTopologicalGroup G] (δ : Kˣ →ₜ* G) :
    δ⁻¹.toWeilCharacter = δ.toWeilCharacter⁻¹ := by
  ext1 _
  rw [toWeilCharacter_apply, ContinuousMonoidHom.inv_apply, ContinuousMonoidHom.inv_apply,
    toWeilCharacter_apply]

/-- The inverse of `toWeilCharacter`: reconstruct a continuous character `Kˣ →ₜ* G` from a Weil
character `ψ : W_K →ₜ* G` by factoring through `W_K^{ab}` and pulling back along
`localWeilGeometricArtinEquiv K`. -/
def ofWeilCharacter [T1Space G] (ψ : WeilGroup K →ₜ* G) : Kˣ →ₜ* G :=
  (TopologicalAbelianization.lift ψ).comp
    (localWeilGeometricArtinEquiv K : Kˣ →ₜ* TopologicalAbelianization (WeilGroup K))

/-- Evaluation of `ψ.ofWeilCharacter` on `x : Kˣ`. -/
@[simp]
theorem ofWeilCharacter_apply [T1Space G] (ψ : WeilGroup K →ₜ* G) (x : Kˣ) :
    ψ.ofWeilCharacter x = TopologicalAbelianization.lift ψ (localWeilGeometricArtinEquiv K x) :=
  (rfl)

/-- Evaluating `ψ.ofWeilCharacter` at `x` gives `ψ w` for any Weil element `w` representing
`localWeilGeometricArtinEquiv K x`. -/
theorem ofWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv [T1Space G]
    (ψ : WeilGroup K →ₜ* G) (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    ψ.ofWeilCharacter x = ψ w := by
  rw [ofWeilCharacter_apply, ← hw, TopologicalAbelianization.lift_mk]

/-- `ofWeilCharacter` is left inverse to `toWeilCharacter`. -/
@[simp]
theorem ofWeilCharacter_toWeilCharacter [T1Space G] (δ : Kˣ →ₜ* G) :
    δ.toWeilCharacter.ofWeilCharacter = δ := by
  ext1 x
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv K x)
  rw [ofWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv δ.toWeilCharacter x w hw,
    δ.toWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw]

/-- `toWeilCharacter` is left inverse to `ofWeilCharacter`. -/
@[simp]
theorem toWeilCharacter_ofWeilCharacter [T1Space G] (ψ : WeilGroup K →ₜ* G) :
    ψ.ofWeilCharacter.toWeilCharacter = ψ := by
  ext1 w
  rw [toWeilCharacter_apply, ofWeilCharacter_apply, ContinuousMulEquiv.apply_symm_apply,
    TopologicalAbelianization.lift_mk]

end CommGroup

end ContinuousMonoidHom

namespace TauCeti.ClassFieldTheory

open _root_.ContinuousMonoidHom

section Uniqueness

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Uniqueness of continuous Galois extensions.** Because `W_K` is dense in `G_K`, two
continuous characters `G_K →ₜ* M` into a Hausdorff monoid that agree on `W_K` are equal. -/
theorem galoisCharacter_eq_of_weilToAbsolute_eq {M : Type*} [Monoid M] [TopologicalSpace M]
    [T2Space M] {χ₁ χ₂ : Field.absoluteGaloisGroup K →ₜ* M}
    (h : ∀ w : WeilGroup K, χ₁ (weilToAbsolute K w) = χ₂ (weilToAbsolute K w)) :
    χ₁ = χ₂ :=
  ContinuousMonoidHom.ext <|
    congrFun ((denseRange_weilToAbsolute K).equalizer χ₁.continuous χ₂.continuous (funext h))

end Uniqueness

section CharZeroGeneral

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

/-- **Identification of `Kˣ`-characters with Weil group characters.** For a characteristic-zero
nonarchimedean local field `K` and a commutative `T1` topological group `G` with continuous
multiplication, geometric local Weil reciprocity yields a group isomorphism
`(Kˣ →ₜ* G) ≃* (WeilGroup K →ₜ* G)`. -/
def localWeilCharacterEquiv (G : Type*) [CommGroup G] [TopologicalSpace G] [ContinuousMul G]
    [T1Space G] : (Kˣ →ₜ* G) ≃* (WeilGroup K →ₜ* G) where
  toFun := ContinuousMonoidHom.toWeilCharacter
  invFun := ContinuousMonoidHom.ofWeilCharacter
  left_inv := ContinuousMonoidHom.ofWeilCharacter_toWeilCharacter
  right_inv := ContinuousMonoidHom.toWeilCharacter_ofWeilCharacter
  map_mul' := ContinuousMonoidHom.toWeilCharacter_mul

variable {K}

/-- `localWeilCharacterEquiv K G` sends `δ` to `δ.toWeilCharacter`. -/
@[simp]
theorem localWeilCharacterEquiv_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (δ : Kˣ →ₜ* G) :
    localWeilCharacterEquiv K G δ = δ.toWeilCharacter :=
  (rfl)

/-- The inverse of `localWeilCharacterEquiv K G` sends `ψ` to `ψ.ofWeilCharacter`. -/
@[simp]
theorem localWeilCharacterEquiv_symm_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (ψ : WeilGroup K →ₜ* G) :
    (localWeilCharacterEquiv K G).symm ψ = ψ.ofWeilCharacter :=
  (rfl)

/-- Evaluating `(localWeilCharacterEquiv K G).symm ψ` at `x` gives `ψ w` for any Weil element `w`
representing `localWeilGeometricArtinEquiv K x`. -/
theorem localWeilCharacterEquiv_symm_apply_of_mk_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (ψ : WeilGroup K →ₜ* G) (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    (localWeilCharacterEquiv K G).symm ψ x = ψ w :=
  ψ.ofWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw

/-- The trivial character `1 : Kˣ →ₜ* M` extends to the trivial Galois character `1`. -/
theorem exists_galoisCharacter_one {M : Type*} [Monoid M] [TopologicalSpace M] :
    ∃ χ : Field.absoluteGaloisGroup K →ₜ* M,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = (1 : Kˣ →ₜ* M).toWeilCharacter w :=
  ⟨1, fun _ ↦ rfl⟩

/-- If `δ₁, δ₂ : Kˣ →ₜ* M` extend continuously to `G_K`, then so does `δ₁ * δ₂`. -/
theorem exists_galoisCharacter_mul {M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] {δ₁ δ₂ : Kˣ →ₜ* M}
    (h₁ : ∃ χ : Field.absoluteGaloisGroup K →ₜ* M,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ₁.toWeilCharacter w)
    (h₂ : ∃ χ : Field.absoluteGaloisGroup K →ₜ* M,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ₂.toWeilCharacter w) :
    ∃ χ : Field.absoluteGaloisGroup K →ₜ* M,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = (δ₁ * δ₂).toWeilCharacter w := by
  obtain ⟨χ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, hχ₂⟩ := h₂
  exact ⟨χ₁ * χ₂, fun w ↦ by
    rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.toWeilCharacter_mul,
      ContinuousMonoidHom.mul_apply, hχ₁ w, hχ₂ w]⟩

/-- If `δ : Kˣ →ₜ* G` extends continuously to `G_K`, then so does `δ⁻¹`. -/
theorem exists_galoisCharacter_inv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] {δ : Kˣ →ₜ* G}
    (h : ∃ χ : Field.absoluteGaloisGroup K →ₜ* G,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ.toWeilCharacter w) :
    ∃ χ : Field.absoluteGaloisGroup K →ₜ* G,
      ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ⁻¹.toWeilCharacter w := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨χ⁻¹, fun w ↦ ?_⟩
  rw [ContinuousMonoidHom.inv_apply, ContinuousMonoidHom.toWeilCharacter_inv,
    ContinuousMonoidHom.inv_apply, hχ w]

/-- **Product law for continuous Galois extensions.** Any continuous Galois character extending
`(δ₁ * δ₂).toWeilCharacter` is the pointwise product of continuous extensions of
`δ₁.toWeilCharacter` and `δ₂.toWeilCharacter`. -/
theorem galoisCharacter_eq_mul_of_weilToAbsolute_eq {M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {δ₁ δ₂ : Kˣ →ₜ* M}
    {χ χ₁ χ₂ : Field.absoluteGaloisGroup K →ₜ* M}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = (δ₁ * δ₂).toWeilCharacter w)
    (hχ₁ : ∀ w : WeilGroup K, χ₁ (weilToAbsolute K w) = δ₁.toWeilCharacter w)
    (hχ₂ : ∀ w : WeilGroup K, χ₂ (weilToAbsolute K w) = δ₂.toWeilCharacter w) :
    χ = χ₁ * χ₂ :=
  galoisCharacter_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [hχ w, ContinuousMonoidHom.toWeilCharacter_mul, ContinuousMonoidHom.mul_apply,
      ContinuousMonoidHom.mul_apply, hχ₁ w, hχ₂ w]

/-- **Inverse law for continuous Galois extensions.** Any continuous Galois character extending
`δ⁻¹.toWeilCharacter` is the pointwise inverse of any continuous extension of
`δ.toWeilCharacter`. -/
theorem galoisCharacter_eq_inv_of_weilToAbsolute_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] {δ : Kˣ →ₜ* G}
    {χ χ₁ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ⁻¹.toWeilCharacter w)
    (hχ₁ : ∀ w : WeilGroup K, χ₁ (weilToAbsolute K w) = δ.toWeilCharacter w) :
    χ = χ₁⁻¹ :=
  galoisCharacter_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [hχ w, ContinuousMonoidHom.toWeilCharacter_inv, ContinuousMonoidHom.inv_apply,
      ContinuousMonoidHom.inv_apply, hχ₁ w]

/-- **Compatibility with the geometric Artin map.** If `χ : G_K →ₜ* G` extends
`δ.toWeilCharacter`, then its abelianization `χ^{ab}` satisfies
`χ^{ab} (geometricArtinMap K x) = δ x` for all `x ∈ Kˣ`. -/
theorem lift_geometricArtinMap_eq_of_weilToAbsolute {G : Type*} [CommGroup G] [TopologicalSpace G]
    [T1Space G] {δ : Kˣ →ₜ* G} {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ.toWeilCharacter w) (x : Kˣ) :
    TopologicalAbelianization.lift χ (geometricArtinMap K x) = δ x := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv K x)
  rw [← localWeilGeometricArtinEquiv_compat K x w hw, TopologicalAbelianization.lift_mk,
    hχ w, δ.toWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw]

/-- **Comparison with the arithmetic Artin map.** If `χ : G_K →ₜ* G` extends
`δ.toWeilCharacter`, then its abelianization `χ^{ab}` satisfies
`χ^{ab} (artinMap K x) = (δ x)⁻¹` for all `x ∈ Kˣ`. -/
theorem lift_artinMap_eq_inv_of_weilToAbsolute {G : Type*} [CommGroup G] [TopologicalSpace G]
    [T1Space G] {δ : Kˣ →ₜ* G} {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ.toWeilCharacter w) (x : Kˣ) :
    TopologicalAbelianization.lift χ (artinMap K x) = (δ x)⁻¹ := by
  have h := lift_geometricArtinMap_eq_of_weilToAbsolute hχ x
  rw [geometricArtinMap_apply, map_inv] at h
  exact inv_eq_iff_eq_inv.mp h

section UnramifiedChecks

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Unramified character check (inertia).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilCharacter` is trivial on the inertia subgroup `I_K`. -/
theorem inertiaSubgroup_le_ker_of_extends_unramifiedCharacter {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilCharacter w) :
    inertiaSubgroup K ≤ χ.toMonoidHom.ker := by
  intro σ hσ
  have h := hχ (inertiaToWeil K ⟨σ, hσ⟩)
  rw [weilToAbsolute_inertiaToWeil, ContinuousMonoidHom.toWeilCharacter_unramifiedCharacter,
    GaloisRep.weilUnramifiedCharacter_apply_of_mem_inertiaSubgroup a⁻¹
      (by rwa [weilToAbsolute_inertiaToWeil])] at h
  exact h

/-- **Unramified character check (geometric Frobenius).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilCharacter` evaluates to `a` on every geometric Frobenius lift `σ`
(i.e. `IsArithFrobeniusLift K σ⁻¹`). -/
theorem apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilCharacter w)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ⁻¹) :
    χ σ = a := by
  have hmem : σ ∈ (weilToAbsolute K).range := by
    rw [range_weilToAbsolute, ← inv_inv σ]
    exact (localWeilGroup K).inv_mem hσ.mem_localWeilGroup
  obtain ⟨w, hw⟩ := hmem
  have hinv := GaloisRep.weilUnramifiedCharacter_apply_of_isArithFrobeniusLift a⁻¹ (w := w⁻¹)
    (by simpa [hw] using hσ)
  rw [map_inv, inv_eq_iff_eq_inv, inv_inv] at hinv
  rw [← hw, hχ w, ContinuousMonoidHom.toWeilCharacter_unramifiedCharacter, hinv]

/-- **Unramified character check (arithmetic Frobenius).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilCharacter` evaluates to `a⁻¹` on every arithmetic Frobenius lift
`σ`. -/
theorem apply_eq_inv_of_extends_unramifiedCharacter_of_isArithFrobeniusLift {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilCharacter w)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    χ σ = a⁻¹ := by
  have hinv := apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv hχ
    (σ := σ⁻¹) (by simpa using hσ)
  rw [map_inv] at hinv
  exact inv_eq_iff_eq_inv.mp hinv

end UnramifiedChecks

end CharZeroGeneral

end TauCeti.ClassFieldTheory
