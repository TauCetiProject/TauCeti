/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.ModP
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GaloisCharacter.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.ZHat
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Unitary
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Characters of `Kˣ` as Weil and Galois characters

By geometric local Weil reciprocity (`TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv K`),
for any nonarchimedean local field `K` of characteristic zero, every continuous character
`δ : Kˣ →ₜ* M` induces a continuous character `δ.toWeilChar : W_K →ₜ* M` of the local Weil group.
When the target `G` is a commutative `T1` topological group with continuous multiplication, this
yields a group isomorphism `(Kˣ →ₜ* G) ≃* (W_K →ₜ* G)`
(`TauCeti.ClassFieldTheory.localWeilCharacterEquiv K G`), with inverse
`ContinuousMonoidHom.ofWeilChar`. For unramified characters `μ_a`, `μ_a.toWeilChar w = a ^ (-deg w)`
(`ContinuousMonoidHom.toWeilChar_unramifiedCharacter`), so any continuous Galois extension is
trivial on inertia and evaluates to `a` on geometric Frobenius lifts (`a⁻¹` on arithmetic Frobenius
lifts).

Because `W_K` is dense in `G_K`, any continuous extension of a Weil character to `G_K` into a
Hausdorff target is unique (`TauCeti.ClassFieldTheory.galoisChar_eq_of_weilToAbsolute_eq`), and
this restriction respects pointwise products and inverses
(`TauCeti.ClassFieldTheory.galoisChar_eq_mul_of_weilToAbsolute_eq`,
`TauCeti.ClassFieldTheory.galoisChar_eq_inv_of_weilToAbsolute_eq`).

Over `ℚ_[p]`, Colmez's explicit reciprocity formula gives
`δ.toWeilChar w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`
(`ContinuousMonoidHom.padic_toWeilChar_apply`). For a commutative topological monoid `Λ` with
continuous multiplication such that `Λˣ` is `T1`, a continuous character `δ : PadicUnitsChar p Λ`
extends continuously to `G_{ℚ_p} →ₜ* Λˣ` if and only if `n ↦ δ(p)^n` extends to a continuous
homomorphism `ℤ̂ →ₜ* Λˣ` (`TauCeti.PadicUnitsChar.exists_galoisChar_iff_exists_zHat`). In
particular, an extension exists when `Λˣ` is profinite (e.g. `ℤ_[p]`, `𝒪[L]`, `ZMod p`), when
`δ(p)` has finite order, or over any nonarchimedean local field `L` when `δ` is unitary
(`TauCeti.PadicUnitsChar.exists_galoisChar_iff_isUnitary`). Under this dictionary, `x ↦ x |x|_p`
corresponds to `continuousLocalCyclotomicCharacter p ℚ_[p]`, `ω` corresponds to
`modPLocalCyclotomicCharacter p ℚ_[p]`, and `x ↦ algebraMap ℚ_[p] L x` admits no continuous Galois
extension.

## Main definitions

* `ContinuousMonoidHom.toWeilChar` and `ContinuousMonoidHom.ofWeilChar`: transport between
  continuous characters of `Kˣ` and of `WeilGroup K`.
* `TauCeti.ClassFieldTheory.localWeilCharacterEquiv`: the group isomorphism
  `(Kˣ →ₜ* G) ≃* (WeilGroup K →ₜ* G)` for a commutative `T1` topological group `G`.
* `TauCeti.padicUnitsCharEquivWeilChar`: specialization to `PadicUnitsChar p Λ` for a commutative
  topological monoid `Λ` with continuous multiplication and `[T1Space Λˣ]`.
* `TauCeti.PadicUnitsChar.toGaloisCharOfZHat`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfProfiniteUnits`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfProfinite`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfFinOrderAtPrime`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfUnitary`: continuous Galois extensions `G_{ℚ_p} →ₜ* Λˣ`.

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

/-! ### General local-field Weil and Galois character correspondence -/

section GeneralWeil

namespace ContinuousMonoidHom

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- The continuous character `W_K →ₜ* M` corresponding to `δ : Kˣ →ₜ* M` via geometric local Weil
reciprocity `Kˣ ≃ₜ* W_K^{ab}`. -/
def toWeilChar (δ : Kˣ →ₜ* M) : WeilGroup K →ₜ* M :=
  (δ.comp ((localWeilGeometricArtinEquiv K).symm :
      TopologicalAbelianization (WeilGroup K) →ₜ* Kˣ)).comp
    (Subgroup.quotientMkContinuousMonoidHom (commutator (WeilGroup K)).topologicalClosure)

private theorem toWeilChar_mk (δ : Kˣ →ₜ* M) (w : WeilGroup K) :
    δ.toWeilChar w =
      δ ((localWeilGeometricArtinEquiv K).symm
        (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))) := by
  simp [toWeilChar]

/-- If `w ∈ W_K` represents `localWeilGeometricArtinEquiv K x`, then `δ.toWeilChar w = δ x`. -/
theorem toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv (δ : Kˣ →ₜ* M) (x : Kˣ)
    (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    δ.toWeilChar w = δ x := by
  rw [toWeilChar_mk, hw, ContinuousMulEquiv.symm_apply_apply]

/-- The trivial character of `Kˣ` corresponds to the trivial Weil character. -/
@[simp]
theorem toWeilChar_one : (1 : Kˣ →ₜ* M).toWeilChar = 1 := by
  ext1 _
  rfl

end Monoid

section Group

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Transport of an unramified character `μ_a : Kˣ →ₜ* G` to `W_K` evaluates to `a ^ (-deg w)`. -/
@[simp]
theorem toWeilChar_unramifiedCharacter (a : G) (w : WeilGroup K) :
    (unramifiedCharacter K a).toWeilChar w = a ^ (-(weilDegree K w).toAdd) := by
  rw [toWeilChar_mk, unramifiedCharacter_apply]
  have hnv : (normalizedValuation K ((localWeilGeometricArtinEquiv K).symm
      (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))))⁻¹ =
      weilDegreeAbelianization K (QuotientGroup.mk w) := by
    rw [← weilDegreeAbelianization_localWeilGeometricArtinEquiv,
      ContinuousMulEquiv.apply_symm_apply]
  have hnv' : normalizedValuation K ((localWeilGeometricArtinEquiv K).symm
      (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K))) =
      (weilDegree K w)⁻¹ := by
    rw [inv_eq_iff_eq_inv.mp hnv, weilDegreeAbelianization_mk]
  rw [hnv', toAdd_inv]

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- `toWeilChar` preserves products of characters. -/
@[simp]
theorem toWeilChar_mul [ContinuousMul G] (δ₁ δ₂ : Kˣ →ₜ* G) :
    (δ₁ * δ₂).toWeilChar = δ₁.toWeilChar * δ₂.toWeilChar := by
  ext1 _
  rfl

/-- Pointwise evaluation of the inverse of a continuous homomorphism. -/
private theorem pointwise_inv_apply {A E : Type*} [Monoid A] [TopologicalSpace A]
    [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E] (f : A →ₜ* E) (a : A) :
    f⁻¹ a = (f a)⁻¹ :=
  (rfl)

/-- `toWeilChar` preserves inverses of characters. -/
@[simp]
theorem toWeilChar_inv [IsTopologicalGroup G] (δ : Kˣ →ₜ* G) :
    δ⁻¹.toWeilChar = δ.toWeilChar⁻¹ := by
  ext1 _
  rw [toWeilChar_mk, pointwise_inv_apply, pointwise_inv_apply, toWeilChar_mk]

/-- The inverse of `toWeilChar`: reconstruct a continuous character `Kˣ →ₜ* G` from a Weil
character `ψ : W_K →ₜ* G` by factoring through `W_K^{ab}` and pulling back along
`localWeilGeometricArtinEquiv K`. -/
def ofWeilChar [T1Space G] (ψ : WeilGroup K →ₜ* G) : Kˣ →ₜ* G :=
  (TopologicalAbelianization.lift ψ).comp
    (localWeilGeometricArtinEquiv K : Kˣ →ₜ* TopologicalAbelianization (WeilGroup K))

/-- Evaluation of `ψ.ofWeilChar` on `x : Kˣ`. -/
@[simp]
theorem ofWeilChar_apply [T1Space G] (ψ : WeilGroup K →ₜ* G) (x : Kˣ) :
    ψ.ofWeilChar x = TopologicalAbelianization.lift ψ (localWeilGeometricArtinEquiv K x) :=
  (rfl)

/-- Evaluating `ψ.ofWeilChar` at `x` gives `ψ w` for any Weil element `w` representing
`localWeilGeometricArtinEquiv K x`. -/
theorem ofWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv [T1Space G]
    (ψ : WeilGroup K →ₜ* G) (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    ψ.ofWeilChar x = ψ w := by
  rw [ofWeilChar_apply, ← hw, TopologicalAbelianization.lift_mk]

end CommGroup

end ContinuousMonoidHom

namespace TauCeti.ClassFieldTheory

open _root_.ContinuousMonoidHom

section Uniqueness

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Uniqueness of continuous Galois extensions.** Because `W_K` is dense in `G_K`, two
continuous characters `G_K →ₜ* M` into a Hausdorff monoid that agree on `W_K` are equal. -/
theorem galoisChar_eq_of_weilToAbsolute_eq {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {χ₁ χ₂ : Field.absoluteGaloisGroup K →ₜ* M}
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
  toFun := ContinuousMonoidHom.toWeilChar
  invFun := ContinuousMonoidHom.ofWeilChar
  left_inv δ := ContinuousMonoidHom.ext fun x ↦ by
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv K x)
    rw [ContinuousMonoidHom.ofWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv δ.toWeilChar x w hw,
      δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw]
  right_inv ψ := ContinuousMonoidHom.ext fun w ↦ by
    rw [ContinuousMonoidHom.toWeilChar_mk, ContinuousMonoidHom.ofWeilChar_apply,
      ContinuousMulEquiv.apply_symm_apply, TopologicalAbelianization.lift_mk]
  map_mul' := ContinuousMonoidHom.toWeilChar_mul

variable {K}

/-- `localWeilCharacterEquiv K G` sends `δ` to `δ.toWeilChar`. -/
@[simp]
theorem localWeilCharacterEquiv_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (δ : Kˣ →ₜ* G) :
    localWeilCharacterEquiv K G δ = δ.toWeilChar :=
  (rfl)

/-- The inverse of `localWeilCharacterEquiv K G` sends `ψ` to `ψ.ofWeilChar`. -/
@[simp]
theorem localWeilCharacterEquiv_symm_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (ψ : WeilGroup K →ₜ* G) :
    (localWeilCharacterEquiv K G).symm ψ = ψ.ofWeilChar :=
  (rfl)

/-- Evaluating `(localWeilCharacterEquiv K G).symm ψ` at `x` gives `ψ w` for any Weil element `w`
representing `localWeilGeometricArtinEquiv K x`. -/
theorem localWeilCharacterEquiv_symm_apply_of_mk_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T1Space G] (ψ : WeilGroup K →ₜ* G) (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    (localWeilCharacterEquiv K G).symm ψ x = ψ w :=
  ψ.ofWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw

/-- **Product law for continuous Galois extensions.** Any continuous Galois character extending
`(δ₁ * δ₂).toWeilChar` is the pointwise product of continuous extensions of `δ₁.toWeilChar` and
`δ₂.toWeilChar`. -/
theorem galoisChar_eq_mul_of_weilToAbsolute_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] [T2Space G] {δ₁ δ₂ : Kˣ →ₜ* G}
    {χ χ₁ χ₂ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = (δ₁ * δ₂).toWeilChar w)
    (hχ₁ : ∀ w : WeilGroup K, χ₁ (weilToAbsolute K w) = δ₁.toWeilChar w)
    (hχ₂ : ∀ w : WeilGroup K, χ₂ (weilToAbsolute K w) = δ₂.toWeilChar w) :
    χ = χ₁ * χ₂ :=
  galoisChar_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [hχ w, ContinuousMonoidHom.toWeilChar_mul, ContinuousMonoidHom.mul_apply,
      ContinuousMonoidHom.mul_apply, hχ₁ w, hχ₂ w]

/-- **Inverse law for continuous Galois extensions.** Any continuous Galois character extending
`δ⁻¹.toWeilChar` is the pointwise inverse of any continuous extension of `δ.toWeilChar`. -/
theorem galoisChar_eq_inv_of_weilToAbsolute_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] {δ : Kˣ →ₜ* G}
    {χ χ₁ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ⁻¹.toWeilChar w)
    (hχ₁ : ∀ w : WeilGroup K, χ₁ (weilToAbsolute K w) = δ.toWeilChar w) :
    χ = χ₁⁻¹ :=
  galoisChar_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [hχ w, ContinuousMonoidHom.toWeilChar_inv, ContinuousMonoidHom.pointwise_inv_apply,
      ContinuousMonoidHom.pointwise_inv_apply, hχ₁ w]

/-- **Compatibility with the geometric Artin map.** If `χ : G_K →ₜ* G` extends `δ.toWeilChar`,
then its abelianization `χ^{ab}` satisfies `χ^{ab} (geometricArtinMap K x) = δ x` for all
`x ∈ Kˣ`. -/
theorem lift_geometricArtinMap_eq_of_weilToAbsolute {G : Type*} [CommGroup G] [TopologicalSpace G]
    [T1Space G] {δ : Kˣ →ₜ* G} {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ.toWeilChar w) (x : Kˣ) :
    TopologicalAbelianization.lift χ (geometricArtinMap K x) = δ x := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv K x)
  rw [← localWeilGeometricArtinEquiv_compat K x w hw, TopologicalAbelianization.lift_mk,
    hχ w, δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw]

/-- **Comparison with the arithmetic Artin map.** If `χ : G_K →ₜ* G` extends `δ.toWeilChar`,
then its abelianization `χ^{ab}` satisfies `χ^{ab} (artinMap K x) = (δ x)⁻¹` for all
`x ∈ Kˣ`. -/
theorem lift_artinMap_eq_inv_of_weilToAbsolute {G : Type*} [CommGroup G] [TopologicalSpace G]
    [T1Space G] {δ : Kˣ →ₜ* G} {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K, χ (weilToAbsolute K w) = δ.toWeilChar w) (x : Kˣ) :
    TopologicalAbelianization.lift χ (artinMap K x) = (δ x)⁻¹ := by
  have h := lift_geometricArtinMap_eq_of_weilToAbsolute hχ x
  rw [geometricArtinMap_apply, map_inv] at h
  exact inv_eq_iff_eq_inv.mp h

section UnramifiedChecks

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Unramified character check (inertia).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilChar` is trivial on the inertia subgroup `I_K`. -/
theorem inertiaSubgroup_le_ker_of_extends_unramifiedCharacter {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilChar w) :
    inertiaSubgroup K ≤ χ.toMonoidHom.ker := by
  intro σ hσ
  have h := hχ (inertiaToWeil K ⟨σ, hσ⟩)
  rw [weilToAbsolute_inertiaToWeil, ContinuousMonoidHom.toWeilChar_unramifiedCharacter,
    weilDegree_inertiaToWeil, toAdd_one, neg_zero, zpow_zero] at h
  exact h

/-- **Unramified character check (geometric Frobenius).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilChar` evaluates to `a` on every geometric Frobenius lift `σ`
(i.e. `IsArithFrobeniusLift K σ⁻¹`). -/
theorem apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilChar w)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ⁻¹) :
    χ σ = a := by
  let w₀ : WeilGroup K :=
    (weilGroupEquivLocalWeilGroup K).symm ⟨σ⁻¹, hσ.mem_localWeilGroup⟩
  have hw₀ : weilToAbsolute K w₀ = σ⁻¹ :=
    weilToAbsolute_weilGroupEquivLocalWeilGroup_symm K _
  have hdeg : weilDegree K w₀ = .ofAdd 1 :=
    weilDegree_eq_ofAdd_one_iff.mpr (by rwa [hw₀])
  have hw : weilToAbsolute K w₀⁻¹ = σ := by
    rw [map_inv, hw₀, inv_inv]
  rw [← hw, hχ w₀⁻¹, ContinuousMonoidHom.toWeilChar_unramifiedCharacter, map_inv, hdeg,
    toAdd_inv, toAdd_ofAdd, neg_neg, zpow_one]

/-- **Unramified character check (arithmetic Frobenius).** Any continuous Galois character extending
`(unramifiedCharacter K a).toWeilChar` evaluates to `a⁻¹` on every arithmetic Frobenius lift `σ`. -/
theorem apply_eq_inv_of_extends_unramifiedCharacter_of_isArithFrobeniusLift {a : G}
    {χ : Field.absoluteGaloisGroup K →ₜ* G}
    (hχ : ∀ w : WeilGroup K,
      χ (weilToAbsolute K w) = (unramifiedCharacter K a).toWeilChar w)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    χ σ = a⁻¹ := by
  have hinv := apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv hχ
    (σ := σ⁻¹) (by simpa using hσ)
  rw [map_inv] at hinv
  exact inv_eq_iff_eq_inv.mp hinv

end UnramifiedChecks

end CharZeroGeneral

end TauCeti.ClassFieldTheory

end GeneralWeil

/-! ### Colmez's `ℚ_pˣ` Weil formula and continuous extensions to `G_{ℚ_p}` -/

namespace ContinuousMonoidHom

open TauCeti TauCeti.ClassFieldTheory

/-- **Colmez's formula on the local Weil group.** For every `w ∈ W_{ℚ_p}`,
`δ.toWeilChar w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`. -/
theorem padic_toWeilChar_apply {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
    (δ : ℚ_[p]ˣ →ₜ* G) (w : WeilGroup ℚ_[p]) :
    δ.toWeilChar w =
      δ (padicPrimeUnit p) ^ (-(weilDegree ℚ_[p] w).toAdd) *
        δ (padicIntUnitsInclusion p
          (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w))) := by
  rw [toWeilChar_mk, localWeilGeometricArtinEquiv_symm_padic_mk, map_mul, map_zpow]

end ContinuousMonoidHom

namespace TauCeti

open TauCeti.ClassFieldTheory

section PadicWeilEquiv

variable (p : ℕ) [Fact p.Prime]
variable (Λ : Type*) [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ] [T1Space Λˣ]

/-- **Identification of `ℚ_[p]ˣ`-characters with Weil group characters.** For a commutative
topological monoid `Λ` with continuous multiplication and `[T1Space Λˣ]`, Colmez's geometric
reciprocity yields a group isomorphism `PadicUnitsChar p Λ ≃* (WeilGroup ℚ_[p] →ₜ* Λˣ)`. -/
def padicUnitsCharEquivWeilChar :
    PadicUnitsChar p Λ ≃* (WeilGroup ℚ_[p] →ₜ* Λˣ) :=
  localWeilCharacterEquiv ℚ_[p] Λˣ

variable {p Λ}

/-- `padicUnitsCharEquivWeilChar p Λ` sends `δ` to `δ.toWeilChar`. -/
@[simp]
theorem padicUnitsCharEquivWeilChar_apply (δ : PadicUnitsChar p Λ) :
    padicUnitsCharEquivWeilChar p Λ δ = δ.toWeilChar :=
  (rfl)

/-- The inverse of `padicUnitsCharEquivWeilChar p Λ` evaluates `ψ.ofWeilChar` on `x`. -/
@[simp]
theorem padicUnitsCharEquivWeilChar_symm_apply (ψ : WeilGroup ℚ_[p] →ₜ* Λˣ) (x : ℚ_[p]ˣ) :
    (padicUnitsCharEquivWeilChar p Λ).symm ψ x = ψ.ofWeilChar x :=
  (rfl)

/-- Evaluating `(padicUnitsCharEquivWeilChar p Λ).symm ψ` at `x` gives `ψ w` for any Weil element
`w` representing `localWeilGeometricArtinEquiv ℚ_[p] x`. -/
theorem padicUnitsCharEquivWeilChar_symm_apply_of_mk_eq (ψ : WeilGroup ℚ_[p] →ₜ* Λˣ)
    (x : ℚ_[p]ˣ) (w : WeilGroup ℚ_[p])
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup ℚ_[p])) =
      localWeilGeometricArtinEquiv ℚ_[p] x) :
    (padicUnitsCharEquivWeilChar p Λ).symm ψ x = ψ w :=
  ψ.ofWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw

end PadicWeilEquiv

section GaloisExtension

variable {p : ℕ} [Fact p.Prime]

/-- The trivial character `1 : PadicUnitsChar p Λ` extends to the trivial Galois character `1`. -/
theorem PadicUnitsChar.exists_galoisChar_one {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] :
    ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = (1 : PadicUnitsChar p Λ).toWeilChar w :=
  ⟨1, fun _ ↦ rfl⟩

section CommMonoid

variable {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]

open scoped IsMulCommutative in
/-- Given `δ : PadicUnitsChar p Λ` and a continuous homomorphism `φ : ℤ̂ →ₜ* Λˣ`, construct the
continuous Galois character `σ ↦ φ((unramifiedCoordinate σ)⁻¹) * δ(χ_cyc(σ))`.

This generalizes `ContinuousMonoidHom.padicGaloisCharacter` by taking the unramified factor
`φ : ℤ̂ →ₜ* Λˣ` as an explicit input rather than building it by profiniteness. When
`φ zHat.gen = δ(p)`, it restricts on `W_{ℚ_p}` to `δ.toWeilChar`
(`PadicUnitsChar.toGaloisCharOfZHat_weilToAbsolute_iff`). -/
def PadicUnitsChar.toGaloisCharOfZHat (δ : PadicUnitsChar p Λ) (φ : zHat.{0} →ₜ* Λˣ) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  ((φ.comp (ContinuousMonoidHom.inv zHat.{0})).coprod δ.toWeight).comp
    ((padicAbsoluteGaloisGroupAbelianizationEquiv p :
        Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* zHat.{0} × ℤ_[p]ˣ).comp
      (Subgroup.quotientMkContinuousMonoidHom
        (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure))

/-- Pointwise formula for `δ.toGaloisCharOfZHat φ`. -/
@[simp]
theorem PadicUnitsChar.toGaloisCharOfZHat_apply (δ : PadicUnitsChar p Λ) (φ : zHat.{0} →ₜ* Λˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    δ.toGaloisCharOfZHat φ σ =
      φ ((unramifiedCoordinate ℚ_[p] (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]))⁻¹) *
        δ (padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] σ)) := by
  simp [toGaloisCharOfZHat, abelianizedLocalCyclotomicCharacter_mk]

/-- **Exact compatibility condition for `toGaloisCharOfZHat`.** `δ.toGaloisCharOfZHat φ`
restricts on `W_{ℚ_p}` to `δ.toWeilChar` if and only if `φ zHat.gen = δ(p)`. -/
theorem PadicUnitsChar.toGaloisCharOfZHat_weilToAbsolute_iff (δ : PadicUnitsChar p Λ)
    (φ : zHat.{0} →ₜ* Λˣ) :
    (∀ w : WeilGroup ℚ_[p], δ.toGaloisCharOfZHat φ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) ↔
      φ zHat.gen = δ (padicPrimeUnit p) := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ :=
      QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv ℚ_[p] (padicPrimeUnit p))
    have hcompat := localWeilGeometricArtinEquiv_compat ℚ_[p] (padicPrimeUnit p) w hw
    have hspec := h w
    rw [toGaloisCharOfZHat_apply, hcompat, unramifiedCoordinate_geometricArtinMap,
      normalizedValuation_padicPrimeUnit, zHat.ofInt_ofAdd, zpow_one, inv_inv,
      ← abelianizedLocalCyclotomicCharacter_mk, hcompat,
      abelianizedLocalCyclotomicCharacter_geometricArtinMap_padic,
      padicUnitPart_padicPrimeUnit, map_one, map_one, mul_one,
      δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv (padicPrimeUnit p) w hw] at hspec
    exact hspec
  · intro hφ w
    rw [toGaloisCharOfZHat_apply, ContinuousMonoidHom.padic_toWeilChar_apply,
      unramifiedCoordinate_weilDegree]
    congr 1
    conv_lhs => rw [← ofAdd_toAdd (weilDegree ℚ_[p] w), zHat.ofInt_ofAdd]
    rw [← zpow_neg, map_zpow, hφ]

/-- If `φ zHat.gen = δ(p)`, then `δ.toGaloisCharOfZHat φ` restricts on `W_{ℚ_p}` to
`δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfZHat_weilToAbsolute (δ : PadicUnitsChar p Λ)
    (φ : zHat.{0} →ₜ* Λˣ) (hφ : φ zHat.gen = δ (padicPrimeUnit p)) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfZHat φ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  (δ.toGaloisCharOfZHat_weilToAbsolute_iff φ).mpr hφ w

open scoped IsMulCommutative in
/-- **Exact extension criterion to `G_{ℚ_p}`.** For a commutative topological monoid `Λ` with
continuous multiplication and `[T1Space Λˣ]`, a continuous character `δ : ℚ_[p]ˣ →ₜ* Λˣ` extends
continuously to `G_{ℚ_p} →ₜ* Λˣ` if and only if there is a continuous homomorphism `φ : ℤ̂ →ₜ* Λˣ`
with `φ zHat.gen = δ(p)`. -/
theorem PadicUnitsChar.exists_galoisChar_iff_exists_zHat [T1Space Λˣ] (δ : PadicUnitsChar p Λ) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) ↔
      ∃ φ : zHat.{0} →ₜ* Λˣ, φ zHat.gen = δ (padicPrimeUnit p) := by
  constructor
  · rintro ⟨χ, hχ⟩
    let invMap : zHat.{0} →ₜ* zHat.{0} × ℤ_[p]ˣ :=
      (ContinuousMonoidHom.inv zHat.{0}).prod 1
    let φ : zHat.{0} →ₜ* Λˣ :=
      ((TopologicalAbelianization.lift χ).comp
        ((padicAbsoluteGaloisGroupAbelianizationEquiv p).symm :
          zHat.{0} × ℤ_[p]ˣ →ₜ* Field.absoluteGaloisGroupAbelianization ℚ_[p])).comp invMap
    refine ⟨φ, ?_⟩
    have hgen : (padicAbsoluteGaloisGroupAbelianizationEquiv p).symm (zHat.gen⁻¹, 1) =
        geometricArtinMap ℚ_[p] (padicPrimeUnit p) := by
      apply (padicAbsoluteGaloisGroupAbelianizationEquiv p).injective
      rw [ContinuousMulEquiv.apply_symm_apply,
        padicAbsoluteGaloisGroupAbelianizationEquiv_geometricArtinMap]
      simp
    simp only [φ, invMap, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_coe, ContinuousMonoidHom.prod_toFun,
      ContinuousMonoidHom.inv_toFun, ContinuousMonoidHom.one_toFun]
    rw [hgen, lift_geometricArtinMap_eq_of_weilToAbsolute hχ]
  · rintro ⟨φ, hφ⟩
    exact ⟨δ.toGaloisCharOfZHat φ, δ.toGaloisCharOfZHat_weilToAbsolute φ hφ⟩

/-- Equivalent form of the extension criterion in terms of the dense subgroup `ℤ → ℤ̂`: for a
commutative topological monoid `Λ` with continuous multiplication and `[T1Space Λˣ]`, `δ` extends
to `G_{ℚ_p}` if and only if `n ↦ δ(p) ^ n` extends continuously along `zHat.ofInt`. -/
theorem PadicUnitsChar.exists_galoisChar_iff_exists_zHat_ofInt [T1Space Λˣ]
    (δ : PadicUnitsChar p Λ) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) ↔
      ∃ φ : zHat.{0} →ₜ* Λˣ, ∀ n : ℤ,
        φ (zHat.ofInt (.ofAdd n)) = δ (padicPrimeUnit p) ^ n := by
  rw [δ.exists_galoisChar_iff_exists_zHat]
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ, fun n ↦ by rw [zHat.ofInt_ofAdd, map_zpow, hφ]⟩,
    fun ⟨φ, hφ⟩ ↦ ⟨φ, by simpa using hφ 1⟩⟩

/-- If `δ₁` and `δ₂` extend continuously to `G_{ℚ_p}`, then so does `δ₁ * δ₂`. -/
theorem PadicUnitsChar.exists_galoisChar_mul {δ₁ δ₂ : PadicUnitsChar p Λ}
    (h₁ : ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ₁.toWeilChar w)
    (h₂ : ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ₂.toWeilChar w) :
    ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = (δ₁ * δ₂).toWeilChar w := by
  obtain ⟨χ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, hχ₂⟩ := h₂
  exact ⟨χ₁ * χ₂, fun w ↦ by
    rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.toWeilChar_mul,
      ContinuousMonoidHom.mul_apply, hχ₁ w, hχ₂ w]⟩

/-- If `δ` extends continuously to `G_{ℚ_p}`, then so does `δ⁻¹`. -/
theorem PadicUnitsChar.exists_galoisChar_inv {δ : PadicUnitsChar p Λ}
    (h : ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) :
    ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ⁻¹.toWeilChar w := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨χ⁻¹, fun w ↦ ?_⟩
  rw [ContinuousMonoidHom.pointwise_inv_apply, ContinuousMonoidHom.toWeilChar_inv,
    ContinuousMonoidHom.pointwise_inv_apply, hχ w]

/-! ### Sufficient conditions for continuous Galois extension -/

/-- Continuous Galois extension when `Λ` is a commutative topological monoid with continuous
multiplication (`[CommMonoid Λ]`, `[TopologicalSpace Λ]`, `[ContinuousMul Λ]`) whose unit group
`Λˣ` is profinite (`[CompactSpace Λˣ]`, `[TotallyDisconnectedSpace Λˣ]`), obtained by pulling back
`ContinuousMonoidHom.padicGaloisCharacter` to `G_{ℚ_p}`. -/
def PadicUnitsChar.toGaloisCharOfProfiniteUnits [CompactSpace Λˣ] [TotallyDisconnectedSpace Λˣ]
    (δ : PadicUnitsChar p Λ) : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  (ContinuousMonoidHom.padicGaloisCharacter δ).comp
    (Subgroup.quotientMkContinuousMonoidHom
      (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure)

/-- `toGaloisCharOfProfiniteUnits` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfProfiniteUnits_weilToAbsolute
    [CompactSpace Λˣ] [TotallyDisconnectedSpace Λˣ]
    (δ : PadicUnitsChar p Λ) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfProfiniteUnits (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w := by
  obtain ⟨x, hx⟩ := (localWeilGeometricArtinEquiv ℚ_[p]).surjective (QuotientGroup.mk w)
  have hcompat := localWeilGeometricArtinEquiv_compat ℚ_[p] x w hx.symm
  rw [PadicUnitsChar.toGaloisCharOfProfiniteUnits, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, Subgroup.quotientMkContinuousMonoidHom_apply, hcompat,
    ContinuousMonoidHom.padicGaloisCharacter_geometricArtinMap,
    δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hx.symm]

/-- Continuous Galois extension when `Λ` is a commutative `T1`, compact, totally disconnected
topological monoid with continuous multiplication (`[CommMonoid Λ]`, `[TopologicalSpace Λ]`,
`[ContinuousMul Λ]`, `[T1Space Λ]`, `[CompactSpace Λ]`, `[TotallyDisconnectedSpace Λ]`), for
instance `ℤ_[p]`, `𝒪[L]`, `ZMod p`, or any finite discrete ring. -/
def PadicUnitsChar.toGaloisCharOfProfinite [T1Space Λ] [CompactSpace Λ]
    [TotallyDisconnectedSpace Λ] (δ : PadicUnitsChar p Λ) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  δ.toGaloisCharOfProfiniteUnits

/-- `toGaloisCharOfProfinite` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfProfinite_weilToAbsolute [T1Space Λ] [CompactSpace Λ]
    [TotallyDisconnectedSpace Λ] (δ : PadicUnitsChar p Λ) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfProfinite (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  δ.toGaloisCharOfProfiniteUnits_weilToAbsolute w

/-- Continuous Galois extension when `δ(p)` has finite order in `Λˣ` (for any commutative
topological monoid `Λ` with continuous multiplication), built via `zHat.liftOfFinOrder`. -/
def PadicUnitsChar.toGaloisCharOfFinOrderAtPrime (δ : PadicUnitsChar p Λ)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  δ.toGaloisCharOfZHat (zHat.liftOfFinOrder hfin)

/-- `toGaloisCharOfFinOrderAtPrime` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfFinOrderAtPrime_weilToAbsolute (δ : PadicUnitsChar p Λ)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfFinOrderAtPrime hfin (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  δ.toGaloisCharOfZHat_weilToAbsolute _ (zHat.liftOfFinOrder_gen hfin) w

end CommMonoid

end GaloisExtension

/-! ### Exact unitary extendability over a nonarchimedean local field `L` -/

section UnitaryExtension

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Continuous Galois extension of a unitary character `δ : ℚ_[p]ˣ →ₜ* Lˣ` into a nonarchimedean
local field `L`, built via `zHatLiftUnitFiltration` into the profinite unit group `U(L, 0)`. -/
def PadicUnitsChar.toGaloisCharOfUnitary (δ : PadicUnitsChar p L) (hδ : δ.IsUnitary) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ :=
  δ.toGaloisCharOfZHat (zHatLiftUnitFiltration (δ (padicPrimeUnit p))
    ((PadicUnitsChar.isUnitary_iff_valuation_padicPrimeUnit_eq_one δ).mp hδ))

/-- `toGaloisCharOfUnitary` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfUnitary_weilToAbsolute (δ : PadicUnitsChar p L)
    (hδ : δ.IsUnitary) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfUnitary hδ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  δ.toGaloisCharOfZHat_weilToAbsolute _
    (zHatLiftUnitFiltration_gen _
      ((PadicUnitsChar.isUnitary_iff_valuation_padicPrimeUnit_eq_one δ).mp hδ)) w

/-- **Exact unitary criterion for Galois extension over a local field.** For any nonarchimedean
local field `L`, a continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` extends continuously to
`G_{ℚ_p} →ₜ* Lˣ` if and only if `δ` is unitary (`v_L(δ(p)) = 1`). -/
theorem PadicUnitsChar.exists_galoisChar_iff_isUnitary (δ : PadicUnitsChar p L) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) ↔ δ.IsUnitary := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := δ.exists_galoisChar_iff_exists_zHat.mp h
    let f : zHat.{0} →ₜ* Multiplicative ℤ :=
      ⟨(normalizedValuation L).comp φ.toMonoidHom,
        (continuous_normalizedValuation L).comp φ.continuous⟩
    have hf : f = 1 := ContinuousMonoidHom.eq_one_of_isMulTorsionFree f
    have hval : normalizedValuation L (δ (padicPrimeUnit p)) = 1 := by
      rw [← hφ]
      exact DFunLike.congr_fun hf zHat.gen
    exact (δ.isUnitary_iff_valuation_padicPrimeUnit_eq_one).mpr
      ((normalizedValuation_eq_one_iff _).mp hval)
  · intro hδ
    exact ⟨δ.toGaloisCharOfUnitary hδ, δ.toGaloisCharOfUnitary_weilToAbsolute hδ⟩

end UnitaryExtension

/-! ### Canonical character identifications and the non-unitary counterexample -/

section CanonicalChecks

variable (p : ℕ) [Fact p.Prime]

/-- **Cyclotomic character check.** Under Colmez's normalization, the unitary character
`x ↦ x |x|_p` (`TauCeti.padicUnitPart p`) corresponds on `W_{ℚ_p}` to the `p`-adic cyclotomic
character. -/
theorem continuousLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicUnitPart
    (w : WeilGroup ℚ_[p]) :
    continuousLocalCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) =
      (padicUnitPart p).toWeilChar w := by
  rw [ContinuousMonoidHom.padic_toWeilChar_apply, padicUnitPart_padicPrimeUnit, one_zpow,
    one_mul, padicUnitPart_padicIntUnitsInclusion, continuousLocalCyclotomicCharacter_apply]

/-- The unique continuous Galois extension of `padicUnitPart p` (`x ↦ x |x|`) is
`continuousLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem toGaloisCharOfProfiniteUnits_padicUnitPart :
    PadicUnitsChar.toGaloisCharOfProfiniteUnits (padicUnitPart p) =
      continuousLocalCyclotomicCharacter p ℚ_[p] := by
  ext1 σ
  simp [PadicUnitsChar.toGaloisCharOfProfiniteUnits]

/-- **Mod-`p` cyclotomic character check.** Under Colmez's normalization, `ω` corresponds on
`W_{ℚ_p}` to `modPLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicModPCyclotomicChar
    (w : WeilGroup ℚ_[p]) :
    modPLocalCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) =
      (padicModPCyclotomicChar p).toWeilChar w := by
  apply Units.ext
  rw [ContinuousMonoidHom.padic_toWeilChar_apply, padicModPCyclotomicChar_padicPrimeUnit,
    one_zpow, one_mul, coe_padicModPCyclotomicChar_padicIntUnitsInclusion,
    coe_modPLocalCyclotomicCharacter_apply]

/-- The unique continuous Galois extension of `padicModPCyclotomicChar p` (`ω`) is
`modPLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem toGaloisCharOfProfinite_padicModPCyclotomicChar :
    (padicModPCyclotomicChar p).toGaloisCharOfProfinite = modPLocalCyclotomicCharacter p ℚ_[p] :=
  galoisChar_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [PadicUnitsChar.toGaloisCharOfProfinite_weilToAbsolute,
      modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicModPCyclotomicChar]

section NonUnitary

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra ℚ_[p] L]

/-- **Non-extendability of `x ↦ algebraMap ℚ_[p] L x`.** For any nonarchimedean local field `L`
with a continuous `ℚ_[p]`-algebra structure (including `ℚ_[p]` itself and its finite extensions),
the character `x ↦ algebraMap ℚ_[p] L x` does not extend continuously from `W_{ℚ_p}` to
`G_{ℚ_p}`. -/
theorem not_exists_galoisChar_padicAlgebraMapChar (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ,
      ∀ w : WeilGroup ℚ_[p],
        χ (weilToAbsolute ℚ_[p] w) = (padicAlgebraMapChar p L h).toWeilChar w := by
  rw [PadicUnitsChar.exists_galoisChar_iff_isUnitary]
  exact not_isUnitary_padicAlgebraMapChar p L h

/-- Equivalently, the map `n ↦ (p : L) ^ n` does not extend to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ`. -/
theorem not_exists_zHat_padicPrimeUnit (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ ∃ φ : zHat.{0} →ₜ* Lˣ,
      φ zHat.gen = Units.map (algebraMap ℚ_[p] L).toMonoidHom (padicPrimeUnit p) := by
  intro ⟨φ, hφ⟩
  refine not_exists_galoisChar_padicAlgebraMapChar p L h ?_
  rw [PadicUnitsChar.exists_galoisChar_iff_exists_zHat]
  refine ⟨φ, hφ.trans (Units.ext ?_)⟩
  simp

end NonUnitary

end CanonicalChecks

end TauCeti
