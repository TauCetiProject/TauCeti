/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.ModP
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GaloisCharacter.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GaloisCharacter.Weil
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.ZHat
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Unitary
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod
import TauCeti.NumberTheory.LocalField.Units.Decomposition
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Colmez's `ℚ_pˣ` Weil formula and Galois extensions

Over `ℚ_[p]`, Colmez's explicit reciprocity formula gives
`δ.toWeilCharacter w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`
(`ContinuousMonoidHom.padic_toWeilCharacter_apply`). For a commutative topological group `G` with
continuous multiplication and `[T1Space G]`, a continuous character `δ : ℚ_[p]ˣ →ₜ* G` extends
continuously to `G_{ℚ_p} →ₜ* G` if and only if `n ↦ δ(p) ^ n` extends to a continuous
homomorphism `ℤ̂ →ₜ* G` (`ContinuousMonoidHom.exists_galoisCharacter_iff_exists_zHat`). In
particular, an extension exists when `G` is profinite (`ContinuousMonoidHom.padicGaloisCharacter`
from `GaloisCharacter/Basic`, restricting on `W_{ℚ_p}` via
`ContinuousMonoidHom.padicGaloisCharacter_weilToAbsolute`, covering e.g. `ℤ_[p]ˣ`, `𝒪[L]ˣ`,
`(ZMod p)ˣ`), when `δ(p)` has finite order
(`ContinuousMonoidHom.toGaloisCharacterOfFinOrderAtPrime`), or over any nonarchimedean local field
`L` when `δ` is unitary (`TauCeti.PadicUnitsCharacter.exists_galoisCharacter_iff_isUnitary`).

Under this dictionary, `x ↦ x |x|_p` corresponds to `continuousLocalCyclotomicCharacter p ℚ_[p]`
(`TauCeti.continuousLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilCharacter_padicUnitPart` and
`ContinuousMonoidHom.padicGaloisCharacter_padicUnitPart`), `ω` corresponds to
`modPLocalCyclotomicCharacter p ℚ_[p]`
(`TauCeti.padicGaloisCharacter_padicModPCyclotomicCharacter`), and for any nonarchimedean
local field `L` with a continuous `ℚ_[p]`-algebra map, `x ↦ algebraMap ℚ_[p] L x` admits no
continuous Galois extension (`TauCeti.not_exists_galoisCharacter_padicAlgebraMapCharacter`).

## Main definitions

* `ContinuousMonoidHom.toGaloisCharacterOfZHat`: continuous Galois character constructor
  `G_{ℚ_p} →ₜ* G` built from `δ : ℚ_[p]ˣ →ₜ* G` and an explicit unramified factor
  `φ : ℤ̂ →ₜ* G` (extending `δ.toWeilCharacter` on `W_{ℚ_p}` exactly when `φ zHat.gen = δ(p)`).
* `ContinuousMonoidHom.toGaloisCharacterOfFinOrderAtPrime`: continuous Galois extension when
  `δ(p)` has finite order.
* `TauCeti.PadicUnitsCharacter.toGaloisCharacterOfUnitary`: continuous Galois extension of a
  unitary character `δ : ℚ_[p]ˣ →ₜ* Lˣ`.

## Main results

* `ContinuousMonoidHom.padic_toWeilCharacter_apply`: Colmez's formula on `W_{ℚ_p}`.
* `ContinuousMonoidHom.exists_galoisCharacter_iff_exists_zHat`,
  `ContinuousMonoidHom.exists_galoisCharacter_iff_exists_zHat_ofInt`: exact extension criteria.
* `ContinuousMonoidHom.padicGaloisCharacter_weilToAbsolute`: Weil compatibility for the profinite
  character `ContinuousMonoidHom.padicGaloisCharacter`.
* `TauCeti.PadicUnitsCharacter.exists_galoisCharacter_iff_isUnitary`: exact unitary criterion over
  a nonarchimedean local field `L`.
* `TauCeti.continuousLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilCharacter_padicUnitPart`,
  `TauCeti.padicGaloisCharacter_padicModPCyclotomicCharacter`,
  `TauCeti.not_exists_galoisCharacter_padicAlgebraMapCharacter`: canonical checks and the
  non-unitary counterexample.

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

section WeilFormula

/-- **Colmez's formula on the local Weil group.** For every `w ∈ W_{ℚ_p}`,
`δ.toWeilCharacter w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`. -/
theorem padic_toWeilCharacter_apply {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [TopologicalSpace G] (δ : ℚ_[p]ˣ →ₜ* G) (w : WeilGroup ℚ_[p]) :
    δ.toWeilCharacter w =
      δ (padicPrimeUnit p) ^ (-(weilDegree ℚ_[p] w).toAdd) *
        δ (padicIntUnitsInclusion p
          (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w))) := by
  rw [toWeilCharacter_apply, localWeilGeometricArtinEquiv_symm_padic_mk, map_mul, map_zpow]

end WeilFormula

section GaloisExtension

variable {p : ℕ} [Fact p.Prime]

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [ContinuousMul G]

/-- Given `δ : ℚ_[p]ˣ →ₜ* G` and a continuous homomorphism `φ : ℤ̂ →ₜ* G`, construct the
continuous Galois character `σ ↦ δ(χ_cyc(σ)) * φ((unramifiedCoordinate σ)⁻¹)`, pulling back
`ContinuousMonoidHom.padicGaloisCharacterOfZHat` to `G_{ℚ_p}`.

This generalizes `ContinuousMonoidHom.padicGaloisCharacter` by taking the unramified factor
`φ : ℤ̂ →ₜ* G` as an explicit input rather than building it by profiniteness. When
`φ zHat.gen = δ(p)`, it restricts on `W_{ℚ_p}` to `δ.toWeilCharacter`
(`ContinuousMonoidHom.toGaloisCharacterOfZHat_weilToAbsolute_iff`). -/
def toGaloisCharacterOfZHat (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* G :=
  (δ.padicGaloisCharacterOfZHat φ).comp
    (Subgroup.quotientMkContinuousMonoidHom
      (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure)

/-- Evaluating `δ.padicGaloisCharacterOfZHat φ` on the abelianized class `(σ : G_{ℚ_p}^{ab})`
gives `δ.toGaloisCharacterOfZHat φ σ`. -/
theorem padicGaloisCharacterOfZHat_mk (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G)
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    δ.padicGaloisCharacterOfZHat φ (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      δ.toGaloisCharacterOfZHat φ σ := by
  rw [toGaloisCharacterOfZHat, coe_comp, Function.comp_apply,
    Subgroup.quotientMkContinuousMonoidHom_apply]

/-- Pointwise formula for `δ.toGaloisCharacterOfZHat φ`. -/
@[simp]
theorem toGaloisCharacterOfZHat_apply (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G)
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    δ.toGaloisCharacterOfZHat φ σ =
      δ (padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] σ)) *
        φ ((unramifiedCoordinate ℚ_[p] (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]))⁻¹) := by
  simp [toGaloisCharacterOfZHat, abelianizedLocalCyclotomicCharacter_mk]

/-- Evaluating `δ.toGaloisCharacterOfZHat φ` on a lift of `geometricArtinMap ℚ_[p] x` gives
`δ (padicIntUnitsInclusion p (padicUnitPart p x)) * φ (zHat.gen ^ (x : ℚ_[p]).valuation)`. -/
theorem toGaloisCharacterOfZHat_geometricArtinMap (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G)
    (x : ℚ_[p]ˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = geometricArtinMap ℚ_[p] x) :
    δ.toGaloisCharacterOfZHat φ σ =
      δ (padicIntUnitsInclusion p (padicUnitPart p x)) *
        φ (zHat.gen ^ (x : ℚ_[p]).valuation) := by
  rw [← padicGaloisCharacterOfZHat_mk, hσ, padicGaloisCharacterOfZHat_geometricArtinMap]

/-- **Exact compatibility condition for `toGaloisCharacterOfZHat`.** `δ.toGaloisCharacterOfZHat φ`
restricts on `W_{ℚ_p}` to `δ.toWeilCharacter` if and only if `φ zHat.gen = δ(p)`. -/
theorem toGaloisCharacterOfZHat_weilToAbsolute_iff (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G) :
    (∀ w : WeilGroup ℚ_[p],
        δ.toGaloisCharacterOfZHat φ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w) ↔
      φ zHat.gen = δ (padicPrimeUnit p) := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ :=
      QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv ℚ_[p] (padicPrimeUnit p))
    have hspec := h w
    rw [toGaloisCharacterOfZHat_geometricArtinMap δ φ (padicPrimeUnit p) (weilToAbsolute ℚ_[p] w)
        (localWeilGeometricArtinEquiv_compat ℚ_[p] (padicPrimeUnit p) w hw),
      δ.toWeilCharacter_eq_of_mk_eq_localWeilGeometricArtinEquiv (padicPrimeUnit p) w hw] at hspec
    simpa using hspec
  · intro hφ w
    rw [toGaloisCharacterOfZHat_apply, padic_toWeilCharacter_apply,
      unramifiedCoordinate_weilDegree, mul_comm]
    congr 1
    conv_lhs => rw [← ofAdd_toAdd (weilDegree ℚ_[p] w), zHat.ofInt_ofAdd]
    rw [← zpow_neg, map_zpow, hφ]

/-- If `φ zHat.gen = δ(p)`, then `δ.toGaloisCharacterOfZHat φ` restricts on `W_{ℚ_p}` to
`δ.toWeilCharacter`. -/
theorem toGaloisCharacterOfZHat_weilToAbsolute (δ : ℚ_[p]ˣ →ₜ* G) (φ : zHat.{0} →ₜ* G)
    (hφ : φ zHat.gen = δ (padicPrimeUnit p)) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharacterOfZHat φ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w :=
  (δ.toGaloisCharacterOfZHat_weilToAbsolute_iff φ).mpr hφ w

/-- **Exact extension criterion to `G_{ℚ_p}`.** For a commutative `T1` topological group `G` with
continuous multiplication, a continuous character `δ : ℚ_[p]ˣ →ₜ* G` extends continuously to
`G_{ℚ_p} →ₜ* G` if and only if there is a continuous homomorphism `φ : ℤ̂ →ₜ* G` with
`φ zHat.gen = δ(p)`. -/
theorem exists_galoisCharacter_iff_exists_zHat [T1Space G] (δ : ℚ_[p]ˣ →ₜ* G) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* G,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w) ↔
      ∃ φ : zHat.{0} →ₜ* G, φ zHat.gen = δ (padicPrimeUnit p) := by
  constructor
  · rintro ⟨χ, hχ⟩
    let φ : zHat.{0} →ₜ* G :=
      ((TopologicalAbelianization.lift χ).comp
        ((padicAbsoluteGaloisGroupAbelianizationEquiv p).symm :
          zHat.{0} × ℤ_[p]ˣ →ₜ* Field.absoluteGaloisGroupAbelianization ℚ_[p])).comp
        ((ContinuousMulEquiv.inv zHat.{0} : zHat.{0} →ₜ* zHat.{0}).prod 1)
    have hφ (z : zHat.{0}) :
        φ z = TopologicalAbelianization.lift χ
          ((padicAbsoluteGaloisGroupAbelianizationEquiv p).symm (z⁻¹, 1)) := by
      simp [φ]
    have hgen : (padicAbsoluteGaloisGroupAbelianizationEquiv p).symm (zHat.gen⁻¹, 1) =
        geometricArtinMap ℚ_[p] (padicPrimeUnit p) := by
      apply (padicAbsoluteGaloisGroupAbelianizationEquiv p).injective
      rw [ContinuousMulEquiv.apply_symm_apply,
        padicAbsoluteGaloisGroupAbelianizationEquiv_geometricArtinMap]
      simp
    refine ⟨φ, ?_⟩
    rw [hφ, hgen, lift_geometricArtinMap_eq_of_weilToAbsolute hχ]
  · rintro ⟨φ, hφ⟩
    exact ⟨δ.toGaloisCharacterOfZHat φ, δ.toGaloisCharacterOfZHat_weilToAbsolute φ hφ⟩

/-- Equivalent form of the extension criterion in terms of the dense subgroup `ℤ → ℤ̂`: for a
commutative `T1` topological group `G` with continuous multiplication, `δ` extends to `G_{ℚ_p}` if
and only if `n ↦ δ(p) ^ n` extends continuously along `zHat.ofInt`. -/
theorem exists_galoisCharacter_iff_exists_zHat_ofInt [T1Space G] (δ : ℚ_[p]ˣ →ₜ* G) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* G,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w) ↔
      ∃ φ : zHat.{0} →ₜ* G, ∀ n : ℤ,
        φ (zHat.ofInt (.ofAdd n)) = δ (padicPrimeUnit p) ^ n := by
  rw [δ.exists_galoisCharacter_iff_exists_zHat]
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ, fun n ↦ by rw [zHat.ofInt_ofAdd, map_zpow, hφ]⟩,
    fun ⟨φ, hφ⟩ ↦ ⟨φ, by simpa using hφ 1⟩⟩

/-- Continuous Galois extension when `δ(p)` has finite order in `G` (for any commutative
topological group `G` with continuous multiplication), built via `zHat.liftOfFinOrder`. -/
def toGaloisCharacterOfFinOrderAtPrime (δ : ℚ_[p]ˣ →ₜ* G)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* G :=
  δ.toGaloisCharacterOfZHat (zHat.liftOfFinOrder hfin)

/-- `toGaloisCharacterOfFinOrderAtPrime` restricts on `W_{ℚ_p}` to `δ.toWeilCharacter`. -/
theorem toGaloisCharacterOfFinOrderAtPrime_weilToAbsolute (δ : ℚ_[p]ˣ →ₜ* G)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharacterOfFinOrderAtPrime hfin (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w :=
  δ.toGaloisCharacterOfZHat_weilToAbsolute _ (zHat.liftOfFinOrder_gen hfin) w

end CommGroup

section Profinite

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- For a profinite commutative topological group `A`, `padicGaloisCharacter δ` restricts on
`W_{ℚ_p}` (via `G_{ℚ_p}^{ab}`) to `δ.toWeilCharacter`. -/
theorem padicGaloisCharacter_weilToAbsolute (δ : ℚ_[p]ˣ →ₜ* A) (w : WeilGroup ℚ_[p]) :
    padicGaloisCharacter δ
        (weilToAbsolute ℚ_[p] w : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      δ.toWeilCharacter w := by
  have h :
      padicGaloisCharacter δ
          (weilToAbsolute ℚ_[p] w : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
        δ.toGaloisCharacterOfZHat (zHat.lift (δ (padicPrimeUnit p))) (weilToAbsolute ℚ_[p] w) := by
    rw [padicGaloisCharacter_eq_padicGaloisCharacterOfZHat, padicGaloisCharacterOfZHat_mk]
  exact h.trans (δ.toGaloisCharacterOfZHat_weilToAbsolute _ (zHat.lift_gen _) w)

end Profinite

end GaloisExtension

end ContinuousMonoidHom

namespace TauCeti

open TauCeti.ClassFieldTheory

/-! ### Exact unitary extendability over a nonarchimedean local field `L` -/

section UnitaryExtension

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Continuous Galois extension of a unitary character `δ : ℚ_[p]ˣ →ₜ* Lˣ` into a nonarchimedean
local field `L`, built via `zHatLiftUnitFiltration` into the profinite unit group `U(L, 0)`. -/
def PadicUnitsCharacter.toGaloisCharacterOfUnitary (δ : PadicUnitsCharacter p L)
    (hδ : δ.IsUnitary) : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ :=
  δ.toGaloisCharacterOfZHat (zHatLiftUnitFiltration (δ (padicPrimeUnit p))
    ((PadicUnitsCharacter.isUnitary_iff_valuation_padicPrimeUnit_eq_one δ).mp hδ))

/-- `toGaloisCharacterOfUnitary` restricts on `W_{ℚ_p}` to `δ.toWeilCharacter`. -/
theorem PadicUnitsCharacter.toGaloisCharacterOfUnitary_weilToAbsolute
    (δ : PadicUnitsCharacter p L) (hδ : δ.IsUnitary) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharacterOfUnitary hδ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w :=
  δ.toGaloisCharacterOfZHat_weilToAbsolute _
    (zHatLiftUnitFiltration_gen _
      ((PadicUnitsCharacter.isUnitary_iff_valuation_padicPrimeUnit_eq_one δ).mp hδ)) w

/-- **Exact unitary criterion for Galois extension over a local field.** For any nonarchimedean
local field `L`, a continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` extends continuously to
`G_{ℚ_p} →ₜ* Lˣ` if and only if `δ` is unitary (`v_L(δ(p)) = 1`). -/
theorem PadicUnitsCharacter.exists_galoisCharacter_iff_isUnitary (δ : PadicUnitsCharacter p L) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilCharacter w) ↔ δ.IsUnitary := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := δ.exists_galoisCharacter_iff_exists_zHat.mp h
    rw [PadicUnitsCharacter.isUnitary_iff_valuation_padicPrimeUnit_eq_one, ← hφ]
    exact φ.valuation_apply_eq_one zHat.gen
  · intro hδ
    exact ⟨δ.toGaloisCharacterOfUnitary hδ, δ.toGaloisCharacterOfUnitary_weilToAbsolute hδ⟩

end UnitaryExtension

/-! ### Canonical character identifications and the non-unitary counterexample -/

section CanonicalChecks

variable (p : ℕ) [Fact p.Prime]

/-- **Cyclotomic character check.** Under Colmez's normalization, the unitary character
`x ↦ x |x|_p` (`TauCeti.padicUnitPart p`) corresponds on `W_{ℚ_p}` to the `p`-adic cyclotomic
character. -/
theorem continuousLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilCharacter_padicUnitPart
    (w : WeilGroup ℚ_[p]) :
    continuousLocalCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) =
      (padicUnitPart p).toWeilCharacter w := by
  rw [ContinuousMonoidHom.padic_toWeilCharacter_apply, padicUnitPart_padicPrimeUnit, one_zpow,
    one_mul, padicUnitPart_padicIntUnitsInclusion, continuousLocalCyclotomicCharacter_apply]

/-- **Mod-`p` cyclotomic character check.** Under Colmez's normalization, `ω` corresponds on
`W_{ℚ_p}` to `modPLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilCharacter_padicModPCyclotomicCharacter
    (w : WeilGroup ℚ_[p]) :
    modPLocalCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) =
      (padicModPCyclotomicCharacter p).toWeilCharacter w := by
  apply Units.ext
  rw [ContinuousMonoidHom.padic_toWeilCharacter_apply,
    padicModPCyclotomicCharacter_padicPrimeUnit, one_zpow, one_mul,
    coe_padicModPCyclotomicCharacter_padicIntUnitsInclusion,
    coe_modPLocalCyclotomicCharacter_apply]

/-- The unique continuous Galois extension of `padicModPCyclotomicCharacter p` (`ω`) is
`modPLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem padicGaloisCharacter_padicModPCyclotomicCharacter
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    ContinuousMonoidHom.padicGaloisCharacter (padicModPCyclotomicCharacter p)
        (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      modPLocalCyclotomicCharacter p ℚ_[p] σ := by
  rw [ContinuousMonoidHom.padicGaloisCharacter_eq_padicGaloisCharacterOfZHat,
    ContinuousMonoidHom.padicGaloisCharacterOfZHat_mk]
  have h : (padicModPCyclotomicCharacter p).toGaloisCharacterOfZHat
        (zHat.lift ((padicModPCyclotomicCharacter p) (padicPrimeUnit p))) =
      modPLocalCyclotomicCharacter p ℚ_[p] :=
    galoisCharacter_eq_of_weilToAbsolute_eq fun w ↦ by
      rw [(padicModPCyclotomicCharacter p).toGaloisCharacterOfZHat_weilToAbsolute _
          (zHat.lift_gen _) w,
        modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilCharacter_padicModPCyclotomicCharacter]
  exact DFunLike.congr_fun h σ

section NonUnitary

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra ℚ_[p] L]

/-- **Non-extendability of `x ↦ algebraMap ℚ_[p] L x`.** For any nonarchimedean local field `L`
with a continuous `ℚ_[p]`-algebra structure (including `ℚ_[p]` itself and its finite extensions),
the character `x ↦ algebraMap ℚ_[p] L x` does not extend continuously from `W_{ℚ_p}` to
`G_{ℚ_p}`. -/
theorem not_exists_galoisCharacter_padicAlgebraMapCharacter (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ,
      ∀ w : WeilGroup ℚ_[p],
        χ (weilToAbsolute ℚ_[p] w) = (padicAlgebraMapCharacter p L h).toWeilCharacter w := by
  rw [PadicUnitsCharacter.exists_galoisCharacter_iff_isUnitary]
  exact not_isUnitary_padicAlgebraMapCharacter p L h

/-- Equivalently, the map `n ↦ (p : L) ^ n` does not extend to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ`. -/
theorem not_exists_zHat_padicPrimeUnit (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ ∃ φ : zHat.{0} →ₜ* Lˣ,
      φ zHat.gen = Units.map (algebraMap ℚ_[p] L).toMonoidHom (padicPrimeUnit p) := by
  intro ⟨φ, hφ⟩
  refine not_exists_galoisCharacter_padicAlgebraMapCharacter p L h ?_
  rw [ContinuousMonoidHom.exists_galoisCharacter_iff_exists_zHat]
  refine ⟨φ, hφ.trans (Units.ext ?_)⟩
  simp

end NonUnitary

end CanonicalChecks

end TauCeti
