/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Rationals

/-!
# Local Kronecker–Weber for `ℚ_p`

The unramified coordinate `unramifiedCoordinate ℚ_[p] : G_{ℚ_p}^{ab} →ₜ* ℤ̂` and the
abelianized `p`-adic cyclotomic character `abelianizedLocalCyclotomicCharacter p ℚ_[p]` combine
into a topological group isomorphism

`TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv p :`
`  G_{ℚ_p}^{ab} ≃ₜ* ℤ̂ × ℤ_[p]ˣ`,

identifying the arithmetic local Artin symbol of `x = p ^ v_p(x) * u` with
`(zHat.gen ^ v_p(x), u⁻¹)` and the geometric Artin symbol with `(zHat.gen ^ (-v_p(x)), u)`.

## Main definitions

* `TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv`: the topological group
  isomorphism `Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃ₜ* zHat.{0} × ℤ_[p]ˣ`.

## Main results

* `TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv_apply`: componentwise
  evaluation of the isomorphism.
* `TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv_artinMap` and
  `TauCeti.ClassFieldTheory.padicAbsoluteGaloisGroupAbelianizationEquiv_geometricArtinMap`:
  images of the arithmetic and geometric Artin symbols.

## References

* J.-P. Serre, *Local Class Field Theory*, in *Algebraic Number Theory* (J. W. S. Cassels and
  A. Fröhlich, eds.), Academic Press, 1967, Chapter VI, §3.
* J. S. Milne, *Class Field Theory*, Chapter I, Local Kronecker–Weber.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti.ClassFieldTheory

variable (p : ℕ) [Fact p.Prime]

/-- The continuous product homomorphism `G_{ℚ_p}^{ab} →ₜ* ℤ̂ × ℤ_[p]ˣ` recording the unramified
coordinate and the `p`-adic cyclotomic character. -/
private def padicAbelianizationProdHom :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* zHat.{0} × ℤ_[p]ˣ :=
  (unramifiedCoordinate ℚ_[p]).prod (abelianizedLocalCyclotomicCharacter p ℚ_[p])

private theorem padicAbelianizationProdHom_apply
    (y : Field.absoluteGaloisGroupAbelianization ℚ_[p]) :
    padicAbelianizationProdHom p y =
      (unramifiedCoordinate ℚ_[p] y, abelianizedLocalCyclotomicCharacter p ℚ_[p] y) :=
  (rfl)

private theorem padicAbelianizationProdHom_artinMap (x : ℚ_[p]ˣ) :
    padicAbelianizationProdHom p (artinMap ℚ_[p] x) =
      (zHat.gen ^ (x : ℚ_[p]).valuation, (padicUnitPart p x)⁻¹) := by
  rw [padicAbelianizationProdHom_apply, unramifiedCoordinate_artinMap,
    ← ofAdd_toAdd (normalizedValuation ℚ_[p] x),
    _root_.Padic.toAdd_normalizedValuation_eq_valuation, zHat.ofInt_ofAdd,
    abelianizedLocalCyclotomicCharacter_artinMap_padicUnitPart]

/-- `padicAbelianizationProdHom p` is injective: classes with trivial unramified coordinate are
Artin symbols of units `u ∈ ℤ_[p]ˣ`, and the cyclotomic character recovers `u⁻¹`. -/
private theorem padicAbelianizationProdHom_injective :
    Function.Injective (padicAbelianizationProdHom p) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : unramifiedCoordinate ℚ_[p] y = 1 :=
    congrArg Prod.fst ((padicAbelianizationProdHom_apply p y).symm.trans hy)
  have hmem : y ∈ (unitFiltration ℚ_[p] 0).map (artinMap ℚ_[p]) := by
    rw [map_artinMap_unitFiltration_zero, ← ker_unramifiedCoordinate]
    exact h1
  obtain ⟨u, hu, rfl⟩ := hmem
  have hy' : (zHat.gen ^ (u : ℚ_[p]).valuation, (padicUnitPart p u)⁻¹) = 1 := by
    rw [← padicAbelianizationProdHom_artinMap, hy]
  have hunit : padicUnitPart p u = 1 := inv_eq_one.mp (congrArg Prod.snd hy')
  have hnv : normalizedValuation ℚ_[p] u = 1 :=
    (normalizedValuation_eq_one_iff u).mpr ((mem_unitFiltration_zero u).mp hu)
  have hval : (u : ℚ_[p]).valuation = 0 := by
    rw [← _root_.Padic.toAdd_normalizedValuation_eq_valuation, hnv, toAdd_one]
  have hu1 : u = 1 := by
    rw [eq_padicPrimeUnit_zpow_mul_padicUnitPart p u, hval, zpow_zero, one_mul, hunit, map_one]
  rw [hu1, map_one]

/-- `padicAbelianizationProdHom p` is surjective: its compact image is closed and contains the dense
set `(range zHat.ofInt) ×ˢ univ`, hit by the Artin symbols of `p ^ n * u⁻¹`. -/
private theorem padicAbelianizationProdHom_surjective :
    Function.Surjective (padicAbelianizationProdHom p) := by
  have hclosed : IsClosed (Set.range (padicAbelianizationProdHom p)) :=
    (isCompact_range (padicAbelianizationProdHom p).continuous).isClosed
  have hsub : (Set.range (zHat.ofInt : Multiplicative ℤ →* zHat.{0})) ×ˢ (Set.univ : Set ℤ_[p]ˣ) ⊆
      Set.range (padicAbelianizationProdHom p) := by
    rintro ⟨_, u⟩ ⟨⟨n, rfl⟩, -⟩
    let x : ℚ_[p]ˣ := padicPrimeUnit p ^ n.toAdd * padicIntUnitsInclusion p u⁻¹
    have hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ n.toAdd * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_padicPrimeUnit,
        coe_padicIntUnitsInclusion_apply]
    have hval : (x : ℚ_[p]).valuation = n.toAdd := TauCeti.Padic.valuation_eq_of_eq hx
    have hunit : padicUnitPart p x = u⁻¹ := padicUnitPart_apply_of_eq hx
    refine ⟨artinMap ℚ_[p] x, ?_⟩
    rw [padicAbelianizationProdHom_artinMap, hval, hunit, inv_inv, ← zHat.ofInt_ofAdd,
      ofAdd_toAdd]
  have hdense : Dense
      ((Set.range (zHat.ofInt : Multiplicative ℤ →* zHat.{0})) ×ˢ (Set.univ : Set ℤ_[p]ˣ)) :=
    zHat.denseRange_ofInt.prod dense_univ
  intro z
  have hz : z ∈ closure (Set.range (padicAbelianizationProdHom p)) :=
    closure_mono hsub (hdense z)
  rwa [hclosed.closure_eq] at hz

/-- **Local Kronecker–Weber for `ℚ_[p]`.** The unramified coordinate and the `p`-adic cyclotomic
character identify the abelianized absolute Galois group `G_{ℚ_p}^{ab}` topologically with
`ℤ̂ × ℤ_[p]ˣ`. -/
def padicAbsoluteGaloisGroupAbelianizationEquiv :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃ₜ* zHat.{0} × ℤ_[p]ˣ :=
  let e : Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃* zHat.{0} × ℤ_[p]ˣ :=
    MulEquiv.ofBijective (padicAbelianizationProdHom p).toMonoidHom
      ⟨padicAbelianizationProdHom_injective p, padicAbelianizationProdHom_surjective p⟩
  ContinuousMulEquiv.mk e (padicAbelianizationProdHom p).continuous
    ((padicAbelianizationProdHom p).continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.toEquiv))

/-- Evaluating `padicAbsoluteGaloisGroupAbelianizationEquiv p` gives the pair of the unramified
coordinate and the abelianized `p`-adic cyclotomic character. -/
@[simp]
theorem padicAbsoluteGaloisGroupAbelianizationEquiv_apply
    (y : Field.absoluteGaloisGroupAbelianization ℚ_[p]) :
    padicAbsoluteGaloisGroupAbelianizationEquiv p y =
      (unramifiedCoordinate ℚ_[p] y, abelianizedLocalCyclotomicCharacter p ℚ_[p] y) :=
  (rfl)

/-- Under `padicAbsoluteGaloisGroupAbelianizationEquiv p`, the arithmetic Artin symbol of
`x = p ^ v_p(x) * u` maps to `(zHat.gen ^ v_p(x), u⁻¹)`. -/
theorem padicAbsoluteGaloisGroupAbelianizationEquiv_artinMap (x : ℚ_[p]ˣ) :
    padicAbsoluteGaloisGroupAbelianizationEquiv p (artinMap ℚ_[p] x) =
      (zHat.gen ^ (x : ℚ_[p]).valuation, (padicUnitPart p x)⁻¹) :=
  padicAbelianizationProdHom_artinMap p x

/-- Under `padicAbsoluteGaloisGroupAbelianizationEquiv p`, the geometric Artin symbol of
`x = p ^ v_p(x) * u` maps to `(zHat.gen ^ (-v_p(x)), u)`. -/
theorem padicAbsoluteGaloisGroupAbelianizationEquiv_geometricArtinMap (x : ℚ_[p]ˣ) :
    padicAbsoluteGaloisGroupAbelianizationEquiv p (geometricArtinMap ℚ_[p] x) =
      (zHat.gen ^ (-(x : ℚ_[p]).valuation), padicUnitPart p x) := by
  rw [geometricArtinMap_apply, map_inv,
    padicAbsoluteGaloisGroupAbelianizationEquiv_artinMap, Prod.inv_mk, inv_inv, zpow_neg]

end TauCeti.ClassFieldTheory
