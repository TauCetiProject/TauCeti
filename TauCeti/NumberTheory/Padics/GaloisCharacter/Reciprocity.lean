/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GaloisCharacter
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Reciprocity
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.Padics.GaloisCharacter.Basic
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod
public import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.NumberTheory.Cyclotomic.ModularCharacter
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Characters of `ℚ_pˣ` as Weil and Galois characters

By local class field theory, the multiplicative group `ℚ_[p]ˣ` is canonically identified with the
topological abelianization `W_{ℚ_p}^{ab}` of the local Weil group via geometric Weil reciprocity
`TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv ℚ_[p]`. In Colmez's convention, this
identification sends the uniformizer `p` to a geometric Frobenius (the inverse of an arithmetic
Frobenius lift) and identifies Colmez's character `x ↦ x |x|_p` (`TauCeti.padicUnitPart p`) with
the `p`-adic cyclotomic character `χ_cyc`.

This file builds the full dictionary between continuous characters `δ : ℚ_[p]ˣ →ₜ* Λˣ`, continuous
characters of the local Weil group `W_{ℚ_p} →ₜ* Λˣ`, and continuous characters of the absolute
Galois group `G_{ℚ_p} →ₜ* Λˣ`:

1. **Local Kronecker–Weber for `ℚ_[p]`** (`TauCeti.padicAbelianizationEquiv`): the topological
   group isomorphism `G_{ℚ_p}^{ab} ≃ₜ* ℤ̂ × ℤ_[p]ˣ` given by the unramified coordinate and the
   `p`-adic cyclotomic character, yielding the explicit Colmez inverse formula
   `w ↦ p ^ (-deg w) * χ_cyc(w)` on `W_{ℚ_p}`
   (`TauCeti.localWeilGeometricArtinEquiv_symm_padic_mk`).
2. **Weil character dictionary** (`TauCeti.PadicUnitsChar.toWeilChar`,
   `TauCeti.padicUnitsCharEquivWeilChar`): every `δ : PadicUnitsChar p Λ` induces a continuous
   Weil character `δ.toWeilChar : W_{ℚ_p} →ₜ* Λˣ` with formula
   `δ.toWeilChar w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`; when `Λ` is commutative and `T1`, this is a
   group isomorphism `PadicUnitsChar p Λ ≃* (W_{ℚ_p} →ₜ* Λˣ)`.
3. **Extension to `G_{ℚ_p}`**: since `W_{ℚ_p}` is dense in `G_{ℚ_p}`, an extension to
   `G_{ℚ_p} →ₜ* Λˣ` is unique when `Λ` is Hausdorff (`TauCeti.galoisChar_eq_of_weilToAbsolute_eq`).
   For commutative `T1` topological monoids `Λ`, a continuous extension exists if and only if
   `n ↦ δ(p)^n` extends to a continuous homomorphism `ℤ̂ →ₜ* Λˣ`
   (`TauCeti.PadicUnitsChar.exists_galoisChar_iff_exists_zHat`). In particular, an extension always
   exists when `Λˣ` is profinite (including `ℤ_[p]`, `𝒪[L]`, `ZMod p`, `𝓀[L]`) or when `δ(p)` has
   finite order.
4. **Unitary criterion over a local field `L`**: for any nonarchimedean local field `L`, a
   character `δ : PadicUnitsChar p L` extends continuously to `G_{ℚ_p} →ₜ* Lˣ` if and only if
   `δ` is unitary (`v_L(δ(p)) = 1`, equivalently `v_L(δ(x)) = 1` for all `x ∈ ℚ_[p]ˣ`;
   `TauCeti.PadicUnitsChar.exists_galoisChar_iff_isUnitary`).
5. **Canonical identifications**: under this dictionary, `x ↦ x |x|_p` corresponds to
   `continuousLocalCyclotomicCharacter p ℚ_[p]`, `ω` corresponds to the mod-`p` cyclotomic
   character (`TauCeti.modPLocalCyclotomicCharacter p`), an unramified character `μ_a` is trivial
   on inertia and evaluates to `a` on geometric Frobenius lifts (`a⁻¹` on arithmetic Frobenius
   lifts), and `x ↦ algebraMap ℚ_[p] L x` (for any `FinitePadicExtension L p`, including `ℚ_[p]`)
   is not unitary and admits no continuous Galois extension.

## Main definitions

* `TauCeti.padicAbelianizationEquiv`: the topological group isomorphism
  `Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃ₜ* zHat.{0} × ℤ_[p]ˣ`.
* `TauCeti.PadicUnitsChar.toWeilChar`: the continuous Weil character `W_{ℚ_p} →ₜ* Λˣ` associated
  to `δ : PadicUnitsChar p Λ`.
* `TauCeti.padicUnitsCharEquivWeilChar`: the group isomorphism
  `PadicUnitsChar p Λ ≃* (WeilGroup ℚ_[p] →ₜ* Λˣ)` for commutative `T1` monoids `Λ`.
* `TauCeti.PadicUnitsChar.toGaloisCharOfZHat`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfProfiniteUnits`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfProfinite`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfFinOrder`,
  `TauCeti.PadicUnitsChar.toGaloisCharOfUnitary`: continuous Galois extensions `G_{ℚ_p} →ₜ* Λˣ`.
* `TauCeti.PadicUnitsChar.IsUnitary`: unitarity predicate `ValuativeRel.valuation L (δ p) = 1`.
* `TauCeti.modPLocalCyclotomicCharacter`: the mod-`p` cyclotomic character
  `G_{ℚ_p} →ₜ* (ZMod p)ˣ`.

## References

* P. Colmez, *Représentations de GL₂(ℚ_p) et (φ, Γ)-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField TauCeti.ClassFieldTheory

namespace TauCeti

/-- A continuous injective map into a totally disconnected space forces its domain to be totally
disconnected. -/
private theorem totallyDisconnectedSpace_of_injective_continuous {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hinj : Function.Injective f) (hcont : Continuous f) :
    TotallyDisconnectedSpace X :=
  ⟨isTotallyDisconnected_of_image hcont.continuousOn hinj
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-! ### Local Kronecker–Weber for `ℚ_[p]` and the explicit Colmez inverse formula -/

section LocalKroneckerWeber

variable (p : ℕ) [Fact p.Prime]

/-- The continuous product homomorphism `G_{ℚ_p}^{ab} →ₜ* ℤ̂ × ℤ_[p]ˣ` recording the unramified
coordinate and the `p`-adic cyclotomic character. -/
private def padicAbelianizationProdHom :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* zHat.{0} × ℤ_[p]ˣ :=
  (unramifiedCoordinate ℚ_[p]).prod (abelianizedLocalCyclotomicCharacter p ℚ_[p])

/-- `padicAbelianizationProdHom p` is injective: classes with trivial unramified coordinate are
Artin symbols of units `u ∈ ℤ_[p]ˣ`, and the cyclotomic character recovers `u⁻¹`. -/
private theorem padicAbelianizationProdHom_injective :
    Function.Injective (padicAbelianizationProdHom p) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : unramifiedCoordinate ℚ_[p] y = 1 := congrArg Prod.fst hy
  have h2 : abelianizedLocalCyclotomicCharacter p ℚ_[p] y = 1 := congrArg Prod.snd hy
  have hmem : y ∈ (unitFiltration ℚ_[p] 0).map (artinMap ℚ_[p]) := by
    rw [map_artinMap_unitFiltration_zero, ← ker_unramifiedCoordinate]
    exact h1
  obtain ⟨u, hu, rfl⟩ := hmem
  let v : ℤ_[p]ˣ := unitFiltrationZeroPadicEquiv p ⟨u, hu⟩
  have huv : (u : ℚ_[p]) = (p : ℚ_[p]) ^ (0 : ℤ) * (v : ℤ_[p]) := by
    rw [zpow_zero, one_mul, coe_unitFiltrationZeroPadicEquiv_apply]
  have hv : v⁻¹ = 1 := by
    rw [← abelianizedLocalCyclotomicCharacter_artinMap_padic p huv, h2]
  have hu1 : u = 1 := Units.ext <| by
    rw [huv, zpow_zero, one_mul, inv_eq_one.mp hv, Units.val_one, PadicInt.coe_one, Units.val_one]
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
    refine ⟨artinMap ℚ_[p] x, Prod.ext ?_ ?_⟩
    · -- Unfold the first projection of `padicAbelianizationProdHom`.
      change unramifiedCoordinate ℚ_[p] (artinMap ℚ_[p] x) = zHat.ofInt n
      rw [unramifiedCoordinate_artinMap]
      congr 1
      simp [x, ← ofAdd_zsmul, ofAdd_toAdd]
    · -- Unfold the second projection of `padicAbelianizationProdHom`.
      change abelianizedLocalCyclotomicCharacter p ℚ_[p] (artinMap ℚ_[p] x) = u
      have hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ n.toAdd * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_padicPrimeUnit,
          coe_padicIntUnitsInclusion_apply]
      rw [abelianizedLocalCyclotomicCharacter_artinMap_padic p hx, inv_inv]
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
def padicAbelianizationEquiv :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃ₜ* zHat.{0} × ℤ_[p]ˣ :=
  let e : Field.absoluteGaloisGroupAbelianization ℚ_[p] ≃* zHat.{0} × ℤ_[p]ˣ :=
    MulEquiv.ofBijective (padicAbelianizationProdHom p).toMonoidHom
      ⟨padicAbelianizationProdHom_injective p, padicAbelianizationProdHom_surjective p⟩
  ContinuousMulEquiv.mk e (padicAbelianizationProdHom p).continuous
    ((padicAbelianizationProdHom p).continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.toEquiv))

/-- Evaluating `padicAbelianizationEquiv p` gives the pair of the unramified coordinate and the
abelianized `p`-adic cyclotomic character. -/
@[simp]
theorem padicAbelianizationEquiv_apply (y : Field.absoluteGaloisGroupAbelianization ℚ_[p]) :
    padicAbelianizationEquiv p y =
      (unramifiedCoordinate ℚ_[p] y, abelianizedLocalCyclotomicCharacter p ℚ_[p] y) :=
  (rfl)

/-- Under `padicAbelianizationEquiv p`, the arithmetic Artin symbol of `x = p ^ v_p(x) * u` maps
to `(zHat.gen ^ v_p(x), u⁻¹)`. -/
theorem padicAbelianizationEquiv_artinMap (x : ℚ_[p]ˣ) :
    padicAbelianizationEquiv p (artinMap ℚ_[p] x) =
      (zHat.gen ^ (x : ℚ_[p]).valuation, (padicUnitPart p x)⁻¹) := by
  refine Prod.ext ?_ ?_
  · rw [padicAbelianizationEquiv_apply, unramifiedCoordinate_artinMap,
      ← ofAdd_toAdd (normalizedValuation ℚ_[p] x),
      _root_.Padic.toAdd_normalizedValuation_eq_valuation, zHat.ofInt_ofAdd]
  · rw [padicAbelianizationEquiv_apply,
      abelianizedLocalCyclotomicCharacter_artinMap_padicUnitPart]

/-- Under `padicAbelianizationEquiv p`, the geometric Artin symbol of `x = p ^ v_p(x) * u` maps
to `(zHat.gen ^ (-v_p(x)), u)`. -/
theorem padicAbelianizationEquiv_geometricArtinMap (x : ℚ_[p]ˣ) :
    padicAbelianizationEquiv p (geometricArtinMap ℚ_[p] x) =
      (zHat.gen ^ (-(x : ℚ_[p]).valuation), padicUnitPart p x) := by
  rw [geometricArtinMap_apply, map_inv, padicAbelianizationEquiv_artinMap, Prod.inv_mk,
    inv_inv, zpow_neg]

/-- **Explicit Colmez inverse reciprocity formula on `W_{ℚ_p}`.** Under the inverse of geometric
local reciprocity `W_{ℚ_p}^{ab} ≃ₜ* ℚ_[p]ˣ`, a Weil element `w` maps to
`p ^ (-deg w) * χ_cyc(w)`. -/
theorem localWeilGeometricArtinEquiv_symm_padic_mk (w : WeilGroup ℚ_[p]) :
    (localWeilGeometricArtinEquiv ℚ_[p]).symm
        (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup ℚ_[p])) =
      padicPrimeUnit p ^ (-(weilDegree ℚ_[p] w).toAdd) *
        padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w)) := by
  apply (localWeilGeometricArtinEquiv ℚ_[p]).injective
  apply injective_weilToAbsoluteAbelianization ℚ_[p]
  apply (padicAbelianizationEquiv p).injective
  rw [ContinuousMulEquiv.apply_symm_apply, weilToAbsoluteAbelianization_mk,
    weilToAbsoluteAbelianization_localWeilGeometricArtinEquiv,
    padicAbelianizationEquiv_apply, padicAbelianizationEquiv_geometricArtinMap,
    unramifiedCoordinate_weilDegree, abelianizedLocalCyclotomicCharacter_mk]
  let x : ℚ_[p]ˣ := padicPrimeUnit p ^ (-(weilDegree ℚ_[p] w).toAdd) *
    padicIntUnitsInclusion p (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w))
  have hx_eq : padicUnitsEquivIntProd p x =
      (.ofAdd (-(weilDegree ℚ_[p] w).toAdd),
        localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w)) :=
    padicUnitsEquivIntProd_eq_of_decomposition p x (-(weilDegree ℚ_[p] w).toAdd)
      (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w)) (by simp [x])
  have hval : (x : ℚ_[p]).valuation = -(weilDegree ℚ_[p] w).toAdd := by
    have h1 := congrArg (Multiplicative.toAdd ∘ Prod.fst) hx_eq
    simpa [padicUnitsEquivIntProd_apply_fst] using h1
  have hunit : padicUnitPart p x =
      localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) := by
    simpa [padicUnitsEquivIntProd_apply_snd] using congrArg Prod.snd hx_eq
  refine Prod.ext ?_ hunit.symm
  rw [hval, neg_neg]
  conv_lhs => rw [← ofAdd_toAdd (weilDegree ℚ_[p] w), zHat.ofInt_ofAdd]

end LocalKroneckerWeber

/-! ### Continuous characters of the local Weil group `W_{ℚ_p}` -/

section WeilCharacters

variable {p : ℕ} [Fact p.Prime]

section Monoid

variable {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ]

/-- The continuous character `W_{ℚ_p} →ₜ* Λˣ` corresponding to `δ : PadicUnitsChar p Λ` via
Colmez's geometric local reciprocity isomorphism `ℚ_[p]ˣ ≃ₜ* W_{ℚ_p}^{ab}`. -/
def PadicUnitsChar.toWeilChar (δ : PadicUnitsChar p Λ) : WeilGroup ℚ_[p] →ₜ* Λˣ :=
  (δ.comp ((localWeilGeometricArtinEquiv ℚ_[p]).symm :
      TopologicalAbelianization (WeilGroup ℚ_[p]) →ₜ* ℚ_[p]ˣ)).comp
    (Subgroup.quotientMkContinuousMonoidHom (commutator (WeilGroup ℚ_[p])).topologicalClosure)

/-- **Colmez's formula on the local Weil group.** For every `w ∈ W_{ℚ_p}`,
`δ.toWeilChar w = δ(p) ^ (-deg w) * δ(χ_cyc(w))`. -/
theorem PadicUnitsChar.toWeilChar_apply (δ : PadicUnitsChar p Λ) (w : WeilGroup ℚ_[p]) :
    δ.toWeilChar w =
      δ (padicPrimeUnit p) ^ (-(weilDegree ℚ_[p] w).toAdd) *
        δ (padicIntUnitsInclusion p
          (localCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w))) := by
  simp only [PadicUnitsChar.toWeilChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    Subgroup.quotientMkContinuousMonoidHom_apply, ContinuousMonoidHom.coe_coe]
  rw [localWeilGeometricArtinEquiv_symm_padic_mk, map_mul, map_zpow]

/-- If `w ∈ W_{ℚ_p}` represents `localWeilGeometricArtinEquiv ℚ_[p] x`, then
`δ.toWeilChar w = δ x`. -/
theorem PadicUnitsChar.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv
    (δ : PadicUnitsChar p Λ) (x : ℚ_[p]ˣ) (w : WeilGroup ℚ_[p])
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup ℚ_[p])) =
      localWeilGeometricArtinEquiv ℚ_[p] x) :
    δ.toWeilChar w = δ x := by
  simp only [PadicUnitsChar.toWeilChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    Subgroup.quotientMkContinuousMonoidHom_apply, ContinuousMonoidHom.coe_coe]
  rw [hw, ContinuousMulEquiv.symm_apply_apply]

/-- The trivial character of `ℚ_[p]ˣ` corresponds to the trivial Weil character. -/
@[simp]
theorem PadicUnitsChar.toWeilChar_one : (1 : PadicUnitsChar p Λ).toWeilChar = 1 := by
  ext1 _
  rfl

end Monoid

section CommMonoid

variable {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]

/-- `toWeilChar` preserves products of characters. -/
@[simp]
theorem PadicUnitsChar.toWeilChar_mul (δ₁ δ₂ : PadicUnitsChar p Λ) :
    (δ₁ * δ₂).toWeilChar = δ₁.toWeilChar * δ₂.toWeilChar := by
  ext1 _
  rfl

/-- `toWeilChar` preserves inverses of characters. -/
@[simp]
theorem PadicUnitsChar.toWeilChar_inv (δ : PadicUnitsChar p Λ) :
    δ⁻¹.toWeilChar = δ.toWeilChar⁻¹ := by
  ext1 _
  rfl

variable (p Λ) in
/-- **Identification of `ℚ_[p]ˣ`-characters with Weil group characters.** For a commutative `T1`
topological monoid `Λ` with continuous multiplication, Colmez's geometric reciprocity yields a
group isomorphism `PadicUnitsChar p Λ ≃* (WeilGroup ℚ_[p] →ₜ* Λˣ)`. -/
def padicUnitsCharEquivWeilChar [T1Space Λ] :
    PadicUnitsChar p Λ ≃* (WeilGroup ℚ_[p] →ₜ* Λˣ) where
  toFun := PadicUnitsChar.toWeilChar
  invFun ψ :=
    (TopologicalAbelianization.lift ψ).comp
      (localWeilGeometricArtinEquiv ℚ_[p] :
        ℚ_[p]ˣ →ₜ* TopologicalAbelianization (WeilGroup ℚ_[p]))
  left_inv δ := by
    ext1 x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv ℚ_[p] x)
    -- Unfold the round-trip composition on `x`.
    change TopologicalAbelianization.lift δ.toWeilChar (localWeilGeometricArtinEquiv ℚ_[p] x) = δ x
    rw [← hw, TopologicalAbelianization.lift_mk]
    exact δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw
  right_inv ψ := by
    ext1 w
    simp only [PadicUnitsChar.toWeilChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      Subgroup.quotientMkContinuousMonoidHom_apply, ContinuousMonoidHom.coe_coe,
      ContinuousMulEquiv.apply_symm_apply, TopologicalAbelianization.lift_mk]
  map_mul' := PadicUnitsChar.toWeilChar_mul

@[simp]
theorem padicUnitsCharEquivWeilChar_apply [T1Space Λ] (δ : PadicUnitsChar p Λ) :
    padicUnitsCharEquivWeilChar p Λ δ = δ.toWeilChar :=
  (rfl)

@[simp]
theorem padicUnitsCharEquivWeilChar_symm_apply [T1Space Λ] (ψ : WeilGroup ℚ_[p] →ₜ* Λˣ)
    (x : ℚ_[p]ˣ) :
    (padicUnitsCharEquivWeilChar p Λ).symm ψ x =
      TopologicalAbelianization.lift ψ (localWeilGeometricArtinEquiv ℚ_[p] x) :=
  (rfl)

/-- Evaluating `(padicUnitsCharEquivWeilChar p Λ).symm ψ` at `x` gives `ψ w` for any Weil element
`w` representing `localWeilGeometricArtinEquiv ℚ_[p] x`. -/
theorem padicUnitsCharEquivWeilChar_symm_apply_of_mk_eq [T1Space Λ]
    (ψ : WeilGroup ℚ_[p] →ₜ* Λˣ) (x : ℚ_[p]ˣ) (w : WeilGroup ℚ_[p])
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup ℚ_[p])) =
      localWeilGeometricArtinEquiv ℚ_[p] x) :
    (padicUnitsCharEquivWeilChar p Λ).symm ψ x = ψ w := by
  rw [padicUnitsCharEquivWeilChar_symm_apply, ← hw, TopologicalAbelianization.lift_mk]

end CommMonoid

end WeilCharacters

/-! ### Continuous extensions to the absolute Galois group `G_{ℚ_p}` -/

section GaloisExtension

variable {p : ℕ} [Fact p.Prime]

/-- **Uniqueness of continuous Galois extensions.** Because `W_{ℚ_p}` is dense in `G_{ℚ_p}`, two
continuous characters `G_{ℚ_p} →ₜ* Λˣ` into a Hausdorff monoid that agree on `W_{ℚ_p}` are
equal. -/
theorem galoisChar_eq_of_weilToAbsolute_eq {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] [T2Space Λ]
    {χ₁ χ₂ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (h : ∀ w : WeilGroup ℚ_[p], χ₁ (weilToAbsolute ℚ_[p] w) = χ₂ (weilToAbsolute ℚ_[p] w)) :
    χ₁ = χ₂ :=
  ContinuousMonoidHom.ext <|
    congrFun ((denseRange_weilToAbsolute ℚ_[p]).equalizer χ₁.continuous χ₂.continuous (funext h))

/-- The trivial character `1 : PadicUnitsChar p Λ` extends to the trivial Galois character `1`. -/
theorem PadicUnitsChar.exists_galoisChar_one {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] :
    ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = (1 : PadicUnitsChar p Λ).toWeilChar w :=
  ⟨1, fun _ ↦ rfl⟩

/-- **Compatibility with the geometric Artin map.** If `χ : G_{ℚ_p} →ₜ* Λˣ` extends `δ.toWeilChar`,
then its abelianization `χ^{ab}` satisfies `χ^{ab} (geometricArtinMap ℚ_[p] x) = δ x` for all
`x ∈ ℚ_[p]ˣ`. -/
theorem lift_geometricArtinMap_eq_of_weilToAbsolute {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [T1Space Λˣ] {δ : PadicUnitsChar p Λ} {χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (hχ : ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) (x : ℚ_[p]ˣ) :
    TopologicalAbelianization.lift χ (geometricArtinMap ℚ_[p] x) = δ x := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (localWeilGeometricArtinEquiv ℚ_[p] x)
  rw [← localWeilGeometricArtinEquiv_compat ℚ_[p] x w hw, TopologicalAbelianization.lift_mk,
    hχ w, δ.toWeilChar_eq_of_mk_eq_localWeilGeometricArtinEquiv x w hw]

/-- **Comparison with the arithmetic Artin map.** If `χ : G_{ℚ_p} →ₜ* Λˣ` extends `δ.toWeilChar`,
then its abelianization `χ^{ab}` satisfies `χ^{ab} (artinMap ℚ_[p] x) = (δ x)⁻¹` for all
`x ∈ ℚ_[p]ˣ`. -/
theorem lift_artinMap_eq_inv_of_weilToAbsolute {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [T1Space Λˣ] {δ : PadicUnitsChar p Λ} {χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (hχ : ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) (x : ℚ_[p]ˣ) :
    TopologicalAbelianization.lift χ (artinMap ℚ_[p] x) = (δ x)⁻¹ := by
  have h := lift_geometricArtinMap_eq_of_weilToAbsolute hχ x
  rw [geometricArtinMap_apply, map_inv] at h
  exact inv_eq_iff_eq_inv.mp h

section CommMonoid

variable {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]

open scoped IsMulCommutative in
/-- Given `δ : PadicUnitsChar p Λ` and a continuous homomorphism `φ : ℤ̂ →ₜ* Λˣ`, construct the
continuous Galois character `σ ↦ φ((unramifiedCoordinate σ)⁻¹) * δ(χ_cyc(σ))`. When
`φ zHat.gen = δ(p)`, this extends `δ.toWeilChar` (`toGaloisCharOfZHat_weilToAbsolute`). -/
def PadicUnitsChar.toGaloisCharOfZHat (δ : PadicUnitsChar p Λ) (φ : zHat.{0} →ₜ* Λˣ) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  ((φ.comp (ContinuousMonoidHom.inv zHat.{0})).coprod δ.toWeight).comp
    ((padicAbelianizationEquiv p :
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

/-- If `φ zHat.gen = δ(p)`, then `δ.toGaloisCharOfZHat φ` restricts on `W_{ℚ_p}` to
`δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfZHat_weilToAbsolute (δ : PadicUnitsChar p Λ)
    (φ : zHat.{0} →ₜ* Λˣ) (hφ : φ zHat.gen = δ (padicPrimeUnit p)) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfZHat φ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w := by
  rw [toGaloisCharOfZHat_apply, toWeilChar_apply, unramifiedCoordinate_weilDegree]
  congr 1
  conv_lhs => rw [← ofAdd_toAdd (weilDegree ℚ_[p] w), zHat.ofInt_ofAdd]
  rw [← zpow_neg, map_zpow, hφ]

open scoped IsMulCommutative in
/-- **Exact extension criterion to `G_{ℚ_p}`.** For a commutative `T1` topological monoid `Λ` with
continuous multiplication, a continuous character `δ : ℚ_[p]ˣ →ₜ* Λˣ` extends continuously to
`G_{ℚ_p} →ₜ* Λˣ` if and only if there is a continuous homomorphism `φ : ℤ̂ →ₜ* Λˣ` with
`φ zHat.gen = δ(p)`. -/
theorem PadicUnitsChar.exists_galoisChar_iff_exists_zHat [T1Space Λ] (δ : PadicUnitsChar p Λ) :
    (∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) ↔
      ∃ φ : zHat.{0} →ₜ* Λˣ, φ zHat.gen = δ (padicPrimeUnit p) := by
  constructor
  · rintro ⟨χ, hχ⟩
    let invMap : zHat.{0} →ₜ* zHat.{0} × ℤ_[p]ˣ :=
      (ContinuousMonoidHom.inv zHat.{0}).prod 1
    let φ : zHat.{0} →ₜ* Λˣ :=
      ((TopologicalAbelianization.lift χ).comp
        ((padicAbelianizationEquiv p).symm :
          zHat.{0} × ℤ_[p]ˣ →ₜ* Field.absoluteGaloisGroupAbelianization ℚ_[p])).comp invMap
    refine ⟨φ, ?_⟩
    have hgen : (padicAbelianizationEquiv p).symm (zHat.gen⁻¹, 1) =
        geometricArtinMap ℚ_[p] (padicPrimeUnit p) := by
      apply (padicAbelianizationEquiv p).injective
      rw [ContinuousMulEquiv.apply_symm_apply, padicAbelianizationEquiv_geometricArtinMap]
      simp
    simp only [φ, invMap, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_coe]
    -- Unfold `(ContinuousMonoidHom.inv zHat.{0}).toMonoidHom` on `zHat.gen`.
    change TopologicalAbelianization.lift χ ((padicAbelianizationEquiv p).symm (zHat.gen⁻¹, 1)) =
      δ (padicPrimeUnit p)
    rw [hgen, lift_geometricArtinMap_eq_of_weilToAbsolute hχ]
  · rintro ⟨φ, hφ⟩
    exact ⟨δ.toGaloisCharOfZHat φ, δ.toGaloisCharOfZHat_weilToAbsolute φ hφ⟩

/-- Equivalent form of the extension criterion in terms of the dense subgroup `ℤ → ℤ̂`:
`δ` extends to `G_{ℚ_p}` if and only if `n ↦ δ(p) ^ n` extends continuously along `zHat.ofInt`. -/
theorem PadicUnitsChar.exists_galoisChar_iff_exists_zHat_ofInt [T1Space Λ]
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
    rw [ContinuousMonoidHom.mul_apply, hχ₁ w, hχ₂ w, toWeilChar_mul,
      ContinuousMonoidHom.mul_apply]⟩

/-- If `δ` extends continuously to `G_{ℚ_p}`, then so does `δ⁻¹`. -/
theorem PadicUnitsChar.exists_galoisChar_inv {δ : PadicUnitsChar p Λ}
    (h : ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w) :
    ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ,
      ∀ w : WeilGroup ℚ_[p], χ (weilToAbsolute ℚ_[p] w) = δ⁻¹.toWeilChar w := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨χ⁻¹, fun w ↦ ?_⟩
  -- Unfold pointwise inversion on both continuous homomorphisms.
  change (χ (weilToAbsolute ℚ_[p] w))⁻¹ = (δ.toWeilChar w)⁻¹
  rw [hχ w]

/-! ### Sufficient conditions for continuous Galois extension -/

/-- Continuous Galois extension when `Λˣ` is profinite (compact and totally disconnected),
obtained by pulling back `ContinuousMonoidHom.padicGaloisCharacter` to `G_{ℚ_p}`. -/
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

/-- Continuous Galois extension when `Λ` is compact, `T1`, and totally disconnected (for instance
`ℤ_[p]`, `𝒪[L]`, `ZMod p`, or any finite discrete ring). -/
def PadicUnitsChar.toGaloisCharOfProfinite [T1Space Λ] [CompactSpace Λ]
    [TotallyDisconnectedSpace Λ] (δ : PadicUnitsChar p Λ) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  have : TotallyDisconnectedSpace Λˣ :=
    totallyDisconnectedSpace_of_injective_continuous Units.val_injective Units.continuous_val
  δ.toGaloisCharOfProfiniteUnits

/-- `toGaloisCharOfProfinite` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfProfinite_weilToAbsolute [T1Space Λ] [CompactSpace Λ]
    [TotallyDisconnectedSpace Λ] (δ : PadicUnitsChar p Λ) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfProfinite (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  have : TotallyDisconnectedSpace Λˣ :=
    totallyDisconnectedSpace_of_injective_continuous Units.val_injective Units.continuous_val
  δ.toGaloisCharOfProfiniteUnits_weilToAbsolute w

/-- Construct a continuous homomorphism `ℤ̂ →ₜ* G` sending `zHat.gen` to an element `a` of finite
order, factoring through `Multiplicative (ZMod (orderOf a))`. -/
private def zHatLiftOfFinOrder {G : Type*} [Group G] [TopologicalSpace G] {a : G}
    (ha : IsOfFinOrder a) : zHat.{0} →ₜ* G :=
  haveI : NeZero (orderOf a) := ⟨(orderOf_pos_iff.mpr ha).ne'⟩
  let ψ : Multiplicative (ZMod (orderOf a)) →ₜ* G :=
    ⟨(TauCeti.zmodMonoidHomEquiv (orderOf a) G).symm ⟨a, pow_orderOf_eq_one a⟩,
      continuous_of_discreteTopology⟩
  ψ.comp (zHat.lift (.ofAdd 1))

private theorem zHatLiftOfFinOrder_gen {G : Type*} [Group G] [TopologicalSpace G] {a : G}
    (ha : IsOfFinOrder a) : zHatLiftOfFinOrder ha zHat.gen = a := by
  have : NeZero (orderOf a) := ⟨(orderOf_pos_iff.mpr ha).ne'⟩
  simp only [zHatLiftOfFinOrder, ContinuousMonoidHom.coe_comp, Function.comp_apply, zHat.lift_gen]
  exact TauCeti.zmodMonoidHomEquiv_symm_apply_ofAdd_one _

/-- Continuous Galois extension when `δ(p)` has finite order in `Λˣ` (for any commutative
topological monoid `Λ` with continuous multiplication). -/
def PadicUnitsChar.toGaloisCharOfFinOrder (δ : PadicUnitsChar p Λ)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ :=
  δ.toGaloisCharOfZHat (zHatLiftOfFinOrder hfin)

/-- `toGaloisCharOfFinOrder` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfFinOrder_weilToAbsolute (δ : PadicUnitsChar p Λ)
    (hfin : IsOfFinOrder (δ (padicPrimeUnit p))) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfFinOrder hfin (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  δ.toGaloisCharOfZHat_weilToAbsolute _ (zHatLiftOfFinOrder_gen hfin) w

end CommMonoid

end GaloisExtension

/-! ### Unitary characters and exact extendability over a local field `L` -/

section UnitaryBasic

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]

/-- A continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` with values in a valuated field `L` is
**unitary** if `v_L(δ(p)) = 1`. When `L` is a nonarchimedean local field, `δ(ℤ_[p]ˣ)`
automatically lies in `U(L, 0)`, so this is equivalent to `v_L(δ(x)) = 1` for all `x ∈ ℚ_[p]ˣ`
(`isUnitary_iff_forall_valuation_eq_one`). -/
def PadicUnitsChar.IsUnitary (δ : PadicUnitsChar p L) : Prop :=
  valuation L (δ (padicPrimeUnit p) : L) = 1

/-- The trivial character is unitary. -/
theorem PadicUnitsChar.isUnitary_one : (1 : PadicUnitsChar p L).IsUnitary := by
  simp [IsUnitary]

/-- The product of two unitary characters is unitary. -/
theorem PadicUnitsChar.isUnitary_mul [ContinuousMul L] {δ₁ δ₂ : PadicUnitsChar p L}
    (h₁ : δ₁.IsUnitary) (h₂ : δ₂.IsUnitary) : (δ₁ * δ₂).IsUnitary := by
  simp only [IsUnitary, ContinuousMonoidHom.mul_apply, Units.val_mul, map_mul]
  rw [h₁, h₂, mul_one]

/-- The inverse of a unitary character is unitary. -/
theorem PadicUnitsChar.isUnitary_inv [ContinuousMul L] {δ : PadicUnitsChar p L}
    (h : δ.IsUnitary) : δ⁻¹.IsUnitary := by
  have hmul : valuation L (δ (padicPrimeUnit p) : L) *
      valuation L ((δ⁻¹ (padicPrimeUnit p) : Lˣ) : L) = 1 := by
    rw [← map_mul]
    have : (δ (padicPrimeUnit p) : L) * ((δ⁻¹ (padicPrimeUnit p) : Lˣ) : L) = 1 :=
      Units.mul_inv _
    rw [this, map_one]
  rw [PadicUnitsChar.IsUnitary] at h ⊢
  rwa [h, one_mul] at hmul

end UnitaryBasic

section UnitaryLocalField

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Every continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` into a nonarchimedean local field `L` sends
all of `ℤ_[p]ˣ` into units of valuation `1`. -/
theorem PadicUnitsChar.valuation_padicIntUnitsInclusion_eq_one (δ : PadicUnitsChar p L)
    (u : ℤ_[p]ˣ) :
    valuation L (δ (padicIntUnitsInclusion p u) : L) = 1 := by
  let f : ℤ_[p]ˣ →ₜ* Multiplicative ℤ :=
    ⟨(normalizedValuation L).comp δ.toWeight.toMonoidHom,
      (continuous_normalizedValuation L).comp δ.toWeight.continuous⟩
  have hf : f = 1 := ContinuousMonoidHom.eq_one_of_isMulTorsionFree f
  have hval : normalizedValuation L (δ (padicIntUnitsInclusion p u)) = 1 := by
    simpa [f, PadicUnitsChar.toWeight_apply] using DFunLike.congr_fun hf u
  exact (normalizedValuation_eq_one_iff _).mp hval

/-- `δ : ℚ_[p]ˣ →ₜ* Lˣ` is unitary if and only if every value `δ(x)` has valuation `1` in `L`. -/
theorem PadicUnitsChar.isUnitary_iff_forall_valuation_eq_one (δ : PadicUnitsChar p L) :
    δ.IsUnitary ↔ ∀ x : ℚ_[p]ˣ, valuation L (δ x : L) = 1 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ h (padicPrimeUnit p)⟩
  rw [eq_padicPrimeUnit_zpow_mul_padicUnitPart p x, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, one_zpow, one_mul]
  exact δ.valuation_padicIntUnitsInclusion_eq_one _

/-- Lift a unit of valuation `1` in a nonarchimedean local field `L` to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ` via the profinite unit group `U(L, 0)`. -/
private def zHatLiftUnitFiltration (u : Lˣ) (hu : valuation L (u : L) = 1) : zHat.{0} →ₜ* Lˣ :=
  have : CompactSpace (unitFiltration L 0) :=
    isCompact_iff_compactSpace.mp (isCompact_unitFiltration 0)
  have : TotallyDisconnectedSpace (unitFiltration L 0) :=
    totallyDisconnectedSpace_of_injective_continuous
      (Units.val_injective.comp Subtype.val_injective)
      (Units.continuous_val.comp continuous_subtypeVal)
  let incl : unitFiltration L 0 →ₜ* Lˣ := ⟨(unitFiltration L 0).subtype, continuous_subtypeVal⟩
  incl.comp (zHat.lift ⟨u, (mem_unitFiltration_zero _).mpr hu⟩)

private theorem zHatLiftUnitFiltration_gen (u : Lˣ) (hu : valuation L (u : L) = 1) :
    zHatLiftUnitFiltration u hu zHat.gen = u := by
  have : CompactSpace (unitFiltration L 0) :=
    isCompact_iff_compactSpace.mp (isCompact_unitFiltration 0)
  have : TotallyDisconnectedSpace (unitFiltration L 0) :=
    totallyDisconnectedSpace_of_injective_continuous
      (Units.val_injective.comp Subtype.val_injective)
      (Units.continuous_val.comp continuous_subtypeVal)
  simp only [zHatLiftUnitFiltration, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    zHat.lift_gen]
  rfl

/-- Continuous Galois extension of a unitary character `δ : ℚ_[p]ˣ →ₜ* Lˣ` into a nonarchimedean
local field `L`, built via `zHat.lift` into the profinite unit group `U(L, 0)`. -/
def PadicUnitsChar.toGaloisCharOfUnitary (δ : PadicUnitsChar p L) (hδ : δ.IsUnitary) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ :=
  δ.toGaloisCharOfZHat (zHatLiftUnitFiltration (δ (padicPrimeUnit p)) hδ)

/-- `toGaloisCharOfUnitary` restricts on `W_{ℚ_p}` to `δ.toWeilChar`. -/
theorem PadicUnitsChar.toGaloisCharOfUnitary_weilToAbsolute (δ : PadicUnitsChar p L)
    (hδ : δ.IsUnitary) (w : WeilGroup ℚ_[p]) :
    δ.toGaloisCharOfUnitary hδ (weilToAbsolute ℚ_[p] w) = δ.toWeilChar w :=
  δ.toGaloisCharOfZHat_weilToAbsolute _ (zHatLiftUnitFiltration_gen _ hδ) w

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
    exact (normalizedValuation_eq_one_iff _).mp hval
  · intro hδ
    exact ⟨δ.toGaloisCharOfUnitary hδ, δ.toGaloisCharOfUnitary_weilToAbsolute hδ⟩

end UnitaryLocalField

/-! ### Canonical character identifications and the non-unitary counterexample -/

section CanonicalChecks

variable (p : ℕ) [Fact p.Prime]

/-- **Cyclotomic character check.** Under Colmez's normalization, the unitary character
`x ↦ x |x|_p` (`TauCeti.padicUnitPart p`) corresponds on `W_{ℚ_p}` to the `p`-adic cyclotomic
character. -/
theorem continuousLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicUnitPart
    (w : WeilGroup ℚ_[p]) :
    continuousLocalCyclotomicCharacter p ℚ_[p] (weilToAbsolute ℚ_[p] w) =
      PadicUnitsChar.toWeilChar (padicUnitPart p) w := by
  rw [PadicUnitsChar.toWeilChar_apply, padicUnitPart_padicPrimeUnit, one_zpow, one_mul,
    padicUnitPart_padicIntUnitsInclusion, continuousLocalCyclotomicCharacter_apply]

/-- The unique continuous Galois extension of `padicUnitPart p` (`x ↦ x |x|`) is
`continuousLocalCyclotomicCharacter p ℚ_[p]`. -/
theorem toGaloisCharOfProfiniteUnits_padicUnitPart :
    PadicUnitsChar.toGaloisCharOfProfiniteUnits (padicUnitPart p) =
      continuousLocalCyclotomicCharacter p ℚ_[p] := by
  ext1 σ
  simp [PadicUnitsChar.toGaloisCharOfProfiniteUnits]

/-- **The mod-`p` cyclotomic character** `G_{ℚ_p} →ₜ* (ZMod p)ˣ`, bundled from Mathlib's finite
`modularCyclotomicCharacter` at level `p` on `AlgebraicClosure ℚ_[p]`. -/
def modPLocalCyclotomicCharacter : Field.absoluteGaloisGroup ℚ_[p] →ₜ* (ZMod p)ˣ :=
  ⟨(modularCyclotomicCharacter (AlgebraicClosure ℚ_[p])
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)).comp
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]) (AlgebraicClosure ℚ_[p])),
    modularCyclotomicCharacter.continuous _⟩

/-- The value of `modPLocalCyclotomicCharacter p` in `ZMod p` is the mod-`p` reduction of
`localCyclotomicCharacter p ℚ_[p]`. -/
@[simp]
theorem coe_modPLocalCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    (modPLocalCyclotomicCharacter p σ : ZMod p) =
      PadicInt.toZMod (localCyclotomicCharacter p ℚ_[p] σ : ℤ_[p]) := by
  have hn : Nat.card (rootsOfUnity (p ^ 1) (AlgebraicClosure ℚ_[p])) = p ^ 1 := by
    rw [pow_one]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p
  rw [← PadicInt.cast_toZModPow_eq_toZMod one_ne_zero, localCyclotomicCharacter_apply,
    cyclotomicCharacter.toZModPow]
  have h := congrArg Units.val <| modularCyclotomicCharacter.unitsMap (dvd_of_eq (pow_one p).symm)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ_[p]) p) hn σ.toRingEquiv
  rw [ZMod.unitsMap_val] at h
  exact h.symm

/-- **Mod-`p` cyclotomic character check.** Under Colmez's normalization, `ω` corresponds on
`W_{ℚ_p}` to `modPLocalCyclotomicCharacter p`. -/
theorem modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicModPCyclotomicChar
    (w : WeilGroup ℚ_[p]) :
    modPLocalCyclotomicCharacter p (weilToAbsolute ℚ_[p] w) =
      (padicModPCyclotomicChar p).toWeilChar w := by
  apply Units.ext
  rw [PadicUnitsChar.toWeilChar_apply, padicModPCyclotomicChar_padicPrimeUnit, one_zpow,
    one_mul, coe_padicModPCyclotomicChar_padicIntUnitsInclusion,
    coe_modPLocalCyclotomicCharacter_apply]

/-- The unique continuous Galois extension of `padicModPCyclotomicChar p` (`ω`) is
`modPLocalCyclotomicCharacter p`. -/
theorem toGaloisCharOfProfinite_padicModPCyclotomicChar :
    (padicModPCyclotomicChar p).toGaloisCharOfProfinite = modPLocalCyclotomicCharacter p :=
  galoisChar_eq_of_weilToAbsolute_eq fun w ↦ by
    rw [PadicUnitsChar.toGaloisCharOfProfinite_weilToAbsolute,
      modPLocalCyclotomicCharacter_weilToAbsolute_eq_toWeilChar_padicModPCyclotomicChar]

/-- Pushing `continuousLocalCyclotomicCharacter p ℚ_[p]` along any continuous ring homomorphism
`f : ℤ_[p] →+* k` into a discrete ring of characteristic `p` (such as a residue field `𝓀[L]`)
agrees with pushing `modPLocalCyclotomicCharacter p` along `ZMod.castHom`, and extends
`(padicUnitPart p).mapMonoidHom f.toMonoidHom hf`. -/
theorem map_continuousLocalCyclotomicCharacter_eq_cast_modP {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] [DiscreteTopology k] (f : ℤ_[p] →+* k) (hf : Continuous f) :
    ContinuousMonoidHom.comp ⟨Units.map f.toMonoidHom, hf.units_map _⟩
        (continuousLocalCyclotomicCharacter p ℚ_[p]) =
      ContinuousMonoidHom.comp
        ⟨Units.map (ZMod.castHom (dvd_refl p) k).toMonoidHom,
          continuous_of_discreteTopology.units_map _⟩
        (modPLocalCyclotomicCharacter p) := by
  ext1 σ
  apply Units.ext
  simpa using DFunLike.congr_fun (padicInt_ringHom_eq_castHom_comp_toZMod p f hf)
    (localCyclotomicCharacter p ℚ_[p] σ : ℤ_[p])

/-! #### Unramified characters on inertia and Frobenius lifts -/

/-- **Unramified character check (inertia).** Any continuous Galois character extending
`unramifiedCharacter ℚ_[p] a` is trivial on the inertia subgroup `I_{ℚ_p}`. -/
theorem inertiaSubgroup_le_ker_of_extends_unramifiedCharacter {Λ : Type*} [Monoid Λ]
    [TopologicalSpace Λ] {a : Λˣ} {χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (hχ : ∀ w : WeilGroup ℚ_[p],
      χ (weilToAbsolute ℚ_[p] w) = PadicUnitsChar.toWeilChar (unramifiedCharacter ℚ_[p] a) w) :
    inertiaSubgroup ℚ_[p] ≤ χ.toMonoidHom.ker := by
  intro σ hσ
  have h := hχ (inertiaToWeil ℚ_[p] ⟨σ, hσ⟩)
  rw [weilToAbsolute_inertiaToWeil, PadicUnitsChar.toWeilChar_apply,
    weilDegree_inertiaToWeil, toAdd_one, neg_zero, zpow_zero, one_mul,
    unramifiedCharacter_apply_of_valuation_eq_one a
      (Padic.valuation_eq_one_of_coe_eq (coe_padicIntUnitsInclusion_apply _))] at h
  exact h

/-- **Unramified character check (geometric Frobenius).** Any continuous Galois character extending
`unramifiedCharacter ℚ_[p] a` evaluates to `a` on every geometric Frobenius lift `σ`
(i.e. `IsArithFrobeniusLift ℚ_[p] σ⁻¹`). -/
theorem apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv {Λ : Type*} [Monoid Λ]
    [TopologicalSpace Λ] {a : Λˣ} {χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (hχ : ∀ w : WeilGroup ℚ_[p],
      χ (weilToAbsolute ℚ_[p] w) = PadicUnitsChar.toWeilChar (unramifiedCharacter ℚ_[p] a) w)
    {σ : Field.absoluteGaloisGroup ℚ_[p]} (hσ : IsArithFrobeniusLift ℚ_[p] σ⁻¹) :
    χ σ = a := by
  let w₀ : WeilGroup ℚ_[p] :=
    (weilGroupEquivLocalWeilGroup ℚ_[p]).symm ⟨σ⁻¹, hσ.mem_localWeilGroup⟩
  have hw₀ : weilToAbsolute ℚ_[p] w₀ = σ⁻¹ :=
    weilToAbsolute_weilGroupEquivLocalWeilGroup_symm ℚ_[p] _
  have hdeg : weilDegree ℚ_[p] w₀ = .ofAdd 1 :=
    weilDegree_eq_ofAdd_one_iff.mpr (by rwa [hw₀])
  have hw : weilToAbsolute ℚ_[p] w₀⁻¹ = σ := by
    rw [map_inv, hw₀, inv_inv]
  rw [← hw, hχ w₀⁻¹, PadicUnitsChar.toWeilChar_apply, map_inv, hdeg, toAdd_inv, toAdd_ofAdd,
    neg_neg, zpow_one,
    unramifiedCharacter_apply_of_isUniformizer a (isUniformizer_padicPrimeUnit p),
    unramifiedCharacter_apply_of_valuation_eq_one a
      (Padic.valuation_eq_one_of_coe_eq (coe_padicIntUnitsInclusion_apply _)), mul_one]

/-- **Unramified character check (arithmetic Frobenius).** Any continuous Galois character extending
`unramifiedCharacter ℚ_[p] a` evaluates to `a⁻¹` on every arithmetic Frobenius lift `σ`. -/
theorem apply_eq_inv_of_extends_unramifiedCharacter_of_isArithFrobeniusLift {Λ : Type*} [Monoid Λ]
    [TopologicalSpace Λ] {a : Λˣ} {χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Λˣ}
    (hχ : ∀ w : WeilGroup ℚ_[p],
      χ (weilToAbsolute ℚ_[p] w) = PadicUnitsChar.toWeilChar (unramifiedCharacter ℚ_[p] a) w)
    {σ : Field.absoluteGaloisGroup ℚ_[p]} (hσ : IsArithFrobeniusLift ℚ_[p] σ) :
    χ σ = a⁻¹ := by
  have hinv := apply_eq_of_extends_unramifiedCharacter_of_isArithFrobeniusLift_inv p hχ
    (σ := σ⁻¹) (by simpa using hσ)
  rw [map_inv] at hinv
  exact inv_eq_iff_eq_inv.mp hinv

/-! #### Non-unitarity and non-extendability of `x ↦ algebraMap ℚ_[p] L x` -/

section NonUnitary

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FinitePadicExtension L p]

/-- The character `x ↦ algebraMap ℚ_[p] L x` into any finite extension `L / ℚ_[p]` (including
`ℚ_[p]` itself) is not unitary, because `v_L(p) < 1`. -/
theorem not_isUnitary_padicAlgebraMapChar (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ (padicAlgebraMapChar p L h).IsUnitary := by
  rw [PadicUnitsChar.IsUnitary, coe_padicAlgebraMapChar_padicPrimeUnit]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hlt : valuation L (p : L) < 1 := by
    rw [valuation_natCast_eq_pow_mul_padicValNat p hπ (Fact.out : p.Prime).ne_zero,
      Nat.padicValNat_def, Nat.multiplicity_self (Fact.out : p.Prime).one_lt, mul_one]
    exact pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ)
      (absoluteRamificationIndex_pos L p).ne'
  exact hlt.ne

/-- **Non-extendability of `x ↦ algebraMap ℚ_[p] L x`.** For any finite extension `L / ℚ_[p]`
(including `ℚ_[p]` itself), the character `x ↦ algebraMap ℚ_[p] L x` does not extend continuously
from `W_{ℚ_p}` to `G_{ℚ_p}`. -/
theorem not_exists_galoisChar_padicAlgebraMapChar (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ ∃ χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* Lˣ,
      ∀ w : WeilGroup ℚ_[p],
        χ (weilToAbsolute ℚ_[p] w) = (padicAlgebraMapChar p L h).toWeilChar w := by
  rw [PadicUnitsChar.exists_galoisChar_iff_isUnitary]
  exact not_isUnitary_padicAlgebraMapChar p L h

/-- Equivalently, the map `n ↦ (p : L) ^ n` does not extend to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ`. -/
theorem not_exists_zHat_padicPrimeUnit :
    ¬ ∃ φ : zHat.{0} →ₜ* Lˣ,
      φ zHat.gen = Units.map (algebraMap ℚ_[p] L).toMonoidHom (padicPrimeUnit p) := by
  intro ⟨φ, hφ⟩
  refine not_exists_galoisChar_padicAlgebraMapChar p L
    (continuous_algebraMap_of_valuativeExtension ℚ_[p] L) ?_
  rw [PadicUnitsChar.exists_galoisChar_iff_exists_zHat]
  refine ⟨φ, hφ.trans (Units.ext ?_)⟩
  simp

end NonUnitary

end CanonicalChecks

end TauCeti
