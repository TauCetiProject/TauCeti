/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.MaximalUnramified
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Restriction
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.LocalH2Bound
import TauCeti.NumberTheory.LocalField.FiniteExtension.Tower
import TauCeti.NumberTheory.LocalField.Unramified.BaseChange

/-!
# The local invariant of the Brauer group

Let `K` be a nonarchimedean local field with separable closure `Kˢ`. This file proves that every
class of the Brauer group `Br K = H²(G_K, (Kˢ)ˣ)` is split by an unramified extension of `K`, and
constructs the **local invariant**

`inv_K : Br K ≃+ ℚ/ℤ`,

normalized by arithmetic Frobenius: on a class inflated from an unramified layer `E/K` inside
`Kˢ` it is the invariant `TauCeti.ClassFieldTheory.unramifiedInv K E` of the layer.

Let `E/K` be a finite Galois extension inside `Kˢ` of degree `n`, and let `Kₙ` be the unramified
extension of degree `n` inside `Kˢ`. The classes of `Br K` split by `E` and by `Kₙ` are the same.
Indeed, let `x ∈ H²(Gal(Kₙ/K), Kₙˣ)` and let `M = E Kₙ`. The extension `M/E` is unramified, and
the restriction of `x` to `H²(Gal(M/E), Mˣ)` has invariant `[E : K] · inv_K(x) = n · inv_K(x)`
(`TauCeti.ClassFieldTheory.unramifiedInv_map_baseChange`), which vanishes since `inv_K(x)` has
order dividing `n`. So the inflation of `x` to `Br K` is split by `E`
(`TauCeti.ClassFieldTheory.relBrInfl_mem_range_relBrInfl_iff`). The classes split by `Kₙ` thus
form a subgroup of order `n` (`TauCeti.ClassFieldTheory.natCard_H2_unramified`) of the classes
split by `E`, which have order dividing `n` (`TauCeti.natCard_H2_units_dvd_finrank`), so the two
groups agree. Since every Brauer class is split by some finite Galois extension
(`TauCeti.ClassFieldTheory.exists_relBrInfl_eq`), the unramified Brauer group
`TauCeti.ClassFieldTheory.unramifiedBr K` is all of `Br K`, and its invariant
`TauCeti.ClassFieldTheory.unramifiedBrInv K` is defined on the whole Brauer group.

Let `L/K` be a finite extension of nonarchimedean local fields, embedded in `Kˢ`. Restriction
`TauCeti.ClassFieldTheory.brRes K L σ` multiplies the invariant by `[L : K]`. Indeed, a class
inflated from the unramified extension `K_f/K` of degree `f` restricts to the class inflated
along the base change `H²(Gal(K_f/K), K_fˣ) → H²(Gal(L_f/L), L_fˣ)`, where `L_f/L` is the
unramified extension of degree `f`, which contains the image of `K_f` under the identification
`Kˢ ≃ Lˢ` (`TauCeti.unramifiedExtension_le_restrictScalars_unramifiedExtension`,
`TauCeti.ClassFieldTheory.brRes_relBrInfl`), and this base change multiplies the unramified
invariant by `[L : K]` (`TauCeti.ClassFieldTheory.unramifiedInv_map_baseChange`). Since
multiplication by `[L : K]` is surjective on `ℚ/ℤ`, restriction is surjective, and corestriction
`TauCeti.ClassFieldTheory.brCor K L σ` preserves the invariant because
`brCor ∘ brRes = [L : K]` (`TauCeti.ClassFieldTheory.brCor_brRes`).

## Main definitions

* `TauCeti.ClassFieldTheory.invMap K`: the local invariant `Br K ≃+ ℚ/ℤ`.

## Main results

* `TauCeti.ClassFieldTheory.range_relBrInfl_eq_range_relBrInfl_unramifiedExtension`: a Brauer
  class is split by a finite Galois extension of degree `n` exactly when it is split by the
  unramified extension of degree `n`.
* `TauCeti.ClassFieldTheory.unramifiedBr_eq_top`: every Brauer class is split by an unramified
  extension.
* `TauCeti.ClassFieldTheory.invMap_eq_unramifiedBrInv`: the local invariant is the invariant of
  the unramified Brauer group.
* `TauCeti.ClassFieldTheory.invMap_relBrInfl`: on a class inflated from an unramified layer, the
  invariant is the invariant `unramifiedInv` of the layer.
* `TauCeti.ClassFieldTheory.invMap_relBrInfl_unramified`: the same, for an unramified extension
  embedded in `Kˢ` by an arbitrary embedding.
* `TauCeti.ClassFieldTheory.range_invMap_comp_relBrInfl`: the invariants of the classes split by a
  finite Galois extension of degree `n` form the subgroup of `ℚ/ℤ` of order `n`.
* `TauCeti.ClassFieldTheory.invMap_brRes`: the restriction square
  `inv_L (brRes x) = [L : K] • inv_K x`.
* `TauCeti.ClassFieldTheory.brRes_surjective`: restriction of Brauer classes is surjective.
* `TauCeti.ClassFieldTheory.invMap_brCor`: the corestriction square `inv_K (brCor y) = inv_L y`.
* `TauCeti.ClassFieldTheory.brCor_bijective`: corestriction of Brauer classes is bijective.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §3.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VI (Serre, *Local
  Class Field Theory*), §1.
-/

public section
noncomputable section

open IntermediateField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The unramified extension of degree `f` of `K` inside its separable closure. -/
local notation "𝓤" f:max => unramifiedExtension K (SeparableClosure K) f

/-- **The classes split by the unramified extension of degree `[E : K]` are split by `E`.** -/
private theorem range_relBrInfl_unramifiedExtension_le
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [Normal K E] {n : ℕ}
    (hEn : Module.finrank K E = n) :
    (relBrInfl K (𝓤 n) (𝓤 n).val).range ≤ (relBrInfl K E E.val).range := by
  have hn : n ≠ 0 := hEn ▸ Module.finrank_pos.ne'
  -- The compositum `M = E Kₙ`, as an extension of `Kₙ` and of `E`.
  let M := E ⊔ 𝓤 n
  let _ : Algebra (𝓤 n) M := (inclusion le_sup_right).toAlgebra
  let _ : Algebra E M := (inclusion le_sup_left).toAlgebra
  have : IsScalarTower K (𝓤 n) M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K E M := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional E M := FiniteDimensional.right K E M
  have : Algebra.IsSeparable K M := Algebra.IsSeparable.of_algHom K _ M.val
  have : IsGalois K M := {}
  have : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  -- `M` is generated over `E` by `Kₙ`. The images of `E` and `Kₙ` in `M` are the intermediate
  -- fields `restrict le_sup_left` and `restrict le_sup_right`, by definition of the algebra
  -- structures, and they lift to `E` and `Kₙ` in `Kˢ`.
  have hadj : adjoin E (Set.range (IsScalarTower.toAlgHom K (𝓤 n) M)) = ⊤ := by
    refine TauCeti.IntermediateField.adjoin_range_eq_top_of_fieldRange_sup_fieldRange_eq_top _
      (lift_injective M ?_)
    rw [lift_sup, lift_top]
    exact congrArg₂ (· ⊔ ·) (lift_restrict le_sup_left) (lift_restrict le_sup_right)
  -- A class inflated from `Kₙ` is split by `E` when its base change to `M/E` vanishes.
  rintro _ ⟨y, rfl⟩
  -- `M.val` restricts to the inclusions `(𝓤 n).val` and `E.val`, by definition of the algebra
  -- structures, so the splitting criterion applies to the inflations along these inclusions.
  refine (relBrInfl_mem_range_relBrInfl_iff K (𝓤 n) E M M.val y).2 ?_
  -- The canonical structures of nonarchimedean local field on `Kₙ`, `E` and `M`.
  let _ := finiteExtensionValuativeRel K (𝓤 n)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 n)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 n)
  have := finiteExtension_valuativeExtension K (𝓤 n)
  have : IsUnramified K (𝓤 n) := isUnramified_unramifiedExtension hn
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := finiteExtension_valuativeExtension K E
  let _ := finiteExtensionValuativeRel K M
  let _ := finiteExtensionNormedFieldTopology K M
  have := finiteExtension_isNonarchimedeanLocalField K M
  have : ValuativeExtension (𝓤 n) M := finiteExtension_valuativeExtension_tower K (𝓤 n) M
  have : ValuativeExtension E M := finiteExtension_valuativeExtension_tower K E M
  -- `M/E` is unramified, being generated over `E` by the unramified extension `Kₙ`, and
  -- `[Kₙ : K] = [E : K]`.
  have : IsUnramified E M := IsUnramified.of_adjoin_range_eq_top (K := K) (L := 𝓤 n) _ hadj
  exact map_baseChange_eq_zero_of_finrank_dvd K (𝓤 n) E M
    (by rw [finrank_unramifiedExtension hn, hEn]) y

/-- **A Brauer class is split by a finite Galois extension of degree `n` exactly when it is split
by the unramified extension of degree `n`.** For `E/K` finite normal inside `Kˢ`, the classes of
`Br K` inflated from `H²(Gal(E/K), Eˣ)` are those inflated from `H²(Gal(Kₙ/K), Kₙˣ)`, where `Kₙ` is
the unramified extension of degree `n = [E : K]` inside `Kˢ`. -/
theorem range_relBrInfl_eq_range_relBrInfl_unramifiedExtension
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [Normal K E] :
    (relBrInfl K E E.val).range =
      (relBrInfl K (𝓤 (Module.finrank K E)) (𝓤 _).val).range := by
  set n := Module.finrank K E
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  let _ := finiteExtensionValuativeRel K (𝓤 n)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 n)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 n)
  have := finiteExtension_valuativeExtension K (𝓤 n)
  have : IsUnramified K (𝓤 n) := isUnramified_unramifiedExtension hn
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := finiteExtension_valuativeExtension K E
  have : Algebra.IsSeparable K E := Algebra.IsSeparable.of_algHom K _ E.val
  have : IsGalois K E := {}
  -- The two groups have orders dividing `n` and equal to `n`.
  have hE : Nat.card (relBrInfl K E E.val).range ∣ n := by
    rw [← Nat.card_congr (AddMonoidHom.ofInjective (relBrInfl_injective K E E.val)).toEquiv]
    exact TauCeti.natCard_H2_units_dvd_finrank K E
  have hU : Nat.card (relBrInfl K (𝓤 n) (𝓤 n).val).range = n := by
    rw [← Nat.card_congr (AddMonoidHom.ofInjective (relBrInfl_injective K _ _)).toEquiv,
      natCard_H2_unramified, finrank_unramifiedExtension hn]
  have : Finite (relBrInfl K E E.val).range :=
    Nat.finite_of_card_ne_zero fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ hE))
  exact (AddSubgroup.eq_of_le_of_card_ge (range_relBrInfl_unramifiedExtension_le K E rfl)
    (hU ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hE)).symm

/-- **Every Brauer class of a nonarchimedean local field is split by an unramified extension.** -/
@[simp]
theorem unramifiedBr_eq_top : unramifiedBr K = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨E, _, _, y, rfl⟩ := exists_relBrInfl_eq x
  obtain ⟨z, hz⟩ : relBrInfl K E E.val y ∈ (relBrInfl K (𝓤 (Module.finrank K E)) (𝓤 _).val).range :=
    range_relBrInfl_eq_range_relBrInfl_unramifiedExtension K E ▸ ⟨y, rfl⟩
  exact (mem_unramifiedBr_iff K).2 ⟨⟨_, Module.finrank_pos⟩, z, hz⟩

/-- **The local invariant** `inv_K : Br K ≃+ ℚ/ℤ` of a nonarchimedean local field `K`, normalized
by arithmetic Frobenius: on the classes inflated from an unramified extension `E/K` inside `Kˢ`
it is the invariant `TauCeti.ClassFieldTheory.unramifiedInv K E` of the layer
(`invMap_relBrInfl`). -/
def invMap : Br K ≃+ AddCircle (1 : ℚ) :=
  (AddSubgroup.topEquiv.symm.trans (AddEquiv.addSubgroupCongr (unramifiedBr_eq_top K).symm)).trans
    (unramifiedBrInv K)

/-- The local invariant of a Brauer class is its invariant in the unramified Brauer group. -/
theorem invMap_eq_unramifiedBrInv (x : Br K) (hx : x ∈ unramifiedBr K) :
    invMap K x = unramifiedBrInv K ⟨x, hx⟩ := by
  rw [invMap, AddEquiv.trans_apply, AddEquiv.trans_apply]
  exact congrArg _ (Subtype.ext (by
    rw [AddEquiv.addSubgroupCongr_apply, AddSubgroup.topEquiv_symm_apply_coe]))

variable {K} in
/-- **The normalization of the local invariant**: a class inflated from an unramified extension
`E` of `K` inside `Kˢ` has invariant its invariant `unramifiedInv K E` in the layer
`H²(Gal(E/K), Eˣ)`. -/
@[simp]
theorem invMap_relBrInfl (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [IsUnramified K E]
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2) :
    invMap K (relBrInfl K E E.val y) = unramifiedInv K E y :=
  (invMap_eq_unramifiedBrInv K _ _).trans (unramifiedBrInv_relBrInfl E y)

/-- The local invariant of a class inflated from a finite unramified Galois extension `L/K`,
embedded in `Kˢ` by an arbitrary `ι`, is its invariant `unramifiedInv K L` in the layer
`H²(Gal(L/K), Lˣ)`. -/
theorem invMap_relBrInfl_unramified (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [IsGalois K L] [IsUnramified K L] (ι : L →ₐ[K] SeparableClosure K)
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    invMap K (relBrInfl K L ι y) = unramifiedInv K L y := by
  -- Transport `y` to the image `E = ι(L)`, an unramified layer inside `Kˢ`.
  let E := ι.fieldRange
  let e : L ≃ₐ[K] E := ι.equivFieldRange
  let _ : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := finiteExtension_valuativeExtension K E
  have : IsGalois K E := IsGalois.of_algEquiv e
  have : IsUnramified K E := IsUnramified.of_algEquiv e
  let _ : Algebra L E := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algHom e.toAlgHom
  have : ValuativeExtension L E := e.toAlgHom.valuativeExtension
  have hι : E.val.comp (IsScalarTower.toAlgHom K L E) = ι :=
    AlgHom.ext fun x => AlgHom.equivFieldRange_apply_coe ι x
  rw [← unramifiedInv_map K L E y, ← invMap_relBrInfl E, relBrInfl_map, hι]

/-- **The degree-`n` piece of the Brauer group.** The invariants of the classes of `Br K` split by
a finite Galois extension `E/K` of degree `n` inside `Kˢ` are the elements of `ℚ/ℤ` of order
dividing `n`. -/
theorem range_invMap_comp_relBrInfl (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [Normal K E] :
    Set.range (invMap K ∘ relBrInfl K E E.val) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (Module.finrank K E) :
        Set (AddCircle (1 : ℚ))) := by
  set n := Module.finrank K E
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  let _ := finiteExtensionValuativeRel K (𝓤 n)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 n)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 n)
  have := finiteExtension_valuativeExtension K (𝓤 n)
  have : IsUnramified K (𝓤 n) := isUnramified_unramifiedExtension hn
  have h := range_unramifiedInv K (𝓤 n)
  rw [finrank_unramifiedExtension hn] at h
  rw [← h, Set.range_comp, ← AddMonoidHom.coe_range,
    range_relBrInfl_eq_range_relBrInfl_unramifiedExtension K E, AddMonoidHom.coe_range,
    ← Set.range_comp]
  exact congrArg Set.range (funext fun y => invMap_relBrInfl (𝓤 n) y)

/-! ### Restriction and corestriction -/

section Restriction

variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] (σ : L →ₐ[K] SeparableClosure K)

/-- The unramified extension of degree `f` of `L` inside its separable closure. -/
local notation "𝓥" f:max => unramifiedExtension L (SeparableClosure L) f

/-- **The restriction square of the local invariant**: restriction of Brauer classes along a
finite extension `L/K` of nonarchimedean local fields multiplies the invariant by the degree,
`inv_L (res x) = [L : K] · inv_K x`. -/
@[simp]
theorem invMap_brRes (x : Br K) :
    invMap L (brRes K L σ x) = Module.finrank K L • invMap K x := by
  -- `x` is inflated from the unramified extension `K_f/K` of some degree `f`. Its restriction is
  -- inflated from the unramified extension `L_f/L` of degree `f`, which contains the image of
  -- `K_f` under the identification `Kˢ ≃ Lˢ`, and the base change from `K_f/K` to `L_f/L`
  -- multiplies the unramified invariant by `[L : K]`.
  obtain ⟨f, y, rfl⟩ := (mem_unramifiedBr_iff K).1 (unramifiedBr_eq_top K ▸ AddSubgroup.mem_top x)
  let ψ : SeparableClosure K ≃ₐ[K] SeparableClosure L :=
    AlgEquiv.ofRingEquiv (f := (separableClosureRingEquiv K L σ).symm)
      (separableClosureRingEquiv_symm_algebraMap_base K L σ)
  have hψ (e : 𝓤 f) : ψ (e : SeparableClosure K) ∈ 𝓥 f :=
    unramifiedExtension_le_restrictScalars_unramifiedExtension (K := K) L f
      (map_unramifiedExtension_le f ψ.toAlgHom ((mem_map _).2 ⟨e, e.2, rfl⟩))
  -- The embedding `K_f → L_f` induced by `ψ`.
  let ι : 𝓤 f →ₐ[K] 𝓥 f :=
    (ψ.toAlgHom.comp (𝓤 f).val).codRestrict ((𝓥 f).restrictScalars K).toSubalgebra hψ
  let _ : Algebra (𝓤 f) (𝓥 f) := ι.toAlgebra
  have : IsScalarTower K (𝓤 f) (𝓥 f) := .of_algebraMap_eq fun c => (ι.commutes c).symm
  -- The canonical structures of nonarchimedean local field on `K_f` and `L_f`.
  let _ := finiteExtensionValuativeRel K (𝓤 f)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 f)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
  have := finiteExtension_valuativeExtension K (𝓤 f)
  have : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension f.ne_zero
  let _ := finiteExtensionValuativeRel L (𝓥 f)
  let _ := finiteExtensionNormedFieldTopology L (𝓥 f)
  have := finiteExtension_isNonarchimedeanLocalField L (𝓥 f)
  have := finiteExtension_valuativeExtension L (𝓥 f)
  have : IsUnramified L (𝓥 f) := isUnramified_unramifiedExtension f.ne_zero
  have : ValuativeExtension K (𝓥 f) := ValuativeExtension.trans K L (𝓥 f)
  have : ValuativeExtension (𝓤 f) (𝓥 f) := ι.valuativeExtension
  rw [brRes_relBrInfl K L (𝓤 f) (𝓥 f) σ (𝓤 f).val (𝓥 f).val
    (fun e => (separableClosureRingEquiv K L σ).apply_symm_apply e) y, invMap_relBrInfl,
    invMap_relBrInfl, unramifiedInv_map_baseChange]

/-- **Restriction of Brauer classes along a finite extension of nonarchimedean local fields is
surjective**, since multiplication by `[L : K]` is surjective on `ℚ/ℤ`. -/
theorem brRes_surjective : Function.Surjective (brRes K L σ) := by
  have := finite_of_valuativeExtension K L
  have hn : (Module.finrank K L : ℤ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  intro y
  obtain ⟨q, hq⟩ := DivisibleBy.surjective_smul _ ℤ hn (invMap L y)
  refine ⟨(invMap K).symm q, (invMap L).injective ?_⟩
  rw [invMap_brRes, AddEquiv.apply_symm_apply, ← natCast_zsmul]
  exact hq

/-- **The corestriction square of the local invariant**: corestriction of Brauer classes along a
finite extension `L/K` of nonarchimedean local fields preserves the invariant,
`inv_K (cor y) = inv_L y`. -/
@[simp]
theorem invMap_brCor [FiniteDimensional K L] (y : Br L) :
    invMap K (brCor K L σ y) = invMap L y := by
  obtain ⟨x, rfl⟩ := brRes_surjective K L σ y
  rw [brCor_brRes, map_nsmul, invMap_brRes]

/-- **Corestriction of Brauer classes along a finite extension of nonarchimedean local fields is
bijective**, since it preserves the invariant. -/
theorem brCor_bijective [FiniteDimensional K L] : Function.Bijective (brCor K L σ) := by
  have h : ⇑(brCor K L σ) = (invMap K).symm ∘ invMap L :=
    funext fun y => (invMap K).eq_symm_apply.2 (invMap_brCor K L σ y)
  rw [h]
  exact (invMap K).symm.bijective.comp (invMap L).bijective

end Restriction

end TauCeti.ClassFieldTheory
