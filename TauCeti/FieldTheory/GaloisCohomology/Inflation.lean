/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# The units along a tower of Galois extensions

Let `K ⊆ L ⊆ M` be a tower of fields with `L/K` normal. Restriction `Gal(M/K) → Gal(L/K)` and the
inclusion `Lˣ → Mˣ` are compatible: `σ(ι(a)) = ι(σ|_L(a))` for `σ ∈ Gal(M/K)` and `a ∈ Lˣ`. This
file records the inclusion as a morphism `unitsInflationHom K L M` from the restriction of the
`Gal(L/K)`-representation `Lˣ` to the `Gal(M/K)`-representation `Mˣ`. Through
`groupCohomology.map (AlgEquiv.restrictNormalHom L)` it induces the inflation maps

`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M/K), Mˣ)`,

in particular the inflation of relative Brauer groups `H²(Gal(L/K), Lˣ) → H²(Gal(M/K), Mˣ)` along
which local invariants are compared.

More generally, for `K ⊆ K'` and `L ⊆ M'` with `M'` a `K'`-algebra, every `σ ∈ Gal(M'/K')` is
`K`-linear and restricts to `L`. The inclusion `Lˣ → M'ˣ` is then a morphism
`unitsBaseChangeHom K L K' M'` from the restriction of `Lˣ` along `Gal(M'/K') → Gal(L/K)` to
`M'ˣ`. Together with that homomorphism it induces the base change map
`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M'/K'), M'ˣ)`.

For `K' = L` and `M' = M` the base change map is restriction `Hⁿ(Gal(M/K), Mˣ) → Hⁿ(Gal(M/L), Mˣ)`,
and inflation from `Gal(E/K)` followed by restriction to `Gal(M/L)` is base change from `E/K` to
`M/L` (`map_unitsInflationHom_comp_map_unitsBaseChangeHom`). In degree two, for `M/K` finite
Galois, inflation and restriction form the exact sequence

`0 → H²(Gal(L/K), Lˣ) → H²(Gal(M/K), Mˣ) → H²(Gal(M/L), Mˣ)`

(`map_unitsInflationHom_two_injective`, `mem_range_map_unitsInflationHom_two_iff`): this is the
inflation-restriction sequence of `Gal(M/L) → Gal(M/K) → Gal(L/K)`, whose hypothesis
`H¹(Gal(M/L), Mˣ) = 0` is Hilbert's Theorem 90, and whose quotient term is identified with
`H²(Gal(L/K), Lˣ)` because the units of `M` fixed by `Gal(M/L)` are the units of `L`. In the
language of relative Brauer groups, `Br(M/K) ∩ ker(res_{M/L}) = Br(L/K)`.

## Main definitions

* `TauCeti.unitsInflationHom`: the inclusion `Lˣ → Mˣ` as a morphism of `Gal(M/K)`-representations
  from the restriction of `Lˣ` along `Gal(M/K) → Gal(L/K)`.
* `TauCeti.unitsBaseChangeHom`: the inclusion `Lˣ → M'ˣ` as a morphism of
  `Gal(M'/K')`-representations from the restriction of `Lˣ` along `Gal(M'/K') → Gal(L/K)`.

## Main results

* `TauCeti.map_unitsInflationHom_comp_map_unitsBaseChangeHom`: inflation followed by restriction
  is base change.
* `TauCeti.map_unitsInflationHom_two_injective`: inflation `H²(Gal(L/K), Lˣ) → H²(Gal(M/K), Mˣ)`
  is injective.
* `TauCeti.mem_range_map_unitsInflationHom_two_iff`: a class of `H²(Gal(M/K), Mˣ)` is inflated
  from `H²(Gal(L/K), Lˣ)` exactly when its restriction to `Gal(M/L)` vanishes.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, Proposition 1.34.
-/

public section

namespace TauCeti

universe u

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [Normal K L]

/-- **The units along a tower of Galois extensions**: for `K ⊆ L ⊆ M` with `L/K` normal, the
inclusion `Lˣ → Mˣ` is a morphism of `Gal(M/K)`-representations from `Lˣ`, on which `Gal(M/K)` acts
through restriction to `L`, to `Mˣ`. It is the coefficient map of inflation
`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M/K), Mˣ)`. -/
noncomputable def unitsInflationHom :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ⟶
      Rep.ofMulDistribMulAction Gal(M/K) Mˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (algebraMap L M : L →* M)).toAdditive.toIntLinearMap fun σ a =>
      Additive.toMul.injective <| Units.ext <|
        AlgEquiv.restrictNormal_commutes σ L (Rep.toAdditive a).toMul

/-- `unitsInflationHom K L M` is the inclusion `Lˣ → Mˣ`. -/
theorem unitsInflationHom_apply (a : Lˣ) :
    (unitsInflationHom K L M).hom
        ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul a)) =
      (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm
        (Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :=
  (rfl)

/-- Read through `Rep.toAdditive`, `unitsInflationHom K L M` is `Units.map (algebraMap L M)`. -/
private theorem toAdditive_comp_unitsInflationHom :
    Rep.toAdditive (M := Gal(M/K)) (G := Mˣ) ∘ (unitsInflationHom K L M).hom =
      Additive.ofMul ∘ Units.map (algebraMap L M : L →* M) ∘ Additive.toMul ∘
        Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) := by
  ext x
  obtain ⟨a, rfl⟩ := (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm.surjective x
  rw [← ofMul_toMul a, Function.comp_apply, unitsInflationHom_apply]
  simp

section BaseChange

variable (K' M' : Type u) [Field K'] [Field M'] [Algebra K K'] [Algebra K' M'] [Algebra K M']
  [IsScalarTower K K' M'] [Algebra L M'] [IsScalarTower K L M']

/-- **The units along a base change of Galois extensions**: for `K ⊆ K'` and `L ⊆ M'` with `L/K`
normal and `M'` a `K'`-algebra, the inclusion `Lˣ → M'ˣ` is a morphism of
`Gal(M'/K')`-representations from `Lˣ`, on which `Gal(M'/K')` acts through restriction to `L`, to
`M'ˣ`. Together with the homomorphism `Gal(M'/K') → Gal(L/K)` it induces the cohomology map
`Hⁿ(Gal(L/K), Lˣ) → Hⁿ(Gal(M'/K'), M'ˣ)`. -/
noncomputable def unitsBaseChangeHom :
    Rep.res ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K) :
        Gal(M'/K') →* Gal(L/K))
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ⟶
      Rep.ofMulDistribMulAction Gal(M'/K') M'ˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (algebraMap L M' : L →* M')).toAdditive.toIntLinearMap fun σ a =>
      Additive.toMul.injective <| Units.ext <|
        AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L (Rep.toAdditive a).toMul

/-- `unitsBaseChangeHom K L K' M'` is the inclusion `Lˣ → M'ˣ`. -/
theorem unitsBaseChangeHom_apply (a : Lˣ) :
    (unitsBaseChangeHom K L K' M').hom
        ((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul a)) =
      (Rep.toAdditive (M := Gal(M'/K')) (G := M'ˣ)).symm
        (Additive.ofMul (Units.map (algebraMap L M' : L →* M') a)) :=
  (rfl)

/-- Read through `Rep.toAdditive`, `unitsBaseChangeHom K L K' M'` is
`Units.map (algebraMap L M')`. -/
private theorem toAdditive_comp_unitsBaseChangeHom :
    Rep.toAdditive (M := Gal(M'/K')) (G := M'ˣ) ∘ (unitsBaseChangeHom K L K' M').hom =
      Additive.ofMul ∘ Units.map (algebraMap L M' : L →* M') ∘ Additive.toMul ∘
        Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) := by
  ext x
  obtain ⟨a, rfl⟩ := (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm.surjective x
  rw [← ofMul_toMul a, Function.comp_apply, unitsBaseChangeHom_apply]
  simp

end BaseChange

open CategoryTheory

section Composition

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M] [Algebra K E] [Algebra K L]
  [Algebra K M] [Algebra E M] [Algebra L M] [IsScalarTower K E M] [IsScalarTower K L M]
  [Normal K E] [Normal K M]

/-- Including `Eˣ` into `Mˣ` and then base changing from `M/K` to `M/L` is base change from `E/K`
to `M/L`. -/
private theorem unitsBaseChangeHom_unitsInflationHom
    (x : Rep.res (AlgEquiv.restrictNormalHom E : Gal(M/K) →* Gal(E/K))
      (Rep.ofMulDistribMulAction Gal(E/K) Eˣ)) :
    (unitsBaseChangeHom K M L M).hom ((unitsInflationHom K E M).hom x) =
      (unitsBaseChangeHom K E L M).hom x := by
  apply (Rep.toAdditive (M := Gal(M/L)) (G := Mˣ)).injective
  have h₁ := congrFun (toAdditive_comp_unitsBaseChangeHom K M L M) ((unitsInflationHom K E M).hom x)
  have h₂ := congrFun (toAdditive_comp_unitsInflationHom K E M) x
  have h₃ := congrFun (toAdditive_comp_unitsBaseChangeHom K E L M) x
  simp only [Function.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp

/-- **Inflation followed by restriction is base change.** For `K ⊆ E ⊆ M` and `K ⊆ L ⊆ M`,
inflating a class of `Hⁿ(Gal(E/K), Eˣ)` to `Hⁿ(Gal(M/K), Mˣ)` and restricting it to
`Hⁿ(Gal(M/L), Mˣ)` is the base change map from `E/K` to `M/L`. -/
theorem map_unitsInflationHom_comp_map_unitsBaseChangeHom (n : ℕ) :
    groupCohomology.map (AlgEquiv.restrictNormalHom E) (unitsInflationHom K E M) n ≫
        groupCohomology.map ((AlgEquiv.restrictNormalHom M).comp (AlgEquiv.restrictScalarsHom K))
          (unitsBaseChangeHom K M L M) n =
      groupCohomology.map ((AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K))
        (unitsBaseChangeHom K E L M) n := by
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · rw [AlgEquiv.restrictNormalHom_id, MonoidHom.id_comp]
  · ext x
    simpa using unitsBaseChangeHom_unitsInflationHom K E L M x

end Composition

section InflationRestriction

variable (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- `unitsBaseChangeHom K M L M` is the identity of `Mˣ`, so it is bijective. -/
private theorem unitsBaseChangeHom_self_bijective [Normal K M] :
    Function.Bijective (unitsBaseChangeHom K M L M).hom := by
  refine (Function.Bijective.of_comp_iff' (Rep.toAdditive (M := Gal(M/L)) (G := Mˣ)).bijective
    _).1 ?_
  -- The underlying unit is unchanged, `Units.map (algebraMap M M)` being the identity.
  rw [toAdditive_comp_unitsBaseChangeHom]
  exact Additive.ofMul.bijective.comp <| (Units.map_bijective Function.bijective_id).comp <|
    Additive.toMul.bijective.comp (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).bijective

variable [Normal K L]

/-- `unitsInflationHom K L M` maps a unit of `L` to its image in `M`. -/
private theorem coe_toMul_unitsInflationHom_apply
    (x : Rep.res (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K))
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    ((Additive.toMul (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)
        ((unitsInflationHom K L M).hom x)) : Mˣ) : M) =
      algebraMap L M (Additive.toMul (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x) : Lˣ) := by
  obtain ⟨a, rfl⟩ := (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm.surjective x
  rw [← ofMul_toMul a, unitsInflationHom_apply]
  simp

/-- `unitsInflationHom K L M` is injective. -/
private theorem unitsInflationHom_injective :
    Function.Injective (unitsInflationHom K L M).hom := by
  refine Function.Injective.of_comp (f := Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)) ?_
  rw [toAdditive_comp_unitsInflationHom]
  exact Additive.ofMul.injective.comp <| (Units.map_injective (algebraMap L M).injective).comp <|
    Additive.toMul.injective.comp (Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).injective

variable [FiniteDimensional K M] [IsGalois K M]

/-- The units of `M` fixed by `Gal(M/L)`, the kernel of restriction to `L`, are the units of `L`. -/
private theorem range_unitsInflationHom :
    LinearMap.range (unitsInflationHom K L M).hom.toLinearMap =
      Representation.invariants ((Rep.ofMulDistribMulAction Gal(M/K) Mˣ).ρ.comp
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker.subtype) := by
  have : FiniteDimensional L M := FiniteDimensional.right K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  ext v
  simp only [LinearMap.mem_range, Representation.mem_invariants,
    Representation.IntertwiningMap.toLinearMap_apply]
  constructor
  · rintro ⟨x, rfl⟩ ⟨s, hs⟩
    refine (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).injective <| Additive.toMul.injective <|
      Units.ext ?_
    -- `s` acts on a unit of `M` by acting on its underlying element.
    have hρ : ((Additive.toMul (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)
        ((Rep.ofMulDistribMulAction Gal(M/K) Mˣ).ρ s ((unitsInflationHom K L M).hom x))) : Mˣ) :
          M) = s (Additive.toMul (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)
            ((unitsInflationHom K L M).hom x)) : Mˣ) :=
      rfl
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hρ, coe_toMul_unitsInflationHom_apply,
      ← AlgEquiv.restrictNormal_commutes,
      ← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, MonoidHom.mem_ker.1 hs,
      AlgEquiv.one_apply]
  · intro hv
    set u : Mˣ := Additive.toMul (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ) v)
    have hfix (τ : Gal(M/L)) : τ (u : M) = u :=
      congrArg (fun w => ((Additive.toMul (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ) w) : Mˣ) : M))
        (hv ⟨τ.restrictScalars K,
          AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M ▸ ⟨τ, rfl⟩⟩)
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (u : M)).2 hfix)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← ha, map_zero])
    refine ⟨(Rep.toAdditive (M := Gal(L/K)) (G := Lˣ)).symm (Additive.ofMul (Units.mk0 a ha0)),
      (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).injective <| Additive.toMul.injective <|
        Units.ext ?_⟩
    rw [coe_toMul_unitsInflationHom_apply, AddEquiv.apply_symm_apply, toMul_ofMul, Units.val_mk0]
    exact ha

/-- **Inflation into `H²(Gal(M/K), Mˣ)` is injective.** For a tower `K ⊆ L ⊆ M` with `M/K` finite
Galois and `L/K` normal, inflation `H²(Gal(L/K), Lˣ) → H²(Gal(M/K), Mˣ)` is injective: by
Hilbert 90, `H¹(Gal(M/L), Mˣ) = 0`. -/
theorem map_unitsInflationHom_two_injective :
    Function.Injective
      (groupCohomology.map (AlgEquiv.restrictNormalHom L) (unitsInflationHom K L M) 2).hom :=
  groupCohomology.map_succ_injective (AlgEquiv.restrictNormalHom_surjective M)
    (unitsInflationHom_injective K L M) (range_unitsInflationHom K L M) 1 fun i hi => by
      obtain rfl : i = 0 := by omega
      exact isZero_groupCohomology_one_res_units (Subgroup.subtype_injective _)

/-- **The inflation-restriction sequence of relative Brauer groups.** For a tower `K ⊆ L ⊆ M`
with `M/K` finite Galois and `L/K` normal, a class of `H²(Gal(M/K), Mˣ)` is inflated from
`H²(Gal(L/K), Lˣ)` exactly when its restriction to `H²(Gal(M/L), Mˣ)` vanishes. Restriction is the
base change map `unitsBaseChangeHom K M L M` along `Gal(M/L) → Gal(M/K)`. -/
theorem mem_range_map_unitsInflationHom_two_iff
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(M/K) Mˣ) 2) :
    x ∈ LinearMap.range
        (groupCohomology.map (AlgEquiv.restrictNormalHom L) (unitsInflationHom K L M) 2).hom ↔
      groupCohomology.map ((AlgEquiv.restrictNormalHom M).comp (AlgEquiv.restrictScalarsHom K))
        (unitsBaseChangeHom K M L M) 2 x = 0 := by
  have hι : Function.Injective
      ((AlgEquiv.restrictNormalHom M).comp (AlgEquiv.restrictScalarsHom K) :
        Gal(M/L) →* Gal(M/K)) := by
    rw [AlgEquiv.restrictNormalHom_id]
    exact AlgEquiv.restrictScalarsHom_injective K
  have hιπ : ((AlgEquiv.restrictNormalHom M).comp (AlgEquiv.restrictScalarsHom K) :
        Gal(M/L) →* Gal(M/K)).range =
      (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker := by
    rw [AlgEquiv.restrictNormalHom_id, MonoidHom.id_comp]
    exact AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M
  have hC : ∀ i < 1, Limits.IsZero
      (groupCohomology (Rep.ofMulDistribMulAction Gal(M/L) Mˣ) (i + 1)) := by
    intro i hi
    obtain rfl : i = 0 := by omega
    have : FiniteDimensional L M := FiniteDimensional.right K L M
    have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    -- `Rep.ofAlgebraAutOnUnits` unfolds to `Rep.ofMulDistribMulAction`, and `H1` to degree one.
    have : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(M/L) Mˣ) 1) :=
      inferInstanceAs <| Subsingleton <| groupCohomology.H1 (Rep.ofAlgebraAutOnUnits L M)
    exact ModuleCat.isZero_of_subsingleton _
  rw [groupCohomology.range_map_succ_eq_ker_map_succ (AlgEquiv.restrictNormalHom_surjective M)
    (unitsInflationHom_injective K L M) (range_unitsInflationHom K L M) hι hιπ
    (unitsBaseChangeHom_self_bijective K L M) 1 hC]
  rfl

end InflationRestriction

end TauCeti
