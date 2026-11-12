/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Equiv
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia

import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Finite
import TauCeti.Topology.Algebra.Group.Profinite.Limit
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The absolute upper ramification filtration of a local field

For a finite Galois extension `M/K` of nonarchimedean local fields, Herbrand's theorem in the upper
numbering (`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`) says
that restriction along a Galois subextension `L/K` maps `Gal(M/K)^v` onto `Gal(L/K)^v` for every
`v ≥ -1`. Unlike the lower numbering, the upper numbering therefore forms an inverse system over
all finite Galois subextensions of an algebraic closure `AlgebraicClosure K` of `K`, including
nonabelian ones.

This file defines the **absolute upper ramification group**

`TauCeti.localAbsoluteUpperRamificationGroup K v : Subgroup (Field.absoluteGaloisGroup K)`

at each `v : RamificationIndexDomain = [-1, ∞)` as the intersection, over all finite Galois
intermediate fields `M` of `AlgebraicClosure K / K`, of the preimages of `Gal(M/K)^v` under
`AlgEquiv.restrictNormalHom M`, using the canonical spectral-norm local-field structure induced
from `K` (`TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup`). By uniqueness of
the extended valuative relation and topology on a finite extension, the same membership condition
holds for any compatible local-field structure on any finite Galois intermediate field.

Compactness of the absolute Galois group turns Herbrand's finite-level surjectivity into
surjectivity from the inverse limit: restriction to every finite Galois subextension `L/K` maps
`G_K^v` onto `Gal(L/K)^v`. More generally, for every Galois intermediate field `E` of
`AlgebraicClosure K / K`, restriction maps `G_K^v` onto the subgroup of `Gal(E/K)` cut out by the
upper ramification groups of the finite Galois intermediate fields of `E/K`.

At special values and in the limit, the filtration recovers the classical subgroups of `G_K`:

* at `v = -1` it is the whole absolute Galois group `⊤`;
* at `v = 0` it is the inertia subgroup `TauCeti.inertiaSubgroup K`;
* the topological closure of the union of `G_K^v` over `v > 0` is the wild inertia subgroup
  `TauCeti.wildInertiaSubgroup K`;
* the intersection over all `v` (and already over natural numbers `n : ℕ`) is trivial.

Finally, a continuous ring isomorphism `e : K ≃+* K'` of nonarchimedean local fields transports
`G_K^v` onto `G_{K'}^v` along any extension `e' : AlgebraicClosure K ≃+* AlgebraicClosure K'`, and
in particular along `Field.absoluteGaloisGroup.map` and `TauCeti.absoluteGaloisGroupMapEquiv`.

## Main definitions

* `TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup`: the upper ramification
  group `Gal(L/K)^v` of `L : FiniteGaloisIntermediateField K Ω` equipped with the canonical
  local-field structure induced from `K`.
* `TauCeti.localAbsoluteUpperRamificationGroup K v`: the upper ramification subgroup `G_K^v` of
  `Field.absoluteGaloisGroup K`, for `v ∈ [-1, ∞)`.

## Main results

* `TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup_eq`: the finite-level adapter
  agrees with `upperRamificationGroup K L v` for any compatible local-field structure on `L`.
* `TauCeti.LocalFieldsRamification.map_algAutCongr_upperRamificationGroup`: a base-continuous
  isomorphism `K ≃+* K'` extended to `L ≃+* L'` carries `Gal(L/K)^v` onto `Gal(L'/K')^v`.
* `TauCeti.mem_localAbsoluteUpperRamificationGroup_iff`: `σ ∈ G_K^v` exactly when its restriction
  to every finite Galois subextension `L` lies in `Gal(L/K)^v`.
* `TauCeti.isClosed_localAbsoluteUpperRamificationGroup`,
  `TauCeti.localAbsoluteUpperRamificationGroup_normal`,
  `TauCeti.localAbsoluteUpperRamificationGroup_antitone`: each `G_K^v` is closed and normal, and
  the filtration is decreasing.
* `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup`: restriction to a finite
  Galois subextension `L/K` maps `G_K^v` onto `Gal(L/K)^v`.
* `TauCeti.localAbsoluteUpperRamificationGroup_neg_one`,
  `TauCeti.localAbsoluteUpperRamificationGroup_zero`,
  `TauCeti.topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup`,
  `TauCeti.iInf_localAbsoluteUpperRamificationGroup`: the values at `-1` and `0`, the closure of
  the positive-depth union (wild inertia), and the trivial intersection of all depths.
* `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup_of_isGalois`: restriction to
  any Galois intermediate field `E/K` cuts out the inverse-limit upper filtration of `Gal(E/K)`.
* `TauCeti.comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup`,
  `TauCeti.comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup`,
  `TauCeti.map_absoluteGaloisGroupMapEquiv_localAbsoluteUpperRamificationGroup`: naturality under
  continuous field isomorphisms `K ≃+* K'`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3, Proposition 14.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, p. 128.
-/

public section
noncomputable section

open ValuativeRel IntermediateField IsLocalRing Polynomial

/-! ### Finite-level upper ramification groups and transport -/

namespace TauCeti.LocalFieldsRamification

section FiniteGaloisAdapter

variable (K Ω : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- **Upper ramification group on a finite Galois intermediate field**, using the canonical
local-field structure induced from `K`. This is the upper-numbering counterpart of
`TauCeti.LocalFieldsRamification.finiteGaloisLowerRamificationGroup`. -/
def finiteGaloisUpperRamificationGroup
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    Subgroup (L ≃ₐ[K] L) :=
  letI := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  letI := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  letI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  letI := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  upperRamificationGroup K L v

/-- The finite-level adapter is `upperRamificationGroup K L v` on the induced local-field
structure. -/
theorem finiteGaloisUpperRamificationGroup_def
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    by
      letI := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
      letI := finiteIntermediateFieldTopology K Ω L.toIntermediateField
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
      haveI := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
      exact finiteGaloisUpperRamificationGroup K Ω L v = upperRamificationGroup K L v :=
  (rfl)

/-- On any finite Galois intermediate field `L` of `Ω/K`, `finiteGaloisUpperRamificationGroup`
agrees with `upperRamificationGroup K L v` for any compatible local-field structure on `L`. -/
theorem finiteGaloisUpperRamificationGroup_eq
    (L : IntermediateField K Ω) [Module.Finite K L] [IsGalois K L]
    [vr : ValuativeRel L] [ts : TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L] (v : RamificationIndexDomain) :
    finiteGaloisUpperRamificationGroup K Ω ⟨L⟩ v = upperRamificationGroup K L v := by
  have hvr : finiteIntermediateFieldValuativeRel K Ω L = vr := by
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    exact (algebraicExtensionValuativeRel_eq K L).symm.trans
      (@algebraicExtensionValuativeRel_eq K _ _ _ _ L _ _ _ vr _)
  have hts : finiteIntermediateFieldTopology K Ω L = ts := by
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    let _ := finiteIntermediateFieldTopology K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    have := finiteIntermediateField_isValuativeTopology K Ω L
    exact (algebraicExtensionNormedFieldTopology_eq K L).symm.trans
      (@algebraicExtensionNormedFieldTopology_eq K _ _ _ _ L _ _ _ vr _ ts _)
  rw [finiteGaloisUpperRamificationGroup_def]
  subst hvr hts
  rfl

/-- Every finite-level upper ramification group `Gal(L/K)^v` is normal in `Gal(L/K)`. -/
instance instNormalFiniteGaloisUpperRamificationGroup
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    (finiteGaloisUpperRamificationGroup K Ω L v).Normal := by
  let _ := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  infer_instance

/-- For each `L : FiniteGaloisIntermediateField K Ω`, the upper ramification filtration is
decreasing. -/
theorem finiteGaloisUpperRamificationGroup_antitone (L : FiniteGaloisIntermediateField K Ω) :
    Antitone (finiteGaloisUpperRamificationGroup K Ω L) := by
  let _ := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  intro v w hvw
  rw [finiteGaloisUpperRamificationGroup_def, finiteGaloisUpperRamificationGroup_def]
  exact upperRamificationGroup_antitone K L hvw

end FiniteGaloisAdapter

section RingEquivTransport

variable {K K' L L' : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Field L'] [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra K' L'] [ValuativeExtension K' L'] [Module.Finite K' L']

omit [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Module.Finite K' L'] in
/-- A ring isomorphism `eL : L ≃+* L'` extending a valuation-preserving isomorphism `e : K ≃+* K'`
of base local fields preserves the valuative relation, by uniqueness of the extended valuative
relation on the algebraic extension `L/K`. -/
private theorem map_vle_map_iff_of_vle_iff (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c)) (x y : L) :
    eL x ≤ᵥ eL y ↔ x ≤ᵥ y := by
  have heq :
      (((valuation L').comap eL.toRingHom).comap (algebraMap K L)).IsEquiv (valuation K) := by
    intro a b
    simp only [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, heL]
    rw [← (valuation L').vle_iff_le, ValuativeExtension.vle_iff_vle, he, (valuation K).vle_iff_le]
  have hExt := algebraicExtensionValuation_isEquiv heq
    (ValuativeRel.isEquiv ((valuation L).comap (algebraMap K L)) (valuation K))
  rw [(valuation L').vle_iff_le, (valuation L).vle_iff_le]
  exact hExt x y

private theorem comap_algAutCongr_lowerRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c)) (i : ℤ) :
    (lowerRamificationGroup K' L' i).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      lowerRamificationGroup K L i := by
  have hvle := map_vle_map_iff_of_vle_iff e he eL heL
  have hmem (x : L) : eL x ∈ 𝒪[L'] ↔ x ∈ 𝒪[L] := by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← map_one (valuation L'),
      ← map_one (valuation L), ← (valuation L').vle_iff_le, ← (valuation L).vle_iff_le,
      ← map_one eL, hvle]
  let fInt : 𝒪[L] ≃+* 𝒪[L'] :=
    { toFun := fun x ↦ ⟨eL x.1, (hmem x.1).2 x.2⟩
      invFun := fun y ↦ ⟨eL.symm y.1, (hmem _).1 (by simp)⟩
      left_inv := fun x ↦ Subtype.ext (eL.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (eL.apply_symm_apply y.1)
      map_mul' := fun x y ↦ Subtype.ext (map_mul eL x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add eL x.1 y.1) }
  have hmax : (maximalIdeal 𝒪[L']).comap fInt.toRingHom = maximalIdeal 𝒪[L] := by
    ext x
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal]
    exact not_congr ⟨fun h ↦ by simpa using h.map fInt.symm.toMonoidHom,
      fun h ↦ h.map fInt.toMonoidHom⟩
  have hcomap_eq_map (I : Ideal 𝒪[L']) :
      I.comap fInt.toRingHom = I.map fInt.symm.toRingHom := by
    refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun y hy ↦ ?_)
    · have hfx : fInt.symm.toRingHom (fInt.toRingHom x) = x := fInt.symm_apply_apply x
      rw [← hfx]
      exact Ideal.mem_map_of_mem fInt.symm.toRingHom hx
    · rw [Ideal.mem_comap, Ideal.mem_comap]
      have hfy : fInt.toRingHom (fInt.symm.toRingHom y) = y := fInt.apply_symm_apply y
      rwa [hfy]
  have hpow (n : ℕ) : (maximalIdeal 𝒪[L'] ^ n).comap fInt.toRingHom = maximalIdeal 𝒪[L] ^ n := by
    rw [hcomap_eq_map, Ideal.map_pow, ← hcomap_eq_map, hmax]
  symm
  rw [lowerRamificationGroup_def, lowerRamificationGroup_def]
  refine TauCeti.IsLocalRing.ramificationGroup_eq_comap_of_comap_maximalIdeal_pow
    (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) fInt.toRingHom (fun σ x ↦ ?_) hpow
    (fun n y ↦ ⟨fInt.symm y, ?_⟩) i
  · exact Subtype.ext (e.algAutCongr_apply_eL eL heL σ x.1).symm
  · have hfy : fInt.toRingHom (fInt.symm y) = y := fInt.apply_symm_apply y
    rw [hfy, sub_self]
    exact zero_mem _

/-- **Transport of lower ramification groups along a base-continuous ring isomorphism.** -/
theorem comap_algAutCongr_lowerRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c)) (i : ℤ) :
    (lowerRamificationGroup K' L' i).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      lowerRamificationGroup K L i :=
  comap_algAutCongr_lowerRamificationGroup_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL i

/-- Image form of `comap_algAutCongr_lowerRamificationGroup`. -/
theorem map_algAutCongr_lowerRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c)) (i : ℤ) :
    (lowerRamificationGroup K L i).map (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      lowerRamificationGroup K' L' i := by
  rw [← comap_algAutCongr_lowerRamificationGroup e he eL heL i,
    Subgroup.map_comap_eq_self_of_surjective (e.algAutCongr eL heL).surjective]

variable [IsGalois K L] [IsGalois K' L']

private theorem comap_algAutCongr_upperRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K' L' v).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K L v := by
  have hcard (i : ℤ) :
      Nat.card (lowerRamificationGroup K L i) = Nat.card (lowerRamificationGroup K' L' i) := by
    have hmap :
        (lowerRamificationGroup K L i).map (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
          lowerRamificationGroup K' L' i := by
      rw [← comap_algAutCongr_lowerRamificationGroup_of_vle_iff e he eL heL i,
        Subgroup.map_comap_eq_self_of_surjective (e.algAutCongr eL heL).surjective]
    rw [← hmap]
    exact Nat.card_congr ((e.algAutCongr eL heL).subgroupMap (lowerRamificationGroup K L i)).toEquiv
  have hherbrand (u : RamificationIndexDomain) : herbrand K L u = herbrand K' L' u := by
    apply Subtype.ext
    rw [coe_herbrand, coe_herbrand]
    congr 1 with t
    rw [lowerRamificationGroupReal_def, lowerRamificationGroupReal_def, hcard, hcard]
  have hinv : inverseHerbrand K L v = inverseHerbrand K' L' v := by
    apply (herbrand_strictMono K' L').injective
    rw [herbrand_inverseHerbrand, ← hherbrand, herbrand_inverseHerbrand]
  rw [upperRamificationGroup_def, upperRamificationGroup_def, ← hinv,
    lowerRamificationGroupReal_def, lowerRamificationGroupReal_def,
    comap_algAutCongr_lowerRamificationGroup_of_vle_iff e he eL heL]

/-- **Invariance of the Herbrand function under a base-continuous ring isomorphism.** -/
theorem herbrand_eq_of_ringEquiv (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (u : RamificationIndexDomain) :
    herbrand K L u = herbrand K' L' u := by
  have hcard (i : ℤ) :
      Nat.card (lowerRamificationGroup K L i) = Nat.card (lowerRamificationGroup K' L' i) := by
    rw [← map_algAutCongr_lowerRamificationGroup e he eL heL i]
    exact Nat.card_congr ((e.algAutCongr eL heL).subgroupMap (lowerRamificationGroup K L i)).toEquiv
  apply Subtype.ext
  rw [coe_herbrand, coe_herbrand]
  congr 1 with t
  rw [lowerRamificationGroupReal_def, lowerRamificationGroupReal_def, hcard, hcard]

/-- **Invariance of the inverse Herbrand function under a base-continuous ring isomorphism.** -/
theorem inverseHerbrand_eq_of_ringEquiv (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    inverseHerbrand K L v = inverseHerbrand K' L' v := by
  apply (herbrand_strictMono K' L').injective
  rw [herbrand_inverseHerbrand, ← herbrand_eq_of_ringEquiv e he eL heL, herbrand_inverseHerbrand]

/-- **Transport of upper ramification groups along a base-continuous ring isomorphism.** -/
theorem comap_algAutCongr_upperRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K' L' v).comap (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K L v :=
  comap_algAutCongr_upperRamificationGroup_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) eL heL v

/-- Image form of `comap_algAutCongr_upperRamificationGroup`. -/
theorem map_algAutCongr_upperRamificationGroup (e : K ≃+* K') (he : Continuous e)
    (eL : L ≃+* L') (heL : ∀ c : K, eL (algebraMap K L c) = algebraMap K' L' (e c))
    (v : RamificationIndexDomain) :
    (upperRamificationGroup K L v).map (e.algAutCongr eL heL : (L ≃ₐ[K] L) →* (L' ≃ₐ[K'] L')) =
      upperRamificationGroup K' L' v := by
  rw [← comap_algAutCongr_upperRamificationGroup e he eL heL v,
    Subgroup.map_comap_eq_self_of_surjective (e.algAutCongr eL heL).surjective]

end RingEquivTransport

end TauCeti.LocalFieldsRamification

/-! ### The absolute upper ramification filtration -/

namespace TauCeti

open LocalFieldsRamification

section Basic

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The absolute upper ramification group of a local field.** For real `v ≥ -1`, an absolute
Galois automorphism belongs to `G_K^v` precisely when its restriction to every finite Galois
intermediate field belongs to its upper ramification group, using the canonical extended valuation
(Serre, *Local Fields*, IV §3, Proposition 14). -/
def localAbsoluteUpperRamificationGroup
    (v : RamificationIndexDomain) : Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
    (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
      (AlgEquiv.restrictNormalHom M : Field.absoluteGaloisGroup K →* (M ≃ₐ[K] M))

/-- The absolute upper ramification group is the intersection, over all finite Galois intermediate
fields of `AlgebraicClosure K / K`, of the preimages of the finite upper ramification groups. -/
theorem localAbsoluteUpperRamificationGroup_def (v : RamificationIndexDomain) :
    localAbsoluteUpperRamificationGroup K v =
      ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
          (AlgEquiv.restrictNormalHom M : Field.absoluteGaloisGroup K →* (M ≃ₐ[K] M)) :=
  (rfl)

variable {K} in
/-- Membership in `localAbsoluteUpperRamificationGroup K v` in terms of
`FiniteGaloisIntermediateField`s equipped with the canonical induced local-field structures. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K} :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      ∀ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        AlgEquiv.restrictNormal σ M ∈
          finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v := by
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  -- `Field.absoluteGaloisGroup K` is semireducible; expose `Gal(AlgebraicClosure K/K)`
  -- so `Subgroup.mem_iInf` applies.
  change σ₀ ∈
      (⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
          (AlgEquiv.restrictNormalHom M) : Subgroup Gal(AlgebraicClosure K/K)) ↔ _
  rw [Subgroup.mem_iInf]
  rfl

variable {K} in
/-- **Restriction to any compatible finite Galois subextension.** For any compatible local-field
structure on a finite Galois intermediate field `L` of `AlgebraicClosure K / K`, an element of
`localAbsoluteUpperRamificationGroup K v` restricts into `upperRamificationGroup K L v`. -/
theorem restrictNormal_mem_upperRamificationGroup
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    (hσ : σ ∈ localAbsoluteUpperRamificationGroup K v) :
    AlgEquiv.restrictNormal σ L ∈ upperRamificationGroup K L v := by
  have hM := mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ ⟨L⟩
  rwa [finiteGaloisUpperRamificationGroup_eq K (AlgebraicClosure K) L v] at hM

variable {K} in
/-- **Inverse-limit characterization across arbitrary compatible local-field structures.** An
automorphism `σ ∈ G_K` lies in `localAbsoluteUpperRamificationGroup K v` if and only if, for every
finite Galois subextension `L` of `AlgebraicClosure K / K` and every compatible local-field
structure on `L`, its restriction to `L` lies in `upperRamificationGroup K L v`. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K} :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      ∀ (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
        [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
        [ValuativeExtension K L],
        AlgEquiv.restrictNormal σ L ∈ upperRamificationGroup K L v := by
  refine ⟨fun hσ L _ _ _ _ _ _ ↦ restrictNormal_mem_upperRamificationGroup L hσ, fun h ↦ ?_⟩
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  exact h M.toIntermediateField

/-- **Every absolute upper ramification group is normal** in `Field.absoluteGaloisGroup K`. -/
instance localAbsoluteUpperRamificationGroup_normal (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).Normal := by
  refine ⟨fun σ hσ τ ↦ mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_⟩
  have hσM := mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M
  let f : Field.absoluteGaloisGroup K →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hmap : AlgEquiv.restrictNormal (τ * σ * τ⁻¹) M =
      AlgEquiv.restrictNormal τ M * AlgEquiv.restrictNormal σ M *
        (AlgEquiv.restrictNormal τ M)⁻¹ :=
    (map_mul f (τ * σ) τ⁻¹).trans (by rw [map_mul, map_inv]; rfl)
  rw [hmap]
  exact (instNormalFiniteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).conj_mem _ hσM _

/-- **Every absolute upper ramification group is closed** in the Krull topology on
`Field.absoluteGaloisGroup K`. -/
theorem isClosed_localAbsoluteUpperRamificationGroup (v : RamificationIndexDomain) :
    IsClosed (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K)) := by
  -- `Field.absoluteGaloisGroup K` is semireducible; expose `Gal(AlgebraicClosure K/K)`
  -- so `Subgroup.coe_iInf` applies.
  change IsClosed (((⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
        (AlgEquiv.restrictNormalHom M) : Subgroup Gal(AlgebraicClosure K/K)) :
    Set Gal(AlgebraicClosure K/K)))
  rw [Subgroup.coe_iInf]
  refine isClosed_iInter fun M ↦ ?_
  have : T2Space (M ≃ₐ[K] M) := krullTopology_t2
  have : DiscreteTopology (M ≃ₐ[K] M) := Finite.instDiscreteTopology
  exact (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)

/-- **The absolute upper ramification filtration is decreasing.** -/
theorem localAbsoluteUpperRamificationGroup_antitone :
    Antitone (localAbsoluteUpperRamificationGroup K) := by
  intro v w hvw σ hσ
  exact mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦
    finiteGaloisUpperRamificationGroup_antitone K (AlgebraicClosure K) M hvw
      (mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M)

end Basic

/-! ### Finite-level surjectivity -/

section FiniteLevel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- In a containment `L ≤ N` of finite Galois intermediate fields of `AlgebraicClosure K / K`,
restricting from `N` to `L` maps `Gal(N/K)^v` onto `Gal(L/K)^v`, and commutes with restriction
from `AlgebraicClosure K`. -/
private theorem restrictNormal_tower_upperRamificationGroup
    (L N : IntermediateField K (AlgebraicClosure K)) (hLN : L ≤ N)
    [Module.Finite K L] [IsGalois K L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    [Module.Finite K N] [IsGalois K N] [ValuativeRel N] [TopologicalSpace N]
    [IsNonarchimedeanLocalField N] [ValuativeExtension K N]
    (v : RamificationIndexDomain) :
    (∀ σ : Gal(AlgebraicClosure K/K),
      AlgEquiv.restrictNormal σ N ∈ upperRamificationGroup K N v →
        AlgEquiv.restrictNormal σ L ∈ upperRamificationGroup K L v) ∧
      (∀ τ ∈ upperRamificationGroup K L v,
        ∃ σ : Gal(AlgebraicClosure K/K),
          AlgEquiv.restrictNormal σ N ∈ upperRamificationGroup K N v ∧
            AlgEquiv.restrictNormal σ L = τ) := by
  let ι : L →ₐ[K] N := inclusion hLN
  let _ : Algebra L N := ι.toAlgebra
  have : IsScalarTower K L N := .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : ValuativeExtension L N := ι.valuativeExtension
  have : Module.Finite L N := .of_restrictScalars_finite K L N
  have hcomp (σ : Gal(AlgebraicClosure K/K)) :
      AlgEquiv.restrictNormal σ L = AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ N) L := by
    ext x
    have h1 := AlgEquiv.restrictNormal_commutes σ L x
    have h2 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormal σ N) L x
    have h3 := AlgEquiv.restrictNormal_commutes σ N (ι x)
    exact h1.trans (h3.symm.trans (congrArg Subtype.val h2).symm)
  refine ⟨fun σ hσN ↦ ?_, fun τ hτ ↦ ?_⟩
  · rw [hcomp σ, ← map_restrictNormalHom_upperRamificationGroup K L N v]
    exact ⟨AlgEquiv.restrictNormal σ N, hσN, rfl⟩
  · rw [← map_restrictNormalHom_upperRamificationGroup K L N v] at hτ
    obtain ⟨ρ, hρ, hρτ⟩ := hτ
    obtain ⟨σ, hσρ⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) ρ
    have hσρ' : AlgEquiv.restrictNormal σ N = ρ := hσρ
    have hρτ' : AlgEquiv.restrictNormal ρ L = τ := hρτ
    exact ⟨σ, hσρ'.symm ▸ hρ, (hcomp σ).trans (hσρ' ▸ hρτ')⟩

private theorem restrictNormal_mono_finiteGaloisUpperRamificationGroup
    {M N : FiniteGaloisIntermediateField K (AlgebraicClosure K)} (hMN : M ≤ N)
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    (hσN : AlgEquiv.restrictNormalHom N.toIntermediateField σ ∈
      finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) N v) :
    AlgEquiv.restrictNormalHom M.toIntermediateField σ ∈
      finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v := by
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) N.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) N.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    N.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) N.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def] at hσN ⊢
  exact (restrictNormal_tower_upperRamificationGroup M.toIntermediateField N.toIntermediateField
    ((FiniteGaloisIntermediateField.le_iff M N).1 hMN) v).1 σ hσN

/-- **Absolute upper ramification groups surject onto finite upper ramification groups.** For every
compatible local-field structure on a finite Galois intermediate field `L` of
`AlgebraicClosure K / K` and every `v ≥ -1`, restriction maps
`localAbsoluteUpperRamificationGroup K v` onto `upperRamificationGroup K L v`. -/
@[simp]
theorem map_restrictNormalHom_localAbsoluteUpperRamificationGroup
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroup K L v := by
  refine le_antisymm ?_ fun τ hτ ↦ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact restrictNormal_mem_upperRamificationGroup L hσ
  · -- Intersect the closed coset fibers `{σ ∈ G_K | σ|_L = τ ∧ σ|_M ∈ Gal(M/K)^v}` over all
    -- finite Galois `M`; Herbrand's theorem on `L ⊔ M` makes each fiber nonempty.
    let S : FiniteGaloisIntermediateField K (AlgebraicClosure K) →
        Set (Field.absoluteGaloisGroup K) := fun M ↦
      (AlgEquiv.restrictNormalHom L) ⁻¹' {τ} ∩
        (AlgEquiv.restrictNormalHom M.toIntermediateField) ⁻¹'
          (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v : Set (M ≃ₐ[K] M))
    have hcl (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : IsClosed (S M) := by
      have : T2Space (L ≃ₐ[K] L) := krullTopology_t2
      have : DiscreteTopology (L ≃ₐ[K] L) := Finite.instDiscreteTopology
      have : T2Space (M ≃ₐ[K] M) := krullTopology_t2
      have : DiscreteTopology (M ≃ₐ[K] M) := Finite.instDiscreteTopology
      exact ((isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous L)).inter
        ((isClosed_discrete _).preimage
          (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField))
    have hne (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : (S M).Nonempty := by
      let L₀ : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⟨L⟩
      let N : FiniteGaloisIntermediateField K (AlgebraicClosure K) := L₀ ⊔ M
      let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) N.toIntermediateField
      let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) N.toIntermediateField
      have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
        N.toIntermediateField
      have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K)
        N.toIntermediateField
      have hLN : L ≤ N.toIntermediateField :=
        (FiniteGaloisIntermediateField.le_iff L₀ N).1 le_sup_left
      obtain ⟨σ, hσN, hσL⟩ :=
        (restrictNormal_tower_upperRamificationGroup L N.toIntermediateField hLN v).2 τ hτ
      exact ⟨σ, hσL, restrictNormal_mono_finiteGaloisUpperRamificationGroup le_sup_right
        (by rwa [finiteGaloisUpperRamificationGroup_def])⟩
    have hdir : Directed (· ⊇ ·) S := fun M₁ M₂ ↦
      ⟨M₁ ⊔ M₂,
        fun _ ⟨hL, hN⟩ ↦
          ⟨hL, restrictNormal_mono_finiteGaloisUpperRamificationGroup le_sup_left hN⟩,
        fun _ ⟨hL, hN⟩ ↦
          ⟨hL, restrictNormal_mono_finiteGaloisUpperRamificationGroup le_sup_right hN⟩⟩
    obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hne
      (fun M ↦ (hcl M).isCompact) hcl
    exact ⟨σ, mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦
      (Set.mem_iInter.1 hσ M).2, (Set.mem_iInter.1 hσ ⟨L⟩).1⟩

/-- Every element of a finite upper ramification group `Gal(L/K)^v` lifts to
`localAbsoluteUpperRamificationGroup K v`. -/
theorem exists_mem_localAbsoluteUpperRamificationGroup_restrictNormal_eq
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    {v : RamificationIndexDomain} {τ : L ≃ₐ[K] L} (hτ : τ ∈ upperRamificationGroup K L v) :
    ∃ σ ∈ localAbsoluteUpperRamificationGroup K v, AlgEquiv.restrictNormal σ L = τ := by
  rwa [← map_restrictNormalHom_localAbsoluteUpperRamificationGroup L v] at hτ

end FiniteLevel

/-! ### Special values and limits -/

section SpecialValues

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **At `-1`, the absolute upper ramification group is the whole absolute Galois group.** -/
@[simp]
theorem localAbsoluteUpperRamificationGroup_neg_one :
    localAbsoluteUpperRamificationGroup K ⟨-1, le_rfl⟩ = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  have hv : ((⟨-1, le_rfl⟩ : RamificationIndexDomain) : ℝ) ≤ 0 := neg_nonpos.2 zero_le_one
  have hneg1 : ((⟨-1, le_rfl⟩ : RamificationIndexDomain) : ℝ) = ((-1 : ℤ) : ℝ) := by norm_num
  rw [finiteGaloisUpperRamificationGroup_def,
    upperRamificationGroup_of_coe_le_zero K M hv, hneg1, lowerRamificationGroupReal_intCast,
    lowerRamificationGroup_eq_top_of_le_neg_one K M le_rfl]
  exact Subgroup.mem_top _

/-- **At `0`, the absolute upper ramification group is the inertia subgroup `I_K`.** -/
@[simp]
theorem localAbsoluteUpperRamificationGroup_zero :
    localAbsoluteUpperRamificationGroup K ⟨0, by norm_num⟩ = inertiaSubgroup K := by
  have h0 : (0 : ℝ) = ((0 : ℤ) : ℝ) := Int.cast_zero.symm
  refine le_antisymm (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)
  · -- Every element of `K^{ur}` lies in a finite unramified Galois subextension `L`, where
    -- `Gal(L/K)^0 = G_0(L/K)` has order `e(L/K) = 1`.
    refine mem_inertiaSubgroup_iff.2 fun x hx ↦ ?_
    obtain ⟨f, _, hxf⟩ := mem_maximalUnramifiedExtension_iff.1 hx
    let L := unramifiedExtension K (AlgebraicClosure K) f
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
    have : IsUnramified K L := isUnramified_unramifiedExtension
    have hσL := restrictNormal_mem_upperRamificationGroup L hσ
    rw [upperRamificationGroup_of_coe_le_zero K L (v := ⟨0, by norm_num⟩) le_rfl, Subtype.coe_mk,
      h0, lowerRamificationGroupReal_intCast] at hσL
    have hcard : Nat.card (lowerRamificationGroup K L 0) = 1 := by
      rw [natCard_lowerRamificationGroup_zero K L,
        (isUnramified_iff_ramificationIndex_eq_one K L).1 ‹IsUnramified K L›]
    rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hσL
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, hxf⟩).symm.trans
      (by rw [hσL, AlgEquiv.one_apply]; rfl)
  · refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
      M.toIntermediateField
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
    rw [finiteGaloisUpperRamificationGroup_def,
      upperRamificationGroup_of_coe_le_zero K M (v := ⟨0, by norm_num⟩) le_rfl,
      Subtype.coe_mk, h0, lowerRamificationGroupReal_intCast]
    exact restrictNormal_mem_lowerRamificationGroup_zero M.toIntermediateField hσ

/-- For nonnegative `v`, `G_K^v` is contained in the inertia subgroup `I_K`. -/
theorem localAbsoluteUpperRamificationGroup_le_inertiaSubgroup
    {v : RamificationIndexDomain} (hv : 0 ≤ (v : ℝ)) :
    localAbsoluteUpperRamificationGroup K v ≤ inertiaSubgroup K := by
  rw [← localAbsoluteUpperRamificationGroup_zero K]
  exact localAbsoluteUpperRamificationGroup_antitone K (Subtype.mk_le_mk.2 hv)

/-- For strictly positive `v`, `G_K^v` is contained in the wild inertia subgroup `P_K`. -/
theorem localAbsoluteUpperRamificationGroup_le_wildInertiaSubgroup
    {v : RamificationIndexDomain} (hv : 0 < (v : ℝ)) :
    localAbsoluteUpperRamificationGroup K v ≤ wildInertiaSubgroup K := by
  intro σ hσ
  refine mem_wildInertiaSubgroup_iff_forall_restrictNormal_mem_finiteGaloisLowerRamificationGroup.2
    fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  rw [finiteGaloisLowerRamificationGroup_def]
  have hσM := mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M
  rw [finiteGaloisUpperRamificationGroup_def, upperRamificationGroup_def,
    lowerRamificationGroupReal_def] at hσM
  have hpos : 0 < (inverseHerbrand K M v : ℝ) := by
    have h0 : inverseHerbrand K M ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
      inverseHerbrand_of_coe_le_zero K M le_rfl
    have hlt := inverseHerbrand_strictMono K M (a := ⟨0, by norm_num⟩) (b := v) hv
    rwa [h0] at hlt
  have h0lt : (0 : ℤ) < ⌈(inverseHerbrand K M v : ℝ)⌉ :=
    Int.lt_ceil.2 (by rwa [Int.cast_zero])
  exact lowerRamificationGroup_antitone K M (by omega : (1 : ℤ) ≤ ⌈(inverseHerbrand K M v : ℝ)⌉) hσM

/-- Because the filtration is decreasing, the union of `G_K^v` over `v > 0` is already a subgroup,
equal to their supremum. -/
theorem coe_biSup_pos_localAbsoluteUpperRamificationGroup :
    ((⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v : Subgroup (Field.absoluteGaloisGroup K)) :
      Set (Field.absoluteGaloisGroup K)) =
      ⋃ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K)) := by
  let PosIdx := {v : RamificationIndexDomain // 0 < (v : ℝ)}
  have : Nonempty PosIdx := ⟨⟨⟨1, by norm_num⟩, by norm_num⟩⟩
  have hdir : Directed (· ≤ ·) (fun i : PosIdx ↦ localAbsoluteUpperRamificationGroup K i.1) :=
    fun i j ↦ ⟨⟨min i.1 j.1, lt_min i.2 j.2⟩,
      localAbsoluteUpperRamificationGroup_antitone K (min_le_left _ _),
      localAbsoluteUpperRamificationGroup_antitone K (min_le_right _ _)⟩
  have hsup : (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v) =
      ⨆ i : PosIdx, localAbsoluteUpperRamificationGroup K i.1 := iSup_subtype'
  rw [hsup, Subgroup.coe_iSup_of_directed hdir]
  ext σ
  simp [PosIdx]

/-- **Wild inertia is the topological closure of the positive-depth upper ramification groups.** -/
@[simp]
theorem topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup :
    (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v).topologicalClosure =
      wildInertiaSubgroup K := by
  set P' := (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
    localAbsoluteUpperRamificationGroup K v).topologicalClosure
  refine le_antisymm ?_ ?_
  · refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_wildInertiaSubgroup K)
    exact iSup₂_le fun v hv ↦ localAbsoluteUpperRamificationGroup_le_wildInertiaSubgroup K hv
  · -- Both `P'` and `wildInertiaSubgroup K` are closed in `G_K`; compare their images in every
    -- finite quotient `G_K ⧸ U`.
    rw [← Subgroup.limitSubgroup_map_mk' P' (Subgroup.isClosed_topologicalClosure _)]
    intro σ hσ
    rw [mem_limitSubgroup_iff]
    intro U
    obtain ⟨E, _, _, hEU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K)
      (U : Set (Field.absoluteGaloisGroup K))).1 (U.isOpen.mem_nhds U.one_mem)
    let M : IntermediateField K (AlgebraicClosure K) := E ⊓ separableClosure K (AlgebraicClosure K)
    have : Module.Finite K M :=
      Module.Finite.of_injective (inclusion (inf_le_left : M ≤ E)).toLinearMap
        (inclusion (inf_le_left : M ≤ E)).injective
    have : Algebra.IsSeparable K M := (le_separableClosure_iff K _ M).1 inf_le_right
    have : Normal K M := inferInstance
    have : IsGalois K M := ⟨⟩
    have hMU : ∀ τ : Gal(AlgebraicClosure K/K), τ ∈ M.fixingSubgroup → τ ∈ U.toSubgroup := by
      intro τ hτ
      rw [IntermediateField.fixingSubgroup_inf_separableClosure] at hτ
      exact hEU hτ
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
    -- In `M/K`, `G_1(M/K) = Gal(M/K)^{φ_{M/K}(1)}` with `φ_{M/K}(1) > 0`.
    set vM : RamificationIndexDomain := herbrand K M ⟨1, by norm_num⟩
    have hvM : 0 < (vM : ℝ) := by
      have h0 : herbrand K M ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
        herbrand_of_coe_le_zero K M le_rfl
      have hlt := herbrand_strictMono K M (a := ⟨0, by norm_num⟩) (b := ⟨1, by norm_num⟩)
        (by norm_num : (0 : ℝ) < 1)
      rwa [h0] at hlt
    have h1 : (⟨1, by norm_num⟩ : RamificationIndexDomain) = ⟨((1 : ℤ) : ℝ), by norm_num⟩ :=
      Subtype.ext Int.cast_one.symm
    have hσM : AlgEquiv.restrictNormal σ M ∈ upperRamificationGroup K M vM := by
      rw [upperRamificationGroup_herbrand, h1, lowerRamificationGroupReal_intCast]
      exact restrictNormal_mem_lowerRamificationGroup_one M hσ
    obtain ⟨τ, hτ, hτσ⟩ := exists_mem_localAbsoluteUpperRamificationGroup_restrictNormal_eq M hσM
    have hτ_sup : τ ∈ ⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v := by
      rw [← SetLike.mem_coe, coe_biSup_pos_localAbsoluteUpperRamificationGroup]
      exact Set.mem_iUnion₂.2 ⟨vM, hvM, hτ⟩
    have hτP' : τ ∈ P' := Subgroup.le_topologicalClosure _ hτ_sup
    let τ₀ : Gal(AlgebraicClosure K/K) := τ
    let σ₀ : Gal(AlgebraicClosure K/K) := σ
    have hτσ' : AlgEquiv.restrictNormalHom M τ₀ = AlgEquiv.restrictNormalHom M σ₀ := hτσ
    refine ⟨τ, hτP', QuotientGroup.eq.2 (hMU (τ₀⁻¹ * σ₀) ?_)⟩
    rw [← M.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hτσ', inv_mul_cancel]

/-- Set-level form of `topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup`: the
topological closure of `⋃_{v > 0} G_K^v` is the wild inertia subgroup. -/
theorem closure_biUnion_pos_localAbsoluteUpperRamificationGroup :
    closure (⋃ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K))) =
      (wildInertiaSubgroup K : Set (Field.absoluteGaloisGroup K)) := by
  rw [← coe_biSup_pos_localAbsoluteUpperRamificationGroup, ← Subgroup.topologicalClosure_coe,
    topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup]

/-- **The intersection of the absolute upper ramification groups at natural indices is trivial.** -/
@[simp]
theorem iInf_natCast_localAbsoluteUpperRamificationGroup :
    (⨅ n : ℕ, localAbsoluteUpperRamificationGroup K
      ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply (absoluteGaloisGroupRestrictEquiv K).injective
  rw [map_one]
  ext x
  -- Build the finite Galois splitting field of `minpoly K x` inside `AlgebraicClosure K`,
  -- avoiding any separability assumption on `AlgebraicClosure K / K`.
  have hxsep : IsSeparable K (x : AlgebraicClosure K) := mem_separableClosure_iff.1 x.2
  let f : K[X] := minpoly K (x : AlgebraicClosure K)
  let L : IntermediateField K (AlgebraicClosure K) := adjoin K (f.rootSet (AlgebraicClosure K))
  have hsplit : (f.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField K L f := adjoin_rootSet_isSplittingField hsplit
  have : IsGalois K L := IsGalois.of_separable_splitting_field hxsep
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
  obtain ⟨N, hN⟩ := exists_forall_upperRamificationGroup_natCast_eq_bot K L
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  have hσN : AlgEquiv.restrictNormal σ₀ L ∈
      upperRamificationGroup K L ⟨N, Nat.cast_mem_ramificationIndexDomain N⟩ :=
    restrictNormal_mem_upperRamificationGroup L (Subgroup.mem_iInf.1 hσ N)
  rw [hN N le_rfl, Subgroup.mem_bot] at hσN
  have hxL : (x : AlgebraicClosure K) ∈ L :=
    subset_adjoin K _ ((Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hxsep.isIntegral)).2
      (minpoly.aeval K _))
  have hfix : σ₀ (x : AlgebraicClosure K) = x :=
    (AlgEquiv.restrictNormal_commutes σ₀ L ⟨x, hxL⟩).symm.trans
      (by rw [hσN, AlgEquiv.one_apply]; rfl)
  exact (coe_absoluteGaloisGroupRestrictEquiv_apply K σ₀ x).trans hfix

/-- **The intersection of all absolute upper ramification groups is trivial.** -/
@[simp]
theorem iInf_localAbsoluteUpperRamificationGroup :
    ⨅ v : RamificationIndexDomain, localAbsoluteUpperRamificationGroup K v = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [← iInf_natCast_localAbsoluteUpperRamificationGroup K, Subgroup.mem_iInf]
  intro n
  exact Subgroup.mem_iInf.1 hσ ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩

end SpecialValues

/-! ### Restriction to infinite Galois intermediate extensions -/

section GaloisIntermediate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem restrictNormal_restrictNormal_mem_finiteGaloisUpperRamificationGroup
    (E : IntermediateField K (AlgebraicClosure K)) [IsGalois K E]
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    (hσ : σ ∈ localAbsoluteUpperRamificationGroup K v)
    (M : FiniteGaloisIntermediateField K E) :
    AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ E) M ∈
      finiteGaloisUpperRamificationGroup K E M v := by
  let _ := finiteIntermediateFieldValuativeRel K E M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K E M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K E M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K E M.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  let L : IntermediateField K (AlgebraicClosure K) := lift M.toIntermediateField
  let eML : M.toIntermediateField ≃ₐ[K] L := liftAlgEquiv M.toIntermediateField
  have : Module.Finite K L := Module.Finite.of_surjective eML.toLinearMap eML.surjective
  have : IsGalois K L := eML.transfer_galois.1 inferInstance
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
  have hσL := restrictNormal_mem_upperRamificationGroup L hσ
  rw [← comap_algAutCongr_upperRamificationGroup (RingEquiv.refl K) continuous_id
    eML.toRingEquiv (fun c ↦ eML.commutes c) v, Subgroup.mem_comap]
  convert hσL using 1
  refine AlgEquiv.ext fun ⟨y, hy⟩ ↦ Subtype.ext ?_
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  have happly :
      (((RingEquiv.refl K).algAutCongr eML.toRingEquiv (fun c ↦ eML.commutes c)
          ((AlgEquiv.restrictNormal σ₀ E).restrictNormal M.toIntermediateField) ⟨y, hy⟩ : L) :
        AlgebraicClosure K) =
      (eML (((AlgEquiv.restrictNormal σ₀ E).restrictNormal M.toIntermediateField)
        (eML.symm ⟨y, hy⟩)) : AlgebraicClosure K) :=
    congrArg Subtype.val (RingEquiv.algAutCongr_apply (RingEquiv.refl K) eML.toRingEquiv
      (fun c ↦ eML.commutes c)
      ((AlgEquiv.restrictNormal σ₀ E).restrictNormal M.toIntermediateField) ⟨y, hy⟩)
  refine happly.trans ?_
  obtain ⟨z, hz⟩ : ∃ z : M.toIntermediateField, eML z = ⟨y, hy⟩ := eML.surjective ⟨y, hy⟩
  rw [← hz, eML.symm_apply_apply]
  have h1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormal σ₀ E)
    M.toIntermediateField z
  have h2 := AlgEquiv.restrictNormal_commutes σ₀ E (z : E)
  have h3 := AlgEquiv.restrictNormal_commutes σ₀ L (eML z)
  exact (congrArg (fun w : E ↦ (w : AlgebraicClosure K)) h1).trans (h2.trans h3.symm)

private theorem exists_restrictNormal_eq_and_mem_finiteGaloisUpperRamificationGroup
    (E : IntermediateField K (AlgebraicClosure K)) [IsGalois K E]
    {v : RamificationIndexDomain} {τ : E ≃ₐ[K] E}
    (hτ : τ ∈ ⨅ M : FiniteGaloisIntermediateField K E,
      (finiteGaloisUpperRamificationGroup K E M v).comap (AlgEquiv.restrictNormalHom M))
    (N : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ∃ σ : Field.absoluteGaloisGroup K,
      AlgEquiv.restrictNormalHom E σ = τ ∧
        AlgEquiv.restrictNormalHom N.toIntermediateField σ ∈
          finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) N v := by
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) N.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) N.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    N.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) N.toIntermediateField
  let M₀ : IntermediateField K (AlgebraicClosure K) := E ⊓ N.toIntermediateField
  have : Module.Finite K M₀ :=
    Module.Finite.of_injective
      (inclusion (inf_le_right : M₀ ≤ N.toIntermediateField)).toLinearMap
      (inclusion (inf_le_right : M₀ ≤ N.toIntermediateField)).injective
  have : Algebra.IsSeparable K M₀ :=
    Algebra.IsSeparable.of_algHom K N.toIntermediateField (inclusion inf_le_right)
  have : Normal K M₀ := inferInstance
  have : IsGalois K M₀ := ⟨⟩
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M₀
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M₀
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M₀
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M₀
  let M' : IntermediateField K E := restrict (inf_le_left : M₀ ≤ E)
  let eM : M' ≃ₐ[K] M₀ :=
    { toFun := fun w ↦ ⟨(w : E).1, (mem_restrict _ _).1 w.2⟩
      invFun := fun x ↦ ⟨⟨x.1, (mem_inf.1 x.2).1⟩, (mem_restrict _ _).2 x.2⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  have : Module.Finite K M' := Module.Finite.of_surjective eM.symm.toLinearMap eM.symm.surjective
  have : IsGalois K M' := eM.symm.transfer_galois.1 inferInstance
  let MF : FiniteGaloisIntermediateField K E := ⟨M'⟩
  let _ := finiteIntermediateFieldValuativeRel K E MF.toIntermediateField
  let _ := finiteIntermediateFieldTopology K E MF.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K E MF.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K E MF.toIntermediateField
  have hτMF : AlgEquiv.restrictNormal τ MF ∈ upperRamificationGroup K MF v := by
    have hmem : AlgEquiv.restrictNormal τ MF ∈ finiteGaloisUpperRamificationGroup K E MF v :=
      Subgroup.mem_iInf.1 hτ MF
    rwa [finiteGaloisUpperRamificationGroup_def] at hmem
  have hσ₀M₀ : AlgEquiv.restrictNormal σ₀ M₀ ∈ upperRamificationGroup K M₀ v := by
    rw [← map_algAutCongr_upperRamificationGroup (RingEquiv.refl K) continuous_id
      eM.toRingEquiv (fun c ↦ eM.commutes c) v]
    refine ⟨AlgEquiv.restrictNormal τ MF, hτMF, ?_⟩
    refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
    have happly :
        (((RingEquiv.refl K).algAutCongr eM.toRingEquiv (fun c ↦ eM.commutes c)
            (AlgEquiv.restrictNormal τ MF.toIntermediateField) x : M₀) : AlgebraicClosure K) =
          (eM (AlgEquiv.restrictNormal τ M' (eM.symm x)) : AlgebraicClosure K) :=
      congrArg Subtype.val (RingEquiv.algAutCongr_apply (RingEquiv.refl K) eM.toRingEquiv
        (fun c ↦ eM.commutes c) (AlgEquiv.restrictNormal τ MF.toIntermediateField) x)
    refine happly.trans ?_
    have h1 := AlgEquiv.restrictNormal_commutes τ M' (eM.symm x)
    have h2 : (τ (eM.symm x : E) : AlgebraicClosure K) = σ₀ (x : AlgebraicClosure K) := by
      rw [← hσ₀]
      exact AlgEquiv.restrictNormal_commutes σ₀ E (eM.symm x : E)
    have h3 := AlgEquiv.restrictNormal_commutes σ₀ M₀ x
    exact (congrArg (fun w : E ↦ (w : AlgebraicClosure K)) h1).trans (h2.trans h3.symm)
  obtain ⟨σ₁, hσ₁N, hσ₁M₀⟩ :=
    (restrictNormal_tower_upperRamificationGroup M₀ N.toIntermediateField inf_le_right v).2
      (AlgEquiv.restrictNormal σ₀ M₀) hσ₀M₀
  set ρ := AlgEquiv.restrictNormal σ₁ N.toIntermediateField
  -- `(σ₀|_N)⁻¹ * ρ` fixes `M₀ = E ⊓ N`, so it comes from an automorphism `g` fixing `E`.
  let φ : E.fixingSubgroup →* (N ≃ₐ[K] N) :=
    (AlgEquiv.restrictNormalHom N.toIntermediateField).comp E.fixingSubgroup.subtype
  have hrange : (restrict (inf_le_right : M₀ ≤ N.toIntermediateField)).fixingSubgroup ≤
      φ.range := by
    rw [← IntermediateField.fixingSubgroup_fixedField φ.range]
    refine fixingSubgroup_antitone fun y hy ↦ (mem_restrict _ _).2 (mem_inf.2 ⟨?_, y.2⟩)
    have hyE : (y : AlgebraicClosure K) ∈
        fixedField E.fixingSubgroup ⊓ separableClosure K (AlgebraicClosure K) := by
      refine mem_inf.2 ⟨(mem_fixedField_iff _ _).2 fun g hg ↦ ?_,
        le_separableClosure K _ N.toIntermediateField y.2⟩
      have hgy := (mem_fixedField_iff _ _).1 hy (φ ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
      exact (AlgEquiv.restrictNormal_commutes g N.toIntermediateField y).symm.trans
        (congrArg Subtype.val hgy)
    rwa [fixedField_fixingSubgroup_inf_separableClosure (le_separableClosure K _ E)] at hyE
  have hδ : (AlgEquiv.restrictNormal σ₀ N.toIntermediateField)⁻¹ * ρ ∈
      (restrict (inf_le_right : M₀ ≤ N.toIntermediateField)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z : M₀, (z : AlgebraicClosure K) = (y : AlgebraicClosure K) :=
      ⟨⟨y.1, (mem_restrict _ _).1 hy⟩, rfl⟩
    apply Subtype.ext
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
    have hρy : (ρ y : AlgebraicClosure K) = (AlgEquiv.restrictNormal σ₀ M₀ z : _) := by
      calc (ρ y : AlgebraicClosure K)
        _ = σ₁ (y : AlgebraicClosure K) :=
            AlgEquiv.restrictNormal_commutes σ₁ N.toIntermediateField y
        _ = σ₁ (z : AlgebraicClosure K) := congrArg σ₁ hz.symm
        _ = (AlgEquiv.restrictNormal σ₁ M₀ z : AlgebraicClosure K) :=
            (AlgEquiv.restrictNormal_commutes σ₁ M₀ z).symm
        _ = (AlgEquiv.restrictNormal σ₀ M₀ z : AlgebraicClosure K) :=
            congrArg Subtype.val (AlgEquiv.congr_fun hσ₁M₀ z)
    have hσ₀y : (AlgEquiv.restrictNormal σ₀ N.toIntermediateField y : AlgebraicClosure K) =
        (AlgEquiv.restrictNormal σ₀ M₀ z : _) := by
      calc (AlgEquiv.restrictNormal σ₀ N.toIntermediateField y : AlgebraicClosure K)
        _ = σ₀ (y : AlgebraicClosure K) :=
            AlgEquiv.restrictNormal_commutes σ₀ N.toIntermediateField y
        _ = σ₀ (z : AlgebraicClosure K) := congrArg σ₀ hz.symm
        _ = (AlgEquiv.restrictNormal σ₀ M₀ z : AlgebraicClosure K) :=
            (AlgEquiv.restrictNormal_commutes σ₀ M₀ z).symm
    have hyeq : ρ y = AlgEquiv.restrictNormal σ₀ N.toIntermediateField y :=
      Subtype.ext (hρy.trans hσ₀y.symm)
    rw [hyeq, AlgEquiv.symm_apply_apply]
  obtain ⟨⟨g, hgE⟩, hgN⟩ := hrange hδ
  have hE : AlgEquiv.restrictNormalHom E (σ₀ * g) = τ := by
    have hgE1 : AlgEquiv.restrictNormalHom E g = 1 :=
      MonoidHom.mem_ker.1 (E.restrictNormalHom_ker.symm ▸ hgE)
    rw [map_mul, hgE1, mul_one, hσ₀]
  have hN : AlgEquiv.restrictNormalHom N.toIntermediateField (σ₀ * g) ∈
      finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) N v := by
    have hgN' : AlgEquiv.restrictNormalHom N.toIntermediateField g =
        (AlgEquiv.restrictNormal σ₀ N.toIntermediateField)⁻¹ * ρ := hgN
    have hσ₀N : AlgEquiv.restrictNormalHom N.toIntermediateField σ₀ =
        AlgEquiv.restrictNormal σ₀ N.toIntermediateField := rfl
    rw [finiteGaloisUpperRamificationGroup_def, map_mul, hgN', hσ₀N, mul_inv_cancel_left]
    exact hσ₁N
  exact ⟨σ₀ * g, hE, hN⟩

/-- **Quotient upper filtration on any Galois intermediate extension.** Let `E` be a Galois
intermediate field of `AlgebraicClosure K / K` (possibly of infinite degree). Restriction from
`G_K` to `Gal(E/K)` maps `localAbsoluteUpperRamificationGroup K v` onto the intersection of the
preimages of `Gal(M/K)^v` as `M` ranges over the finite Galois intermediate fields of `E/K`. -/
theorem map_restrictNormalHom_localAbsoluteUpperRamificationGroup_of_isGalois
    (E : IntermediateField K (AlgebraicClosure K)) [IsGalois K E]
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).map (AlgEquiv.restrictNormalHom E) =
      ⨅ M : FiniteGaloisIntermediateField K E,
        (finiteGaloisUpperRamificationGroup K E M v).comap (AlgEquiv.restrictNormalHom M) := by
  refine le_antisymm ?_ fun τ hτ ↦ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact Subgroup.mem_iInf.2
      (restrictNormal_restrictNormal_mem_finiteGaloisUpperRamificationGroup E hσ)
  · let S : FiniteGaloisIntermediateField K (AlgebraicClosure K) →
        Set (Field.absoluteGaloisGroup K) := fun N ↦
      (AlgEquiv.restrictNormalHom E) ⁻¹' {τ} ∩
        (AlgEquiv.restrictNormalHom N.toIntermediateField) ⁻¹'
          (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) N v : Set (N ≃ₐ[K] N))
    have hcl (N : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : IsClosed (S N) := by
      have : T2Space (E ≃ₐ[K] E) := krullTopology_t2
      have : T2Space (N ≃ₐ[K] N) := krullTopology_t2
      have : DiscreteTopology (N ≃ₐ[K] N) := Finite.instDiscreteTopology
      exact (isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous E)).inter
        ((isClosed_discrete _).preimage
          (InfiniteGalois.restrictNormalHom_continuous N.toIntermediateField))
    have hne (N : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : (S N).Nonempty := by
      obtain ⟨σ, hσE, hσN⟩ :=
        exists_restrictNormal_eq_and_mem_finiteGaloisUpperRamificationGroup E hτ N
      exact ⟨σ, hσE, hσN⟩
    have hdir : Directed (· ⊇ ·) S := fun N₁ N₂ ↦
      ⟨N₁ ⊔ N₂,
        fun _ ⟨hE, hN⟩ ↦
          ⟨hE, restrictNormal_mono_finiteGaloisUpperRamificationGroup le_sup_left hN⟩,
        fun _ ⟨hE, hN⟩ ↦
          ⟨hE, restrictNormal_mono_finiteGaloisUpperRamificationGroup le_sup_right hN⟩⟩
    obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hne
      (fun N ↦ (hcl N).isCompact) hcl
    exact ⟨σ, mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun N ↦
      (Set.mem_iInter.1 hσ N).2, (Set.mem_iInter.1 hσ ⊥).1⟩

end GaloisIntermediate

/-! ### Naturality in the local field -/

section FieldIso

variable {K K' : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

/-- Forward inclusion along a valuation-preserving isomorphism `e : K ≃+* K'` extended to
`e' : AlgebraicClosure K ≃+* AlgebraicClosure K'`. -/
private theorem mem_localAbsoluteUpperRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    {σ' : Field.absoluteGaloisGroup K'}
    (hσσ' : ∀ y : AlgebraicClosure K,
      e' (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ y) =
        DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' (e' y))
    (hσ : σ ∈ localAbsoluteUpperRamificationGroup K v) :
    σ' ∈ localAbsoluteUpperRamificationGroup K' v := by
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M' ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K' (AlgebraicClosure K') M'.toIntermediateField
  let _ := finiteIntermediateFieldTopology K' (AlgebraicClosure K') M'.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K' (AlgebraicClosure K')
    M'.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K' (AlgebraicClosure K')
    M'.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  -- Pull the subfield `M'` back along `e'` to an intermediate field `M` of
  -- `AlgebraicClosure K / K`.
  let M : IntermediateField K (AlgebraicClosure K) :=
    { M'.toIntermediateField.toSubfield.comap e'.toRingHom with
      algebraMap_mem' := fun c ↦ Subfield.mem_comap.2 <| by
        rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he']
        exact M'.toIntermediateField.algebraMap_mem (e c) }
  let eM : M ≃+* M' :=
    { toFun := fun x ↦ ⟨e' x.1, x.2⟩
      invFun := fun y ↦ ⟨e'.symm y.1, Subfield.mem_comap.2 <| by
        rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, e'.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x ↦ Subtype.ext (e'.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (e'.apply_symm_apply y.1)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e' x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add e' x.1 y.1) }
  have heM (c : K) : eM (algebraMap K M c) = algebraMap K' M' (e c) :=
    Subtype.ext (he' c)
  have hcomp_symm :
      (algebraMap K M).comp e.symm.toRingHom = eM.symm.toRingHom.comp (algebraMap K' M') :=
    RingHom.ext fun c' ↦ by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact (eM.symm_apply_eq.2 (by rw [heM, e.apply_symm_apply])).symm
  have : Module.Finite K M := Module.Finite.of_equiv_equiv e.symm eM.symm hcomp_symm
  have : IsGalois K M := IsGalois.of_equiv_equiv (f := e.symm) (g := eM.symm) hcomp_symm
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
  have hσM := restrictNormal_mem_upperRamificationGroup M hσ
  rw [← comap_algAutCongr_upperRamificationGroup_of_vle_iff e he eM heM v,
    Subgroup.mem_comap] at hσM
  convert hσM using 1
  refine AlgEquiv.ext fun y' ↦ Subtype.ext ?_
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  let σ'₀ : Gal(AlgebraicClosure K'/K') := σ'
  have hy : (eM (AlgEquiv.restrictNormal σ₀ M (eM.symm y')) : AlgebraicClosure K') =
      e' (σ₀ (eM.symm y' : AlgebraicClosure K)) :=
    congrArg e' (AlgEquiv.restrictNormal_commutes σ₀ M (eM.symm y'))
  have hsymm : (eM.symm y' : AlgebraicClosure K) = e'.symm (y' : AlgebraicClosure K') := rfl
  have happly :
      ((e.algAutCongr eM heM (AlgEquiv.restrictNormal σ₀ M) y' : M') : AlgebraicClosure K') =
        (eM (AlgEquiv.restrictNormal σ₀ M (eM.symm y')) : AlgebraicClosure K') :=
    congrArg Subtype.val (RingEquiv.algAutCongr_apply e eM heM (AlgEquiv.restrictNormal σ₀ M) y')
  refine (AlgEquiv.restrictNormal_commutes σ'₀ M'.toIntermediateField y').trans (Eq.trans ?_
    happly.symm)
  rw [IntermediateField.algebraMap_apply, hy, hsymm, hσσ', e'.apply_symm_apply]

/-- **Naturality of membership in `localAbsoluteUpperRamificationGroup` under continuous field
isomorphisms.** Let `e : K ≃+* K'` be a continuous ring isomorphism of nonarchimedean local fields
and `e' : AlgebraicClosure K ≃+* AlgebraicClosure K'` any ring isomorphism extending `e`. If `σ`
and `σ'` are intertwined by `e'`, then `σ ∈ G_K^v ↔ σ' ∈ G_{K'}^v`. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff_of_ringEquiv
    (e : K ≃+* K') (he : Continuous e)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    {σ' : Field.absoluteGaloisGroup K'}
    (hσσ' : ∀ y : AlgebraicClosure K,
      e' (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ y) =
        DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' (e' y)) :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      σ' ∈ localAbsoluteUpperRamificationGroup K' v := by
  have hvle : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b := e.toRingHom.map_vle_map_iff_of_continuous he
  have hvle_symm : ∀ a' b' : K', e.symm a' ≤ᵥ e.symm b' ↔ a' ≤ᵥ b' := fun a' b' ↦ by
    rw [← hvle, e.apply_symm_apply, e.apply_symm_apply]
  have he'_symm (c' : K') :
      e'.symm (algebraMap K' (AlgebraicClosure K') c') =
        algebraMap K (AlgebraicClosure K) (e.symm c') :=
    e'.symm_apply_eq.2 (by rw [he', e.apply_symm_apply])
  have hσσ'_symm (y' : AlgebraicClosure K') :
      e'.symm (DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' y') =
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ (e'.symm y') :=
    e'.symm_apply_eq.2 (by rw [hσσ', e'.apply_symm_apply])
  exact ⟨mem_localAbsoluteUpperRamificationGroup_of_vle_iff e hvle e' he' hσσ',
    mem_localAbsoluteUpperRamificationGroup_of_vle_iff e.symm hvle_symm e'.symm he'_symm hσσ'_symm⟩

/-- **Pullback along `Field.absoluteGaloisGroup.mapOfAlgebra` preserves the absolute upper
filtration** along any continuous field isomorphism `K →+* K'` and compatible embedding of
algebraic closures. -/
theorem comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup
    [Algebra K K'] [Algebra (AlgebraicClosure K) (AlgebraicClosure K')]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure K')]
    (hbij : Function.Bijective (algebraMap K K')) (hcont : Continuous (algebraMap K K'))
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).comap
        (Field.absoluteGaloisGroup.mapOfAlgebra K K') =
      localAbsoluteUpperRamificationGroup K' v := by
  let e : K ≃+* K' := RingEquiv.ofBijective (algebraMap K K') hbij
  have : Algebra.IsIntegral K K' := Algebra.isIntegral_of_surjective hbij.2
  have : Algebra.IsIntegral K (AlgebraicClosure K') := Algebra.IsIntegral.trans K'
  have : Algebra.IsIntegral (AlgebraicClosure K) (AlgebraicClosure K') :=
    Algebra.IsIntegral.tower_top K
  have hφ : Function.Bijective (algebraMap (AlgebraicClosure K) (AlgebraicClosure K')) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e' : AlgebraicClosure K ≃+* AlgebraicClosure K' := RingEquiv.ofBijective _ hφ
  have he' (c : K) :
      e' (algebraMap K (AlgebraicClosure K) c) = algebraMap K' (AlgebraicClosure K') (e c) :=
    (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) (AlgebraicClosure K') c).symm.trans
      (IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K') c)
  ext g'
  rw [Subgroup.mem_comap]
  exact mem_localAbsoluteUpperRamificationGroup_iff_of_ringEquiv e hcont e' he' fun y ↦
    absoluteGaloisGroup_mapOfAlgebra_commutes K K' g' y

/-- **Pullback along `Field.absoluteGaloisGroup.map` preserves the absolute upper filtration.** -/
@[simp]
theorem comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup
    (e : K ≃+* K') (he : Continuous e) (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).comap
        (Field.absoluteGaloisGroup.map (e : K →+* K')) =
      localAbsoluteUpperRamificationGroup K' v := by
  let _ : Algebra K K' := (e : K →+* K').toAlgebra
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure K') :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure K').toAlgebra
  have : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure K') :=
    .of_algebraMap_eq fun c ↦
      ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure K').commutes c).symm
  exact comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup e.bijective he v

/-- **Transport along `TauCeti.absoluteGaloisGroupMapEquiv` maps `G_{K'}^v` onto `G_K^v`.** -/
@[simp]
theorem map_absoluteGaloisGroupMapEquiv_localAbsoluteUpperRamificationGroup
    (e : K ≃+* K') (he : Continuous e) (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K' v).map
        (absoluteGaloisGroupMapEquiv e :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) =
      localAbsoluteUpperRamificationGroup K v := by
  have hhom :
      (absoluteGaloisGroupMapEquiv e :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) =
        (Field.absoluteGaloisGroup.map (e : K →+* K') :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) :=
    MonoidHom.ext (absoluteGaloisGroupMapEquiv_apply e)
  have hsurj : Function.Surjective
      (Field.absoluteGaloisGroup.map (e : K →+* K') :
        Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) := fun g ↦
    ⟨(absoluteGaloisGroupMapEquiv e).symm g,
      (absoluteGaloisGroupMapEquiv_apply e _).symm.trans
        ((absoluteGaloisGroupMapEquiv e).apply_symm_apply g)⟩
  rw [hhom, ← comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup e he v]
  exact Subgroup.map_comap_eq_self_of_surjective hsurj _

end FieldIso

end TauCeti
