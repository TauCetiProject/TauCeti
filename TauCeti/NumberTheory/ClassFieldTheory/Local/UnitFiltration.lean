/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Abelian.Maximal
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.LocalField.Herbrand.AbsoluteFiltration

import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.UpperNumbering
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.RingTheory.Norm.Equiv

/-!
# Reciprocity on the unit filtration and the upper ramification filtration

Let `K` be a nonarchimedean local field in either characteristic. Local reciprocity identifies the
filtration of `Kˣ` by higher unit groups `U(K, n)` (`TauCeti.unitFiltration`) with the filtration
of Galois groups in the upper numbering:

* **Finite level** (`normResidue_map_unitFiltration`): for every finite Galois extension `L/K` of
  nonarchimedean local fields and every `n : ℕ`, the composite
  `Kˣ → Kˣ ⧸ N_{L/K}(Lˣ) ≃* Gal(L/K)^ab` maps `U(K, n)` onto the image of the upper ramification
  group `Gal(L/K)^n` in `Gal(L/K)^ab`. When `L/K` is abelian, pulling back along `Abelianization.of`
  identifies the image of `U(K, n)` directly with `Gal(L/K)^n`
  (`comap_abelianization_of_normResidue_map_unitFiltration`).
* **Maximal abelian extension**
  (`map_topologicalAbelianizationEquivMaximalAbelianExtension_artinMap_unitFiltration`): reading
  the absolute local Artin map `artinMap K : Kˣ →* G_K^ab` in `Gal(K^{ab}/K)` through
  `TauCeti.topologicalAbelianizationEquivMaximalAbelianExtension` maps `U(K, n)` onto the inverse
  limit of `Gal(M/K)^n` over the finite Galois intermediate fields `M` of `K^{ab}/K`.
* **Absolute level** (`map_artinMap_unitFiltration_eq_upper`): the image of `U(K, n)` under
  `artinMap K` is the image of the absolute upper ramification group
  `TauCeti.localAbsoluteUpperRamificationGroup K n` in `G_K^ab` modulo the closed commutator
  subgroup of `G_K`. Neither side requires taking a topological closure, because `U(K, n)` and
  `G_K^n` are compact and their images in the Hausdorff group `G_K^ab` are already closed.

At `n = 0`, `U(K, 0) = 𝒪[K]ˣ` and `G_K^0 = inertiaSubgroup K`, recovering
`map_artinMap_unitFiltration_zero`.

## Main results

* `normResidue_map_unitFiltration`: finite local reciprocity maps `U(K, n)` onto the image of
  `Gal(L/K)^n` in `Gal(L/K)^ab` for any finite Galois extension `L/K`.
* `comap_abelianization_of_normResidue_map_unitFiltration`: when `Gal(L/K)` is commutative,
  pulling back along `Abelianization.of` recovers `Gal(L/K)^n`.
* `normResidue_mk_mem_map_upperRamificationGroup_iff`: the norm residue symbol of `x ∈ Kˣ` lies in
  the image of `Gal(L/K)^n` exactly when `x ∈ U(K, n) ⊔ N_{L/K}(Lˣ)`.
* `abelianization_of_restrictNormalHom_maximalAbelianExtension_artinMap`: on every finite Galois
  intermediate field `M` of `K^{ab}/K`, restricting `artinMap K x` computes `normResidue K M x`.
* `map_topologicalAbelianizationEquivMaximalAbelianExtension_artinMap_unitFiltration`: in
  `Gal(K^{ab}/K)`, the Artin image of `U(K, n)` is the intersection of the preimages of
  `Gal(M/K)^n` over all finite Galois subextensions `M` of `K^{ab}/K`.
* `map_artinMap_unitFiltration_eq_upper`: in `G_K^ab`, the Artin image of `U(K, n)` equals the
  image of `localAbsoluteUpperRamificationGroup K n`.
* `isClosed_map_artinMap_unitFiltration` and
  `isClosed_map_mk'_localAbsoluteUpperRamificationGroup`: both sides of the absolute reciprocity
  identity are closed subgroups of `G_K^ab`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter XV, §2, Theorems 1–2 and Corollary 3.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §6, Theorem 6.2.
-/

public section
noncomputable section

open IntermediateField TauCeti.LocalFieldsRamification

namespace TauCeti.ClassFieldTheory

/-! ### Finite unit-filtration reciprocity -/

section Finite

/-- Universe-polymorphic form of `unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot`,
obtained by embedding `M` into `AlgebraicClosure K : Type`. -/
private theorem unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot'
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsAbelianGalois K M] (v : ℕ) :
    unitFiltration K v ≤ normGroup K M ↔
      upperRamificationGroup K M ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ = ⊥ := by
  let ι : M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let M₀ : IntermediateField K (AlgebraicClosure K) := ι.fieldRange
  let eM : M ≃ₐ[K] M₀ := ι.equivFieldRange
  have : Module.Finite K M₀ := Module.Finite.equiv eM.toLinearEquiv
  have : IsAbelianGalois K M₀ := .of_algHom eM.symm.toAlgHom
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M₀
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M₀
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M₀
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M₀
  have hnorm : normGroup K M = normGroup K M₀ := eM.normGroup_eq
  have hram :
      (upperRamificationGroup K M ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩).map
          ((RingEquiv.refl K).algAutCongr eM.toRingEquiv (fun c ↦ eM.commutes c) :
            Gal(M/K) →* Gal(M₀/K)) =
        upperRamificationGroup K M₀ ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ :=
    map_algAutCongr_upperRamificationGroup (RingEquiv.refl K) continuous_id eM.toRingEquiv
      (fun c ↦ eM.commutes c) ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩
  rw [hnorm, unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot K M₀ v, ← hram,
    Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)]

/-- Every subgroup `N` of `Gal(L/K)^ab` cuts out an abelian Galois subextension `F = L^H` (where
`H = N.comap Abelianization.of`), and `N` contains the norm-residue image of `U(K, n)` precisely
when `N` contains the image of `Gal(L/K)^n`. -/
private theorem map_normResidue_unitFiltration_le_iff
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]
    (n : ℕ) (N : Subgroup (Abelianization Gal(L/K))) :
    (unitFiltration K n).map
        ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L))) ≤ N ↔
      (upperRamificationGroup K L
          ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map Abelianization.of ≤ N := by
  let H : Subgroup Gal(L/K) := N.comap Abelianization.of
  have hcomm_le : commutator Gal(L/K) ≤ H := by
    rw [← Abelianization.ker_of]
    intro σ hσ
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hσ]
    exact one_mem N
  set F : IntermediateField K L := fixedField H
  let _ := finiteIntermediateFieldValuativeRel K L F
  let _ := finiteIntermediateFieldTopology K L F
  have := finiteIntermediateField_isNonarchimedeanLocalField K L F
  have := finiteIntermediateField_valuativeExtension K L F
  have : IsAbelianGalois K F := by
    refine { is_comm := ⟨fun a b ↦ ?_⟩ }
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L a
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L b
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
    exact hcomm_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ))
  -- Identify containment of the unit-filtration image in `N` with `U(K, n) ≤ N_{F/K}(Fˣ)`.
  have hunit :
      (unitFiltration K n).map
          ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L))) ≤ N ↔
        unitFiltration K n ≤ normGroup K F := by
    rw [Subgroup.map_le_iff_le_comap]
    refine forall₂_congr fun u _ ↦ ?_
    let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap K u)
    set σ : Gal(L/K) := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K τ)
    have hnr : normResidue K L (u : Kˣ ⧸ normGroup K L) = Abelianization.of σ := by
      rw [normResidue_mk K L ι, artinMap_restrict K L ι u τ hτ, toMul_ofMul]
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, hnr, ← Subgroup.mem_comap (f := Abelianization.of),
      ← abelianization_of_restrictNormalHom_fixedField_eq_one_iff H σ,
      ← IntermediateField.restrictNormalHom_val, AlgHom.restrictNormalHom_restrictNormalHom,
      ← ofMul_eq_zero, ← artinMap_restrict K F (ι.comp F.val) u τ hτ, localArtinMap_eq_zero_iff]
  rw [hunit, unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot' K F n,
    ← map_restrictNormalHom_upperRamificationGroup K F L, Subgroup.map_eq_bot_iff,
    IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField,
    Subgroup.map_le_iff_le_comap]

/-- **The upper-numbering theorem for finite local reciprocity.** For every finite Galois extension
`L/K` of nonarchimedean local fields and every `n : ℕ`, the reciprocity homomorphism
`Kˣ → Kˣ ⧸ N_{L/K}(Lˣ) ≃* Gal(L/K)^ab` maps the unit group `U(K, n)` onto the image of the upper
ramification group `Gal(L/K)^n` in `Gal(L/K)^ab` (Neukirch, *Algebraic Number Theory*, V Theorem
6.2; Serre, *Local Fields*, XV §2, Theorem 1 and Corollary 3). -/
theorem normResidue_map_unitFiltration
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L] (n : ℕ) :
    (unitFiltration K n).map
        ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L))) =
      (LocalFieldsRamification.upperRamificationGroup K L
          ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map Abelianization.of :=
  le_antisymm
    ((map_normResidue_unitFiltration_le_iff K L n _).2 le_rfl)
    ((map_normResidue_unitFiltration_le_iff K L n _).1 le_rfl)

open scoped IsMulCommutative in
/-- **Abelian form of `normResidue_map_unitFiltration`.** When `Gal(L/K)` is commutative, pulling
back the norm-residue image of `U(K, n)` along the bijection `Abelianization.of` recovers
`Gal(L/K)^n` itself. -/
theorem comap_abelianization_of_normResidue_map_unitFiltration
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (n : ℕ) :
    ((unitFiltration K n).map
        ((normResidue K L).toMonoidHom.comp (QuotientGroup.mk' (normGroup K L)))).comap
        Abelianization.of =
      LocalFieldsRamification.upperRamificationGroup K L
        ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ := by
  rw [normResidue_map_unitFiltration,
    Subgroup.comap_map_eq_self_of_injective Abelianization.of_injective]

/-- **Elementwise criterion for membership in the abelianized upper ramification group.** For a
finite Galois extension `L/K` of nonarchimedean local fields, the norm residue symbol of `x ∈ Kˣ`
lies in the image of `Gal(L/K)^n` in `Gal(L/K)^ab` precisely when `x` lies in
`U(K, n) ⊔ N_{L/K}(Lˣ)`. -/
theorem normResidue_mk_mem_map_upperRamificationGroup_iff
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]
    (n : ℕ) (x : Kˣ) :
    normResidue K L (x : Kˣ ⧸ normGroup K L) ∈
        (LocalFieldsRamification.upperRamificationGroup K L
            ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map Abelianization.of ↔
      x ∈ unitFiltration K n ⊔ normGroup K L := by
  rw [← normResidue_map_unitFiltration K L n, ← Subgroup.map_map, Subgroup.mem_map_equiv,
    MulEquiv.symm_apply_apply, ← QuotientGroup.mk'_apply, ← Subgroup.mem_comap,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk']

end Finite

/-! ### Absolute unit-filtration reciprocity -/

section Absolute

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Finite restrictions of `artinMap K` on `K^{ab}/K`.** Let `M` be a finite Galois intermediate
field of `maximalAbelianExtension K (AlgebraicClosure K) / K`. Reading `artinMap K x` as an
automorphism of `K^{ab}` via `topologicalAbelianizationEquivMaximalAbelianExtension` and
restricting to `M` computes `normResidue K M x`. -/
theorem abelianization_of_restrictNormalHom_maximalAbelianExtension_artinMap
    (M : FiniteGaloisIntermediateField K (maximalAbelianExtension K (AlgebraicClosure K)))
    (x : Kˣ) :
    Abelianization.of
        (AlgEquiv.restrictNormalHom M.toIntermediateField
          (topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
            (artinMap K x))) =
      normResidue K M.toIntermediateField (x : Kˣ ⧸ normGroup K M.toIntermediateField) := by
  let ιSep : maximalAbelianExtension K (AlgebraicClosure K) →ₐ[K] SeparableClosure K :=
    IntermediateField.inclusion (maximalAbelianExtension_le_separableClosure K (AlgebraicClosure K))
  let ι : M.toIntermediateField →ₐ[K] SeparableClosure K := ιSep.comp M.toIntermediateField.val
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K x)
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  have hmk :
      topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K) (artinMap K x) =
        AlgEquiv.restrictNormalHom (maximalAbelianExtension K (AlgebraicClosure K)) σ₀ := by
    rw [← hσ]
    exact AlgEquiv.topologicalAbelianizationEquivMaximalAbelianExtension_mk σ₀
  have hres :
      AlgEquiv.restrictNormalHom M.toIntermediateField
          (topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
            (artinMap K x)) =
        ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) := by
    rw [hmk]
    refine AlgEquiv.ext fun y ↦ Subtype.ext (Subtype.ext ?_)
    have h₁ :
        (((AlgEquiv.restrictNormalHom M.toIntermediateField
              (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (AlgebraicClosure K)) σ₀) y :
            M.toIntermediateField) : maximalAbelianExtension K (AlgebraicClosure K)) :
          AlgebraicClosure K) =
          σ₀ ((y : maximalAbelianExtension K (AlgebraicClosure K)) : AlgebraicClosure K) :=
      (congrArg Subtype.val
        (AlgEquiv.restrictNormal_commutes
          (AlgEquiv.restrictNormal σ₀ (maximalAbelianExtension K (AlgebraicClosure K)))
          M.toIntermediateField y)).trans
        (AlgEquiv.restrictNormal_commutes σ₀
          (maximalAbelianExtension K (AlgebraicClosure K))
          (y : maximalAbelianExtension K (AlgebraicClosure K)))
    have h₂ :
        (((ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) y :
            M.toIntermediateField) : maximalAbelianExtension K (AlgebraicClosure K)) :
          AlgebraicClosure K) =
          σ₀ ((y : maximalAbelianExtension K (AlgebraicClosure K)) : AlgebraicClosure K) := by
      have hcomm := congrArg (fun z : SeparableClosure K ↦ (z : AlgebraicClosure K))
        (ι.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv K σ) y)
      exact hcomm.trans (coe_absoluteGaloisGroupRestrictEquiv_apply K σ (ι y))
    exact h₁.trans h₂.symm
  rw [hres, normResidue_mk K M.toIntermediateField ι x,
    artinMap_restrict K M.toIntermediateField ι x σ hσ, toMul_ofMul]

private theorem exists_mem_unitFiltration_restrictNormalHom_eq (n : ℕ)
    (M : FiniteGaloisIntermediateField K (maximalAbelianExtension K (AlgebraicClosure K)))
    {τ : Gal(maximalAbelianExtension K (AlgebraicClosure K)/K)}
    (hτM : AlgEquiv.restrictNormalHom M.toIntermediateField τ ∈
      finiteGaloisUpperRamificationGroup K (maximalAbelianExtension K (AlgebraicClosure K)) M
        ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩) :
    ∃ u ∈ unitFiltration K n,
      AlgEquiv.restrictNormalHom M.toIntermediateField
          (topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
            (artinMap K u)) =
        AlgEquiv.restrictNormalHom M.toIntermediateField τ := by
  let Kab := maximalAbelianExtension K (AlgebraicClosure K)
  let _ := finiteIntermediateFieldValuativeRel K Kab M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Kab M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Kab M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Kab M.toIntermediateField
  have : IsAbelianGalois K M.toIntermediateField := .tower_bot K M.toIntermediateField Kab
  have hmem :
      Abelianization.of (AlgEquiv.restrictNormalHom M.toIntermediateField τ) ∈
        (upperRamificationGroup K M.toIntermediateField
            ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map Abelianization.of :=
    ⟨AlgEquiv.restrictNormalHom M.toIntermediateField τ,
      by rwa [finiteGaloisUpperRamificationGroup_def] at hτM, rfl⟩
  rw [← normResidue_map_unitFiltration K M.toIntermediateField n] at hmem
  obtain ⟨u, hu, hu_eq⟩ := hmem
  exact ⟨u, hu, Abelianization.of_injective
    ((abelianization_of_restrictNormalHom_maximalAbelianExtension_artinMap K M u).trans hu_eq)⟩

/-- **Unit-filtration reciprocity on the maximal abelian extension.** Reading `artinMap K` in
`Gal(K^{ab}/K)` via `topologicalAbelianizationEquivMaximalAbelianExtension` maps `U(K, n)` onto the
intersection of the preimages of `Gal(M/K)^n` over all finite Galois intermediate fields `M` of
`K^{ab}/K`. -/
theorem map_topologicalAbelianizationEquivMaximalAbelianExtension_artinMap_unitFiltration
    (n : ℕ) :
    ((unitFiltration K n).map (artinMap K)).map
        (topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)).toMonoidHom =
      ⨅ M : FiniteGaloisIntermediateField K (maximalAbelianExtension K (AlgebraicClosure K)),
        (finiteGaloisUpperRamificationGroup K (maximalAbelianExtension K (AlgebraicClosure K)) M
            ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).comap
          (AlgEquiv.restrictNormalHom M.toIntermediateField) := by
  set Kab := maximalAbelianExtension K (AlgebraicClosure K)
  let e := topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
  let φ : Kˣ →* Gal(Kab/K) := e.toMonoidHom.comp (artinMap K)
  have hφ_cont : Continuous φ := (map_continuous e).comp (continuous_artinMap K)
  refine (Subgroup.map_map (unitFiltration K n) e.toMonoidHom (artinMap K)).trans ?_
  refine le_antisymm ?_ fun τ hτ ↦ ?_
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_iInf.2 fun M ↦ ?_
    let _ := finiteIntermediateFieldValuativeRel K Kab M.toIntermediateField
    let _ := finiteIntermediateFieldTopology K Kab M.toIntermediateField
    have := finiteIntermediateField_isNonarchimedeanLocalField K Kab M.toIntermediateField
    have := finiteIntermediateField_valuativeExtension K Kab M.toIntermediateField
    have : IsAbelianGalois K M.toIntermediateField := .tower_bot K M.toIntermediateField Kab
    rw [Subgroup.mem_comap, finiteGaloisUpperRamificationGroup_def,
      ← Subgroup.mem_map_iff_mem Abelianization.of_injective,
      ← normResidue_map_unitFiltration K M.toIntermediateField n]
    exact ⟨u, hu, (abelianization_of_restrictNormalHom_maximalAbelianExtension_artinMap K M u).symm⟩
  · -- Intersect the closed fibers `{u ∈ U(K, n) | φ(u)|_M = τ|_M}` inside the compact space
    -- `U(K, n)`; finite reciprocity makes every fiber nonempty.
    have : CompactSpace ↥(unitFiltration K n) :=
      isCompact_iff_compactSpace.1 (isCompact_unitFiltration n)
    let T : FiniteGaloisIntermediateField K Kab → Set ↥(unitFiltration K n) := fun M ↦
      (fun u : ↥(unitFiltration K n) ↦
        AlgEquiv.restrictNormalHom M.toIntermediateField (φ u.1)) ⁻¹'
          {AlgEquiv.restrictNormalHom M.toIntermediateField τ}
    have hcl (M : FiniteGaloisIntermediateField K Kab) : IsClosed (T M) := by
      have : DiscreteTopology (M.toIntermediateField ≃ₐ[K] M.toIntermediateField) :=
        Finite.instDiscreteTopology
      exact (isClosed_discrete _).preimage
        ((InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField).comp
          (hφ_cont.comp continuous_subtype_val))
    have hne (M : FiniteGaloisIntermediateField K Kab) : (T M).Nonempty := by
      obtain ⟨u, hu, hu_eq⟩ := exists_mem_unitFiltration_restrictNormalHom_eq K n M
        (Subgroup.mem_iInf.1 hτ M)
      exact ⟨⟨u, hu⟩, hu_eq⟩
    have hres_le {M N : FiniteGaloisIntermediateField K Kab} (hMN : M ≤ N) : T N ⊆ T M := by
      intro u hu
      have hle := (FiniteGaloisIntermediateField.le_iff M N).1 hMN
      refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
      have hsup := congrArg (fun ρ ↦ (ρ ⟨y.1, hle y.2⟩ : Kab)) (Set.mem_singleton_iff.1 hu)
      simpa only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormal_commutes] using hsup
    have hdir : Directed (· ⊇ ·) T := fun M₁ M₂ ↦
      ⟨M₁ ⊔ M₂, hres_le le_sup_left, hres_le le_sup_right⟩
    obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hne
      (fun M ↦ (hcl M).isCompact) hcl
    refine ⟨u.1, u.2, AlgEquiv.ext fun y ↦ ?_⟩
    let M : FiniteGaloisIntermediateField K Kab := FiniteGaloisIntermediateField.adjoin K {y}
    have hy : y ∈ M.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K {y} (Set.mem_singleton y)
    have hM := congrArg (fun ρ ↦ (ρ ⟨y, hy⟩ : Kab))
      (Set.mem_singleton_iff.1 (Set.mem_iInter.1 hu M))
    simpa only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormal_commutes] using hM

/-- **Absolute unit-filtration reciprocity.** For a nonarchimedean local field `K` in either
characteristic and every `n : ℕ`, the image of `U(K, n)` under `artinMap K` equals the image of
`localAbsoluteUpperRamificationGroup K n` in `G_K^ab` modulo the closed commutator subgroup of
`G_K` (Serre, *Local Fields*, XV §2, Theorem 2 and Corollary 3 to Theorem 1). -/
theorem map_artinMap_unitFiltration_eq_upper (n : ℕ) :
    (unitFiltration K n).map (artinMap K) =
      (localAbsoluteUpperRamificationGroup K ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map
        (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure) := by
  let e := topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  have hcomp :
      e.toMonoidHom.comp
        (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure) =
        AlgEquiv.restrictNormalHom (maximalAbelianExtension K (AlgebraicClosure K)) :=
    MonoidHom.ext fun σ ↦ AlgEquiv.topologicalAbelianizationEquivMaximalAbelianExtension_mk σ
  have hrhs :
      ((localAbsoluteUpperRamificationGroup K ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map
          (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)).map
        e.toMonoidHom =
      ⨅ M : FiniteGaloisIntermediateField K (maximalAbelianExtension K (AlgebraicClosure K)),
        (finiteGaloisUpperRamificationGroup K (maximalAbelianExtension K (AlgebraicClosure K)) M
            ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).comap
          (AlgEquiv.restrictNormalHom M.toIntermediateField) :=
    ((Subgroup.map_map
        (localAbsoluteUpperRamificationGroup K ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩)
        e.toMonoidHom
        (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)).trans
      (congrArg (fun f ↦ (localAbsoluteUpperRamificationGroup K
        ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩).map f) hcomp)).trans
      (map_restrictNormalHom_localAbsoluteUpperRamificationGroup_of_isGalois
        (maximalAbelianExtension K (AlgebraicClosure K))
        ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩)
  exact (map_topologicalAbelianizationEquivMaximalAbelianExtension_artinMap_unitFiltration K
    n).trans hrhs.symm

/-- The image of `U(K, n)` under the absolute local Artin map is a closed subgroup of `G_K^ab`,
since `U(K, n)` is compact and `artinMap K` is continuous into the Hausdorff group `G_K^ab`. -/
theorem isClosed_map_artinMap_unitFiltration (n : ℕ) :
    IsClosed
      (((unitFiltration K n).map (artinMap K) :
          Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
        Set (Field.absoluteGaloisGroupAbelianization K)) := by
  let e := topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
  have : T2Space (Field.absoluteGaloisGroupAbelianization K) :=
    @T2Space.of_injective_continuous _ _ _ _ krullTopology_t2 e e.injective e.continuous
  rw [Subgroup.coe_map]
  exact ((isCompact_unitFiltration (K := K) n).image (continuous_artinMap K)).isClosed

/-- The image of `localAbsoluteUpperRamificationGroup K v` in `G_K^ab` is closed, as the continuous
image of a closed subgroup of the compact group `G_K`. -/
theorem isClosed_map_mk'_localAbsoluteUpperRamificationGroup (v : RamificationIndexDomain) :
    IsClosed
      (((localAbsoluteUpperRamificationGroup K v).map
          (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure) :
            Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
        Set (Field.absoluteGaloisGroupAbelianization K)) := by
  let e := topologicalAbelianizationEquivMaximalAbelianExtension K (AlgebraicClosure K)
  have : T2Space (Field.absoluteGaloisGroupAbelianization K) :=
    @T2Space.of_injective_continuous _ _ _ _ krullTopology_t2 e e.injective e.continuous
  rw [Subgroup.coe_map]
  exact ((isClosed_localAbsoluteUpperRamificationGroup K v).isCompact.image
    QuotientGroup.continuous_mk).isClosed

end Absolute

end TauCeti.ClassFieldTheory
