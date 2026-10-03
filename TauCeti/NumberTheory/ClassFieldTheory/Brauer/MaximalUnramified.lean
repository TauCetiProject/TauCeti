/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Unramified
public import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.LinearAlgebra.Submodule.DirectedUnion
import TauCeti.NumberTheory.LocalField.FiniteExtension.Tower

/-!
# The invariant of the unramified Brauer group

Let `K` be a nonarchimedean local field with separable closure `Kˢ`. For every `f ≥ 1`, the
unramified extension `K_f = TauCeti.unramifiedExtension K Kˢ f` of degree `f` carries the local
invariant `TauCeti.ClassFieldTheory.unramifiedInv K K_f : H²(Gal(K_f/K), K_fˣ) → ℚ/ℤ`, normalized
by arithmetic Frobenius, injective with image the subgroup of order `f`. This file glues these
invariants along the inflations `relBrInfl K K_f : H²(Gal(K_f/K), K_fˣ) → Br K` into the
invariant of the **unramified Brauer group**

`Br(Kⁿʳ/K) = ⋃_f relBrInfl K K_f (H²(Gal(K_f/K), K_fˣ)) ≤ Br K`,

the subgroup of the Brauer classes split by an unramified extension.

The images of the layers form a directed family: for `f ∣ g`, `K_f ⊆ K_g`, and inflation
`H²(Gal(K_f/K), K_fˣ) → H²(Gal(K_g/K), K_gˣ)` commutes with the inflations into `Br K`
(`TauCeti.ClassFieldTheory.relBrInfl_map`) and preserves the invariant
(`TauCeti.ClassFieldTheory.unramifiedInv_map`). Since each `relBrInfl` is injective, a class
inflated from two layers has the same invariant in both, which defines the invariant on
`Br(Kⁿʳ/K)`. It is injective because each layer invariant is, and surjective onto `ℚ/ℤ` because
every element of `ℚ/ℤ` has finite order `f`, and the invariant of `K_f` has image the elements of
order dividing `f`.

The invariant of the full Brauer group `Br K` is this invariant once every Brauer class is known
to be split by an unramified extension.

## Main definitions

* `TauCeti.ClassFieldTheory.unramifiedBr K`: the unramified Brauer group `Br(Kⁿʳ/K) ≤ Br K`.
* `TauCeti.ClassFieldTheory.unramifiedBrInv K`: its invariant `Br(Kⁿʳ/K) ≃+ ℚ/ℤ`.

## Main results

* `TauCeti.ClassFieldTheory.mem_unramifiedBr_iff`: a Brauer class is unramified exactly when it
  is inflated from the unramified extension of some degree.
* `TauCeti.ClassFieldTheory.relBrInfl_mem_unramifiedBr`: a class inflated from any unramified
  extension of `K` inside `Kˢ` is unramified.
* `TauCeti.ClassFieldTheory.unramifiedBrInv_relBrInfl`: on such a class, the invariant is the
  invariant `unramifiedInv` of the layer.

## Implementation notes

An unramified extension `E` of `K` inside `Kˢ` carries no preferred topology or valuative
relation, but any two compatible with those of `K` agree
(`TauCeti.finiteExtensionValuativeRel_eq`, `TauCeti.finiteExtensionNormedFieldTopology_eq`), so
`unramifiedInv K E` does not depend on the choice. The statements are made for an arbitrary
compatible structure, and the construction uses that of `TauCeti.finiteExtensionValuativeRel`.

## References

* J.-P. Serre, *Local Fields*, Chapter XII, §1.
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

/-- **The unramified Brauer group** `Br(Kⁿʳ/K)`: the subgroup of `Br K` of the classes inflated
from `H²(Gal(L/K), Lˣ)` for the unramified extensions `L` of `K` of every degree `f ≥ 1` inside
`Kˢ` (`TauCeti.unramifiedExtension`). -/
def unramifiedBr : AddSubgroup (Br K) :=
  ⨆ f : ℕ+, (relBrInfl K (𝓤 f) (𝓤 f).val).range

/-- The unramified invariant of the degree-`f` unramified extension inside `Kˢ`, for its
canonical structure of nonarchimedean local field. -/
private def layerInv (f : ℕ+) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(𝓤 f/K) (𝓤 f)ˣ) 2 →+ AddCircle (1 : ℚ) :=
  letI := finiteExtensionValuativeRel K (𝓤 f)
  letI := finiteExtensionNormedFieldTopology K (𝓤 f)
  haveI := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
  haveI := finiteExtension_valuativeExtension K (𝓤 f)
  haveI : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension f.ne_zero
  unramifiedInv K (𝓤 f)

/-- The unramified invariant of the degree-`f` unramified extension inside `Kˢ` does not depend on
the structure of nonarchimedean local field compatible with `K`. -/
private theorem unramifiedInv_eq_layerInv (f : ℕ+) [ValuativeRel (𝓤 f)]
    [TopologicalSpace (𝓤 f)] [IsNonarchimedeanLocalField (𝓤 f)] [ValuativeExtension K (𝓤 f)]
    [IsUnramified K (𝓤 f)] :
    unramifiedInv K (𝓤 f) = layerInv K f := by
  -- Both the topology and the valuative relation are the canonical ones.
  obtain rfl : ‹TopologicalSpace (𝓤 f)› = finiteExtensionNormedFieldTopology K (𝓤 f) :=
    (finiteExtensionNormedFieldTopology_eq K _).symm
  obtain rfl : ‹ValuativeRel (𝓤 f)› = finiteExtensionValuativeRel K (𝓤 f) :=
    (finiteExtensionValuativeRel_eq K _).symm
  rfl

/-- A class inflated from the degree-`f` unramified extension is inflated from the degree-`g`
one for `f ∣ g`, with the same invariant. -/
private theorem exists_relBrInfl_eq_layerInv_eq (f g : ℕ+) (hfg : (f : ℕ) ∣ g)
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(𝓤 f/K) (𝓤 f)ˣ) 2) :
    ∃ y' : groupCohomology (Rep.ofMulDistribMulAction Gal(𝓤 g/K) (𝓤 g)ˣ) 2,
      relBrInfl K (𝓤 g) (𝓤 g).val y' = relBrInfl K (𝓤 f) (𝓤 f).val y ∧
        layerInv K g y' = layerInv K f y := by
  let _ : Algebra (𝓤 f) (𝓤 g) :=
    (IntermediateField.inclusion (unramifiedExtension_le_of_dvd g.ne_zero hfg)).toAlgebra
  have : IsScalarTower K (𝓤 f) (𝓤 g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨groupCohomology.map (AlgEquiv.restrictNormalHom (𝓤 f))
    (unitsInflationHom K (𝓤 f) (𝓤 g)) 2 y, ?_, ?_⟩
  · have hσ : (𝓤 g).val.comp (IsScalarTower.toAlgHom K (𝓤 f) (𝓤 g)) = (𝓤 f).val :=
      AlgHom.ext fun _ => rfl
    rw [relBrInfl_map, hσ]
  · let _ := finiteExtensionValuativeRel K (𝓤 f)
    let _ := finiteExtensionNormedFieldTopology K (𝓤 f)
    have := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
    have := finiteExtension_valuativeExtension K (𝓤 f)
    have : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension f.ne_zero
    let _ := finiteExtensionValuativeRel K (𝓤 g)
    let _ := finiteExtensionNormedFieldTopology K (𝓤 g)
    have := finiteExtension_isNonarchimedeanLocalField K (𝓤 g)
    have := finiteExtension_valuativeExtension K (𝓤 g)
    have : IsUnramified K (𝓤 g) := isUnramified_unramifiedExtension g.ne_zero
    have : ValuativeExtension (𝓤 f) (𝓤 g) :=
      finiteExtension_valuativeExtension_tower K (𝓤 f) (𝓤 g)
    exact unramifiedInv_map K (𝓤 f) (𝓤 g) y

/-- The classes inflated from the degree-`f` unramified extension are inflated from the degree-`g`
one, for `f ∣ g`. -/
private theorem range_relBrInfl_le (f g : ℕ+) (hfg : (f : ℕ) ∣ g) :
    (relBrInfl K (𝓤 f) (𝓤 f).val).range ≤ (relBrInfl K (𝓤 g) (𝓤 g).val).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨y', hy', -⟩ := exists_relBrInfl_eq_layerInv_eq K f g hfg y
  exact ⟨y', hy'⟩

/-- The classes inflated from the unramified extensions form a directed family. -/
private theorem directed_range_relBrInfl :
    Directed (· ≤ ·) fun f : ℕ+ => (relBrInfl K (𝓤 f) (𝓤 f).val).range :=
  fun f g => ⟨f * g, range_relBrInfl_le K f (f * g) (by simp),
    range_relBrInfl_le K g (f * g) (by simp)⟩

/-- `x ∈ Br K` lies in the unramified Brauer group exactly when it is inflated from the unramified
extension of some degree `f ≥ 1`. -/
@[simp]
theorem mem_unramifiedBr_iff {x : Br K} :
    x ∈ unramifiedBr K ↔ ∃ (f : ℕ+) (y : groupCohomology
      (Rep.ofMulDistribMulAction Gal(𝓤 f/K) (𝓤 f)ˣ) 2), relBrInfl K (𝓤 f) (𝓤 f).val y = x := by
  rw [unramifiedBr, AddSubgroup.mem_iSup_of_directed (directed_range_relBrInfl K)]
  rfl

/-- The invariant of a class of the unramified Brauer group inflated from the degree-`f` layer. -/
private def rangeInv (f : ℕ+) : (relBrInfl K (𝓤 f) (𝓤 f).val).range →+ AddCircle (1 : ℚ) :=
  (layerInv K f).comp (AddMonoidHom.ofInjective (relBrInfl_injective K (𝓤 f) (𝓤 f).val)).symm

/-- The invariant of a class inflated from `y` in the degree-`f` layer is the invariant of `y`. -/
private theorem rangeInv_eq (f : ℕ+) {x : Br K} (hx : x ∈ (relBrInfl K (𝓤 f) (𝓤 f).val).range)
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(𝓤 f/K) (𝓤 f)ˣ) 2)
    (hy : relBrInfl K (𝓤 f) (𝓤 f).val y = x) :
    rangeInv K f ⟨x, hx⟩ = layerInv K f y := by
  exact congrArg (layerInv K f) ((AddEquiv.symm_apply_eq _).2 (Subtype.ext hy.symm))

/-- A class inflated from two unramified layers has the same invariant in both. -/
private theorem rangeInv_compat (f g : ℕ+) (x : Br K)
    (hf : x ∈ (relBrInfl K (𝓤 f) (𝓤 f).val).range)
    (hg : x ∈ (relBrInfl K (𝓤 g) (𝓤 g).val).range) :
    rangeInv K f ⟨x, hf⟩ = rangeInv K g ⟨x, hg⟩ := by
  obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 hf
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hg
  obtain ⟨y', hy', hy'inv⟩ := exists_relBrInfl_eq_layerInv_eq K f (f * g) (by simp) y
  obtain ⟨z', hz', hz'inv⟩ := exists_relBrInfl_eq_layerInv_eq K g (f * g) (by simp) z
  obtain rfl : y' = z' := relBrInfl_injective K _ _ ((hy'.trans hy).trans (hz'.trans hz).symm)
  rw [rangeInv_eq K f _ y hy, rangeInv_eq K g _ z hz, ← hy'inv, ← hz'inv]

/-- Every class of the unramified Brauer group is inflated from some unramified layer. -/
private theorem exists_mem_range_relBrInfl (x : unramifiedBr K) :
    ∃ f : ℕ+, (x : Br K) ∈ (relBrInfl K (𝓤 f) (𝓤 f).val).range :=
  (AddSubgroup.mem_iSup_of_directed (directed_range_relBrInfl K)).1 x.2

/-- The invariant of the unramified Brauer group, glued from the invariants of the layers. -/
private def unramifiedBrInvHom : unramifiedBr K →+ AddCircle (1 : ℚ) :=
  -- `Br K` carries the `ℤ`-module structure of a cohomology group; `toIntSubmodule` and
  -- `toIntLinearMap` use the canonical one of an additive group.
  letI : Module ℤ (Br K) := AddCommGroup.toIntModule _
  (Submodule.iSupLift (fun f : ℕ+ => (relBrInfl K (𝓤 f) (𝓤 f).val).range.toIntSubmodule)
    ((directed_range_relBrInfl K).mono_comp _ fun _ _ h => AddSubgroup.toIntSubmodule.monotone h)
    (fun f => (rangeInv K f).toIntLinearMap)
    (fun f g h => LinearMap.ext fun x => rangeInv_compat K f g x x.2 (h x.2))
    (unramifiedBr K).toIntSubmodule (AddSubgroup.toIntSubmodule.map_iSup _).le).toAddMonoidHom

/-- The invariant of the unramified Brauer group may be read on any layer of a class. -/
private theorem unramifiedBrInvHom_eq (x : unramifiedBr K) (f : ℕ+)
    (hx : (x : Br K) ∈ (relBrInfl K (𝓤 f) (𝓤 f).val).range) :
    unramifiedBrInvHom K x = rangeInv K f ⟨x, hx⟩ :=
  letI : Module ℤ (Br K) := AddCommGroup.toIntModule _
  Submodule.iSupLift_of_mem
    (K := fun f : ℕ+ => (relBrInfl K (𝓤 f) (𝓤 f).val).range.toIntSubmodule)
    (f := fun f => (rangeInv K f).toIntLinearMap) (T := (unramifiedBr K).toIntSubmodule) x hx

/-- The invariant of an unramified layer is injective. -/
private theorem layerInv_injective (f : ℕ+) : Function.Injective (layerInv K f) :=
  let _ := finiteExtensionValuativeRel K (𝓤 f)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 f)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
  have := finiteExtension_valuativeExtension K (𝓤 f)
  have : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension f.ne_zero
  unramifiedInv_injective K (𝓤 f)

/-- The invariant of the degree-`f` layer takes every value of order dividing `f`. -/
private theorem exists_layerInv_eq (f : ℕ+) {q : AddCircle (1 : ℚ)}
    (hq : q ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (f : ℕ)) :
    ∃ y, layerInv K f y = q := by
  let _ := finiteExtensionValuativeRel K (𝓤 f)
  let _ := finiteExtensionNormedFieldTopology K (𝓤 f)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
  have := finiteExtension_valuativeExtension K (𝓤 f)
  have : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension f.ne_zero
  have h := range_unramifiedInv K (𝓤 f)
  rw [finrank_unramifiedExtension f.ne_zero] at h
  exact (Set.ext_iff.1 h q).2 hq

/-- **The invariant of the unramified Brauer group** `inv : Br(Kⁿʳ/K) ≃ ℚ/ℤ`, normalized by
arithmetic Frobenius: on the classes inflated from an unramified extension `L/K` inside `Kˢ` it
is the invariant `TauCeti.ClassFieldTheory.unramifiedInv K L` of the layer
(`unramifiedBrInv_relBrInfl`). -/
def unramifiedBrInv : unramifiedBr K ≃+ AddCircle (1 : ℚ) :=
  AddEquiv.ofBijective (unramifiedBrInvHom K) ⟨(injective_iff_map_eq_zero _).2 fun x hx => by
    obtain ⟨f, hxf⟩ := exists_mem_range_relBrInfl K x
    obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 hxf
    have h0 : layerInv K f y = 0 :=
      (rangeInv_eq K f hxf y hy).symm.trans ((unramifiedBrInvHom_eq K x f hxf).symm.trans hx)
    rw [(injective_iff_map_eq_zero _).1 (layerInv_injective K f) y h0, map_zero] at hy
    exact Subtype.ext hy.symm, fun q => by
    obtain ⟨n, hn, hq⟩ := AddCircle.exists_mem_torsionBy_rat q
    obtain ⟨y, rfl⟩ := exists_layerInv_eq K ⟨n, hn⟩ hq
    have hy := (mem_unramifiedBr_iff K).2 ⟨_, y, rfl⟩
    exact ⟨⟨_, hy⟩, (unramifiedBrInvHom_eq K ⟨_, hy⟩ _ ⟨y, rfl⟩).trans (rangeInv_eq K _ _ y rfl)⟩⟩

variable {K} in
/-- A class inflated from an unramified extension `E` of `K` inside `Kˢ` lies in the unramified
Brauer group. -/
theorem relBrInfl_mem_unramifiedBr (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [Normal K E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [IsUnramified K E]
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2) :
    relBrInfl K E E.val y ∈ unramifiedBr K := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ+, E = 𝓤 f :=
    ⟨⟨_, Module.finrank_pos⟩, E.eq_unramifiedExtension_finrank⟩
  exact (mem_unramifiedBr_iff K).2 ⟨f, y, rfl⟩

variable {K} in
/-- **The normalization of the unramified invariant**: a class inflated from an unramified
extension `E` of `K` inside `Kˢ` has invariant its invariant `unramifiedInv K E` in the layer
`H²(Gal(E/K), Eˣ)`. -/
@[simp]
theorem unramifiedBrInv_relBrInfl (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [IsUnramified K E]
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2) :
    unramifiedBrInv K ⟨relBrInfl K E E.val y, relBrInfl_mem_unramifiedBr E y⟩ =
      unramifiedInv K E y := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ+, E = 𝓤 f :=
    ⟨⟨_, Module.finrank_pos⟩, E.eq_unramifiedExtension_finrank⟩
  rw [unramifiedInv_eq_layerInv K f]
  exact (unramifiedBrInvHom_eq K _ f ⟨y, rfl⟩).trans (rangeInv_eq K f _ y rfl)

end TauCeti.ClassFieldTheory
