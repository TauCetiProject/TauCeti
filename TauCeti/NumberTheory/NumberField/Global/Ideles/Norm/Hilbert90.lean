/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import TauCeti.FieldTheory.Galois.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.RepNorm
import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology

/-!
# Hilbert 90 for ideles in norm-kernel form

For a cyclic extension of number fields, a norm-one idele is a quotient of an idele by its
image under a Galois generator. In a CM field this describes the adelic points of the
relative norm-one torus by `y / conj y`. The same description holds on finite ideles, since
inclusion and projection at the finite part commute with conjugation.

This is the idelic Hilbert 90 used in `New.divStar_surjective` and
`New.exists_snd_div_divStar_finIdeleIncl_eq_one` in
`grh/src/Lib/ClassField/HeckeCharacter/Basic.lean` of [lsernau/grh-lean][short-proof].
Here it is deduced from `subsingleton_groupCohomology_one_idelesRep` and the cyclic cohomology
formula, rather than solving again at each place.

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open CategoryTheory IsDedekindDomain NumberField
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields

open ClassFieldTheory Rep.FiniteCyclicGroup

/-- Idelic Hilbert 90 in a cyclic Galois extension: every norm-one idele is `y / (g • y)`
for the chosen generator `g`. -/
theorem exists_idele_div_smul_eq_of_ideleNormMap_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {g : L ≃ₐ[K] L}
    (hg : Subgroup.zpowers g = ⊤) {x : IdeleGroup (𝓞 L) L}
    (hx : ideleNormMap K L x = 1) : ∃ y : IdeleGroup (𝓞 L) L, y / (g • y) = x := by
  classical
  have hgen (σ : L ≃ₐ[K] L) : σ ∈ Subgroup.zpowers g := hg ▸ Subgroup.mem_top σ
  let : IsCyclic (L ≃ₐ[K] L) := ⟨g, hgen⟩
  let : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  let A := idelesRep K L
  let a : A := Rep.toAdditive.symm (Additive.ofMul x)
  have ha : a ∈ LinearMap.ker A.norm.asHom.hom.toLinearMap := by
    rw [LinearMap.mem_ker]
    apply Rep.toAdditive.injective
    rw [map_zero, Representation.IntertwiningMap.coe_toLinearMap]
    simpa only [A, a, AddEquiv.apply_symm_apply, toMul_ofMul, hx, map_one, ofMul_one] using
      (idelesRep_norm_apply (K := K) (L := L) a)
  obtain ⟨b, hb⟩ := (groupCohomologyπOdd_eq_zero_iff A g hgen 1 odd_one ⟨a, ha⟩).mp
    (Subsingleton.elim _ _)
  have hba : A.ρ g b - b = a := by
    simpa only [Rep.sub_hom, Representation.IntertwiningMap.coe_toLinearMap,
      Representation.IntertwiningMap.coe_sub, Pi.sub_apply, Rep.applyAsHom_apply,
      Rep.hom_id, Representation.IntertwiningMap.id_apply] using hb
  let z : IdeleGroup (𝓞 L) L := (Rep.toAdditive b).toMul
  have he : (g • z) / z = x := by
    exact congrArg (fun b : A ↦ (Rep.toAdditive b).toMul) hba
  exact ⟨z⁻¹, by rw [smul_inv', inv_div_inv, he]⟩

/-- In a quadratic extension, the relative idele norm is one exactly when the product of the
idele and its conjugate is one. -/
theorem ideleNormMap_eq_one_iff_mul_smul_eq_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    {g : L ≃ₐ[K] L} (hg : g ≠ 1) (x : IdeleGroup (𝓞 L) L) :
    ideleNormMap K L x = 1 ↔ x * (g • x) = 1 := by
  classical
  have hN := ideleExtension_ideleNormMap K L x
  rw [Algebra.IsQuadraticExtension.univ_eq_pair K L hg, Finset.prod_pair (Ne.symm hg)] at hN
  simp only [← idele_smul_def, one_smul] at hN
  rw [← hN, ← map_one (ideleExtension K L), (ideleExtension_injective K L).eq_iff]

open Algebra.IsQuadraticExtension

/-- For a quadratic extension, the adelic norm-one torus is the image of `y ↦ y / (g • y)`
on ideles, where `g` is the nonidentity automorphism. -/
theorem exists_idele_div_smul_eq_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L] {g : L ≃ₐ[K] L}
    (hg : g ≠ 1) (x : IdeleGroup (𝓞 L) L) :
    (∃ y : IdeleGroup (𝓞 L) L, y / (g • y) = x) ↔ x * (g • x) = 1 := by
  refine ⟨?_, fun hx ↦ exists_idele_div_smul_eq_of_ideleNormMap_eq_one ?_
    ((ideleNormMap_eq_one_iff_mul_smul_eq_one hg x).mpr hx)⟩
  · rintro ⟨y, rfl⟩
    rw [smul_div', smul_smul, algEquiv_mul_self, one_smul, div_mul_div_comm,
      mul_comm (g • y) y, div_self']
  · refine top_unique fun σ _ ↦ ?_
    rcases algEquiv_eq_one_or_eq K L hg σ with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/-- For a quadratic extension, the finite adelic norm-one torus is the image of `y ↦ y / conj y`
on finite ideles. The conjugate is taken via the Galois action on the finite adele ring. -/
theorem exists_finiteIdele_div_smul_eq_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L] {g : L ≃ₐ[K] L}
    (hg : g ≠ 1) (x : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    let conj := Units.map (finiteAdeleGaloisAction K L g : _ →* _)
    (∃ y, y / conj y = x) ↔ x * conj x = 1 := by
  intro conj
  let i := IdeleGroup.ofFiniteIdele (𝓞 L) L
  let π := IdeleGroup.toFiniteIdele (𝓞 L) L
  have hi (y) : i (conj y) = g • i y := ofFiniteIdele_map_finiteAdeleGaloisAction g y
  constructor
  · rintro ⟨y, rfl⟩
    have h := (exists_idele_div_smul_eq_iff hg (i y / (g • i y))).mp ⟨i y, rfl⟩
    rw [← hi, ← map_div, ← hi, ← map_mul] at h
    simpa only [π, i, IdeleGroup.toFiniteIdele_ofFiniteIdele, map_one] using congrArg π h
  · intro hx
    have h : i x * (g • i x) = 1 := by rw [← hi, ← map_mul, hx, map_one]
    obtain ⟨y, hy⟩ := (exists_idele_div_smul_eq_iff hg _).mpr h
    refine ⟨π y, ?_⟩
    simpa only [π, i, map_div, toFiniteIdele_smul, IdeleGroup.toFiniteIdele_ofFiniteIdele] using
      congrArg π hy

end TauCeti.GlobalNumberFields
