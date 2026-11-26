/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Connecting maps and boundary preimages in short exact sequences of complexes of modules

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of homological complexes of modules,
and let `c.Rel i j`. When `S.X₃` is not exact in degree `i`, the image of the boundary map from
`LinearMap.range (S.X₁.d i j).hom` into `LinearMap.range (S.X₂.d i j).hom` can be smaller than the
kernel of the boundary map onto `LinearMap.range (S.X₃.d i j).hom`, with the discrepancy measured by
`LinearMap.range (hS.δ i j hij).hom`: an element of `S.X₁.X j` whose image in `S.X₂.X j` is a
boundary is a cycle of `S.X₁`, and its homology class is the image under the connecting map
`hS.δ i j hij` of a homology class in `S.X₃.homology i`. Consequently the preimage
`(LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom` sits in two short exact sequences of
`R`-modules:

* `0 → range (S.X₁.d i j) → comap (S.f.f j) (range (S.X₂.d i j)) → range (hS.δ i j hij) → 0`
  (`CategoryTheory.ShortComplex.ShortExact.exact_inclusion_comapRangeHomologyClass`,
  `CategoryTheory.ShortComplex.ShortExact.comapRangeHomologyClass_surjective`);
* `0 → comap (S.f.f j) (range (S.X₂.d i j)) → range (S.X₂.d i j) → range (S.X₃.d i j) → 0`
  (`HomologicalComplex.Hom.exact_comapBoundaryMap_boundaryMap`,
  `HomologicalComplex.Hom.boundaryMap_surjective`).

These two short exact sequences decompose the boundaries of `S.X₂` in Milnor's multiplicativity
formula for Reidemeister torsion with homology bases. From the long exact homology sequence,
surjectivity of `Hᵢ(S.g)`, vanishing of `hS.δ i j hij`, and injectivity of `Hⱼ(S.f)` are all
equivalent (`CategoryTheory.ShortComplex.ShortExact.homologyMap_g_surjective_iff_δ_eq_zero`,
`CategoryTheory.ShortComplex.ShortExact.homologyMap_f_injective_iff_δ_eq_zero`,
`CategoryTheory.ShortComplex.ShortExact.homologyMap_f_injective_iff_homologyMap_g_surjective`).

For maps `φ : X ⟶ Y` and `ψ : Y ⟶ Z` of complexes of modules with `ψ` a monomorphism, the short
exact sequence `cokernel φ ⟶ cokernel (φ ≫ ψ) ⟶ cokernel ψ`
(`TauCeti.cokernelCompSequence_shortExact`) also has a connecting map on
homology, computed on classes of elements in `TauCeti.exists_δ_cokernelCompSequence_eq`.

## Main declarations

* `CategoryTheory.ShortComplex.ShortExact.comapRangeHomologyClass`,
  `CategoryTheory.ShortComplex.ShortExact.exact_inclusion_comapRangeHomologyClass`,
  `CategoryTheory.ShortComplex.ShortExact.comapRangeHomologyClass_surjective`: the homology class
  map from the preimage of the boundaries of `S.X₂` onto the image of the connecting map, with
  kernel the boundaries of `S.X₁`.
* `CategoryTheory.ShortComplex.ShortExact.homologyMap_g_surjective_iff_δ_eq_zero`,
  `CategoryTheory.ShortComplex.ShortExact.homologyMap_f_injective_iff_δ_eq_zero`,
  `CategoryTheory.ShortComplex.ShortExact.homologyMap_f_injective_iff_homologyMap_g_surjective`:
  equivalences between surjectivity of `Hᵢ(S.g)`, vanishing of `hS.δ i j hij`, and injectivity of
  `Hⱼ(S.f)`.
* `TauCeti.exists_δ_cokernelCompSequence_eq`: the connecting map of
  `cokernel φ ⟶ cokernel (φ ≫ ψ) ⟶ cokernel ψ` on classes of elements.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat R) c)} (hS : S.ShortExact)

include hS in
/-- Every element of `S.X₁.X j` whose image in `S.X₂.X j` lies in the image of `S.X₂.d i j` is
killed by every outgoing differential of `S.X₁`. -/
theorem d_apply_eq_zero_of_mem_comap_range_d {i j : ι}
    (z : (LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom) (k : ι) :
    S.X₁.d j k ((Submodule.subtype _) z) = 0 := by
  obtain ⟨x₂, hx₂⟩ := z.property
  exact hS.d_eq_zero_of_f_eq_d_apply i j x₂ z.val hx₂.symm k

include hS in
/-- The homology class in `S.X₁.homology j` of an element of `S.X₁.X j` whose image in `S.X₂.X j`
is a boundary from degree `i` lies in the image of the connecting map `hS.δ i j hij`. -/
theorem moduleCatHomologyClass_mem_range_δ {i j : ι} (hij : c.Rel i j)
    (z : (LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom) :
    S.X₁.moduleCatHomologyClass rfl (Submodule.subtype _)
        (fun w ↦ hS.d_apply_eq_zero_of_mem_comap_range_d w (c.next j)) z ∈
      LinearMap.range (hS.δ i j hij).hom := by
  obtain ⟨x₂, hx₂⟩ := z.property
  have hd₃ : (S.X₃.d i j).hom ((S.g.f i).hom x₂) = 0 := by
    have hcomm : (S.X₃.d i j).hom ((S.g.f i).hom x₂) = (S.g.f j).hom ((S.X₂.d i j).hom x₂) :=
      HomologicalComplex.Hom.comm_apply S.g i j x₂
    rw [hcomm, hx₂, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, S.zero]
    simp
  let z₃ := S.X₃.moduleCatCyclesMk ((S.g.f i).hom x₂) j (c.next_eq' hij) hd₃
  refine ⟨(S.X₃.homologyπ i).hom z₃, ?_⟩
  rw [HomologicalComplex.moduleCatHomologyClass_apply]
  exact hS.moduleCat_δ_homologyπ i j hij z₃ x₂
    (S.X₃.iCycles_moduleCatCyclesMk i _ j (c.next_eq' hij) hd₃).symm _
    ((congrArg (S.f.f j).hom (S.X₁.iCycles_moduleCatCyclesMk j _ _ rfl _)).trans hx₂.symm)

/-- The linear map sending an element of `S.X₁.X j` whose image in `S.X₂.X j` is a boundary from
degree `i` to its homology class in `LinearMap.range (hS.δ i j hij).hom`. -/
noncomputable def comapRangeHomologyClass {i j : ι} (hij : c.Rel i j) :
    (LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom →ₗ[R]
      LinearMap.range (hS.δ i j hij).hom :=
  (S.X₁.moduleCatHomologyClass rfl (Submodule.subtype _)
    fun w ↦ hS.d_apply_eq_zero_of_mem_comap_range_d w (c.next j)).codRestrict
    (LinearMap.range (hS.δ i j hij).hom) (hS.moduleCatHomologyClass_mem_range_δ hij)

/-- The underlying homology class of `hS.comapRangeHomologyClass hij z` is the class of `z` as a
cycle of `S.X₁`. -/
theorem coe_comapRangeHomologyClass {i j : ι} (hij : c.Rel i j)
    (z : (LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom) :
    (hS.comapRangeHomologyClass hij z : S.X₁.homology j) =
      (S.X₁.homologyπ j).hom (S.X₁.moduleCatCyclesMk z.val (c.next j) rfl
        (hS.d_apply_eq_zero_of_mem_comap_range_d z (c.next j))) :=
  S.X₁.moduleCatHomologyClass_apply rfl _ _ z

/-- Evaluating `hS.comapRangeHomologyClass hij` on the underlying element of a cycle `z₁` of `S.X₁`
gives `(S.X₁.homologyπ j).hom z₁`. -/
@[simp]
theorem coe_comapRangeHomologyClass_iCycles {i j : ι} (hij : c.Rel i j) (z₁ : S.X₁.cycles j)
    (hz₁ : (S.X₁.iCycles j).hom z₁ ∈ (LinearMap.range (S.X₂.d i j).hom).comap (S.f.f j).hom) :
    (hS.comapRangeHomologyClass hij ⟨(S.X₁.iCycles j).hom z₁, hz₁⟩ : S.X₁.homology j) =
      (S.X₁.homologyπ j).hom z₁ := by
  rw [coe_comapRangeHomologyClass]
  congr 1
  exact S.X₁.moduleCat_iCycles_injective j (S.X₁.iCycles_moduleCatCyclesMk j _ _ rfl _)

/-- The inclusion of the boundaries of `S.X₁` into the preimage of the boundaries of `S.X₂` and the
homology class map `hS.comapRangeHomologyClass hij` form an exact pair. -/
theorem exact_inclusion_comapRangeHomologyClass {i j : ι} (hij : c.Rel i j) :
    Function.Exact (Submodule.inclusion (S.f.range_d_le_comap_range_d i j))
      (hS.comapRangeHomologyClass hij) := by
  intro z
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, comapRangeHomologyClass, LinearMap.codRestrict_apply,
    S.X₁.moduleCatHomologyClass_eq_zero_iff rfl _ _ (c.prev_eq' hij)]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨⟨(S.X₁.d i j).hom y, y, rfl⟩, Subtype.ext hy⟩,
    fun ⟨⟨_, y, rfl⟩, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩⟩

/-- Every element in the image of the connecting map `hS.δ i j hij` is the homology class of an
element of `S.X₁.X j` whose image in `S.X₂.X j` is a boundary from degree `i`. -/
theorem comapRangeHomologyClass_surjective {i j : ι} (hij : c.Rel i j) :
    Function.Surjective (hS.comapRangeHomologyClass hij) := by
  rintro ⟨_, x₃, rfl⟩
  obtain ⟨z₁, hz₁⟩ := S.X₁.moduleCat_homologyπ_surjective j ((hS.δ i j hij).hom x₃)
  obtain ⟨x₂, -, hx₂, -, -⟩ := hS.moduleCat_exists_d_eq_of_δ_eq i j hij x₃ z₁ hz₁.symm
  exact ⟨⟨(S.X₁.iCycles j).hom z₁, x₂, hx₂⟩,
    Subtype.ext ((hS.coe_comapRangeHomologyClass_iCycles hij z₁ ⟨x₂, hx₂⟩).trans hz₁)⟩

/-- In a short exact sequence of complexes of modules, for `c.Rel i j`, the induced map `Hᵢ(S.g)`
on homology is surjective if and only if the connecting morphism `hS.δ i j hij` vanishes. -/
theorem homologyMap_g_surjective_iff_δ_eq_zero {i j : ι} (hij : c.Rel i j) :
    Function.Surjective (HomologicalComplex.homologyMap S.g i).hom ↔ hS.δ i j hij = 0 := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (hS.homology_exact₃ i j hij).epi_f_iff

/-- In a short exact sequence of complexes of modules, for `c.Rel i j`, the induced map `Hⱼ(S.f)`
on homology is injective if and only if the connecting morphism `hS.δ i j hij` vanishes. -/
theorem homologyMap_f_injective_iff_δ_eq_zero {i j : ι} (hij : c.Rel i j) :
    Function.Injective (HomologicalComplex.homologyMap S.f j).hom ↔ hS.δ i j hij = 0 := by
  rw [← ModuleCat.mono_iff_injective]
  exact (hS.homology_exact₁ i j hij).mono_g_iff

include hS in
/-- In a short exact sequence of complexes of modules, for `c.Rel i j`, the induced map `Hⱼ(S.f)`
on homology is injective if and only if `Hᵢ(S.g)` is surjective. -/
theorem homologyMap_f_injective_iff_homologyMap_g_surjective {i j : ι} (hij : c.Rel i j) :
    Function.Injective (HomologicalComplex.homologyMap S.f j).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap S.g i).hom :=
  (hS.homologyMap_f_injective_iff_δ_eq_zero hij).trans
    (hS.homologyMap_g_surjective_iff_δ_eq_zero hij).symm

end CategoryTheory.ShortComplex.ShortExact

namespace TauCeti

universe w

/-- **The connecting map of the cokernel sequence of a composite, on classes.** Let `φ : X ⟶ Y` and
`ψ : Y ⟶ Z` be maps of complexes of modules, `ψ` a monomorphism, `s` an element of `Z` in degree
`n` and `t` an element of `Y` in degree `n + 1` with `ψ t = d s`, such that the image of `s` in
`cokernel ψ` is a cycle `x`. Then the image of `t` in `cokernel φ` is a cycle, and it represents
the image of the class of `x` under the connecting map of
`cokernel φ ⟶ cokernel (φ ≫ ψ) ⟶ cokernel ψ`. -/
theorem exists_δ_cokernelCompSequence_eq {R : Type*} [Ring R]
    {X Y Z : CochainComplex (ModuleCat.{w} R) ℤ} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [Mono ψ] (n : ℤ)
    (s : Z.X n) (t : Y.X (n + 1)) (hst : (ψ.f (n + 1)).hom t = (Z.d n (n + 1)).hom s)
    (x : (cokernel ψ).X n) (hx : ((cokernel ψ).d n (n + 1)).hom x = 0)
    (hsx : ((cokernel.π ψ).f n).hom s = x) :
    ∃ hc : ((cokernel φ).d (n + 1) (n + 1 + 1)).hom (((cokernel.π φ).f (n + 1)).hom t) = 0,
      ((cokernelCompSequence_shortExact φ ψ).δ n (n + 1) rfl).hom
          (((cokernel ψ).homologyπ n).hom ((cokernel ψ).moduleCatCyclesMk x (n + 1) (by simp) hx)) =
        ((cokernel φ).homologyπ (n + 1)).hom ((cokernel φ).moduleCatCyclesMk
          (((cokernel.π φ).f (n + 1)).hom t) (n + 1 + 1) (by simp) hc) := by
  have hS := cokernelCompSequence_shortExact φ ψ
  have hLg : cokernel.π (φ ≫ ψ) ≫ (kernelCokernelCompSequence.snakeInput φ ψ).L₃.g =
      cokernel.π ψ := by
    simp [kernelCokernelCompSequence.snakeInput]
  have hLf : cokernel.π φ ≫ (kernelCokernelCompSequence.snakeInput φ ψ).L₃.f =
      ψ ≫ cokernel.π (φ ≫ ψ) := by
    simp [kernelCokernelCompSequence.snakeInput]
  have hx₂ : (((kernelCokernelCompSequence.snakeInput φ ψ).L₃.g.f n).hom
      (((cokernel.π (φ ≫ ψ)).f n).hom s)) = x :=
    (congrArg (fun ξ ↦ (ξ.f n).hom s) hLg).trans hsx
  have hz₁ : (((kernelCokernelCompSequence.snakeInput φ ψ).L₃.f.f (n + 1)).hom
      (((cokernel.π φ).f (n + 1)).hom t)) =
      ((cokernel (φ ≫ ψ)).d n (n + 1)).hom (((cokernel.π (φ ≫ ψ)).f n).hom s) := by
    refine (congrArg (fun ξ ↦ (ξ.f (n + 1)).hom t) hLf).trans ?_
    -- `ψ ≫ cokernel.π` applied to `t`, written as a composite of elements.
    change ((cokernel.π (φ ≫ ψ)).f (n + 1)).hom (((ψ).f (n + 1)).hom t) = _
    rw [hst]
    exact (HomologicalComplex.Hom.comm_apply _ _ _ _).symm
  have hcyc : ((cokernel φ).d (n + 1) (n + 1 + 1)).hom (((cokernel.π φ).f (n + 1)).hom t) = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply n (n + 1) _ _ hz₁ _
  exact ⟨hcyc, hS.moduleCat_δ_homologyπ n (n + 1) rfl
    ((cokernel ψ).moduleCatCyclesMk x (n + 1) (by simp) hx)
    (((cokernel.π (φ ≫ ψ)).f n).hom s)
    (hx₂.trans (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm)
    ((cokernel φ).moduleCatCyclesMk (((cokernel.π φ).f (n + 1)).hom t) (n + 1 + 1) (by simp) hcyc)
    ((congrArg _ (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _)).trans hz₁)⟩

end TauCeti
