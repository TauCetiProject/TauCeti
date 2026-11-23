/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.ChainComplex
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.MinimalCosetRep
public import TauCeti.RepresentationTheory.LSPath.Simplex.BruhatComplex

/-!
# The `A₂` Bruhat-chain realization and its four maximal tetrahedra

For the general type-`Aₙ` identification `RootPairing.typeAMinimalCosetRepEquiv` between minimal
coset representatives off simple root walls and `Equiv.Perm (Fin (n + 1))`, see
`TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.MinimalCosetRep`.

Specializing to rank two (`A₂`), when `λ` lies off both simple root walls
(`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`, so `P.wallIndices b lam = ∅`; when `λ` is dominant this means
`λ` is regular and `W_λ` is trivial), `TauCeti.LSPath.bruhatChainComplex P b lam` is isomorphic to
`TauCeti.symmetricThreeBruhatComplex` on the six permutations of `Fin 3`, with homeomorphic
polyhedron (`TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`) and four maximal tetrahedra
(`TauCeti.LSPath.typeATwoBruhatTetrahedron`) meeting along shared triangles or the common edge
`{1, w₀}`. At any weight with unit-magnitude simple-coroot pairings `|⟨λ, αᵢ^∨⟩| = 1` (such as
`![1, 1]` on `DynkinType.typeASimplyConnectedRootDatum 2`), every Lakshmibai–Seshadri path has at
most two internal breaks (`π.length < 3`, deduced from the general type-independent integrality
obstruction `TauCeti.LSPath.dir_succ_ne_one_of_dir_castSucc_eq_simple`), so no LS path has support
equal to any of the four maximal tetrahedra.

## Main definitions

* `TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`: homeomorphism between
  `(bruhatChainComplex P b lam).Realization` in type `A₂` and
  `symmetricThreeBruhatComplex.Realization`.
* `TauCeti.LSPath.typeATwoBruhatTetrahedron`: the four maximal Bruhat tetrahedra in type `A₂`.

## Main results

* `TauCeti.LSPath.maximal_typeATwo_bruhatChainComplex_iff` and
  `TauCeti.LSPath.typeATwoBruhatTetrahedron_inter`: the four maximal tetrahedra of
  `bruhatChainComplex P b lam` in type `A₂` and their pairwise intersections.
* `TauCeti.LSPath.length_lt_three_of_hasCartanType_A_two`,
  `TauCeti.LSPath.support_toBruhatRealization_ne_typeATwoBruhatTetrahedron`, and
  `TauCeti.LSPath.length_lt_three_typeASimplyConnectedRootDatum_two`: at unit-magnitude
  simple-coroot pairings in type `A₂`, every LS path has fewer than three internal breaks and its
  support is distinct from each of the four maximal tetrahedra.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, GTM 231, Springer (2005), §§2.2–2.5.
* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329–346, §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §4.
-/

public section

universe u w x

namespace TauCeti.LSPath

open RootPairing

section TypeATwo

attribute [local instance] Classical.propDecidable

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- Under `RootPairing.typeAMinimalCosetRepEquiv` in rank two, a finite set of minimal coset
representatives is a face of `bruhatChainComplex P b lam` if and only if its image in
`Equiv.Perm (Fin 3)` is a face of `symmetricThreeBruhatComplex`. -/
theorem map_mem_symmetricThreeBruhatComplex_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    σ.map (P.typeAMinimalCosetRepEquiv b e he hreg).toEmbedding ∈ symmetricThreeBruhatComplex ↔
      σ ∈ bruhatChainComplex P b lam := by
  let eqv := P.typeAMinimalCosetRepEquiv b e he hreg
  rw [mem_symmetricThreeBruhatComplex_iff_bruhatLE, mem_bruhatChainComplex_iff,
    Finset.map_nonempty]
  refine and_congr_right fun _ ↦ ⟨fun h u hu v hv ↦ ?_, fun h x hx y hy ↦ ?_⟩
  · exact (h (eqv u) (Finset.mem_map_of_mem _ hu) (eqv v) (Finset.mem_map_of_mem _ hv)).imp
      (P.bruhatLE_typeAMinimalCosetRepEquiv_iff b e he hreg).mp
      (P.bruhatLE_typeAMinimalCosetRepEquiv_iff b e he hreg).mp
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact (h u hu v hv).imp
      (P.bruhatLE_typeAMinimalCosetRepEquiv_iff b e he hreg).mpr
      (P.bruhatLE_typeAMinimalCosetRepEquiv_iff b e he hreg).mpr

private noncomputable def typeATwoBruhatSimplicialMap (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    _root_.PreAbstractSimplicialComplex.SimplicialMap
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex where
  toFun := P.typeAMinimalCosetRepEquiv b e he hreg
  map_face' σ hσ := by
    rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      ← (P.typeAMinimalCosetRepEquiv b e he hreg).coe_toEmbedding, ← Finset.map_eq_image,
      map_mem_symmetricThreeBruhatComplex_iff e he hreg]
    exact hσ

private theorem coe_typeATwoBruhatSimplicialMap (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    ⇑(typeATwoBruhatSimplicialMap e he hreg) = P.typeAMinimalCosetRepEquiv b e he hreg :=
  (rfl)

private noncomputable def typeATwoBruhatSimplicialMapSymm (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    _root_.PreAbstractSimplicialComplex.SimplicialMap
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex where
  toFun := (P.typeAMinimalCosetRepEquiv b e he hreg).symm
  map_face' σ hσ := by
    let eqv := P.typeAMinimalCosetRepEquiv b e he hreg
    rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      ← eqv.symm.coe_toEmbedding, ← Finset.map_eq_image,
      ← map_mem_symmetricThreeBruhatComplex_iff e he hreg]
    have hmap : (σ.map eqv.symm.toEmbedding).map eqv.toEmbedding = σ := by
      simp [Finset.map_map]
    rwa [hmap]

private theorem coe_typeATwoBruhatSimplicialMapSymm (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    ⇑(typeATwoBruhatSimplicialMapSymm e he hreg) =
      (P.typeAMinimalCosetRepEquiv b e he hreg).symm :=
  (rfl)

/-- **Homeomorphism of the `A₂` Bruhat-chain polyhedron (off simple root walls) with the six-vertex
`S₃` four-tetrahedron complex.** -/
noncomputable def typeATwoBruhatRealizationHomeomorph (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    (bruhatChainComplex P b lam).Realization ≃ₜ symmetricThreeBruhatComplex.Realization :=
  (typeATwoBruhatSimplicialMap e he hreg).realizationHomeomorph
    (typeATwoBruhatSimplicialMapSymm e he hreg)
    (DFunLike.coe_injective (by
      rw [_root_.PreAbstractSimplicialComplex.SimplicialMap.coe_comp,
        _root_.PreAbstractSimplicialComplex.SimplicialMap.coe_id,
        coe_typeATwoBruhatSimplicialMap, coe_typeATwoBruhatSimplicialMapSymm]
      exact (P.typeAMinimalCosetRepEquiv b e he hreg).symm_comp_self))
    (DFunLike.coe_injective (by
      rw [_root_.PreAbstractSimplicialComplex.SimplicialMap.coe_comp,
        _root_.PreAbstractSimplicialComplex.SimplicialMap.coe_id,
        coe_typeATwoBruhatSimplicialMap, coe_typeATwoBruhatSimplicialMapSymm]
      exact (P.typeAMinimalCosetRepEquiv b e he hreg).self_comp_symm))

/-- `typeATwoBruhatRealizationHomeomorph` pushes barycentric coordinates forward along
`RootPairing.typeAMinimalCosetRepEquiv`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_val (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (x : (bruhatChainComplex P b lam).Realization) :
    (typeATwoBruhatRealizationHomeomorph e he hreg x : Equiv.Perm (Fin 3) →₀ ℝ) =
      x.val.mapDomain (P.typeAMinimalCosetRepEquiv b e he hreg) := by
  rw [typeATwoBruhatRealizationHomeomorph,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_apply,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
    coe_typeATwoBruhatSimplicialMap]

/-- The inverse of `typeATwoBruhatRealizationHomeomorph` pushes barycentric coordinates forward
along `(P.typeAMinimalCosetRepEquiv b e he hreg).symm`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_symm_val (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (y : symmetricThreeBruhatComplex.Realization) :
    ((typeATwoBruhatRealizationHomeomorph e he hreg).symm y :
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} →₀ ℝ) =
      y.val.mapDomain (P.typeAMinimalCosetRepEquiv b e he hreg).symm := by
  rw [typeATwoBruhatRealizationHomeomorph,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_symm_apply,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
    coe_typeATwoBruhatSimplicialMapSymm]

/-- `typeATwoBruhatRealizationHomeomorph` maps each realization vertex `u` to the vertex
`P.typeAMinimalCosetRepEquiv b e he hreg u` of `symmetricThreeBruhatComplex`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_vertex (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (u : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    typeATwoBruhatRealizationHomeomorph e he hreg
        (_root_.AbstractSimplicialComplex.vertex (bruhatChainComplex P b lam) u) =
      _root_.AbstractSimplicialComplex.vertex symmetricThreeBruhatComplex
        (P.typeAMinimalCosetRepEquiv b e he hreg u) := by
  apply Subtype.ext
  simp

/-- The inverse of `typeATwoBruhatRealizationHomeomorph` maps each vertex `σ` of
`symmetricThreeBruhatComplex` to `(P.typeAMinimalCosetRepEquiv b e he hreg).symm σ`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_symm_vertex (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (σ : Equiv.Perm (Fin 3)) :
    (typeATwoBruhatRealizationHomeomorph e he hreg).symm
        (_root_.AbstractSimplicialComplex.vertex symmetricThreeBruhatComplex σ) =
      _root_.AbstractSimplicialComplex.vertex (bruhatChainComplex P b lam)
        ((P.typeAMinimalCosetRepEquiv b e he hreg).symm σ) := by
  apply Subtype.ext
  simp

/-- The four maximal tetrahedra of `bruhatChainComplex P b lam` in type `A₂` off simple root walls,
transported from `symmetricThreeBruhatTetrahedron`. -/
noncomputable def typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
  (symmetricThreeBruhatTetrahedron a c).map
    (P.typeAMinimalCosetRepEquiv b e he hreg).symm.toEmbedding

/-- Defining formula for `typeATwoBruhatTetrahedron`. -/
theorem typeATwoBruhatTetrahedron_def (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c =
      (symmetricThreeBruhatTetrahedron a c).map
        (P.typeAMinimalCosetRepEquiv b e he hreg).symm.toEmbedding :=
  (rfl)

/-- Each maximal tetrahedron of `bruhatChainComplex P b lam` in type `A₂` has `4` vertices. -/
@[simp]
theorem card_typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    (typeATwoBruhatTetrahedron e he hreg a c).card = 4 := by
  simp [typeATwoBruhatTetrahedron_def]

/-- Each `typeATwoBruhatTetrahedron` is a face of `bruhatChainComplex P b lam`. -/
@[simp↓]
theorem typeATwoBruhatTetrahedron_mem (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c ∈ bruhatChainComplex P b lam := by
  rw [← map_mem_symmetricThreeBruhatComplex_iff e he hreg]
  have hmap : (typeATwoBruhatTetrahedron e he hreg a c).map
      (P.typeAMinimalCosetRepEquiv b e he hreg).toEmbedding =
      symmetricThreeBruhatTetrahedron a c := by
    simp [typeATwoBruhatTetrahedron_def, Finset.map_map]
  rw [hmap]
  exact symmetricThreeBruhatTetrahedron_mem a c

/-- The four tetrahedra `typeATwoBruhatTetrahedron e he hreg a c` are pairwise distinct. -/
theorem typeATwoBruhatTetrahedron_injective (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    Function.Injective
      (fun ac : Fin 2 × Fin 2 ↦ typeATwoBruhatTetrahedron e he hreg ac.1 ac.2) := by
  intro ac bd h
  apply symmetricThreeBruhatTetrahedron_injective
  have hmap := congrArg (Finset.map (P.typeAMinimalCosetRepEquiv b e he hreg).toEmbedding) h
  simpa [typeATwoBruhatTetrahedron_def, Finset.map_map] using hmap

/-- Two maximal tetrahedra of `bruhatChainComplex P b lam` in type `A₂` share both endpoints and
whichever middle vertices agree between their index pairs. -/
theorem typeATwoBruhatTetrahedron_inter (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c a' c' : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c ∩ typeATwoBruhatTetrahedron e he hreg a' c' =
      Finset.map (P.typeAMinimalCosetRepEquiv b e he hreg).symm.toEmbedding
        ({symmetricThreeVertex 0, symmetricThreeVertex 5} ∪
          (if a = a' then {symmetricThreeVertex (![1, 2] a)} else ∅) ∪
          (if c = c' then {symmetricThreeVertex (![3, 4] c)} else ∅)) := by
  rw [typeATwoBruhatTetrahedron_def, typeATwoBruhatTetrahedron_def, ← Finset.map_inter,
    symmetricThreeBruhatTetrahedron_inter]

/-- The maximal faces of `bruhatChainComplex P b lam` in type `A₂` off simple root walls are
precisely the four tetrahedra `typeATwoBruhatTetrahedron e he hreg a c`. -/
theorem maximal_typeATwo_bruhatChainComplex_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    Maximal (· ∈ bruhatChainComplex P b lam) σ ↔
      ∃ a c, σ = typeATwoBruhatTetrahedron e he hreg a c := by
  let eqv := P.typeAMinimalCosetRepEquiv b e he hreg
  have hsurj : ({ρ | ρ ∈ symmetricThreeBruhatComplex} : Set _) ⊆
      Set.range (Finset.mapEmbedding eqv.toEmbedding) := fun ρ _ ↦
    ⟨(Equiv.finsetCongr eqv).symm ρ, by
      simp [Finset.mapEmbedding_apply, Equiv.finsetCongr_symm, Finset.map_map]⟩
  have hmax := (Finset.mapEmbedding eqv.toEmbedding).maximal_apply_mem_iff (x := σ) hsurj
  simp only [Finset.mapEmbedding_apply, Set.mem_ofPred_eq, eqv,
    map_mem_symmetricThreeBruhatComplex_iff e he hreg] at hmax
  rw [← hmax, maximal_symmetricThreeBruhatComplex_iff]
  refine exists₂_congr fun a c ↦ ?_
  rw [← Equiv.finsetCongr_apply, ← (Equiv.finsetCongr eqv).eq_symm_apply,
    Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, ← typeATwoBruhatTetrahedron_def]

private theorem dir_two_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    {π : LSPath P b lam} (hlen : 3 ≤ π.length) :
    (π.dir ⟨3, by omega⟩).val = 1 ∧
      ∃ i : b.support, (π.dir ⟨2, by omega⟩).val = (weylCoxeterSystem P b).simple i := by
  let i0 : Fin (π.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (π.length + 1) := ⟨1, by omega⟩
  let i2 : Fin (π.length + 1) := ⟨2, by omega⟩
  let i3 : Fin (π.length + 1) := ⟨3, by omega⟩
  have htop : (weylCoxeterSystem P b).length (π.dir i0).val ≤ 3 := by
    rw [length_weylCoxeterSystem_eq]
    exact (ncard_inversions_le P b _).trans (by rw [P.ncard_posRoots_of_hasCartanType_A b hA])
  have hi01 : i0 < i1 := Fin.mk_lt_mk.mpr (by omega)
  have hi12 : i1 < i2 := Fin.mk_lt_mk.mpr (by omega)
  have hi23 : i2 < i3 := Fin.mk_lt_mk.mpr (by omega)
  have h01 : (weylCoxeterSystem P b).length (π.dir i1).val <
      (weylCoxeterSystem P b).length (π.dir i0).val := π.strictAnti_length_dir hi01
  have h12 : (weylCoxeterSystem P b).length (π.dir i2).val <
      (weylCoxeterSystem P b).length (π.dir i1).val := π.strictAnti_length_dir hi12
  have h23 : (weylCoxeterSystem P b).length (π.dir i3).val <
      (weylCoxeterSystem P b).length (π.dir i2).val := π.strictAnti_length_dir hi23
  have hl3 : (weylCoxeterSystem P b).length (π.dir i3).val = 0 := by omega
  have hl2 : (weylCoxeterSystem P b).length (π.dir i2).val = 1 := by omega
  obtain ⟨ω, hω, hprod⟩ := (weylCoxeterSystem P b).exists_isReduced (π.dir i2).val
  rw [hprod] at hl2
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp (hω.eq.symm.trans hl2)
  exact ⟨(weylCoxeterSystem P b).length_eq_zero_iff.mp hl3, i, by simpa [i2] using hprod⟩

/-- **Length bound for type `A₂` at unit-magnitude simple-coroot pairings.** On any root datum of
Cartan type `A₂` and any weight `λ` with `|⟨λ, αᵢ^∨⟩| = 1` on both simple coroots, every
Lakshmibai–Seshadri path of shape `λ` has `π.length < 3` (at most three directions). For the
resulting support obstruction against the four maximal Bruhat tetrahedra, see
`support_toBruhatRealization_ne_typeATwoBruhatTetrahedron`. -/
theorem length_lt_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    (hρ : ∀ i : b.support, (P.coroot' i lam).natAbs = 1) (π : LSPath P b lam) :
    π.length < 3 := by
  by_contra! hlen
  obtain ⟨hd3, i, hd2⟩ := dir_two_three_of_hasCartanType_A_two hA hlen
  exact π.dir_succ_ne_one_of_dir_castSucc_eq_simple (j := ⟨2, by omega⟩) (hρ i) hd2 hd3

/-- No LS path of shape `λ` with unit-magnitude simple-coroot pairings in type `A₂` has support
equal to any of the four maximal Bruhat tetrahedra. -/
theorem support_toBruhatRealization_ne_typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hρ : ∀ i : b.support, (P.coroot' i lam).natAbs = 1) (π : LSPath P b lam) (a c : Fin 2) :
    π.toBruhatRealization.val.support ≠
      typeATwoBruhatTetrahedron e he
        (fun i h ↦ by have := hρ i; simp [h] at this) a c := by
  intro heq
  have hA : HasCartanType P b (.A 2) := by
    rw [hasCartanType_iff, DynkinType.cartanMatrix_A]
    exact ⟨e, he⟩
  have hlt := length_lt_three_of_hasCartanType_A_two hA hρ π
  have h4 := congrArg Finset.card heq
  rw [support_toBruhatRealization, Finset.card_image_of_injective _ π.dir_injective,
    Finset.card_univ, Fintype.card_fin, card_typeATwoBruhatTetrahedron] at h4
  omega

/-- Concrete specialization to the pinned simply connected root datum of type `A₂` at the
fundamental-weight sum `![1, 1]`: every Lakshmibai–Seshadri path has fewer than `3` internal
breaks. -/
theorem length_lt_three_typeASimplyConnectedRootDatum_two
    (π : LSPath (DynkinType.typeASimplyConnectedRootDatum 2)
      (DynkinType.typeASimplyConnectedBase 2) ![1, 1]) :
    π.length < 3 := by
  refine length_lt_three_of_hasCartanType_A_two
    (DynkinType.hasCartanType_typeASimplyConnectedRootDatum 2) (fun i ↦ ?_) π
  have hi : (i.val : ℕ) < 2 := DynkinType.mem_typeASimplyConnectedBase_support.mp i.property
  let k : Fin 2 := ⟨i.val, hi⟩
  have hik : i.val = DynkinType.typeASimpleIndex 2 k := Fin.ext (by simp [k])
  simp only [RootPairing.coroot', LinearMap.flip_apply,
    DynkinType.toLinearMap_typeASimplyConnectedRootDatum, hik,
    DynkinType.coroot_typeASimpleIndex, dotProduct_single, mul_one]
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with h | h <;> simp [h]

end TypeATwo

end TauCeti.LSPath
