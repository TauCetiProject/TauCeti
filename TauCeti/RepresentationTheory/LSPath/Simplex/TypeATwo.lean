/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.ChainComplex
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.Presentation
public import TauCeti.RepresentationTheory.LSPath.Simplex.BruhatComplex

/-!
# Type `A` minimal coset representatives and the `A₂` Bruhat-chain realization

On a finite reduced root datum `(P, b)` of Cartan type `Aₙ`, a weight `λ` that lies off every
simple root wall (`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`, so `P.wallIndices b lam = ∅`; when `λ` is
dominant this means `λ` is regular and `W_λ` is trivial) has all `(n + 1)!` Weyl group elements as
minimal coset representatives, identified Bruhat-isomorphically with `Equiv.Perm (Fin (n + 1))` by
`TauCeti.LSPath.typeAMinimalCosetRepEquiv`.

Specializing to rank two (`A₂`), `TauCeti.LSPath.bruhatChainComplex P b lam` is isomorphic to
`TauCeti.symmetricThreeBruhatComplex` on the six permutations of `Fin 3`, with homeomorphic
polyhedron (`TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`) and four maximal tetrahedra
(`TauCeti.LSPath.typeATwoBruhatTetrahedron`) meeting along shared triangles or the common edge
`{1, w₀}`. At any weight with unit simple-coroot pairings `⟨λ, αᵢ^∨⟩ = 1` (such as `![1, 1]` on
`DynkinType.typeASimplyConnectedRootDatum 2`), every Lakshmibai–Seshadri path has at most two
internal breaks (`π.length < 3`), so the fixed-`λ` finite LS path set is disjoint from the open
interior of all four maximal tetrahedra.

## Main definitions

* `TauCeti.LSPath.typeAMinimalCosetRepEquiv`: Bruhat-preserving equivalence between minimal coset
  representatives for `P.wallIndices b lam` in type `Aₙ` (when `∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`)
  and `Equiv.Perm (Fin (n + 1))`.
* `TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`: homeomorphism between
  `(bruhatChainComplex P b lam).Realization` in type `A₂` and
  `symmetricThreeBruhatComplex.Realization`.
* `TauCeti.LSPath.typeATwoBruhatTetrahedron`: the four maximal Bruhat tetrahedra in type `A₂`.

## Main results

* `TauCeti.LSPath.card_minimalCosetRep_of_hasCartanType_A`: in type `Aₙ` off all simple root walls,
  there are `(n + 1)!` minimal coset representatives.
* `TauCeti.LSPath.maximal_typeATwo_bruhatChainComplex_iff` and
  `TauCeti.LSPath.typeATwoBruhatTetrahedron_inter`: the four maximal tetrahedra of
  `bruhatChainComplex P b lam` in type `A₂` and their pairwise intersections.
* `TauCeti.LSPath.length_lt_three_of_hasCartanType_A_two`,
  `TauCeti.LSPath.support_toBruhatRealization_ne_typeATwoBruhatTetrahedron`, and
  `TauCeti.LSPath.length_lt_three_typeASimplyConnectedRootDatum_two`: at unit simple-coroot
  pairings in type `A₂`, every LS path has fewer than three internal breaks and avoids the open
  interior of all four maximal tetrahedra.

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

section TypeA

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- On a root datum of Cartan type `Aₙ` at a weight `λ` off all simple root walls
(`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`, so `P.wallIndices b lam = ∅`; when `λ` is dominant this means
`λ` is regular and `W_λ` is trivial), the minimal coset representatives identify with
`Equiv.Perm (Fin (n + 1))` via `RootPairing.typeAWeylGroupEquiv`. -/
noncomputable def typeAMinimalCosetRepEquiv {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} ≃
      Equiv.Perm (Fin (n + 1)) where
  toFun u := P.typeAWeylGroupEquiv b e he u.1
  invFun σ := ⟨(P.typeAWeylGroupEquiv b e he).symm σ, by
    have hwall : P.wallIndices b lam = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦ hreg i (mem_wallIndices.mp hi)
    simp [hwall]⟩
  left_inv u := Subtype.ext ((P.typeAWeylGroupEquiv b e he).symm_apply_apply u.1)
  right_inv σ := (P.typeAWeylGroupEquiv b e he).apply_symm_apply σ

/-- Applying `typeAMinimalCosetRepEquiv` applies `RootPairing.typeAWeylGroupEquiv` to the
underlying Weyl group element. -/
@[simp]
theorem typeAMinimalCosetRepEquiv_apply {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (u : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    typeAMinimalCosetRepEquiv e he hreg u = P.typeAWeylGroupEquiv b e he u.1 :=
  (rfl)

/-- The underlying Weyl group element of `(typeAMinimalCosetRepEquiv e he hreg).symm σ` is
`(P.typeAWeylGroupEquiv b e he).symm σ`. -/
@[simp]
theorem coe_typeAMinimalCosetRepEquiv_symm {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (σ : Equiv.Perm (Fin (n + 1))) :
    ((typeAMinimalCosetRepEquiv e he hreg).symm σ).1 =
      (P.typeAWeylGroupEquiv b e he).symm σ :=
  (rfl)

/-- `typeAMinimalCosetRepEquiv` preserves and reflects the Bruhat order. -/
theorem bruhatLE_typeAMinimalCosetRepEquiv_iff {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {u v : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    (permCoxeterSystem (n + 1)).BruhatLE
        (typeAMinimalCosetRepEquiv e he hreg u)
        (typeAMinimalCosetRepEquiv e he hreg v) ↔
      (weylCoxeterSystem P b).BruhatLE u.1 v.1 :=
  P.bruhatLE_typeAWeylGroupEquiv_iff b e he

/-- The inverse of `typeAMinimalCosetRepEquiv` preserves and reflects the Bruhat order. -/
theorem bruhatLE_typeAMinimalCosetRepEquiv_symm_iff {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ τ : Equiv.Perm (Fin (n + 1))} :
    (weylCoxeterSystem P b).BruhatLE
        ((typeAMinimalCosetRepEquiv e he hreg).symm σ).1
        ((typeAMinimalCosetRepEquiv e he hreg).symm τ).1 ↔
      (permCoxeterSystem (n + 1)).BruhatLE σ τ :=
  P.bruhatLE_typeAWeylGroupEquiv_symm_iff b e he

/-- On a root datum of Cartan type `Aₙ` at a weight `λ` off all simple root walls, there are
`(n + 1)!` minimal coset representatives for `P.wallIndices b lam`. -/
theorem card_minimalCosetRep_of_hasCartanType_A {n : ℕ} (hA : HasCartanType P b (.A n))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    Nat.card {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} =
      (n + 1).factorial := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b (.A n)).mp hA
  rw [DynkinType.cartanMatrix_A] at he
  rw [Nat.card_congr (typeAMinimalCosetRepEquiv e he hreg), Nat.card_perm, Nat.card_fin]
  simp

end TypeA

section TypeATwo

attribute [local instance] Classical.propDecidable

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- Under `typeAMinimalCosetRepEquiv` in rank two, a finite set of minimal coset representatives is
a face of `bruhatChainComplex P b lam` if and only if its image in `Equiv.Perm (Fin 3)` is a face of
`symmetricThreeBruhatComplex`. -/
theorem map_mem_symmetricThreeBruhatComplex_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    σ.map (typeAMinimalCosetRepEquiv e he hreg).toEmbedding ∈ symmetricThreeBruhatComplex ↔
      σ ∈ bruhatChainComplex P b lam := by
  let eqv := typeAMinimalCosetRepEquiv e he hreg
  rw [mem_symmetricThreeBruhatComplex_iff_bruhatLE, mem_bruhatChainComplex_iff,
    Finset.map_nonempty]
  refine and_congr_right fun _ ↦ ⟨fun h u hu v hv ↦ ?_, fun h x hx y hy ↦ ?_⟩
  · exact (h (eqv u) (Finset.mem_map_of_mem _ hu) (eqv v) (Finset.mem_map_of_mem _ hv)).imp
      (bruhatLE_typeAMinimalCosetRepEquiv_iff e he hreg).mp
      (bruhatLE_typeAMinimalCosetRepEquiv_iff e he hreg).mp
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact (h u hu v hv).imp
      (bruhatLE_typeAMinimalCosetRepEquiv_iff e he hreg).mpr
      (bruhatLE_typeAMinimalCosetRepEquiv_iff e he hreg).mpr

/-- **Homeomorphism of the `A₂` Bruhat-chain polyhedron (off simple root walls) with the six-vertex
`S₃` four-tetrahedron complex.** -/
noncomputable def typeATwoBruhatRealizationHomeomorph (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    (bruhatChainComplex P b lam).Realization ≃ₜ symmetricThreeBruhatComplex.Realization := by
  let eqv := typeAMinimalCosetRepEquiv e he hreg
  let fSimp : _root_.PreAbstractSimplicialComplex.SimplicialMap
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex :=
    { toFun := eqv
      map_face' := fun σ hσ ↦ by
        rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
          ← eqv.coe_toEmbedding, ← Finset.map_eq_image,
          map_mem_symmetricThreeBruhatComplex_iff e he hreg]
        exact hσ }
  let gSimp : _root_.PreAbstractSimplicialComplex.SimplicialMap
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex :=
    { toFun := eqv.symm
      map_face' := fun σ hσ ↦ by
        rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
          ← eqv.symm.coe_toEmbedding, ← Finset.map_eq_image,
          ← map_mem_symmetricThreeBruhatComplex_iff e he hreg]
        have hmap : (σ.map eqv.symm.toEmbedding).map eqv.toEmbedding = σ := by
          simp [Finset.map_map]
        rwa [hmap] }
  exact fSimp.realizationHomeomorph gSimp
    (DFunLike.coe_injective (funext fun u ↦ Subtype.ext (by simp [fSimp, gSimp, eqv])))
    (DFunLike.coe_injective (funext fun σ ↦ by simp [fSimp, gSimp, eqv]))

/-- `typeATwoBruhatRealizationHomeomorph` pushes barycentric coordinates forward along
`typeAMinimalCosetRepEquiv`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_val (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (x : (bruhatChainComplex P b lam).Realization) :
    (typeATwoBruhatRealizationHomeomorph e he hreg x : Equiv.Perm (Fin 3) →₀ ℝ) =
      x.1.mapDomain (typeAMinimalCosetRepEquiv e he hreg) := by
  simp only [typeATwoBruhatRealizationHomeomorph,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_apply,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val]
  rfl

/-- The inverse of `typeATwoBruhatRealizationHomeomorph` pushes barycentric coordinates forward
along `(typeAMinimalCosetRepEquiv e he hreg).symm`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_symm_val (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (y : symmetricThreeBruhatComplex.Realization) :
    ((typeATwoBruhatRealizationHomeomorph e he hreg).symm y :
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} →₀ ℝ) =
      y.1.mapDomain (typeAMinimalCosetRepEquiv e he hreg).symm := by
  simp only [typeATwoBruhatRealizationHomeomorph,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_symm_apply,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val]
  rfl

/-- `typeATwoBruhatRealizationHomeomorph` maps each realization vertex `u` to the vertex
`typeAMinimalCosetRepEquiv e he hreg u` of `symmetricThreeBruhatComplex`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_vertex (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (u : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    typeATwoBruhatRealizationHomeomorph e he hreg
        (_root_.AbstractSimplicialComplex.vertex (bruhatChainComplex P b lam) u) =
      _root_.AbstractSimplicialComplex.vertex symmetricThreeBruhatComplex
        (typeAMinimalCosetRepEquiv e he hreg u) := by
  apply Subtype.ext
  simp

/-- The inverse of `typeATwoBruhatRealizationHomeomorph` maps each vertex `σ` of
`symmetricThreeBruhatComplex` to `(typeAMinimalCosetRepEquiv e he hreg).symm σ`. -/
@[simp]
theorem typeATwoBruhatRealizationHomeomorph_symm_vertex (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (σ : Equiv.Perm (Fin 3)) :
    (typeATwoBruhatRealizationHomeomorph e he hreg).symm
        (_root_.AbstractSimplicialComplex.vertex symmetricThreeBruhatComplex σ) =
      _root_.AbstractSimplicialComplex.vertex (bruhatChainComplex P b lam)
        ((typeAMinimalCosetRepEquiv e he hreg).symm σ) := by
  apply Subtype.ext
  simp

/-- The four maximal tetrahedra of `bruhatChainComplex P b lam` in type `A₂` off simple root walls,
transported from `symmetricThreeBruhatTetrahedron`. -/
noncomputable def typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
  (symmetricThreeBruhatTetrahedron a c).map
    (typeAMinimalCosetRepEquiv e he hreg).symm.toEmbedding

/-- Defining formula for `typeATwoBruhatTetrahedron`. -/
theorem typeATwoBruhatTetrahedron_def (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c =
      (symmetricThreeBruhatTetrahedron a c).map
        (typeAMinimalCosetRepEquiv e he hreg).symm.toEmbedding :=
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
      (typeAMinimalCosetRepEquiv e he hreg).toEmbedding =
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
  have hmap := congrArg (Finset.map (typeAMinimalCosetRepEquiv e he hreg).toEmbedding) h
  simpa [typeATwoBruhatTetrahedron_def, Finset.map_map] using hmap

/-- Two maximal tetrahedra of `bruhatChainComplex P b lam` in type `A₂` share both endpoints and
whichever middle vertices agree between their index pairs. -/
theorem typeATwoBruhatTetrahedron_inter (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c a' c' : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c ∩ typeATwoBruhatTetrahedron e he hreg a' c' =
      Finset.map (typeAMinimalCosetRepEquiv e he hreg).symm.toEmbedding
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
  let eqv := typeAMinimalCosetRepEquiv e he hreg
  have hsurj : ({ρ | ρ ∈ symmetricThreeBruhatComplex} : Set _) ⊆
      Set.range (Finset.mapEmbedding eqv.toEmbedding) := fun ρ _ ↦
    ⟨(Equiv.finsetCongr eqv).symm ρ, by
      simp [Finset.mapEmbedding_apply, Equiv.finsetCongr_symm, Finset.map_map]⟩
  have hmax := (Finset.mapEmbedding eqv.toEmbedding).maximal_apply_mem_iff (x := σ) hsurj
  simp only [Finset.mapEmbedding_apply, Set.mem_ofPred_eq, eqv,
    map_mem_symmetricThreeBruhatComplex_iff e he hreg] at hmax
  rw [← hmax, maximal_symmetricThreeBruhatComplex_iff]
  refine exists₂_congr fun a c ↦ ?_
  rw [← Equiv.finsetCongr_apply, ← (Equiv.finsetCongr eqv).eq_symm_apply]
  rfl

private theorem dir_two_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    {π : LSPath P b lam} (hlen : 3 ≤ π.length) :
    (π.dir ⟨3, by omega⟩).1 = 1 ∧
      ∃ i : b.support, (π.dir ⟨2, by omega⟩).1 = (weylCoxeterSystem P b).simple i := by
  let i0 : Fin (π.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (π.length + 1) := ⟨1, by omega⟩
  let i2 : Fin (π.length + 1) := ⟨2, by omega⟩
  let i3 : Fin (π.length + 1) := ⟨3, by omega⟩
  have htop : (weylCoxeterSystem P b).length (π.dir i0).1 ≤ 3 := by
    rw [length_weylCoxeterSystem_eq]
    exact (ncard_inversions_le P b _).trans (by rw [P.ncard_posRoots_of_hasCartanType_A b hA])
  have hi01 : i0 < i1 := Fin.mk_lt_mk.mpr (by omega)
  have hi12 : i1 < i2 := Fin.mk_lt_mk.mpr (by omega)
  have hi23 : i2 < i3 := Fin.mk_lt_mk.mpr (by omega)
  have h01 : (weylCoxeterSystem P b).length (π.dir i1).1 <
      (weylCoxeterSystem P b).length (π.dir i0).1 := π.strictAnti_length_dir hi01
  have h12 : (weylCoxeterSystem P b).length (π.dir i2).1 <
      (weylCoxeterSystem P b).length (π.dir i1).1 := π.strictAnti_length_dir hi12
  have h23 : (weylCoxeterSystem P b).length (π.dir i3).1 <
      (weylCoxeterSystem P b).length (π.dir i2).1 := π.strictAnti_length_dir hi23
  have hl3 : (weylCoxeterSystem P b).length (π.dir i3).1 = 0 := by omega
  have hl2 : (weylCoxeterSystem P b).length (π.dir i2).1 = 1 := by omega
  obtain ⟨ω, hω, hprod⟩ := (weylCoxeterSystem P b).exists_isReduced (π.dir i2).1
  rw [hprod] at hl2
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp (hω.eq.symm.trans hl2)
  exact ⟨(weylCoxeterSystem P b).length_eq_zero_iff.mp hl3, i, by simpa [i2] using hprod⟩

/-- **Distinguishing the four-tetrahedron `S₃` realization from the fixed-`λ` LS path set at unit
simple-coroot pairings.** On any root datum of Cartan type `A₂` and any weight `λ` with
`⟨λ, αᵢ^∨⟩ = 1` on both simple coroots, every LS path of shape `λ` has `π.length < 3` (at most
three directions). Consequently no LS path of shape `λ` enters the open interior of any of the
four maximal tetrahedra. -/
theorem length_lt_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    (hρ : ∀ i : b.support, P.coroot' i lam = 1) (π : LSPath P b lam) :
    π.length < 3 := by
  by_contra! hlen
  have hlam : lam ∈ dominantChamber P b :=
    (mem_dominantChamber P b lam).mpr fun i hi ↦ by rw [hρ ⟨i, hi⟩]; exact zero_le_one
  obtain ⟨hd3, i, hd2⟩ := dir_two_three_of_hasCartanType_A_two hA hlen
  let j : Fin π.length := ⟨2, by omega⟩
  obtain ⟨C, hCh, hCl, hC⟩ := π.exists_isAChain j
  have hdvd : (π.time j.castSucc.succ).den ∣
      intervalBondGcd b lam ((weylCoxeterSystem P b).simple i) 1 := by
    rw [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl] at hC
    simpa [j, hd2, hd3] using hC
  have hcov := minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero (i := i)
    (by rw [hρ i]; exact one_ne_zero)
  rw [intervalBondGcd_of_minimalCosetRepCovBy hlam hcov,
    reflectionBond_simple_smul_one_smul, hρ i] at hdvd
  have hden : (π.time j.castSucc.succ).den = 1 := Nat.dvd_one.mp hdvd
  have h0 : (0 : ℚ) < π.time j.castSucc.succ := by
    rw [← π.time_zero]
    exact π.strictMono_time (Fin.succ_pos _)
  have h1 : π.time j.castSucc.succ < 1 := by
    rw [← π.time_last]
    exact π.strictMono_time (by simp [Fin.lt_def, j]; omega)
  have hnum : ((π.time j.castSucc.succ).num : ℚ) = π.time j.castSucc.succ :=
    Rat.intCast_num_of_den_eq_one hden
  rw [← hnum] at h0 h1
  have h0' : (0 : ℤ) < (π.time j.castSucc.succ).num := Int.cast_pos.mp h0
  have h1' : (π.time j.castSucc.succ).num < 1 := by exact_mod_cast h1
  omega

/-- No LS path of shape `λ` with unit simple-coroot pairings in type `A₂` has support equal to any
of the four maximal Bruhat tetrahedra. -/
theorem support_toBruhatRealization_ne_typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hρ : ∀ i : b.support, P.coroot' i lam = 1) (π : LSPath P b lam) (a c : Fin 2) :
    π.toBruhatRealization.1.support ≠
      typeATwoBruhatTetrahedron e he (fun i ↦ by rw [hρ i]; exact one_ne_zero) a c := by
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
breaks, so none meets the open interior of any of the four maximal Bruhat tetrahedra. -/
theorem length_lt_three_typeASimplyConnectedRootDatum_two
    (π : LSPath (DynkinType.typeASimplyConnectedRootDatum 2)
      (DynkinType.typeASimplyConnectedBase 2) ![1, 1]) :
    π.length < 3 := by
  refine length_lt_three_of_hasCartanType_A_two
    (DynkinType.hasCartanType_typeASimplyConnectedRootDatum 2) (fun i ↦ ?_) π
  have hi : (i.1 : ℕ) < 2 := DynkinType.mem_typeASimplyConnectedBase_support.mp i.2
  let k : Fin 2 := ⟨i.1, hi⟩
  have hik : i.1 = DynkinType.typeASimpleIndex 2 k := Fin.ext (by simp [k])
  simp only [RootPairing.coroot', LinearMap.flip_apply,
    DynkinType.toLinearMap_typeASimplyConnectedRootDatum, hik,
    DynkinType.coroot_typeASimpleIndex, dotProduct_single, mul_one]
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with h | h <;> simp [h]

end TypeATwo

end TauCeti.LSPath
