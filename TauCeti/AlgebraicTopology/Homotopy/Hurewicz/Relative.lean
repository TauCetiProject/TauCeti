/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Hurewicz
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Relative

/-!
# Surjectivity of the relative Hurewicz map

Let `A` be a path-connected subspace of a space `X` and `a₀ ∈ A`. Suppose that every point of `X`
is joined by a path to a point of `A`, and that the relative homotopy sets `πₖ(X, A, a₀)` are
trivial for `0 < k < n`, where `n ≥ 2`. This file proves that the relative Hurewicz map
`πₙ(X, A, a₀) → Hₙ(X, A; ℤ)`, `[p] ↦ p_*[Iⁿ]`, is surjective
(`TauCeti.RelHomotopyGroup.surjective_hurewicz`).

This is half of the relative Hurewicz theorem in degree `n`. Unlike injectivity, it needs no
assumption on the fundamental group of `A`: under these hypotheses the relative Hurewicz map
identifies `Hₙ(X, A; ℤ)` with the quotient of `πₙ(X, A, a₀)` by the action of `π₁(A, a₀)`
(Hatcher, Theorem 4.37), which is trivial when `A` is simply connected.

## Proof

The proof is Eilenberg's deformation of singular chains, as for the vanishing of `Hₖ(X, A)` below
degree `n` (`TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`).

* By the compression lemma the singular cubes of `X` deform coherently into `A` below dimension
  `n` (`TauCeti.nonempty_subspaceCubeDeformation_of_relHomotopyGroup`). On relative normalized
  cubical chains the end of the deformation is chain homotopic to the identity, and it carries
  every `n`-cube to a cube whose faces, of dimension `n - 1`, lie in `A`. So every class of
  `Hₙ(X, A)` in cubical homology is a combination of classes of single `n`-cubes `c` sending the
  boundary of the cube into `A` (`TauCeti.SubspaceCubeDeformation.homologyπ_mem_of_cube`).
* Such a cube is a map of pairs `c : (Iⁿ, ∂Iⁿ) ⟶ (X, A)`, and its class is the image under `c_*`
  of the class of the fundamental cycle of `(Iⁿ, ∂Iⁿ)`
  (`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`). The comparison of relative
  cubical and simplicial chains is natural, so in singular homology every class of `Hₙ(X, A; ℤ)`
  is a combination of the images `c_*(x)` with `x ∈ Hₙ(Iⁿ, ∂Iⁿ; ℤ) ≅ ℤ`, that is, of integer
  multiples of the classes `c_*[Iⁿ]`.
* A map of pairs out of the cube is homotopic, through maps of pairs, to a relative cube at some
  point of `A` (`TauCeti.exists_homotopicWith_relGenLoop`), and transporting that relative cube
  along a path in `A` to `a₀` is another homotopy through maps of pairs
  (`TauCeti.RelGenLoop.HomotopyAlong.homotopicWith`). Hence `c_*[Iⁿ]` is the relative Hurewicz
  class of a relative cube at `a₀`
  (`TauCeti.RelHomotopyGroup.exists_hurewicz_eq_singularHomologyMap`), and every `c_*(x)` is a
  relative Hurewicz image
  (`TauCeti.RelHomotopyGroup.exists_hurewicz_apply_one_eq_singularHomologyMap`).

As the relative Hurewicz map is a homomorphism in degrees at least two, its image is a subgroup,
and it contains a set of generators of `Hₙ(X, A; ℤ)`.

## Main results

* `TauCeti.cubeBoundaryPairCycle`: the fundamental relative cycle of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`,
  sent by the map of pairs of a cube `c` to the class of `c`
  (`TauCeti.homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle`).
* `TauCeti.RelHomotopyGroup.exists_hurewicz_eq_singularHomologyMap`: when `A` is path connected,
  the image of the generator of `Hₙ(Iⁿ, ∂Iⁿ)` under a cube sending the boundary of the cube into
  `A` is a relative Hurewicz class at any point of `A`.
* `TauCeti.RelHomotopyGroup.surjective_hurewicz`: the relative Hurewicz map
  `πₙ₊₂(X, A, a₀) → Hₙ₊₂(X, A; ℤ)` is surjective when `A` is path connected and the pair is
  `(n + 1)`-connected.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains of a highly connected pair.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Theorem 4.32 (the relative Hurewicz theorem) and Theorem 4.37.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Set
open scoped unitInterval Topology

universe u

namespace TauCeti

/-! ### The fundamental cycle of the cube pair -/

section CubeBoundaryPair

variable (k : Type u) [Ring k]

/-- The identity cube `upCube m` sends the boundary of `Iᵐ` into the subspace `∂Iᵐ` of the cube
pair. -/
lemma mapsTo_upCube_boundary (m : ℕ) :
    MapsTo (upCube.{u} m : SingularCube (cubeBoundaryPair.{u} m).fst m) (Cube.boundary (Fin m))
      (range (cubeBoundaryPair.{u} m).map) :=
  fun y hy ↦ ⟨⟨ULift.up y, hy⟩, rfl⟩

/-- The fundamental relative cycle of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`: the identity cube `upCube`,
as a relative cycle of the normalized cubical chains with coefficients in `k`. -/
def cubeBoundaryPairCycle (m : ℕ) :
    ((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).cycles (m + 1) :=
  TopPair.cubicalCycleOfCube k _ (mapsTo_upCube_boundary (m + 1))

/-- The map of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` given by a cube `c` sends the class of the fundamental
cycle of the cube pair to the class of `c` in relative cubical homology. -/
theorem homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle {P : TopPair.{u}} {m : ℕ}
    (c : SingularCube P.fst (m + 1)) (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (cubeBoundaryPairHom c hc)) (m + 1)
        (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) =
      (P.cubicalChainComplex k).homologyπ (m + 1) (TopPair.cubicalCycleOfCube k c hc) := by
  -- The cube `c ∘ upCube` is `c`.
  have hcid : (TopPair.Hom.fst (cubeBoundaryPairHom c hc)).hom.comp
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1)) = c :=
    ContinuousMap.ext fun y ↦ cubeBoundaryPairHom_fst_apply c hc _
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  exact congrArg _ ((TopPair.cyclesMap_cubicalCycleOfCube k _ _ _ (by rw [hcid]; exact hc)).trans
    (by congr 1))

end CubeBoundaryPair

variable {Y : TopCat.{0}} {B : Set Y}

namespace RelHomotopyGroup

/-! ### Cubes with boundary in the subspace -/

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The class of a cube with boundary in a path-connected subspace is a relative Hurewicz
class.** If `B` is path connected and `b ∈ B`, then for every singular `(n + 1)`-cube `c` sending
the boundary of the cube into `B`, the image under `c : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (Y, B)` of the generator
of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` is the relative Hurewicz class of a relative cube at `b`. -/
theorem exists_hurewicz_eq_singularHomologyMap (b : B) (hB : IsPathConnected B) {n : ℕ}
    (c : SingularCube (TopPair.ofSubset B).fst (n + 1))
    (hc : MapsTo c (Cube.boundary (Fin (n + 1))) (range (TopPair.ofSubset B).map)) :
    ∃ a : RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset B, b⟩,
      hurewicz R n a =
        (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
          TopPair.singularHomologyMap (cubeBoundaryPairHom c hc) R (n + 1) := by
  -- Read `c` on `I × Iⁿ` and deform it, through maps of pairs, to a relative cube at some `b'`.
  let g : C(I × (I^(Fin n)), Y) := c.comp ((cubeSplitHomeomorph n).symm : C(_, _))
  have hg : MapsTo g (Cube.prodBoundary (Fin n)) B := fun x hx ↦ by
    have := hc (cubeSplitHomeomorph_symm_mem_boundary hx)
    rwa [TopPair.range_ofSubset_map] at this
  obtain ⟨b', -, p, hgp⟩ := exists_homotopicWith_relGenLoop g hg
  -- Transport that relative cube along a path in `B` from `b'` to `b`.
  let γ : Path b' b := (hB.joinedIn _ b'.2 _ b.2).joined_subtype.somePath
  let q := RelGenLoop.transport γ p
  have hpq := (RelGenLoop.collarHomotopyAlong γ p).homotopicWith
  rw [TopPair.range_ofSubset_map] at hpq
  refine ⟨RelHomotopyGroup.mk q, ?_⟩
  rw [RelHomotopyGroup.hurewicz_mk, RelGenLoop.hurewicz_def]
  congr 1
  -- The relative cube `q` is homotopic to `g`, that is to `c`, through maps of pairs.
  have H : q.1.HomotopicWith g
      fun f ↦ MapsTo f (Cube.prodBoundary (Fin n)) (range (TopPair.ofSubset B).map) := by
    rw [TopPair.range_ofSubset_map]
    exact (hgp.trans hpq).symm
  have hcg : g.comp (cubeSplitHomeomorph n : C(_, _)) = c :=
    ContinuousMap.ext fun z ↦ congrArg c ((cubeSplitHomeomorph n).symm_apply_apply z)
  rw [RelGenLoop.toCubeBoundaryPairHom_def]
  convert singularHomologyMap_cubeBoundaryPairHom_eq R H
    (RelGenLoop.mapsTo_comp_cubeSplitHomeomorph q) (hcg ▸ hc) (n + 1) using 3
  exact hcg.symm

/-! ### Surjectivity of the relative Hurewicz map -/

/-- Over `ℤ`, if `B` is path connected and `b ∈ B`, then for every singular `(n + 2)`-cube `c`
sending the boundary of the cube into `B`, the image of every class of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ)` under
`c : (Iⁿ⁺², ∂Iⁿ⁺²) ⟶ (Y, B)` is the relative Hurewicz image of a class of `πₙ₊₂(Y, B, b)`. -/
theorem exists_hurewicz_apply_one_eq_singularHomologyMap (b : B) (hB : IsPathConnected B) {n : ℕ}
    (c : SingularCube (TopPair.ofSubset B).fst (n + 2))
    (hc : MapsTo c (Cube.boundary (Fin (n + 2))) (range (TopPair.ofSubset B).map))
    (x : ((cubeBoundaryPair.{0} (n + 2)).singularHomology (ModuleCat.of ℤ ℤ) (n + 2) :
      ModuleCat ℤ)) :
    ∃ a : RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩,
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 =
        TopPair.singularHomologyMap (cubeBoundaryPairHom c hc) (ModuleCat.of ℤ ℤ) (n + 2) x := by
  let R := ModuleCat.of ℤ ℤ
  obtain ⟨a, ha⟩ := exists_hurewicz_eq_singularHomologyMap R b hB c hc
  -- `x` is an integer multiple of the generator of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`.
  let e := singularHomologyCubeBoundaryPairIso R (n + 2)
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, k • e.inv (1 : ℤ) = x :=
    ⟨e.hom x, by rw [← map_zsmul, smul_eq_mul, mul_one, Iso.hom_inv_id_apply]⟩
  refine ⟨(k • Additive.ofMul a).toMul, ?_⟩
  rw [← hurewiczHom_apply, map_zsmul, ModuleCat.hom_zsmul, map_zsmul, hurewiczHom_apply,
    toMul_ofMul, ha]
  rfl

/-- **The relative Hurewicz map is surjective.** Let `B` be a path-connected subset of `Y` and
`b ∈ B`. If every point of `Y` is joined by a path to a point of `B`, and the relative homotopy set
`π_{k+1}(Y, B, b)` is trivial for every `k + 1 < n + 2`, then the relative Hurewicz map
`πₙ₊₂(Y, B, b) → Hₙ₊₂(Y, B; ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`, is surjective. -/
theorem surjective_hurewicz (b : B) {n : ℕ} (h₀ : ∀ y : Y, ∃ a ∈ B, Joined y a)
    (hB : IsPathConnected B)
    (h : ∀ k : ℕ, k + 1 < n + 2 →
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset B, b⟩)) :
    Function.Surjective fun a : RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩ ↦
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 := by
  let R := ModuleCat.of ℤ ℤ
  -- The image of the relative Hurewicz homomorphism, evaluated at `1`, is a subgroup.
  let φ : Additive (RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩) →+
      ↑((TopPair.ofSubset B).singularHomology R (n + 2) : ModuleCat ℤ) :=
    { toFun a := (hurewiczHom R n a).hom 1
      map_zero' := by simp
      map_add' a a' := by simp }
  -- The relative homotopy sets vanish at every point of `B`, by base-point change.
  have h' (k : ℕ) (hk : k + 1 < n + 2) (a : B) :
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset B, a⟩) :=
    have := h k hk
    (equivOfPath (N := Fin k) (X := ⟨TopPair.ofSubset B, b⟩)
      (hB.joinedIn _ b.2 _ a.2).joined_subtype.somePath).symm.subsingleton
  obtain ⟨D⟩ := nonempty_subspaceCubeDeformation_of_relHomotopyGroup (n := (n + 2 : ℕ)) h₀
    fun k hk ↦ h' k (by exact_mod_cast hk)
  rw [← TopPair.range_ofSubset_map (B := B)] at D
  intro y
  let iso := TopPair.singularCubicalHomologyIso ℤ (TopPair.ofSubset B) (n + 2)
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ _ (iso.hom y)
  -- The preimage of the image of the relative Hurewicz homomorphism, as a submodule of relative
  -- cubical homology.
  let T : Submodule ℤ (((TopPair.ofSubset B).cubicalChainComplex ℤ).homology (n + 2)) :=
    { φ.range.comap iso.inv.hom.toAddMonoidHom with
      smul_mem' k x hx := by
        have := (φ.range.comap iso.inv.hom.toAddMonoidHom).zsmul_mem hx k
        rwa [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] at this }
  have hmem := D.homologyπ_mem_of_cube ℤ (m := n + 1) (by exact_mod_cast Nat.lt_succ_self _) T
      (fun c hc ↦ by
    rw [← homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle ℤ c hc]
    refine AddSubgroup.mem_comap.2 ?_
    -- Relative cubical and singular homology are naturally isomorphic.
    rw [LinearMap.toAddMonoidHom_coe, ← ModuleCat.comp_apply,
      TopPair.singularCubicalHomologyIso_inv_naturality, ModuleCat.comp_apply]
    exact (exists_hurewicz_apply_one_eq_singularHomologyMap b hB c hc _).elim
      fun a ha ↦ ⟨Additive.ofMul a,
        (congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) (hurewiczHom_apply R n _)).trans ha⟩) z
  have hmem' := AddSubgroup.mem_comap.1 hmem
  rw [LinearMap.toAddMonoidHom_coe, hz, Iso.hom_inv_id_apply] at hmem'
  obtain ⟨a, rfl⟩ := hmem'
  exact ⟨a.toMul, (congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) (hurewiczHom_apply R n a)).symm⟩

end RelHomotopyGroup

end TauCeti
