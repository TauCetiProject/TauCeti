/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Relative.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Hurewicz
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.CubePair
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Relative

/-!
# Surjectivity of the relative Hurewicz map, and the isomorphism for highly connected spaces

Let `A` be a path-connected subspace of a space `X` and `a₀ ∈ A`. Suppose that every point of `X`
is joined by a path to a point of `A`, and that the relative homotopy sets `πₖ(X, A, a₀)` are
trivial for `0 < k < n`, where `n ≥ 2`. This file proves that the relative Hurewicz map
`πₙ(X, A, a₀) → Hₙ(X, A; ℤ)`, `[p] ↦ p_*[Iⁿ]`, is surjective
(`TauCeti.RelHomotopyGroup.surjective_hurewicz`).

This is half of the relative Hurewicz theorem in degree `n`. Unlike injectivity, it needs no
assumption on the fundamental group of `A`: under these hypotheses the relative Hurewicz map
identifies `Hₙ(X, A; ℤ)` with the quotient of `πₙ(X, A, a₀)` by the action of `π₁(A, a₀)`
(Hatcher, Theorem 4.37), which is trivial when `A` is simply connected.

The file then proves injectivity, and so the relative Hurewicz isomorphism in degree `n`, when
`A` and `X` are both `(n - 1)`-connected
(`TauCeti.RelHomotopyGroup.bijective_hurewicz_of_subsingleton_homotopyGroup`). In degree two
this is the full relative Hurewicz theorem: if `A` and `X` are simply connected, then
`π₂(X, A, a₀)`, which is commutative (`TauCeti.RelHomotopyGroup.mul_comm_of_subsingleton`), is
isomorphic to `H₂(X, A; ℤ)`. The proof of injectivity is a diagram chase. As `πₙ₋₁(A, a₀)` is
trivial, every relative class comes from `πₙ(X, a₀)`; the relative Hurewicz map extends the
absolute one (`TauCeti.RelHomotopyGroup.hurewicz_ofHomotopyGroup`), and the absolute Hurewicz
theorem for `A` and `X` (`HomotopyGroup.bijective_hurewicz`), together with exactness of the
homology sequence of the pair at `Hₙ(X; ℤ)`, shows that a class in the kernel comes from
`πₙ(A, a₀)`, hence is trivial in `πₙ(X, A, a₀)`. For `n ≥ 3` the relative Hurewicz theorem only
needs `A` to be simply connected; that case is not covered here.

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
  (`TauCeti.RelHomotopyGroup.exists_hurewicz_apply_one_eq_singularHomologyMap`). So the class of
  every such cube, read in singular homology, is a relative Hurewicz image
  (`TauCeti.RelHomotopyGroup.exists_hurewicz_apply_one_eq_singularCubicalHomologyIso_inv`).

As the relative Hurewicz map is a homomorphism in degrees at least two
(`TauCeti.RelHomotopyGroup.hurewiczIntHom`), its image is a subgroup, and it contains a set of
generators of `Hₙ(X, A; ℤ)`.

## Main results

* `TauCeti.RelHomotopyGroup.exists_hurewicz_eq_singularHomologyMap`: when `A` is path connected,
  the image of the generator of `Hₙ(Iⁿ, ∂Iⁿ)` under a cube sending the boundary of the cube into
  `A` is a relative Hurewicz class at any point of `A`.
* `TauCeti.RelHomotopyGroup.surjective_hurewicz`: the relative Hurewicz map
  `πₙ₊₂(X, A, a₀) → Hₙ₊₂(X, A; ℤ)` is surjective when `A` is path connected and the pair is
  `(n + 1)`-connected.
* `TauCeti.RelHomotopyGroup.injective_hurewicz_of_subsingleton_homotopyGroup`,
  `TauCeti.RelHomotopyGroup.bijective_hurewicz_of_subsingleton_homotopyGroup`: the relative
  Hurewicz map `πₙ₊₂(X, A, a₀) → Hₙ₊₂(X, A; ℤ)` is injective, and bijective, when `A` and `X`
  are `(n + 1)`-connected.
* `TauCeti.RelHomotopyGroup.hurewiczAddEquivOfSubsingletonHomotopyGroup`: the resulting additive
  isomorphism `πₙ₊₂(X, A, a₀) ≃ Hₙ₊₂(X, A; ℤ)`.

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

namespace RelHomotopyGroup

/-! ### Cubes with boundary in the subspace -/

section Coefficients

variable {Y : TopCat.{u}} {B : Set Y}
variable {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C)

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

end Coefficients

/-! ### Surjectivity of the relative Hurewicz map -/

variable {Y : TopCat.{0}} {B : Set Y}

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
  obtain ⟨a, ha⟩ := exists_hurewicz_eq_singularHomologyMap (ModuleCat.of ℤ ℤ) b hB c hc
  -- `x` is an integer multiple of the generator of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ`.
  let e := singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) (n + 2)
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, k • e.inv (1 : ℤ) = x :=
    ⟨e.hom x, by rw [← map_zsmul, smul_eq_mul, mul_one, Iso.hom_inv_id_apply]⟩
  refine ⟨(k • Additive.ofMul a).toMul, ?_⟩
  rw [← hurewiczIntHom_apply, map_zsmul, hurewiczIntHom_apply, toMul_ofMul, ha, map_zsmul,
    ModuleCat.comp_apply]

/-- Over `ℤ`, if `B` is path connected and `b ∈ B`, then the class of every singular `(n + 2)`-cube
`c` sending the boundary of the cube into `B`, read in relative singular homology
`Hₙ₊₂(Y, B; ℤ)`, is the relative Hurewicz image of a class of `πₙ₊₂(Y, B, b)`. -/
theorem exists_hurewicz_apply_one_eq_singularCubicalHomologyIso_inv (b : B)
    (hB : IsPathConnected B) {n : ℕ} (c : SingularCube (TopPair.ofSubset B).fst (n + 2))
    (hc : MapsTo c (Cube.boundary (Fin (n + 2))) (range (TopPair.ofSubset B).map)) :
    ∃ a : RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩,
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 =
        (TopPair.singularCubicalHomologyIso ℤ (TopPair.ofSubset B) (n + 2)).inv
          (((TopPair.ofSubset B).cubicalChainComplex ℤ).homologyπ (n + 2)
            (TopPair.cubicalCycleOfCube ℤ c hc)) := by
  -- Relative cubical and singular homology are naturally isomorphic.
  rw [← homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle ℤ c hc, ← ModuleCat.comp_apply,
    TopPair.singularCubicalHomologyIso_inv_naturality, ModuleCat.comp_apply]
  exact exists_hurewicz_apply_one_eq_singularHomologyMap b hB c hc _

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
  -- The relative homotopy sets vanish at every point of `B`, by base-point change.
  obtain ⟨D⟩ := nonempty_subspaceCubeDeformation_of_relHomotopyGroup (n := (n + 2 : ℕ)) h₀
    fun k hk a ↦ (subsingleton_iff_of_joined (N := Fin k) (X := ⟨TopPair.ofSubset B, b⟩)
      (hB.joinedIn _ b.2 _ a.2).joined_subtype).1 (h k (by exact_mod_cast hk))
  rw [← TopPair.range_ofSubset_map (B := B)] at D
  intro y
  let iso := TopPair.singularCubicalHomologyIso ℤ (TopPair.ofSubset B) (n + 2)
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ _ (iso.hom y)
  -- The preimage of the image of the relative Hurewicz homomorphism, as a submodule of relative
  -- cubical homology. `AddSubgroup.toIntSubmodule` would use the `ℤ`-action
  -- `AddCommGroup.toIntModule`, which is not definitionally the `ModuleCat ℤ` action, so
  -- `smul_mem'` rewrites the latter (`Int.cast_smul_eq_zsmul`) into the `zsmul` of `zsmul_mem`.
  let S := (hurewiczIntHom ⟨TopPair.ofSubset B, b⟩ n).range.comap iso.inv.hom.toAddMonoidHom
  let T : Submodule ℤ (((TopPair.ofSubset B).cubicalChainComplex ℤ).homology (n + 2)) :=
    { S with
      smul_mem' k x hx := by
        have := S.zsmul_mem hx k
        rwa [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] at this }
  have hmem := D.homologyπ_mem_of_cube ℤ (m := n + 1) (by exact_mod_cast Nat.lt_succ_self _) T
    (fun c hc ↦ (exists_hurewicz_apply_one_eq_singularCubicalHomologyIso_inv b hB c hc).elim
      fun a ha ↦ ⟨Additive.ofMul a, (hurewiczIntHom_apply _ n _).trans ha⟩) z
  obtain ⟨a, ha⟩ := AddSubgroup.mem_comap.1 hmem
  rw [LinearMap.toAddMonoidHom_coe, hz, Iso.hom_inv_id_apply] at ha
  exact ⟨a.toMul, (hurewiczIntHom_apply _ n a).symm.trans ha⟩

/-! ### The relative Hurewicz isomorphism for highly connected pairs -/

section Isomorphism

variable {X : BasedTopPair.{0}} {n : ℕ}

/-- **Injectivity of the relative Hurewicz map for highly connected spaces.** If `πₖ(A, a₀)` and
`πₖ(X, a₀)` are trivial for every `k < n + 2`, then the relative Hurewicz map
`πₙ₊₂(X, A, a₀) → Hₙ₊₂(X, A; ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`, is injective. In degree two, that is for
`n = 0`, the hypotheses say that `A` and `X` are simply connected. -/
theorem injective_hurewicz_of_subsingleton_homotopyGroup
    (hA : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X.pair.snd X.basepoint))
    (hX : ∀ k < n + 2,
      Subsingleton (HomotopyGroup (Fin k) X.pair.fst (X.pair.map X.basepoint))) :
    Function.Injective fun a : RelHomotopyGroup (Fin (n + 1)) X ↦
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 := by
  let R := ModuleCat.of ℤ ℤ
  let e := HomotopyGroup.congrEquiv (X := X.pair.fst) (x := X.pair.map X.basepoint)
    (finSuccEquiv (n + 1))
  -- The relative Hurewicz map is additive, so it is enough to show that its kernel is trivial.
  suffices h : ∀ a : RelHomotopyGroup (Fin (n + 1)) X,
      (hurewicz R (n + 1) a).hom 1 = 0 → a = 1 by
    have := ((injective_iff_map_eq_zero (hurewiczIntHom X n)).2 fun a ha ↦
      congrArg Additive.ofMul (h a.toMul (by simpa using ha))).comp Additive.ofMul.injective
    simpa [Function.comp_def] using this
  intro a ha
  -- As `πₙ₊₁(A, a₀)` is trivial, `a` comes from a class `α` of `πₙ₊₂(X, a₀)`.
  obtain ⟨α, rfl⟩ := surjective_ofHomotopyGroup_of_subsingleton (hA (n + 1) (by lia)) a
  rw [hurewicz_ofHomotopyGroup] at ha
  -- So the absolute Hurewicz class of `α` lies in the kernel of `Hₙ₊₂(X; ℤ) ⟶ Hₙ₊₂(X, A; ℤ)`.
  -- The composite with this quotient map unfolds to function application.
  have ha' : (X.pair.singularHomologyπ R (n + 2)).hom
      ((HomotopyGroup.hurewicz R (n + 1) (e.symm α)).hom 1) = 0 := ha
  -- By exactness of the homology sequence of the pair, that class comes from `Hₙ₊₂(A; ℤ)`, and
  -- hence from the Hurewicz class of some `γ ∈ πₙ₊₂(A, a₀)`.
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (X.pair.singularHomology_exact_space R (n + 2)) ha'
  obtain ⟨γ, rfl⟩ := (HomotopyGroup.bijective_hurewicz hA).2 y
  -- The Hurewicz map of `X` is injective, so `α` is the image of `γ`, which dies in
  -- `πₙ₊₂(X, A, a₀)`.
  have hγ : HomotopyGroup.map X.pair.map.hom rfl γ = e.symm α :=
    (HomotopyGroup.bijective_hurewicz hX).1 <| by
      beta_reduce
      rw [HomotopyGroup.hurewicz_map]
      exact hy
  rw [← e.apply_symm_apply α, ← hγ, ← HomotopyGroup.map_congrEquiv,
    ofHomotopyGroup_homotopyGroupMap, one_eq_default]

/-- **The relative Hurewicz isomorphism for highly connected spaces.** Let `B` be a subspace of
`Y` and `b ∈ B`. If `πₖ(B, b)` and `πₖ(Y, b)` are trivial for every `k < n + 2`, then the
relative Hurewicz map `πₙ₊₂(Y, B, b) → Hₙ₊₂(Y, B; ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`, is bijective. In degree
two, that is for `n = 0`, the hypotheses say that `B` and `Y` are simply connected. -/
theorem bijective_hurewicz_of_subsingleton_homotopyGroup (b : B)
    (hB : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) B b))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y b)) :
    Function.Bijective fun a : RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩ ↦
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 := by
  refine ⟨injective_hurewicz_of_subsingleton_homotopyGroup hB hY, ?_⟩
  -- Triviality of `π₀` makes `B` and `Y` path connected.
  have hpc {Z : Type} [TopologicalSpace Z] [Nonempty Z] {z : Z}
      (h : Subsingleton (HomotopyGroup (Fin 0) Z z)) : PathConnectedSpace Z :=
    pathConnectedSpace_iff_zerothHomotopy.2
      ⟨inferInstance, (HomotopyGroup.pi0EquivZerothHomotopy (x := z)).symm.subsingleton⟩
  have : Nonempty B := ⟨b⟩
  have : Nonempty Y := ⟨b⟩
  have : PathConnectedSpace Y := hpc (hY 0 (by lia))
  -- The relative homotopy sets below degree `n + 2` vanish, by the exact homotopy sequence.
  refine surjective_hurewicz b (fun y ↦ ⟨b, b.2, PathConnectedSpace.joined y b⟩)
    (isPathConnected_iff_pathConnectedSpace.2 (hpc (hB 0 (by lia)))) fun k hk ↦
      subsingleton_of_subsingleton_homotopyGroup (hB k (by lia)) ?_
  exact @Equiv.subsingleton _ _ (HomotopyGroup.congrEquiv (finSuccEquiv k)).symm
    (hY (k + 1) (by lia))

/-- **The relative Hurewicz isomorphism** `πₙ₊₂(Y, B, b) ≃ Hₙ₊₂(Y, B; ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`,
when `πₖ(B, b)` and `πₖ(Y, b)` are trivial for every `k < n + 2`. In degree two, where `B` and `Y`
are simply connected, this identifies `π₂(Y, B, b)`, which is then commutative
(`TauCeti.RelHomotopyGroup.mul_comm_of_subsingleton`), with `H₂(Y, B; ℤ)`. -/
def hurewiczAddEquivOfSubsingletonHomotopyGroup (b : B)
    (hB : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) B b))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y b)) :
    Additive (RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩) ≃+
      ↑((TopPair.ofSubset B).singularHomology (ModuleCat.of ℤ ℤ) (n + 2) : ModuleCat ℤ) :=
  AddEquiv.ofBijective (hurewiczIntHom _ n) <| by
    convert (bijective_hurewicz_of_subsingleton_homotopyGroup b hB hY).comp
      Additive.toMul.bijective using 1
    funext a
    exact hurewiczIntHom_apply _ n a

@[simp]
theorem hurewiczAddEquivOfSubsingletonHomotopyGroup_apply (b : B)
    (hB : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) B b))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y b))
    (a : Additive (RelHomotopyGroup (Fin (n + 1)) ⟨TopPair.ofSubset B, b⟩)) :
    hurewiczAddEquivOfSubsingletonHomotopyGroup b hB hY a =
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a.toMul).hom 1 :=
  (AddEquiv.ofBijective_apply _ _ a).trans (hurewiczIntHom_apply _ n a)

end Isomorphism

end RelHomotopyGroup

end TauCeti
