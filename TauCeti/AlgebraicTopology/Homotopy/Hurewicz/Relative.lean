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
  boundary of the cube into `A`.
* Such a cube is a map of pairs `c : (Iⁿ, ∂Iⁿ) ⟶ (X, A)`, and its class is the image under `c_*`
  of a class of `Hₙ(Iⁿ, ∂Iⁿ)`. The comparison of relative cubical and simplicial chains is natural,
  so in singular homology every class of `Hₙ(X, A; ℤ)` is a combination of the images
  `c_*(x)` with `x ∈ Hₙ(Iⁿ, ∂Iⁿ; ℤ) ≅ ℤ`, that is, of integer multiples of the classes
  `c_*[Iⁿ]`.
* A map of pairs out of the cube is homotopic, through maps of pairs, to a relative cube at some
  point of `A` (`TauCeti.exists_homotopicWith_relGenLoop`), and transporting that relative cube
  along a path in `A` to `a₀` is another homotopy through maps of pairs. Hence `c_*[Iⁿ]` is the
  relative Hurewicz class of a relative cube at `a₀`.

As the relative Hurewicz map is a homomorphism in degrees at least two, its image is a subgroup,
and it contains a set of generators of `Hₙ(X, A; ℤ)`.

## Main results

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

namespace TauCeti

variable {Y : TopCat.{0}} {B : Set Y}

/-! ### Singular cubes with boundary in the subspace -/

/-- A singular `m`-cube of the ambient space of a pair `P` sending the boundary of the cube into
the subspace, as a map of pairs `(Iᵐ, ∂Iᵐ) ⟶ P`. -/
private def cubePairHom {P : TopPair.{0}} {m : ℕ} (c : SingularCube P.fst m)
    (hc : MapsTo c (Cube.boundary (Fin m)) (range P.map)) : cubeBoundaryPair.{0} m ⟶ P :=
  TopPair.ofHom (TopCat.ofHom (c.comp ⟨ULift.down, continuous_uliftDown⟩))
    (TopCat.ofHom (P.liftSnd ((c.comp ⟨ULift.down, continuous_uliftDown⟩).comp
      ⟨Subtype.val, continuous_subtype_val⟩) fun z ↦ hc z.2))
    (by ext z; exact TopPair.map_liftSnd _ _ z)

@[simp]
private lemma cubePairHom_fst_apply {P : TopPair.{0}} {m : ℕ} (c : SingularCube P.fst m)
    (hc : MapsTo c (Cube.boundary (Fin m)) (range P.map)) (z : (cubeBoundaryPair.{0} m).fst) :
    TopPair.Hom.fst (cubePairHom c hc) z = c z.down :=
  (rfl)

/-- Split a point of `Iⁿ⁺¹` into its first coordinate and the remaining ones. -/
private def cubeSplit (n : ℕ) : C(ULift.{0} (I^(Fin (n + 1))), I × (I^(Fin n))) :=
  ⟨fun z ↦ (z.down 0, Fin.tail z.down), by fun_prop⟩

@[simp]
private lemma cubeSplit_apply {n : ℕ} (z : ULift.{0} (I^(Fin (n + 1)))) :
    cubeSplit n z = (z.down 0, Fin.tail z.down) :=
  (rfl)

private lemma cubeSplit_mem_prodBoundary {n : ℕ} {z : ULift.{0} (I^(Fin (n + 1)))}
    (hz : z.down ∈ Cube.boundary (Fin (n + 1))) : cubeSplit n z ∈ Cube.prodBoundary (Fin n) := by
  rw [Cube.mem_prodBoundary_iff]
  exact Cube.boundary_fin_succ_iff.1 hz

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The class of a cube with boundary in a path-connected subspace is a relative Hurewicz
class.** If `B` is path connected and `b ∈ B`, then for every singular `(n + 1)`-cube `c` sending
the boundary of the cube into `B`, the image under `c : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (Y, B)` of the generator
of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` is the relative Hurewicz class of a relative cube at `b`. -/
private theorem exists_hurewicz_eq (b : B) (hB : IsPathConnected B) {n : ℕ}
    (c : SingularCube (TopPair.ofSubset B).fst (n + 1))
    (hc : MapsTo c (Cube.boundary (Fin (n + 1))) (range (TopPair.ofSubset B).map)) :
    ∃ a : RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset B, b⟩,
      RelHomotopyGroup.hurewicz R n a =
        (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
          TopPair.singularHomologyMap (cubePairHom c hc) R (n + 1) := by
  -- Read `c` on `I × Iⁿ` and deform it, through maps of pairs, to a relative cube at some `b'`.
  rw [TopPair.range_ofSubset_map] at hc
  let g : C(I × (I^(Fin n)), Y) := c.comp ⟨fun x ↦ Fin.cons x.1 x.2, by fun_prop⟩
  have hg : MapsTo g (Cube.prodBoundary (Fin n)) B := fun x hx ↦ hc <|
    Cube.boundary_fin_succ_iff.2 (by simpa using hx)
  obtain ⟨b', -, p, hgp⟩ := exists_homotopicWith_relGenLoop g hg
  -- Transport that relative cube along a path in `B` from `b'` to `b`.
  let γ : Path b' b := (hB.joinedIn _ b'.2 _ b.2).joined_subtype.somePath
  let q := RelGenLoop.transport γ p
  have hpq : p.1.HomotopicWith q.1 fun f ↦ MapsTo f (Cube.prodBoundary (Fin n)) B := by
    let H := RelGenLoop.collarHomotopyAlong γ p
    refine ⟨{ toHomotopy := H.toHomotopy, prop' := fun t x hx ↦ ?_ }⟩
    simp only [ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe,
      ContinuousMap.Homotopy.coe_toContinuousMap]
    rcases Cube.mem_prodBoundary_iff.1 hx with (h | h) | h
    · have := H.apply_zero_mem_range t x.2
      rwa [TopPair.range_ofSubset_map, ← h] at this
    · rw [H.apply_eq_path t x.1 x.2 (.inl h)]
      exact (γ t).2
    · rw [H.apply_eq_path t x.1 x.2 (.inr h)]
      exact (γ t).2
  obtain ⟨F⟩ := hgp.trans hpq
  refine ⟨RelHomotopyGroup.mk q, ?_⟩
  rw [RelHomotopyGroup.hurewicz_mk, RelGenLoop.hurewicz_def]
  congr 1
  -- The homotopy `F`, read on `Iⁿ⁺¹`, is a homotopy of maps of pairs from `c` to `q`.
  have H := TopPair.ofSubsetHomotopy (X := TopCat.of (ULift.{0} (I^(Fin (n + 1)))))
    (B := ULift.down ⁻¹' Cube.boundary (Fin (n + 1))) (B' := B)
    (g₀ := TopCat.ofHom (g.comp (cubeSplit n))) (g₁ := TopCat.ofHom (q.1.comp (cubeSplit n)))
    (F.toHomotopy.compContinuousMap (cubeSplit n))
    fun τ z hz ↦ F.prop τ (cubeSplit_mem_prodBoundary (z := z) hz)
  refine (congrArg (TopPair.singularHomologyMap · R (n + 1)) ?_).trans
    ((H.congr_singularHomologyMap R (n + 1)).symm.trans
      (congrArg (TopPair.singularHomologyMap · R (n + 1)) ?_)) <;>
    refine TopPair.hom_ext_of_fst _ ?_
  · exact TopCat.ext fun z ↦ (RelGenLoop.toCubeBoundaryPairHom_fst_apply q z).trans
      (TopPair.ofSubsetMap_fst_apply (TopCat.ofHom (q.1.comp (cubeSplit n))) _ z).symm
  · exact TopCat.ext fun z ↦ (TopPair.ofSubsetMap_fst_apply _ _ z).trans
      ((congrArg c (Fin.cons_self_tail z.down)).trans (cubePairHom_fst_apply c _ z).symm)

/-! ### Relative cubical homology is generated by single cubes -/

section Cubical

variable {P : TopPair.{0}}

/-- The quotient map from the normalized cubical chains of the ambient space of `P` to the relative
normalized cubical chains of `P`. -/
private abbrev relπ (P : TopPair.{0}) :=
  cokernel.π ((normalizedCubicalChainComplex ℤ).map P.map)

/-- A singular cube of the ambient space of `P`, as a relative normalized cubical chain of `P`. -/
private abbrev relCube {m : ℕ} (c : SingularCube P.fst m) : (P.cubicalChainComplex ℤ).X m :=
  (relπ P).f m ((normalizedCubicalChainComplexXEquiv P.fst m).symm
    (NormalizedCubicalChain.ofCube P.fst ℤ c))

/-- A singular cube sending the boundary of the cube into the subspace is a relative cycle. -/
private lemma d_relCube {m : ℕ} {c : SingularCube P.fst (m + 1)}
    (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)) :
    (P.cubicalChainComplex ℤ).d (m + 1) m (relCube c) = 0 := by
  -- The boundary of `c` is a chain of the subspace, which vanishes in the relative chains.
  obtain ⟨a, ha⟩ :
      NormalizedCubicalChain.boundary P.fst ℤ m (NormalizedCubicalChain.ofCube P.fst ℤ c) ∈
        LinearMap.range (NormalizedCubicalChain.map ℤ P.map.hom m) := by
    rw [NormalizedCubicalChain.boundary_ofCube]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
      refine NormalizedCubicalChain.ofCube_mem_range_map ℤ P.isEmbedding_map.isInducing ?_ <;>
      rintro _ ⟨y, rfl⟩ <;>
      rw [SingularCube.face_apply] <;>
      exact hc ⟨i, by simp⟩
  have hd : ((normalizedCubicalChainComplex ℤ).obj P.fst).d (m + 1) m
      ((normalizedCubicalChainComplexXEquiv P.fst (m + 1)).symm
        (NormalizedCubicalChain.ofCube P.fst ℤ c)) =
        ((normalizedCubicalChainComplex ℤ).map P.map).f m
          ((normalizedCubicalChainComplexXEquiv P.snd m).symm a) :=
    (normalizedCubicalChainComplex_obj_d_apply P.fst m _).trans
      (ha.symm.trans (normalizedCubicalChainComplex_map_f_apply P.map m a).symm)
  rw [relCube, HomologicalComplex.Hom.comm_apply, hd]
  exact congr(ModuleCat.Hom.hom $(TopPair.cubicalChainComplex_condition_f ℤ P m) _)

/-- The identity map of `Iᵐ`, as a singular cube of the cube pair `(Iᵐ, ∂Iᵐ)`. -/
private def idCube (m : ℕ) : SingularCube (cubeBoundaryPair.{0} m).fst m :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- The identity cube, as a relative cycle of the cube pair `(Iᵐ⁺¹, ∂Iᵐ⁺¹)`. -/
private def idCubeCycle (m : ℕ) :
    ((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).cycles (m + 1) :=
  HomologicalComplex.moduleCatCyclesMk _ (relCube (idCube (m + 1))) m (by simp)
    (d_relCube fun y hy ↦ ⟨⟨ULift.up y, hy⟩, rfl⟩)

/-- The map of pairs given by a cube `c` sends the identity cube to `c`. -/
private lemma cubicalChainComplexMap_f_relCube_idCube {m : ℕ} (c : SingularCube P.fst m)
    (hc : MapsTo c (Cube.boundary (Fin m)) (range P.map)) :
    (TopPair.cubicalChainComplexMap ℤ (cubePairHom c hc)).f m (relCube (idCube m)) =
      relCube c := by
  rw [relCube, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    TopPair.π_cubicalChainComplexMap, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  -- The cube `c ∘ idCube` is `c`, by the definitions of `cubePairHom` and `idCube`.
  exact congrArg _ ((normalizedCubicalChainComplex_map_f_apply _ m _).trans
    (NormalizedCubicalChain.map_ofCube ℤ _ _))

/-- **Every class of relative cubical homology in degree `m + 1` comes from single cubes.** If the
singular cubes of the ambient space of `P` deform into the subspace below dimension `m + 1`, then
every subgroup of the relative normalized cubical homology `H^□ₘ₊₁(P)` containing the images of the
class of the identity cube under all maps of pairs `c : (Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ P` given by singular cubes
is everything. -/
private theorem homologyπ_mem {m : ℕ}
    (D : SubspaceCubeDeformation (range P.map) (m + 1 : ℕ))
    (T : AddSubgroup ((P.cubicalChainComplex ℤ).homology (m + 1)))
    (hT : ∀ (c : SingularCube P.fst (m + 1))
      (hc : MapsTo c (Cube.boundary (Fin (m + 1))) (range P.map)),
      HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap ℤ (cubePairHom c hc)) (m + 1)
        (((cubeBoundaryPair.{0} (m + 1)).cubicalChainComplex ℤ).homologyπ (m + 1)
          (idCubeCycle m)) ∈ T)
    (z : (P.cubicalChainComplex ℤ).cycles (m + 1)) :
    (P.cubicalChainComplex ℤ).homologyπ (m + 1) z ∈ T := by
  -- The end of the deformation carries every `(m + 1)`-cube to a cube with boundary in the
  -- subspace.
  have hend (c : SingularCube P.fst (m + 1)) :
      MapsTo (D.endCube c) (Cube.boundary (Fin (m + 1))) (range P.map) := by
    rintro y ⟨i, hi⟩
    rw [SubspaceCubeDeformation.endCube_apply, ← Fin.insertNth_self_removeNth i y,
      D.homotopy_insertNth c i hi]
    exact D.homotopy_one_mem (by exact_mod_cast Nat.lt_succ_self m) _ _
  -- The end of the deformation, followed by the projection to relative chains, has values in
  -- relative cycles.
  let j : NormalizedCubicalChain P.fst ℤ (m + 1) →ₗ[ℤ] (P.cubicalChainComplex ℤ).X (m + 1) :=
    ((relπ P).f (m + 1)).hom ∘ₗ
      (normalizedCubicalChainComplexXEquiv P.fst (m + 1)).symm.toLinearMap ∘ₗ
        D.endChain ℤ (m + 1)
  have hj (g : NormalizedCubicalChain P.fst ℤ (m + 1)) :
      (P.cubicalChainComplex ℤ).d (m + 1) m (j g) = 0 := by
    induction g using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | smul r a ha => simp [ha]
    | ofCube c =>
      simp only [j, LinearMap.comp_apply, SubspaceCubeDeformation.endChain_ofCube]
      exact d_relCube (hend c)
  have hΦ (g : NormalizedCubicalChain P.fst ℤ (m + 1)) :
      (P.cubicalChainComplex ℤ).moduleCatHomologyClass (by simp) j hj g ∈ T := by
    induction g using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using T.add_mem ha hb
    | smul r a ha => simpa only [map_zsmul] using T.zsmul_mem ha r
    | ofCube c =>
      rw [HomologicalComplex.moduleCatHomologyClass_apply]
      convert hT (D.endCube c) (hend c) using 1
      rw [idCubeCycle, HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
      congr 1
      apply (P.cubicalChainComplex ℤ).moduleCat_iCycles_injective
      simp only [HomologicalComplex.iCycles_moduleCatCyclesMk, j, LinearMap.comp_apply,
        SubspaceCubeDeformation.endChain_ofCube, cubicalChainComplexMap_f_relCube_idCube, relCube,
        LinearEquiv.coe_coe]
  -- The end of the deformation induces the identity on homology.
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective ((relπ P).f (m + 1))).1 inferInstance
    ((P.cubicalChainComplex ℤ).iCycles (m + 1) z)
  have hz : z = (P.cubicalChainComplex ℤ).moduleCatCyclesMk
      ((P.cubicalChainComplex ℤ).iCycles (m + 1) z) m (by simp)
      (by rw [← ModuleCat.comp_apply, (P.cubicalChainComplex ℤ).iCycles_d]; rfl) :=
    (P.cubicalChainComplex ℤ).moduleCat_iCycles_injective _ (by simp)
  have hid := congr(ModuleCat.Hom.hom $((D.relEndHomotopy ℤ).homologyMap_eq (m + 1))
    ((P.cubicalChainComplex ℤ).homologyπ (m + 1) z))
  rw [HomologicalComplex.homologyMap_id, ModuleCat.id_apply] at hid
  rw [hid, hz, HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  have hw' := hΦ (normalizedCubicalChainComplexXEquiv P.fst (m + 1) w)
  rw [HomologicalComplex.moduleCatHomologyClass_apply] at hw'
  convert hw' using 2
  apply (P.cubicalChainComplex ℤ).moduleCat_iCycles_injective
  simp only [HomologicalComplex.iCycles_moduleCatCyclesMk, j, LinearMap.comp_apply, ← hw]
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    SubspaceCubeDeformation.π_relEndChainMap, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  exact congrArg _ (D.endChainMap_f_apply ℤ (m + 1) w)

end Cubical

/-! ### Surjectivity of the relative Hurewicz map -/

namespace RelHomotopyGroup

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
  -- The image under a cube `c` of a class of `Hₙ₊₂(Iⁿ⁺², ∂Iⁿ⁺²; ℤ) ≅ ℤ` is an integer multiple of a
  -- relative Hurewicz class.
  have hcube (c : SingularCube (TopPair.ofSubset B).fst (n + 2))
      (hc : MapsTo c (Cube.boundary (Fin (n + 2))) (range (TopPair.ofSubset B).map))
      (x : ((cubeBoundaryPair.{0} (n + 2)).singularHomology R (n + 2) : ModuleCat ℤ)) :
      TopPair.singularHomologyMap (cubePairHom c hc) R (n + 2) x ∈ φ.range := by
    obtain ⟨a, ha⟩ := exists_hurewicz_eq R b hB c hc
    let e := singularHomologyCubeBoundaryPairIso R (n + 2)
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, k • e.inv (1 : ℤ) = x :=
      ⟨e.hom x, by rw [← map_zsmul, smul_eq_mul, mul_one, Iso.hom_inv_id_apply]⟩
    refine ⟨k • Additive.ofMul a, ?_⟩
    rw [map_zsmul, map_zsmul]
    congr 1
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) ((hurewiczHom_apply R n _).trans ha)
  intro y
  let iso := TopPair.singularCubicalHomologyIso ℤ (TopPair.ofSubset B) (n + 2)
  obtain ⟨z, hz⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ _ (iso.hom y)
  have hmem := homologyπ_mem D (φ.range.comap iso.inv.hom.toAddMonoidHom) (fun c hc ↦ by
    -- Relative cubical and singular homology are naturally isomorphic.
    have hnat : HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap ℤ (cubePairHom c hc)) (n + 2) ≫ iso.inv =
          (TopPair.singularCubicalHomologyIso ℤ _ (n + 2)).inv ≫
            TopPair.singularHomologyMap (cubePairHom c hc) R (n + 2) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, TopPair.singularCubicalHomologyIso_hom_naturality,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, ← ModuleCat.comp_apply, hnat,
      ModuleCat.comp_apply]
    exact hcube c hc _) z
  rw [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, hz, Iso.hom_inv_id_apply] at hmem
  obtain ⟨a, rfl⟩ := hmem
  exact ⟨a.toMul, (congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) (hurewiczHom_apply R n a)).symm⟩

end RelHomotopyGroup

end TauCeti
