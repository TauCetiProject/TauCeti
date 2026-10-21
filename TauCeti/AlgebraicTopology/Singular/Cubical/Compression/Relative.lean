/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction

/-!
# Relative homology vanishes below the connectivity of a pair

Let `A` be a subspace of `X` such that every point of `X` is joined by a path to `A` and the
relative homotopy sets `πₖ(X, A, a)` are trivial for `0 < k < n` and every `a ∈ A`. Then the
relative singular homology `Hₘ(X, A; R)` vanishes for every `m < n` and every coefficient ring `R`
(`TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`). This is the vanishing half of
the relative Hurewicz theorem; unlike the isomorphism in degree `n`, it needs no assumption on the
fundamental groups of `X` and `A`.

The proof is Eilenberg's deformation of singular chains, as for the absolute case
`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`. By the compression lemma
the singular cubes of `X` deform into `A` below dimension `n`
(`TauCeti.nonempty_subspaceCubeDeformation_of_relHomotopyGroup`). The end of such a deformation
`D` is a chain endomorphism `D.endChainMap R` of the normalized cubical chains of `X`, chain
homotopic to the identity through the swept-cube operator. It fixes the chains of `A`, and the
swept-cube operator kills them, because the deformation of a cube of `A` is constant. So the
homotopy descends to the relative cubical chains of `(X, A)`. There the end of the deformation
vanishes in every degree `m < n`, since it carries every cube of dimension `m` into `A`. Hence
the identity of the relative cubical homology in degree `m` is zero
(`TauCeti.SubspaceCubeDeformation.isZero_homology_cubicalChainComplex`), and the comparison of
relative cubical and simplicial chains transports this to relative singular homology.

The long exact sequence of the pair then gives the range in which the inclusion of `A` sees the
homology of `X`: `Hₘ(A; R) ⟶ Hₘ(X; R)` is surjective for `m < n`
(`TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup`) and bijective for `m + 1 < n`
(`TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`).

## Main results

* `TauCeti.SubspaceCubeDeformation.relEndHomotopy`: the chain homotopy from the identity to the
  end of the deformation, on the relative cubical chains of `(X, A)`.
* `TauCeti.SubspaceCubeDeformation.isZero_homology_cubicalChainComplex`: relative cubical
  homology vanishes below the dimension bound of a deformation into `A`.
* `TauCeti.isZero_singularHomology_ofSubset_of_relHomotopyGroup`: relative singular homology
  vanishes below the connectivity of the pair.
* `TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup`,
  `TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`: the inclusion
  of the subspace is surjective on homology below the connectivity of the pair, and bijective one
  degree lower.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of the singular chains of a pair into those of the subspace.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.6 (the compression lemma), and Section 4.2, Theorem 4.32 (the relative
  Hurewicz theorem).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology unitInterval Set

universe u

namespace TauCeti

namespace SubspaceCubeDeformation

variable {P : TopPair.{u}} {n : ℕ∞} (D : SubspaceCubeDeformation (range P.map) n) (R : Type u)
  [Ring R]

/-- The end of a deformation into the subspace of a pair fixes the chains of the subspace, as
chain maps. -/
@[reassoc (attr := simp)]
theorem normalizedCubicalChainComplex_map_comp_endChainMap :
    (normalizedCubicalChainComplex R).map P.map ≫ D.endChainMap R =
      (normalizedCubicalChainComplex R).map P.map := by
  ext m g
  exact (D.endChainMap_f_apply R m _).trans (D.endChain_map R g)

/-- The end of a deformation into the subspace of a pair, on the relative cubical chains of the
pair. -/
def relEndChainMap : P.cubicalChainComplex R ⟶ P.cubicalChainComplex R :=
  cokernel.desc _ (D.endChainMap R ≫ cokernel.π _) (by simp)

@[reassoc (attr := simp)]
theorem π_relEndChainMap :
    cokernel.π _ ≫ D.relEndChainMap R = D.endChainMap R ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

/-- After projection to relative chains, the homotopy `D.endHomotopy R` vanishes on the chains of
the subspace: between consecutive degrees it is the swept-cube operator, which kills them. -/
private theorem map_comp_endHomotopy_hom_comp_π (i j : ℕ) :
    ((normalizedCubicalChainComplex R).map P.map).f i ≫ (D.endHomotopy R).hom i j ≫
      (cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f j = 0 := by
  by_cases hij : i + 1 = j
  · subst hij
    ext g
    have hg : (D.endHomotopy R).hom i (i + 1)
        (((normalizedCubicalChainComplex R).map P.map).f i g) = 0 :=
      (D.endHomotopy_hom_succ R i _).trans (neg_eq_zero.2 (D.prismChain_map R g))
    exact (congrArg ((cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f (i + 1)) hg).trans
      (map_zero _)
  · rw [(D.endHomotopy R).zero i j (by simpa using hij), zero_comp, comp_zero]

/-- **The chain homotopy from the identity to the end of a deformation into the subspace of a
pair, on relative cubical chains**, descended from `TauCeti.SubspaceCubeDeformation.endHomotopy`. -/
def relEndHomotopy : Homotopy (𝟙 _) (D.relEndChainMap R) :=
  Homotopy.descCokernel (D.endHomotopy R) ((normalizedCubicalChainComplex R).map P.map)
    (cokernel.π _) (cokernel.π _)
    (P.cubicalChainComplex_condition_f R)
    (fun m ↦ isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) m) _)
    (D.map_comp_endHomotopy_hom_comp_π R) (by simp) (D.π_relEndChainMap R)

/-- The quotient equation for the homotopy operator on relative cubical chains. -/
@[reassoc (attr := simp)]
theorem π_relEndHomotopy_hom (i j : ℕ) :
    (cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f i ≫
        (D.relEndHomotopy R).hom i j =
      (D.endHomotopy R).hom i j ≫
        (cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f j := by
  unfold relEndHomotopy
  apply Homotopy.π_descCokernel_hom

/-- **Below dimension `n`, the end of a deformation into the subspace vanishes on relative cubical
chains**: it carries every cube into the subspace. -/
theorem relEndChainMap_f_eq_zero {m : ℕ} (hm : (m : ℕ∞) < n) : (D.relEndChainMap R).f m = 0 := by
  rw [← cancel_epi ((cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f m),
    ← HomologicalComplex.comp_f, π_relEndChainMap, comp_zero]
  ext g
  obtain ⟨a, ha⟩ := D.endChain_mem_range_map R P.isEmbedding_map.isInducing hm g
  exact (congrArg
    (ModuleCat.Hom.hom ((cokernel.π ((normalizedCubicalChainComplex R).map P.map)).f m))
    ((D.endChainMap_f_apply R m g).trans ha.symm)).trans
      congr(ModuleCat.Hom.hom $(P.cubicalChainComplex_condition_f R m) a)

include D in
/-- **Relative cubical homology vanishes below the dimension bound of a deformation into the
subspace**: if the singular cubes of `X` deform into `A` below dimension `n`, then the relative
normalized cubical homology of `(X, A)` vanishes in every degree `m < n`. -/
theorem isZero_homology_cubicalChainComplex {m : ℕ} (hm : (m : ℕ∞) < n) :
    IsZero ((P.cubicalChainComplex R).homology m) := by
  have hcycles : HomologicalComplex.cyclesMap (D.relEndChainMap R) m = 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ m), HomologicalComplex.cyclesMap_i,
      D.relEndChainMap_f_eq_zero R hm, comp_zero, zero_comp]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id,
    (D.relEndHomotopy R).homologyMap_eq, ← cancel_epi (HomologicalComplex.homologyπ _ m),
    HomologicalComplex.homologyπ_naturality, hcycles, zero_comp, comp_zero]

include D in
/-- **Relative singular homology vanishes below the dimension bound of a deformation into the
subspace.** -/
theorem isZero_singularHomology {m : ℕ} (hm : (m : ℕ∞) < n) :
    IsZero (P.singularHomology (ModuleCat.of R R) m) :=
  (D.isZero_homology_cubicalChainComplex R hm).of_iso (TopPair.singularCubicalHomologyIso R P m)

end SubspaceCubeDeformation

/-- **Relative singular homology vanishes below the connectivity of the pair.** If every point of
`X` is joined by a path to a point of `A`, and the relative homotopy set `π_{k+1}(X, A, a)` is
trivial for every `k + 1 < n` and every `a ∈ A`, then `Hₘ(X, A; R) = 0` for every `m < n` and
every coefficient ring `R`. -/
theorem isZero_singularHomology_ofSubset_of_relHomotopyGroup {X : TopCat.{u}} {A : Set X} {n : ℕ}
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (R : Type u) [Ring R] {m : ℕ} (hm : m < n) :
    IsZero ((TopPair.ofSubset A).singularHomology (ModuleCat.of R R) m) := by
  obtain ⟨D⟩ := nonempty_subspaceCubeDeformation_of_relHomotopyGroup (n := n) h₀ fun k hk ↦
    h k (by exact_mod_cast hk)
  rw [← TopPair.range_ofSubset_map (B := A)] at D
  exact D.isZero_singularHomology R (by exact_mod_cast hm)

/-- **The inclusion of a subspace induces surjections on homology below the connectivity of the
pair.** If every point of `X` is joined by a path to a point of `A`, and the relative homotopy set
`π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then the inclusion of `A`
into `X` induces an epimorphism `Hₘ(A; R) ⟶ Hₘ(X; R)` for every `m < n` and every coefficient
ring `R`. -/
theorem epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup {X : TopCat.{u}} {A : Set X}
    {n : ℕ} (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (R : Type u) [Ring R] {m : ℕ} (hm : m < n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) :=
  -- The map induced on singular homology is `SSet.homologyMap (TopCat.toSSet.map P.map)` for the
  -- pair `P = TopPair.ofSubset A`, whose subspace inclusion is `Subtype.val`, by definition.
  (TopPair.ofSubset A).epi_homologyMap_map_of_isZero _
    (isZero_singularHomology_ofSubset_of_relHomotopyGroup h₀ h R hm)

/-- **The inclusion of a subspace induces isomorphisms on homology below the connectivity of the
pair minus one.** If every point of `X` is joined by a path to a point of `A`, and the relative
homotopy set `π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then the
inclusion of `A` into `X` induces an isomorphism `Hₘ(A; R) ≅ Hₘ(X; R)` for every `m + 1 < n` and
every coefficient ring `R`. Together with
`TauCeti.epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup` in degree `m = n - 1`, this is
the range given by the long exact sequence of the pair. -/
theorem isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt {X : TopCat.{u}}
    {A : Set X} {n : ℕ} (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, k + 1 < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩))
    (R : Type u) [Ring R] {m : ℕ} (hm : m + 1 < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) :=
  -- The map induced on singular homology is `SSet.homologyMap (TopCat.toSSet.map P.map)` for the
  -- pair `P = TopPair.ofSubset A`, whose subspace inclusion is `Subtype.val`, by definition.
  (TopPair.ofSubset A).isIso_homologyMap_map_of_isZero _
    (isZero_singularHomology_ofSubset_of_relHomotopyGroup h₀ h R hm)
    (isZero_singularHomology_ofSubset_of_relHomotopyGroup h₀ h R (by lia))

end TauCeti
