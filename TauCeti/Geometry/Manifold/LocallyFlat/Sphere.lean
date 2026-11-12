/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Separation
public import TauCeti.Geometry.Sphere.Connected
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Brown's bicollaring theorem for locally flat spheres

A locally flat codimension-one sphere in a sphere has a global bicollar.  This is the global
collaring theorem that turns the local product charts in `TauCeti.IsLocallyFlat` into one product
neighbourhood of the entire embedded sphere.  It is the structural input to the annulus theorem:
the collar presents a whole neighbourhood of the sphere as a product, which is what identifies
the regions adjacent to it.  It is that global bicollar that wild embeddings such as the
Alexander horned sphere fail to admit.

Brown's theorem is recorded as the dimension-indexed proposition
`TauCeti.BrownBicollaring`.  Its hypothesis may equally be read through the codimension-one
comparison `TauCeti.isLocallyFlat_iff_isEmbedding_and_isLocallyBicollared`, which says that a map
out of a sphere is locally flat exactly when it is an embedding that is locally bicollared.

The indexing uses an `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))` embedded in the
`(n + 1)`-sphere in `EuclideanSpace ℝ (Fin (n + 2))`.  Local flatness is read in the split
ambient model `EuclideanSpace ℝ (Fin n) × ℝ`: the first factor is the model of the source
sphere, and the second is its one-dimensional normal direction.  No orientation or choice of
side is included in the statement.

Conversely, once an embedded sphere `Sᵐ⁻¹ → Sᵐ`, `m ≥ 2`, has a global bicollar, the
Jordan–Brouwer separation theorem identifies the two sides of the bicollar with the two path
components of the complement of the image
(`TauCeti.IsBicollar.exists_pathComponents_sphere`).

## Main definitions

* `TauCeti.BrownBicollaring`: every locally flat embedding `Sⁿ → Sⁿ⁺¹` is globally
  bicollared.

## Main results

* `TauCeti.brownBicollaring_iff`: the defining characterization of Brown's theorem.
* `TauCeti.BrownBicollaring.exists_isOpen_sdiff_range_eq_union`: granting Brown's theorem, a
  locally flat sphere is two-sided, so it separates a neighbourhood of itself into two disjoint
  nonempty open sides.
* `TauCeti.IsLocallyFlat.isBicollared_of_not_isPreconnected_compl_range`: for `n ≥ 1`, a locally
  flat `n`-sphere in the `(n + 1)`-sphere whose complement is disconnected is bicollared. By the
  Jordan–Brouwer separation theorem the complement is always disconnected, and this is how Brown
  proves the theorem.
* `TauCeti.IsBicollar.exists_pathComponents_sphere`: the complement of a bicollared sphere
  `Sᵐ⁻¹ → Sᵐ`, `m ≥ 2`, has two path components, one on each side of the bicollar.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76. The identification of the two sides of a bicollared sphere with the complementary
  components (`TauCeti.IsBicollar.exists_pathComponents_sphere`) is a step of its proof.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. J. Daverman and G. A. Venema, *Embeddings in Manifolds*, Graduate Studies in Mathematics
  106, American Mathematical Society (2009), Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open Topology
open scoped EuclideanSpace

/-- **Brown's bicollaring theorem in dimension `n`:** every locally flat embedding of the
standard `n`-sphere in the standard `(n + 1)`-sphere admits a global bicollar.

The local-flatness model is `EuclideanSpace ℝ (Fin n) × ℝ`: its zero slice has dimension
`n`, and its complementary factor has dimension one.  Thus the hypothesis says precisely that
the embedding is locally a codimension-one coordinate slice.  The conclusion is the existence of
an open embedding `Sⁿ × ℝ → Sⁿ⁺¹` whose zero slice is the original embedding. -/
def BrownBicollaring (n : ℕ) : Prop :=
  ∀ f :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
    IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f

/-- Brown's bicollaring theorem in dimension `n` spelled out: every locally flat embedding of the
standard `n`-sphere in the standard `(n + 1)`-sphere, with local-flatness model
`EuclideanSpace ℝ (Fin n)`, admits a global bicollar. -/
@[simp]
theorem brownBicollaring_iff {n : ℕ} :
    BrownBicollaring n ↔
      ∀ f :
          sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f :=
  by rfl

/-- Granting Brown's theorem, a locally flat `n`-sphere in the `(n + 1)`-sphere is **two-sided**:
it has an open neighbourhood whose complement in that neighbourhood is the union of two disjoint
nonempty open sets, the two sides of the collar the theorem provides.  This is the separation
statement the annulus theorem consumes.  What local flatness supplies is the collar, not the
separation on its own: a wild embedding such as the Alexander horned sphere admits no global
bicollar, even though its complement is still a union of two open regions. -/
theorem BrownBicollaring.exists_isOpen_sdiff_range_eq_union {n : ℕ} (h : BrownBicollaring n)
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (hf : IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f) :
    ∃ U V W : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1),
      IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧ V.Nonempty ∧ W.Nonempty ∧
        Disjoint V W ∧ U \ range f = V ∪ W :=
  haveI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  (h f hf).exists_isOpen_sdiff_range_eq_union

/-- **Brown's bicollaring theorem for separating spheres.** For `n ≥ 1`, a locally flat embedding
of the `n`-sphere in the `(n + 1)`-sphere whose image has disconnected complement is bicollared.

The Jordan–Brouwer separation theorem says that the complement is always disconnected, so this
reduces `TauCeti.BrownBicollaring n` to it. The hypothesis `n ≠ 0` makes the source sphere
connected; the `0`-sphere is two points. -/
theorem IsLocallyFlat.isBicollared_of_not_isPreconnected_compl_range {n : ℕ} (hn : n ≠ 0)
    {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1}
    (hf : IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f) (hsep : ¬ IsPreconnected (range f)ᶜ) :
    IsBicollared f :=
  haveI := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n))
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  haveI := connectedSpace_euclideanSphere (m := n + 1) (by omega)
  haveI := connectedSpace_euclideanSphere (m := n + 2) (by omega)
  hf.isLocallyBicollared.isBicollared_of_not_isPreconnected_compl_range hf.injective hsep

section SidesOfSphere

open Module


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : sphere (0 : E) 1 → sphere (0 : F) 1} {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- **The two sides of a bicollared sphere.** Let `b` be a bicollar of an embedding `f` of the
unit sphere of `E` into the unit sphere of `F`, where `dim F = dim E + 1` and `dim E ≥ 2`. Then
the complement of the image of `f` is the union of two disjoint open path-connected sets `A` and
`B`, its two path components, with the positive side of the bicollar in `A` and the negative side
in `B`. This is a step of Brown's proof of the generalized Schoenflies theorem (Brown, 1960). -/
theorem IsBicollar.exists_pathComponents_sphere (h : IsBicollar f b) (hE : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) :
    ∃ A B : Set (sphere (0 : F) 1), IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧
      (range f)ᶜ = A ∪ B ∧ IsPathConnected A ∧ IsPathConnected B ∧
      MapsTo b (univ ×ˢ Ioi 0) A ∧ MapsTo b (univ ×ˢ Iio 0) B := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : E) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (isPathConnected_sphere
      (one_lt_rank_of_one_lt_finrank (by omega)) 0 zero_le_one).isConnected.isPreconnected
  have : PreconnectedSpace (sphere (0 : F) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (isPathConnected_sphere
      (one_lt_rank_of_one_lt_finrank (by omega)) 0 zero_le_one).isConnected.isPreconnected
  -- The unit sphere of `F` is homeomorphic to a Euclidean sphere, a manifold, so it is locally
  -- path connected.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) = finrank ℝ E + 1) :=
    ⟨by simp⟩
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1)
  have := (sphereHomeomorphOfFinrankEq (F := F)
    (E := EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) (by simp [hEF])).locallyPathConnectedSpace
  set X := (range f)ᶜ
  have hX : IsOpen X := (isCompact_range h.continuous).isClosed.isOpen_compl
  -- By the Jordan–Brouwer theorem, `X` has two path components, those of some `p` and `q`.
  obtain ⟨c, d, hcd, hcover⟩ := Nat.card_eq_two_iff.1
    (natCard_zerothHomotopy_sphere_compl_range_eq_two hEF h.continuous h.injective)
  obtain ⟨⟨p, hp⟩, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨⟨q, hq⟩, rfl⟩ := ZerothHomotopy.mk_surjective d
  have hjoined : ∀ {u v : sphere (0 : F) 1} (hu : u ∈ X) (hv : v ∈ X),
      ZerothHomotopy.mk (⟨u, hu⟩ : X) = ZerothHomotopy.mk ⟨v, hv⟩ ↔ JoinedIn X u v := by
    intro u v hu hv
    rw [joinedIn_iff_joined hu hv, ← mem_pathComponent_iff,
      ← ZerothHomotopy.preimage_singleton_eq_pathComponent, mem_preimage, mem_singleton_iff,
      eq_comm]
  set A := pathComponentIn X p
  set B := pathComponentIn X q
  have hAB : Disjoint A B := by
    refine disjoint_left.2 fun r hrA hrB ↦ hcd ?_
    exact (hjoined hp hq).2 ((hrA : JoinedIn X p r).trans (hrB : JoinedIn X q r).symm)
  have hXAB : X = A ∪ B := by
    refine Subset.antisymm (fun r hr ↦ ?_) (union_subset pathComponentIn_subset
      pathComponentIn_subset)
    have hr' : ZerothHomotopy.mk (⟨r, hr⟩ : X) ∈ ({ZerothHomotopy.mk ⟨p, hp⟩,
        ZerothHomotopy.mk ⟨q, hq⟩} : Set (ZerothHomotopy X)) := hcover ▸ mem_univ _
    rcases hr' with hr' | hr'
    · exact Or.inl ((hjoined hr hp).1 hr').symm
    · exact Or.inr ((hjoined hr hq).1 hr').symm
  have hAo : IsOpen A := hX.pathComponentIn p
  have hBo : IsOpen B := hX.pathComponentIn q
  rcases h.mapsTo_and_mapsTo_or_mapsTo_and_mapsTo hAo hBo hAB hXAB
      ⟨p, mem_pathComponentIn_self hp⟩ ⟨q, mem_pathComponentIn_self hq⟩ with
    ⟨hpos, hneg⟩ | ⟨hpos, hneg⟩
  · exact ⟨A, B, hAo, hBo, hAB, hXAB, isPathConnected_pathComponentIn hp,
      isPathConnected_pathComponentIn hq, hpos, hneg⟩
  · exact ⟨B, A, hBo, hAo, hAB.symm, hXAB.trans (union_comm _ _),
      isPathConnected_pathComponentIn hq, isPathConnected_pathComponentIn hp, hpos, hneg⟩

end SidesOfSphere

end TauCeti
