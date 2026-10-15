/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
public import TauCeti.Geometry.Manifold.Irreducible
public import TauCeti.Geometry.Manifold.Orientation
public import TauCeti.LowDimTopology.SeifertFibration
public import TauCeti.Topology.ConnectedComponents
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Atoroidal 3-manifolds and the JSJ decomposition

The JSJ decomposition theorem of Jaco–Shalen and Johannson says that a closed orientable
irreducible 3-manifold `M` can be cut along finitely many disjoint incompressible tori into pieces
each of which is Seifert fibred or atoroidal, and that a minimal such family of tori is unique up
to isotopy (Hatcher, *Notes on Basic 3-Manifold Topology*, Theorem 1.9). This file states that
theorem.

As in the statement of the geometrization conjecture (`TauCeti.GeometrizationConjecture`), the
pieces are the connected components of the complement `M \ ⋃ i, T i (S¹ × S¹)` of the tori. Such a
component `U` is the interior of the compact piece `N` obtained by cutting `M` along the tori, and
it is open in `M`.

A compact piece `N` is *atoroidal* when every incompressible torus in `N` is boundary parallel:
it cobounds with a boundary torus of `N` a product region `T² × [0, 1]`. In the interior `U` of `N`
such a region becomes a product end `T² × [0, 1)`. So a torus `S : S¹ × S¹ → U` is called
*peripheral* (`TauCeti.IsPeripheralTorus S`) when it is the end `T² × {0}` of a closed embedding
of the half-open product `T² × [0, ∞)` into `U`, and `U` is *atoroidal* (`TauCeti.IsAtoroidal U`)
when every locally flat incompressible torus in `U` is peripheral. Since `T² × [0, ∞)` is not
compact, a compact space has no peripheral torus, and being atoroidal then means having no locally
flat incompressible torus at all (`TauCeti.isAtoroidal_iff_of_compactSpace`). A simply connected
space has no incompressible torus, so it is atoroidal
(`TauCeti.isAtoroidal_of_simplyConnectedSpace`).

A *torus decomposition* (`TauCeti.IsTorusDecomposition T`) is a finite family of disjoint locally
flat incompressible tori whose complementary components are Seifert fibred or atoroidal, and a
*JSJ decomposition* (`TauCeti.IsJSJDecomposition T`) is a torus decomposition no proper
subfamily of which is a torus decomposition. `TauCeti.JSJTheorem` asserts that every closed
orientable irreducible 3-manifold has a JSJ decomposition and that any two JSJ decompositions are
carried onto each other by an ambient isotopy. The theorem is stated, not proved.

## Main definitions

* `TauCeti.IsPeripheralTorus S`: the torus `S` is the end of a closed product end `T² × [0, ∞)`.
* `TauCeti.IsAtoroidal N`: every locally flat incompressible torus in `N` is peripheral.
* `TauCeti.IsTorusDecomposition T`: a finite family of disjoint locally flat incompressible tori
  cutting a 3-manifold into Seifert-fibred and atoroidal pieces.
* `TauCeti.IsJSJDecomposition T`: a torus decomposition that is minimal under inclusion.
* `TauCeti.JSJTheorem`: existence and uniqueness up to ambient isotopy of JSJ decompositions of
  closed orientable irreducible 3-manifolds.

## Main results

* `Homeomorph.isAtoroidal_iff`: being atoroidal is invariant under homeomorphism.
* `TauCeti.isPeripheralTorus_prodMk_zero`: the slice `T² × {0}` of `T² × ℝ` is peripheral.
* `TauCeti.isAtoroidal_iff_of_compactSpace`: a compact space is atoroidal exactly when it has no
  locally flat incompressible torus.
* `TauCeti.isAtoroidal_of_simplyConnectedSpace`: simply connected spaces are atoroidal.
* `TauCeti.isJSJDecomposition_of_isEmpty`: a connected Seifert-fibred or atoroidal 3-manifold has
  the empty JSJ decomposition.
* `TauCeti.JSJTheorem.exists_isJSJDecomposition` and
  `TauCeti.JSJTheorem.exists_ambientIsotopy_image_eq`: applying the theorem.
* `TauCeti.JSJTheorem.card_eq`: the theorem makes the number of tori of a JSJ decomposition an
  invariant of the manifold, since the tori are the connected components of their union.

## References

* W. H. Jaco, P. B. Shalen, *Seifert fibered spaces in 3-manifolds*, Mem. Amer. Math. Soc. 21
  (1979), no. 220.
* K. Johannson, *Homotopy equivalences of 3-manifolds with boundaries*, Lecture Notes in Math.
  761, Springer (1979).
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Section 1.2, Theorem 1.9.
-/

public section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff NNReal

universe u

namespace TauCeti

section Atoroidal

variable {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N']

/-- A torus `S : S¹ × S¹ → N` is **peripheral** when it is the end `T² × {0}` of a closed embedding
of the half-open product `T² × [0, ∞)` into `N`. When `N` is the interior of a compact 3-manifold
with torus boundary, these are the tori parallel to a boundary torus: the product region between
the torus and the boundary becomes the closed product end `T² × [0, 1) ≃ T² × [0, ∞)` of the
interior. -/
def IsPeripheralTorus (S : C(Circle × Circle, N)) : Prop :=
  ∃ E : C((Circle × Circle) × ℝ≥0, N), IsClosedEmbedding E ∧ ∀ x, E (x, 0) = S x

/-- The defining condition of a peripheral torus. -/
theorem isPeripheralTorus_iff {S : C(Circle × Circle, N)} :
    IsPeripheralTorus S ↔
      ∃ E : C((Circle × Circle) × ℝ≥0, N), IsClosedEmbedding E ∧ ∀ x, E (x, 0) = S x :=
  Iff.rfl

/-- A homeomorphism carries peripheral tori to peripheral tori. -/
theorem IsPeripheralTorus.homeomorph_comp {S : C(Circle × Circle, N)} (h : IsPeripheralTorus S)
    (e : N ≃ₜ N') : IsPeripheralTorus ((e : C(N, N')).comp S) := by
  obtain ⟨E, hE, hES⟩ := h
  exact ⟨(e : C(N, N')).comp E, e.isClosedEmbedding.comp hE, fun x ↦ by simp [hES]⟩

/-- The slice `T² × {0}` of the product `T² × ℝ` is peripheral: it is the end of the closed half
`T² × [0, ∞)`. -/
theorem isPeripheralTorus_prodMk_zero :
    IsPeripheralTorus (ContinuousMap.prodMk (ContinuousMap.id (Circle × Circle))
      (ContinuousMap.const (Circle × Circle) (0 : ℝ))) :=
  ⟨ContinuousMap.prodMap (ContinuousMap.id _) ⟨NNReal.toReal, NNReal.continuous_coe⟩,
    IsClosedEmbedding.id.prodMap NNReal.isClosedEmbedding_coe, fun _ ↦ rfl⟩

/-- No torus in a compact space is peripheral: a closed embedding of `T² × [0, ∞)` into a compact
space would make `[0, ∞)` compact. -/
theorem not_isPeripheralTorus_of_compactSpace [CompactSpace N] (S : C(Circle × Circle, N)) :
    ¬ IsPeripheralTorus S := by
  rintro ⟨E, hE, -⟩
  have := hE.compactSpace
  obtain ⟨b, hb⟩ := (isCompact_range (X := (Circle × Circle) × ℝ≥0)
    (f := fun p ↦ (p.2 : ℝ)) (by fun_prop)).bddAbove
  have hb' : max (b + 1) 0 ≤ b := by
    simpa using hb ⟨(1, (b + 1).toNNReal), rfl⟩
  linarith [le_max_left (b + 1) 0]

variable (N) in
/-- A space is **atoroidal** when every locally flat incompressible torus in it is peripheral. For
the interior of a compact 3-manifold with torus boundary components this is the usual condition
that every incompressible torus is boundary parallel; for a compact space it says that there is no
locally flat incompressible torus (`TauCeti.isAtoroidal_iff_of_compactSpace`). -/
def IsAtoroidal : Prop :=
  ∀ S : C(Circle × Circle, N), IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ S →
    IsIncompressible S → IsPeripheralTorus S

/-- The defining condition of an atoroidal space. -/
theorem isAtoroidal_iff :
    IsAtoroidal N ↔ ∀ S : C(Circle × Circle, N), IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ S →
      IsIncompressible S → IsPeripheralTorus S :=
  Iff.rfl

/-- A homeomorphism carries an atoroidal space to an atoroidal space. -/
theorem IsAtoroidal.of_homeomorph (h : IsAtoroidal N) (e : N ≃ₜ N') : IsAtoroidal N' := by
  intro S hflat hinc
  have hS : (e : C(N, N')).comp ((e.symm : C(N', N)).comp S) = S := by ext; simp
  rw [← hS]
  refine (h _ (hflat.homeomorph_comp e.symm) ?_).homeomorph_comp e
  exact (isIncompressible_of_leftInverse (r := (e : C(N, N'))) (by ext; simp)).comp hinc

/-- Being atoroidal is invariant under homeomorphism. -/
theorem _root_.Homeomorph.isAtoroidal_iff (e : N ≃ₜ N') : IsAtoroidal N ↔ IsAtoroidal N' :=
  ⟨fun h ↦ h.of_homeomorph e, fun h ↦ h.of_homeomorph e.symm⟩

/-- A compact space is atoroidal exactly when it contains no locally flat incompressible torus. -/
theorem isAtoroidal_iff_of_compactSpace [CompactSpace N] :
    IsAtoroidal N ↔ ∀ S : C(Circle × Circle, N), IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ S →
      ¬ IsIncompressible S :=
  forall_congr' fun S ↦ forall_congr' fun _ ↦ by
    simp only [not_isPeripheralTorus_of_compactSpace, imp_false]

/-- A simply connected space is atoroidal: it contains no incompressible torus, since the
fundamental group of the torus is nontrivial. -/
theorem isAtoroidal_of_simplyConnectedSpace [SimplyConnectedSpace N] : IsAtoroidal N := by
  intro S _ hS
  obtain ⟨x, y⟩ := Classical.arbitrary (Circle × Circle)
  have : Nontrivial (FundamentalGroup Circle x) := Circle.nontrivial_fundamentalGroup x
  -- The circle `S¹ × {y}` is a retract of the torus, so `π₁(S¹)` injects into `π₁(T²)`.
  have : Nontrivial (FundamentalGroup (Circle × Circle) (x, y)) :=
    ((isIncompressible_of_leftInverse (f := ContinuousMap.prodMk (ContinuousMap.id Circle)
      (ContinuousMap.const Circle y)) (r := ContinuousMap.fst) rfl).fundamentalGroup_injective
      x).nontrivial
  exact (not_isIncompressible_of_simplyConnectedSpace S (x, y) hS).elim

end Atoroidal

section Decomposition

variable {M : Type*} [TopologicalSpace M] {ι : Type*}

/-- A family of maps `T i : S¹ × S¹ → M` is a **torus decomposition** of the 3-manifold `M` when
there are finitely many maps, they are disjoint locally flat incompressible embeddings of the
torus, and every connected component of the complement of their images is Seifert fibred or
atoroidal. In a Hausdorff 3-manifold the components are open
(`TauCeti.exists_opens_eq_connectedComponentIn_compl_iUnion_range`): they are the interiors of the
pieces of `M` cut along the tori. -/
structure IsTorusDecomposition (T : ι → C(Circle × Circle, M)) : Prop where
  /-- There are finitely many tori. -/
  finite : Finite ι
  /-- Each torus is locally flat, flattened by charts of `M` onto `ℝ² × {0} ⊆ ℝ² × ℝ`. -/
  isLocallyFlat (i : ι) : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ (T i)
  /-- Each torus is incompressible. -/
  isIncompressible (i : ι) : IsIncompressible (T i)
  /-- The tori are pairwise disjoint. -/
  pairwise_disjoint : Pairwise (Disjoint on fun i ↦ range (T i))
  /-- Each connected component of the complement of the tori is Seifert fibred or atoroidal. -/
  isSeifertFibered_or_isAtoroidal (x : M) (hx : x ∉ ⋃ i, range (T i)) (U : Opens M)
    (hU : (U : Set M) = connectedComponentIn (⋃ i, range (T i))ᶜ x) :
    IsSeifertFibered U ∨ IsAtoroidal U

/-- A family of tori is a **JSJ decomposition** of `M` when it is a torus decomposition and no
proper subfamily is a torus decomposition. -/
structure IsJSJDecomposition (T : ι → C(Circle × Circle, M)) : Prop where
  /-- The family is a torus decomposition. -/
  isTorusDecomposition : IsTorusDecomposition T
  /-- A subfamily that is a torus decomposition is the whole family. -/
  eq_univ_of_isTorusDecomposition (s : Set ι) :
    IsTorusDecomposition (fun i : s ↦ T i) → s = univ

/-- A connected space that is Seifert fibred or atoroidal is a torus decomposition of itself with
no tori: it is its own single piece. -/
theorem isTorusDecomposition_of_isEmpty [IsEmpty ι] [ConnectedSpace M]
    (h : IsSeifertFibered M ∨ IsAtoroidal M) (T : ι → C(Circle × Circle, M)) :
    IsTorusDecomposition T where
  finite := inferInstance
  isLocallyFlat i := isEmptyElim i
  isIncompressible i := isEmptyElim i
  pairwise_disjoint i := isEmptyElim i
  isSeifertFibered_or_isAtoroidal x _ U hU := by
    have hU' : (U : Set M) = univ := by
      rw [hU, iUnion_of_empty, compl_empty, connectedComponentIn_univ,
        PreconnectedSpace.connectedComponent_eq_univ]
    have e := (Homeomorph.setCongr hU').trans (Homeomorph.Set.univ M)
    exact h.imp e.isSeifertFibered_iff.2 e.isAtoroidal_iff.2

/-- A connected space that is Seifert fibred or atoroidal has the empty JSJ decomposition. -/
theorem isJSJDecomposition_of_isEmpty [IsEmpty ι] [ConnectedSpace M]
    (h : IsSeifertFibered M ∨ IsAtoroidal M) (T : ι → C(Circle × Circle, M)) :
    IsJSJDecomposition T where
  isTorusDecomposition := isTorusDecomposition_of_isEmpty h T
  eq_univ_of_isTorusDecomposition s _ := Subsingleton.elim s univ

end Decomposition

/-- The **JSJ decomposition theorem** (Jaco–Shalen, Johannson): every closed orientable irreducible
3-manifold `M`, that is a compact connected orientable smooth 3-manifold without boundary in which
every locally flat 2-sphere bounds a ball, has a JSJ decomposition, a minimal family of disjoint
locally flat incompressible tori cutting `M` into Seifert-fibred and atoroidal pieces; and any two
JSJ decompositions of `M` are isotopic: some ambient isotopy of `M` carries the union of the tori
of one onto the union of the tori of the other. -/
def JSJTheorem : Prop :=
  ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) ∞ M],
    IsSphereBoundsBall M →
      (∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsJSJDecomposition T) ∧
      ∀ (n n' : ℕ) (T : Fin n → C(Circle × Circle, M)) (T' : Fin n' → C(Circle × Circle, M)),
        IsJSJDecomposition T → IsJSJDecomposition T' →
          ∃ Φ : AmbientIsotopy M, Φ.final '' ⋃ i, range (T i) = ⋃ j, range (T' j)

/-- The defining characterization of the JSJ decomposition theorem. -/
theorem jsjTheorem_iff :
    JSJTheorem.{u} ↔
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) ∞ M],
        IsSphereBoundsBall M →
          (∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsJSJDecomposition T) ∧
          ∀ (n n' : ℕ) (T : Fin n → C(Circle × Circle, M))
            (T' : Fin n' → C(Circle × Circle, M)),
            IsJSJDecomposition T → IsJSJDecomposition T' →
              ∃ Φ : AmbientIsotopy M, Φ.final '' ⋃ i, range (T i) = ⋃ j, range (T' j) :=
  Iff.rfl

section Apply

variable (h : JSJTheorem.{u}) (M : Type u) [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M]
  [ConnectedSpace M] [Orientable (𝓡 3) ∞ M] (hM : IsSphereBoundsBall M)
include h hM

/-- A proof of the JSJ decomposition theorem gives every closed orientable irreducible 3-manifold
a JSJ decomposition. -/
theorem JSJTheorem.exists_isJSJDecomposition :
    ∃ (n : ℕ) (T : Fin n → C(Circle × Circle, M)), IsJSJDecomposition T :=
  (h M hM).1

/-- A proof of the JSJ decomposition theorem makes any two JSJ decompositions of a closed
orientable irreducible 3-manifold isotopic. -/
theorem JSJTheorem.exists_ambientIsotopy_image_eq {n n' : ℕ}
    {T : Fin n → C(Circle × Circle, M)} {T' : Fin n' → C(Circle × Circle, M)}
    (hT : IsJSJDecomposition T) (hT' : IsJSJDecomposition T') :
    ∃ Φ : AmbientIsotopy M, Φ.final '' ⋃ i, range (T i) = ⋃ j, range (T' j) :=
  (h M hM).2 n n' T T' hT hT'

/-- A proof of the JSJ decomposition theorem makes the number of tori of a JSJ decomposition an
invariant of a closed orientable irreducible 3-manifold: any two JSJ decompositions have the same
number of tori. -/
theorem JSJTheorem.card_eq {n n' : ℕ} {T : Fin n → C(Circle × Circle, M)}
    {T' : Fin n' → C(Circle × Circle, M)} (hT : IsJSJDecomposition T)
    (hT' : IsJSJDecomposition T') : n = n' := by
  -- The tori of a decomposition are the connected components of their union.
  have hcard {k : ℕ} (S : Fin k → C(Circle × Circle, M))
      (hS : Pairwise (Disjoint on fun i ↦ range (S i))) :
      Nat.card (ConnectedComponents (⋃ i, range (S i))) = k := by
    refine (natCard_connectedComponents_eq_of_iUnion_eq_univ
      (U := fun i ↦ Subtype.val ⁻¹' range (S i))
      (fun i ↦ (isCompact_range (S i).continuous).isClosed.preimage continuous_subtype_val)
      (fun i j hij ↦ (hS hij).preimage _) ?_ fun i ↦ ?_).trans (Nat.card_fin k)
    · ext ⟨x, hx⟩
      simpa using hx
    · have : Subtype.val ⁻¹' range (S i) = range fun p ↦
          (⟨S i p, mem_iUnion_of_mem i (mem_range_self p)⟩ : ⋃ i, range (S i)) := by
        ext ⟨x, hx⟩
        simp
      rw [this]
      exact isConnected_range (by fun_prop)
  obtain ⟨Φ, hΦ⟩ := h.exists_ambientIsotopy_image_eq M hM hT hT'
  have e : (⋃ i, range (T i) : Set M) ≃ₜ (⋃ j, range (T' j) : Set M) :=
    (Φ.finalHomeomorph.image _).trans (Homeomorph.setCongr (by
      rw [← hΦ]
      exact congrArg (· '' _) (funext Φ.finalHomeomorph_apply)))
  rw [← hcard T hT.isTorusDecomposition.pairwise_disjoint,
    ← hcard T' hT'.isTorusDecomposition.pairwise_disjoint]
  exact Nat.card_congr (e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    rw [← e.image_symm, image_singleton]
    exact isConnected_singleton).toEquiv

end Apply

end TauCeti
