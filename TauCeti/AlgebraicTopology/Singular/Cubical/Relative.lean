/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Relative cubical chains

For a subspace `A ⊆ X`, the normalized cubical chains of `A` push forward to those of `X` along
the inclusion, and the **relative cubical chains** `C^□_n(X, A; R)` are the quotient of the chains
of `X` by this image.  The boundary descends, since it is natural, and the three complexes fit
into the short exact sequence `C^□_*(A) → C^□_*(X) → C^□_*(X, A)`: the projection kills exactly
the chains supported in `A` (`Submodule.ker_mkQ`), and the connecting map gives the long exact
sequence of the pair once the complexes are packaged as chain complexes.

A cube contributes to a chain supported in `A` only if its image lies in `A`, so a chain supported
in `A` and in `B` is supported in `A ∩ B`. This is what makes the relative chains of a product of
pairs fit into a short exact sequence.

## Main definitions

* `TauCeti.NormalizedCubicalChain.supportedIn R A n`: the chains of `X` supported in `A`, the image
  of the chains of `A`.
* `TauCeti.RelativeCubicalChain X A R n`: the relative chains, their boundary
  `TauCeti.RelativeCubicalChain.boundary` and their push-forward `TauCeti.RelativeCubicalChain.map`
  along a map of pairs.

## Main results

* `TauCeti.NormalizedCubicalChain.boundary_mem_supportedIn`: the chains supported in `A` form a
  subcomplex.
* `TauCeti.NormalizedCubicalChain.range_map_eq_supportedIn_range`: the push-forward along an
  inducing map has image the chains supported in its range.
* `TauCeti.NormalizedCubicalChain.supportedIn_inter`: chains supported in `A` and in `B` are
  supported in `A ∩ B`.
* `TauCeti.RelativeCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0` on relative chains.
* `TauCeti.RelativeCubicalChain.map_boundary`: the relative boundary is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (R : Type*) [Ring R]

namespace NormalizedCubicalChain

/-- The normalized chains of `X` **supported in** the subspace `A`: the image of the chains of
`A` along the inclusion. -/
def supportedIn (A : Set X) (n : ℕ) : Submodule R (NormalizedCubicalChain X R n) :=
  LinearMap.range (map R (ContinuousMap.subtypeVal A) n)

theorem supportedIn_def (A : Set X) (n : ℕ) :
    supportedIn R A n = LinearMap.range (map R (ContinuousMap.subtypeVal A) n) := by
  rw [supportedIn]

/-- The push-forward of a chain of `A` is supported in `A`. -/
theorem map_subtypeVal_mem_supportedIn {A : Set X} {n : ℕ} (c : NormalizedCubicalChain A R n) :
    map R (ContinuousMap.subtypeVal A) n c ∈ supportedIn R A n := by
  rw [supportedIn_def]
  exact LinearMap.mem_range_self _ c

/-- The chain of a cube with image in `A` is supported in `A`. -/
theorem ofCube_mem_supportedIn {A : Set X} {n : ℕ} {c : SingularCube X n}
    (hc : Set.range c ⊆ A) : ofCube X R c ∈ supportedIn R A n := by
  rw [supportedIn_def]
  exact ofCube_mem_range_map R Topology.IsInducing.subtypeVal fun _ hy ↦ ⟨⟨_, hc hy⟩, rfl⟩

/-- The chains supported in a subspace form a subcomplex. -/
theorem boundary_mem_supportedIn {A : Set X} {n : ℕ} {g : NormalizedCubicalChain X R (n + 1)}
    (hg : g ∈ supportedIn R A (n + 1)) : boundary X R n g ∈ supportedIn R A n := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨boundary A R n h, ?_⟩
  rw [← LinearMap.comp_apply, map_boundary, LinearMap.comp_apply]

private theorem supportedIn_le_comap_boundary (A : Set X) (n : ℕ) :
    supportedIn R A (n + 1) ≤ (supportedIn R A n).comap (boundary X R n) :=
  fun _ hg ↦ boundary_mem_supportedIn R hg

/-- A map of pairs `f : (X, A) → (Y, B)` carries the chains supported in `A` to chains supported
in `B`. -/
theorem map_mem_supportedIn {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} {f : C(X, Y)}
    (hf : Set.MapsTo f A B) {n : ℕ} {g : NormalizedCubicalChain X R n}
    (hg : g ∈ supportedIn R A n) : map R f n g ∈ supportedIn R B n := by
  obtain ⟨h, rfl⟩ := hg
  -- `f` restricted to `A`, with values in `B`.
  let f' : C(A, B) :=
    ⟨fun a ↦ ⟨f a, hf a.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hres : (ContinuousMap.subtypeVal B).comp f' = f.comp (ContinuousMap.subtypeVal A) :=
    ContinuousMap.ext fun _ ↦ rfl
  refine ⟨map R f' n h, ?_⟩
  rw [← LinearMap.comp_apply, ← map_comp, hres, map_comp, LinearMap.comp_apply]

private theorem supportedIn_le_comap_map {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y}
    {f : C(X, Y)} (hf : Set.MapsTo f A B) (n : ℕ) :
    supportedIn R A n ≤ (supportedIn R B n).comap (map R f n) :=
  fun _ hg ↦ map_mem_supportedIn R hf hg

/-- Chains supported in a smaller subspace are supported in a larger one. -/
theorem supportedIn_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    supportedIn R A n ≤ supportedIn R B n := fun g hg ↦ by
  simpa using map_mem_supportedIn R (f := ContinuousMap.id X) (Set.mapsTo_id _ |>.mono_right h) hg

/-- The image of the push-forward along an inducing map `f` consists of the chains supported in
the range of `f`. -/
theorem range_map_eq_supportedIn_range {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}
    (hf : Topology.IsInducing f) (n : ℕ) :
    LinearMap.range (map R f n) = supportedIn R (Set.range f) n := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    induction g using induction_on with
    | zero => simp
    | add a b ha hb => simpa using add_mem ha hb
    | smul r a ha => simpa using Submodule.smul_mem _ r ha
    | ofCube c =>
      rw [map_ofCube]
      exact ofCube_mem_supportedIn R fun _ ⟨t, ht⟩ ↦ ⟨c t, ht⟩
  · rintro _ ⟨g, rfl⟩
    induction g using induction_on with
    | zero => simp
    | add a b ha hb => simpa using add_mem ha hb
    | smul r a ha => simpa using Submodule.smul_mem _ r ha
    | ofCube c =>
      rw [map_ofCube]
      exact ofCube_mem_range_map R hf fun _ ⟨t, ht⟩ ↦ ht ▸ (c t).2

open Classical in
/-- The projection of normalized chains onto the chains supported in `A`, keeping the cubes with
image in `A` and killing the others. -/
private def restrictTo (A : Set X) (n : ℕ) :
    NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain X R n :=
  desc (fun c ↦ if Set.range c ⊆ A then ofCube X R c else 0) fun c hc ↦ by
    split_ifs <;> simp [hc]

open Classical in
private theorem restrictTo_ofCube (A : Set X) {n : ℕ} (c : SingularCube X n) :
    restrictTo R A n (ofCube X R c) = if Set.range c ⊆ A then ofCube X R c else 0 := by
  rw [restrictTo, desc_ofCube]

private theorem restrictTo_eq_self {A : Set X} {n : ℕ} {g : NormalizedCubicalChain X R n}
    (hg : g ∈ supportedIn R A n) : restrictTo R A n g = g := by
  obtain ⟨g, rfl⟩ := hg
  induction g using induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul r a ha => simp [ha]
  | ofCube c =>
    rw [map_ofCube, restrictTo_ofCube]
    exact ite_eq_left_of_eq_true _ _ (eq_true fun _ ⟨t, ht⟩ ↦ ht ▸ (c t).2)

private theorem restrictTo_restrictTo_mem (A B : Set X) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    restrictTo R A n (restrictTo R B n g) ∈ supportedIn R (A ∩ B) n := by
  induction g using induction_on with
  | zero => simp
  | add a b ha hb => simpa using add_mem ha hb
  | smul r a ha => simpa using Submodule.smul_mem _ r ha
  | ofCube c =>
    rw [restrictTo_ofCube R B]
    split_ifs with hB
    · rw [restrictTo_ofCube]
      split_ifs with hA
      · exact ofCube_mem_supportedIn R (Set.subset_inter hA hB)
      · exact zero_mem _
    · simp

/-- **Chains supported in two subspaces are supported in their intersection.** A cube contributes
to a normalized chain supported in `A` only if its image lies in `A`, so a chain supported both in
`A` and in `B` is a combination of cubes with image in `A ∩ B`. -/
theorem supportedIn_inter (A B : Set X) (n : ℕ) :
    supportedIn R (A ∩ B) n = supportedIn R A n ⊓ supportedIn R B n := by
  refine le_antisymm (le_inf (supportedIn_mono R Set.inter_subset_left n)
    (supportedIn_mono R Set.inter_subset_right n)) (fun g ⟨hA, hB⟩ ↦ ?_)
  rw [← restrictTo_eq_self R hA, ← restrictTo_eq_self R hB]
  exact restrictTo_restrictTo_mem R A B g

end NormalizedCubicalChain

/-- The **relative normalized cubical chains** of the pair `(X, A)`: the chains of `X` modulo
those supported in `A`. -/
abbrev RelativeCubicalChain (X : Type*) [TopologicalSpace X] (A : Set X) (R : Type*) [Ring R]
    (n : ℕ) : Type _ :=
  NormalizedCubicalChain X R n ⧸ NormalizedCubicalChain.supportedIn R A n

namespace RelativeCubicalChain

variable (X) (A : Set X)

/-- Reindex relative chains along an equality of dimensions. -/
def cast {n m : ℕ} (h : n = m) :
    RelativeCubicalChain X A R n →ₗ[R] RelativeCubicalChain X A R m := by
  subst h
  exact LinearMap.id

@[simp]
theorem cast_mk {n m : ℕ} (h : n = m) (g : NormalizedCubicalChain X R n) :
    cast X R A h (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (NormalizedCubicalChain.cast R h g) := by
  subst h
  simp [cast]

@[simp]
theorem cast_rfl {n : ℕ} (g : RelativeCubicalChain X A R n) : cast X R A rfl g = g :=
  (rfl)

/-- Successive reindexings compose. -/
@[simp]
theorem cast_cast {n m k : ℕ} (h : n = m) (h' : m = k)
    (g : RelativeCubicalChain X A R n) :
    cast X R A h' (cast X R A h g) = cast X R A (h.trans h') g := by
  subst h
  subst h'
  rfl

/-- Reindexing is injective. -/
theorem cast_injective {n m : ℕ} (h : n = m) :
    Function.Injective (cast X R A h) := fun a b hab ↦ by
  simpa using congrArg (cast X R A h.symm) hab

variable {X R A} in
/-- Equal after reindexing implies heterogeneously equal. -/
theorem heq_of_cast_eq {n m : ℕ} (h : n = m) {x : RelativeCubicalChain X A R n}
    {y : RelativeCubicalChain X A R m} (hxy : cast X R A h x = y) : HEq x y := by
  subst h
  rw [cast_rfl] at hxy
  exact heq_of_eq hxy

/-- The boundary of relative chains, induced by the boundary of the chains of `X`. -/
def boundary (n : ℕ) : RelativeCubicalChain X A R (n + 1) →ₗ[R] RelativeCubicalChain X A R n :=
  Submodule.mapQ _ _ (NormalizedCubicalChain.boundary X R n)
    (NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)

@[simp]
theorem boundary_mk {n : ℕ} (g : NormalizedCubicalChain X R (n + 1)) :
    boundary X R A n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (NormalizedCubicalChain.boundary X R n g) :=
  Submodule.mapQ_apply _ _ _ g

/-- Reindexing commutes with the relative boundary. -/
theorem boundary_cast {n m : ℕ} (h : n = m) (g : RelativeCubicalChain X A R (n + 1)) :
    boundary X R A m (cast X R A (congrArg Nat.succ h) g) =
      cast X R A h (boundary X R A n g) := by
  subst h
  simp

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary X R A n ∘ₗ boundary X R A (n + 1) = 0 := by
  rw [boundary, boundary,
    ← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_boundary R A (n + 1))
      (hg := NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)]
  simp only [NormalizedCubicalChain.boundary_boundary, Submodule.mapQ_zero]

section Map

variable {X A} {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {B : Set Y} {C : Set Z}

/-- The relative chains pushed forward along a map of pairs `f : (X, A) → (Y, B)`. -/
def map (f : C(X, Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    RelativeCubicalChain X A R n →ₗ[R] RelativeCubicalChain Y B R n :=
  Submodule.mapQ _ _ (NormalizedCubicalChain.map R f n)
    (NormalizedCubicalChain.supportedIn_le_comap_map R hf n)

@[simp]
theorem map_mk (f : C(X, Y)) (hf : Set.MapsTo f A B) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    map R f hf n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (NormalizedCubicalChain.map R f n g) :=
  Submodule.mapQ_apply _ _ _ g

/-- Reindexing commutes with maps of relative chains. -/
theorem map_cast (f : C(X, Y)) (hf : Set.MapsTo f A B) {n m : ℕ} (h : n = m)
    (g : RelativeCubicalChain X A R n) :
    map R f hf m (cast X R A h g) = cast Y R B h (map R f hf n g) := by
  subst h
  simp

@[simp]
theorem map_id (n : ℕ) : map R (ContinuousMap.id X) (Set.mapsTo_id A) n = LinearMap.id := by
  unfold map
  simp only [NormalizedCubicalChain.map_id, Submodule.mapQ_id]

theorem map_comp (g : C(Y, Z)) (hg : Set.MapsTo g B C) (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (n : ℕ) : map R (g.comp f) (hg.comp hf) n = map R g hg n ∘ₗ map R f hf n := by
  unfold map
  simp only [NormalizedCubicalChain.map_comp]
  exact Submodule.mapQ_comp _ _ _ _ _ (NormalizedCubicalChain.supportedIn_le_comap_map R hf n)
    (NormalizedCubicalChain.supportedIn_le_comap_map R hg n)

/-- The relative boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    map R f hf n ∘ₗ boundary X R A n = boundary Y R B n ∘ₗ map R f hf (n + 1) := by
  unfold map boundary
  rw [← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_boundary R A n)
      (hg := NormalizedCubicalChain.supportedIn_le_comap_map R hf n),
    ← Submodule.mapQ_comp (hf := NormalizedCubicalChain.supportedIn_le_comap_map R hf (n + 1))
      (hg := NormalizedCubicalChain.supportedIn_le_comap_boundary R B n)]
  simp only [NormalizedCubicalChain.map_boundary]

end Map

end RelativeCubicalChain

end TauCeti

end
