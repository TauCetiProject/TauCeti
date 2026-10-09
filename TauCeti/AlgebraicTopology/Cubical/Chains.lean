/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.AlgebraicTopology.Cubical.SingularCube
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# The normalized cubical singular chain complex

For a ring `A` and a topological space `X`, the cubical `n`-chains are the free
`A`-module on the singular `n`-cubes of `X`, and the cubical boundary of a singular
`(n + 1)`-cube `s` is Massey's

`∂ s = ∑ᵢ (-1)ⁱ (Bᵢ s - Aᵢ s)`,

where `Aᵢ s` and `Bᵢ s` are the faces of `s` at height `0` and `1` in coordinate `i` (counted
from `0`). It squares to zero by the cubical face identity.

The chains supported on degenerate cubes (cubes that do not depend on one of their coordinates)
form a subcomplex: in the boundary of a cube that does not depend on its coordinate `i`, the two
faces in coordinate `i` cancel, and the faces in the other coordinates are degenerate. The
quotient by this subcomplex is the normalized cubical chain complex `C^□_*(X; A)`. Without this
normalization the cubical chains of a point would have nonzero homology in every degree.

A continuous map sends degenerate cubes to degenerate cubes and commutes with faces, so the
normalized cubical chain complex is a functor of the space.

## Main definitions

* `TauCeti.SingularCube.boundary`: the cubical boundary on cubical chains.
* `TauCeti.SingularCube.degenerateChains`: the chains supported on degenerate cubes.
* `TauCeti.cubicalChainComplex A X`: the normalized cubical chain complex `C^□_*(X; A)`.
* `TauCeti.cubicalChainComplexFunctor A`: the normalized cubical chain complex as a functor
  on topological spaces.

## Main results

* `TauCeti.SingularCube.boundary_comp_boundary`: the cubical boundary squares to zero.
* `TauCeti.SingularCube.degenerateChains_le_comap_boundary`: the boundary of a degenerate chain
  is degenerate.

## References

* W. S. Massey, *Singular Homology Theory*, Chapter II.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, §5.2.
-/

public section

noncomputable section

open CategoryTheory

universe u v

namespace TauCeti

namespace SingularCube

variable (A : Type u) [Ring A] (X : Type v) [TopologicalSpace X] {Y Z : Type*}
  [TopologicalSpace Y] [TopologicalSpace Z]

/-- The **cubical boundary** `∂ s = ∑ᵢ (-1)ⁱ (Bᵢ s - Aᵢ s)` on cubical chains with coefficients
in `A`, where `Aᵢ s = s.face i 0` and `Bᵢ s = s.face i 1`. -/
def boundary (n : ℕ) : (SingularCube X (n + 1) →₀ A) →ₗ[A] (SingularCube X n →₀ A) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
    (Finsupp.lmapDomain A A (face · i 1) - Finsupp.lmapDomain A A (face · i 0))

variable {A X} in
/-- The cubical boundary of a single cube. -/
@[simp]
lemma boundary_single {n : ℕ} (s : SingularCube X (n + 1)) (a : A) :
    boundary A X n (Finsupp.single s a) = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      (Finsupp.single (s.face i 1) a - Finsupp.single (s.face i 0) a) := by
  simp [boundary]

/-- The cubical boundary squares to zero. -/
@[simp]
theorem boundary_comp_boundary (n : ℕ) : boundary A X n ∘ₗ boundary A X (n + 1) = 0 := by
  refine Finsupp.lhom_ext fun s a ↦ ?_
  simp only [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, map_sub,
    ← Finset.sum_sub_distrib, Finset.smul_sum, LinearMap.zero_apply]
  -- the terms cancel in pairs by the cubical face identity
  refine (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_).trans
    (sum_sum_neg_one_pow_smul_eq_zero (fun k l ↦
      (Finsupp.single ((s.face k 1).face l 1) a - Finsupp.single ((s.face k 1).face l 0) a) -
        (Finsupp.single ((s.face k 0).face l 1) a - Finsupp.single ((s.face k 0).face l 0) a))
      fun i j h ↦ ?_)
  · simp only [pow_add, mul_smul, smul_sub]
  · simp only [face_face s h]
    abel

variable {A X} in
/-- The cubical boundary squares to zero, evaluated on a chain. -/
@[simp]
lemma boundary_boundary {n : ℕ} (c : SingularCube X (n + 2) →₀ A) :
    boundary A X n (boundary A X (n + 1) c) = 0 :=
  LinearMap.congr_fun (boundary_comp_boundary A X n) c

/-- Postcomposition with a continuous map commutes with the cubical boundary. -/
theorem lmapDomain_comp_boundary (f : C(Y, Z)) (n : ℕ) :
    Finsupp.lmapDomain A A f.comp ∘ₗ boundary A Y n =
      boundary A Z n ∘ₗ Finsupp.lmapDomain A A f.comp := by
  refine Finsupp.lhom_ext fun s a ↦ ?_
  simp [map_sum, map_zsmul, map_sub]

/-- The **degenerate cubical chains**: the chains supported on degenerate singular cubes. -/
def degenerateChains (n : ℕ) : Submodule A (SingularCube X n →₀ A) :=
  Finsupp.supported A A {s | s.IsDegenerate}

variable {A X} in
/-- A chain is degenerate when every cube in its support is degenerate. -/
lemma mem_degenerateChains {n : ℕ} {c : SingularCube X n →₀ A} :
    c ∈ degenerateChains A X n ↔ ∀ s ∈ c.support, s.IsDegenerate :=
  Finsupp.mem_supported A c

variable {A X} in
/-- A multiple of a degenerate cube is a degenerate chain. -/
lemma single_mem_degenerateChains {n : ℕ} {s : SingularCube X n} (hs : s.IsDegenerate) (a : A) :
    Finsupp.single s a ∈ degenerateChains A X n :=
  Finsupp.single_mem_supported A a hs

/-- In degree `0` there are no degenerate chains. -/
@[simp]
lemma degenerateChains_zero : degenerateChains A X 0 = ⊥ := by
  simp [degenerateChains, not_isDegenerate_zero]

/-- The cubical boundary maps degenerate chains to degenerate chains. -/
theorem degenerateChains_le_comap_boundary (n : ℕ) :
    degenerateChains A X (n + 1) ≤ (degenerateChains A X n).comap (boundary A X n) := by
  rw [degenerateChains, Finsupp.supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨i, t, rfl⟩ := isDegenerate_iff_exists_eq_degeneracy.1 hs
  rw [SetLike.mem_coe, Submodule.mem_comap, boundary_single]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_of_tower_mem _ _ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · exact sub_mem (single_mem_degenerateChains (isDegenerate_face_degeneracy t hj 1) (1 : A))
      (single_mem_degenerateChains (isDegenerate_face_degeneracy t hj 0) (1 : A))

/-- Postcomposition with a continuous map sends degenerate chains to degenerate chains. -/
theorem degenerateChains_le_comap_lmapDomain (f : C(Y, Z)) (n : ℕ) :
    degenerateChains A Y n ≤
      (degenerateChains A Z n).comap (Finsupp.lmapDomain A A f.comp) := by
  rw [← Submodule.map_le_iff_le_comap, degenerateChains, degenerateChains,
    Finsupp.lmapDomain_supported]
  exact Finsupp.supported_mono (Set.image_subset_iff.2 fun _ hs ↦ hs.comp f)

end SingularCube

open SingularCube

variable (A : Type u) [Ring A]

/-- The **normalized cubical chain complex** `C^□_*(X; A)`: cubical chains with coefficients in
`A` modulo the degenerate chains, with the cubical boundary. -/
abbrev cubicalChainComplex (X : Type v) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{max u v} A) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of A ((SingularCube X n →₀ A) ⧸ degenerateChains A X n))
    (fun n ↦ ModuleCat.ofHom ((degenerateChains A X (n + 1)).mapQ (degenerateChains A X n)
      (boundary A X n) (degenerateChains_le_comap_boundary A X n)))
    fun n ↦ by
      ext : 1
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ← Submodule.mapQ_comp]
      simp only [boundary_comp_boundary, Submodule.mapQ_zero, ModuleCat.hom_zero]

variable {A}

/-- The differential of the normalized cubical chain complex is induced by the cubical
boundary. -/
lemma cubicalChainComplex_d_mk {X : Type v} [TopologicalSpace X] {n : ℕ}
    (c : SingularCube X (n + 1) →₀ A) :
    ((cubicalChainComplex A X).d (n + 1) n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (p := degenerateChains A X n) (boundary A X n c) := by
  simp only [ChainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

variable (A)

/-- The chain map of normalized cubical chain complexes induced by a continuous map. -/
def cubicalChainMap {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    cubicalChainComplex A X ⟶ cubicalChainComplex A Y :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom ((degenerateChains A X n).mapQ
      (degenerateChains A Y n) (Finsupp.lmapDomain A A f.comp)
      (degenerateChains_le_comap_lmapDomain A f n)))
    fun n ↦ by
      ext : 1
      simp only [cubicalChainComplex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      rw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
      simp only [lmapDomain_comp_boundary]

variable {A}

/-- The chain map induced by a continuous map postcomposes each cube with it. -/
@[simp]
lemma cubicalChainMap_f_mk {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (c : SingularCube X n →₀ A) :
    ((cubicalChainMap A f).f n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (p := degenerateChains A Y n) (Finsupp.mapDomain f.comp c) :=
  (rfl)

variable (A)

/-- The normalized cubical chain complex `C^□_*(-; A)` as a functor on topological spaces. -/
@[expose]
def cubicalChainComplexFunctor : TopCat.{v} ⥤ ChainComplex (ModuleCat.{max u v} A) ℕ where
  obj X := cubicalChainComplex A X
  map f := cubicalChainMap A f.hom
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext ?_
    have h : ((ContinuousMap.id X).comp : SingularCube X n → SingularCube X n) = id :=
      funext ContinuousMap.id_comp
    simp only [cubicalChainMap, HomologicalComplex.id_f, ModuleCat.hom_id, ModuleCat.hom_ofHom,
      TopCat.hom_id, h, Finsupp.lmapDomain_id, Submodule.mapQ_id]
  map_comp {X Y Z} f g := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext ?_
    have h : ((g.hom.comp f.hom).comp : SingularCube X n → SingularCube Z n) =
        g.hom.comp ∘ f.hom.comp :=
      funext fun s ↦ ContinuousMap.comp_assoc _ _ s
    simp only [cubicalChainMap, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, TopCat.hom_comp, h, Finsupp.lmapDomain_comp]
    rw [Submodule.mapQ_comp]

variable {A}

/-- The functor `C^□_*(-; A)` sends a space to its normalized cubical chain complex. -/
@[simp]
lemma cubicalChainComplexFunctor_obj (X : TopCat.{v}) :
    (cubicalChainComplexFunctor A).obj X = cubicalChainComplex A X :=
  (rfl)

/-- The functor `C^□_*(-; A)` sends a continuous map to its induced chain map. -/
@[simp]
lemma cubicalChainComplexFunctor_map {X Y : TopCat.{v}} (f : X ⟶ Y) :
    (cubicalChainComplexFunctor A).map f = cubicalChainMap A f.hom :=
  (rfl)

end TauCeti
