/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Hom
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomologyZero
public import TauCeti.Topology.PathSpace.Moore

/-!
# The augmented DG algebra of chains on the Moore loop space

For a pointed space `(B, b)`, the Moore loop space `Ω_b B = MooreLoopSpace B b` is a topological
monoid, strictly associative and strictly unital under concatenation.  Its normalized cubical
chains `C_*(Ω_b B; R)`, with the Pontryagin product, `C_n` in cohomological degree `-n` and the
boundary as differential, form an augmented differential graded algebra: the DG algebra over
which the DG local systems on `(B, b)` are right modules.

A based map `f : (B, b) → (B', b')` induces the continuous monoid homomorphism
`MooreLoopSpace.map f`, hence a morphism of augmented DG algebras
`C_*(Ωf) : C_*(Ω_b B; R) → C_*(Ω_{b'} B'; R)`, functorially in `f`.

## Main definitions

* `TauCeti.loopChainAlgebra B b R`: the algebra `C_*(Ω_b B; R)`.
* `TauCeti.loopChainAugmentation B b R`: its augmentation.
* `TauCeti.loopChainMap R f hf`: the DG algebra morphism `C_*(Ωf)` of a based map.
* `TauCeti.loopChainToGroupAlgebra B b R`: the algebra map to the group algebra `R[π₁(B, b)]`,
  the zeroth-homology projection `loopZeroChainToGroupAlgebra` in dimension zero and zero in
  positive dimension.

## Main results

* `TauCeti.loopChain_isDGAlgebra`: `C_*(Ω_b B; R)` is a differential graded algebra.
* `TauCeti.loopChainMap_lof`, `TauCeti.loopChainAugmentation_lof_zero`,
  `TauCeti.loopChainAugmentation_lof_succ`: the values on chains of a given dimension.
* `TauCeti.loopChainMap_id`, `TauCeti.loopChainMap_comp`: functoriality.
* `TauCeti.loopChainAugmentation_comp_loopChainMap`: compatibility with the augmentations.
* `TauCeti.loopChainToGroupAlgebra_differential`,
  `TauCeti.loopChainToGroupAlgebra_eq_zero_of_mem`: it kills boundaries and elements of nonzero
  cohomological degree.
* `TauCeti.loopChainToGroupAlgebra_loopChainMap`: naturality in based maps.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

section Algebra

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- The **chain algebra of the Moore loop space**: `C_*(Ω_b B; R)`, the normalized cubical chains
of the Moore loops at `b`, with the Pontryagin product. -/
abbrev loopChainAlgebra : Type _ := normalizedCubicalChainAlgebra (MooreLoopSpace B b) R

/-- **`C_*(Ω_b B; R)` is a differential graded algebra**, with the chains of dimension `n` in
cohomological degree `-n` and the boundary as differential. -/
theorem loopChain_isDGAlgebra :
    IsDGAlgebra (R := R) (A := loopChainAlgebra B b R) (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) :=
  cubicalChain_isDGAlgebra (MooreLoopSpace B b) R

/-- The **augmentation** of `C_*(Ω_b B; R)`, induced by the map to a point. -/
def loopChainAugmentation : DGAlgAugmentation (loopChain_isDGAlgebra B b R) :=
  cubicalChainAugmentation (MooreLoopSpace B b) R

variable {B b R}

/-- The augmentation of a `0`-chain of Moore loops. -/
@[simp]
theorem loopChainAugmentation_lof_zero (y : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    loopChainAugmentation B b R (cubicalChainLof (MooreLoopSpace B b) R 0 y) =
      NormalizedCubicalChain.augment (MooreLoopSpace B b) R y := by
  rw [loopChainAugmentation, cubicalChainAugmentation_lof, cubicalChainAugmentLof_zero]

/-- The augmentation vanishes on chains of Moore loops of positive dimension. -/
@[simp]
theorem loopChainAugmentation_lof_succ (k : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R (k + 1)) :
    loopChainAugmentation B b R (cubicalChainLof (MooreLoopSpace B b) R (k + 1) y) = 0 := by
  rw [loopChainAugmentation, cubicalChainAugmentation_lof,
    cubicalChainAugmentLof_of_ne_zero (Nat.succ_ne_zero k)]

end Algebra

section Map

variable {B B' B'' : Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  {b : B} {b' : B'} {b'' : B''} (R : Type*) [CommRing R]

/-- The **morphism of DG algebras `C_*(Ωf)`** induced by a based map `f : (B, b) → (B', b')`. -/
def loopChainMap (f : C(B, B')) (hf : f b = b') :
    DGAlgHom (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B' b' R) :=
  cubicalChainDGAlgHom R (MooreLoopSpace.map f hf)

/-- `C_*(Ωf)` on a chain of dimension `n` is the push-forward along `Ωf`. -/
@[simp]
theorem loopChainMap_lof (f : C(B, B')) (hf : f b = b') (n : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainMap R f hf (cubicalChainLof (MooreLoopSpace B b) R n y) =
      cubicalChainLof (MooreLoopSpace B' b') R n
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf).toContinuousMap n y) := by
  rw [loopChainMap, cubicalChainDGAlgHom_lof]

/-- The identity map induces the identity. -/
@[simp]
theorem loopChainMap_id :
    loopChainMap R (.id B) (ContinuousMap.id_apply b) =
      DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  rw [loopChainMap, MooreLoopSpace.map_id, cubicalChainDGAlgHom_id]

/-- The morphism induced by a composite is the composite of the induced morphisms. -/
theorem loopChainMap_comp (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b') :
    loopChainMap R (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (loopChainMap R g hg).comp (loopChainMap R f hf) := by
  rw [loopChainMap, MooreLoopSpace.map_comp g f hg hf, cubicalChainDGAlgHom_comp]
  rfl

/-- The morphisms induced by based maps are compatible with the augmentations. -/
theorem loopChainAugmentation_comp_loopChainMap (f : C(B, B')) (hf : f b = b') :
    (loopChainAugmentation B' b' R).comp (loopChainMap R f hf) = loopChainAugmentation B b R :=
  cubicalChainAugmentation_comp_dgAlgHom _

end Map

section DegreeZero

universe u

variable (B : Type u) [TopologicalSpace B] (b : B) (R : Type u) [CommRing R]

/-- The component of `loopChainToGroupAlgebra` in dimension `n`: the class map in dimension zero and
zero in positive dimensions. -/
private def loopChainToGroupAlgebraComponent :
    (n : ℕ) → NormalizedCubicalChain (MooreLoopSpace B b) R n →ₗ[R]
      MonoidAlgebra R (FundamentalGroup B b)
  | 0 => loopZeroChainToGroupAlgebra B b R
  | _ + 1 => 0

variable {B b R}

private theorem loopChainToGroupAlgebraComponent_zero :
    loopChainToGroupAlgebraComponent B b R 0 = loopZeroChainToGroupAlgebra B b R :=
  (rfl)

private theorem loopChainToGroupAlgebraComponent_eq_zero {n : ℕ} (h : n ≠ 0)
    (x : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainToGroupAlgebraComponent B b R n x = 0 := by
  cases n with
  | zero => exact absurd rfl h
  | succ n => rfl

variable (B b R)

/-- **The degree-zero ring map**: the algebra map from the chains on the Moore loop space to the
group ring of the fundamental group, which is `loopZeroChainToGroupAlgebra` on `0`-chains and zero
on chains of positive dimension. -/
def loopChainToGroupAlgebra : loopChainAlgebra B b R →ₐ[R] MonoidAlgebra R (FundamentalGroup B b) :=
  DirectSum.toAlgebra R _ (loopChainToGroupAlgebraComponent B b R)
    (by simp [loopChainToGroupAlgebraComponent])
    (fun {i j} x y ↦ by
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · subst hi hj
          simp [loopChainToGroupAlgebraComponent]
        · rw [loopChainToGroupAlgebraComponent_eq_zero (by omega),
            loopChainToGroupAlgebraComponent_eq_zero hj, mul_zero]
      · rw [loopChainToGroupAlgebraComponent_eq_zero (by omega),
          loopChainToGroupAlgebraComponent_eq_zero hi, zero_mul])

variable {B b R}

private theorem loopChainToGroupAlgebra_lof_component (n : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R n y) =
      loopChainToGroupAlgebraComponent B b R n y := by
  rw [loopChainToGroupAlgebra, DirectSum.toAlgebra_apply, cubicalChainLof, DirectSum.lof_eq_of]
  exact DirectSum.toSemiring_of _ _ _ n y

/-- The degree-zero ring map on a `0`-chain is the projection to the group algebra. -/
@[simp]
theorem loopChainToGroupAlgebra_lof_zero (y : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R 0 y) =
      loopZeroChainToGroupAlgebra B b R y :=
  loopChainToGroupAlgebra_lof_component 0 y

/-- The degree-zero ring map kills the chains of positive dimension. -/
@[simp]
theorem loopChainToGroupAlgebra_lof_succ (k : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R (k + 1)) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R (k + 1) y) = 0 :=
  (loopChainToGroupAlgebra_lof_component (k + 1) y).trans
    (loopChainToGroupAlgebraComponent_eq_zero k.succ_ne_zero y)

/-- The degree-zero ring map kills boundaries. -/
@[simp]
theorem loopChainToGroupAlgebra_differential (a : loopChainAlgebra B b R) :
    loopChainToGroupAlgebra B b R (cubicalChainDifferential (MooreLoopSpace B b) R a) = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    cases n with
    | zero =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_zero, map_zero]
    | succ k =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_succ]
      cases k with
      | zero =>
        rw [loopChainToGroupAlgebra_lof_zero]
        exact loopZeroChainToGroupAlgebra_boundary y
      | succ k => simp
  | add x y hx hy => simp [hx, hy]

/-- The degree-zero ring map kills homogeneous elements of nonzero cohomological degree. -/
theorem loopChainToGroupAlgebra_eq_zero_of_mem {i : ℤ} (hi : i ≠ 0) {a : loopChainAlgebra B b R}
    (ha : a ∈ cubicalChainGrading (MooreLoopSpace B b) R i) :
    loopChainToGroupAlgebra B b R a = 0 := by
  rcases (mem_cubicalChainGrading_iff _ _).1 ha with rfl | ⟨n, y, hn, rfl⟩
  · exact map_zero _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact loopChainToGroupAlgebra_lof_succ k y

-- The component-wise form of `loopChainToGroupAlgebra_loopChainMap`.
private theorem loopChainToGroupAlgebraComponent_map {B' : Type u} [TopologicalSpace B']
    {b' : B'} (f : C(B, B')) (hf : f b = b') (n : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainToGroupAlgebraComponent B' b' R n
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf : C(_, _)) n y) =
      MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf)
        (loopChainToGroupAlgebraComponent B b R n y) := by
  cases n with
  | zero =>
    rw [loopChainToGroupAlgebraComponent_zero, loopChainToGroupAlgebraComponent_zero]
    exact loopZeroChainToGroupAlgebra_map f hf y
  | succ n =>
    rw [loopChainToGroupAlgebraComponent_eq_zero n.succ_ne_zero,
      loopChainToGroupAlgebraComponent_eq_zero n.succ_ne_zero, map_zero]

/-- **Naturality of the degree-zero ring map**: it intertwines `C_*(Ωf)` with the map of group
rings induced by `π₁(f)`. -/
@[simp]
theorem loopChainToGroupAlgebra_loopChainMap {B' : Type u} [TopologicalSpace B'] {b' : B'}
    (f : C(B, B')) (hf : f b = b') (a : loopChainAlgebra B b R) :
    loopChainToGroupAlgebra B' b' R (loopChainMap R f hf a) =
      MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf)
        (loopChainToGroupAlgebra B b R a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    rw [← DirectSum.lof_eq_of R, loopChainMap_lof, loopChainToGroupAlgebra_lof_component,
      loopChainToGroupAlgebra_lof_component]
    exact loopChainToGroupAlgebraComponent_map f hf n y
  | add x y hx hy => simp only [map_add, hx, hy]

end DegreeZero

end TauCeti

end
