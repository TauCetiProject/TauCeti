/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.DGAlgebra
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Functoriality and augmentation of the DG algebra of cubical chains of a monoid

For a continuous monoid homomorphism `φ : G →ₜ* G'` between topological monoids, pushing chains
forward along `φ` is multiplicative for the Pontryagin product and sends the unit to the unit, so
it induces a morphism of differential graded algebras
`cubicalChainDGAlgHom R φ : C^□_*(G; R) → C^□_*(G'; R)`, functorially in `φ`.

The augmentation of `0`-chains, extended by zero to the chains of positive dimension, is an
augmentation of the DG algebra `C^□_*(G; R)` in the sense of
`TauCeti.Algebra.Homology.DG.Algebra.Augmentation`: a DG algebra morphism to `R`, placed in
degree zero with zero differential.  The morphisms induced by continuous monoid homomorphisms are
compatible with these augmentations.

## Main definitions

* `TauCeti.cubicalChainAlgHom R φ`: the algebra homomorphism induced by `φ : G →ₜ* G'`.
* `TauCeti.cubicalChainDGAlgHom R φ`: the same as a morphism of DG algebras.
* `TauCeti.cubicalChainAugmentation G R`: the augmentation of `C^□_*(G; R)`.

## Main results

* `TauCeti.cubicalChainDGAlgHom_id`, `TauCeti.cubicalChainDGAlgHom_comp`: functoriality.
* `TauCeti.cubicalChainAugmentation_comp_dgAlgHom`: compatibility with the augmentations.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti

variable {G G' G'' : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']
  [Monoid G''] [TopologicalSpace G''] [ContinuousMul G''] {R : Type*} [CommRing R]

open NormalizedCubicalChain

section Hom

variable (R) in
/-- The algebra homomorphism `C^□_*(G; R) → C^□_*(G'; R)` induced by a continuous monoid
homomorphism `φ : G →ₜ* G'`: the push-forward of chains, dimension by dimension. -/
def cubicalChainAlgHom (φ : G →ₜ* G') :
    cubicalChainAlgebra G R →ₐ[R] cubicalChainAlgebra G' R :=
  DirectSum.toAlgebra R _
    (fun n ↦ cubicalChainLof G' R n ∘ₗ map R φ.toContinuousMap n)
    (by
      change cubicalChainLof G' R 0 (map R φ.toContinuousMap 0 (one G R)) = 1
      rw [NormalizedCubicalChain.map_one, DirectSum.lof_eq_of]
      rfl)
    (fun {i j} a b ↦ by
      change cubicalChainLof G' R (i + j) (map R φ.toContinuousMap (i + j) (mul G R i j a b)) =
        cubicalChainLof G' R i (map R φ.toContinuousMap i a) *
          cubicalChainLof G' R j (map R φ.toContinuousMap j b)
      rw [NormalizedCubicalChain.map_mul, cubicalChainLof_mul])

/-- The induced algebra homomorphism on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainAlgHom_lof (φ : G →ₜ* G') (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainAlgHom R φ (cubicalChainLof G R n y) =
      cubicalChainLof G' R n (map R φ.toContinuousMap n y) := by
  rw [DirectSum.lof_eq_of]
  exact DirectSum.toAddMonoid_of _ _ _

variable (R) in
/-- The **morphism of DG algebras** `C^□_*(G; R) → C^□_*(G'; R)` induced by a continuous monoid
homomorphism. -/
def cubicalChainDGAlgHom (φ : G →ₜ* G') :
    DGAlgHom (cubicalChain_isDGAlgebra G R) (cubicalChain_isDGAlgebra G' R) where
  toAlgHom := cubicalChainAlgHom R φ
  map_mem := fun {i a} ha ↦ by
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨n, y, hn, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · change cubicalChainAlgHom R φ (cubicalChainLof G R n y) ∈ _
      rw [cubicalChainAlgHom_lof]
      exact (mem_cubicalChainGrading_iff G' R).2 (Or.inr ⟨n, _, hn, rfl⟩)
  map_d' := fun a ↦ by
    change cubicalChainDifferential G' R (cubicalChainAlgHom R φ a) =
      cubicalChainAlgHom R φ (cubicalChainDifferential G R a)
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n y =>
      rw [← DirectSum.lof_eq_of R, cubicalChainAlgHom_lof]
      rcases n with _ | k
      · rw [cubicalChainDifferential_lof_zero, cubicalChainDifferential_lof_zero, map_zero]
      · rw [cubicalChainDifferential_lof_succ, cubicalChainDifferential_lof_succ,
          cubicalChainAlgHom_lof, ← LinearMap.comp_apply (boundary G' R k), ← map_boundary,
          LinearMap.comp_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- The induced DG algebra morphism on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainDGAlgHom_lof (φ : G →ₜ* G') (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainDGAlgHom R φ (cubicalChainLof G R n y) =
      cubicalChainLof G' R n (map R φ.toContinuousMap n y) :=
  cubicalChainAlgHom_lof φ n y

/-- Two DG algebra morphisms out of `C^□_*(G; R)` agree if they agree on chains of each
dimension. -/
theorem cubicalChain_dgAlgHom_ext {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
    [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    {f g : DGAlgHom (cubicalChain_isDGAlgebra G R) hB}
    (h : ∀ n y, f (cubicalChainLof G R n y) = g (cubicalChainLof G R n y)) : f = g :=
  DGAlgHom.ext fun a ↦ by
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n y =>
      rw [← DirectSum.lof_eq_of R]
      exact h n y
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The identity homomorphism induces the identity. -/
@[simp]
theorem cubicalChainDGAlgHom_id :
    cubicalChainDGAlgHom R (ContinuousMonoidHom.id G) =
      DGAlgHom.id (cubicalChain_isDGAlgebra G R) :=
  cubicalChain_dgAlgHom_ext fun n y ↦ by
    rw [cubicalChainDGAlgHom_lof, DGAlgHom.id_apply]
    congr 1
    exact LinearMap.congr_fun (map_id R n) y

/-- The induced morphism of a composite is the composite of the induced morphisms. -/
theorem cubicalChainDGAlgHom_comp (ψ : G' →ₜ* G'') (φ : G →ₜ* G') :
    cubicalChainDGAlgHom R (ψ.comp φ) =
      (cubicalChainDGAlgHom R ψ).comp (cubicalChainDGAlgHom R φ) :=
  cubicalChain_dgAlgHom_ext fun n y ↦ by
    rw [DGAlgHom.comp_apply, cubicalChainDGAlgHom_lof, cubicalChainDGAlgHom_lof,
      cubicalChainDGAlgHom_lof, map_comp_apply]
    rfl

end Hom

section Augmentation

variable (G R) in
/-- The augmentation on the chains of dimension `n`: the augmentation of `0`-chains, and zero in
positive dimension. -/
def cubicalChainAugmentLof (n : ℕ) : NormalizedCubicalChain G R n →ₗ[R] R :=
  if h : n = 0 then augment G R ∘ₗ cast R h else 0

omit [Monoid G] [ContinuousMul G] in
/-- The augmentation on `0`-chains. -/
@[simp]
theorem cubicalChainAugmentLof_zero (y : NormalizedCubicalChain G R 0) :
    cubicalChainAugmentLof G R 0 y = augment G R y := by
  simp [cubicalChainAugmentLof, cast_rfl]

omit [Monoid G] [ContinuousMul G] in
/-- The augmentation vanishes on chains of positive dimension. -/
theorem cubicalChainAugmentLof_of_ne_zero {n : ℕ} (hn : n ≠ 0)
    (y : NormalizedCubicalChain G R n) : cubicalChainAugmentLof G R n y = 0 := by
  simp [cubicalChainAugmentLof, hn]

variable (G R) in
/-- The augmentation `C^□_*(G; R) → R` as an algebra homomorphism. -/
def cubicalChainAugmentAlgHom : cubicalChainAlgebra G R →ₐ[R] R :=
  DirectSum.toAlgebra R _ (cubicalChainAugmentLof G R)
    (by
      change cubicalChainAugmentLof G R 0 (one G R) = 1
      rw [cubicalChainAugmentLof_zero, augment_one])
    (fun {i j} a b ↦ by
      change cubicalChainAugmentLof G R (i + j) (mul G R i j a b) =
        cubicalChainAugmentLof G R i a * cubicalChainAugmentLof G R j b
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [cubicalChainAugmentLof_zero a, cubicalChainAugmentLof_zero b, ← augment_mul]
          exact cubicalChainAugmentLof_zero _
        · rw [cubicalChainAugmentLof_of_ne_zero (show 0 + j ≠ 0 by omega),
            cubicalChainAugmentLof_of_ne_zero (show j ≠ 0 by omega) b, mul_zero]
      · rw [cubicalChainAugmentLof_of_ne_zero (show i + j ≠ 0 by omega),
          cubicalChainAugmentLof_of_ne_zero (show i ≠ 0 by omega) a, zero_mul])

/-- The augmentation on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainAugmentAlgHom_lof (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainAugmentAlgHom G R (cubicalChainLof G R n y) = cubicalChainAugmentLof G R n y := by
  rw [DirectSum.lof_eq_of]
  exact DirectSum.toAddMonoid_of (fun n ↦ (cubicalChainAugmentLof G R n).toAddMonoidHom) n y

variable (G R) in
/-- The **augmentation of the DG algebra of cubical chains**: the augmentation of `0`-chains,
extended by zero, as a DG algebra morphism to the ground ring. -/
def cubicalChainAugmentation : DGAlgAugmentation (cubicalChain_isDGAlgebra G R) where
  toAlgHom := cubicalChainAugmentAlgHom G R
  map_mem := fun {i a} ha ↦ by
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨n, y, hn, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · change cubicalChainAugmentAlgHom G R (cubicalChainLof G R n y) ∈ _
      rw [cubicalChainAugmentAlgHom_lof, mem_trivialGrading_iff]
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · left
        omega
      · right
        exact cubicalChainAugmentLof_of_ne_zero (by omega) y
  map_d' := fun a ↦ by
    change (0 : R →ₗ[R] R) (cubicalChainAugmentAlgHom G R a) =
      cubicalChainAugmentAlgHom G R (cubicalChainDifferential G R a)
    rw [LinearMap.zero_apply]
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n y =>
      rw [← DirectSum.lof_eq_of R]
      rcases n with _ | k
      · rw [cubicalChainDifferential_lof_zero, map_zero]
      · rw [cubicalChainDifferential_lof_succ, cubicalChainAugmentAlgHom_lof]
        rcases k with _ | j
        · rw [cubicalChainAugmentLof_zero, ← LinearMap.comp_apply, augment_boundary,
            LinearMap.zero_apply]
        · rw [cubicalChainAugmentLof_of_ne_zero (by omega)]
    | add a b ha hb => rw [map_add, map_add, ← ha, ← hb, add_zero]

/-- The augmentation on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainAugmentation_lof (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainAugmentation G R (cubicalChainLof G R n y) = cubicalChainAugmentLof G R n y :=
  cubicalChainAugmentAlgHom_lof n y

/-- The morphisms induced by continuous monoid homomorphisms are compatible with the
augmentations. -/
theorem cubicalChainAugmentation_comp_dgAlgHom (φ : G →ₜ* G') :
    (cubicalChainAugmentation G' R).comp (cubicalChainDGAlgHom R φ) =
      cubicalChainAugmentation G R :=
  cubicalChain_dgAlgHom_ext fun n y ↦ by
    rw [DGAlgHom.comp_apply, cubicalChainDGAlgHom_lof, cubicalChainAugmentation_lof,
      cubicalChainAugmentation_lof]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cubicalChainAugmentLof_zero, cubicalChainAugmentLof_zero, ← LinearMap.comp_apply,
        augment_map]
    · rw [cubicalChainAugmentLof_of_ne_zero (by omega), cubicalChainAugmentLof_of_ne_zero
        (by omega)]

end Augmentation

end TauCeti

end
