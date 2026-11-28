/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import TauCeti.Algebra.Module.Lattice
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Extending full lattices along a change of coefficients

Let `f : V →ₗ[K] W` exhibit `W` as the scalar extension of `V` from `K` to `F`.
Given coefficient rings `R → S` acting compatibly on these modules, the extended
lattice of `L` is the `S`-span of `f '' L` in `W`. When `F` is the fraction field of
`S`, this construction takes full lattices to full lattices.

An integral basis of `L` gives a basis of the extended lattice whose vectors are
the images under `f` of the original basis vectors. This lets one compute with
several lattices after extending their common ambient space.
-/

public section

open Module Submodule

variable {R S K F V W ι : Type*} [CommRing R] [CommRing S] [CommRing K]
  [Algebra R K] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [Module S W]
  [IsScalarTower R K W] [IsScalarTower R S W] {f : V →ₗ[K] W} {L : Submodule R V}

section Basis

variable [CommRing F] [Algebra K F] [Module F W] [IsScalarTower K F W]

/-- The extended lattice is spanned by the scalar extension of any lattice basis. -/
theorem Module.Basis.span_image_eq_span_range_isBaseChange [L.IsFullLattice K]
    (b : Basis ι R L) (hf : IsBaseChange F f) :
    span S (f '' (L : Set V)) = span S (Set.range (hf.basis (b.extendOfIsFullLattice K))) := by
  conv_lhs => rw [← b.span_range_extendOfIsFullLattice (K := K),
    ← f.coe_restrictScalars R, ← Submodule.map_coe, Submodule.map_span, span_span_of_tower,
    ← Set.range_comp]
  congr 2
  ext i
  simp [IsBaseChange.basis_apply]

variable [Algebra S F] [IsDomain S] [Nontrivial F] [IsTorsionFree S F] [IsScalarTower S F W]

/-- The integral basis of the extended lattice obtained by applying the base change map
to the given basis vectors. -/
noncomputable def Module.Basis.baseChangeOfIsFullLattice [L.IsFullLattice K]
    (b : Basis ι R L) (hf : IsBaseChange F f) : Basis ι S (span S (f '' (L : Set V))) :=
  ((hf.basis (b.extendOfIsFullLattice K)).restrictScalars S).map
    (LinearEquiv.ofEq _ _ (b.span_image_eq_span_range_isBaseChange hf).symm)

@[simp]
theorem Module.Basis.baseChangeOfIsFullLattice_apply [L.IsFullLattice K]
    (b : Basis ι R L) (hf : IsBaseChange F f) (i : ι) :
    (b.baseChangeOfIsFullLattice (S := S) hf i : W) = f (b i) := by
  simp [baseChangeOfIsFullLattice, IsBaseChange.basis_apply]

end Basis

variable [Field F] [Algebra K F] [Module F W] [IsScalarTower K F W]
  [Algebra S F] [IsScalarTower S F W] [IsFractionRing S F]

/-- The span over the new coefficient ring of the image of a full lattice is full in
the scalar extension of its ambient space. -/
theorem IsBaseChange.isFullLattice_span_image (hf : IsBaseChange F f)
    (L : Submodule R V) [L.IsFullLattice K] : (span S (f '' (L : Set V))).IsFullLattice F := by
  obtain ⟨s, hs⟩ := IsLattice.fg K L
  rw [← hs, ← f.coe_restrictScalars R, ← Submodule.map_coe, Submodule.map_span,
    span_span_of_tower, LinearMap.coe_restrictScalars]
  apply isFullLattice_span (s.finite_toSet.image _)
  have h := IsFullLattice.span_eq_top (A := K) (M := L)
  rw [← hs, span_span_of_tower] at h
  rw [← span_span_of_tower K, span_image, h, Submodule.map_top]
  exact hf.span_range_eq_top
