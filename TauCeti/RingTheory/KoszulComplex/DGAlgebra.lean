/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.RingTheory.GradedAlgebra.Coarsen
public import TauCeti.RingTheory.KoszulComplex.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The Koszul complex as a differential graded algebra

For a linear functional `φ : M → R`, the terms `⋀ⁿ M` of the Koszul complex `K(φ)` are the
graded pieces of the exterior algebra `⋀ M`, and its differential is the restriction of the
contraction `φ ⌋ ·`. This file records the multiplicative structure of `K(φ)`: the exterior
algebra, graded with `⋀ⁿ M` in cohomological degree `-n` (`TauCeti.koszulGrading`), is a
differential graded algebra for the contraction by `φ`, which satisfies the graded Leibniz rule
`φ ⌋ (a ∧ b) = (φ ⌋ a) ∧ b + (-1) ^ n a ∧ (φ ⌋ b)` for `a ∈ ⋀ⁿ M`. A linear map `g : M → N` with
`ψ ∘ g = φ` induces a morphism of differential graded algebras `K(φ) → K(ψ)`, functorially in `g`,
which in each degree `n` is the chain map `TauCeti.koszulComplex.map` induced by `g`, namely
`⋀ⁿ g`.

Placing `⋀ⁿ M` in degree `-n` turns the homological Koszul complex into a cochain complex
concentrated in nonpositive degrees, so that its differential raises the degree by one, as
`TauCeti.IsDGAlgebra` requires. The grade involution on `⋀ⁿ M` is the sign `(-1) ^ n`, which is
also `(-1) ^ (-n)`, so the Leibniz sign is the same in either convention.

## Main definitions

* `TauCeti.koszulGrading R M`: the `ℤ`-grading of the exterior algebra with `⋀ⁿ M` in degree `-n`.
* `TauCeti.koszulComplex.mapDGAlgHom g h`: the morphism of differential graded algebras
  `K(φ) → K(ψ)` induced by a linear map `g` with `h : ψ ∘ g = φ`.

## Main results

* `TauCeti.koszulComplex.isDGAlgebra`: the exterior algebra, with the grading `koszulGrading` and
  the contraction by `φ`, is a differential graded algebra.
* `TauCeti.koszulComplex.mapDGAlgHom_id` and `TauCeti.koszulComplex.mapDGAlgHom_comp`:
  functoriality of the induced morphisms.
* `TauCeti.koszulComplex.subtype_map_f_hom_apply`: in degree `n`, the chain map
  `TauCeti.koszulComplex.map g h` is the restriction of `mapDGAlgHom g h`.

## References

* [The Stacks Project, Tags 0622 and 0624](https://stacks.math.columbia.edu/tag/0621)
-/

public section

noncomputable section

open CategoryTheory CliffordAlgebra

universe v

namespace TauCeti

variable {R : Type*} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Grading

variable (R M)

/-- The grading of the exterior algebra underlying the Koszul complex: `⋀ⁿ M` sits in degree
`-n`, and the positive degrees are zero (see `koszulGrading_apply`). It is the negative of the
grading `TauCeti.ExteriorAlgebra.integerGrading` by exterior degree. -/
def koszulGrading : ℤ → Submodule R (ExteriorAlgebra R M) :=
  coarsenGrading (ExteriorAlgebra.integerGrading R M) (-AddMonoidHom.id ℤ)

/-- The exterior algebra is a `ℤ`-graded algebra for `koszulGrading`, obtained by reindexing the
grading by exterior degree along the negation of `ℤ`. -/
instance koszulGradedAlgebra : GradedAlgebra (koszulGrading R M) :=
  inferInstanceAs (GradedAlgebra (coarsenGrading (ExteriorAlgebra.integerGrading R M)
    (-AddMonoidHom.id ℤ)))

variable {R M}

/-- The piece of degree `p` of `koszulGrading` is the piece of exterior degree `-p`. -/
theorem koszulGrading_apply (p : ℤ) :
    koszulGrading R M p = ExteriorAlgebra.integerGrading R M (-p) := by
  rw [koszulGrading]
  refine le_antisymm (coarsenGrading_le_iff.2 fun i hi ↦ ?_) ?_
  · rw [Pi.neg_apply, AddMonoidHom.id_apply] at hi
    rw [← hi, neg_neg]
  · have h := le_coarsenGrading (ExteriorAlgebra.integerGrading R M) (-AddMonoidHom.id ℤ) (-p)
    rwa [AddMonoidHom.neg_apply, AddMonoidHom.id_apply, neg_neg] at h

/-- In degree `-n`, `koszulGrading` is the `n`-th exterior power. -/
@[simp]
theorem koszulGrading_neg_natCast (n : ℕ) : koszulGrading R M (-n) = ⋀[R]^n M := by
  rw [koszulGrading_apply, neg_neg, ExteriorAlgebra.integerGrading_natCast]

/-- In positive degrees, `koszulGrading` vanishes. -/
theorem koszulGrading_of_pos {p : ℤ} (hp : 0 < p) : koszulGrading R M p = ⊥ := by
  rw [koszulGrading_apply, ExteriorAlgebra.integerGrading_of_neg (by omega)]

end Grading

namespace koszulComplex

variable (φ : Module.Dual R M)

/-- **The Koszul complex is a differential graded algebra**: the exterior algebra, with `⋀ⁿ M` in
degree `-n`, is a differential graded algebra for the contraction by `φ`. The Leibniz rule reads
`φ ⌋ (a * b) = (φ ⌋ a) * b + (-1) ^ n a * (φ ⌋ b)` for `a ∈ ⋀ⁿ M`. -/
theorem isDGAlgebra :
    IsDGAlgebra (koszulGrading R M) (contractLeft (Q := (0 : QuadraticForm R M)) φ) where
  map_mem {p _} hx := by
    rw [koszulGrading_apply] at hx ⊢
    rw [neg_add']
    exact ExteriorAlgebra.contractLeft_mem_integerGrading φ hx
  sq_zero := contractLeft_contractLeft φ
  leibniz {p a} ha b := by
    rw [koszulGrading_apply] at ha
    rw [contractLeft_mul, ExteriorAlgebra.involute_of_mem_integerGrading ha, Int.negOnePow_neg,
      smul_mul_assoc]

section Map

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {φ} {ψ : Module.Dual R N} {χ : Module.Dual R P}

/-- The morphism of differential graded algebras `K(φ) → K(ψ)` induced by a linear map
`g : M → N` with `ψ ∘ g = φ`: the map `⋀ g` of exterior algebras. In degree `n` it is the chain
map `koszulComplex.map g h` (see `subtype_map_f_hom_apply`). -/
def mapDGAlgHom (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) :
    DGAlgHom (isDGAlgebra φ) (isDGAlgebra ψ) where
  toAlgHom := ExteriorAlgebra.map g
  map_mem {p _} hx := by
    rw [koszulGrading_apply] at hx
    exact (koszulGrading_apply p).ge (ExteriorAlgebra.map_mem_integerGrading g hx)
  map_d' x := by
    rw [← h]
    exact ExteriorAlgebra.contractLeft_map g ψ x

/-- The morphism induced by `g` is the map `⋀ g` of exterior algebras. -/
@[simp]
theorem mapDGAlgHom_apply (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (x : ExteriorAlgebra R M) :
    mapDGAlgHom g h x = ExteriorAlgebra.map g x :=
  (rfl)

/-- The identity of `M` induces the identity of `K(φ)`. -/
@[simp]
theorem mapDGAlgHom_id :
    mapDGAlgHom (φ := φ) LinearMap.id (LinearMap.comp_id φ) = DGAlgHom.id (isDGAlgebra φ) := by
  ext x
  simp

/-- The morphism induced by a composite is the composite of the induced morphisms. -/
theorem mapDGAlgHom_comp (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (g' : N →ₗ[R] P)
    (h' : χ ∘ₗ g' = ψ) :
    mapDGAlgHom (g' ∘ₗ g) (by rw [← LinearMap.comp_assoc, h', h]) =
      (mapDGAlgHom g' h').comp (mapDGAlgHom g h) := by
  ext x
  simp [← ExteriorAlgebra.map_comp_map]

end Map

section ChainMap

variable {N : Type v} [AddCommGroup N] [Module R N] {φ} {ψ : Module.Dual R N}

/-- **The induced morphism acts in degree `n` as `⋀ⁿ g`**: on `⋀ⁿ M`, the morphism of
differential graded algebras induced by `g` is the degree-`n` component of the chain map
`koszulComplex.map g h`. -/
theorem subtype_map_f_hom_apply (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (n : ℕ) (x : ⋀[R]^n M) :
    (⋀[R]^n N).subtype (((map g h).f n).hom x) = mapDGAlgHom g h x := by
  rw [map_f, mapDGAlgHom_apply]
  -- `ModuleCat.hom_ofHom` does not rewrite here because the terms of `koszulComplex φ` are only
  -- definitionally the exterior powers, so the evaluation is closed up to that equality.
  exact exteriorPower.coe_map g x

end ChainMap

end koszulComplex

end TauCeti
