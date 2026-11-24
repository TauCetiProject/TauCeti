/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Descent of coefficients of homomorphisms into `GL_n`

Let `ρ : Γ →* GL_n(K)` be a homomorphism from a group to the general linear group over a
commutative ring `K`, and let `f : R →+* K` be an injective ring map whose range contains every
matrix entry of every value of `ρ`. Since the entries of `ρ g⁻¹` are entries of `ρ`, the inverse
of each matrix lifts as well, and `ρ` factors uniquely through `GL_n(R) → GL_n(K)`.

## Main definitions

* `TauCeti.CoefficientDescent.entries ρ`: the set of matrix entries of the values of `ρ`.
* `TauCeti.CoefficientDescent.descend hf h`: for an injective ring map `f : R →+* K` whose range
  contains the entries of `ρ`, the homomorphism `Γ →* GL_n(R)` through which `ρ` factors.
* `TauCeti.CoefficientDescent.entryField F ρ`: for a field `K`, the subfield of `K` generated
  over `F` by the entries.

## Main results

* `TauCeti.CoefficientDescent.map_descend`: `ρ` is the composite of `descend` with
  `GL_n(R) → GL_n(K)`.
* `TauCeti.CoefficientDescent.eq_descend_iff`: `descend` is the unique such factorization.
* `TauCeti.CoefficientDescent.entries_subset_range_of_le`: the entries lie in every intermediate
  field containing `entryField F ρ`, so `ρ` descends to each of them.
-/

public section

open Matrix

namespace TauCeti.CoefficientDescent

variable {Γ : Type*} [Group Γ] {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {K : Type*} [CommRing K]

/-- The matrix entries of the values of `ρ : Γ →* GL_n(K)`. -/
def entries (ρ : Γ →* GL n K) : Set K := {x | ∃ g i j, (ρ g : Matrix n n K) i j = x}

@[simp]
theorem mem_entries_iff {ρ : Γ →* GL n K} {x : K} :
    x ∈ entries ρ ↔ ∃ g i j, (ρ g : Matrix n n K) i j = x :=
  Iff.rfl

theorem mem_entries (ρ : Γ →* GL n K) (g : Γ) (i j : n) : (ρ g : Matrix n n K) i j ∈ entries ρ :=
  ⟨g, i, j, rfl⟩

section Descend

variable {R : Type*} [CommRing R] (ρ : Γ →* GL n K) (f : R →+* K)

/-- The matrix over `R` whose entries are preimages under `f` of the entries of `ρ g`. -/
private noncomputable def descendMatrix (g : Γ) : Matrix n n R :=
  Matrix.of fun i j ↦ Function.invFun f ((ρ g : Matrix n n K) i j)

variable {ρ f}

private theorem map_descendMatrix (h : entries ρ ⊆ Set.range f) (g : Γ) :
    (descendMatrix ρ f g).map f = ρ g := by
  ext i j
  exact Function.invFun_eq (h (mem_entries ρ g i j))

private theorem descendMatrix_one (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) :
    descendMatrix ρ f 1 = 1 :=
  Matrix.map_injective hf <| by
    dsimp only
    rw [map_descendMatrix h, map_one, Units.val_one, Matrix.map_one _ f.map_zero f.map_one]

private theorem descendMatrix_mul (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f)
    (g g' : Γ) :
    descendMatrix ρ f g * descendMatrix ρ f g' = descendMatrix ρ f (g * g') :=
  Matrix.map_injective hf <| by
    dsimp only
    rw [Matrix.map_mul, map_descendMatrix h, map_descendMatrix h, map_descendMatrix h, map_mul,
      Units.val_mul]

/-- **Descent of coefficients.** If `f : R →+* K` is injective and its range contains the matrix
entries of `ρ`, then `ρ` factors through `GL_n(R) → GL_n(K)`. -/
noncomputable def descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) :
    Γ →* GL n R where
  toFun g :=
    { val := descendMatrix ρ f g
      inv := descendMatrix ρ f g⁻¹
      val_inv := by rw [descendMatrix_mul hf h, mul_inv_cancel, descendMatrix_one hf h]
      inv_val := by rw [descendMatrix_mul hf h, inv_mul_cancel, descendMatrix_one hf h] }
  map_one' := Units.ext (descendMatrix_one hf h)
  map_mul' g g' := Units.ext (descendMatrix_mul hf h g g').symm

@[simp]
theorem map_coe_descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) (g : Γ) :
    (descend hf h g : Matrix n n R).map f = ρ g :=
  map_descendMatrix h g

@[simp]
theorem map_descend_apply (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) (g : Γ)
    (i j : n) : f ((descend hf h g : Matrix n n R) i j) = (ρ g : Matrix n n K) i j :=
  congrFun (congrFun (map_coe_descend hf h g) i) j

/-- `ρ` is the composite of `descend` with `GL_n(R) → GL_n(K)`. -/
@[simp]
theorem map_descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) (g : Γ) :
    Matrix.GeneralLinearGroup.map f (descend hf h g) = ρ g :=
  Units.ext (map_descendMatrix h g)

theorem map_comp_descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) :
    (Matrix.GeneralLinearGroup.map f).comp (descend hf h) = ρ :=
  MonoidHom.ext (map_descend hf h)

/-- **Uniqueness of the descent.** `descend` is the only homomorphism `Γ →* GL_n(R)` whose
composite with `GL_n(R) → GL_n(K)` is `ρ`. -/
theorem eq_descend_iff (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f)
    {ψ : Γ →* GL n R} :
    ψ = descend hf h ↔ ∀ g, Matrix.GeneralLinearGroup.map f (ψ g) = ρ g := by
  refine ⟨fun hψ g ↦ hψ ▸ map_descend hf h g, fun hψ ↦ MonoidHom.ext fun g ↦ ?_⟩
  exact Matrix.GeneralLinearGroup.map_injective hf ((hψ g).trans (map_descend hf h g).symm)

end Descend

end CommRing

section EntryField

variable {K : Type*} [Field K] (F : Type*) [Field F] [Algebra F K]

/-- The subfield of `K` generated over `F` by the matrix entries of `ρ`. -/
def entryField (ρ : Γ →* GL n K) : IntermediateField F K :=
  IntermediateField.adjoin F (entries ρ)

theorem entryField_def (ρ : Γ →* GL n K) :
    entryField F ρ = IntermediateField.adjoin F (entries ρ) :=
  (rfl)

theorem entryField_le_iff {ρ : Γ →* GL n K} {L : IntermediateField F K} :
    entryField F ρ ≤ L ↔ entries ρ ⊆ L :=
  IntermediateField.adjoin_le_iff

theorem entries_subset_entryField (ρ : Γ →* GL n K) : entries ρ ⊆ entryField F ρ :=
  IntermediateField.subset_adjoin F (entries ρ)

/-- The entries of `ρ` lie in the image of every intermediate field containing `entryField F ρ`,
so `ρ` descends to any such field via `descend`. -/
theorem entries_subset_range_of_le {ρ : Γ →* GL n K} {L : IntermediateField F K}
    (hL : entryField F ρ ≤ L) : entries ρ ⊆ Set.range (algebraMap L K) :=
  fun x hx ↦ ⟨⟨x, hL (entries_subset_entryField F ρ hx)⟩, rfl⟩

end EntryField

end TauCeti.CoefficientDescent
