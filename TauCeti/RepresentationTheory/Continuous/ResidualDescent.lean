/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix

/-!
# Residual descent of continuous representations with discrete coefficients

Let `Γ` be a compact topological group and `K` a field with the discrete topology, for instance
`AlgebraicClosure (ZMod p)`. A continuous homomorphism `ρ : Γ →* GL_n(K)`, where `GL_n(K)`
carries the units topology, takes only finitely many values: its image is a compact subset of a
discrete space. Hence only finitely many field elements occur as matrix entries of
`ρ`. When `K` is algebraic over a finite field `F`, these entries generate a finite subfield `k`
of `K`, and `ρ` takes values in `GL_n(k)`. Since the entries of `ρ g⁻¹` are entries of `ρ`, any
subring of `K` containing the entries works, so `ρ` descends to every finite `k' ⊇ k`.

## Main definitions

* `TauCeti.ResidualDescent.entries ρ`: the set of matrix entries of the values of `ρ`.
* `TauCeti.ResidualDescent.descend ρ f hf h`: for an injective ring map `f : R →+* K` whose range
  contains the entries of `ρ`, the homomorphism `Γ →* GL_n(R)` through which `ρ` factors.
* `TauCeti.ResidualDescent.entryField F ρ`: the subfield of `K` generated over `F` by the entries.

## Main results

* `TauCeti.ResidualDescent.finite_range`: a continuous `ρ` has finite image.
* `TauCeti.ResidualDescent.map_descend`: `ρ` is the composite of `descend` with `GL_n(R) → GL_n(K)`.
* `TauCeti.ResidualDescent.continuous_descend`: the descended homomorphism is continuous.
* `TauCeti.ResidualDescent.exists_finite_descend`: for `K` algebraic over a finite field `F`, a
  continuous `ρ` is the image of a continuous `Γ →* GL_n(k)` for a finite subfield `k`.
* `TauCeti.ResidualDescent.finite_entryField`: for `K` algebraic over a finite field `F`, the
  entries generate a finite field.

## References

* J.-P. Serre, *Sur les représentations modulaires de degré 2 de Gal(ℚ-bar/ℚ)*, Duke Math. J. 54
  (1987), 179–230, 1.1, p. 180.
* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, revised version (2007) of Current
  Developments in Mathematics 1995, §2.1, p. 53.
-/

public section

open Matrix

namespace TauCeti.ResidualDescent

variable {Γ : Type*} [Group Γ] {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix entries of the values of `ρ : Γ →* GL_n(K)`. -/
def entries (ρ : Γ →* GL n K) : Set K := {x | ∃ g i j, (ρ g : Matrix n n K) i j = x}

theorem mem_entries (ρ : Γ →* GL n K) (g : Γ) (i j : n) : (ρ g : Matrix n n K) i j ∈ entries ρ :=
  ⟨g, i, j, rfl⟩

section Descend

variable {R : Type*} [CommRing R] (ρ : Γ →* GL n K) (f : R →+* K)

/-- The matrix over `R` whose entries are preimages under `f` of the entries of `ρ g`. -/
@[expose] noncomputable def descendMatrix (g : Γ) : Matrix n n R :=
  Matrix.of fun i j ↦ Function.invFun f ((ρ g : Matrix n n K) i j)

variable {ρ f}

theorem map_descendMatrix (h : entries ρ ⊆ Set.range f) (g : Γ) :
    (descendMatrix ρ f g).map f = ρ g := by
  ext i j
  exact Function.invFun_eq (h (mem_entries ρ g i j))

/-- **Descent of coefficients.** If `f : R →+* K` is injective and its range contains the matrix
entries of `ρ`, then `ρ` factors through `GL_n(R) → GL_n(K)`. -/
@[expose] noncomputable def descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) :
    Γ →* GL n R where
  toFun g :=
    { val := descendMatrix ρ f g
      inv := descendMatrix ρ f g⁻¹
      val_inv := Matrix.map_injective hf <| by
        dsimp only
        rw [Matrix.map_mul, map_descendMatrix h, map_descendMatrix h, Matrix.map_one _ f.map_zero
          f.map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      inv_val := Matrix.map_injective hf <| by
        dsimp only
        rw [Matrix.map_mul, map_descendMatrix h, map_descendMatrix h, Matrix.map_one _ f.map_zero
          f.map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one] }
  map_one' := Units.ext <| Matrix.map_injective hf <| by
    dsimp only
    rw [Units.val_one, Matrix.map_one _ f.map_zero f.map_one, map_descendMatrix h, map_one,
      Units.val_one]
  map_mul' g g' := Units.ext <| Matrix.map_injective hf <| by
    dsimp only
    rw [Units.val_mul, Matrix.map_mul, map_descendMatrix h, map_descendMatrix h,
      map_descendMatrix h, map_mul, Units.val_mul]

theorem coe_descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) (g : Γ) :
    (descend hf h g : Matrix n n R) = descendMatrix ρ f g :=
  rfl

/-- `ρ` is the composite of `descend` with `GL_n(R) → GL_n(K)`. -/
@[simp]
theorem map_descend (hf : Function.Injective f) (h : entries ρ ⊆ Set.range f) (g : Γ) :
    Matrix.GeneralLinearGroup.map f (descend hf h g) = ρ g :=
  Units.ext (map_descendMatrix h g)

section EntryField

variable (F : Type*) [Field F] [Algebra F K]

/-- The subfield of `K` generated over `F` by the matrix entries of `ρ`. -/
def entryField (ρ : Γ →* GL n K) : IntermediateField F K :=
  IntermediateField.adjoin F (entries ρ)

theorem entries_subset_entryField (ρ : Γ →* GL n K) : entries ρ ⊆ entryField F ρ :=
  IntermediateField.subset_adjoin F (entries ρ)

theorem entries_subset_range_entryField (ρ : Γ →* GL n K) :
    entries ρ ⊆ Set.range (algebraMap (entryField F ρ) K) :=
  fun x hx ↦ ⟨⟨x, entries_subset_entryField F ρ hx⟩, rfl⟩

end EntryField

end Descend

variable [TopologicalSpace Γ] [TopologicalSpace K]

/-- Each matrix entry of a continuous `ρ : Γ →* GL_n(K)` is continuous. -/
theorem continuous_entry {ρ : Γ →* GL n K} (hρ : Continuous ρ) (i j : n) :
    Continuous fun g ↦ (ρ g : Matrix n n K) i j :=
  ((Units.continuous_val (M := Matrix n n K)).comp hρ).matrix_elem i j

variable [DiscreteTopology K]

/-- The descended homomorphism is continuous for every topology on `R`: its matrix entries are
functions of the entries of `ρ`, which take values in the discrete space `K`. -/
theorem continuous_descend {R : Type*} [CommRing R] [TopologicalSpace R]
    {ρ : Γ →* GL n K} (hρ : Continuous ρ) {f : R →+* K} (hf : Function.Injective f)
    (h : entries ρ ⊆ Set.range f) : Continuous (descend hf h) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    exact (continuous_of_discreteTopology (f := Function.invFun f)).comp (continuous_entry hρ i j)
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    have : (fun g ↦ ((descend hf h g)⁻¹ : GL n R) i j) =
        fun g ↦ Function.invFun f (((ρ g)⁻¹ : GL n K) i j) := by
      ext g
      rw [← map_inv, ← map_inv]
      rfl
    rw [this]
    exact (continuous_of_discreteTopology (f := Function.invFun f)).comp
      (((Units.continuous_coe_inv (M := Matrix n n K)).comp hρ).matrix_elem i j)

variable [CompactSpace Γ]

/-- **Finite image.** A continuous homomorphism from a compact group to `GL_n(K)`, `K` discrete,
takes finitely many values. -/
theorem finite_range {ρ : Γ →* GL n K} (hρ : Continuous ρ) : (Set.range ρ).Finite :=
  (isCompact_range hρ).finite_of_discrete

/-- Only finitely many field elements are matrix entries of a continuous `ρ`. -/
theorem finite_entries {ρ : Γ →* GL n K} (hρ : Continuous ρ) : (entries ρ).Finite := by
  have : entries ρ = ⋃ (i : n) (j : n), Set.range fun g ↦ (ρ g : Matrix n n K) i j := by
    ext x
    simp [entries, Set.mem_iUnion]
    tauto
  rw [this]
  exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
    (isCompact_range (continuous_entry hρ i j)).finite_of_discrete

section EntryField

variable (F : Type*) [Field F] [Algebra F K]

/-- For `K` algebraic over `F`, the entries of a continuous `ρ` generate a finite extension
of `F`. -/
theorem finiteDimensional_entryField [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) : FiniteDimensional F (entryField F ρ) := by
  have := (finite_entries hρ).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

/-- **Residual descent.** For `K` algebraic over a finite field `F`, the entries of a continuous
`ρ` generate a finite field. -/
theorem finite_entryField [Finite F] [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) : Finite (entryField F ρ) :=
  have := finiteDimensional_entryField F hρ
  Module.finite_of_finite F

/-- **Residual descent.** For `K` algebraic over a finite field `F` and `Γ` compact, a continuous
`ρ : Γ →* GL_n(K)` is the image of a continuous `Γ →* GL_n(k)` for a finite subfield `k` of `K`. -/
theorem exists_finite_descend [Finite F] [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) :
    ∃ (k : IntermediateField F K) (ρk : Γ →* GL n k), Finite k ∧ Continuous ρk ∧
      ∀ g, Matrix.GeneralLinearGroup.map (algebraMap k K) (ρk g) = ρ g :=
  ⟨entryField F ρ, descend (algebraMap (entryField F ρ) K).injective
    (entries_subset_range_entryField F ρ), finite_entryField F hρ,
    continuous_descend hρ _ _, map_descend _ _⟩

end EntryField

end TauCeti.ResidualDescent
