/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum
public import TauCeti.Algebra.Homology.GradedCochainComplex
public import TauCeti.Algebra.CharP.Two

/-!
# Total-degree tensor complexes in characteristic two

The finite slot sum raises total degree by one when each factor differential does.
Over a ground ring of characteristic two it therefore defines a cochain complex whenever the
factor differentials square to zero. This uses the dependent-family `slotSum` and
`totalDegreePiece` constructions, so tensor powers and tensor products of different complexes
share the same grading and differential API.

The construction accepts families of submodules, without requiring a direct-sum decomposition:
its terms are precisely their total-degree tensor spans. In applications to graded modules,
these are the usual total-degree pieces.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct
open CategoryTheory

namespace TauCeti.PiTensorProduct

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
  {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

open Classical in
/-- The total-degree tensor cochain complex in characteristic two. Its terms are the tensor
pieces and its differential is the restriction of the slot sum of the factor differentials. -/
noncomputable def cochainComplex [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex (totalDegreePiece ι ℳ) (slotSum ι d) (isHomogeneous_slotSum hdeg)
    (fun _ x ↦ LinearMap.congr_fun
      (slotSum_comp_slotSum (fun _ ↦ add_self_eq_zero_of_charTwo R) hd) x)

open Classical in
/-- The degree-`n` term is the total-degree tensor piece. -/
@[simp]
theorem cochainComplex_X [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n = ModuleCat.of R (totalDegreePiece ι ℳ n) := by
  rw [cochainComplex, gradedCochainComplex_X]

open Classical in
/-- The complex differential is the restricted slot sum, transported along the
identifications of its source and target degree pieces. -/
@[simp]
theorem cochainComplex_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).d n (n + 1) =
      eqToHom (cochainComplex_X ℳ d hdeg hd n) ≫
        ModuleCat.ofHom ((slotSum ι d).restrict
          (p := totalDegreePiece ι ℳ n) (q := totalDegreePiece ι ℳ (n + 1))
          fun _ hz ↦ (isHomogeneous_slotSum hdeg).map_mem hz) ≫
        eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1)).symm :=
  gradedCochainComplex_d n

open Classical in
/-- Under the degree-piece identification, the complex differential applies the slot sum
of the factor differentials to the underlying tensor. -/
theorem cochainComplex_d_apply [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : totalDegreePiece ι ℳ n) :
    CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1))
        ((cochainComplex ℳ d hdeg hd).d n (n + 1)
          (CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd n).symm z)) =
      (⟨slotSum ι d z, (isHomogeneous_slotSum hdeg).map_mem z.2⟩ :
        totalDegreePiece ι ℳ (n + 1)) :=
  gradedCochainComplex_d_apply n z

open Classical in
/-- The degree-`n` term of the tensor cochain complex identified with its total-degree piece
as a linear equivalence. -/
noncomputable def cochainComplexXEquiv [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n ≃ₗ[R] totalDegreePiece ι ℳ n :=
  gradedCochainComplexXEquiv (hdeg := isHomogeneous_slotSum hdeg)
    (hsq := fun _ x ↦ LinearMap.congr_fun
      (slotSum_comp_slotSum (fun _ ↦ add_self_eq_zero_of_charTwo R) hd) x) n

open Classical in
/-- Under the degree-piece equivalence, the complex differential applies the slot sum
of the factor differentials to the underlying tensor. -/
theorem cochainComplexXEquiv_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : (cochainComplex ℳ d hdeg hd).X n) :
    (cochainComplexXEquiv ℳ d hdeg hd (n + 1)
        (((cochainComplex ℳ d hdeg hd).d n (n + 1)).hom z) : ⨂[R] i, M i) =
      slotSum ι d (cochainComplexXEquiv ℳ d hdeg hd n z) := by
  dsimp only [cochainComplexXEquiv]
  exact gradedCochainComplexXEquiv_d n z

end TauCeti.PiTensorProduct
