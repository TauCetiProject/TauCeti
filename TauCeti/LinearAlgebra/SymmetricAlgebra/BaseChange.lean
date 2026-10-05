/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Graded base change of symmetric algebras

The canonical equivalence `S ⊗[R] Sym(M) ≃ Sym(S ⊗[R] M)` identifies the scalar extension
of every homogeneous piece with the corresponding homogeneous piece over `S`. Both directions
are bundled as graded algebra maps, so the equivalence can be used on projective spectra.
This supplies the homogeneous-coordinate comparison needed to construct families of projective
linear transformations. No freeness, flatness, or finite generation of the module is required.

The underlying equivalence is `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`; the grading
on its source is Mathlib's `GradedAlgebra.baseChange`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective actions and homogeneous spaces.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The scalar-extension equivalence sends a pure tensor with homogeneous right factor to an
element of the same degree. -/
private theorem scalarTensorBialgEquiv_tmul_mem_homogeneousSubmodule {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule R M n) (s : S) :
    scalarTensorBialgEquiv (k := R) (K := S) (s ⊗ₜ[R] x) ∈
      homogeneousSubmodule S (S ⊗[R] M) n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      scalarTensorBialgEquiv_tmul_one]
    exact Submodule.algebraMap_mem _
  | add x y n _ _ hx hy =>
    simpa only [TensorProduct.tmul_add, map_add] using Submodule.add_mem _ hx hy
  | mem_mul m hm n x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [← one_mul s, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
      scalarTensorBialgEquiv_tmul_ι]
    simpa only [Nat.add_comm] using
      SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule S (S ⊗[R] M) (1 ⊗ₜ[R] m)) hx

/-- The base-change equivalence preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule {n : ℕ}
    {x : S ⊗[R] SymmetricAlgebra R M}
    (hx : x ∈ (homogeneousSubmodule R M n).baseChange S) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  obtain ⟨x, rfl⟩ := Submodule.toBaseChange_surjective' S _ hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    simpa only [Submodule.coe_toBaseChange_tmul] using
      scalarTensorBialgEquiv_tmul_mem_homogeneousSubmodule x.property s
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using Submodule.add_mem _ hx hy

/-- The inverse base-change equivalence also preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_symm_mem_baseChange {n : ℕ}
    {x : SymmetricAlgebra S (S ⊗[R] M)}
    (hx : x ∈ homogeneousSubmodule S (S ⊗[R] M) n) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
      (homogeneousSubmodule R M n).baseChange S := by
  have hι (z : S ⊗[R] M) :
      (scalarTensorBialgEquiv (k := R) (K := S)).symm (SymmetricAlgebra.ι S _ z) ∈
        (homogeneousSubmodule R M 1).baseChange S := by
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      rw [scalarTensorBialgEquiv_symm_ι_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem s (ι_mem_homogeneousSubmodule R M m)
    | add x y hx hy => simpa only [map_add, Submodule.coe_add] using Submodule.add_mem _ hx hy
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [AlgHomClass.commutes]
    simpa only [homogeneousSubmodule, pow_zero, map_one, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply] using
      (Submodule.tmul_mem_baseChange_of_mem s (Submodule.algebraMap_mem (R := R)
        (A := SymmetricAlgebra R M) 1))
  | add x y n _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | mem_mul m hm n x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul]
    simpa only [Nat.add_comm] using
      (SetLike.mul_mem_graded (A := fun n ↦ (homogeneousSubmodule R M n).baseChange S)
        (hι m) hx)

/-- Membership in a homogeneous piece is preserved and reflected by scalar extension. -/
@[simp]
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff {n : ℕ}
    (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n ↔
      x ∈ (homogeneousSubmodule R M n).baseChange S := by
  constructor
  · intro hx
    simpa only [BialgEquiv.symm_apply_apply] using
      scalarTensorBialgEquiv_symm_mem_baseChange hx
  · exact scalarTensorBialgEquiv_mem_homogeneousSubmodule

/-- The inverse comparison preserves and reflects homogeneous degree as well. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_mem_baseChange_iff {n : ℕ}
    (x : SymmetricAlgebra S (S ⊗[R] M)) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
        (homogeneousSubmodule R M n).baseChange S ↔
      x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  rw [← scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff, BialgEquiv.apply_symm_apply]

/-- The image of the scalar-extended degree-`n` piece is exactly the degree-`n` piece of the
symmetric algebra on the scalar-extended module. -/
@[simp]
theorem map_baseChange_homogeneousSubmodule (n : ℕ) :
    ((homogeneousSubmodule R M n).baseChange S).map
        (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearMap =
      homogeneousSubmodule S (S ⊗[R] M) n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact scalarTensorBialgEquiv_mem_homogeneousSubmodule hy
  · intro hx
    exact ⟨(scalarTensorBialgEquiv (k := R) (K := S)).symm x,
      scalarTensorBialgEquiv_symm_mem_baseChange hx, BialgEquiv.apply_symm_apply _ _⟩

/-- Scalar extension identifies the degree-`n` homogeneous pieces as `S`-modules. -/
noncomputable def homogeneousSubmoduleBaseChangeEquiv (n : ℕ) :
    (homogeneousSubmodule R M n).baseChange S ≃ₗ[S]
      homogeneousSubmodule S (S ⊗[R] M) n :=
  (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearEquiv.ofSubmodules _ _
    (map_baseChange_homogeneousSubmodule n)

/-- The degreewise equivalence is the restriction of the scalar-extension equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_apply (n : ℕ)
    (x : (homogeneousSubmodule R M n).baseChange S) :
    (homogeneousSubmoduleBaseChangeEquiv n x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S) x := (rfl)

/-- The inverse degreewise equivalence is the restriction of the inverse scalar-extension
equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_symm_apply (n : ℕ)
    (x : homogeneousSubmodule S (S ⊗[R] M) n) :
    ((homogeneousSubmoduleBaseChangeEquiv n).symm x : S ⊗[R] SymmetricAlgebra R M) =
      (scalarTensorBialgEquiv (k := R) (K := S)).symm x := (rfl)

/-- The canonical scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHom :
    (fun n ↦ (homogeneousSubmodule R M n).baseChange S) →ₐᵍ[S]
      homogeneousSubmodule S (S ⊗[R] M) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_mem_homogeneousSubmodule

/-- The inverse scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHomSymm :
    homogeneousSubmodule S (S ⊗[R] M) →ₐᵍ[S]
      (fun n ↦ (homogeneousSubmodule R M n).baseChange S) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm.toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_symm_mem_baseChange

/-- The forward graded map is the existing scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHom_apply (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorGradedAlgHom x = scalarTensorBialgEquiv (k := R) (K := S) x := (rfl)

/-- The inverse graded map is the inverse scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHomSymm_apply (x : SymmetricAlgebra S (S ⊗[R] M)) :
    scalarTensorGradedAlgHomSymm x = (scalarTensorBialgEquiv (k := R) (K := S)).symm x := (rfl)

/-- The scalar-extension comparison commutes with maps induced by linear maps. -/
theorem scalarTensorBialgEquiv_comp_map {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    (scalarTensorBialgEquiv (k := R) (K := S) (M := N)).toAlgEquiv.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) (SymmetricAlgebra.map R f)) =
      (SymmetricAlgebra.map S (f.baseChange S)).comp
        (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply SymmetricAlgebra.algHom_ext
    ext m
    simp

end TauCeti.SymmetricAlgebra
