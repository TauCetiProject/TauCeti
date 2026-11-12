/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Descent
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix

/-!
# Descending a finite free comodule by its coefficient matrix

A finite free comodule descends through an injective coalgebra map exactly when
every entry of its coefficient matrix lies in the image. This is the finite-basis
form of `CoalgHom.existsUnique_comoduleFactor_iff`.

See Sweedler, *Hopf Algebras*, Chapter 2, for coalgebra corestriction.
-/

public section

open scoped TensorProduct

open TauCeti TauCeti.Comodule

variable {R C D M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid D] [Module R D] [Coalgebra R D]
  [AddCommMonoid M] [Module R M] [Comodule R D M]

namespace Module.Basis

/-- For a finite free comodule, descent through a coalgebra inclusion is equivalent
to every entry of its coefficient matrix belonging to the image. -/
theorem existsUnique_comoduleFactor_iff
    [Module.Flat R C] [Module.Flat R D]
    {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (f : C →ₗc[R] D) (hf : Function.Injective f) :
    (∃! σ : Comodule R C M,
      f.toLinearMap.lTensor M ∘ₗ σ.coact = coact (R := R) (C := D)) ↔
      ∀ i j, coefficientMatrix (C := D) b i j ∈ LinearMap.range f.toLinearMap := by
  classical
  let := Fintype.ofFinite ι
  let := Module.Free.of_basis b
  constructor
  · rintro ⟨σ, hσ, _⟩ i j
    let := σ
    have heq : Corestrict f = (inferInstance : Comodule R D M) :=
      f.corestrict_eq_of_factor σ hσ
    have hc := coefficientMatrix_corestrict b f
    rw [heq] at hc
    exact ⟨coefficientMatrix (C := C) b i j, congrFun (congrFun hc i) j |>.symm⟩
  · intro h
    apply (CoalgHom.existsUnique_comoduleFactor_iff f hf).mpr
    have hb (j : ι) : coact (R := R) (C := D) (b j) ∈
        LinearMap.range (f.toLinearMap.lTensor M) := by
      rw [coact_basis_eq_sum_coefficientMatrix b]
      apply Submodule.sum_mem
      intro i _
      obtain ⟨c, hc⟩ := h i j
      have hc' : f c = coefficientMatrix (C := D) b i j := by simpa using hc
      exact ⟨b i ⊗ₜ[R] c, by simp [hc']⟩
    intro m
    rw [← b.sum_repr m, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hb j)

end Module.Basis
