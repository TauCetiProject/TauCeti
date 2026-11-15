/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.Trace.Projective

/-!
# Hattori–Stallings trace

For a finite projective left module over an arbitrary ring `R`, the Hattori–Stallings trace
of an endomorphism takes values in the additive cyclic quotient `R / [R, R]`, implemented
as `TauCeti.cyclicQuotient ℤ R`. Compute it on a finite free retract by summing the diagonal
coefficients. The answer is independent of the retract and of its basis, and is cyclic
across different finite projective modules. In particular it is invariant under linear
equivalences and additive on products and split exact sequences.

Right modules are covered by taking `R` to be an opposite ring. No commutativity of `R`,
constant-rank hypothesis, or division by a group order is involved.

## References

* The Stacks Project, Sections 64.4–64.5, traces on finite projective modules.
* H. Bass, *Algebraic K-theory*, Chapter II, Section 4 (the universal trace).
-/

public section

noncomputable section

open Module

namespace Module.Basis

open LinearMap

variable {R : Type*} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The diagonal sum in the additive cyclic quotient, computed in a finite basis.
Over a noncommutative ring the codomain is an additive group, not an `R`-module. -/
def hattoriStallingsTrace {ι : Type*} [Fintype ι] (b : Basis ι R M) :
    Module.End R M →+ TauCeti.cyclicQuotient ℤ R where
  toFun f := (TauCeti.commutatorSubmodule ℤ R).mkQ (∑ i, b.repr (f (b i)) i)
  map_zero' := by simp
  map_add' f g := by
    dsimp
    simp only [map_add, Finsupp.add_apply, Finset.sum_add_distrib]
    exact (TauCeti.commutatorSubmodule ℤ R).mkQ.map_add _ _

/-- In a finite basis the universal trace is the cyclic class of the diagonal sum. -/
@[simp]
theorem hattoriStallingsTrace_apply {ι : Type*} [Fintype ι] (b : Basis ι R M)
    (f : Module.End R M) :
    b.hattoriStallingsTrace f =
      (TauCeti.commutatorSubmodule ℤ R).mkQ (∑ i, b.repr (f (b i)) i) :=
  (rfl)

/-- Cyclicity of the diagonal sum, including maps between free modules of different ranks. -/
theorem hattoriStallingsTrace_comp_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Basis ι R M) (c : Basis κ R N) (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    b.hattoriStallingsTrace (g ∘ₗ f) = c.hattoriStallingsTrace (f ∘ₗ g) := by
  simp only [hattoriStallingsTrace_apply, repr_comp_apply_apply b c,
    repr_comp_apply_apply c b, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply (Submodule.Quotient.eq _).mpr
  exact TauCeti.mul_sub_mul_mem_commutatorSubmodule ℤ R _ _

/-- Cyclicity computed in finite free retracts, without finiteness assumptions on the
modules between which the maps are defined. -/
theorem hattoriStallingsTrace_retract_comp_comm
    {F G : Type*} [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι R F) (c : Basis κ R G)
    (i : M →ₗ[R] F) (r : F →ₗ[R] M) (hr : r ∘ₗ i = .id)
    (j : N →ₗ[R] G) (s : G →ₗ[R] N) (hs : s ∘ₗ j = .id)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    b.hattoriStallingsTrace (i ∘ₗ (g ∘ₗ f) ∘ₗ r) =
      c.hattoriStallingsTrace (j ∘ₗ (f ∘ₗ g) ∘ₗ s) := by
  have h := hattoriStallingsTrace_comp_comm b c (j ∘ₗ f ∘ₗ r) (i ∘ₗ g ∘ₗ s)
  simpa only [comp_assoc, ← comp_assoc _ j s, hs, id_comp, ← comp_assoc _ i r, hr] using h

/-- The diagonal trace on a finite free retract is independent of the retract and its basis.
The retraction equations are essential: an arbitrary pair of maps is not retract data. -/
theorem hattoriStallingsTrace_retract_eq
    {F G : Type*} [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι R F) (c : Basis κ R G)
    (i : M →ₗ[R] F) (r : F →ₗ[R] M) (hr : r ∘ₗ i = .id)
    (j : M →ₗ[R] G) (s : G →ₗ[R] M) (hs : s ∘ₗ j = .id) (f : Module.End R M) :
    b.hattoriStallingsTrace (i ∘ₗ f ∘ₗ r) =
      c.hattoriStallingsTrace (j ∘ₗ f ∘ₗ s) := by
  simpa only [id_comp, comp_id] using
    hattoriStallingsTrace_retract_comp_comm b c i r hr j s hs f .id

end Module.Basis

namespace LinearMap

variable {R : Type*} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable (R M) in
/-- The Hattori–Stallings trace of an endomorphism of a finite projective left module.
It is characterized by `hattoriStallingsTrace_eq_of_retract`, so does not depend on the
finite free retract chosen in its construction. -/
def hattoriStallingsTrace [Module.Finite R M] [Module.Projective R M] :
    Module.End R M →+ TauCeti.cyclicQuotient ℤ R := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  let n := h.choose
  let r := h.choose_spec.choose
  let i := h.choose_spec.choose_spec.choose
  exact (Pi.basisFun R (Fin n)).hattoriStallingsTrace.comp
    { toFun := fun f ↦ i ∘ₗ f ∘ₗ r
      map_zero' := by simp
      map_add' := fun f g ↦ by simp [add_comp, comp_add] }

/-- The chosen retract satisfies its retraction equation and computes the canonical trace. -/
private theorem exists_hattoriStallingsTrace_retract [Module.Finite R M]
    [Module.Projective R M] :
    ∃ (n : ℕ) (r : (Fin n → R) →ₗ[R] M) (i : M →ₗ[R] Fin n → R),
      r ∘ₗ i = .id ∧ ∀ f : Module.End R M,
        hattoriStallingsTrace R M f =
          (Pi.basisFun R (Fin n)).hattoriStallingsTrace (i ∘ₗ f ∘ₗ r) := by
  classical
  -- Isolate the existential projections used to choose the data in the definition.
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨-, -, hr⟩ := h.choose_spec.choose_spec.choose_spec
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose, hr, ?_⟩
  intro f
  -- Evaluation of the additive-hom composite on the same chosen data is definitional.
  rfl

/-- Compute the Hattori–Stallings trace in any finite free retract, with any finite basis. -/
theorem hattoriStallingsTrace_eq_of_retract [Module.Finite R M] [Module.Projective R M]
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} [Fintype ι] (b : Basis ι R F)
    (i : M →ₗ[R] F) (r : F →ₗ[R] M) (hr : r ∘ₗ i = .id) (f : Module.End R M) :
    hattoriStallingsTrace R M f = b.hattoriStallingsTrace (i ∘ₗ f ∘ₗ r) := by
  obtain ⟨n, s, j, hs, htrace⟩ := exists_hattoriStallingsTrace_retract (R := R) (M := M)
  rw [htrace]
  exact Basis.hattoriStallingsTrace_retract_eq (Pi.basisFun R (Fin n)) b j s hs i r hr f

/-- On a finite free module the Hattori–Stallings trace is its diagonal sum in any basis. -/
theorem hattoriStallingsTrace_eq_of_basis [Module.Finite R M] [Module.Projective R M]
    {ι : Type*} [Fintype ι] (b : Basis ι R M) (f : Module.End R M) :
    hattoriStallingsTrace R M f = b.hattoriStallingsTrace f := by
  simpa using hattoriStallingsTrace_eq_of_retract b .id .id (by simp) f

/-- Cyclicity across arbitrary finite projective modules over a possibly noncommutative ring. -/
theorem hattoriStallingsTrace_comp_comm [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    hattoriStallingsTrace R M (g ∘ₗ f) = hattoriStallingsTrace R N (f ∘ₗ g) := by
  obtain ⟨m, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨n, s, j, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  rw [hattoriStallingsTrace_eq_of_retract (Pi.basisFun R (Fin m)) i r hr,
    hattoriStallingsTrace_eq_of_retract (Pi.basisFun R (Fin n)) j s hs]
  exact Basis.hattoriStallingsTrace_retract_comp_comm (Pi.basisFun R (Fin m))
    (Pi.basisFun R (Fin n)) i r hr j s hs f g

/-- The universal trace is invariant under conjugation. -/
@[simp]
theorem hattoriStallingsTrace_conj [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : Module.End R M) (e : M ≃ₗ[R] N) :
    hattoriStallingsTrace R N (e.conjRingEquiv f) = hattoriStallingsTrace R M f := by
  have he : e.conjRingEquiv f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := by
    ext x
    simp
  rw [he, ← hattoriStallingsTrace_comp_comm, comp_assoc, e.symm_comp, comp_id]

/-- Trace is additive on a product of finite projective modules. -/
@[simp]
theorem hattoriStallingsTrace_prodMap [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : Module.End R M) (g : Module.End R N) :
    hattoriStallingsTrace R (M × N) (f.prodMap g) =
      hattoriStallingsTrace R M f + hattoriStallingsTrace R N g := by
  have h : f.prodMap g = inl R M N ∘ₗ (f ∘ₗ fst R M N) +
      inr R M N ∘ₗ (g ∘ₗ snd R M N) := by
    ext <;> simp
  rw [h, map_add, ← hattoriStallingsTrace_comp_comm (inl R M N),
    ← hattoriStallingsTrace_comp_comm (inr R M N)]
  simp [comp_assoc]

/-- Trace additivity from a decomposition of the identity into two factorizations.
In particular this applies to a split exact sequence, even when the endomorphism does
not preserve the chosen splitting; no off-diagonal vanishing is needed. -/
theorem hattoriStallingsTrace_eq_add_of_id_decomposition
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R P] [Module.Projective R P]
    (i : M →ₗ[R] P) (r : P →ₗ[R] M) (j : N →ₗ[R] P) (s : P →ₗ[R] N)
    (h : i ∘ₗ r + j ∘ₗ s = .id) (f : Module.End R P) :
    hattoriStallingsTrace R P f =
      hattoriStallingsTrace R M (r ∘ₗ f ∘ₗ i) +
        hattoriStallingsTrace R N (s ∘ₗ f ∘ₗ j) := by
  calc
    hattoriStallingsTrace R P f = hattoriStallingsTrace R P
        (f ∘ₗ (i ∘ₗ r + j ∘ₗ s)) := by rw [h, comp_id]
    _ = _ := by
      rw [comp_add, map_add, ← comp_assoc, ← comp_assoc,
        hattoriStallingsTrace_comp_comm r, hattoriStallingsTrace_comp_comm s]

/-- On a finite free module the identity has trace equal to the cyclic class of the rank,
including rank zero. -/
theorem hattoriStallingsTrace_id_of_basis [Module.Finite R M] [Module.Projective R M]
    {ι : Type*} [Fintype ι] (b : Basis ι R M) :
    hattoriStallingsTrace R M .id =
      (TauCeti.commutatorSubmodule ℤ R).mkQ (Fintype.card ι : R) := by
  classical
  rw [hattoriStallingsTrace_eq_of_basis b, Basis.hattoriStallingsTrace_apply]
  congr 1
  simp

/-- On the zero module the Hattori–Stallings trace vanishes. -/
@[simp]
theorem hattoriStallingsTrace_eq_zero_of_subsingleton [Module.Finite R M]
    [Module.Projective R M] [Subsingleton M] (f : Module.End R M) :
    hattoriStallingsTrace R M f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

end LinearMap

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- Over a commutative ring the Hattori–Stallings trace is the cyclic class of the
finite-projective contraction trace, including on projective modules of varying local rank. -/
theorem hattoriStallingsTrace_eq_projectiveTrace (f : Module.End R M) :
    hattoriStallingsTrace R M f =
      (TauCeti.commutatorSubmodule ℤ R).mkQ (projectiveTrace R M f) := by
  classical
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let b := Pi.basisFun R (Fin n)
  have h : projectiveTrace R (Fin n → R) (i ∘ₗ f ∘ₗ r) = projectiveTrace R M f := by
    rw [← comp_assoc, projectiveTrace_cyclic r, ← comp_assoc, hr, id_comp]
  rw [hattoriStallingsTrace_eq_of_retract b i r hr, Basis.hattoriStallingsTrace_apply, ← h,
    projectiveTrace_eq_trace, trace_eq_matrix_trace R b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

end LinearMap
