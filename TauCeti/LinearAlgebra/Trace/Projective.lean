/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.Contraction

/-!
# The trace of an endomorphism of a finite projective module

For a finite projective module `M` over a commutative semiring `R`, the map
`dualTensorHom : Dual R M ⊗[R] M → End R M` is an isomorphism, and the trace of an endomorphism
is its image under the contraction `Dual R M ⊗[R] M → R`, `φ ⊗ m ↦ φ m`. This is the trace of a
finite locally free module (Stacks, Tag 02DU and Tag 0BVH; Kedlaya–Liu, *Relative p-adic Hodge
theory: foundations*, §1.1).

For a related formalization of the same contraction definition, see Mathlib PR
https://github.com/leanprover-community/mathlib4/pull/44636.

Mathlib's `LinearMap.trace R M` is defined through a finite basis and is `0` when `M` has none,
so it is the trace of a finite projective module only when the module is free:
for the idempotent `e = (1, 0)` of `ℚ × ℚ`, the ideal `M = (e)` is projective but not free, and
the identity of `M` has projective trace `e` and Mathlib trace `0`
(`LinearMap.projectiveTrace_nonfree`).

## Main definitions

* `LinearMap.projectiveTrace R M`: the trace `End R M →ₗ[R] R` of a finite projective module,
  `contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm`.

## Main statements

* `LinearMap.projectiveTrace_smulRight`: the trace of `x ↦ φ x • m` is `φ m`.
* `LinearMap.projectiveTrace_cyclic`: `tr_M (g ∘ f) = tr_N (f ∘ g)` for linear maps
  `f : M → N` and `g : N → M` between finite projective modules.
* `LinearMap.projectiveTrace_eq_trace`: on finite free modules the projective trace is Mathlib's
  `LinearMap.trace`.
* `LinearMap.projectiveTrace_baseChange`: the trace commutes with extension of scalars.
* `LinearMap.projectiveTrace_prodMap`: the trace is additive on products.
* `LinearMap.algebraMap_projectiveTrace_id`: over a commutative ring, the trace of the identity is
  the locally constant rank `Module.rankAtStalk M`.
* `LinearMap.isNilpotent_projectiveTrace_of_isNilpotent`: over a commutative ring, nilpotent
  endomorphisms have nilpotent trace.

All statements except the last two hold over commutative semirings: the proofs reduce to pure
tensors `φ ⊗ m`, whose endomorphism `φ.smulRight m` has trace `φ m`
(`LinearMap.induction_on_smulRight`).
-/

public section

open Module TensorProduct

namespace LinearMap

section CommSemiring

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The trace of an endomorphism of a finite projective module: the contraction
`Dual R M ⊗[R] M → R`, `φ ⊗ m ↦ φ m`, transported along the isomorphism
`dualTensorHomEquiv R M M : Dual R M ⊗[R] M ≃ End R M`. It agrees with `LinearMap.trace` on
finite free modules (`LinearMap.projectiveTrace_eq_trace`) and, unlike it, is the trace of a
finite locally free module when `M` is not free. -/
noncomputable def projectiveTrace : (M →ₗ[R] M) →ₗ[R] R :=
  contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap

/-- The projective trace is characterised by its values on the image of `dualTensorHom`. -/
theorem projectiveTrace_comp_dualTensorHom :
    projectiveTrace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  ext x
  simp [projectiveTrace]

variable {R M}

@[simp]
theorem projectiveTrace_dualTensorHom (x : Dual R M ⊗[R] M) :
    projectiveTrace R M (dualTensorHom R M M x) = contractLeft R M x := by
  rw [← comp_apply, projectiveTrace_comp_dualTensorHom]

/-- The trace of the rank-one endomorphism `x ↦ φ x • m` is `φ m`. -/
@[simp]
theorem projectiveTrace_smulRight (φ : Dual R M) (m : M) :
    projectiveTrace R M (φ.smulRight m) = φ m := by
  rw [← dualTensorHom_tmul_eq_smulRight, projectiveTrace_dualTensorHom, contractLeft_apply]

/-- **Cyclicity of the trace** across two finite projective modules:
`tr_M (g ∘ f) = tr_N (f ∘ g)`. -/
theorem projectiveTrace_cyclic {N : Type*} [AddCommMonoid N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    projectiveTrace R M (g ∘ₗ f) = projectiveTrace R N (f ∘ₗ g) := by
  induction g using induction_on_smulRight with
  | smulRight ψ m =>
    have h₁ : ψ.smulRight m ∘ₗ f = (ψ ∘ₗ f).smulRight m := by ext; simp
    have h₂ : f ∘ₗ ψ.smulRight m = ψ.smulRight (f m) := by ext; simp
    simp [h₁, h₂]
  | add g₁ g₂ h₁ h₂ => simp [add_comp, comp_add, h₁, h₂]

theorem projectiveTrace_mul_comm (f g : Module.End R M) :
    projectiveTrace R M (f * g) = projectiveTrace R M (g * f) :=
  projectiveTrace_cyclic g f

/-- The trace is invariant under conjugation by a linear equivalence. -/
@[simp]
theorem projectiveTrace_conj {N : Type*} [AddCommMonoid N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) :
    projectiveTrace R N (e.conj f) = projectiveTrace R M f := by
  rw [e.conj_apply, ← projectiveTrace_cyclic, ← comp_assoc, e.symm_comp, id_comp]

/-- On a finite free module the projective trace is Mathlib's trace. -/
theorem projectiveTrace_eq_trace [Module.Free R M] :
    projectiveTrace R M = LinearMap.trace R M := by
  classical
  let b := Module.Free.chooseBasis R M
  ext f
  induction f using induction_on_smulRight with
  | smulRight φ m =>
    simp only [projectiveTrace_smulRight, trace_eq_matrix_trace R b, Matrix.trace,
      Matrix.diag_apply, LinearMap.toMatrix_apply, smulRight_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul]
    conv_lhs => rw [← b.sum_repr m]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  | add f g hf hg => simp [hf, hg]

/-- The trace of an endomorphism of `R` is its value at `1`. -/
@[simp]
theorem projectiveTrace_self_apply (f : R →ₗ[R] R) : projectiveTrace R R f = f 1 := by
  have : f = (LinearMap.id : Dual R R).smulRight (f 1) := by ext; simp
  rw [this]
  simp

/-- The trace on the zero module vanishes. -/
@[simp]
theorem projectiveTrace_eq_zero_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) :
    projectiveTrace R M f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

/-- The trace is additive on products: `tr (f × g) = tr f + tr g`. -/
@[simp]
theorem projectiveTrace_prodMap {N : Type*} [AddCommMonoid N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    projectiveTrace R (M × N) (f.prodMap g) = projectiveTrace R M f + projectiveTrace R N g := by
  have : f.prodMap g = inl R M N ∘ₗ (f ∘ₗ fst R M N) + inr R M N ∘ₗ (g ∘ₗ snd R M N) := by
    ext <;> simp
  rw [this, map_add, ← projectiveTrace_cyclic (inl R M N), ← projectiveTrace_cyclic (inr R M N)]
  simp [comp_assoc]

/-- **Base change of the trace**: extending scalars along `R → A` carries the trace of `f` to the
trace of `A ⊗ f`. -/
@[simp]
theorem projectiveTrace_baseChange (A : Type*) [CommSemiring A] [Algebra R A]
    (f : M →ₗ[R] M) :
    projectiveTrace A (A ⊗[R] M) (f.baseChange A) = algebraMap R A (projectiveTrace R M f) := by
  induction f using induction_on_smulRight with
  | smulRight φ m =>
    have : (φ.smulRight m).baseChange A = (φ.baseChange A).smulRight (1 ⊗ₜ m) := by
      ext x
      simp [smul_tmul']
    simp [this, Algebra.algebraMap_eq_smul_one]
  | add f g hf hg => simp [baseChange_add, hf, hg]

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The trace of a nilpotent endomorphism of a finite projective module is nilpotent. -/
theorem isNilpotent_projectiveTrace_of_isNilpotent {f : M →ₗ[R] M} (hf : IsNilpotent f) :
    IsNilpotent (projectiveTrace R M f) := by
  -- `M` is a direct summand of a finite free module `F`; transport `f` to `F`.
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hps (y : M) : p (s y) = y := congr($hs y)
  have key (j : ℕ) (x : Fin n → R) :
      ((s ∘ₗ f ∘ₗ p) ^ (j + 1)) x = s ((f ^ (j + 1)) (p x)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' (s ∘ₗ f ∘ₗ p), mul_apply_eq_comp, ih, pow_succ' f (j + 1),
        mul_apply_eq_comp]
      simp only [comp_apply, hps]
  obtain ⟨k, hk⟩ := hf
  have hf' : IsNilpotent (s ∘ₗ f ∘ₗ p) :=
    ⟨k + 1, LinearMap.ext fun x ↦ by rw [key, pow_succ, hk, zero_mul]; simp⟩
  rw [← comp_id f, ← hs, ← comp_assoc, projectiveTrace_cyclic, projectiveTrace_eq_trace]
  exact isNilpotent_trace_of_isNilpotent hf'

/-- The trace of the identity is the locally constant rank: its image in the localisation at a
prime `p` is the rank of `M` at `p`. -/
theorem algebraMap_projectiveTrace_id (p : PrimeSpectrum R) :
    algebraMap R (Localization.AtPrime p.asIdeal) (projectiveTrace R M LinearMap.id) =
      rankAtStalk M p := by
  have : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    free_of_flat_of_isLocalRing
  rw [← projectiveTrace_baseChange, baseChange_id, projectiveTrace_eq_trace, trace_id,
    rankAtStalk_eq_finrank_tensorProduct]

end CommRing

end LinearMap
