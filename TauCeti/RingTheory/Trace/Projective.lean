/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.LinearAlgebra.Trace.Projective
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Fiber
import TauCeti.RingTheory.Etale.Discriminant
import TauCeti.RingTheory.LocalProperties.Fiber
import TauCeti.RingTheory.Unramified.Fiber

/-!
# The trace of a finite projective algebra

For a commutative `R`-algebra `S` which is finitely generated and projective as an `R`-module (a
finite locally free algebra), the trace `Tr_{S/R} : S → R` sends `s` to the trace of
multiplication by `s`, computed with the trace `LinearMap.projectiveTrace` of an endomorphism of
a finite projective module. Mathlib's `Algebra.trace` is defined through a basis and vanishes on
algebras which are not free; the two agree on finite free algebras
(`Algebra.projectiveTrace_eq_trace`). The trace form is `(x, y) ↦ Tr_{S/R}(x y)`.

The trace commutes with arbitrary base change, and its value at `1` is the locally constant rank
of `S`. The main result is the trace-form criterion for étaleness: a finite projective algebra
is étale iff its trace form, read as a map `S → Hom_R(S, R)`, is bijective
(`Algebra.etale_iff_projectiveTraceForm_bijective`). Both sides can be checked on the fibres at
the primes of `R`, where the criterion is the classical one for finite algebras over a field
(`TauCeti.Algebra.etale_iff_traceForm_nondegenerate`).

## Main definitions

* `Algebra.projectiveTrace R S`: the trace `S →ₗ[R] R` of a finite projective algebra.
* `Algebra.projectiveTraceForm R S`: the trace form `(x, y) ↦ projectiveTrace R S (x * y)`.

## Main statements

* `Algebra.projectiveTrace_eq_trace`: on finite free algebras it is Mathlib's `Algebra.trace`.
* `Algebra.projectiveTrace_tmul`: compatibility with base change,
  `Tr_{A ⊗ S/A}(a ⊗ s) = a · Tr_{S/R}(s)`.
* `Algebra.algebraMap_projectiveTrace_one`: `Tr_{S/R}(1)` is the rank of `S` at every prime.
* `Algebra.projectiveTrace_prod_apply`: the trace is additive on products of algebras.
* `Algebra.etale_iff_projectiveTraceForm_bijective`: a finite projective algebra is étale iff its
  trace pairing is perfect.

## References

* The Stacks Project, Exercise 111.22.7 (02DV), the trace of a finite locally free algebra, and
  Lemma 49.3.1 (0BJF), étaleness via the discriminant.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §1.2, where the trace of a finite projective algebra and this criterion are used.
-/

public section

open scoped TensorProduct

namespace Algebra

section CommSemiring

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Module.Finite R S]
  [Module.Projective R S]

/-- The trace `Tr_{S/R} : S → R` of a finite projective algebra: `s` maps to the trace of
multiplication by `s`, as an endomorphism of the finite projective module `S`. It agrees with
`Algebra.trace` on finite free algebras (`Algebra.projectiveTrace_eq_trace`) and, unlike it, is
the trace of a finite locally free algebra when `S` is not free. -/
noncomputable def projectiveTrace : S →ₗ[R] R :=
  LinearMap.projectiveTrace R S ∘ₗ (lmul R S).toLinearMap

/-- The trace form `(x, y) ↦ Tr_{S/R}(x y)` of a finite projective algebra. -/
noncomputable def projectiveTraceForm : LinearMap.BilinForm R S :=
  (LinearMap.mul R S).compr₂ (projectiveTrace R S)

variable {R S}

theorem projectiveTrace_apply (s : S) :
    projectiveTrace R S s = LinearMap.projectiveTrace R S (lmul R S s) :=
  (rfl)

@[simp]
theorem projectiveTraceForm_apply (x y : S) :
    projectiveTraceForm R S x y = projectiveTrace R S (x * y) :=
  (rfl)

theorem projectiveTraceForm_isSymm : (projectiveTraceForm R S).IsSymm :=
  ⟨fun x y ↦ by simp [mul_comm]⟩

@[simp]
theorem projectiveTrace_algebraMap (r : R) :
    projectiveTrace R S (algebraMap R S r) = r * projectiveTrace R S 1 := by
  rw [algebraMap_eq_smul_one, map_smul, smul_eq_mul]

/-- The trace of `R` over itself is the identity. -/
@[simp]
theorem projectiveTrace_self : projectiveTrace R R = LinearMap.id := by
  ext
  simp [projectiveTrace_apply]

/-- The trace is invariant under isomorphisms of algebras. -/
@[simp]
theorem projectiveTrace_eq_of_algEquiv {T : Type*} [CommSemiring T] [Algebra R T]
    [Module.Finite R T] [Module.Projective R T] (e : S ≃ₐ[R] T) (s : S) :
    projectiveTrace R T (e s) = projectiveTrace R S s := by
  have : lmul R T (e s) = e.toLinearEquiv.conj (lmul R S s) := by
    ext t
    simp [LinearEquiv.conj_apply]
  rw [projectiveTrace_apply, this, LinearMap.projectiveTrace_conj, projectiveTrace_apply]

/-- **Base change of the trace**: `Tr_{A ⊗ S/A}(a ⊗ s) = a · Tr_{S/R}(s)`. -/
@[simp]
theorem projectiveTrace_tmul (A : Type*) [CommSemiring A] [Algebra R A] (a : A) (s : S) :
    projectiveTrace A (A ⊗[R] S) (a ⊗ₜ s) = a * algebraMap R A (projectiveTrace R S s) := by
  have : lmul A (A ⊗[R] S) (1 ⊗ₜ s) = (lmul R S s).baseChange A := by
    ext t
    simp
  have hs : a ⊗ₜ[R] s = a • (1 ⊗ₜ[R] s : A ⊗[R] S) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, projectiveTrace_apply, this, LinearMap.projectiveTrace_baseChange, smul_eq_mul,
    projectiveTrace_apply]

/-- The trace is additive on products: `Tr_{S × T/R}(s, t) = Tr_{S/R}(s) + Tr_{T/R}(t)`. -/
@[simp]
theorem projectiveTrace_prod_apply {T : Type*} [CommSemiring T] [Algebra R T]
    [Module.Finite R T] [Module.Projective R T] (s : S) (t : T) :
    projectiveTrace R (S × T) (s, t) = projectiveTrace R S s + projectiveTrace R T t := by
  have : lmul R (S × T) (s, t) = (lmul R S s).prodMap (lmul R T t) := by
    ext <;> simp
  simp only [projectiveTrace_apply, this, LinearMap.projectiveTrace_prodMap]

/-- The trace form commutes with base change: under the identification
`A ⊗[R] Hom_R(S, R) ≃ Hom_A(A ⊗[R] S, A)`, the base change of the trace form of `S` is the trace
form of `A ⊗[R] S`. -/
theorem baseChangeEvaluation_comp_projectiveTraceForm_baseChange (A : Type*) [CommSemiring A]
    [Algebra R A] :
    TauCeti.Module.Dual.baseChangeEvaluation ∘ₗ (projectiveTraceForm R S).baseChange A =
      projectiveTraceForm A (A ⊗[R] S) := by
  ext s t
  simp [TauCeti.Module.Dual.baseChangeEvaluation_tmul]

/-- The trace form of `A ⊗[R] S` is perfect iff the base change of the trace form of `S` is
bijective. -/
private theorem projectiveTraceForm_tensorProduct_bijective_iff (A : Type*) [CommSemiring A]
    [Algebra R A] :
    Function.Bijective (projectiveTraceForm A (A ⊗[R] S)) ↔
      Function.Bijective ((projectiveTraceForm R S).lTensor A) := by
  have : ⇑(TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := S) (A := A)) =
      TauCeti.Module.Dual.baseChangeEvaluationEquiv :=
    funext fun z ↦ (TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply z).symm
  rw [← baseChangeEvaluation_comp_projectiveTraceForm_baseChange, LinearMap.coe_comp, this,
    EquivLike.comp_bijective, LinearMap.baseChange_eq_lTensor]

end CommSemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.Projective R S]

/-- On a finite free algebra the projective trace is Mathlib's `Algebra.trace`. -/
theorem projectiveTrace_eq_trace [Module.Free R S] : projectiveTrace R S = trace R S := by
  ext s
  rw [projectiveTrace_apply, LinearMap.projectiveTrace_eq_trace, trace_apply]

/-- On a finite free algebra the projective trace form is Mathlib's `Algebra.traceForm`. -/
theorem projectiveTraceForm_eq_traceForm [Module.Free R S] :
    projectiveTraceForm R S = traceForm R S := by
  ext x y
  simp [projectiveTrace_eq_trace]

/-- `Tr_{S/R}(1)` is the locally constant rank of `S`: its image in the localisation at a prime
`p` is the rank of `S` at `p`. -/
theorem algebraMap_projectiveTrace_one (p : PrimeSpectrum R) :
    algebraMap R (Localization.AtPrime p.asIdeal) (projectiveTrace R S 1) =
      Module.rankAtStalk S p := by
  rw [projectiveTrace_apply, map_one, Module.End.one_eq_id,
    LinearMap.algebraMap_projectiveTrace_id]

/-- The trace-form criterion over a field: a finite algebra over a field is étale iff its trace
form is perfect. -/
private theorem etale_iff_projectiveTraceForm_bijective_of_field (K B : Type*) [Field K]
    [CommRing B] [Algebra K B] [FiniteDimensional K B] :
    Etale K B ↔ Function.Bijective (projectiveTraceForm K B) := by
  rw [projectiveTraceForm_eq_traceForm, TauCeti.Algebra.etale_iff_traceForm_nondegenerate]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert ((traceForm K B).toDual h).bijective using 1
    ext x y
    exact (LinearMap.BilinForm.toDual_def h).symm
  · exact (traceForm_isSymm K (S := B)).isRefl.nondegenerate_iff_separatingLeft.mpr
      (LinearMap.separatingLeft_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr h.1))

/-- **The trace-form criterion for étaleness.** A finite projective algebra `S` over a
commutative ring `R` is étale iff its trace pairing is perfect, that is, iff
`x ↦ (y ↦ Tr_{S/R}(x y))` is a bijection `S → Hom_R(S, R)`. -/
@[stacks 0BJF "affine form, for finite projective algebras"]
theorem etale_iff_projectiveTraceForm_bijective :
    Etale R S ↔ Function.Bijective (projectiveTraceForm R S) := by
  refine ⟨fun _ ↦ (LinearMap.bijective_iff_forall_bijective_lTensor_residueField _).mpr fun p ↦ ?_,
    fun h ↦ ?_⟩
  · -- Each fibre `κ(p) ⊗[R] S` is étale over the field `κ(p)`.
    rw [← projectiveTraceForm_tensorProduct_bijective_iff,
      ← etale_iff_projectiveTraceForm_bijective_of_field]
    infer_instance
  · -- Conversely, `S` is flat and finitely presented, so it suffices that `S` is unramified,
    -- which can be checked on the fibres `K ⊗[R] S` at all fields `K`.
    have : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
    have : FormallyUnramified R S :=
      FormallyUnramified.of_formallyUnramified_baseChange_field fun K _ _ ↦ by
        have : Etale K (K ⊗[R] S) := (etale_iff_projectiveTraceForm_bijective_of_field _ _).mpr
          ((projectiveTraceForm_tensorProduct_bijective_iff K).mpr
            ((LinearEquiv.ofBijective _ h).lTensor K).bijective)
        infer_instance
    exact Etale.of_formallyUnramified_of_flat

end CommRing

end Algebra
