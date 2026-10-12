/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.KrullSchmidt.Cancellation
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Cancellation after tensoring with the field of fractions

Let `R` be a commutative ring with field of fractions `K` and let `A` be an `R`-algebra. For an
`A`-module `M`, the rationalization `M ⊗[R] K` is again an `A`-module. If `P` is finitely
generated over `R`, then `P ⊗[R] K` cancels from `A`-linear equivalences of rationalizations:
`(M × P) ⊗[R] K ≃ (N × P) ⊗[R] K` gives `M ⊗[R] K ≃ N ⊗[R] K`.

As an `A`-module `P ⊗[R] K` rarely has finite length (`K` itself does not over `R` unless `R` is a
field), so cancellation over `A` does not apply directly. Instead the rationalizations are modules
over the ring `K ⊗[R] A`, with `K` acting on the right factor, and over this ring `P ⊗[R] K` has
finite length because it is finite-dimensional over `K`. An `A`-linear map of rationalizations is
`R`-linear, hence `K`-linear because `K` is a localization of `R`, hence `K ⊗[R] A`-linear; so
cancellation of a summand of finite length over `K ⊗[R] A` applies.

For `R = ℤ_p`, `K = ℚ_p` and `A = ℤ_p[G]` this is the cancellation of rational representations
of a finite group used to pass from a stable isomorphism of `ℤ_p[G]`-lattices to an isomorphism.

## Main results

* `TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_of_prod_tensor_linearEquiv`: the
  rationalization of a module that is finitely generated over `R` cancels from an `A`-linear
  equivalence of rationalizations.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.11).
-/

public section

namespace TauCeti.IsFractionRing

open scoped TensorProduct

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K]
  {A : Type*} [Ring A] [Algebra R A]

section RightAction

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- `K` acting on `M ⊗[R] K` through the right factor, as an algebra map to the
`R`-endomorphisms. -/
private noncomputable def rightAct : K →ₐ[R] Module.End R (M ⊗[R] K) :=
  (Module.End.lTensorAlgHom R K M).comp (Algebra.lsmul R R K)

/-- The `K`-module structure on `M ⊗[R] K` through the right factor. It is only a local instance:
when `M` is itself a `K`-module, `TensorProduct.leftModule` is a different `K`-action. -/
private noncomputable abbrev rightModule : Module K (M ⊗[R] K) :=
  Module.compHom (M ⊗[R] K) (rightAct (R := R) K M).toRingHom

attribute [local instance] rightModule

private theorem rightModule_smul (q : K) (v : M ⊗[R] K) : q • v = rightAct (R := R) K M q v :=
  rfl

private theorem smul_tmul_right (q : K) (m : M) (r : K) : q • (m ⊗ₜ[R] r) = m ⊗ₜ (q * r) :=
  rfl

private instance : IsScalarTower R K (M ⊗[R] K) :=
  ⟨fun r q v ↦ by rw [rightModule_smul, rightModule_smul, map_smul, LinearMap.smul_apply]⟩

/-- The right action of `K` on `M ⊗[R] K` is `K`-linearly the rationalization `K ⊗[R] M`. -/
private noncomputable def commLinearEquiv : M ⊗[R] K ≃ₗ[K] K ⊗[R] M :=
  AddEquiv.toLinearEquiv (TensorProduct.comm R M K).toAddEquiv fun q v ↦ by
    induction v using TensorProduct.inductionOn with
    | tmul m r => simp [smul_tmul_right, TensorProduct.smul_tmul', smul_eq_mul]
    | add v w hv hw => simp_all [smul_add]

variable [Module A M] [IsScalarTower R A M]

private instance : SMulCommClass K A (M ⊗[R] K) :=
  ⟨fun q a v ↦ by
    induction v using TensorProduct.inductionOn with
    | tmul m r => rw [TensorProduct.smul_tmul', smul_tmul_right, smul_tmul_right,
        TensorProduct.smul_tmul']
    | add v w hv hw => simp_all [smul_add]⟩

end RightAction

attribute [local instance] rightModule

/-- **Cancellation of rationalizations.** Let `R` have field of fractions `K` and let `A` be an
`R`-algebra. If `P` is finitely generated over `R`, an `A`-linear equivalence
`(M × P) ⊗[R] K ≃ (N × P) ⊗[R] K` induces an `A`-linear equivalence `M ⊗[R] K ≃ N ⊗[R] K`. No
finiteness is required of `M` and `N`. -/
theorem nonempty_tensor_linearEquiv_of_prod_tensor_linearEquiv [IsFractionRing R K]
    {M N P : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P] [Module.Finite R P]
    (h : Nonempty (((M × P) ⊗[R] K) ≃ₗ[A] ((N × P) ⊗[R] K))) :
    Nonempty ((M ⊗[R] K) ≃ₗ[A] (N ⊗[R] K)) := by
  obtain ⟨e⟩ := h
  -- Let `q ⊗ a ∈ K ⊗[R] A` act on each rationalization as `q • a • _`.
  let _ : Module (K ⊗[R] A) (M ⊗[R] K) := TensorProduct.Algebra.module
  let _ : Module (K ⊗[R] A) (N ⊗[R] K) := TensorProduct.Algebra.module
  let _ : Module (K ⊗[R] A) (P ⊗[R] K) := TensorProduct.Algebra.module
  have hM (q : K) (a : A) (v : M ⊗[R] K) : (q ⊗ₜ[R] a) • v = q • a • v :=
    TensorProduct.Algebra.smul_def q a v
  have hN (q : K) (a : A) (v : N ⊗[R] K) : (q ⊗ₜ[R] a) • v = q • a • v :=
    TensorProduct.Algebra.smul_def q a v
  have hT (q : K) (a : A) (v : P ⊗[R] K) : (q ⊗ₜ[R] a) • v = q • a • v :=
    TensorProduct.Algebra.smul_def q a v
  -- `P ⊗[R] K` is finite-dimensional over `K`, so it has finite length over `K ⊗[R] A`.
  have : FiniteDimensional K (P ⊗[R] K) := .equiv (commLinearEquiv K P).symm
  have : IsScalarTower K (K ⊗[R] A) (P ⊗[R] K) := ⟨fun q b v ↦ by
    induction b using TensorProduct.inductionOn with
    | tmul q' a => rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, mul_smul]
    | add b c hb hc => rw [smul_add, add_smul, add_smul, hb, hc, smul_add]⟩
  have hP : IsFiniteLength (K ⊗[R] A) (P ⊗[R] K) := isFiniteLength_of_tower K
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  -- Upgrade the `A`-linear equivalence to a `K ⊗[R] A`-linear one, and cancel `P ⊗[R] K`.
  let e' := (TensorProduct.prodLeft R A M P K).symm.trans
    (e.trans (TensorProduct.prodLeft R A N P K))
  obtain ⟨f⟩ := nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength hP
    ⟨AddEquiv.toLinearEquiv e'.toAddEquiv
      ((IsLocalization.linearMap_compatibleSMul_tensorProduct (nonZeroDivisors R) K
        (fun q a v ↦ Prod.ext (hM q a v.1) (hT q a v.2))
        (fun q a v ↦ Prod.ext (hN q a v.1) (hT q a v.2))).map_smul e'.toLinearMap)⟩
  -- A `K ⊗[R] A`-linear equivalence is `A`-linear, since `a` acts as `1 ⊗ a`.
  refine ⟨AddEquiv.toLinearEquiv f.toAddEquiv fun a v ↦ ?_⟩
  have h1 := f.map_smul ((1 : K) ⊗ₜ[R] a) v
  rwa [hM, hN, one_smul, one_smul] at h1

end TauCeti.IsFractionRing
