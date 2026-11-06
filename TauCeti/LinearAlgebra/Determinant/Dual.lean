/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.Dual.Rank
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Determinant lines of duals and of dual maps

The top exterior power of the dual of a finite free module `V` is the dual of its top exterior
power: the pairing `(φ₁ ∧ ⋯ ∧ φₙ, v₁ ∧ ⋯ ∧ vₙ) ↦ det (φᵢ vⱼ)` identifies
`det (V^*) ≃ (det V)^*` (`TauCeti.detLineDualEquiv`). This is Mathlib's
`exteriorPower.pairingDual` in top degree.

For a linear map `f : M → N` of vector spaces, the dual map `f^* : N^* → M^*` exchanges kernel and
cokernel up to duality: `ker f^*` is the space of functionals vanishing on `range f`, which is
`(coker f)^*` (`LinearMap.kerDualMapEquiv`), and `coker f^* = M^* ⧸ range f^*` is `(ker f)^*` by
restriction (`LinearMap.cokerDualMapEquiv`). When kernel and cokernel are finite-dimensional, as
for a Fredholm operator, the determinant lines therefore agree:

`det f^* = det (ker f^*) ⊗ (det (coker f^*))^* ≃ (det (coker f))^* ⊗ (det (ker f))^{**}`
`≃ det (ker f) ⊗ (det (coker f))^* = det f`

(`LinearMap.detLineDualMapEquiv`), using the pairing of the first paragraph twice, the
evaluation isomorphism of the line `det (ker f)` with its double dual, and the symmetry of the
tensor product. No bases or complements are chosen. Its value on exterior products is
`LinearMap.smul_detLineDualMapEquiv_tmul`. The underlying dimension count is that the kernel and
cokernel of `f^*` have the dimensions of the cokernel and kernel of `f`
(`LinearMap.finrank_ker_dualMap_eq_finrank_quotient_range`,
`LinearMap.finrank_quotient_range_dualMap`), so `f^*` has index minus that of `f`.

This is the dual comparison of determinant lines through which orientations of the determinant
line of an operator are transported to the determinant line of its adjoint.

## Main declarations

* `TauCeti.detLineDualEquiv`: the isomorphism `det (V^*) ≃ (det V)^*`, with value
  `TauCeti.detLineDualEquiv_ιMulti_ιMulti`.
* `LinearMap.kerDualMapEquiv`: `ker f^* ≃ (coker f)^*`.
* `LinearMap.cokerDualMapEquiv`: `coker f^* ≃ (ker f)^*`.
* `LinearMap.detLineDualMapEquiv`: the isomorphism `det f^* ≃ det f`, with value
  `LinearMap.smul_detLineDualMapEquiv_tmul`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (dualization of
  determinant lines).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The **determinant line of the dual** of a finite free module is the dual of its determinant
line: `φ₁ ∧ ⋯ ∧ φₙ` acts on `v₁ ∧ ⋯ ∧ vₙ` by `det (φᵢ vⱼ)`
(`TauCeti.detLineDualEquiv_ιMulti_ιMulti`). This is `exteriorPower.pairingDual` in top degree. -/
def detLineDualEquiv : detLine R (Dual R V) ≃ₗ[R] Dual R (detLine R V) :=
  (LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· (Dual R V)) (Module.dual_finrank_eq R V))).trans
    (LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual R V _))

variable {R V}

@[simp]
theorem detLineDualEquiv_ιMulti_ιMulti (φ : Fin (finrank R (Dual R V)) → Dual R V)
    (v : Fin (finrank R V) → V) :
    detLineDualEquiv R V (exteriorPower.ιMulti R _ φ) (exteriorPower.ιMulti R _ v) =
      (Matrix.of fun i j ↦ φ (Fin.cast (Module.dual_finrank_eq R V).symm j) (v i)).det := by
  rw [detLineDualEquiv, LinearEquiv.trans_apply,
    exteriorPower.ofEq_ιMulti (Module.dual_finrank_eq R V), LinearEquiv.ofBijective_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (f : M →ₗ[K] N)

/-- The kernel of the dual map `f^*` is the dual of the cokernel of `f`: a functional on `N`
vanishing on `range f` is a functional on `N ⧸ range f`. -/
def kerDualMapEquiv : ker f.dualMap ≃ₗ[K] Dual K (N ⧸ range f) :=
  (LinearEquiv.ofEq _ _ f.ker_dualMap_eq_dualAnnihilator_range).trans
    (range f).dualQuotEquivDualAnnihilator.symm

@[simp]
theorem kerDualMapEquiv_apply_mk (φ : ker f.dualMap) (n : N) :
    f.kerDualMapEquiv φ (Submodule.Quotient.mk n) = (φ : Dual K N) n :=
  (rfl)

@[simp]
theorem coe_kerDualMapEquiv_symm (ψ : Dual K (N ⧸ range f)) :
    (f.kerDualMapEquiv.symm ψ : Dual K N) = ψ ∘ₗ (range f).mkQ :=
  (rfl)

/-- The cokernel of the dual map `f^*` is the dual of the kernel of `f`: the class of a functional
on `M` modulo `range f^*` is its restriction to `ker f`. -/
def cokerDualMapEquiv : (Dual K M ⧸ range f.dualMap) ≃ₗ[K] Dual K (ker f) :=
  (Submodule.quotEquivOfEq _ _ f.range_dualMap_eq_dualAnnihilator_ker).trans
    (Subspace.quotAnnihilatorEquiv (ker f))

@[simp]
theorem cokerDualMapEquiv_mk_apply (θ : Dual K M) (u : ker f) :
    f.cokerDualMapEquiv (Submodule.Quotient.mk θ) u = θ u :=
  (rfl)

/-- The kernel of `f^*` has the dimension of the cokernel of `f`. -/
theorem finrank_ker_dualMap_eq_finrank_quotient_range :
    finrank K (ker f.dualMap) = finrank K (N ⧸ range f) :=
  f.kerDualMapEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- The cokernel of `f^*` has the dimension of the kernel of `f`. -/
theorem finrank_quotient_range_dualMap :
    finrank K (Dual K M ⧸ range f.dualMap) = finrank K (ker f) :=
  f.cokerDualMapEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- The isomorphism `det (ker f^*) ≃ (det (coker f))^*` underlying `detLineDualMapEquiv`. -/
private def detLineKerDualMapEquiv [FiniteDimensional K (N ⧸ range f)] :
    TauCeti.detLine K (ker f.dualMap) ≃ₗ[K] Dual K (TauCeti.detLine K (N ⧸ range f)) :=
  (LinearEquiv.detLineCongr f.kerDualMapEquiv).trans (detLineDualEquiv K (N ⧸ range f))

/-- The isomorphism `det (coker f^*) ≃ (det (ker f))^*` underlying `detLineDualMapEquiv`. -/
private def detLineCokerDualMapEquiv [FiniteDimensional K (ker f)] :
    TauCeti.detLine K (Dual K M ⧸ range f.dualMap) ≃ₗ[K] Dual K (TauCeti.detLine K (ker f)) :=
  (LinearEquiv.detLineCongr f.cokerDualMapEquiv).trans (detLineDualEquiv K (ker f))

/-- The **determinant line of the dual map** is the determinant line of the map:
`det f^* = det (ker f^*) ⊗ (det (coker f^*))^*` is identified with
`det f = det (ker f) ⊗ (det (coker f))^*` through `ker f^* ≃ (coker f)^*`,
`coker f^* ≃ (ker f)^*`, the pairing `det (W^*) ≃ (det W)^*` on both factors, the evaluation
isomorphism of `det (ker f)` with its double dual, and the symmetry of the tensor product. Its value
on exterior products is `LinearMap.smul_detLineDualMapEquiv_tmul`. -/
def detLineDualMapEquiv [FiniteDimensional K (ker f)] [FiniteDimensional K (N ⧸ range f)] :
    f.dualMap.detLine ≃ₗ[K] f.detLine :=
  (TensorProduct.congr f.detLineKerDualMapEquiv
      (f.detLineCokerDualMapEquiv.symm.dualMap.trans (evalEquiv K _).symm)).trans
    (TensorProduct.comm K _ _)

/-- `detLineDualMapEquiv` on a pure tensor, in terms of its two factors. -/
private theorem detLineDualMapEquiv_tmul [FiniteDimensional K (ker f)]
    [FiniteDimensional K (N ⧸ range f)] (a : TauCeti.detLine K (ker f.dualMap))
    (β : Dual K (TauCeti.detLine K (Dual K M ⧸ range f.dualMap))) :
    f.detLineDualMapEquiv (a ⊗ₜ β) =
      (evalEquiv K _).symm (f.detLineCokerDualMapEquiv.symm.dualMap β) ⊗ₜ
        f.detLineKerDualMapEquiv a := by
  rw [detLineDualMapEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.comm_tmul, LinearEquiv.trans_apply]

variable {f}

/-- The step of `smul_detLineDualMapEquiv_tmul` computing the cokernel factor: in a line `L`, the
vector `x` with pairings `ψ x = β (C.symm ψ)`, for an isomorphism `C : P ≃ L^*`, satisfies
`C p w • x = β p • w` for all `p` and `w`. -/
private theorem smul_evalEquiv_symm_dualMap {L P : Type*} [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] [AddCommGroup P] [Module K P] (hL : finrank K L = 1)
    (C : P ≃ₗ[K] Dual K L) (β : Dual K P) (p : P) (w : L) :
    C p w • (evalEquiv K L).symm (C.symm.dualMap β) = β p • w := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).mp fun ψ ↦ ?_
  rw [map_sub, map_smul, map_smul, apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply,
    ← map_smul, ← map_smul, (C p).apply_smul_eq_apply_smul_of_finrank_eq_one hL ψ w, map_smul,
    LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]

/-- The kernel factor of `detLineDualMapEquiv`: the image of `φ₁ ∧ ⋯ ∧ φ_c`, for functionals
`φᵢ` on `N` vanishing on `range f`, is the functional on `det (coker f)` sending the exterior
product of the classes of `n₁, …, n_c` to `det (φⱼ nᵢ)`. -/
private theorem detLineKerDualMapEquiv_ιMulti [FiniteDimensional K (N ⧸ range f)]
    (φ : Fin (finrank K (ker f.dualMap)) → ker f.dualMap)
    (n : Fin (finrank K (N ⧸ range f)) → N) :
    f.detLineKerDualMapEquiv (exteriorPower.ιMulti K _ φ)
        (exteriorPower.ιMulti K _ ((range f).mkQ ∘ n)) =
      (Matrix.of fun i j ↦
        (φ (Fin.cast f.finrank_ker_dualMap_eq_finrank_quotient_range.symm j) : Dual K N)
          (n i)).det := by
  simp only [detLineKerDualMapEquiv, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_ιMulti,
    detLineDualEquiv_ιMulti_ιMulti, Function.comp_apply, Submodule.mkQ_apply,
    kerDualMapEquiv_apply_mk, Fin.cast_cast]

/-- The cokernel factor of `detLineDualMapEquiv`: the image of the exterior product of the
classes of functionals `θ₁, …, θ_k` on `M` is the functional on `det (ker f)` sending
`u₁ ∧ ⋯ ∧ u_k` to `det (θⱼ uᵢ)`. -/
private theorem detLineCokerDualMapEquiv_ιMulti [FiniteDimensional K (ker f)]
    (θ : Fin (finrank K (Dual K M ⧸ range f.dualMap)) → Dual K M)
    (u : Fin (finrank K (ker f)) → ker f) :
    f.detLineCokerDualMapEquiv (exteriorPower.ιMulti K _ ((range f.dualMap).mkQ ∘ θ))
        (exteriorPower.ιMulti K _ u) =
      (Matrix.of fun i j ↦ θ (Fin.cast f.finrank_quotient_range_dualMap.symm j) (u i)).det := by
  simp only [detLineCokerDualMapEquiv, LinearEquiv.trans_apply, LinearEquiv.detLineCongr_ιMulti,
    detLineDualEquiv_ιMulti_ιMulti, Function.comp_apply, Submodule.mkQ_apply,
    cokerDualMapEquiv_mk_apply, Fin.cast_cast]

/-- **The value of `detLineDualMapEquiv` on exterior products.** Let `φ₁, …, φ_c` be functionals
on `N` vanishing on `range f` and `β` a functional on `det (coker f^*)`. The image of
`(φ₁ ∧ ⋯ ∧ φ_c) ⊗ β` is `x ⊗ ψ`, where `ψ` is the functional on `det (coker f)` sending the
exterior product of the classes of `n₁, …, n_c` to `det (φⱼ nᵢ)`, and `x ∈ det (ker f)` is
determined by pairing with the classes of functionals `θ₁, …, θ_k` on `M`: for every
`u₁, …, u_k` in `ker f`, `det (θⱼ uᵢ) • x = β (θ₁ ∧ ⋯ ∧ θ_k) • (u₁ ∧ ⋯ ∧ u_k)`. -/
theorem smul_detLineDualMapEquiv_tmul [FiniteDimensional K (ker f)]
    [FiniteDimensional K (N ⧸ range f)]
    (φ : Fin (finrank K (ker f.dualMap)) → ker f.dualMap)
    (β : Dual K (TauCeti.detLine K (Dual K M ⧸ range f.dualMap)))
    (θ : Fin (finrank K (Dual K M ⧸ range f.dualMap)) → Dual K M)
    (u : Fin (finrank K (ker f)) → ker f) (ψ : Dual K (TauCeti.detLine K (N ⧸ range f)))
    (hψ : ∀ n : Fin (finrank K (N ⧸ range f)) → N,
      ψ (exteriorPower.ιMulti K _ ((range f).mkQ ∘ n)) =
        (Matrix.of fun i j ↦
          (φ (Fin.cast f.finrank_ker_dualMap_eq_finrank_quotient_range.symm j) : Dual K N)
            (n i)).det) :
    (Matrix.of fun i j ↦ θ (Fin.cast f.finrank_quotient_range_dualMap.symm j) (u i)).det •
        f.detLineDualMapEquiv (exteriorPower.ιMulti K _ φ ⊗ₜ β) =
      β (exteriorPower.ιMulti K _ ((range f.dualMap).mkQ ∘ θ)) •
        (exteriorPower.ιMulti K _ u ⊗ₜ ψ) := by
  -- The kernel factor is `ψ`: both functionals agree on the exterior products spanning
  -- `det (coker f)`, since every family of classes lifts to `N`.
  have hker : f.detLineKerDualMapEquiv (exteriorPower.ιMulti K _ φ) = ψ := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    obtain ⟨n, rfl⟩ := (range f).mkQ_surjective.comp_left w
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      detLineKerDualMapEquiv_ιMulti, hψ]
  -- The cokernel factor `x` pairs with each functional `ψ'` on `det (ker f)` through `β`, and
  -- `det (ker f)` is a line, so `det (θⱼ uᵢ) • x = β (θ₁ ∧ ⋯ ∧ θ_k) • (u₁ ∧ ⋯ ∧ u_k)`.
  have hcoker := smul_evalEquiv_symm_dualMap (TauCeti.finrank_detLine K (ker f))
    f.detLineCokerDualMapEquiv β (exteriorPower.ιMulti K _ ((range f.dualMap).mkQ ∘ θ))
    (exteriorPower.ιMulti K _ u)
  rw [← detLineCokerDualMapEquiv_ιMulti, detLineDualMapEquiv_tmul, hker,
    TensorProduct.smul_tmul', hcoker, ← TensorProduct.smul_tmul']

end LinearMap
