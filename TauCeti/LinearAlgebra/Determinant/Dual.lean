/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.Dual.Annihilator
public import TauCeti.LinearAlgebra.Dual.Basis
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Determinant lines of duals and of dual maps

The top exterior power of the dual of a finite free module `V` is the dual of its top exterior
power: the pairing `(φ₁ ∧ ⋯ ∧ φₙ, v₁ ∧ ⋯ ∧ vₙ) ↦ det (φᵢ vⱼ)` identifies
`det (V^*) ≃ (det V)^*` (`TauCeti.detLineDualEquiv`). This is Mathlib's
`exteriorPower.pairingDual` in top degree.

For a linear map `f : M → N` of vector spaces, the dual map `f^* : N^* → M^*` exchanges kernel and
cokernel up to duality: `ker f^* ≃ (coker f)^*` (`LinearMap.kerDualMapEquiv`) and
`coker f^* ≃ (ker f)^*` (`LinearMap.cokerDualMapEquiv`), both from
`TauCeti.LinearAlgebra.Dual.Annihilator`. When kernel and cokernel are finite-dimensional, as
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

This identifies the determinant line of the algebraic dual map `f^*`, on full algebraic duals
over a field, with that of `f`.

A map `g` whose kernel and cokernel are copies of the cokernel and kernel of `f` themselves,
rather than of their duals, has instead the dual determinant line: identifications
`e₁ : ker g ≃ coker f` and `e₂ : coker g ≃ ker f` give

`det g = det (ker g) ⊗ (det (coker g))^* ≃ det (coker f) ⊗ (det (ker f))^* ≃ (det f)^*`

(`LinearMap.detLineEquivDualOfKerCoker`), under which `x ⊗ ψ` pairs with `u ⊗ φ` to
`φ (e₁ x) * ψ (e₂⁻¹ u)`. The pairing is symmetric in `f` and `g`, and for bijective maps it is the
pairing of `K` with itself. The Hilbert space adjoint of a Fredholm operator is the case in
point: its kernel is the orthogonal complement of the range, a copy of the cokernel
(`ContinuousLinearMap.detLineAdjointEquivDual`).

## Main declarations

* `TauCeti.detLineDualEquiv`: the isomorphism `det (V^*) ≃ (det V)^*`, with value
  `TauCeti.detLineDualEquiv_ιMulti_ιMulti`.
* `LinearMap.detLineDualMapEquiv`: the isomorphism `det f^* ≃ det f`, with value
  `LinearMap.smul_detLineDualMapEquiv_tmul`.
* `LinearMap.detLineEquivDualOfKerCoker`: the isomorphism `det g ≃ (det f)^*` for
  `ker g ≃ coker f` and `coker g ≃ ker f`, with value
  `LinearMap.detLineEquivDualOfKerCoker_tmul_tmul`, symmetry
  `LinearMap.detLineEquivDualOfKerCoker_symm_symm_apply` and bijective case
  `LinearMap.detLineEquivDualOfKerCoker_apply_detLineEquivOfBijective_symm_one`.

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
  simp only [detLineDualEquiv, LinearEquiv.trans_apply,
    exteriorPower.ofEq_ιMulti (Module.dual_finrank_eq R V), LinearEquiv.ofBijective_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply]

end TauCeti

namespace LinearMap

open TauCeti

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (f : M →ₗ[K] N)

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
  have hcoker := Dual.smul_evalEquiv_symm_dualMap (TauCeti.finrank_detLine K (ker f))
    f.detLineCokerDualMapEquiv β (exteriorPower.ιMulti K _ ((range f.dualMap).mkQ ∘ θ))
    (exteriorPower.ιMulti K _ u)
  rw [← detLineCokerDualMapEquiv_ιMulti, detLineDualMapEquiv_tmul, hker,
    TensorProduct.smul_tmul', hcoker, ← TensorProduct.smul_tmul']

section KerCoker

variable {K : Type*} [Field K] {M N P Q : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  {f : M →ₗ[K] N} {g : P →ₗ[K] Q} [FiniteDimensional K (ker f)]
  [FiniteDimensional K (N ⧸ range f)]

/-- **Determinant lines of maps exchanging kernel and cokernel.** If the kernel of `g` is
identified with the cokernel of `f` (`e₁`) and the cokernel of `g` with the kernel of `f` (`e₂`),
the determinant line `det g = det (ker g) ⊗ (det (coker g))^*` is identified with the dual of
`det f = det (ker f) ⊗ (det (coker f))^*`: `x ⊗ ψ` pairs with `u ⊗ φ` to `φ (e₁ x) * ψ (e₂⁻¹ u)`,
with `e₁` and `e₂⁻¹` acting on determinant lines
(`LinearMap.detLineEquivDualOfKerCoker_tmul_tmul`). For the Hilbert space adjoint `g = f†` of a
Fredholm operator, whose kernel is the orthogonal complement of the range of `f`, this is the
comparison `det f† ≃ (det f)^*` (`ContinuousLinearMap.detLineAdjointEquivDual`). -/
def detLineEquivDualOfKerCoker (e₁ : ker g ≃ₗ[K] N ⧸ range f) (e₂ : (Q ⧸ range g) ≃ₗ[K] ker f) :
    g.detLine ≃ₗ[K] Dual K f.detLine :=
  (TensorProduct.congr (LinearEquiv.detLineCongr e₁)
      (LinearEquiv.detLineCongr e₂).symm.dualMap).trans <|
    (TensorProduct.comm K _ _).trans <|
      (TensorProduct.congr (LinearEquiv.refl K _) (evalEquiv K _)).trans
        (dualDistribEquiv K _ _)

/-- `LinearMap.detLineEquivDualOfKerCoker` pairs `x ⊗ ψ` with `u ⊗ φ` to `φ (e₁ x) * ψ (e₂⁻¹ u)`. -/
@[simp]
theorem detLineEquivDualOfKerCoker_tmul_tmul (e₁ : ker g ≃ₗ[K] N ⧸ range f)
    (e₂ : (Q ⧸ range g) ≃ₗ[K] ker f) (x : TauCeti.detLine K (ker g))
    (ψ : Dual K (TauCeti.detLine K (Q ⧸ range g))) (u : TauCeti.detLine K (ker f))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range f))) :
    detLineEquivDualOfKerCoker e₁ e₂ (x ⊗ₜ ψ) (u ⊗ₜ φ) =
      φ (LinearEquiv.detLineCongr e₁ x) * ψ (LinearEquiv.detLineCongr e₂.symm u) := by
  simp [detLineEquivDualOfKerCoker]

/-- **The pairing is symmetric.** Exchanging the roles of `f` and `g`, with the inverse
identifications, pairs `det f` with `det g` by the same values. -/
theorem detLineEquivDualOfKerCoker_symm_symm_apply [FiniteDimensional K (ker g)]
    [FiniteDimensional K (Q ⧸ range g)] (e₁ : ker g ≃ₗ[K] N ⧸ range f)
    (e₂ : (Q ⧸ range g) ≃ₗ[K] ker f) (a : g.detLine) (b : f.detLine) :
    detLineEquivDualOfKerCoker e₂.symm e₁.symm b a = detLineEquivDualOfKerCoker e₁ e₂ a b := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => rw [map_add, map_add, LinearMap.add_apply, ha, ha']
  | tmul x ψ =>
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' => rw [map_add, LinearMap.add_apply, map_add, hb, hb']
    | tmul u φ =>
      rw [detLineEquivDualOfKerCoker_tmul_tmul, detLineEquivDualOfKerCoker_tmul_tmul,
        LinearEquiv.symm_symm, mul_comm]

/-- **The bijective case.** When `f` and `g` are bijective, their determinant lines are
identified with `K` (`LinearMap.detLineEquivOfBijective`), and through these identifications
`LinearMap.detLineEquivDualOfKerCoker` is the identification of `K` with its dual: it pairs the
generators `1` of both lines to `1`. -/
theorem detLineEquivDualOfKerCoker_apply_detLineEquivOfBijective_symm_one
    (e₁ : ker g ≃ₗ[K] N ⧸ range f) (e₂ : (Q ⧸ range g) ≃ₗ[K] ker f) (hf : Function.Bijective f)
    (hg : Function.Bijective g) (a : g.detLine) :
    detLineEquivDualOfKerCoker e₁ e₂ a ((detLineEquivOfBijective hf).symm 1) =
      detLineEquivOfBijective hg a := by
  have hcf : finrank K (N ⧸ range f) = 0 :=
    have := Submodule.Quotient.subsingleton_iff.mpr (range_eq_top.mpr hf.2)
    finrank_zero_of_subsingleton
  have hcg : finrank K (Q ⧸ range g) = 0 :=
    have := Submodule.Quotient.subsingleton_iff.mpr (range_eq_top.mpr hg.2)
    finrank_zero_of_subsingleton
  -- Both sides are linear in `a`, and `g.detLine` is spanned by `(detLineEquivOfBijective hg)⁻¹ 1`,
  -- the tensor of the empty exterior product of the kernel with a functional taking the value `1`
  -- on the empty exterior product of the cokernel; the same holds for `f`.
  obtain ⟨c, rfl⟩ : ∃ c : K, c • (detLineEquivOfBijective hg).symm 1 = a :=
    ⟨detLineEquivOfBijective hg a, by rw [← map_smul, smul_eq_mul, mul_one,
      LinearEquiv.symm_apply_apply]⟩
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearEquiv.apply_symm_apply,
    detLineEquivOfBijective_symm_one hg 0 (TauCeti.detLineEquivOfFinrankEqZero hcg).toLinearMap 0
      (TauCeti.detLineEquivOfFinrankEqZero_ιMulti hcg _),
    detLineEquivOfBijective_symm_one hf 0 (TauCeti.detLineEquivOfFinrankEqZero hcf).toLinearMap 0
      (TauCeti.detLineEquivOfFinrankEqZero_ιMulti hcf _),
    detLineEquivDualOfKerCoker_tmul_tmul]
  simp [TauCeti.detLineEquivOfFinrankEqZero_ιMulti]

end KerCoker

end LinearMap
