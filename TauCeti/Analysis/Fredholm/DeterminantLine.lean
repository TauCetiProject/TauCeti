/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.LinearIndependent.Append
public import TauCeti.Data.Fin.Tuple.Basic

/-!
# The determinant line of a Fredholm operator

A Fredholm operator `T : E →L[𝕜] F` has finite-dimensional kernel and cokernel, so its
determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` (`LinearMap.detLine`) is a line over `𝕜`.
Orientations of moduli spaces in Morse and Floer theory are orientations of these lines for
the linearized operators.

Kernel and cokernel jump as the operator varies, so the determinant lines of a family are
compared through a **stabilization**. Adjoin finitely many directions `D₂ : Λ →L[𝕜] F`, with `Λ`
finite-dimensional, so that `D₁.coprod D₂ : E × Λ →L[𝕜] F` is onto. The stabilized operator has
no cokernel, and it stays onto, with kernel of the same dimension, under small perturbations of
`D₁`. The exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → 0` of
`TauCeti.Analysis.Fredholm.Parametric` then identifies the determinant line of `D₁` with
`det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*` (`ContinuousLinearMap.detLineCoprodEquiv`). This is the
fibrewise comparison through which the determinant lines of a continuous family of Fredholm
operators form a line bundle.

Different stabilizations give compatible identifications. Any two stabilizations `Λ₁`, `Λ₂` are
dominated by `Λ₁ × Λ₂`, so it suffices to compare a stabilization `Λ` with an enlargement
`Λ × Λ'`. The exact sequence
`0 → ker (D₁.coprod D₂) → ker (D₁.coprod (D₂.coprod D₃)) → Λ × Λ' → Λ → 0` identifies the two
stabilized determinant lines (`ContinuousLinearMap.detLineStabilizerChangeEquiv`), and the two
determinant isomorphisms agree through it up to an explicit Koszul sign
(`ContinuousLinearMap.detLineCoprodEquiv_coprod`).

## Main results

* `ContinuousLinearMap.IsFredholm.finrank_detLine`: the determinant line of a Fredholm operator is
  one-dimensional.
* `ContinuousLinearMap.detLineCoprodEquiv`: for a surjective stabilization `D₁.coprod D₂` by a
  finite-dimensional space `Λ`, the isomorphism
  `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^* ≃ det (ker D₁) ⊗ (det (F ⧸ range D₁))^*`.
* `ContinuousLinearMap.detLineCoprodEquiv_tmul`: its value on exterior products.
* `ContinuousLinearMap.detLineStabilizerChangeEquiv`: for further directions `D₃ : Λ' →L[𝕜] F`,
  the isomorphism
  `det (ker (D₁.coprod (D₂.coprod D₃))) ⊗ (det (Λ × Λ'))^* ≃ det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`
  of the exact sequence `0 → ker (D₁.coprod D₂) → ker (D₁.coprod (D₂.coprod D₃)) → Λ × Λ' → Λ → 0`.
* `ContinuousLinearMap.detLineCoprodEquiv_coprod`: **stabilizer independence**. The determinant
  isomorphisms of the stabilizations by `Λ` and by `Λ × Λ'` agree through
  `detLineStabilizerChangeEquiv`, up to the sign `(-1) ^ (k * dim Λ')` with `k` the rank of the
  parameter projection of `D₁.coprod D₂`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` of a Fredholm operator is
one-dimensional. -/
theorem IsFredholm.finrank_detLine {T : E →L[𝕜] F} (hT : IsFredholm T) :
    finrank 𝕜 (T : E →ₗ[𝕜] F).detLine = 1 :=
  have := hT.finite_ker
  have := hT.finite_coker
  LinearMap.finrank_detLine _

section Stabilization

variable {𝕜 E Λ F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ]

variable (D₁ D₂) in
/-- **The determinant line of a stabilized operator.** If adjoining the finite-dimensional
directions `D₂ : Λ →L[𝕜] F` makes `D₁.coprod D₂ : E × Λ →L[𝕜] F` surjective and `D₁` has
finite-dimensional kernel, the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → 0` identifies
`det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*` with the determinant line
`det (ker D₁) ⊗ (det (F ⧸ range D₁))^*` of `D₁`. This is `TauCeti.detLineFourTermEquiv` for that
sequence; its value is `ContinuousLinearMap.detLineCoprodEquiv_tmul`. -/
noncomputable def detLineCoprodEquiv (h : Function.Surjective (D₁.coprod D₂)) :
    TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) ≃ₗ[𝕜]
      (D₁ : E →ₗ[𝕜] F).detLine :=
  TauCeti.detLineFourTermEquiv (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h)

/-- **The value of `ContinuousLinearMap.detLineCoprodEquiv` on exterior products.** Let `u` be a
family of `dim (ker D₁)` vectors of `ker D₁`, let `v` be a family of `dim (range p)` vectors of
the kernel of `D₁.coprod D₂`, where `p` is the parameter projection
`ContinuousLinearMap.parameterProj`, and let `z` be a family of `dim (F ⧸ range D₁)` parameters.
Let `β` be the exterior product of the vectors `(u i, 0)` followed by `v`, and `γ` the exterior
product of the parameter components `p ∘ v` followed by `z`. Then `β ⊗ φ` goes to `α ⊗ ψ`, with
`α` the exterior product of `u` and `ψ` the functional taking the value `φ γ` at the exterior
product of the classes of `D₂ ∘ z` in the cokernel. -/
theorem detLineCoprodEquiv_tmul (h : Function.Surjective (D₁.coprod D₂))
    (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ) {β : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod D₂).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v))
    {γ : TauCeti.detLine 𝕜 Λ} (hγ : (γ : ExteriorAlgebra 𝕜 Λ) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterProj D₁ D₂ ∘ v) z))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    TensorProduct.rid 𝕜 _
        ((Dual.eval 𝕜 _ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker D₁ D₂ ∘ z))).lTensor _
          (detLineCoprodEquiv D₁ D₂ h (β ⊗ₜ φ))) =
      φ γ • exteriorPower.ιMulti 𝕜 _ u :=
  TauCeti.detLineFourTermEquiv_tmul _ _ _ _ u v z hβ hγ φ

end Stabilization

section Helpers

/-! ### Exterior products used in the change of stabilizer -/

variable {𝕜 : Type*} [Field 𝕜]

/-- In `Λ × Λ'`, let `a` and `c` be families of `Λ` with `dim Λ` vectors in total. The exterior
product of `(a, 0)`, then a family `q`, then `(c, 0)` is `(-1) ^ (k * l)` times the exterior
product of the added components `(0, q.2)` followed by `(a, 0)` and `(c, 0)`: the components of
`q` in `Λ × 0` are absorbed by `(a, 0)` and `(c, 0)`, and the reordering costs the sign. -/
private theorem ιMulti_append_inl_eq {Λ Λ' : Type*} [AddCommGroup Λ] [Module 𝕜 Λ]
    [FiniteDimensional 𝕜 Λ] [AddCommGroup Λ'] [Module 𝕜 Λ'] {k d l : ℕ}
    (hΛ : finrank 𝕜 Λ = k + d) (a : Fin k → Λ) (c : Fin d → Λ) (q : Fin l → Λ × Λ') :
    ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append (LinearMap.inl 𝕜 Λ Λ' ∘ a) q)
        (LinearMap.inl 𝕜 Λ Λ' ∘ c)) =
      ((-1 : 𝕜) ^ (k * l)) • ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append (fun j ↦ ((0 : Λ), (q j).2)) (LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append a c)) := by
  set A := ExteriorAlgebra.ιMulti 𝕜 _ (LinearMap.inl 𝕜 Λ Λ' ∘ a)
  set C := ExteriorAlgebra.ιMulti 𝕜 _ (LinearMap.inl 𝕜 Λ Λ' ∘ c)
  set B := ExteriorAlgebra.ιMulti 𝕜 _ (fun j ↦ ((0 : Λ), (q j).2))
  -- The components of `q` in `Λ × 0` lie in the span of `(a, 0), (c, 0)`.
  have hqb : A * C * ExteriorAlgebra.ιMulti 𝕜 _ q = A * C * B := by
    simp only [A, C, B, ExteriorAlgebra.ιMulti_mul_ιMulti]
    have key := (LinearMap.range (LinearMap.inl 𝕜 Λ Λ')).ιMulti_eq_of_sub_mem
      (x := Fin.append (Fin.append (LinearMap.inl 𝕜 Λ Λ' ∘ a) (LinearMap.inl 𝕜 Λ Λ' ∘ c)) q)
      (x' := Fin.append (Fin.append (LinearMap.inl 𝕜 Λ Λ' ∘ a) (LinearMap.inl 𝕜 Λ Λ' ∘ c))
        fun j ↦ ((0 : Λ), (q j).2))
      (Finset.univ.map (Fin.castAddEmb l)) ?_ ?_ ?_ ?_
    · simpa only [exteriorPower.ιMulti_apply_coe] using congrArg Subtype.val key
    · rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Finset.card_map,
        Finset.card_univ, Fintype.card_fin, hΛ]
    · intro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
      cases j using Fin.addCases <;> simp
    · intro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
      simp
    · intro i hi
      cases i using Fin.addCases with
      | left j => exact absurd (Finset.mem_map.2 ⟨j, Finset.mem_univ _, by simp⟩) hi
      | right j => exact ⟨(q j).1, Prod.ext (by simp) (by simp)⟩
  have hu : ∀ (n : ℕ) (y : ExteriorAlgebra 𝕜 (Λ × Λ')),
      ((-1 : ℤˣ) ^ n) • y = ((-1 : 𝕜) ^ n) • y := fun n y ↦ by
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul 𝕜]
    simp
  have hexp : k * l + (k + d) * l = d * l + 2 * (k * l) := by ring
  rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ExteriorAlgebra.ιMulti_mul_ιMulti, Fin.comp_append,
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, mul_assoc, ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm,
    mul_smul_comm, ← mul_assoc, hqb,
    ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm 𝕜 (fun j ↦ ((0 : Λ), (q j).2)),
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, hu, hu, smul_smul, ← pow_add, hexp, pow_add,
    pow_mul (-1 : 𝕜) 2, neg_one_sq, one_pow, mul_one]

/-- Renumbering the factors of an exterior product along an equality of lengths does not change
it. -/
private theorem ιMulti_comp_finCast {M : Type*} [AddCommGroup M] [Module 𝕜 M] {m n : ℕ}
    (e : m = n) (f : Fin n → M) :
    ExteriorAlgebra.ιMulti 𝕜 m (f ∘ Fin.cast e) = ExteriorAlgebra.ιMulti 𝕜 n f := by
  subst e
  rfl

/-- An exterior product of `dim M` vectors, read in the determinant line of `M`. -/
private theorem exists_coe_detLine_eq {M : Type*} [AddCommGroup M] [Module 𝕜 M] {n : ℕ}
    (e : finrank 𝕜 M = n) (f : Fin n → M) :
    ∃ β : TauCeti.detLine 𝕜 M, (β : ExteriorAlgebra 𝕜 M) = ExteriorAlgebra.ιMulti 𝕜 n f :=
  ⟨exteriorPower.ιMulti 𝕜 _ (f ∘ Fin.cast e), by
    rw [exteriorPower.ιMulti_apply_coe, ιMulti_comp_finCast]⟩

/-- The exterior product of linearly independent vectors is a nonzero element of the
determinant line. -/
private theorem ne_zero_of_coe_detLine_eq {M : Type*} [AddCommGroup M] [Module 𝕜 M] {n : ℕ}
    {f : Fin n → M} (hf : LinearIndependent 𝕜 f) {β : TauCeti.detLine 𝕜 M}
    (hβ : (β : ExteriorAlgebra 𝕜 M) = ExteriorAlgebra.ιMulti 𝕜 n f) : β ≠ 0 := by
  rintro rfl
  exact (exteriorPower.ιMulti_ne_zero_iff f).2 hf (Subtype.ext (by simpa using hβ.symm))

/-- On `L ⊗ V^*` for a line `V`, pairing with a nonzero vector `θ` of `V` is injective. -/
private theorem injective_rid_lTensor_eval {L V : Type*} [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup V] [Module 𝕜 V] (hV : finrank 𝕜 V = 1) {θ : V} (hθ : θ ≠ 0) :
    Function.Injective fun t : L ⊗[𝕜] Dual 𝕜 V ↦
      TensorProduct.rid 𝕜 L ((Dual.eval 𝕜 V θ).lTensor L t) := by
  refine (TensorProduct.rid 𝕜 L).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ fun φ₁ φ₂ hφ ↦ ?_)
  ext y
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' θ hθ).1 hV y
  simp only [Dual.eval_apply] at hφ
  simp [hφ]

/-- In `L ⊗ N`, if every vector of `L` is a multiple of `β`, then every element is `β ⊗ n` for
some `n`. -/
private theorem exists_eq_tmul_of_forall_smul_eq {L N : Type*} [AddCommMonoid L] [Module 𝕜 L]
    [AddCommMonoid N] [Module 𝕜 N] {β : L} (hβ : ∀ y : L, ∃ c : 𝕜, c • β = y) (t : L ⊗[𝕜] N) :
    ∃ n : N, t = β ⊗ₜ n := by
  induction t using TensorProduct.inductionOn with
  | tmul y n =>
    obtain ⟨c, rfl⟩ := hβ y
    exact ⟨c • n, TensorProduct.smul_tmul _ _ _⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, rfl⟩ := h₁
    obtain ⟨n₂, rfl⟩ := h₂
    exact ⟨n₁ + n₂, (TensorProduct.tmul_add _ _ _).symm⟩

end Helpers

section StabilizerChange

/-! ### Enlarging the stabilizer

A stabilization `D₂ : Λ →L[𝕜] F` of `D₁` can be enlarged by further directions `D₃ : Λ' →L[𝕜] F`
to the stabilization `D₂.coprod D₃ : Λ × Λ' →L[𝕜] F`. The two determinant isomorphisms
`ContinuousLinearMap.detLineCoprodEquiv` are related by the exact sequence
`0 → ker (D₁.coprod D₂) → ker (D₁.coprod (D₂.coprod D₃)) → Λ × Λ' → Λ → 0`, whose maps are
`(x, l) ↦ (x, (l, 0))`, `(x, (l, l')) ↦ (0, l')` and the first projection. -/

variable {𝕜 E Λ Λ' F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup Λ'] [Module 𝕜 Λ']
  [TopologicalSpace Λ'] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]

variable (D₁ : E →L[𝕜] F) (D₂ : Λ →L[𝕜] F) (D₃ : Λ' →L[𝕜] F)

variable [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 Λ']

/-- **Change of stabilizer.** For a surjective stabilization `D₁.coprod D₂` and further directions
`D₃ : Λ' →L[𝕜] F`, the exact sequence
`0 → ker (D₁.coprod D₂) → ker (D₁.coprod (D₂.coprod D₃)) → Λ × Λ' → Λ → 0` identifies
`det (ker (D₁.coprod (D₂.coprod D₃))) ⊗ (det (Λ × Λ'))^*` with
`det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`. This is `TauCeti.detLineFourTermEquiv` for that sequence;
its value is `ContinuousLinearMap.detLineStabilizerChangeEquiv_tmul`, and its compatibility with
the two determinant isomorphisms is `ContinuousLinearMap.detLineCoprodEquiv_coprod`. -/
noncomputable def detLineStabilizerChangeEquiv (h : Function.Surjective (D₁.coprod D₂)) :
    TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ')) ≃ₗ[𝕜]
      TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) :=
  have := finiteDimensional_ker_coprod D₁ D₂
  TauCeti.detLineFourTermEquiv (kerCoprodCoprodHom_injective D₁ D₂ D₃)
    (exact_kerCoprodCoprodHom_addedParameterProj D₁ D₂ D₃) (exact_addedParameterProj_fst D₁ D₂ D₃ h)
    LinearMap.fst_surjective

/-- **The value of `ContinuousLinearMap.detLineStabilizerChangeEquiv` on exterior products.** Let
`u` be a family of `dim (ker (D₁.coprod D₂))` vectors of that kernel, let `w` be a family of
`dim (range q)` vectors of the enlarged kernel, where `q` is the added projection
`ContinuousLinearMap.addedParameterProj`, and let `z` be a family of `dim Λ` vectors of `Λ × Λ'`.
Let `β` be the exterior product of the vectors `(x, (l, 0))` for `(x, l)` in `u`, followed by `w`,
and `γ` the exterior product of `q ∘ w` followed by `z`. Then `β ⊗ φ` goes to `α ⊗ ψ`, with `α`
the exterior product of `u` and `ψ` the functional taking the value `φ γ` at the exterior product
of the first components of `z`. -/
theorem detLineStabilizerChangeEquiv_tmul (h : Function.Surjective (D₁.coprod D₂))
    (u : Fin (finrank 𝕜 (D₁.coprod D₂).ker) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))) →
      (D₁.coprod (D₂.coprod D₃)).ker)
    (z : Fin (finrank 𝕜 Λ) → Λ × Λ') {β : TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod (D₂.coprod D₃)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodCoprodHom D₁ D₂ D₃ ∘ u) w))
    {γ : TauCeti.detLine 𝕜 (Λ × Λ')} (hγ : (γ : ExteriorAlgebra 𝕜 (Λ × Λ')) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (addedParameterProj D₁ D₂ D₃ ∘ w) z))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ'))) :
    TensorProduct.rid 𝕜 _
        ((Dual.eval 𝕜 _ (exteriorPower.ιMulti 𝕜 _ (LinearMap.fst 𝕜 Λ Λ' ∘ z))).lTensor _
          (detLineStabilizerChangeEquiv D₁ D₂ D₃ h (β ⊗ₜ φ))) =
      φ γ • exteriorPower.ιMulti 𝕜 _ u :=
  have := finiteDimensional_ker_coprod D₁ D₂
  TauCeti.detLineFourTermEquiv_tmul _ _ _ _ u w z hβ hγ φ

private theorem finrank_range_parameterProj_coprod_eq :
    finrank 𝕜 (parameterProj D₁ (D₂.coprod D₃)).range = finrank 𝕜 (parameterProj D₁ D₂).range +
      finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃)) := by
  have := finrank_ker_coprod D₁ D₂
  have := finrank_ker_coprod D₁ (D₂.coprod D₃)
  have := finrank_ker_coprod_coprod D₁ D₂ D₃
  omega

/-- The enlarged determinant isomorphism on the adapted generator `β' ⊗ φ`, paired with the
exterior product of a cokernel basis. -/
private theorem rid_lTensor_detLineCoprodEquiv_coprod_tmul (h : Function.Surjective (D₁.coprod D₂))
    (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))) →
      (D₁.coprod (D₂.coprod D₃)).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ)
    {β' : TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker}
    (hβ' : (β' : ExteriorAlgebra 𝕜 (D₁.coprod (D₂.coprod D₃)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append
        (kerCoprodHom D₁ (D₂.coprod D₃) ∘ u) (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v)) w))
    {γ' : TauCeti.detLine 𝕜 (Λ × Λ')} (hγ' : (γ' : ExteriorAlgebra 𝕜 (Λ × Λ')) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append
        (LinearMap.inl 𝕜 Λ Λ' ∘ (parameterProj D₁ D₂ ∘ v)) (parameterProj D₁ (D₂.coprod D₃) ∘ w))
        (LinearMap.inl 𝕜 Λ Λ' ∘ z)))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ'))) :
    TensorProduct.rid 𝕜 _
        ((Dual.eval 𝕜 _ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker D₁ D₂ ∘ z))).lTensor _
          (detLineCoprodEquiv D₁ (D₂.coprod D₃) (surjective_coprod_coprod D₁ D₂ D₃ h)
            (β' ⊗ₜ φ))) =
      φ γ' • exteriorPower.ιMulti 𝕜 _ u := by
  have hp' := finrank_range_parameterProj_coprod_eq D₁ D₂ D₃
  have hp'v : parameterProj D₁ (D₂.coprod D₃) ∘
      (Fin.append (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v) w ∘ Fin.cast hp') = (Fin.append
        (LinearMap.inl 𝕜 Λ Λ' ∘ (parameterProj D₁ D₂ ∘ v))
        (parameterProj D₁ (D₂.coprod D₃) ∘ w)) ∘ Fin.cast hp' := by
    rw [← Function.comp_assoc, Fin.comp_append]
    congr 2
    funext i
    simp
  have hbig := detLineCoprodEquiv_tmul (surjective_coprod_coprod D₁ D₂ D₃ h) u
    (Fin.append (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v) w ∘ Fin.cast hp') (LinearMap.inl 𝕜 Λ Λ' ∘ z)
    (β := β') (by
      rw [hβ']
      simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ιMulti_comp_finCast, mul_assoc])
    (γ := γ') (by
      rw [hγ', hp'v]
      simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ιMulti_comp_finCast]) φ
  rwa [show parameterToCoker D₁ (D₂.coprod D₃) ∘ (LinearMap.inl 𝕜 Λ Λ' ∘ z) =
    parameterToCoker D₁ D₂ ∘ z from funext fun i ↦ by simp] at hbig

/-- The change of stabilizer sends the adapted generator `β' ⊗ φ` to `β ⊗ φ₀`, where `φ₀` takes
the value `φ γ''` at `γ`. -/
private theorem exists_detLineStabilizerChangeEquiv_tmul_eq
    (h : Function.Surjective (D₁.coprod D₂)) (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))) →
      (D₁.coprod (D₂.coprod D₃)).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ)
    {β : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker} (hβ0 : β ≠ 0)
    (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod D₂).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v))
    {β' : TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker}
    (hβ' : (β' : ExteriorAlgebra 𝕜 (D₁.coprod (D₂.coprod D₃)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append
        (kerCoprodHom D₁ (D₂.coprod D₃) ∘ u) (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v)) w))
    {γ : TauCeti.detLine 𝕜 Λ} (hγ : (γ : ExteriorAlgebra 𝕜 Λ) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterProj D₁ D₂ ∘ v) z))
    {γ'' : TauCeti.detLine 𝕜 (Λ × Λ')} (hγ'' : (γ'' : ExteriorAlgebra 𝕜 (Λ × Λ')) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (addedParameterProj D₁ D₂ D₃ ∘ w)
        (LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append (parameterProj D₁ D₂ ∘ v) z)))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ'))) :
    ∃ φ₀, detLineStabilizerChangeEquiv D₁ D₂ D₃ h (β' ⊗ₜ φ) = β ⊗ₜ φ₀ ∧ φ₀ γ = φ γ'' := by
  have := finiteDimensional_ker_coprod D₁ D₂
  have hK := finrank_ker_coprod D₁ D₂
  have hΛ := finrank_eq_finrank_range_parameterProj_add_finrank_quotient D₁ D₂ h
  have hstab := detLineStabilizerChangeEquiv_tmul D₁ D₂ D₃ h
    (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v ∘ Fin.cast hK) w
    ((LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append (parameterProj D₁ D₂ ∘ v) z) ∘ Fin.cast hΛ) (β := β') (by
      rw [hβ', ← Function.comp_assoc, Fin.comp_append]
      have : kerCoprodCoprodHom D₁ D₂ D₃ ∘ (kerCoprodHom D₁ D₂ ∘ u) =
          kerCoprodHom D₁ (D₂.coprod D₃) ∘ u := funext fun i ↦ by simp [Subtype.ext_iff]
      simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ιMulti_comp_finCast, this])
    (γ := γ'') (by
      rw [hγ'']
      simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ιMulti_comp_finCast]) φ
  obtain ⟨φ₀, hφ₀⟩ := exists_eq_tmul_of_forall_smul_eq
    ((finrank_eq_one_iff_of_ne_zero' β hβ0).1 (TauCeti.finrank_detLine 𝕜 _))
    (detLineStabilizerChangeEquiv D₁ D₂ D₃ h (β' ⊗ₜ φ))
  refine ⟨φ₀, hφ₀, smul_left_injective 𝕜 hβ0 ?_⟩
  -- The first components of the parameter family are the family whose exterior product is `γ`.
  have hfst : exteriorPower.ιMulti 𝕜 _ (LinearMap.fst 𝕜 Λ Λ' ∘
      ((LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append (parameterProj D₁ D₂ ∘ v) z) ∘ Fin.cast hΛ)) = γ :=
    -- `LinearMap.fst` undoes `LinearMap.inl` pointwise by definition, hence the closing `rfl`.
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, hγ, ← ιMulti_comp_finCast hΛ]; rfl)
  have hβeq : exteriorPower.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v ∘ Fin.cast hK) =
      β :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, ιMulti_comp_finCast, hβ])
  calc φ₀ γ • β = TensorProduct.rid 𝕜 _ ((Dual.eval 𝕜 _ γ).lTensor _ (β ⊗ₜ φ₀)) := by simp
    _ = φ γ'' • β := by rw [← hφ₀, ← hfst, hstab, hβeq]

omit [FiniteDimensional 𝕜 D₁.ker] in
/-- The exterior products `γ'` and `γ''` of the two adapted families of `Λ × Λ'` differ by the
Koszul sign of the reordering in `ιMulti_append_inl_eq`. -/
private theorem eq_neg_one_pow_smul_of_coe_eq (h : Function.Surjective (D₁.coprod D₂))
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))) →
      (D₁.coprod (D₂.coprod D₃)).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ)
    {γ' : TauCeti.detLine 𝕜 (Λ × Λ')} (hγ' : (γ' : ExteriorAlgebra 𝕜 (Λ × Λ')) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append
        (LinearMap.inl 𝕜 Λ Λ' ∘ (parameterProj D₁ D₂ ∘ v)) (parameterProj D₁ (D₂.coprod D₃) ∘ w))
        (LinearMap.inl 𝕜 Λ Λ' ∘ z)))
    {γ'' : TauCeti.detLine 𝕜 (Λ × Λ')} (hγ'' : (γ'' : ExteriorAlgebra 𝕜 (Λ × Λ')) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (addedParameterProj D₁ D₂ D₃ ∘ w)
        (LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append (parameterProj D₁ D₂ ∘ v) z))) :
    γ' = ((-1 : 𝕜) ^ (finrank 𝕜 (parameterProj D₁ D₂).range * finrank 𝕜 Λ')) • γ'' := by
  have hq : (fun j ↦ ((0 : Λ), ((parameterProj D₁ (D₂.coprod D₃) ∘ w) j).2)) =
      addedParameterProj D₁ D₂ D₃ ∘ w := funext fun j ↦ by simp
  refine Subtype.ext ?_
  rw [Submodule.coe_smul, hγ', hγ'', ← finrank_range_addedParameterProj D₁ D₂ D₃ h, ← hq]
  exact ιMulti_append_inl_eq
    (finrank_eq_finrank_range_parameterProj_add_finrank_quotient D₁ D₂ h) _ _ _

/-- `ContinuousLinearMap.detLineCoprodEquiv_coprod` on a generator: `β` and `γ` are the exterior
products of adapted families of `ker (D₁.coprod D₂)` and `Λ`, and `β'` that of the adapted family
of the enlarged kernel built from them and from lifts `w` of the added directions. -/
private theorem detLineCoprodEquiv_coprod_tmul (h : Function.Surjective (D₁.coprod D₂))
    (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (w : Fin (finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))) →
      (D₁.coprod (D₂.coprod D₃)).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ)
    (hθ : exteriorPower.ιMulti 𝕜 _ (parameterToCoker D₁ D₂ ∘ z) ≠ 0)
    {β : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker} (hβ0 : β ≠ 0)
    (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod D₂).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v))
    {β' : TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker}
    (hβ' : (β' : ExteriorAlgebra 𝕜 (D₁.coprod (D₂.coprod D₃)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (Fin.append
        (kerCoprodHom D₁ (D₂.coprod D₃) ∘ u) (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v)) w))
    {γ : TauCeti.detLine 𝕜 Λ} (hγ : (γ : ExteriorAlgebra 𝕜 Λ) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterProj D₁ D₂ ∘ v) z))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ'))) :
    detLineCoprodEquiv D₁ (D₂.coprod D₃) (surjective_coprod_coprod D₁ D₂ D₃ h) (β' ⊗ₜ φ) =
      ((-1 : 𝕜) ^ (finrank 𝕜 (parameterProj D₁ D₂).range * finrank 𝕜 Λ')) •
        detLineCoprodEquiv D₁ D₂ h (detLineStabilizerChangeEquiv D₁ D₂ D₃ h (β' ⊗ₜ φ)) := by
  have hΛ := finrank_eq_finrank_range_parameterProj_add_finrank_quotient D₁ D₂ h
  have hl := finrank_range_addedParameterProj D₁ D₂ D₃ h
  have : FiniteDimensional 𝕜 (F ⧸ D₁.range) := Module.Finite.of_surjective _
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h)
  have h₁ : finrank 𝕜 (Λ × Λ') = finrank 𝕜 (parameterProj D₁ D₂).range +
      finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃)) + finrank 𝕜 (F ⧸ D₁.range) := by
    rw [Module.finrank_prod, hΛ, hl]
    omega
  have h₂ : finrank 𝕜 (Λ × Λ') = finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃)) +
      (finrank 𝕜 (parameterProj D₁ D₂).range + finrank 𝕜 (F ⧸ D₁.range)) := by
    rw [Module.finrank_prod, hΛ, hl]
    omega
  obtain ⟨γ', hγ'⟩ := exists_coe_detLine_eq h₁
    (Fin.append (Fin.append (LinearMap.inl 𝕜 Λ Λ' ∘ (parameterProj D₁ D₂ ∘ v))
      (parameterProj D₁ (D₂.coprod D₃) ∘ w)) (LinearMap.inl 𝕜 Λ Λ' ∘ z))
  obtain ⟨γ'', hγ''⟩ := exists_coe_detLine_eq h₂
    (Fin.append (addedParameterProj D₁ D₂ D₃ ∘ w)
      (LinearMap.inl 𝕜 Λ Λ' ∘ Fin.append (parameterProj D₁ D₂ ∘ v) z))
  obtain ⟨φ₀, hφ₀, hφ₀γ⟩ := exists_detLineStabilizerChangeEquiv_tmul_eq D₁ D₂ D₃ h u v w z hβ0
    hβ hβ' hγ hγ'' φ
  -- Compare the two sides after pairing with the exterior product of a cokernel basis.
  apply injective_rid_lTensor_eval (TauCeti.finrank_detLine 𝕜 _) hθ
  simp only [map_smul]
  rw [rid_lTensor_detLineCoprodEquiv_coprod_tmul D₁ D₂ D₃ h u v w z hβ' hγ' φ, hφ₀,
    detLineCoprodEquiv_tmul h u v z hβ hγ φ₀, hφ₀γ, eq_neg_one_pow_smul_of_coe_eq D₁ D₂ D₃ h v w z
      hγ' hγ'', map_smul, smul_assoc]

omit [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 Λ'] in
/-- The adapted families of the two stabilized kernels are linearly independent: a basis `bu` of
`ker D₁`, embedded by `x ↦ (x, 0)`, followed by lifts `v` of a basis of the range of the
parameter projection, and then, in the enlarged kernel, by lifts `w` of a basis of the range of
the added projection. -/
private theorem linearIndependent_adapted {a k l : ℕ} (bu : Basis (Fin a) 𝕜 D₁.ker)
    (br : Basis (Fin k) 𝕜 (parameterProj D₁ D₂).range)
    (bg : Basis (Fin l) 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃)))
    (v : Fin k → (D₁.coprod D₂).ker) (w : Fin l → (D₁.coprod (D₂.coprod D₃)).ker)
    (hv : ∀ i, parameterProj D₁ D₂ (v i) = br i)
    (hw : ∀ i, addedParameterProj D₁ D₂ D₃ (w i) = bg i) :
    LinearIndependent 𝕜 (Fin.append (kerCoprodHom D₁ D₂ ∘ bu) v) ∧
      LinearIndependent 𝕜 (Fin.append (Fin.append (kerCoprodHom D₁ (D₂.coprod D₃) ∘ bu)
        (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v)) w) := by
  have hx : LinearIndependent 𝕜 (Fin.append (kerCoprodHom D₁ D₂ ∘ bu) v) :=
    .fin_append_of_map_eq_zero (parameterProj D₁ D₂).toLinearMap
      (bu.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (kerCoprodHom_injective D₁ D₂)))
      (fun i ↦ by simp) (by
        convert br.linearIndependent.map' _ (Submodule.ker_subtype _)
        exact funext hv)
  refine ⟨hx, ?_⟩
  convert LinearIndependent.fin_append_of_map_eq_zero (addedParameterProj D₁ D₂ D₃)
    (hx.map' _ (LinearMap.ker_eq_bot.2 (kerCoprodCoprodHom_injective D₁ D₂ D₃)))
    (fun i ↦ (exact_kerCoprodCoprodHom_addedParameterProj D₁ D₂ D₃).apply_apply_eq_zero _) (by
      convert bg.linearIndependent.map' _ (Submodule.ker_subtype _)
      exact funext hw) using 2
  rw [Fin.comp_append]
  congr 1
  funext i
  simp [Subtype.ext_iff, Prod.mk_zero_zero]

/-- **Stabilizer independence of the determinant isomorphism.** Enlarging a surjective
stabilization `D₁.coprod D₂` by further directions `D₃ : Λ' →L[𝕜] F` changes the determinant
isomorphism `ContinuousLinearMap.detLineCoprodEquiv` only by the change of stabilizer
`ContinuousLinearMap.detLineStabilizerChangeEquiv`, up to the Koszul sign `(-1) ^ (k * l)`, where
`k` is the dimension of the range of the parameter projection of `D₁.coprod D₂` and `l = dim Λ'`.
So the identifications of the determinant line of `D₁` through the two stabilizations agree up to
this sign. -/
theorem detLineCoprodEquiv_coprod (h : Function.Surjective (D₁.coprod D₂))
    (x : TauCeti.detLine 𝕜 (D₁.coprod (D₂.coprod D₃)).ker ⊗[𝕜]
      Dual 𝕜 (TauCeti.detLine 𝕜 (Λ × Λ'))) :
    detLineCoprodEquiv D₁ (D₂.coprod D₃) (surjective_coprod_coprod D₁ D₂ D₃ h) x =
      ((-1 : 𝕜) ^ (finrank 𝕜 (parameterProj D₁ D₂).range * finrank 𝕜 Λ')) •
        detLineCoprodEquiv D₁ D₂ h (detLineStabilizerChangeEquiv D₁ D₂ D₃ h x) := by
  have := finiteDimensional_ker_coprod D₁ D₂
  have := finiteDimensional_ker_coprod D₁ (D₂.coprod D₃)
  have hsurj := (parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h
  have : FiniteDimensional 𝕜 (F ⧸ D₁.range) := Module.Finite.of_surjective _ hsurj
  -- Adapted families: a basis of `ker D₁`, lifts of bases of the ranges of the two parameter
  -- projections, and parameters whose classes form a basis of the cokernel of `D₁`.
  let bu := Module.finBasis 𝕜 D₁.ker
  let br := Module.finBasis 𝕜 (parameterProj D₁ D₂).range
  let bg := Module.finBasis 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃))
  let bc := Module.finBasis 𝕜 (F ⧸ D₁.range)
  choose v hv using fun i ↦ LinearMap.mem_range.1 (br i).2
  choose w hw using fun i ↦ LinearMap.mem_range.1 (bg i).2
  choose z hz using fun i ↦ hsurj (bc i)
  obtain ⟨hx, hy⟩ := linearIndependent_adapted D₁ D₂ D₃ bu br bg v w hv hw
  obtain ⟨β, hβ⟩ := exists_coe_detLine_eq (finrank_ker_coprod D₁ D₂)
    (Fin.append (kerCoprodHom D₁ D₂ ∘ bu) v)
  have hK' : finrank 𝕜 (D₁.coprod (D₂.coprod D₃)).ker = finrank 𝕜 D₁.ker +
      finrank 𝕜 (parameterProj D₁ D₂).range +
        finrank 𝕜 (LinearMap.range (addedParameterProj D₁ D₂ D₃)) := by
    rw [finrank_ker_coprod_coprod, finrank_ker_coprod]
  obtain ⟨β', hβ'⟩ := exists_coe_detLine_eq hK'
    (Fin.append (Fin.append (kerCoprodHom D₁ (D₂.coprod D₃) ∘ bu)
      (kerCoprodCoprodHom D₁ D₂ D₃ ∘ v)) w)
  obtain ⟨γ, hγ⟩ := exists_coe_detLine_eq
    (finrank_eq_finrank_range_parameterProj_add_finrank_quotient D₁ D₂ h)
    (Fin.append (parameterProj D₁ D₂ ∘ v) z)
  have hθ : exteriorPower.ιMulti 𝕜 _ (parameterToCoker D₁ D₂ ∘ z) ≠ 0 := by
    rw [show parameterToCoker D₁ D₂ ∘ z = bc from funext hz]
    exact (exteriorPower.ιMulti_ne_zero_iff _).2 bc.linearIndependent
  -- `β'` spans the one-dimensional source, so the generators `β' ⊗ φ` suffice.
  have hspan := (finrank_eq_one_iff_of_ne_zero' β' (ne_zero_of_coe_detLine_eq hy hβ')).1
    (TauCeti.finrank_detLine 𝕜 _)
  obtain ⟨φ, rfl⟩ := exists_eq_tmul_of_forall_smul_eq hspan x
  exact detLineCoprodEquiv_coprod_tmul D₁ D₂ D₃ h bu v w z hθ (ne_zero_of_coe_detLine_eq hx hβ)
    hβ hβ' hγ φ

end StabilizerChange

end ContinuousLinearMap
