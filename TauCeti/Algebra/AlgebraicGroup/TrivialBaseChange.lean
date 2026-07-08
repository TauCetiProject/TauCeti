/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# Base change of the trivial affine group

The coordinate Hopf algebra of the trivial affine group over `k` is `k` itself. After a
base change `k → K`, the coordinate Hopf algebra is `K ⊗[k] k`, which still represents the
trivial group-valued functor. This file records the corresponding functor-of-points
calculation: for every commutative `K`-algebra `A`, the convolution group of
`K`-algebra maps `K ⊗[k] k →ₐ[K] A` is the one-element group `PUnit`.

This is the terminal-object worked example for the ReductiveGroups roadmap, Layer 0: the
Hopf-algebra/functor-of-points dictionary needs both the terminal object over `Spec k` and
compatibility with base change. The file packages the base-change point equivalence, tensor-value
normal forms, and identity and inverse normal forms. Naturality in the value algebra is not
restated here: all the groups involved are trivial, and the general statement is the
composite of `TauCeti.AlgHom.mapValue_baseChangePointsMulEquiv` with
`TauCeti.TrivialGroup.pointsMulEquiv_mapValue`.

## Main declarations

* `TauCeti.TrivialGroup.baseChangePointsMulEquiv`: base-changed trivial-group points are
  `PUnit`.
* `TauCeti.TrivialGroup.baseChangePointsMulEquiv_symm_apply_tmul`: the unique point sends
  `s ⊗ r` to `s • algebraMap k A r`.

## References

This reuses Tau Ceti's `AlgHom.baseChangePointsMulEquiv` and
`TrivialGroup.pointsMulEquiv`, which are built on Mathlib's tensor-product base-change
adjunction `AlgHom.liftEquiv` and the canonical Hopf algebra structure on the base ring.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace TrivialGroup

universe u v w

variable {k : Type u} {K : Type v} {A : Type w}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The `A`-points of the base change of the trivial affine group are the one-element group.

The source is the convolution group of `K`-algebra maps out of `K ⊗[k] k`. The equivalence is
the inverse of the generic base-change equivalence for points, followed by the trivial-group
points calculation over `k`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] k →ₐ[K] A) ≃* PUnit.{1} :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := k) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (A := A))

/-- The base-changed trivial-group points equivalence sends every point to the unique
element of `PUnit`. -/
@[simp]
theorem baseChangePointsMulEquiv_apply (f : WithConv (K ⊗[k] k →ₐ[K] A)) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) f = PUnit.unit :=
  Subsingleton.elim _ _

/-- The inverse base-changed trivial-group points equivalence sends the unique element to
the scalar-extension of the unique `k`-point of the trivial group. -/
private theorem baseChangePointsMulEquiv_symm_apply (u : PUnit.{1}) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u =
      AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := k) (R := A)
        ((pointsMulEquiv (R := k) (A := A)).symm u) :=
  rfl

/-- The unique base-changed trivial-group point sends `s ⊗ r` to
`s • algebraMap k A r`. -/
theorem baseChangePointsMulEquiv_symm_apply_tmul (u : PUnit.{1}) (s : K) (r : k) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u).ofConv
        (s ⊗ₜ[k] r) =
      s • algebraMap k A r := by
  rw [baseChangePointsMulEquiv_symm_apply, AlgHom.baseChangePointsMulEquiv_apply_tmul]
  simp

/-- On `1 ⊗ r`, the unique base-changed trivial-group point is the structure map
`k → A`. -/
theorem baseChangePointsMulEquiv_symm_apply_one_tmul (u : PUnit.{1}) (r : k) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u).ofConv
        (1 ⊗ₜ[k] r) =
      algebraMap k A r := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul, one_smul]

/-- Every base-changed trivial-group convolution point is the identity point. -/
theorem baseChangeConvPoint_eq_one (f : WithConv (K ⊗[k] k →ₐ[K] A)) : f = 1 := by
  apply (baseChangePointsMulEquiv (k := k) (K := K) (A := A)).injective
  simp

/-- The identity normal form for base-changed trivial-group convolution points, as a simp
proposition. -/
@[simp]
theorem baseChangeConvPoint_eq_one_iff (f : WithConv (K ⊗[k] k →ₐ[K] A)) : f = 1 ↔ True :=
  ⟨fun _ => trivial, fun _ => baseChangeConvPoint_eq_one f⟩

/-- Every base-changed trivial-group point sends `s ⊗ r` to `s • algebraMap k A r`. -/
@[simp]
theorem convPoint_apply_tmul (f : WithConv (K ⊗[k] k →ₐ[K] A)) (s : K) (r : k) :
    f.ofConv (s ⊗ₜ[k] r) = s • algebraMap k A r := by
  have hf :
      f = (baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm PUnit.unit := by
    apply (baseChangePointsMulEquiv (k := k) (K := K) (A := A)).injective
    simp
  rw [hf, baseChangePointsMulEquiv_symm_apply_tmul]

/-- The inverse of any base-changed trivial-group point is again the unique point. -/
theorem convInv_apply_tmul (f : WithConv (K ⊗[k] k →ₐ[K] A)) (s : K) (r : k) :
    (f⁻¹).ofConv (s ⊗ₜ[k] r) = s • algebraMap k A r := by
  rw [baseChangeConvPoint_eq_one (f⁻¹), convPoint_apply_tmul]

end TrivialGroup

end TauCeti
