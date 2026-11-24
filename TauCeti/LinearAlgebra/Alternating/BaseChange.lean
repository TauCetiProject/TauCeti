/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Extension of scalars for alternating maps

Let `A` be a commutative `R`-algebra. An `R`-alternating map `f : M [⋀^Fin n]→ₗ[R] N` extends
uniquely to an `A`-alternating map `f.baseChange A : (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)` with
`f.baseChange A (fun i ↦ a i ⊗ₜ m i) = (∏ i, a i) ⊗ₜ f m` (`AlternatingMap.baseChange_tmul`).
It is constructed through the universal property of exterior powers and the comparison
`⋀[A]^n (A ⊗[R] M) ≃ A ⊗[R] ⋀[R]^n M` (`TauCeti.exteriorPower.equivBaseChange`); this is the
alternating analogue of `LinearMap.baseChange` and `LinearMap.BilinMap.baseChange`.

An `A`-alternating map on `A ⊗[R] M` is determined by its values on the families `1 ⊗ₜ m i`
(`AlternatingMap.baseChange_ext`), or, in positive degree, by its interior products with the
tensors `1 ⊗ₜ x` (`AlternatingMap.baseChange_ext_curryLeft`). Inserting `1 ⊗ₜ x` as first argument
of `f.baseChange A` gives the extension of scalars of `f.curryLeft x`
(`AlternatingMap.curryLeft_baseChange`).

When `M` is finite free, extension of scalars identifies `A ⊗[R] (M [⋀^Fin n]→ₗ[R] N)` with the
`A`-alternating maps on `A ⊗[R] M` (`AlternatingMap.baseChangeEquiv`), sending `a ⊗ₜ f` to
`a • f.baseChange A`. Taking `M` a finite-dimensional Lie algebra, this is the degreewise
comparison of Chevalley–Eilenberg cochains with their extension of scalars.

## Main definitions

* `AlternatingMap.baseChange`: the extension of scalars of an alternating map.
* `AlternatingMap.baseChangeEquiv`: for finite free `M`, the isomorphism
  `A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[A] (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N)`.

## Main results

* `AlternatingMap.baseChange_tmul`: the value on a family of pure tensors.
* `AlternatingMap.baseChange_ext`, `AlternatingMap.baseChange_ext_curryLeft`: extensionality for
  alternating maps on `A ⊗[R] M`.
* `AlternatingMap.curryLeft_baseChange`: compatibility with interior products.
* `AlternatingMap.baseChangeEquiv_tmul`: the comparison on pure tensors.
-/

public section

open TensorProduct

namespace AlternatingMap

variable {R : Type*} (A : Type*) {M N P : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]

/-- The extension of scalars of an alternating map: the `A`-alternating map on `A ⊗[R] M` sending
`(a i ⊗ₜ m i)ᵢ` to `(∏ i, a i) ⊗ₜ f m`. -/
noncomputable def baseChange {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) :
    (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N) :=
  exteriorPower.alternatingMapLinearEquiv.symm
    ((exteriorPower.alternatingMapLinearEquiv f).baseChange A ∘ₗ
      (TauCeti.exteriorPower.equivBaseChange A n).toLinearMap)

/-- The extension of scalars of `f` on a family of pure tensors. -/
@[simp]
theorem baseChange_tmul {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (a : Fin n → A) (m : Fin n → M) :
    f.baseChange A (fun i ↦ a i ⊗ₜ m i) = (∏ i, a i) ⊗ₜ f m := by
  simp [baseChange]

/-- Two `A`-alternating maps on `A ⊗[R] M` agree as soon as they agree on all families of tensors
`1 ⊗ₜ m i`. -/
theorem baseChange_ext {n : ℕ} {f g : (A ⊗[R] M) [⋀^Fin n]→ₗ[A] P}
    (h : ∀ m : Fin n → M, f (fun i ↦ 1 ⊗ₜ m i) = g (fun i ↦ 1 ⊗ₜ m i)) : f = g := by
  set e := TauCeti.exteriorPower.equivBaseChange (R := R) (M := M) A n
  set F := exteriorPower.alternatingMapLinearEquiv f
  set G := exteriorPower.alternatingMapLinearEquiv g
  have h1 : (F ∘ₗ e.symm.toLinearMap).restrictScalars R ∘ₗ TensorProduct.mk R A _ 1 =
      (G ∘ₗ e.symm.toLinearMap).restrictScalars R ∘ₗ TensorProduct.mk R A _ 1 := by
    ext m
    simp [e, F, G, h]
  have hFG : F ∘ₗ e.symm.toLinearMap = G ∘ₗ e.symm.toLinearMap :=
    (LinearMap.liftBaseChangeEquiv A).symm.injective (LinearMap.ext fun x ↦ by
      simpa using congr($h1 x))
  apply exteriorPower.alternatingMapLinearEquiv.injective
  exact LinearMap.ext fun y ↦ by simpa using congr($hFG (e y))

/-- Two `A`-alternating maps on `A ⊗[R] M` in `n + 1` arguments agree as soon as their interior
products with all tensors `1 ⊗ₜ x` agree. -/
theorem baseChange_ext_curryLeft {n : ℕ} {f g : (A ⊗[R] M) [⋀^Fin (n + 1)]→ₗ[A] P}
    (h : ∀ x : M, f.curryLeft (1 ⊗ₜ x) = g.curryLeft (1 ⊗ₜ x)) : f = g := by
  refine baseChange_ext A fun m ↦ ?_
  have hcons : Matrix.vecCons ((1 : A) ⊗ₜ[R] m 0) (fun i ↦ 1 ⊗ₜ m i.succ) =
      fun i ↦ 1 ⊗ₜ m i :=
    Fin.cons_self_tail (fun i ↦ (1 : A) ⊗ₜ[R] m i)
  simpa [curryLeft_apply_apply, hcons] using congr($(h (m 0)) (fun i ↦ 1 ⊗ₜ m i.succ))

/-- The extension of scalars of the zero map is zero. -/
@[simp]
theorem baseChange_zero {n : ℕ} : (0 : M [⋀^Fin n]→ₗ[R] N).baseChange A = 0 :=
  baseChange_ext A fun m ↦ by simp

/-- Extension of scalars of alternating maps is additive. -/
@[simp]
theorem baseChange_add {n : ℕ} (f g : M [⋀^Fin n]→ₗ[R] N) :
    (f + g).baseChange A = f.baseChange A + g.baseChange A :=
  baseChange_ext A fun m ↦ by simp [tmul_add]

/-- Extension of scalars of alternating maps is `R`-linear. -/
@[simp]
theorem baseChange_smul {n : ℕ} (r : R) (f : M [⋀^Fin n]→ₗ[R] N) :
    (r • f).baseChange A = r • f.baseChange A :=
  baseChange_ext A fun m ↦ by simp [tmul_smul]

/-- Extension of scalars of alternating maps commutes with negation. -/
@[simp]
theorem baseChange_neg {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) :
    (-f).baseChange A = -f.baseChange A :=
  baseChange_ext A fun m ↦ by simp [tmul_neg]

/-- Extension of scalars of alternating maps commutes with subtraction. -/
@[simp]
theorem baseChange_sub {n : ℕ} (f g : M [⋀^Fin n]→ₗ[R] N) :
    (f - g).baseChange A = f.baseChange A - g.baseChange A :=
  baseChange_ext A fun m ↦ by simp [tmul_sub]

/-- Inserting `1 ⊗ₜ x` as the first argument of the extension of scalars of `f` gives the
extension of scalars of `f.curryLeft x`. -/
@[simp]
theorem curryLeft_baseChange {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) :
    (f.baseChange A).curryLeft ((1 : A) ⊗ₜ x) = (f.curryLeft x).baseChange A := by
  refine baseChange_ext A fun m ↦ ?_
  have hcons : Matrix.vecCons ((1 : A) ⊗ₜ[R] x) (fun i ↦ 1 ⊗ₜ m i) =
      fun i ↦ 1 ⊗ₜ Matrix.vecCons x m i :=
    (Fin.comp_cons _ x m).symm
  simp [curryLeft_apply_apply, hcons]

section Equiv

variable (R M N) (n : ℕ) [Module.Free R M] [Module.Finite R M]

/-- For finite free `M`, extension of scalars identifies `A ⊗[R] (M [⋀^Fin n]→ₗ[R] N)` with the
`A`-alternating maps on `A ⊗[R] M` with values in `A ⊗[R] N`: it sends `a ⊗ₜ f` to
`a • f.baseChange A` (`AlternatingMap.baseChangeEquiv_tmul`). -/
noncomputable def baseChangeEquiv :
    A ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[A] (A ⊗[R] M) [⋀^Fin n]→ₗ[A] (A ⊗[R] N) :=
  LinearEquiv.baseChange R A _ _ exteriorPower.alternatingMapLinearEquiv ≪≫ₗ
    ((TensorProduct.isBaseChange R (⋀[R]^n M) A).linearMapLeftRight
      (TensorProduct.isBaseChange R N A)).equiv ≪≫ₗ
    LinearEquiv.congrLeft (A ⊗[R] N) A (TauCeti.exteriorPower.equivBaseChange A n).symm ≪≫ₗ
    exteriorPower.alternatingMapLinearEquiv.symm

variable {R M N n}

/-- The comparison `AlternatingMap.baseChangeEquiv` on pure tensors. -/
@[simp]
theorem baseChangeEquiv_tmul (a : A) (f : M [⋀^Fin n]→ₗ[R] N) :
    baseChangeEquiv R A M N n (a ⊗ₜ f) = a • f.baseChange A := by
  refine baseChange_ext A fun m ↦ ?_
  have h := IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R _ A)
    (TensorProduct.mk R A N 1) (exteriorPower.alternatingMapLinearEquiv f)
    (exteriorPower.ιMulti R n m)
  simp only [TensorProduct.mk_apply] at h
  simp [baseChangeEquiv, IsBaseChange.equiv_tmul, h]

end Equiv

end AlternatingMap
