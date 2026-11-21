/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Locally constant families of finitely supported functions as linear maps

Let `ι` be a finite discrete space and `X` a topological space. A locally constant function
`X → (ι →₀ R)` is the same as an `R`-linear map `LocallyConstant ι R →ₗ[R] LocallyConstant X R`:
a family `φ` sends `f` to `x ↦ ∑ i, φ x i * f i`, and a linear map `L` is recovered from its
values on the indicator functions of the points of `ι`
(`LocallyConstant.finsuppLinearEquiv`). The index type of the finitely supported functions is
allowed to differ from `ι` by an equivalence, so that it can be a universe lift of `ι`.

For a finite set `T`, the left-hand side is the module of sections over `X` of the discrete
condensed module `R[T]`. The equivalence thus identifies `R[T]` with the dual of the locally
constant functions on `T`, which is the finite case of the description of free solid modules on
profinite sets.
-/

public section

namespace LocallyConstant

variable (R : Type*) [CommSemiring R] (X : Type*) [TopologicalSpace X]
  {ι κ : Type*} [TopologicalSpace ι] [DiscreteTopology ι] [Finite κ] (e : κ ≃ ι)

/-- For a finite discrete space `ι` and an equivalence `e : κ ≃ ι`, locally constant maps
`X → (κ →₀ R)` are the same as `R`-linear maps `LocallyConstant ι R →ₗ[R] LocallyConstant X R`.
A family `φ` sends `f` to `x ↦ ∑ k, φ x k * f (e k)`; the inverse records the values of a linear
map on the indicator functions of the points of `ι`. -/
noncomputable def finsuppLinearEquiv :
    LocallyConstant X (κ →₀ R) ≃ₗ[R] (LocallyConstant ι R →ₗ[R] LocallyConstant X R) where
  toFun φ :=
    { toFun f := φ.map (Finsupp.linearCombination R (f ∘ e))
      map_add' f g := by
        ext x
        simp [Finsupp.linearCombination_apply, mul_add, Finsupp.sum_add]
      map_smul' r f := by
        ext x
        simp [Finsupp.linearCombination_apply, Finsupp.mul_sum, mul_left_comm] }
  map_add' φ ψ := by ext f x; simp
  map_smul' r φ := by ext f x; simp
  invFun L :=
    letI := Fintype.ofFinite κ
    ∑ k, (L (charFn R (isClopen_discrete {e k}))).map (Finsupp.single k)
  left_inv φ := by
    classical
    let := Fintype.ofFinite κ
    ext x k
    have hx (g : κ → LocallyConstant X (κ →₀ R)) : (∑ k, g k) x = ∑ k, g k x :=
      map_sum (evalₗ R x) g _
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hx, map_apply, Function.comp_apply]
    rw [Finset.sum_apply']
    simp [Finsupp.single_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype, coe_charFn,
      Pi.single_apply]
  right_inv L := by
    classical
    let := Fintype.ofFinite κ
    ext f x
    -- Expand `f` in the basis of indicator functions of the points of `ι`.
    have hf : f = ∑ k, f (e k) • charFn R (isClopen_discrete {e k}) := by
      ext i
      obtain ⟨j, rfl⟩ := e.surjective i
      have hi (g : κ → LocallyConstant ι R) : (∑ k, g k) (e j) = ∑ k, g k (e j) :=
        map_sum (evalₗ R (e j)) g _
      simp [hi, coe_charFn, Pi.single_apply]
    have hx (g : κ → LocallyConstant X (κ →₀ R)) : (∑ k, g k) x = ∑ k, g k x :=
      map_sum (evalₗ R x) g _
    have hx' (g : κ → LocallyConstant X R) : (∑ k, g k) x = ∑ k, g k x :=
      map_sum (evalₗ R x) g _
    conv_rhs => rw [hf]
    simp [hx, hx', Finsupp.linearCombination_apply, Finsupp.sum_fintype, Finsupp.single_apply,
      mul_comm]

@[simp]
lemma finsuppLinearEquiv_apply_apply (φ : LocallyConstant X (κ →₀ R)) (f : LocallyConstant ι R) :
    finsuppLinearEquiv R X e φ f = φ.map (Finsupp.linearCombination R (f ∘ e)) :=
  (rfl)

end LocallyConstant
