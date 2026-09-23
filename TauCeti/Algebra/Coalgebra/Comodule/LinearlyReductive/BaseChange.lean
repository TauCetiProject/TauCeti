/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.Algebra.TensorProduct.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Complete reducibility descends along scalar extension

Let `C` be a coalgebra over a field `k`, let `V` be a `C`-comodule, and let `A` be a nonzero
commutative `k`-algebra. If the base-changed comodule `A ⊗[k] V` over `A ⊗[k] C` is completely
reducible, then so is `V`.

Consequently linear reductivity of a coalgebra descends from any field extension. For coordinate
Hopf algebras this is the statement that an affine group over `k` is linearly reductive as soon as
it becomes linearly reductive over some extension field; this is how linear reductivity of groups
which are only diagonalizable after extension, such as non-split tori, is reached.

## Main declarations

* `TauCeti.Comodule.IsCompletelyReducible.of_baseChange`: complete reducibility of
  `A ⊗[k] V` over `A ⊗[k] C` implies complete reducibility of `V` over `C`.
* `TauCeti.Coalgebra.IsLinearlyReductive.of_baseChange`: linear reductivity of `K ⊗[k] C`
  over a field extension `K` implies linear reductivity of `C`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {k : Type u} {C : Type v} {V : Type w} (A : Type x)
variable [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid V] [Module k V] [Comodule k C V]
variable [CommRing A] [Algebra k A]

/-- Pairing the scalar factor against a `k`-linear functional `l : A → k` intertwines the
base-changed coaction on `A ⊗[k] V` with the original coaction on `V`. -/
private theorem coact_lid_rTensor (l : A →ₗ[k] k) (x : A ⊗[k] V) :
    letI := Comodule.baseChange (R := k) (H := C) (M := V) A
    coact (R := k) (C := C) (M := V) (TensorProduct.lid k V (l.rTensor V x)) =
      TensorProduct.lid k (V ⊗[k] C) (l.rTensor (V ⊗[k] C)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange k A V C).symm
          (coact (R := A) (C := A ⊗[k] C) (M := A ⊗[k] V) x))) := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := V) A
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a v => simp

/-- The `k`-linear endomorphism `v ↦ (l ⊗ id) (π (1 ⊗ v))` of `V` obtained from an endomorphism
`π` of the base-changed comodule and a `k`-linear functional `l : A → k`. -/
private noncomputable def descendLinearMap (l : A →ₗ[k] k) (π : A ⊗[k] V →ₗ[A] A ⊗[k] V) :
    V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap ∘ₗ l.rTensor V ∘ₗ π.restrictScalars k ∘ₗ
    TensorProduct.mk k A V 1

private theorem descendLinearMap_apply (l : A →ₗ[k] k) (π : A ⊗[k] V →ₗ[A] A ⊗[k] V) (v : V) :
    descendLinearMap A l π v = TensorProduct.lid k V (l.rTensor V (π ((1 : A) ⊗ₜ[k] v))) :=
  rfl

/-- If `π` is a comodule endomorphism of `A ⊗[k] V`, then `v ↦ (l ⊗ id) (π (1 ⊗ v))` is a
comodule endomorphism of `V`. -/
private noncomputable def descendHom (l : A →ₗ[k] k)
    (π : letI := Comodule.baseChange (R := k) (H := C) (M := V) A
      Hom A (A ⊗[k] C) (A ⊗[k] V) (A ⊗[k] V)) :
    Hom k C V V := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := V) A
  refine ⟨descendLinearMap A l π.toLinearMap, ?_⟩
  ext v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, descendLinearMap_apply, coact_lid_rTensor,
    Hom.coe_toLinearMap, ← Hom.map_coact_apply, baseChange_coact, baseChangeCoact_tmul]
  induction coact (R := k) (C := C) (M := V) v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul u c =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [Algebra.TensorProduct.lid_rTensor_distribBaseChange_symm, descendLinearMap_apply]

private theorem descendHom_toLinearMap (l : A →ₗ[k] k)
    (π : letI := Comodule.baseChange (R := k) (H := C) (M := V) A
      Hom A (A ⊗[k] C) (A ⊗[k] V) (A ⊗[k] V)) :
    letI := Comodule.baseChange (R := k) (H := C) (M := V) A
    (descendHom A l π).toLinearMap = descendLinearMap A l π.toLinearMap :=
  rfl

private theorem descendHom_apply (l : A →ₗ[k] k)
    (π : letI := Comodule.baseChange (R := k) (H := C) (M := V) A
      Hom A (A ⊗[k] C) (A ⊗[k] V) (A ⊗[k] V)) (v : V) :
    descendHom A l π v = TensorProduct.lid k V (l.rTensor V (π ((1 : A) ⊗ₜ[k] v))) := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := V) A
  rw [← Hom.coe_toLinearMap, descendHom_toLinearMap, descendLinearMap_apply, Hom.coe_toLinearMap]

/-- **Complete reducibility descends along scalar extension.** If `A` is a nonzero commutative
algebra over the field `k` and the base-changed comodule `A ⊗[k] V` over `A ⊗[k] C` is completely
reducible, then `V` is completely reducible over `C`. -/
theorem IsCompletelyReducible.of_baseChange [Nontrivial A]
    (h : letI := Comodule.baseChange (R := k) (H := C) (M := V) A
      IsCompletelyReducible A (A ⊗[k] C) (A ⊗[k] V)) :
    IsCompletelyReducible k C V := by
  -- Descend a projection along a complementary base-changed subcomodule by pairing its scalar
  -- factor against a functional that sends `1` to `1`.
  let _ := Comodule.baseChange (R := k) (H := C) (M := V) A
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  have : Module.Flat k C := by
    let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
    infer_instance
  -- A `k`-linear functional on `A` taking the value `1` at `1`.
  obtain ⟨l, hl⟩ := (Algebra.linearMap k A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k A).injective)
  have hl1 : l 1 = 1 := by
    simpa using LinearMap.congr_fun hl 1
  rw [isCompletelyReducible_iff_forall_exists_hom]
  intro W
  let _ : Comodule k C W := Subcomodule.instComodule W
  let _ := Comodule.baseChange (R := k) (H := C) (M := W) A
  -- The scalar extension of `W` is a subcomodule of `A ⊗[k] V`; project onto it equivariantly
  -- along a complementary subcomodule, then push the projection down to `V` using `l`.
  let WA : Subcomodule A (A ⊗[k] C) (A ⊗[k] V) :=
    Hom.range (Hom.baseChange A (Subcomodule.subtype W))
  obtain ⟨QA, hQA⟩ := h.exists_isCompl WA
  have hWA : ∀ y ∈ WA, TensorProduct.lid k V (l.rTensor V y) ∈ W := by
    intro y hy
    obtain ⟨z, rfl⟩ := Hom.mem_range.1 hy
    clear hy
    rw [← Hom.coe_toLinearMap, Hom.baseChange_toLinearMap]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact add_mem hx hy
    | tmul a w => simpa using W.toSubmodule.smul_mem (l a) w.2
  refine ⟨descendHom A l (Subcomodule.projection WA QA hQA), fun v ↦ ?_, fun w hw ↦ ?_⟩
  · rw [descendHom_apply]
    exact hWA _ (Subcomodule.projection_apply_mem hQA _)
  · have hw' : (1 : A) ⊗ₜ[k] w ∈ WA := Hom.mem_range.2 ⟨(1 : A) ⊗ₜ[k] ⟨w, hw⟩, by simp⟩
    simp [descendHom_apply, Subcomodule.projection_apply_of_mem_left hQA hw', hl1]

end Comodule

namespace Coalgebra

variable {k : Type u} {C : Type v} (K : Type x)
variable [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [Field K] [Algebra k K]

/-- **Linear reductivity descends along field extensions.** If the scalar extension `K ⊗[k] C`
of a coalgebra to an extension field `K` is linearly reductive, then so is `C`.

Linear reductivity of `K ⊗[k] C` is only required for carriers in the universe of `K`, which by
`TauCeti.Coalgebra.IsLinearlyReductive.isCompletelyReducible` covers every universe. -/
theorem IsLinearlyReductive.of_baseChange
    (h : IsLinearlyReductive.{x, max x v, x} K (K ⊗[k] C)) :
    IsLinearlyReductive.{u, v, w} k C := by
  refine of_forall_isCompletelyReducible k fun V _ _ _ _ ↦ ?_
  let _ := Comodule.baseChange (R := k) (H := C) (M := V) K
  exact Comodule.IsCompletelyReducible.of_baseChange K h.isCompletelyReducible

end Coalgebra

end TauCeti
