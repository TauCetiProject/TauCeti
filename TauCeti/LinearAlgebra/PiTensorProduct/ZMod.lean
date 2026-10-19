/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Data.ZMod.Basic

/-!
# Indexed tensor powers of cyclic groups

For a nonempty finite index type, the tensor product over `ℤ` of copies of `ZMod n` is again
`ZMod n`.  The equivalence is multiplication of the tensor factors.  This is the coefficient
calculation used when tensor induction is applied to the trivial `𝔽₂`-representation in the
construction of the Evens norm.

## Main definitions

* `PiTensorProduct.zmodEquiv`: multiplication as a linear equivalence from an indexed tensor
  power of `ZMod n` to `ZMod n`.
* `PiTensorProduct.uliftZModEquiv`: the same equivalence for the universe-lifted coefficient
  `ULift (ZMod n)`.
-/

public section

open scoped TensorProduct

universe u

namespace PiTensorProduct

variable {ι : Type*} [Fintype ι] (n : ℕ)

private noncomputable def zmodMul : (⨂[ℤ] _ : ι, ZMod n) →ₗ[ℤ] ZMod n :=
  lift (MultilinearMap.mkPiAlgebra ℤ ι (ZMod n))

@[simp]
private theorem zmodMul_tprod (x : ι → ZMod n) :
    zmodMul (ι := ι) n (tprod ℤ x) = ∏ i, x i := by
  simp [zmodMul]

omit [Fintype ι] in
/-- In a tensor power over `ℤ` of `ZMod n`, the embeddings of `ZMod n` as the different tensor
factors all agree, since every element of `ZMod n` is an integer multiple of `1`. -/
theorem singleAlgHom_zmod_eq [DecidableEq ι] (i j : ι) (x : ZMod n) :
    singleAlgHom (R := ℤ) (A := fun _ : ι ↦ ZMod n) i x = singleAlgHom j x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  simp only [map_intCast]

variable [Nonempty ι]

private noncomputable def zmodUnit [DecidableEq ι] :
    ZMod n →ₗ[ℤ] (⨂[ℤ] _ : ι, ZMod n) :=
  (singleAlgHom (R := ℤ) (A := fun _ : ι ↦ ZMod n)
    (Classical.choice ‹Nonempty ι›)).toLinearMap

omit [Fintype ι] in
private theorem zmodUnit_apply [DecidableEq ι] (x : ZMod n) :
    zmodUnit (ι := ι) n x =
      tprod ℤ (Pi.mulSingle (Classical.choice ‹Nonempty ι›) x) := by
  classical
  rfl

private theorem zmodUnit_comp_zmodMul [DecidableEq ι] :
    (zmodUnit (ι := ι) n).comp (zmodMul (ι := ι) n) = LinearMap.id := by
  classical
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
    zmodMul_tprod, zmodUnit, AlgHom.toLinearMap_apply]
  calc
    singleAlgHom (Classical.choice ‹Nonempty ι›) (∏ i, x i) =
        ∏ i, singleAlgHom (Classical.choice ‹Nonempty ι›) (x i) := by simp
    _ = ∏ i, singleAlgHom i (x i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact singleAlgHom_zmod_eq n _ _ _
    _ = ∏ i, tprod ℤ (Pi.mulSingle i (x i)) := rfl
    _ = tprod ℤ (∏ i, Pi.mulSingle i (x i)) := (tprod_prod Finset.univ _).symm
    _ = tprod ℤ x := by
      congr 1
      funext i
      simp

private theorem zmodMul_comp_zmodUnit [DecidableEq ι] :
    (zmodMul (ι := ι) n).comp (zmodUnit (ι := ι) n) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, zmodUnit_apply, zmodMul_tprod]
  simp [Pi.mulSingle, Finset.prod_update_of_mem]

/-- A nonempty finite tensor power over `ℤ` of `ZMod n` is canonically `ZMod n`, by multiplying
the tensor factors. -/
noncomputable def zmodEquiv : (⨂[ℤ] _ : ι, ZMod n) ≃ₗ[ℤ] ZMod n := by
  classical
  exact LinearEquiv.ofLinearMap (zmodMul (ι := ι) n) (zmodUnit (ι := ι) n)
    (zmodMul_comp_zmodUnit n) (zmodUnit_comp_zmodMul n)

/-- The cyclic tensor-power equivalence multiplies pure tensors. -/
@[simp]
theorem zmodEquiv_tprod (x : ι → ZMod n) :
    zmodEquiv (ι := ι) n (tprod ℤ x) = ∏ i, x i := by
  simp [zmodEquiv]

/-- A nonempty finite tensor power over `ℤ` of the universe-lifted coefficient `ULift (ZMod n)` is
again that coefficient, by multiplying the tensor factors. -/
noncomputable def uliftZModEquiv :
    (⨂[ℤ] _ : ι, ULift.{u} (ZMod n)) ≃ₗ[ℤ] ULift.{u} (ZMod n) :=
  PiTensorProduct.congr (fun _ ↦ ULift.moduleEquiv) ≪≫ₗ
    zmodEquiv (ι := ι) n ≪≫ₗ ULift.moduleEquiv.symm

/-- The lifted cyclic tensor-power equivalence multiplies the underlying values of a pure
tensor. -/
@[simp]
theorem uliftZModEquiv_tprod (x : ι → ULift.{u} (ZMod n)) :
    uliftZModEquiv (ι := ι) n (tprod ℤ x) = ULift.up (∏ i, (x i).down) := by
  simp [uliftZModEquiv]

end PiTensorProduct
