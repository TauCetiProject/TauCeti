/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.PicardGroup
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Character lines of affine diagonalizable torsors

For an affine action of a diagonalizable group on `Spec A` over `Spec R`, the action on
coordinates is a comodule algebra over the group algebra of its character group. The internal
direct sum `Comodule.isInternal_weightSpace` breaks `A` into the character weight spaces.
Surjectivity of the torsor's Galois map forces the product of opposite weights to contain
`1` by projecting a lift of a character monomial to the two opposite weights.

For a faithfully flat torsor the trivial weight is the image of `R`. The weight spaces are
then invertible submodules, and multiplication identifies the tensor product of two character
lines with their product character line. On affine opens these are the coefficient modules
used in relative torus embeddings. Conversely, on a faithful algebra this condition on
opposite weights yields faithful flatness and a bijective Galois map.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, §6.1.2.1.
* K.-H. Ulbrich's strong-grading criterion, as stated in S. Montgomery,
  *Hopf Galois theory: a survey*, Theorem 2.6.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

open Comodule

section Monoid

variable {R G A : Type*} [CommSemiring R] [Monoid G] [Semiring A] [Algebra R A]
  [ComoduleAlgebra R (MonoidAlgebra R G) A]

local notation "W" => weightSpace R G A

/-- A product of homogeneous elements has the product character. -/
theorem mul_mem_weightSpace {g h : G} {a b : A} (ha : a ∈ W g) (hb : b ∈ W h) :
    a * b ∈ W (g * h) := by
  simp [mem_weightSpace, mem_weightSpace.mp ha, mem_weightSpace.mp hb,
    MonoidAlgebra.single_mul_single]

/-- The trivial weight space is the underlying submodule of the coinvariant algebra. -/
theorem weightSpace_one_eq_coinvariants :
    W 1 = (coinvariants R (MonoidAlgebra R G) A).toSubmodule := by
  ext a
  simp [MonoidAlgebra.one_def]

/-- The unit belongs to the trivial weight space. -/
theorem one_mem_weightSpace : (1 : A) ∈ W (1 : G) := by
  rw [weightSpace_one_eq_coinvariants]
  exact (coinvariants R (MonoidAlgebra R G) A).one_mem

/-- The product of two weight submodules lies in the weight given by the product character. -/
theorem weightSpace_mul_le (g h : G) : W g * W h ≤ W (g * h) :=
  Submodule.mul_le.mpr fun _ ha _ hb ↦ mul_mem_weightSpace ha hb

/-- The weight spaces give a graded algebra, with multiplicative characters written additively
for the direct sum. -/
noncomputable instance weightSpaceGradedAlgebra [DecidableEq G] :
    GradedAlgebra (fun g : Additive G ↦ W g.toMul) where
  one_mem := one_mem_weightSpace
  mul_mem _ _ _ _ := mul_mem_weightSpace
  toDecomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    -- The internal direct sum uses classical decidability; this grading uses the supplied instance.
    change DirectSum.IsInternal W
    convert isInternal_weightSpace R G A

/-- The component of the graded decomposition is the comodule weight projection. -/
@[simp]
theorem coe_decompose_weightSpace [DecidableEq G] (a : A) (g : Additive G) :
    (DirectSum.decompose (fun i : Additive G ↦ W i.toMul) a g : A) =
      weightProj R G A g.toMul a := by
  let S (i : Additive G) := W i.toMul
  suffices (S g).subtype ∘ₗ DirectSum.component R (Additive G) (fun i ↦ S i) g ∘ₗ
      (DirectSum.decomposeLinearEquiv S).toLinearMap = weightProj R G A g.toMul from
    LinearMap.congr_fun this a
  apply DirectSum.decompose_lhom_ext S
  intro i
  ext x
  by_cases hi : i = g
  · subst i
    simp [S, weightProj_of_mem x.property]
  · have hne : g.toMul ≠ i.toMul := fun e ↦ hi (congrArg Additive.ofMul e.symm)
    simp [DirectSum.component.of, hi, weightProj_of_mem_of_ne hne x.property]

end Monoid

section StrongGrading

variable {R G A : Type*} [CommSemiring R] [Group G] [Semiring A] [Algebra R A]
  [ComoduleAlgebra R (MonoidAlgebra R G) A]

local notation "W" => weightSpace R G A
local notation "P" => weightProj R G A

/-- Right multiplication by a homogeneous element of weight `h` shifts weight projections by
right multiplication by `h` on the character group. -/
theorem weightProj_mul_right_of_mem_weightSpace {h : G} {b : A} (hb : b ∈ W h)
    (g : G) (a : A) : P (g * h) (a * b) = P g a * b := by
  classical
  simpa only [coe_decompose_weightSpace, toMul_add, toMul_ofMul] using
    (DirectSum.coe_decompose_mul_add_of_right_mem (fun i : Additive G ↦ W i.toMul)
      (i := Additive.ofMul g) (j := Additive.ofMul h) (a := a) hb)

/-- If opposite weight submodules multiply to the scalar submodule, multiplication is strong:
the product spans the entire submodule of the product weight. -/
theorem weightSpace_mul_eq (g h : G) (hInv : W h⁻¹ * W h = 1) : W g * W h = W (g * h) := by
  refine le_antisymm (weightSpace_mul_le g h) ?_
  calc
    W (g * h) = W (g * h) * (W h⁻¹ * W h) := by rw [hInv, mul_one]
    _ = (W (g * h) * W h⁻¹) * W h := by rw [mul_assoc]
    _ ≤ W g * W h := by
      gcongr
      simpa [mul_assoc] using (weightSpace_mul_le (R := R) (A := A) (g * h) h⁻¹)

/-- In a strong grading the weights form a homomorphism to the group of invertible submodules
of the coordinate algebra. -/
noncomputable def weightSpaceUnits (hInv : ∀ g : G, W g⁻¹ * W g = 1) :
    G →* (Submodule R A)ˣ :=
  MonoidHom.mk' (fun g ↦ ⟨W g, W g⁻¹, by simpa only [inv_inv] using hInv g⁻¹, hInv g⟩)
    fun g h ↦ Units.ext (weightSpace_mul_eq g h (hInv h)).symm

variable (hInv : ∀ g : G, weightSpace R G A g⁻¹ * weightSpace R G A g = 1)

/-- The underlying submodule attached to a character is its original weight submodule. -/
@[simp]
theorem coe_weightSpaceUnits (g : G) : (weightSpaceUnits hInv g : Submodule R A) = W g :=
  (rfl)

/-- The inverse character unit has the opposite weight as its underlying submodule. -/
@[simp]
theorem coe_inv_weightSpaceUnits (g : G) :
    (((weightSpaceUnits hInv g)⁻¹ : (Submodule R A)ˣ) : Submodule R A) = W g⁻¹ := by
  rfl

end StrongGrading

section Group

variable {R G A : Type*} [CommSemiring R] [Group G] [CommSemiring A] [Algebra R A]
  [ComoduleAlgebra R (MonoidAlgebra R G) A]

local notation "W" => weightSpace R G A
local notation "P" => weightProj R G A

/-- Surjectivity of the Galois map forces a finite sum of products of opposite-weight elements
to be equal to one. -/
theorem one_mem_weightSpace_inv_mul_of_surjective_galoisMap
    (hsurj : Function.Surjective (galoisMap R
      (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r)))
    (g : G) : (1 : A) ∈ W g⁻¹ * W g := by
  let β := galoisMap R (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r)
  let coeff : A ⊗[R] MonoidAlgebra R G →ₗ[A] A :=
    ((Algebra.linearMap R A).comp (monoidCoeff R G g)).liftBaseChange A
  have h (t : A ⊗[R] A) : P 1 (coeff (β t)) ∈ W g⁻¹ * W g := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hcoeff : coeff (β (a ⊗ₜ[R] b)) = a * P g b := by
        have hone : β ((1 : A) ⊗ₜ[R] b) = coact (R := R) (C := MonoidAlgebra R G) b := by
          rw [galoisMap_tmul, ← Algebra.TensorProduct.one_def, one_mul]
        calc
          coeff (β (a ⊗ₜ[R] b)) = a * coeff (coact (R := R) (C := MonoidAlgebra R G) b) := by
            rw [TensorProduct.tmul_eq_smul_one_tmul]
            simp only [map_smul, hone, smul_eq_mul]
          _ = a * P g b := by
            rw [weightProj_apply, LinearMap.tensorComponent_eq_liftBaseChange]
      rw [hcoeff]
      have hb := weightProj_mem_weightSpace (R := R) (G := G) g b
      have he := weightProj_mul_right_of_mem_weightSpace hb g⁻¹ a
      rw [inv_mul_cancel] at he
      rw [he]
      exact Submodule.mul_mem_mul (weightProj_mem_weightSpace g⁻¹ a) hb
    | add x y hx hy => simpa only [map_add] using (W g⁻¹ * W g).add_mem hx hy
  obtain ⟨t, ht⟩ := hsurj ((1 : A) ⊗ₜ[R] MonoidAlgebra.single g (1 : R))
  have ht' : coeff (β t) = 1 := by
    rw [ht, ← LinearMap.tensorComponent_eq_liftBaseChange]
    simp
  simpa only [ht', weightProj_of_mem (one_mem_weightSpace (G := G))] using h t

/-- If the trivial weight is the image of the base and the Galois map is surjective, each
weight submodule and its opposite multiply to the trivial weight. -/
theorem weightSpace_inv_mul_eq_one_of_surjective_galoisMap (h₁ : W 1 = 1)
    (hsurj : Function.Surjective (galoisMap R
      (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r)))
    (g : G) : W g⁻¹ * W g = 1 := by
  refine le_antisymm ?_ (Submodule.one_le.mpr
    (one_mem_weightSpace_inv_mul_of_surjective_galoisMap hsurj g))
  simpa only [inv_mul_cancel, h₁] using (weightSpace_mul_le (R := R) (A := A) g⁻¹ g)

variable [FaithfulSMul R A]

/-- A weight space whose product with its opposite is the scalar submodule is an invertible
module over the base. -/
theorem invertible_weightSpace (g : G) (h : W g⁻¹ * W g = 1) : Module.Invertible R (W g) :=
  -- The inverse of the constructed unit has underlying submodule definitionally equal to `W g`.
  inferInstanceAs (Module.Invertible R ↥(↑((Units.mkOfMulEqOne (W g⁻¹) (W g) h)⁻¹) :
    Submodule R A))

/-- Multiplication identifies the tensor product of two character lines with the character line
of the product weight. -/
noncomputable def weightSpaceMulEquiv (hInv : ∀ g : G, W g⁻¹ * W g = 1) (g h : G) :
    W g ⊗[R] W h ≃ₗ[R] W (g * h) :=
  (Submodule.tensorEquivMul (weightSpaceUnits hInv g) (weightSpaceUnits hInv h)).trans
    (LinearEquiv.ofEq _ _ (weightSpace_mul_eq g h (hInv h)))

/-- The multiplication equivalence takes pure tensors to the product in the coordinate ring. -/
@[simp]
theorem coe_weightSpaceMulEquiv_tmul (hInv : ∀ g : G, W g⁻¹ * W g = 1) {g h : G}
    (a : W g) (b : W h) :
    (weightSpaceMulEquiv hInv g h (a ⊗ₜ[R] b) : A) = (a : A) * (b : A) :=
  -- Mathlib constructs `tensorEquivMul` with `Submodule.mulMap'` as its forward map.
  (rfl)

/-- Multiplication trivializes a character line over the coordinate algebra itself. -/
noncomputable def weightSpaceBaseChangeEquiv (g : G) (h : W g⁻¹ * W g = 1) :
    A ⊗[R] W g ≃ₗ[A] A := by
  let := invertible_weightSpace g h
  let m := (W g).subtype.liftBaseChange A
  refine LinearEquiv.ofBijective m (Module.Invertible.bijective_of_surjective ?_)
  let e := (Submodule.topEquiv (R := R) (M := A)).rTensor (W g)
  have hm : (m.restrictScalars R).comp e.toLinearMap = Submodule.mulMap ⊤ (W g) :=
    TensorProduct.ext' fun a b ↦ by simp [m, e]
  have hs : Function.Surjective (Submodule.mulMap (⊤ : Submodule R A) (W g)) := by
    rw [← LinearMap.range_eq_top, Submodule.mulMap_range]
    exact Submodule.top_mul_eq_top_of_mul_eq_one h
  have hcomp : Function.Surjective (m ∘ e) := by
    rw [← hm] at hs
    simpa only [LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_toLinearMap] using hs
  exact hcomp.of_comp

/-- The trivialization is multiplication on pure tensors. -/
@[simp]
theorem weightSpaceBaseChangeEquiv_tmul (g : G) (h : W g⁻¹ * W g = 1) (a : A) (b : W g) :
    weightSpaceBaseChangeEquiv g h (a ⊗ₜ[R] b) = a * (b : A) := by
  simp [weightSpaceBaseChangeEquiv]

/-- If opposite weight spaces in a faithful algebra multiply to the scalar submodule, the Galois
map is bijective. -/
theorem bijective_galoisMap_of_weightSpace_inv_mul_eq_one
    (hInv : ∀ g : G, W g⁻¹ * W g = 1) :
    Function.Bijective (galoisMap R
      (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r)) := by
  classical
  let β := galoisMap R (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r)
  let fromWeights := LinearEquiv.ofBijective (DirectSum.coeLinearMap W)
    (isInternal_weightSpace R G A)
  let d := TensorProduct.directSumRight R R A (fun g ↦ ↥(W g))
  let e := d.symm.trans (fromWeights.lTensor A)
  let f := (tensorCoeffEquiv R G A).trans (finsuppLEquivDirectSum R A G)
  let m (g : G) := (weightSpaceBaseChangeEquiv g (hInv g)).restrictScalars R
  have h : f.toLinearMap ∘ₗ (β.toLinearMap.restrictScalars R) ∘ₗ e.toLinearMap =
      (DirectSum.congrLinearEquiv m).toLinearMap := by
    apply DirectSum.linearMap_ext R
    intro g
    apply TensorProduct.ext'
    intro a b
    have he : e (DirectSum.lof R G _ g (a ⊗ₜ[R] b)) = a ⊗ₜ[R] (b : A) := by
      simp only [e, d, LinearEquiv.trans_apply, TensorProduct.directSumRight_symm_lof_tmul,
        LinearEquiv.lTensor_tmul]
      congr 1
      exact DirectSum.coeLinearMap_lof W g b
    have hβ : β (a ⊗ₜ[R] (b : A)) =
        (a * (b : A)) ⊗ₜ[R] MonoidAlgebra.single g (1 : R) := by
      rw [galoisMap_tmul, mem_weightSpace.mp b.property, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
    have hf (x : A) : tensorCoeffEquiv R G A (x ⊗ₜ[R] MonoidAlgebra.single g (1 : R)) =
        Finsupp.single g x := by
      rw [← tensorCoeffEquiv_symm_single, LinearEquiv.apply_symm_apply]
    simp [he, hβ, hf, f, m, DirectSum.congrLinearEquiv_toLinearMap]
  have hfun : f ∘ β ∘ e = ⇑(DirectSum.congrLinearEquiv m) := by
    simpa only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_toLinearMap,
      AlgHom.coe_toLinearMap] using congrArg DFunLike.coe h
  have hb : Function.Bijective (f ∘ β ∘ e) :=
    hfun ▸ (DirectSum.congrLinearEquiv m).bijective
  exact (f.bijective.of_comp_iff' β).1 ((Function.Bijective.of_comp_iff (f ∘ β) e.bijective).1 hb)

end Group

section Torsor

variable {R G A : Type*} [CommRing R] [Group G] [CommRing A] [Algebra R A]
  [ComoduleAlgebra R (MonoidAlgebra R G) A]

local notation "W" => weightSpace R G A

/-- On a faithfully flat comodule algebra with injective Galois map, the trivial weight
submodule is the image of the base ring. -/
theorem weightSpace_one_eq_one_of_injective_galoisMap [Module.FaithfullyFlat R A]
    (hinj : Function.Injective (galoisMap R
      (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r))) : W 1 = 1 := by
  rw [weightSpace_one_eq_coinvariants, coinvariants_eq_range _ hinj]
  ext a
  simp [Submodule.mem_one]

/-- If opposite weight spaces in a faithful algebra multiply to the scalar submodule, the
coordinate algebra is faithfully flat. -/
theorem faithfullyFlat_of_weightSpace_inv_mul_eq_one [FaithfulSMul R A]
    (hInv : ∀ g : G, W g⁻¹ * W g = 1) : Module.FaithfullyFlat R A := by
  classical
  let fromWeights := LinearEquiv.ofBijective (DirectSum.coeLinearMap W)
    (isInternal_weightSpace R G A)
  let (g : G) := invertible_weightSpace g (hInv g)
  let (g : G) : Module.Flat R (W g) := inferInstance
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_faithful]
  refine ⟨Module.Flat.of_linearEquiv fromWeights.symm, fun N _ _ hN ↦ ?_⟩
  have h₁ : W (1 : G) = 1 := by
    simpa only [coe_weightSpaceUnits, Units.val_one] using
      congrArg Units.val (map_one (weightSpaceUnits hInv))
  let base : W (1 : G) ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (h₁.trans Submodule.one_eq_range)).trans
      (LinearEquiv.ofInjective (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm
  let : Nontrivial (W (1 : G) ⊗[R] N) :=
    ((base.rTensor N).trans (TensorProduct.lid R N)).toEquiv.nontrivial
  let : Nontrivial (DirectSum G fun g ↦ W g ⊗[R] N) :=
    (DirectSum.of_injective (β := fun g ↦ W g ⊗[R] N) (1 : G)).nontrivial
  exact ((fromWeights.symm.rTensor N).trans
    (TensorProduct.directSumLeft R R (fun g ↦ ↥(W g)) N)).toEquiv.nontrivial

/-- The affine diagonalizable torsor condition is equivalent to a strong character grading whose
trivial part is identified with the base ring by the algebra map. -/
theorem faithfullyFlat_and_bijective_galoisMap_iff :
    (Module.FaithfullyFlat R A ∧ Function.Bijective (galoisMap R
      (fun r ↦ (coinvariants R (MonoidAlgebra R G) A).algebraMap_mem r))) ↔
      Function.Injective (algebraMap R A) ∧ ∀ g : G, W g⁻¹ * W g = 1 := by
  constructor
  · rintro ⟨hFlat, hβ⟩
    let := hFlat
    have h₁ := weightSpace_one_eq_one_of_injective_galoisMap hβ.injective
    exact ⟨FaithfulSMul.algebraMap_injective R A,
      weightSpace_inv_mul_eq_one_of_surjective_galoisMap h₁ hβ.surjective⟩
  · rintro ⟨hinj, hInv⟩
    let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
    exact ⟨faithfullyFlat_of_weightSpace_inv_mul_eq_one hInv,
      bijective_galoisMap_of_weightSpace_inv_mul_eq_one hInv⟩

end Torsor

end TauCeti.ComoduleAlgebra
