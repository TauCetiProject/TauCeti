/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.Basic
public import TauCeti.RepresentationTheory.Continuous.TopRep.KernelCokernel

/-!
# The root contraction `μₙ ⊗ μₙ → μₙ` and its dependence on the root

Two Kummer classes cup naturally into `H²(G_F, μₙ ⊗ μₙ)`. A primitive `n`th root of unity
`ζ ∈ F` selects the coefficient pairing `kummerCupPairing ζ hζ : μₙ × μₙ → μₙ`; this file
constructs the linear map through which it factors, the **root contraction**

```text
c_ζ : μₙ ⊗_{ℤ/n} μₙ → μₙ,   ζ^i ⊗ ζ^j ↦ ζ^(i j).
```

It is the tensor lift of the pairing (`kummerContraction_tmul`), and it is the map
`x ⊗ y ↦ e_ζ(y) • x`, that is `id ⊗ e_ζ` followed by the scalar unitor, where `e_ζ : μₙ ≃ ℤ/n` is
the chosen-root coordinate `muNRepEquivZMod ζ hζ` (`kummerContraction_eq_rid_comp_map`); in
particular it is a linear equivalence (`kummerContractionEquiv`). It is equivariant for the
diagonal Galois action (`kummerContraction_map_ρ`). It is not multiplication of roots: on the
generator `g = ζ` it sends `(i • g) ⊗ (j • g)` to `(i j) • g`, written additively.

The contraction depends on `ζ`. If `ζ ^ k` is another primitive root, then the chosen-root
coordinate of `ζ` is `k` times that of `ζ ^ k` (`muNRepEquivZMod_eq_mul_muNRepEquivZMod_pow`), and

```text
k • c_(ζ^k) = c_ζ,   k • β_(ζ^k)(a, b) = β_ζ(a, b),
```

where `β_ζ(a, b) = kummerBrauerClass ζ hζ a b` is the Brauer class of the cup of the Kummer
classes of `a` and `b` along `kummerCupPairing ζ hζ`. Thus for a unit `u` of `ℤ/n` represented by
`k`, the contraction and the Brauer symbol of `ζ ^ k` are `u⁻¹` times those of `ζ`
(`kummerContraction_pow_eq_inv_smul`, `kummerBrauerClass_pow_eq_nsmul`). For example, at `n = 5`
the contraction of `ζ ^ 2` is `3` times that of `ζ`.

## Main definitions

* `TauCeti.ClassFieldTheory.kummerContraction`: the root contraction `μₙ ⊗ μₙ → μₙ` of a
  primitive root `ζ`, the tensor lift of `kummerCupPairing ζ hζ`.
* `TauCeti.ClassFieldTheory.kummerContractionEquiv`: the root contraction as a linear
  equivalence `μₙ ⊗ μₙ ≃ μₙ`.

## Main results

* `TauCeti.ClassFieldTheory.kummerContraction_tmul`: the value on a pure tensor is the pairing.
* `TauCeti.ClassFieldTheory.kummerContraction_smul_tmul_smul`: `(i • ζ) ⊗ (j • ζ) ↦ (i j) • ζ`.
* `TauCeti.ClassFieldTheory.kummerContraction_map_ρ`: equivariance for the diagonal action.
* `TauCeti.ClassFieldTheory.eq_kummerContraction`,
  `TauCeti.ClassFieldTheory.eq_kummerContraction_of_apply_generator_tmul`: uniqueness, from the
  values on pure tensors or from the single value `ζ ⊗ ζ ↦ ζ`.
* `TauCeti.ClassFieldTheory.kummerContraction_eq_rid_comp_map`: `c_ζ = rid ∘ (id ⊗ e_ζ)`.
* `TauCeti.ClassFieldTheory.natCast_smul_kummerContraction_pow`,
  `TauCeti.ClassFieldTheory.kummerContraction_pow_eq_inv_smul`: the root-change formula for the
  contraction.
* `TauCeti.ClassFieldTheory.nsmul_kummerBrauerClass_pow`,
  `TauCeti.ClassFieldTheory.kummerBrauerClass_pow_eq_nsmul`: the root-change formula for the
  Kummer-cup Brauer class.

## References

* C. A. Weibel, *The K-book*, Graduate Studies in Mathematics 145, AMS (2013), Chapter III,
  6.10–6.10.3, for the identification `μₙ ⊗ μₙ ≅ μₙ` selected by a primitive root.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Step 4, for the coefficient pairing of a
  primitive root.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology
open scoped TensorProduct

universe u

variable {n : ℕ} {F : Type u} [Field F]

/-! ### The root contraction -/

section Contraction

variable [NeZero n] (ζ : F) (hζ : IsPrimitiveRoot ζ n)

/-- **The root contraction** `c_ζ : μₙ ⊗_{ℤ/n} μₙ → μₙ` of a primitive `n`th root of unity
`ζ ∈ F`, sending `ζ ^ i ⊗ ζ ^ j` to `ζ ^ (i j)`: the tensor lift of the coefficient pairing
`kummerCupPairing ζ hζ`. -/
def kummerContraction : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V →ₗ[ZMod n] (muNRep n F).V :=
  TensorProduct.lift (kummerCupPairing ζ hζ).bil

/-- **The root contraction on a pure tensor is the pairing of the root.** -/
@[simp]
theorem kummerContraction_tmul (x y : (muNRep n F).V) :
    kummerContraction ζ hζ (x ⊗ₜ y) = (kummerCupPairing ζ hζ).bil x y :=
  TensorProduct.lift.tmul x y

/-- The root contraction composed with the tensor product map is the pairing of the root. -/
theorem kummerContraction_compr₂_mk :
    (TensorProduct.mk (ZMod n) (muNRep n F).V (muNRep n F).V).compr₂ (kummerContraction ζ hζ) =
      (kummerCupPairing ζ hζ).bil :=
  LinearMap.ext₂ (kummerContraction_tmul ζ hζ)

/-- **The chosen-root coordinate of a contraction is the product of the coordinates.** -/
theorem muNRepEquivZMod_kummerContraction_tmul (x y : (muNRep n F).V) :
    muNRepEquivZMod ζ hζ (kummerContraction ζ hζ (x ⊗ₜ y)) =
      muNRepEquivZMod ζ hζ x * muNRepEquivZMod ζ hζ y := by
  rw [kummerContraction_tmul, kummerCupPairing_bil, ZMod.map_smul, smul_eq_mul]

/-- **The root contraction multiplies exponents**: written additively with the chosen generator
`g = ζ`, it sends `(i • g) ⊗ (j • g)` to `(i j) • g`. -/
theorem kummerContraction_smul_tmul_smul (i j : ZMod n) :
    kummerContraction ζ hζ
        ((i • muNRepGenerator ζ hζ) ⊗ₜ (j • muNRepGenerator ζ hζ)) =
      (i * j) • muNRepGenerator ζ hζ := by
  apply (muNRepEquivZMod ζ hζ).injective
  simp only [muNRepEquivZMod_kummerContraction_tmul, ZMod.map_smul, muNRepEquivZMod_generator,
    smul_eq_mul, mul_one]

/-- The root contraction sends `ζ ⊗ ζ` to `ζ`. -/
theorem kummerContraction_generator_tmul_generator :
    kummerContraction ζ hζ (muNRepGenerator ζ hζ ⊗ₜ muNRepGenerator ζ hζ) =
      muNRepGenerator ζ hζ := by
  simpa only [one_smul, mul_one] using kummerContraction_smul_tmul_smul ζ hζ 1 1

/-- **The root contraction on roots of unity**: if `x` and `y` represent the roots `ζ ^ i` and
`ζ ^ j` of `Fˢ`, then their contraction represents `ζ ^ (i j)`. -/
theorem coe_kummerCoeffEquivMuNRep_symm_kummerContraction_tmul {x y : (muNRep n F).V} {i j : ℤ}
    (hx : ((((kummerCoeffEquivMuNRep n F).symm x).toMul : (SeparableClosure F)ˣ) :
      SeparableClosure F) = algebraMap F (SeparableClosure F) ζ ^ i)
    (hy : ((((kummerCoeffEquivMuNRep n F).symm y).toMul : (SeparableClosure F)ˣ) :
      SeparableClosure F) = algebraMap F (SeparableClosure F) ζ ^ j) :
    ((((kummerCoeffEquivMuNRep n F).symm (kummerContraction ζ hζ (x ⊗ₜ y))).toMul :
        (SeparableClosure F)ˣ) : SeparableClosure F) =
      algebraMap F (SeparableClosure F) ζ ^ (i * j) := by
  rw [kummerContraction_tmul, kummerCupPairing_bil_apply ζ hζ hx,
    coe_kummerCoeffEquivMuNRep_symm_zsmul, hy, ← zpow_mul,
    mul_comm]

/-- **The root contraction is equivariant for the diagonal Galois action** on `μₙ ⊗ μₙ`. -/
theorem kummerContraction_map_ρ (g : Field.absoluteGaloisGroup F)
    (t : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V) :
    kummerContraction ζ hζ
        (TensorProduct.map ((muNRep n F).ρ g).toLinearMap ((muNRep n F).ρ g).toLinearMap t) =
      (muNRep n F).ρ g (kummerContraction ζ hζ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, kummerContraction_tmul,
      kummerContraction_tmul, (kummerCupPairing ζ hζ).equivariant]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **Uniqueness of the root contraction**: a linear map on `μₙ ⊗ μₙ` whose value on every pure
tensor is the pairing of the root is the root contraction. -/
theorem eq_kummerContraction
    {f : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V →ₗ[ZMod n] (muNRep n F).V}
    (hf : ∀ x y, f (x ⊗ₜ y) = (kummerCupPairing ζ hζ).bil x y) : f = kummerContraction ζ hζ :=
  TensorProduct.ext' fun x y ↦ by rw [hf, kummerContraction_tmul]

/-- Two linear maps out of `μₙ ⊗ μₙ` agreeing on `ζ ⊗ ζ` are equal: `μₙ ⊗ μₙ` is generated by
`ζ ⊗ ζ`. -/
theorem linearMap_ext_muNRepGenerator_tmul {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {f f' : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V →ₗ[ZMod n] M}
    (h : f (muNRepGenerator ζ hζ ⊗ₜ muNRepGenerator ζ hζ) =
      f' (muNRepGenerator ζ hζ ⊗ₜ muNRepGenerator ζ hζ)) : f = f' :=
  TensorProduct.ext' fun x y ↦ by
    rw [← muNRepEquivZMod_smul_generator hζ x, ← muNRepEquivZMod_smul_generator hζ y,
      TensorProduct.smul_tmul_smul, map_smul, map_smul, h]

/-- **Uniqueness of the root contraction from one value**: a linear map on `μₙ ⊗ μₙ` sending
`ζ ⊗ ζ` to `ζ` is the root contraction. -/
theorem eq_kummerContraction_of_apply_generator_tmul
    {f : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V →ₗ[ZMod n] (muNRep n F).V}
    (hf : f (muNRepGenerator ζ hζ ⊗ₜ muNRepGenerator ζ hζ) = muNRepGenerator ζ hζ) :
    f = kummerContraction ζ hζ :=
  linearMap_ext_muNRepGenerator_tmul ζ hζ (by rw [hf, kummerContraction_generator_tmul_generator])

/-- **The root contraction is `id ⊗ e_ζ` followed by the scalar unitor**, where
`e_ζ = muNRepEquivZMod ζ hζ` is the chosen-root coordinate `μₙ ≃ ℤ/n`. -/
theorem kummerContraction_eq_rid_comp_map :
    kummerContraction ζ hζ =
      (TensorProduct.rid (ZMod n) (muNRep n F).V).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id ((muNRepEquivZMod ζ hζ).toAddMonoidHom.toZModLinearMap n) :=
  (eq_kummerContraction_of_apply_generator_tmul ζ hζ (by simp)).symm

/-- **The root contraction as a linear equivalence** `μₙ ⊗_{ℤ/n} μₙ ≃ μₙ`: the tensor product of
the identity with the chosen-root coordinate `μₙ ≃ ℤ/n`, followed by the scalar unitor. Its
underlying linear map is `kummerContraction ζ hζ` (`kummerContractionEquiv_toLinearMap`). -/
def kummerContractionEquiv : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V ≃ₗ[ZMod n] (muNRep n F).V :=
  (TensorProduct.congr (LinearEquiv.refl (ZMod n) (muNRep n F).V)
    ((muNRepEquivZMod ζ hζ).toLinearEquiv (ZMod.map_smul _))).trans (TensorProduct.rid (ZMod n) _)

/-- The linear equivalence `kummerContractionEquiv ζ hζ` is the root contraction. -/
@[simp]
theorem kummerContractionEquiv_toLinearMap :
    (kummerContractionEquiv ζ hζ).toLinearMap = kummerContraction ζ hζ :=
  eq_kummerContraction_of_apply_generator_tmul ζ hζ (by
    simp only [kummerContractionEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, AddEquiv.coe_toLinearEquiv,
      muNRepEquivZMod_generator, TensorProduct.rid_tmul, one_smul])

/-- The linear equivalence `kummerContractionEquiv ζ hζ` acts as the root contraction. -/
@[simp]
theorem kummerContractionEquiv_apply (t : (muNRep n F).V ⊗[ZMod n] (muNRep n F).V) :
    kummerContractionEquiv ζ hζ t = kummerContraction ζ hζ t :=
  LinearMap.congr_fun (kummerContractionEquiv_toLinearMap ζ hζ) t

/-- The inverse of `kummerContractionEquiv ζ hζ` sends `x` to `x ⊗ ζ`. -/
@[simp]
theorem kummerContractionEquiv_symm_apply (x : (muNRep n F).V) :
    (kummerContractionEquiv ζ hζ).symm x = x ⊗ₜ muNRepGenerator ζ hζ := by
  rw [LinearEquiv.symm_apply_eq, kummerContractionEquiv_apply, kummerContraction_tmul,
    kummerCupPairing_bil, muNRepEquivZMod_smul_generator]

/-- The root contraction is bijective. -/
theorem kummerContraction_bijective : Function.Bijective (kummerContraction ζ hζ) := by
  rw [← kummerContractionEquiv_toLinearMap]
  exact (kummerContractionEquiv ζ hζ).bijective

end Contraction

/-! ### Changing the root -/

section RootChange

variable [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ} (hζk : IsPrimitiveRoot (ζ ^ k) n)

/-- **The pairing of a root under a change of root**: `k` times the pairing of `ζ ^ k` is the
pairing of `ζ`. -/
theorem nsmul_kummerCupPairing_pow_bil (x y : (muNRep n F).V) :
    k • (kummerCupPairing (ζ ^ k) hζk).bil x y = (kummerCupPairing ζ hζ).bil x y := by
  rw [kummerCupPairing_bil, kummerCupPairing_bil, muNRepEquivZMod_eq_mul_muNRepEquivZMod_pow hζ hζk,
    mul_smul, Nat.cast_smul_eq_nsmul]

/-- **The root contraction under a change of root**: `k` times the contraction of `ζ ^ k` is
the contraction of `ζ`. -/
theorem natCast_smul_kummerContraction_pow :
    (k : ZMod n) • kummerContraction (ζ ^ k) hζk = kummerContraction ζ hζ :=
  TensorProduct.ext' fun x y ↦ by
    rw [LinearMap.smul_apply, kummerContraction_tmul, kummerContraction_tmul,
      Nat.cast_smul_eq_nsmul, nsmul_kummerCupPairing_pow_bil hζ hζk]

/-- **The root contraction of `ζ ^ u` is `u⁻¹` times that of `ζ`**, for a unit `u` of `ℤ/n`
represented by `k`. -/
theorem kummerContraction_pow_eq_inv_smul (v : (ZMod n)ˣ) (hv : (k : ZMod n) = v) :
    kummerContraction (ζ ^ k) hζk = ((v⁻¹ : (ZMod n)ˣ) : ZMod n) • kummerContraction ζ hζ := by
  rw [← natCast_smul_kummerContraction_pow hζ hζk, hv, smul_smul, Units.inv_mul, one_smul]

/-- **The Kummer-cup Brauer class under a change of root**: `k` times the Brauer class of the
cup along the pairing of `ζ ^ k` is the Brauer class of the cup along the pairing of `ζ`. -/
theorem nsmul_kummerBrauerClass_pow (a b : Fˣ) :
    k • kummerBrauerClass (ζ ^ k) hζk a b = kummerBrauerClass ζ hζ a b := by
  have hn : IsUnit (n : F) := hζ.neZero'.out.isUnit
  -- Multiplication by `k` on `μₙ` intertwines the pairing of `ζ ^ k` with the pairing of `ζ`.
  have hcup := (kummerCupPairing (ζ ^ k) hζk).cup_coeffMap (kummerCupPairing ζ hζ)
    (𝟙 _) (𝟙 _) ((k : ZMod n) • 𝟙 (muNRep n F)) (fun x y ↦ by
      rw [CategoryTheory.id_apply, CategoryTheory.id_apply, TopRep.natCast_smul_id_apply,
        nsmul_kummerCupPairing_pow_bil hζ hζk]) 1 1 (kummerClass F hn a) (kummerClass F hn b)
  -- The functor `H²(G_F, ·)` is `ℤ/n`-linear, so it sends `(k : ℤ/n) • 𝟙` to `k • 𝟙`.
  have hk : TauCeti.ContinuousCohomology.coeffMap ((k : ZMod n) • 𝟙 (muNRep n F)) (1 + 1) =
      k • 𝟙 (continuousCohomology (1 + 1) (muNRep n F)) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ← TauCeti.ContinuousCohomology.coeffMap_id]
    exact (TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod n)
      (Field.absoluteGaloisGroup F) (1 + 1)).map_smul _ _
  rw [TauCeti.ContinuousCohomology.coeffMap_id, CategoryTheory.id_apply, CategoryTheory.id_apply,
    hk] at hcup
  simp only [TopModuleCat.hom_nsmul, smul_apply, TopModuleCat.hom_id,
    ContinuousLinearMap.id_apply] at hcup
  rw [kummerBrauerClass_def, kummerBrauerClass_def, ← map_nsmul, hcup]

/-- **The Kummer-cup Brauer class of `ζ ^ u` is `u⁻¹` times that of `ζ`**: if `l` is an inverse of
`k` modulo `n`, the Brauer class of the cup along the pairing of `ζ ^ k` is `l` times the Brauer
class of the cup along the pairing of `ζ`. -/
theorem kummerBrauerClass_pow_eq_nsmul {l : ℕ} (hkl : k * l ≡ 1 [MOD n]) (a b : Fˣ) :
    kummerBrauerClass (ζ ^ k) hζk a b = l • kummerBrauerClass ζ hζ a b := by
  rw [← nsmul_kummerBrauerClass_pow hζ hζk, smul_smul, mul_comm,
    nsmul_eq_nsmul_of_modEq hkl (nsmul_kummerBrauerClass_eq_zero (ζ ^ k) hζk a b), one_smul]

end RootChange

end TauCeti.ClassFieldTheory
