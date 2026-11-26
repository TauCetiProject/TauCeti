/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Iterated coproducts and conilpotent coalgebras

For a linear map `Δ : C ⟶ C ⊗ C`, thought of as the (reduced) coproduct of a noncounital
coalgebra, the `n`-fold iterated coproduct `Δ⁽ⁿ⁾ : C ⟶ C^{⊗(n + 1)}` is defined by repeatedly
cutting the left factor: `Δ⁽⁰⁾` is the identification of `C` with its first tensor power and
`Δ⁽ⁿ⁺¹⁾ = (Δ⁽ⁿ⁾ ⊗ 1) ∘ Δ`, with the output factors flattened by Mathlib's tensor-power
multiplication equivalence. The coproduct is *conilpotent* when every element is annihilated by
some iterated coproduct.

This is the finiteness condition under which the reduced tensor coalgebra `Tᶜ(N)` is cofree: for
a conilpotent coassociative `C`, a coalgebra map `C ⟶ Tᶜ(N)` is the same as a linear map
`C ⟶ N`, whose `(n + 1)`-st Taylor component is computed from `Δ⁽ⁿ⁾`. The coaugmentation coideal
of a coaugmented conilpotent coalgebra, such as the reduced bar construction, carries such a
coproduct; Tau Ceti's noncounital differential graded coalgebras
(`TauCeti.IsNonCounitalDGCoalgebra`) are stored by exactly this kind of map `Δ`.

Iterating on the left needs no coassociativity, and each iterated coproduct factors through the
previous one, so once an iterate vanishes on an element all later ones do
(`LinearMap.iteratedComul_eq_zero_of_le`). With coassociativity, the iterates can be split at any
position (`LinearMap.iteratedComul_succ_add`). Neither statement needs flatness, a field, or any
hypothesis on the characteristic.

## Main definitions

* `LinearMap.iteratedComul`: the `n`-fold iterated coproduct `C ⟶ C^{⊗(n + 1)}`.
* `LinearMap.IsConilpotent`: every element is annihilated by some iterated coproduct.

## Main results

* `LinearMap.iteratedComul_eq_zero_of_le`: the iterated coproducts vanishing on an element form an
  upper set.
* `LinearMap.iteratedComul_succ_add`: for a coassociative coproduct,
  `Δ⁽ⁱ⁺ʲ⁺¹⁾ = (Δ⁽ⁱ⁾ ⊗ Δ⁽ʲ⁾) ∘ Δ` up to flattening.
* `LinearMap.iteratedComul_comp`: iterated coproducts are natural along coalgebra maps.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Sections 1.2.4 and 1.2.6, for iterated coproducts and conilpotent
  coalgebras.
-/

public section

open scoped TensorProduct

universe uR uC uD

namespace LinearMap

variable {R : Type uR} {C : Type uC} {D : Type uD} [CommSemiring R] [AddCommMonoid C]
  [Module R C] [AddCommMonoid D] [Module R D]

/-- The `n`-fold iterated coproduct `Δ⁽ⁿ⁾ : C ⟶ C^{⊗(n + 1)}` of a coproduct `Δ : C ⟶ C ⊗ C`,
obtained by repeatedly cutting the left factor: `Δ⁽⁰⁾` identifies `C` with its first tensor power
and `Δ⁽ⁿ⁺¹⁾ = (Δ⁽ⁿ⁾ ⊗ 1) ∘ Δ`, with the output factors flattened by
`TensorPower.mulEquiv`. -/
noncomputable def iteratedComul (Δ : C →ₗ[R] C ⊗[R] C) :
    (n : ℕ) → C →ₗ[R] TensorPower R (n + 1) C
  | 0 => (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap
  | n + 1 => TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (iteratedComul Δ n) (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap ∘ₗ
        Δ

variable (Δ : C →ₗ[R] C ⊗[R] C)

/-- The zeroth iterated coproduct is the identification with the first tensor power. -/
@[simp]
theorem iteratedComul_zero :
    Δ.iteratedComul 0 = (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap := (rfl)

/-- Each further iterated coproduct cuts the left factor once more. -/
theorem iteratedComul_succ (n : ℕ) :
    Δ.iteratedComul (n + 1) = TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (Δ.iteratedComul n) (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap ∘ₗ
        Δ := (rfl)

/-- The first iterated coproduct is the coproduct, with its two output factors flattened. -/
theorem iteratedComul_one :
    Δ.iteratedComul 1 = TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap
        (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap ∘ₗ Δ := (rfl)

/-- Apply the coproduct to the first factor of a tensor power. -/
private noncomputable def comulFirst :
    (n : ℕ) → TensorPower R (n + 1) C →ₗ[R] TensorPower R (n + 2) C
  | 0 => Δ.iteratedComul 1 ∘ₗ (TauCeti.TensorPower.oneEquiv R C).toLinearMap
  | n + 1 => (TensorPower.mulEquiv (R := R) (M := C) (n := n + 2) (m := 1)).toLinearMap ∘ₗ
      (comulFirst n).rTensor (TensorPower R 1 C) ∘ₗ
        (TensorPower.mulEquiv (R := R) (M := C) (n := n + 1) (m := 1)).symm.toLinearMap

/-- Each iterated coproduct is the previous one followed by the coproduct of its first factor.
No coassociativity is needed, since both cut the left factor. -/
private theorem iteratedComul_succ_eq_comulFirst_comp (n : ℕ) :
    Δ.iteratedComul (n + 1) = comulFirst Δ n ∘ₗ Δ.iteratedComul n := by
  induction n with
  | zero =>
    rw [comulFirst, iteratedComul_zero, LinearMap.comp_assoc, LinearEquiv.comp_symm,
      LinearMap.comp_id]
  | succ n ih =>
    rw [comulFirst, iteratedComul_succ Δ (n + 1)]
    conv_lhs => rw [ih]
    rw [iteratedComul_succ Δ n]
    refine LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← LinearMap.comp_apply (LinearMap.rTensor _ _), LinearMap.rTensor_comp_map]

variable {Δ}

/-- Once an iterated coproduct vanishes on an element, so do all later ones. -/
theorem iteratedComul_eq_zero_of_le {c : C} {m n : ℕ} (hc : Δ.iteratedComul m c = 0)
    (hmn : m ≤ n) : Δ.iteratedComul n c = 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact hc
  | succ n _ ih =>
    rw [iteratedComul_succ_eq_comulFirst_comp, LinearMap.comp_apply, ih, map_zero]

variable (Δ)

/-- A coproduct `Δ : C ⟶ C ⊗ C` is **conilpotent** when every element of `C` is annihilated by
some iterated coproduct `Δ⁽ⁿ⁾`. -/
def IsConilpotent : Prop :=
  ∀ c : C, ∃ n, Δ.iteratedComul n c = 0

variable {Δ}

/-- The defining property of a conilpotent coproduct, as a reusable `Iff`. -/
theorem isConilpotent_iff : Δ.IsConilpotent ↔ ∀ c : C, ∃ n, Δ.iteratedComul n c = 0 :=
  Iff.rfl

/-- For a conilpotent coproduct, all sufficiently high iterated coproducts of an element
vanish. -/
theorem IsConilpotent.exists_forall_iteratedComul_eq_zero (hΔ : Δ.IsConilpotent) (c : C) :
    ∃ n, ∀ k, n ≤ k → Δ.iteratedComul k c = 0 := by
  obtain ⟨n, hn⟩ := hΔ c
  exact ⟨n, fun _ hk ↦ iteratedComul_eq_zero_of_le hn hk⟩

/-- **Generalized coassociativity.** For a coassociative coproduct, the iterated coproduct with
`i + j + 2` output factors is obtained by applying `Δ⁽ⁱ⁾` and `Δ⁽ʲ⁾` to the two factors of `Δ`
and flattening. -/
theorem iteratedComul_succ_add
    (hΔ : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ)
    (i j : ℕ) :
    Δ.iteratedComul (i + 1 + j) = TensorPower.mulEquiv.toLinearMap ∘ₗ
      TensorProduct.map (Δ.iteratedComul i) (Δ.iteratedComul j) ∘ₗ Δ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    -- The index `i + 1 + (j + 1)` is definitionally `i + 1 + j + 1`, so the left side unfolds
    -- by one more left cut.
    change Δ.iteratedComul (i + 1 + j + 1) = _
    set ι := (TauCeti.TensorPower.oneEquiv R C).symm.toLinearMap
    set I := Δ.iteratedComul i
    set J := Δ.iteratedComul j
    -- Flattening three blocks does not depend on how they are bracketed.
    have hassoc :
        (TensorPower.mulEquiv (R := R) (M := C) (n := i + 1 + (j + 1)) (m := 1)).toLinearMap ∘ₗ
          (TensorPower.mulEquiv (R := R) (M := C) (n := i + 1) (m := j + 1)).toLinearMap.rTensor _ =
        (TensorPower.mulEquiv (R := R) (M := C) (n := i + 1) (m := j + 1 + 1)).toLinearMap ∘ₗ
          (TensorPower.mulEquiv (R := R) (M := C) (n := j + 1) (m := 1)).toLinearMap.lTensor _ ∘ₗ
            (TensorProduct.assoc R _ _ _).toLinearMap := by
      refine TensorProduct.ext_threefold fun x y z ↦ ?_
      have hxyz := TensorPower.mul_assoc x y z
      rw [TensorPower.cast_refl, LinearEquiv.refl_apply] at hxyz
      simpa only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.assoc_tmul, ← TensorPower.gMul_def] using hxyz
    have hL : TensorProduct.map (TensorPower.mulEquiv.toLinearMap ∘ₗ TensorProduct.map I J ∘ₗ Δ) ι =
        TensorPower.mulEquiv.toLinearMap.rTensor _ ∘ₗ TensorProduct.map (TensorProduct.map I J) ι ∘ₗ
          Δ.rTensor C :=
      TensorProduct.ext' fun x y ↦ by simp
    have hR : TensorProduct.map I (TensorPower.mulEquiv.toLinearMap ∘ₗ TensorProduct.map J ι ∘ₗ Δ) =
        TensorPower.mulEquiv.toLinearMap.lTensor _ ∘ₗ TensorProduct.map I (TensorProduct.map J ι) ∘ₗ
          Δ.lTensor C :=
      TensorProduct.ext' fun x y ↦ by simp
    have hmap : (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
        TensorProduct.map (TensorProduct.map I J) ι ∘ₗ Δ.rTensor C ∘ₗ Δ =
          TensorProduct.map I (TensorProduct.map J ι) ∘ₗ Δ.lTensor C ∘ₗ Δ := by
      rw [← hΔ, ← LinearMap.comp_assoc, ← TensorProduct.map_map_comp_assoc_eq,
        LinearMap.comp_assoc]
    rw [iteratedComul_succ, iteratedComul_succ Δ j, ih, hL, hR]
    simp only [LinearMap.comp_assoc]
    rw [← hmap]
    simp only [← LinearMap.comp_assoc]
    rw [hassoc]
    simp only [LinearMap.comp_assoc]

/-- Iterated coproducts are natural along a coalgebra map: if `g : C ⟶ D` intertwines the
coproducts, then `Δ_D⁽ⁿ⁾ ∘ g = g^{⊗(n + 1)} ∘ Δ_C⁽ⁿ⁾`. -/
theorem iteratedComul_comp {Δ' : D →ₗ[R] D ⊗[R] D} {g : C →ₗ[R] D}
    (hg : Δ' ∘ₗ g = TensorProduct.map g g ∘ₗ Δ) (n : ℕ) :
    Δ'.iteratedComul n ∘ₗ g = PiTensorProduct.map (fun _ ↦ g) ∘ₗ Δ.iteratedComul n := by
  induction n with
  | zero => exact TauCeti.TensorPower.oneEquiv_symm_comp g
  | succ n ih =>
    rw [iteratedComul_succ, iteratedComul_succ, LinearMap.comp_assoc, LinearMap.comp_assoc, hg,
      ← LinearMap.comp_assoc _ (TensorProduct.map g g), ← TensorProduct.map_comp, ih,
      TauCeti.TensorPower.oneEquiv_symm_comp, TensorProduct.map_comp]
    simp only [← LinearMap.comp_assoc]
    rw [TauCeti.TensorPower.mulEquiv_comp_map_const]

end LinearMap
