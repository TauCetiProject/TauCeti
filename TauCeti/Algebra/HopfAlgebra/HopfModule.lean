/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The coinvariant projection of a Hopf module

A right Hopf module over a Hopf algebra `H` is a right `H`-comodule `M` with a right
`H`-action `m · h` such that `ρ(m · h) = Σ m₀ · h₁ ⊗ m₁ h₂`. Here the action is a bilinear
map `act : M →ₗ[R] H →ₗ[R] M`, written `act m h = m · h`, and the compatibility is stated with
`TensorProduct.tensorTensorTensorComm`.

The coinvariant projection is `P(m) = Σ m₀ · S(m₁)`. It is defined for any bilinear map
`act` and any right comodule. Compatibility alone makes `P(m)` coinvariant, that is,
`ρ(P m) = P m ⊗ 1`; the unit law makes `P` fix coinvariants, so `P` is a projection onto
them, and the action laws alone give the reconstruction formula `Σ P(m₀) · m₁ = m`.
Together they show that a nonzero Hopf module has a nonzero coinvariant vector. This is the
step of the fundamental theorem of Hopf modules used to show that a finite projective Hopf
algebra has nonzero cointegrals.

## Main declarations

* `TauCeti.Comodule.coinvariantProj`: the projection `m ↦ Σ m₀ · S(m₁)`.
* `TauCeti.Comodule.coact_coinvariantProj`: its values are coinvariant.
* `TauCeti.Comodule.coinvariantProj_eq_self`, `TauCeti.Comodule.isIdempotentElem_coinvariantProj`:
  it fixes coinvariants, so it is a projection onto them.
* `TauCeti.Comodule.lift_rTensor_coinvariantProj_coact`: the reconstruction formula.
* `TauCeti.Comodule.fixedSubcomodule_ne_bot_of_hopfModule`: a nonzero Hopf module has
  nonzero coinvariants.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf
  algebras*, Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §1.9.
-/

public section

open TensorProduct Coalgebra HopfAlgebra
open scoped Coalgebra

namespace TauCeti.Comodule

variable {R H M : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]

noncomputable section

/-- The coinvariant projection `m ↦ Σ m₀ · S(m₁)` of a right comodule with a bilinear right
action `act m h = m · h` of `H`. -/
def coinvariantProj (act : M →ₗ[R] H →ₗ[R] M) : M →ₗ[R] M :=
  TensorProduct.lift (act.compl₂ (antipode R)) ∘ₗ coact

/-- The coinvariant projection sends `m` to `Σ m₀ · S(m₁)`. -/
theorem coinvariantProj_apply (act : M →ₗ[R] H →ₗ[R] M) (m : M) :
    coinvariantProj act m = TensorProduct.lift (act.compl₂ (antipode R)) (coact m) := (rfl)

/-- The reconstruction formula `Σ P(m₀) · m₁ = m` for a right action of `H`. -/
theorem lift_rTensor_coinvariantProj_coact (act : M →ₗ[R] H →ₗ[R] M)
    (one : ∀ m, act m 1 = m) (mul : ∀ m a b, act (act m a) b = act m (a * b)) (m : M) :
    TensorProduct.lift act ((coinvariantProj act).rTensor H (coact (R := R) m)) = m := by
  have key (y : (M ⊗[R] H) ⊗[R] H) :
      TensorProduct.lift act ((TensorProduct.lift (act.compl₂ (antipode R))).rTensor H y) =
        TensorProduct.lift act ((LinearMap.mul' R H ∘ₗ (antipode R).rTensor H).lTensor M
          (TensorProduct.assoc R M H H y)) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul x b =>
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
      | tmul m a => simp [mul]
  rw [coinvariantProj, LinearMap.rTensor_comp_apply, key, coassoc_apply,
    ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul,
    LinearMap.lTensor_comp_apply, lTensor_counit_coact]
  simp [one]

/-- After comultiplying the coefficient, the map `m ⊗ (a ⊗ b) ↦ Σ m · S(b₂) ⊗ a S(b₁)`. -/
private def coinvariantAux (act : M →ₗ[R] H →ₗ[R] M) : M ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] H :=
  TensorProduct.map (TensorProduct.lift act) (LinearMap.mul' R H) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M H H H).toLinearMap ∘ₗ
      (comul ∘ₗ antipode R).lTensor (M ⊗[R] H) ∘ₗ
        (TensorProduct.assoc R M H H).symm.toLinearMap

omit [Comodule R H M] in
/-- On a comultiplied coefficient, `Σ m · S(c₂₂) ⊗ c₁ S(c₂₁) = m · S(c) ⊗ 1`. -/
private theorem coinvariantAux_tmul_comul (act : M →ₗ[R] H →ₗ[R] M) (x : M) (c : H) :
    coinvariantAux act (x ⊗ₜ comul c) = act x (antipode R c) ⊗ₜ 1 := by
  let r := ℛ R c
  -- `T (a ⊗ (b ⊗ d)) = x · S(d) ⊗ a S(b)`; coassociativity moves the double coproduct
  -- from the right leg of `Δ c` to its left leg, where the antipode axiom applies.
  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] H :=
    (TensorProduct.comm R H M).toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.mul' R H ∘ₗ (antipode R).lTensor H)
        (act x ∘ₗ antipode R) ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap
  have h1 : coinvariantAux act (x ⊗ₜ comul c) =
      ∑ i ∈ r.index, ∑ j ∈ (ℛ R (r.right i)).index,
        T (r.left i ⊗ₜ ((ℛ R (r.right i)).left j ⊗ₜ (ℛ R (r.right i)).right j)) := by
    rw [← r.eq]
    simp only [TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [coinvariantAux, T, ← (ℛ R (r.right i)).eq, TensorProduct.tmul_sum, map_sum]
  have h2 := congrArg T
    (Coalgebra.sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
  simp only [map_sum] at h2
  rw [h1, ← h2]
  simp only [T, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, TensorProduct.comm_tmul]
  simp_rw [← TensorProduct.tmul_sum, HopfAlgebra.sum_mul_antipode_eq_smul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [← TensorProduct.sum_tmul]
  simp_rw [← map_smul, ← map_sum, Coalgebra.sum_counit_smul]

/-- For a Hopf-module action, the coinvariant projection lands in the coinvariants:
`ρ(P m) = P m ⊗ 1`. -/
theorem coact_coinvariantProj (act : M →ₗ[R] H →ₗ[R] M)
    (hcoact : ∀ m h, coact (R := R) (act m h) = TensorProduct.map (TensorProduct.lift act)
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R M H H H
        (coact m ⊗ₜ comul h))) (m : M) :
    coact (R := R) (coinvariantProj act m) = coinvariantProj act m ⊗ₜ[R] (1 : H) := by
  have hlift (x : M ⊗[R] H) : coact (R := R) (TensorProduct.lift (act.compl₂ (antipode R)) x) =
      TensorProduct.map (TensorProduct.lift act) (LinearMap.mul' R H)
        (TensorProduct.tensorTensorTensorComm R M H H H
          (TensorProduct.map coact (comul ∘ₗ antipode R) x)) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c => simp [hcoact]
  have haux : coinvariantAux act ∘ₗ (comul (R := R) (A := H)).lTensor M =
      (TensorProduct.mk R M H).flip 1 ∘ₗ TensorProduct.lift (act.compl₂ (antipode R)) :=
    TensorProduct.ext' fun x c => by simpa using coinvariantAux_tmul_comul act x c
  have hcoassoc : coact (R := R) (coinvariantProj act m) =
      coinvariantAux act ((comul (R := R) (A := H)).lTensor M (coact m)) := by
    rw [coinvariantProj_apply, hlift, ← coassoc_apply, coinvariantAux]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, ← LinearMap.lTensor_comp_rTensor]
  rw [hcoassoc, ← LinearMap.comp_apply, haux]
  simp [coinvariantProj_apply]

/-- For a Hopf-module action, the coinvariant projection lands in the fixed subcomodule. -/
theorem coinvariantProj_mem_fixedSubcomodule (act : M →ₗ[R] H →ₗ[R] M)
    (hcoact : ∀ m h, coact (R := R) (act m h) = TensorProduct.map (TensorProduct.lift act)
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R M H H H
        (coact m ⊗ₜ comul h))) (m : M) :
    coinvariantProj act m ∈ fixedSubcomodule R H M :=
  mem_fixedSubcomodule.mpr (coact_coinvariantProj act hcoact m)

/-- Under the unit law, the coinvariant projection fixes every coinvariant vector. -/
@[simp]
theorem coinvariantProj_eq_self (act : M →ₗ[R] H →ₗ[R] M) (one : ∀ m, act m 1 = m) {m : M}
    (hm : m ∈ fixedSubcomodule R H M) : coinvariantProj act m = m := by
  rw [coinvariantProj_apply, mem_fixedSubcomodule.mp hm]
  simp [one]

/-- For a unital Hopf-module action, the coinvariant projection is idempotent. -/
theorem coinvariantProj_coinvariantProj (act : M →ₗ[R] H →ₗ[R] M) (one : ∀ m, act m 1 = m)
    (hcoact : ∀ m h, coact (R := R) (act m h) = TensorProduct.map (TensorProduct.lift act)
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R M H H H
        (coact m ⊗ₜ comul h))) (m : M) :
    coinvariantProj act (coinvariantProj act m) = coinvariantProj act m :=
  coinvariantProj_eq_self act one (coinvariantProj_mem_fixedSubcomodule act hcoact m)

/-- For a unital Hopf-module action, the coinvariant projection is an idempotent endomorphism. -/
theorem isIdempotentElem_coinvariantProj (act : M →ₗ[R] H →ₗ[R] M) (one : ∀ m, act m 1 = m)
    (hcoact : ∀ m h, coact (R := R) (act m h) = TensorProduct.map (TensorProduct.lift act)
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R M H H H
        (coact m ⊗ₜ comul h))) :
    IsIdempotentElem (coinvariantProj act) :=
  LinearMap.ext (coinvariantProj_coinvariantProj act one hcoact)

/-- A nonzero right Hopf module has a nonzero coinvariant vector. -/
theorem fixedSubcomodule_ne_bot_of_hopfModule [Nontrivial M] (act : M →ₗ[R] H →ₗ[R] M)
    (one : ∀ m, act m 1 = m) (mul : ∀ m a b, act (act m a) b = act m (a * b))
    (hcoact : ∀ m h, coact (R := R) (act m h) = TensorProduct.map (TensorProduct.lift act)
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R M H H H
        (coact m ⊗ₜ comul h))) :
    fixedSubcomodule R H M ≠ ⊥ := by
  intro hbot
  have hP : coinvariantProj act = 0 := LinearMap.ext fun m => by
    simpa [hbot] using coinvariantProj_mem_fixedSubcomodule act hcoact m
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  apply hm
  rw [← lift_rTensor_coinvariantProj_coact act one mul m, hP]
  simp

end

end TauCeti.Comodule
