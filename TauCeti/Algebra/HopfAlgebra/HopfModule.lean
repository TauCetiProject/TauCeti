/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Right Hopf modules and the fundamental theorem of Hopf modules

A right-right Hopf module over a bialgebra `H` is an `R`-module `M` carrying both a right
`H`-module structure (`Module Hᵐᵒᵖ M`, compatible with the base `R`-action) and a right
`H`-comodule structure (`TauCeti.Comodule R H M`) such that the right action map
`M ⊗[R] H →ₗ[R] M` is a right `H`-comodule morphism:

```text
ρ(m · h) = ∑ (m₀ · h₁) ⊗ (m₁ h₂).
```

When `H` is a Hopf algebra over an arbitrary commutative semiring `R`, the coinvariant projection
`P(m) = ∑ m₀ · S(m₁)` lands in the fixed subcomodule `Comodule.fixedSubcomodule R H M` and induces
a canonical `R`-linear isomorphism

```text
Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M,    v ⊗ h ↦ v · h,
```

which is also right `H`-linear and right `H`-colinear. This is the fundamental theorem of Hopf
modules (Sweedler's structure theorem).

## Main definitions

* `TauCeti.RightHopfModule.rightAct`: the right `H`-action bundled as an `R`-linear map
  `M ⊗[R] H →ₗ[R] M`.
* `TauCeti.RightHopfModule`: the compatibility axiom making `M` a right-right Hopf module over a
  bialgebra `H`.
* `TauCeti.RightHopfModule.instSelf`: the regular right Hopf module of a bialgebra over itself.
* `TauCeti.RightHopfModule.coinvariantProj`: the projection `m ↦ ∑ m₀ · S(m₁)` onto coinvariants.
* `TauCeti.RightHopfModule.coinvariantEquiv`: the fundamental isomorphism
  `Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M`.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Theorem 4.1.1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, AMS, 1993, Theorem 1.9.4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace RightHopfModule

section RightAct

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [Algebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]

variable (R H M) in
/-- The right `H`-action on `M`, bundled as an `R`-linear map `M ⊗[R] H →ₗ[R] M` sending
`m ⊗ₜ h` to `MulOpposite.op h • m`. -/
noncomputable def rightAct : M ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun m ↦
        { toFun := fun h ↦ MulOpposite.op h • m
          map_add' := fun h₁ h₂ ↦ by rw [MulOpposite.op_add, add_smul]
          map_smul' := fun r h ↦ by simp [smul_assoc] }
      map_add' := fun m₁ m₂ ↦ by
        ext h
        simp [smul_add]
      map_smul' := fun r m ↦ by
        ext h
        exact smul_comm (MulOpposite.op h) r m }

/-- On a pure tensor, `rightAct` evaluates the right action. -/
@[simp]
theorem rightAct_tmul (m : M) (h : H) :
    rightAct R H M (m ⊗ₜ[R] h) = MulOpposite.op h • m :=
  (rfl)

variable (R H M) in
/-- Associativity of the right action as an equality of linear maps on `M ⊗[R] H ⊗[R] H`. -/
theorem rightAct_comp_rTensor :
    rightAct R H M ∘ₗ (rightAct R H M).rTensor H =
      rightAct R H M ∘ₗ (LinearMap.mul' R H).lTensor M ∘ₗ
        (TensorProduct.assoc R M H H).toLinearMap := by
  apply TensorProduct.ext_threefold
  intro m h₁ h₂
  simp [← mul_smul]

end RightAct

end RightHopfModule

/-- A right-right Hopf module over a bialgebra `H`: a module with compatible right `H`-action
and right `H`-coaction satisfying `ρ(m · h) = ∑ (m₀ · h₁) ⊗ (m₁ h₂)`. -/
class RightHopfModule (R : Type u) (H : Type v) (M : Type w) [CommSemiring R] [Semiring H]
    [Bialgebra R H] [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
    [Comodule R H M] : Prop where
  /-- Compatibility between the right `H`-action and the right `H`-coaction. -/
  coact_op_smul (m : M) (h : H) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • m) =
      TensorProduct.map (RightHopfModule.rightAct R H M) (LinearMap.mul' R H)
        (TensorProduct.tensorTensorTensorComm R M H H H
          (Comodule.coact (R := R) (C := H) m ⊗ₜ[R] Coalgebra.comul (R := R) h))

namespace RightHopfModule

section Bialgebra

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
variable [Comodule R H M]

/-- The compatibility law of a right Hopf module on `rightAct (m ⊗ₜ h)`. -/
theorem coact_rightAct_tmul [RightHopfModule R H M] (m : M) (h : H) :
    Comodule.coact (R := R) (C := H) (rightAct R H M (m ⊗ₜ[R] h)) =
      TensorProduct.map (rightAct R H M) (LinearMap.mul' R H)
        (TensorProduct.tensorTensorTensorComm R M H H H
          (Comodule.coact (R := R) (C := H) m ⊗ₜ[R] Coalgebra.comul (R := R) h)) :=
  coact_op_smul m h

/-- On a coinvariant vector `v`, the coaction of `v · h` splits as `∑ (v · h₁) ⊗ h₂`. -/
theorem coact_op_smul_of_mem_fixedSubcomodule [RightHopfModule R H M] {v : M}
    (hv : v ∈ Comodule.fixedSubcomodule R H M) (h : H) :
    Comodule.coact (R := R) (C := H) (MulOpposite.op h • v) =
      ((rightAct R H M ∘ₗ TensorProduct.mk R M H v).rTensor H) (Coalgebra.comul (R := R) h) := by
  rw [coact_op_smul, Comodule.mem_fixedSubcomodule.mp hv]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul h₁ h₂ => simp

/-- The regular right Hopf module of a bialgebra over itself, with right multiplication as the
action and comultiplication as the coaction. -/
instance instSelf : RightHopfModule R H H where
  coact_op_smul m h := by
    have hmul :
        TensorProduct.map (rightAct R H H) (LinearMap.mul' R H)
            (TensorProduct.tensorTensorTensorComm R H H H H
              (Coalgebra.comul (R := R) m ⊗ₜ[R] Coalgebra.comul (R := R) h)) =
          Coalgebra.comul (R := R) m * Coalgebra.comul (R := R) h := by
      induction Coalgebra.comul (R := R) m using TensorProduct.inductionOn with
      | add x y hx hy =>
        simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hy]
      | tmul m₁ m₂ =>
        induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
        | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]
        | tmul h₁ h₂ =>
          simp [Algebra.TensorProduct.tmul_mul_tmul]
    simpa [Comodule.instSelf_coact, Bialgebra.comul_mul] using hmul.symm

/-- The coinvariants of the regular right comodule are the scalar multiples of `1`. -/
theorem mem_fixedSubcomodule_self {x : H} :
    x ∈ Comodule.fixedSubcomodule R H H ↔ x = algebraMap R H (Coalgebra.counit (R := R) x) := by
  rw [Comodule.mem_fixedSubcomodule, Comodule.instSelf_coact]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have h := congrArg
      ((TensorProduct.lid R H).toLinearMap ∘ₗ (Coalgebra.counit (R := R)).rTensor H) hx
    simpa [Coalgebra.rTensor_counit_comul, Algebra.algebraMap_eq_smul_one] using h
  · rw [hx, Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']

end Bialgebra

section FundamentalTheorem

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Module Hᵐᵒᵖ M] [IsScalarTower R Hᵐᵒᵖ M]
variable [Comodule R H M]

variable (R H M) in
/-- The coinvariant projection `P(m) = ∑ m₀ · S(m₁)` on a right Hopf module. -/
noncomputable def coinvariantProj : M →ₗ[R] M :=
  rightAct R H M ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor M ∘ₗ
    Comodule.coact (R := R) (C := H) (M := M)

/-- Expanding `coinvariantProj` into its three factors. -/
theorem coinvariantProj_apply (m : M) :
    coinvariantProj R H M m =
      rightAct R H M ((HopfAlgebra.antipode R (A := H)).lTensor M
        (Comodule.coact (R := R) (C := H) m)) :=
  (rfl)

/-- Helper contraction `m₀ ⊗ ((a ⊗ b) ⊗ c) ↦ (m₀ · S c) ⊗ (a * S b)` used to prove that
`coinvariantProj` lands in the fixed subcomodule. -/
private noncomputable def projContraction :
    M ⊗[R] ((H ⊗[R] H) ⊗[R] H) →ₗ[R] M ⊗[R] H :=
  (rightAct R H M).rTensor H ∘ₗ
    (TensorProduct.assoc R M H H).symm.toLinearMap ∘ₗ
    (TensorProduct.comm R H H).toLinearMap.lTensor M ∘ₗ
    (TensorProduct.map
      (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor H)
      (HopfAlgebra.antipode R (A := H))).lTensor M

omit [Comodule R H M] in
private theorem projContraction_pure (m₀ : M) (a b c : H) :
    projContraction (R := R) (H := H) (M := M) (m₀ ⊗ₜ[R] ((a ⊗ₜ[R] b) ⊗ₜ[R] c)) =
      (MulOpposite.op (HopfAlgebra.antipode R c) • m₀) ⊗ₜ[R]
        (a * HopfAlgebra.antipode R b) := by
  simp [projContraction]

/-- Applying `projContraction` after `(comul ⊗ id) ∘ comul` on the coalgebra leg cancels the
inner antipode pair and leaves `coinvariantProj m ⊗ₜ 1`. -/
private theorem projContraction_comul_rTensor (m : M) :
    projContraction (R := R) (H := H) (M := M)
        (((Coalgebra.comul (R := R) (A := H)).rTensor H ∘ₗ Coalgebra.comul).lTensor M
          (Comodule.coact (R := R) (C := H) m)) =
      coinvariantProj R H M m ⊗ₜ[R] (1 : H) := by
  have hinner :
      TensorProduct.map
          (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor H)
          (HopfAlgebra.antipode R (A := H)) ∘ₗ
        (Coalgebra.comul (R := R) (A := H)).rTensor H ∘ₗ Coalgebra.comul =
      (TensorProduct.mk R H H (1 : H)).comp (HopfAlgebra.antipode R (A := H)) := by
    have hmap :
        TensorProduct.map
            (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor H)
            (HopfAlgebra.antipode R (A := H)) ∘ₗ
          (Coalgebra.comul (R := R) (A := H)).rTensor H =
        TensorProduct.map
          (Algebra.linearMap R H ∘ₗ Coalgebra.counit (R := R) (A := H))
          (HopfAlgebra.antipode R (A := H)) := by
      rw [LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id,
        LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul]
    rw [← LinearMap.comp_assoc, hmap]
    ext h
    have hc :
        TensorProduct.map
            (Algebra.linearMap R H ∘ₗ Coalgebra.counit (R := R) (A := H))
            (HopfAlgebra.antipode R (A := H)) (Coalgebra.comul (R := R) h) =
          TensorProduct.map (Algebra.linearMap R H) (HopfAlgebra.antipode R (A := H))
            ((Coalgebra.counit (R := R) (A := H)).rTensor H (Coalgebra.comul (R := R) h)) := by
      rw [LinearMap.rTensor_def, TensorProduct.map_map, LinearMap.comp_id]
    rw [LinearMap.comp_apply, hc, Coalgebra.rTensor_counit_comul]
    simp
  have houter :
      projContraction (R := R) (H := H) (M := M) ∘ₗ
          ((Coalgebra.comul (R := R) (A := H)).rTensor H ∘ₗ Coalgebra.comul).lTensor M =
        (TensorProduct.mk R M H).flip (1 : H) ∘ₗ rightAct R H M ∘ₗ
          (HopfAlgebra.antipode R (A := H)).lTensor M := by
    dsimp only [projContraction]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.comp_assoc,
      ← LinearMap.lTensor_comp, hinner]
    apply TensorProduct.ext'
    intro m₀ h
    simp
  exact LinearMap.congr_fun houter (Comodule.coact (R := R) (C := H) m)

/-- Applying `projContraction` after reassociating `coact` and `comul` equals the coaction of
`rightAct ((antipode R).lTensor M x)`. -/
private theorem coact_rightAct_antipode [RightHopfModule R H M] (x : M ⊗[R] H) :
    Comodule.coact (R := R) (C := H)
        (rightAct R H M ((HopfAlgebra.antipode R (A := H)).lTensor M x)) =
      projContraction (R := R) (H := H) (M := M)
        (((TensorProduct.assoc R H H H).symm.toLinearMap ∘ₗ
            (Coalgebra.comul (R := R) (A := H)).lTensor H).lTensor M
          (TensorProduct.assoc R M H H ((Comodule.coact (R := R) (C := H)).rTensor H x))) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  | tmul n h =>
    simp only [LinearMap.lTensor_tmul, rightAct_tmul, coact_op_smul,
      TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, LinearMap.rTensor_tmul]
    induction Comodule.coact (R := R) (C := H) n using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.add_tmul, map_add, hy₁, hy₂]
    | tmul m₀ m₁ =>
      simp only [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply]
      induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
      | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
      | tmul h₁ h₂ =>
        simp [projContraction_pure]

/-- The coinvariant projection fixes every coinvariant element. -/
@[simp]
theorem coinvariantProj_of_mem {v : M} (hv : v ∈ Comodule.fixedSubcomodule R H M) :
    coinvariantProj R H M v = v := by
  rw [coinvariantProj_apply, Comodule.mem_fixedSubcomodule.mp hv]
  simp

variable [RightHopfModule R H M]

/-- The image of `coinvariantProj` is fixed by the coaction. -/
theorem coact_coinvariantProj (m : M) :
    Comodule.coact (R := R) (C := H) (coinvariantProj R H M m) =
      coinvariantProj R H M m ⊗ₜ[R] (1 : H) := by
  conv_lhs => rw [coinvariantProj_apply]
  rw [coact_rightAct_antipode, Comodule.coassoc_apply,
    ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc, Coalgebra.coassoc_symm,
    projContraction_comul_rTensor]

/-- The coinvariant projection lands in the fixed subcomodule. -/
theorem coinvariantProj_mem_fixedSubcomodule (m : M) :
    coinvariantProj R H M m ∈ Comodule.fixedSubcomodule R H M :=
  Comodule.mem_fixedSubcomodule.mpr (coact_coinvariantProj m)

/-- On `v · h` with `v` coinvariant, the projection contracts `h` by the counit. -/
theorem coinvariantProj_op_smul_of_mem {v : M} (hv : v ∈ Comodule.fixedSubcomodule R H M) (h : H) :
    coinvariantProj R H M (MulOpposite.op h • v) = Coalgebra.counit (R := R) h • v := by
  rw [coinvariantProj_apply, coact_op_smul_of_mem_fixedSubcomodule hv]
  have hstep :
      rightAct R H M ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor M ∘ₗ
          (rightAct R H M ∘ₗ TensorProduct.mk R M H v).rTensor H =
        rightAct R H M ∘ₗ TensorProduct.mk R M H v ∘ₗ
          (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).lTensor H) := by
    apply TensorProduct.ext'
    intro h₁ h₂
    simp [← mul_smul]
  have hval := LinearMap.congr_fun hstep (Coalgebra.comul (R := R) h)
  simp only [LinearMap.comp_apply] at hval
  rw [hval, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The coinvariant projection is idempotent. -/
theorem coinvariantProj_comp_coinvariantProj :
    coinvariantProj R H M ∘ₗ coinvariantProj R H M = coinvariantProj R H M :=
  LinearMap.ext fun m ↦ coinvariantProj_of_mem (coinvariantProj_mem_fixedSubcomodule m)

variable (R H M) in
/-- The coinvariant projection corestricted to the fixed subcomodule. -/
noncomputable def coinvariantProjToFixed : M →ₗ[R] Comodule.fixedSubcomodule R H M :=
  { toFun := fun m ↦ ⟨coinvariantProj R H M m, coinvariantProj_mem_fixedSubcomodule m⟩
    map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
    map_smul' := fun r x ↦ Subtype.ext (map_smul _ r x) }

@[simp]
theorem coe_coinvariantProjToFixed_apply (m : M) :
    (coinvariantProjToFixed R H M m : M) = coinvariantProj R H M m :=
  (rfl)

/-- The forward map `v ⊗ h ↦ v · h` of the fundamental theorem of Hopf modules. -/
private noncomputable def coinvariantToFun :
    Comodule.fixedSubcomodule R H M ⊗[R] H →ₗ[R] M :=
  rightAct R H M ∘ₗ (SMulMemClass.subtype (Comodule.fixedSubcomodule R H M)).rTensor H

/-- The inverse map `m ↦ ∑ P(m₀) ⊗ m₁` of the fundamental theorem of Hopf modules. -/
private noncomputable def coinvariantInvFun :
    M →ₗ[R] Comodule.fixedSubcomodule R H M ⊗[R] H :=
  (coinvariantProjToFixed R H M).rTensor H ∘ₗ Comodule.coact (R := R) (C := H) (M := M)

private theorem coinvariantToFun_comp_invFun :
    coinvariantToFun (R := R) (H := H) (M := M) ∘ₗ coinvariantInvFun = LinearMap.id := by
  apply LinearMap.ext
  intro m
  have hsub :
      SMulMemClass.subtype (Comodule.fixedSubcomodule R H M) ∘ₗ coinvariantProjToFixed R H M =
        coinvariantProj R H M :=
    LinearMap.ext fun _ ↦ (rfl)
  have hstep :
      rightAct R H M ∘ₗ (rightAct R H M).rTensor H ∘ₗ
          ((HopfAlgebra.antipode R (A := H)).lTensor M).rTensor H =
        rightAct R H M ∘ₗ
          (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).rTensor H).lTensor M ∘ₗ
          (TensorProduct.assoc R M H H).toLinearMap := by
    apply TensorProduct.ext_threefold
    intro m₀ h₁ h₂
    simp [← mul_smul]
  have hcalc :
      coinvariantToFun (R := R) (H := H) (M := M) (coinvariantInvFun m) =
        rightAct R H M
          ((LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).rTensor H).lTensor M
            (TensorProduct.assoc R M H H
              ((Comodule.coact (R := R) (C := H)).rTensor H
                (Comodule.coact (R := R) (C := H) m)))) := by
    dsimp only [coinvariantToFun, coinvariantInvFun]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.rTensor_comp_apply, hsub]
    dsimp only [coinvariantProj]
    rw [LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply]
    exact LinearMap.congr_fun hstep _
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [hcalc, Comodule.coassoc_apply, ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.lTensor_comp_apply,
    Comodule.lTensor_counit_coact]
  simp

private theorem coinvariantInvFun_comp_toFun :
    coinvariantInvFun (R := R) (H := H) (M := M) ∘ₗ coinvariantToFun = LinearMap.id := by
  apply TensorProduct.ext'
  intro v h
  dsimp only [coinvariantToFun, coinvariantInvFun]
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, rightAct_tmul, LinearMap.id_apply]
  have hv : SMulMemClass.subtype (Comodule.fixedSubcomodule R H M) v = (v : M) := (rfl)
  rw [hv, coact_op_smul_of_mem_fixedSubcomodule v.2, ← LinearMap.rTensor_comp_apply]
  have hproj :
      coinvariantProjToFixed R H M ∘ₗ rightAct R H M ∘ₗ TensorProduct.mk R M H (v : M) =
        LinearMap.toSpanSingleton R (Comodule.fixedSubcomodule R H M) v ∘ₗ
          Coalgebra.counit (R := R) (A := H) := by
    ext x
    simpa [LinearMap.toSpanSingleton_apply] using coinvariantProj_op_smul_of_mem v.2 x
  rw [hproj, LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul]
  simp

variable (R H M) in
/-- **The fundamental theorem of Hopf modules**: every right-right Hopf module `M` over a Hopf
algebra `H` is canonically isomorphic to `Comodule.fixedSubcomodule R H M ⊗[R] H` via the right
action `v ⊗ h ↦ v · h`. -/
noncomputable def coinvariantEquiv : Comodule.fixedSubcomodule R H M ⊗[R] H ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap coinvariantToFun coinvariantInvFun
    coinvariantToFun_comp_invFun coinvariantInvFun_comp_toFun

/-- On a pure tensor, `coinvariantEquiv` acts by the right `H`-action. -/
@[simp]
theorem coinvariantEquiv_tmul (v : Comodule.fixedSubcomodule R H M) (h : H) :
    coinvariantEquiv R H M (v ⊗ₜ[R] h) = MulOpposite.op h • (v : M) :=
  (rfl)

/-- The inverse of `coinvariantEquiv` applies the coinvariant projection to the first leg of the
coaction. -/
theorem coinvariantEquiv_symm_apply (m : M) :
    (coinvariantEquiv R H M).symm m =
      (coinvariantProjToFixed R H M).rTensor H (Comodule.coact (R := R) (C := H) m) :=
  (rfl)

/-- `coinvariantEquiv` is right `H`-linear: multiplying in the `H` tensor factor corresponds to the
right `H`-action on `M`. -/
theorem coinvariantEquiv_tmul_mul (v : Comodule.fixedSubcomodule R H M) (h₁ h₂ : H) :
    coinvariantEquiv R H M (v ⊗ₜ[R] (h₁ * h₂)) =
      MulOpposite.op h₂ • coinvariantEquiv R H M (v ⊗ₜ[R] h₁) := by
  simp [← mul_smul]

/-- `coinvariantEquiv` is right `H`-colinear: the coaction on `M` corresponds to comultiplication
on the `H` tensor factor. -/
theorem coact_coinvariantEquiv (x : Comodule.fixedSubcomodule R H M ⊗[R] H) :
    Comodule.coact (R := R) (C := H) (coinvariantEquiv R H M x) =
      (coinvariantEquiv R H M).toLinearMap.rTensor H
        ((TensorProduct.assoc R (Comodule.fixedSubcomodule R H M) H H).symm
          ((Coalgebra.comul (R := R) (A := H)).lTensor (Comodule.fixedSubcomodule R H M) x)) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  | tmul v h =>
    simp only [coinvariantEquiv_tmul, coact_op_smul_of_mem_fixedSubcomodule v.2,
      LinearMap.lTensor_tmul]
    induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
    | tmul h₁ h₂ => simp

end FundamentalTheorem

end RightHopfModule

end TauCeti
