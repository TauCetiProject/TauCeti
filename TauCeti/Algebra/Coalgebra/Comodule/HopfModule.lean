/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finrank
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The fundamental theorem of Hopf modules

A right Hopf module over a bialgebra `H` is a right `H`-comodule `M` with a right `H`-action
`m ⊗ h ↦ m • h` which is unital, associative and colinear for the diagonal coaction on `M ⊗ H`:

```text
ρ(m • h) = Σ m₀ • h₁ ⊗ m₁ h₂.
```

Here the action is a linear map `act : M ⊗[R] H →ₗ[R] M`, and `TauCeti.Comodule.IsHopfModuleAction`
records the three laws. Over a Hopf algebra the map `P(m) = Σ m₀ • S(m₁)` takes values in the
fixed subcomodule `M^{co H}`, and every vector is recovered as `m = Σ P(m₀) • m₁`. Together with
`P(n • h) = ε(h) n` for fixed `n`, this shows that the action restricts to a linear equivalence
`M^{co H} ⊗ H ≃ M`. This is the fundamental theorem of Hopf modules of Larson and Sweedler.
Over a field it gives `dim M = dim M^{co H} · dim H`; applied to the linear dual of a
finite-dimensional Hopf algebra it produces cointegrals.

## Main declarations

* `TauCeti.Comodule.IsHopfModuleAction`: the Hopf-module laws for a right action.
* `LinearMap.hopfModuleProj`: the projection `m ↦ Σ m₀ • S(m₁)`.
* `TauCeti.Comodule.IsHopfModuleAction.hopfModuleProj_mem_fixedSubcomodule`: it lands in the
  fixed subcomodule.
* `TauCeti.Comodule.IsHopfModuleAction.range_hopfModuleProj`: its image is exactly the fixed
  subcomodule.
* `TauCeti.Comodule.IsHopfModuleAction.act_rTensor_hopfModuleProj_coact`: the reconstruction
  `Σ P(m₀) • m₁ = m`.
* `TauCeti.Comodule.IsHopfModuleAction.fixedTensorEquiv`: the fundamental theorem
  `M^{co H} ⊗ H ≃ M`, which is `H`-linear (`act_fixedTensorEquiv_tmul`) and colinear
  (`coact_fixedTensorEquiv`).
* `TauCeti.Comodule.IsHopfModuleAction.finrank_eq`: `dim M = dim M^{co H} · dim H` over a field.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Proposition 1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 1.9.4.
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti.Comodule

variable {R H M : Type*} [CommSemiring R]

section Bialgebra

variable [Semiring H] [Bialgebra R H] [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The laws of a right Hopf-module action `act (m ⊗ h) = m • h` on a right `H`-comodule: the
action is unital and associative, and the coaction of `m • h` is `Σ m₀ • h₁ ⊗ m₁ h₂`, that is,
`act` is colinear for the diagonal coaction on `M ⊗ H`. -/
structure IsHopfModuleAction (act : M ⊗[R] H →ₗ[R] M) : Prop where
  /-- The unit of `H` acts trivially. -/
  act_one (m : M) : act (m ⊗ₜ 1) = m
  /-- The action is associative. -/
  act_act (m : M) (a b : H) : act (act (m ⊗ₜ a) ⊗ₜ b) = act (m ⊗ₜ (a * b))
  /-- The action is colinear for the diagonal coaction: `ρ(m • h) = Σ m₀ • h₁ ⊗ m₁ h₂`. -/
  coact_act (m : M) (h : H) :
    coact (act (m ⊗ₜ h)) = act.rTensor H (tensorCoact (m ⊗ₜ[R] h))

namespace IsHopfModuleAction

variable {act : M ⊗[R] H →ₗ[R] M}

/-- Colinearity of a Hopf-module action, as an equality of linear maps. -/
theorem coact_comp_act (hact : IsHopfModuleAction act) :
    coact (R := R) (C := H) (M := M) ∘ₗ act = act.rTensor H ∘ₗ tensorCoact :=
  TensorProduct.ext' hact.coact_act

/-- Associativity of a Hopf-module action, applied to an arbitrary tensor `x ∈ (M ⊗ H) ⊗ H`. -/
theorem act_rTensor_act (hact : IsHopfModuleAction act) (x : (M ⊗[R] H) ⊗[R] H) :
    act (act.rTensor H x) =
      act ((LinearMap.mul' R H).lTensor M (TensorProduct.assoc R M H H x)) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul y b =>
    induction y with
    | add y z hy hz => simp only [add_tmul, map_add, hy, hz]
    | tmul m a => simp [hact.act_act]

/-- On a fixed vector `n`, the coaction of `n • h` is `Σ n • h₁ ⊗ h₂`. -/
theorem coact_act_of_mem_fixedSubcomodule (hact : IsHopfModuleAction act) {n : M}
    (hn : n ∈ fixedSubcomodule R H M) (h : H) :
    coact (act (n ⊗ₜ h)) = (act ∘ₗ TensorProduct.mk R M H n).rTensor H (Coalgebra.comul h) := by
  rw [hact.coact_act, tensorCoact_tmul, mem_fixedSubcomodule.mp hn, instSelf_coact]
  induction Coalgebra.comul (R := R) h with
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a b => simp

end IsHopfModuleAction

end Bialgebra

section HopfAlgebra

variable [Semiring H] [HopfAlgebra R H] [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The projection `m ↦ Σ m₀ • S(m₁)` of a Hopf module onto its fixed vectors. -/
noncomputable def _root_.LinearMap.hopfModuleProj (act : M ⊗[R] H →ₗ[R] M) : M →ₗ[R] M :=
  act ∘ₗ (HopfAlgebra.antipode R).lTensor M ∘ₗ coact

/-- The projection `hopfModuleProj` as a composite of linear maps. -/
theorem _root_.LinearMap.hopfModuleProj_def (act : M ⊗[R] H →ₗ[R] M) :
    act.hopfModuleProj = act ∘ₗ (HopfAlgebra.antipode R).lTensor M ∘ₗ coact :=
  (rfl)

/-- Unfolding `hopfModuleProj`: it applies the antipode to the coefficient of the coaction and
then acts. -/
theorem _root_.LinearMap.hopfModuleProj_apply (act : M ⊗[R] H →ₗ[R] M) (m : M) :
    act.hopfModuleProj m = act ((HopfAlgebra.antipode R).lTensor M (coact (C := H) m)) :=
  (rfl)

variable {act : M ⊗[R] H →ₗ[R] M}

namespace IsHopfModuleAction

/-- The projection `m ↦ Σ m₀ • S(m₁)` takes values in the fixed subcomodule. -/
theorem hopfModuleProj_mem_fixedSubcomodule (hact : IsHopfModuleAction act) (m : M) :
    act.hopfModuleProj m ∈ fixedSubcomodule R H M := by
  set S := HopfAlgebra.antipode R (A := H)
  -- The diagonal coaction of `m' ⊗ S c` only needs the coaction of `m'`.
  have hcoact (y : M ⊗[R] H) :
      tensorCoact (S.lTensor M y) =
        tensorCombine ((Coalgebra.comul ∘ₗ S).lTensor (M ⊗[R] H) (coact.rTensor H y)) := by
    induction y with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul m' c => simp
  -- Acting on the first leg reduces the computation to `Σ (S c₂)₁ ⊗ c₁ (S c₂)₂` in `H`.
  have hleg (m' : M) (a : H) (z : H ⊗[R] H) :
      act.rTensor H (tensorCombine ((m' ⊗ₜ a) ⊗ₜ z)) =
        (act ∘ₗ TensorProduct.mk R M H m').rTensor H
          ((LinearMap.mul' R H).lTensor H (TensorProduct.leftComm R H H H (a ⊗ₜ z))) := by
    induction z with
    | add z w hz hw => simp only [tmul_add, map_add, hz, hw]
    | tmul x y => simp
  have hy (y : M ⊗[R] H) :
      act.rTensor H (tensorCombine ((Coalgebra.comul ∘ₗ S).lTensor (M ⊗[R] H)
        ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M y)))) =
        act (S.lTensor M y) ⊗ₜ 1 := by
    induction y with
    | add y z hy hz => simp only [map_add, add_tmul, hy, hz]
    | tmul m' c =>
      have hw (w : H ⊗[R] H) :
          act.rTensor H (tensorCombine ((Coalgebra.comul ∘ₗ S).lTensor (M ⊗[R] H)
            ((TensorProduct.assoc R M H H).symm (m' ⊗ₜ w)))) =
            (act ∘ₗ TensorProduct.mk R M H m').rTensor H
              ((LinearMap.mul' R H).lTensor H (TensorProduct.leftComm R H H H
                ((Coalgebra.comul ∘ₗ S).lTensor H w))) := by
        induction w with
        | add w w' hw hw' => simp only [tmul_add, map_add, hw, hw']
        | tmul a b => simpa using hleg m' a (Coalgebra.comul (S b))
      rw [LinearMap.lTensor_tmul, hw,
        TauCeti.HopfAlgebra.lTensor_mul'_leftComm_comul_antipode_comul]
      simp [S]
  rw [mem_fixedSubcomodule, LinearMap.hopfModuleProj_apply,
    ← LinearMap.comp_apply (coact (C := H)), hact.coact_comp_act, LinearMap.comp_apply, hcoact,
    ← (TensorProduct.assoc R M H H).symm_apply_apply (coact.rTensor H (coact m)), coassoc_apply,
    hy]

/-- Every vector of a Hopf module is recovered from its projection: `Σ P(m₀) • m₁ = m`. -/
theorem act_rTensor_hopfModuleProj_coact (hact : IsHopfModuleAction act) (m : M) :
    act (act.hopfModuleProj.rTensor H (coact m)) = m := by
  have hS : (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H) ∘ₗ Coalgebra.comul =
      Algebra.linearMap R H ∘ₗ Coalgebra.counit := by
    rw [LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul]
  have hassoc (x : (M ⊗[R] H) ⊗[R] H) :
      TensorProduct.assoc R M H H (((HopfAlgebra.antipode R).lTensor M).rTensor H x) =
        ((HopfAlgebra.antipode R).rTensor H).lTensor M (TensorProduct.assoc R M H H x) :=
    (LinearMap.congr_fun (LinearMap.lTensor_rTensor_comp_assoc (P := M) (Q := H)
      (x := HopfAlgebra.antipode R (A := H))) x).symm
  -- `Σ (m₀₀ • S(m₀₁)) • m₁ = Σ m₀ • (S(m₁) m₂) = Σ m₀ • ε(m₁) = m`, by associativity of the
  -- action, coassociativity of the coaction, the antipode axiom and the counit law.
  rw [LinearMap.hopfModuleProj, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
    hact.act_rTensor_act, hassoc, coassoc_apply, ← LinearMap.lTensor_comp_apply,
    ← LinearMap.lTensor_comp_apply, hS, LinearMap.lTensor_comp_apply,
    lTensor_counit_coact]
  simp [hact.act_one]

/-- The projection sends `n • h` to `ε(h) n` when `n` is fixed. -/
theorem hopfModuleProj_act_of_mem_fixedSubcomodule (hact : IsHopfModuleAction act) {n : M}
    (hn : n ∈ fixedSubcomodule R H M) (h : H) :
    act.hopfModuleProj (act (n ⊗ₜ h)) = Coalgebra.counit (R := R) h • n := by
  have hx (x : H ⊗[R] H) :
      act ((HopfAlgebra.antipode R).lTensor M
        ((act ∘ₗ TensorProduct.mk R M H n).rTensor H x)) =
        act (n ⊗ₜ LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H x)) := by
    induction x with
    | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    | tmul a b => simp [hact.act_act]
  rw [LinearMap.hopfModuleProj_apply, hact.coact_act_of_mem_fixedSubcomodule hn, hx,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, Algebra.algebraMap_eq_smul_one, tmul_smul,
    map_smul, hact.act_one]

/-- The projection fixes the fixed vectors. -/
theorem hopfModuleProj_of_mem_fixedSubcomodule (hact : IsHopfModuleAction act) {n : M}
    (hn : n ∈ fixedSubcomodule R H M) : act.hopfModuleProj n = n := by
  simpa [hact.act_one] using hact.hopfModuleProj_act_of_mem_fixedSubcomodule hn 1

/-- The image of the projection `m ↦ Σ m₀ • S(m₁)` is the fixed subcomodule. -/
theorem range_hopfModuleProj (hact : IsHopfModuleAction act) :
    LinearMap.range act.hopfModuleProj = (fixedSubcomodule R H M).toSubmodule := by
  ext m
  refine ⟨?_, fun hm ↦ ⟨m, hact.hopfModuleProj_of_mem_fixedSubcomodule
    (Subcomodule.mem_toSubmodule.mp hm)⟩⟩
  rintro ⟨m', rfl⟩
  exact Subcomodule.mem_toSubmodule.mpr (hact.hopfModuleProj_mem_fixedSubcomodule m')

/-- **The fundamental theorem of Hopf modules.** The action restricts to a linear equivalence
`M^{co H} ⊗ H ≃ M`, `n ⊗ h ↦ n • h`, with inverse `m ↦ Σ P(m₀) ⊗ m₁`. -/
noncomputable def fixedTensorEquiv (hact : IsHopfModuleAction act) :
    (fixedSubcomodule R H M).toSubmodule ⊗[R] H ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (act ∘ₗ (fixedSubcomodule R H M).toSubmodule.subtype.rTensor H)
    ((act.hopfModuleProj.codRestrict (fixedSubcomodule R H M).toSubmodule
      fun m ↦ Subcomodule.mem_toSubmodule.mpr
        (hact.hopfModuleProj_mem_fixedSubcomodule m)).rTensor H ∘ₗ coact)
    (by
      ext m
      simpa [← LinearMap.rTensor_comp_apply] using hact.act_rTensor_hopfModuleProj_coact m)
    (by
      refine TensorProduct.ext' fun n h ↦ ?_
      have hn : (n : M) ∈ fixedSubcomodule R H M := Subcomodule.mem_toSubmodule.mp n.2
      have hx (x : H ⊗[R] H) :
          (act.hopfModuleProj.codRestrict (fixedSubcomodule R H M).toSubmodule
              fun m ↦ Subcomodule.mem_toSubmodule.mpr
                (hact.hopfModuleProj_mem_fixedSubcomodule m)).rTensor H
            ((act ∘ₗ TensorProduct.mk R M H n).rTensor H x) =
            (LinearMap.toSpanSingleton R _ n).rTensor H (Coalgebra.counit.rTensor H x) := by
        induction x with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, TensorProduct.mk_apply,
            LinearMap.toSpanSingleton_apply]
          congr 1
          exact Subtype.ext (hact.hopfModuleProj_act_of_mem_fixedSubcomodule hn a)
      simp [hact.coact_act_of_mem_fixedSubcomodule hn, hx, Coalgebra.rTensor_counit_comul])

@[simp]
theorem fixedTensorEquiv_tmul (hact : IsHopfModuleAction act)
    (n : (fixedSubcomodule R H M).toSubmodule) (h : H) :
    hact.fixedTensorEquiv (n ⊗ₜ h) = act ((n : M) ⊗ₜ h) :=
  (rfl)

/-- `fixedTensorEquiv` is `H`-linear for the right action on the second factor of
`M^{co H} ⊗ H`: `(n ⊗ a) • h ↦ (n • a) • h`. -/
theorem act_fixedTensorEquiv_tmul (hact : IsHopfModuleAction act)
    (x : (fixedSubcomodule R H M).toSubmodule ⊗[R] H) (h : H) :
    act (hact.fixedTensorEquiv x ⊗ₜ h) =
      hact.fixedTensorEquiv ((LinearMap.mul' R H).lTensor _
        (TensorProduct.assoc R _ H H (x ⊗ₜ h))) := by
  induction x with
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul n a => simp [hact.act_act]

/-- `fixedTensorEquiv` is colinear for the cofree coaction `n ⊗ a ↦ Σ (n ⊗ a₁) ⊗ a₂` on
`M^{co H} ⊗ H`. -/
theorem coact_fixedTensorEquiv (hact : IsHopfModuleAction act)
    (x : (fixedSubcomodule R H M).toSubmodule ⊗[R] H) :
    coact (hact.fixedTensorEquiv x) =
      hact.fixedTensorEquiv.toLinearMap.rTensor H
        ((TensorProduct.assoc R _ H H).symm (Coalgebra.comul.lTensor _ x)) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n a =>
    rw [fixedTensorEquiv_tmul, hact.coact_act_of_mem_fixedSubcomodule
      (Subcomodule.mem_toSubmodule.mp n.2), LinearMap.lTensor_tmul]
    induction Coalgebra.comul (R := R) a with
    | add u w hu hw => simp only [tmul_add, map_add, hu, hw]
    | tmul b c => simp

/-- The inverse of `fixedTensorEquiv` is `m ↦ Σ P(m₀) ⊗ m₁`, with `P` corestricted to the fixed
subcomodule. -/
theorem fixedTensorEquiv_symm_apply (hact : IsHopfModuleAction act) (m : M) :
    hact.fixedTensorEquiv.symm m =
      (act.hopfModuleProj.codRestrict (fixedSubcomodule R H M).toSubmodule
        fun m ↦ Subcomodule.mem_toSubmodule.mpr
          (hact.hopfModuleProj_mem_fixedSubcomodule m)).rTensor H (coact m) :=
  (rfl)

/-- The inverse of `fixedTensorEquiv` is `m ↦ Σ P(m₀) ⊗ m₁`. -/
@[simp]
theorem rTensor_subtype_fixedTensorEquiv_symm (hact : IsHopfModuleAction act) (m : M) :
    (fixedSubcomodule R H M).toSubmodule.subtype.rTensor H (hact.fixedTensorEquiv.symm m) =
      act.hopfModuleProj.rTensor H (coact m) := by
  simp [fixedTensorEquiv, ← LinearMap.rTensor_comp_apply]

end IsHopfModuleAction

end HopfAlgebra

section Field

variable {k : Type*} [Field k] [Ring H] [HopfAlgebra k H] [AddCommGroup M] [Module k M]
  [Comodule k H M] {act : M ⊗[k] H →ₗ[k] M}

/-- Over a field, the dimension of a Hopf module is the dimension of its fixed vectors times the
dimension of the Hopf algebra. -/
theorem IsHopfModuleAction.finrank_eq (hact : IsHopfModuleAction act) :
    Module.finrank k M = Module.finrank k (fixedSubcomodule k H M) * Module.finrank k H := by
  rw [← hact.fixedTensorEquiv.finrank_eq, Module.finrank_tensorProduct,
    Subcomodule.finrank_toSubmodule]

end Field

end TauCeti.Comodule
