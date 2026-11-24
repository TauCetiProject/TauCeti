/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.Group.Action.Pow
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Topological `ℤ_[p]`-modules and their additive groups

A continuous additive map `f : E →+ F` between topological `ℤ_[p]`-modules with `F` Hausdorff is
automatically `ℤ_[p]`-linear: for fixed `x`, the continuous maps `c ↦ f (c • x)` and `c ↦ c • f x`
agree on the dense subset `ℕ` of `ℤ_[p]`, and two continuous maps into a Hausdorff space that agree
on a dense set are equal. So the `ℤ_[p]`-module structure of a Hausdorff topological
`ℤ_[p]`-module is determined by its topological group structure, and continuous additive maps and
isomorphisms between such modules can be treated as continuous `ℤ_[p]`-linear ones. In the
automatic-linearity and rank results, the codomain `F` is assumed Hausdorff.

This file adapts `Mathlib/Topology/Instances/RealVectorSpace.lean` (Yury Kudryashov) from `ℝ` to
`ℤ_[p]`: `TauCeti.map_padicInt_smul`, `AddMonoidHom.toPadicIntLinearMap`, and
`AddEquiv.toPadicIntLinearEquiv` are the `ℤ_[p]` counterparts of `map_real_smul`,
`AddMonoidHom.toRealLinearMap`, and `AddEquiv.toRealLinearEquiv`.

In particular the rank of a finite free `ℤ_[p]`-module is a topological invariant: a continuous
additive isomorphism between two such modules preserves `Module.finrank`, and `ℤ_[p] ^ r` and
`ℤ_[p] ^ r'` are topologically isomorphic groups only when `r = r'`.

Algebraically, every `p`-primary abelian group `M` carries a canonical (and unique) `ℤ_[p]`-module
structure in which `a : ℤ_[p]` acts on an element `x` killed by `p ^ k` through its truncation
`a.appr k • x` (`IsAddPGroup.padicIntModule`), and every additive homomorphism out of `M` into a
`ℤ_[p]`-module is automatically `ℤ_[p]`-linear (`IsAddPGroup.map_padicInt_smul`).

## Main results

* `TauCeti.closedAddSubgroupPadicIntSubmoduleOrderIso`: closed additive subgroups are precisely
  closed submodules. This correspondence needs neither compactness nor separation: closedness
  and density of the natural-number scalars give stability under all `ℤ_[p]`-scalars.
* `TauCeti.map_padicInt_smul`: a continuous additive map between topological `ℤ_[p]`-modules
  with Hausdorff codomain commutes with scalar multiplication by `ℤ_[p]`.
* `AddMonoidHom.toPadicIntLinearMap`, `AddEquiv.toPadicIntLinearEquiv`: the resulting continuous
  `ℤ_[p]`-linear map and continuous `ℤ_[p]`-linear equivalence.
* `AddEquiv.finrank_padicInt_eq`: a continuous additive isomorphism preserves the `ℤ_[p]`-rank.
* `TauCeti.eq_of_continuousMulEquiv_pi_padicInt`: topologically isomorphic groups `ℤ_[p] ^ r` and
  `ℤ_[p] ^ r'` have `r = r'`.
* `Submodule.torsion_padicInt`: the torsion submodule of a `ℤ_[p]`-module is its torsion subgroup.
  This is purely algebraic, the `ℤ_[p]` counterpart of `Submodule.torsion_int`.
* `TauCeti.restrictScalars_pPowerTorsion`: over `ℤ_p`, the `p`-power torsion is the whole torsion
  submodule.
* `TauCeti.isTorsionFree_quotient_pPowerTorsion`: modulo its `p`-power torsion, a `ℤ_p`-module
  is torsion-free.
* `PadicInt.smul_eq_appr_nsmul`: in any `ℤ_[p]`-module, `a • x = a.appr k • x` whenever
  `p ^ k • x = 0`.
* `IsAddPGroup.padicIntModule` and `IsAddPGroup.map_padicInt_smul`: the canonical `ℤ_[p]`-module
  structure on a `p`-primary abelian group, and automatic `ℤ_[p]`-linearity of additive
  homomorphisms out of it.
* `AddCommGroup.primaryComponent.instModulePadicInt` and
  `TauCeti.AddCommGroup.primaryComponentMap`: the canonical `ℤ_[p]`-module instance and
  `ℤ_[p]`-linear functoriality of `A[p^∞]`.
* `LinearMap.padicIntCodRestrict`: a `ℚ_[p]`-valued `ℤ_[p]`-linear map with values in
  `ℤ_[p]`, as a `ℤ_[p]`-valued functional.
-/

public section

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
  {F : Type*} [AddCommMonoid F] [TopologicalSpace F] [T2Space F]

section

variable {p : ℕ} [Fact p.Prime] [Module ℤ_[p] E] [ContinuousSMul ℤ_[p] E] [Module ℤ_[p] F]
  [ContinuousSMul ℤ_[p] F]

/-- A continuous additive map between two topological `ℤ_[p]`-modules, the codomain being
Hausdorff, is `ℤ_[p]`-linear. -/
theorem TauCeti.map_padicInt_smul {G : Type*} [FunLike G E F] [AddMonoidHomClass G E F] (f : G)
    (hf : Continuous f) (c : ℤ_[p]) (x : E) : f (c • x) = c • f x :=
  suffices (fun c : ℤ_[p] ↦ f (c • x)) = fun c : ℤ_[p] ↦ c • f x from congr_fun this c
  PadicInt.denseRange_natCast.equalizer (hf.comp (continuous_id.smul continuous_const))
    (continuous_id.smul continuous_const) (funext fun n ↦ by simp [Nat.cast_smul_eq_nsmul])

/-- A continuous additive isomorphism between topological `ℤ_[p]`-modules, the codomain being
Hausdorff, preserves the `ℤ_[p]`-rank: the rank of a finite free `ℤ_[p]`-module is a topological
invariant. -/
theorem AddEquiv.finrank_padicInt_eq (e : E ≃+ F) (he : Continuous e) :
    Module.finrank ℤ_[p] E = Module.finrank ℤ_[p] F :=
  LinearEquiv.finrank_eq (e.toLinearEquiv (TauCeti.map_padicInt_smul e he))

/-- The rank of `ℤ_[p] ^ r` is a topological invariant: if the additive groups `ℤ_[p] ^ r` and
`ℤ_[p] ^ r'`, written multiplicatively, are topologically isomorphic, then `r = r'`. -/
theorem TauCeti.eq_of_continuousMulEquiv_pi_padicInt {r r' : ℕ}
    (e : Multiplicative (Fin r → ℤ_[p]) ≃ₜ* Multiplicative (Fin r' → ℤ_[p])) : r = r' := by
  have hf : Continuous (AddEquiv.toMultiplicative.symm e.toMulEquiv) :=
    continuous_toAdd.comp (e.continuous.comp continuous_ofAdd)
  simpa [Module.finrank_fin_fun] using
    (AddEquiv.toMultiplicative.symm e.toMulEquiv).finrank_padicInt_eq (p := p) hf

end

section ClosedSubgroups

variable (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [Module ℤ_[p] M] [ContinuousSMul ℤ_[p] M]

/-- A closed additive subgroup of a topological `ℤ_[p]`-module is stable under `ℤ_[p]`-scalars.
No separation or compactness hypothesis is needed. -/
theorem ClosedAddSubgroup.padicInt_smul_mem (H : ClosedAddSubgroup M) {x : M}
    (hx : x ∈ H) (c : ℤ_[p]) : c • x ∈ H := by
  refine PadicInt.denseRange_natCast.induction_on c ?_ fun n ↦ ?_
  · exact H.isClosed'.preimage (continuous_id.smul continuous_const)
  · rw [Nat.cast_smul_eq_nsmul]
    exact H.toAddSubgroup.nsmul_mem hx n

/-- The closed `ℤ_[p]`-submodule with the same carrier as a closed additive subgroup. -/
def ClosedAddSubgroup.toPadicIntSubmodule (H : ClosedAddSubgroup M) :
    ClosedSubmodule ℤ_[p] M where
  toSubmodule :=
    { H.toAddSubgroup with smul_mem' := fun c _ hx ↦ H.padicInt_smul_mem p hx c }
  isClosed' := H.isClosed'

@[simp]
theorem ClosedAddSubgroup.coe_toPadicIntSubmodule (H : ClosedAddSubgroup M) :
    (H.toPadicIntSubmodule p : Set M) = H :=
  (rfl)

@[simp]
theorem ClosedAddSubgroup.mem_toPadicIntSubmodule (H : ClosedAddSubgroup M) {x : M} :
    x ∈ H.toPadicIntSubmodule p ↔ x ∈ H :=
  Iff.rfl

@[simp]
theorem ClosedAddSubgroup.toAddSubgroup_toPadicIntSubmodule (H : ClosedAddSubgroup M) :
    (H.toPadicIntSubmodule p).toSubmodule.toAddSubgroup = H.toAddSubgroup :=
  (rfl)

/-- Closed additive subgroups and closed `ℤ_[p]`-submodules of a topological `ℤ_[p]`-module
are the same ordered collection of subsets. -/
noncomputable def TauCeti.closedAddSubgroupPadicIntSubmoduleOrderIso :
    ClosedAddSubgroup M ≃o ClosedSubmodule ℤ_[p] M where
  toFun H := H.toPadicIntSubmodule p
  invFun S := ⟨S.toSubmodule.toAddSubgroup, S.isClosed⟩
  left_inv H := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem TauCeti.closedAddSubgroupPadicIntSubmoduleOrderIso_apply (H : ClosedAddSubgroup M) :
    closedAddSubgroupPadicIntSubmoduleOrderIso p H = H.toPadicIntSubmodule p :=
  (rfl)

@[simp]
theorem TauCeti.closedAddSubgroupPadicIntSubmoduleOrderIso_symm_toAddSubgroup
    (S : ClosedSubmodule ℤ_[p] M) :
    ((closedAddSubgroupPadicIntSubmoduleOrderIso p).symm S).toAddSubgroup =
      S.toSubmodule.toAddSubgroup :=
  (rfl)

@[simp]
theorem TauCeti.mem_closedAddSubgroupPadicIntSubmoduleOrderIso_symm
    (S : ClosedSubmodule ℤ_[p] M) {x : M} :
    x ∈ (closedAddSubgroupPadicIntSubmoduleOrderIso p).symm S ↔ x ∈ S :=
  Iff.rfl

end ClosedSubgroups

section

variable (p : ℕ) [Fact p.Prime] [Module ℤ_[p] E] [ContinuousSMul ℤ_[p] E] [Module ℤ_[p] F]
  [ContinuousSMul ℤ_[p] F]

/-- Reinterpret a continuous additive homomorphism between two topological `ℤ_[p]`-modules, the
codomain being Hausdorff, as a continuous `ℤ_[p]`-linear map. The prime is explicit because the
map does not determine it. -/
def AddMonoidHom.toPadicIntLinearMap (f : E →+ F) (hf : Continuous f) : E →L[ℤ_[p]] F :=
  ⟨{ toFun := f
     map_add' := f.map_add
     map_smul' := TauCeti.map_padicInt_smul f hf }, hf⟩

@[simp]
theorem AddMonoidHom.coe_toPadicIntLinearMap (f : E →+ F) (hf : Continuous f) :
    ⇑(f.toPadicIntLinearMap p hf) = f :=
  (rfl)

/-- Reinterpret a continuous additive equivalence between two topological `ℤ_[p]`-modules, the
codomain being Hausdorff, as a continuous `ℤ_[p]`-linear equivalence. The prime is explicit
because the equivalence does not determine it. -/
def AddEquiv.toPadicIntLinearEquiv (e : E ≃+ F) (h₁ : Continuous e)
    (h₂ : Continuous e.symm) : E ≃L[ℤ_[p]] F :=
  -- Reuse the continuous linear map to keep the supplied functions computable.
  { e, e.toAddMonoidHom.toPadicIntLinearMap p h₁ with
    continuous_toFun := h₁
    continuous_invFun := h₂ }

@[simp]
theorem AddEquiv.coe_toPadicIntLinearEquiv (e : E ≃+ F) (h₁ : Continuous e)
    (h₂ : Continuous e.symm) : ⇑(e.toPadicIntLinearEquiv p h₁ h₂) = e :=
  (rfl)

@[simp]
theorem AddEquiv.coe_toPadicIntLinearEquiv_symm (e : E ≃+ F) (h₁ : Continuous e)
    (h₂ : Continuous e.symm) : ⇑(e.toPadicIntLinearEquiv p h₁ h₂).symm = e.symm :=
  (rfl)

end

section Torsion

variable (p : ℕ) [hp : Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

/-- **The torsion submodule of a `ℤ_[p]`-module is its torsion subgroup.** This is the `ℤ_[p]`
analogue of `Submodule.torsion_int`. -/
theorem Submodule.torsion_padicInt :
    (torsion ℤ_[p] M).toAddSubgroup = AddCommGroup.torsion M := by
  -- A nonzero `p`-adic integer is a unit times a power of `p`, so an element it kills is killed
  -- by a positive integer; conversely a positive integer is a nonzero `p`-adic integer.
  ext x
  simp only [mem_toAddSubgroup, mem_torsion_iff, AddCommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨a, ha⟩
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p ^ a.valuation, pow_pos hp.out.pos _, ?_⟩
    -- `p ^ v(a)` is `a` divided by its unit part.
    have hpow : ((p ^ a.valuation : ℕ) : ℤ_[p]) = ↑(PadicInt.unitCoeff ha0)⁻¹ * a := by
      rw [eq_comm, Units.inv_mul_eq_iff_eq_mul, Nat.cast_pow]
      exact PadicInt.unitCoeff_spec ha0
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], hpow, mul_smul]
    simpa using hax
  · intro hx
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')⟩,
      by simpa [Nat.cast_smul_eq_nsmul] using hnx⟩

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]

/-- Over `ℤ_p`, the `p`-power torsion is the whole torsion submodule: a nonzero `p`-adic integer is
a unit times a power of `p`. -/
@[simp]
theorem restrictScalars_pPowerTorsion {A : Type*} [Semiring A] [Module A M] [SMul ℤ_[p] A]
    [IsScalarTower ℤ_[p] A M] :
    (pPowerTorsion p A M).restrictScalars ℤ_[p] = Submodule.torsion ℤ_[p] M := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_pPowerTorsion_iff, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    refine ⟨⟨(p : ℤ_[p]) ^ k, pow_mem (mem_nonZeroDivisors_of_ne_zero hp) k⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hk]
  · rintro ⟨⟨r, hr⟩, hrx⟩
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    refine ⟨r.valuation, ?_⟩
    -- `p ^ v(r)` is `r` divided by its unit part.
    have hpow : (p : ℤ_[p]) ^ r.valuation = ↑(PadicInt.unitCoeff hr0)⁻¹ * r := by
      rw [eq_comm, Units.inv_mul_eq_iff_eq_mul]
      exact PadicInt.unitCoeff_spec hr0
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow, hpow, mul_smul, ← Submonoid.mk_smul _ hr, hrx,
      smul_zero]

/-- Modulo its `p`-power torsion, a module over `ℤ_p` is torsion-free: the quotient is the quotient
by the whole torsion submodule. -/
noncomputable instance isTorsionFree_quotient_pPowerTorsion {A : Type*} [Ring A] [Module A M]
    [SMul ℤ_[p] A]
    [IsScalarTower ℤ_[p] A M] :
    Module.IsTorsionFree ℤ_[p] (M ⧸ pPowerTorsion p A M) :=
  let e := (Submodule.Quotient.restrictScalarsEquiv ℤ_[p] (pPowerTorsion p A M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ restrictScalars_pPowerTorsion
  e.injective.moduleIsTorsionFree _ (map_smul e)

end TauCeti

end Torsion

section IntegralFunctional

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddCommGroup X] [Module ℤ_[p] X]

/-- A `ℚ_[p]`-valued `ℤ_[p]`-linear map whose values lie in `ℤ_[p]`, as a `ℤ_[p]`-valued
functional. -/
def _root_.LinearMap.padicIntCodRestrict (Φ : X →ₗ[ℤ_[p]] ℚ_[p])
    (h : ∀ x, Φ x ∈ (1 : Submodule ℤ_[p] ℚ_[p])) : Module.Dual ℤ_[p] X where
  toFun x := ⟨Φ x, by
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp (h x)
    rw [← hy]
    exact y.property⟩
  map_add' x y := Subtype.ext (map_add Φ x y)
  map_smul' c x := Subtype.ext (map_smul Φ c x)

@[simp]
theorem _root_.LinearMap.coe_padicIntCodRestrict_apply (Φ : X →ₗ[ℤ_[p]] ℚ_[p])
    (h : ∀ x, Φ x ∈ (1 : Submodule ℤ_[p] ℚ_[p])) (x : X) :
    (Φ.padicIntCodRestrict h x : ℚ_[p]) = Φ x :=
  (rfl)

end TauCeti

end IntegralFunctional

/-! ### Canonical `ℤ_[p]`-module structure on `p`-primary abelian groups -/

section PrimaryModule

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]

/-- **A `p`-adic scalar acts on a `p`-power torsion element through its truncation.** In any
`ℤ_[p]`-module, if `p ^ k • x = 0`, then `a • x = a.appr k • x`. In particular, the `ℤ_[p]`-module
structure on a `p`-primary abelian group is unique. -/
theorem smul_eq_appr_nsmul [Module ℤ_[p] M] (a : ℤ_[p]) {k : ℕ} {x : M} (hx : p ^ k • x = 0) :
    a • x = a.appr k • x := by
  obtain ⟨t, ht⟩ := PadicInt.dvd_sub_appr a k
  have ha : a = (a.appr k : ℤ_[p]) + t * (p : ℤ_[p]) ^ k := by
    rw [mul_comm]
    exact eq_add_of_sub_eq' ht
  conv_lhs => rw [ha]
  rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx,
    smul_zero, add_zero]

end PadicInt

namespace IsAddPGroup

variable {p : ℕ} [Fact p.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- **Every `p`-primary abelian group is canonically a `ℤ_[p]`-module**, where `a : ℤ_[p]` acts on
an element `x` killed by `p ^ k` as `a.appr k • x`. Because `p` is not determined by the type `M`,
this is a reducible definition rather than a global instance; for `AddCommGroup.primaryComponent`,
where `p` is part of the type, it is registered as an instance below. -/
@[instance_reducible]
noncomputable def padicIntModule (hM : IsAddPGroup p M) : Module ℤ_[p] M :=
  letI : SMul ℤ_[p] M := ⟨fun a x ↦ a.appr (hM.exists_pow_nsmul_eq_zero x).choose • x⟩
  { one_smul x := by
      have hx := (hM.exists_pow_nsmul_eq_zero x).choose_spec
      have h1 : (1 : ℤ_[p]).appr (hM.exists_pow_nsmul_eq_zero x).choose ≡
          1 [MOD p ^ (hM.exists_pow_nsmul_eq_zero x).choose] := by
        simpa using PadicInt.appr_natCast_modEq (p := p) 1 (hM.exists_pow_nsmul_eq_zero x).choose
      exact (nsmul_eq_nsmul_of_modEq h1 hx).trans (one_nsmul x)
    mul_smul a b x := by
      have hx := (hM.exists_pow_nsmul_eq_zero x).choose_spec
      have hbx : p ^ (hM.exists_pow_nsmul_eq_zero x).choose •
          (b.appr (hM.exists_pow_nsmul_eq_zero x).choose • x) = 0 := by
        rw [← mul_nsmul, mul_comm, mul_nsmul, hx, nsmul_zero]
      exact (nsmul_eq_nsmul_of_modEq (PadicInt.appr_mul_modEq a b _) hx).trans <| by
        rw [mul_comm, mul_nsmul]
        exact (a.appr_nsmul_eq_appr_nsmul (hM.exists_pow_nsmul_eq_zero _).choose_spec hbx).symm
    smul_zero a := nsmul_zero _
    smul_add a x y := by
      set k := max (hM.exists_pow_nsmul_eq_zero x).choose (hM.exists_pow_nsmul_eq_zero y).choose
      have hkx : p ^ k • x = 0 :=
        TauCeti.pow_smul_eq_zero_of_le (le_max_left _ _)
          (hM.exists_pow_nsmul_eq_zero x).choose_spec
      have hky : p ^ k • y = 0 :=
        TauCeti.pow_smul_eq_zero_of_le (le_max_right _ _)
          (hM.exists_pow_nsmul_eq_zero y).choose_spec
      have hkxy : p ^ k • (x + y) = 0 := by rw [nsmul_add, hkx, hky, add_zero]
      exact (a.appr_nsmul_eq_appr_nsmul
          (hM.exists_pow_nsmul_eq_zero (x + y)).choose_spec hkxy).trans <|
        (nsmul_add _ _ _).trans <| congrArg₂ (· + ·)
          (a.appr_nsmul_eq_appr_nsmul (hM.exists_pow_nsmul_eq_zero x).choose_spec hkx).symm
          (a.appr_nsmul_eq_appr_nsmul (hM.exists_pow_nsmul_eq_zero y).choose_spec hky).symm
    add_smul a b x :=
      (nsmul_eq_nsmul_of_modEq (PadicInt.appr_add_modEq a b _)
        (hM.exists_pow_nsmul_eq_zero x).choose_spec).trans (add_nsmul _ _ _)
    zero_smul x := by
      have h0 : (0 : ℤ_[p]).appr (hM.exists_pow_nsmul_eq_zero x).choose = 0 := by
        simpa using PadicInt.appr_natCast (p := p) 0 (hM.exists_pow_nsmul_eq_zero x).choose
      exact (congrArg (· • x) h0).trans (zero_nsmul x) }

/-- **Every additive homomorphism out of a `p`-primary group into a `ℤ_[p]`-module is
`ℤ_[p]`-linear.** Both sides reduce to multiplication by the natural number `a.appr k` for any `k`
with `p ^ k • x = 0`. -/
theorem map_padicInt_smul [Module ℤ_[p] M] [Module ℤ_[p] N] (hM : IsAddPGroup p M)
    (f : M →+ N) (a : ℤ_[p]) (x : M) : f (a • x) = a • f x := by
  obtain ⟨k, hk⟩ := hM.exists_pow_nsmul_eq_zero x
  have hfx : p ^ k • f x = 0 := by rw [← map_nsmul, hk, map_zero]
  rw [a.smul_eq_appr_nsmul hk, map_nsmul, a.smul_eq_appr_nsmul hfx]

end IsAddPGroup

namespace AddCommGroup.primaryComponent

variable {p : ℕ} {A : Type*} [AddCommGroup A]

/-- The `p`-primary component of an abelian group is an additive `p`-group. -/
theorem isAddPGroup (A : Type*) [AddCommGroup A] (p : ℕ) :
    IsAddPGroup p (AddCommGroup.primaryComponent A p) := fun x ↦
  (AddCommGroup.mem_primaryComponent.mp x.property).imp fun _ hk ↦ Subtype.ext <| by simpa using hk

/-- The `p`-primary component of an abelian group is canonically a `ℤ_[p]`-module. -/
noncomputable instance instModulePadicInt [Fact p.Prime] :
    Module ℤ_[p] (AddCommGroup.primaryComponent A p) :=
  (AddCommGroup.primaryComponent.isAddPGroup A p).padicIntModule

end AddCommGroup.primaryComponent

namespace TauCeti.AddCommGroup

variable {p : ℕ} [Fact p.Prime] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

variable (p) in
/-- **Functoriality of the `p`-primary component as a `ℤ_[p]`-linear map.** Every additive
homomorphism `f : A →+ B` restricts to a `ℤ_[p]`-linear map `A[p^∞] →ₗ[ℤ_[p]] B[p^∞]`. -/
noncomputable def primaryComponentMap (f : A →+ B) :
    AddCommGroup.primaryComponent A p →ₗ[ℤ_[p]] AddCommGroup.primaryComponent B p :=
  let g : AddCommGroup.primaryComponent A p →+ AddCommGroup.primaryComponent B p :=
    (f.comp (AddCommGroup.primaryComponent A p).subtype).codRestrict
      (AddCommGroup.primaryComponent B p) fun x ↦ by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.property
        refine AddCommGroup.mem_primaryComponent.mpr ⟨k, ?_⟩
        rw [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← map_nsmul, hk, map_zero]
  { toAddHom := g.toAddHom
    map_smul' := fun a x ↦
      (AddCommGroup.primaryComponent.isAddPGroup A p).map_padicInt_smul g a x }

@[simp]
theorem coe_primaryComponentMap_apply (f : A →+ B) (x : AddCommGroup.primaryComponent A p) :
    (primaryComponentMap p f x : B) = f (x : A) :=
  (rfl)

@[simp]
theorem primaryComponentMap_id :
    primaryComponentMap p (AddMonoidHom.id A) = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem primaryComponentMap_comp (g : B →+ C) (f : A →+ B) :
    primaryComponentMap p (g.comp f) =
      (primaryComponentMap p g).comp (primaryComponentMap p f) := by
  ext x
  rfl

end TauCeti.AddCommGroup

end PrimaryModule
