/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.Dimension.Constructions

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

end Torsion
