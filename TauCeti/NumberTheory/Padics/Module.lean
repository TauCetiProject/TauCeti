/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Continuous additive maps between `ℤ_[p]`-modules are `ℤ_[p]`-linear

A continuous additive map `f : E →+ F` between topological `ℤ_[p]`-modules with `F` Hausdorff is
automatically `ℤ_[p]`-linear: for fixed `x`, the continuous maps `c ↦ f (c • x)` and `c ↦ c • f x`
agree on the dense subset `ℕ` of `ℤ_[p]`, and two continuous maps into a Hausdorff space that agree
on a dense set are equal. So the `ℤ_[p]`-module structure of a Hausdorff topological
`ℤ_[p]`-module is determined by its topological group structure, and continuous additive maps and
isomorphisms between such modules can be treated as continuous `ℤ_[p]`-linear ones. Throughout,
the codomain `F` is assumed Hausdorff.

This file adapts `Mathlib/Topology/Instances/RealVectorSpace.lean` (Yury Kudryashov) from `ℝ` to
`ℤ_[p]`: `TauCeti.map_padicInt_smul`, `AddMonoidHom.toPadicIntLinearMap`, and
`AddEquiv.toPadicIntLinearEquiv` are the `ℤ_[p]` counterparts of `map_real_smul`,
`AddMonoidHom.toRealLinearMap`, and `AddEquiv.toRealLinearEquiv`.

In particular the rank of a finite free `ℤ_[p]`-module is a topological invariant: a continuous
additive isomorphism between two such modules preserves `Module.finrank`, and `ℤ_[p] ^ r` and
`ℤ_[p] ^ r'` are topologically isomorphic groups only when `r = r'`.

## Main results

* `TauCeti.map_padicInt_smul`: a continuous additive map between topological `ℤ_[p]`-modules
  with Hausdorff codomain commutes with scalar multiplication by `ℤ_[p]`.
* `AddMonoidHom.toPadicIntLinearMap`, `AddEquiv.toPadicIntLinearEquiv`: the resulting continuous
  `ℤ_[p]`-linear map and continuous `ℤ_[p]`-linear equivalence.
* `AddEquiv.finrank_padicInt_eq`: a continuous additive isomorphism preserves the `ℤ_[p]`-rank.
* `TauCeti.eq_of_continuousMulEquiv_pi_padicInt`: topologically isomorphic groups `ℤ_[p] ^ r` and
  `ℤ_[p] ^ r'` have `r = r'`.
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
