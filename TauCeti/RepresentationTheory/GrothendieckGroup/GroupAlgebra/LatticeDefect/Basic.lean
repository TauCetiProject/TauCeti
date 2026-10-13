/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Module.Torsion.Tensor
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.TorsionBy
-- Non-public: `DistribMulActionHom.toIntertwiningMap` is used only in proofs.
import TauCeti.RepresentationTheory.Intertwining

/-!
# Reduction classes and the lattice defect of a `G`-module

Let `G` be a monoid and `k` a commutative ring, typically a field. A representation `ρ` of `G` on an
abelian group `W` has a **reduction** `k ⊗_ℤ W`, with `G` acting on the second factor
(`Representation.baseChange`). When it is finitely generated over `k`, for instance because `W` is
a finitely generated abelian group, it has a class

`TauCeti.reductionK0 k ρ = [k ⊗_ℤ W] ∈ G₀(k[G])`

in the exact Grothendieck group of finitely generated `k[G]`-modules.

For a `G`-module `V` (an abelian group with a distributive `G`-action) and a natural number `ℓ`
such that `V ⧸ ℓV` and the `ℓ`-torsion `V[ℓ]` are finite, the **lattice defect** is

`TauCeti.latticeDefect k G ℓ V = [k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]] ∈ G₀(k[G])`.

Here `V ⧸ ℓV` is `QuotSMulTop ℓ V` and `V[ℓ]` is `Submodule.torsionBy ℤ V ℓ`, with the
`G`-actions `Representation.quotSMulTop` and `Representation.torsionBy`. At `k = 𝔽_ℓ` the defect is
`[V ⧸ ℓV] - [V[ℓ]]`, the invariant of Neukirch–Schmidt–Wingberg (7.3.3).

Its main property is **additivity** (`TauCeti.latticeDefect_add_of_exact`): for a prime `ℓ` and a
short exact sequence `0 → A → B → C → 0` of `G`-modules, the defect of `B` is the sum of the
defects of `A` and `C`. The snake lemma for multiplication by `ℓ` gives the six-term exact
sequence of representations

`0 → A[ℓ] → B[ℓ] → C[ℓ] → A ⧸ ℓA → B ⧸ ℓB → C ⧸ ℓC → 0`

(`Representation.IntertwiningMap.torsionByδ`). Every term is killed by `ℓ`, so tensoring over `ℤ`
with `k` keeps it exact, although `k` need not be flat over `ℤ`
(`TauCeti.lTensor_exact_of_isTorsionBy`). Along a six-term exact sequence of finitely generated
`k[G]`-modules the odd-indexed and even-indexed classes have the same sum
(`TauCeti.exactK0_add_add_eq_add_add_of_exact`), and the six classes regroup into the three
defects. Neither the characteristic of `k` nor finiteness of `G` is used.

## Main definitions

* `TauCeti.reductionK0`: the class in `G₀(k[G])` of the reduction `k ⊗_ℤ W`.
* `TauCeti.latticeDefect`: the class `[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]`.

## Main results

* `TauCeti.reductionK0_congr`: equivalent representations have equal reduction classes.
* `TauCeti.reductionK0_quotSMulTop`: in characteristic `ℓ`, the reduction class of `W ⧸ ℓW` is
  that of `W`.
* `TauCeti.latticeDefect_eq_reductionK0_sub`: in characteristic `ℓ`, the lattice defect is
  `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`.
* `TauCeti.latticeDefect_add_of_exact`: additivity of the lattice defect.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

namespace TauCeti

open Function TensorProduct
open _root_.Representation (IntertwiningMap)
open scoped MonoidAlgebra

-- The `ℤ`-module structures on submodules, quotients and tensor products agree with the canonical
-- one of an abelian group, but not definitionally; prefer the structural ones, as the torsion and
-- reduction representations do.
attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

universe u

variable (k : Type u) [CommRing k] {G : Type u} [Monoid G]

/-! ### The reduction class -/

section Reduction

/-- The module of a reduction `k ⊗_ℤ W` that is finitely generated over `k`, for instance because
`W` is a finitely generated abelian group, is finitely generated over `k[G]`. -/
instance instModuleFiniteAsModuleBaseChange {W : Type u} [AddCommGroup W] [Module ℤ W]
    [Module.Finite k (k ⊗[ℤ] W)] (ρ : Representation ℤ G W) :
    Module.Finite k[G] (Representation.baseChange k ρ).asModule :=
  Module.Finite.of_restrictScalars_finite k k[G] _

variable {W : Type u} [AddCommGroup W] [Module ℤ W] [Module.Finite k (k ⊗[ℤ] W)]

/-- **The reduction class** of a representation `ρ` of `G` on an abelian group `W` whose reduction
`k ⊗_ℤ W` is finitely generated over `k`, for instance because `W` is finitely generated: the class
in `G₀(k[G])` of its scalar extension `k ⊗_ℤ W`, with `G` acting on the second factor. -/
noncomputable def reductionK0 (ρ : Representation ℤ G W) :
    ExactK0 (finiteModulesExactStructure k[G]) :=
  ExactK0.of (FGModuleCat.of k[G] (Representation.baseChange k ρ).asModule)

/-- The reduction class is the class of the `k[G]`-module of the base-changed representation. -/
theorem reductionK0_def (ρ : Representation ℤ G W) :
    reductionK0 k ρ = ExactK0.of (FGModuleCat.of k[G] (Representation.baseChange k ρ).asModule) :=
  (rfl)

/-- Equivalent scalar extensions have equal reduction classes. -/
theorem reductionK0_congr_baseChange {W' : Type u} [AddCommGroup W'] [Module ℤ W']
    [Module.Finite k (k ⊗[ℤ] W')] {ρ : Representation ℤ G W} {σ : Representation ℤ G W'}
    (e : (Representation.baseChange k ρ).Equiv (Representation.baseChange k σ)) :
    reductionK0 k ρ = reductionK0 k σ := by
  rw [reductionK0_def, reductionK0_def]
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso

/-- Equivalent representations have equal reduction classes. -/
theorem reductionK0_congr {W' : Type u} [AddCommGroup W'] [Module ℤ W']
    [Module.Finite k (k ⊗[ℤ] W')]
    {ρ : Representation ℤ G W} {σ : Representation ℤ G W'} (e : ρ.Equiv σ) :
    reductionK0 k ρ = reductionK0 k σ :=
  reductionK0_congr_baseChange k (e.baseChange k)

/-- The reduction class of a zero module is zero. -/
@[simp]
theorem reductionK0_eq_zero_of_subsingleton [Subsingleton W] (ρ : Representation ℤ G W) :
    reductionK0 k ρ = 0 := by
  have : Subsingleton (Representation.baseChange k ρ).asModule :=
    (Representation.baseChange k ρ).asModuleEquiv.injective.subsingleton
  exact ExactK0.of_eq_zero_of_isZero <| CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero
    (ModuleCat.isFG k[G]).ι _
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of k[G] (Representation.baseChange k ρ).asModule))

end Reduction

/-- **The reduction of `W ⧸ ℓW` is that of `W`** in characteristic `ℓ`: the reduction classes of
`ρ.quotSMulTop ℓ` and of `ρ` agree. Here `k ⊗_ℤ W` is finitely generated over `k` as soon as
`k ⊗_ℤ (W ⧸ ℓW)` is, even when `W` is not. -/
theorem reductionK0_quotSMulTop (ℓ : ℕ) [CharP k ℓ] {W : Type u} [AddCommGroup W] [Module ℤ W]
    [Module.Finite k (k ⊗[ℤ] QuotSMulTop (ℓ : ℤ) W)] (ρ : Representation ℤ G W) :
    haveI : Module.Finite k (k ⊗[ℤ] W) :=
      Module.Finite.equiv
        (ρ.baseChangeQuotSMulTopEquiv (A := k) (r := (ℓ : ℤ)) (by simp)).symm.toLinearEquiv
    reductionK0 k (ρ.quotSMulTop ℓ) = reductionK0 k ρ :=
  haveI : Module.Finite k (k ⊗[ℤ] W) :=
    Module.Finite.equiv
      (ρ.baseChangeQuotSMulTopEquiv (A := k) (r := (ℓ : ℤ)) (by simp)).symm.toLinearEquiv
  ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv
    (ρ.baseChangeQuotSMulTopEquiv (by simp)).symm).toFGModuleCatIso

/-! ### The six-term sequence of reductions -/

section SixTerm

variable {W W' : Type u} [AddCommGroup W] [Module ℤ W] [AddCommGroup W'] [Module ℤ W']

/-- The module `k ⊗_ℤ W` of the reduction of a representation `ρ` on `W`. -/
private abbrev reductionModule (ρ : Representation ℤ G W) : Type u :=
  (Representation.baseChange k ρ).asModule

/-- The `k[G]`-linear map between the reductions induced by an intertwining map. -/
private noncomputable abbrev reductionLinearMap {ρ : Representation ℤ G W}
    {σ : Representation ℤ G W'} (f : IntertwiningMap ρ σ) :
    reductionModule k ρ →ₗ[k[G]] reductionModule k σ :=
  IntertwiningMap.equivLinearMapAsModule _ _ (f.baseChange k)

private theorem coe_reductionLinearMap {ρ : Representation ℤ G W} {σ : Representation ℤ G W'}
    (f : IntertwiningMap ρ σ) : ⇑(reductionLinearMap k f) = f.toLinearMap.lTensor k := by
  -- `equivLinearMapAsModule` keeps the underlying function of an intertwining map
  have h : ⇑(reductionLinearMap k f) = ⇑(f.baseChange k).toLinearMap := rfl
  rw [h, IntertwiningMap.toLinearMap_baseChange, LinearMap.baseChange_eq_ltensor]

variable (ℓ : ℕ) [Fact ℓ.Prime] {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module ℤ V₁]
  [AddCommGroup V₂] [Module ℤ V₂] [AddCommGroup V₃] [Module ℤ V₃] {ρ₁ : Representation ℤ G V₁}
  {ρ₂ : Representation ℤ G V₂} {ρ₃ : Representation ℤ G V₃} {f : IntertwiningMap ρ₁ ρ₂}
  {g : IntertwiningMap ρ₂ ρ₃}

/-- **The Euler relation of the reduced torsion–reduction sequence.** For a short exact sequence
`0 → V₁ → V₂ → V₃ → 0` of representations on abelian groups, tensoring the six-term sequence
`0 → V₁[ℓ] → V₂[ℓ] → V₃[ℓ] → V₁ ⧸ ℓV₁ → V₂ ⧸ ℓV₂ → V₃ ⧸ ℓV₃ → 0` with `k` keeps it exact, since
all its terms are killed by `ℓ`; so its odd-indexed and even-indexed reduction classes have the
same sum. -/
private theorem reductionK0_six_term (hfg : Exact f g) (hf : Injective f) (hg : Surjective g)
    [Module.Finite ℤ (Submodule.torsionBy ℤ V₁ ℓ)] [Module.Finite ℤ (Submodule.torsionBy ℤ V₂ ℓ)]
    [Module.Finite ℤ (Submodule.torsionBy ℤ V₃ ℓ)] [Module.Finite ℤ (QuotSMulTop (ℓ : ℤ) V₁)]
    [Module.Finite ℤ (QuotSMulTop (ℓ : ℤ) V₂)] [Module.Finite ℤ (QuotSMulTop (ℓ : ℤ) V₃)] :
    reductionK0 k (ρ₁.torsionBy ℓ) + reductionK0 k (ρ₃.torsionBy ℓ) +
        reductionK0 k (ρ₂.quotSMulTop ℓ) =
      reductionK0 k (ρ₂.torsionBy ℓ) + reductionK0 k (ρ₁.quotSMulTop ℓ) +
        reductionK0 k (ρ₃.quotSMulTop ℓ) := by
  have htors {M : Type u} [AddCommGroup M] [Module ℤ M] :
      Module.IsTorsionBy ℤ (Submodule.torsionBy ℤ M ℓ) (ℓ : ℤ) :=
    Submodule.torsionBy_isTorsionBy _
  -- Exactness of each of the five reduced maps, from the tensored snake sequence.
  have h₁ : Injective (reductionLinearMap k (f.torsionBy ℓ)) := by
    rw [coe_reductionLinearMap, IntertwiningMap.toLinearMap_torsionBy]
    exact LinearMap.lTensor_injective_of_isTorsionBy k _ ℓ (injective_torsionByMap hf) htors
  have h₁₂ : Exact (reductionLinearMap k (f.torsionBy ℓ))
      (reductionLinearMap k (g.torsionBy ℓ)) := by
    rw [coe_reductionLinearMap, coe_reductionLinearMap, IntertwiningMap.toLinearMap_torsionBy,
      IntertwiningMap.toLinearMap_torsionBy]
    exact lTensor_exact_of_isTorsionBy k ℓ (exact_torsionByMap hfg hf) htors
  have h₂₃ : Exact (reductionLinearMap k (g.torsionBy ℓ))
      (reductionLinearMap k (IntertwiningMap.torsionByδ (ℓ : ℤ) hfg hf hg)) := by
    rw [coe_reductionLinearMap, coe_reductionLinearMap, IntertwiningMap.toLinearMap_torsionBy,
      IntertwiningMap.toLinearMap_torsionByδ]
    exact lTensor_exact_torsionByMap_torsionByδ k ℓ hfg hf hg
  have h₃₄ : Exact (reductionLinearMap k (IntertwiningMap.torsionByδ (ℓ : ℤ) hfg hf hg))
      (reductionLinearMap k (f.quotSMulTop ℓ)) := by
    rw [coe_reductionLinearMap, coe_reductionLinearMap, IntertwiningMap.toLinearMap_torsionByδ,
      IntertwiningMap.toLinearMap_quotSMulTop]
    exact lTensor_exact_torsionByδ_quotSMulTop_map k ℓ hfg hf hg
  have h₄₅ : Exact (reductionLinearMap k (f.quotSMulTop ℓ))
      (reductionLinearMap k (g.quotSMulTop ℓ)) := by
    rw [coe_reductionLinearMap, coe_reductionLinearMap, IntertwiningMap.toLinearMap_quotSMulTop,
      IntertwiningMap.toLinearMap_quotSMulTop]
    exact lTensor_exact k (QuotSMulTop.map_exact _ hfg hg) (QuotSMulTop.map_surjective _ hg)
  have h₅ : Surjective (reductionLinearMap k (g.quotSMulTop ℓ)) := by
    rw [coe_reductionLinearMap, IntertwiningMap.toLinearMap_quotSMulTop]
    exact LinearMap.lTensor_surjective k (QuotSMulTop.map_surjective _ hg)
  -- The module types are given explicitly: the instances of `Representation.asModule` used by
  -- `reductionLinearMap` differ syntactically from those `FGModuleCat.of` asks for.
  exact exactK0_add_add_eq_add_add_of_exact (R := k[G])
    (M₁ := reductionModule k (ρ₁.torsionBy ℓ)) (M₂ := reductionModule k (ρ₂.torsionBy ℓ))
    (M₃ := reductionModule k (ρ₃.torsionBy ℓ)) (M₄ := reductionModule k (ρ₁.quotSMulTop ℓ))
    (M₅ := reductionModule k (ρ₂.quotSMulTop ℓ)) (M₆ := reductionModule k (ρ₃.quotSMulTop ℓ))
    h₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅

end SixTerm

/-! ### The lattice defect -/

section Defect

variable (G) (ℓ : ℕ)

/-- **The lattice defect** `[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]` of a `G`-module `V` with `V ⧸ ℓV`
and `V[ℓ]` finite, in `G₀(k[G])`. At `k = 𝔽_ℓ` it is `[V ⧸ ℓV] - [V[ℓ]]`; it is additive in short
exact sequences (`TauCeti.latticeDefect_add_of_exact`). -/
noncomputable def latticeDefect (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Finite (QuotSMulTop (ℓ : ℤ) V)] [Finite (Submodule.torsionBy ℤ V ℓ)] :
    ExactK0 (finiteModulesExactStructure k[G]) :=
  haveI := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  haveI := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ V ℓ)
  reductionK0 k ((Representation.ofDistribMulAction ℤ G V).quotSMulTop ℓ) -
    reductionK0 k ((Representation.ofDistribMulAction ℤ G V).torsionBy ℓ)

/-- The lattice defect is the difference of the reduction classes of `V ⧸ ℓV` and of `V[ℓ]`. -/
theorem latticeDefect_def (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Finite (QuotSMulTop (ℓ : ℤ) V)] [Finite (Submodule.torsionBy ℤ V ℓ)] :
    haveI := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
    haveI := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ V ℓ)
    latticeDefect k G ℓ V =
      reductionK0 k ((Representation.ofDistribMulAction ℤ G V).quotSMulTop ℓ) -
        reductionK0 k ((Representation.ofDistribMulAction ℤ G V).torsionBy ℓ) :=
  (rfl)

/-- **The lattice defect is `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`** in characteristic `ℓ`: the reduction of
`V ⧸ ℓV` in the definition of `TauCeti.latticeDefect` may be replaced by the reduction of `V`
itself, which is then finitely generated over `k`
(`TauCeti.finite_baseChange_of_finite_quotSMulTop`). -/
theorem latticeDefect_eq_reductionK0_sub [CharP k ℓ] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite (QuotSMulTop (ℓ : ℤ) V)]
    [Finite (Submodule.torsionBy ℤ V ℓ)] :
    haveI := finite_baseChange_of_finite_quotSMulTop k ℓ V
    haveI := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ V ℓ)
    latticeDefect k G ℓ V = reductionK0 k (Representation.ofDistribMulAction ℤ G V) -
      reductionK0 k ((Representation.ofDistribMulAction ℤ G V).torsionBy ℓ) := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  rw [latticeDefect_def, reductionK0_quotSMulTop k ℓ]

/-- **Additivity of the lattice defect** (Neukirch–Schmidt–Wingberg (7.3.3)): for a short exact
sequence `0 → A → B → C → 0` of `G`-modules whose reductions modulo `ℓ` and `ℓ`-torsion are finite,
the defect of `B` is the sum of the defects of `A` and `C`. -/
theorem latticeDefect_add_of_exact [Fact ℓ.Prime] {A B C : Type u} [AddCommGroup A]
    [DistribMulAction G A] [AddCommGroup B] [DistribMulAction G B] [AddCommGroup C]
    [DistribMulAction G C] (f : A →+[G] B) (g : B →+[G] C) (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g)
    [Finite (QuotSMulTop (ℓ : ℤ) A)] [Finite (Submodule.torsionBy ℤ A ℓ)]
    [Finite (QuotSMulTop (ℓ : ℤ) B)] [Finite (Submodule.torsionBy ℤ B ℓ)]
    [Finite (QuotSMulTop (ℓ : ℤ) C)] [Finite (Submodule.torsionBy ℤ C ℓ)] :
    latticeDefect k G ℓ B = latticeDefect k G ℓ A + latticeDefect k G ℓ C := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) A)
  have := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ A ℓ)
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) B)
  have := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ B ℓ)
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) C)
  have := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ C ℓ)
  have key := reductionK0_six_term k ℓ (f := f.toIntertwiningMap)
    (g := g.toIntertwiningMap)
    (by simpa only [DistribMulActionHom.coe_toIntertwiningMap] using hfg)
    (by simpa only [DistribMulActionHom.coe_toIntertwiningMap] using hf)
    (by simpa only [DistribMulActionHom.coe_toIntertwiningMap] using hg)
  rw [latticeDefect_def, latticeDefect_def, latticeDefect_def]
  linear_combination (norm := abel) key

end Defect

end TauCeti
