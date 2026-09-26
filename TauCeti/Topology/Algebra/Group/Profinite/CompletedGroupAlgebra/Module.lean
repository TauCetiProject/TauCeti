/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
public import TauCeti.Topology.Algebra.Module.GroupAction

/-!
# Compact modules over the completed group algebra

Let `Γ` be a compact topological group, `R` a compact topological ring and `M` a compact `R`-module
(`TauCeti.IsCompactModule R M`) with a continuous `R`-linear action of `Γ`. This file extends the
action of `Γ` on `M` to a continuous action of the completed group algebra `R[[Γ]]`, making `M` a
topological `R[[Γ]]`-module in which the group elements `of R Γ γ` act as `γ` does. This is the
structure through which Iwasawa theory and Labute's classification of Demushkin groups study a
compact abelian pro-`p` group with a continuous action of a profinite group: Labute's relation
module `E = X ⧸ (X, X)`, for `X` the kernel of the orientation character on a free pro-`p`
group `F`, is a compact `ℤ_p`-module with a continuous action of `Γ = F ⧸ X` by conjugation, and
its structure as a module over `Λ = ℤ_p[[Γ]]` is the setting of his Theorems 5 and 6.

**The construction.** Let `V ≤ M` be a `Γ`-invariant open submodule. The quotient `M ⧸ V` is a
finite discrete `R`-module on which `Γ` acts through a finite quotient `Γ ⧸ U`, `U` open normal
(`Submodule.quotientActionKernel`), so the group algebra `R[Γ ⧸ U]` acts on `M ⧸ V`, and hence so
does `R[[Γ]]` through its projection onto `R[Γ ⧸ U]`; this is the algebra homomorphism
`completedGroupAlgebra.toQuotientEnd`, and it does not depend on `U`. These actions are compatible
with the factor maps `M ⧸ V → M ⧸ V'`, and since the invariant open submodules form a basis of
neighbourhoods of zero in the compact module `M`, the inverse-limit description of `M` assembles
them into a unique action on `M` itself: `x • m` is the unique element of `M` whose class modulo
every invariant open `V` is `toQuotientEnd x` applied to the class of `m`.

The module structure is a definition taking the compact-module hypothesis as an argument rather
than an instance, in the same way as the `ℤ_p`-module structure `TauCeti.IsProP.module` of an
abelian pro-`p` group; consumers introduce it with `letI := hM.completedGroupAlgebraModule Γ`.

## Main definitions

* `TauCeti.completedGroupAlgebra.toQuotientEnd`: the action of `R[[Γ]]` on the quotient of `M`
  by an invariant submodule on which an open normal subgroup acts trivially.
* `TauCeti.IsCompactModule.completedSMul`: the scalar action of `R[[Γ]]` on a compact module
  with a continuous `Γ`-action.
* `TauCeti.IsCompactModule.completedGroupAlgebraModule`: the resulting `R[[Γ]]`-module structure.

## Main results

* `TauCeti.completedGroupAlgebra.toQuotientEnd_of`,
  `TauCeti.completedGroupAlgebra.toQuotientEnd_eq`,
  `TauCeti.completedGroupAlgebra.factor_toQuotientEnd`,
  `TauCeti.completedGroupAlgebra.continuous_toQuotientEnd`: the level actions extend the action of
  `Γ`, are independent of the open normal subgroup, are compatible with the factor maps, and are
  continuous.
* `TauCeti.IsCompactModule.mkQ_completedSMul`: the defining property of the scalar action, its
  class modulo every invariant open submodule.
* `TauCeti.IsCompactModule.completedSMul_of`, `TauCeti.IsCompactModule.completedSMul_algebraMap`:
  the group elements act as `Γ` does and the scalars of `R` act as scalars.
* `TauCeti.IsCompactModule.isScalarTower_completedGroupAlgebraModule`,
  `TauCeti.IsCompactModule.continuousSMul_completedGroupAlgebraModule`: the module structure is
  compatible with the `R`-module structure and is topological.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 5.1 and 5.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4,
  p. 121.
-/

public section

open Topology

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
  {M : Type w} [AddCommGroup M] [Module R M] [DistribMulAction Γ M] [SMulCommClass Γ R M]
  {V V' : Submodule R M}

namespace completedGroupAlgebra

section Level

variable (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) (U : OpenNormalSubgroup Γ)
  (hU : U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker)

/-- **The level action.** For a `Γ`-invariant submodule `V ≤ M` and an open normal subgroup `U`
of `Γ` acting trivially on `M ⧸ V`, the completed group algebra `R[[Γ]]` acts on `M ⧸ V` through
its projection onto `R[Γ ⧸ U]` and the action of `R[Γ ⧸ U]` on `M ⧸ V` induced by that of
`Γ ⧸ U`. The action does not depend on `U` (`toQuotientEnd_eq`), and a group element acts as it
does on `M ⧸ V` (`toQuotientEnd_of`). -/
noncomputable def toQuotientEnd : completedGroupAlgebra R Γ →ₐ[R] Module.End R (M ⧸ V) :=
  (MonoidAlgebra.lift R (Module.End R (M ⧸ V)) (Γ ⧸ U.toSubgroup)
    (QuotientGroup.lift U.toSubgroup (Submodule.quotientToModuleEnd hV) hU)).comp (proj R Γ U)

/-- The level action, unfolded: the projection to `R[Γ ⧸ U]` followed by the action of the group
algebra on `M ⧸ V`. -/
theorem toQuotientEnd_apply (x : completedGroupAlgebra R Γ) :
    toQuotientEnd hV U hU x = MonoidAlgebra.lift R (Module.End R (M ⧸ V)) (Γ ⧸ U.toSubgroup)
      (QuotientGroup.lift U.toSubgroup (Submodule.quotientToModuleEnd hV) hU) (proj R Γ U x) :=
  (rfl)

/-- A group element of `R[[Γ]]` acts on `M ⧸ V` as the group element does. -/
@[simp]
theorem toQuotientEnd_of (γ : Γ) :
    toQuotientEnd hV U hU (of R Γ γ) = Submodule.quotientToModuleEnd hV γ := by
  rw [toQuotientEnd_apply, proj_of, MonoidAlgebra.lift_single, one_smul, QuotientGroup.lift_mk]

/-- The level actions through `U ≤ U'` agree, because the projections of `R[[Γ]]` are compatible
along `R[Γ ⧸ U] → R[Γ ⧸ U']`. -/
theorem toQuotientEnd_eq_of_le {U U' : OpenNormalSubgroup Γ}
    (hU : U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker) (hUU' : U ≤ U')
    (hU' : U'.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker) :
    toQuotientEnd hV U hU = toQuotientEnd hV U' hU' := by
  refine AlgHom.ext fun x ↦ ?_
  rw [toQuotientEnd_apply, toQuotientEnd_apply, ← mapDomain_mapOfLE_proj hUU' x]
  generalize proj R Γ U x = f
  induction f using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective m
    simp
  | add f g hf hg => simp only [MonoidAlgebra.mapDomain_add, map_add, hf, hg]
  | smul r f hf => simp only [MonoidAlgebra.mapDomain_smul, map_smul, hf]

/-- **Independence of the open normal subgroup.** The level action on `M ⧸ V` is the same for
every open normal subgroup acting trivially on `M ⧸ V`. -/
theorem toQuotientEnd_eq {U U' : OpenNormalSubgroup Γ}
    (hU : U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker)
    (hU' : U'.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker) :
    toQuotientEnd hV U hU = toQuotientEnd hV U' hU' :=
  (toQuotientEnd_eq_of_le hV (inf_le_left.trans hU) inf_le_left hU).symm.trans
    (toQuotientEnd_eq_of_le hV (inf_le_right.trans hU') inf_le_right hU')

/-- **Compatibility with the factor maps.** For invariant `V ≤ V'`, the level actions on `M ⧸ V`
and `M ⧸ V'` commute with the factor map `M ⧸ V → M ⧸ V'`. -/
theorem factor_toQuotientEnd (hV' : ∀ γ : Γ, ∀ x ∈ V', γ • x ∈ V') (h : V ≤ V')
    (x : completedGroupAlgebra R Γ) (y : M ⧸ V) :
    Submodule.factor h (toQuotientEnd hV U hU x y) =
      toQuotientEnd hV' U (hU.trans (by
        simpa only [← MonoidHom.ker_toSubmonoid, Subgroup.toSubmonoid_le] using
          Submodule.mker_quotientToModuleEnd_mono hV hV' h)) x
        (Submodule.factor h y) := by
  rw [toQuotientEnd_apply, toQuotientEnd_apply]
  generalize proj R Γ U x = f
  induction f using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective m
    simp [Submodule.factor_quotientToModuleEnd hV hV' h]
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

/-- The level action as a finite sum over the classes of `Γ ⧸ U`, weighted by the coefficients of
the projection. -/
theorem toQuotientEnd_apply_apply [Fintype (Γ ⧸ U.toSubgroup)] (x : completedGroupAlgebra R Γ)
    (y : M ⧸ V) :
    toQuotientEnd hV U hU x y = ∑ g : Γ ⧸ U.toSubgroup, (proj R Γ U x).coeff g •
      QuotientGroup.lift U.toSubgroup (Submodule.quotientToModuleEnd hV) hU g y := by
  rw [toQuotientEnd_apply, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ fun g ↦ by simp,
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- **Continuity of the level action** for an invariant open submodule `V` of a topological
module over a topological ring: the quotient `M ⧸ V` is discrete, and each coefficient of the
projection is continuous. -/
theorem continuous_toQuotientEnd [TopologicalSpace R] [CompactSpace Γ] [SeparatelyContinuousMul Γ]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M] (hVo : IsOpen (V : Set M)) :
    Continuous fun p : completedGroupAlgebra R Γ × (M ⧸ V) ↦ toQuotientEnd hV U hU p.1 p.2 := by
  have := Submodule.Quotient.discreteTopology_of_isOpen V hVo
  refine continuous_prod_of_discrete_right.2 fun y ↦ ?_
  let _ := Fintype.ofFinite (Γ ⧸ U.toSubgroup)
  simp only [toQuotientEnd_apply_apply]
  refine continuous_finsetSum _ fun g _ ↦ ?_
  generalize QuotientGroup.lift U.toSubgroup (Submodule.quotientToModuleEnd hV) hU g y = c
  induction c using Submodule.Quotient.induction_on with | _ m => ?_
  simp only [← Submodule.Quotient.mk_smul]
  simp only [← Submodule.mkQ_apply]
  exact V.continuous_mkQ.comp ((continuous_coeff_proj R Γ U g).smul continuous_const)

end Level

end completedGroupAlgebra

namespace IsCompactModule

open completedGroupAlgebra

variable [TopologicalSpace R] [CompactSpace R] [CompactSpace Γ] [SeparatelyContinuousMul Γ]
  [TopologicalSpace M] [ContinuousSMul Γ M] (hM : IsCompactModule R M)
include hM

omit [CompactSpace R] [CompactSpace Γ] in
/-- Every invariant open submodule of a compact module admits an open normal subgroup of `Γ`
acting trivially on the quotient. -/
theorem exists_le_ker_quotientToModuleEnd (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V)
    (hVo : IsOpen (V : Set M)) :
    ∃ U : OpenNormalSubgroup Γ, U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker :=
  have := hM.compactSpace
  have := hM.isTopologicalAddGroup
  ⟨Submodule.quotientActionKernel hV hVo, (Submodule.quotientActionKernel_toSubgroup hV hVo).le⟩

omit [SeparatelyContinuousMul Γ] in
variable (Γ) in
/-- **Separation by the invariant open submodules**, for a compact module: two elements that
agree modulo every `Γ`-invariant open submodule are equal. -/
theorem eq_of_forall_invariant_mkQ_eq {m m' : M}
    (h : ∀ V : Submodule R M, IsOpen (V : Set M) → (∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) →
      V.mkQ m = V.mkQ m') : m = m' :=
  have := hM.isTopologicalAddGroup
  have := hM.t2Space
  have := hM.isLinearTopology
  IsLinearTopology.eq_of_forall_invariant_mkQ_eq Γ h

/-- **The inverse-limit construction of the scalar action.** For `x : R[[Γ]]` and `m : M` there
is exactly one element of `M` whose class modulo every `Γ`-invariant open submodule `V` is the
level action of `x` on the class of `m`, for every open normal subgroup `U` acting trivially on
`M ⧸ V`. -/
theorem existsUnique_forall_mkQ_eq_toQuotientEnd (x : completedGroupAlgebra R Γ) (m : M) :
    ∃! n : M, ∀ (V : Submodule R M) (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V), IsOpen (V : Set M) →
      ∀ (U : OpenNormalSubgroup Γ) (hU : U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker),
        V.mkQ n = toQuotientEnd hV U hU x (V.mkQ m) := by
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  -- The invariant core of an open submodule `N` is an invariant open submodule below `N`; the
  -- compatible family is the level action there, pushed forward to `M ⧸ N`.
  have hcore : ∀ N : Submodule R M, ∀ γ : Γ, ∀ x ∈ N.invariantCore Γ, γ • x ∈ N.invariantCore Γ :=
    fun _ γ _ hx ↦ Submodule.smul_mem_invariantCore γ hx
  let K : ∀ N : {N : Submodule R M // IsOpen (N : Set M)}, OpenNormalSubgroup Γ := fun N ↦
    Submodule.quotientActionKernel (hcore N.1) (N.1.isOpen_invariantCore Γ N.2)
  have hK : ∀ N, (K N).toSubgroup ≤ (Submodule.quotientToModuleEnd (hcore N.1)).ker := fun N ↦
    (Submodule.quotientActionKernel_toSubgroup _ _).le
  obtain ⟨n, hn, huniq⟩ := hM.existsUnique_forall_mkQ_eq
    (fun N ↦ Submodule.factor (N.1.invariantCore_le Γ)
      (toQuotientEnd (hcore N.1) (K N) (hK N) x ((N.1.invariantCore Γ).mkQ m)))
    fun N N' h ↦ by
      rw [Submodule.factor_comp_apply,
        ← Submodule.factor_comp_apply (Submodule.invariantCore_mono h) (N'.1.invariantCore_le Γ),
        factor_toQuotientEnd (hcore N.1) (K N) (hK N) (hcore N'.1), Submodule.factor_mk,
        toQuotientEnd_eq (hcore N'.1) _ (hK N')]
  refine ⟨n, fun V hV hVo U hU ↦ ?_, fun n' hn' ↦ huniq n' fun N ↦ ?_⟩
  · rw [hn ⟨V, hVo⟩, factor_toQuotientEnd (hcore V) (K ⟨V, hVo⟩) (hK ⟨V, hVo⟩) hV,
      Submodule.factor_mk, toQuotientEnd_eq hV _ hU]
  · rw [← hn' (N.1.invariantCore Γ) (hcore N.1) (N.1.isOpen_invariantCore Γ N.2) (K N) (hK N),
      Submodule.factor_mk]

/-- **The scalar action of the completed group algebra** on a compact module `M` with a continuous
`R`-linear action of `Γ`: `hM.completedSMul x m` is the unique element of `M` whose class modulo
every `Γ`-invariant open submodule `V` is the level action of `x` on the class of `m`
(`TauCeti.IsCompactModule.mkQ_completedSMul`). It extends the action of `Γ`
(`TauCeti.IsCompactModule.completedSMul_of`), and it is the scalar action of the module structure
`TauCeti.IsCompactModule.completedGroupAlgebraModule`. -/
noncomputable def completedSMul (x : completedGroupAlgebra R Γ) (m : M) : M :=
  (hM.existsUnique_forall_mkQ_eq_toQuotientEnd x m).exists.choose

/-- **The defining property of the scalar action**: modulo a `Γ`-invariant open submodule `V`,
`x • m` is the level action of `x` on the class of `m`, computed through any open normal subgroup
`U` acting trivially on `M ⧸ V`. -/
theorem mkQ_completedSMul (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) (hVo : IsOpen (V : Set M))
    (U : OpenNormalSubgroup Γ) (hU : U.toSubgroup ≤ (Submodule.quotientToModuleEnd hV).ker)
    (x : completedGroupAlgebra R Γ) (m : M) :
    V.mkQ (hM.completedSMul x m) = toQuotientEnd hV U hU x (V.mkQ m) :=
  (hM.existsUnique_forall_mkQ_eq_toQuotientEnd x m).exists.choose_spec V hV hVo U hU

/-- **A group element acts as itself**: `of R Γ γ • m = γ • m`. -/
@[simp]
theorem completedSMul_of (γ : Γ) (m : M) : hM.completedSMul (of R Γ γ) m = γ • m :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    rw [hM.mkQ_completedSMul hV hVo U hU, toQuotientEnd_of, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.quotientToModuleEnd_mk]

/-- **A scalar of `R` acts as a scalar**: `algebraMap R R[[Γ]] r • m = r • m`. -/
@[simp]
theorem completedSMul_algebraMap (r : R) (m : M) :
    hM.completedSMul (algebraMap R (completedGroupAlgebra R Γ) r) m = r • m :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    rw [hM.mkQ_completedSMul hV hVo U hU, AlgHom.commutes, Module.algebraMap_end_apply, map_smul]

variable (Γ) in
/-- The unit of `R[[Γ]]` acts as the identity on `M`. -/
@[simp]
theorem one_completedSMul (m : M) : hM.completedSMul (1 : completedGroupAlgebra R Γ) m = m :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    rw [hM.mkQ_completedSMul hV hVo U hU, map_one, Module.End.one_apply]

/-- Multiplication in `R[[Γ]]` acts by successive scalar actions. -/
theorem mul_completedSMul (x y : completedGroupAlgebra R Γ) (m : M) :
    hM.completedSMul (x * y) m = hM.completedSMul x (hM.completedSMul y m) :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    simp only [hM.mkQ_completedSMul hV hVo U hU, map_mul, Module.End.mul_apply]

/-- Every element of `R[[Γ]]` sends the zero element of `M` to zero. -/
@[simp]
theorem completedSMul_zero (x : completedGroupAlgebra R Γ) : hM.completedSMul x 0 = 0 :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    rw [hM.mkQ_completedSMul hV hVo U hU, map_zero, map_zero]

/-- The action of `R[[Γ]]` distributes over addition in `M`. -/
theorem completedSMul_add (x : completedGroupAlgebra R Γ) (m m' : M) :
    hM.completedSMul x (m + m') = hM.completedSMul x m + hM.completedSMul x m' :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    simp only [hM.mkQ_completedSMul hV hVo U hU, map_add]

/-- The sum of two elements of `R[[Γ]]` acts as the sum of their actions. -/
theorem add_completedSMul (x y : completedGroupAlgebra R Γ) (m : M) :
    hM.completedSMul (x + y) m = hM.completedSMul x m + hM.completedSMul y m :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    simp only [hM.mkQ_completedSMul hV hVo U hU, map_add, LinearMap.add_apply]

variable (Γ) in
/-- The zero element of `R[[Γ]]` acts as zero on `M`. -/
@[simp]
theorem zero_completedSMul (m : M) : hM.completedSMul (0 : completedGroupAlgebra R Γ) m = 0 :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    rw [hM.mkQ_completedSMul hV hVo U hU, map_zero, LinearMap.zero_apply, map_zero]

/-- Scaling an element of `R[[Γ]]` by `r : R` scales its action on `M` by `r`. -/
theorem smul_completedSMul (r : R) (x : completedGroupAlgebra R Γ) (m : M) :
    hM.completedSMul (r • x) m = r • hM.completedSMul x m :=
  hM.eq_of_forall_invariant_mkQ_eq Γ fun V hVo hV ↦ by
    obtain ⟨U, hU⟩ := hM.exists_le_ker_quotientToModuleEnd hV hVo
    simp only [hM.mkQ_completedSMul hV hVo U hU, map_smul, LinearMap.smul_apply]

variable (Γ) in
/-- **A compact module with a continuous `Γ`-action is a module over the completed group
algebra.** The scalar action is `TauCeti.IsCompactModule.completedSMul`, so the group elements
act as `Γ` does. The compact-module hypothesis is an argument rather than an instance; consumers
introduce the structure with `letI := hM.completedGroupAlgebraModule Γ`. -/
@[instance_reducible]
noncomputable def completedGroupAlgebraModule : Module (completedGroupAlgebra R Γ) M where
  smul := hM.completedSMul
  one_smul := hM.one_completedSMul Γ
  mul_smul := hM.mul_completedSMul
  smul_zero := hM.completedSMul_zero
  smul_add := hM.completedSMul_add
  add_smul := hM.add_completedSMul
  zero_smul := hM.zero_completedSMul Γ

/-- The scalar action of `TauCeti.IsCompactModule.completedGroupAlgebraModule` is
`TauCeti.IsCompactModule.completedSMul`. -/
@[simp]
theorem completedGroupAlgebraModule_smul (x : completedGroupAlgebra R Γ) (m : M) :
    letI := hM.completedGroupAlgebraModule Γ
    x • m = hM.completedSMul x m :=
  (rfl)

/-- The `R[[Γ]]`-module structure is compatible with the `R`-module structure. -/
theorem isScalarTower_completedGroupAlgebraModule :
    letI := hM.completedGroupAlgebraModule Γ
    IsScalarTower R (completedGroupAlgebra R Γ) M :=
  letI := hM.completedGroupAlgebraModule Γ
  ⟨hM.smul_completedSMul⟩

/-- **Continuity of the scalar action**: modulo every invariant open submodule it is the level
action, which is continuous. -/
theorem continuous_completedSMul :
    Continuous fun p : completedGroupAlgebra R Γ × M ↦ hM.completedSMul p.1 p.2 := by
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  have := hM.continuousSMul
  have := hM.isLinearTopology
  refine (IsLinearTopology.continuous_iff_forall_invariant_continuous_mkQ Γ R).2
    fun V hVo hV ↦ ?_
  have hK := (Submodule.quotientActionKernel_toSubgroup hV hVo).le
  have h : V.mkQ ∘ (fun p : completedGroupAlgebra R Γ × M ↦ hM.completedSMul p.1 p.2) =
      (fun q : completedGroupAlgebra R Γ × (M ⧸ V) ↦ toQuotientEnd hV _ hK q.1 q.2) ∘
        Prod.map id V.mkQ :=
    funext fun p ↦ hM.mkQ_completedSMul hV hVo _ hK p.1 p.2
  rw [h]
  exact (continuous_toQuotientEnd hV _ hK hVo).comp (continuous_id.prodMap V.continuous_mkQ)

/-- The `R[[Γ]]`-module structure on a compact module is topological. -/
theorem continuousSMul_completedGroupAlgebraModule :
    letI := hM.completedGroupAlgebraModule Γ
    ContinuousSMul (completedGroupAlgebra R Γ) M :=
  letI := hM.completedGroupAlgebraModule Γ
  ⟨hM.continuous_completedSMul⟩

end IsCompactModule

end TauCeti
