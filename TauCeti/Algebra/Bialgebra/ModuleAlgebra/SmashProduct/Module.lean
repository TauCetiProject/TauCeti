/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic

/-!
# Modules over the smash product

Let `H` be an `R`-bialgebra and `A` a left `H`-module algebra (`TauCeti.LeftModuleAlgebra R H A`).
Left modules over the smash product `A # H` (`μ.SmashProduct`) correspond bijectively to `R`-modules
equipped with an `A`-action and an `H`-action satisfying the smash-product Leibniz law

`h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`,

and `A # H`-linear maps are `A`-linear maps that commute with the `H`-action.

## Main definitions

* `TauCeti.LeftModuleAlgebra.IsCompatibleAction`: predicate on `R`-compatible `Module A M` and
  `Module H M` instances expressing the smash-product Leibniz law via `SmashCompatible`.
* `TauCeti.LeftModuleAlgebra.IsSmashModule`: compatibility mixin relating `Module A M`,
  `Module H M`, and `Module μ.SmashProduct M` by `(a # h) • m = a • (h • m)`.
* `TauCeti.LeftModuleAlgebra.toEndAlgHom`: the canonical `R`-algebra homomorphism
  `A # H →ₐ[R] Module.End R A` sending `a # h` to `b ↦ a * (h · b)`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.moduleOfCompatible`, `moduleA`, and `moduleH`:
  passage between compatible `(A, H)`-actions and `A # H`-module structures.
* `TauCeti.LeftModuleAlgebra.SmashProduct.CompatibleActionData` and
  `TauCeti.LeftModuleAlgebra.SmashProduct.moduleEquiv`: bijection between `R`-compatible
  `Module μ.SmashProduct M` structures and compatible `(Module A M, Module H M)` pairs.
* `TauCeti.LeftModuleAlgebra.SmashProduct.equivariantLinearMaps` and
  `TauCeti.LeftModuleAlgebra.SmashProduct.linearMapEquiv`: `R`-linear isomorphism between
  `M →ₗ[μ.SmashProduct] N` and the submodule of `H`-equivariant `A`-linear maps `M →ₗ[A] N`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8 and §5.1.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w x y

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-! ### Canonical left `A # H`-action on `A` -/

/-- Left multiplication by `A` and `μ.action` form a `SmashCompatible` pair in `Module.End R A`. -/
theorem smashCompatible_lsmul_action (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible (Algebra.lsmul R R A) μ.action := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  ext b
  simpa [LinearMap.sum_apply] using μ.action_mul_eq_sum (ℛ R h) a b

/-- The canonical `R`-algebra homomorphism `A # H →ₐ[R] Module.End R A` sending `a # h` to
`b ↦ a * (h · b)`. -/
noncomputable def toEndAlgHom (μ : LeftModuleAlgebra R H A) :
    μ.SmashProduct →ₐ[R] Module.End R A :=
  SmashProduct.lift (Algebra.lsmul R R A) μ.action μ.smashCompatible_lsmul_action

@[simp]
theorem toEndAlgHom_smash (μ : LeftModuleAlgebra R H A) (a : A) (h : H) (b : A) :
    μ.toEndAlgHom (μ.smash a h) b = a * μ.action h b := by
  simp [toEndAlgHom]

@[simp]
theorem toEndAlgHom_comp_includeA (μ : LeftModuleAlgebra R H A) :
    μ.toEndAlgHom.comp μ.includeA = Algebra.lsmul R R A :=
  SmashProduct.lift_comp_includeA ..

@[simp]
theorem toEndAlgHom_comp_includeH (μ : LeftModuleAlgebra R H A) :
    μ.toEndAlgHom.comp μ.includeH = μ.action :=
  SmashProduct.lift_comp_includeH ..

theorem toEndAlgHom_includeA (μ : LeftModuleAlgebra R H A) (a b : A) :
    μ.toEndAlgHom (μ.includeA a) b = a * b := by
  simp

theorem toEndAlgHom_includeH (μ : LeftModuleAlgebra R H A) (h : H) (b : A) :
    μ.toEndAlgHom (μ.includeH h) b = μ.action h b := by
  simp

/-! ### Compatible `A`- and `H`-actions -/

/-- Predicate expressing that `R`-compatible `A`- and `H`-module structures on `M` satisfy the
smash-product Leibniz law `h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`, formulated without choosing a
coproduct representation. -/
@[mk_iff]
class IsCompatibleAction (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] : Prop where
  /-- The `A`-action and `H`-action form a `SmashCompatible` pair in `Module.End R M`. -/
  smashCompatible : μ.SmashCompatible (Algebra.lsmul R (A := A) R M) (Algebra.lsmul R (A := H) R M)

/-- The smash-product Leibniz law in any finite representation of `comul h`. -/
theorem IsCompatibleAction.smul_smul_eq_sum {μ : LeftModuleAlgebra R H A} {M : Type*}
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] [hc : μ.IsCompatibleAction M]
    {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) (m : M) :
    h • (a • m) = ∑ i ∈ r.index, μ.action (r.left i) a • (r.right i • m) := by
  simpa [LinearMap.sum_apply] using DFunLike.congr_fun (hc.smashCompatible.mul_eq_sum r a) m

/-- Characterization of `IsCompatibleAction` using a family of finite coproduct representations. -/
theorem isCompatibleAction_iff_sum (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] {ι : H → Type*} (r : ∀ h, Coalgebra.Repr R h (ι h)) :
    μ.IsCompatibleAction M ↔ ∀ h a (m : M),
      h • (a • m) = ∑ i ∈ (r h).index, μ.action ((r h).left i) a • ((r h).right i • m) := by
  rw [isCompatibleAction_iff, μ.smashCompatible_iff_sum _ _ r]
  refine ⟨fun hf h a m => by simpa [LinearMap.sum_apply] using DFunLike.congr_fun (hf h a) m,
    fun hf h a => ?_⟩
  ext m
  simpa [LinearMap.sum_apply] using hf h a m

/-- Compatibility mixin relating `Module A M`, `Module H M`, and `Module μ.SmashProduct M` by
`(a # h) • m = a • (h • m)`. -/
class IsSmashModule (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module A M] [Module H M] [Module μ.SmashProduct M] : Prop where
  /-- Pure smash elements act as `H` followed by `A`. -/
  smash_smul : ∀ (a : A) (h : H) (m : M), μ.smash a h • m = a • (h • m)

namespace IsSmashModule

attribute [simp] smash_smul

variable {μ : LeftModuleAlgebra R H A} {M : Type x}
  [AddCommMonoid M] [Module A M] [Module H M] [Module μ.SmashProduct M] [μ.IsSmashModule M]

theorem includeA_smul (a : A) (m : M) : μ.includeA a • m = a • m := by
  simp

theorem includeH_smul (h : H) (m : M) : μ.includeH h • m = h • m := by
  simp

/-- An `R`-compatible `IsSmashModule` satisfies `IsCompatibleAction`. -/
theorem toIsCompatibleAction [Module R M] [IsScalarTower R A M] [IsScalarTower R H M] :
    μ.IsCompatibleAction M := by
  rw [μ.isCompatibleAction_iff_sum M (ℛ R)]
  intro h a m
  calc h • (a • m)
      = μ.includeH h • (μ.includeA a • m) := by rw [includeH_smul, includeA_smul]
    _ = (μ.includeH h * μ.includeA a) • m := (mul_smul _ _ _).symm
    _ = (∑ i ∈ (ℛ R h).index,
          μ.includeA (μ.action ((ℛ R h).left i) a) * μ.includeH ((ℛ R h).right i)) • m := by
          rw [μ.includeH_mul_includeA_eq_sum (ℛ R h) a]
    _ = ∑ i ∈ (ℛ R h).index, μ.action ((ℛ R h).left i) a • ((ℛ R h).right i • m) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_smul, includeA_smul, includeH_smul]

end IsSmashModule

namespace SmashProduct

section ModuleEquivalence

variable (μ : LeftModuleAlgebra R H A) (M : Type x)

/-- The `R`-algebra homomorphism `A # H →ₐ[R] Module.End R M` induced by compatible `A`- and
`H`-actions on `M`. -/
noncomputable def lsmulAlgHom [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [hc : μ.IsCompatibleAction M] : μ.SmashProduct →ₐ[R] Module.End R M :=
  lift (Algebra.lsmul R (A := A) R M) (Algebra.lsmul R (A := H) R M) hc.smashCompatible

@[simp]
theorem lsmulAlgHom_smash [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] (a : A) (h : H) (m : M) :
    lsmulAlgHom μ M (μ.smash a h) m = a • (h • m) := by
  simp [lsmulAlgHom]

/-- Left `A # H`-module structure on `M` assembled from compatible `A`- and `H`-actions. -/
@[instance_reducible]
noncomputable def moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] : Module μ.SmashProduct M :=
  Module.compHom M (lsmulAlgHom μ M).toRingHom

theorem isScalarTower_moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    let _ := moduleOfCompatible μ M
    IsScalarTower R μ.SmashProduct M := by
  let _ := moduleOfCompatible μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change lsmulAlgHom μ M (algebraMap R μ.SmashProduct r) m = r • m
  rw [AlgHom.commutes]
  rfl

theorem isSmashModule_moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    let _ := moduleOfCompatible μ M
    μ.IsSmashModule M := by
  let _ := moduleOfCompatible μ M
  exact ⟨fun a h m => lsmulAlgHom_smash μ M a h m⟩

/-- Restriction of scalars of an `A # H`-module along `includeA : A →ₐ[R] A # H`. -/
@[instance_reducible]
noncomputable def moduleA [AddCommMonoid M] [Module μ.SmashProduct M] : Module A M :=
  Module.compHom M μ.includeA.toRingHom

/-- Restriction of scalars of an `A # H`-module along `includeH : H →ₐ[R] A # H`. -/
@[instance_reducible]
noncomputable def moduleH [AddCommMonoid M] [Module μ.SmashProduct M] : Module H M :=
  Module.compHom M μ.includeH.toRingHom

theorem isSmashModule_moduleA_moduleH [AddCommMonoid M] [Module μ.SmashProduct M] :
    let _ := moduleA μ M
    let _ := moduleH μ M
    μ.IsSmashModule M := by
  let _ := moduleA μ M
  let _ := moduleH μ M
  refine ⟨fun a h m => ?_⟩
  change μ.smash a h • m = μ.includeA a • (μ.includeH h • m)
  rw [← mul_smul, μ.includeA_mul_includeH]

theorem isScalarTower_moduleA [AddCommMonoid M] [Module R M]
    [Module μ.SmashProduct M] [IsScalarTower R μ.SmashProduct M] :
    let _ := moduleA μ M
    IsScalarTower R A M := by
  let _ := moduleA μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change μ.includeA (algebraMap R A r) • m = r • m
  rw [AlgHom.commutes, algebraMap_smul]

theorem isScalarTower_moduleH [AddCommMonoid M] [Module R M]
    [Module μ.SmashProduct M] [IsScalarTower R μ.SmashProduct M] :
    let _ := moduleH μ M
    IsScalarTower R H M := by
  let _ := moduleH μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change μ.includeH (algebraMap R H r) • m = r • m
  rw [AlgHom.commutes, algebraMap_smul]

/-- Bundled data of `R`-compatible `Module A M` and `Module H M` structures satisfying
`μ.IsCompatibleAction M`. -/
structure CompatibleActionData [AddCommMonoid M] [Module R M] where
  /-- The underlying `A`-module structure on `M`. -/
  moduleA : Module A M
  /-- `R`-compatibility of `moduleA`. -/
  towerA : @IsScalarTower R A M _ moduleA.toSMul _
  /-- The underlying `H`-module structure on `M`. -/
  moduleH : Module H M
  /-- `R`-compatibility of `moduleH`. -/
  towerH : @IsScalarTower R H M _ moduleH.toSMul _
  /-- The smash-product Leibniz law between `moduleA` and `moduleH`. -/
  compatible : @IsCompatibleAction R H A _ _ _ _ _ μ M _ _ moduleA towerA moduleH towerH

@[ext]
theorem CompatibleActionData.ext {μ : LeftModuleAlgebra R H A} {M : Type x}
    [AddCommMonoid M] [Module R M] {d₁ d₂ : CompatibleActionData μ M}
    (hA : ∀ (a : A) (m : M),
      (let _ := d₁.moduleA; a • m) = (let _ := d₂.moduleA; a • m))
    (hH : ∀ (h : H) (m : M),
      (let _ := d₁.moduleH; h • m) = (let _ := d₂.moduleH; h • m)) :
    d₁ = d₂ := by
  have hmA : d₁.moduleA = d₂.moduleA := Module.ext' _ _ hA
  have hmH : d₁.moduleH = d₂.moduleH := Module.ext' _ _ hH
  cases d₁; cases d₂; cases hmA; cases hmH
  rfl

private noncomputable def ofSmashModule [AddCommMonoid M] [Module R M]
    (m : { m : Module μ.SmashProduct M // @IsScalarTower R μ.SmashProduct M _ m.toSMul _ }) :
    CompatibleActionData μ M :=
  let _ : Module μ.SmashProduct M := m.1
  let _ : IsScalarTower R μ.SmashProduct M := m.2
  let mA := moduleA μ M
  let tA := isScalarTower_moduleA μ M
  let mH := moduleH μ M
  let tH := isScalarTower_moduleH μ M
  let _ := isSmashModule_moduleA_moduleH μ M
  ⟨mA, tA, mH, tH, IsSmashModule.toIsCompatibleAction⟩

private noncomputable def toSmashModule [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) :
    { m : Module μ.SmashProduct M // @IsScalarTower R μ.SmashProduct M _ m.toSMul _ } :=
  let _ := d.moduleA
  let _ := d.towerA
  let _ := d.moduleH
  let _ := d.towerH
  let _ := d.compatible
  ⟨moduleOfCompatible μ M, isScalarTower_moduleOfCompatible μ M⟩

private theorem toSmashModule_ofSmashModule [AddCommMonoid M] [Module R M]
    (m : { m : Module μ.SmashProduct M // @IsScalarTower R μ.SmashProduct M _ m.toSMul _ }) :
    toSmashModule μ M (ofSmashModule μ M m) = m := by
  rcases m with ⟨m, hm⟩
  let _ : Module μ.SmashProduct M := m
  let _ : IsScalarTower R μ.SmashProduct M := hm
  let mA := moduleA μ M
  let tA := isScalarTower_moduleA μ M
  let mH := moduleH μ M
  let tH := isScalarTower_moduleH μ M
  have hs := isSmashModule_moduleA_moduleH μ M
  have hc : @IsCompatibleAction R H A _ _ _ _ _ μ M _ _ mA tA mH tH :=
    @IsSmashModule.toIsCompatibleAction R H A _ _ _ _ _ μ M _ mA mH m hs _ tA tH
  have hF : @lsmulAlgHom R H A _ _ _ _ _ μ M _ _ mA tA mH tH hc = Algebra.lsmul R R M := by
    ext a x
    · simp only [AlgHom.comp_apply, lsmulAlgHom, lift_includeA, Algebra.lsmul_coe]
      exact (IsSmashModule.includeA_smul (μ := μ) a x).symm
    · simp only [AlgHom.comp_apply, lsmulAlgHom, lift_includeH, Algebra.lsmul_coe]
      exact (IsSmashModule.includeH_smul (μ := μ) a x).symm
  exact Subtype.ext <| Module.ext' _ m fun z x =>
    DFunLike.congr_fun (DFunLike.congr_fun hF z) x

private theorem ofSmashModule_toSmashModule [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) :
    ofSmashModule μ M (toSmashModule μ M d) = d := by
  let _ := d.moduleA
  let _ := d.towerA
  let _ := d.moduleH
  let _ := d.towerH
  let _ := d.compatible
  refine CompatibleActionData.ext (fun a x => ?_) (fun h x => ?_)
  · change lsmulAlgHom μ M (μ.includeA a) x = a • x
    simp [lsmulAlgHom]
  · change lsmulAlgHom μ M (μ.includeH h) x = h • x
    simp [lsmulAlgHom]

/-- Bijection between `R`-compatible left `A # H`-module structures on `M` and compatible pairs of
`R`-compatible `A`- and `H`-module structures on `M`. -/
noncomputable def moduleEquiv [AddCommMonoid M] [Module R M] :
    { m : Module μ.SmashProduct M // @IsScalarTower R μ.SmashProduct M _ m.toSMul _ } ≃
      CompatibleActionData μ M where
  toFun := ofSmashModule μ M
  invFun := toSmashModule μ M
  left_inv := toSmashModule_ofSmashModule μ M
  right_inv := ofSmashModule_toSmashModule μ M

end ModuleEquivalence

/-! ### `A # H`-linear maps -/

section LinearMaps

section EquivariantSubmodule

omit [Bialgebra R H]

variable (R H A) (M : Type x) (N : Type y)
  [AddCommMonoid M] [Module A M] [Module H M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]
  [Module H N] [SMulCommClass R H N]

/-- The `R`-submodule of `M →ₗ[A] N` consisting of `H`-equivariant `A`-linear maps. -/
def equivariantLinearMaps : Submodule R (M →ₗ[A] N) where
  carrier := { f : M →ₗ[A] N | ∀ (h : H) (m : M), f (h • m) = h • f m }
  zero_mem' _ _ := by simp
  add_mem' hf hg h m := by simp [hf h m, hg h m, smul_add]
  smul_mem' r _ hf h m := by simp [hf h m, smul_comm r h]

@[simp]
theorem mem_equivariantLinearMaps {R : Type u} {H : Type v} {A : Type w}
    [CommSemiring R] [Semiring H] [Semiring A] [Algebra R A]
    {M : Type x} {N : Type y}
    [AddCommMonoid M] [Module A M] [Module H M]
    [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module H N] [SMulCommClass R H N] (f : M →ₗ[A] N) :
    f ∈ equivariantLinearMaps R H A M N ↔ ∀ (h : H) (m : M), f (h • m) = h • f m :=
  Iff.rfl

end EquivariantSubmodule

variable {μ : LeftModuleAlgebra R H A} {M : Type x} {N : Type y}
  [AddCommMonoid M] [Module A M] [Module H M] [Module μ.SmashProduct M] [μ.IsSmashModule M]
  [AddCommMonoid N] [Module A N] [Module H N] [Module μ.SmashProduct N] [μ.IsSmashModule N]

/-- Every `A # H`-linear map is `A`-linear. -/
def restrictScalarsLinearMapA (f : M →ₗ[μ.SmashProduct] N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' a m := by
    rw [← IsSmashModule.includeA_smul (μ := μ), f.map_smul, IsSmashModule.includeA_smul]
    rfl

@[simp]
theorem restrictScalarsLinearMapA_apply (f : M →ₗ[μ.SmashProduct] N) (m : M) :
    restrictScalarsLinearMapA f m = f m :=
  (rfl)

/-- Every `A # H`-linear map commutes with the `H`-action. -/
theorem map_smulH_of_smashLinear (f : M →ₗ[μ.SmashProduct] N) (h : H) (m : M) :
    f (h • m) = h • f m := by
  rw [← IsSmashModule.includeH_smul (μ := μ), f.map_smul, IsSmashModule.includeH_smul]

/-- An `H`-equivariant `A`-linear map upgrades to an `A # H`-linear map. -/
def mkLinearMap (f : M →ₗ[A] N) (hf : ∀ (h : H) (m : M), f (h • m) = h • f m) :
    M →ₗ[μ.SmashProduct] N where
  toFun := f
  map_add' := f.map_add
  map_smul' z m := by
    induction z using SmashProduct.inductionOn with
    | smash a h =>
      simp only [RingHom.id_apply, IsSmashModule.smash_smul, f.map_smul, hf]
    | add x y hx hy =>
      simp only [RingHom.id_apply] at hx hy ⊢
      rw [add_smul, map_add, hx, hy, add_smul]

@[simp]
theorem mkLinearMap_apply (f : M →ₗ[A] N)
    (hf : ∀ (h : H) (m : M), f (h • m) = h • f m) (m : M) :
    mkLinearMap (μ := μ) f hf m = f m :=
  (rfl)

variable (R μ M N) in
/-- `R`-linear equivalence between `A # H`-linear maps `M →ₗ[μ.SmashProduct] N` and
`H`-equivariant `A`-linear maps `M →ₗ[A] N`. -/
def linearMapEquiv [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R μ.SmashProduct N] :
    (M →ₗ[μ.SmashProduct] N) ≃ₗ[R] equivariantLinearMaps R H A M N where
  toFun f := ⟨restrictScalarsLinearMapA f, map_smulH_of_smashLinear f⟩
  invFun f := mkLinearMap f.1 f.2
  left_inv _ := LinearMap.ext fun _ => rfl
  right_inv _ := Subtype.ext <| LinearMap.ext fun _ => rfl
  map_add' _ _ := Subtype.ext <| LinearMap.ext fun _ => rfl
  map_smul' _ _ := Subtype.ext <| LinearMap.ext fun _ => rfl

@[simp]
theorem linearMapEquiv_apply_coe [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R μ.SmashProduct N] (f : M →ₗ[μ.SmashProduct] N) (m : M) :
    ((linearMapEquiv R μ M N f : M →ₗ[A] N) m) = f m :=
  (rfl)

@[simp]
theorem linearMapEquiv_symm_apply [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R μ.SmashProduct N] (f : equivariantLinearMaps R H A M N) (m : M) :
    (linearMapEquiv R μ M N).symm f m = (f : M →ₗ[A] N) m :=
  (rfl)

end LinearMaps

end SmashProduct

end LeftModuleAlgebra

end TauCeti
