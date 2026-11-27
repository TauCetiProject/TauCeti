/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Compatibility
public import TauCeti.Algebra.Module.LinearMap.Equivariant

/-!
# Modules over the smash product

Let `H` be an `R`-bialgebra and `A` a left `H`-module algebra (`TauCeti.LeftModuleAlgebra R H A`).
Left modules over the smash product `A # H` (`SmashProduct μ`) correspond bijectively to `R`-modules
equipped with an `A`-action and an `H`-action satisfying the smash-product Leibniz law

`h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`,

and `A # H`-linear maps are `A`-linear maps that commute with the `H`-action.

## Main definitions

* `TauCeti.LeftModuleAlgebra.IsSmashModule`: compatibility mixin relating `Module A M`,
  `Module H M`, and `Module (SmashProduct μ) M` by `(a # h) • m = a • (h • m)`.
* `TauCeti.LeftModuleAlgebra.toEndAlgHom`: the canonical `R`-algebra homomorphism
  `A # H →ₐ[R] Module.End R A` sending `a # h` to `b ↦ a * (h · b)`.
* `TauCeti.LeftModuleAlgebra.SmashProduct.moduleOfCompatible`, `moduleA`, and `moduleH`:
  passage between compatible `(A, H)`-actions and `A # H`-module structures.
* `TauCeti.LeftModuleAlgebra.SmashProduct.CompatibleActionData` and
  `TauCeti.LeftModuleAlgebra.SmashProduct.moduleEquiv`: bijection between `R`-compatible
  `Module (SmashProduct μ) M` structures and compatible `(Module A M, Module H M)` pairs.
* `TauCeti.LeftModuleAlgebra.SmashProduct.linearMapEquiv`: `R`-linear isomorphism between
  `M →ₗ[SmashProduct μ] N` and the submodule `TauCeti.equivariantLinearMaps R H A M N` of
  `H`-equivariant `A`-linear maps `M →ₗ[A] N`.

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

/-- The canonical `R`-algebra homomorphism `A # H →ₐ[R] Module.End R A` sending `a # h` to
`b ↦ a * (h · b)`. -/
noncomputable def toEndAlgHom (μ : LeftModuleAlgebra R H A) :
    SmashProduct μ →ₐ[R] Module.End R A :=
  SmashProduct.lift (Algebra.lsmul R R A) μ.action μ.smashCompatible_lsmul_action

@[simp]
theorem toEndAlgHom_pure (μ : LeftModuleAlgebra R H A) (a : A) (h : H) (b : A) :
    μ.toEndAlgHom (SmashProduct.pure a h) b = a * μ.action h b := by
  simp [toEndAlgHom]

@[simp]
theorem toEndAlgHom_comp_includeA (μ : LeftModuleAlgebra R H A) :
    μ.toEndAlgHom.comp SmashProduct.includeA = Algebra.lsmul R R A :=
  SmashProduct.lift_comp_includeA ..

@[simp]
theorem toEndAlgHom_comp_includeH (μ : LeftModuleAlgebra R H A) :
    μ.toEndAlgHom.comp SmashProduct.includeH = μ.action :=
  SmashProduct.lift_comp_includeH ..

@[simp]
theorem toEndAlgHom_includeA (μ : LeftModuleAlgebra R H A) (a b : A) :
    μ.toEndAlgHom (SmashProduct.includeA a) b = a * b := by
  simp [toEndAlgHom]

@[simp]
theorem toEndAlgHom_includeH (μ : LeftModuleAlgebra R H A) (h : H) (b : A) :
    μ.toEndAlgHom (SmashProduct.includeH h) b = μ.action h b := by
  simp [toEndAlgHom]

/-! ### Smash-product modules -/

/-- Compatibility mixin relating `Module A M`, `Module H M`, and `Module (SmashProduct μ) M` by
`(a # h) • m = a • (h • m)`. -/
class IsSmashModule (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module A M] [Module H M] [Module (SmashProduct μ) M] : Prop where
  /-- Pure smash elements act as `H` followed by `A`. -/
  pure_smul : ∀ (a : A) (h : H) (m : M), SmashProduct.pure (μ := μ) a h • m = a • (h • m)

namespace IsSmashModule

attribute [simp] pure_smul

variable {μ : LeftModuleAlgebra R H A} {M : Type x}
  [AddCommMonoid M] [Module A M] [Module H M] [Module (SmashProduct μ) M] [μ.IsSmashModule M]

@[simp]
theorem includeA_smul (a : A) (m : M) : SmashProduct.includeA (μ := μ) a • m = a • m := by
  simp [SmashProduct.includeA_eq_pure]

@[simp]
theorem includeH_smul (h : H) (m : M) : SmashProduct.includeH (μ := μ) h • m = h • m := by
  simp [SmashProduct.includeH_eq_pure]

/-- An `R`-compatible `IsSmashModule` satisfies `IsCompatibleAction`. -/
instance toIsCompatibleAction [Module R M] [IsScalarTower R A M] [IsScalarTower R H M] :
    μ.IsCompatibleAction M := by
  rw [μ.isCompatibleAction_iff_sum M (ℛ R)]
  intro h a m
  calc h • (a • m)
      = SmashProduct.includeH (μ := μ) h • (SmashProduct.includeA (μ := μ) a • m) := by
          rw [includeH_smul, includeA_smul]
    _ = (SmashProduct.includeH (μ := μ) h * SmashProduct.includeA a) • m := (mul_smul _ _ _).symm
    _ = (∑ i ∈ (ℛ R h).index,
          SmashProduct.includeA (μ := μ) (μ.action ((ℛ R h).left i) a) *
            SmashProduct.includeH ((ℛ R h).right i)) • m := by
          rw [SmashProduct.includeH_mul_includeA (ℛ R h) a]
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
    [hc : μ.IsCompatibleAction M] : SmashProduct μ →ₐ[R] Module.End R M :=
  lift (Algebra.lsmul R (A := A) R M) (Algebra.lsmul R (A := H) R M) hc.smashCompatible

@[simp]
theorem lsmulAlgHom_pure [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] (a : A) (h : H) (m : M) :
    lsmulAlgHom μ M (pure a h) m = a • (h • m) := by
  simp [lsmulAlgHom]

@[simp]
theorem lsmulAlgHom_comp_includeA [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    (lsmulAlgHom μ M).comp includeA = Algebra.lsmul R R M :=
  lift_comp_includeA ..

@[simp]
theorem lsmulAlgHom_comp_includeH [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    (lsmulAlgHom μ M).comp includeH = Algebra.lsmul R R M :=
  lift_comp_includeH ..

@[simp]
theorem lsmulAlgHom_includeA [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] (a : A) (m : M) :
    lsmulAlgHom μ M (includeA a) m = a • m := by
  simp [includeA_eq_pure]

@[simp]
theorem lsmulAlgHom_includeH [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] (h : H) (m : M) :
    lsmulAlgHom μ M (includeH h) m = h • m := by
  simp [includeH_eq_pure]

/-- Left `A # H`-module structure on `M` assembled from compatible `A`- and `H`-actions. -/
@[instance_reducible]
noncomputable def moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] : Module (SmashProduct μ) M :=
  Module.compHom M (lsmulAlgHom μ M).toRingHom

@[simp]
theorem moduleOfCompatible_smul [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] (z : SmashProduct μ) (m : M) :
    let _ := moduleOfCompatible μ M
    z • m = lsmulAlgHom μ M z m :=
  (rfl)

theorem isScalarTower_moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    let _ := moduleOfCompatible μ M
    IsScalarTower R (SmashProduct μ) M := by
  let _ := moduleOfCompatible μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  rw [moduleOfCompatible_smul, AlgHom.commutes, Module.algebraMap_end_apply]

theorem isSmashModule_moduleOfCompatible [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module H M] [IsScalarTower R H M]
    [μ.IsCompatibleAction M] :
    let _ := moduleOfCompatible μ M
    μ.IsSmashModule M := by
  let _ := moduleOfCompatible μ M
  exact ⟨fun a h m => lsmulAlgHom_pure μ M a h m⟩

/-- Restriction of scalars of an `A # H`-module along `includeA : A →ₐ[R] A # H`. -/
@[instance_reducible]
noncomputable def moduleA [AddCommMonoid M] [Module (SmashProduct μ) M] : Module A M :=
  Module.compHom M (includeA (μ := μ)).toRingHom

/-- Restriction of scalars of an `A # H`-module along `includeH : H →ₐ[R] A # H`. -/
@[instance_reducible]
noncomputable def moduleH [AddCommMonoid M] [Module (SmashProduct μ) M] : Module H M :=
  Module.compHom M (includeH (μ := μ)).toRingHom

@[simp]
theorem moduleA_smul [AddCommMonoid M] [Module (SmashProduct μ) M] (a : A) (m : M) :
    let _ := moduleA μ M
    a • m = includeA (μ := μ) a • m :=
  (rfl)

@[simp]
theorem moduleH_smul [AddCommMonoid M] [Module (SmashProduct μ) M] (h : H) (m : M) :
    let _ := moduleH μ M
    h • m = includeH (μ := μ) h • m :=
  (rfl)

theorem isSmashModule_moduleA_moduleH [AddCommMonoid M] [Module (SmashProduct μ) M] :
    let _ := moduleA μ M
    let _ := moduleH μ M
    μ.IsSmashModule M := by
  let _ := moduleA μ M
  let _ := moduleH μ M
  refine ⟨fun a h m => ?_⟩
  rw [moduleA_smul, moduleH_smul, ← mul_smul, includeA_mul_includeH]

theorem isScalarTower_moduleA [AddCommMonoid M] [Module R M]
    [Module (SmashProduct μ) M] [IsScalarTower R (SmashProduct μ) M] :
    let _ := moduleA μ M
    IsScalarTower R A M := by
  let _ := moduleA μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  rw [moduleA_smul, AlgHom.commutes, algebraMap_smul]

theorem isScalarTower_moduleH [AddCommMonoid M] [Module R M]
    [Module (SmashProduct μ) M] [IsScalarTower R (SmashProduct μ) M] :
    let _ := moduleH μ M
    IsScalarTower R H M := by
  let _ := moduleH μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  rw [moduleH_smul, AlgHom.commutes, algebraMap_smul]

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
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ }) :
    CompatibleActionData μ M :=
  let _ : Module (SmashProduct μ) M := m.val
  let _ : IsScalarTower R (SmashProduct μ) M := m.property
  let mA := moduleA μ M
  let tA := isScalarTower_moduleA μ M
  let mH := moduleH μ M
  let tH := isScalarTower_moduleH μ M
  let _ := isSmashModule_moduleA_moduleH μ M
  ⟨mA, tA, mH, tH, IsSmashModule.toIsCompatibleAction⟩

private noncomputable def toSmashModule [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) :
    { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ } :=
  let _ := d.moduleA
  let _ := d.towerA
  let _ := d.moduleH
  let _ := d.towerH
  let _ := d.compatible
  ⟨moduleOfCompatible μ M, isScalarTower_moduleOfCompatible μ M⟩

private theorem toSmashModule_ofSmashModule [AddCommMonoid M] [Module R M]
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ }) :
    toSmashModule μ M (ofSmashModule μ M m) = m := by
  rcases m with ⟨m, hm⟩
  let _ : Module (SmashProduct μ) M := m
  have _ : IsScalarTower R (SmashProduct μ) M := hm
  let _ := moduleA μ M
  have _ := isScalarTower_moduleA μ M
  let _ := moduleH μ M
  have _ := isScalarTower_moduleH μ M
  have _ := isSmashModule_moduleA_moduleH μ M
  have hF : lsmulAlgHom μ M = Algebra.lsmul R R M := by
    ext a x
    · simp only [AlgHom.comp_apply, lsmulAlgHom_comp_includeA, Algebra.lsmul_coe]
      exact (IsSmashModule.includeA_smul (μ := μ) a x).symm
    · simp only [AlgHom.comp_apply, lsmulAlgHom_comp_includeH, Algebra.lsmul_coe]
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
  · dsimp only [ofSmashModule, toSmashModule]
    rw [moduleA_smul]
    exact (moduleOfCompatible_smul μ M (includeA a) x).trans (lsmulAlgHom_includeA μ M a x)
  · dsimp only [ofSmashModule, toSmashModule]
    rw [moduleH_smul]
    exact (moduleOfCompatible_smul μ M (includeH h) x).trans (lsmulAlgHom_includeH μ M h x)

/-- Bijection between `R`-compatible left `A # H`-module structures on `M` and compatible pairs of
`R`-compatible `A`- and `H`-module structures on `M`. -/
noncomputable def moduleEquiv [AddCommMonoid M] [Module R M] :
    { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ } ≃
      CompatibleActionData μ M where
  toFun := ofSmashModule μ M
  invFun := toSmashModule μ M
  left_inv := toSmashModule_ofSmashModule μ M
  right_inv := ofSmashModule_toSmashModule μ M

@[simp]
theorem moduleEquiv_apply_moduleA [AddCommMonoid M] [Module R M]
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ }) :
    (moduleEquiv μ M m).moduleA = let _ := m.val; moduleA μ M :=
  (rfl)

@[simp]
theorem moduleEquiv_apply_moduleH [AddCommMonoid M] [Module R M]
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ }) :
    (moduleEquiv μ M m).moduleH = let _ := m.val; moduleH μ M :=
  (rfl)

@[simp]
theorem moduleEquiv_apply_moduleA_smul [AddCommMonoid M] [Module R M]
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ })
    (a : A) (x : M) :
    (let _ := (moduleEquiv μ M m).moduleA; a • x) = (let _ := m.val; includeA (μ := μ) a • x) :=
  (rfl)

@[simp]
theorem moduleEquiv_apply_moduleH_smul [AddCommMonoid M] [Module R M]
    (m : { m : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ m.toSMul _ })
    (h : H) (x : M) :
    (let _ := (moduleEquiv μ M m).moduleH; h • x) = (let _ := m.val; includeH (μ := μ) h • x) :=
  (rfl)

@[simp]
theorem moduleEquiv_symm_apply_val [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) :
    ((moduleEquiv μ M).symm d).val =
      let _ := d.moduleA
      let _ := d.towerA
      let _ := d.moduleH
      let _ := d.towerH
      let _ := d.compatible
      moduleOfCompatible μ M :=
  (rfl)

@[simp]
theorem moduleEquiv_symm_apply_smul [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) (z : SmashProduct μ) (x : M) :
    (let _ := ((moduleEquiv μ M).symm d).val; z • x) =
      let _ := d.moduleA
      let _ := d.towerA
      let _ := d.moduleH
      let _ := d.towerH
      let _ := d.compatible
      lsmulAlgHom μ M z x :=
  (rfl)

theorem moduleEquiv_symm_apply_pure_smul [AddCommMonoid M] [Module R M]
    (d : CompatibleActionData μ M) (a : A) (h : H) (x : M) :
    (let _ := ((moduleEquiv μ M).symm d).val; pure (μ := μ) a h • x) =
      (let _ := d.moduleA; let _ := d.moduleH; a • (h • x)) := by
  simp

end ModuleEquivalence

/-! ### `A # H`-linear maps -/

section LinearMaps

variable {μ : LeftModuleAlgebra R H A} {M : Type x} {N : Type y}
  [AddCommMonoid M] [Module A M] [Module H M] [Module (SmashProduct μ) M] [μ.IsSmashModule M]
  [AddCommMonoid N] [Module A N] [Module H N] [Module (SmashProduct μ) N] [μ.IsSmashModule N]

/-- Every `A # H`-linear map is `A`-linear. -/
def restrictScalarsLinearMapA (f : M →ₗ[SmashProduct μ] N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' a m := by
    simp only [RingHom.id_apply, ← IsSmashModule.includeA_smul (μ := μ), f.map_smul]

@[simp]
theorem restrictScalarsLinearMapA_apply (f : M →ₗ[SmashProduct μ] N) (m : M) :
    restrictScalarsLinearMapA f m = f m :=
  (rfl)

/-- Every `A # H`-linear map commutes with the `H`-action. -/
theorem map_smulH_of_smashLinear (f : M →ₗ[SmashProduct μ] N) (h : H) (m : M) :
    f (h • m) = h • f m := by
  rw [← IsSmashModule.includeH_smul (μ := μ), f.map_smul, IsSmashModule.includeH_smul]

/-- An `H`-equivariant `A`-linear map upgrades to an `A # H`-linear map. -/
def mkLinearMap (f : M →ₗ[A] N) (hf : ∀ (h : H) (m : M), f (h • m) = h • f m) :
    M →ₗ[SmashProduct μ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' z m := by
    induction z using SmashProduct.inductionOn with
    | pure a h =>
      simp only [RingHom.id_apply, IsSmashModule.pure_smul, f.map_smul, hf]
    | add x y hx hy =>
      simp only [RingHom.id_apply] at hx hy ⊢
      rw [add_smul, map_add, hx, hy, add_smul]

@[simp]
theorem mkLinearMap_apply (f : M →ₗ[A] N)
    (hf : ∀ (h : H) (m : M), f (h • m) = h • f m) (m : M) :
    mkLinearMap (μ := μ) f hf m = f m :=
  (rfl)

variable (R μ M N) in
/-- `R`-linear equivalence between `A # H`-linear maps `M →ₗ[SmashProduct μ] N` and
`H`-equivariant `A`-linear maps `M →ₗ[A] N`. -/
def linearMapEquiv [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R (SmashProduct μ) N] :
    (M →ₗ[SmashProduct μ] N) ≃ₗ[R] equivariantLinearMaps R H A M N where
  toFun f := ⟨restrictScalarsLinearMapA f,
    (mem_equivariantLinearMaps _).2 (map_smulH_of_smashLinear f)⟩
  invFun f := mkLinearMap f.val ((mem_equivariantLinearMaps _).1 f.property)
  left_inv _ := LinearMap.ext fun _ => rfl
  right_inv _ := Subtype.ext <| LinearMap.ext fun _ => rfl
  map_add' _ _ := Subtype.ext <| LinearMap.ext fun _ => rfl
  map_smul' _ _ := Subtype.ext <| LinearMap.ext fun _ => rfl

@[simp]
theorem linearMapEquiv_apply_coe [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R (SmashProduct μ) N] (f : M →ₗ[SmashProduct μ] N) (m : M) :
    ((linearMapEquiv R μ M N f : M →ₗ[A] N) m) = f m :=
  (rfl)

@[simp]
theorem linearMapEquiv_symm_apply [Module R N] [IsScalarTower R A N] [SMulCommClass R H N]
    [IsScalarTower R (SmashProduct μ) N] (f : equivariantLinearMaps R H A M N) (m : M) :
    (linearMapEquiv R μ M N).symm f m = (f : M →ₗ[A] N) m :=
  (rfl)

end LinearMaps

end SmashProduct

end LeftModuleAlgebra

end TauCeti
