/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic

/-!
# Modules over a smash product

Given a left `H`-module algebra `μ : LeftModuleAlgebra R H A`, a left module over `SmashProduct μ`
whose `R`-action agrees with the given `R`-module structure is the same datum as an `A`-module and
an `H`-module over `R` satisfying the covariance identity

`h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`

(`LeftModuleAlgebra.IsCompatibleModule`).

This file formulates `IsCompatibleModule` directly in terms of `LeftModuleAlgebra.SmashCompatible`
applied to `Algebra.lsmul`, derives its Sweedler, group-like, skew-primitive, and primitive
specializations, constructs the canonical action `SmashProduct.toEndAlgHom` of `SmashProduct μ` on
`A` itself (`(a # h) · b = a * (h · b)`), establishes the equivalence `SmashProduct.moduleEquiv`
between `SmashProduct μ`-module structures over `R` and compatible `(A, H)`-module structures over
`R`, and characterizes `SmashProduct μ`-equivariant additive maps as maps equivariant for `A` and
`H` separately.

## Main definitions

* `TauCeti.LeftModuleAlgebra.IsCompatibleModule`: compatibility of `A`- and `H`-actions on an
  `R`-module `M`.
* `TauCeti.SmashProduct.toEndAlgHom`: the canonical `R`-algebra homomorphism
  `SmashProduct μ →ₐ[R] Module.End R A` sending `a # h` to `b ↦ a * (h · b)`.
* `TauCeti.SmashProduct.moduleOfCompatible`: the `SmashProduct μ`-module structure assembled from a
  compatible `(A, H)`-module.
* `TauCeti.SmashProduct.CompatibleModuleData`: bundled `(A, H)`-module structures over `R`
  satisfying `IsCompatibleModule`.
* `TauCeti.SmashProduct.moduleEquiv`: equivalence between `SmashProduct μ`-module structures on `M`
  compatible with `R` and `CompatibleModuleData μ M`.

## Main results

* `TauCeti.LeftModuleAlgebra.isCompatibleModule_iff_sum`: `IsCompatibleModule` is equivalent to
  `h • (a • m) = ∑ (h₁ · a) • (h₂ • m)` in any family of coproduct representations.
* `TauCeti.SmashProduct.map_smul_iff`: an additive map between `SmashProduct μ`-modules commutes
  with the `SmashProduct μ`-action if and only if it commutes with the restricted `A`- and
  `H`-actions.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §4.1.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), 1–45, §2.2 and §5.1.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

universe u v w uM

namespace LeftModuleAlgebra

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- An `R`-module `M` carrying compatible `A`- and `H`-module structures over `R` is a
**compatible `(A, H)`-module** for `μ : LeftModuleAlgebra R H A` when the two actions satisfy
`h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`, expressed without choosing a coproduct representation via
`LeftModuleAlgebra.SmashCompatible`. -/
def IsCompatibleModule (μ : LeftModuleAlgebra R H A) (M : Type uM)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] : Prop :=
  μ.SmashCompatible (Algebra.lsmul R R M (A := A)) (Algebra.lsmul R R M (A := H))

section CompatibleLemmas

variable {μ : LeftModuleAlgebra R H A} {M : Type uM}
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module H M] [IsScalarTower R H M]

/-- Compatibility expanded on elements in any finite representation of the coproduct:
`h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`. -/
theorem IsCompatibleModule.smul_smul_eq_sum (hc : μ.IsCompatibleModule M)
    {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) (m : M) :
    h • (a • m) = ∑ i ∈ r.index, μ.action (r.left i) a • (r.right i • m) := by
  have key := LinearMap.congr_fun (hc.mul_eq_sum r a) m
  simpa [LinearMap.sum_apply] using key

/-- `IsCompatibleModule` can be checked pointwise on elements in any chosen family of coproduct
representations. -/
theorem isCompatibleModule_iff_sum (μ : LeftModuleAlgebra R H A) (M : Type uM)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] {ι : Type*} (r : ∀ h : H, Coalgebra.Repr R h ι) :
    μ.IsCompatibleModule M ↔
      ∀ h (a : A) (m : M),
        h • (a • m) = ∑ i ∈ (r h).index, μ.action ((r h).left i) a • ((r h).right i • m) := by
  rw [IsCompatibleModule, μ.smashCompatible_iff_sum _ _ r]
  refine ⟨fun hc h a m => ?_, fun hc h a => ?_⟩
  · simpa [LinearMap.sum_apply] using LinearMap.congr_fun (hc h a) m
  · ext m
    simpa [LinearMap.sum_apply] using hc h a m

/-- On a compatible `(A, H)`-module, a group-like element `g` satisfies
`g • (a • m) = (g · a) • (g • m)`. -/
theorem IsCompatibleModule.smul_smul_of_isGroupLikeElem (hc : μ.IsCompatibleModule M)
    {g : H} (hg : IsGroupLikeElem R g) (a : A) (m : M) :
    g • (a • m) = μ.action g a • (g • m) := by
  have key := LinearMap.congr_fun (hc.apply g a) m
  simpa [hg.comul_eq_tmul_self] using key

/-- On a compatible `(A, H)`-module, a `(g, h)`-skew-primitive element `d` satisfies the twisted
Leibniz law `d • (a • m) = (g · a) • (d • m) + (d · a) • (h • m)`. -/
theorem IsCompatibleModule.smul_smul_of_isSkewPrimitiveElem (hc : μ.IsCompatibleModule M)
    {g h d : H} (hd : IsSkewPrimitiveElem R g h d) (a : A) (m : M) :
    d • (a • m) = μ.action g a • (d • m) + μ.action d a • (h • m) := by
  have key := LinearMap.congr_fun (hc.apply d a) m
  simpa [hd.comul_eq_tmul_add_tmul] using key

/-- On a compatible `(A, H)`-module, a primitive element `d` acts as a derivation relative to `A`:
`d • (a • m) = (d · a) • m + a • (d • m)`. -/
theorem IsCompatibleModule.smul_smul_of_isPrimitiveElem (hc : μ.IsCompatibleModule M)
    {d : H} (hd : Bialgebra.IsPrimitiveElem R d) (a : A) (m : M) :
    d • (a • m) = μ.action d a • m + a • (d • m) := by
  rw [hc.smul_smul_of_isSkewPrimitiveElem hd a m, map_one, one_apply_eq_self, one_smul, add_comm]

end CompatibleLemmas

/-- Left multiplication by `A` and the module-algebra action `μ.action` of `H` satisfy
`SmashCompatible` in `Module.End R A`. -/
theorem smashCompatible_lsmul_action (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible (Algebra.lsmul R R A) μ.action := by
  classical
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  ext b
  simpa [LinearMap.sum_apply] using μ.action_mul_eq_sum (ℛ R h) a b

end LeftModuleAlgebra

namespace SmashProduct

section Semiring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-! ### Canonical action of `A # H` on `A` -/

/-- The canonical `R`-algebra homomorphism `SmashProduct μ →ₐ[R] Module.End R A` sending `a # h`
to `b ↦ a * (h · b)`. -/
def toEndAlgHom (μ : LeftModuleAlgebra R H A) : SmashProduct μ →ₐ[R] Module.End R A :=
  lift (Algebra.lsmul R R A) μ.action μ.smashCompatible_lsmul_action

@[simp]
theorem toEndAlgHom_tmul_apply (μ : LeftModuleAlgebra R H A) (a : A) (h : H) (b : A) :
    toEndAlgHom μ (tmul μ a h) b = a * μ.action h b := by
  simp [toEndAlgHom]

theorem toEndAlgHom_includeLeft_apply (μ : LeftModuleAlgebra R H A) (a b : A) :
    toEndAlgHom μ (includeLeft μ a) b = a * b := by
  simp

theorem toEndAlgHom_includeRight_apply (μ : LeftModuleAlgebra R H A) (h : H) (b : A) :
    toEndAlgHom μ (includeRight μ h) b = μ.action h b := by
  simp

/-! ### Assembling and restricting `SmashProduct`-modules -/

section Assemble

variable {μ : LeftModuleAlgebra R H A} {M : Type uM}
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module H M] [IsScalarTower R H M]

/-- The `R`-algebra homomorphism `SmashProduct μ →ₐ[R] Module.End R M` induced by a compatible
`(A, H)`-module structure on `M`. -/
def lsmulOfCompatible (hc : μ.IsCompatibleModule M) : SmashProduct μ →ₐ[R] Module.End R M :=
  lift (Algebra.lsmul R R M (A := A)) (Algebra.lsmul R R M (A := H)) hc

@[simp]
theorem lsmulOfCompatible_tmul_apply (hc : μ.IsCompatibleModule M) (a : A) (h : H) (m : M) :
    lsmulOfCompatible hc (tmul μ a h) m = a • (h • m) :=
  LinearMap.congr_fun (lift_tmul _ _ hc a h) m

theorem lsmulOfCompatible_includeLeft_apply (hc : μ.IsCompatibleModule M) (a : A) (m : M) :
    lsmulOfCompatible hc (includeLeft μ a) m = a • m := by
  rw [includeLeft_apply, lsmulOfCompatible_tmul_apply, one_smul]

theorem lsmulOfCompatible_includeRight_apply (hc : μ.IsCompatibleModule M) (h : H) (m : M) :
    lsmulOfCompatible hc (includeRight μ h) m = h • m := by
  rw [includeRight_apply, lsmulOfCompatible_tmul_apply, one_smul]

/-- Assemble a `Module (SmashProduct μ) M` structure from a compatible `(A, H)`-module structure,
with `(a # h) • m = a • (h • m)`. -/
abbrev moduleOfCompatible (hc : μ.IsCompatibleModule M) : Module (SmashProduct μ) M :=
  Module.compHom M (lsmulOfCompatible hc).toRingHom

theorem isScalarTowerOfCompatible (hc : μ.IsCompatibleModule M) :
    letI := moduleOfCompatible hc
    IsScalarTower R (SmashProduct μ) M := by
  let := moduleOfCompatible hc
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change lsmulOfCompatible hc (algebraMap R (SmashProduct μ) r) m = r • m
  rw [(lsmulOfCompatible hc).commutes]
  rfl

theorem moduleOfCompatible_tmul_smul (hc : μ.IsCompatibleModule M) (a : A) (h : H) (m : M) :
    (letI := moduleOfCompatible hc; tmul μ a h • m) = a • (h • m) :=
  lsmulOfCompatible_tmul_apply hc a h m

end Assemble

section Restrict

variable (μ : LeftModuleAlgebra R H A) (M : Type uM)
variable [AddCommMonoid M] [Module R M] [Module (SmashProduct μ) M]
  [IsScalarTower R (SmashProduct μ) M]

/-- Restrict a `SmashProduct μ`-module along `includeLeft μ : A →ₐ[R] SmashProduct μ`. -/
abbrev restrictModuleLeft : Module A M :=
  Module.compHom M (includeLeft μ).toRingHom

/-- Restrict a `SmashProduct μ`-module along `includeRight μ : H →ₐ[R] SmashProduct μ`. -/
abbrev restrictModuleRight : Module H M :=
  Module.compHom M (includeRight μ).toRingHom

theorem isScalarTower_restrictModuleLeft :
    letI := restrictModuleLeft μ M
    IsScalarTower R A M := by
  let := restrictModuleLeft μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change includeLeft μ (algebraMap R A r) • m = r • m
  rw [(includeLeft μ).commutes, algebraMap_smul]

theorem isScalarTower_restrictModuleRight :
    letI := restrictModuleRight μ M
    IsScalarTower R H M := by
  let := restrictModuleRight μ M
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change includeRight μ (algebraMap R H r) • m = r • m
  rw [(includeRight μ).commutes, algebraMap_smul]

/-- Restricting a `SmashProduct μ`-module along `includeLeft μ` and `includeRight μ` produces a
compatible `(A, H)`-module. -/
theorem isCompatibleModule_restrict :
    letI := restrictModuleLeft μ M
    letI := restrictModuleRight μ M
    haveI := isScalarTower_restrictModuleLeft μ M
    haveI := isScalarTower_restrictModuleRight μ M
    μ.IsCompatibleModule M := by
  let := restrictModuleLeft μ M
  let := restrictModuleRight μ M
  have := isScalarTower_restrictModuleLeft μ M
  have := isScalarTower_restrictModuleRight μ M
  have hlA : Algebra.lsmul R R M (A := A) =
      (Algebra.lsmul R R M (A := SmashProduct μ)).comp (includeLeft μ) := by
    ext a m
    rfl
  have hlH : Algebra.lsmul R R M (A := H) =
      (Algebra.lsmul R R M (A := SmashProduct μ)).comp (includeRight μ) := by
    ext h m
    rfl
  rw [LeftModuleAlgebra.IsCompatibleModule, hlA, hlH]
  exact smashCompatible_comp (Algebra.lsmul R R M (A := SmashProduct μ))

variable {μ M}

/-- On any `SmashProduct μ`-module, a pure smash tensor acts by
`(a # h) • m = (a # 1) • ((1 # h) • m)`. -/
theorem tmul_smul_eq_includeLeft_smul_includeRight_smul
    {N : Type uM} [AddCommMonoid N] [Module (SmashProduct μ) N]
    (a : A) (h : H) (m : N) :
    tmul μ a h • m = includeLeft μ a • (includeRight μ h • m) := by
  rw [← mul_smul, includeLeft_mul_includeRight]

/-- An additive map between `SmashProduct μ`-modules commutes with the `SmashProduct μ`-action if
and only if it commutes with the actions of `includeLeft μ a` and `includeRight μ h` separately. -/
theorem map_smul_iff {N P : Type*} [AddCommMonoid N] [Module (SmashProduct μ) N]
    [AddCommMonoid P] [Module (SmashProduct μ) P] (f : N →+ P) :
    (∀ (x : SmashProduct μ) (m : N), f (x • m) = x • f m) ↔
      (∀ (a : A) (m : N), f (includeLeft μ a • m) = includeLeft μ a • f m) ∧
        (∀ (h : H) (m : N), f (includeRight μ h • m) = includeRight μ h • f m) := by
  refine ⟨fun hf => ⟨fun a m => hf _ m, fun h m => hf _ m⟩, fun ⟨hfA, hfH⟩ x m => ?_⟩
  exact SmashProduct.inductionOn x
    (fun a h => by
      rw [tmul_smul_eq_includeLeft_smul_includeRight_smul, hfA, hfH,
        tmul_smul_eq_includeLeft_smul_includeRight_smul])
    (fun x₁ x₂ hx₁ hx₂ => by rw [add_smul, map_add, hx₁, hx₂, add_smul])

end Restrict

/-! ### Bundled equivalence of module structures -/

/-- Bundled datum of an `A`-module structure and an `H`-module structure on an `R`-module `M`, both
compatible with `R` and satisfying `LeftModuleAlgebra.IsCompatibleModule μ M`. -/
structure CompatibleModuleData (μ : LeftModuleAlgebra R H A) (M : Type uM)
    [AddCommMonoid M] [Module R M] where
  /-- The `A`-module structure on `M`. -/
  moduleA : Module A M
  /-- Compatibility of the `A`-action with the `R`-action. -/
  isScalarTowerA : @IsScalarTower R A M _ moduleA.toSMul _
  /-- The `H`-module structure on `M`. -/
  moduleH : Module H M
  /-- Compatibility of the `H`-action with the `R`-action. -/
  isScalarTowerH : @IsScalarTower R H M _ moduleH.toSMul _
  /-- Covariance `h • (a • m) = ∑ (h₁ · a) • (h₂ • m)` between the two actions. -/
  compatible :
    @LeftModuleAlgebra.IsCompatibleModule R H A _ _ _ _ _ μ M _ _
      moduleA isScalarTowerA moduleH isScalarTowerH

/-- Two `CompatibleModuleData` structures on `M` are equal when their `A`-actions agree and their
`H`-actions agree. -/
@[ext]
theorem CompatibleModuleData.ext {μ : LeftModuleAlgebra R H A} {M : Type uM}
    [AddCommMonoid M] [Module R M] {d₁ d₂ : CompatibleModuleData μ M}
    (hA : ∀ (a : A) (m : M),
      (@SMul.smul A M d₁.moduleA.toSMul a m) = (@SMul.smul A M d₂.moduleA.toSMul a m))
    (hH : ∀ (h : H) (m : M),
      (@SMul.smul H M d₁.moduleH.toSMul h m) = (@SMul.smul H M d₂.moduleH.toSMul h m)) :
    d₁ = d₂ := by
  have hmA : d₁.moduleA = d₂.moduleA := Module.ext' d₁.moduleA d₂.moduleA hA
  have hmH : d₁.moduleH = d₂.moduleH := Module.ext' d₁.moduleH d₂.moduleH hH
  rcases d₁ with ⟨mA₁, tA₁, mH₁, tH₁, c₁⟩
  rcases d₂ with ⟨mA₂, tA₂, mH₂, tH₂, c₂⟩
  subst hmA hmH
  congr

/-- Bijection between `SmashProduct μ`-module structures on an `R`-module `M` forming a scalar
tower over `R` and compatible `(A, H)`-module structures on `M` (`CompatibleModuleData μ M`). -/
def moduleEquiv (μ : LeftModuleAlgebra R H A) (M : Type uM) [AddCommMonoid M] [Module R M] :
    {_inst : Module (SmashProduct μ) M // @IsScalarTower R (SmashProduct μ) M _ _inst.toSMul _} ≃
      CompatibleModuleData μ M where
  toFun s :=
    letI : Module (SmashProduct μ) M := s.1
    haveI : IsScalarTower R (SmashProduct μ) M := s.2
    { moduleA := restrictModuleLeft μ M
      isScalarTowerA := isScalarTower_restrictModuleLeft μ M
      moduleH := restrictModuleRight μ M
      isScalarTowerH := isScalarTower_restrictModuleRight μ M
      compatible := isCompatibleModule_restrict μ M }
  invFun d :=
    letI : Module A M := d.moduleA
    haveI : IsScalarTower R A M := d.isScalarTowerA
    letI : Module H M := d.moduleH
    haveI : IsScalarTower R H M := d.isScalarTowerH
    ⟨moduleOfCompatible d.compatible, isScalarTowerOfCompatible d.compatible⟩
  left_inv := fun ⟨inst, hT⟩ => by
    let : Module (SmashProduct μ) M := inst
    have : IsScalarTower R (SmashProduct μ) M := hT
    let : Module A M := restrictModuleLeft μ M
    have : IsScalarTower R A M := isScalarTower_restrictModuleLeft μ M
    let : Module H M := restrictModuleRight μ M
    have : IsScalarTower R H M := isScalarTower_restrictModuleRight μ M
    apply Subtype.ext
    refine Module.ext' _ inst fun x m => ?_
    exact SmashProduct.inductionOn x
      (fun a h => by
        change lsmulOfCompatible (isCompatibleModule_restrict μ M) (tmul μ a h) m = tmul μ a h • m
        rw [lsmulOfCompatible_tmul_apply, tmul_smul_eq_includeLeft_smul_includeRight_smul]
        rfl)
      (fun x₁ x₂ hx₁ hx₂ => by
        change lsmulOfCompatible (isCompatibleModule_restrict μ M) (x₁ + x₂) m = (x₁ + x₂) • m
        rw [map_add, LinearMap.add_apply, add_smul]
        exact congrArg₂ (· + ·) hx₁ hx₂)
  right_inv d := by
    let : Module A M := d.moduleA
    have : IsScalarTower R A M := d.isScalarTowerA
    let : Module H M := d.moduleH
    have : IsScalarTower R H M := d.isScalarTowerH
    ext x m
    · exact lsmulOfCompatible_includeLeft_apply d.compatible x m
    · exact lsmulOfCompatible_includeRight_apply d.compatible x m

end Semiring

end SmashProduct

end TauCeti
