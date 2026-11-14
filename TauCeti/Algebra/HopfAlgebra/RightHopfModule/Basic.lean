/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Right Hopf modules and the Fundamental Theorem of Hopf Modules

A **right Hopf module** over an `R`-bialgebra `H` (in the sense of Larson and Sweedler) is an
`R`-module `M` equipped with both a right `H`-comodule structure `ρ : M →ₗ[R] M ⊗[R] H` and a
right `H`-module action `(m, h) ↦ m ◁ h` such that the coaction is equivariant for the diagonal
right `H`-action:
`ρ (m ◁ h) = ∑ (m₀ ◁ h₁) ⊗ (m₁ * h₂)`.

Following `TauCeti.LeftModuleAlgebra`, the right `H`-action is bundled as an `R`-algebra
homomorphism `action : Hᵐᵒᵖ →ₐ[R] Module.End R M` rather than a `Module Hᵐᵒᵖ M` typeclass. This
avoids `Module` diamonds on tensor products such as `V ⊗[R] H` and `H ⊗[R] H`, where Mathlib
already installs scalar actions through the left tensor factor.

Over a general bialgebra `H`, we construct:
* `TauCeti.RightHopfModule.coinvariants`: the submodule `M^{co H}` of vectors `m` with
  `ρ(m) = m ⊗ 1`;
* `TauCeti.RightHopfModule.self`: the regular right Hopf module `H`;
* `TauCeti.RightHopfModule.cofree`: the cofree right Hopf module `V ⊗[R] H` for an `R`-module `V`,
  with `TauCeti.RightHopfModule.cofreeCoinvariantsEquiv : V ≃ₗ[R] (cofree R H V).coinvariants`;
* `TauCeti.RightHopfModule.Hom` and `TauCeti.RightHopfModule.Equiv`: morphisms and equivalences of
  right Hopf modules.

When `H` is a Hopf algebra over an arbitrary commutative semiring `R` (with no group, field, or
finiteness hypothesis on `R`, `H`, or `M`), the antipode provides the coinvariant projection
`P(m) = ∑ m₀ ◁ S(m₁)` (`TauCeti.RightHopfModule.coinvariantProj`) and proves the **Fundamental
Theorem of Hopf Modules** (`TauCeti.RightHopfModule.coinvariantsTensorHopfEquiv` and
`TauCeti.RightHopfModule.coinvariantsTensorEquiv`): every right `H`-Hopf module `M` is canonically
isomorphic to `μ.coinvariants ⊗[R] H` via `v ⊗ h ↦ v ◁ h` with inverse
`m ↦ ∑ P(m₀) ⊗ m₁`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Proposition 1.
* M. E. Sweedler, *Hopf Algebras* (1969), Theorem 4.1.1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 1.9.4.
-/

public section

open scoped TensorProduct Coalgebra

namespace TauCeti

universe u v w x

/-- A right Hopf module over an `R`-bialgebra `H`.

It bundles a right `H`-comodule structure on `M` together with an `R`-bilinear right `H`-action
`action : Hᵐᵒᵖ →ₐ[R] Module.End R M` whose coaction is equivariant for the diagonal right action
`ρ (m ◁ h) = ∑ (m₀ ◁ h₁) ⊗ (m₁ * h₂)`. -/
structure RightHopfModule (R : Type u) (H : Type v) (M : Type w) [CommSemiring R]
    [Semiring H] [Bialgebra R H] [AddCommMonoid M] [Module R M]
    extends Comodule R H M where
  /-- The unital, associative, `R`-bilinear right `H`-action on `M`, bundled as an algebra
  homomorphism from `Hᵐᵒᵖ` to `Module.End R M`. -/
  action : Hᵐᵒᵖ →ₐ[R] Module.End R M
  /-- The coaction is equivariant for the diagonal right `H`-action:
  `ρ (m ◁ h) = ∑ (m₀ ◁ h₁) ⊗ (m₁ * h₂)`. -/
  coact_action : ∀ (m : M) (h : H),
    coact (action (MulOpposite.op h) m) =
      TensorProduct.map₂
        ((action.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).flip)
        (LinearMap.mul R H)
        (coact m) (Coalgebra.comul h)

namespace RightHopfModule

section Bialgebra

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Right Hopf module structures are determined by their coactions and actions. -/
@[ext]
theorem ext {μ ν : RightHopfModule R H M}
    (hcoact : μ.coact = ν.coact)
    (hact : ∀ (h : Hᵐᵒᵖ) (m : M), μ.action h m = ν.action h m) :
    μ = ν := by
  have hcom : μ.toComodule = ν.toComodule := Comodule.ext hcoact
  have ha : μ.action = ν.action := by ext h m; exact hact h m
  cases μ
  cases ν
  cases hcom
  cases ha
  rfl

/-- The bilinear map `(m, h) ↦ m ◁ h` underlying a right Hopf module's right `H`-action. -/
private abbrev actRightLinear (μ : RightHopfModule R H M) : M →ₗ[R] H →ₗ[R] M :=
  (μ.action.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).flip

@[simp]
private theorem actRightLinear_apply (μ : RightHopfModule R H M) (m : M) (h : H) :
    μ.actRightLinear m h = μ.action (MulOpposite.op h) m :=
  (rfl)

/-- Acting by `1 : Hᵐᵒᵖ` is the identity on `M`. -/
theorem action_one_apply (μ : RightHopfModule R H M) (m : M) :
    μ.action 1 m = m := by
  simp

/-- Acting by `MulOpposite.op 1` is the identity on `M`. -/
theorem action_op_one_apply (μ : RightHopfModule R H M) (m : M) :
    μ.action (MulOpposite.op (1 : H)) m = m := by
  simp

/-- Right associativity of the action: `m ◁ (a * b) = (m ◁ a) ◁ b`. -/
theorem action_op_mul_apply (μ : RightHopfModule R H M) (a b : H) (m : M) :
    μ.action (MulOpposite.op (a * b)) m =
      μ.action (MulOpposite.op b) (μ.action (MulOpposite.op a) m) := by
  rw [MulOpposite.op_mul, map_mul, mul_apply_eq_comp]

/-- Scalars from `R` act via `algebraMap R H` by the module scalar multiplication on `M`. -/
@[simp]
theorem action_op_algebraMap_apply (μ : RightHopfModule R H M) (r : R) (m : M) :
    μ.action (MulOpposite.op (algebraMap R H r)) m = r • m := by
  rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, MulOpposite.op_one, map_smul,
    LinearMap.smul_apply, action_one_apply]

private theorem map₂_actRightLinear_tmul (μ : RightHopfModule R H M) (z : M ⊗[R] H) (a b : H) :
    TensorProduct.map₂ μ.actRightLinear (LinearMap.mul R H) z (a ⊗ₜ[R] b) =
      TensorProduct.map (μ.action (MulOpposite.op a)) (LinearMap.mulRight R b) z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, hz₁, hz₂]
  | tmul m c => rfl

/-- Sweedler-sum form of the Hopf-module compatibility equation in any finite representation of
the coproduct of `h`. -/
theorem coact_action_sum (μ : RightHopfModule R H M) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) (m : M) :
    μ.coact (μ.action (MulOpposite.op h) m) =
      ∑ i ∈ r.index,
        TensorProduct.map (μ.action (MulOpposite.op (r.left i)))
          (LinearMap.mulRight R (r.right i)) (μ.coact m) := by
  rw [μ.coact_action]
  change TensorProduct.map₂ μ.actRightLinear (LinearMap.mul R H) (μ.coact m) (Coalgebra.comul h) = _
  rw [← r.eq, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ μ.map₂_actRightLinear_tmul (μ.coact m) (r.left i) (r.right i)

/-! ### Coinvariants -/

/-- The submodule of coinvariant elements of a right Hopf module: those `m : M` satisfying
`μ.coact m = m ⊗ₜ 1`. -/
def coinvariants (μ : RightHopfModule R H M) : Submodule R M :=
  letI := μ.toComodule
  (Comodule.fixedSubcomodule R H M).carrier

/-- An element is coinvariant exactly when its coaction is `m ⊗ₜ 1`. -/
@[simp]
theorem mem_coinvariants (μ : RightHopfModule R H M) {m : M} :
    m ∈ μ.coinvariants ↔ μ.coact m = m ⊗ₜ[R] (1 : H) := by
  let _ := μ.toComodule
  exact Comodule.mem_fixedSubcomodule

/-- The coinvariant submodule agrees with the carrier of `Comodule.fixedSubcomodule`. -/
theorem coinvariants_eq_fixedSubcomodule (μ : RightHopfModule R H M) :
    μ.coinvariants =
      (letI := μ.toComodule; (Comodule.fixedSubcomodule R H M).carrier) := by
  rfl

/-- On a coinvariant element `m`, the coaction of `m ◁ h` applies `m ◁ ·` to the left leg of
`Δ(h)`. -/
theorem coact_action_of_mem_coinvariants (μ : RightHopfModule R H M) {m : M}
    (hm : m ∈ μ.coinvariants) (h : H) :
    μ.coact (μ.action (MulOpposite.op h) m) =
      ((μ.action.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).flip m).rTensor H
        (Coalgebra.comul h) := by
  rw [μ.coact_action, μ.mem_coinvariants.mp hm, TensorProduct.map₂_apply_tmul]
  have hmul : LinearMap.mul R H 1 = LinearMap.id := by ext x; simp
  rw [hmul, ← LinearMap.rTensor_def]

/-! ### Regular and cofree right Hopf modules -/

/-- Right multiplication on an `R`-algebra, bundled as an algebra homomorphism from `Hᵐᵒᵖ` to
`Module.End R H`. -/
private def mulRightAlgHom (R : Type u) (H : Type v) [CommSemiring R] [Semiring H]
    [Algebra R H] : Hᵐᵒᵖ →ₐ[R] Module.End R H :=
  AlgHom.ofLinearMap
    ((LinearMap.mul R H).flip ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap)
    (by ext x; simp)
    (by intro a b; ext x; simp [mul_assoc])

variable (R H) in
/-- The regular right Hopf module of a bialgebra `H` over itself, with coaction given by
comultiplication and right action given by multiplication on the right. -/
noncomputable def self : RightHopfModule R H H where
  toComodule := Comodule.instSelf R H
  action := mulRightAlgHom R H
  coact_action m h := by
    change Coalgebra.comul (m * h) = _
    rw [Bialgebra.comul_mul]
    have hflip : ((mulRightAlgHom R H).toLinearMap ∘ₗ
        (MulOpposite.opLinearEquiv R).toLinearMap).flip = LinearMap.mul R H := by
      ext x y
      rfl
    rw [hflip]
    generalize Coalgebra.comul (R := R) m = u, Coalgebra.comul (R := R) h = v
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ hu₁ hu₂ => simp only [add_mul, map_add, LinearMap.add_apply, hu₁, hu₂]
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | add v₁ v₂ hv₁ hv₂ => simp only [mul_add, map_add, hv₁, hv₂]
      | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The coaction of the regular right Hopf module is comultiplication. -/
@[simp]
theorem self_coact : (self R H).coact = Coalgebra.comul :=
  (rfl)

/-- The right `H`-action of the regular right Hopf module is right multiplication. -/
@[simp]
theorem self_action_op_apply (h x : H) :
    (self R H).action (MulOpposite.op h) x = x * h :=
  (rfl)

variable (R H) in
/-- The cofree (trivial-action) right Hopf module `V ⊗[R] H` associated to an `R`-module `V`, with
coaction `v ⊗ a ↦ ∑ (v ⊗ a₁) ⊗ a₂` and right `H`-action `(v ⊗ a) ◁ h = v ⊗ (a * h)`. -/
noncomputable def cofree (V : Type w) [AddCommMonoid V] [Module R V] :
    RightHopfModule R H (V ⊗[R] H) where
  toComodule := Comodule.cofree R H V
  action := AlgHom.ofLinearMap
    (LinearMap.lTensorHom V ∘ₗ (mulRightAlgHom R H).toLinearMap)
    (by ext v a; simp)
    (by intro a b; ext v c; simp)
  coact_action z h := by
    let actV : (V ⊗[R] H) →ₗ[R] H →ₗ[R] (V ⊗[R] H) :=
      ((AlgHom.ofLinearMap
        (LinearMap.lTensorHom V ∘ₗ (mulRightAlgHom R H).toLinearMap)
        (by ext v a; simp)
        (by intro a b; ext v c; simp)).toLinearMap ∘ₗ
          (MulOpposite.opLinearEquiv R).toLinearMap).flip
    change Comodule.cofreeCoact R H V ((LinearMap.mulRight R h).lTensor V z) =
      TensorProduct.map₂ actV (LinearMap.mul R H) (Comodule.cofreeCoact R H V z)
        (Coalgebra.comul h)
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, hz₁, hz₂]
    | tmul v a =>
      simp only [LinearMap.lTensor_tmul, LinearMap.mulRight_apply, Comodule.cofreeCoact_tmul,
        Bialgebra.comul_mul]
      generalize Coalgebra.comul (R := R) a = u, Coalgebra.comul (R := R) h = w
      induction u using TensorProduct.inductionOn with
      | add u₁ u₂ hu₁ hu₂ =>
        simp only [add_mul, TensorProduct.tmul_add, map_add, LinearMap.add_apply, hu₁, hu₂]
      | tmul p q =>
        induction w using TensorProduct.inductionOn with
        | add w₁ w₂ hw₁ hw₂ =>
          simp only [mul_add, TensorProduct.tmul_add, map_add, hw₁, hw₂]
        | tmul c d =>
          simp [actV, mulRightAlgHom, Algebra.TensorProduct.tmul_mul_tmul]

/-- The underlying comodule of `RightHopfModule.cofree` is `Comodule.cofree`. -/
@[simp]
theorem cofree_toComodule (V : Type w) [AddCommMonoid V] [Module R V] :
    (cofree R H V).toComodule = Comodule.cofree R H V :=
  (rfl)

/-- The coaction of `RightHopfModule.cofree` is `Comodule.cofreeCoact`. -/
@[simp]
theorem cofree_coact (V : Type w) [AddCommMonoid V] [Module R V] :
    (cofree R H V).coact = Comodule.cofreeCoact R H V :=
  (rfl)

/-- The right `H`-action of `RightHopfModule.cofree` acts on the right tensor factor. -/
@[simp]
theorem cofree_action_op_apply (V : Type w) [AddCommMonoid V] [Module R V]
    (h : H) (z : V ⊗[R] H) :
    (cofree R H V).action (MulOpposite.op h) z = (LinearMap.mulRight R h).lTensor V z :=
  (rfl)

/-- On pure tensors, `RightHopfModule.cofree` acts by `(v ⊗ₜ a) ◁ h = v ⊗ₜ (a * h)`. -/
theorem cofree_action_op_tmul (V : Type w) [AddCommMonoid V] [Module R V]
    (h : H) (v : V) (a : H) :
    (cofree R H V).action (MulOpposite.op h) (v ⊗ₜ[R] a) = v ⊗ₜ[R] (a * h) :=
  (rfl)

/-- Every vector `v ⊗ₜ 1` in `V ⊗[R] H` is coinvariant in the cofree right Hopf module. -/
theorem tmul_one_mem_cofree_coinvariants {V : Type w} [AddCommMonoid V] [Module R V] (v : V) :
    v ⊗ₜ[R] (1 : H) ∈ (cofree R H V).coinvariants := by
  rw [mem_coinvariants, cofree_coact, Comodule.cofreeCoact_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def, TensorProduct.assoc_symm_tmul]

variable (R H) in
/-- The coinvariants of the cofree right Hopf module `V ⊗[R] H` are canonically linearly
equivalent to `V` via `v ↦ v ⊗ₜ 1` and `z ↦ (id ⊗ ε)(z)`. -/
noncomputable def cofreeCoinvariantsEquiv (V : Type w) [AddCommMonoid V] [Module R V] :
    V ≃ₗ[R] (cofree R H V).coinvariants :=
  LinearEquiv.ofLinearMap
    (((TensorProduct.mk R V H).flip 1).codRestrict (cofree R H V).coinvariants
      tmul_one_mem_cofree_coinvariants)
    ((TensorProduct.rid R V).toLinearMap ∘ₗ Coalgebra.counit.lTensor V ∘ₗ
      (cofree R H V).coinvariants.subtype)
    (by
      ext z
      change TensorProduct.rid R V (Coalgebra.counit.lTensor V (z : V ⊗[R] H)) ⊗ₜ[R] (1 : H) =
        (z : V ⊗[R] H)
      have hz : Comodule.cofreeCoact R H V (z : V ⊗[R] H) = (z : V ⊗[R] H) ⊗ₜ[R] (1 : H) :=
        ((cofree R H V).mem_coinvariants).mp z.2
      have hret := LinearMap.congr_fun
        (Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := H) (M := V))
        (z : V ⊗[R] H)
      simpa only [LinearMap.comp_apply, hz, LinearMap.rTensor_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe] using hret)
    (by
      ext v
      change TensorProduct.rid R V (Coalgebra.counit.lTensor V (v ⊗ₜ[R] (1 : H))) = v
      simp)

/-- `cofreeCoinvariantsEquiv` embeds `v : V` as `v ⊗ₜ 1`. -/
@[simp]
theorem coe_cofreeCoinvariantsEquiv_apply {V : Type w} [AddCommMonoid V] [Module R V] (v : V) :
    (cofreeCoinvariantsEquiv R H V v : V ⊗[R] H) = v ⊗ₜ[R] (1 : H) :=
  (rfl)

/-- The inverse of `cofreeCoinvariantsEquiv` contracts the right tensor factor with the counit. -/
@[simp]
theorem cofreeCoinvariantsEquiv_symm_apply {V : Type w} [AddCommMonoid V] [Module R V]
    (z : (cofree R H V).coinvariants) :
    (cofreeCoinvariantsEquiv R H V).symm z =
      TensorProduct.rid R V (Coalgebra.counit.lTensor V (z : V ⊗[R] H)) :=
  (rfl)

/-! ### Morphisms and equivalences of right Hopf modules -/

/-- A morphism of right Hopf modules: an `R`-linear map commuting with both the right `H`-coactions
and the right `H`-actions. -/
structure Hom (μ : RightHopfModule R H M) (ν : RightHopfModule R H N)
    extends M →ₗ[R] N where
  /-- A right Hopf module morphism commutes with the coactions. -/
  map_coact' :
    TensorProduct.map toLinearMap LinearMap.id ∘ₗ μ.coact = ν.coact ∘ₗ toLinearMap
  /-- A right Hopf module morphism commutes with the right `H`-actions. -/
  map_action' : ∀ (h : Hᵐᵒᵖ) (m : M), toLinearMap (μ.action h m) = ν.action h (toLinearMap m)

namespace Hom

variable {P Q : Type*}
variable [AddCommMonoid P] [Module R P]
variable [AddCommMonoid Q] [Module R Q]
variable {μ : RightHopfModule R H M} {ν : RightHopfModule R H N}
variable {ξ : RightHopfModule R H P} {ζ : RightHopfModule R H Q}

instance : FunLike (Hom μ ν) M N where
  coe f := f.toLinearMap
  coe_injective f g h := by
    have hlin : f.toLinearMap = g.toLinearMap := DFunLike.coe_injective h
    cases f
    cases g
    cases hlin
    rfl

instance : LinearMapClass (Hom μ ν) R M N where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

/-- Morphisms of right Hopf modules are determined by their underlying functions. -/
@[ext]
theorem ext {f g : Hom μ ν} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h

/-- Coercing `f.toLinearMap` to a function agrees with coercing `f`. -/
@[simp]
theorem coe_toLinearMap (f : Hom μ ν) : ⇑f.toLinearMap = f :=
  (rfl)

/-- Coercing a constructed `Hom` to a function yields the underlying linear map. -/
@[simp]
theorem coe_mk (φ : M →ₗ[R] N) (h₁ h₂) : ⇑(⟨φ, h₁, h₂⟩ : Hom μ ν) = φ :=
  (rfl)

/-- Forget the right `H`-action compatibility of a Hopf-module morphism. -/
def toComoduleHom (f : Hom μ ν) :
    letI := μ.toComodule; letI := ν.toComodule; Comodule.Hom R H M N :=
  letI := μ.toComodule
  letI := ν.toComodule
  { toLinearMap := f.toLinearMap
    map_coact := f.map_coact' }

/-- `toComoduleHom` has the same underlying function as the Hopf-module morphism. -/
@[simp]
theorem toComoduleHom_apply (f : Hom μ ν) (m : M) : f.toComoduleHom m = f m :=
  (rfl)

/-- Pointwise coaction equivariance of a morphism of right Hopf modules. -/
@[simp]
theorem map_coact_apply (f : Hom μ ν) (m : M) :
    TensorProduct.map f.toLinearMap LinearMap.id (μ.coact m) = ν.coact (f m) :=
  LinearMap.congr_fun f.map_coact' m

/-- Pointwise right `H`-action equivariance of a morphism of right Hopf modules. -/
@[simp]
theorem map_action (f : Hom μ ν) (h : Hᵐᵒᵖ) (m : M) :
    f (μ.action h m) = ν.action h (f m) :=
  f.map_action' h m

/-- The identity morphism of a right Hopf module. -/
def id (μ : RightHopfModule R H M) : Hom μ μ where
  toLinearMap := LinearMap.id
  map_coact' := by ext m; simp
  map_action' _ _ := rfl

/-- Composition of morphisms of right Hopf modules. -/
def comp (g : Hom ν ξ) (f : Hom μ ν) : Hom μ ξ where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_coact' := by
    let _ := μ.toComodule
    let _ := ν.toComodule
    let _ := ξ.toComodule
    exact (g.toComoduleHom.comp f.toComoduleHom).map_coact
  map_action' h m := by simp

/-- The identity morphism acts as the identity function. -/
@[simp]
theorem id_apply (μ : RightHopfModule R H M) (m : M) : id μ m = m :=
  (rfl)

/-- Composition of morphisms acts by function composition. -/
@[simp]
theorem comp_apply (g : Hom ν ξ) (f : Hom μ ν) (m : M) : g.comp f m = g (f m) :=
  (rfl)

/-- Left identity law for composition of Hopf-module morphisms. -/
@[simp]
theorem id_comp (f : Hom μ ν) : (id ν).comp f = f := by
  ext; rfl

/-- Right identity law for composition of Hopf-module morphisms. -/
@[simp]
theorem comp_id (f : Hom μ ν) : f.comp (id μ) = f := by
  ext; rfl

/-- Associativity of composition of Hopf-module morphisms. -/
theorem comp_assoc (h : Hom ξ ζ) (g : Hom ν ξ) (f : Hom μ ν) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext; rfl

/-- A morphism of right Hopf modules sends coinvariants to coinvariants. -/
theorem map_mem_coinvariants (f : Hom μ ν) {m : M} (hm : m ∈ μ.coinvariants) :
    f m ∈ ν.coinvariants := by
  let _ := μ.toComodule
  let _ := ν.toComodule
  exact f.toComoduleHom.mem_fixedSubcomodule hm

/-- Restrict a morphism of right Hopf modules to the coinvariant submodules. -/
def mapCoinvariants (f : Hom μ ν) : μ.coinvariants →ₗ[R] ν.coinvariants :=
  f.toLinearMap.restrict fun _ hm ↦ f.map_mem_coinvariants hm

/-- `mapCoinvariants` acts on underlying vectors by `f`. -/
@[simp]
theorem coe_mapCoinvariants (f : Hom μ ν) (m : μ.coinvariants) :
    (f.mapCoinvariants m : N) = f (m : M) :=
  (rfl)

/-- Restricting the identity morphism to coinvariants gives the identity linear map. -/
@[simp]
theorem mapCoinvariants_id (μ : RightHopfModule R H M) :
    (id μ).mapCoinvariants = LinearMap.id := by
  ext; rfl

/-- Restriction to coinvariants is functorial under composition. -/
@[simp]
theorem mapCoinvariants_comp (g : Hom ν ξ) (f : Hom μ ν) :
    (g.comp f).mapCoinvariants = g.mapCoinvariants.comp f.mapCoinvariants := by
  ext; rfl

end Hom

/-- An equivalence of right Hopf modules: an `R`-linear equivalence commuting with both the right
`H`-coactions and the right `H`-actions. -/
structure Equiv (μ : RightHopfModule R H M) (ν : RightHopfModule R H N)
    extends M ≃ₗ[R] N where
  /-- A right Hopf module equivalence commutes with the coactions. -/
  map_coact' :
    TensorProduct.map toLinearEquiv.toLinearMap LinearMap.id ∘ₗ μ.coact =
      ν.coact ∘ₗ toLinearEquiv.toLinearMap
  /-- A right Hopf module equivalence commutes with the right `H`-actions. -/
  map_action' : ∀ (h : Hᵐᵒᵖ) (m : M),
    toLinearEquiv (μ.action h m) = ν.action h (toLinearEquiv m)

namespace Equiv

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {μ : RightHopfModule R H M} {ν : RightHopfModule R H N} {ξ : RightHopfModule R H P}

instance : EquivLike (Equiv μ ν) M N where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e₁ e₂ h _ := by
    have he : e₁.toLinearEquiv = e₂.toLinearEquiv := DFunLike.coe_injective h
    cases e₁
    cases e₂
    cases he
    rfl

instance : LinearEquivClass (Equiv μ ν) R M N where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

/-- Equivalences of right Hopf modules are determined by their underlying functions. -/
@[ext]
theorem ext {e₁ e₂ : Equiv μ ν} (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

/-- Coercing `e.toLinearEquiv` to a function agrees with coercing `e`. -/
@[simp]
theorem coe_toLinearEquiv (e : Equiv μ ν) : ⇑e.toLinearEquiv = e :=
  (rfl)

/-- View an equivalence of right Hopf modules as a morphism of right Hopf modules. -/
def toHom (e : Equiv μ ν) : Hom μ ν where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_coact' := e.map_coact'
  map_action' := e.map_action'

/-- `toHom` has the same underlying function as the equivalence. -/
@[simp]
theorem toHom_apply (e : Equiv μ ν) (m : M) : e.toHom m = e m :=
  (rfl)

/-- Pointwise coaction equivariance of an equivalence of right Hopf modules. -/
@[simp]
theorem map_coact_apply (e : Equiv μ ν) (m : M) :
    TensorProduct.map e.toLinearEquiv.toLinearMap LinearMap.id (μ.coact m) = ν.coact (e m) :=
  e.toHom.map_coact_apply m

/-- Pointwise right `H`-action equivariance of an equivalence of right Hopf modules. -/
@[simp]
theorem map_action (e : Equiv μ ν) (h : Hᵐᵒᵖ) (m : M) :
    e (μ.action h m) = ν.action h (e m) :=
  e.map_action' h m

/-- The identity equivalence of a right Hopf module. -/
def refl (μ : RightHopfModule R H M) : Equiv μ μ where
  toLinearEquiv := LinearEquiv.refl R M
  map_coact' := by ext m; simp
  map_action' _ _ := rfl

/-- The inverse of an equivalence of right Hopf modules. -/
def symm (e : Equiv μ ν) : Equiv ν μ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_coact' := by
    ext n
    apply (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R H)).injective
    have hmap :
        TensorProduct.map e.toLinearEquiv.toLinearMap LinearMap.id
            (TensorProduct.map e.toLinearEquiv.symm.toLinearMap LinearMap.id (ν.coact n)) =
          ν.coact n := by
      rw [TensorProduct.map_map, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, LinearMap.comp_id, TensorProduct.map_id, LinearMap.id_apply]
    have hrhs :
        TensorProduct.map e.toLinearEquiv.toLinearMap LinearMap.id
            (μ.coact (e.toLinearEquiv.symm n)) = ν.coact n := by
      rw [e.map_coact_apply]
      exact congrArg ν.coact (e.toLinearEquiv.apply_symm_apply n)
    exact hmap.trans hrhs.symm
  map_action' h n := by
    apply e.toLinearEquiv.injective
    rw [e.map_action', e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.apply_symm_apply]

/-- Composition of equivalences of right Hopf modules. -/
def trans (e₁ : Equiv μ ν) (e₂ : Equiv ν ξ) : Equiv μ ξ where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_coact' := (e₂.toHom.comp e₁.toHom).map_coact'
  map_action' := (e₂.toHom.comp e₁.toHom).map_action'

/-- The reflexive equivalence acts as the identity function. -/
@[simp]
theorem refl_apply (μ : RightHopfModule R H M) (m : M) : refl μ m = m :=
  (rfl)

/-- Transitivity of equivalences acts by function composition. -/
@[simp]
theorem trans_apply (e₁ : Equiv μ ν) (e₂ : Equiv ν ξ) (m : M) :
    (e₁.trans e₂) m = e₂ (e₁ m) :=
  (rfl)

/-- Applying `e.symm` after `e` is the identity. -/
@[simp]
theorem symm_apply_apply (e : Equiv μ ν) (m : M) : e.symm (e m) = m :=
  e.toLinearEquiv.symm_apply_apply m

/-- Applying `e` after `e.symm` is the identity. -/
@[simp]
theorem apply_symm_apply (e : Equiv μ ν) (n : N) : e (e.symm n) = n :=
  e.toLinearEquiv.apply_symm_apply n

/-- Restrict an equivalence of right Hopf modules to a linear equivalence on coinvariants. -/
def coinvariantsEquiv (e : Equiv μ ν) : μ.coinvariants ≃ₗ[R] ν.coinvariants :=
  LinearEquiv.ofLinearMap e.toHom.mapCoinvariants e.symm.toHom.mapCoinvariants
    (by ext x; exact e.apply_symm_apply x)
    (by ext x; exact e.symm_apply_apply x)

/-- `coinvariantsEquiv` acts on underlying vectors by `e`. -/
@[simp]
theorem coe_coinvariantsEquiv_apply (e : Equiv μ ν) (m : μ.coinvariants) :
    (e.coinvariantsEquiv m : N) = e (m : M) :=
  (rfl)

/-- `coinvariantsEquiv.symm` acts on underlying vectors by `e.symm`. -/
@[simp]
theorem coe_coinvariantsEquiv_symm_apply (e : Equiv μ ν) (n : ν.coinvariants) :
    (e.coinvariantsEquiv.symm n : M) = e.symm (n : N) :=
  (rfl)

end Equiv

end Bialgebra

/-! ### Coinvariant projection and the Fundamental Theorem of Hopf Modules -/

section HopfAlgebra

open _root_.HopfAlgebra

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M]

/-- Contract a tensor `x ⊗ a : M ⊗[R] H` to `x ◁ S(a)`. -/
private noncomputable def evalActionAntipode (μ : RightHopfModule R H M) : M ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift μ.actRightLinear ∘ₗ (antipode R).lTensor M

@[simp]
private theorem evalActionAntipode_tmul (μ : RightHopfModule R H M) (m : M) (a : H) :
    μ.evalActionAntipode (m ⊗ₜ[R] a) = μ.action (MulOpposite.op (antipode R a)) m :=
  (rfl)

/-- The coinvariant projection `P : M →ₗ[R] M` on a right Hopf module over a Hopf algebra, sending
`m` with coaction `∑ m₀ ⊗ m₁` to `∑ m₀ ◁ S(m₁)`. -/
noncomputable def coinvariantProj (μ : RightHopfModule R H M) : M →ₗ[R] M :=
  μ.evalActionAntipode ∘ₗ μ.coact

/-- The coinvariant projection fixes every coinvariant element. -/
@[simp]
theorem coinvariantProj_of_mem_coinvariants (μ : RightHopfModule R H M) {m : M}
    (hm : m ∈ μ.coinvariants) : μ.coinvariantProj m = m := by
  rw [coinvariantProj, LinearMap.comp_apply, μ.mem_coinvariants.mp hm, evalActionAntipode_tmul,
    antipode_one, action_op_one_apply]

/-- The coinvariant projection converts the right `H`-action into scalar multiplication by the
counit: `P(m ◁ h) = ε(h) • P(m)`. -/
@[simp]
theorem coinvariantProj_action_op (μ : RightHopfModule R H M) (h : H) (m : M) :
    μ.coinvariantProj (μ.action (MulOpposite.op h) m) =
      Coalgebra.counit (R := R) h • μ.coinvariantProj m := by
  rw [coinvariantProj, LinearMap.comp_apply, μ.coact_action]
  change μ.evalActionAntipode
      (TensorProduct.map₂ μ.actRightLinear (LinearMap.mul R H) (μ.coact m)
        (Coalgebra.comul h)) = Coalgebra.counit (R := R) h • μ.evalActionAntipode (μ.coact m)
  generalize μ.coact m = z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, smul_add, hz₁, hz₂]
  | tmul x a =>
    classical
    rw [TensorProduct.map₂_apply_tmul, ← (ℛ R h).eq, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, actRightLinear_apply, LinearMap.mul_apply',
      evalActionAntipode_tmul, antipode_mul_antidistrib, ← μ.action_op_mul_apply]
    have hsum :
        ∑ i ∈ (ℛ R h).index,
          μ.actRightLinear x
            ((ℛ R h).left i * (antipode R ((ℛ R h).right i) * antipode R a)) =
          μ.actRightLinear x
            ((∑ i ∈ (ℛ R h).index, (ℛ R h).left i * antipode R ((ℛ R h).right i)) *
              antipode R a) := by
      rw [← map_sum, Finset.sum_mul]
      exact congrArg (μ.actRightLinear x) (Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm)
    change ∑ i ∈ (ℛ R h).index,
        μ.actRightLinear x
          ((ℛ R h).left i * (antipode R ((ℛ R h).right i) * antipode R a)) = _
    rw [hsum, sum_mul_antipode_eq_smul, smul_mul_assoc, one_mul, map_smul]
    rfl

/-- Auxiliary trilinear contraction `(z, b) ↦ map₂(◁, *)(z, Δ(S(b)))` computing the coaction of
`evalActionAntipode`. -/
private noncomputable def coactEvalAntipodeAux (μ : RightHopfModule R H M) :
    (M ⊗[R] H) ⊗[R] H →ₗ[R] M ⊗[R] H :=
  TensorProduct.lift
    (LinearMap.compl₂ (TensorProduct.map₂ μ.actRightLinear (LinearMap.mul R H))
      (Coalgebra.comul ∘ₗ antipode R))

private theorem coact_evalActionAntipode (μ : RightHopfModule R H M) (t : M ⊗[R] H) :
    μ.coact (μ.evalActionAntipode t) = μ.coactEvalAntipodeAux (μ.coact.rTensor H t) := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
  | tmul x b =>
    simpa [coactEvalAntipodeAux, evalActionAntipode_tmul] using μ.coact_action x (antipode R b)

private theorem coactEvalAntipodeAux_assoc_symm_tmul (μ : RightHopfModule R H M)
    (x : M) (u : H ⊗[R] H) :
    μ.coactEvalAntipodeAux ((TensorProduct.assoc R M H H).symm (x ⊗ₜ[R] u)) =
      (μ.actRightLinear x).rTensor H
        (LinearMap.mul' R (H ⊗[R] H)
          (TensorProduct.map
            (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toLinearMap
            (Coalgebra.comul ∘ₗ antipode R) u)) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [TensorProduct.tmul_add, map_add, hu₁, hu₂]
  | tmul a b =>
    simp only [TensorProduct.assoc_symm_tmul, coactEvalAntipodeAux, TensorProduct.lift.tmul,
      LinearMap.compl₂_apply, TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]
    generalize Coalgebra.comul (R := R) (antipode R b) = w
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ hw₁ hw₂ => simp only [map_add, LinearMap.mul'_apply, mul_add, hw₁, hw₂]
    | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem coactEvalAntipodeAux_assoc_symm_lTensor_comul (μ : RightHopfModule R H M)
    (t : M ⊗[R] H) :
    μ.coactEvalAntipodeAux ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M t)) =
      μ.evalActionAntipode t ⊗ₜ[R] (1 : H) := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simp only [map_add, TensorProduct.add_tmul, ht₁, ht₂]
  | tmul x h =>
    rw [LinearMap.lTensor_tmul, μ.coactEvalAntipodeAux_assoc_symm_tmul,
      HopfAlgebra.mul_includeRight_comul_antipode_apply, LinearMap.rTensor_tmul]
    rfl

/-- Every value of `coinvariantProj` lies in `μ.coinvariants`. -/
theorem coinvariantProj_mem_coinvariants (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantProj m ∈ μ.coinvariants := by
  let _ := μ.toComodule
  rw [mem_coinvariants]
  change μ.coact (μ.evalActionAntipode (μ.coact m)) =
    μ.evalActionAntipode (μ.coact m) ⊗ₜ[R] (1 : H)
  rw [μ.coact_evalActionAntipode, ← Comodule.coassoc_symm_apply (R := R) (C := H) (M := M) m,
    μ.coactEvalAntipodeAux_assoc_symm_lTensor_comul]

/-- The coinvariant projection is idempotent. -/
@[simp]
theorem coinvariantProj_coinvariantProj (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantProj (μ.coinvariantProj m) = μ.coinvariantProj m :=
  μ.coinvariantProj_of_mem_coinvariants (μ.coinvariantProj_mem_coinvariants m)

/-- The `R`-linear projection from a right Hopf module onto its coinvariant submodule. -/
noncomputable def toCoinvariants (μ : RightHopfModule R H M) : M →ₗ[R] μ.coinvariants :=
  μ.coinvariantProj.codRestrict μ.coinvariants μ.coinvariantProj_mem_coinvariants

/-- `toCoinvariants` agrees on underlying vectors with `coinvariantProj`. -/
@[simp]
theorem coe_toCoinvariants (μ : RightHopfModule R H M) (m : M) :
    (μ.toCoinvariants m : M) = μ.coinvariantProj m :=
  (rfl)

/-- `toCoinvariants` is a retraction of the inclusion `μ.coinvariants.subtype`. -/
@[simp]
theorem toCoinvariants_coe (μ : RightHopfModule R H M) (v : μ.coinvariants) :
    μ.toCoinvariants (v : M) = v :=
  Subtype.ext (μ.coinvariantProj_of_mem_coinvariants v.2)

/-- `toCoinvariants` converts the right `H`-action into scalar multiplication by the counit. -/
@[simp]
theorem toCoinvariants_action_op (μ : RightHopfModule R H M) (h : H) (m : M) :
    μ.toCoinvariants (μ.action (MulOpposite.op h) m) =
      Coalgebra.counit (R := R) h • μ.toCoinvariants m :=
  Subtype.ext (μ.coinvariantProj_action_op h m)

/-- The forward linear map `μ.coinvariants ⊗[R] H →ₗ[R] M` of the Hopf-module structure theorem,
sending `v ⊗ h` to `(v : M) ◁ h`. -/
private def fromCoinvariantsTensor (μ : RightHopfModule R H M) :
    μ.coinvariants ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift (μ.actRightLinear ∘ₗ μ.coinvariants.subtype)

@[simp]
private theorem fromCoinvariantsTensor_tmul (μ : RightHopfModule R H M)
    (v : μ.coinvariants) (h : H) :
    μ.fromCoinvariantsTensor (v ⊗ₜ[R] h) = μ.action (MulOpposite.op h) (v : M) :=
  (rfl)

/-- Auxiliary contraction `(x ⊗ a) ⊗ b ↦ (x ◁ S(a)) ◁ b` for the reconstruction identity. -/
private noncomputable def evalAntipodeActAux (μ : RightHopfModule R H M) :
    (M ⊗[R] H) ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift (LinearMap.compl₂ (LinearMap.comp μ.actRightLinear μ.evalActionAntipode)
    LinearMap.id)

private theorem lift_actRightLinear_rTensor_coinvariantProj (μ : RightHopfModule R H M)
    (t : M ⊗[R] H) :
    TensorProduct.lift μ.actRightLinear (μ.coinvariantProj.rTensor H t) =
      μ.evalAntipodeActAux (μ.coact.rTensor H t) := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
  | tmul x b => rfl

private theorem evalAntipodeActAux_assoc_symm_lTensor_comul (μ : RightHopfModule R H M)
    (t : M ⊗[R] H) :
    μ.evalAntipodeActAux ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M t)) =
      TensorProduct.rid R M (Coalgebra.counit.lTensor M t) := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
  | tmul x h =>
    classical
    rw [LinearMap.lTensor_tmul, ← (ℛ R h).eq, TensorProduct.tmul_sum, map_sum, map_sum]
    simp only [TensorProduct.assoc_symm_tmul, evalAntipodeActAux, TensorProduct.lift.tmul,
      LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.id_apply, evalActionAntipode_tmul,
      actRightLinear_apply, ← μ.action_op_mul_apply]
    have hsum :
        ∑ i ∈ (ℛ R h).index,
          μ.actRightLinear x (antipode R ((ℛ R h).left i) * (ℛ R h).right i) =
          μ.actRightLinear x
            (∑ i ∈ (ℛ R h).index, antipode R ((ℛ R h).left i) * (ℛ R h).right i) :=
      (map_sum (μ.actRightLinear x) _ _).symm
    change ∑ i ∈ (ℛ R h).index,
        μ.actRightLinear x (antipode R ((ℛ R h).left i) * (ℛ R h).right i) = _
    rw [hsum, sum_antipode_mul_eq_smul, map_smul, actRightLinear_apply, action_op_one_apply]
    simp

private theorem fromCoinvariantsTensor_comp_toCoinvariants_rTensor_coact
    (μ : RightHopfModule R H M) (m : M) :
    μ.fromCoinvariantsTensor (μ.toCoinvariants.rTensor H (μ.coact m)) = m := by
  let _ := μ.toComodule
  have hfactor :
      μ.fromCoinvariantsTensor (μ.toCoinvariants.rTensor H (μ.coact m)) =
        TensorProduct.lift μ.actRightLinear (μ.coinvariantProj.rTensor H (μ.coact m)) := by
    have hsub : μ.coinvariants.subtype ∘ₗ μ.toCoinvariants = μ.coinvariantProj := rfl
    rw [← hsub, LinearMap.rTensor_comp_apply]
    generalize μ.toCoinvariants.rTensor H (μ.coact m) = z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul v h => rfl
  rw [hfactor, μ.lift_actRightLinear_rTensor_coinvariantProj,
    ← Comodule.coassoc_symm_apply (R := R) (C := H) (M := M) m,
    μ.evalAntipodeActAux_assoc_symm_lTensor_comul, Comodule.rid_lTensor_counit_coact]

private theorem toCoinvariants_rTensor_coact_fromCoinvariantsTensor
    (μ : RightHopfModule R H M) (z : μ.coinvariants ⊗[R] H) :
    μ.toCoinvariants.rTensor H (μ.coact (μ.fromCoinvariantsTensor z)) = z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
  | tmul v h =>
    rw [fromCoinvariantsTensor_tmul, μ.coact_action_of_mem_coinvariants v.2 h,
      ← LinearMap.rTensor_comp_apply]
    have hcomp : μ.toCoinvariants ∘ₗ μ.actRightLinear (v : M) =
        LinearMap.toSpanSingleton R μ.coinvariants v ∘ₗ Coalgebra.counit := by
      ext a
      simp [LinearMap.toSpanSingleton_apply]
    change (μ.toCoinvariants ∘ₗ μ.actRightLinear (v : M)).rTensor H (Coalgebra.comul h) = v ⊗ₜ[R] h
    rw [hcomp, LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul]
    simp

/-- **The Fundamental Theorem of Hopf Modules** (Larson–Sweedler): every right Hopf module `μ` over
a Hopf algebra `H` is canonically equivalent, as a right Hopf module, to the cofree right Hopf
module `μ.coinvariants ⊗[R] H` on its submodule of coinvariants. -/
noncomputable def coinvariantsTensorHopfEquiv (μ : RightHopfModule R H M) :
    (cofree R H μ.coinvariants).Equiv μ where
  toLinearEquiv := LinearEquiv.ofLinearMap
    μ.fromCoinvariantsTensor
    (μ.toCoinvariants.rTensor H ∘ₗ μ.coact)
    (LinearMap.ext μ.fromCoinvariantsTensor_comp_toCoinvariants_rTensor_coact)
    (LinearMap.ext μ.toCoinvariants_rTensor_coact_fromCoinvariantsTensor)
  map_coact' := by
    refine TensorProduct.ext' fun v h ↦ ?_
    change TensorProduct.map μ.fromCoinvariantsTensor LinearMap.id
        ((cofree R H μ.coinvariants).coact (v ⊗ₜ[R] h)) =
      μ.coact (μ.fromCoinvariantsTensor (v ⊗ₜ[R] h))
    rw [cofree_coact, Comodule.cofreeCoact_tmul, fromCoinvariantsTensor_tmul,
      μ.coact_action_of_mem_coinvariants v.2 h]
    generalize Coalgebra.comul (R := R) h = u
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ hu₁ hu₂ => simp only [TensorProduct.tmul_add, map_add, hu₁, hu₂]
    | tmul a b => rfl
  map_action' h z := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective h
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul v b =>
      change μ.fromCoinvariantsTensor ((cofree R H μ.coinvariants).action (MulOpposite.op a)
          (v ⊗ₜ[R] b)) =
        μ.action (MulOpposite.op a) (μ.fromCoinvariantsTensor (v ⊗ₜ[R] b))
      simp only [cofree_action_op_tmul, fromCoinvariantsTensor_tmul, μ.action_op_mul_apply]

/-- **The Fundamental Theorem of Hopf Modules** as an `R`-linear equivalence
`μ.coinvariants ⊗[R] H ≃ₗ[R] M`. It sends `v ⊗ h` to `(v : M) ◁ h` and has inverse
`m ↦ ∑ P(m₀) ⊗ m₁`. -/
noncomputable def coinvariantsTensorEquiv (μ : RightHopfModule R H M) :
    μ.coinvariants ⊗[R] H ≃ₗ[R] M :=
  μ.coinvariantsTensorHopfEquiv.toLinearEquiv

/-- On pure tensors, `coinvariantsTensorEquiv` sends `v ⊗ₜ h` to `(v : M) ◁ h`. -/
@[simp]
theorem coinvariantsTensorEquiv_tmul (μ : RightHopfModule R H M) (v : μ.coinvariants) (h : H) :
    μ.coinvariantsTensorEquiv (v ⊗ₜ[R] h) = μ.action (MulOpposite.op h) (v : M) :=
  (rfl)

/-- The inverse of `coinvariantsTensorEquiv` sends `m` to `(P ⊗ id)(ρ(m))`. -/
@[simp]
theorem coinvariantsTensorEquiv_symm_apply (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantsTensorEquiv.symm m = μ.toCoinvariants.rTensor H (μ.coact m) :=
  (rfl)

/-- `coinvariantsTensorEquiv` intertwines right multiplication on the `H` tensor factor with the
right `H`-action on `M`. -/
@[simp]
theorem coinvariantsTensorEquiv_lTensor_mulRight (μ : RightHopfModule R H M) (h : H)
    (z : μ.coinvariants ⊗[R] H) :
    μ.coinvariantsTensorEquiv ((LinearMap.mulRight R h).lTensor μ.coinvariants z) =
      μ.action (MulOpposite.op h) (μ.coinvariantsTensorEquiv z) :=
  μ.coinvariantsTensorHopfEquiv.map_action (MulOpposite.op h) z

/-- `coinvariantsTensorEquiv` intertwines the cofree coaction on `μ.coinvariants ⊗[R] H` with the
coaction on `M`. -/
theorem coact_coinvariantsTensorEquiv (μ : RightHopfModule R H M) (z : μ.coinvariants ⊗[R] H) :
    μ.coact (μ.coinvariantsTensorEquiv z) =
      μ.coinvariantsTensorEquiv.toLinearMap.rTensor H
        (Comodule.cofreeCoact R H μ.coinvariants z) :=
  (μ.coinvariantsTensorHopfEquiv.map_coact_apply z).symm

end HopfAlgebra

end RightHopfModule

end TauCeti
