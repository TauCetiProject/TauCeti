/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.ZMod

/-!
# The continuous `ZMod n`-dual of a topological group

The continuous characters of a topological group with values in the multiplicative encoding
`Multiplicative (ZMod n)` of `ZMod n` form a commutative group, written additively as the
**continuous `ZMod n`-dual** `TauCeti.continuousZModDual n G`. Scalar `n` kills the target, hence
the character group as well, so the dual is a `ZMod n`-module; for a prime `p` it is an
`𝔽_p`-vector space, the discrete companion of a compact `𝔽_p`-vector group.

When the group is itself commutative with a `ZMod p`-module structure on its additive copy — for a
prime `p`, an elementary abelian group — a continuous character of it is in particular a linear
functional on that module, so `TauCeti.continuousZModDualToDual` reads the continuous dual inside
the algebraic dual, injectively.

## Main definitions

* `TauCeti.continuousZModDual`: the group of continuous `ZMod n`-valued characters of a topological
  group, written additively; for a prime `p` it is the continuous `𝔽_p`-dual.
* `TauCeti.continuousZModDual.evalₗ`: evaluation at a point, as a linear functional on the dual.
* `TauCeti.continuousZModHom.evalₗ`: evaluation at a point, as a linear map on continuous
  homomorphisms into a `ZMod n`-module.
* `TauCeti.continuousZModDualTensorEquiv`: for a finite free discrete `ZMod n`-module `A` (for
  prime `n = p`, any finite-dimensional discrete `𝔽_p`-vector space), evaluation identifies
  `continuousZModDual n G ⊗ A` with the continuous homomorphisms `G → A`.
* `ContinuousMonoidHom.continuousZModDualMap`: precomposition with a continuous homomorphism, the
  transpose map between continuous duals.
  The transpose of a topological group isomorphism is bijective
  (`ContinuousMulEquiv.continuousZModDualMap_bijective`).
* `TauCeti.continuousZModDualToDual`: a continuous `ZMod p`-valued character of a commutative group
  whose additive copy is a `ZMod p`-module, read as a linear functional on that module.
-/

public section

namespace TauCeti

universe u

section ZModDual

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- The **continuous `ZMod n`-dual** of a topological group: its group of continuous characters
with values in `ZMod n`, written additively so that it is a `ZMod n`-module. For a prime `p` it is
the continuous `𝔽_p`-dual, an `𝔽_p`-vector space. -/
abbrev continuousZModDual (n : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  Additive (G →ₜ* Multiplicative (ZMod n))

/-- Continuous homomorphisms into a topological `ZMod n`-module `A` form a `ZMod n`-module
pointwise: `n` kills `A`, hence also the homomorphism group. For `A = ZMod n` this is the
`ZMod n`-module structure on the continuous `ZMod n`-dual. -/
instance instModuleContinuousZModHom {A : Type*} [AddCommGroup A] [Module (ZMod n) A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] :
    Module (ZMod n) (Additive (G →ₜ* Multiplicative A)) :=
  AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd.injective
    simpa using ZModModule.char_nsmul_eq_zero n (Multiplicative.toAdd (Additive.toMul x g))

/-- **Evaluation at a point** `g : G`, as a `ZMod n`-linear functional on the continuous
`ZMod n`-dual of `G`: a character `χ` goes to its value at `g`, read additively. -/
def continuousZModDual.evalₗ (g : G) : continuousZModDual n G →ₗ[ZMod n] ZMod n :=
  AddMonoidHom.toZModLinearMap n
    { toFun χ := Multiplicative.toAdd (Additive.toMul χ g)
      map_zero' := by simp
      map_add' := fun χ ψ ↦ by simp [toMul_add] }

/-- Evaluation at `g` sends a character to its value at `g`. -/
@[simp]
theorem continuousZModDual.evalₗ_apply (g : G) (χ : continuousZModDual n G) :
    continuousZModDual.evalₗ g χ = Multiplicative.toAdd (Additive.toMul χ g) := by
  rfl

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- **Precomposition with a continuous homomorphism** `f : G →ₜ* H`, as a `ZMod n`-linear map from
the continuous `ZMod n`-dual of `H` to that of `G`: the transpose of `f`. -/
def _root_.ContinuousMonoidHom.continuousZModDualMap (f : G →ₜ* H) :
    continuousZModDual n H →ₗ[ZMod n] continuousZModDual n G :=
  AddMonoidHom.toZModLinearMap n
    { toFun χ := Additive.ofMul (χ.toMul.comp f)
      map_zero' := congrArg Additive.ofMul (ContinuousMonoidHom.ext fun _ ↦ rfl)
      map_add' := fun χ ψ ↦ congrArg Additive.ofMul (ContinuousMonoidHom.ext fun g ↦ by
        simp [toMul_add, ContinuousMonoidHom.mul_apply]) }

/-- The transpose of `f` precomposes a character of `H` with `f`. -/
theorem _root_.ContinuousMonoidHom.toMul_continuousZModDualMap (f : G →ₜ* H)
    (χ : continuousZModDual n H) : (f.continuousZModDualMap χ).toMul = χ.toMul.comp f := by
  rfl

/-- The transpose of `f` evaluates a character of `H` along `f`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.toMul_continuousZModDualMap_apply (f : G →ₜ* H)
    (χ : continuousZModDual n H) (g : G) : (f.continuousZModDualMap χ).toMul g = χ.toMul (f g) := by
  rfl

/-- The transpose of the identity is the identity. -/
@[simp]
theorem _root_.ContinuousMonoidHom.continuousZModDualMap_id :
    (ContinuousMonoidHom.id G).continuousZModDualMap (n := n) = LinearMap.id :=
  LinearMap.ext fun _ ↦ Additive.toMul.injective (ContinuousMonoidHom.ext fun _ ↦ rfl)

variable {K : Type*} [Group K] [TopologicalSpace K]

/-- The transpose of a composite is the composite of the transposes, in the reverse order. -/
@[simp]
theorem _root_.ContinuousMonoidHom.continuousZModDualMap_comp (g : H →ₜ* K) (f : G →ₜ* H) :
    (g.comp f).continuousZModDualMap (n := n) =
      f.continuousZModDualMap.comp g.continuousZModDualMap :=
  LinearMap.ext fun _ ↦ Additive.toMul.injective (ContinuousMonoidHom.ext fun _ ↦ rfl)

/-- **The transpose of a topological group isomorphism is bijective**: its inverse is the
transpose of the inverse isomorphism. -/
theorem _root_.ContinuousMulEquiv.continuousZModDualMap_bijective (e : G ≃ₜ* H) :
    Function.Bijective ((e : G →ₜ* H).continuousZModDualMap (n := n)) :=
  Function.bijective_iff_has_inverse.2 ⟨(e.symm : H →ₜ* G).continuousZModDualMap,
    fun _ ↦ Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by simp,
    fun _ ↦ Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by simp⟩

end ZModDual

section Tensor

open scoped TensorProduct

universe v

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type v} [AddCommGroup A] [Module (ZMod n) A] [TopologicalSpace A]

section

variable [IsTopologicalAddGroup A]

/-- **Evaluation of a continuous homomorphism at a point**, as a `ZMod n`-linear map. -/
def continuousZModHom.evalₗ (g : G) :
    Additive (G →ₜ* Multiplicative A) →ₗ[ZMod n] A :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun f ↦ Multiplicative.toAdd (Additive.toMul f g)
      map_zero' := by simp
      map_add' := fun f h ↦ by simp [toMul_add] }

/-- Evaluating a continuous homomorphism returns its value, read additively. -/
@[simp]
theorem continuousZModHom.evalₗ_apply (g : G) (f : Additive (G →ₜ* Multiplicative A)) :
    continuousZModHom.evalₗ (n := n) (A := A) g f =
      Multiplicative.toAdd (Additive.toMul f g) := by
  rw [continuousZModHom.evalₗ, AddMonoidHom.coe_toZModLinearMap]
  rfl

end

private def continuousZModDualTensorPure (x : continuousZModDual n G) (a : A) :
    Additive (G →ₜ* Multiplicative A) :=
  Additive.ofMul
    { toFun := fun g ↦ Multiplicative.ofAdd
        (Multiplicative.toAdd (Additive.toMul x g) • a)
      map_one' := by simp
      map_mul' := fun g h ↦ by simp [map_mul, add_smul]
      continuous_toFun := (continuous_of_discreteTopology : Continuous fun z :
        Multiplicative (ZMod n) ↦ Multiplicative.ofAdd (Multiplicative.toAdd z • a)).comp
          (Additive.toMul x).continuous }

@[simp]
private theorem continuousZModDualTensorPure_apply
    (x : continuousZModDual n G) (a : A) (g : G) :
    Additive.toMul (continuousZModDualTensorPure x a) g =
      Multiplicative.ofAdd (Multiplicative.toAdd (Additive.toMul x g) • a) :=
  rfl

@[simp]
private theorem continuousZModDualTensorPure_zero (x : continuousZModDual n G) :
    continuousZModDualTensorPure (A := A) x 0 = 0 :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by simp

@[simp]
private theorem continuousZModDualTensorPure_zero_left (a : A) :
    continuousZModDualTensorPure (G := G) (0 : continuousZModDual n G) a = 0 :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by simp

variable [IsTopologicalAddGroup A]

@[simp]
private theorem continuousZModDualTensorPure_add (x : continuousZModDual n G) (a b : A) :
    continuousZModDualTensorPure x (a + b) =
      continuousZModDualTensorPure x a + continuousZModDualTensorPure x b :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by
    simp [toMul_add, ContinuousMonoidHom.mul_apply, smul_add, ofAdd_add]

@[simp]
private theorem continuousZModDualTensorPure_add_left
    (x y : continuousZModDual n G) (a : A) :
    continuousZModDualTensorPure (x + y) a =
      continuousZModDualTensorPure x a + continuousZModDualTensorPure y a :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by
    simp [toMul_add, ContinuousMonoidHom.mul_apply, add_smul, ofAdd_add]

private def continuousZModDualTensorBilinear :
    continuousZModDual n G →ₗ[ZMod n] A →ₗ[ZMod n] Additive (G →ₜ* Multiplicative A) :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun x ↦ AddMonoidHom.toZModLinearMap n
        { toFun := continuousZModDualTensorPure x
          map_zero' := continuousZModDualTensorPure_zero x
          map_add' := continuousZModDualTensorPure_add x }
      map_zero' := LinearMap.ext fun a ↦ continuousZModDualTensorPure_zero_left a
      map_add' := fun x y ↦ LinearMap.ext fun a ↦
        continuousZModDualTensorPure_add_left x y a }

/-- The canonical evaluation map `continuousZModDual n G ⊗ A → Hom_cont(G, A)`. -/
def continuousZModDualTensorMap :
    continuousZModDual n G ⊗[ZMod n] A →ₗ[ZMod n] Additive (G →ₜ* Multiplicative A) :=
  TensorProduct.lift continuousZModDualTensorBilinear

/-- The evaluation map sends `x ⊗ a` to `g ↦ x(g) • a`. -/
@[simp]
theorem continuousZModDualTensorMap_tmul_apply
    (x : continuousZModDual n G) (a : A) (g : G) :
    Additive.toMul (continuousZModDualTensorMap (x ⊗ₜ a)) g =
      Multiplicative.ofAdd (Multiplicative.toAdd (Additive.toMul x g) • a) := by
  rw [continuousZModDualTensorMap, TensorProduct.lift.tmul]
  rfl

variable [DiscreteTopology A] {ι : Type*}

/-- The `i`-th coordinate, in the basis `b` of `A`, of a continuous homomorphism `G → A`. -/
private noncomputable def continuousZModHomCoord (b : Module.Basis ι (ZMod n) A)
    (f : Additive (G →ₜ* Multiplicative A)) (i : ι) : continuousZModDual n G :=
  Additive.ofMul
    { toFun := fun g ↦ Multiplicative.ofAdd
        (b.repr (Multiplicative.toAdd (Additive.toMul f g)) i)
      map_one' := by simp
      map_mul' := fun g h ↦ by simp [map_mul]
      continuous_toFun := (continuous_of_discreteTopology : Continuous fun a : A ↦
        Multiplicative.ofAdd (b.repr a i)).comp
          -- The additive/multiplicative wrappers have definitionally identical underlying maps.
          (show Continuous fun g ↦ Multiplicative.toAdd (Additive.toMul f g) from
            (Additive.toMul f).continuous) }

/-- A coordinate character evaluates by applying the corresponding basis coordinate. -/
@[simp]
private theorem continuousZModHomCoord_apply (b : Module.Basis ι (ZMod n) A)
    (f : Additive (G →ₜ* Multiplicative A)) (i : ι) (g : G) :
    Additive.toMul (continuousZModHomCoord b f i) g =
      Multiplicative.ofAdd (b.repr (continuousZModHom.evalₗ (n := n) (A := A) g f) i) :=
  rfl

@[simp]
private theorem continuousZModHomCoord_zero (b : Module.Basis ι (ZMod n) A) (i : ι) :
    continuousZModHomCoord (G := G) b 0 i = 0 :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by simp

@[simp]
private theorem continuousZModHomCoord_add (b : Module.Basis ι (ZMod n) A)
    (f h : Additive (G →ₜ* Multiplicative A)) (i : ι) :
    continuousZModHomCoord b (f + h) i =
      continuousZModHomCoord b f i + continuousZModHomCoord b h i :=
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun _ ↦ by
    simp [toMul_add, ContinuousMonoidHom.mul_apply, ofAdd_add]

/-- Taking a coordinate after evaluating a pure tensor scales the original character by that
coordinate of the tensor's second factor. -/
private theorem continuousZModHomCoord_tensorMap_tmul (b : Module.Basis ι (ZMod n) A)
    (x : continuousZModDual n G) (a : A) (i : ι) :
    continuousZModHomCoord b (continuousZModDualTensorMap (x ⊗ₜ a)) i = b.repr a i • x := by
  apply Additive.toMul.injective
  ext g
  apply Multiplicative.toAdd.injective
  -- The scalar action on characters is read off through the linear evaluation map at `g`.
  rw [← continuousZModDual.evalₗ_apply g (b.repr a i • x), map_smul]
  simp [mul_comm]

variable [Module.Free (ZMod n) A] [Module.Finite (ZMod n) A]

private noncomputable def continuousZModDualTensorInv :
    Additive (G →ₜ* Multiplicative A) →ₗ[ZMod n]
      continuousZModDual n G ⊗[ZMod n] A :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun f ↦ ∑ i, continuousZModHomCoord (Module.Free.chooseBasis (ZMod n) A) f i ⊗ₜ
        Module.Free.chooseBasis (ZMod n) A i
      map_zero' := by simp
      map_add' := fun f h ↦ by simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }

/-- The basis-dependent inverse is the sum of its coordinate characters tensored with the
corresponding basis vectors. -/
private theorem continuousZModDualTensorInv_apply (f : Additive (G →ₜ* Multiplicative A)) :
    continuousZModDualTensorInv (n := n) (G := G) (A := A) f =
      ∑ i, continuousZModHomCoord (Module.Free.chooseBasis (ZMod n) A) f i ⊗ₜ
        Module.Free.chooseBasis (ZMod n) A i :=
  rfl

private theorem continuousZModDualTensorMap_inv (f : Additive (G →ₜ* Multiplicative A)) :
    continuousZModDualTensorMap
      (continuousZModDualTensorInv (n := n) (G := G) (A := A) f) = f := by
  apply Additive.toMul.injective
  ext g
  apply Multiplicative.toAdd.injective
  -- Evaluation at `g` is linear, so it commutes with the sum defining the inverse.
  rw [← continuousZModHom.evalₗ_apply (n := n), ← continuousZModHom.evalₗ_apply (n := n),
    continuousZModDualTensorInv_apply, map_sum, map_sum]
  simp_rw [continuousZModHom.evalₗ_apply, continuousZModDualTensorMap_tmul_apply,
    toAdd_ofAdd, continuousZModHomCoord_apply, toAdd_ofAdd]
  exact (Module.Free.chooseBasis (ZMod n) A).sum_repr _

private theorem continuousZModDualTensorInv_map (x : continuousZModDual n G ⊗[ZMod n] A) :
    continuousZModDualTensorInv (n := n) (G := G) (A := A)
      (continuousZModDualTensorMap x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul x a =>
      simp_rw [continuousZModDualTensorInv_apply, continuousZModHomCoord_tensorMap_tmul,
        TensorProduct.smul_tmul, ← TensorProduct.tmul_sum,
        (Module.Free.chooseBasis (ZMod n) A).sum_repr]

/-- For finite free `A` with the discrete topology, the canonical evaluation map from the tensor
product to the space of continuous `A`-valued homomorphisms is bijective. -/
theorem continuousZModDualTensorMap_bijective :
    Function.Bijective (continuousZModDualTensorMap (n := n) (G := G) (A := A)) :=
  Function.bijective_iff_has_inverse.2 ⟨continuousZModDualTensorInv,
    continuousZModDualTensorInv_map, continuousZModDualTensorMap_inv⟩

/-- **Tensoring the continuous `ZMod n`-dual with a finite free module.** For a finite free
`ZMod n`-module `A` with the discrete topology (for prime `n = p`: any finite-dimensional
`𝔽_p`-vector space), evaluation is the canonical equivalence
`Hom_cont(G, ZMod n) ⊗ A ≃ Hom_cont(G, A)`. The inverse uses a basis only to prove
bijectivity; the exported forward map is basis-independent. -/
noncomputable def continuousZModDualTensorEquiv :
    continuousZModDual n G ⊗[ZMod n] A ≃ₗ[ZMod n]
      Additive (G →ₜ* Multiplicative A) :=
  LinearEquiv.ofBijective continuousZModDualTensorMap
    continuousZModDualTensorMap_bijective

/-- The forward map of `continuousZModDualTensorEquiv` is canonical evaluation. -/
@[simp]
theorem continuousZModDualTensorEquiv_apply (x : continuousZModDual n G ⊗[ZMod n] A) :
    continuousZModDualTensorEquiv x = continuousZModDualTensorMap x :=
  LinearEquiv.ofBijective_apply _ x

end Tensor

section ToDual

variable {p : ℕ} {W : Type u} [CommGroup W] [TopologicalSpace W]
  [Module (ZMod p) (Additive W)]

/-- A continuous `ZMod p`-valued character of a commutative group `W` whose additive copy is a
`ZMod p`-module, read as a linear functional on that module; for a prime `p` and an elementary
abelian `W` this is a functional on the `𝔽_p`-vector space `Additive W`. It is injective
(`TauCeti.continuousZModDualToDual_injective`), so the continuous dual is a subspace of the
algebraic dual. -/
def continuousZModDualToDual :
    continuousZModDual p W →ₗ[ZMod p] Module.Dual (ZMod p) (Additive W) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x ↦ AddMonoidHom.toZModLinearMap p
        { toFun := fun w ↦ Multiplicative.toAdd (Additive.toMul x (Additive.toMul w))
          map_zero' := by simp
          map_add' := fun a b ↦ by simp [toMul_add] }
      map_zero' := by ext _; simp
      map_add' := fun x y ↦ by ext w; simp }

@[simp]
theorem continuousZModDualToDual_apply (x : continuousZModDual p W) (w : Additive W) :
    continuousZModDualToDual x w = Multiplicative.toAdd (Additive.toMul x (Additive.toMul w)) := by
  rfl

theorem continuousZModDualToDual_injective :
    Function.Injective (continuousZModDualToDual (p := p) (W := W)) := fun _ _ h ↦
  Additive.toMul.injective <| ContinuousMonoidHom.ext fun w ↦ by
    simpa using LinearMap.congr_fun h (Additive.ofMul w)

theorem continuousZModDualToDual_eq_zero_iff {x : continuousZModDual p W} {w : Additive W} :
    continuousZModDualToDual x w = 0 ↔ Additive.toMul w ∈ (Additive.toMul x).ker := by
  simp [MonoidHom.mem_ker]

end ToDual

end TauCeti
