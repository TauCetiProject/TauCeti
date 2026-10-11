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
* `TauCeti.continuousZModDualTensorEquiv`: for prime `p` and finite-dimensional discrete `A`,
  evaluation identifies `continuousZModDual p G ⊗ A` with the continuous homomorphisms `G → A`.
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

/-- The continuous `ZMod n`-valued characters form a `ZMod n`-module: the target has exponent
dividing `n`, hence so does the character group. -/
instance instModuleContinuousZModDual : Module (ZMod n) (continuousZModDual n G) :=
  AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    ext g
    simp [ContinuousMonoidHom.pow_apply, toAdd_pow, nsmul_eq_mul]

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
    continuousZModDual.evalₗ g χ = Multiplicative.toAdd (Additive.toMul χ g) :=
  (rfl)

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
    (χ : continuousZModDual n H) : (f.continuousZModDualMap χ).toMul = χ.toMul.comp f :=
  (rfl)

/-- The transpose of `f` evaluates a character of `H` along `f`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.toMul_continuousZModDualMap_apply (f : G →ₜ* H)
    (χ : continuousZModDual n H) (g : G) : (f.continuousZModDualMap χ).toMul g = χ.toMul (f g) :=
  (rfl)

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
    Function.Bijective ((e : G →ₜ* H).continuousZModDualMap (n := n)) := by
  refine ⟨fun χ ψ hχψ ↦ Additive.toMul.injective (ContinuousMonoidHom.ext fun h ↦ ?_),
    fun χ ↦ ⟨(e.symm : H →ₜ* G).continuousZModDualMap χ,
      Additive.toMul.injective (ContinuousMonoidHom.ext fun g ↦ ?_)⟩⟩
  · have := congrArg (fun x : continuousZModDual n G ↦ Additive.toMul x (e.symm h)) hχψ
    have he : (e : G →ₜ* H) (e.symm h) = h := e.apply_symm_apply h
    simpa only [ContinuousMonoidHom.toMul_continuousZModDualMap_apply, he] using this
  · have he : (e.symm : H →ₜ* G) ((e : G →ₜ* H) g) = g := e.symm_apply_apply g
    simp only [ContinuousMonoidHom.toMul_continuousZModDualMap_apply, he]

end ZModDual

section Tensor

open scoped TensorProduct

universe v

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type v} [AddCommGroup A] [Module (ZMod n) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A]

/-- Continuous homomorphisms into a `ZMod n`-module form a `ZMod n`-module pointwise. -/
noncomputable instance instModuleContinuousZModHom :
    Module (ZMod n) (Additive (G →ₜ* Multiplicative A)) :=
  AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply ContinuousMonoidHom.ext
    intro g
    apply Multiplicative.toAdd.injective
    simpa using ZModModule.char_nsmul_eq_zero n
      (Multiplicative.toAdd (Additive.toMul x g))

/-- **Evaluation of a continuous homomorphism at a point**, as a `ZMod n`-linear map. -/
noncomputable def continuousZModHom.evalₗ (g : G) :
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

omit [IsTopologicalAddGroup A] in
@[simp]
private theorem continuousZModDualTensorPure_apply
    (x : continuousZModDual n G) (a : A) (g : G) :
    Additive.toMul (continuousZModDualTensorPure x a) g =
      Multiplicative.ofAdd (Multiplicative.toAdd (Additive.toMul x g) • a) :=
  rfl

omit [IsTopologicalAddGroup A] in
@[simp]
private theorem continuousZModDualTensorPure_zero (x : continuousZModDual n G) :
    continuousZModDualTensorPure (A := A) x 0 = 0 := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModDualTensorPure_apply]
  simp

@[simp]
private theorem continuousZModDualTensorPure_add (x : continuousZModDual n G) (a b : A) :
    continuousZModDualTensorPure x (a + b) =
      continuousZModDualTensorPure x a + continuousZModDualTensorPure x b := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModDualTensorPure_apply]
  simp only [toMul_add, ContinuousMonoidHom.mul_apply,
    continuousZModDualTensorPure_apply]
  exact congrArg Multiplicative.ofAdd (smul_add _ _ _)

omit [IsTopologicalAddGroup A] in
@[simp]
private theorem continuousZModDualTensorPure_zero_left (a : A) :
    continuousZModDualTensorPure (G := G) (0 : continuousZModDual n G) a = 0 := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModDualTensorPure_apply]
  simp

@[simp]
private theorem continuousZModDualTensorPure_add_left
    (x y : continuousZModDual n G) (a : A) :
    continuousZModDualTensorPure (x + y) a =
      continuousZModDualTensorPure x a + continuousZModDualTensorPure y a := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModDualTensorPure_apply]
  simp only [toMul_add, ContinuousMonoidHom.mul_apply,
    continuousZModDualTensorPure_apply, toAdd_mul]
  exact congrArg Multiplicative.ofAdd (add_smul _ _ _)

private noncomputable def continuousZModDualTensorBilinear :
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
noncomputable def continuousZModDualTensorMap :
    continuousZModDual n G ⊗[ZMod n] A →ₗ[ZMod n] Additive (G →ₜ* Multiplicative A) :=
  TensorProduct.lift continuousZModDualTensorBilinear

/-- The evaluation map sends `x ⊗ a` to `g ↦ x(g) • a`. -/
@[simp]
theorem continuousZModDualTensorMap_tmul_apply
    (x : continuousZModDual n G) (a : A) (g : G) :
    Additive.toMul (continuousZModDualTensorMap (x ⊗ₜ a)) g =
      Multiplicative.ofAdd (Multiplicative.toAdd (Additive.toMul x g) • a) :=
  by
    rw [continuousZModDualTensorMap, TensorProduct.lift.tmul]
    rfl

private noncomputable def continuousZModHomCoord [DiscreteTopology A]
    (b : Module.Basis (Fin (Module.finrank (ZMod n) A)) (ZMod n) A)
    (f : Additive (G →ₜ* Multiplicative A)) (i : Fin (Module.finrank (ZMod n) A)) :
    continuousZModDual n G :=
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
private theorem continuousZModHomCoord_apply [DiscreteTopology A]
    (b : Module.Basis (Fin (Module.finrank (ZMod n) A)) (ZMod n) A)
    (f : Additive (G →ₜ* Multiplicative A)) (i : Fin (Module.finrank (ZMod n) A)) (g : G) :
    Additive.toMul (continuousZModHomCoord b f i) g =
      Multiplicative.ofAdd (b.repr (continuousZModHom.evalₗ (n := n) (A := A) g f) i) :=
  rfl

@[simp]
private theorem continuousZModHomCoord_zero [DiscreteTopology A]
    (b : Module.Basis (Fin (Module.finrank (ZMod n) A)) (ZMod n) A)
    (i : Fin (Module.finrank (ZMod n) A)) :
    continuousZModHomCoord (G := G) b 0 i = 0 := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModHomCoord_apply]
  simp

@[simp]
private theorem continuousZModHomCoord_add [DiscreteTopology A]
    (b : Module.Basis (Fin (Module.finrank (ZMod n) A)) (ZMod n) A)
    (f h : Additive (G →ₜ* Multiplicative A)) (i : Fin (Module.finrank (ZMod n) A)) :
    continuousZModHomCoord b (f + h) i =
      continuousZModHomCoord b f i + continuousZModHomCoord b h i := by
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModHomCoord_apply]
  simp only [toMul_add, ContinuousMonoidHom.mul_apply, continuousZModHomCoord_apply,
    continuousZModHom.evalₗ_apply, map_add]
  simp

private noncomputable def continuousZModDualTensorInv [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] :
    Additive (G →ₜ* Multiplicative A) →ₗ[ZMod n]
      continuousZModDual n G ⊗[ZMod n] A :=
  letI : Module.Free (ZMod n) A :=
    @Module.Free.of_divisionRing (ZMod n) A inferInstance inferInstance inferInstance
  let b := Module.finBasis (ZMod n) A
  AddMonoidHom.toZModLinearMap n
    { toFun := fun f ↦ ∑ i, continuousZModHomCoord b f i ⊗ₜ[ZMod n] b i
      map_zero' := by
        apply Finset.sum_eq_zero
        intro i _
        simp
      map_add' := fun f h ↦ by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [continuousZModHomCoord_add]
        simp [TensorProduct.add_tmul] }

/-- The basis-dependent inverse is the sum of its coordinate characters tensored with the
corresponding basis vectors. -/
private theorem continuousZModDualTensorInv_apply [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] (f : Additive (G →ₜ* Multiplicative A)) :
    continuousZModDualTensorInv (n := n) (G := G) (A := A) f =
      ∑ i, continuousZModHomCoord (Module.finBasis (ZMod n) A) f i ⊗ₜ[ZMod n]
        (Module.finBasis (ZMod n) A) i := by
  -- Unfold the private basis choice once; consumers use this computation theorem instead.
  change (∑ i, continuousZModHomCoord (Module.finBasis (ZMod n) A) f i ⊗ₜ[ZMod n]
    (Module.finBasis (ZMod n) A) i) = _
  rfl

/-- Taking a coordinate after evaluating a pure tensor scales the original character by that
coordinate of the tensor's second factor. -/
private theorem continuousZModHomCoord_tensorMap_tmul [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] (x : continuousZModDual n G) (a : A)
    (i : Fin (Module.finrank (ZMod n) A)) :
    continuousZModHomCoord (Module.finBasis (ZMod n) A)
        (continuousZModDualTensorMap (x ⊗ₜ a)) i =
      ((Module.finBasis (ZMod n) A).repr a i) • x := by
  let _ : Module.Free (ZMod n) A :=
    @Module.Free.of_divisionRing (ZMod n) A inferInstance inferInstance inferInstance
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  rw [continuousZModHomCoord_apply, continuousZModHom.evalₗ_apply,
    continuousZModDualTensorMap_tmul_apply]
  simp only [toAdd_ofAdd, map_smul]
  apply Multiplicative.toAdd.injective
  -- The scalar action on the additive character is observed through its linear evaluation map.
  change continuousZModDual.evalₗ g x *
      ((Module.finBasis (ZMod n) A).repr a i) =
    continuousZModDual.evalₗ g ((Module.finBasis (ZMod n) A).repr a i • x)
  rw [map_smul, mul_comm]
  exact (smul_eq_mul _ _).symm

private theorem continuousZModDualTensorMap_inv [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] (f : Additive (G →ₜ* Multiplicative A)) :
    continuousZModDualTensorMap
      (continuousZModDualTensorInv (n := n) (G := G) (A := A) f) = f := by
  let _ : Module.Free (ZMod n) A :=
    @Module.Free.of_divisionRing (ZMod n) A inferInstance inferInstance inferInstance
  rw [continuousZModDualTensorInv_apply]
  rw [map_sum]
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  apply Multiplicative.toAdd.injective
  -- Evaluation is on the additive presentation of continuous homomorphisms, whereas extensionality
  -- leaves the same underlying equality in the multiplicative presentation.
  change continuousZModHom.evalₗ (n := n) (A := A) g
      (∑ i, continuousZModDualTensorMap
        (continuousZModHomCoord (Module.finBasis (ZMod n) A) f i ⊗ₜ
          (Module.finBasis (ZMod n) A) i)) =
    continuousZModHom.evalₗ (n := n) (A := A) g f
  rw [map_sum]
  -- Unwrap the additive presentation to apply the pure-tensor evaluation theorem.
  change (∑ i, Multiplicative.toAdd (Additive.toMul
      (continuousZModDualTensorMap
        (continuousZModHomCoord (Module.finBasis (ZMod n) A) f i ⊗ₜ
          (Module.finBasis (ZMod n) A) i)) g)) =
    Multiplicative.toAdd (Additive.toMul f g)
  simp_rw [continuousZModDualTensorMap_tmul_apply]
  -- The remaining equality is precisely reconstruction from coordinates in `Module.finBasis`.
  change (∑ i, (Module.finBasis (ZMod n) A).repr
      (Multiplicative.toAdd (Additive.toMul f g)) i • (Module.finBasis (ZMod n) A) i) =
    Multiplicative.toAdd (Additive.toMul f g)
  exact (Module.finBasis (ZMod n) A).sum_repr _

private theorem continuousZModDualTensorInv_map [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] (x : continuousZModDual n G ⊗[ZMod n] A) :
    continuousZModDualTensorInv (n := n) (G := G) (A := A)
      (continuousZModDualTensorMap x) = x := by
  let _ : Module.Free (ZMod n) A :=
    @Module.Free.of_divisionRing (ZMod n) A inferInstance inferInstance inferInstance
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul x a =>
      rw [continuousZModDualTensorInv_apply]
      calc
        _ = ∑ i, ((Module.finBasis (ZMod n) A).repr a i • x) ⊗ₜ[ZMod n]
              (Module.finBasis (ZMod n) A) i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [continuousZModHomCoord_tensorMap_tmul]
        _ = ∑ i, x ⊗ₜ[ZMod n] ((Module.finBasis (ZMod n) A).repr a i •
              (Module.finBasis (ZMod n) A) i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [TensorProduct.smul_tmul]
        _ = x ⊗ₜ (∑ i, (Module.finBasis (ZMod n) A).repr a i •
              (Module.finBasis (ZMod n) A) i) := by
            rw [TensorProduct.tmul_sum]
        _ = x ⊗ₜ a := by rw [(Module.finBasis (ZMod n) A).sum_repr]

/-- For prime `p` and finite-dimensional `A` with the discrete topology, the canonical evaluation
map from the tensor product to the space of continuous `A`-valued homomorphisms is bijective. -/
theorem continuousZModDualTensorMap_bijective [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] : Function.Bijective
      (continuousZModDualTensorMap (n := n) (G := G) (A := A)) :=
    ⟨fun x y h ↦ by
        simpa only [continuousZModDualTensorInv_map] using
          congrArg (continuousZModDualTensorInv (n := n) (G := G) (A := A)) h,
      fun f ↦ ⟨continuousZModDualTensorInv (n := n) (G := G) (A := A) f,
        continuousZModDualTensorMap_inv (n := n) (G := G) (A := A) f⟩⟩

/-- **Tensoring the continuous `ZMod p`-dual with a finite vector space.** For prime `p` and a
finite-dimensional `A` with the discrete topology, evaluation is the canonical equivalence
`Hom_cont(G, ZMod p) ⊗ A ≃ Hom_cont(G, A)`. The inverse uses a basis only to prove
bijectivity; the exported forward map is basis-independent. -/
noncomputable def continuousZModDualTensorEquiv [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] :
    continuousZModDual n G ⊗[ZMod n] A ≃ₗ[ZMod n]
      Additive (G →ₜ* Multiplicative A) :=
  LinearEquiv.ofBijective continuousZModDualTensorMap
    continuousZModDualTensorMap_bijective

/-- The forward map of `continuousZModDualTensorEquiv` is canonical evaluation. -/
@[simp]
theorem continuousZModDualTensorEquiv_apply [Fact n.Prime] [DiscreteTopology A]
    [Module.Finite (ZMod n) A] (x : continuousZModDual n G ⊗[ZMod n] A) :
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
    continuousZModDualToDual x w = Multiplicative.toAdd (Additive.toMul x (Additive.toMul w)) :=
  (rfl)

theorem continuousZModDualToDual_injective :
    Function.Injective (continuousZModDualToDual (p := p) (W := W)) := fun x y h ↦ by
  apply Additive.toMul.injective
  ext w
  have hw := congrArg (fun f ↦ f (Additive.ofMul w)) h
  simp only [continuousZModDualToDual_apply, toMul_ofMul] at hw
  exact Multiplicative.toAdd.injective hw

theorem continuousZModDualToDual_eq_zero_iff {x : continuousZModDual p W} {w : Additive W} :
    continuousZModDualToDual x w = 0 ↔ Additive.toMul w ∈ (Additive.toMul x).ker := by
  simp [MonoidHom.mem_ker]

end ToDual

end TauCeti
