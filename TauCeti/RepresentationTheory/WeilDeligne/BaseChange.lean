/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.WeilDeligne.Operations
public import TauCeti.RepresentationTheory.WeilDeligne.Special
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Scalar extension of raw Weil–Deligne parameters

For a field extension `E'` of `E`, a raw Weil–Deligne parameter `(V, r, N)` over `E`
(`TauCeti.WeilDeligneParameter`) gives the parameter `(E' ⊗[E] V, E' ⊗ r, E' ⊗ N)` over `E'`
(`TauCeti.WeilDeligneParameter.baseChange`). Over a field the kernel does not change, so it stays
open, the monodromy stays nilpotent, and the conjugation relation is the base change of the
original one, the scalar `q ^ deg w` of `E` becoming the same scalar of `E'`.

Scalar extension is functorial on morphisms and isomorphisms of parameters, and it commutes with
transport along a linear equivalence (base-changed), with direct sums (through
`TensorProduct.prodRight`), with tensor products (through
`TensorProduct.AlgebraTensorModule.distribBaseChange`), with duals of finite-dimensional
parameters (through `IsBaseChange.toDualBaseChange`), with twists by a character (the character
read in `E'ˣ`), and with the special parameters `Sp(n)` (through `TensorProduct.piScalarRight`).

## Main definitions

* `TauCeti.WeilDeligneParameter.baseChange E' D`: the scalar extension of `D` to `E'`.
* `TauCeti.WeilDeligneParameter.Hom.baseChange`, `TauCeti.WeilDeligneParameter.Iso.baseChange`:
  scalar extension of morphisms and isomorphisms.
* `TauCeti.WeilDeligneParameter.baseChangeProdIso`: `E' ⊗ (D ⊕ D') ≅ E' ⊗ D ⊕ E' ⊗ D'`.
* `TauCeti.WeilDeligneParameter.baseChangeTensorIso`:
  `E' ⊗ (D ⊗ D') ≅ (E' ⊗ D) ⊗_{E'} (E' ⊗ D')`.
* `TauCeti.WeilDeligneParameter.baseChangeDualIso`: `E' ⊗ D^∨ ≅ (E' ⊗ D)^∨` for
  finite-dimensional `V`.
* `TauCeti.WeilDeligneParameter.baseChangeSpecialIso`: `E' ⊗ Sp(n) ≅ Sp(n)` over `E'`.

## Main results

* `TauCeti.WeilDeligneParameter.Hom.baseChange_id`,
  `TauCeti.WeilDeligneParameter.Hom.baseChange_comp`, and their counterparts for isomorphisms:
  scalar extension is functorial.
* `TauCeti.WeilDeligneParameter.baseChange_transport`: scalar extension commutes with transport.
* `TauCeti.WeilDeligneParameter.baseChange_twist`: scalar extension commutes with twists.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

namespace WeilDeligneParameter

variable {E W V V' V₁ V₂ V₃ : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V₁] [Module E V₁] [AddCommGroup V₂] [Module E V₂]
  [AddCommGroup V₃] [Module E V₃]
  {deg : W →* Multiplicative ℤ} {q : ℕ}
  (E' : Type*) [Field E'] [Algebra E E']

/-- The **scalar extension** `(E' ⊗[E] V, E' ⊗ r, E' ⊗ N)` of a raw Weil–Deligne parameter along
a field extension `E → E'`. -/
def baseChange (D : WeilDeligneParameter E W V deg q) :
    WeilDeligneParameter E' W (E' ⊗[E] V) deg q where
  r := Representation.baseChange E' D.r
  isOpen_ker := by
    rw [Representation.ker_baseChange]
    exact D.isOpen_ker
  N := D.N.baseChange E'
  isNilpotent_N := D.isNilpotent_N.map (Module.End.baseChangeHom E E' V)
  conj_N w := by
    simp only [Representation.baseChange_apply, ← LinearMap.baseChange_mul, D.conj_N,
      LinearMap.baseChange_smul, ← algebraMap_smul E', map_zpow₀, map_natCast]

variable (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)

@[simp]
theorem baseChange_r : (D.baseChange E').r = Representation.baseChange E' D.r :=
  (rfl)

@[simp]
theorem baseChange_N : (D.baseChange E').N = D.N.baseChange E' :=
  (rfl)

theorem baseChange_r_tmul (w : W) (a : E') (v : V) :
    (D.baseChange E').r w (a ⊗ₜ v) = a ⊗ₜ D.r w v := by
  simp

theorem baseChange_N_tmul (a : E') (v : V) : (D.baseChange E').N (a ⊗ₜ v) = a ⊗ₜ D.N v :=
  (rfl)

variable {D₁ : WeilDeligneParameter E W V₁ deg q} {D₂ : WeilDeligneParameter E W V₂ deg q}
  {D₃ : WeilDeligneParameter E W V₃ deg q}

/-- The scalar extension of a morphism of parameters. -/
def Hom.baseChange (f : Hom D₁ D₂) : Hom (D₁.baseChange E') (D₂.baseChange E') where
  toIntertwiningMap := f.toIntertwiningMap.baseChange E'
  comp_N := by
    ext v
    simp [f.map_N_apply]

@[simp]
theorem Hom.baseChange_tmul (f : Hom D₁ D₂) (a : E') (v : V₁) :
    f.baseChange E' (a ⊗ₜ v) = a ⊗ₜ f v :=
  Representation.IntertwiningMap.baseChange_tmul ..

@[simp]
theorem Hom.baseChange_id : (Hom.id D₁).baseChange E' = Hom.id (D₁.baseChange E') := by
  ext1
  ext v
  simp [Hom.coe_toIntertwiningMap]

@[simp]
theorem Hom.baseChange_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) :
    (f.comp g).baseChange E' = (f.baseChange E').comp (g.baseChange E') := by
  ext1
  ext v
  simp [Hom.coe_toIntertwiningMap]

/-- The scalar extension of an isomorphism of parameters. -/
def Iso.baseChange (f : Iso D₁ D₂) : Iso (D₁.baseChange E') (D₂.baseChange E') where
  toRepresentationEquiv := f.toRepresentationEquiv.baseChange E'
  comp_N := by
    ext v
    -- `simp` does not see through `(D₁.baseChange E').r = Representation.baseChange E' D₁.r` in the
    -- coercion of the equivalence, so restate the goal (definitionally) through the latter for
    -- `Representation.Equiv.baseChange_tmul` to apply.
    change (f.toRepresentationEquiv.baseChange E') (1 ⊗ₜ D₁.N v) =
      (D₂.N.baseChange E') ((f.toRepresentationEquiv.baseChange E') (1 ⊗ₜ v))
    simp [f.map_N_apply]

@[simp]
theorem Iso.baseChange_tmul (f : Iso D₁ D₂) (a : E') (v : V₁) :
    f.baseChange E' (a ⊗ₜ v) = a ⊗ₜ f v :=
  Representation.Equiv.baseChange_tmul ..

@[simp]
theorem Iso.toHom_baseChange (f : Iso D₁ D₂) : (f.baseChange E').toHom = f.toHom.baseChange E' := by
  ext1
  ext v
  simp [Hom.coe_toIntertwiningMap]

@[simp]
theorem Iso.baseChange_refl : (Iso.refl D₁).baseChange E' = Iso.refl (D₁.baseChange E') := by
  ext1
  refine LinearEquiv.toLinearMap_injective ?_
  ext v
  simp

@[simp]
theorem Iso.baseChange_trans (f : Iso D₁ D₂) (g : Iso D₂ D₃) :
    (f.trans g).baseChange E' = (f.baseChange E').trans (g.baseChange E') := by
  ext1
  refine LinearEquiv.toLinearMap_injective ?_
  ext v
  simp

@[simp]
theorem Iso.baseChange_symm (f : Iso D₁ D₂) : (f.baseChange E').symm = f.symm.baseChange E' := by
  ext1
  refine LinearEquiv.toLinearMap_injective ?_
  ext v
  apply (f.baseChange E').injective
  simp

/-- **Scalar extension commutes with transport**: extending the scalars of the transport along `e`
gives the transport of the scalar extension along `E' ⊗ e`. -/
theorem baseChange_transport (e : V ≃ₗ[E] V') :
    (D.transport e).baseChange E' = (D.baseChange E').transport (e.baseChange E E' V V') := by
  refine WeilDeligneParameter.ext ?_ ?_
  · ext w v
    simp [transport_r_apply]
  · ext v
    simp [transport_N_apply]

/-- **Scalar extension commutes with direct sums**: `E' ⊗ (D ⊕ D') ≅ E' ⊗ D ⊕ E' ⊗ D'`, through
`TensorProduct.prodRight`. -/
def baseChangeProdIso :
    Iso ((D.prod D').baseChange E') ((D.baseChange E').prod (D'.baseChange E')) where
  toRepresentationEquiv := .mk (TensorProduct.prodRight E E' E' V V') fun w ↦ by
    ext x <;> simp
  comp_N := by
    ext x <;> simp

@[simp]
theorem baseChangeProdIso_tmul (a : E') (x : V × V') :
    D.baseChangeProdIso E' D' (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) :=
  TensorProduct.prodRight_tmul ..

/-- **Scalar extension commutes with twists**: extending the scalars of the twist by `χ` gives the
twist of the scalar extension by `χ` read in `E'ˣ`. -/
theorem baseChange_twist [SeparatelyContinuousMul W] (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) :
    (D.twist χ hχ).baseChange E' =
      (D.baseChange E').twist ((Units.map (algebraMap E E' : E →* E')).comp χ)
        (by
          convert hχ using 2
          ext w
          exact (Units.map_injective (algebraMap E E').injective).eq_iff' (map_one _)) := by
  refine WeilDeligneParameter.ext ?_ ?_
  · ext w v
    simp [TensorProduct.tmul_smul, Algebra.smul_def]
  · ext v
    simp

/-- **Scalar extension commutes with tensor products**:
`E' ⊗ (D ⊗ D') ≅ (E' ⊗ D) ⊗_{E'} (E' ⊗ D')`, through
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
def baseChangeTensorIso [SeparatelyContinuousMul W] :
    Iso ((D.tensor D').baseChange E') ((D.baseChange E').tensor (D'.baseChange E')) where
  toRepresentationEquiv :=
    .mk (AlgebraTensorModule.distribBaseChange E E' V V') fun w ↦ by
      ext v v'
      simp
  comp_N := by
    ext v v'
    simp

@[simp]
theorem baseChangeTensorIso_tmul [SeparatelyContinuousMul W] (a : E') (v : V) (v' : V') :
    D.baseChangeTensorIso E' D' (a ⊗ₜ (v ⊗ₜ v')) = (a ⊗ₜ v) ⊗ₜ (1 ⊗ₜ v') :=
  AlgebraTensorModule.distribBaseChange_tmul ..

/-- **Scalar extension commutes with `Sp(n)`**: `E' ⊗ Sp(n) ≅ Sp(n)` over `E'`, through
`TensorProduct.piScalarRight`. -/
def baseChangeSpecialIso (n : ℕ) (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    Iso ((special q n hdeg hq).baseChange E')
      (special q n hdeg (by rwa [← map_natCast (algebraMap E E'), map_ne_zero])) where
  toRepresentationEquiv := .mk (TensorProduct.piScalarRight E E' E' (Fin n)) fun w ↦ by
    ext v i
    simp [Algebra.smul_def, mul_comm]
  comp_N := by
    ext v i
    simp [finShift_apply]

@[simp]
theorem baseChangeSpecialIso_tmul (n : ℕ) (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (a : E')
    (v : Fin n → E) (i : Fin n) :
    baseChangeSpecialIso E' n hdeg hq (a ⊗ₜ v) i = a * algebraMap E E' (v i) := by
  simp [baseChangeSpecialIso, Algebra.smul_def, mul_comm]

/-- **Scalar extension commutes with duals** for finite-dimensional `V`:
`E' ⊗ D^∨ ≅ (E' ⊗ D)^∨`, through Mathlib's `IsBaseChange.toDualBaseChange`. -/
def baseChangeDualIso [FiniteDimensional E V] :
    Iso (D.dual.baseChange E') (D.baseChange E').dual where
  toRepresentationEquiv :=
    .mk (TensorProduct.isBaseChange E V E').toDualBaseChange fun w ↦ by
      ext f v
      simp [Representation.dual_apply, Module.Dual.transpose_apply]
  comp_N := by
    ext f v
    simp

@[simp]
theorem baseChangeDualIso_tmul_tmul [FiniteDimensional E V] (a : E') (f : Module.Dual E V)
    (b : E') (v : V) :
    D.baseChangeDualIso E' (a ⊗ₜ f) (b ⊗ₜ v) = a * b * algebraMap E E' (f v) :=
  IsBaseChange.toDualBaseChange_tmul_tmul ..

end WeilDeligneParameter

end TauCeti
