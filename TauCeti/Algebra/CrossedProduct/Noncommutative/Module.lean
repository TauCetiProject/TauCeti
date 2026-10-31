/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Opposite
public import Mathlib.Algebra.Algebra.Tower

/-!
# Semilinear modules over noncommutative crossed products

For a crossed system `(σ, a)` on `D`, an action on a coefficient module `M` consists of
operators `U_g` satisfying `U_g(d m) = σ_g(d) U_g(m)` and
`U_g U_h(m) = a(g,h) U_(gh)(m)`. These data are equivalent to algebra maps from the
crossed product to `End_k(M)` extending the given coefficient action. They therefore give
ordinary modules over the crossed product, with no extra global module instance.

A map between these modules is linear over the crossed product exactly when it is
coefficient-linear and intertwines the operators. For a right `D`-module the corresponding
construction uses `c.opInv`: the multiplication law is then
`U_g U_h(m) = U_(gh)(m) a(g,h)⁻¹`. This keeps the opposite and inverse conventions explicit
for multiplicity spaces over noncommutative endomorphism algebras.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).

The construction uses `CrossedSystem.Algebra.lift` and Mathlib's `Module.compHom`.
-/

public section

namespace TauCeti.CrossedSystem

universe u v w z z'

variable {k : Type u} {D : Type v} {G : Type w}
  [CommSemiring k] [Semiring D] [_root_.Algebra k D] [Monoid G]
  (c : CrossedSystem k D G)
  (M : Type z) [AddCommMonoid M] [Module k M]

section Coefficients

variable [Module D M]

/-- Semilinear operators on a fixed coefficient module, with multiplication twisted by
exactly the factors of the crossed system. -/
@[ext]
structure SemilinearAction where
  /-- The ground-linear operator associated to an index. -/
  operator : G → Module.End k M
  /-- The identity index acts identically. -/
  operator_one : operator 1 = 1
  /-- Semilinearity for the coefficient automorphism. -/
  operator_smul (g : G) (d : D) (m : M) :
    operator g (d • m) = c.action g d • operator g m
  /-- Composition of operators uses the specified factor. -/
  operator_mul (g h : G) (m : M) :
    operator g (operator h m) = (c.factor g h : D) • operator (g * h) m

namespace SemilinearAction

variable {c M} [IsScalarTower k D M]

/-- Extend semilinear operators to an algebra action by the crossed-product universal property. -/
noncomputable def toAlgHom (s : SemilinearAction c M) :
    Algebra c →ₐ[k] Module.End k M :=
  Algebra.lift (_root_.Algebra.lsmul k k M) s.operator
    (fun g d ↦ LinearMap.ext (s.operator_smul g d))
    (fun g h ↦ LinearMap.ext (s.operator_mul g h)) s.operator_one

/-- A coefficient multiple of a basis element acts by the corresponding operator followed by
coefficient multiplication. -/
@[simp]
theorem toAlgHom_smul_basis (s : SemilinearAction c M) (g : G) (d : D) (m : M) :
    s.toAlgHom (d • Algebra.basis c g) m = d • s.operator g m := by
  simp [toAlgHom, _root_.Algebra.lsmul_apply]

/-- A basis element acts by its given semilinear operator. -/
@[simp]
theorem toAlgHom_basis (s : SemilinearAction c M) (g : G) :
    s.toAlgHom (Algebra.basis c g) = s.operator g := by
  simp [toAlgHom]

/-- The algebra action extends the original coefficient action. -/
@[simp]
theorem toAlgHom_inc (s : SemilinearAction c M) (d : D) :
    s.toAlgHom (Algebra.inc c d) = _root_.Algebra.lsmul k k M d := by
  simp [toAlgHom]

/-- Recover the semilinear operators of an algebra action extending the coefficient action. -/
noncomputable def ofAlgHom (F : Algebra c →ₐ[k] Module.End k M)
    (hF : ∀ d, F (Algebra.inc c d) = _root_.Algebra.lsmul k k M d) :
    SemilinearAction c M where
  operator g := F (Algebra.basis c g)
  operator_one := by simp
  operator_smul g d m := by
    have h := congrArg (fun f : Module.End k M ↦ f m)
      (congrArg F (Algebra.basis_mul_inc (c := c) g d))
    simpa only [map_mul, Module.End.mul_apply, hF, _root_.Algebra.lsmul_apply] using h
  operator_mul g h m := by
    have he := congrArg (fun f : Module.End k M ↦ f m)
      (congrArg F (Algebra.basis_mul_basis (c := c) g h))
    simpa only [map_mul, Module.End.mul_apply, hF, _root_.Algebra.lsmul_apply] using he

/-- The recovered operator is the action of the basis element. -/
@[simp]
theorem ofAlgHom_operator (F : Algebra c →ₐ[k] Module.End k M) (hF) (g : G) :
    (ofAlgHom F hF).operator g = F (Algebra.basis c g) := (rfl)

/-- Semilinear actions are exactly crossed-product algebra actions extending the coefficients. -/
noncomputable def algHomEquiv :
    SemilinearAction c M ≃
      {F : Algebra c →ₐ[k] Module.End k M //
        ∀ d, F (Algebra.inc c d) = _root_.Algebra.lsmul k k M d} where
  toFun s := ⟨s.toAlgHom, s.toAlgHom_inc⟩
  invFun F := ofAlgHom F.val F.property
  left_inv s := by ext g; simp
  right_inv F := by
    apply Subtype.ext
    exact Algebra.algHom_ext (fun d ↦ by simp [F.property]) (fun g ↦ by simp)

/-- The correspondence sends a semilinear action to its extension on the algebra. -/
@[simp]
theorem algHomEquiv_apply (s : SemilinearAction c M) :
    (algHomEquiv s).val = s.toAlgHom := (rfl)

/-- The inverse correspondence reads the operators from the basis elements. -/
@[simp]
theorem algHomEquiv_symm_operator
    (F : {F : Algebra c →ₐ[k] Module.End k M //
      ∀ d, F (Algebra.inc c d) = _root_.Algebra.lsmul k k M d}) (g : G) :
    (algHomEquiv.symm F).operator g = F.val (Algebra.basis c g) := (rfl)

/-- The ordinary crossed-product module associated to semilinear operators. Use this
explicitly with `letI`; a coefficient module may carry several different actions. -/
noncomputable abbrev module (s : SemilinearAction c M) : Module (Algebra c) M :=
  Module.compHom M s.toAlgHom.toRingHom

/-- The module's scalar multiplication is evaluation of the algebra action. -/
theorem module_smul (s : SemilinearAction c M) (a : Algebra c) (m : M) :
    letI := s.module
    a • m = s.toAlgHom a m := (rfl)

/-- The constructed module agrees with the original ground-semiring action. -/
theorem isScalarTower (s : SemilinearAction c M) :
    letI := s.module
    IsScalarTower k (Algebra c) M := by
  let := s.module
  exact IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rw [module_smul, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The coefficient action is the restriction of the constructed algebra action. -/
@[simp]
theorem module_inc_smul (s : SemilinearAction c M) (d : D) (m : M) :
    letI := s.module
    Algebra.inc c d • m = d • m := by
  rw [module_smul, toAlgHom_inc, _root_.Algebra.lsmul_apply]

/-- A basis element acts by its specified operator in the constructed module. -/
@[simp]
theorem module_basis_smul (s : SemilinearAction c M) (g : G) (m : M) :
    letI := s.module
    Algebra.basis c g • m = s.operator g m := by
  rw [module_smul, toAlgHom_basis]

/-- The original coefficient-module structure associates with the algebra action. -/
theorem coefficientIsScalarTower (s : SemilinearAction c M) :
    letI := s.module
    IsScalarTower D (Algebra c) M := by
  let := s.module
  exact ⟨fun d a m ↦ by
    rw [Algebra.smul_def, mul_smul, module_inc_smul]⟩

section Maps

variable {N : Type z'} [AddCommMonoid N] [Module k N] [Module D N] [IsScalarTower k D N]
  (s : SemilinearAction c M) (t : SemilinearAction c N)

/-- A ground-linear map intertwines the full algebra actions exactly when it respects the
coefficient action and the semilinear operators. -/
theorem map_toAlgHom_iff (f : M →ₗ[k] N) :
    (∀ (a : Algebra c) m, f (s.toAlgHom a m) = t.toAlgHom a (f m)) ↔
      (∀ (d : D) m, f (d • m) = d • f m) ∧
        ∀ (g : G) m, f (s.operator g m) = t.operator g (f m) := by
  constructor
  · intro hf
    exact ⟨fun d m ↦ by simpa using hf (Algebra.inc c d) m,
      fun g m ↦ by simpa using hf (Algebra.basis c g) m⟩
  · rintro ⟨hd, hg⟩ a m
    induction a using Algebra.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | smul_basis g d => simp [hd, hg]

/-- A coefficient-linear intertwiner becomes a linear map of ordinary crossed-product modules. -/
def linearMap (f : M →ₗ[k] N) (hd : ∀ (d : D) m, f (d • m) = d • f m)
    (hg : ∀ (g : G) m, f (s.operator g m) = t.operator g (f m)) :
    letI := s.module
    letI := t.module
    M →ₗ[Algebra c] N :=
  letI := s.module
  letI := t.module
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun a m ↦ (map_toAlgHom_iff s t f).2 ⟨hd, hg⟩ a m }

/-- Extending linearity leaves the underlying map unchanged. -/
@[simp]
theorem linearMap_apply (f : M →ₗ[k] N) (hd hg) (m : M) :
    linearMap s t f hd hg m = f m := (rfl)

end Maps
end SemilinearAction

end Coefficients

/-- Right-coefficient semilinear operators act through the opposite-coefficient,
inverse-factor crossed system. Here `op d • m` denotes the right action `m d`. -/
def opInvSemilinearAction [Module Dᵐᵒᵖ M]
    (U : G → Module.End k M) (hU : U 1 = 1)
    (hsmul : ∀ g d m, U g (MulOpposite.op d • m) = MulOpposite.op (c.action g d) • U g m)
    (hmul : ∀ g h m, U g (U h m) =
      MulOpposite.op (↑(c.factor g h)⁻¹ : D) • U (g * h) m) :
    SemilinearAction c.opInv M where
  operator := U
  operator_one := hU
  operator_smul g d m := by simpa only [opInv_action, MulOpposite.op_unop] using hsmul g d.unop m
  operator_mul g h m := by simpa only [opInv_factor] using hmul g h m

/-- The right-module constructor retains exactly the supplied operators. -/
@[simp]
theorem opInvSemilinearAction_operator [Module Dᵐᵒᵖ M]
    (U : G → Module.End k M) (hU hsmul hmul) (g : G) :
    (opInvSemilinearAction c M U hU hsmul hmul).operator g = U g := (rfl)

end TauCeti.CrossedSystem
