/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Crossed products with noncommutative coefficients

A normalized crossed system consists of algebra automorphisms `σ_g` and units `a(g,h)`
with `σ_g σ_h = Ad(a(g,h)) σ_(gh)` and the noncommutative cocycle law. The automorphisms
need not form an action. Its crossed product is the finite-support algebra with multiplication
`(d[g])(e[h]) = d σ_g(e) a(g,h)[gh]`.

We construct its left coefficient-module basis, scalar inclusion, and universal property.
The coefficient algebra need not be commutative, and its inclusion need not be central.
Only the base semiring acts centrally. This is the algebraic setting for Clifford theory over
nonsplitting fields, where equivariant endomorphisms form a nonscalar division algebra.

The coordinate construction follows the existing `TauCeti.CrossedProduct` construction for
Galois cocycles, retaining the order of all noncommuting factors.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti

universe u v w

variable (k : Type u) (D : Type v) (G : Type w)
  [CommSemiring k] [Monoid G]

section Semiring

variable [Semiring D] [_root_.Algebra k D]

/-- Normalized algebra automorphisms and unit factors satisfying the crossed-system laws.
The automorphisms compose only up to inner conjugation by the factors. -/
@[ext]
structure CrossedSystem where
  /-- The coefficient automorphism attached to each monoid element. -/
  action : G → D ≃ₐ[k] D
  /-- The twisting units in the coefficient algebra. -/
  factor : G → G → Dˣ
  /-- The identity element acts trivially. -/
  action_one : action 1 = 1
  /-- Left normalization of the factor. -/
  factor_one_left (g : G) : factor 1 g = 1
  /-- Right normalization of the factor. -/
  factor_one_right (g : G) : factor g 1 = 1
  /-- The automorphisms compose up to the specified inner conjugation. -/
  action_mul (g h : G) (d : D) :
    action g (action h d) * factor g h = factor g h * action (g * h) d
  /-- The noncommutative cocycle law. -/
  factor_assoc (g h j : G) :
    (factor g h : D) * factor (g * h) j = action g (factor h j) * factor g (h * j)

variable {k D G}

namespace CrossedSystem

attribute [simp] action_one factor_one_left factor_one_right

/-- The crossed-product algebra of a normalized crossed system, with finite-support
coordinates indexed by the acting monoid. -/
@[ext]
structure Algebra (c : CrossedSystem k D G) where
  /-- Construct an element from its coefficient coordinates. -/
  ofFinsupp ::
  /-- The finitely supported coefficients. -/
  toFinsupp : G →₀ D

namespace Algebra

variable (c : CrossedSystem k D G)

noncomputable instance : AddCommMonoid (Algebra c) :=
  Equiv.addCommMonoid ⟨toFinsupp, ofFinsupp, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Forget multiplication and retain the finite-support coordinates. -/
def equivFinsupp : Algebra c ≃+ (G →₀ D) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The coefficient algebra acts by left multiplication on coordinates. -/
noncomputable instance : Module D (Algebra c) := (equivFinsupp c).module D

noncomputable instance : Module k (Algebra c) := (equivFinsupp c).module k

instance : IsScalarTower k D (Algebra c) where
  smul_assoc r d a := (equivFinsupp c).injective (smul_assoc r d a.toFinsupp)

/-- The coefficient-module basis, with `basis c g` denoting `[g]`. -/
noncomputable def basis : Module.Basis G D (Algebra c) :=
  .ofRepr ((equivFinsupp c).linearEquiv D)

noncomputable instance : Mul (Algebra c) where
  mul a b := ((basis c).repr a).sum fun g d => ((basis c).repr b).sum fun h e =>
    (d * c.action g e * c.factor g h) • basis c (g * h)

noncomputable instance : One (Algebra c) := ⟨basis c 1⟩

variable {c}

/-- Multiplication in coefficient coordinates. -/
theorem mul_def (a b : Algebra c) :
    a * b = ((basis c).repr a).sum fun g d => ((basis c).repr b).sum fun h e =>
      (d * c.action g e * c.factor g h) • basis c (g * h) := (rfl)

/-- The identity is the basis element at the identity of the monoid. -/
theorem one_def : (1 : Algebra c) = basis c 1 := (rfl)

/-- The multiplication table, with the order of the coefficient factors fixed. -/
@[simp]
theorem smul_basis_mul_smul_basis (g h : G) (d e : D) :
    (d • basis c g) * (e • basis c h) =
      (d * c.action g e * c.factor g h) • basis c (g * h) := by
  simp [mul_def, Finsupp.smul_single]

/-- Additive induction on coefficient multiples of basis elements. -/
@[elab_as_elim]
theorem induction_on {motive : Algebra c → Prop} (a : Algebra c) (zero : motive 0)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (smul_basis : ∀ (g : G) (d : D), motive (d • basis c g)) : motive a := by
  rw [← (basis c).repr.symm_apply_apply a]
  induction (basis c).repr a using Finsupp.induction_linear with
  | zero => simpa using zero
  | add f g hf hg => simpa using add _ _ hf hg
  | single g d => simpa using smul_basis g d

noncomputable instance : NonUnitalNonAssocSemiring (Algebra c) where
  zero_mul a := by simp [mul_def]
  mul_zero a := by simp [mul_def]
  left_distrib a b d := by
    simp only [mul_def, map_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => Finsupp.sum_add_index' (fun _ => by simp) fun h x y => ?_
    simp only [map_add, mul_add, add_mul, add_smul]
  right_distrib a b d := by
    simp only [mul_def, map_add]
    refine Finsupp.sum_add_index' (fun _ => by simp) fun g x y => ?_
    simp only [add_mul, add_smul, Finsupp.sum_add]

noncomputable instance : NonUnitalSemiring (Algebra c) where
  mul_assoc a b d := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a a' ha ha' => simp only [add_mul, ha, ha']
    | smul_basis g x =>
    induction b using induction_on with
    | zero => simp only [zero_mul, mul_zero]
    | add b b' hb hb' => simp only [add_mul, mul_add, hb, hb']
    | smul_basis h y =>
    induction d using induction_on with
    | zero => simp only [mul_zero]
    | add d d' hd hd' => simp only [mul_add, hd, hd']
    | smul_basis j z =>
      -- The cocycle law brings the factors together; the twisted action law then moves `z`.
      simp only [smul_basis_mul_smul_basis, map_mul, mul_assoc]
      congr 1
      rw [← c.factor_assoc, ← mul_assoc (c.action g (c.action h z)),
        c.action_mul, mul_assoc]

noncomputable instance : NonAssocSemiring (Algebra c) where
  one_mul a := by
    induction a using induction_on with
    | zero => simp only [mul_zero]
    | add a b ha hb => simp only [mul_add, ha, hb]
    | smul_basis g d =>
      rw [one_def, ← one_smul D (basis c 1), smul_basis_mul_smul_basis]
      simp
  mul_one a := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a b ha hb => simp only [add_mul, ha, hb]
    | smul_basis g d =>
      rw [one_def, ← one_smul D (basis c 1), smul_basis_mul_smul_basis]
      simp

noncomputable instance : Semiring (Algebra c) where
  __ := (inferInstance : NonUnitalSemiring (Algebra c))
  __ := (inferInstance : NonAssocSemiring (Algebra c))

/-- The left coefficient action associates with multiplication. -/
instance : IsScalarTower D (Algebra c) (Algebra c) where
  smul_assoc d a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [smul_add, add_mul, ha, ha']
    | smul_basis g x =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis h y => simp only [smul_smul, smul_basis_mul_smul_basis, mul_assoc]

/-- Base-semiring scalars commute with multiplication, since the coefficient automorphisms
are algebra automorphisms. -/
instance : SMulCommClass k (Algebra c) (Algebra c) where
  smul_comm r a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, smul_add, ha, ha']
    | smul_basis g x =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis h y =>
      simp only [← algebraMap_smul (A := D) r, smul_smul, smul_basis_mul_smul_basis,
        map_mul, AlgEquiv.commutes, mul_assoc]
      congr 1
      rw [← mul_assoc, _root_.Algebra.commutes, mul_assoc]

/-- The crossed product is an algebra over the central base semiring. -/
noncomputable instance : _root_.Algebra k (Algebra c) :=
  _root_.Algebra.ofModule
    (fun r a b => by rw [← algebraMap_smul D r a, smul_mul_assoc, algebraMap_smul])
    fun r a b => mul_smul_comm r a b

variable (c) in
/-- The coefficient inclusion `d ↦ d[1]`, which is generally noncentral. -/
noncomputable def inc : D →ₐ[k] Algebra c where
  toFun d := d • basis c 1
  map_one' := by simp [one_def]
  map_mul' d e := by simp
  map_zero' := by simp
  map_add' d e := by simp [add_smul]
  commutes' r := by
    simp only [_root_.Algebra.algebraMap_eq_smul_one, one_def]
    rw [smul_assoc, one_smul]

theorem inc_apply (d : D) : inc c d = d • basis c 1 := (rfl)

/-- The coefficient inclusion is injective. -/
theorem inc_injective : Function.Injective (inc c) := by
  intro d e h
  have := congrArg (fun a => (basis c).repr a 1) h
  simpa [inc_apply] using this

/-- Left multiplication by the coefficient inclusion is the coefficient-module action. -/
theorem smul_def (d : D) (a : Algebra c) : d • a = inc c d * a := by
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, mul_add, ha, hb]
  | smul_basis g e => simp [inc_apply, smul_smul]

/-- The identity basis element is the algebra identity. -/
@[simp]
theorem basis_one : basis c 1 = 1 := one_def.symm

/-- Multiplying by a coefficient on the right applies the corresponding automorphism. -/
@[simp]
theorem basis_mul_inc (g : G) (d : D) :
    basis c g * inc c d = inc c (c.action g d) * basis c g := by
  rw [← smul_def, inc_apply, ← one_smul D (basis c g), smul_basis_mul_smul_basis]
  simp

/-- Basis elements multiply with the specified unit factor. -/
@[simp]
theorem basis_mul_basis (g h : G) :
    basis c g * basis c h = inc c (c.factor g h) * basis c (g * h) := by
  rw [← smul_def, ← one_smul D (basis c g), ← one_smul D (basis c h),
    smul_basis_mul_smul_basis]
  simp

section Lift

variable {R : Type*} [Semiring R] [_root_.Algebra k R]

/-- A coefficient algebra map and images of the basis elements extend to an algebra map
exactly when they respect the twisting, multiplication, and identity relations. -/
noncomputable def lift (f : D →ₐ[k] R) (u : G → R)
    (hf : ∀ g d, u g * f d = f (c.action g d) * u g)
    (hu : ∀ g h, u g * u h = f (c.factor g h) * u (g * h)) (hu₁ : u 1 = 1) :
    Algebra c →ₐ[k] R :=
  have hsb (g : G) (d : D) : (Finsupp.lsum k fun g ↦
      LinearMap.mulRight k (u g) ∘ₗ f.toLinearMap) ((basis c).repr (d • basis c g)) =
      f d * u g := by simp
  AlgHom.ofLinearMap ((Finsupp.lsum k fun g ↦ LinearMap.mulRight k (u g) ∘ₗ f.toLinearMap) ∘ₗ
      (basis c).repr.toLinearMap.restrictScalars k)
    (by
      rw [LinearMap.comp_apply, one_def, ← one_smul D (basis c 1),
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, hsb, map_one, hu₁, mul_one])
    fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
      induction a using induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
      | smul_basis g d =>
        induction b using induction_on with
        | zero => simp
        | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
        | smul_basis h e =>
          simp only [smul_basis_mul_smul_basis, hsb, map_mul, mul_assoc]
          rw [← hu, ← mul_assoc (f (c.action g e)), ← hf]
          simp only [mul_assoc]

variable (f : D →ₐ[k] R) (u : G → R)
  (hf : ∀ g d, u g * f d = f (c.action g d) * u g)
  (hu : ∀ g h, u g * u h = f (c.factor g h) * u (g * h)) (hu₁ : u 1 = 1)

/-- The universal map sends a coefficient multiple of `[g]` to `f(d) u(g)`. -/
@[simp]
theorem lift_smul_basis (g : G) (d : D) :
    lift f u hf hu hu₁ (d • basis c g) = f d * u g := by simp [lift]

/-- The universal map has the specified values on basis elements. -/
@[simp]
theorem lift_basis (g : G) : lift f u hf hu hu₁ (basis c g) = u g := by
  rw [← one_smul D (basis c g), lift_smul_basis, map_one, one_mul]

/-- The universal map restricts to the given coefficient map. -/
@[simp]
theorem lift_inc (d : D) : lift f u hf hu hu₁ (inc c d) = f d := by
  rw [inc_apply, lift_smul_basis, hu₁, mul_one]

/-- An algebra map is determined by the coefficient inclusion and the basis elements. -/
@[ext]
theorem algHom_ext {F H : Algebra c →ₐ[k] R}
    (hinc : ∀ d, F (inc c d) = H (inc c d))
    (hbasis : ∀ g, F (basis c g) = H (basis c g)) : F = H :=
  AlgHom.ext fun a ↦ by
    induction a using induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul_basis g d => rw [smul_def, map_mul, map_mul, hinc, hbasis]

/-- The universal map is the unique map with the prescribed coefficient and basis values. -/
theorem lift_unique (F : Algebra c →ₐ[k] R) (hinc : ∀ d, F (inc c d) = f d)
    (hbasis : ∀ g, F (basis c g) = u g) : F = lift f u hf hu hu₁ :=
  algHom_ext (fun d ↦ by rw [hinc, lift_inc]) fun g ↦ by rw [hbasis, lift_basis]

end Lift

instance [Nontrivial D] : Nontrivial (Algebra c) :=
  Function.Injective.nontrivial (f := inc c) inc_injective

end Algebra
end CrossedSystem

end Semiring

namespace CrossedSystem.Algebra

variable {k D G} [Ring D] [_root_.Algebra k D] (c : CrossedSystem k D G)

noncomputable instance : AddCommGroup (Algebra c) :=
  Equiv.addCommGroup ⟨toFinsupp, ofFinsupp, fun _ ↦ rfl, fun _ ↦ rfl⟩

noncomputable instance : Ring (Algebra c) where
  __ := (inferInstance : Semiring (Algebra c))
  __ := (inferInstance : AddCommGroup (Algebra c))

end CrossedSystem.Algebra
end TauCeti
