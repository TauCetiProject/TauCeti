/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Crossed-product algebras of Galois `2`-cocycles

Let `L` be a commutative `K`-algebra. A **`2`-cocycle** `c` of `Aut_K(L)` with values in `Lˣ` is a
function `c : Aut_K(L) × Aut_K(L) → Lˣ` satisfying Mathlib's multiplicative cocycle identity
`groupCohomology.IsMulCocycle₂`, which reads
`c(στ, ρ) · c(σ, τ) = σ(c(τ, ρ)) · c(σ, τρ)`
for the Galois action of `Aut_K(L)` on `Lˣ`. This is the inhomogeneous normalization of
Gille–Szamuely §4.4 and Serre, *Local Fields*, Chapter X.

The **crossed product** `(L, Aut_K(L), c)` is the free `L`-module on symbols `u_σ`, one for each
`σ : L ≃ₐ[K] L`, with the multiplication determined by `L`-linearity on the left and the two rules
`u_σ · x = σ(x) · u_σ` and `u_σ · u_τ = c(σ, τ) · u_{στ}`. On basis multiples this is
`(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`, and associativity of this product is
exactly the cocycle identity. The cocycle is not assumed normalized: the identity element is
`c(1, 1)⁻¹ · u_1`, and `L` embeds by `x ↦ (x · c(1, 1)⁻¹) · u_1`.

An element is a wrapper around a finitely supported function `Aut_K(L) →₀ L`, its coordinates
`(CrossedProduct.basis c).repr` in the `L`-basis `u_σ`, and the
crossed product is a `K`-algebra of `K`-dimension `[L : K] · #Aut_K(L)`, that is `[L : K]²` when
`L/K` is finite Galois. It is **not** an `L`-algebra: `L` acts on the left by multiplication, but
is not central unless the automorphism group is trivial.

Central simplicity of the crossed product of a finite Galois extension of fields is proved in
`TauCeti.Algebra.CrossedProduct.CentralSimple`.

## Main definitions

* `TauCeti.TwoCocycle K L`: the `2`-cocycles of `L ≃ₐ[K] L` with values in `Lˣ`.
* `TauCeti.CrossedProduct c`: the crossed-product ring of a cocycle `c`, with its `K`-algebra and
  left `L`-module structures.
* `TauCeti.CrossedProduct.basis c`: the `L`-basis `u_σ` of the crossed product.
* `TauCeti.CrossedProduct.inc c`: the embedding of `L` as a `K`-subalgebra.

## Main results

* `TauCeti.CrossedProduct.smul_basis_mul_smul_basis`: the multiplication table
  `(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`.
* `TauCeti.CrossedProduct.basis_mul_inc`: `u_σ · x = σ(x) · u_σ`.
* `TauCeti.CrossedProduct.basis_mul_basis`: `u_σ · u_τ = c(σ, τ) · u_{στ}`.
* `TauCeti.CrossedProduct.finrank_eq_finrank_mul_card`: over fields the crossed product has
  dimension `[L : K] · #Aut_K(L)` over `K`, and `TauCeti.CrossedProduct.finrank_eq_finrank_sq`: for
  a finite Galois extension this is `[L : K]²`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open groupCohomology

universe u v

namespace TauCeti

variable (K : Type u) [CommRing K] (L : Type v) [CommRing L] [Algebra K L]

/-- A **`2`-cocycle** of the automorphism group `Aut_K(L)` with values in the units of `L`: a
function `c : Aut_K(L) × Aut_K(L) → Lˣ` satisfying the multiplicative cocycle identity
`c(στ, ρ) · c(σ, τ) = σ(c(τ, ρ)) · c(σ, τρ)` of `groupCohomology.IsMulCocycle₂`, for the Galois
action of `L ≃ₐ[K] L` on `Lˣ`. -/
@[ext]
structure TwoCocycle where
  /-- The underlying function. -/
  toFun : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ
  /-- The cocycle identity. -/
  isMulCocycle₂ : IsMulCocycle₂ toFun

variable {K L}

namespace TwoCocycle

variable (c : TwoCocycle K L)

/-- The cocycle identity `σ(c(τ, ρ)) · c(σ, τρ) = c(σ, τ) · c(στ, ρ)`, read in `L`. -/
theorem map_toFun_mul_toFun (σ τ ρ : L ≃ₐ[K] L) :
    σ (c.toFun (τ, ρ) : L) * c.toFun (σ, τ * ρ) = c.toFun (σ, τ) * c.toFun (σ * τ, ρ) := by
  have h := congrArg ((↑) : Lˣ → L) (c.isMulCocycle₂ σ τ ρ)
  simp only [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass] at h
  rw [← h, mul_comm]

/-- `c(σ, 1) = σ(c(1, 1))`, Mathlib's `groupCohomology.map_one_snd_of_isMulCocycle₂` read in `L`
through the Galois action. -/
theorem toFun_one_right (σ : L ≃ₐ[K] L) : (c.toFun (σ, 1) : L) = σ (c.toFun (1, 1) : L) := by
  simp [map_one_snd_of_isMulCocycle₂ c.isMulCocycle₂ σ]

end TwoCocycle

/-- The **crossed-product algebra** `(L, Aut_K(L), c)` of a `2`-cocycle `c`: the free `L`-module on
symbols `u_σ`, one for each `σ : L ≃ₐ[K] L`, with the multiplication
`(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`. An element is a wrapper around its
coordinates `Aut_K(L) →₀ L` in the basis `CrossedProduct.basis c`; the cocycle is a parameter of
the type so that the multiplication can be an instance. -/
structure CrossedProduct (c : TwoCocycle K L) : Type v where
  /-- The element of the crossed product with the given coordinates in the basis `u_σ`. -/
  ofFinsupp ::
  /-- The coordinates `σ ↦ a_σ` of an element in the basis `u_σ`. -/
  toFinsupp : (L ≃ₐ[K] L) →₀ L

namespace CrossedProduct

variable (c : TwoCocycle K L)

noncomputable instance : AddCommGroup (CrossedProduct c) :=
  Equiv.addCommGroup ⟨toFinsupp, ofFinsupp, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The identification of the crossed product with its coordinates `Aut_K(L) →₀ L` as an additive
group, forgetting the multiplication. -/
def equivFinsupp : CrossedProduct c ≃+ ((L ≃ₐ[K] L) →₀ L) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `L` acts on the crossed product by left multiplication; see `CrossedProduct.smul_def`. -/
noncomputable instance : Module L (CrossedProduct c) :=
  (equivFinsupp c).module L

noncomputable instance : Module K (CrossedProduct c) :=
  (equivFinsupp c).module K

instance : IsScalarTower K L (CrossedProduct c) where
  smul_assoc r x a := (equivFinsupp c).injective (smul_assoc r x a.toFinsupp)

/-- The `L`-basis `u_σ` of the crossed product, indexed by `L ≃ₐ[K] L`. -/
noncomputable def basis : Module.Basis (L ≃ₐ[K] L) L (CrossedProduct c) :=
  .ofRepr ((equivFinsupp c).linearEquiv L)

/-- The multiplication of the crossed product,
`(∑ x_σ · u_σ) · (∑ y_τ · u_τ) = ∑ (x_σ · σ(y_τ) · c(σ, τ)) · u_{στ}`. -/
noncomputable instance : Mul (CrossedProduct c) where
  mul a b := ((basis c).repr a).sum fun σ x => ((basis c).repr b).sum fun τ y =>
    (x * σ y * c.toFun (σ, τ)) • basis c (σ * τ)

/-- The identity of the crossed product, `c(1, 1)⁻¹ · u_1`. -/
noncomputable instance : One (CrossedProduct c) where
  one := ((c.toFun (1, 1))⁻¹ : Lˣ) • basis c 1

variable {c}

/-- The multiplication of the crossed product in coordinates. -/
theorem mul_def (a b : CrossedProduct c) :
    a * b = ((basis c).repr a).sum fun σ x => ((basis c).repr b).sum fun τ y =>
      (x * σ y * c.toFun (σ, τ)) • basis c (σ * τ) :=
  (rfl)

variable (c) in
/-- The identity of the crossed product is `c(1, 1)⁻¹ · u_1`. -/
theorem one_def : (1 : CrossedProduct c) = (((c.toFun (1, 1))⁻¹ : Lˣ) : L) • basis c 1 :=
  (rfl)

/-- The multiplication table of the crossed product:
`(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`. -/
@[simp]
theorem smul_basis_mul_smul_basis (σ τ : L ≃ₐ[K] L) (x y : L) :
    (x • basis c σ) * (y • basis c τ) = (x * σ y * c.toFun (σ, τ)) • basis c (σ * τ) := by
  simp [mul_def, Finsupp.smul_single]

/-- Induction principle along the `L`-basis `u_σ`: a property of elements of the crossed product
that holds for `0` and for every `x · u_σ` and is closed under addition holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : CrossedProduct c → Prop} (a : CrossedProduct c) (zero : motive 0)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (smul_basis : ∀ (σ : L ≃ₐ[K] L) (x : L), motive (x • basis c σ)) : motive a := by
  rw [← (basis c).repr.symm_apply_apply a]
  induction (basis c).repr a using Finsupp.induction_linear with
  | zero => simpa using zero
  | add f g hf hg => simpa using add _ _ hf hg
  | single σ x => simpa using smul_basis σ x

noncomputable instance : NonUnitalNonAssocRing (CrossedProduct c) where
  zero_mul a := by simp [mul_def]
  mul_zero a := by simp [mul_def]
  left_distrib a b d := by
    simp only [mul_def, map_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun σ _ => Finsupp.sum_add_index' (fun _ => by simp) fun τ x y => ?_
    simp only [map_add, mul_add, add_mul, add_smul]
  right_distrib a b d := by
    simp only [mul_def, map_add]
    refine Finsupp.sum_add_index' (fun _ => by simp) fun σ x y => ?_
    simp only [add_mul, add_smul, Finsupp.sum_add]

noncomputable instance : NonUnitalRing (CrossedProduct c) where
  mul_assoc a b d := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a a' ha ha' => simp only [add_mul, ha, ha']
    | smul_basis σ x =>
    induction b using induction_on with
    | zero => simp only [zero_mul, mul_zero]
    | add b b' hb hb' => simp only [add_mul, mul_add, hb, hb']
    | smul_basis τ y =>
    induction d using induction_on with
    | zero => simp only [mul_zero]
    | add d d' hd hd' => simp only [mul_add, hd, hd']
    | smul_basis ρ z =>
    -- both sides are multiples of `u_{στρ}`; their coefficients agree by the cocycle identity
    simp only [smul_basis_mul_smul_basis, map_mul, AlgEquiv.mul_apply, mul_assoc]
    congr 1
    linear_combination (-(x * σ y * σ (τ z))) * c.map_toFun_mul_toFun σ τ ρ

noncomputable instance : NonAssocRing (CrossedProduct c) where
  one_mul a := by
    induction a using induction_on with
    | zero => simp only [mul_zero]
    | add a b ha hb => simp only [mul_add, ha, hb]
    | smul_basis σ x =>
      rw [one_def, smul_basis_mul_smul_basis, map_one_fst_of_isMulCocycle₂ c.isMulCocycle₂ σ,
        AlgEquiv.one_apply, one_mul, mul_right_comm, Units.inv_mul, one_mul]
  mul_one a := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a b ha hb => simp only [add_mul, ha, hb]
    | smul_basis σ x =>
      rw [one_def, smul_basis_mul_smul_basis, c.toFun_one_right, mul_assoc, ← map_mul,
        Units.inv_mul, map_one, mul_one, mul_one]

noncomputable instance : Ring (CrossedProduct c) where
  __ := (inferInstance : NonUnitalRing (CrossedProduct c))
  __ := (inferInstance : NonAssocRing (CrossedProduct c))

/-- `L` acts on the crossed product by left multiplication: `(x • a) * b = x • (a * b)`. -/
instance : IsScalarTower L (CrossedProduct c) (CrossedProduct c) where
  smul_assoc x a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [smul_add, add_mul, ha, ha']
    | smul_basis σ y =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis τ z => simp only [smul_smul, smul_basis_mul_smul_basis, mul_assoc]

/-- Scalars from `K` commute with the multiplication of the crossed product, because the
automorphisms `σ` are `K`-linear. -/
instance : SMulCommClass K (CrossedProduct c) (CrossedProduct c) where
  smul_comm r a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, smul_add, ha, ha']
    | smul_basis σ y =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis τ z =>
      simp only [← algebraMap_smul (A := L) r, smul_smul, smul_basis_mul_smul_basis, map_mul,
        AlgEquiv.commutes]
      ring_nf

/-- The crossed product is a `K`-algebra. -/
noncomputable instance : Algebra K (CrossedProduct c) :=
  Algebra.ofModule
    (fun r a b => by rw [← algebraMap_smul L r a, smul_mul_assoc, algebraMap_smul])
    fun r a b => mul_smul_comm r a b

variable (c) in
/-- The embedding `x ↦ (x · c(1, 1)⁻¹) · u_1` of `L` into the crossed product, a homomorphism of
`K`-algebras. -/
noncomputable def inc : L →ₐ[K] CrossedProduct c where
  toFun x := (x * (((c.toFun (1, 1))⁻¹ : Lˣ) : L)) • basis c 1
  map_one' := by rw [one_mul, one_def]
  map_mul' x y := by
    rw [smul_basis_mul_smul_basis, AlgEquiv.one_apply, mul_one]
    congr 1
    linear_combination (-(x * y * (((c.toFun (1, 1))⁻¹ : Lˣ) : L))) * Units.inv_mul (c.toFun (1, 1))
  map_zero' := by simp
  map_add' x y := by simp [add_mul, add_smul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one (A := CrossedProduct c), one_def, ← smul_assoc,
      Algebra.smul_def]

theorem inc_apply (x : L) : inc c x = (x * (((c.toFun (1, 1))⁻¹ : Lˣ) : L)) • basis c 1 :=
  (rfl)

/-- Left multiplication by `inc c x` is the `L`-module structure. -/
theorem smul_def (x : L) (a : CrossedProduct c) : x • a = inc c x * a := by
  rw [inc_apply, smul_mul_assoc]
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [mul_add, smul_add, ha, hb]
  | smul_basis σ y =>
    rw [← one_smul L (basis c 1), smul_basis_mul_smul_basis,
      map_one_fst_of_isMulCocycle₂ c.isMulCocycle₂ σ, AlgEquiv.one_apply, one_mul, one_mul,
      smul_smul, smul_smul]
    congr 1
    linear_combination (-(x * y)) * Units.inv_mul (c.toFun (1, 1))

/-- `u_1 = c(1, 1) · 1`. -/
theorem basis_one : basis c 1 = inc c (c.toFun (1, 1)) := by
  rw [inc_apply, Units.mul_inv, one_smul]

/-- **The semilinearity rule** `u_σ · x = σ(x) · u_σ`. -/
theorem basis_mul_inc (σ : L ≃ₐ[K] L) (x : L) :
    basis c σ * inc c x = inc c (σ x) * basis c σ := by
  rw [← smul_def, inc_apply, ← one_smul L (basis c σ), smul_basis_mul_smul_basis, one_smul,
    c.toFun_one_right, one_mul, map_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one,
    mul_one]

/-- **The cocycle rule** `u_σ · u_τ = c(σ, τ) · u_{στ}`. -/
theorem basis_mul_basis (σ τ : L ≃ₐ[K] L) :
    basis c σ * basis c τ = inc c (c.toFun (σ, τ)) * basis c (σ * τ) := by
  rw [← smul_def, ← one_smul L (basis c σ), ← one_smul L (basis c τ), smul_basis_mul_smul_basis,
    map_one, one_mul, one_mul]

/-- Right multiplication by `inc c x` twists the `σ`-th coordinate by `σ`:
`(∑ a_σ · u_σ) · x = ∑ (a_σ · σ(x)) · u_σ`. -/
@[simp]
theorem repr_mul_inc (a : CrossedProduct c) (x : L) (σ : L ≃ₐ[K] L) :
    (basis c).repr (a * inc c x) σ = (basis c).repr a σ * σ x := by
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, Finsupp.add_apply, ha, hb]
  | smul_basis τ y =>
    rw [smul_mul_assoc, basis_mul_inc, ← smul_def, smul_smul]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
    by_cases h : τ = σ
    · subst h
      ring
    · simp [h]

/-- A crossed product over a nontrivial ring `L` is nontrivial. -/
instance [Nontrivial L] : Nontrivial (CrossedProduct c) :=
  nontrivial_of_ne _ _ ((basis c).ne_zero 1)

section Field

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (c : TwoCocycle K L)

/-- The crossed product has `K`-dimension `[L : K] · #Aut_K(L)`. -/
theorem finrank_eq_finrank_mul_card :
    Module.finrank K (CrossedProduct c) = Module.finrank K L * Nat.card (L ≃ₐ[K] L) := by
  rw [← Module.finrank_mul_finrank K L, Module.finrank_eq_nat_card_basis (basis c)]

/-- **The crossed product of a finite Galois extension has dimension `[L : K]²`**, so it has degree
`[L : K]` as a central simple algebra. -/
theorem finrank_eq_finrank_sq [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct c) = Module.finrank K L ^ 2 := by
  rw [finrank_eq_finrank_mul_card, IsGalois.card_aut_eq_finrank, sq]

instance [FiniteDimensional K L] : FiniteDimensional K (CrossedProduct c) :=
  have : Module.Finite L (CrossedProduct c) := .of_basis (basis c)
  Module.Finite.trans L (CrossedProduct c)

end Field

end CrossedProduct

end TauCeti
