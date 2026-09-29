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

Let `K` be a commutative semiring and `L` a commutative ring over `K`. A **`2`-cocycle** `c` of
`Aut_K(L)` with values in `Lˣ` is a
function `c(σ, τ) ∈ Lˣ` of two automorphisms, stored curried as `c.toFun σ τ`, whose uncurried
form `Aut_K(L) × Aut_K(L) → Lˣ` satisfies Mathlib's multiplicative cocycle identity
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
crossed product is a `K`-algebra. Over fields its `Module.finrank` is
`Module.finrank K L * Nat.card (Aut_K(L))`; when `L/K` is finite Galois, this is the actual
dimension `[L : K]²`. It is **not** an `L`-algebra: `L` acts on the left by multiplication, but is
not central unless the automorphism group is trivial.

Central simplicity of the crossed product of a finite Galois extension of fields is proved in
`TauCeti.Algebra.CrossedProduct.CentralSimple`.

## Main definitions

* `TauCeti.TwoCocycle K L`: the `2`-cocycles of `L ≃ₐ[K] L` with values in `Lˣ`, a commutative
  group under pointwise multiplication (`TauCeti.TwoCocycle.instCommGroup`).
* `TauCeti.TwoCocycle.comap f ι hf c`: the inflation of `c` along a homomorphism
  `f : Aut_K(M) → Aut_K(L)` and an embedding `ι : L →ₐ[K] M` intertwining it.
* `TauCeti.CrossedProduct c`: the crossed-product ring of a cocycle `c`, with its `K`-algebra and
  left `L`-module structures.
* `TauCeti.CrossedProduct.basis c`: the `L`-basis `u_σ` of the crossed product.
* `TauCeti.CrossedProduct.inc c`: the embedding of `L` as a `K`-subalgebra.
* `TauCeti.CrossedProduct.lift`: the universal property, extending `f : L →ₐ[K] R` and elements
  `u σ ∈ R` satisfying the relations of the crossed product to a `K`-algebra homomorphism.

## Main results

* `TauCeti.CrossedProduct.smul_basis_mul_smul_basis`: the multiplication table
  `(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`.
* `TauCeti.CrossedProduct.basis_mul_inc`: `u_σ · x = σ(x) · u_σ`.
* `TauCeti.CrossedProduct.basis_mul_basis`: `u_σ · u_τ = c(σ, τ) · u_{στ}`.
* `TauCeti.CrossedProduct.algHom_ext`, `TauCeti.CrossedProduct.lift_unique`: a `K`-algebra
  homomorphism out of the crossed product is determined by its values on `L` and on the `u_σ`.
* `TauCeti.CrossedProduct.finrank_eq_finrank_mul_card`: over fields, the `Module.finrank` of the
  crossed product is `Module.finrank K L * Nat.card (Aut_K(L))`; and
  `TauCeti.CrossedProduct.finrank_eq_finrank_sq`: for a finite Galois extension its dimension is
  `[L : K]²`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open groupCohomology

universe u v w

namespace TauCeti

variable (K : Type u) [CommSemiring K] (L : Type v) [CommRing L] [Algebra K L]

/-- A **`2`-cocycle** of the automorphism group `Aut_K(L)` with values in the units of `L`: a
function `c(σ, τ) = c.toFun σ τ ∈ Lˣ` whose uncurried form satisfies the multiplicative
cocycle identity `c(στ, ρ) · c(σ, τ) = σ(c(τ, ρ)) · c(σ, τρ)` of
`groupCohomology.IsMulCocycle₂`, for the Galois action of `L ≃ₐ[K] L` on `Lˣ`. -/
@[ext]
structure TwoCocycle where
  /-- The underlying function `(σ, τ) ↦ c(σ, τ)`, in curried form. -/
  toFun : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ
  /-- The cocycle identity, for the uncurried function `(σ, τ) ↦ c(σ, τ)`. -/
  isMulCocycle₂ : IsMulCocycle₂ fun p ↦ toFun p.1 p.2

variable {K L}

namespace TwoCocycle

variable (c : TwoCocycle K L)

/-- The cocycle identity `σ(c(τ, ρ)) · c(σ, τρ) = c(σ, τ) · c(στ, ρ)`, read in `L`. -/
theorem map_toFun_mul_toFun (σ τ ρ : L ≃ₐ[K] L) :
    σ (c.toFun τ ρ : L) * c.toFun σ (τ * ρ) = c.toFun σ τ * c.toFun (σ * τ) ρ := by
  have h := congrArg ((↑) : Lˣ → L) (c.isMulCocycle₂ σ τ ρ)
  simp only [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass] at h
  rw [← h, mul_comm]

/-- `c(1, σ) = c(1, 1)`, Mathlib's `groupCohomology.map_one_fst_of_isMulCocycle₂` for a
`2`-cocycle. -/
@[simp]
theorem toFun_one_left (σ : L ≃ₐ[K] L) : c.toFun 1 σ = c.toFun 1 1 :=
  map_one_fst_of_isMulCocycle₂ c.isMulCocycle₂ σ

/-- `c(σ, 1) = σ(c(1, 1))`, Mathlib's `groupCohomology.map_one_snd_of_isMulCocycle₂` read in `L`
through the Galois action. Not a `simp` lemma: at `σ = 1` its left-hand side `c(1, 1)` reappears
inside its right-hand side, so `simp` would loop. -/
theorem toFun_one_right (σ : L ≃ₐ[K] L) : (c.toFun σ 1 : L) = σ (c.toFun 1 1 : L) := by
  simp [map_one_snd_of_isMulCocycle₂ c.isMulCocycle₂ σ]

/-! ### The pointwise group of `2`-cocycles -/

/-- The trivial `2`-cocycle, constantly `1`. -/
instance : One (TwoCocycle K L) where
  one := ⟨fun _ _ ↦ 1, fun σ _ _ ↦ by simp⟩

/-- The pointwise product `(c · d)(σ, τ) = c(σ, τ) · d(σ, τ)` of two `2`-cocycles. -/
instance : Mul (TwoCocycle K L) where
  mul c d := ⟨fun σ τ ↦ c.toFun σ τ * d.toFun σ τ, fun σ τ ρ ↦ by
    rw [mul_mul_mul_comm, c.isMulCocycle₂ σ τ ρ, d.isMulCocycle₂ σ τ ρ, smul_mul',
      mul_mul_mul_comm]⟩

/-- The pointwise inverse `c⁻¹(σ, τ) = c(σ, τ)⁻¹` of a `2`-cocycle. -/
instance : Inv (TwoCocycle K L) where
  inv c := ⟨fun σ τ ↦ (c.toFun σ τ)⁻¹, fun σ τ ρ ↦ by
    rw [← mul_inv, c.isMulCocycle₂ σ τ ρ, mul_inv, smul_inv']⟩

/-- The pointwise quotient `(c / d)(σ, τ) = c(σ, τ) / d(σ, τ)` of two `2`-cocycles. -/
instance : Div (TwoCocycle K L) where
  div c d := ⟨fun σ τ ↦ c.toFun σ τ / d.toFun σ τ, fun σ τ ρ ↦ by
    rw [div_mul_div_comm, c.isMulCocycle₂ σ τ ρ, d.isMulCocycle₂ σ τ ρ, smul_div',
      div_mul_div_comm]⟩

/-- The pointwise power `cⁿ(σ, τ) = c(σ, τ)ⁿ` of a `2`-cocycle. -/
instance : Pow (TwoCocycle K L) ℕ where
  pow c n := ⟨fun σ τ ↦ c.toFun σ τ ^ n, fun σ τ ρ ↦ by
    rw [← mul_pow, c.isMulCocycle₂ σ τ ρ, mul_pow, smul_pow']⟩

/-- The pointwise integer power `cⁿ(σ, τ) = c(σ, τ)ⁿ` of a `2`-cocycle. -/
instance : Pow (TwoCocycle K L) ℤ where
  pow c n := ⟨fun σ τ ↦ c.toFun σ τ ^ n, fun σ τ ρ ↦ by
    rw [← mul_zpow, c.isMulCocycle₂ σ τ ρ, mul_zpow, smul_zpow']⟩

/-- The trivial `2`-cocycle is constantly `1`. -/
@[simp]
theorem toFun_one (σ τ : L ≃ₐ[K] L) : (1 : TwoCocycle K L).toFun σ τ = 1 :=
  rfl

/-- Multiplication of `2`-cocycles is pointwise multiplication. -/
@[simp]
theorem toFun_mul (d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) :
    (c * d).toFun σ τ = c.toFun σ τ * d.toFun σ τ :=
  rfl

/-- Inversion of `2`-cocycles is pointwise inversion. -/
@[simp]
theorem toFun_inv (σ τ : L ≃ₐ[K] L) : c⁻¹.toFun σ τ = (c.toFun σ τ)⁻¹ :=
  rfl

/-- Division of `2`-cocycles is pointwise division. -/
@[simp]
theorem toFun_div (d : TwoCocycle K L) (σ τ : L ≃ₐ[K] L) :
    (c / d).toFun σ τ = c.toFun σ τ / d.toFun σ τ :=
  rfl

/-- Powers of `2`-cocycles are pointwise powers. -/
@[simp]
theorem toFun_pow (n : ℕ) (σ τ : L ≃ₐ[K] L) : (c ^ n).toFun σ τ = c.toFun σ τ ^ n :=
  rfl

/-- Integer powers of `2`-cocycles are pointwise integer powers. -/
@[simp]
theorem toFun_zpow (n : ℤ) (σ τ : L ≃ₐ[K] L) : (c ^ n).toFun σ τ = c.toFun σ τ ^ n :=
  rfl

/-- The `2`-cocycles form a commutative group under pointwise multiplication, the group of
`2`-cocycles whose quotient by coboundaries is `H²(Aut_K(L), Lˣ)`. -/
instance : CommGroup (TwoCocycle K L) :=
  Function.Injective.commGroup TwoCocycle.toFun (fun _ _ h ↦ TwoCocycle.ext h) rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

section Comap

variable {M : Type w} [CommRing M] [Algebra K M]

/-- The **inflation** of a `2`-cocycle `c` of `Aut_K(L)` along a compatible pair: a homomorphism
`f : Aut_K(M) → Aut_K(L)` and an embedding `ι : L → M` intertwining it, `ι (f g x) = g (ι x)`.
Its values are `(g, g') ↦ ι (c (f g, f g'))`; the intertwining hypothesis is what makes this a
cocycle. -/
def comap (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hf : ∀ g x, ι (f g x) = g (ι x))
    (c : TwoCocycle K L) : TwoCocycle K M where
  toFun g g' := Units.map (ι : L →* M) (c.toFun (f g) (f g'))
  isMulCocycle₂ g g' g'' := by
    have hsmul (x : Lˣ) : g • Units.map (ι : L →* M) x = Units.map (ι : L →* M) (f g • x) :=
      Units.ext (by simp [AlgEquiv.smul_units_def, hf])
    have h := c.isMulCocycle₂ (f g) (f g') (f g'')
    dsimp only at h ⊢
    rw [← map_mul f, ← map_mul f] at h
    rw [hsmul, ← map_mul, ← map_mul, h]

variable (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hf : ∀ g x, ι (f g x) = g (ι x))

/-- The defining equation of the inflated cocycle, `(c.comap f ι hf)(g, g') = ι (c (f g, f g'))`,
as units. -/
@[simp]
theorem comap_toFun (g g' : M ≃ₐ[K] M) :
    (c.comap f ι hf).toFun g g' = Units.map (ι : L →* M) (c.toFun (f g) (f g')) :=
  (rfl)

/-- The values of the inflated cocycle, `(c.comap f ι hf)(g, g') = ι (c (f g, f g'))`. Not a
`simp` lemma: `simp` reaches its right-hand side through `comap_toFun` and `Units.coe_map`. -/
theorem coe_comap_toFun (g g' : M ≃ₐ[K] M) :
    ((c.comap f ι hf).toFun g g' : M) = ι (c.toFun (f g) (f g')) :=
  (rfl)

/-- Inflation of the trivial `2`-cocycle is trivial. -/
@[simp]
theorem comap_one : (1 : TwoCocycle K L).comap f ι hf = 1 :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

/-- Inflation is multiplicative. -/
@[simp]
theorem comap_mul (d : TwoCocycle K L) : (c * d).comap f ι hf = c.comap f ι hf * d.comap f ι hf :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

/-- Inflation commutes with inversion. -/
@[simp]
theorem comap_inv : c⁻¹.comap f ι hf = (c.comap f ι hf)⁻¹ :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

/-- Inflation commutes with division. -/
@[simp]
theorem comap_div (d : TwoCocycle K L) : (c / d).comap f ι hf = c.comap f ι hf / d.comap f ι hf :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

/-- Inflation commutes with natural powers. -/
@[simp]
theorem comap_pow (n : ℕ) : (c ^ n).comap f ι hf = c.comap f ι hf ^ n :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

/-- Inflation commutes with integer powers. -/
@[simp]
theorem comap_zpow (n : ℤ) : (c ^ n).comap f ι hf = c.comap f ι hf ^ n :=
  TwoCocycle.ext (funext₂ fun _ _ ↦ by simp)

end Comap

end TwoCocycle

/-- The **crossed-product algebra** `(L, Aut_K(L), c)` of a `2`-cocycle `c`: the free `L`-module on
symbols `u_σ`, one for each `σ : L ≃ₐ[K] L`, with the multiplication
`(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`. An element is a wrapper around its
coordinates `Aut_K(L) →₀ L` in the basis `CrossedProduct.basis c`; the cocycle is a parameter of
the type so that the multiplication can be an instance. -/
@[ext]
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
    (x * σ y * c.toFun σ τ) • basis c (σ * τ)

/-- The identity of the crossed product, `c(1, 1)⁻¹ · u_1`. -/
noncomputable instance : One (CrossedProduct c) where
  one := ((c.toFun 1 1)⁻¹ : Lˣ) • basis c 1

variable {c}

/-- The multiplication of the crossed product in coordinates. -/
theorem mul_def (a b : CrossedProduct c) :
    a * b = ((basis c).repr a).sum fun σ x => ((basis c).repr b).sum fun τ y =>
      (x * σ y * c.toFun σ τ) • basis c (σ * τ) :=
  (rfl)

variable (c) in
/-- The identity of the crossed product is `c(1, 1)⁻¹ · u_1`. -/
theorem one_def : (1 : CrossedProduct c) = (((c.toFun 1 1)⁻¹ : Lˣ) : L) • basis c 1 :=
  (rfl)

/-- The multiplication table of the crossed product:
`(x · u_σ) · (y · u_τ) = (x · σ(y) · c(σ, τ)) · u_{στ}`. -/
@[simp]
theorem smul_basis_mul_smul_basis (σ τ : L ≃ₐ[K] L) (x y : L) :
    (x • basis c σ) * (y • basis c τ) = (x * σ y * c.toFun σ τ) • basis c (σ * τ) := by
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
      simp only [one_def, smul_basis_mul_smul_basis, c.toFun_one_left, AlgEquiv.one_apply,
        one_mul]
      congr 1
      calc
        (↑(c.toFun 1 1)⁻¹ : L) * x * c.toFun 1 1 =
            x * (↑(c.toFun 1 1)⁻¹ : L) * c.toFun 1 1 := by rw [mul_comm (↑_ : L) x]
        _ = x := by rw [mul_assoc, Units.inv_mul, mul_one]
  mul_one a := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a b ha hb => simp only [add_mul, ha, hb]
    | smul_basis σ x =>
      rw [one_def, smul_basis_mul_smul_basis, c.toFun_one_right]
      congr 1
      calc
        x * σ (↑(c.toFun 1 1)⁻¹ : L) * σ (c.toFun 1 1 : L) =
            x * σ ((↑(c.toFun 1 1)⁻¹ : L) * c.toFun 1 1) := by
              rw [mul_assoc, map_mul]
        _ = x := by rw [Units.inv_mul, map_one, mul_one]

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
  toFun x := (x * (((c.toFun 1 1)⁻¹ : Lˣ) : L)) • basis c 1
  map_one' := by rw [one_mul, one_def]
  map_mul' x y := by
    rw [smul_basis_mul_smul_basis, AlgEquiv.one_apply, mul_one]
    congr 1
    linear_combination (-(x * y * (((c.toFun 1 1)⁻¹ : Lˣ) : L))) * Units.inv_mul (c.toFun 1 1)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, add_smul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one (A := CrossedProduct c), one_def, ← smul_assoc,
      Algebra.smul_def]

theorem inc_apply (x : L) : inc c x = (x * (((c.toFun 1 1)⁻¹ : Lˣ) : L)) • basis c 1 :=
  (rfl)

/-- Left multiplication by `inc c x` is the `L`-module structure. -/
theorem smul_def (x : L) (a : CrossedProduct c) : x • a = inc c x * a := by
  rw [inc_apply, smul_mul_assoc]
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [mul_add, smul_add, ha, hb]
  | smul_basis σ y =>
    rw [← one_smul L (basis c 1), smul_basis_mul_smul_basis]
    simp only [c.toFun_one_left, AlgEquiv.one_apply, one_mul, smul_smul]
    congr 1
    linear_combination (-(x * y)) * Units.inv_mul (c.toFun 1 1)

/-- `u_1 = c(1, 1) · 1`. -/
theorem basis_one : basis c 1 = inc c (c.toFun 1 1) := by
  rw [inc_apply, Units.mul_inv, one_smul]

/-- **The semilinearity rule** `u_σ · x = σ(x) · u_σ`. -/
@[simp]
theorem basis_mul_inc (σ : L ≃ₐ[K] L) (x : L) :
    basis c σ * inc c x = inc c (σ x) * basis c σ := by
  rw [← smul_def, inc_apply, ← one_smul L (basis c σ), smul_basis_mul_smul_basis]
  rw [one_smul, c.toFun_one_right, one_mul]
  congr 1
  calc
    σ (x * (↑(c.toFun 1 1)⁻¹ : L)) * σ (c.toFun 1 1 : L) =
        σ x * σ ((↑(c.toFun 1 1)⁻¹ : L) * c.toFun 1 1) := by
          rw [map_mul, mul_assoc, map_mul]
    _ = σ x := by rw [Units.inv_mul, map_one, mul_one]

/-- **The cocycle rule** `u_σ · u_τ = c(σ, τ) · u_{στ}`. -/
@[simp]
theorem basis_mul_basis (σ τ : L ≃ₐ[K] L) :
    basis c σ * basis c τ = inc c (c.toFun σ τ) * basis c (σ * τ) := by
  rw [← smul_def, ← one_smul L (basis c σ), ← one_smul L (basis c τ),
    smul_basis_mul_smul_basis]
  simp only [map_one, one_mul]

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

section Lift

variable {R : Type*} [Semiring R] [Algebra K R]

/-- The **universal property of the crossed product**: a `K`-algebra homomorphism `f : L → R`
together with elements `u σ ∈ R` satisfying `u σ · f(x) = f(σ x) · u σ`,
`u σ · u τ = f(c(σ, τ)) · u (στ)` and `u 1 = f(c(1, 1))` extends to the `K`-algebra homomorphism
`x · u_σ ↦ f(x) · u σ` out of `CrossedProduct c`. The last condition is `basis_one`; without it
`u = 0` would satisfy the first two. -/
noncomputable def lift (f : L →ₐ[K] R) (u : (L ≃ₐ[K] L) → R)
    (hf : ∀ σ x, u σ * f x = f (σ x) * u σ)
    (hu : ∀ σ τ, u σ * u τ = f (c.toFun σ τ) * u (σ * τ)) (hu₁ : u 1 = f (c.toFun 1 1)) :
    CrossedProduct c →ₐ[K] R :=
  have hsb (σ : L ≃ₐ[K] L) (x : L) : (Finsupp.lsum K fun σ ↦
      LinearMap.mulRight K (u σ) ∘ₗ f.toLinearMap) ((basis c).repr (x • basis c σ)) =
      f x * u σ := by
    simp
  AlgHom.ofLinearMap ((Finsupp.lsum K fun σ ↦ LinearMap.mulRight K (u σ) ∘ₗ f.toLinearMap) ∘ₗ
      (basis c).repr.toLinearMap.restrictScalars K)
    (by
      rw [LinearMap.comp_apply, one_def, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, hsb,
        hu₁, ← map_mul, Units.inv_mul, map_one])
    fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
      induction a using induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
      | smul_basis σ x =>
        induction b using induction_on with
        | zero => simp
        | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
        | smul_basis τ y =>
          rw [smul_basis_mul_smul_basis, hsb, hsb, hsb, map_mul, map_mul, mul_assoc, mul_assoc,
            ← hu, ← mul_assoc (f (σ y)), ← hf]
          simp only [mul_assoc]

variable (f : L →ₐ[K] R) (u : (L ≃ₐ[K] L) → R) (hf : ∀ σ x, u σ * f x = f (σ x) * u σ)
  (hu : ∀ σ τ, u σ * u τ = f (c.toFun σ τ) * u (σ * τ)) (hu₁ : u 1 = f (c.toFun 1 1))

/-- `CrossedProduct.lift` sends `x · u_σ` to `f(x) · u σ`. -/
@[simp]
theorem lift_smul_basis (σ : L ≃ₐ[K] L) (x : L) :
    lift f u hf hu hu₁ (x • basis c σ) = f x * u σ := by
  simp [lift]

/-- `CrossedProduct.lift` sends the basis element `u_σ` to `u σ`. -/
@[simp]
theorem lift_basis (σ : L ≃ₐ[K] L) : lift f u hf hu hu₁ (basis c σ) = u σ := by
  rw [← one_smul L (basis c σ), lift_smul_basis, map_one, one_mul]

/-- `CrossedProduct.lift` restricts to `f` on the copy `inc c` of `L`. -/
@[simp]
theorem lift_inc (x : L) : lift f u hf hu hu₁ (inc c x) = f x := by
  rw [inc_apply, lift_smul_basis, hu₁, ← map_mul, mul_assoc, Units.inv_mul, mul_one]

/-- **Uniqueness in the universal property**: a `K`-algebra homomorphism out of `CrossedProduct c`
is determined by its values on the copy `inc c` of `L` and on the basis elements `u_σ`. -/
@[ext]
theorem algHom_ext {F G : CrossedProduct c →ₐ[K] R} (hinc : ∀ x, F (inc c x) = G (inc c x))
    (hbasis : ∀ σ, F (basis c σ) = G (basis c σ)) : F = G :=
  AlgHom.ext fun a ↦ by
    induction a using induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul_basis σ x => rw [smul_def, map_mul, map_mul, hinc, hbasis]

/-- `CrossedProduct.lift` is the unique `K`-algebra homomorphism restricting to `f` on `inc c` and
sending each `u_σ` to `u σ`. -/
theorem lift_unique (F : CrossedProduct c →ₐ[K] R) (hinc : ∀ x, F (inc c x) = f x)
    (hbasis : ∀ σ, F (basis c σ) = u σ) : F = lift f u hf hu hu₁ :=
  algHom_ext (fun x ↦ by rw [hinc, lift_inc]) fun σ ↦ by rw [hbasis, lift_basis]

end Lift

/-- A crossed product over a nontrivial ring `L` is nontrivial. -/
instance [Nontrivial L] : Nontrivial (CrossedProduct c) :=
  nontrivial_of_ne _ _ ((basis c).ne_zero 1)

section Field

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (c : TwoCocycle K L)

/-- The crossed product satisfies the natural-number identity
`Module.finrank K (CrossedProduct c) = Module.finrank K L * Nat.card (Aut_K(L))`.
Without finite-dimensionality, these are truncated invariants rather than cardinal dimensions. -/
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
