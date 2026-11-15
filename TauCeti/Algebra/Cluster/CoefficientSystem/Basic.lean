/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.ExchangePolynomial
public import Mathlib.Algebra.Group.Subgroup.Lattice

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.NNRat
import Mathlib.Tactic.NormNum

/-!
# Coefficient systems

Under cluster mutation, dilating an exchange polynomial by the endpoint propagation factor fixes
the mutated polynomial only up to a unit multiple. A *coefficient system* over a commutative
semiring `R` specifies:

* a commutative monoid with zero `𝕂` in which the polynomial coefficients live;
* a multiplicative map `toScalar : 𝕂 →*₀ R` realizing coefficients as scalars in `R` (without
  requiring additivity or injectivity);
* a *normalizer* `normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ` invariant under polynomial reversal and
  satisfying `normalizer (H.scale (normalizer H')) * normalizer H' = normalizer H`.

Multiplying `H` by `normalizer H` defines an idempotent normalization operator `normalize`. Calling
`H` *normalized* when `normalizer H = 1`, the values of `normalizer` form a subgroup
`normalizerSubgroup ≤ 𝕂ˣ` on which `normalizer` is homogeneous of degree `-1`, and the normalized
polynomials form a reversal-stable set of orbit representatives for the unit-scaling action of that
subgroup. Conversely, any subgroup `G ≤ 𝕂ˣ` and reversal-stable set of orbit representatives for
`G` uniquely determine a coefficient system with those invariants.

The *scalar system* `CoefficientSystem.trivial R` takes `𝕂 = R`, `toScalar = id`, and
`normalizer = 1`; its exchange-data mutation is unnormalized polynomial mutation.

## Main definitions

* `TauCeti.CoefficientSystem 𝕂 R`: a coefficient system over `R` with coefficient monoid `𝕂`.
* `TauCeti.CoefficientSystem.normalize`: the normalized multiple `H.scale (c.normalizer H)`.
* `TauCeti.CoefficientSystem.IsNormalized`: the predicate `c.normalizer H = 1`.
* `TauCeti.CoefficientSystem.valueAtOne`: the scalar sum `∑_{l=0}^r c.toScalar (H.coeff l)`.
* `TauCeti.CoefficientSystem.normalizerSubgroup`: the subgroup `G_ν ≤ 𝕂ˣ` of normalizer values.
* `TauCeti.CoefficientSystem.ofRepresentatives`: the coefficient system determined by a subgroup
  `G ≤ 𝕂ˣ` and a reversal-stable set of orbit representatives for `G`.
* `TauCeti.CoefficientSystem.trivial R`: the scalar system with `𝕂 = R` and `normalizer = 1`.

## Main results

* `TauCeti.CoefficientSystem.normalize_normalize`: normalization is idempotent.
* `TauCeti.CoefficientSystem.isNormalized_reverse`: reversal preserves normalized polynomials.
* `TauCeti.CoefficientSystem.normalizer_scale_of_mem`: `normalizer` is homogeneous of degree `-1`
  with respect to `normalizerSubgroup`.
* `TauCeti.CoefficientSystem.existsUnique_mem_normalizerSubgroup_isNormalized`: every exchange
  polynomial has a unique scaling in `normalizerSubgroup` that is normalized.
* `TauCeti.CoefficientSystem.eq_ofRepresentatives`: a coefficient system is uniquely determined by
  its scalar map, its normalizer subgroup, and its set of normalized polynomials.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002), §5.
* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2.
-/

public section

namespace TauCeti

/-- A *coefficient system* over a commutative semiring `R` with coefficients in a commutative
monoid with zero `𝕂`: a multiplicative scalar map `toScalar : 𝕂 →*₀ R` (which need not be additive
or injective) together with a reversal-invariant normalizer `normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ`
satisfying `normalizer (H.scale (normalizer H')) * normalizer H' = normalizer H`. -/
@[ext]
structure CoefficientSystem (𝕂 : Type*) [CommMonoidWithZero 𝕂]
    (R : Type*) [CommSemiring R] where
  /-- The multiplicative realization of coefficients in the scalar semiring `R`. -/
  toScalar : 𝕂 →*₀ R
  /-- The normalizer assigning a unit of `𝕂` to each exchange polynomial. -/
  normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ
  /-- Reversing an exchange polynomial leaves its normalizer unchanged. -/
  normalizer_reverse : ∀ H, normalizer H.reverse = normalizer H
  /-- Scaling by any value of the normalizer scales the normalizer inversely. -/
  normalizer_scale : ∀ H H', normalizer (H.scale (normalizer H')) * normalizer H' = normalizer H

namespace CoefficientSystem

variable {𝕂 R : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R]

attribute [simp] normalizer_reverse normalizer_scale

/-! ### Normalization and normalized polynomials -/

/-- The normalized multiple `ν(H) H` of an exchange polynomial `H`. -/
def normalize (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 :=
  H.scale (c.normalizer H)

/-- Restatement of `normalize` as scaling by `c.normalizer H`. -/
theorem normalize_def (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.normalize H = H.scale (c.normalizer H) :=
  (rfl)

@[simp]
theorem normalize_degree (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    (c.normalize H).degree = H.degree := by
  simp [normalize_def]

@[simp]
theorem normalize_coeff (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂)
    (l : Fin ((c.normalize H).degree + 1)) :
    (c.normalize H).coeff l =
      (c.normalizer H : 𝕂) * H.coeff (l.cast (congrArg (· + 1) (c.normalize_degree H))) :=
  ExchangePolynomial.scale_coeff H (c.normalizer H) l

/-- The normalizer of a normalized polynomial `c.normalize H` is `1`. -/
@[simp]
theorem normalizer_normalize (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.normalizer (c.normalize H) = 1 :=
  mul_eq_right.mp (c.normalizer_scale H H)

/-- Normalization is idempotent: `N(N(H)) = N(H)`. -/
@[simp]
theorem normalize_normalize (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.normalize (c.normalize H) = c.normalize H := by
  rw [normalize_def, normalizer_normalize, ExchangePolynomial.scale_one]

/-- Normalization commutes with polynomial reversal. -/
@[simp]
theorem reverse_normalize (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    (c.normalize H).reverse = c.normalize H.reverse := by
  rw [normalize_def, normalize_def, ExchangePolynomial.reverse_scale, normalizer_reverse]

/-- An exchange polynomial `H` is *normalized* for `c` when `c.normalizer H = 1`. -/
def IsNormalized (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) : Prop :=
  c.normalizer H = 1

/-- Restatement of `IsNormalized` as `c.normalizer H = 1`. -/
theorem isNormalized_def {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂} :
    c.IsNormalized H ↔ c.normalizer H = 1 :=
  Iff.rfl

theorem IsNormalized.normalizer_eq {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂}
    (h : c.IsNormalized H) : c.normalizer H = 1 :=
  h

/-- Normalized polynomials are fixed points of `normalize`. -/
theorem IsNormalized.normalize_eq {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂}
    (h : c.IsNormalized H) : c.normalize H = H := by
  rw [normalize_def, h.normalizer_eq, ExchangePolynomial.scale_one]

/-- An exchange polynomial is normalized if and only if `c.normalize H = H`. -/
theorem isNormalized_iff_normalize_eq {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂} :
    c.IsNormalized H ↔ c.normalize H = H := by
  rw [isNormalized_def, normalize_def, ExchangePolynomial.scale_eq_self]

@[simp]
theorem isNormalized_normalize (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.IsNormalized (c.normalize H) :=
  c.normalizer_normalize H

/-- Reversal preserves normalized exchange polynomials. -/
protected theorem IsNormalized.reverse {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂}
    (h : c.IsNormalized H) : c.IsNormalized H.reverse := by
  simpa only [isNormalized_def, normalizer_reverse] using h

@[simp]
theorem isNormalized_reverse {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂} :
    c.IsNormalized H.reverse ↔ c.IsNormalized H := by
  simp only [isNormalized_def, normalizer_reverse]

/-- The scalar value `H(1) = ∑ l, c.toScalar (H.coeff l)` of an exchange polynomial `H` in `R`. -/
def valueAtOne (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) : R :=
  ∑ l, c.toScalar (H.coeff l)

theorem valueAtOne_def (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.valueAtOne H = ∑ l, c.toScalar (H.coeff l) :=
  (rfl)

@[simp]
theorem valueAtOne_reverse (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.valueAtOne H.reverse = c.valueAtOne H :=
  H.sum_reverse c.toScalar

theorem valueAtOne_scale (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    c.valueAtOne (H.scale e) = c.toScalar e * c.valueAtOne H := by
  rw [valueAtOne_def, H.sum_scale e c.toScalar]
  simp only [map_mul, ← Finset.mul_sum, ← valueAtOne_def]

@[simp]
theorem valueAtOne_binary (c : CoefficientSystem 𝕂 R) :
    c.valueAtOne ExchangePolynomial.binary = 2 := by
  rw [valueAtOne_def, ExchangePolynomial.sum_binary, map_one, one_add_one_eq_two]

/-! ### The normalizer subgroup and orbit representatives -/

/-- The subgroup `G_ν ≤ 𝕂ˣ` generated by the values of `c.normalizer`. -/
def normalizerSubgroup (c : CoefficientSystem 𝕂 R) : Subgroup 𝕂ˣ :=
  Subgroup.closure (Set.range c.normalizer)

/-- Every value of `c.normalizer` belongs to `c.normalizerSubgroup`. -/
theorem normalizer_mem_normalizerSubgroup (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂) :
    c.normalizer H ∈ c.normalizerSubgroup :=
  Subgroup.subset_closure ⟨H, rfl⟩

/-- The normalizer `c.normalizer` is homogeneous of degree `-1` for the scaling action of
`c.normalizerSubgroup`. -/
theorem normalizer_scale_of_mem (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂)
    {g : 𝕂ˣ} (hg : g ∈ c.normalizerSubgroup) :
    c.normalizer (H.scale g) = g⁻¹ * c.normalizer H := by
  induction hg using Subgroup.closure_induction generalizing H with
  | mem x hx =>
    obtain ⟨H', rfl⟩ := hx
    exact eq_inv_mul_of_mul_eq (by rw [mul_comm, c.normalizer_scale])
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [← ExchangePolynomial.scale_scale, ihy, ihx, mul_inv_rev, mul_assoc]
  | inv x _ ihx =>
    have h := ihx (H.scale x⁻¹)
    rw [ExchangePolynomial.scale_inv_mul_cancel] at h
    calc
      c.normalizer (H.scale x⁻¹) = x * (x⁻¹ * c.normalizer (H.scale x⁻¹)) := by simp
      _ = (x⁻¹)⁻¹ * c.normalizer H := by rw [← h, inv_inv]

/-- The underlying set of `c.normalizerSubgroup` is already `Set.range c.normalizer`: the values of
`c.normalizer` form a subgroup of `𝕂ˣ` without taking products or inverses. -/
@[simp]
theorem coe_normalizerSubgroup (c : CoefficientSystem 𝕂 R) :
    (c.normalizerSubgroup : Set 𝕂ˣ) = Set.range c.normalizer := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_range]
  refine ⟨fun hg ↦ ?_, fun ⟨H, hH⟩ ↦ hH ▸ c.normalizer_mem_normalizerSubgroup H⟩
  refine ⟨(c.normalize ExchangePolynomial.binary).scale g⁻¹, ?_⟩
  rw [c.normalizer_scale_of_mem _ (inv_mem hg), inv_inv, normalizer_normalize, mul_one]

/-- Membership in `c.normalizerSubgroup` is equivalent to being a value of `c.normalizer`. -/
theorem mem_normalizerSubgroup_iff {c : CoefficientSystem 𝕂 R} {g : 𝕂ˣ} :
    g ∈ c.normalizerSubgroup ↔ ∃ H, c.normalizer H = g := by
  rw [← SetLike.mem_coe, coe_normalizerSubgroup, Set.mem_range]

/-- Scaling by an element of `c.normalizerSubgroup` does not change `c.normalize H`. -/
@[simp]
theorem normalize_scale_of_mem (c : CoefficientSystem 𝕂 R) (H : ExchangePolynomial 𝕂)
    {g : 𝕂ˣ} (hg : g ∈ c.normalizerSubgroup) :
    c.normalize (H.scale g) = c.normalize H := by
  rw [normalize_def, c.normalizer_scale_of_mem H hg, ExchangePolynomial.scale_scale,
    mul_inv_cancel_left, ← normalize_def]

@[simp]
theorem normalize_scale_normalizer (c : CoefficientSystem 𝕂 R) (H H' : ExchangePolynomial 𝕂) :
    c.normalize (H.scale (c.normalizer H')) = c.normalize H :=
  c.normalize_scale_of_mem H (c.normalizer_mem_normalizerSubgroup H')

/-- The normalized polynomials form a set of orbit representatives for the scaling action of
`c.normalizerSubgroup`: every exchange polynomial `H` has a unique `g ∈ c.normalizerSubgroup` for
which `H.scale g` is normalized, namely `c.normalizer H`. -/
theorem existsUnique_mem_normalizerSubgroup_isNormalized (c : CoefficientSystem 𝕂 R)
    (H : ExchangePolynomial 𝕂) :
    ∃! g : c.normalizerSubgroup, c.IsNormalized (H.scale g) := by
  refine ⟨⟨c.normalizer H, c.normalizer_mem_normalizerSubgroup H⟩, c.isNormalized_normalize H, ?_⟩
  rintro ⟨g, hg⟩ hnorm
  rw [isNormalized_def, c.normalizer_scale_of_mem H hg, inv_mul_eq_one] at hnorm
  exact Subtype.ext hnorm

/-! ### Converse construction from orbit representatives -/

/-- Construct a coefficient system from a scalar map `toScalar : 𝕂 →*₀ R`, a subgroup
`G : Subgroup 𝕂ˣ`, and a reversal-stable set `S` of orbit representatives for the unit-scaling
action of `G`. -/
noncomputable def ofRepresentatives (toScalar : 𝕂 →*₀ R) (G : Subgroup 𝕂ˣ)
    (S : Set (ExchangePolynomial 𝕂)) (hrev : ∀ ⦃H⦄, H ∈ S → H.reverse ∈ S)
    (hex : ∀ H : ExchangePolynomial 𝕂, ∃! g : G, H.scale g ∈ S) : CoefficientSystem 𝕂 R where
  toScalar := toScalar
  normalizer H := ((hex H).choose : 𝕂ˣ)
  normalizer_reverse H := by
    have hmem : H.reverse.scale ((hex H).choose : 𝕂ˣ) ∈ S := by
      rw [← ExchangePolynomial.reverse_scale]
      exact hrev (hex H).choose_spec.1
    exact congrArg Subtype.val ((hex H.reverse).choose_spec.2 _ hmem).symm
  normalizer_scale H H' := by
    let g : G := (hex H).choose
    let g' : G := (hex H').choose
    have hmem : (H.scale (g' : 𝕂ˣ)).scale ((g * g'⁻¹ : G) : 𝕂ˣ) ∈ S := by
      rw [ExchangePolynomial.scale_scale, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_comm (g' : 𝕂ˣ), inv_mul_cancel_right]
      exact (hex H).choose_spec.1
    have heq : (hex (H.scale (g' : 𝕂ˣ))).choose = g * g'⁻¹ :=
      ((hex (H.scale (g' : 𝕂ˣ))).choose_spec.2 (g * g'⁻¹) hmem).symm
    calc
      ((hex (H.scale (g' : 𝕂ˣ))).choose : 𝕂ˣ) * (g' : 𝕂ˣ)
          = ((g * g'⁻¹ : G) : 𝕂ˣ) * (g' : 𝕂ˣ) := by rw [heq]
      _ = (g : 𝕂ˣ) := by simp

section OfRepresentatives

variable (toScalar : 𝕂 →*₀ R) (G : Subgroup 𝕂ˣ) (S : Set (ExchangePolynomial 𝕂))
  (hrev : ∀ ⦃H⦄, H ∈ S → H.reverse ∈ S)
  (hex : ∀ H : ExchangePolynomial 𝕂, ∃! g : G, H.scale g ∈ S)

@[simp]
theorem ofRepresentatives_toScalar :
    (ofRepresentatives toScalar G S hrev hex).toScalar = toScalar :=
  (rfl)

theorem normalizer_ofRepresentatives_mem (H : ExchangePolynomial 𝕂) :
    (ofRepresentatives toScalar G S hrev hex).normalizer H ∈ G :=
  ((hex H).choose).property

@[simp]
theorem normalize_ofRepresentatives_mem (H : ExchangePolynomial 𝕂) :
    (ofRepresentatives toScalar G S hrev hex).normalize H ∈ S :=
  (hex H).choose_spec.1

/-- The normalized polynomials of `ofRepresentatives` are precisely the members of `S`. -/
@[simp]
theorem isNormalized_ofRepresentatives_iff {H : ExchangePolynomial 𝕂} :
    (ofRepresentatives toScalar G S hrev hex).IsNormalized H ↔ H ∈ S := by
  constructor
  · intro h
    have hmem := normalize_ofRepresentatives_mem toScalar G S hrev hex H
    rwa [h.normalize_eq] at hmem
  · intro hS
    have h1 : H.scale ((1 : G) : 𝕂ˣ) ∈ S := by simpa using hS
    have heq : (hex H).choose = 1 := ((hex H).choose_spec.2 1 h1).symm
    exact congrArg Subtype.val heq

/-- The normalizer subgroup of `ofRepresentatives` recovers `G`. -/
@[simp]
theorem normalizerSubgroup_ofRepresentatives :
    (ofRepresentatives toScalar G S hrev hex).normalizerSubgroup = G := by
  let c := ofRepresentatives toScalar G S hrev hex
  ext g
  rw [mem_normalizerSubgroup_iff]
  constructor
  · rintro ⟨H, rfl⟩
    exact normalizer_ofRepresentatives_mem toScalar G S hrev hex H
  · intro hg
    let H₀ := c.normalize ExchangePolynomial.binary
    have hH₀ : H₀ ∈ S := normalize_ofRepresentatives_mem toScalar G S hrev hex _
    refine ⟨H₀.scale g⁻¹, ?_⟩
    have hmem : (H₀.scale g⁻¹).scale (⟨g, hg⟩ : G) ∈ S := by
      simpa using hH₀
    exact congrArg Subtype.val ((hex (H₀.scale g⁻¹)).choose_spec.2 ⟨g, hg⟩ hmem).symm

/-- A coefficient system is uniquely determined by its scalar map, its normalizer subgroup, and its
set of normalized exchange polynomials. -/
theorem eq_ofRepresentatives (c : CoefficientSystem 𝕂 R) {G : Subgroup 𝕂ˣ}
    {S : Set (ExchangePolynomial 𝕂)} (hG : c.normalizerSubgroup = G)
    (hS : {H | c.IsNormalized H} = S) (hrev : ∀ ⦃H⦄, H ∈ S → H.reverse ∈ S)
    (hex : ∀ H : ExchangePolynomial 𝕂, ∃! g : G, H.scale g ∈ S) :
    c = ofRepresentatives c.toScalar G S hrev hex := by
  ext x : 2
  · rfl
  · have hxG : c.normalizer x ∈ G := hG ▸ c.normalizer_mem_normalizerSubgroup x
    have hxS : x.scale (c.normalizer x) ∈ S := hS ▸ c.isNormalized_normalize x
    exact congrArg Subtype.val ((hex x).choose_spec.2 ⟨c.normalizer x, hxG⟩ hxS)

end OfRepresentatives

/-! ### The scalar system -/

/-- The *scalar coefficient system* over a commutative semiring `R`: coefficients live in `R`
itself, `toScalar` is the identity, and `normalizer` is identically `1`. Its exchange-data
mutation is unnormalized polynomial mutation. -/
def trivial (R : Type*) [CommSemiring R] : CoefficientSystem R R where
  toScalar := MonoidWithZeroHom.id R
  normalizer _ := 1
  normalizer_reverse _ := rfl
  normalizer_scale _ _ := one_mul 1

@[simp]
theorem trivial_toScalar : (trivial R).toScalar = MonoidWithZeroHom.id R :=
  (rfl)

@[simp]
theorem trivial_normalizer (H : ExchangePolynomial R) : (trivial R).normalizer H = 1 :=
  (rfl)

@[simp]
theorem normalize_trivial (H : ExchangePolynomial R) : (trivial R).normalize H = H := by
  simp [normalize_def]

@[simp]
theorem isNormalized_trivial (H : ExchangePolynomial R) : (trivial R).IsNormalized H := by
  rw [isNormalized_def, trivial_normalizer]

@[simp]
theorem normalizerSubgroup_trivial : (trivial R).normalizerSubgroup = ⊥ := by
  ext g
  simp only [mem_normalizerSubgroup_iff, trivial_normalizer, Subgroup.mem_bot]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨ExchangePolynomial.binary, h.symm⟩⟩

/-! ### Checks -/

/-- Over `ℚ≥0`, normalizing every exchange polynomial by the inverse of the sum of its coefficients
defines a coefficient system in which `1 + T` is not normalized (`ν(1 + T) = 1 / 2`), whereas its
normalization `(1 + T) / 2` is normalized. -/
noncomputable example :
    ∃ c : CoefficientSystem ℚ≥0 ℚ≥0,
      ¬ c.IsNormalized ExchangePolynomial.binary ∧
        c.IsNormalized (c.normalize ExchangePolynomial.binary) := by
  have hsum_ne : ∀ H : ExchangePolynomial ℚ≥0, ∑ l, H.coeff l ≠ 0 := fun H ↦ by
    have h0 : 0 < H.coeff 0 := lt_of_le_of_ne zero_le H.isUnit_coeff_zero.ne_zero.symm
    have hle : H.coeff 0 ≤ ∑ l, H.coeff l :=
      Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ 0)
    exact (h0.trans_le hle).ne'
  let μ (H : ExchangePolynomial ℚ≥0) : ℚ≥0ˣ := (Units.mk0 (∑ l, H.coeff l) (hsum_ne H))⁻¹
  let c : CoefficientSystem ℚ≥0 ℚ≥0 :=
    { toScalar := MonoidWithZeroHom.id ℚ≥0
      normalizer := μ
      normalizer_reverse H := by
        apply inv_inj.mpr
        refine Units.ext ?_
        simpa [μ] using H.sum_reverse id
      normalizer_scale H H' := by
        refine Units.ext ?_
        have hscale : ∑ l, (H.scale (μ H')).coeff l = ∑ l, ((μ H' : ℚ≥0) * H.coeff l) :=
          H.sum_scale (μ H') id
        simp only [μ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at hscale ⊢
        rw [hscale, ← Finset.mul_sum, mul_inv, mul_right_comm, inv_inv,
          mul_inv_cancel₀ (hsum_ne H'), one_mul] }
  refine ⟨c, ?_, c.isNormalized_normalize _⟩
  rw [isNormalized_def]
  intro h
  have hval : ((c.normalizer ExchangePolynomial.binary : ℚ≥0ˣ) : ℚ≥0) = 1 :=
    congrArg Units.val h
  have hbin : ∑ l, (ExchangePolynomial.binary : ExchangePolynomial ℚ≥0).coeff l = 1 + 1 :=
    ExchangePolynomial.sum_binary id
  simp only [c, μ, Units.val_inv_eq_inv_val, Units.val_mk0, hbin] at hval
  norm_num at hval

end CoefficientSystem

end TauCeti
