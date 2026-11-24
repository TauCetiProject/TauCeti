/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import TauCeti.Algebra.Cluster.CoefficientSystem.ExchangePolynomial

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.NNRat

/-!
# Coefficient systems

A *coefficient system* over a commutative semiring `R` specifies a commutative monoid with zero `𝕂`
in which polynomial coefficients live, a multiplicative scalar map `φ : 𝕂 →*₀ R` (which need not be
additive or injective), and a normalizer `ν : ExchangePolynomial 𝕂 → 𝕂ˣ` invariant under reversal
and homogeneous of degree `-1` along its own values (`ν(H.scale (ν H')) * ν(H') = ν(H)`).

Two canonical instances govern cluster patterns: `CoefficientSystem.trivial R` (`𝕂 = R`, `φ = id`,
`ν = 1`) for unnormalized polynomial mutation, and `CoefficientSystem.ofSemifield φ`
(`ν(H) = (∑_{l=0}^r h_l)⁻¹` formed in `F` before `φ`) for zero-sum-free semifields `F`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  Definition 5.3.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  (2.14).
-/

public section

namespace TauCeti

/-- A *coefficient system* over a commutative semiring `R`: a commutative monoid with zero `𝕂` in
which polynomial coefficients live, a multiplicative map `toScalar : 𝕂 →*₀ R` (which need not be
additive or injective), and a normalizer `normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ` invariant under
reversal and homogeneous of degree `-1` for the units it produces. -/
@[ext]
structure CoefficientSystem (𝕂 : Type*) [CommMonoidWithZero 𝕂] (R : Type*) [CommSemiring R] where
  /-- Multiplicative map sending coefficients in `𝕂` to scalars in `R`. -/
  toScalar : 𝕂 →*₀ R
  /-- Normalizing unit attached to each exchange polynomial over `𝕂`. -/
  normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ
  /-- Reversing an exchange polynomial leaves its normalizer unchanged. -/
  normalizer_reverse : ∀ H, normalizer H.reverse = normalizer H
  /-- Scaling by any normalizer value multiplies the normalizer by the inverse unit. -/
  normalizer_scale : ∀ H H', normalizer (H.scale (normalizer H')) * normalizer H' = normalizer H

attribute [simp] CoefficientSystem.normalizer_reverse

namespace CoefficientSystem

section General

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂] {R : Type*} [CommSemiring R]
  (c : CoefficientSystem 𝕂 R)

/-- The normalized multiple `ν(H) H` of an exchange polynomial. -/
def normalize (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 := H.scale (c.normalizer H)

theorem normalize_def (H : ExchangePolynomial 𝕂) : c.normalize H = H.scale (c.normalizer H) := (rfl)

@[simp]
theorem degree_normalize (H : ExchangePolynomial 𝕂) : (c.normalize H).degree = H.degree :=
  H.degree_scale _

@[simp]
theorem coeff_normalize (H : ExchangePolynomial 𝕂) (l : ℕ) :
    (c.normalize H).coeff l = (c.normalizer H : 𝕂) * H.coeff l :=
  H.coeff_scale (c.normalizer H) l

/-- An exchange polynomial is *normalized* for `c` when its normalizer is `1`. -/
def IsNormalized (H : ExchangePolynomial 𝕂) : Prop := c.normalizer H = 1

theorem isNormalized_iff {H : ExchangePolynomial 𝕂} : c.IsNormalized H ↔ c.normalizer H = 1 :=
  Iff.rfl

@[simp]
theorem normalizer_normalize (H : ExchangePolynomial 𝕂) : c.normalizer (c.normalize H) = 1 :=
  (mul_left_inj (c.normalizer H)).mp (by simpa [normalize_def] using c.normalizer_scale H H)

@[simp]
theorem isNormalized_normalize (H : ExchangePolynomial 𝕂) : c.IsNormalized (c.normalize H) :=
  c.normalizer_normalize H

protected theorem IsNormalized.normalize_eq {H : ExchangePolynomial 𝕂} (h : c.IsNormalized H) :
    c.normalize H = H := by rw [normalize_def, h, H.scale_one]

@[simp]
theorem normalize_eq_self_iff {H : ExchangePolynomial 𝕂} :
    c.normalize H = H ↔ c.IsNormalized H := by
  rw [normalize_def, H.scale_eq_self, isNormalized_iff]

/-- Normalization is idempotent. -/
@[simp]
theorem normalize_normalize (H : ExchangePolynomial 𝕂) :
    c.normalize (c.normalize H) = c.normalize H :=
  (c.isNormalized_normalize H).normalize_eq

@[simp]
theorem normalize_reverse (H : ExchangePolynomial 𝕂) :
    c.normalize H.reverse = (c.normalize H).reverse := by simp [normalize_def]

protected theorem IsNormalized.reverse {H : ExchangePolynomial 𝕂} (h : c.IsNormalized H) :
    c.IsNormalized H.reverse := by simpa [IsNormalized] using h

@[simp]
theorem isNormalized_reverse_iff {H : ExchangePolynomial 𝕂} :
    c.IsNormalized H.reverse ↔ c.IsNormalized H :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

/-- The normalized polynomials are exactly the normalized multiples. -/
theorem isNormalized_iff_exists_normalize_eq {H : ExchangePolynomial 𝕂} :
    c.IsNormalized H ↔ ∃ G, c.normalize G = H :=
  ⟨fun hH ↦ ⟨H, hH.normalize_eq⟩, fun ⟨G, hG⟩ ↦ hG ▸ c.isNormalized_normalize G⟩

/-- Scaling by a value of the normalizer divides the normalizer by that value. -/
theorem normalizer_scale_normalizer (H H' : ExchangePolynomial 𝕂) :
    c.normalizer (H.scale (c.normalizer H')) = c.normalizer H * (c.normalizer H')⁻¹ :=
  eq_mul_inv_of_mul_eq (c.normalizer_scale H H')

/-- Scaling by the inverse of a value of the normalizer multiplies the normalizer by that
value. -/
theorem normalizer_scale_inv_normalizer (H H' : ExchangePolynomial 𝕂) :
    c.normalizer (H.scale (c.normalizer H')⁻¹) = c.normalizer H * c.normalizer H' := by
  simpa using (c.normalizer_scale (H.scale (c.normalizer H')⁻¹) H').symm

/-! ### Value subgroup and orbit transversals -/

/-- The subgroup `G_ν ≤ 𝕂ˣ` generated by all values of the normalizer. -/
def normalizerSubgroup : Subgroup 𝕂ˣ := Subgroup.closure (Set.range c.normalizer)

theorem normalizerSubgroup_def : c.normalizerSubgroup = Subgroup.closure (Set.range c.normalizer) :=
  (rfl)

theorem normalizer_mem_normalizerSubgroup (H : ExchangePolynomial 𝕂) :
    c.normalizer H ∈ c.normalizerSubgroup :=
  Subgroup.subset_closure ⟨H, rfl⟩

/-- The normalizer is homogeneous of degree `-1` for the subgroup `G_ν` generated by its values. -/
theorem normalizer_scale_of_mem {u : 𝕂ˣ} (hu : u ∈ c.normalizerSubgroup)
    (H : ExchangePolynomial 𝕂) : c.normalizer (H.scale u) = u⁻¹ * c.normalizer H := by
  induction hu using Subgroup.closure_induction generalizing H with
  | mem _ hx =>
    obtain ⟨H', rfl⟩ := hx
    exact eq_inv_mul_of_mul_eq (by rw [mul_comm, c.normalizer_scale])
  | one => simp
  | mul x y _ _ ihx ihy =>
    conv_lhs => rw [mul_comm x y]
    simpa [ihx, mul_assoc] using ihy (H.scale x)
  | inv x _ ihx => simpa [mul_assoc] using congrArg (x * ·) (ihx (H.scale x⁻¹)).symm

theorem mem_normalizerSubgroup_iff {u : 𝕂ˣ} :
    u ∈ c.normalizerSubgroup ↔ ∃ H, c.normalizer H = u := by
  refine ⟨fun hu ↦ ⟨(c.normalize ExchangePolynomial.binary).scale u⁻¹, ?_⟩, ?_⟩
  · simp [c.normalizer_scale_of_mem (inv_mem hu)]
  · rintro ⟨H, rfl⟩; exact c.normalizer_mem_normalizerSubgroup H

/-- Normalization is invariant under scaling by any element of `G_ν`. -/
theorem normalize_scale_of_mem {u : 𝕂ˣ} (hu : u ∈ c.normalizerSubgroup)
    (H : ExchangePolynomial 𝕂) : c.normalize (H.scale u) = c.normalize H := by
  simp [normalize_def, c.normalizer_scale_of_mem hu H, mul_comm _ u]

@[simp]
theorem normalize_scale_normalizer (H H' : ExchangePolynomial 𝕂) :
    c.normalize (H.scale (c.normalizer H')) = c.normalize H :=
  c.normalize_scale_of_mem (c.normalizer_mem_normalizerSubgroup H') H

/-- Every `G_ν`-scaling orbit meets `{H | c.IsNormalized H}` in a unique element. -/
theorem existsUnique_mem_normalizerSubgroup_isNormalized_scale (H : ExchangePolynomial 𝕂) :
    ∃! u : c.normalizerSubgroup, c.IsNormalized (H.scale u.val) := by
  refine ⟨⟨c.normalizer H, c.normalizer_mem_normalizerSubgroup H⟩, c.isNormalized_normalize H, ?_⟩
  rintro ⟨u, hu⟩ hnorm
  exact Subtype.ext (inv_mul_eq_one.mp ((c.normalizer_scale_of_mem hu H).symm.trans hnorm))

/-- The normalizer subgroup consists exactly of the values of the normalizer. -/
@[simp]
theorem coe_normalizerSubgroup : (c.normalizerSubgroup : Set 𝕂ˣ) = Set.range c.normalizer :=
  Set.ext fun _ ↦ c.mem_normalizerSubgroup_iff

/-- Two normalized polynomials that differ by an element of the normalizer subgroup agree. -/
theorem IsNormalized.eq_one_of_isNormalized_scale {H : ExchangePolynomial 𝕂}
    (hH : c.IsNormalized H) {u : 𝕂ˣ} (hu : u ∈ c.normalizerSubgroup)
    (h : c.IsNormalized (H.scale u)) : u = 1 := by
  rwa [isNormalized_iff, c.normalizer_scale_of_mem hu, hH, mul_one, inv_eq_one] at h

section Transversal

variable (toScalar : 𝕂 →*₀ R) (G : Subgroup 𝕂ˣ) (S : Set (ExchangePolynomial 𝕂))
  (hrev : ∀ ⦃H⦄, H ∈ S → H.reverse ∈ S)
  (htrans : ∀ H : ExchangePolynomial 𝕂, ∃! u : G, H.scale u.val ∈ S)

/-- Construct a coefficient system from a scalar map, a subgroup `G ≤ 𝕂ˣ`, and a reversal-stable
transversal `S` of the `G`-scaling orbits on `ExchangePolynomial 𝕂`. -/
noncomputable def ofTransversal : CoefficientSystem 𝕂 R where
  toScalar := toScalar
  normalizer H := ((htrans H).choose : 𝕂ˣ)
  normalizer_reverse H := congrArg Subtype.val ((htrans H.reverse).choose_spec.2
    (htrans H).choose (cast (congrArg (· ∈ S) (H.reverse_scale _)) <|
      hrev (htrans H).choose_spec.1)).symm
  normalizer_scale H H' := by
    rw [← (htrans (H.scale (htrans H').choose.val)).choose_spec.2
      ((htrans H).choose * (htrans H').choose⁻¹) (by simpa using (htrans H).choose_spec.1)]
    simp

@[simp]
theorem ofTransversal_toScalar :
    (ofTransversal toScalar G S hrev htrans).toScalar = toScalar := (rfl)

theorem ofTransversal_normalizer (H : ExchangePolynomial 𝕂) :
    (ofTransversal toScalar G S hrev htrans).normalizer H = ((htrans H).choose : 𝕂ˣ) := (rfl)

theorem ofTransversal_normalizer_mem (H : ExchangePolynomial 𝕂) :
    (ofTransversal toScalar G S hrev htrans).normalizer H ∈ G :=
  ((htrans H).choose).prop

theorem ofTransversal_normalizer_eq_iff {H : ExchangePolynomial 𝕂} {u : 𝕂ˣ} :
    (ofTransversal toScalar G S hrev htrans).normalizer H = u ↔ u ∈ G ∧ H.scale u ∈ S := by
  refine ⟨?_, fun ⟨huG, huS⟩ ↦ congrArg Subtype.val ((htrans H).choose_spec.2 ⟨u, huG⟩ huS).symm⟩
  rintro rfl; exact ⟨((htrans H).choose).prop, (htrans H).choose_spec.1⟩

@[simp]
theorem isNormalized_ofTransversal_iff {H : ExchangePolynomial 𝕂} :
    (ofTransversal toScalar G S hrev htrans).IsNormalized H ↔ H ∈ S := by
  simp [isNormalized_iff, ofTransversal_normalizer_eq_iff]

@[simp]
theorem normalizerSubgroup_ofTransversal :
    (ofTransversal toScalar G S hrev htrans).normalizerSubgroup = G := by
  let c := ofTransversal toScalar G S hrev htrans
  ext u
  refine c.mem_normalizerSubgroup_iff.trans ⟨?_, fun hu ↦ ⟨(c.normalize .binary).scale u⁻¹, ?_⟩⟩
  · rintro ⟨H, rfl⟩; exact ofTransversal_normalizer_mem toScalar G S hrev htrans H
  · refine (ofTransversal_normalizer_eq_iff _ _ _ _ _).mpr ⟨hu, ?_⟩
    simpa using (isNormalized_ofTransversal_iff _ _ _ _ _).mp (c.isNormalized_normalize .binary)

end Transversal

/-- A coefficient system is uniquely recovered from its scalar map, its normalizer subgroup, and
its set of normalized polynomials. -/
theorem ofTransversal_eq_self :
    ofTransversal c.toScalar c.normalizerSubgroup {H | c.IsNormalized H}
        (fun _ h ↦ h.reverse) c.existsUnique_mem_normalizerSubgroup_isNormalized_scale = c := by
  ext : 1; · rfl
  exact funext fun H ↦ (ofTransversal_normalizer_eq_iff _ _ _ _ _).mpr
    ⟨c.normalizer_mem_normalizerSubgroup H, c.isNormalized_normalize H⟩

/-- Two coefficient systems with the same scalar map, the same normalizer subgroup and the same
normalized polynomials are equal. -/
theorem ext_of_isNormalized {c c' : CoefficientSystem 𝕂 R} (hφ : c.toScalar = c'.toScalar)
    (hG : c.normalizerSubgroup = c'.normalizerSubgroup)
    (hN : ∀ H, c.IsNormalized H ↔ c'.IsNormalized H) : c = c' := by
  rw [← c.ofTransversal_eq_self, ← c'.ofTransversal_eq_self]
  congr! -closePre -closePost 1
  · exact hφ
  · exact hG
  · exact Set.ext hN

end General

/-! ### The scalar system -/

/-- The *scalar coefficient system* on `R`: coefficients live directly in `R`, `toScalar = id`, and
`normalizer = 1`. -/
def trivial (R : Type*) [CommSemiring R] : CoefficientSystem R R where
  toScalar := MonoidWithZeroHom.id R
  normalizer _ := 1
  normalizer_reverse _ := rfl
  normalizer_scale _ _ := one_mul 1

section Trivial

variable {R : Type*} [CommSemiring R]

@[simp] theorem trivial_toScalar : (trivial R).toScalar = MonoidWithZeroHom.id R := (rfl)

@[simp]
theorem trivial_normalizer (H : ExchangePolynomial R) : (trivial R).normalizer H = 1 := (rfl)

@[simp]
theorem trivial_normalize (H : ExchangePolynomial R) : (trivial R).normalize H = H := H.scale_one

@[simp]
theorem isNormalized_trivial (H : ExchangePolynomial R) : (trivial R).IsNormalized H := (rfl)

@[simp]
theorem normalizerSubgroup_trivial : (trivial R).normalizerSubgroup = ⊥ :=
  Subgroup.closure_eq_bot_iff.mpr (by rintro _ ⟨_, rfl⟩; rfl)

end Trivial

/-! ### Normalized systems from zero-sum-free semifields -/

section Semifield

variable {F : Type*} [Semifield F] [Subsingleton (AddUnits F)] {R : Type*} [CommSemiring R]

private theorem mk0_sum_scale_inv (u : Fˣ) (H : ExchangePolynomial F) :
    (Units.mk0 (∑ l ∈ Finset.range ((H.scale u).degree + 1), (H.scale u).coeff l)
        (H.scale u).sum_coeff_ne_zero)⁻¹ =
      u⁻¹ * (Units.mk0 (∑ l ∈ Finset.range (H.degree + 1), H.coeff l) H.sum_coeff_ne_zero)⁻¹ := by
  ext
  simp [← Finset.mul_sum, mul_comm]

/-- The *normalized coefficient system* of a zero-sum-free semifield `F` along `φ : F →*₀ R`, with
normalizer `ν(H) = (∑_{l=0}^r h_l)⁻¹` formed in `F` before `φ` is applied. -/
noncomputable def ofSemifield (φ : F →*₀ R) : CoefficientSystem F R where
  toScalar := φ
  normalizer H := (Units.mk0 (∑ l ∈ Finset.range (H.degree + 1), H.coeff l) H.sum_coeff_ne_zero)⁻¹
  normalizer_reverse H := inv_inj.mpr <| Units.ext <| by
    rw [Units.val_mk0, Units.val_mk0, H.degree_reverse]
    exact H.sum_reverse_coeff fun x ↦ x
  normalizer_scale H H' := by rw [mk0_sum_scale_inv]; simp

@[simp] theorem ofSemifield_toScalar (φ : F →*₀ R) : (ofSemifield φ).toScalar = φ := (rfl)

@[simp]
theorem val_ofSemifield_normalizer (φ : F →*₀ R) (H : ExchangePolynomial F) :
    (((ofSemifield φ).normalizer H : Fˣ) : F) =
      (∑ l ∈ Finset.range (H.degree + 1), H.coeff l)⁻¹ := by
  simp [ofSemifield]

@[simp]
theorem ofSemifield_normalizer_scale (φ : F →*₀ R) (u : Fˣ) (H : ExchangePolynomial F) :
    (ofSemifield φ).normalizer (H.scale u) = u⁻¹ * (ofSemifield φ).normalizer H :=
  mk0_sum_scale_inv u H

@[simp]
theorem isNormalized_ofSemifield_iff (φ : F →*₀ R) {H : ExchangePolynomial F} :
    (ofSemifield φ).IsNormalized H ↔ ∑ l ∈ Finset.range (H.degree + 1), H.coeff l = 1 := by
  rw [isNormalized_iff, Units.ext_iff, val_ofSemifield_normalizer, Units.val_one, inv_eq_one]

@[simp]
theorem normalizerSubgroup_ofSemifield (φ : F →*₀ R) : (ofSemifield φ).normalizerSubgroup = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ (ofSemifield φ).mem_normalizerSubgroup_iff.mpr
    ⟨((ofSemifield φ).normalize ExchangePolynomial.binary).scale u⁻¹, by simp⟩

@[simp]
theorem ofSemifield_normalize_scale (φ : F →*₀ R) (u : Fˣ) (H : ExchangePolynomial F) :
    (ofSemifield φ).normalize (H.scale u) = (ofSemifield φ).normalize H :=
  (ofSemifield φ).normalize_scale_of_mem (by simp) H

end Semifield

/-! ### Checks -/

noncomputable example : CoefficientSystem ℚ≥0 ℚ := ofSemifield NNRat.coeHom.toMonoidWithZeroHom

/-- Over `ℚ≥0`, normalizing by `h_0⁻¹` violates reversal invariance on `1 + 2T`. -/
example : ¬ ∀ H : ExchangePolynomial ℚ≥0, H.reverse.constantUnit⁻¹ = H.constantUnit⁻¹ := by
  intro h
  simpa using congrArg Units.val (inv_inj.mp (h (.binomial (Units.mk0 (2 : ℚ≥0) (by simp)))))

/-- Over `ℚ≥0`, the constant map `ν(H) = 2` violates `ν(ν(H') H) * ν(H') = ν(H)`. -/
example :
    let u : ℚ≥0ˣ := Units.mk0 (2 : ℚ≥0) (by simp)
    u * u ≠ u := by
  intro u h
  simp [u, Units.ext_iff] at h

end CoefficientSystem

end TauCeti
