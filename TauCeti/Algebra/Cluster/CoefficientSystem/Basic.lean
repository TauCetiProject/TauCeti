/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import TauCeti.Algebra.Cluster.ExchangePolynomial.Basic

/-!
# Coefficient systems

A coefficient system over a commutative semiring `R` says where the coefficients of exchange
polynomials live and how exchange polynomials are normalized. It consists of a commutative monoid
with zero `𝕂`, a map `𝕂 →*₀ R` that realizes coefficients as scalars (it need be neither additive
nor injective), and a *normalizer* `ν` assigning a unit `ν H ∈ 𝕂ˣ` to every exchange polynomial
`H` over `𝕂`, subject to

* `ν (H.reverse) = ν H`;
* `ν (ν H' • H) * ν H' = ν H` for all `H` and `H'`.

The normalized multiple of `H` is `N H = ν H • H` (`CoefficientSystem.normalize`), and `H` is
normalized when `ν H = 1`. Normalization is idempotent and commutes with reversal. The values of
`ν` form a subgroup `G_ν` of `𝕂ˣ` (`CoefficientSystem.normalizerSubgroup`), for which `ν` is
homogeneous of degree `-1`, and the normalized polynomials are a reversal-stable set of
representatives for the scaling action of `G_ν`. Conversely, a subgroup together with a
reversal-stable set of representatives for its scaling action determines a unique coefficient
system (`CoefficientSystem.ofRepresentatives`).

When a direction of a cluster seed is mutated, the exchange polynomials of the other directions
are dilated by units fixed by the propagation law; this prescribes them only up to a unit, and the
normalizer chooses the unit. The scalar system `CoefficientSystem.trivial R`, with `𝕂 = R` and
`ν = 1`, normalizes nothing: every exchange polynomial is normalized. Maps of coefficient systems
(`CoefficientSystem.Hom`) are multiplicative maps of coefficients compatible with the scalar maps
and the normalizers; they commute with normalization.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. IMRN 2014, §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti

open ExchangePolynomial

/-- A coefficient system over a commutative semiring `R`: coefficients in a commutative monoid
with zero `𝕂`, a multiplicative scalar map `𝕂 →*₀ R`, which need be neither additive nor
injective, and a normalizer that is invariant under reversal and homogeneous of degree `-1` for
its own values. -/
@[ext]
structure CoefficientSystem (𝕂 : Type*) [CommMonoidWithZero 𝕂] (R : Type*) [CommSemiring R] where
  /-- The realization of coefficients as scalars. -/
  toScalar : 𝕂 →*₀ R
  /-- The normalizer, a unit by which an exchange polynomial is multiplied to normalize it. -/
  normalizer : ExchangePolynomial 𝕂 → 𝕂ˣ
  normalizer_reverse : ∀ H, normalizer H.reverse = normalizer H
  normalizer_scale_normalizer_mul : ∀ H H',
    normalizer (H.scale (normalizer H')) * normalizer H' = normalizer H

namespace CoefficientSystem

attribute [simp] normalizer_reverse

variable {𝕂 𝕂' 𝕂'' 𝕂''' R : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] [CommMonoidWithZero 𝕂'''] [CommSemiring R]

section Normalize

variable (c : CoefficientSystem 𝕂 R)

/-- The normalized multiple `ν H • H` of an exchange polynomial. -/
def normalize (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 :=
  H.scale (c.normalizer H)

theorem normalize_def (H : ExchangePolynomial 𝕂) : c.normalize H = H.scale (c.normalizer H) :=
  (rfl)

@[simp] theorem degree_normalize (H : ExchangePolynomial 𝕂) :
    (c.normalize H).degree = H.degree := by
  simp [normalize_def]

@[simp] theorem coeff_normalize (H : ExchangePolynomial 𝕂) (i : ℕ) :
    (c.normalize H).coeff i = c.normalizer H * H.coeff i := by
  simp [normalize_def]

/-- An exchange polynomial is normalized when its normalizer is one. -/
def IsNormalized (H : ExchangePolynomial 𝕂) : Prop :=
  c.normalizer H = 1

theorem isNormalized_iff (H : ExchangePolynomial 𝕂) : c.IsNormalized H ↔ c.normalizer H = 1 :=
  Iff.rfl

/-- Scaling by a value of the normalizer divides the normalizer by that value. -/
theorem normalizer_scale_normalizer (H H' : ExchangePolynomial 𝕂) :
    c.normalizer (H.scale (c.normalizer H')) = c.normalizer H * (c.normalizer H')⁻¹ :=
  eq_mul_inv_of_mul_eq (c.normalizer_scale_normalizer_mul H H')

/-- Scaling by the inverse of a value of the normalizer multiplies the normalizer by that
value. -/
theorem normalizer_scale_inv_normalizer (H H' : ExchangePolynomial 𝕂) :
    c.normalizer (H.scale (c.normalizer H')⁻¹) = c.normalizer H * c.normalizer H' := by
  have h := c.normalizer_scale_normalizer_mul (H.scale (c.normalizer H')⁻¹) H'
  rw [scale_scale, mul_inv_cancel, scale_one] at h
  exact h.symm

/-- A normalized multiple is normalized. -/
@[simp] theorem normalizer_normalize (H : ExchangePolynomial 𝕂) :
    c.normalizer (c.normalize H) = 1 := by
  rw [normalize_def, normalizer_scale_normalizer, mul_inv_cancel]

theorem isNormalized_normalize (H : ExchangePolynomial 𝕂) : c.IsNormalized (c.normalize H) :=
  c.normalizer_normalize H

/-- Normalization is idempotent. -/
@[simp] theorem normalize_normalize (H : ExchangePolynomial 𝕂) :
    c.normalize (c.normalize H) = c.normalize H := by
  rw [normalize_def (H := c.normalize H), normalizer_normalize, scale_one]

theorem isNormalized_iff_normalize_eq (H : ExchangePolynomial 𝕂) :
    c.IsNormalized H ↔ c.normalize H = H := by
  rw [normalize_def, scale_eq_self, isNormalized_iff]

theorem IsNormalized.normalize_eq {c : CoefficientSystem 𝕂 R} {H : ExchangePolynomial 𝕂}
    (hH : c.IsNormalized H) : c.normalize H = H :=
  (c.isNormalized_iff_normalize_eq H).mp hH

/-- The normalized polynomials are exactly the normalized multiples. -/
theorem isNormalized_iff_exists_normalize_eq (H : ExchangePolynomial 𝕂) :
    c.IsNormalized H ↔ ∃ G, c.normalize G = H :=
  ⟨fun hH ↦ ⟨H, hH.normalize_eq⟩, fun ⟨G, hG⟩ ↦ hG ▸ c.isNormalized_normalize G⟩

/-- Reversal preserves normalized polynomials. -/
@[simp] theorem isNormalized_reverse_iff (H : ExchangePolynomial 𝕂) :
    c.IsNormalized H.reverse ↔ c.IsNormalized H := by
  simp [isNormalized_iff]

/-- Normalization commutes with reversal. -/
@[simp] theorem normalize_reverse (H : ExchangePolynomial 𝕂) :
    c.normalize H.reverse = (c.normalize H).reverse := by
  simp [normalize_def]

end Normalize

/-! ### The subgroup of normalizer values -/

section Subgroup

variable (c : CoefficientSystem 𝕂 R)

/-- The values of the normalizer, which form a subgroup `G_ν` of the units of the coefficients:
the normalizer of a normalized polynomial scaled by a value `e` is `e⁻¹`. -/
def normalizerSubgroup : Subgroup 𝕂ˣ where
  carrier := Set.range c.normalizer
  one_mem' := ⟨c.normalize binary, c.normalizer_normalize binary⟩
  mul_mem' := by
    rintro _ _ ⟨H, rfl⟩ ⟨H', rfl⟩
    refine ⟨((c.normalize binary).scale (c.normalizer H)⁻¹).scale (c.normalizer H')⁻¹, ?_⟩
    rw [normalizer_scale_inv_normalizer, normalizer_scale_inv_normalizer, normalizer_normalize,
      one_mul]
  inv_mem' := by
    rintro _ ⟨H, rfl⟩
    exact ⟨(c.normalize binary).scale (c.normalizer H), by
      rw [normalizer_scale_normalizer, normalizer_normalize, one_mul]⟩

theorem mem_normalizerSubgroup {e : 𝕂ˣ} :
    e ∈ c.normalizerSubgroup ↔ ∃ H, c.normalizer H = e :=
  Iff.rfl

@[simp] theorem coe_normalizerSubgroup :
    (c.normalizerSubgroup : Set 𝕂ˣ) = Set.range c.normalizer :=
  (rfl)

@[simp] theorem normalizer_mem_normalizerSubgroup (H : ExchangePolynomial 𝕂) :
    c.normalizer H ∈ c.normalizerSubgroup :=
  ⟨H, rfl⟩

/-- The subgroup generated by the normalizer values consists of those values. -/
theorem closure_range_normalizer :
    Subgroup.closure (Set.range c.normalizer) = c.normalizerSubgroup := by
  rw [← coe_normalizerSubgroup, Subgroup.closure_eq]

/-- The normalizer is homogeneous of degree `-1` for the subgroup of its values. -/
theorem normalizer_scale {e : 𝕂ˣ} (he : e ∈ c.normalizerSubgroup) (H : ExchangePolynomial 𝕂) :
    c.normalizer (H.scale e) = e⁻¹ * c.normalizer H := by
  obtain ⟨H', rfl⟩ := he
  rw [normalizer_scale_normalizer, mul_comm]

/-- Scaling by an element of the normalizer subgroup does not change the normalized multiple. -/
theorem normalize_scale {e : 𝕂ˣ} (he : e ∈ c.normalizerSubgroup)
    (H : ExchangePolynomial 𝕂) : c.normalize (H.scale e) = c.normalize H := by
  rw [normalize_def, normalizer_scale c he, scale_scale, mul_right_comm, inv_mul_cancel, one_mul,
    normalize_def]

/-- The normalized polynomials are a set of representatives for the scaling action of the
normalizer subgroup: every exchange polynomial has exactly one normalized multiple by an element
of that subgroup. -/
theorem existsUnique_isNormalized_scale (H : ExchangePolynomial 𝕂) :
    ∃! e : c.normalizerSubgroup, c.IsNormalized (H.scale e) := by
  refine ⟨⟨c.normalizer H, c.normalizer_mem_normalizerSubgroup H⟩,
    c.isNormalized_normalize H, ?_⟩
  rintro ⟨e, he⟩ h
  rw [isNormalized_iff, normalizer_scale c he, inv_mul_eq_one] at h
  exact Subtype.ext h

/-- Two normalized polynomials that differ by an element of the normalizer subgroup agree. -/
theorem IsNormalized.eq_one_of_isNormalized_scale {c : CoefficientSystem 𝕂 R}
    {H : ExchangePolynomial 𝕂} (hH : c.IsNormalized H) {e : 𝕂ˣ}
    (he : e ∈ c.normalizerSubgroup) (h : c.IsNormalized (H.scale e)) : e = 1 := by
  rw [isNormalized_iff, normalizer_scale c he, hH, mul_one, inv_eq_one] at h
  exact h

end Subgroup

/-! ### Coefficient systems from representatives -/

section OfRepresentatives

variable (φ : 𝕂 →*₀ R) (G : Subgroup 𝕂ˣ) (S : Set (ExchangePolynomial 𝕂))
  (hrev : ∀ H ∈ S, H.reverse ∈ S) (hrep : ∀ H : ExchangePolynomial 𝕂, ∃! e : G, H.scale ↑e ∈ S)

/-- The coefficient system with scalar map `φ` whose normalizer sends `H` to the unique element
`e` of the subgroup `G` with `e • H ∈ S`, for a reversal-stable set `S` of representatives for
the scaling action of `G`. -/
noncomputable def ofRepresentatives : CoefficientSystem 𝕂 R where
  toScalar := φ
  normalizer H := (hrep H).exists.choose
  normalizer_reverse H := by
    have hH := (hrep H).exists.choose_spec
    have h := (hrep H.reverse).unique (hrep H.reverse).exists.choose_spec
      (y₂ := (hrep H).exists.choose) (by rw [← reverse_scale]; exact hrev _ hH)
    exact congrArg Subtype.val h
  normalizer_scale_normalizer_mul H H' := by
    have hg := (hrep (H.scale (hrep H').exists.choose)).exists.choose_spec
    rw [scale_scale, ← Subgroup.coe_mul] at hg
    simpa using congrArg Subtype.val ((hrep H).unique hg (hrep H).exists.choose_spec)

variable {φ G S hrev hrep}

@[simp] theorem toScalar_ofRepresentatives :
    (ofRepresentatives φ G S hrev hrep).toScalar = φ :=
  (rfl)

theorem normalizer_ofRepresentatives_mem (H : ExchangePolynomial 𝕂) :
    (ofRepresentatives φ G S hrev hrep).normalizer H ∈ G :=
  (hrep H).exists.choose.2

/-- The normalizer of `ofRepresentatives` is characterized by the representatives. -/
theorem normalizer_ofRepresentatives_eq_iff (H : ExchangePolynomial 𝕂) {e : 𝕂ˣ} (he : e ∈ G) :
    (ofRepresentatives φ G S hrev hrep).normalizer H = e ↔ H.scale e ∈ S := by
  constructor
  · rintro rfl
    exact (hrep H).exists.choose_spec
  · intro h
    exact congrArg Subtype.val ((hrep H).unique (hrep H).exists.choose_spec (y₂ := ⟨e, he⟩) h)

/-- The normalized polynomials of `ofRepresentatives` are the representatives. -/
@[simp] theorem isNormalized_ofRepresentatives_iff (H : ExchangePolynomial 𝕂) :
    (ofRepresentatives φ G S hrev hrep).IsNormalized H ↔ H ∈ S := by
  rw [isNormalized_iff, normalizer_ofRepresentatives_eq_iff H G.one_mem, scale_one]

/-- The normalizer subgroup of `ofRepresentatives` is the given subgroup. -/
@[simp] theorem normalizerSubgroup_ofRepresentatives :
    (ofRepresentatives φ G S hrev hrep).normalizerSubgroup = G := by
  ext e
  refine ⟨fun ⟨H, hH⟩ ↦ hH ▸ normalizer_ofRepresentatives_mem H, fun he ↦ ?_⟩
  obtain ⟨⟨g, hg⟩, hgS, -⟩ := hrep binary
  refine ⟨(binary.scale g).scale e⁻¹, ?_⟩
  rw [normalizer_ofRepresentatives_eq_iff _ he, scale_scale, scale_scale, mul_inv_cancel, one_mul]
  exact hgS

end OfRepresentatives

/-- Every coefficient system is determined by its scalar map, its normalizer subgroup and its
normalized polynomials. -/
theorem ofRepresentatives_eq (c : CoefficientSystem 𝕂 R) :
    ofRepresentatives c.toScalar c.normalizerSubgroup {H | c.IsNormalized H}
      (fun H hH ↦ (c.isNormalized_reverse_iff H).mpr hH) c.existsUnique_isNormalized_scale = c := by
  ext H : 2
  · rfl
  · rw [normalizer_ofRepresentatives_eq_iff _ (c.normalizer_mem_normalizerSubgroup H)]
    exact c.isNormalized_normalize H

/-- Two coefficient systems with the same scalar map, the same normalizer subgroup and the same
normalized polynomials are equal. -/
theorem ext_of_isNormalized {c c' : CoefficientSystem 𝕂 R} (hφ : c.toScalar = c'.toScalar)
    (hG : c.normalizerSubgroup = c'.normalizerSubgroup)
    (hN : ∀ H, c.IsNormalized H ↔ c'.IsNormalized H) : c = c' := by
  rw [← c.ofRepresentatives_eq, ← c'.ofRepresentatives_eq]
  congr! -closePre -closePost 1
  · exact hφ
  · exact hG
  · exact Set.ext hN

/-! ### The scalar system -/

section Trivial

variable (R)

/-- The scalar coefficient system of `R`: coefficients are the scalars themselves and the
normalizer is `1`, so every exchange polynomial is normalized. -/
def trivial : CoefficientSystem R R where
  toScalar := MonoidWithZeroHom.id R
  normalizer _ := 1
  normalizer_reverse _ := rfl
  normalizer_scale_normalizer_mul _ _ := one_mul 1

@[simp] theorem toScalar_trivial : (trivial R).toScalar = MonoidWithZeroHom.id R := (rfl)

@[simp] theorem normalizer_trivial (H : ExchangePolynomial R) : (trivial R).normalizer H = 1 :=
  (rfl)

variable {R}

@[simp] theorem normalize_trivial (H : ExchangePolynomial R) : (trivial R).normalize H = H := by
  simp [normalize_def]

@[simp] theorem isNormalized_trivial (H : ExchangePolynomial R) : (trivial R).IsNormalized H :=
  normalizer_trivial R H

@[simp] theorem normalizerSubgroup_trivial : (trivial R).normalizerSubgroup = ⊥ := by
  ext e
  rw [Subgroup.mem_bot]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨binary, h.symm⟩⟩

end Trivial

/-! ### Maps of coefficient systems -/

/-- A map of coefficient systems over the same scalars: a multiplicative map of coefficients
preserving zero, compatible with the scalar maps and carrying normalizers to normalizers. -/
structure Hom (c : CoefficientSystem 𝕂 R) (c' : CoefficientSystem 𝕂' R) extends 𝕂 →*₀ 𝕂' where
  toScalar_comp : c'.toScalar.comp toMonoidWithZeroHom = c.toScalar
  normalizer_map : ∀ H, c'.normalizer (H.map toMonoidWithZeroHom) =
    Units.map toMonoidWithZeroHom.toMonoidHom (c.normalizer H)

namespace Hom

variable {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
  {c'' : CoefficientSystem 𝕂'' R} {c''' : CoefficientSystem 𝕂''' R}

instance : FunLike (Hom c c') 𝕂 𝕂' where
  coe f := f.toMonoidWithZeroHom
  coe_injective f g h := by
    obtain ⟨f, _, _⟩ := f
    obtain ⟨g, _, _⟩ := g
    congr
    exact DFunLike.coe_injective h

instance : MonoidWithZeroHomClass (Hom c c') 𝕂 𝕂' where
  map_mul f := f.toMonoidWithZeroHom.map_mul
  map_one f := f.toMonoidWithZeroHom.map_one
  map_zero f := f.toMonoidWithZeroHom.map_zero

@[simp] theorem coe_toMonoidWithZeroHom (f : Hom c c') : ⇑f.toMonoidWithZeroHom = f := (rfl)

@[ext] theorem ext {f g : Hom c c'} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- A map of coefficient systems commutes with the scalar maps. -/
@[simp] theorem toScalar_apply (f : Hom c c') (a : 𝕂) : c'.toScalar (f a) = c.toScalar a :=
  DFunLike.congr_fun f.toScalar_comp a

/-- A map of coefficient systems commutes with normalization. -/
@[simp] theorem map_normalize (f : Hom c c') (H : ExchangePolynomial 𝕂) :
    (c.normalize H).map f.toMonoidWithZeroHom = c'.normalize (H.map f.toMonoidWithZeroHom) := by
  rw [normalize_def, normalize_def, map_scale, f.normalizer_map]

/-- A map of coefficient systems carries normalized polynomials to normalized polynomials. -/
theorem isNormalized_map (f : Hom c c') {H : ExchangePolynomial 𝕂} (hH : c.IsNormalized H) :
    c'.IsNormalized (H.map f.toMonoidWithZeroHom) := by
  rw [isNormalized_iff, f.normalizer_map, (c.isNormalized_iff H).mp hH, map_one]

/-- A map of coefficient systems carries the normalizer subgroup into the normalizer subgroup. -/
theorem map_normalizerSubgroup_le (f : Hom c c') :
    Subgroup.map (Units.map f.toMonoidWithZeroHom.toMonoidHom) c.normalizerSubgroup ≤
      c'.normalizerSubgroup := by
  rintro _ ⟨_, ⟨H, rfl⟩, rfl⟩
  exact ⟨H.map f.toMonoidWithZeroHom, f.normalizer_map H⟩

variable (c) in
/-- The identity map of a coefficient system. -/
protected def id : Hom c c where
  toMonoidWithZeroHom := MonoidWithZeroHom.id 𝕂
  toScalar_comp := MonoidWithZeroHom.comp_id _
  normalizer_map H := by
    rw [map_id]
    ext
    simp

@[simp] theorem id_apply (a : 𝕂) : Hom.id c a = a := (rfl)

/-- The composite of two maps of coefficient systems. -/
def comp (g : Hom c' c'') (f : Hom c c') : Hom c c'' where
  toMonoidWithZeroHom := g.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom
  toScalar_comp := by
    rw [← MonoidWithZeroHom.comp_assoc, g.toScalar_comp, f.toScalar_comp]
  normalizer_map H := by
    rw [← map_map, g.normalizer_map, f.normalizer_map]
    ext
    simp

@[simp] theorem comp_apply (g : Hom c' c'') (f : Hom c c') (a : 𝕂) : g.comp f a = g (f a) :=
  (rfl)

@[simp] theorem comp_id (f : Hom c c') : f.comp (Hom.id c) = f := by
  ext
  rfl

@[simp] theorem id_comp (f : Hom c c') : (Hom.id c').comp f = f := by
  ext
  rfl

theorem comp_assoc (h : Hom c'' c''') (g : Hom c' c'') (f : Hom c c') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

variable (c) in
/-- When the scalar map sends every normalizer value to one, the scalar map is a map from `c` to
the scalar system: realizing the coefficients forgets the normalization. -/
def toTrivial (h : ∀ H, c.toScalar (c.normalizer H) = 1) : Hom c (trivial R) where
  toMonoidWithZeroHom := c.toScalar
  toScalar_comp := MonoidWithZeroHom.id_comp _
  normalizer_map H := Units.ext (by simp [h])

@[simp] theorem toTrivial_apply (h : ∀ H, c.toScalar (c.normalizer H) = 1) (a : 𝕂) :
    toTrivial c h a = c.toScalar a :=
  (rfl)

end Hom

end CoefficientSystem

end TauCeti
