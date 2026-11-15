/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic

/-!
# Homomorphisms of coefficient systems

A homomorphism between coefficient systems `c : CoefficientSystem 𝕂 R` and
`c' : CoefficientSystem 𝕂' R` over a common scalar semiring `R` is a monoid-with-zero homomorphism
`ψ : 𝕂 →*₀ 𝕂'` commuting with the scalar maps to `R` and intertwining the normalizers. Such maps
transport exchange polynomials, normalization, normalized exchange data, and mutation patterns from
`c` to `c'`.

## Main definitions

* `TauCeti.CoefficientSystemHom c c'`: bundled homomorphisms of coefficient systems over `R`,
  equipped with `FunLike` and `MonoidWithZeroHomClass` instances.
* `TauCeti.CoefficientSystemHom.id`: the identity homomorphism of a coefficient system.
* `TauCeti.CoefficientSystemHom.comp`: composition of homomorphisms of coefficient systems.
* `TauCeti.CoefficientSystemHom.toTrivial`: the canonical map from `c` to the scalar system
  `CoefficientSystem.trivial R` when `c.toScalar` sends every normalizer value to `1`.

## Main results

* `TauCeti.CoefficientSystemHom.map_normalize`: homomorphisms of coefficient systems commute with
  polynomial normalization.
* `TauCeti.CoefficientSystem.IsNormalized.map`: homomorphisms of coefficient systems preserve
  normalized exchange polynomials.
-/

public section

namespace TauCeti

/-- A homomorphism of coefficient systems over `R`: a morphism of monoids with zero `ψ : 𝕂 →*₀ 𝕂'`
commuting with the scalar maps to `R` and intertwining the normalizers. -/
structure CoefficientSystemHom {𝕂 𝕂' R : Type*}
    [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂'] [CommSemiring R]
    (c : CoefficientSystem 𝕂 R) (c' : CoefficientSystem 𝕂' R) extends 𝕂 →*₀ 𝕂' where
  /-- Composing `ψ` with the target scalar map gives the source scalar map. -/
  toScalar_comp : c'.toScalar.comp toMonoidWithZeroHom = c.toScalar
  /-- Pushing an exchange polynomial forward along `ψ` maps its normalizer by `ψ`. -/
  normalizer_map : ∀ H : ExchangePolynomial 𝕂,
    c'.normalizer (H.map toMonoidWithZeroHom) =
      Units.map toMonoidWithZeroHom.toMonoidHom (c.normalizer H)

/-- Reinterpret a homomorphism of coefficient systems as a monoid-with-zero homomorphism. -/
add_decl_doc CoefficientSystemHom.toMonoidWithZeroHom

namespace CoefficientSystemHom

variable {𝕂 𝕂' 𝕂'' 𝕂''' R : Type*}
  [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] [CommMonoidWithZero 𝕂'''] [CommSemiring R]
  {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
  {c'' : CoefficientSystem 𝕂'' R} {c''' : CoefficientSystem 𝕂''' R}

instance : FunLike (CoefficientSystemHom c c') 𝕂 𝕂' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _, _⟩, _, _⟩ := g
    congr

instance : MonoidWithZeroHomClass (CoefficientSystemHom c c') 𝕂 𝕂' where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

@[ext]
theorem ext {f g : CoefficientSystemHom c c'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_mk (f : 𝕂 →*₀ 𝕂') (h₁ : c'.toScalar.comp f = c.toScalar)
    (h₂ : ∀ H : ExchangePolynomial 𝕂,
      c'.normalizer (H.map f) = Units.map f.toMonoidHom (c.normalizer H)) :
    ⇑(CoefficientSystemHom.mk f h₁ h₂) = f :=
  (rfl)

@[simp]
theorem coe_toMonoidWithZeroHom (f : CoefficientSystemHom c c') : ⇑f.toMonoidWithZeroHom = f :=
  (rfl)

/-- Applying `f` followed by the target scalar map equals the source scalar map. -/
@[simp]
theorem toScalar_apply (f : CoefficientSystemHom c c') (x : 𝕂) :
    c'.toScalar (f x) = c.toScalar x :=
  DFunLike.congr_fun f.toScalar_comp x

/-- Pushing an exchange polynomial forward along `f` maps its normalizer by `f`. -/
@[simp]
theorem map_normalizer (f : CoefficientSystemHom c c') (H : ExchangePolynomial 𝕂) :
    c'.normalizer (H.map f) = Units.map (MonoidHom.ofClass f) (c.normalizer H) := by
  have hmap : H.map f = H.map f.toMonoidWithZeroHom := by
    refine ExchangePolynomial.ext (by simp) fun l ↦ ?_
    simp
  have hunits :
      Units.map (MonoidHom.ofClass f) (c.normalizer H) =
        Units.map f.toMonoidWithZeroHom.toMonoidHom (c.normalizer H) := by
    ext
    rfl
  rw [hmap, hunits, f.normalizer_map]

/-- Homomorphisms of coefficient systems commute with polynomial normalization. -/
@[simp]
theorem map_normalize (f : CoefficientSystemHom c c') (H : ExchangePolynomial 𝕂) :
    (c.normalize H).map f = c'.normalize (H.map f) := by
  rw [CoefficientSystem.normalize_def, CoefficientSystem.normalize_def,
    ExchangePolynomial.scale_map, map_normalizer]

/-- Homomorphisms of coefficient systems preserve normalized exchange polynomials. -/
theorem _root_.TauCeti.CoefficientSystem.IsNormalized.map {H : ExchangePolynomial 𝕂}
    (h : c.IsNormalized H) (f : CoefficientSystemHom c c') : c'.IsNormalized (H.map f) := by
  rw [CoefficientSystem.isNormalized_def, map_normalizer, h.normalizer_eq, map_one]

/-- Homomorphisms of coefficient systems preserve `CoefficientSystem.valueAtOne`. -/
@[simp]
theorem valueAtOne_map (f : CoefficientSystemHom c c') (H : ExchangePolynomial 𝕂) :
    c'.valueAtOne (H.map f) = c.valueAtOne H := by
  rw [CoefficientSystem.valueAtOne_def, CoefficientSystem.valueAtOne_def,
    ExchangePolynomial.sum_map]
  simp only [f.toScalar_apply]

variable (c) in
/-- The identity homomorphism of a coefficient system. -/
protected def id : CoefficientSystemHom c c where
  toMonoidWithZeroHom := MonoidWithZeroHom.id 𝕂
  toScalar_comp := c.toScalar.comp_id
  normalizer_map H := by
    rw [ExchangePolynomial.map_id]
    ext
    rfl

@[simp]
theorem coe_id : ⇑(CoefficientSystemHom.id c) = _root_.id :=
  (rfl)

theorem id_apply (x : 𝕂) : CoefficientSystemHom.id c x = x :=
  (rfl)

/-- The composition of two homomorphisms of coefficient systems over `R`. -/
def comp (g : CoefficientSystemHom c' c'') (f : CoefficientSystemHom c c') :
    CoefficientSystemHom c c'' where
  toMonoidWithZeroHom := g.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom
  toScalar_comp := by
    rw [← MonoidWithZeroHom.comp_assoc, g.toScalar_comp, f.toScalar_comp]
  normalizer_map H := by
    have hmap :
        H.map (g.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom) =
          (H.map f).map g := by
      refine ExchangePolynomial.ext (by simp) fun l ↦ ?_
      simp
    rw [hmap, g.map_normalizer, f.map_normalizer]
    ext
    rfl

@[simp]
theorem coe_comp (g : CoefficientSystemHom c' c'') (f : CoefficientSystemHom c c') :
    ⇑(g.comp f) = g ∘ f :=
  (rfl)

theorem comp_apply (g : CoefficientSystemHom c' c'') (f : CoefficientSystemHom c c') (x : 𝕂) :
    g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : CoefficientSystemHom c c') : f.comp (CoefficientSystemHom.id c) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem id_comp (f : CoefficientSystemHom c c') : (CoefficientSystemHom.id c').comp f = f :=
  ext fun _ ↦ rfl

/-- Composition of homomorphisms of coefficient systems is associative. -/
theorem comp_assoc (h : CoefficientSystemHom c'' c''') (g : CoefficientSystemHom c' c'')
    (f : CoefficientSystemHom c c') : (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ ↦ rfl

/-- When `c.toScalar` sends every normalizer value to `1`, `c.toScalar` itself forms a homomorphism
from `c` into the scalar system `CoefficientSystem.trivial R`. -/
def toTrivial (c : CoefficientSystem 𝕂 R)
    (h : ∀ H, Units.map c.toScalar.toMonoidHom (c.normalizer H) = 1) :
    CoefficientSystemHom c (CoefficientSystem.trivial R) where
  toMonoidWithZeroHom := c.toScalar
  toScalar_comp := by simp
  normalizer_map H := by simp [h H]

@[simp]
theorem coe_toTrivial (c : CoefficientSystem 𝕂 R)
    (h : ∀ H, Units.map c.toScalar.toMonoidHom (c.normalizer H) = 1) :
    ⇑(toTrivial c h) = c.toScalar :=
  (rfl)

end CoefficientSystemHom

end TauCeti
