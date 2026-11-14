/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic

/-!
# Homomorphisms of coefficient systems

A homomorphism `c.Hom c'` between coefficient systems over a common scalar semiring `R` is a
morphism of monoids with zero `ψ : 𝕂 →*₀ 𝕂'` compatible with the scalar maps (`φ' ∘ ψ = φ`) and
intertwining the normalizers (`ν'(H.map ψ) = ψ(ν(H))`). Because such morphisms commute with
normalization, they transport exchange data, normalized states, and mutations without changing the
realized scalar quantities in `R`.

## Main definitions

* `TauCeti.CoefficientSystem.Hom c c'`: bundled homomorphisms between coefficient systems over `R`,
  equipped with `FunLike` and `MonoidWithZeroHomClass` instances.
* `TauCeti.CoefficientSystem.Hom.id` and `TauCeti.CoefficientSystem.Hom.comp`: identity and
  composition of homomorphisms.
* `TauCeti.CoefficientSystem.Hom.toTrivial`: canonical morphism into `CoefficientSystem.trivial R`
  when `toScalar` trivializes every normalizer value.
* `TauCeti.CoefficientSystem.Hom.ofSemifield`: functoriality of `CoefficientSystem.ofSemifield`
  along semiring homomorphisms between zero-sum-free semifields.

## Main results

* `TauCeti.CoefficientSystem.Hom.map_normalize` and `TauCeti.CoefficientSystem.IsNormalized.map`:
  homomorphisms of coefficient systems commute with polynomial normalization and preserve
  normalized polynomials.
-/

public section

namespace TauCeti

namespace CoefficientSystem

/-- A homomorphism of coefficient systems over a common scalar semiring `R`: a morphism of monoids
with zero `ψ : 𝕂 →*₀ 𝕂'` commuting with the scalar maps into `R` and intertwining the
normalizers. -/
structure Hom {𝕂 𝕂' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
    {R : Type*} [CommSemiring R] (c : CoefficientSystem 𝕂 R) (c' : CoefficientSystem 𝕂' R)
    extends 𝕂 →*₀ 𝕂' where
  /-- Compatibility with the scalar maps into `R`. -/
  toScalar_comp : c'.toScalar.comp toMonoidWithZeroHom = c.toScalar
  /-- The underlying map intertwines the normalizers of exchange polynomials. -/
  map_normalizer : ∀ H : ExchangePolynomial 𝕂,
    c'.normalizer (H.map toMonoidWithZeroHom) =
      Units.map toMonoidWithZeroHom.toMonoidHom (c.normalizer H)

/-- Reinterpret a homomorphism of coefficient systems as a morphism of monoids with zero. -/
add_decl_doc Hom.toMonoidWithZeroHom

attribute [simp] Hom.map_normalizer

namespace Hom

section General

variable {𝕂 𝕂' 𝕂'' 𝕂''' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] [CommMonoidWithZero 𝕂''']
  {R : Type*} [CommSemiring R]
  {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
  {c'' : CoefficientSystem 𝕂'' R} {c''' : CoefficientSystem 𝕂''' R}

instance : FunLike (c.Hom c') 𝕂 𝕂' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := g
    congr

instance : MonoidWithZeroHomClass (c.Hom c') 𝕂 𝕂' where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'

@[ext]
theorem ext {f g : c.Hom c'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_toMonoidWithZeroHom (f : c.Hom c') : ⇑f.toMonoidWithZeroHom = f :=
  (rfl)

@[simp]
theorem coe_mk (f : 𝕂 →*₀ 𝕂') (h₁ : c'.toScalar.comp f = c.toScalar)
    (h₂ : ∀ H : ExchangePolynomial 𝕂,
      c'.normalizer (H.map f) = Units.map f.toMonoidHom (c.normalizer H)) :
    ⇑(Hom.mk f h₁ h₂) = f :=
  (rfl)

@[simp]
theorem toScalar_apply (f : c.Hom c') (x : 𝕂) : c'.toScalar (f x) = c.toScalar x :=
  DFunLike.congr_fun f.toScalar_comp x

/-- Homomorphisms of coefficient systems commute with polynomial normalization. -/
@[simp]
theorem map_normalize (f : c.Hom c') (H : ExchangePolynomial 𝕂) :
    (c.normalize H).map f.toMonoidWithZeroHom = c'.normalize (H.map f.toMonoidWithZeroHom) := by
  simp [CoefficientSystem.normalize_def]

/-- Homomorphisms of coefficient systems map the normalizer subgroup into that of the target. -/
theorem map_mem_normalizerSubgroup (f : c.Hom c') {u : 𝕂ˣ} (hu : u ∈ c.normalizerSubgroup) :
    Units.map f.toMonoidWithZeroHom.toMonoidHom u ∈ c'.normalizerSubgroup := by
  rw [c.normalizerSubgroup_def] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨H, rfl⟩ := hx
    rw [← f.map_normalizer H]
    exact c'.normalizer_mem_normalizerSubgroup _
  | one => simp
  | mul _ _ _ _ ihx ihy => simpa only [map_mul] using mul_mem ihx ihy
  | inv _ _ ihx => simpa only [map_inv] using inv_mem ihx

variable (c) in
/-- The identity homomorphism of a coefficient system. -/
protected def id : c.Hom c where
  toMonoidWithZeroHom := MonoidWithZeroHom.id 𝕂
  toScalar_comp := MonoidWithZeroHom.comp_id c.toScalar
  map_normalizer H := by
    ext
    simp

@[simp]
theorem coe_id : ⇑(Hom.id c) = _root_.id :=
  (rfl)

@[simp]
theorem toMonoidWithZeroHom_id : (Hom.id c).toMonoidWithZeroHom = MonoidWithZeroHom.id 𝕂 :=
  (rfl)

theorem id_apply (x : 𝕂) : Hom.id c x = x :=
  (rfl)

/-- Composition of homomorphisms of coefficient systems over `R`. -/
def comp (g : c'.Hom c'') (f : c.Hom c') : c.Hom c'' where
  toMonoidWithZeroHom := g.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom
  toScalar_comp := by
    rw [← MonoidWithZeroHom.comp_assoc, g.toScalar_comp, f.toScalar_comp]
  map_normalizer H := by
    rw [← ExchangePolynomial.map_map, g.map_normalizer, f.map_normalizer]
    ext
    simp

@[simp]
theorem coe_comp (g : c'.Hom c'') (f : c.Hom c') : ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem toMonoidWithZeroHom_comp (g : c'.Hom c'') (f : c.Hom c') :
    (g.comp f).toMonoidWithZeroHom = g.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom :=
  (rfl)

theorem comp_apply (g : c'.Hom c'') (f : c.Hom c') (x : 𝕂) : g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : c.Hom c') : f.comp (Hom.id c) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem id_comp (f : c.Hom c') : (Hom.id c').comp f = f :=
  ext fun _ ↦ rfl

theorem comp_assoc (h : c''.Hom c''') (g : c'.Hom c'') (f : c.Hom c') :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ ↦ rfl

/-- When `c.toScalar` sends every normalizer unit to `1`, `c.toScalar` defines a homomorphism from
`c` into the scalar system `CoefficientSystem.trivial R`. -/
def toTrivial (c : CoefficientSystem 𝕂 R)
    (h : ∀ H, Units.map c.toScalar.toMonoidHom (c.normalizer H) = 1) :
    c.Hom (CoefficientSystem.trivial R) where
  toMonoidWithZeroHom := c.toScalar
  toScalar_comp := by simp
  map_normalizer H := by simp [h H]

@[simp]
theorem toMonoidWithZeroHom_toTrivial (c : CoefficientSystem 𝕂 R)
    (h : ∀ H, Units.map c.toScalar.toMonoidHom (c.normalizer H) = 1) :
    (toTrivial c h).toMonoidWithZeroHom = c.toScalar :=
  (rfl)

@[simp]
theorem coe_toTrivial (c : CoefficientSystem 𝕂 R)
    (h : ∀ H, Units.map c.toScalar.toMonoidHom (c.normalizer H) = 1) :
    ⇑(toTrivial c h) = c.toScalar :=
  (rfl)

end General

section Semifield

variable {F F' : Type*} [Semifield F] [Subsingleton (AddUnits F)]
  [Semifield F'] [Subsingleton (AddUnits F')]
  {R : Type*} [CommSemiring R] {φ : F →*₀ R} {φ' : F' →*₀ R}

/-- An addition-preserving homomorphism `ψ : F →+* F'` between zero-sum-free semifields compatible
with the scalar maps induces a homomorphism between their normalized coefficient systems. -/
noncomputable def ofSemifield (ψ : F →+* F') (hφ : φ'.comp ψ.toMonoidWithZeroHom = φ) :
    (CoefficientSystem.ofSemifield φ).Hom (CoefficientSystem.ofSemifield φ') where
  toMonoidWithZeroHom := ψ.toMonoidWithZeroHom
  toScalar_comp := by simpa using hφ
  map_normalizer H := by
    ext
    rw [val_ofSemifield_normalizer, Units.coe_map, val_ofSemifield_normalizer,
      H.sum_map_coeff ψ.toMonoidWithZeroHom (fun x ↦ x)]
    have hinv : (ψ (∑ l, H.coeff l))⁻¹ = ψ (∑ l, H.coeff l)⁻¹ :=
      inv_eq_of_mul_eq_one_right <| by
        rw [← map_mul, mul_inv_cancel₀ (sum_coeff_ne_zero H), map_one]
    simpa [← map_sum] using hinv

@[simp]
theorem toMonoidWithZeroHom_ofSemifield (ψ : F →+* F')
    (hφ : φ'.comp ψ.toMonoidWithZeroHom = φ) :
    (ofSemifield ψ hφ).toMonoidWithZeroHom = ψ.toMonoidWithZeroHom :=
  (rfl)

@[simp]
theorem coe_ofSemifield (ψ : F →+* F') (hφ : φ'.comp ψ.toMonoidWithZeroHom = φ) :
    ⇑(ofSemifield ψ hφ) = ψ :=
  (rfl)

end Semifield

end Hom

protected theorem IsNormalized.map {𝕂 𝕂' R : Type*} [CommMonoidWithZero 𝕂]
    [CommMonoidWithZero 𝕂'] [CommSemiring R] {c : CoefficientSystem 𝕂 R}
    {c' : CoefficientSystem 𝕂' R} {H : ExchangePolynomial 𝕂} (h : c.IsNormalized H)
    (f : c.Hom c') : c'.IsNormalized (H.map f.toMonoidWithZeroHom) := by
  rw [c'.isNormalized_iff, f.map_normalizer, (c.isNormalized_iff).mp h, map_one]

end CoefficientSystem

end TauCeti
