/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import TauCeti.AlgebraicGeometry.Frobenius.Basic
public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf

/-!
# The Frobenius endomorphism of `𝔾_a` over an `𝔽_p`-scheme

Let `p` be a prime and `S` a scheme in which `p` vanishes. For every `S`-scheme `T` the prime `p`
vanishes in `Γ(T, 𝒪_T)`, so the `p`-th power map `a ↦ a ^ p` is additive there, and it commutes
with the restriction maps since these are ring homomorphisms. It is therefore an endomorphism
`AlgebraicGeometry.Scheme.gaFrobenius` of the additive group `𝔾_a : T ↦ Γ(T, 𝒪_T)` on the big
fpqc site over `S`.

It is not linear over the big structure sheaf: an endomorphism of the unit module that is the
`p`-th power map on every test scheme would fix `a = a • 1` for every function `a`, so the `p`-th
power map would be the identity on every test scheme
(`AlgebraicGeometry.Scheme.pow_eq_self_of_unit_hom_app_eq_pow`). On `𝔸¹_{𝔽_p}` the coordinate `t`
has `t ^ p ≠ t`, so the Frobenius of `𝔾_a` does not lift to a morphism of modules over the big
structure sheaf (`TauCeti/Examples/AlgebraicGeometry/Sites/Big/Frobenius.lean`).

## Main declarations

* `AlgebraicGeometry.Scheme.gaFrobenius S hS`: the Frobenius endomorphism `a ↦ a ^ p` of `𝔾_a`.
* `AlgebraicGeometry.Scheme.pow_eq_self_of_unit_hom_app_eq_pow`: if an endomorphism of the unit
  module over the big structure sheaf is the `p`-th power map, then `a ^ p = a` for every function
  `a` on every `S`-scheme.
* `AlgebraicGeometry.Scheme.not_exists_unit_hom_app_eq_pow`: no such endomorphism exists as soon
  as some function on some `S`-scheme is not fixed by the `p`-th power map.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {p : ℕ} [Fact p.Prime]

/-- The **Frobenius endomorphism** `a ↦ a ^ p` of the additive group `𝔾_a : T ↦ Γ(T, 𝒪_T)` on the
big fpqc site over a scheme `S` in which the prime `p` vanishes. -/
noncomputable def gaFrobenius (hS : (p : Γ(S, ⊤)) = 0) : Ga S ⟶ Ga S where
  hom :=
    { app T := AddCommGrpCat.ofHom
        (TauCeti.powRingHom Γ(T.unop.left, ⊤) p
          (natCast_eq_zero_of_hom T.unop.hom hS)).toAddMonoidHom
      naturality T T' f := by
        ext (a : Γ(T.unop.left, ⊤))
        -- The restriction maps of `𝔾_a` are the ring homomorphisms `f.unop.left.appTop`.
        change TauCeti.powRingHom _ p (natCast_eq_zero_of_hom T'.unop.hom hS)
            (f.unop.left.appTop a) =
          f.unop.left.appTop (TauCeti.powRingHom _ p (natCast_eq_zero_of_hom T.unop.hom hS) a)
        rw [TauCeti.powRingHom_apply, TauCeti.powRingHom_apply, map_pow] }

/-- The Frobenius endomorphism of `𝔾_a` is the `p`-th power map on every test scheme. -/
@[simp]
lemma gaFrobenius_app_apply (hS : (p : Γ(S, ⊤)) = 0) (T : Over S) (a : Γ(T.left, ⊤)) :
    (gaFrobenius S hS).hom.app (op T) a = a ^ p :=
  TauCeti.powRingHom_apply _ a

variable {S}

omit [Fact p.Prime] in
/-- If an endomorphism `φ` of the unit module over the big structure sheaf of `S` is the `p`-th
power map on every test scheme, then the `p`-th power map is the identity on every test
scheme. -/
theorem pow_eq_self_of_unit_hom_app_eq_pow
    (φ : SheafOfModules.unit (bigRingCatSheaf S) ⟶ SheafOfModules.unit (bigRingCatSheaf S))
    (hφ : ∀ (T : Over S) (a : Γ(T.left, ⊤)), φ.val.app (op T) a = a ^ p)
    (T : Over S) (a : Γ(T.left, ⊤)) : a ^ p = a := by
  -- By definition, the sections of the unit module over `T` and its ring of scalars are both
  -- `Γ(T.left, ⊤)`, acting on itself by multiplication, so `φ` over `T` is a linear endomorphism
  -- of `Γ(T.left, ⊤)`.
  let ψ : Γ(T.left, ⊤) →ₗ[Γ(T.left, ⊤)] Γ(T.left, ⊤) := (φ.val.app (op T)).hom
  have hψ (b : Γ(T.left, ⊤)) : ψ b = b ^ p := hφ T b
  -- `a = a • 1` is sent to `a • ψ 1 = a • 1 ^ p = a`.
  have h := ψ.map_smul a 1
  rwa [smul_eq_mul, smul_eq_mul, mul_one, hψ, hψ, one_pow, mul_one] at h

omit [Fact p.Prime] in
/-- The Frobenius of `𝔾_a` does not lift to the unit module over the big structure sheaf: if some
function `a` on some `S`-scheme has `a ^ p ≠ a`, no endomorphism of the unit module is the `p`-th
power map on every test scheme. -/
theorem not_exists_unit_hom_app_eq_pow {T : Over S} {a : Γ(T.left, ⊤)} (ha : a ^ p ≠ a) :
    ¬ ∃ φ : SheafOfModules.unit (bigRingCatSheaf S) ⟶ SheafOfModules.unit (bigRingCatSheaf S),
      ∀ (T : Over S) (a : Γ(T.left, ⊤)), φ.val.app (op T) a = a ^ p :=
  fun ⟨φ, hφ⟩ ↦ ha (pow_eq_self_of_unit_hom_app_eq_pow φ hφ T a)

end AlgebraicGeometry.Scheme
