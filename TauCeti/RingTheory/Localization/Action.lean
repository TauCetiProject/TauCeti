/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.Algebra.Algebra.Basic

/-!
# Extending an action to a localization

Let a monoid `G` act on a commutative semiring `A` by ring endomorphisms, and let `B` be a
localization of `A` at a submonoid `S`. If every `g : G` sends the elements of `S` to elements that
become units in `B`, the action extends uniquely to an action on `B` by ring endomorphisms,
compatible with the localization map. This holds when `S` is `G`-stable; for a group `G`, `S` may
be the non-zero-divisors of `A`. The action of `g` is the universal property `IsLocalization.lift`
applied to `A → A → B`.

When `G` acts on the `R`-algebra `A` by `R`-algebra endomorphisms (`SMulCommClass G R A`), it fixes
the image in `A` of every submonoid `M` of `R`, and the action on the localization `M⁻¹A`
(`Localization (Algebra.algebraMapSubmonoid A M)`) is an instance, under which `G` acts on a
fraction `a / s` through its numerator.

## Main definitions

* `TauCeti.IsLocalization.localizationRingEnd B hU`: the action of `G` on a localization `B` of `A`
  at a submonoid `S`, given that `g • s` becomes a unit in `B` for every `g : G` and `s ∈ S`.
* `TauCeti.Localization.instMulSemiringActionLocalization`: for `[SMulCommClass G R A]` and a
  submonoid `M` of `R`, the instance `MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid
  A M))` given by `localizationRingEnd`.

## Main results

* `TauCeti.IsLocalization.localizationRingEnd_algebraMap` and
  `TauCeti.Localization.smul_algebraMap`: the localization map is `G`-equivariant.
* `TauCeti.IsLocalization.localizationRingEnd_unique`: an action on `B` by ring endomorphisms
  compatible with the localization map is `localizationRingEnd`.
* `TauCeti.IsLocalization.localizationRingEnd_mk'_spec`: `g • (a / s) = v` if and only if
  `g • a = (g • s) v` in `B`, and `TauCeti.IsLocalization.localizationRingEnd_mk'`:
  `g • (a / s) = (g • a) / (g • s)` when `g • s` is again a denominator.
* `TauCeti.Localization.smul_mk'`: `g • (a / s) = (g • a) / s` on `M⁻¹A`.
* `TauCeti.IsFractionRing.div_mem_fixedPoints_iff`: for any action on a fraction field `L` of a
  domain `B` extending the action on `B`, the fraction `b / c` is invariant if and only if
  `(g • b) * c = b * (g • c)` for all `g`.
-/

public section

namespace TauCeti.IsLocalization

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]

section Localization

variable {S : Submonoid A} (B : Type*) [CommSemiring B] [Algebra A B] [IsLocalization S B]

/-- The action of `G` on a localization `B` of `A` at a submonoid `S`, induced by its action on
`A`, when every `g • s` with `s ∈ S` becomes a unit in `B`: `g` acts by the ring endomorphism
`IsLocalization.lift` of `A → A → B`, the action of `g` followed by the localization map. -/
noncomputable def localizationRingEnd
    (hU : ∀ (g : G) (s : S), IsUnit (algebraMap A B (g • (s : A)))) : G →* B →+* B where
  -- The `show` states `hU g` in the form `IsLocalization.lift` takes, so that `simp` can use
  -- `IsLocalization.lift_eq`.
  toFun g := IsLocalization.lift (M := S)
    (g := (algebraMap A B).comp (MulSemiringAction.toRingHom G A g))
    (show ∀ s : S, IsUnit ((algebraMap A B).comp (MulSemiringAction.toRingHom G A g) s) from hU g)
  map_one' := IsLocalization.ringHom_ext S <| RingHom.ext fun a ↦ by simp
  map_mul' g h := IsLocalization.ringHom_ext S <| RingHom.ext fun a ↦ by simp [mul_smul]

variable (hU : ∀ (g : G) (s : S), IsUnit (algebraMap A B (g • (s : A))))

/-- `localizationRingEnd B hU g` extends the action of `g` on `A`. -/
@[simp]
theorem localizationRingEnd_algebraMap (g : G) (a : A) :
    localizationRingEnd B hU g (algebraMap A B a) = algebraMap A B (g • a) :=
  IsLocalization.lift_eq (hU g) a

/-- An action of `G` on `B` by ring endomorphisms extending the action on `A` is
`localizationRingEnd B hU`. -/
theorem localizationRingEnd_unique (ρ : G →* B →+* B)
    (hρ : ∀ (g : G) (a : A), ρ g (algebraMap A B a) = algebraMap A B (g • a)) :
    localizationRingEnd B hU = ρ :=
  MonoidHom.ext fun g ↦ IsLocalization.lift_unique (hU g) (hρ g)

/-- The image of a fraction `a / s` under `localizationRingEnd B hU g` is the element `v` of `B`
with `g • a = (g • s) v`. -/
theorem localizationRingEnd_mk'_spec (g : G) (a : A) (s : S) (v : B) :
    localizationRingEnd B hU g (IsLocalization.mk' B a s) = v ↔
      algebraMap A B (g • a) = algebraMap A B (g • (s : A)) * v :=
  IsLocalization.lift_mk'_spec (hU g) a v s

/-- `localizationRingEnd B hU g` acts on a fraction `a / s` by acting on numerator and denominator,
when `g • s` is again a denominator. -/
@[simp]
theorem localizationRingEnd_mk' (g : G) (a : A) (s : S) (hs : g • (s : A) ∈ S) :
    localizationRingEnd B hU g (IsLocalization.mk' B a s) =
      IsLocalization.mk' B (g • a) ⟨g • (s : A), hs⟩ :=
  (localizationRingEnd_mk'_spec B hU g a s _).mpr
    (IsLocalization.mk'_spec' B (g • a) ⟨g • s, hs⟩).symm

end Localization

variable {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The hypothesis of `localizationRingEnd` for a localization `B` of `A` at the image of a
submonoid `M` of `R`: `G` fixes the denominators, so they stay units in `B`. -/
theorem isUnit_algebraMap_smul (B : Type*) [CommSemiring B] [Algebra A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B] (g : G)
    (s : Algebra.algebraMapSubmonoid A M) : IsUnit (algebraMap A B (g • (s : A))) := by
  rw [Algebra.smul_eq_of_mem_algebraMapSubmonoid g s.property]
  exact IsLocalization.map_units B s

end TauCeti.IsLocalization

namespace TauCeti.Localization

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]
  {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The action of `G` on the localization `M⁻¹A` at the image of a submonoid `M` of `R`, where `G`
acts on the `R`-algebra `A` by `R`-algebra endomorphisms, given by `localizationRingEnd`. -/
noncomputable instance instMulSemiringActionLocalization :
    MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid A M)) :=
  MulSemiringAction.compHom _ <| IsLocalization.localizationRingEnd _ <|
    IsLocalization.isUnit_algebraMap_smul (A := A) (M := M)
      (Localization (Algebra.algebraMapSubmonoid A M))

end TauCeti.Localization

namespace TauCeti.IsLocalization

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]
  {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The action of `G` on `M⁻¹A` is `localizationRingEnd`. -/
@[simp]
theorem localizationRingEnd_apply
    (hU : ∀ (g : G) (s : Algebra.algebraMapSubmonoid A M),
      IsUnit (algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) (g • (s : A))))
    (g : G) (x : Localization (Algebra.algebraMapSubmonoid A M)) :
    localizationRingEnd _ hU g x = g • x :=
  (RingHom.smul_def (f := localizationRingEnd _ hU g) (a := x)).symm.trans
    (MulAction.compHom_smul_def _ g x).symm

end TauCeti.IsLocalization

namespace TauCeti.Localization

open TauCeti.IsLocalization

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]
  {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] {M : Submonoid R}

/-- The action of `G` on `M⁻¹A` extends the action on `A`. -/
@[simp]
theorem smul_algebraMap (g : G) (a : A) :
    g • algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) (g • a) := by
  rw [← localizationRingEnd_apply (isUnit_algebraMap_smul (A := A) (M := M) _)]
  exact localizationRingEnd_algebraMap _ _ g a

/-- The action of `G` on `M⁻¹A` on fractions: `g • (a / s) = (g • a) / s`, since the
denominator `s` is invariant. -/
@[simp]
theorem smul_mk' (g : G) (a : A) (s : Algebra.algebraMapSubmonoid A M) :
    g • _root_.IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A M)) a s =
      _root_.IsLocalization.mk' _ (g • a) s := by
  rw [← localizationRingEnd_apply (isUnit_algebraMap_smul (A := A) (M := M) _),
    localizationRingEnd_mk' _ _ g a s
      (Algebra.algebraMapSubmonoid_le_comap M (MulSemiringAction.toAlgHom R A g) s.property)]
  exact congrArg _ <| Subtype.ext <| Algebra.smul_eq_of_mem_algebraMapSubmonoid g s.property

end TauCeti.Localization

namespace TauCeti.IsFractionRing

variable {G B : Type*} [Monoid G] [CommRing B] [MulSemiringAction G B] (L : Type*) [Field L]
  [Algebra B L] [IsFractionRing B L] [MulSemiringAction G L] [SMulDistribClass G B L]

/-- For an action on a fraction field `L` of `B` extending the action on `B`, the fraction
`b / c` is invariant exactly when `(g • b) * c = b * (g • c)` for all `g`. -/
theorem div_mem_fixedPoints_iff (b : B) {c : B} (hc : c ≠ 0) :
    algebraMap B L b / algebraMap B L c ∈ MulAction.fixedPoints G L ↔
      ∀ g : G, (g • b) * c = b * (g • c) := by
  have hc' : algebraMap B L c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).2 hc
  refine forall_congr' fun g ↦ ?_
  have hgc : g • algebraMap B L c ≠ 0 := (map_ne_zero (MulSemiringAction.toRingHom G L g)).2 hc'
  rw [show g • (algebraMap B L b / algebraMap B L c) = g • algebraMap B L b / g • algebraMap B L c
      from map_div₀ (MulSemiringAction.toRingHom G L g) _ _, div_eq_div_iff hgc hc',
    ← algebraMap.smul', ← algebraMap.smul', ← map_mul, ← map_mul,
    (IsFractionRing.injective B L).eq_iff]

end TauCeti.IsFractionRing
