/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus

/-!
# The scheme of primitive `N`-torsion points

Let `E` be an elliptic curve over a scheme `S` and `N` a natural number. A point `y` of the
`N`-torsion `E[N]` with values in a scheme `Z` over `S` is **primitive** when none of the multiples
`y, 2y, …, (N - 1)y` of its image in `E` meets the zero section of `E` at any point of `Z`. For
`N ≠ 0` this says that `y` has **exact order `N` in every fibre**; for `N = 0` the condition is
vacuous, so every point of `E[0]` is primitive. This file constructs the open subscheme `E[N]^×` of
`E[N]` (`EllipticCurveGeom.primitiveTorsion`) whose points with values in `Z` are exactly the
primitive points of `E[N]` with values in `Z` (`EllipticCurveGeom.primitiveTorsionHomEquiv`).

The condition is pointwise on `Z`, so it is cut out of `E[N]` by the inclusion `ι : E[N] ⟶ E`,
viewed as a point of `E` with values in `E[N]`: `E[N]^×` is the complement in `E[N]` of the closed
sets on which one of the multiples `kι`, `0 < k < N`, meets the zero section
(`EllipticCurveGeom.mem_primitiveTorsionOpens_iff`). No hypothesis on `N` or on `S` is needed for
the construction; for `N = 0` it gives all of `E[0]`. When `N` is invertible on `S`, `E[N]` is
étale over `S`, and hence so is its open subscheme `E[N]^×`
(`EllipticCurveGeom.etale_primitiveTorsion_hom`).

For `N ≠ 0`, the primitive points of `E[N]` are the homomorphisms
`ℤ/Nℤ →* E(S)` injective on every fibre (`EllipticCurveGeom.isFiberwiseInjective_zmod_iff`). Over a
base on which `N` is invertible these are the naive `[Γ₁(N)]`-structures of Katz and Mazur, so
`E[N]^×` is the scheme representing naive `[Γ₁(N)]`-structures on base changes of `E`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.primitiveTorsionOpens E N`: the open subset of
  `E[N]` of primitive points, of exact order `N` in their fibre when `N ≠ 0`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.primitiveTorsion E N`: the open subscheme `E[N]^×`
  of `E[N]`, as a scheme over `S`, with its inclusion
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.primitiveTorsionι E N : E[N]^× ⟶ E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.primitiveTorsionHomEquiv E N Z`: the points of
  `E[N]^×` with values in `Z` are the primitive points of `E[N]` with values in `Z`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.left_apply_mem_primitiveTorsionOpens_iff`: a point
  of `E[N]` with values in `Z` lands in `E[N]^×` at a point `z` of `Z` exactly when none of the
  multiples `y, …, (N - 1)y` meets the zero section at `z`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_primitiveTorsion_hom`: if `N` is invertible
  on `S`, then `E[N]^×` is étale over `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and §3.7.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (N : ℕ)

/-- The open subset of the `N`-torsion `E[N]` of primitive points: the points `z` of `E[N]` at
which none of the multiples `kι`, `0 < k < N`, of the inclusion `ι : E[N] ⟶ E`, viewed as a point
of `E` with values in `E[N]`, meets the zero section. For `N ≠ 0` these are the points of exact
order `N` in their fibre; for `N = 0` the condition is vacuous and this is all of `E[0]`. -/
noncomputable def primitiveTorsionOpens : (E.torsion N).X.left.Opens where
  carrier := {z | ∀ k : ℕ, 0 < k → k < N →
    (E.torsionι N ^ k).left z ≠ E.zero ((E.torsion N).X.hom z)}
  is_open' := by
    have : {z | ∀ k : ℕ, 0 < k → k < N →
          (E.torsionι N ^ k).left z ≠ E.zero ((E.torsion N).X.hom z)} =
        ⋂ k ∈ Finset.Ioo 0 N,
          {z | (E.torsionι N ^ k).left z = E.zero ((E.torsion N).X.hom z)}ᶜ := by
      ext
      simp [and_imp]
    rw [this]
    exact isOpen_biInter_finset fun k _ ↦ (E.isClosed_setOf_left_apply_eq_zero _).isOpen_compl

/-- The defining property of `primitiveTorsionOpens E N`. -/
@[simp]
theorem mem_primitiveTorsionOpens_iff {z : (E.torsion N).X.left} :
    z ∈ E.primitiveTorsionOpens N ↔ ∀ k : ℕ, 0 < k → k < N →
      (E.torsionι N ^ k).left z ≠ E.zero ((E.torsion N).X.hom z) :=
  Iff.rfl

/-- **The scheme `E[N]^×` of primitive `N`-torsion points**: the open subscheme
`primitiveTorsionOpens E N` of the `N`-torsion `E[N]`, as a scheme over `S`. Its points with values
in a scheme `Z` over `S` are the primitive points of `E[N]` with values in `Z`
(`primitiveTorsionHomEquiv`), which for `N ≠ 0` are those of exact order `N` in every fibre. Its
underlying scheme is the open subscheme `primitiveTorsionOpens E N` of `E[N]`; it is reducible, so
that instances on open subschemes apply to it. -/
noncomputable abbrev primitiveTorsion : Over S :=
  Over.mk ((E.primitiveTorsionOpens N).ι ≫ (E.torsion N).X.hom)

/-- The inclusion `E[N]^× ⟶ E[N]`, an open immersion. -/
noncomputable def primitiveTorsionι : E.primitiveTorsion N ⟶ (E.torsion N).X :=
  Over.homMk (E.primitiveTorsionOpens N).ι

@[simp]
theorem primitiveTorsionι_left :
    (E.primitiveTorsionι N).left = (E.primitiveTorsionOpens N).ι :=
  (rfl)

/-- The inclusion `E[N]^× ⟶ E[N]` is an open immersion. -/
instance isOpenImmersion_primitiveTorsionι_left :
    IsOpenImmersion (E.primitiveTorsionι N).left := by
  rw [primitiveTorsionι_left]
  infer_instance

/-- The inclusion `E[N]^× ⟶ E[N]` is a monomorphism. -/
instance mono_primitiveTorsionι : Mono (E.primitiveTorsionι N) :=
  Over.mono_homMk _

variable {E N}

/-- **The points of `E[N]^×`, pointwise.** A point `y` of `E[N]` with values in a scheme `Z` over
`S` lands in `E[N]^×` at a point `z` of `Z` exactly when none of the multiples
`y, 2y, …, (N - 1)y` of its image in `E` meets the zero section at `z`. -/
theorem left_apply_mem_primitiveTorsionOpens_iff {Z : Over S} (y : Z ⟶ (E.torsion N).X)
    (z : Z.left) : y.left z ∈ E.primitiveTorsionOpens N ↔
      ∀ k : ℕ, 0 < k → k < N → ((y ≫ E.torsionι N) ^ k).left z ≠ E.zero (Z.hom z) := by
  have hw : y.left ≫ (E.torsion N).X.hom = Z.hom := Over.w y
  simp only [mem_primitiveTorsionOpens_iff, ← MonObj.comp_pow, Over.comp_left,
    Scheme.Hom.comp_apply, ← hw]

variable (E N) in
/-- **The points of `E[N]^×`.** The points of `E[N]^×` with values in a scheme `Z` over `S` are the
primitive points `y` of `E[N]` with values in `Z`: none of the multiples `y, 2y, …, (N - 1)y` of the
image of `y` in `E` meets the zero section at any point of `Z`. For `N ≠ 0` these are the points of
exact order `N` in every fibre. -/
noncomputable def primitiveTorsionHomEquiv (Z : Over S) :
    (Z ⟶ E.primitiveTorsion N) ≃ {y : Z ⟶ (E.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ z, ((y ≫ E.torsionι N) ^ k).left z ≠ E.zero (Z.hom z)} where
  toFun a := ⟨a ≫ E.primitiveTorsionι N, fun k hk hkN z ↦
    (left_apply_mem_primitiveTorsionOpens_iff _ z).mp (by
      rw [Over.comp_left, Scheme.Hom.comp_apply, primitiveTorsionι_left]
      -- `U.ι x` is `x.val` by `Scheme.Opens.ι_apply`, which `rw` cannot apply to this point of `U`
      exact (a.left z).2) k hk hkN⟩
  invFun y := Over.homMk (IsOpenImmersion.lift (E.primitiveTorsionOpens N).ι y.1.left (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (left_apply_mem_primitiveTorsionOpens_iff y.1 z).mpr fun k hk hkN ↦ y.2 k hk hkN z))
    ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y.1))
  left_inv a := (cancel_mono (E.primitiveTorsionι N)).mp <| by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv y := by
    ext1
    ext1
    exact IsOpenImmersion.lift_fac _ _ _

/-- The point of `E[N]` of a point `a` of `E[N]^×` is its image `a ≫ ι` under the inclusion. -/
@[simp]
theorem coe_primitiveTorsionHomEquiv_apply {Z : Over S} (a : Z ⟶ E.primitiveTorsion N) :
    (E.primitiveTorsionHomEquiv N Z a : Z ⟶ (E.torsion N).X) = a ≫ E.primitiveTorsionι N :=
  (rfl)

/-- The point of `E[N]^×` of a primitive point `y` of `E[N]` maps to `y`. -/
@[reassoc (attr := simp)]
theorem primitiveTorsionHomEquiv_symm_apply_comp {Z : Over S}
    (y : {y : Z ⟶ (E.torsion N).X //
      ∀ k : ℕ, 0 < k → k < N → ∀ z, ((y ≫ E.torsionι N) ^ k).left z ≠ E.zero (Z.hom z)}) :
    (E.primitiveTorsionHomEquiv N Z).symm y ≫ E.primitiveTorsionι N = y := by
  rw [← coe_primitiveTorsionHomEquiv_apply, Equiv.apply_symm_apply]

variable (E N) in
/-- **`E[N]^×` is étale where `N` is invertible.** If `N` is invertible in every residue field of
`S`, the scheme `E[N]^×` of primitive `N`-torsion points is étale over `S`, as an open subscheme of
the étale `S`-scheme `E[N]`. -/
theorem etale_primitiveTorsion_hom (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    Etale (E.primitiveTorsion N).hom := by
  have := E.etale_torsion_hom_of_forall_intCast_ne_zero (n := N) (by simpa using hN)
  exact inferInstanceAs (Etale ((E.primitiveTorsionOpens N).ι ≫ (E.torsion N).X.hom))

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
