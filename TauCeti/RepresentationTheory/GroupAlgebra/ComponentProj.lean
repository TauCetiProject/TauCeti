/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.MonoidAlgebra.TwistedProj
public import TauCeti.RepresentationTheory.GroupAlgebra.IdempotentEval

/-!
# Character idempotents and twisted component projections

Let `O` be a commutative ring, `G` a commutative group, `P, H ≤ G` complementary subgroups
(`P.IsComplement' H`), and `χ : H →* Oˣ` a character of `H` with embedded character idempotent
`e_χ ∈ O[G]`. This file connects `MonoidAlgebra.componentProj hPH χ : O[G] →ₐ[O] O[P]` with
`TauCeti.charIdempotent χ`:

* When `#H` is a unit in `O`, `componentProj hPH χ (e_χ) = 1`, and over a domain `O` it vanishes on
  `e_ω` for `ω ≠ χ`.
* Multiplying any `x ∈ O[G]` by `e_χ` agrees with multiplying its projection
  `componentProj hPH χ x` by `e_χ`
  (`MonoidAlgebra.charIdempotent_mul_eq_mul_mapDomain_componentProj`).
* When `#H` is a unit in `O`, the kernel of `componentProj hPH χ` is the principal ideal
  `(1 - e_χ)` (`MonoidAlgebra.ker_componentProj`).

## Main results

* `MonoidAlgebra.componentProj_mapDomainAlgHom_charIdempotent_self`,
  `MonoidAlgebra.componentProj_mapDomainAlgHom_charIdempotent_of_ne`, and
  `MonoidAlgebra.componentProj_mapDomainAlgHom_charIdempotent`: values on embedded character
  idempotents.
* `MonoidAlgebra.charIdempotent_mul_eq_mul_mapDomain_componentProj` and
  `MonoidAlgebra.ker_componentProj`: idempotent factorisation and kernel `(1 - e_χ)` when `#H` is
  invertible in `O`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.2.
-/

public section

namespace MonoidAlgebra

variable {O G : Type*} [CommRing O] [CommGroup G] {P H : Subgroup G}

/-- When `#H` is a unit in `O`, `componentProj hPH χ` sends the embedded character idempotent
`e_χ` to `1`. No domain hypothesis on `O` is required. -/
theorem componentProj_mapDomainAlgHom_charIdempotent_self [Fintype H] (hPH : P.IsComplement' H)
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    componentProj hPH χ (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) = 1 := by
  rw [componentProj_mapDomainAlgHom_right, χ.charEval_charIdempotent_self hH, map_one]

/-- Over a domain, `componentProj hPH χ` kills the embedded character idempotent `e_ω` of any
distinct character `ω ≠ χ`. No unit hypothesis on `#H` is required. -/
theorem componentProj_mapDomainAlgHom_charIdempotent_of_ne [IsDomain O] [Fintype H]
    (hPH : P.IsComplement' H) {χ ω : H →* Oˣ} (h : ω ≠ χ) :
    componentProj hPH χ (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent ω)) = 0 := by
  rw [componentProj_mapDomainAlgHom_right, MonoidHom.charEval_charIdempotent_of_ne h, map_zero]

/-- Over a domain in which `#H` is a unit, `componentProj hPH χ` sends the embedded character
idempotent `e_ω` to `1` if `ω = χ` and to `0` otherwise. -/
theorem componentProj_mapDomainAlgHom_charIdempotent [IsDomain O] [Fintype H]
    [DecidableEq (H →* Oˣ)] (hPH : P.IsComplement' H) (hH : IsUnit (Nat.card H : O))
    (χ ω : H →* Oˣ) :
    componentProj hPH χ (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent ω)) =
      if ω = χ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact componentProj_mapDomainAlgHom_charIdempotent_self hPH hH ω
  · exact componentProj_mapDomainAlgHom_charIdempotent_of_ne hPH h

/-- Multiplying any `x ∈ O[G]` by the embedded character idempotent `e_χ` agrees with multiplying
the `P`-component lift `componentProj hPH χ x` by `e_χ`. -/
theorem charIdempotent_mul_eq_mul_mapDomain_componentProj [Fintype H] (hPH : P.IsComplement' H)
    (χ : H →* Oˣ) (x : MonoidAlgebra O G) :
    mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x =
      mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) *
        mapDomainAlgHom O O P.subtype (componentProj hPH χ x) := by
  let e := mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  have he_mul (h : H) : e * single (h : G) (1 : O) = (χ h : O) • e := by
    simpa only [e, map_mul, map_smul, mapDomainAlgHom_apply, mapDomain_single,
      Subgroup.coe_subtype] using
      congrArg (mapDomainAlgHom O O H.subtype) (TauCeti.charIdempotent_mul_single χ h)
  have hbase (p : P) (h : H) :
      e * single ((p : G) * (h : G)) (1 : O) =
        e * mapDomainAlgHom O O P.subtype
          (componentProj hPH χ (single ((p : G) * (h : G)) (1 : O))) := by
    calc
      e * single ((p : G) * (h : G)) (1 : O)
          = (e * single (h : G) (1 : O)) * single (p : G) (1 : O) := by
            simp [mul_assoc, single_mul_single, mul_comm (h : G)]
      _ = ((χ h : O) • e) * single (p : G) (1 : O) := by rw [he_mul h]
      _ = e * ((χ h : O) • single (p : G) (1 : O)) := by rw [smul_mul_assoc, mul_smul_comm]
      _ = e * mapDomainAlgHom O O P.subtype
            (componentProj hPH χ (single ((p : G) * (h : G)) (1 : O))) := by
            simp [componentProj_single_mul, smul_single]
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, map_add, mul_add, hx, hy]
  | single g a =>
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    have ha : single ((p : G) * (h : G)) a = a • single ((p : G) * (h : G)) (1 : O) := by
      simp [smul_single]
    rw [Subgroup.IsComplement'.prodMulEquiv_apply, ha, mul_smul_comm, map_smul, map_smul,
      mul_smul_comm, hbase p h]

/-- Over any commutative ring `O` in which `#H` is a unit, the kernel of
`componentProj hPH χ : O[G] →ₐ[O] O[P]` is the principal ideal `(1 - e_χ)` generated by the
complementary idempotent of `χ`. -/
theorem ker_componentProj [Fintype H] (hPH : P.IsComplement' H)
    (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    RingHom.ker (componentProj hPH χ) =
      Ideal.span {(1 - mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ))} := by
  have hker : RingHom.ker (componentProj hPH χ) =
      LinearMap.ker (LinearMap.toSpanSingleton (MonoidAlgebra O G) (MonoidAlgebra O G)
        (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ))) := by
    ext x
    rw [RingHom.mem_ker, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_comm x]
    constructor
    · intro hx
      rw [charIdempotent_mul_eq_mul_mapDomain_componentProj hPH χ x, hx, map_zero, mul_zero]
    · intro hx
      calc
        componentProj hPH χ x =
            componentProj hPH χ (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) *
              componentProj hPH χ x := by
          rw [componentProj_mapDomainAlgHom_charIdempotent_self hPH hH χ, one_mul]
        _ = componentProj hPH χ (mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ) * x) :=
          (map_mul _ _ _).symm
        _ = 0 := by rw [hx, map_zero]
  exact hker.trans
    (TauCeti.isIdempotentElem_mapDomainAlgHom_charIdempotent H χ).ker_toSpanSingleton_eq_span

end MonoidAlgebra
