/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Idempotent
public import TauCeti.GroupTheory.Complement.Prod

/-!
# Twisted component projections of group algebras across complements

Let `O` be a commutative semiring (or commutative ring, where subtraction is not needed), `G` a
commutative group, and `P, H ≤ G` complementary subgroups (`P.IsComplement' H`, e.g. `G = P × H`).
Given a character `χ : H →* Oˣ`, sending `(p : G) * (h : G) ↦ χ(h) • p` defines a surjective
`O`-algebra homomorphism `MonoidAlgebra.componentProj hPH χ : O[G] →ₐ[O] O[P]` splitting the
inclusion `O[P] →ₐ[O] O[G]`, and acting on `O[H]` via character evaluation `χ.charEval`.

When `O` is a commutative ring, `H` is finite, and `#H` is a unit in `O`, multiplying any element
`x ∈ O[G]` by the embedded character idempotent `e_χ` agrees with multiplying its projection
`componentProj hPH χ x` by `e_χ`
(`MonoidAlgebra.charIdempotent_mul_eq_mul_mapDomain_componentProj`), and the kernel of
`componentProj hPH χ` is the principal ideal `(1 - e_χ)` (`MonoidAlgebra.ker_componentProj`).

## Main definitions

* `MonoidAlgebra.componentProj`: the `χ`-twisted projection `O[G] →ₐ[O] O[P]` sending
  `p * h ↦ χ(h) p`.

## Main results

* `MonoidAlgebra.componentProj_single_mul`, `MonoidAlgebra.componentProj_mapDomain_left`,
  `MonoidAlgebra.componentProj_mapDomain_right`, and `MonoidAlgebra.componentProj_surjective`:
  evaluation on basis elements, splitting on `O[P]`, evaluation on `O[H]`, and surjectivity.
* `MonoidAlgebra.charEval_componentProj`: evaluating `componentProj hPH χ x` at `φ : P →* Oˣ`
  agrees with evaluating `x` at `hPH.extendChar φ χ`.
* `MonoidAlgebra.componentProj_mapDomainAlgHom_charIdempotent`: values on embedded character
  idempotents.
* `MonoidAlgebra.charIdempotent_mul_eq_mul_mapDomain_componentProj` and
  `MonoidAlgebra.ker_componentProj`: idempotent factorisation and kernel `(1 - e_χ)` when `#H` is
  invertible in `O`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.2.
-/

public section

namespace MonoidAlgebra

section CommSemiring

variable {O G : Type*} [CommSemiring O] [CommGroup G] {P H : Subgroup G}

/-- **The `χ`-twisted component projection `O[G] →ₐ[O] O[P]`** across complementary subgroups
`P.IsComplement' H`: the `O`-algebra homomorphism sending `(p : G) * (h : G)` to `χ(h) • p` for
`p ∈ P` and `h ∈ H` (Dasgupta–Kakde, §2.2). -/
noncomputable def componentProj (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    MonoidAlgebra O G →ₐ[O] MonoidAlgebra O P :=
  let f : P × H →* MonoidAlgebra O P :=
    singleHom.comp ((((Units.coeHom O).comp χ).comp (MonoidHom.snd P H)).prod (MonoidHom.fst P H))
  lift O (MonoidAlgebra O P) G (f.comp hPH.prodMulEquiv.symm.toMonoidHom)

/-- `componentProj` sends `single (p * h) a` to `single p (a * χ(h))` for `p ∈ P` and `h ∈ H`. -/
@[simp]
theorem componentProj_single_mul (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (p : P) (h : H) (a : O) :
    componentProj hPH χ (single ((p : G) * (h : G)) a) = single p (a * (χ h : O)) := by
  simp [componentProj, Subgroup.IsComplement'.prodMulEquiv_symm_mul, smul_single]

/-- `componentProj` sends `single (p : G) a` for `p : P` to `single p a`. -/
@[simp]
theorem componentProj_single_left (hPH : P.IsComplement' H) (χ : H →* Oˣ) (p : P) (a : O) :
    componentProj hPH χ (single (p : G) a) = single p a := by
  simpa using componentProj_single_mul hPH χ p 1 a

/-- `componentProj` sends `single (h : G) a` for `h : H` to `single 1 (a * χ(h))`. -/
@[simp]
theorem componentProj_single_right (hPH : P.IsComplement' H) (χ : H →* Oˣ) (h : H) (a : O) :
    componentProj hPH χ (single (h : G) a) = single 1 (a * (χ h : O)) := by
  simpa using componentProj_single_mul hPH χ 1 h a

/-- Applying `componentProj` to an element embedded from `O[P]` via `mapDomain Subtype.val`
recovers it. -/
@[simp]
theorem componentProj_mapDomain_left (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    componentProj hPH χ (mapDomain (Subtype.val : P → G) y) = y := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapDomain_add, map_add, hx, hy]
  | single p a => simp

/-- Applying `componentProj` to an element pushed forward from `O[P]` recovers it. -/
theorem componentProj_mapDomainAlgHom_left (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O P) :
    componentProj hPH χ (mapDomainAlgHom O O P.subtype y) = y := by
  simp

/-- `componentProj` is a left inverse to the canonical inclusion `O[P] →ₐ[O] O[G]`. -/
@[simp]
theorem componentProj_comp_mapDomainAlgHom_left (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    (componentProj hPH χ).comp (mapDomainAlgHom O O P.subtype) =
      AlgHom.id O (MonoidAlgebra O P) :=
  AlgHom.ext (componentProj_mapDomainAlgHom_left hPH χ)

/-- `componentProj` is surjective, with right inverse `mapDomainAlgHom O O P.subtype`. -/
theorem componentProj_surjective (hPH : P.IsComplement' H) (χ : H →* Oˣ) :
    Function.Surjective (componentProj hPH χ) :=
  Function.RightInverse.surjective (componentProj_mapDomainAlgHom_left hPH χ)

/-- On `O[H]` embedded into `O[G]` via `mapDomain Subtype.val`, `componentProj hPH χ` acts as
`single 1 (χ.charEval y)`. -/
@[simp]
theorem componentProj_mapDomain_right (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O H) :
    componentProj hPH χ (mapDomain (Subtype.val : H → G) y) = single 1 (χ.charEval y) := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapDomain_add, map_add, map_add, single_add, hx, hy]
  | single h a => simp

/-- On `O[H] ⊆ O[G]`, `componentProj hPH χ` acts as scalar evaluation `χ.charEval` followed by
`algebraMap O O[P]`. -/
theorem componentProj_mapDomainAlgHom_right (hPH : P.IsComplement' H) (χ : H →* Oˣ)
    (y : MonoidAlgebra O H) :
    componentProj hPH χ (mapDomainAlgHom O O H.subtype y) =
      algebraMap O (MonoidAlgebra O P) (χ.charEval y) := by
  simp

/-- Evaluating `componentProj hPH χ x` at a character `φ : P →* Oˣ` agrees with evaluating `x` at
the extended character `hPH.extendChar φ χ : G →* Oˣ`. -/
@[simp]
theorem charEval_componentProj (hPH : P.IsComplement' H) (φ : P →* Oˣ) (χ : H →* Oˣ)
    (x : MonoidAlgebra O G) :
    φ.charEval (componentProj hPH χ x) = (hPH.extendChar φ χ).charEval x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a =>
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    rw [Subgroup.IsComplement'.prodMulEquiv_apply]
    simp [mul_assoc, mul_comm (χ h : O)]

end CommSemiring

section CommRing

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
    have hsingle : single ((p : G) * (h : G)) (1 : O) =
        single (h : G) (1 : O) * single (p : G) (1 : O) := by
      simp [single_mul_single, mul_comm (h : G)]
    have hsmul : (χ h : O) • single (p : G) (1 : O) = single (p : G) (1 * (χ h : O)) := by
      simp [smul_single]
    nth_rw 1 [hsingle]
    rw [← mul_assoc, he_mul h, smul_mul_assoc, componentProj_single_mul,
      mapDomainAlgHom_apply, mapDomain_single, Subgroup.coe_subtype, ← hsmul, mul_smul_comm]
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
  let e := mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · rw [RingHom.mem_ker] at hx
    have hex : e * x = 0 := by
      rw [charIdempotent_mul_eq_mul_mapDomain_componentProj hPH χ x, hx, map_zero, mul_zero]
    exact Ideal.mem_span_singleton.mpr ⟨x, by rw [sub_mul, one_mul, hex, sub_zero]⟩
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      componentProj_mapDomainAlgHom_charIdempotent_self hPH hH χ, sub_self]

end CommRing

end MonoidAlgebra
