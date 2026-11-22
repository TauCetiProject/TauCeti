/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.MonoidAlgebra.CharEval.Basic
public import TauCeti.GroupTheory.Complement.Prod

/-!
# Twisted component projections of group algebras across complements

Let `O` be a commutative semiring (or commutative ring, where subtraction is not needed), `G` a
commutative group, and `P, H ≤ G` complementary subgroups (`P.IsComplement' H`, e.g. `G = P × H`).
Given a character `χ : H →* Oˣ`, sending `(p : G) * (h : G) ↦ χ(h) • p` defines a surjective
`O`-algebra homomorphism `MonoidAlgebra.componentProj hPH χ : O[G] →ₐ[O] O[P]` splitting the
inclusion `O[P] →ₐ[O] O[G]`, and acting on `O[H]` via character evaluation `χ.charEval`.

## Main definitions

* `MonoidAlgebra.componentProj`: the `χ`-twisted projection `O[G] →ₐ[O] O[P]` sending
  `p * h ↦ χ(h) p`.

## Main results

* `MonoidAlgebra.componentProj_single`, `MonoidAlgebra.componentProj_single_mul`,
  `MonoidAlgebra.componentProj_mapDomain_left`, `MonoidAlgebra.componentProj_mapDomain_right`,
  and `MonoidAlgebra.componentProj_surjective`: evaluation on basis elements, splitting on `O[P]`,
  evaluation on `O[H]`, and surjectivity.
* `MonoidAlgebra.charEval_componentProj`: evaluating `componentProj hPH χ x` at `φ : P →* Oˣ`
  agrees with evaluating `x` at `hPH.extendChar φ χ`.

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

/-- `componentProj` evaluates at `single g a` via the coordinates of `hPH.prodMulEquiv.symm g`. -/
theorem componentProj_single (hPH : P.IsComplement' H) (χ : H →* Oˣ) (g : G) (a : O) :
    componentProj hPH χ (single g a) =
      single (hPH.prodMulEquiv.symm g).1 (a * (χ (hPH.prodMulEquiv.symm g).2 : O)) := by
  simp [componentProj, smul_single]

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

end MonoidAlgebra
