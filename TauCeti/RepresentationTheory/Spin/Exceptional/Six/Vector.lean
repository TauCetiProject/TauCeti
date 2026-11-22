/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.Transvection
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.Hyperbolic
import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Basic

/-!
# The vector representation of `Spin₆` as an exterior square

Let `V = W ⊕ W'` be a polarized six-dimensional quadratic space over a field of characteristic
different from two, and let `S⁺ = ⋀ᵉᵛᵉⁿ W` be its even half-spin module. The half-spin action
identifies `Spin(Q)` with `SL(S⁺) ≅ SL₄`
(`TauCeti.spinGroupEquivSpecialLinearGroupOfFinrankEqSix`). This file proves that under this
identification the vector representation of `Spin(Q)` on `V` is the exterior square of the
half-spin representation. This is the vector half of the exceptional isomorphism
`D₃ = A₃`, distinct from the identification of `S⁺` with the standard module.

For a basis `e₀, e₁, e₂` of `W` with polar-dual vectors `f₀, f₁, f₂` in `W'`, the even monomials
`1, e₀e₁, e₀e₂, e₁e₂` form a basis of `S⁺`. The comparison
`TauCeti.spinSixVectorEquivExteriorSquare : V ≃ ⋀²S⁺` sends `eₐ` to the wedge of the two
monomials containing `eₐ`, and `fₐ` to the wedge of `1` with the monomial avoiding `eₐ`, up to
order:

```text
e₀ ↦ e₀e₁ ∧ e₀e₂,  e₁ ↦ e₀e₁ ∧ e₁e₂,  e₂ ↦ e₀e₂ ∧ e₁e₂,
f₀ ↦ e₁e₂ ∧ 1,     f₁ ↦ 1 ∧ e₀e₂,      f₂ ↦ e₀e₁ ∧ 1.
```

## The argument

The canonical Spin lifts `TauCeti.spinSixTransvectionLift` of the twelve elementary
transvections of `S⁺` act on `V` by Eichler transvections with explicit isotropic vectors. On
each of them the comparison intertwines the vector action with the exterior square of the
half-spin action; this is a finite computation in the basis above. These lifts generate the
Spin group, because the half-spin matrix map is injective and the elementary transvections
generate `SL₄`. Two homomorphisms agreeing on generators agree everywhere.

## Main definitions

* `TauCeti.spinSixVectorEquivExteriorSquare`: the comparison `V ≃ ⋀²S⁺` defined by the formulas
  above.

## Main results

* `TauCeti.spinSixVectorEquivExteriorSquare_spinVectorAction`: the comparison intertwines the
  vector action of a Spin element with the exterior square of its half-spin action.
* `TauCeti.spin6_vector_equiv_exteriorSquare`: under the polarized equivalence
  `Spin(Q) ≃ SL₄`, the vector representation is the exterior square of the standard
  representation of `SL₄`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20, §20.1.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra Module
open scoped Matrix

variable {K : Type*} [Field K]

section Polarized

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q) (hline : P.line = ⊥) (b : Basis (Fin 3) K P.W)

/-! ### The comparison in standard coordinates -/

/-- The wedge-basis index of each vector of the hyperbolic basis `e₀, e₁, e₂, f₀, f₁, f₂`. -/
private def wedgeIndex : (Fin 3 ⊕ Fin 3) ≃ (Fin 3 ⊕ Fin 3) :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr Fin.revPerm Fin.revPerm)

/-- The sign of each vector of the hyperbolic basis in the wedge basis. -/
private def wedgeIndexSign : Fin 3 ⊕ Fin 3 → Kˣ := Sum.elim 1 (-1)

variable (K) in
/-- The basis of `⋀²(K⁴)` matching the hyperbolic basis `e₀, e₁, e₂, f₀, f₁, f₂`. -/
private noncomputable def wedgeTarget : Basis (Fin 3 ⊕ Fin 3) K (⋀[K]^2 (Fin 4 → K)) :=
  ((spinSixWedgeBasis K).reindex wedgeIndex.symm).unitsSMul wedgeIndexSign

/-- The comparison `V ≃ ⋀²(K⁴)` in the coordinates of the even-monomial basis of `S⁺`. -/
private noncomputable def vectorCoordEquiv : V ≃ₗ[K] ⋀[K]^2 (Fin 4 → K) :=
  (P.typeDBasis b hline).equiv (wedgeTarget K) (Equiv.refl _)

private theorem vectorCoordEquiv_basis (a : Fin 3) :
    vectorCoordEquiv P hline b (b a : V) =
      exteriorPower.ιMulti K 2 ![Pi.single (![1, 1, 2] a) 1, Pi.single (![2, 3, 3] a) 1] := by
  rw [← P.typeDBasis_inl b hline, vectorCoordEquiv, Basis.equiv_apply]
  fin_cases a <;> simp [wedgeTarget, wedgeIndex, wedgeIndexSign, Basis.unitsSMul_apply,
    exteriorPower.ιMulti_two_comp (R := K) fun q : Fin 4 ↦ (Pi.single q 1 : Fin 4 → K)]

private theorem vectorCoordEquiv_dualVector (a : Fin 3) :
    vectorCoordEquiv P hline b (P.dualVector b a : V) =
      exteriorPower.ιMulti K 2 ![Pi.single (![3, 0, 1] a) 1, Pi.single (![0, 2, 0] a) 1] := by
  rw [← P.typeDBasis_inr b hline, vectorCoordEquiv, Basis.equiv_apply]
  fin_cases a <;> simp [wedgeTarget, wedgeIndex, wedgeIndexSign, Basis.unitsSMul_apply,
    Units.smul_def,
    exteriorPower.ιMulti_two_swap_of_lt (R := K) fun q : Fin 4 ↦ (Pi.single q 1 : Fin 4 → K)]
  -- The middle vector `f₁` carries the sign of `-e₀₂` twice.
  module

private theorem polar_dualVector_basis (i j : Fin 3) :
    QuadraticMap.polar Q (P.dualVector b i : V) (b j : V) = if j = i then 1 else 0 := by
  rw [QuadraticMap.polar_comm, P.polar_dualVector]

/-! ### The comparison with the exterior square of the half-spin module -/

/-- **The vector space of a polarized six-dimensional quadratic space is the exterior square of
the even half-spin module.** Write `e₀, e₁, e₂` for the basis `b` of `W`, `f₀, f₁, f₂` for its
polar-dual vectors in `W'`, and `1, e₀e₁, e₀e₂, e₁e₂` for the even-monomial basis of `S⁺`. The
equivalence sends `eₐ` to the wedge of the two monomials containing `eₐ`, and `fₐ` to a wedge of
`1` with the monomial avoiding `eₐ`; see `TauCeti.spinSixVectorEquivExteriorSquare_basis` and
`TauCeti.spinSixVectorEquivExteriorSquare_dualVector`. It intertwines the vector action of Spin
with the exterior square of the half-spin action
(`TauCeti.spinSixVectorEquivExteriorSquare_spinVectorAction`). -/
noncomputable def spinSixVectorEquivExteriorSquare : V ≃ₗ[K] ⋀[K]^2 (spinPlus Q P) :=
  (vectorCoordEquiv P hline b).trans
    ((b.spinSixEvenMonomialBasis (spinPlus_def P)).equivFun.symm.exteriorPower 2)

/-- The comparison is the coordinate comparison followed by the even-monomial basis of `S⁺`. -/
private theorem spinSixVectorEquivExteriorSquare_apply (v : V) :
    spinSixVectorEquivExteriorSquare P hline b v =
      exteriorPower.map 2 (b.spinSixEvenMonomialBasis (spinPlus_def P)).equivFun.symm.toLinearMap
        (vectorCoordEquiv P hline b v) := by
  rw [spinSixVectorEquivExteriorSquare, LinearEquiv.trans_apply]
  exact LinearMap.congr_fun (LinearEquiv.exteriorPower_toLinearMap _ 2) _

/-- The comparison sends `e₀, e₁, e₂` to `e₀e₁ ∧ e₀e₂`, `e₀e₁ ∧ e₁e₂` and `e₀e₂ ∧ e₁e₂`. -/
@[simp]
theorem spinSixVectorEquivExteriorSquare_basis (a : Fin 3) :
    spinSixVectorEquivExteriorSquare P hline b (b a : V) =
      exteriorPower.ιMulti K 2
        ![b.spinSixEvenMonomialBasis (spinPlus_def P) (![1, 1, 2] a),
          b.spinSixEvenMonomialBasis (spinPlus_def P) (![2, 3, 3] a)] := by
  rw [spinSixVectorEquivExteriorSquare_apply, vectorCoordEquiv_basis,
    exteriorPower.map_apply_ιMulti_two]
  simp only [LinearEquiv.coe_coe, Basis.equivFun_symm_single]

/-- The comparison sends `f₀, f₁, f₂` to `e₁e₂ ∧ 1`, `1 ∧ e₀e₂` and `e₀e₁ ∧ 1`. -/
@[simp]
theorem spinSixVectorEquivExteriorSquare_dualVector (a : Fin 3) :
    spinSixVectorEquivExteriorSquare P hline b (P.dualVector b a : V) =
      exteriorPower.ιMulti K 2
        ![b.spinSixEvenMonomialBasis (spinPlus_def P) (![3, 0, 1] a),
          b.spinSixEvenMonomialBasis (spinPlus_def P) (![0, 2, 0] a)] := by
  rw [spinSixVectorEquivExteriorSquare_apply, vectorCoordEquiv_dualVector,
    exteriorPower.map_apply_ιMulti_two]
  simp only [LinearEquiv.coe_coe, Basis.equivFun_symm_single]

variable [Invertible (2 : K)]

/-! ### The comparison on the transvection lifts -/

/-- The coordinate comparison intertwines the vector action of the lift of an elementary
transvection with the exterior square of that transvection. -/
private abbrev LiftIntertwines (i j : Fin 4) (hij : i ≠ j) (c : K) : Prop :=
  (vectorCoordEquiv P hline b).toLinearMap ∘ₗ
      (spinVectorAction Q (spinSixTransvectionLift P hline b hij c)).toLinearMap =
    exteriorPower.map 2 (Matrix.toLin' (Matrix.transvection i j c)) ∘ₗ
      (vectorCoordEquiv P hline b).toLinearMap

/- Proves `LiftIntertwines P hline b i j _ c` for explicit indices `i ≠ j`, by evaluating both
sides on the six vectors of the hyperbolic basis. The vector action of the lift is an Eichler
transvection with explicit isotropic vectors, and both sides expand to the same combination of
increasing wedges of standard basis vectors. The proof is shared by all twelve index pairs, each
of which needs only part of the lemma list. -/
local macro "prove_liftIntertwines" : tactic => `(tactic|
  (refine (P.typeDBasis b hline).ext fun k ↦ ?_
   rcases k with a | a <;>
   simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, P.typeDBasis_inl, P.typeDBasis_inr,
     spinVectorAction_spinSixTransvectionLift_apply] <;>
   fin_cases a <;>
   simp [-exteriorPower.map_apply_ιMulti, -Matrix.toLin'_apply,
     spinSixTransvectionFirstVector_apply, spinSixTransvectionSecondVector_apply,
     vectorCoordEquiv_basis, vectorCoordEquiv_dualVector, exteriorPower.map_apply_ιMulti_two,
     Matrix.toLin'_transvection_single, P.polar_W_eq_zero, P.polar_W'_eq_zero,
     polar_dualVector_basis, exteriorPower.ιMulti_two_add_left,
     exteriorPower.ιMulti_two_add_right, exteriorPower.ιMulti_two_smul_left,
     exteriorPower.ιMulti_two_smul_right, QuadraticMap.map_smul,
     exteriorPower.ιMulti_two_swap_of_lt (R := K) fun q : Fin 4 ↦ (Pi.single q 1 : Fin 4 → K)] <;>
   module))

private theorem liftIntertwines_zero_one (c : K) :
    LiftIntertwines P hline b 0 1 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_zero_two (c : K) :
    LiftIntertwines P hline b 0 2 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_zero_three (c : K) :
    LiftIntertwines P hline b 0 3 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_one_zero (c : K) :
    LiftIntertwines P hline b 1 0 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_one_two (c : K) :
    LiftIntertwines P hline b 1 2 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_one_three (c : K) :
    LiftIntertwines P hline b 1 3 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_two_zero (c : K) :
    LiftIntertwines P hline b 2 0 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_two_one (c : K) :
    LiftIntertwines P hline b 2 1 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_two_three (c : K) :
    LiftIntertwines P hline b 2 3 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_three_zero (c : K) :
    LiftIntertwines P hline b 3 0 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_three_one (c : K) :
    LiftIntertwines P hline b 3 1 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines_three_two (c : K) :
    LiftIntertwines P hline b 3 2 (by decide) c := by
  prove_liftIntertwines

private theorem liftIntertwines {i j : Fin 4} (hij : i ≠ j) (c : K) :
    LiftIntertwines P hline b i j hij c := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact liftIntertwines_zero_one P hline b c
  · exact liftIntertwines_zero_two P hline b c
  · exact liftIntertwines_zero_three P hline b c
  · exact liftIntertwines_one_zero P hline b c
  · exact (hij rfl).elim
  · exact liftIntertwines_one_two P hline b c
  · exact liftIntertwines_one_three P hline b c
  · exact liftIntertwines_two_zero P hline b c
  · exact liftIntertwines_two_one P hline b c
  · exact (hij rfl).elim
  · exact liftIntertwines_two_three P hline b c
  · exact liftIntertwines_three_zero P hline b c
  · exact liftIntertwines_three_one P hline b c
  · exact liftIntertwines_three_two P hline b c
  · exact (hij rfl).elim

omit [Invertible (2 : K)] in
/-- If a linear automorphism `A` of `V` acts in the coordinates of `vectorCoordEquiv` by the
exterior square of a matrix `T`, and `T` is the matrix of `φ` in the even-monomial basis, then the
comparison intertwines `A` with the exterior square of `φ`. -/
private theorem spinSixVectorEquivExteriorSquare_apply_of_toMatrix_eq (A : V ≃ₗ[K] V)
    (φ : Module.End K (spinPlus Q P)) {T : Matrix (Fin 4) (Fin 4) K}
    (hA : (vectorCoordEquiv P hline b).toLinearMap ∘ₗ A.toLinearMap =
      exteriorPower.map 2 (Matrix.toLin' T) ∘ₗ (vectorCoordEquiv P hline b).toLinearMap)
    (hφ : LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
      (b.spinSixEvenMonomialBasis (spinPlus_def P)) φ = T) (x : V) :
    spinSixVectorEquivExteriorSquare P hline b (A x) =
      exteriorPower.map 2 φ (spinSixVectorEquivExteriorSquare P hline b x) := by
  subst hφ
  have hx := LinearMap.congr_fun hA x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
  exact (spinSixVectorEquivExteriorSquare_apply P hline b (A x)).trans <|
    (congrArg (exteriorPower.map 2 _) hx).trans <|
      (exteriorPower.map_apply_map_of_comp_eq
        (LinearMap.equivFun_symm_comp_toLin'_toMatrix _ _ φ) _).trans <|
        congrArg (exteriorPower.map 2 φ) (spinSixVectorEquivExteriorSquare_apply P hline b x).symm

/-- The comparison intertwines the vector action of the lift of an elementary transvection with
the exterior square of its half-spin action. -/
private theorem spinSixVectorEquivExteriorSquare_spinVectorAction_lift {i j : Fin 4}
    (hij : i ≠ j) (c : K) (x : V) :
    spinSixVectorEquivExteriorSquare P hline b
        (spinVectorAction Q (spinSixTransvectionLift P hline b hij c) x) =
      exteriorPower.map 2
        (spinPlusAction Q P hline (spinGroupToEven Q (spinSixTransvectionLift P hline b hij c)))
        (spinSixVectorEquivExteriorSquare P hline b x) :=
  spinSixVectorEquivExteriorSquare_apply_of_toMatrix_eq P hline b _ _
    (liftIntertwines P hline b hij c)
    (toMatrix_spinPlusAction_spinSixTransvectionLift P hline b hij c) x

/-- The half-spin matrices in the even-monomial basis give an injective homomorphism from Spin
to `SL₄` taking each canonical transvection lift to its transvection, so these lifts generate
the Spin group. -/
private theorem closure_range_spinSixTransvectionLift :
    Subgroup.closure (Set.range fun t : Matrix.TransvectionStruct (Fin 4) K ↦
      spinSixTransvectionLift P hline b t.hij t.c) = ⊤ := by
  let B := b.spinSixEvenMonomialBasis (spinPlus_def P)
  have hW : finrank K P.W = 3 := (finrank_eq_card_basis b).trans (Fintype.card_fin 3)
  have hV : finrank K V = 6 := (P.finrank_eq_two_mul_card b hline).trans (by simp)
  let ψ : spinGroup Q →* Matrix.SpecialLinearGroup (Fin 4) K :=
    { toFun s := ⟨LinearMap.toMatrix B B (spinPlusAction Q P hline (spinGroupToEven Q s)), by
        rw [LinearMap.det_toMatrix]
        exact det_spinPlusAction_spinGroupToEven P hline hW s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' s t := Subtype.ext (by
        simp only [map_mul, LinearMap.toMatrix_mul]
        rfl) }
  -- The half-spin action determines the Spin element through the polarized equivalence.
  have hψ : Function.Injective ψ := by
    intro s t h
    have hst : spinPlusAction Q P hline (spinGroupToEven Q s) =
        spinPlusAction Q P hline (spinGroupToEven Q t) :=
      (LinearMap.toMatrix B B).injective (congrArg Subtype.val h)
    apply (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV).injective
    apply Subtype.ext
    rw [coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply,
      coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply]
    exact congrArg (LinearMap.toMatrix _ _) hst
  have hmap : (Subgroup.closure (Set.range fun t : Matrix.TransvectionStruct (Fin 4) K ↦
      spinSixTransvectionLift P hline b t.hij t.c)).map ψ = ⊤ := by
    rw [MonoidHom.map_closure, eq_top_iff,
      ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨_, ⟨t, rfl⟩, Subtype.ext
      (toMatrix_spinPlusAction_spinSixTransvectionLift P hline b t.hij t.c)⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, hgh⟩ := (Subgroup.mem_map).mp (hmap ▸ Subgroup.mem_top (ψ g))
  rwa [hψ hgh] at hh

/-- **The vector representation of `Spin₆` is the exterior square of the half-spin
representation.** The comparison `TauCeti.spinSixVectorEquivExteriorSquare` sends the vector
action of a Spin element to the exterior square of its action on the even half-spin module. -/
theorem spinSixVectorEquivExteriorSquare_spinVectorAction (g : spinGroup Q) (v : V) :
    spinSixVectorEquivExteriorSquare P hline b (spinVectorAction Q g v) =
      exteriorPower.map 2 (spinPlusAction Q P hline (spinGroupToEven Q g))
        (spinSixVectorEquivExteriorSquare P hline b v) := by
  let Ψ := spinSixVectorEquivExteriorSquare P hline b
  -- The vector action transported along the comparison, as a representation on `⋀²S⁺`.
  let σ : spinGroup Q →* Module.End K (⋀[K]^2 (spinPlus Q P)) :=
    { toFun s := Ψ.toLinearMap ∘ₗ (spinVectorAction Q s).toLinearMap ∘ₗ Ψ.symm.toLinearMap
      map_one' := LinearMap.ext fun y ↦ by simp
      map_mul' s t := LinearMap.ext fun y ↦ by simp }
  have hσ : σ = Representation.exteriorPower
      ((spinPlusAction Q P hline : even Q →* Module.End K (spinPlus Q P)).comp
        (spinGroupToEven Q)) 2 := by
    refine MonoidHom.eq_of_eqOn_dense (closure_range_spinSixTransvectionLift P hline b) ?_
    rintro _ ⟨t, rfl⟩
    refine LinearMap.ext fun y ↦ ?_
    have h := spinSixVectorEquivExteriorSquare_spinVectorAction_lift P hline b t.hij t.c
      (Ψ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.exteriorPower_apply, MonoidHom.coe_comp, Function.comp_apply,
      AlgHom.coe_toMonoidHom]
    exact h
  have h := LinearMap.congr_fun (congrArg (fun ρ ↦ ρ g) hσ) (Ψ v)
  simpa only [σ, Ψ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Representation.exteriorPower_apply, MonoidHom.coe_comp,
    Function.comp_apply, AlgHom.coe_toMonoidHom] using h

/-- **The vector representation of `Spin₆` is the exterior square of the standard
representation of `SL₄`.** For a polarized six-dimensional quadratic space over a field of
characteristic different from two, take the equivalence `f : Spin(Q) ≃ SL₄` given by the action
on the even half-spin module, `TauCeti.spinGroupEquivSpecialLinearGroupOfFinrankEqSix`. There is
a linear equivalence `E : V ≃ ⋀²(K⁴)` with `E (g • v) = (⋀² f g) (E v)` for every Spin element
`g` acting on `V` through `spinToSpecialOrthogonal`. -/
theorem spin6_vector_equiv_exteriorSquare (hV : finrank K V = 6) :
    ∃ E : V ≃ₗ[K] ⋀[K]^2 (Fin 4 → K), ∀ (g : spinGroup Q) (v : V),
      E ((spinToSpecialOrthogonal Q g : V ≃ₗ[K] V) v) =
        ((stdSLRep K 4).exteriorPower 2
          (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV g)) (E v) := by
  have hline := P.line_eq_bot_of_finrank_eq_six hV
  have : Module.Finite K P.W := Module.finite_of_finrank_pos
    (by rw [P.finrank_W_eq_three_of_finrank_eq_six hV]; omega)
  let b := finBasisOfFinrankEq K P.W (P.finrank_W_eq_three_of_finrank_eq_six hV)
  let B := spinPlusFinBasisOfFinrankEqSix P hV
  refine ⟨(spinSixVectorEquivExteriorSquare P hline b).trans (B.equivFun.exteriorPower 2),
    fun g v ↦ ?_⟩
  let Ψ := spinSixVectorEquivExteriorSquare P hline b
  let φ := spinPlusAction Q P hline (spinGroupToEven Q g)
  -- In the basis `B`, the half-spin action of `g` is the matrix `f g`.
  have hf : stdSLRep K 4 (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV g) =
      Matrix.toLin' (LinearMap.toMatrix B B φ) := by
    rw [stdSLRep_apply, coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply,
      Matrix.toLin'_apply']
  have he (z : ⋀[K]^2 (spinPlus Q P)) :
      B.equivFun.exteriorPower 2 z = exteriorPower.map 2 B.equivFun.toLinearMap z :=
    LinearMap.congr_fun (LinearEquiv.exteriorPower_toLinearMap B.equivFun 2) z
  calc (Ψ.trans (B.equivFun.exteriorPower 2)) ((spinToSpecialOrthogonal Q g : V ≃ₗ[K] V) v)
      = (Ψ.trans (B.equivFun.exteriorPower 2)) (spinVectorAction Q g v) :=
        congrArg (Ψ.trans (B.equivFun.exteriorPower 2)) (coe_spinToSpecialOrthogonal_apply Q g v)
    _ = exteriorPower.map 2 B.equivFun.toLinearMap (exteriorPower.map 2 φ (Ψ v)) :=
        (LinearEquiv.trans_apply (e₁₂ := Ψ) (e₂₃ := B.equivFun.exteriorPower 2) _).trans <|
          (he _).trans <| congrArg (exteriorPower.map 2 B.equivFun.toLinearMap)
            (spinSixVectorEquivExteriorSquare_spinVectorAction P hline b g v)
    _ = exteriorPower.map 2 (Matrix.toLin' (LinearMap.toMatrix B B φ))
          (exteriorPower.map 2 B.equivFun.toLinearMap (Ψ v)) :=
        exteriorPower.map_apply_map_of_comp_eq
          (LinearMap.toLin'_toMatrix_comp_equivFun B B φ).symm _
    _ = exteriorPower.map 2 (stdSLRep K 4 (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV g))
          ((Ψ.trans (B.equivFun.exteriorPower 2)) v) :=
        (congrArg (fun L ↦ exteriorPower.map 2 L
          (exteriorPower.map 2 B.equivFun.toLinearMap (Ψ v))) hf.symm).trans <|
          congrArg (exteriorPower.map 2 (stdSLRep K 4
            (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV g)))
            ((he _).symm.trans
              (LinearEquiv.trans_apply (e₁₂ := Ψ) (e₂₃ := B.equivFun.exteriorPower 2) v).symm)
    _ = ((stdSLRep K 4).exteriorPower 2
          (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hV g))
          ((Ψ.trans (B.equivFun.exteriorPower 2)) v) := by
        rw [Representation.exteriorPower_apply (stdSLRep K 4) 2]

end Polarized

end TauCeti
