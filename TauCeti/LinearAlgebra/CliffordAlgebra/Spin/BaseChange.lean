/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.ParameterBaseChange

/-!
# Extension of scalars for Spin groups and even unitary groups

Mathlib's `CliffordAlgebra.ofBaseChangeAux` is the canonical map from a Clifford algebra to the
Clifford algebra of a scalar extension; it preserves the even part and Clifford conjugation, as
recorded in `TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange`. It therefore restricts to a
homomorphism of Spin groups. For the canonical lift of an Eichler transvection, this homomorphism
sends `1 + ι w * ι u` to the lift determined by the pure tensors `1 ⊗ u` and `1 ⊗ w`.

The same map restricts to the even unitary carriers `U(C₀, σ)`, compatibly with the inclusion of
Spin. Over a field `K`, this is how `U(C₀, σ)` is read as a twisted form: after extension to a
field `L` splitting the even Clifford algebra, the image lands in the unitary group of a matrix
algebra with involution.

## Main results

* `CliffordAlgebra.spinGroupBaseChange` extends a Spin element's scalars.
* `CliffordAlgebra.spinGroupBaseChange_injective` proves injectivity for faithful flat extensions.
* `CliffordAlgebra.spinVectorAction_baseChange_tmul` computes the extended action on pure tensors.
* `CliffordAlgebra.spinToSpecialOrthogonal_baseChange` gives the commuting square with extension
  of special orthogonal automorphisms.
* `TauCeti.CliffordAlgebra.spinToOrthogonal_baseChange` gives the corresponding commuting square
  for orthogonal automorphisms.
* `CliffordAlgebra.spinGroupBaseChange_spinTransvection` identifies the scalar extension of a
  canonical transvection lift.
* `TauCeti.CliffordAlgebra.spinGroupBaseChange_comp_spinTransvectionHom` transports the entire
  quotient root-subgroup homomorphism.
* `CliffordAlgebra.spinGroupBaseChange_baseChange` identifies direct and successive scalar
  extension.
* `CliffordAlgebra.evenUnitaryGroupBaseChange` extends the scalars of an even unitary unit, and
  `CliffordAlgebra.evenUnitaryGroupBaseChange_injective` proves injectivity for faithful flat
  extensions.
* `CliffordAlgebra.evenUnitaryGroupBaseChange_spinGroupToEvenUnitary` gives the commuting square
  with the inclusion of Spin into the even unitary carrier.
* `CliffordAlgebra.evenUnitaryGroupBaseChange_baseChange` identifies direct and successive scalar
  extension.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The homomorphism of Spin groups induced by extension of scalars. -/
def spinGroupBaseChange (Q : QuadraticForm R M) :
    spinGroup Q →* spinGroup (Q.baseChange A) where
  toFun x := ⟨ofBaseChangeAux A Q x, by
    rw [spinGroup.mem_iff, pinGroup.mem_iff]
    refine ⟨⟨?_, ?_⟩, ofBaseChangeAux_mem_even (A := A) Q x.2.2⟩
    · -- `spinGroup.toUnits` leaves the Clifford value untouched, so extending the scalars of
      -- `x`'s underlying Lipschitz unit produces a Lipschitz unit with value
      -- `ofBaseChangeAux A Q x`.
      obtain ⟨y, hy⟩ : ∃ y : lipschitzGroup (Q.baseChange A),
          ((y : (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
            ofBaseChangeAux A Q (x : CliffordAlgebra Q) :=
        ⟨lipschitzGroupBaseChange (A := A) Q
            ⟨spinGroup.toUnits x, spinGroup.units_mem_lipschitzGroup x.2⟩,
          coe_lipschitzGroupBaseChange_apply (A := A) Q _⟩
      rw [← hy]
      exact lipschitzGroup.coe_mem_iff_mem.mpr y.2
    · rw [Unitary.mem_iff]
      constructor
      · rw [← ofBaseChangeAux_star, ← map_mul, spinGroup.star_mul_self_of_mem x.2,
          map_one]
      · rw [← ofBaseChangeAux_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
          map_one]⟩
  map_one' := Subtype.ext (map_one (ofBaseChangeAux A Q))
  map_mul' x y := Subtype.ext
    (map_mul (ofBaseChangeAux A Q) (x : CliffordAlgebra Q) (y : CliffordAlgebra Q))

/-- The Clifford value of a scalar-extended Spin element is obtained from the canonical Clifford
map. -/
@[simp]
theorem coe_spinGroupBaseChange_apply (Q : QuadraticForm R M) (x : spinGroup Q) :
    (spinGroupBaseChange (A := A) Q x : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q (x : CliffordAlgebra Q) :=
  (rfl)

/-- Extension of scalars of Spin groups is injective when the extension is faithful and the
Clifford algebra is flat; in particular, for every extension of fields. -/
theorem spinGroupBaseChange_injective [FaithfulSMul R A] (Q : QuadraticForm R M)
    [Module.Flat R (CliffordAlgebra Q)] :
    Function.Injective (spinGroupBaseChange (A := A) Q) := fun x y hxy ↦
  Subtype.ext <| ofBaseChangeAux_injective Q <| by
    simpa only [coe_spinGroupBaseChange_apply] using congrArg Subtype.val hxy

/-- On a pure tensor, the action of a scalar-extended Spin element is the extension of the
original action. -/
@[simp]
theorem spinVectorAction_baseChange_tmul (Q : QuadraticForm R M) (x : spinGroup Q)
    (a : A) (m : M) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    spinVectorAction (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] spinVectorAction Q x m := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  suffices hOne :
      spinVectorAction (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) (1 ⊗ₜ[R] m) =
        1 ⊗ₜ[R] spinVectorAction Q x m by
    have ha (n : M) : a ⊗ₜ[R] n = a • (1 ⊗ₜ[R] n) := by
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' a (1 : A) n).symm
    rw [ha, map_smul, hOne, ← ha]
  apply ι_injective (Q.baseChange A)
  rw [ι_spinVectorAction_apply, coe_spinGroupBaseChange_apply,
    ← ofBaseChangeAux_ι A Q m, ← ofBaseChangeAux_star, ← map_mul, ← map_mul,
    ← ι_spinVectorAction_apply, ofBaseChangeAux_ι]

/-- Extension of scalars commutes with the Spin homomorphism to the special orthogonal group. -/
@[simp]
theorem spinToSpecialOrthogonal_baseChange [Module.Free R M] [Module.Finite R M]
    (Q : QuadraticForm R M) (x : spinGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange (A := A) Q
        (spinToSpecialOrthogonal Q x) =
      spinToSpecialOrthogonal (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange_apply_tmul,
        coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply,
        spinVectorAction_baseChange_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

section Field

variable {K : Type u} {L : Type v} {V : Type w}
variable [Field K] [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]
variable {Q : QuadraticForm K V} {u w : V}

/-- Extension of scalars carries the canonical Spin lift of `E_{u,w}` to the canonical lift of
`E_{1 ⊗ u,1 ⊗ w}`. -/
@[simp]
theorem spinGroupBaseChange_spinTransvection (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (huw : QuadraticMap.polar Q u w = 0) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    spinGroupBaseChange (A := L) Q (spinTransvection hQ hu huw) =
      spinTransvection (QuadraticForm.Nondegenerate.baseChange hQ)
        (u := 1 ⊗ₜ[K] u) (w := 1 ⊗ₜ[K] w)
        (by simp [QuadraticForm.baseChange_tmul, hu])
        (by simp [QuadraticForm.polar_baseChange_tmul, huw]) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  rw [coe_spinGroupBaseChange_apply, coe_spinTransvection, coe_spinTransvection, map_add,
    map_one, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι]

end Field

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (Q : QuadraticForm R M)

/-- Direct and successive scalar extension of a Spin element agree after transport along the
canonical scalar-tower isometry. -/
@[simp]
theorem spinGroupBaseChange_baseChange (z : spinGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry.spinGroupMap
        (spinGroupBaseChange (A := B) Q z) =
      spinGroupBaseChange (A := B) (Q.baseChange A)
        (spinGroupBaseChange (A := A) Q z) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupBaseChange_apply, coe_spinGroupBaseChange_apply,
    coe_spinGroupBaseChange_apply]
  exact ofBaseChangeAux_baseChange Q _

end ScalarTower

/-! ### The even unitary carrier -/

/-- The homomorphism of even unitary carriers `U(C₀, σ) → U(C₀ ⊗ A, σ)` induced by extension of
scalars. -/
def evenUnitaryGroupBaseChange (Q : QuadraticForm R M) :
    evenUnitaryGroup Q →* evenUnitaryGroup (Q.baseChange A) :=
  ((Units.map (ofBaseChangeAux A Q : CliffordAlgebra Q →* CliffordAlgebra (Q.baseChange A))).comp
      (evenUnitaryGroup Q).subtype).codRestrict _ fun x ↦ by
    have hx := (evenUnitaryGroup.mem_iff Q).mp x.2
    rw [evenUnitaryGroup.mem_iff, MonoidHom.comp_apply, Units.coe_map, Unitary.mem_iff]
    refine ⟨ofBaseChangeAux_mem_even Q hx.1, ?_, ?_⟩ <;>
      rw [MonoidHom.coe_ofClass, ← ofBaseChangeAux_star, ← map_mul] <;>
      simp [Unitary.star_mul_self_of_mem hx.2, Unitary.mul_star_self_of_mem hx.2]

/-- The Clifford value of a scalar-extended even unitary unit is obtained from the canonical
Clifford map. -/
@[simp]
theorem coe_evenUnitaryGroupBaseChange_apply (Q : QuadraticForm R M) (x : evenUnitaryGroup Q) :
    (((evenUnitaryGroupBaseChange (A := A) Q x : evenUnitaryGroup (Q.baseChange A)) :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  (rfl)

/-- Extension of scalars of even unitary carriers is injective when the extension is faithful and
the Clifford algebra is flat; in particular, for every extension of fields. -/
theorem evenUnitaryGroupBaseChange_injective [FaithfulSMul R A] (Q : QuadraticForm R M)
    [Module.Flat R (CliffordAlgebra Q)] :
    Function.Injective (evenUnitaryGroupBaseChange (A := A) Q) := fun x y hxy ↦
  Subtype.ext <| Units.ext <| ofBaseChangeAux_injective Q <| by
    simpa only [coe_evenUnitaryGroupBaseChange_apply] using
      congrArg (fun z : evenUnitaryGroup (Q.baseChange A) ↦
        ((z : (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A))) hxy

/-- Extension of scalars commutes with the inclusion of Spin into the even unitary carrier. -/
@[simp]
theorem evenUnitaryGroupBaseChange_spinGroupToEvenUnitary (Q : QuadraticForm R M)
    (x : spinGroup Q) :
    evenUnitaryGroupBaseChange (A := A) Q (spinGroupToEvenUnitary Q x) =
      spinGroupToEvenUnitary (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_evenUnitaryGroupBaseChange_apply, coe_spinGroupToEvenUnitary_apply,
      coe_spinGroupToEvenUnitary_apply]
    -- Mathlib states no coercion lemma for `spinGroup.toUnits`, whose value field is the
    -- underlying Clifford element, so both sides are `ofBaseChangeAux A Q x` by definition.
    exact (coe_spinGroupBaseChange_apply Q x).symm

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (Q : QuadraticForm R M)

/-- Direct and successive scalar extension of an even unitary unit agree after transport along
the canonical scalar-tower isometry. -/
@[simp]
theorem evenUnitaryGroupBaseChange_baseChange (z : evenUnitaryGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry.evenUnitaryGroupMap
        (evenUnitaryGroupBaseChange (A := B) Q z) =
      evenUnitaryGroupBaseChange (A := B) (Q.baseChange A)
        (evenUnitaryGroupBaseChange (A := A) Q z) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  apply Units.ext
  rw [QuadraticMap.Isometry.coe_evenUnitaryGroupMap_apply, Units.coe_map,
    coe_evenUnitaryGroupBaseChange_apply, coe_evenUnitaryGroupBaseChange_apply,
    coe_evenUnitaryGroupBaseChange_apply]
  exact ofBaseChangeAux_baseChange Q _

end ScalarTower

end CliffordAlgebra

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra TauCeti.QuadraticMap

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- Extension of scalars commutes with the Spin homomorphism to the orthogonal group. -/
@[simp]
theorem spinToOrthogonal_baseChange (Q : QuadraticForm R M) (x : spinGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    spinToOrthogonal (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) =
      orthogonalGroupBaseChange (A := A) Q (spinToOrthogonal Q x) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  rw [coe_orthogonalGroupBaseChange]
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [coe_spinToOrthogonal_apply, LinearEquiv.baseChange_tmul,
        coe_spinToOrthogonal_apply]
      exact spinVectorAction_baseChange_tmul (A := A) Q x a m
  | add z w hz hw => simp only [map_add, hz, hw]

open _root_.QuadraticMap

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]

/-- Extending scalars along a field extension carries the canonical Spin root-subgroup
homomorphism to that of the extended quotient parameters, preserving its additive composition
law. -/
theorem spinGroupBaseChange_comp_spinTransvectionHom {Q : QuadraticForm K V} {u : V}
    (hQ : Q.Nondegenerate) (hu : Q u = 0) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (spinGroupBaseChange (A := L) Q).toAdditive.comp (spinTransvectionHom hQ hu) =
      (spinTransvectionHom (QuadraticForm.Nondegenerate.baseChange hQ)
        (u := 1 ⊗ₜ[K] u) (by simp [QuadraticForm.baseChange_tmul, hu])).comp
          (transvectionParameterBaseChange (A := L) Q u).toAddMonoidHom := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply AddMonoidHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with | H w =>
    have huw : polar Q u (w : V) = 0 := LinearMap.mem_ker.mp w.2
    apply Additive.toMul.injective
    simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
      LinearMap.toAddMonoidHom_coe, transvectionParameterBaseChange_mk, toMul_ofMul]
    rw [toMul_spinTransvectionHom_mk hQ hu huw, spinGroupBaseChange_spinTransvection,
      toMul_spinTransvectionHom_mk]

end TauCeti.CliffordAlgebra
