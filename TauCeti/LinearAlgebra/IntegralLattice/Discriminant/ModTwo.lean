/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Scaling
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.ModTwo

/-!
# The discriminant form of `M(2)` for an even unimodular lattice `M`

Let `M` be an even unimodular lattice and `M(2) = 2 • M` its rescaling by two. Multiplication by
two identifies the discriminant group of `M(2)` with `M / 2M`
(`TauCeti.IntegralLattice.IsUnimodular.discriminantGroupScaleEquiv`), and under this
identification the discriminant quadratic form of `M(2)`, valued in `ℚ/ℤ`, is half of the
quadratic form `Q₂(x mod 2) = B(x, x) / 2 mod 2` over `ZMod 2`:

```text
q_{M(2)}(x / 2 mod M) = Q₂(x mod 2) / 2 mod ℤ.
```

Since `ZMod 2 → ℚ/ℤ`, `t ↦ t / 2`, is injective, a transformation of `M / 2M` preserves `Q₂` exactly
when the corresponding transformation of the discriminant group preserves `q_{M(2)}`. So the
orthogonal group `O(q_{M(2)})` of the discriminant form is the orthogonal group `O(Q₂)` of the
nonsingular quadratic space `M / 2M` over `ZMod 2`, and the action of `O(M) = O(M(2))` on the
discriminant form is its action on `M / 2M` by reduction modulo two.

This turns the image of `O(M(2)) → O(q_{M(2)})` into a subgroup of `O(Q₂)` containing the
reductions of all isometries of `M`, in particular the orthogonal transvections coming from
reflections in roots of `M`. For `M = U ⊕ E₈(-1)` the rescaling `U(2) ⊕ E₈(-2)` is the invariant
lattice of an Enriques involution on the K3 lattice.

## Main declarations

* `q_{M(2)} = Q₂ / 2` under `A_{M(2)} ≃ M / 2M`:
  `TauCeti.IntegralLattice.IsUnimodular.discriminantQuadraticMap_discriminantGroupScaleEquiv_symm`.
* `TauCeti.IntegralLattice.IsUnimodular.discriminantOrthogonalGroupEquivModTwo`: the group
  isomorphism `O(q_{M(2)}) ≃* O(Q₂)` induced by `A_{M(2)} ≃ M / 2M`.
* `discriminantOrthogonalGroupEquivModTwo_discriminantOrthogonalHom_smul`: it carries the
  discriminant action of an isometry of `M`, viewed in `O(M(2))`, to its reduction modulo two.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
* V. Gritsenko and K. Hulek, *Moduli of polarized Enriques surfaces*, §2.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace IsUnimodular

/-- **The discriminant form of `M(2)` is half the quadratic form of `M / 2M`.** For an even
unimodular lattice `L`, under the identification `A_{L(2)} ≃ L / 2L` given by multiplication by two,
the discriminant quadratic form of `L(2)` is `Q₂ / 2 mod ℤ`, where `Q₂` is the quadratic form
`B(x, x) / 2 mod 2` on `L / 2L`. -/
theorem discriminantQuadraticMap_discriminantGroupScaleEquiv_symm (hu : L.IsUnimodular)
    (hL : L.IsEven) (c : QuotSMulTop (2 : ℤ) L) :
    ((2 : ℤ) • L).discriminantQuadraticMap (hL.smul 2)
        ((hu.discriminantGroupScaleEquiv two_ne_zero).symm c) =
      ZMod.toRatAddCircle 2 ((L.quadraticForm hL).reduceModTwo c) := by
  induction c using Submodule.Quotient.induction_on with
  | _ y =>
    obtain ⟨k, hk⟩ := hL.exists_norm_eq_two_mul y
    have hform : L.form y y = 2 * k := by rw [← L.norm_apply, hk]
    have hdiv : L.integralNorm y / 2 = k := by
      have : L.integralNorm y = 2 * k := by exact_mod_cast (L.integralNorm_cast y).trans hk
      omega
    rw [hu.discriminantQuadraticMap_discriminantGroupScaleEquiv_symm_mk two_ne_zero, hform,
      QuadraticForm.reduceModTwo_mk, quadraticForm_apply, hdiv, ZMod.toRatAddCircle_intCast]
    -- the remaining identity `2k / (2 * 2) = k / 2` holds already in `ℚ`
    congr 1
    push_cast
    ring

/-- The discriminant form of `L(2)` at a class `a`, read off from `Q₂` at its image in `L / 2L`. -/
private theorem discriminantQuadraticMap_eq (hu : L.IsUnimodular) (hL : L.IsEven)
    (a : ((2 : ℤ) • L).DiscriminantGroup) :
    ((2 : ℤ) • L).discriminantQuadraticMap (hL.smul 2) a =
      ZMod.toRatAddCircle 2
        ((L.quadraticForm hL).reduceModTwo (hu.discriminantGroupScaleEquiv two_ne_zero a)) := by
  rw [← hu.discriminantQuadraticMap_discriminantGroupScaleEquiv_symm hL,
    LinearEquiv.symm_apply_apply]

variable [((2 : ℤ) • L).IsNondegenerate]

/-- The identification `A_{L(2)} ≃ L / 2L`, on the carrier of the discriminant quadratic module. -/
private noncomputable def moduleEquivModTwo (hu : L.IsUnimodular) (hL : L.IsEven) :
    ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2) ≃ₗ[ℤ] QuotSMulTop (2 : ℤ) L :=
  hu.discriminantGroupScaleEquiv two_ne_zero

private theorem quadratic_eq (hu : L.IsUnimodular) (hL : L.IsEven)
    (a : ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2)) :
    (((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2)).quadratic a =
      ZMod.toRatAddCircle 2 ((L.quadraticForm hL).reduceModTwo (moduleEquivModTwo hu hL a)) :=
  (discriminantQuadraticModule_quadratic _ _ a).trans (discriminantQuadraticMap_eq hu hL a)

/-- The `ZMod 2`-linear automorphism of `L / 2L` corresponding to an automorphism of the
discriminant group of `L(2)`. -/
private noncomputable def conjModTwo (hu : L.IsUnimodular) (hL : L.IsEven)
    (σ : ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2) ≃ₗ[ℤ]
      ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2)) :
    QuotSMulTop (2 : ℤ) L ≃ₗ[ZMod 2] QuotSMulTop (2 : ℤ) L :=
  let e := (moduleEquivModTwo hu hL).symm ≪≫ₗ σ ≪≫ₗ moduleEquivModTwo hu hL
  { e with map_smul' := ZMod.map_smul e }

private theorem conjModTwo_apply (hu : L.IsUnimodular) (hL : L.IsEven)
    (σ : ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2) ≃ₗ[ℤ]
      ((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2))
    (c : QuotSMulTop (2 : ℤ) L) :
    conjModTwo hu hL σ c = moduleEquivModTwo hu hL (σ ((moduleEquivModTwo hu hL).symm c)) :=
  (rfl)

/-- **The orthogonal group of the discriminant form of `M(2)`.** For an even unimodular lattice
`L`, the identification `A_{L(2)} ≃ L / 2L` given by multiplication by two identifies the
orthogonal group of the discriminant quadratic form of `L(2)` with the orthogonal group of the
quadratic form `B(x, x) / 2 mod 2` over `ZMod 2` on `L / 2L`. -/
noncomputable def discriminantOrthogonalGroupEquivModTwo (hu : L.IsUnimodular) (hL : L.IsEven) :
    FiniteQuadraticModule.orthogonalGroup (((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2))
      ≃* QuadraticMap.orthogonalGroup (L.quadraticForm hL).reduceModTwo where
  toFun σ := ⟨conjModTwo hu hL σ, QuadraticMap.mem_orthogonalGroup_iff.mpr fun c ↦
    ZMod.toRatAddCircle_injective 2 <| by
      rw [conjModTwo_apply, ← quadratic_eq hu hL]
      simp [QuadraticMap.map_app_of_mem_orthogonalGroup σ.property, quadratic_eq hu hL]⟩
  invFun τ := ⟨moduleEquivModTwo hu hL ≪≫ₗ
      (τ : QuotSMulTop (2 : ℤ) L ≃ₗ[ZMod 2] QuotSMulTop (2 : ℤ) L).restrictScalars ℤ ≪≫ₗ
      (moduleEquivModTwo hu hL).symm,
    QuadraticMap.mem_orthogonalGroup_iff.mpr fun a ↦ by
      rw [quadratic_eq hu hL, quadratic_eq hu hL]
      simp [QuadraticMap.map_app_of_mem_orthogonalGroup τ.property]⟩
  left_inv σ := Subtype.ext <| LinearEquiv.ext fun a ↦ by
    simp [conjModTwo_apply]
  right_inv τ := Subtype.ext <| LinearEquiv.ext fun c ↦ by
    simp [conjModTwo_apply]
  map_mul' σ σ' := Subtype.ext <| LinearEquiv.ext fun c ↦ by
    simp [conjModTwo_apply]

/-- The orthogonal transformation of `L / 2L` corresponding to `σ ∈ O(q_{L(2)})` is `σ`
conjugated by the identification `A_{L(2)} ≃ L / 2L`. -/
@[simp]
theorem coe_discriminantOrthogonalGroupEquivModTwo_apply (hu : L.IsUnimodular) (hL : L.IsEven)
    (σ : FiniteQuadraticModule.orthogonalGroup
      (((2 : ℤ) • L).discriminantQuadraticModule (hL.smul 2)))
    (c : QuotSMulTop (2 : ℤ) L) :
    (hu.discriminantOrthogonalGroupEquivModTwo hL σ :
        QuotSMulTop (2 : ℤ) L ≃ₗ[ZMod 2] QuotSMulTop (2 : ℤ) L) c =
      hu.discriminantGroupScaleEquiv two_ne_zero
        (σ.val ((hu.discriminantGroupScaleEquiv two_ne_zero).symm c)) :=
  (rfl)

/-- The automorphism of the discriminant group of `L(2)` corresponding to `τ ∈ O(Q₂)` is `τ`
conjugated by the identification `A_{L(2)} ≃ L / 2L`. -/
@[simp]
theorem coe_discriminantOrthogonalGroupEquivModTwo_symm_apply (hu : L.IsUnimodular)
    (hL : L.IsEven) (τ : QuadraticMap.orthogonalGroup (L.quadraticForm hL).reduceModTwo)
    (a : ((2 : ℤ) • L).DiscriminantGroup) :
    ((hu.discriminantOrthogonalGroupEquivModTwo hL).symm τ).val a =
      (hu.discriminantGroupScaleEquiv two_ne_zero).symm
        ((τ : QuotSMulTop (2 : ℤ) L ≃ₗ[ZMod 2] QuotSMulTop (2 : ℤ) L)
          (hu.discriminantGroupScaleEquiv two_ne_zero a)) :=
  (rfl)

/-- **The discriminant action of `O(M)` on `M(2)` is reduction modulo two.** For an even
unimodular lattice `L` and an isometry `g` of `L`, viewed as an isometry of `L(2)`, the
isomorphism `O(q_{L(2)}) ≃* O(Q₂)` carries the action of `g` on the discriminant form of `L(2)` to
the reduction of `g` modulo two. -/
theorem discriminantOrthogonalGroupEquivModTwo_discriminantOrthogonalHom_smul
    (hu : L.IsUnimodular) (hL : L.IsEven) (g : Isometry L L) :
    hu.discriminantOrthogonalGroupEquivModTwo hL
        (Isometry.discriminantOrthogonalHom ((2 : ℤ) • L) (hL.smul 2) (g.smul 2)) =
      Isometry.reductionModTwoHom hL g :=
  Subtype.ext <| LinearEquiv.ext fun c ↦ by
    rw [coe_discriminantOrthogonalGroupEquivModTwo_apply, Isometry.coe_reductionModTwoHom_apply]
    -- `coe_discriminantOrthogonalHom` is stated on the carrier of the discriminant quadratic
    -- module, which `rw` does not identify with `DiscriminantGroup`; apply it by `congrArg`.
    exact (congrArg (fun f ↦ hu.discriminantGroupScaleEquiv two_ne_zero
        (f ((hu.discriminantGroupScaleEquiv two_ne_zero).symm c)))
        (Isometry.coe_discriminantOrthogonalHom (hL.smul 2) (g.smul 2))).trans <|
      (g.discriminantGroupScaleEquiv_discriminantGroupHom_smul hu two_ne_zero _).trans
        (congrArg _ (LinearEquiv.apply_symm_apply _ c))

end IsUnimodular

end TauCeti.IntegralLattice
