/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Unitary
public import TauCeti.NumberTheory.BinaryQuadraticForm.QuadraticMap
public import TauCeti.NumberTheory.BinaryQuadraticForm.Stabilizer
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.NumberTheory.IntegralLattice.Localization.Stabilizer

/-!
# The norm-one torus of a binary lattice and its local points

Let `L` be an integral lattice of rank two with nonzero form, let `Δ` be the discriminant of its
primitive norm form (`TauCeti.IntegralLattice.binaryDiscriminant`), and let
`𝒪 = ℤ[ω]/(ω² - Δ ω + (Δ² - Δ)/4)` be the quadratic order of discriminant `Δ`, written
`QuadraticAlgebra ℤ ((Δ - Δ²)/4) Δ`. For a commutative ring `R`, the norm-one elements of
`R ⊗ 𝒪 = QuadraticAlgebra R ((Δ - Δ²)/4) Δ`, which are its unitary elements, form the group
`T_L(R)` of `R`-points of the norm-one group of `𝒪`. Over a `ℚ`-algebra these are, for nonsquare
`Δ`, the points of the norm-one torus of the quadratic field `ℚ(√Δ)`, and for nonzero square `Δ`
those of the split torus. A ring homomorphism `R → S` maps `T_L(R)` to `T_L(S)` coefficientwise
(`QuadraticAlgebra.unitaryMap`); for the inclusions `ℤ_p → ℚ_p` and `ℚ → ℚ_p` this map is
injective.

This file identifies the special orthogonal groups of `L` over rings with points of `T_L`:

* over every `ℚ`-algebra `A`, the proper isometries of the base change to `A ⊗ V` of the rational
  norm form of `L` form a group isomorphic to `T_L(A)`
  (`TauCeti.IntegralLattice.specialOrthogonalGroupBaseChangeEquivUnitary`); this covers
  `SO(ℚ ⊗ V) ≅ T_L(ℚ)`, `SO(V_p) ≅ T_L(ℚ_p)` and `SO(ℝ ⊗ V) ≅ T_L(ℝ)`;
* at a prime `p`, the proper isometries of `V_p` preserving the localization `L_p`, which form the
  proper local stabilizer `K_p⁺(L)`, are those whose norm-one elements have coordinates in `ℤ_p`
  (`TauCeti.IntegralLattice.specialOrthogonalToOrthogonal_mem_localStabilizer_iff_mem_range`).
  They form a group isomorphic to `T_L(ℤ_p)`, compatibly with the inclusion
  `T_L(ℤ_p) → T_L(ℚ_p)` (`TauCeti.IntegralLattice.localStabilizerSpecialOrthogonalEquivUnitary`).

The identifications depend on a carrier basis `b` of `L`, through conjugation. They are the
rank-two computation `SO(Q) ≅ Stab_{SL(2)}(f)` of the special orthogonal group of a binary
quadratic space (`QuadraticMap.specialOrthogonalGroupEquivStabilizer`), applied to the norm form
of `L` read over `A`, followed by the description of the automorphs of a primitive binary form by
norm-one elements (`TauCeti.BinaryQuadraticForm.stabilizerEquivUnitary`). Over a `ℚ`-algebra the
content of the norm form is a unit, so the norm form and its primitive part have the same
automorphs; over `ℤ_p` the content may be divisible by `p`, and the integrality of the automorph
of a norm-one element is read off its coordinates
(`TauCeti.BinaryQuadraticForm.forall_coe_stabilizerEquivUnitary_symm_apply_mem_iff`). Together
with `TauCeti.IntegralLattice.specialOrthogonalGroupEquivNormOneUnits` for `SO(L) ≅ T_L(ℤ)`, these
identify the local stabilizers and local groups entering the adelic double cosets of the genus of
a binary lattice with the local points of `T_L`.

## Main definitions

* `TauCeti.IntegralLattice.specialOrthogonalGroupBaseChangeEquivUnitary`: `SO(A ⊗ V) ≅ T_L(A)`.
* `TauCeti.IntegralLattice.localStabilizerSpecialOrthogonalEquivUnitary`: `K_p⁺(L) ≅ T_L(ℤ_p)`.

## Main results

* `TauCeti.IntegralLattice.toBinaryQuadraticForm_norm_baseChange`: the binary form of the norm of
  `A ⊗ V` in the basis of `b` is the binary norm form of `b` read in `A`.
* `TauCeti.IntegralLattice.specialOrthogonalToOrthogonal_mem_localStabilizer_iff_mem_range`:
  a proper isometry of `V_p` preserves `L_p` exactly when its norm-one element has coordinates
  in `ℤ_p`.
* `TauCeti.IntegralLattice.unitaryMap_localStabilizerSpecialOrthogonalEquivUnitary`: the two
  identifications are compatible with `T_L(ℤ_p) → T_L(ℚ_p)`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13.
* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §§101–102.
-/

public section

open Module MulAction QuadraticAlgebra
open scoped TensorProduct MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
variable (b : Basis (Fin 2) ℤ L) (hV : Module.finrank ℚ V = 2)

section BaseChange

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- In the basis of `A ⊗ V` given by a carrier basis `b`, the binary form of the base change of the
rational norm form of `L` is the binary norm form of `b`, read in `A`. -/
theorem toBinaryQuadraticForm_norm_baseChange :
    (L.norm.baseChange A).toBinaryQuadraticForm ((b.extendOfIsFullLattice ℚ).baseChange A) =
      (L.binaryNormForm b).map (Int.castRingHom A) := by
  have hcast (q : ℤ) : ((q : ℚ) • (1 : A)) = (q : A) := by
    rw [Algebra.smul_def, mul_one, map_intCast]
  have hn (x : L) : (L.norm.baseChange A) (1 ⊗ₜ[ℚ] (x : V)) = ((L.integralNorm x : ℤ) : A) := by
    rw [QuadraticForm.baseChange_tmul, mul_one, ← integralNorm_cast, hcast]
  ext <;> simp only [QuadraticMap.toBinaryQuadraticForm_a, QuadraticMap.toBinaryQuadraticForm_b,
    QuadraticMap.toBinaryQuadraticForm_c, Basis.baseChange_apply, Basis.extendOfIsFullLattice_apply,
    QuadraticMap.polar, ← TensorProduct.tmul_add, ← Submodule.coe_add, hn,
    BinaryQuadraticForm.map_a, BinaryQuadraticForm.map_b, BinaryQuadraticForm.map_c,
    binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, gramMatrix_apply, integralNorm_add,
    eq_intCast] <;>
    simp only [integralNorm_apply]
  push_cast
  ring

/-- Over a `ℚ`-algebra, the binary norm form of `b` and its primitive part have the same
automorphs: they differ by the content, which is a nonzero integer and hence a unit. -/
private theorem stabilizer_map_binaryNormForm (hL : L.form ≠ 0) :
    stabilizer SL(2, A) ((L.binaryNormForm b).map (Int.castRingHom A)) =
      stabilizer SL(2, A) ((L.binaryNormForm b).primPart.map (Int.castRingHom A)) := by
  set f := L.binaryNormForm b
  have hc : IsUnit ((f.content : ℤ) : A) := by
    rw [← map_intCast (algebraMap ℚ A)]
    refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
    exact_mod_cast (content_binaryNormForm_pos L b hL).ne'
  have hmap : f.map (Int.castRingHom A) =
      ((f.content : ℤ) : A) • f.primPart.map (Int.castRingHom A) := by
    conv_lhs => rw [← f.content_smul_primPart]
    ext <;> simp only [BinaryQuadraticForm.map_a, BinaryQuadraticForm.map_b,
      BinaryQuadraticForm.map_c, BinaryQuadraticForm.smul_a', BinaryQuadraticForm.smul_b',
      BinaryQuadraticForm.smul_c', nsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul,
      Int.cast_natCast]
  have : SMulCommClass SL(2, A) A (BinaryQuadraticForm A) := SMulCommClass.symm _ _ _
  rw [hmap, ← hc.unit_spec, ← Units.smul_def, stabilizer_smul_eq_right]

/-- **The special orthogonal group of a binary lattice over a `ℚ`-algebra.** For a rank-two
lattice `L` with nonzero form and a `ℚ`-algebra `A`, the proper isometries of the base change to
`A ⊗ V` of the rational norm form of `L` form a group isomorphic to `T_L(A)`, the norm-one elements
of the quadratic order of discriminant `Δ = binaryDiscriminant L` with coefficients in `A`. A
proper isometry corresponds to the norm-one element whose regular representation, in the basis of
`A ⊗ V` given by the carrier basis `b`, is its matrix. -/
noncomputable def specialOrthogonalGroupBaseChangeEquivUnitary (hL : L.form ≠ 0) :
    QuadraticMap.specialOrthogonalGroup (L.norm.baseChange A) ≃*
      unitary (QuadraticAlgebra A
        (((L.binaryDiscriminant hV - L.binaryDiscriminant hV ^ 2) / 4 : ℤ) : A)
        (L.binaryDiscriminant hV)) :=
  (QuadraticMap.specialOrthogonalGroupEquivStabilizer _
      ((b.extendOfIsFullLattice ℚ).baseChange A)).trans <|
    (MulEquiv.subgroupCongr ((congrArg (stabilizer SL(2, A))
      (toBinaryQuadraticForm_norm_baseChange b A)).trans
        (stabilizer_map_binaryNormForm b A hL))).trans <|
      BinaryQuadraticForm.stabilizerEquivUnitary
        (L.isPrimitive_binaryNormForm_primPart b hL).span_intCast_eq_top
        (L.binaryDiscriminant_eq_discrim_primPart b hV).symm
        -- `2` is a unit in a `ℚ`-algebra, so it is not a zero divisor.
        (by simpa only [map_ofNat] using
          ((IsUnit.mk0 (2 : ℚ) two_ne_zero).map (algebraMap ℚ A)).isRegular.left)

/-- The matrix, in the basis of `A ⊗ V` given by `b`, of a proper isometry is the automorph of the
primitive norm form attached to its norm-one element. -/
theorem coe_stabilizerEquivUnitary_symm_specialOrthogonalGroupBaseChangeEquivUnitary
    (hL : L.form ≠ 0) (h2 : IsLeftRegular (2 : A))
    (g : QuadraticMap.specialOrthogonalGroup (L.norm.baseChange A)) :
    (((BinaryQuadraticForm.stabilizerEquivUnitary
        (L.isPrimitive_binaryNormForm_primPart b hL).span_intCast_eq_top
        (L.binaryDiscriminant_eq_discrim_primPart b hV).symm h2).symm
          (specialOrthogonalGroupBaseChangeEquivUnitary b hV A hL g) : SL(2, A)) :
        Matrix (Fin 2) (Fin 2) A) =
      LinearMap.toMatrix ((b.extendOfIsFullLattice ℚ).baseChange A)
        ((b.extendOfIsFullLattice ℚ).baseChange A) (g : A ⊗[ℚ] V ≃ₗ[A] A ⊗[ℚ] V).toLinearMap := by
  rw [specialOrthogonalGroupBaseChangeEquivUnitary, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.subgroupCongr_apply,
    QuadraticMap.coe_specialOrthogonalGroupEquivStabilizer_apply]

end BaseChange

section Local

variable (p : ℕ) [Fact p.Prime]

/-- **Integral proper isometries are integral norm-one elements.** A proper isometry of `V_p`
preserves the localization `L_p`, that is, lies in the local stabilizer `K_p(L)`, exactly when both
coordinates of its norm-one element are `p`-adic integers. -/
theorem specialOrthogonalToOrthogonal_mem_localStabilizer_iff (hL : L.form ≠ 0)
    (g : QuadraticMap.specialOrthogonalGroup (L.norm.baseChange ℚ_[p])) :
    QuadraticMap.specialOrthogonalToOrthogonal _ g ∈ L.localStabilizer p ↔
      ((specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL g).val.re ∈ PadicInt.subring p ∧
        (specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL g).val.im ∈
          PadicInt.subring p) := by
  set e := specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL
  set S := PadicInt.subring p
  have hmat (h : QuadraticMap.specialOrthogonalGroup (L.norm.baseChange ℚ_[p])) :
      (∀ i j, LinearMap.toMatrix ((b.extendOfIsFullLattice ℚ).baseChange ℚ_[p])
        ((b.extendOfIsFullLattice ℚ).baseChange ℚ_[p])
          (h : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V).toLinearMap i j ∈ S) ↔
        (e h).val.re ∈ S ∧ (e h).val.im ∈ S := by
    rw [← coe_stabilizerEquivUnitary_symm_specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p]
      hL ((IsUnit.mk0 (2 : ℚ_[p]) two_ne_zero).isRegular.left)]
    exact BinaryQuadraticForm.forall_coe_stabilizerEquivUnitary_symm_apply_mem_iff
      (L.isPrimitive_binaryNormForm_primPart b hL) _ _ S (e h)
  have hinv : ((QuadraticMap.specialOrthogonalToOrthogonal _ g :
      QuadraticMap.orthogonalGroup (L.norm.baseChange ℚ_[p])) :
        ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V)⁻¹ = ((g⁻¹ : QuadraticMap.specialOrthogonalGroup _) :
          ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) := by
    rw [QuadraticMap.coe_specialOrthogonalToOrthogonal, Subgroup.coe_inv]
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p b,
    QuadraticMap.mem_integralOrthogonalSubgroup_iff, hinv,
    QuadraticMap.coe_specialOrthogonalToOrthogonal, hmat, hmat, map_inv,
    ← Unitary.star_eq_inv, Unitary.coe_star, re_star, im_star]
  -- The conjugate `x + Δ y - y ω` of `x + y ω` has integral coordinates when `x + y ω` does.
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_, S.neg_mem h.2⟩⟩
  exact S.add_mem h.1 (S.mul_mem (intCast_mem S _) h.2)

/-- **The proper local stabilizer consists of the `ℤ_p`-points.** A proper isometry of `V_p`
preserves `L_p` exactly when its norm-one element comes from a norm-one element of the order with
coefficients in `ℤ_p`. -/
theorem specialOrthogonalToOrthogonal_mem_localStabilizer_iff_mem_range
    (hL : L.form ≠ 0) (g : QuadraticMap.specialOrthogonalGroup (L.norm.baseChange ℚ_[p])) :
    QuadraticMap.specialOrthogonalToOrthogonal _ g ∈ L.localStabilizer p ↔
      specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL g ∈
        (unitaryMap PadicInt.Coe.ringHom (map_intCast _ _)
          (map_intCast _ _)).range := by
  have hrange : (PadicInt.Coe.ringHom (p := p)).range = PadicInt.subring p :=
    Subring.range_subtype _
  rw [specialOrthogonalToOrthogonal_mem_localStabilizer_iff,
    mem_range_unitaryMap_iff Subtype.coe_injective, hrange]

/-- The image of the proper local stabilizer `K_p⁺(L)` under `SO(V_p) ≅ T_L(ℚ_p)` is the image of
`T_L(ℤ_p)`. -/
private theorem map_localStabilizer_comap (hL : L.form ≠ 0) :
    ((L.localStabilizer p).comap (QuadraticMap.specialOrthogonalToOrthogonal _)).map
        (MonoidHom.ofClass (specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL)) =
      (unitaryMap PadicInt.Coe.ringHom (map_intCast _ _)
        (map_intCast _ _)).range := by
  ext z
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, Subgroup.mem_comap,
    specialOrthogonalToOrthogonal_mem_localStabilizer_iff_mem_range b hV p hL,
    MulEquiv.apply_symm_apply]

/-- **The proper local stabilizer of a binary lattice.** For a rank-two lattice `L` with nonzero
form and a prime `p`, the proper isometries of `V_p` preserving `L_p` form a group isomorphic to
`T_L(ℤ_p)`, the norm-one elements of the quadratic order of discriminant `binaryDiscriminant L`
with coefficients in `ℤ_p`. It is the restriction of `SO(V_p) ≅ T_L(ℚ_p)`
(`TauCeti.IntegralLattice.unitaryMap_localStabilizerSpecialOrthogonalEquivUnitary`). -/
noncomputable def localStabilizerSpecialOrthogonalEquivUnitary (hL : L.form ≠ 0) :
    (L.localStabilizer p).comap (QuadraticMap.specialOrthogonalToOrthogonal _) ≃*
      unitary (QuadraticAlgebra ℤ_[p]
        (((L.binaryDiscriminant hV - L.binaryDiscriminant hV ^ 2) / 4 : ℤ) : ℤ_[p])
        (L.binaryDiscriminant hV)) :=
  ((specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL).subgroupMap _).trans <|
    (MulEquiv.subgroupCongr (map_localStabilizer_comap b hV p hL)).trans <|
      (MonoidHom.ofInjective (unitaryMap_injective (f := PadicInt.Coe.ringHom (p := p))
        Subtype.coe_injective _ _)).symm

/-- The identification `K_p⁺(L) ≅ T_L(ℤ_p)`, followed by `T_L(ℤ_p) → T_L(ℚ_p)`, is the
restriction of `SO(V_p) ≅ T_L(ℚ_p)` to `K_p⁺(L)`. -/
@[simp]
theorem unitaryMap_localStabilizerSpecialOrthogonalEquivUnitary (hL : L.form ≠ 0)
    (k : (L.localStabilizer p).comap (QuadraticMap.specialOrthogonalToOrthogonal _)) :
    unitaryMap PadicInt.Coe.ringHom (map_intCast _ _) (map_intCast _ _)
        (localStabilizerSpecialOrthogonalEquivUnitary b hV p hL k) =
      specialOrthogonalGroupBaseChangeEquivUnitary b hV ℚ_[p] hL k := by
  simp only [localStabilizerSpecialOrthogonalEquivUnitary, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

end Local

end TauCeti.IntegralLattice
