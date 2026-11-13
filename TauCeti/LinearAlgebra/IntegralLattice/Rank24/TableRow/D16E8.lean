/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Plus

/-!
# Explicit carriers for the `D₁₆ E₈` table lattice

The second Conway--Sloane row adjoins the spinor of its `D₁₆` component and does
not enlarge its `E₈` component. We identify the actual decoded table generator
`[10]` with this vector in the dual of the orthogonal root lattice. The table
lattice is exactly the union of that root lattice and its spinor translate.

In checkerboard coordinates on the first component and simple-root coordinates
on the second, membership is therefore membership in `D₁₆⁺` and integrality of
the eight remaining coordinates. The spinor has norm four and, together with
the simple roots, generates the table lattice. The decoding argument
follows the `D₂₄` comparison by the Tau Ceti contributors in
`TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.D24`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  3rd ed., Chapter 4 §8.1 and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

open IntegralLattice DynkinType

/-- The spinor glue vector of the `D₁₆ E₈` row, in its original simple-root
coordinates: the inverse image of `(1/2, …, 1/2)` on `D₁₆`, and zero on `E₈`. -/
noncomputable def d16e8GlueVector :
    ∀ i, Fin (RootfulNiemeierType.d16e8.componentType i).rank → ℚ :=
  Fin.cons
    ((rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)).symm
      (checkerboardSpinor 16)) (Fin.cons 0 finZeroElim)

/-- The first component of the glue vector is the checkerboard spinor. -/
@[simp]
theorem d16e8GlueVector_zero :
    d16e8GlueVector ⟨0, by decide⟩ =
      (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)).symm
        (checkerboardSpinor 16) := (rfl)

/-- The second component of the glue vector vanishes. -/
@[simp]
theorem d16e8GlueVector_one : d16e8GlueVector ⟨1, by decide⟩ = 0 := (rfl)

/-- The explicit spinor vector lies in the dual of the table root lattice. -/
theorem d16e8GlueVector_mem_dualCarrier :
    d16e8GlueVector ∈ RootfulNiemeierType.d16e8.rootLattice.dualCarrier := by
  rw [mem_dualCarrier_pi_iff]
  intro i
  fin_cases i
  · rw [d16e8GlueVector_zero]
    exact (Isometry.apply_mem_dualCarrier_iff
      (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)).symm _).mpr
        checkerboardSpinor_mem_dualCarrier
  · rw [d16e8GlueVector_one]
    exact zero_mem _

private noncomputable def spinorWord : RootfulNiemeierType.d16e8.glueModule :=
  fun i ↦ (RootfulNiemeierType.d16e8.componentType i).glueLabelEquiv
    (RootfulNiemeierType.d16e8.isSimplyLaced_componentType i)
      ⟨if i.val = 0 then 1 else 0, by fin_cases i <;> decide⟩

private theorem encode_spinorWord :
    encodeGlueWord RootfulNiemeierType.d16e8.componentType
      RootfulNiemeierType.d16e8.isSimplyLaced_componentType spinorWord = [1, 0] := by
  rw [encodeGlueWord_def]
  simp only [spinorWord, Equiv.symm_apply_apply]
  -- `List.ofFn` evaluates the two digits at the table's component positions.
  rfl

private theorem spinorWord_one : spinorWord ⟨1, by decide⟩ = 0 :=
  glueLabelEquiv_zero _ _

private theorem glueGenerators_d16e8 :
    RootfulNiemeierType.d16e8.glueGenerators = {spinorWord} :=
  RootfulNiemeierType.d16e8.glueGenerators_eq_singleton (by decide) encode_spinorWord

private theorem glueSubgroup_d16e8 :
    RootfulNiemeierType.d16e8.glueSubgroup = AddSubgroup.zmultiples spinorWord :=
  RootfulNiemeierType.d16e8.glueSubgroup_eq_zmultiples (by decide) encode_spinorWord

private theorem spinorWord_zero_class :
    (D 16).glueAlphabetIsometry (by decide) (isSimplyLaced_D 16) (spinorWord ⟨0, by decide⟩) =
      (rootLatticeIsometryCheckerboard 16 (by decide)
        (isSimplyLaced_D 16)).discriminantGroupEquiv.symm (checkerboardSpinorClass 16) := by
  -- Unfolding the table component at zero identifies `spinorWord` with label 1 of D₁₆.
  exact glueAlphabetIsometry_glueLabelEquiv_one_D_of_even
    16 (by decide) (isSimplyLaced_D 16) (by decide)

private theorem glueVector_class :
    (Submodule.Quotient.mk ⟨d16e8GlueVector, d16e8GlueVector_mem_dualCarrier⟩ :
      RootfulNiemeierType.d16e8.rootLattice.DiscriminantGroup) =
    glueWordIsometry RootfulNiemeierType.d16e8.componentType
      RootfulNiemeierType.d16e8.isSimplyLaced_componentType
      RootfulNiemeierType.d16e8.valid_componentType spinorWord := by
  apply (discriminantGroupPiEquiv _).injective
  funext i
  rw [discriminantGroupPiEquiv_mk, discriminantGroupPiEquiv_glueWordIsometry]
  fin_cases i
  · -- Identify the component at zero with D₁₆ before using its class formula.
    erw [spinorWord_zero_class, ← Isometry.discriminantGroupEquiv_symm,
      checkerboardSpinorClass_def, Isometry.discriminantGroupEquiv_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (by
      simp only [coe_piDualCarrierEquiv_apply, Isometry.coe_dualCarrierEquiv_apply,
        d16e8GlueVector_zero]
      -- The inverse dual-carrier map and inverse ambient isometry have the same function.
      rfl))
  · rw [spinorWord_one, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by
      simp only [mem_carrierInDual_iff, coe_piDualCarrierEquiv_apply,
        d16e8GlueVector_one]
      exact zero_mem _)

/-- The table's decoded subgroup `[10]`, in the actual discriminant group of
`D₁₆ ⊥ E₈`, is generated by the class of the explicit spinor vector. -/
theorem map_glueSubgroup_d16e8_eq_zmultiples :
    RootfulNiemeierType.d16e8.glueSubgroup.map
      (glueWordIsometry RootfulNiemeierType.d16e8.componentType
        RootfulNiemeierType.d16e8.isSimplyLaced_componentType
        RootfulNiemeierType.d16e8.valid_componentType).toAddEquiv.toAddMonoidHom =
      AddSubgroup.zmultiples (Submodule.Quotient.mk
        ⟨d16e8GlueVector, d16e8GlueVector_mem_dualCarrier⟩ :
          RootfulNiemeierType.d16e8.rootLattice.DiscriminantGroup) := by
  rw [glueSubgroup_d16e8, AddMonoidHom.map_zmultiples, glueVector_class]
  -- The additive-hom coercion of `glueWordIsometry` evaluates as the isometry itself.
  rfl

private theorem two_nsmul_glueVector_class :
    2 • (Submodule.Quotient.mk
      ⟨d16e8GlueVector, d16e8GlueVector_mem_dualCarrier⟩ :
        RootfulNiemeierType.d16e8.rootLattice.DiscriminantGroup) = 0 := by
  -- The quadratic-module carrier is the discriminant group, but this identification
  -- is not exposed to rewriting at the default transparency.
  erw [glueVector_class, ← map_nsmul]
  suffices 2 • spinorWord = 0 by
    erw [this, map_zero]
    -- Zero in the discriminant quadratic module is zero in its underlying discriminant group.
    rfl
  funext i
  fin_cases i
  · apply ((D 16).glueAlphabetIsometry (by decide) (isSimplyLaced_D 16)).injective
    simp only [Pi.smul_apply]
    -- `erw` identifies the table component's alphabet with D₁₆ and its quadratic-module
    -- carrier with the discriminant group, so nsmul passes through both isometries.
    erw [map_nsmul, map_zero, spinorWord_zero_class, ← map_nsmul]
    -- Both twice-actions are addition to itself; the available spinor-order lemma uses ℤ.
    erw [two_nsmul, ← two_zsmul, two_zsmul_checkerboardSpinorClass_of_even 16 (by decide),
      map_zero]
    -- The alphabet isometry sends zero to discriminant-group zero definitionally.
    rfl
  · simp only [Pi.smul_apply, spinorWord_one, smul_zero]
    -- Pi zero evaluates to zero in the table's E₈ alphabet.
    rfl

/-- The literal two-coset carrier of the table lattice `D₁₆ E₈`. -/
theorem mem_niemeierD16E8_carrier_iff
    (x : ∀ i, Fin (RootfulNiemeierType.d16e8.componentType i).rank → ℚ) :
    x ∈ niemeierD16E8.carrier ↔
      x ∈ RootfulNiemeierType.d16e8.rootLattice.carrier ∨
        x - d16e8GlueVector ∈ RootfulNiemeierType.d16e8.rootLattice.carrier := by
  rw [niemeierD16E8, RootfulNiemeierType.lattice_def, gluedLattice_def]
  -- The gluing definition uses the quadratic-module carrier for its subgroup,
  -- whereas the inverse-image API uses the definitionally equal discriminant group.
  erw [ofIsotropicSubgroup_carrier, map_glueSubgroup_d16e8_eq_zmultiples]
  exact mem_intermediateCarrierOfDiscriminantSubgroup_zmultiples_iff _
    d16e8GlueVector_mem_dualCarrier two_nsmul_glueVector_class x

/-- The spinor glue vector belongs to the actual table lattice. -/
@[simp]
theorem d16e8GlueVector_mem_niemeierD16E8_carrier :
    d16e8GlueVector ∈ niemeierD16E8.carrier := by
  rw [mem_niemeierD16E8_carrier_iff]
  exact Or.inr (by simpa only [sub_self] using
    RootfulNiemeierType.d16e8.rootLattice.carrier.zero_mem)

/-- The root lattice and the single explicit spinor vector generate the
`D₁₆ E₈` table lattice over the integers. -/
theorem niemeierD16E8_carrier_eq_sup_span :
    niemeierD16E8.carrier = RootfulNiemeierType.d16e8.rootLattice.carrier ⊔
      Submodule.span ℤ {d16e8GlueVector} := by
  refine (RootfulNiemeierType.d16e8.lattice_carrier_eq_sup_span
    (fun _ ↦ ⟨d16e8GlueVector, d16e8GlueVector_mem_dualCarrier⟩) ?_).trans ?_
  · intro w hw
    rw [glueGenerators_d16e8, Set.mem_singleton_iff] at hw
    subst w
    exact glueVector_class
  · rw [glueGenerators_d16e8, Set.image_singleton]

/-- In checkerboard coordinates on `D₁₆` and simple-root coordinates on `E₈`,
the table lattice consists exactly of `D₁₆⁺` and eight integral coordinates. -/
theorem mem_niemeierD16E8_carrier_iff_checkerboard
    (x : ∀ i, Fin (RootfulNiemeierType.d16e8.componentType i).rank → ℚ) :
    x ∈ niemeierD16E8.carrier ↔
      (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)) (x ⟨0, by decide⟩) ∈
        (checkerboardPlusCarrier 16).1 ∧
        ∀ j, ∃ z : ℤ, (z : ℚ) = x ⟨1, by decide⟩ j := by
  rw [mem_niemeierD16E8_carrier_iff]
  have hmem (y : ∀ i, Fin (RootfulNiemeierType.d16e8.componentType i).rank → ℚ) :
      y ∈ RootfulNiemeierType.d16e8.rootLattice.carrier ↔
        y ⟨0, by decide⟩ ∈ ((D 16).rootLattice (isSimplyLaced_D 16)).carrier ∧
        y ⟨1, by decide⟩ ∈ (E8.rootLattice (isSimplyLaced_E8)).carrier :=
    (mem_pi_carrier_iff _ _).trans Fin.forall_fin_two
  simp only [hmem, Pi.sub_apply, d16e8GlueVector_zero, d16e8GlueVector_one, sub_zero]
  -- The explicit indices require the same table-to-component conversion as above.
  erw [← Isometry.apply_mem_carrier_iff
      (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)),
    ← (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)).apply_mem_carrier_iff,
    map_sub, Isometry.apply_symm_apply,
    checkerboardLattice_carrier, mem_rootLattice_carrier_iff,
    mem_checkerboardPlusCarrier_iff 16 (by decide), checkerboardLattice_carrier]
  exact or_and_right.symm

/-- The adjoined table glue vector has squared norm four. -/
theorem form_d16e8GlueVector_self :
    niemeierD16E8.form d16e8GlueVector d16e8GlueVector = 4 := by
  rw [RootfulNiemeierType.lattice_form]
  have hsum : RootfulNiemeierType.d16e8.rootLattice.form d16e8GlueVector d16e8GlueVector =
      ((D 16).rootLattice (isSimplyLaced_D 16)).form
        (d16e8GlueVector ⟨0, by decide⟩) (d16e8GlueVector ⟨0, by decide⟩) +
      (E8.rootLattice isSimplyLaced_E8).form
        (d16e8GlueVector ⟨1, by decide⟩) (d16e8GlueVector ⟨1, by decide⟩) := by
    rw [pi_form]
    exact (piForm_apply _ d16e8GlueVector d16e8GlueVector).trans (Fin.sum_univ_two _)
  rw [hsum, d16e8GlueVector_zero, d16e8GlueVector_one]
  -- The zero vector in the E₈ summand still has its table component type.
  erw [map_zero, add_zero]
  rw [← (rootLatticeIsometryCheckerboard 16 (by decide) (isSimplyLaced_D 16)).map_app,
    Isometry.apply_symm_apply,
    checkerboardLattice_form_checkerboardSpinor_self]
  norm_num

end TauCeti
