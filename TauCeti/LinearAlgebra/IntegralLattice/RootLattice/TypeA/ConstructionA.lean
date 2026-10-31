/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.CoordinateDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum

/-!
# Binary Construction A in simple-root coordinates

The orthogonal sum of copies of `A₁` has form `2 ∑ xᵢ yᵢ` in simple-root
coordinates. Multiplying each coordinate by two identifies it with the zero-code
Construction A lattice, whose carrier is `2 ℤ^ι` and whose form is the halved dot product.
The induced discriminant map identifies the `A₁` glue labels with binary coordinates.
This comparison lets binary code gluing be read in either lattice model.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  Chapter 4 §3 and Chapter 7 §6.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

variable (ι : Type*) [Fintype ι]

private def a1DoublingEquiv : (ι → Fin 1 → ℚ) ≃ₗ[ℚ] (ι → ℚ) where
  toFun x i := 2 * x i 0
  invFun y i _ := y i / 2
  left_inv x := by ext i j; fin_cases j; simp
  right_inv y := by ext i; dsimp; ring
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

private noncomputable def a1SimpleZeroIsometry :
    IntegralLattice.Isometry (pi fun _ : ι ↦ typeARootLattice 1)
      (ConstructionA.zeroLattice 2 ι) where
  toIsometryEquiv :=
    { a1DoublingEquiv ι with
      map_app' := by
        intro x y
        rw [ConstructionA.zeroLattice_form, ConstructionA.form_apply, pi_form, piForm_apply]
        simp only [dotProduct, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [typeARootLattice_form_apply]
        simp [CartanMatrix.A, a1DoublingEquiv]
        ring }
  map_carrier := by
    ext y
    rw [Submodule.mem_map_equiv, mem_pi_carrier_iff, ConstructionA.zeroLattice_carrier,
      ConstructionA.mem_lattice]
    simp only [AddSubgroup.mem_bot]
    constructor
    · intro h
      have h' (i : ι) := (mem_typeARootLattice_carrier_iff 1 _).mp (h i) 0
      choose z hz using h'
      refine ⟨fun i ↦ 2 * z i, ?_, ?_⟩
      · ext i
        simp [show (2 : ZMod 2) = 0 from rfl]
      · ext i
        have hi := hz i
        -- The inverse ambient map divides the sole simple-root coordinate by two.
        change (z i : ℚ) = y i / 2 at hi
        push_cast
        linarith
    · rintro ⟨z, hz, rfl⟩ i
      apply (mem_typeARootLattice_carrier_iff 1 _).mpr
      intro j
      have hzi : (z i : ZMod 2) = 0 := congrFun hz i
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzi
      refine ⟨k, ?_⟩
      -- Evaluation of the inverse ambient map is division by two, at every Fin 1 index.
      change (k : ℚ) = (z i : ℚ) / 2
      rw [hk]
      push_cast
      ring

/-- Doubling simple-root coordinates identifies an orthogonal sum of `A₁` root lattices
with the zero-code binary Construction A lattice. -/
noncomputable def a1ZeroLatticeIsometry :
    IntegralLattice.Isometry (pi fun _ : ι ↦ (A 1).rootLattice (isSimplyLaced_A 1))
      (ConstructionA.zeroLattice 2 ι) :=
  (Isometry.pi fun _ ↦ Isometry.ofEq (rootLattice_A 1 (isSimplyLaced_A 1))).trans
    (a1SimpleZeroIsometry ι)

/-- The base-lattice comparison doubles the unique coordinate of each `A₁` component. -/
-- Not a simp lemma: `rank_A` first normalizes the ambient index type.
theorem a1ZeroLatticeIsometry_apply (x : ι → Fin 1 → ℚ) (i : ι) :
    a1ZeroLatticeIsometry ι x i = 2 * x i 0 := by
  erw [a1ZeroLatticeIsometry, Isometry.trans_apply]
  -- The local doubling map evaluates at the componentwise identity comparison.
  calc
    _ = 2 * ((Isometry.pi fun _ : ι ↦
        Isometry.ofEq (rootLattice_A 1 (isSimplyLaced_A 1))) x i) ⟨0, by decide⟩ := rfl
    _ = 2 * x i 0 := congrArg (fun z : Fin 1 → ℚ ↦ 2 * z 0)
      ((Isometry.pi_apply _ x i).trans (Isometry.ofEq_apply _ (x i)))

private noncomputable def a1WordRepresentative
    (w : ι → (A 1).glueAlphabet (isSimplyLaced_A 1)) :
    (pi fun _ : ι ↦ (A 1).rootLattice (isSimplyLaced_A 1)).dualCarrier :=
  (piDualCarrierEquiv _).symm fun i ↦
    (Isometry.ofEq (rootLattice_A 1 (isSimplyLaced_A 1)).symm).dualCarrierEquiv
      (ZMod.val (n := 2) (w i) • typeAFundamentalWeightDual 1)

private theorem mk_a1WordRepresentative
    (w : ι → (A 1).glueAlphabet (isSimplyLaced_A 1)) :
    Submodule.Quotient.mk (a1WordRepresentative ι w) =
      glueWordIsometry (fun _ : ι ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
        (fun _ ↦ by decide) w := by
  apply (discriminantGroupPiEquiv _).injective
  ext i
  erw [discriminantGroupPiEquiv_mk,
    discriminantGroupPiEquiv_glueWordIsometry, glueAlphabetIsometry_A_apply,
    typeADiscriminantGroupEquiv_apply]
  unfold a1WordRepresentative
  erw [LinearEquiv.apply_symm_apply]
  exact (Isometry.discriminantGroupEquiv_mk _ _).symm.trans
    (congrArg _ ((Submodule.Quotient.mk_smul _ _ _).trans
      (congrArg _ (mk_typeAFundamentalWeightDual 1))))

private theorem a1ZeroLatticeIsometry_a1WordRepresentative
    (w : ι → (A 1).glueAlphabet (isSimplyLaced_A 1)) :
    a1ZeroLatticeIsometry ι (a1WordRepresentative ι w) = fun i ↦ (ZMod.val (n := 2) (w i) : ℚ) := by
  ext i
  erw [a1ZeroLatticeIsometry_apply]
  unfold a1WordRepresentative
  erw [coe_piDualCarrierEquiv_symm_apply]
  dsimp only
  have hc := Isometry.coe_dualCarrierEquiv_apply
    (Isometry.ofEq (rootLattice_A 1 (isSimplyLaced_A 1)).symm)
    (ZMod.val (n := 2) (w i) • typeAFundamentalWeightDual 1)
  have hc' := hc.trans (Isometry.ofEq_apply _ _)
  have hv := congrArg (fun z : Fin 1 → ℚ ↦ 2 * z 0) hc'
  exact hv.trans (by simp [typeAFundamentalWeight_apply]; ring)

/-- In discriminant coordinates, doubling sends each `A₁` glue label to the same
binary residue. This is the compatibility between root-lattice gluing and Construction A. -/
-- Not a simp lemma: `rank_A` simplifies the type of the discriminant-group map.
theorem discriminantEquiv_a1ZeroLatticeIsometry_glueWordIsometry
    (w : ι → (A 1).glueAlphabet (isSimplyLaced_A 1)) :
    ConstructionA.discriminantEquiv 2 ι
      ((a1ZeroLatticeIsometry ι).discriminantGroupEquiv
        (glueWordIsometry (fun _ : ι ↦ A 1) (fun _ ↦ isSimplyLaced_A 1)
          (fun _ ↦ by decide) w)) = fun i ↦ (w i : ZMod 2) := by
  rw [← mk_a1WordRepresentative, Isometry.discriminantGroupEquiv_mk]
  have hrep : (a1ZeroLatticeIsometry ι).dualCarrierEquiv (a1WordRepresentative ι w) =
      ConstructionA.dualCarrierIntEquiv 2 ι (fun i ↦ (ZMod.val (n := 2) (w i) : ℤ)) := by
    apply Subtype.ext
    rw [Isometry.coe_dualCarrierEquiv_apply, a1ZeroLatticeIsometry_a1WordRepresentative,
      ConstructionA.coe_dualCarrierIntEquiv_apply]
    simp
  rw [hrep, ConstructionA.discriminantEquiv_mk_intCast]
  funext i
  exact_mod_cast ZMod.natCast_zmod_val (n := 2) (w i)

end TauCeti.DynkinType
