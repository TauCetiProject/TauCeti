/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit

/-!
# The dense torus of an analytic toric fan realization

For a nonempty regular fan, the orbit indexed by the zero cone is the analytic dense torus. This
module records that this set is independent of the witness of nonemptiness and is dense and open
in the analytic realization.

## Main declarations

* `TauCeti.Toric.Fan.analyticDenseTorus`: the orbit of the zero cone in a nonempty fan.
* `TauCeti.Toric.Fan.dense_analyticDenseTorus`: the analytic dense torus is dense.
* `TauCeti.Toric.Fan.isOpen_analyticDenseTorus`: the analytic dense torus is open.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2--3.3.
-/

public section

open Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (hPhi : Phi.IsRegular)

/-- The analytic dense torus of a nonempty regular fan is the orbit indexed by its zero cone. -/
noncomputable def analyticDenseTorus (hPhi0 : Nonempty Phi.cones) :
    Set (Phi.analyticRealization hPhi) :=
  Phi.analyticConeOrbit hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩

/-- The analytic dense torus is the orbit indexed by the selected zero cone. -/
theorem analyticDenseTorus_def (hPhi0 : Nonempty Phi.cones) :
    Phi.analyticDenseTorus hPhi hPhi0 =
      Phi.analyticConeOrbit hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩ := by
  apply congrArg (Phi.analyticConeOrbit hPhi)
  apply Subtype.ext
  rfl

/-- The analytic dense torus does not depend on the witness that the fan is nonempty. -/
theorem analyticDenseTorus_eq (hPhi0 hPhi1 : Nonempty Phi.cones) :
    Phi.analyticDenseTorus hPhi hPhi0 = Phi.analyticDenseTorus hPhi hPhi1 := by
  apply congrArg (Phi.analyticConeOrbit hPhi)
  apply Subtype.ext
  rfl

/-- Using a cone as the nonemptiness witness identifies the dense torus with the orbit of the
zero cone obtained as a face of that cone. -/
theorem analyticDenseTorus_eq_analyticConeOrbit_bot (sigma : Phi.cones) :
    Phi.analyticDenseTorus hPhi (Nonempty.intro sigma) =
      Phi.analyticConeOrbit hPhi ⟨⊥, Phi.bot_mem sigma.2⟩ := by
  apply congrArg (Phi.analyticConeOrbit hPhi)
  apply Subtype.ext
  rfl

/-- The orbit of the zero cone is dense in the analytic fan realization. -/
theorem dense_analyticDenseTorus (hPhi0 : Nonempty Phi.cones) :
    Dense (Phi.analyticDenseTorus hPhi hPhi0) := by
  rw [dense_iff_closure_eq, analyticDenseTorus_def,
    Phi.closure_analyticConeOrbit hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩]
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_univ, iff_true]
  obtain ⟨sigma, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  refine ⟨sigma, ?_, hx⟩
  -- Unwrap the inherited order on the fan's subtype of cones.
  change (⊥ : PointedCone ℝ V) ≤ sigma.1
  exact bot_le

/-- The analytic dense torus is open in the fan realization. -/
theorem isOpen_analyticDenseTorus (hPhi0 : Nonempty Phi.cones) :
    IsOpen (Phi.analyticDenseTorus hPhi hPhi0) := by
  rw [Phi.isOpen_iff_forall_preimage_analyticAffineChartι hPhi]
  intro sigma
  have hbot : (⟨⊥, Phi.bot_mem hPhi0.some.2⟩ : Phi.cones) ≤ sigma := by
    change (⊥ : PointedCone ℝ V) ≤ sigma.1
    exact bot_le
  rw [analyticDenseTorus_def,
    Phi.preimage_analyticAffineChartι_analyticConeOrbit hPhi hbot]
  let hσ := (isRegular_iff.mp hPhi) sigma.1 sigma.2
  let botCone : Phi.cones := ⟨⊥, Phi.bot_mem hPhi0.some.2⟩
  let F : sigma.1.Face :=
    ⟨botCone.1, Phi.isFaceOf_of_le sigma.2 botCone.2 hbot⟩
  have hF : F = ⊥ := by
    apply le_antisymm
    · change (⊥ : PointedCone ℝ V) ≤ ((⊥ : sigma.1.Face) : PointedCone ℝ V)
      exact bot_le
    · exact bot_le
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  change @IsOpen _
    (affinePointTopology (Phi.analyticChartGenerators sigma hσ).2)
    (affineConeOrbit Phi.lattice F)
  rw [hF, affineConeOrbit_eq_orbit Phi.lattice hσ, distinguishedPoint_bot]
  exact isOpen_orbit_complexTorus_default Phi.lattice hσ.toIsToricCone hb
    (Phi.analyticChartGenerators sigma hσ).2

end TauCeti.Toric.Fan
