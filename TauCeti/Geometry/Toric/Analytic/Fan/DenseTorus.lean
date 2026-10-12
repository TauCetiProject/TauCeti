/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic

/-!
# The dense torus of an analytic toric fan realization

For a nonempty regular fan, the orbit indexed by the zero cone is the analytic dense torus. This
module records that this set is independent of the witness of nonemptiness and is dense and open
in the analytic realization. Its canonical parametrization by the coordinate-free complex torus
is continuous and injective, and determines continuous maps into Hausdorff spaces uniquely.

## Main declarations

* `TauCeti.Toric.Fan.analyticDenseTorus`: the orbit of the zero cone in a nonempty fan.
* `TauCeti.Toric.Fan.dense_analyticDenseTorus`: the analytic dense torus is dense.
* `TauCeti.Toric.Fan.isOpen_analyticDenseTorus`: the analytic dense torus is open.
* `TauCeti.Toric.Fan.analyticTorusι`: the canonical parametrization by the complex torus.
* `TauCeti.Toric.Fan.analyticRealization_hom_ext_torus`: continuous maps to a Hausdorff space
  are determined by their values on the complex torus.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2--3.3.
-/

public section

open CategoryTheory Set Topology

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
    exact Subtype.coe_le_coe.1 (bot_le : (⊥ : PointedCone ℝ V) ≤ sigma.1)
  rw [analyticDenseTorus_def,
    Phi.preimage_analyticAffineChartι_analyticConeOrbit hPhi hbot]
  let hσ := (isRegular_iff.mp hPhi) sigma.1 sigma.2
  let F : sigma.1.Face := Phi.orbitFace hbot
  have hF : F = ⊥ := by
    dsimp only [F]
    apply le_antisymm
    · rw [← PointedCone.Face.toPointedCone_le_toPointedCone, Phi.coe_orbitFace]
      exact bot_le
    · exact bot_le
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  have hopen : @IsOpen _
      (affinePointTopology (Phi.analyticChartGenerators sigma).2)
      (affineConeOrbit Phi.lattice F) := by
    rw [hF, affineConeOrbit_eq_orbit Phi.lattice hσ, distinguishedPoint_bot]
    exact isOpen_orbit_complexTorus_default Phi.lattice hσ.toIsToricCone hb
      (Phi.analyticChartGenerators sigma).2
  rw [← Phi.analyticAffineChart_str_eq sigma
    (Phi.analyticChartGenerators sigma).2] at hopen
  exact hopen

/-- The canonical inclusion of the coordinate-free complex torus into the realization of a
nonempty regular fan, obtained by translating the distinguished point of the zero cone.
By proof irrelevance, different nonemptiness witnesses give definitionally equal inclusions. -/
noncomputable def analyticTorusι (hPhi0 : Nonempty Phi.cones) (t : ComplexTorus N) :
    Phi.analyticRealization hPhi :=
  t • Phi.analyticDistinguishedPoint hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩

/-- The torus inclusion is translation of the distinguished point of the zero cone. -/
theorem analyticTorusι_def (hPhi0 : Nonempty Phi.cones) (t : ComplexTorus N) :
    Phi.analyticTorusι hPhi hPhi0 t =
      t • Phi.analyticDistinguishedPoint hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩ :=
  (rfl)

/-- In every affine chart the torus inclusion is translation of the point whose monomial values
are all one. In particular this formula does not choose coordinates on the lattice. -/
theorem analyticTorusι_eq_analyticAffineChartι (hPhi0 : Nonempty Phi.cones)
    (sigma : Phi.cones) (t : ComplexTorus N) :
    Phi.analyticTorusι hPhi hPhi0 t = Phi.analyticAffineChartι hPhi sigma
      (t • (default : AffineSemigroupComplexPoint (dualSemigroup Phi.lattice sigma.1))) := by
  let tau : Phi.cones := ⟨⊥, Phi.bot_mem hPhi0.some.2⟩
  have hle : tau ≤ sigma := Subtype.coe_le_coe.1 bot_le
  have hface : Phi.orbitFace hle = (⊥ : sigma.1.Face) := by
    apply le_antisymm
    · rw [← PointedCone.Face.toPointedCone_le_toPointedCone, Phi.coe_orbitFace]
      exact bot_le
    · exact bot_le
  rw [analyticTorusι_def, ← Phi.analyticAffineChartι_distinguishedPoint hPhi hle,
    hface, distinguishedPoint_bot]
  exact Phi.smul_analyticAffineChartι hPhi t sigma _

/-- The torus inclusion respects translation. -/
@[simp]
theorem analyticTorusι_mul (hPhi0 : Nonempty Phi.cones) (s t : ComplexTorus N) :
    Phi.analyticTorusι hPhi hPhi0 (s * t) = s • Phi.analyticTorusι hPhi hPhi0 t := by
  simp only [analyticTorusι_def]
  exact @mul_smul (ComplexTorus N) (Phi.analyticRealization hPhi) inferInstance inferInstance
    s t (Phi.analyticDistinguishedPoint hPhi ⟨⊥, Phi.bot_mem hPhi0.some.2⟩)

/-- The canonical torus parametrization is injective. -/
theorem analyticTorusι_injective (hPhi0 : Nonempty Phi.cones) :
    Function.Injective (Phi.analyticTorusι hPhi hPhi0) := by
  let sigma := hPhi0.some
  have hreg := (isRegular_iff.mp hPhi) sigma.1 sigma.2
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  intro s t h
  rw [Phi.analyticTorusι_eq_analyticAffineChartι hPhi hPhi0 sigma,
    Phi.analyticTorusι_eq_analyticAffineChartι hPhi hPhi0 sigma] at h
  exact complexTorus_smul_default_injective Phi.lattice hreg.toIsToricCone hb
    ((Phi.isOpenEmbedding_analyticAffineChartι hPhi sigma).injective h)

/-- The range of the canonical torus inclusion is exactly the analytic dense torus. -/
@[simp]
theorem range_analyticTorusι (hPhi0 : Nonempty Phi.cones) :
    Set.range (Phi.analyticTorusι hPhi hPhi0) = Phi.analyticDenseTorus hPhi hPhi0 := by
  rw [analyticDenseTorus_def, analyticConeOrbit_eq_orbit]
  exact congrArg Set.range (funext (Phi.analyticTorusι_def hPhi hPhi0))

/-- The canonical torus inclusion is continuous for the coordinate-free torus topology. -/
@[fun_prop]
theorem continuous_analyticTorusι (hPhi0 : Nonempty Phi.cones) :
    Continuous (Phi.analyticTorusι hPhi hPhi0) := by
  unfold analyticTorusι
  exact continuous_id.smul continuous_const

/-- Maps from a nonempty regular fan realization to a Hausdorff space agree if they agree at
every point of the canonical complex torus. -/
theorem analyticRealization_hom_ext_torus (hPhi0 : Nonempty Phi.cones)
    {Z : TopCat.{u}} [T2Space Z] {g g' : Phi.analyticRealization hPhi ⟶ Z}
    (h : ∀ t, g (Phi.analyticTorusι hPhi hPhi0 t) =
      g' (Phi.analyticTorusι hPhi hPhi0 t)) : g = g' := by
  have hd : DenseRange (Phi.analyticTorusι hPhi hPhi0) := by
    rw [DenseRange, Phi.range_analyticTorusι hPhi hPhi0]
    exact Phi.dense_analyticDenseTorus hPhi hPhi0
  ext x
  exact congrFun (hd.equalizer g.hom.continuous g'.hom.continuous (funext h)) x

end TauCeti.Toric.Fan
