/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Face
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Basic

/-!
# The orbit–cone correspondence on the analytic realization of a fan

Every cone `σ` of a regular fan has a distinguished point in the analytic realization: the image of
the distinguished point of the top face of `σ` in the affine chart of `σ`. Its torus orbit is the
image of the stratum of the top face of `σ` in that chart. This file proves that these orbits are
all the torus orbits of the realization, that distinct cones give distinct orbits, and that the
closure order on orbits is the reverse of the face order on cones.

The key point is that the stratum of a point does not depend on the chart used to see it. A point
of the chart of `σ` that lies in the stratum of a face `F` of `σ` comes from the chart of `σ ⊓ τ`
whenever it also lies in the chart of `τ`; restriction along a face inclusion preserves strata, so
the strata seen in the charts of `σ` and `τ` are both the stratum of the same cone. Consequently a
point of the chart of `σ` lies in the orbit of a cone `τ` exactly when its affine stratum is
indexed by `τ`, and the orbit of `τ` meets the chart of `σ` precisely when `τ` is a face of `σ`,
in the affine stratum of `τ`. Since every chart is an open subspace of the realization, the closure
order is computed in a single chart, where it is the affine closure order.

## Main declarations

* `TauCeti.Toric.Fan.analyticDistinguishedPoint`: the distinguished point of a cone.
* `TauCeti.Toric.Fan.analyticConeOrbit`: the torus orbit of a cone, with
  `TauCeti.Toric.Fan.analyticConeOrbit_eq_orbit` identifying it with the orbit of the
  distinguished point.
* `TauCeti.Toric.Fan.analyticAffineChartι_mem_analyticConeOrbit_iff`: a point of a chart lies in
  the orbit of `τ` exactly when its affine stratum is indexed by `τ`.
* `TauCeti.Toric.Fan.existsUnique_mem_analyticConeOrbit`: the orbits of the cones partition the
  realization.
* `TauCeti.Toric.Fan.coneEquivOrbitRelQuotient`: the orbit–cone correspondence between the cones
  of the fan and the torus orbits of its analytic realization.
* `TauCeti.Toric.Fan.analyticConeOrbit_subset_closure_iff` and
  `TauCeti.Toric.Fan.closure_analyticConeOrbit`: the correspondence reverses the closure order.
* `TauCeti.Toric.Fan.mem_stabilizer_analyticDistinguishedPoint_iff`: the stabilizer of the
  distinguished point of `σ` is the subtorus trivial on the characters vanishing on `σ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and Theorem 3.2.6.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-! ### Strata do not depend on the chart -/

/-- A cone `τ` of a fan, viewed as a face of a cone `σ` containing it. This is the affine stratum
in the chart of `σ` that represents the global orbit of `τ`. -/
def orbitFace {τ σ : Φ.cones} (h : τ ≤ σ) : σ.1.Face :=
  ⟨τ.1, Φ.isFaceOf_of_le σ.2 τ.2 h⟩

/-- The cone underlying `orbitFace` is the smaller cone. -/
@[simp]
theorem coe_orbitFace {τ σ : Φ.cones} (h : τ ≤ σ) :
    (Φ.orbitFace h : PointedCone ℝ V) = τ.1 :=
  (rfl)

/-- A map of the chart diagram sends the stratum of a face of the smaller cone into the stratum of
the same cone, viewed as a face of the larger cone. -/
private theorem analyticAffineChartDiagram_map_mem_affineConeOrbit {τ σ : Φ.cones} (f : τ ⟶ σ)
    {F : τ.1.Face} {G : σ.1.Face} (hFG : (F : PointedCone ℝ V) = G)
    {x : (Φ.analyticAffineChartDiagram hΦ).obj τ} (hx : x ∈ affineConeOrbit Φ.lattice F) :
    (Φ.analyticAffineChartDiagram hΦ).map f x ∈ affineConeOrbit Φ.lattice G := by
  rw [analyticAffineChartDiagram_map_apply,
    ← faceAffinePointMap_def Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))]
  exact faceAffinePointMap_mem_affineConeOrbit Φ.lattice _ hFG hx

/-- The stratum of a point of the analytic realization does not depend on the chart: if points of
the charts of `σ` and `τ` have the same image, and lie in the strata of a face `F` of `σ` and a
face `G` of `τ`, then `F` and `G` are the same cone. -/
theorem coe_eq_coe_of_analyticAffineChartι_eq {σ τ : Φ.cones}
    {x : (Φ.analyticAffineChartDiagram hΦ).obj σ} {y : (Φ.analyticAffineChartDiagram hΦ).obj τ}
    (hxy : Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y)
    {F : σ.1.Face} {G : τ.1.Face} (hx : x ∈ affineConeOrbit Φ.lattice F)
    (hy : y ∈ affineConeOrbit Φ.lattice G) :
    (F : PointedCone ℝ V) = G := by
  -- Both points come from a point `z` of the chart of `σ ⊓ τ`, in the stratum of some face `H`.
  obtain ⟨z, rfl, rfl⟩ := (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).1 hxy
  rw [analyticOverlapLeft_def] at hx
  rw [analyticOverlapRight_def] at hy
  obtain ⟨H, hz, -⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice
    ((isRegular_iff.mp hΦ) _ (σ ⊓ τ).2) z
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hτ := (isRegular_iff.mp hΦ) τ.1 τ.2
  have hHσ : (H : PointedCone ℝ V).IsFaceOf σ :=
    H.isFaceOf.trans (Φ.isFaceOf_of_le σ.2 (σ ⊓ τ).2 inf_le_left)
  have hHτ : (H : PointedCone ℝ V).IsFaceOf τ :=
    H.isFaceOf.trans (Φ.isFaceOf_of_le τ.2 (σ ⊓ τ).2 inf_le_right)
  -- Restriction preserves strata, so both `F` and `G` are the cone `H`.
  have hF : F = ⟨H, hHσ⟩ := (existsUnique_face_mem_affineConeOrbit Φ.lattice hσ _).unique hx
    (Φ.analyticAffineChartDiagram_map_mem_affineConeOrbit hΦ (homOfLE inf_le_left)
      (G := ⟨H, hHσ⟩) rfl hz)
  have hG : G = ⟨H, hHτ⟩ := (existsUnique_face_mem_affineConeOrbit Φ.lattice hτ _).unique hy
    (Φ.analyticAffineChartDiagram_map_mem_affineConeOrbit hΦ (homOfLE inf_le_right)
      (G := ⟨H, hHτ⟩) rfl hz)
  rw [hF, hG]

/-! ### Distinguished points and orbits of cones -/

/-- The distinguished point of a cone `σ` of a regular fan: the distinguished point of the top face
of `σ` in the affine chart of `σ`, viewed in the analytic realization. -/
noncomputable def analyticDistinguishedPoint (σ : Φ.cones) : Φ.analyticRealization hΦ :=
  Φ.analyticAffineChartι hΦ σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face))

/-- The distinguished point of a cone is the image of the distinguished point of its top face. -/
theorem analyticDistinguishedPoint_def (σ : Φ.cones) :
    Φ.analyticDistinguishedPoint hΦ σ =
      Φ.analyticAffineChartι hΦ σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face)) :=
  (rfl)

/-- The distinguished point of a face `τ` of `σ`, seen in the chart of `σ`, is the distinguished
point of `τ` as a face of `σ`. -/
theorem analyticAffineChartι_distinguishedPoint {τ σ : Φ.cones} (h : τ ≤ σ) :
    Φ.analyticAffineChartι hΦ σ
        (distinguishedPoint Φ.lattice (Φ.orbitFace h)) =
      Φ.analyticDistinguishedPoint hΦ τ := by
  have hd : (Φ.analyticAffineChartDiagram hΦ).map (homOfLE h)
      (distinguishedPoint Φ.lattice (⊤ : τ.1.Face)) =
        distinguishedPoint Φ.lattice (Φ.orbitFace h) := by
    rw [analyticAffineChartDiagram_map_apply Φ hΦ (homOfLE h)
        (distinguishedPoint Φ.lattice (⊤ : τ.1.Face)),
      ← faceAffinePointMap_def Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 h)]
    exact faceAffinePointMap_distinguishedPoint Φ.lattice _ rfl
  rw [← hd, analyticDistinguishedPoint_def]
  exact ConcreteCategory.congr_hom
    (Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι hΦ (homOfLE h)) _

/-- The torus orbit of a cone `σ` of a regular fan: the image in the analytic realization of the
stratum of the top face of `σ` in the affine chart of `σ`. By `analyticConeOrbit_eq_orbit`, it is
the torus orbit of the distinguished point of `σ`. -/
def analyticConeOrbit (σ : Φ.cones) : Set (Φ.analyticRealization hΦ) :=
  Φ.analyticAffineChartι hΦ σ '' affineConeOrbit Φ.lattice (⊤ : σ.1.Face)

/-- The orbit of a cone is the image of the stratum of its top face. -/
theorem analyticConeOrbit_def (σ : Φ.cones) :
    Φ.analyticConeOrbit hΦ σ =
      Φ.analyticAffineChartι hΦ σ '' affineConeOrbit Φ.lattice (⊤ : σ.1.Face) :=
  (rfl)

/-- The orbit of a cone `σ` is the torus orbit of the distinguished point of `σ`. -/
theorem analyticConeOrbit_eq_orbit (σ : Φ.cones) :
    Φ.analyticConeOrbit hΦ σ =
      MulAction.orbit (ComplexTorus N) (Φ.analyticDistinguishedPoint hΦ σ) := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  ext x
  rw [analyticConeOrbit_def, affineConeOrbit_eq_orbit Φ.lattice hσ, analyticDistinguishedPoint_def]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, Φ.smul_analyticAffineChartι hΦ t σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face))⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t • distinguishedPoint Φ.lattice (⊤ : σ.1.Face), ⟨t, rfl⟩,
      (Φ.smul_analyticAffineChartι hΦ t σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face))).symm⟩

/-- The distinguished point of a cone lies in its orbit. -/
theorem analyticDistinguishedPoint_mem_analyticConeOrbit (σ : Φ.cones) :
    Φ.analyticDistinguishedPoint hΦ σ ∈ Φ.analyticConeOrbit hΦ σ := by
  rw [analyticConeOrbit_eq_orbit]
  exact MulAction.mem_orbit_self (M := ComplexTorus N) _

/-- A point of the chart of `σ` in the stratum of a face `F` lies in the orbit of a cone `τ` exactly
when `F` is the cone `τ`. -/
theorem analyticAffineChartι_mem_analyticConeOrbit_iff {σ τ : Φ.cones}
    {x : (Φ.analyticAffineChartDiagram hΦ).obj σ} {F : σ.1.Face}
    (hx : x ∈ affineConeOrbit Φ.lattice F) :
    Φ.analyticAffineChartι hΦ σ x ∈ Φ.analyticConeOrbit hΦ τ ↔ (F : PointedCone ℝ V) = τ := by
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ Φ.coe_eq_coe_of_analyticAffineChartι_eq hΦ hxy.symm hx hy, ?_⟩
  intro hF
  have hτσ : τ ≤ σ := Subtype.coe_le_coe.1 (hF ▸ F.toPointedCone_le)
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  -- `x` is a torus translate of the distinguished point of `F`, which is that of `τ`.
  have hFτ : F = Φ.orbitFace hτσ := PointedCone.Face.ext fun y ↦
    SetLike.ext_iff.mp hF y
  rw [affineConeOrbit_eq_orbit Φ.lattice hσ, hFτ] at hx
  obtain ⟨t, ht⟩ := hx
  have hxt : Φ.analyticAffineChartι hΦ σ x = t • Φ.analyticDistinguishedPoint hΦ τ := by
    rw [← Φ.analyticAffineChartι_distinguishedPoint hΦ hτσ, Φ.smul_analyticAffineChartι hΦ t σ
      (distinguishedPoint Φ.lattice (Φ.orbitFace hτσ))]
    exact congrArg _ ht.symm
  rw [hxt, analyticConeOrbit_eq_orbit]
  exact MulAction.mem_orbit _ t

/-- The orbit of a face `τ` of `σ` meets the chart of `σ` in the stratum of `τ`. -/
theorem preimage_analyticAffineChartι_analyticConeOrbit {τ σ : Φ.cones} (h : τ ≤ σ) :
    Φ.analyticAffineChartι hΦ σ ⁻¹' Φ.analyticConeOrbit hΦ τ =
      affineConeOrbit Φ.lattice (Φ.orbitFace h) := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  ext x
  obtain ⟨F, hx, hF⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice hσ x
  rw [mem_preimage, Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hx]
  refine ⟨fun hFτ ↦ ?_, fun hτ ↦ ?_⟩
  · have : F = Φ.orbitFace h := PointedCone.Face.ext fun y ↦
      SetLike.ext_iff.mp hFτ y
    rwa [this] at hx
  · rw [← hF _ hτ, Φ.coe_orbitFace]

/-- The orbit of a cone `τ` does not meet the chart of a cone `σ` that does not contain `τ`. -/
theorem preimage_analyticAffineChartι_analyticConeOrbit_of_not_le {τ σ : Φ.cones}
    (h : ¬τ ≤ σ) :
    Φ.analyticAffineChartι hΦ σ ⁻¹' Φ.analyticConeOrbit hΦ τ = ∅ := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  refine eq_empty_of_forall_notMem fun x hx ↦ h ?_
  obtain ⟨F, hxF, -⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice hσ x
  have hF := (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hxF).1 hx
  exact Subtype.coe_le_coe.1 (hF ▸ F.toPointedCone_le)

/-- A point in the orbit of `σ` belongs to the affine chart of `τ` exactly when `σ ≤ τ`. -/
theorem mem_range_analyticAffineChartι_iff {σ τ : Φ.cones} {x : Φ.analyticRealization hΦ}
    (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    x ∈ range (Φ.analyticAffineChartι hΦ τ) ↔ σ ≤ τ := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨F, hy, -⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice
      ((isRegular_iff.mp hΦ) τ.1 τ.2) y
    have hF := (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).1 hx
    exact Subtype.coe_le_coe.1 (hF ▸ F.toPointedCone_le)
  · intro h
    rw [Φ.analyticConeOrbit_eq_orbit hΦ] at hx
    obtain ⟨t, rfl⟩ := hx
    refine ⟨t • distinguishedPoint Φ.lattice (Φ.orbitFace h), ?_⟩
    exact (Φ.smul_analyticAffineChartι hΦ t τ _).symm.trans
      (congrArg (t • ·) (Φ.analyticAffineChartι_distinguishedPoint hΦ h))

/-! ### The orbit–cone correspondence -/

/-- The orbits of the cones partition the analytic realization: every point lies in the orbit of a
unique cone. -/
theorem existsUnique_mem_analyticConeOrbit (x : Φ.analyticRealization hΦ) :
    ∃! σ : Φ.cones, x ∈ Φ.analyticConeOrbit hΦ σ := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  obtain ⟨F, hy, -⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2) y
  refine ⟨⟨F, Φ.mem_of_isFaceOf σ.2 F.isFaceOf⟩,
    (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl, fun τ hτ ↦ ?_⟩
  exact Subtype.ext ((Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).1 hτ).symm

/-- Every point of the analytic realization lies in the orbit of some cone. -/
theorem exists_mem_analyticConeOrbit (x : Φ.analyticRealization hΦ) :
    ∃ σ : Φ.cones, x ∈ Φ.analyticConeOrbit hΦ σ :=
  (Φ.existsUnique_mem_analyticConeOrbit hΦ x).exists

/-- The orbits of two cones meet only when the cones are equal. -/
theorem eq_of_mem_analyticConeOrbit {σ τ : Φ.cones} {x : Φ.analyticRealization hΦ}
    (hσ : x ∈ Φ.analyticConeOrbit hΦ σ) (hτ : x ∈ Φ.analyticConeOrbit hΦ τ) : σ = τ :=
  (Φ.existsUnique_mem_analyticConeOrbit hΦ x).unique hσ hτ

/-- The orbit–cone correspondence for a regular fan: the cones of the fan correspond bijectively to
the torus orbits of its analytic realization, a cone corresponding to the orbit of its
distinguished point. By `analyticConeOrbit_subset_closure_iff`, the correspondence reverses the
closure order. -/
noncomputable def coneEquivOrbitRelQuotient :
    Φ.cones ≃ MulAction.orbitRel.Quotient (ComplexTorus N) (Φ.analyticRealization hΦ) :=
  Equiv.ofBijective (fun σ ↦ Quotient.mk'' (Φ.analyticDistinguishedPoint hΦ σ)) ⟨fun σ τ h ↦ by
    refine Φ.eq_of_mem_analyticConeOrbit hΦ
      (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ) ?_
    rw [analyticConeOrbit_eq_orbit]
    exact Quotient.exact' h, fun q ↦ by
    induction q using Quotient.inductionOn' with
    | h x =>
      obtain ⟨σ, hx⟩ := Φ.exists_mem_analyticConeOrbit hΦ x
      rw [analyticConeOrbit_eq_orbit] at hx
      exact ⟨σ, Quotient.sound' (MulAction.mem_orbit_symm.1 hx)⟩⟩

/-- The orbit–cone correspondence sends a cone to the orbit of its distinguished point. -/
@[simp]
theorem coneEquivOrbitRelQuotient_apply (σ : Φ.cones) :
    Φ.coneEquivOrbitRelQuotient hΦ σ = Quotient.mk'' (Φ.analyticDistinguishedPoint hΦ σ) :=
  (rfl)

/-- The torus orbit corresponding to a cone is its orbit `analyticConeOrbit`. -/
theorem orbit_coneEquivOrbitRelQuotient (σ : Φ.cones) :
    (Φ.coneEquivOrbitRelQuotient hΦ σ).orbit = Φ.analyticConeOrbit hΦ σ := by
  rw [coneEquivOrbitRelQuotient_apply, MulAction.orbitRel.Quotient.orbit_mk,
    analyticConeOrbit_eq_orbit]

/-- The cone corresponding to the torus orbit of a point is the cone whose orbit contains it. -/
theorem coneEquivOrbitRelQuotient_symm_mk {σ : Φ.cones} {x : Φ.analyticRealization hΦ}
    (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    (Φ.coneEquivOrbitRelQuotient hΦ).symm (Quotient.mk'' x) = σ := by
  rw [Equiv.symm_apply_eq, coneEquivOrbitRelQuotient_apply]
  refine Quotient.sound' ?_
  rw [analyticConeOrbit_eq_orbit] at hx
  exact hx

/-! ### The closure order -/

/-- A point of the orbit of `σ` lies in the closure of the orbit of `τ` exactly when `τ` is a face
of `σ`. -/
theorem mem_closure_analyticConeOrbit_iff {σ τ : Φ.cones} {x : Φ.analyticRealization hΦ}
    (hx : x ∈ Φ.analyticConeOrbit hΦ σ) :
    x ∈ closure (Φ.analyticConeOrbit hΦ τ) ↔ τ ≤ σ := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hι := Φ.isOpenEmbedding_analyticAffineChartι hΦ σ
  obtain ⟨y, hy, rfl⟩ := hx
  -- The chart of `σ` is an open subspace, so the closure can be computed in that chart.
  rw [← mem_preimage, hι.isOpenMap.preimage_closure_eq_closure_preimage hι.continuous]
  by_cases h : τ ≤ σ
  · rw [Φ.preimage_analyticAffineChartι_analyticConeOrbit hΦ h]
    refine iff_of_true ?_ h
    exact (mem_closure_affineConeOrbit_iff_le Φ.lattice hσ _ ⊤
      (Φ.analyticChartGenerators σ hσ).2 hy).2 le_top
  · rw [Φ.preimage_analyticAffineChartι_analyticConeOrbit_of_not_le hΦ h, closure_empty]
    exact iff_of_false (notMem_empty y) h

/-- The closure of the orbit of a cone `τ` is the union of the orbits of the cones containing
`τ`. -/
theorem closure_analyticConeOrbit (τ : Φ.cones) :
    closure (Φ.analyticConeOrbit hΦ τ) = ⋃ σ ∈ Ici τ, Φ.analyticConeOrbit hΦ σ := by
  ext x
  obtain ⟨σ, hx⟩ := Φ.exists_mem_analyticConeOrbit hΦ x
  rw [Φ.mem_closure_analyticConeOrbit_iff hΦ hx, mem_iUnion₂]
  exact ⟨fun h ↦ ⟨σ, h, hx⟩, fun ⟨σ', h, hx'⟩ ↦ Φ.eq_of_mem_analyticConeOrbit hΦ hx' hx ▸ h⟩

/-- Under the orbit–cone correspondence, inclusion of cones is the reverse of the closure order
on orbits. -/
theorem analyticConeOrbit_subset_closure_iff (σ τ : Φ.cones) :
    Φ.analyticConeOrbit hΦ σ ⊆ closure (Φ.analyticConeOrbit hΦ τ) ↔ τ ≤ σ :=
  ⟨fun h ↦ (Φ.mem_closure_analyticConeOrbit_iff hΦ
      (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ)).1
      (h (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ)),
    fun h _ hx ↦ (Φ.mem_closure_analyticConeOrbit_iff hΦ hx).2 h⟩

/-! ### Stabilizers -/

/-- The stabilizer of the distinguished point of a cone `σ` is the subtorus of torus points that
are trivial on the characters vanishing on `σ`. -/
theorem mem_stabilizer_analyticDistinguishedPoint_iff (σ : Φ.cones) (T : ComplexTorus N) :
    T ∈ MulAction.stabilizer (ComplexTorus N) (Φ.analyticDistinguishedPoint hΦ σ) ↔
      ∀ m : N →+ ℤ, (∀ y ∈ σ.1, Φ.lattice.realCharacter m y = 0) → T m = 1 := by
  rw [MulAction.mem_stabilizer_iff, analyticDistinguishedPoint_def,
    Φ.smul_analyticAffineChartι hΦ T σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face))]
  -- The chart inclusion is injective and equivariant, so the stabilizer is the affine one.
  exact (Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).injective.eq_iff.trans
    (MulAction.mem_stabilizer_iff.symm.trans
      (mem_stabilizer_distinguishedPoint_iff Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2) ⊤ T))

end TauCeti.Toric.Fan
