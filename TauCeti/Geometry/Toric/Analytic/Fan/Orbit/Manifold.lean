/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic

/-!
# Complex charts on torus orbits of a fan

Let `τ` be a cone of a regular fan. In every affine chart indexed by a cone `σ` containing `τ`,
the global orbit of `τ` is represented by the affine-cone orbit of `τ` as a face of `σ`. These
representations are biholomorphic: the transition sends a point to the unique point in the other
affine chart with the same image in the glued analytic realization.

This proves that the complex structures on an orbit obtained from different affine charts agree
on their overlaps. The transition is independent of coordinate choices as a map; arbitrary
extending bases, ray numberings, and monomial generating families may be used to verify that it is
holomorphic.

## Main declarations

* `TauCeti.Toric.Fan.analyticConeOrbitTransition`: the change of affine chart on a fixed global
  cone orbit.
* `TauCeti.Toric.Fan.analyticConeOrbitEquiv`: the chart transition as an equivalence.
* `TauCeti.Toric.Fan.analyticConeOrbitDiffeomorph`: the chart transition is biholomorphic for any
  regular coordinate systems on the two affine charts.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1--2.2.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1--3.2.
-/

public section

open CategoryTheory Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- Change affine charts on the orbit of `τ`. If `τ` is a face of both `σ` and `υ`, a point of
the affine orbit in the chart of `σ` has a unique representative in the chart of `υ`; this map
chooses that representative. -/
noncomputable def analyticConeOrbitTransition {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) :
    affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) →
      affineConeOrbit Φ.lattice (Φ.orbitFace hτυ) := fun x ↦ by
  let hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  let hτ := (isRegular_iff.mp hΦ) τ.1 τ.2
  let hτσ' := Φ.isFaceOf_of_le σ.2 τ.2 hτσ
  let hτυ' := Φ.isFaceOf_of_le υ.2 τ.2 hτυ
  have hxrange : x.1 ∈ range (faceAffinePointMap Φ.lattice hτσ') := by
    rw [hσ.rational.range_faceAffinePointMap Φ.lattice hτσ']
    intro m hm
    exact ((mem_affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) x.1).1 x.2 m).2 <| by
      intro v hv
      exact hm v ((SetLike.ext_iff.mp (Φ.coe_orbitFace hτσ) v).1 hv)
  let z : (Φ.analyticAffineChartDiagram hΦ).obj τ := hxrange.choose
  have hz : z ∈ affineConeOrbit Φ.lattice (⊤ : τ.1.Face) := by
    obtain ⟨F, hzF, hF⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice hτ z
    let G : σ.1.Face := ⟨F.1, F.isFaceOf.trans hτσ'⟩
    have hzx : faceAffinePointMap Φ.lattice hτσ' z ∈ affineConeOrbit Φ.lattice G :=
      faceAffinePointMap_mem_affineConeOrbit Φ.lattice hτσ' rfl hzF
    rw [hxrange.choose_spec] at hzx
    have hG : G = Φ.orbitFace hτσ :=
      (existsUnique_face_mem_affineConeOrbit Φ.lattice hσ x.1).unique hzx x.2
    have hFtop : F = ⊤ := by
      have hcones := congrArg (fun H : σ.1.Face ↦ (H : PointedCone ℝ V)) hG
      change (F : PointedCone ℝ V) = (Φ.orbitFace hτσ : PointedCone ℝ V) at hcones
      have hcones' : (F : PointedCone ℝ V) = τ.1 :=
        hcones.trans (Φ.coe_orbitFace hτσ)
      apply PointedCone.Face.ext
      intro m
      change m ∈ F ↔ m ∈ τ.1
      exact SetLike.ext_iff.mp hcones' m
    rwa [hFtop] at hzF
  refine ⟨faceAffinePointMap Φ.lattice hτυ' z, ?_⟩
  apply faceAffinePointMap_mem_affineConeOrbit Φ.lattice hτυ'
    (F := (⊤ : τ.1.Face)) (G := Φ.orbitFace hτυ)
  · change τ.1 = Φ.orbitFace hτυ
    exact (Φ.coe_orbitFace hτυ).symm
  · exact hz

/-- Changing affine charts on an orbit does not change the represented point of the analytic
realization. This equation characterizes `analyticConeOrbitTransition`, since affine chart
inclusions are injective. -/
@[simp]
theorem analyticAffineChartι_analyticConeOrbitTransition {τ σ υ : Φ.cones}
    (hτσ : τ ≤ σ) (hτυ : τ ≤ υ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticAffineChartι hΦ υ (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x).1 =
      Φ.analyticAffineChartι hΦ σ x.1 := by
  let hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  let hτσ' := Φ.isFaceOf_of_le σ.2 τ.2 hτσ
  have hxrange : x.1 ∈ range (faceAffinePointMap Φ.lattice hτσ') := by
    rw [hσ.rational.range_faceAffinePointMap Φ.lattice hτσ']
    intro m hm
    exact ((mem_affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) x.1).1 x.2 m).2 <| by
      intro v hv
      exact hm v ((SetLike.ext_iff.mp (Φ.coe_orbitFace hτσ) v).1 hv)
  let z : (Φ.analyticAffineChartDiagram hΦ).obj τ := hxrange.choose
  have hzσ : faceAffinePointMap Φ.lattice hτσ' z = x.1 := hxrange.choose_spec
  have hzυ :
      (Φ.analyticAffineChartDiagram hΦ).map (homOfLE hτυ) z =
        faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le υ.2 τ.2 hτυ) z := by
    rw [analyticAffineChartDiagram_map_apply,
      ← faceAffinePointMap_def Φ.lattice (Φ.isFaceOf_of_le υ.2 τ.2 hτυ)]
  have hzσ' :
      (Φ.analyticAffineChartDiagram hΦ).map (homOfLE hτσ) z =
        faceAffinePointMap Φ.lattice hτσ' z := by
    rw [analyticAffineChartDiagram_map_apply,
      ← faceAffinePointMap_def Φ.lattice hτσ']
  rw [show (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x).1 =
      faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le υ.2 τ.2 hτυ) z by rfl,
    ← hzυ, ← hzσ, ← hzσ']
  exact ConcreteCategory.congr_hom
    (Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι hΦ (homOfLE hτυ)) z |>.trans <|
      (ConcreteCategory.congr_hom
        (Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι hΦ (homOfLE hτσ)) z).symm

/-- The affine representations of a fixed cone orbit in any two charts containing that cone are
equivalent. The equivalence is canonical: it is defined only by equality in the glued analytic
realization. -/
noncomputable def analyticConeOrbitEquiv {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) :
    affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) ≃
      affineConeOrbit Φ.lattice (Φ.orbitFace hτυ) where
  toFun := Φ.analyticConeOrbitTransition hΦ hτσ hτυ
  invFun := Φ.analyticConeOrbitTransition hΦ hτυ hτσ
  left_inv x := Subtype.ext <| (Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).injective <|
    (Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτυ hτσ
      (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x)).trans
        (Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτσ hτυ x)
  right_inv x := Subtype.ext <| (Φ.isOpenEmbedding_analyticAffineChartι hΦ υ).injective <|
    (Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτσ hτυ
      (Φ.analyticConeOrbitTransition hΦ hτυ hτσ x)).trans
        (Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτυ hτσ x)

/-- The canonical equivalence of affine representations of an orbit acts by the orbit chart
transition. -/
@[simp]
theorem analyticConeOrbitEquiv_apply {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticConeOrbitEquiv hΦ hτσ hτυ x =
      Φ.analyticConeOrbitTransition hΦ hτσ hτυ x :=
  (rfl)

section Holomorphic

variable {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ)
  {kσ lσ kυ lυ sσ sυ : ℕ}
  {Bσ : Module.Basis (ToricRay σ.1 ⊕ Fin lσ) ℤ N}
  (hBσ : ∀ ρ, IsPrimitiveGenerator i ρ (Bσ (Sum.inl ρ)))
  (κσ : ToricRay σ.1 ≃ Fin kσ)
  (gσ : AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) sσ)
  {Bυ : Module.Basis (ToricRay υ.1 ⊕ Fin lυ) ℤ N}
  (hBυ : ∀ ρ, IsPrimitiveGenerator i ρ (Bυ (Sum.inl ρ)))
  (κυ : ToricRay υ.1 ≃ Fin kυ)
  (gυ : AddGeneratingFamily (dualSemigroup Φ.lattice υ.1) sυ)

local notation "Fσ" => Φ.orbitFace hτσ
local notation "Fυ" => Φ.orbitFace hτυ

include κσ κυ

/-- The change of affine chart on a fixed cone orbit is holomorphic for arbitrary regular
coordinates on the source and target cone charts. -/
theorem contMDiff_analyticConeOrbitTransition
    [Fintype {ρ : ToricRay σ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ}]
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ}]
    (n : ℕ∞ω) :
    let _ := affinePointTopology gσ
    let _ := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
    let _ := affinePointTopology gυ
    let _ := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
    ContMDiff
      𝓘(ℂ, (({ρ : ToricRay σ.1 // ρ ∉
        ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ} → ℂ) × (Fin lσ → ℂ)))
      𝓘(ℂ, (({ρ : ToricRay υ.1 // ρ ∉
        ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ} → ℂ) × (Fin lυ → ℂ))) n
      (Φ.analyticConeOrbitTransition hΦ hτσ hτυ) := by
  let hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  let hυ := (isRegular_iff.mp hΦ) υ.1 υ.2
  let _ := affinePointTopology gσ
  let _ := affineConeOrbitChartedSpace Φ.lattice hσ hBσ Fσ gσ
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hBσ κσ gσ
  let _ := affinePointTopology gυ
  let _ := affineConeOrbitChartedSpace Φ.lattice hυ hBυ Fυ gυ
  let _ := coneChartedSpace Φ.lattice hυ.toIsToricCone hBυ κυ gυ
  let _ := Φ.analyticChartedSpace hΦ
  apply contMDiff_of_contMDiff_subtypeVal_affineConeOrbit Φ.lattice hυ hBυ κυ Fυ gυ
  let e := Φ.analyticAffineChartPartialDiffeomorph hΦ υ hBυ κυ gυ n
  have hsource : ContMDiff
      𝓘(ℂ, (({ρ : ToricRay σ.1 // ρ ∉ hσ.faceOrderIso Φ.lattice Fσ} → ℂ) ×
        (Fin lσ → ℂ)))
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (fun x : affineConeOrbit Φ.lattice Fσ ↦ Φ.analyticAffineChartι hΦ σ x.1) :=
    (Φ.contMDiff_analyticAffineChartι hΦ σ hBσ κσ gσ n).comp
      (contMDiff_subtypeVal_affineConeOrbit Φ.lattice hσ hBσ κσ Fσ gσ n)
  have hrange (x : affineConeOrbit Φ.lattice Fσ) :
      Φ.analyticAffineChartι hΦ σ x.1 ∈ e.target := by
    rw [analyticAffineChartPartialDiffeomorph_target]
    have hx : Φ.analyticAffineChartι hΦ σ x.1 ∈ Φ.analyticConeOrbit hΦ τ :=
      (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ x.2).2 (Φ.coe_orbitFace hτσ)
    exact (Φ.mem_range_analyticAffineChartι_iff hΦ hx).2 hτυ
  refine (e.contMDiffOn_invFun.comp_contMDiff hsource hrange).congr fun x ↦ ?_
  change (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x).1 =
    e.symm (Φ.analyticAffineChartι hΦ σ x.1)
  apply (Φ.isOpenEmbedding_analyticAffineChartι hΦ υ).injective
  rw [Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτσ hτυ x]
  exact ((Φ.analyticAffineChartPartialDiffeomorph_apply hΦ υ hBυ κυ gυ n _).symm.trans
    (e.right_inv (hrange x))).symm

/-- Orbit charts obtained from any two affine charts of a regular fan agree: their canonical
transition is a biholomorphism, for arbitrary extending bases, ray numberings, and finite
monomial generating families. -/
noncomputable def analyticConeOrbitDiffeomorph
    [Fintype {ρ : ToricRay σ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ}]
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ}]
    (n : ℕ∞ω) :
    letI := affinePointTopology gσ
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
    letI := affinePointTopology gυ
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
    Diffeomorph
      𝓘(ℂ, (({ρ : ToricRay σ.1 // ρ ∉
        ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ} → ℂ) × (Fin lσ → ℂ)))
      𝓘(ℂ, (({ρ : ToricRay υ.1 // ρ ∉
        ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ} → ℂ) × (Fin lυ → ℂ)))
      (affineConeOrbit Φ.lattice Fσ) (affineConeOrbit Φ.lattice Fυ) n := by
  let _ := affinePointTopology gσ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
  let _ := affinePointTopology gυ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
  exact
    { toEquiv := Φ.analyticConeOrbitEquiv hΦ hτσ hτυ
      contMDiff_toFun := Φ.contMDiff_analyticConeOrbitTransition hΦ hτσ hτυ
        hBσ κσ gσ hBυ κυ gυ n
      contMDiff_invFun := Φ.contMDiff_analyticConeOrbitTransition hΦ hτυ hτσ
        hBυ κυ gυ hBσ κσ gσ n }

/-- The orbit-chart biholomorphism is the canonical chart transition. -/
@[simp]
theorem analyticConeOrbitDiffeomorph_apply
    [Fintype {ρ : ToricRay σ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ}]
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ}]
    (n : ℕ∞ω) (x : affineConeOrbit Φ.lattice Fσ) :
    Φ.analyticConeOrbitDiffeomorph hΦ hτσ hτυ hBσ κσ gσ hBυ κυ gυ n x =
      Φ.analyticConeOrbitTransition hΦ hτσ hτυ x :=
  (rfl)

end Holomorphic

end TauCeti.Toric.Fan
