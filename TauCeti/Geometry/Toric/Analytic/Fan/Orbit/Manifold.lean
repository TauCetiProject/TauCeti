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
* `TauCeti.Toric.Fan.analyticConeOrbitTransition_analyticConeOrbitTransition`: the chart
  transitions satisfy the cocycle condition.
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

/-- A point of the affine orbit of `τ` in the chart of `σ` lies in the global orbit of `τ`. -/
private theorem analyticAffineChartι_val_mem_analyticConeOrbit {τ σ : Φ.cones} (hτσ : τ ≤ σ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticAffineChartι hΦ σ x.1 ∈ Φ.analyticConeOrbit hΦ τ :=
  (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ x.2).2 (Φ.coe_orbitFace hτσ)

/-- A point of the chart of `υ` whose image lies in the global orbit of `τ` lies in the affine
orbit of `τ` as a face of `υ`. -/
private theorem mem_affineConeOrbit_orbitFace {τ υ : Φ.cones} (hτυ : τ ≤ υ)
    {y : (Φ.analyticAffineChartDiagram hΦ).obj υ}
    (hy : Φ.analyticAffineChartι hΦ υ y ∈ Φ.analyticConeOrbit hΦ τ) :
    y ∈ affineConeOrbit Φ.lattice (Φ.orbitFace hτυ) := by
  obtain ⟨F, hyF, -⟩ := existsUnique_face_mem_affineConeOrbit Φ.lattice
    ((isRegular_iff.mp hΦ) υ.1 υ.2) y
  have hF := (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hyF).1 hy
  rwa [PointedCone.Face.ext fun m ↦ SetLike.ext_iff.mp (hF.trans (Φ.coe_orbitFace hτυ).symm) m]
    at hyF

/-- Change affine charts on the orbit of `τ`. If `τ` is a face of both `σ` and `υ`, a point of
the affine orbit in the chart of `σ` has a unique representative in the chart of `υ`; this map
chooses that representative. -/
noncomputable def analyticConeOrbitTransition {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) :
    affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) →
      affineConeOrbit Φ.lattice (Φ.orbitFace hτυ) := fun x ↦
  have hx := Φ.analyticAffineChartι_val_mem_analyticConeOrbit hΦ hτσ x
  have hy := (Φ.mem_range_analyticAffineChartι_iff hΦ hx).2 hτυ
  ⟨hy.choose, Φ.mem_affineConeOrbit_orbitFace hΦ hτυ (by rw [hy.choose_spec]; exact hx)⟩

/-- Changing affine charts on an orbit does not change the represented point of the analytic
realization. This equation characterizes `analyticConeOrbitTransition`, since affine chart
inclusions are injective. -/
@[simp]
theorem analyticAffineChartι_analyticConeOrbitTransition {τ σ υ : Φ.cones}
    (hτσ : τ ≤ σ) (hτυ : τ ≤ υ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticAffineChartι hΦ υ (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x).1 =
      Φ.analyticAffineChartι hΦ σ x.1 := by
  unfold analyticConeOrbitTransition
  exact ((Φ.mem_range_analyticAffineChartι_iff hΦ
    (Φ.analyticAffineChartι_val_mem_analyticConeOrbit hΦ hτσ x)).2 hτυ).choose_spec

/-- Changing from an affine chart on an orbit to the same chart is the identity. -/
@[simp]
theorem analyticConeOrbitTransition_self {τ σ : Φ.cones} (hτσ : τ ≤ σ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticConeOrbitTransition hΦ hτσ hτσ x = x :=
  Subtype.ext <| (Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).injective <|
    Φ.analyticAffineChartι_analyticConeOrbitTransition hΦ hτσ hτσ x

/-- The cocycle condition: changing affine charts on an orbit from `σ` to `υ` and then from `υ`
to `ν` is the change of chart from `σ` to `ν`. -/
@[simp]
theorem analyticConeOrbitTransition_analyticConeOrbitTransition {τ σ υ ν : Φ.cones}
    (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) (hτν : τ ≤ ν)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticConeOrbitTransition hΦ hτυ hτν (Φ.analyticConeOrbitTransition hΦ hτσ hτυ x) =
      Φ.analyticConeOrbitTransition hΦ hτσ hτν x :=
  Subtype.ext <| (Φ.isOpenEmbedding_analyticAffineChartι hΦ ν).injective <| by
    simp only [analyticAffineChartι_analyticConeOrbitTransition]

/-- The affine representations of a fixed cone orbit in any two charts containing that cone are
equivalent. The equivalence is canonical: it is defined only by equality in the glued analytic
realization. -/
noncomputable def analyticConeOrbitEquiv {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) :
    affineConeOrbit Φ.lattice (Φ.orbitFace hτσ) ≃
      affineConeOrbit Φ.lattice (Φ.orbitFace hτυ) where
  toFun := Φ.analyticConeOrbitTransition hΦ hτσ hτυ
  invFun := Φ.analyticConeOrbitTransition hΦ hτυ hτσ
  left_inv x := by simp
  right_inv x := by simp

/-- The canonical equivalence of affine representations of an orbit acts by the orbit chart
transition. -/
@[simp]
theorem analyticConeOrbitEquiv_apply {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ)
    (x : affineConeOrbit Φ.lattice (Φ.orbitFace hτσ)) :
    Φ.analyticConeOrbitEquiv hΦ hτσ hτυ x =
      Φ.analyticConeOrbitTransition hΦ hτσ hτυ x :=
  (rfl)

/-- The inverse of the canonical equivalence of affine orbit representations is the canonical
equivalence in the opposite direction. -/
@[simp]
theorem analyticConeOrbitEquiv_symm {τ σ υ : Φ.cones} (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) :
    (Φ.analyticConeOrbitEquiv hΦ hτσ hτυ).symm = Φ.analyticConeOrbitEquiv hΦ hτυ hτσ :=
  (rfl)

/-- The canonical equivalence from an affine orbit representation to itself is the identity. -/
@[simp]
theorem analyticConeOrbitEquiv_self {τ σ : Φ.cones} (hτσ : τ ≤ σ) :
    Φ.analyticConeOrbitEquiv hΦ hτσ hτσ = Equiv.refl _ :=
  Equiv.ext <| Φ.analyticConeOrbitTransition_self hΦ hτσ

/-- The canonical equivalences of affine orbit representations compose according to the cocycle
condition. -/
@[simp]
theorem analyticConeOrbitEquiv_trans {τ σ υ ν : Φ.cones}
    (hτσ : τ ≤ σ) (hτυ : τ ≤ υ) (hτν : τ ≤ ν) :
    (Φ.analyticConeOrbitEquiv hΦ hτσ hτυ).trans (Φ.analyticConeOrbitEquiv hΦ hτυ hτν) =
      Φ.analyticConeOrbitEquiv hΦ hτσ hτν :=
  Equiv.ext <| Φ.analyticConeOrbitTransition_analyticConeOrbitTransition hΦ hτσ hτυ hτν

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
    exact (Φ.mem_range_analyticAffineChartι_iff hΦ
      (Φ.analyticAffineChartι_val_mem_analyticConeOrbit hΦ hτσ x)).2 hτυ
  refine (e.contMDiffOn_invFun.comp_contMDiff hsource hrange).congr fun x ↦ ?_
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

/-- The inverse of the orbit-chart biholomorphism is the orbit-chart biholomorphism in the
opposite direction. -/
@[simp]
theorem analyticConeOrbitDiffeomorph_symm
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
    (Φ.analyticConeOrbitDiffeomorph hΦ hτσ hτυ hBσ κσ gσ hBυ κυ gυ n).symm =
      Φ.analyticConeOrbitDiffeomorph hΦ hτυ hτσ hBυ κυ gυ hBσ κσ gσ n := by
  let _ := affinePointTopology gσ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
  let _ := affinePointTopology gυ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
  exact Diffeomorph.ext fun _ ↦ rfl

omit κυ in
/-- The orbit-chart biholomorphism from an affine orbit representation to itself, with the same
coordinates on both sides, is the identity. -/
@[simp]
theorem analyticConeOrbitDiffeomorph_self
    [Fintype {ρ : ToricRay σ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ}]
    (n : ℕ∞ω) :
    letI := affinePointTopology gσ
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
    Φ.analyticConeOrbitDiffeomorph hΦ hτσ hτσ hBσ κσ gσ hBσ κσ gσ n = Diffeomorph.refl _ _ n := by
  let _ := affinePointTopology gσ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
  exact Diffeomorph.ext <| Φ.analyticConeOrbitTransition_self hΦ hτσ

section Trans

variable {ν : Φ.cones} (hτν : τ ≤ ν) {kν lν sν : ℕ}
  {Bν : Module.Basis (ToricRay ν.1 ⊕ Fin lν) ℤ N}
  (hBν : ∀ ρ, IsPrimitiveGenerator i ρ (Bν (Sum.inl ρ)))
  (κν : ToricRay ν.1 ≃ Fin kν)
  (gν : AddGeneratingFamily (dualSemigroup Φ.lattice ν.1) sν)

/-- Orbit-chart biholomorphisms compose according to the cocycle condition. -/
@[simp]
theorem analyticConeOrbitDiffeomorph_trans
    [Fintype {ρ : ToricRay σ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) σ.1 σ.2).faceOrderIso Φ.lattice Fσ}]
    [Fintype {ρ : ToricRay υ.1 // ρ ∉
      ((isRegular_iff.mp hΦ) υ.1 υ.2).faceOrderIso Φ.lattice Fυ}]
    [Fintype {ρ : ToricRay ν.1 // ρ ∉
      ((isRegular_iff.mp hΦ) ν.1 ν.2).faceOrderIso Φ.lattice (Φ.orbitFace hτν)}]
    (n : ℕ∞ω) :
    letI := affinePointTopology gσ
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
    letI := affinePointTopology gυ
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
    letI := affinePointTopology gν
    letI := affineConeOrbitChartedSpace Φ.lattice
      ((isRegular_iff.mp hΦ) ν.1 ν.2) hBν (Φ.orbitFace hτν) gν
    (Φ.analyticConeOrbitDiffeomorph hΦ hτσ hτυ hBσ κσ gσ hBυ κυ gυ n).trans
        (Φ.analyticConeOrbitDiffeomorph hΦ hτυ hτν hBυ κυ gυ hBν κν gν n) =
      Φ.analyticConeOrbitDiffeomorph hΦ hτσ hτν hBσ κσ gσ hBν κν gν n := by
  let _ := affinePointTopology gσ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2) hBσ Fσ gσ
  let _ := affinePointTopology gυ
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) υ.1 υ.2) hBυ Fυ gυ
  let _ := affinePointTopology gν
  let _ := affineConeOrbitChartedSpace Φ.lattice
    ((isRegular_iff.mp hΦ) ν.1 ν.2) hBν (Φ.orbitFace hτν) gν
  exact Diffeomorph.ext <|
    Φ.analyticConeOrbitTransition_analyticConeOrbitTransition hΦ hτσ hτυ hτν

end Trans

end Holomorphic

end TauCeti.Toric.Fan
