/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.QuotientPullback
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.LocalSystem
public import TauCeti.RepresentationTheory.ExteriorPower

/-!
# Sheet markings and monodromy of a descended family of tori

For a continuous full-lattice family `P : Y → Λ →ₗ[ℤ] E` with a continuous affine `Γ`-action
intertwining `P` with `ρ : Representation ℤ Γ Λ` and a quotient covering `β : Y → Z` by `Γ`, let
`q = TauCeti.torusFamilyAffineQuotientMap`. Choosing `y : Y` over `z = β y` yields sheet markings
`TauCeti.torusFamilyAffineQuotientHomologyMarking` (`Hₙ(q⁻¹ z; ℤ) ≃ₗ[ℤ] ⋀[ℤ]^n Λ`) and
`TauCeti.torusFamilyAffineQuotientMarking` (`H₁(q⁻¹ z; ℤ) ≃ₗ[ℤ] Λ`):

* `TauCeti.torusFamilyAffineQuotientHomologyMarking_smul` and `...Marking_smul`: sheet change
  `y ↦ g • y` precomposes the inverse fiber homeomorphism with `g`, acting by `ρ.exteriorPower n g`
  (`ρ g` in degree `1`).
* `TauCeti.torusFamilyAffineQuotientHomologyMarking_transport_of_lift`, `..._of_lift_smul`,
  `..._transport_monodromy`, and degree-`1` counterparts: lifting a loop at `z` from `y` to `g • y`
  preserves markings along the lift and compares back to `y` by `g⁻¹`, acting by
  `ρ.exteriorPower n g⁻¹` (`ρ g⁻¹` in degree `1`), matching `associatedLocalSystem` coinvariants.

Spaces carrying integer singular chains (`Y`, `Z`, `E`, and `Λ` in `PathTransport`) live in `Type`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* W. P. Barth, K. Hulek, C. A. M. Peters, and A. Van de Ven, *Compact Complex Surfaces*, 2nd ed.,
  Springer, 2004, Chapter V.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§1.3, 3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function

namespace TauCeti

/-- `n`-th integral singular homology `Hₙ(q⁻¹ z; ℤ)` of the `z`-fiber of
`q = TauCeti.torusFamilyAffineQuotientMap`. -/
abbrev torusFamilyAffineQuotientFiberHomology {Y Z E : Type} [TopologicalSpace Y]
    [TopologicalSpace Z] [AddCommGroup E] [TopologicalSpace E] {Λ Γ : Type*} [AddCommGroup Λ]
    (P : Y → Λ →ₗ[ℤ] E) [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
    (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
    (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
    (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (z : Z) (n : ℕ) :=
  ((singularChains ℤ).obj (TopCat.of
    (torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ ⁻¹' {z}))).homology n

variable {Y Z E : Type} [TopologicalSpace Y] [TopologicalSpace Z] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Γ : Type*} [Group Γ] [MulAction Γ Y]

section SheetMarking

variable {Λ : Type*} [AddCommGroup Λ] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) {z : Z} (y : Y)

/-- **Sheet-indexed homology marking in degree `n`**, identifying `Hₙ(q⁻¹ z; ℤ)` (for
`q = TauCeti.torusFamilyAffineQuotientMap`) with `⋀[ℤ]^n Λ` via `y : Y` over `z = β y`. -/
def torusFamilyAffineQuotientHomologyMarking (hy : β y = z := by rfl) (n : ℕ) :
    torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n ≃ₗ[ℤ]
      ⋀[ℤ]^n Λ :=
  letI := periodAddAction P
  ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
    y hy).toHomotopyEquiv.singularHomologyIso (ModuleCat.of ℤ ℤ) n).symm.toLinearEquiv ≪≫ₗ
    torusFamilyHomologyMarking P hcont hinj y n

/-- `torusFamilyAffineQuotientHomologyMarking` pulls back to `y` and applies
`torusFamilyHomologyMarking`. -/
theorem torusFamilyAffineQuotientHomologyMarking_apply (hy : β y = z) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    letI := periodAddAction P
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n c = torusFamilyHomologyMarking P hcont hinj y n
      (ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass
        (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
          β hβ y hy).symm) c) := by
  let _ := periodAddAction P; rw [torusFamilyAffineQuotientHomologyMarking]
  exact (LinearEquiv.trans_apply c).trans <| congrArg _ <| congrArg (ModuleCat.Hom.hom · c) <|
    (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      y hy).toHomotopyEquiv.singularHomologyIso_inv (ModuleCat.of ℤ ℤ) n

/-- `(torusFamilyAffineQuotientHomologyMarking ...).symm` pushes `w` from sheet `y` to `q⁻¹ z`. -/
theorem torusFamilyAffineQuotientHomologyMarking_symm_apply (hy : β y = z) (n : ℕ) (w : ⋀[ℤ]^n Λ) :
    letI := periodAddAction P
    (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n).symm w = ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass
      (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
        β hβ y hy)) ((torusFamilyHomologyMarking P hcont hinj y n).symm w) := by
  let _ := periodAddAction P; rw [torusFamilyAffineQuotientHomologyMarking]
  exact (LinearEquiv.symm_trans_apply w).trans <| congrArg (ModuleCat.Hom.hom · _)
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      y hy).toHomotopyEquiv.singularHomologyIso_hom (ModuleCat.of ℤ ℤ) n)

/-- On a class from sheet `y`, the `y`-sheet marking recovers `torusFamilyHomologyMarking`. -/
@[simp] theorem torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph (hy : β y = z) (n : ℕ)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of (torusFamilyProjection P ⁻¹' {y}))).homology n) :
    letI := periodAddAction P
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass
          (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
            β hβ y hy)) c) = torusFamilyHomologyMarking P hcont hinj y n c := by
  let _ := periodAddAction P
  rw [torusFamilyAffineQuotientHomologyMarking_apply, ← ContinuousMap.singularHomologyMap_comp]
  simp only [Homeomorph.symm_comp_toContinuousMap, ContinuousMap.singularHomologyMap_id]

/-- **Sheet-indexed marking in degree one**, identifying `H₁(q⁻¹ z; ℤ)` with `Λ` via `y`. -/
def torusFamilyAffineQuotientMarking (hy : β y = z := by rfl) :
    torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1 ≃ₗ[ℤ] Λ :=
  torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
    y hy 1 ≪≫ₗ exteriorPower.oneEquiv ℤ Λ

/-- `exteriorPower.oneEquiv ℤ Λ` maps degree-`1` marking to `torusFamilyAffineQuotientMarking`. -/
@[simp] theorem oneEquiv_torusFamilyAffineQuotientHomologyMarking (hy : β y = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    exteriorPower.oneEquiv ℤ Λ (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv
      b hb hone hmul hbmul hR hbc β hβ y hy 1 c) =
      torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y hy c := (rfl)

/-- `torusFamilyAffineQuotientMarking` pulls back to `y` and applies `torusFamilyMarking`. -/
theorem torusFamilyAffineQuotientMarking_apply (hy : β y = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    letI := periodAddAction P
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y hy c = torusFamilyMarking P hcont hinj y (ContinuousMap.singularHomologyMap ℤ 1
      (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone
        hmul hbmul hcont hR hbc β hβ y hy).symm) c) :=
  let _ := periodAddAction P
  (congrArg (exteriorPower.oneEquiv ℤ Λ) (torusFamilyAffineQuotientHomologyMarking_apply P hcont
    hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy 1 c)).trans
    (oneEquiv_torusFamilyHomologyMarking P hcont hinj y _)

/-- `(torusFamilyAffineQuotientMarking ...).symm` pushes `l ∈ Λ` from sheet `y` to `q⁻¹ z`. -/
theorem torusFamilyAffineQuotientMarking_symm_apply (hy : β y = z) (l : Λ) :
    letI := periodAddAction P
    (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y hy).symm l = ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.ofClass
      (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
        β hβ y hy)) ((torusFamilyMarking P hcont hinj y).symm l) := by
  let _ := periodAddAction P
  have hmark : torusFamilyMarking P hcont hinj y =
      torusFamilyHomologyMarking P hcont hinj y 1 ≪≫ₗ exteriorPower.oneEquiv ℤ Λ :=
    LinearEquiv.ext fun c ↦ (oneEquiv_torusFamilyHomologyMarking P hcont hinj y c).symm
  rw [torusFamilyAffineQuotientMarking, hmark, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_trans_apply, torusFamilyAffineQuotientHomologyMarking_symm_apply]

/-- On a degree-one class from sheet `y`, the `y`-sheet marking recovers `torusFamilyMarking`. -/
@[simp] theorem torusFamilyAffineQuotientMarking_fiberHomeomorph (hy : β y = z)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of (torusFamilyProjection P ⁻¹' {y}))).homology 1) :
    letI := periodAddAction P
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy
        (ContinuousMap.singularHomologyMap ℤ 1 (ContinuousMap.ofClass
          (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
            β hβ y hy)) c) = torusFamilyMarking P hcont hinj y c :=
  let _ := periodAddAction P
  (congrArg (exteriorPower.oneEquiv ℤ Λ) (torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph
    P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy 1 c)).trans
    (oneEquiv_torusFamilyHomologyMarking P hcont hinj y c)

/-- **Sheet-change law in degree `n`:** `y ↦ g • y` acts by `ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_smul (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ (g • y) hgy n c = ρ.exteriorPower n g (torusFamilyAffineQuotientHomologyMarking P
      hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy n c) := by
  let _ := periodAddAction P
  rw [torusFamilyAffineQuotientHomologyMarking_apply,
    torusFamilyAffineQuotientHomologyMarking_apply]
  let e y' (hy' : β y' = z) := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul
    hbmul hcont hR hbc β hβ y' hy'
  let φ : C(torusFamilyProjection P ⁻¹' {y}, torusFamilyProjection P ⁻¹' {g • y}) :=
    (ContinuousMap.ofClass (e (g • y) hgy).symm).comp (ContinuousMap.ofClass (e y hy))
  have hcomp : ContinuousMap.ofClass (e (g • y) hgy).symm =
      φ.comp (ContinuousMap.ofClass (e y hy).symm) := by ext; simp [φ]
  rw [hcomp, ContinuousMap.singularHomologyMap_comp, Representation.exteriorPower_apply]
  exact torusFamilyHomologyMarking_singularHomologyMap_affineMap P hcont hinj R ρ hequiv b hb φ
    (torusFamilyAffineQuotientFiberHomeomorph_smul_symm_apply P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ y hy g hgy) ((hR g).comp (continuous_const.prodMk continuous_id)) n _

/-- **Sheet-change law in degree one:** `y ↦ g • y` acts by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_smul (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        (g • y) hgy c = ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone
      hmul hbmul hR hbc β hβ y hy c) :=
  (congrArg _ (torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone
    hmul hbmul hR hbc β hβ y hy g hgy 1 c)).trans (ρ.oneEquiv_exteriorPower_apply g _)

end SheetMarking

section PathTransport

variable {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g)) (β : Y → Z)
  (hβ : IsQuotientCoveringMap β Γ)
  (L : LiftingFunction (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom)

/-- **Transport along a lifted path preserves sheet markings** between `y₀` and `y₁`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift {z₀ z₁ : Z} {y₀ y₁ : Y}
    (hy₀ : β y₀ = z₀) (hy₁ : β y₁ = z₁) (γ : Path z₀ z₁) (γ' : Path y₀ y₁)
    (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y₁ hy₁ n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y₀ hy₀ n c := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let LY := torusFamilyLiftingFunction P hcont hinj
  let e {z'} y' (hy' : β y' = z') := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb
    hone hmul hbmul hcont hR hbc β hβ y' hy'
  let hcoe {z'} y' (hy' : β y' = z') := torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv
    b hb hone hmul hbmul hcont hR hbc β hβ y' hy'
  have hhom := L.transport_comp_homotopic_of_map_eq LY (g := ⟨Quotient.mk _, continuous_quot_mk⟩)
    (f := ⟨β, hβ.continuous⟩) (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul
      β _) γ' γ hγ' (g₀ := ContinuousMap.ofClass (e y₀ hy₀))
    (g₁ := ContinuousMap.ofClass (e y₁ hy₁)) (hcoe y₀ hy₀) (hcoe y₁ hy₁)
  set d := ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass (e y₀ hy₀).symm) c
  have hc : ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass (e y₀ hy₀)) d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]; simp [Homeomorph.toContinuousMap_comp_symm]
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp,
    LinearMap.congr_fun (ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ n hhom) d,
    ContinuousMap.singularHomologyMap_comp,
    torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph,
    torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph]
  exact torusFamilyHomologyMarking_transport P hcont hinj LY γ' n d

/-- **Degree-one transport along a lifted path.** -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift {z₀ z₁ : Z} {y₀ y₁ : Y}
    (hy₀ : β y₀ = z₀) (hy₁ : β y₁ = z₁) (γ : Path z₀ z₁) (γ' : Path y₀ y₁)
    (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y₁ hy₁ (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y₀ hy₀ c :=
  congrArg (exteriorPower.oneEquiv ℤ Λ) (torusFamilyAffineQuotientHomologyMarking_transport_of_lift
    P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy₀ hy₁ γ γ' hγ' 1 c)

/-- **Compatibility with covering-space monodromy** `hβ.isCoveringMap.monodromy (.mk γ) e`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_monodromy {z₀ z₁ : Z} (γ : Path z₀ z₁)
    (e : β ⁻¹' {z₀}) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ n) :
    let e' := hβ.isCoveringMap.monodromy (.mk γ) e
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ e'.val e'.property n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ e.val e.property n c :=
  have h0 : γ.toContinuousMap 0 = β e.val := γ.source.trans e.property.symm
  torusFamilyAffineQuotientHomologyMarking_transport_of_lift P hcont hinj R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ L e.property (hβ.isCoveringMap.monodromy (.mk γ) e).property γ
    ⟨hβ.isCoveringMap.liftPath γ.toContinuousMap e.val h0,
      hβ.isCoveringMap.liftPath_zero γ.toContinuousMap e.val h0,
      (hβ.isCoveringMap.coe_monodromy_mk γ e).symm⟩
    (congr_fun (hβ.isCoveringMap.liftPath_lifts γ.toContinuousMap e.val h0)) n c

/-- **Degree-one compatibility with covering-space monodromy** `hβ.isCoveringMap.monodromy`. -/
theorem torusFamilyAffineQuotientMarking_transport_monodromy {z₀ z₁ : Z} (γ : Path z₀ z₁)
    (e : β ⁻¹' {z₀})
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ 1) :
    let e' := hβ.isCoveringMap.monodromy (.mk γ) e
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        e'.val e'.property (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        e.val e.property c :=
  congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyAffineQuotientHomologyMarking_transport_monodromy P hcont hinj R ρ hequiv b hb hone
      hmul hbmul hR hbc β hβ L γ e 1 c)

section LoopLift

variable {z : Z} {y : Y} (hy : β y = z) {g : Γ}

/-- **Monodromy in degree `n` for a loop lifted `y ↝ g • y`**, acting by `ρ.exteriorPower n g⁻¹`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul (γ : Path z z)
    (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n g⁻¹ (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) := by
  have hgy : β (g • y) = z := (hβ.map_smul g).trans hy
  have hinv := congrArg (ρ.exteriorPower n g⁻¹) <|
    (torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy g hgy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c)).symm.trans
      (torusFamilyAffineQuotientHomologyMarking_transport_of_lift P hcont hinj R ρ hequiv b hb hone
        hmul hbmul hR hbc β hβ L hy hgy γ γ' hγ' n c)
  simpa only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self] using hinv

/-- **Monodromy in degree one for a loop lifted `y ↝ g • y`**, acting by `ρ g⁻¹`. -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift_smul (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy
        (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ g⁻¹ (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy c) :=
  (congrArg _ (torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ
    hequiv b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' 1 c)).trans
    (ρ.oneEquiv_exteriorPower_apply g⁻¹ _)

/-- **Monodromy in degree `n` for a loop lifted `y ↝ g⁻¹ • y`**, acting by `ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift_inv_smul (γ : Path z z)
    (γ' : Path y (g⁻¹ • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n g (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) := by
  simpa only [inv_inv] using torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont
    hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy (g := g⁻¹) γ γ' hγ' n c

/-- **Monodromy in degree one for a loop lifted `y ↝ g⁻¹ • y`**, acting by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift_inv_smul (γ : Path z z)
    (γ' : Path y (g⁻¹ • y)) (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy
        (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy c) := by
  simpa only [inv_inv] using torusFamilyAffineQuotientMarking_transport_of_lift_smul P hcont hinj
    R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy (g := g⁻¹) γ γ' hγ' c

/-- **Loop reversal in degree `n`:** transport along `γ.symm` acts by `ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_symm_of_lift_smul (γ : Path z z)
    (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ.symm) c) =
      ρ.exteriorPower n g (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) :=
  have := hβ.toContinuousConstSMul
  torusFamilyAffineQuotientHomologyMarking_transport_of_lift_inv_smul P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc β hβ L hy γ.symm
    ⟨⟨fun t ↦ g⁻¹ • γ'.symm t, (continuous_const_smul g⁻¹).comp γ'.symm.continuous⟩,
      by simp [inv_smul_smul], by simp⟩
    (fun t ↦ (hβ.map_smul g⁻¹).trans (hγ' (unitInterval.symm t))) n c

/-- **Loop reversal in degree one:** transport along `γ.symm` acts by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_transport_symm_of_lift_smul (γ : Path z z)
    (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ y hy
        (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ.symm) c) =
      ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ y hy c) :=
  (congrArg _ (torusFamilyAffineQuotientHomologyMarking_transport_symm_of_lift_smul P hcont hinj
    R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' 1 c)).trans
    (ρ.oneEquiv_exteriorPower_apply g _)

/-- **Conjugation of the marking in degree `n`** in an arbitrary linear marking `ν`. -/
theorem
  apply_singularHomologyMap_transport_of_lift_smul_eq_conj_torusFamilyAffineQuotientHomologyMarking
    (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ) {N : Type*}
    [AddCommGroup N]
    (ν : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n ≃ₗ[ℤ] N)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    ν (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ((torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n).symm.trans ν).conj (ρ.exteriorPower n g⁻¹) (ν c) := by
  have h := torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' n c; simp [LinearEquiv.eq_symm_apply, h]

/-- **Conjugation of the marking in degree one.** -/
theorem apply_singularHomologyMap_transport_of_lift_smul_eq_conj_torusFamilyAffineQuotientMarking
    (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) {N : Type*} [AddCommGroup N]
    (ν : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1 ≃ₗ[ℤ] N)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    ν (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ((torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        y hy).symm.trans ν).conj (ρ g⁻¹) (ν c) := by
  have h := torusFamilyAffineQuotientMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb
    hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' c; simp [← h]

include hy in
/-- **Conjugation under change of base sheet in degree `n`:** `h • y` conjugates by `h`. -/
theorem torusFamilyAffineQuotientHomologyMarking_smul_transport_of_lift_smul (h : Γ)
    (hhy : β (h • y) = z) (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ (h • y) hhy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n (h * g⁻¹ * h⁻¹) (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ
        hequiv b hb hone hmul hbmul hR hbc β hβ (h • y) hhy n c) := by
  rw [torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy h hhy n, torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P
      hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' n c,
    torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy h hhy n]
  simp only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel_right]

include hy in
/-- **Conjugation under change of base sheet in degree one.** -/
theorem torusFamilyAffineQuotientMarking_smul_transport_of_lift_smul (h : Γ) (hhy : β (h • y) = z)
    (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        (h • y) hhy (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ (h * g⁻¹ * h⁻¹) (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ (h • y) hhy c) :=
  (congrArg _ (torusFamilyAffineQuotientHomologyMarking_smul_transport_of_lift_smul P hcont hinj
    R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L hy h hhy γ γ' hγ' 1 c)).trans
    (ρ.oneEquiv_exteriorPower_apply (h * g⁻¹ * h⁻¹) _)

end LoopLift

end PathTransport

end TauCeti
