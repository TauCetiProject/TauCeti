/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.QuotientPullback
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.LocalSystem

/-!
# Sheet markings and monodromy of a descended family of tori

For a continuous full-lattice family `P : Y → Λ →ₗ[ℤ] E` with a continuous affine `Γ`-action
intertwining `P` with `ρ : Representation ℤ Γ Λ` and a quotient covering `β : Y → Z` by `Γ`, a
sheet `y` over `z = β y` yields markings `TauCeti.torusFamilyAffineQuotientHomologyMarking`
(`Hₙ(q⁻¹ z; ℤ) ≃ₗ[ℤ] ⋀[ℤ]^n Λ`) and `TauCeti.torusFamilyAffineQuotientMarking`
(`H₁(q⁻¹ z; ℤ) ≃ₗ[ℤ] Λ`):

* `TauCeti.torusFamilyAffineQuotientHomologyMarking_smul` and
  `TauCeti.torusFamilyAffineQuotientMarking_smul`: sheet change `y ↦ g • y` acts by
  `ρ.exteriorPower n g` (`ρ g` in degree `1`).
* `TauCeti.torusFamilyAffineQuotientHomologyMarking_transport_of_lift`,
  `TauCeti.torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul`, and
  `TauCeti.torusFamilyAffineQuotientHomologyMarking_transport_monodromy`: Hurewicz transport along a
  loop lifted from `y` to `g • y` acts by `ρ.exteriorPower n g⁻¹` (`ρ g⁻¹` in degree `1`), with
  reversal, marking-conjugation, and base-sheet change formulas.

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

/-! ### Sheet-indexed homology markings and the sheet-change law -/

section SheetMarking

variable {Y Z E : Type} [TopologicalSpace Y] [TopologicalSpace Z] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Λ : Type*} [AddCommGroup Λ] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  {Γ : Type*} [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)

omit [TopologicalSpace Y] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  hcont hinj hR hbc in
/-- The `n`-th integral singular homology `Hₙ(q⁻¹ z; ℤ)` of the descended torus fiber over `z`. -/
abbrev torusFamilyAffineQuotientFiberHomology (z : Z) (n : ℕ) :=
  ((singularChains ℤ).obj (TopCat.of
    (torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ ⁻¹' {z}))).homology n

/-- **Sheet-indexed homology marking in degree `n`**, identifying `Hₙ(q⁻¹ z; ℤ)` with `⋀[ℤ]^n Λ` via
the chosen sheet `y : Y` over `z : Z` (`β y = z`). -/
def torusFamilyAffineQuotientHomologyMarking {z : Z} (y : Y) (hy : β y = z := by rfl) (n : ℕ) :
    torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n ≃ₗ[ℤ]
      ⋀[ℤ]^n Λ :=
  letI := periodAddAction P
  ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y hy).toHomotopyEquiv.singularHomologyIso
      (ModuleCat.of ℤ ℤ) n).symm.toLinearEquiv ≪≫ₗ
    torusFamilyHomologyMarking P hcont hinj y n

/-- `torusFamilyAffineQuotientHomologyMarking` pulls a class back to the `y`-sheet fiber and applies
`torusFamilyHomologyMarking`. -/
theorem torusFamilyAffineQuotientHomologyMarking_apply {z : Z} (y : Y) (hy : β y = z) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    letI := periodAddAction P
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n c =
      torusFamilyHomologyMarking P hcont hinj y n
        (ContinuousMap.singularHomologyMap ℤ n
          (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb
            hone hmul hbmul hcont hR hbc β hβ y hy).symm) c) := by
  let _ := periodAddAction P
  rw [torusFamilyAffineQuotientHomologyMarking]
  refine (LinearEquiv.trans_apply c).trans (congrArg _ (congrArg (ModuleCat.Hom.hom · c) ?_))
  exact (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y hy).toHomotopyEquiv.singularHomologyIso_inv (ModuleCat.of ℤ ℤ) n

/-- `(torusFamilyAffineQuotientHomologyMarking ...).symm` pushes `w ∈ ⋀[ℤ]^n Λ` from the `y`-sheet
fiber into the descended fiber over `z`. -/
theorem torusFamilyAffineQuotientHomologyMarking_symm_apply {z : Z} (y : Y) (hy : β y = z) (n : ℕ)
    (w : ⋀[ℤ]^n Λ) :
    letI := periodAddAction P
    (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n).symm w =
      ContinuousMap.singularHomologyMap ℤ n
        (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb
          hone hmul hbmul hcont hR hbc β hβ y hy))
        ((torusFamilyHomologyMarking P hcont hinj y n).symm w) := by
  let _ := periodAddAction P
  rw [torusFamilyAffineQuotientHomologyMarking]
  exact (LinearEquiv.symm_trans_apply w).trans <| congrArg (ModuleCat.Hom.hom · _)
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ y hy).toHomotopyEquiv.singularHomologyIso_hom (ModuleCat.of ℤ ℤ) n)

/-- On a class carried from the `y`-sheet fiber, the `y`-sheet marking recovers
`torusFamilyHomologyMarking` at `y`. -/
@[simp] theorem torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph {z : Z} (y : Y)
    (hy : β y = z) (n : ℕ) (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of (torusFamilyProjection P ⁻¹' {y}))).homology n) :
    letI := periodAddAction P
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n
        (ContinuousMap.singularHomologyMap ℤ n
          (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb
            hone hmul hbmul hcont hR hbc β hβ y hy)) c) =
      torusFamilyHomologyMarking P hcont hinj y n c := by
  let _ := periodAddAction P
  rw [torusFamilyAffineQuotientHomologyMarking_apply, ← ContinuousMap.singularHomologyMap_comp]
  simp only [Homeomorph.symm_comp_toContinuousMap, ContinuousMap.singularHomologyMap_id]

/-- **Sheet-indexed marking in degree one**, identifying `H₁(q⁻¹ z; ℤ)` with `Λ` via `y`. -/
def torusFamilyAffineQuotientMarking {z : Z} (y : Y) (hy : β y = z := by rfl) :
    torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1 ≃ₗ[ℤ] Λ :=
  torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc β hβ y hy 1 ≪≫ₗ exteriorPower.oneEquiv ℤ Λ

/-- Under `exteriorPower.oneEquiv ℤ Λ`, the degree-one `y`-sheet marking is
`torusFamilyAffineQuotientMarking`. -/
@[simp] theorem oneEquiv_torusFamilyAffineQuotientHomologyMarking {z : Z} (y : Y) (hy : β y = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    exteriorPower.oneEquiv ℤ Λ
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ y hy 1 c) =
      torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c := (rfl)

/-- `torusFamilyAffineQuotientMarking` pulls a degree-one class back to the `y`-sheet fiber and
applies `torusFamilyMarking`. -/
theorem torusFamilyAffineQuotientMarking_apply {z : Z} (y : Y) (hy : β y = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    letI := periodAddAction P
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c =
      torusFamilyMarking P hcont hinj y
        (ContinuousMap.singularHomologyMap ℤ 1
          (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb
            hone hmul hbmul hcont hR hbc β hβ y hy).symm) c) := by
  let _ := periodAddAction P
  rw [← oneEquiv_torusFamilyAffineQuotientHomologyMarking,
    torusFamilyAffineQuotientHomologyMarking_apply]
  exact oneEquiv_torusFamilyHomologyMarking P hcont hinj y _

/-- **Sheet-change law in degree `n`.** Changing the sheet over `z` from `y` to `g • y` multiplies
the degree-`n` homology marking by `ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_smul {z : Z} (y : Y) (hy : β y = z)
    (g : Γ) (hgy : β (g • y) = z) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (g • y) hgy n c =
      ρ.exteriorPower n g
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ y hy n c) := by
  let _ := periodAddAction P
  let ey := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y hy
  let egy := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ (g • y) hgy
  let φ : C(torusFamilyProjection P ⁻¹' {y}, torusFamilyProjection P ⁻¹' {g • y}) :=
    (ContinuousMap.ofClass egy.symm).comp (ContinuousMap.ofClass ey)
  have hcomp : ContinuousMap.ofClass egy.symm = φ.comp (ContinuousMap.ofClass ey.symm) := by
    ext; simp [φ]
  have hRgy : Continuous (R g y) := (hR g).comp (continuous_const.prodMk continuous_id)
  rw [torusFamilyAffineQuotientHomologyMarking_apply,
    torusFamilyAffineQuotientHomologyMarking_apply]
  change torusFamilyHomologyMarking P hcont hinj (g • y) n
      (ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass egy.symm) c) =
    ρ.exteriorPower n g (torusFamilyHomologyMarking P hcont hinj y n
      (ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass ey.symm) c))
  rw [hcomp, ContinuousMap.singularHomologyMap_comp]
  exact torusFamilyHomologyMarking_singularHomologyMap_affineMap P hcont hinj R ρ hequiv b hb φ
    (fun u ↦ torusFamilyAffineQuotientFiberHomeomorph_smul_symm_apply P R ρ hequiv b hb hone hmul
      hbmul hcont hR hbc β hβ y hy g hgy u) hRgy n _

/-- **Sheet-change law in degree one.** Changing `y` to `g • y` multiplies by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_smul {z : Z} (y : Y) (hy : β y = z)
    (g : Γ) (hgy : β (g • y) = z)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (g • y) hgy c =
      ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c) := by
  rw [← oneEquiv_torusFamilyAffineQuotientHomologyMarking,
    torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy g hgy 1 c, Representation.exteriorPower_apply]
  exact LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (ρ g)) _

end SheetMarking

/-! ### Hurewicz transport along lifted paths and the monodromy formula -/

section PathTransport

variable {Y Z Λ E : Type} [TopologicalSpace Y] [TopologicalSpace Z] [AddCommGroup Λ]
  [Module.Free ℤ Λ] [Module.Finite ℤ Λ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hinj : ∀ y, Injective (P y)) {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)
  (L : LiftingFunction
    (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom)

/-- **Transport along a lifted path preserves sheet markings.** Hurewicz transport along
`γ : Path z₀ z₁` lifted to `γ' : Path y₀ y₁` intertwines the `y₀`- and `y₁`-sheet markings. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift
    {z₀ z₁ : Z} {y₀ y₁ : Y} (hy₀ : β y₀ = z₀) (hy₁ : β y₁ = z₁)
    (γ : Path z₀ z₁) (γ' : Path y₀ y₁) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y₁ hy₁ n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y₀ hy₀ n c := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let LY := torusFamilyLiftingFunction P hcont hinj
  let e₀ := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y₀ hy₀
  let e₁ := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y₁ hy₁
  have hhom : ((L.transport γ).comp (ContinuousMap.ofClass e₀)).Homotopic
      ((ContinuousMap.ofClass e₁).comp (LY.transport γ')) :=
    L.transport_comp_homotopic_of_map_eq LY
      (g := ⟨Quotient.mk _, continuous_quot_mk⟩) (f := ⟨β, hβ.continuous⟩)
      (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _) γ' γ hγ'
      (fun u ↦ torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv b hb hone hmul hbmul
        hcont hR hbc β hβ y₀ hy₀ u)
      (fun u ↦ torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv b hb hone hmul hbmul
        hcont hR hbc β hβ y₁ hy₁ u)
  set d := ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e₀.symm) c
  have hc : ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e₀) d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]; simp [Homeomorph.toContinuousMap_comp_symm]
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp,
    LinearMap.congr_fun (ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ n hhom) d,
    ContinuousMap.singularHomologyMap_comp,
    torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph,
    torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph]
  exact torusFamilyHomologyMarking_transport P hcont hinj LY γ' n d

/-- **Degree-one transport along a lifted path.** -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift
    {z₀ z₁ : Z} {y₀ y₁ : Y} (hy₀ : β y₀ = z₀) (hy₁ : β y₁ = z₁)
    (γ : Path z₀ z₁) (γ' : Path y₀ y₁) (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y₁ hy₁ (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y₀ hy₀ c :=
  congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyAffineQuotientHomologyMarking_transport_of_lift P hcont hinj R ρ hequiv b hb hone
      hmul hbmul hR hbc β hβ L hy₀ hy₁ γ γ' hγ' 1 c)

/-- **Monodromy in degree `n` for a loop lifted from `y` to `g • y`**, acting by
`ρ.exteriorPower n g⁻¹`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n g⁻¹ (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) := by
  have hgy : β (g • y) = z := (hβ.map_smul g).trans hy
  have hy' : β (g⁻¹ • (g • y)) = z := (inv_smul_smul g y).symm ▸ hy
  have hback := torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone
    hmul hbmul hR hbc β hβ (g • y) hgy g⁻¹ hy' n
    (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c)
  have hcongr : ∀ {y' : Y} (_ : y' = y) (hy'' : β y' = z),
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y' hy'' n =
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n := by rintro _ rfl _; rfl
  rw [hcongr (inv_smul_smul g y) hy'] at hback
  exact hback.trans (congrArg (ρ.exteriorPower n g⁻¹)
    (torusFamilyAffineQuotientHomologyMarking_transport_of_lift P hcont hinj R ρ hequiv b hb hone
      hmul hbmul hR hbc β hβ L hy hgy γ γ' hγ' n c))

/-- **Monodromy in degree one for a loop lifted from `y` to `g • y`**, acting by `ρ g⁻¹`. -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ g⁻¹ (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c) := by
  rw [← oneEquiv_torusFamilyAffineQuotientHomologyMarking,
    torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb
      hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' 1 c, Representation.exteriorPower_apply]
  exact LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (ρ g⁻¹)) _

/-- **Monodromy in degree `n` for a loop lifted from `y` to `g⁻¹ • y`**, acting by
`ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_of_lift_inv_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g⁻¹ • y))
    (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n g (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) := by
  simpa only [inv_inv] using
    torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb
      hone hmul hbmul hR hbc β hβ L hy (g := g⁻¹) γ γ' hγ' n c

/-- **Monodromy in degree one for a loop lifted from `y` to `g⁻¹ • y`**, acting by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_transport_of_lift_inv_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g⁻¹ • y))
    (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c) := by
  simpa only [inv_inv] using
    torusFamilyAffineQuotientMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ L hy (g := g⁻¹) γ γ' hγ' c

/-- **Compatibility with covering-space monodromy** `hβ.isCoveringMap.monodromy (.mk γ) e`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_monodromy
    {z₀ z₁ : Z} (γ : Path z₀ z₁) (e : β ⁻¹' {z₀}) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z₀ n) :
    let e' := hβ.isCoveringMap.monodromy (.mk γ) e
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ e'.1 e'.2 n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ e.1 e.2 n c := by
  have h0 : γ.toContinuousMap 0 = β e.1 := γ.source.trans e.2.symm
  let γ' : Path e.1 (hβ.isCoveringMap.monodromy (.mk γ) e).1 :=
    ⟨hβ.isCoveringMap.liftPath γ.toContinuousMap e.1 h0,
      hβ.isCoveringMap.liftPath_zero γ.toContinuousMap e.1 h0,
      (hβ.isCoveringMap.coe_monodromy_mk γ e).symm⟩
  exact torusFamilyAffineQuotientHomologyMarking_transport_of_lift P hcont hinj R ρ hequiv b hb
    hone hmul hbmul hR hbc β hβ L e.2 (hβ.isCoveringMap.monodromy (.mk γ) e).2 γ γ'
    (fun t ↦ congr_fun (hβ.isCoveringMap.liftPath_lifts γ.toContinuousMap e.1 h0) t) n c

/-- **Loop reversal in degree `n`:** transport along `γ.symm` acts by `ρ.exteriorPower n g`. -/
theorem torusFamilyAffineQuotientHomologyMarking_transport_symm_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ.symm) c) =
      ρ.exteriorPower n g (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ y hy n c) := by
  have := hβ.toContinuousConstSMul
  let γ'rev : Path y (g⁻¹ • y) :=
    ⟨⟨fun t ↦ g⁻¹ • γ'.symm t, (continuous_const_smul g⁻¹).comp γ'.symm.continuous⟩,
      by simp [inv_smul_smul], by simp⟩
  exact torusFamilyAffineQuotientHomologyMarking_transport_of_lift_inv_smul P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc β hβ L hy γ.symm γ'rev
    (fun t ↦ (hβ.map_smul g⁻¹).trans (hγ' (unitInterval.symm t))) n c

/-- **Loop reversal in degree one:** transport along `γ.symm` acts by `ρ g`. -/
theorem torusFamilyAffineQuotientMarking_transport_symm_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ.symm) c) =
      ρ g (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy c) := by
  rw [← oneEquiv_torusFamilyAffineQuotientHomologyMarking,
    torusFamilyAffineQuotientHomologyMarking_transport_symm_of_lift_smul P hcont hinj R ρ hequiv
      b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' 1 c, Representation.exteriorPower_apply]
  exact LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (ρ g)) _

/-- **Conjugation of the marking in degree `n`** in an arbitrary linear marking `ν`. -/
theorem apply_torusFamilyAffineQuotientTransport_of_lift_smul_eq_conj
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ) {N : Type*} [AddCommGroup N]
    (ν : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n ≃ₗ[ℤ] N)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    ν (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ((torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy n).symm.trans ν).conj (ρ.exteriorPower n g⁻¹) (ν c) := by
  have h := torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' n c
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply, ← h, LinearEquiv.symm_apply_apply]

/-- **Conjugation of the marking in degree one.** -/
theorem apply_torusFamilyAffineQuotientTransport_of_lift_smul_eq_conj_one
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (γ : Path z z) (γ' : Path y (g • y))
    (hγ' : ∀ t, β (γ' t) = γ t) {N : Type*} [AddCommGroup N]
    (ν : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1 ≃ₗ[ℤ] N)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    ν (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ((torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ y hy).symm.trans ν).conj (ρ g⁻¹) (ν c) := by
  have h := torusFamilyAffineQuotientMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb
    hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' c
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply, ← h, LinearEquiv.symm_apply_apply]

/-- **Conjugation under change of base sheet in degree `n`:** `h • y` conjugates by `h`. -/
theorem torusFamilyAffineQuotientHomologyMarking_smul_transport_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (h : Γ) (hhy : β (h • y) = z)
    (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t) (n : ℕ)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z n) :
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (h • y) hhy n (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      ρ.exteriorPower n (h * g⁻¹ * h⁻¹) (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ
        hequiv b hb hone hmul hbmul hR hbc β hβ (h • y) hhy n c) := by
  rw [torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy h hhy n,
    torusFamilyAffineQuotientHomologyMarking_transport_of_lift_smul P hcont hinj R ρ hequiv b hb
      hone hmul hbmul hR hbc β hβ L hy γ γ' hγ' n c,
    torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ y hy h hhy n]
  simp only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel_right]

/-- **Conjugation under change of base sheet in degree one.** -/
theorem torusFamilyAffineQuotientMarking_smul_transport_of_lift_smul
    {z : Z} {y : Y} (hy : β y = z) {g : Γ} (h : Γ) (hhy : β (h • y) = z)
    (γ : Path z z) (γ' : Path y (g • y)) (hγ' : ∀ t, β (γ' t) = γ t)
    (c : torusFamilyAffineQuotientFiberHomology P R ρ hequiv b hb hone hmul hbmul β hβ z 1) :
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (h • y) hhy (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      ρ (h * g⁻¹ * h⁻¹) (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ (h • y) hhy c) := by
  rw [← oneEquiv_torusFamilyAffineQuotientHomologyMarking,
    torusFamilyAffineQuotientHomologyMarking_smul_transport_of_lift_smul P hcont hinj R ρ hequiv
      b hb hone hmul hbmul hR hbc β hβ L hy h hhy γ γ' hγ' 1 c, Representation.exteriorPower_apply]
  exact LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (ρ (h * g⁻¹ * h⁻¹))) _

end PathTransport

end TauCeti
