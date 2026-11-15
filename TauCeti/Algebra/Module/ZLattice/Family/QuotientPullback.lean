/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.AffineQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.Fibration
public import TauCeti.Geometry.Manifold.Quotient.Pullback
public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial

/-!
# Recovering a torus family through a covering of the base

Let `X = (Y × E)/Λ` be a varying period quotient, with an affine action of `Γ` lifting
an action on `Y`, and let `β : Y → Z` be a quotient covering by `Γ`. The canonical map
`x ↦ (p x, [x])` identifies `X` with the literal pullback of `X/Γ → Z` along `β`.
The inverse takes an orbit representative and translates it to the specified base point.

Restricting to a single sheet `y : Y` over `z = β y` identifies the torus fibre over `y`
homeomorphically with the descended fibre over `z`
(`TauCeti.torusFamilyAffineQuotientFiberHomeomorph`), with sheet transition from `g • y`
back to `y` given by the inverse affine action `g⁻¹ • ·`. Combining the global topological
product decomposition `TauCeti.torusFamilyHomeomorphProd` upstairs with local inverses of `β`
supplies local trivializations of the descended projection `X/Γ → Z`
(`TauCeti.exists_trivialization_torusFamilyAffineQuotientLift`), making `X/Γ → Z` (and in
particular `X/Γ → Y/Γ` over a free properly discontinuous second-countable locally compact
Hausdorff base) a Hurewicz and Serre fibration
(`TauCeti.isHurewiczFibration_torusFamilyAffineQuotientLift`,
`TauCeti.isHurewiczFibration_orbitRelQuotientMap_torusFamilyAffineProjection`).

This is the covering comparison for cyclic quotients over a punctured disc. It allows
nontrivial linear monodromy and does not identify the quotient downstairs with a family
extending across the puncture. The lattice continues to vary with the base point.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*,
  second edition, Chapter V, section on logarithmic transformations.
-/

public section

open CategoryTheory Function Topology
open scoped Manifold ContDiff

universe w u

namespace TauCeti

section Topology

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  (P : Y → Λ →ₗ[ℤ] E) {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : ∀ g, Continuous (b g))
  {Z : Type*} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)

/-- The upstairs torus family is the pullback of its affine quotient through the quotient
covering of the base, via `x ↦ (p x, [x])`. The target has the product subspace topology. -/
noncomputable def torusFamilyAffineQuotientPullbackHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ₜ
      β.Pullback (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientPullbackHomeomorph β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)

/-- The covering comparison preserves the base point and records the affine orbit. -/
@[simp] theorem torusFamilyAffineQuotientPullbackHomeomorph_val
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ x).1 = (torusFamilyProjection P x, Quotient.mk _ x) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  simp only [torusFamilyAffineQuotientPullbackHomeomorph,
    MulActionHom.orbitRelQuotientPullbackHomeomorph_apply,
    MulActionHom.orbitRelQuotientPullback_val]
  rfl

/-- The inverse covering comparison sends `(g • y, [[y, v]])` to `g • [y, v]`.
This formula allows arbitrary linear and translation parts of the affine action. -/
@[simp] theorem torusFamilyAffineQuotientPullbackHomeomorph_symm_mk
    (g : Γ) (y : Y) (v : E) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ).symm
        ⟨(g • y, Quotient.mk _ (Quotient.mk _ (y, v))), by
          simpa only [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk] using
            hβ.map_smul g (e := y)⟩ =
      g • (Quotient.mk _ (y, v) : AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  apply (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ).injective
  apply Subtype.ext
  simp only [Homeomorph.apply_symm_apply, torusFamilyAffineQuotientPullbackHomeomorph_val]
  exact Prod.ext (by simp [hb]) MulAction.orbitRel.Quotient.quotient_smul_eq.symm

/-- For any sheet `y : Y` over `z : Z` (`β y = z`), the orbit map restricts to a homeomorphism
between the torus fibre over `y` upstairs and the fibre of the descended projection over `z`. -/
noncomputable def torusFamilyAffineQuotientFiberHomeomorph {z : Z} (y : Y)
    (hy : β y = z := by rfl) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    torusFamilyProjection P ⁻¹' {y} ≃ₜ
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g) ⁻¹' {z} := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientFiberHomeomorph β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    y hy

/-- `torusFamilyAffineQuotientFiberHomeomorph` sends a point in the `y`-fibre to its `Γ`-orbit. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_coe {z : Z} (y : Y) (hy : β y = z)
    (u : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {y}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ y hy u :
        MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) =
      Quotient.mk _ u.1 := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientFiberHomeomorph_coe β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    y hy u

/-- Pulling an orbit class `[x]` with `torusFamilyProjection P x = g • y` back to the `y`-sheet
fibre translates `x` by the inverse affine action `g⁻¹`. -/
theorem torusFamilyAffineQuotientFiberHomeomorph_symm_mk_of_smul
    {z : Z} (y : Y) (hy : β y = z) (g : Γ)
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = g • y)
    (hq : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g) (Quotient.mk _ x) = z) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ y hy).symm ⟨Quotient.mk _ x, hq⟩ :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g⁻¹ x := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact (p.orbitRelQuotientFiberHomeomorph_symm_mk_of_smul β _
      (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
      (continuous_torusFamilyProjection P) hβ
      (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
      y hy g hx hq).trans (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g⁻¹ x)

/-- Identifying the `(g • y)`-sheet fibre back with the `y`-sheet fibre through the common
descended fibre over `z` acts by `torusFamilyAffineMap ... g⁻¹`. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_symm_apply_smul
    {z : Z} (y : Y) (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (v : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {g • y}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ y hy).symm
        (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
          hcont hR hbc β hβ (g • y) hgy v) :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g⁻¹ v.1 := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact (p.orbitRelQuotientFiberHomeomorph_symm_apply_smul β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    y hy g hgy v).trans (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g⁻¹ v.1)

/-- Identifying the `y`-sheet fibre with the `(g • y)`-sheet fibre through the common descended
fibre over `z` acts by `torusFamilyAffineMap ... g`. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_smul_symm_apply
    {z : Z} (y : Y) (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (u : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {y}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ (g • y) hgy).symm
        (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
          hcont hR hbc β hβ y hy u) :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g u.1 := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact (p.orbitRelQuotientFiberHomeomorph_smul_symm_apply β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    y hy g hgy u).trans (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g u.1)

end Topology

section CommSq

variable {Y Z E : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  {Λ : Type*} [AddCommGroup Λ] [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  (P : Y → Λ →ₗ[ℤ] E) {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  {β : Y → Z}

omit [ContinuousAdd E] in
/-- The commutative square in `TopCat` relating the upstairs torus family `(Y × E)/Λ → Y` to its
descended quotient `((Y × E)/Λ)/Γ → Z` along a continuous `Γ`-invariant map `β : Y → Z`. -/
theorem torusFamilyAffineQuotientCommSq (hf : ∀ (g : Γ) y, β (g • y) = β y) (hβc : Continuous β) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    CommSq
      (TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel Γ (AddAction.orbitRel.Quotient Λ (Y × E))),
        continuous_quot_mk⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (TopCat.ofHom ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul β hf,
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβc⟩)
      (TopCat.ofHom ⟨β, hβc⟩) where
  w := by
    let _ := periodAddAction P
    let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ext x
    exact torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β hf x

/-- When `β : Y → Z` is a quotient covering by `Γ`, `torusFamilyAffineQuotientCommSq` induces an
isomorphism in `TopCat` on every fibre. -/
theorem isIso_torusFamilyAffineQuotientCommSq_fiberMap
    (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (hβ : IsQuotientCoveringMap β Γ) (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsIso ((torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap y) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let e := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
    hcont hR hbc β hβ y rfl
  have heq : (torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap y = (TopCat.isoOfHomeo e).hom := by
    ext u
    exact ((torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap_apply_coe y u).trans
      (torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv b hb hone hmul hbmul
        hcont hR hbc β hβ y rfl u).symm
  rw [heq]
  infer_instance

end CommSq

section Fibration

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) (hcont : ∀ l, Continuous fun y ↦ P y l)
  {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))

include hinj hcont hR hbc in
/-- Combining `TauCeti.torusFamilyHomeomorphProd` upstairs with local inverses of a quotient
covering `β : Y → Z` equips the descended torus family `((Y × E)/Λ)/Γ → Z` with local
trivializations around every point of `Z`. -/
theorem exists_trivialization_torusFamilyAffineQuotientLift
    {Z : Type*} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (z : Z) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ∃ e : Bundle.Trivialization
      ((Module.Free.ChooseBasisIndex ℤ Λ → ℝ) ⧸
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ Λ))))
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g)), z ∈ e.baseSet := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let B := Module.Free.chooseBasis ℤ Λ
  let e₀ := (torusFamilyHomeomorphProd P B hinj hcont).toTrivialization
    (fst_torusFamilyHomeomorphProd P B hinj hcont)
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.exists_orbitRelQuotientTrivialization β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    (fun y ↦ ⟨e₀, by simp [e₀]⟩) z

include hinj hcont hR hbc in
/-- **The descended torus family over a normal paracompact base is a Hurewicz fibration**, for test
spaces in every universe `w`. -/
theorem isHurewiczFibration_torusFamilyAffineQuotientLift
    {Z : Type*} [TopologicalSpace Z] [NormalSpace Z] [ParacompactSpace Z]
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsHurewiczFibration.{w}
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g)) :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  isHurewiczFibration_of_exists_trivialization
    (exists_trivialization_torusFamilyAffineQuotientLift P hinj hcont R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ)

/-- **The descended torus family over a normal paracompact base is a Serre fibration.** -/
theorem mem_serreFibrations_torusFamilyAffineQuotientLift
    {Y Z E : Type u} [TopologicalSpace Y] [TopologicalSpace Z] [NormalSpace Z] [ParacompactSpace Z]
    {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hinj : ∀ y, Injective (P y)) (hcont : ∀ l, Continuous fun y ↦ P y l)
    {Γ : Type*} [Group Γ] [MulAction Γ Y]
    (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
    (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (hone : ∀ (y : Y) (v : E), R 1 y v = v)
    (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
    (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
    (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    TopCat.serreFibrations
      (TopCat.ofHom ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g),
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          hβ.continuous⟩) :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  (isHurewiczFibration_torusFamilyAffineQuotientLift.{0} P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ).mem_serreFibrations

include hinj hcont hR hbc in
/-- **Hurewicz fibration over the canonical orbit space `Y/Γ`.** When `Γ` acts freely, properly
discontinuously, and continuously on a second-countable locally compact Hausdorff space `Y` (which
includes `TauCeti.freeLocus Γ Y₀` for any properly discontinuous action on a second-countable
locally compact Hausdorff space `Y₀`), the descended projection `((Y × E)/Λ)/Γ → Y/Γ` is a Hurewicz
fibration with no auxiliary covering or paracompactness hypotheses. -/
theorem isHurewiczFibration_orbitRelQuotientMap_torusFamilyAffineProjection
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsHurewiczFibration.{w}
      (MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbmul)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have : T2Space (MulAction.orbitRel.Quotient Γ Y) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient Γ Y) :=
    MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have : SecondCountableTopology (MulAction.orbitRel.Quotient Γ Y) :=
    ContinuousConstSMul.secondCountableTopology
  have hβ : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel Γ Y)) Γ :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have heq : MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbmul) =
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        (Quotient.mk (MulAction.orbitRel Γ Y)) (fun g _ ↦ hβ.map_smul g) := by
    ext q
    induction q using Quotient.ind with | _ x =>
    simp [coe_torusFamilyAffineProjectionHom]
  rw [heq]
  exact isHurewiczFibration_torusFamilyAffineQuotientLift P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc (Quotient.mk (MulAction.orbitRel Γ Y)) hβ

end Fibration

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
  {Z : Type*} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)

/-- Recovering a `C^n` varying torus family from its affine quotient through a covering
of the base is a `C^n` diffeomorphism. For holomorphic input it is biholomorphic.
The literal pullback receives its atlas from the installed quotient atlas through the
second projection; no manifold structure on that pullback is assumed. -/
noncomputable def torusFamilyAffineQuotientPullbackDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := hβ.isCancelSMul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous)
      (isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul)
    letI := (hβ.isLocalHomeomorph.pullback_snd
      (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        (hf := fun g _ ↦ hβ.map_smul g) hβ.continuous)).chartedSpaceComap (H := ModelProd H E)
    Diffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E))
      (AddAction.orbitRel.Quotient Λ (Y × E))
      (β.Pullback (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g))) n := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := hβ.isCancelSMul
  have hfree := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
    hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
    (fun g ↦ (hbc g).continuous) hfree
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientPullbackDiffeomorph β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous)
    (isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul
      hbmul hR hbc hfree)

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
/-- The differentiable covering comparison has the canonical homeomorphism as its underlying
map, so its inverse and both projection formulas agree with the topological comparison. -/
@[simp] theorem torusFamilyAffineQuotientPullbackDiffeomorph_toHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := hβ.isCancelSMul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous)
      (isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul)
    letI := (hβ.isLocalHomeomorph.pullback_snd
      (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        (hf := fun g _ ↦ hβ.map_smul g) hβ.continuous)).chartedSpaceComap (H := ModelProd H E)
    (torusFamilyAffineQuotientPullbackDiffeomorph P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ).toHomeomorph =
      torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbmul
        (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
        β hβ := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
  simp only [torusFamilyAffineQuotientPullbackDiffeomorph,
    MulActionHom.orbitRelQuotientPullbackDiffeomorph_toHomeomorph,
    torusFamilyAffineQuotientPullbackHomeomorph]

end Regularity

end TauCeti
