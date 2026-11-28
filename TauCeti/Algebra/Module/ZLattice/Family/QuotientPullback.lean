/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.AffineQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
public import TauCeti.Geometry.Manifold.Quotient.Pullback
public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Homotopy.HurewiczFibration.LocallyTrivial
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction

/-!
# Recovering a torus family through a covering of the base

Let `X = (Y × E)/Λ` be a varying period quotient, with an affine action of `Γ` lifting
an action on `Y`, and let `β : Y → Z` be a quotient covering by `Γ`. The canonical map
`x ↦ (p x, [x])` identifies `X` with the literal pullback of `X/Γ → Z` along `β`.
The inverse takes an orbit representative and translates it to the specified base point.

Restricting to a sheet `y` over `z = β y` identifies the `y`-fibre with the descended `z`-fibre
(`TauCeti.torusFamilyAffineQuotientFiberHomeomorph`), with sheet transition by `g⁻¹ • ·`. For finite
free `Λ`, finite-dimensional real `E`, and continuous injective full-lattice embeddings `P`, local
inverses of `β` descend `TauCeti.torusFamilyHomeomorphProd` to local trivializations
(`TauCeti.exists_trivialization_torusFamilyAffineQuotientMap`), giving a Hurewicz/Serre fibration
over any normal paracompact base `Z` (`TauCeti.isHurewiczFibration_torusFamilyAffineQuotientMap`,
`TauCeti.torusFamilyAffineQuotientLiftingFunction`,
`TauCeti.mem_serreFibrations_torusFamilyAffineQuotientTopHom`), and over `Y/Γ` for a free properly
discontinuous continuous action on a second-countable locally compact Hausdorff `Y`
(`TauCeti.isHurewiczFibration_orbitRelQuotientMap_torusFamilyAffineProjection`,
`TauCeti.torusFamilyOrbitQuotientLiftingFunction`).

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
      hcont hR hbc β hβ x).val = (torusFamilyProjection P x, Quotient.mk _ x) := by
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

omit [TopologicalSpace Y] [TopologicalSpace E] [ContinuousAdd E] hcont hR hbc
  [TopologicalSpace Z] in
/-- The descended torus projection `((Y × E)/Λ)/Γ → Z` along a quotient covering `β : Y → Z`. -/
abbrev torusFamilyAffineQuotientMap :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)) → Z :=
  letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul β (fun g _ ↦ hβ.map_smul g)

/-- For a sheet `y : Y` over `z = β y`, the orbit map restricts to a homeomorphism between the
`y`-fibre upstairs and the descended `z`-fibre. -/
noncomputable def torusFamilyAffineQuotientFiberHomeomorph {z : Z} (y : Y)
    (hy : β y = z := by rfl) :
    letI := periodAddAction P; torusFamilyProjection P ⁻¹' {y} ≃ₜ
      torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ ⁻¹' {z} :=
  letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  MulActionHom.orbitRelQuotientFiberHomeomorph ⟨torusFamilyProjection P, by simp⟩ β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
    (continuous_torusFamilyProjection P) hβ y hy

/-- `torusFamilyAffineQuotientFiberHomeomorph` sends a point in the `y`-fibre to its `Γ`-orbit. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_coe {z : Z} (y : Y) (hy : β y = z)
    (u : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {y}) :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      y hy u : MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) =
      Quotient.mk _ u.val := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  exact MulActionHom.orbitRelQuotientFiberHomeomorph_coe ⟨torusFamilyProjection P, by simp⟩ β _ _ _
    hβ y hy u

/-- Pulling `[x]` with `torusFamilyProjection P x = g • y` back to the `y`-sheet fibre acts by
`torusFamilyAffineMap ... g⁻¹`. -/
theorem torusFamilyAffineQuotientFiberHomeomorph_symm_mk_of_smul {z : Z} (y : Y) (hy : β y = z)
    (g : Γ) {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : torusFamilyProjection P x = g • y)
    (hq : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
      torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ (Quotient.mk _ x) = z) :
    letI := periodAddAction P
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      y hy).symm ⟨Quotient.mk _ x, hq⟩ : AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g⁻¹ x := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  exact (MulActionHom.orbitRelQuotientFiberHomeomorph_symm_mk_of_smul
      ⟨torusFamilyProjection P, by simp⟩ β _
      (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _)
      (continuous_torusFamilyProjection P) hβ y hy g hx hq).trans
    (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g⁻¹ x)

/-- Identifying the `(g • y)`-sheet fibre back with the `y`-sheet fibre over `z` acts by `g⁻¹`. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_symm_apply_smul {z : Z} (y : Y)
    (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (v : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {g • y}) :
    letI := periodAddAction P
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      y hy).symm (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
        hcont hR hbc β hβ (g • y) hgy v) : AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g⁻¹ v.val := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  exact (MulActionHom.orbitRelQuotientFiberHomeomorph_symm_apply_smul
      ⟨torusFamilyProjection P, by simp⟩ β _ _ _ hβ y hy g hgy v).trans
    (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g⁻¹ v.val)

/-- Identifying the `y`-sheet fibre with the `(g • y)`-sheet fibre over `z` acts by `g`. -/
@[simp] theorem torusFamilyAffineQuotientFiberHomeomorph_smul_symm_apply {z : Z} (y : Y)
    (hy : β y = z) (g : Γ) (hgy : β (g • y) = z)
    (u : letI := periodAddAction P; torusFamilyProjection P ⁻¹' {y}) :
    letI := periodAddAction P
    ((torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ
      (g • y) hgy).symm (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
        hcont hR hbc β hβ y hy u) : AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyAffineMap R P ρ hequiv b hb g u.val := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  exact (MulActionHom.orbitRelQuotientFiberHomeomorph_smul_symm_apply
      ⟨torusFamilyProjection P, by simp⟩ β _ _ _ hβ y hy g hgy u).trans
    (torusFamilyAffineMulAction_smul R hone hmul P ρ hequiv b hb hbmul g u.val)

end Topology

section Fibration

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hinj : ∀ y, Injective (P y))
  (hcont : ∀ l, Continuous fun y ↦ P y l) {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))

include hinj hcont hR hbc in
/-- Local trivializations of the descended torus family `((Y × E)/Λ)/Γ → Z` around every `z : Z`. -/
theorem exists_trivialization_torusFamilyAffineQuotientMap {Z : Type*} [TopologicalSpace Z]
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (z : Z) :
    ∃ e : Bundle.Trivialization ((Module.Free.ChooseBasisIndex ℤ Λ → ℝ) ⧸
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ Λ))))
      (torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ), z ∈ e.baseSet := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    hcont hR hbc
  let B := Module.Free.chooseBasis ℤ Λ
  let e₀ := (torusFamilyHomeomorphProd P B hinj hcont).toTrivialization
    (fst_torusFamilyHomeomorphProd P B hinj hcont)
  exact MulActionHom.exists_orbitRelQuotientTrivialization ⟨torusFamilyProjection P, by simp⟩ β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β _) hβ
    (fun y ↦ ⟨e₀, by simp [e₀]⟩) z

include hinj hcont hR hbc in
/-- **The descended torus family over a normal paracompact base is a Hurewicz fibration.** -/
theorem isHurewiczFibration_torusFamilyAffineQuotientMap {Z : Type*} [TopologicalSpace Z]
    [NormalSpace Z] [ParacompactSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    IsHurewiczFibration.{w} (torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ) :=
  isHurewiczFibration_of_exists_trivialization
    (exists_trivialization_torusFamilyAffineQuotientMap P hinj hcont R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ)

include hinj hcont hR hbc in
/-- A Hurewicz lifting function for `((Y × E)/Λ)/Γ → Z` over a normal paracompact base `Z`. -/
noncomputable def torusFamilyAffineQuotientLiftingFunction {Z : Type*} [TopologicalSpace Z]
    [NormalSpace Z] [ParacompactSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    LiftingFunction ⟨torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ,
      continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous⟩ :=
  (isHurewiczFibration_torusFamilyAffineQuotientMap P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ).nonempty_liftingFunction.some

include hinj hcont hR hbc in
/-- **Hurewicz fibration over `Y/Γ`** for a free properly discontinuous continuous action on a
second-countable locally compact Hausdorff space `Y`. -/
theorem isHurewiczFibration_orbitRelQuotientMap_torusFamilyAffineProjection [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [ProperlyDiscontinuousSMul Γ Y]
    [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y] :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsHurewiczFibration.{w} (MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbmul)) := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
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
      torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul _ hβ := by
    ext q; induction q using Quotient.ind with | _ x => simp [coe_torusFamilyAffineProjectionHom]
  rw [heq]; exact isHurewiczFibration_torusFamilyAffineQuotientMap P hinj hcont R ρ hequiv b hb hone
    hmul hbmul hR hbc _ hβ

include hinj hcont hR hbc in
/-- A Hurewicz lifting function for the descended torus family over `Y/Γ`, for a free properly
discontinuous continuous action of `Γ` on a second-countable locally compact Hausdorff space `Y`. -/
noncomputable def torusFamilyOrbitQuotientLiftingFunction [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y]
    [IsCancelSMul Γ Y] :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    LiftingFunction ⟨torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul
      (Quotient.mk (MulAction.orbitRel Γ Y))
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul,
      continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.continuous⟩ :=
  haveI : T2Space (MulAction.orbitRel.Quotient Γ Y) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  haveI : LocallyCompactSpace (MulAction.orbitRel.Quotient Γ Y) :=
    MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.orbitRel.Quotient Γ Y) :=
    ContinuousConstSMul.secondCountableTopology
  torusFamilyAffineQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul hR hbc
    (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

end Fibration

section CommSq

variable {Y Z E : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {Λ Γ : Type*} [AddCommGroup Λ]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] (P : Y → Λ →ₗ[ℤ] E) [Group Γ]
  [MulAction Γ Y] (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

omit [ContinuousAdd E] in
/-- The descended torus projection `((Y × E)/Λ)/Γ ⟶ Z` along `β : Y → Z` as a `TopCat` morphism. -/
abbrev torusFamilyAffineQuotientTopHom (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    TopCat.of (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) ⟶
      TopCat.of Z :=
  letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  TopCat.ofHom ⟨torusFamilyAffineQuotientMap P R ρ hequiv b hb hone hmul hbmul β hβ,
    continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβ.continuous⟩

omit [ContinuousAdd E] in
/-- The commutative square in `TopCat` relating `(Y × E)/Λ → Y` to `((Y × E)/Λ)/Γ → Z`. -/
theorem torusFamilyAffineQuotientCommSq {β : Y → Z} (hf : ∀ (g : Γ) y, β (g • y) = β y)
    (hβc : Continuous β) :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    CommSq (TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel Γ (AddAction.orbitRel.Quotient Λ
        (Y × E))), continuous_quot_mk⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (TopCat.ofHom ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul β hf,
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul hβc⟩)
      (TopCat.ofHom ⟨β, hβc⟩) := ⟨by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  ext x; exact torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbmul β hf x⟩

/-- When `β` is a quotient covering, `torusFamilyAffineQuotientCommSq` is a fibrewise `IsIso`. -/
theorem isIso_torusFamilyAffineQuotientCommSq_fiberMap {β : Y → Z}
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g)) (hβ : IsQuotientCoveringMap β Γ)
    (y : Y) :
    letI := periodAddAction P; letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsIso ((torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap y) := by
  let _ := periodAddAction P; let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have heq : (torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap y =
      (TopCat.isoOfHomeo (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul
        hbmul hcont hR hbc β hβ y rfl)).hom := by
    ext u; exact ((torusFamilyAffineQuotientCommSq P R ρ hequiv b hb hone hmul hbmul
      (fun g _ ↦ hβ.map_smul g) hβ.continuous).fiberMap_apply_coe y u).trans
      (torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
        β hβ y rfl u).symm
  rw [heq]; infer_instance

/-- **The descended torus family over a normal paracompact base is a Serre fibration.** -/
theorem mem_serreFibrations_torusFamilyAffineQuotientTopHom {Y Z E : Type u} [TopologicalSpace Y]
    [TopologicalSpace Z] [NormalSpace Z] [ParacompactSpace Z] {Λ Γ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hinj : ∀ y, Injective (P y))
    (hcont : ∀ l, Continuous fun y ↦ P y l) [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
    (ρ : Representation ℤ Γ Λ) (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
    (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
    (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
    (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g)) (β : Y → Z)
    (hβ : IsQuotientCoveringMap β Γ) : TopCat.serreFibrations
      (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ) :=
  (isHurewiczFibration_torusFamilyAffineQuotientMap.{0} P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ).mem_serreFibrations

end CommSq

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
