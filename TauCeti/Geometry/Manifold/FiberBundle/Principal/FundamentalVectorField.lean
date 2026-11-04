/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Right
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Equivariant
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback

/-!
# Fundamental vector fields on smooth principal bundles

Let `P` be a `C^n` principal `G`-bundle over a manifold `B` modelled on `IB`, with structure group
`G` modelled on `IG`. Its charted total space `TauCeti.ManifoldTotalSpace G P` carries the fibrewise
right action `MulAction Gᵐᵒᵖ (ManifoldTotalSpace G P)` (`TauCeti.ManifoldTotalSpace.instMulAction`),
so every Lie algebra element `ξ : GroupLieAlgebra IG G` directly generates the fundamental vector
field `TauCeti.rightFundamentalVectorField (IB.prod IG) ξ` on `ManifoldTotalSpace G P` without a
wrapper definition.

This file connects the general right-action theory of
`TauCeti.Geometry.Lie.FundamentalVectorField.Right` to the smooth principal-bundle geometry of
`TauCeti.Geometry.Manifold.FiberBundle.Principal`:

* **Smoothness of the right action**: `(x, g) ↦ op g • x` on `ManifoldTotalSpace G P × G` is `C^n`
  (`TauCeti.PrincipalBundle.contMDiff_op_smul`), and `ManifoldTotalSpace G P` carries a
  `ContMDiffConstSMul (IB.prod IG) n Gᵐᵒᵖ (ManifoldTotalSpace G P)` instance so that right
  translation by `g` is packaged by `Diffeomorph.constSmul (IB.prod IG) n (op g)`.
* **Regularity, equivariance, bracket, and exponential flow**: `ξ♯` is `C^m` whenever `m + 1 ≤ n`,
  satisfies `d(R_g)_x (ξ♯ x) = (Ad(g⁻¹) ξ)♯ (x · g)` and `[ξ♯, η♯] = ⁅ξ, η⁆♯`, and over `ℝ` has
  integral curves `t ↦ x · exp(t ξ)` with initial velocity `ξ♯ x` at `0`.
* **Verticality, freeness, and the vertical-fibre isomorphism**: on a `C¹` principal bundle,
  `ξ♯ x` lies in the kernel of `mfderiv (IB.prod IG) IB proj x`
  (`TauCeti.PrincipalBundle.mfderiv_proj_rightFundamentalVectorField`),
  the map `ξ ↦ ξ♯ x` is injective (`TauCeti.PrincipalBundle.rightFundamentalVectorField_injective`),
  and its corestriction `TauCeti.PrincipalBundle.verticalLinearEquiv` is a linear equivalence
  between `GroupLieAlgebra IG G` and the vertical tangent space `(mfderiv proj x).ker`.
* **Naturality under bundle maps and trivial-bundle formula**: equivariant principal-bundle
  diffeomorphisms (`diffeomorphOfEquivariant`) and canonical pullback lifts (`Pullback.lift`)
  intertwine fundamental vector fields, and under the product diffeomorphism
  `TauCeti.ManifoldTotalSpace.diffeomorphProd` from `ManifoldTotalSpace G (Bundle.Trivial B G)` to
  `B × G` the fundamental vector field of `ξ` at `(b, g)` is `(0, mulInvariantVectorField ξ g)`
  (`TauCeti.PrincipalBundle.mfderiv_diffeomorphProd_rightFundamentalVectorField`).

## Main definitions

* `TauCeti.PrincipalBundle.rightFundamentalLinearMap`: the linear map `ξ ↦ ξ♯ x` from
  `GroupLieAlgebra IG G` into `TangentSpace (IB.prod IG) x`.
* `TauCeti.PrincipalBundle.verticalLinearEquiv`: the canonical linear isomorphism
  `GroupLieAlgebra IG G ≃ₗ[𝕜] (mfderiv proj x).ker` onto the vertical tangent space at `x`.

## Main results

* `TauCeti.PrincipalBundle.contMDiff_op_smul`, `TauCeti.PrincipalBundle.instContMDiffConstSMul`:
  joint and pointwise `C^n` smoothness of the right action on `ManifoldTotalSpace G P`.
* `TauCeti.PrincipalBundle.contMDiff_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.mfderiv_op_smul_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.mlieBracket_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.isMIntegralCurve_op_mulInvariantExp_smul`,
  `TauCeti.PrincipalBundle.tangentMap_op_mulInvariantExp_smul_zero`: smoothness, right-translation
  equivariance, Lie bracket homomorphism, and exponential flow on `ManifoldTotalSpace G P`.
* `TauCeti.PrincipalBundle.mfderiv_proj_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.rightFundamentalVectorField_injective`,
  `TauCeti.PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj`: verticality,
  pointwise freeness, and exactness at the vertical tangent space.
* `TauCeti.PrincipalBundle.mfderiv_diffeomorphOfEquivariant_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.mfderiv_pullbackLift_rightFundamentalVectorField`,
  `TauCeti.PrincipalBundle.mfderiv_diffeomorphProd_rightFundamentalVectorField`: naturality under
  equivariant equivalences and pullback lifts, and the formula `(0, dL_g ξ)` on `B × G`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5, Proposition 5.1 and Chapter II, §1 (fundamental vector fields and vertical tangent
  spaces of principal bundles).
* I. Kolář, P. W. Michor, and J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10–§11.
-/

public section

noncomputable section

open Bundle Function Manifold MulOpposite
open scoped ContDiff Manifold

namespace TauCeti.PrincipalBundle

section Field

variable {n : ℕ∞ω} {𝕜 B G : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

section SmoothAction

variable [ContMDiffMul IG n G]

/-- **The right action on the charted total space of a principal bundle is jointly `C^n` whenever
group multiplication is `C^n`.** -/
theorem contMDiff_op_smul :
    ContMDiff ((IB.prod IG).prod IG) (IB.prod IG) n
      (fun p : ManifoldTotalSpace G P × G => op p.2 • p.1) := by
  have hp : ContMDiff ((IB.prod IG).prod IG) (IB.prod IG) n
      (fun p : ManifoldTotalSpace G P × G =>
        ManifoldTotalSpace.homeomorph G P
          ⟨((ManifoldTotalSpace.homeomorph G P).symm p.1).proj,
            ((ManifoldTotalSpace.homeomorph G P).symm p.1).2⟩) :=
    contMDiff_fst.congr fun p => by simp only [TotalSpace.eta, Homeomorph.apply_symm_apply]
  exact (hp.totalSpaceMk_smul contMDiff_snd).congr fun ⟨x, g⟩ => by
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
    rw [ManifoldTotalSpace.smul_homeomorph, Homeomorph.symm_apply_apply]

/-- Each element of `Gᵐᵒᵖ` acts on `ManifoldTotalSpace G P` by a `C^n` map; in particular,
`Diffeomorph.constSmul (IB.prod IG) n (op g)` packages right translation by `g` as a `C^n`
diffeomorphism. -/
instance instContMDiffConstSMul :
    ContMDiffConstSMul (IB.prod IG) n Gᵐᵒᵖ (ManifoldTotalSpace G P) where
  contMDiff_const_smul γ := by
    have h := (contMDiff_op_smul (n := n) (G := G) (P := P) (IB := IB) (IG := IG)).comp
      (contMDiff_id.prodMk (contMDiff_const (c := unop γ)))
    exact h.congr fun x => by simp

/-- Every right orbit map `g ↦ op g • x` on `ManifoldTotalSpace G P` is `C^n`. -/
theorem contMDiff_orbit (x : ManifoldTotalSpace G P) :
    ContMDiff IG (IB.prod IG) n (fun g : G => op g • x) :=
  contMDiff_op_smul.comp (contMDiff_const.prodMk contMDiff_id)

/-- When `n ≠ 0`, every right orbit map `g ↦ op g • x` on `ManifoldTotalSpace G P` is differentiable
at every `g : G`. -/
theorem mdifferentiableAt_orbit (hn : n ≠ 0) (x : ManifoldTotalSpace G P) (g : G) :
    MDifferentiableAt IG (IB.prod IG) (fun h : G => op h • x) g :=
  ((contMDiff_orbit (n := n) x) g).mdifferentiableAt hn

/-- On a `C¹` principal bundle with `C^n` group multiplication, the fundamental vector field
`rightFundamentalVectorField` of `ξ` is `C^m` whenever `m + 1 ≤ n`. -/
theorem contMDiff_rightFundamentalVectorField {m : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IG 1 G]
    [ContMDiffFiberBundle 1 G P IB IG] (hmn : m + 1 ≤ n) (ξ : GroupLieAlgebra IG G) :
    ContMDiff (IB.prod IG) (IB.prod IG).tangent m
      (fun x : ManifoldTotalSpace G P =>
        (⟨x, rightFundamentalVectorField (IB.prod IG) ξ x⟩ :
          TangentBundle (IB.prod IG) (ManifoldTotalSpace G P))) :=
  TauCeti.contMDiff_rightFundamentalVectorField hmn (contMDiff_op_smul (n := n)) ξ

end SmoothAction

omit [PrincipalBundle G P] in
/-- At a transported point `ManifoldTotalSpace.homeomorph G P ⟨b, p⟩`, the fundamental vector field
agrees with the derivative at `1` of the fibrewise orbit map `g ↦ ⟨b, op g • p⟩`. -/
theorem rightFundamentalVectorField_homeomorph (b : B) (p : P b) (ξ : GroupLieAlgebra IG G) :
    rightFundamentalVectorField (IB.prod IG) ξ (ManifoldTotalSpace.homeomorph G P ⟨b, p⟩) =
      mfderiv IG (IB.prod IG)
        (fun g : G => ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) 1 ξ := by
  rw [rightFundamentalVectorField_apply]
  congr 2
  funext g
  exact ManifoldTotalSpace.smul_homeomorph (op g) ⟨b, p⟩

/-- **Right-translation equivariance on a principal bundle.** For a principal `G`-bundle with a
`C¹` Lie group `G`, right translation by `g` transforms the fundamental vector field of `ξ` into
that of `Ad(g⁻¹) ξ`. -/
theorem mfderiv_op_smul_rightFundamentalVectorField [LieGroup IG 1 G]
    (g : G) (ξ : GroupLieAlgebra IG G) (x : ManifoldTotalSpace G P) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x
        (rightFundamentalVectorField (IB.prod IG) ξ x) =
      rightFundamentalVectorField (IB.prod IG) (Lie.adjointContinuousLinearMap g⁻¹ ξ)
        (op g • x) :=
  TauCeti.mfderiv_op_smul_rightFundamentalVectorField
    ((contMDiff_const_smul (I := IB.prod IG) (n := 1) (op g) x).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_orbit (n := 1) one_ne_zero x 1)
    (mdifferentiableAt_orbit (n := 1) one_ne_zero (op g • x) 1) ξ

/-- **Lie bracket homomorphism on a principal bundle.** On a `C²` principal `G`-bundle with a `C³`
Lie group `G`, `[ξ♯, η♯] = ⁅ξ, η⁆♯`. -/
theorem mlieBracket_rightFundamentalVectorField [CompleteSpace EB] [CompleteSpace EG]
    [LieGroup IG (minSmoothness 𝕜 3) G] [IsManifold IB (minSmoothness 𝕜 2) B]
    [ContMDiffFiberBundle (minSmoothness 𝕜 2) G P IB IG] (ξ η : GroupLieAlgebra IG G) :
    VectorField.mlieBracket (IB.prod IG)
        (rightFundamentalVectorField (M := ManifoldTotalSpace G P) (IB.prod IG) ξ)
        (rightFundamentalVectorField (IB.prod IG) η) =
      rightFundamentalVectorField (IB.prod IG) ⁅ξ, η⁆ := by
  have h23 : minSmoothness 𝕜 2 ≤ minSmoothness 𝕜 3 := minSmoothness_monotone (by norm_num)
  have : LieGroup IG (minSmoothness 𝕜 2) G := LieGroup.of_le h23
  exact TauCeti.mlieBracket_rightFundamentalVectorField
    (contMDiff_op_smul (n := minSmoothness 𝕜 2)) ξ η

/-! ### Verticality, freeness, and the vertical-fibre isomorphism -/

section Vertical

omit [PrincipalBundle G P] in
variable (IB IG) in
/-- Evaluation of fundamental vector fields at `x : ManifoldTotalSpace G P`, bundled as a `𝕜`-linear
map `ξ ↦ rightFundamentalVectorField (IB.prod IG) ξ x`. -/
def rightFundamentalLinearMap (x : ManifoldTotalSpace G P) :
    GroupLieAlgebra IG G →ₗ[𝕜] TangentSpace (IB.prod IG) x where
  toFun ξ := rightFundamentalVectorField (IB.prod IG) ξ x
  map_add' ξ η := congrFun (rightFundamentalVectorField_add ξ η) x
  map_smul' c ξ := congrFun (rightFundamentalVectorField_smul c ξ) x

omit [PrincipalBundle G P] in
@[simp]
theorem rightFundamentalLinearMap_apply (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    rightFundamentalLinearMap IB IG x ξ = rightFundamentalVectorField (IB.prod IG) ξ x :=
  (rfl)

variable [ContMDiffMul IG 1 G]

/-- **Fundamental vector fields on a principal bundle are vertical.** The derivative of the bundle
projection annihilates `rightFundamentalVectorField (IB.prod IG) ξ x` at every point `x`. -/
@[simp]
theorem mfderiv_proj_rightFundamentalVectorField (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x
        (rightFundamentalVectorField (IB.prod IG) ξ x) = 0 := by
  have hproj : MDifferentiableAt (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x :=
    (ManifoldTotalSpace.contMDiff_proj 1 G P IB IG x).mdifferentiableAt one_ne_zero
  have hconst : ((fun y : ManifoldTotalSpace G P =>
      ((ManifoldTotalSpace.homeomorph G P).symm y).proj) ∘ fun g : G => op g • x) =
        fun _ : G => ((ManifoldTotalSpace.homeomorph G P).symm x).proj := by
    funext g
    simp
  rw [rightFundamentalVectorField_apply, ← mfderiv_comp_apply_of_eq (1 : G) hproj
    (mdifferentiableAt_orbit (n := 1) one_ne_zero x 1) (by simp) ξ, hconst, mfderiv_const]
  rfl

variable [ContMDiffFiberBundle 1 G P IB IG]

/-- **Pointwise freeness at the infinitesimal level.** At every point `x` of a `C¹` principal
bundle, the map `ξ ↦ rightFundamentalVectorField (IB.prod IG) ξ x` is injective. -/
theorem rightFundamentalVectorField_injective (x : ManifoldTotalSpace G P) :
    Function.Injective fun ξ : GroupLieAlgebra IG G =>
      rightFundamentalVectorField (IB.prod IG) ξ x := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  intro ξ η h
  dsimp only at h
  rw [rightFundamentalVectorField_homeomorph, rightFundamentalVectorField_homeomorph] at h
  exact mfderiv_totalSpaceMk_smul_injective IB IG (n := 1) one_ne_zero p 1 h

/-- A fundamental vector field on a principal bundle vanishes at a point `x` if and only if its
generating Lie algebra element is zero. -/
@[simp]
theorem rightFundamentalVectorField_eq_zero_iff (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G) :
    rightFundamentalVectorField (IB.prod IG) ξ x = 0 ↔ ξ = 0 :=
  ⟨fun h => rightFundamentalVectorField_injective x
    (h.trans (congrFun rightFundamentalVectorField_zero x).symm),
    by rintro rfl; simp⟩

/-- Two Lie algebra elements generate the same tangent vector at `x` if and only if they are
equal. -/
theorem rightFundamentalVectorField_eq_iff (x : ManifoldTotalSpace G P)
    (ξ η : GroupLieAlgebra IG G) :
    rightFundamentalVectorField (IB.prod IG) ξ x =
      rightFundamentalVectorField (IB.prod IG) η x ↔ ξ = η :=
  (rightFundamentalVectorField_injective x).eq_iff

/-- **Exactness at the vertical tangent space.** At every point `x` of a `C¹` principal bundle,
the range of `ξ ↦ ξ♯ x` equals the kernel of the derivative of the bundle projection. -/
theorem range_rightFundamentalLinearMap_eq_ker_mfderiv_proj (x : ManifoldTotalSpace G P) :
    LinearMap.range (rightFundamentalLinearMap IB IG x) =
      (mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P =>
          ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨ξ, rfl⟩
    exact mfderiv_proj_rightFundamentalVectorField x ξ
  · intro w hw
    obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
    have hw' : w ∈ (mfderiv IG (IB.prod IG)
        (fun g : G => ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩) 1).range := by
      rwa [← ker_mfderiv_proj_eq_range_mfderiv_totalSpaceMk_smul_one G IB IG (n := 1)
        one_ne_zero p]
    obtain ⟨ξ, hξ⟩ := hw'
    exact ⟨ξ, (rightFundamentalVectorField_homeomorph b p ξ).trans hξ⟩

variable (IB IG) in
/-- **The canonical vertical-fibre isomorphism `𝔤 ≃ₗ[𝕜] V_x P`.** At every point `x` of a `C¹`
principal `G`-bundle, evaluation of fundamental vector fields identifies `GroupLieAlgebra IG G`
linearly with the vertical tangent space `(mfderiv proj x).ker`. -/
def verticalLinearEquiv (x : ManifoldTotalSpace G P) :
    GroupLieAlgebra IG G ≃ₗ[𝕜]
      (mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P =>
          ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker :=
  (LinearEquiv.ofInjective (rightFundamentalLinearMap IB IG x)
    (rightFundamentalVectorField_injective x)).trans
    (LinearEquiv.ofEq _ _ (range_rightFundamentalLinearMap_eq_ker_mfderiv_proj x))

@[simp]
theorem coe_verticalLinearEquiv_apply (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G) :
    (verticalLinearEquiv IB IG x ξ : TangentSpace (IB.prod IG) x) =
      rightFundamentalVectorField (IB.prod IG) ξ x :=
  (rfl)

@[simp]
theorem verticalLinearEquiv_symm_mk (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G)
    (hξ : rightFundamentalVectorField (IB.prod IG) ξ x ∈
      (mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P =>
          ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker) :
    (verticalLinearEquiv IB IG x).symm
        ⟨rightFundamentalVectorField (IB.prod IG) ξ x, hξ⟩ = ξ :=
  (verticalLinearEquiv IB IG x).symm_apply_eq.2 rfl

@[simp]
theorem rightFundamentalVectorField_verticalLinearEquiv_symm
    (x : ManifoldTotalSpace G P)
    (v : (mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P =>
        ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker) :
    rightFundamentalVectorField (IB.prod IG)
        ((verticalLinearEquiv IB IG x).symm v) x = (v : TangentSpace (IB.prod IG) x) :=
  congrArg Subtype.val ((verticalLinearEquiv IB IG x).apply_symm_apply v)

end Vertical

/-! ### Naturality under equivariant equivalences, pullback lifts, and trivializations -/

section Naturality

/-- `diffeomorphOfEquivariant` is equivariant for the right `G`-actions on the charted total
spaces. -/
theorem diffeomorphOfEquivariant_op_smul {Q : B → Type*}
    [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle G Q]
    [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q] [LieGroup IG n G]
    (e : ∀ b, P b ≃ Q b) (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n
      (ManifoldTotalSpace.fiberwiseMap (F := G) fun b => e b))
    (g : G) (x : ManifoldTotalSpace G P) :
    diffeomorphOfEquivariant G e he hf (op g • x) =
      op g • diffeomorphOfEquivariant G e he hf x := by
  obtain ⟨⟨b, p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G P).surjective x
  simp [he]

/-- **Naturality under equivariant principal-bundle equivalences.** When `n ≠ 0`, the differential
of `diffeomorphOfEquivariant` sends `ξ♯ x` to `ξ♯ (diffeomorphOfEquivariant x)`. -/
theorem mfderiv_diffeomorphOfEquivariant_rightFundamentalVectorField {Q : B → Type*}
    [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle G Q]
    [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q] [LieGroup IG n G] (hn : n ≠ 0)
    (e : ∀ b, P b ≃ Q b) (he : ∀ b (g : G) (p : P b), e b (op g • p) = op g • e b p)
    (hf : ContMDiff (IB.prod IG) (IB.prod IG) n
      (ManifoldTotalSpace.fiberwiseMap (F := G) fun b => e b))
    (x : ManifoldTotalSpace G P) (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) (IB.prod IG) (diffeomorphOfEquivariant G e he hf) x
        (rightFundamentalVectorField (IB.prod IG) ξ x) =
      rightFundamentalVectorField (IB.prod IG) ξ (diffeomorphOfEquivariant G e he hf x) :=
  mfderiv_rightFundamentalVectorField_of_map_op_smul
    ((diffeomorphOfEquivariant G e he hf).mdifferentiable hn x)
    (mdifferentiableAt_orbit hn x 1)
    (fun g => diffeomorphOfEquivariant_op_smul e he hf g x) ξ

/-- **Naturality under pullback lifts.** For a `C^n` map `f : B' → B` (`n ≠ 0`), the canonical map
`Bundle.Pullback.lift f` between charted total spaces sends the fundamental vector field of `ξ` on
`f *ᵖ P` to the fundamental vector field of `ξ` on `P`. -/
theorem mfderiv_pullbackLift_rightFundamentalVectorField
    {B' : Type*} {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB']
    {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners 𝕜 EB' HB'}
    [TopologicalSpace B'] [ChartedSpace HB' B'] [∀ b, Nonempty (P b)]
    [ContMDiffMul IG n G] (hn : n ≠ 0) (f : C^n⟮IB', B'; IB, B⟯)
    (z : ManifoldTotalSpace G ((f : B' → B) *ᵖ P)) (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB'.prod IG) (IB.prod IG)
        (fun w : ManifoldTotalSpace G ((f : B' → B) *ᵖ P) =>
          ManifoldTotalSpace.homeomorph G P
            (Pullback.lift f ((ManifoldTotalSpace.homeomorph G ((f : B' → B) *ᵖ P)).symm w)))
        z (rightFundamentalVectorField (IB'.prod IG) ξ z) =
      rightFundamentalVectorField (IB.prod IG) ξ
        (ManifoldTotalSpace.homeomorph G P
          (Pullback.lift f ((ManifoldTotalSpace.homeomorph G ((f : B' → B) *ᵖ P)).symm z))) := by
  have hlift : MDifferentiableAt (IB'.prod IG) (IB.prod IG)
      (fun w : ManifoldTotalSpace G ((f : B' → B) *ᵖ P) =>
        ManifoldTotalSpace.homeomorph G P
          (Pullback.lift f ((ManifoldTotalSpace.homeomorph G ((f : B' → B) *ᵖ P)).symm w))) z :=
    (ManifoldTotalSpace.contMDiff_pullbackLift n IG f f.contMDiff z).mdifferentiableAt hn
  refine mfderiv_rightFundamentalVectorField_of_map_op_smul hlift
    (mdifferentiableAt_orbit (n := n) hn z 1) (fun g => ?_) ξ
  obtain ⟨⟨b', p⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G ((f : B' → B) *ᵖ P)).surjective z
  simp only [ManifoldTotalSpace.smul_homeomorph, Homeomorph.symm_apply_apply]
  rfl

/-- **Fundamental vector fields on the trivial principal bundle `B × G`.** Under
`ManifoldTotalSpace.diffeomorphProd`, the fundamental vector field of `ξ : GroupLieAlgebra IG G` at
`x` with coordinates `(b, g) ∈ B × G` is `(0, mulInvariantVectorField ξ g)`: zero along `B` and the
left-invariant vector field of `ξ` along `G`. -/
theorem mfderiv_diffeomorphProd_rightFundamentalVectorField [ContMDiffMul IG n G] (hn : n ≠ 0)
    (x : ManifoldTotalSpace G (Bundle.Trivial B G)) (ξ : GroupLieAlgebra IG G) :
    mfderiv (IB.prod IG) (IB.prod IG) (ManifoldTotalSpace.diffeomorphProd n B G IB IG) x
        (rightFundamentalVectorField (IB.prod IG) ξ x) =
      ((0 : TangentSpace IB (ManifoldTotalSpace.diffeomorphProd n B G IB IG x).1),
        mulInvariantVectorField ξ (ManifoldTotalSpace.diffeomorphProd n B G IB IG x).2) := by
  obtain ⟨⟨b, g⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph G (Bundle.Trivial B G)).surjective x
  have hdiff : MDifferentiableAt (IB.prod IG) (IB.prod IG)
      (ManifoldTotalSpace.diffeomorphProd n B G IB IG)
      (ManifoldTotalSpace.homeomorph G (Bundle.Trivial B G) ⟨b, g⟩) :=
    ((ManifoldTotalSpace.diffeomorphProd n B G IB IG).contMDiff _).mdifferentiableAt hn
  have horbit : MDifferentiableAt IG (IB.prod IG)
      (fun h : G => op h • ManifoldTotalSpace.homeomorph G (Bundle.Trivial B G) ⟨b, g⟩) 1 :=
    mdifferentiableAt_orbit (n := n) hn _ 1
  have hsmul (h : G) : (op h • g : Bundle.Trivial B G b) = g * h :=
    division_eq_iff.1
      ((division_trivial (B := B) (G := G) (b := b) g (g * h)).trans (inv_mul_cancel_left g h))
  have hcomp : (ManifoldTotalSpace.diffeomorphProd n B G IB IG ∘
      fun h : G => op h • ManifoldTotalSpace.homeomorph G (Bundle.Trivial B G) ⟨b, g⟩) =
        fun h : G => (b, g * h) := by
    funext h
    rw [Function.comp_apply, ManifoldTotalSpace.smul_homeomorph,
      ManifoldTotalSpace.diffeomorphProd_homeomorph, hsmul]
  have h1 := (mfderiv_comp_apply_of_eq (1 : G) hdiff horbit (by simp) ξ).symm
  rw [rightFundamentalVectorField_apply]
  refine h1.trans ?_
  rw [hcomp]
  have hmul : MDifferentiableAt IG IG (fun h : G => g * h) 1 :=
    ((contMDiffAt_const (c := g)).mul contMDiffAt_id).mdifferentiableAt hn
  have hp := DFunLike.congr_fun
    (mfderiv_prodMk (mdifferentiableAt_const (I := IG) (I' := IB) (c := b)) hmul) ξ
  -- `TangentSpace (IB.prod IG)` is definitionally `EB × EG`, so `.prod` evaluates componentwise.
  erw [ContinuousLinearMap.prod_apply] at hp
  apply Prod.ext
  · exact (congrArg Prod.fst hp).trans (by rw [mfderiv_const, zero_apply]; rfl)
  · have hg : (ManifoldTotalSpace.diffeomorphProd n B G IB IG
        (ManifoldTotalSpace.homeomorph G (Bundle.Trivial B G) ⟨b, g⟩)).2 = g :=
      congrArg Prod.snd (ManifoldTotalSpace.diffeomorphProd_homeomorph n IB IG ⟨b, g⟩)
    exact (congrArg Prod.snd hp).trans
      (congrArg (fun k : G => (mulInvariantVectorField ξ k : EG)) hg.symm)

end Naturality

end Field

section Real

variable {B G : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [LieGroup IG (minSmoothness ℝ 3) G] [IsManifold IG 1 G] [T2Space G]
  [BoundarylessManifold IG G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- **The exponential flow on a principal bundle.** For every point `x` of the charted total space,
`t ↦ op (exp(t ξ)) • x` is an integral curve of `rightFundamentalVectorField (IB.prod IG) ξ`. -/
theorem isMIntegralCurve_op_mulInvariantExp_smul
    (ξ : GroupLieAlgebra IG G) (x : ManifoldTotalSpace G P) :
    IsMIntegralCurve (fun t : ℝ => op (mulInvariantExp (t • ξ)) • x)
      (rightFundamentalVectorField (IB.prod IG) ξ) := by
  have : LieGroup IG 1 G := LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)
  exact TauCeti.isMIntegralCurve_op_mulInvariantExp_smul
    (fun y => mdifferentiableAt_orbit (n := 1) one_ne_zero y 1) ξ x

/-- **Initial velocity of a fibrewise exponential curve on a principal bundle.** The tangent map of
`t ↦ op (exp(t ξ)) • x` sends `⟨0, 1⟩` to `⟨x, rightFundamentalVectorField (IB.prod IG) ξ x⟩`. -/
theorem tangentMap_op_mulInvariantExp_smul_zero
    (ξ : GroupLieAlgebra IG G) (x : ManifoldTotalSpace G P) :
    tangentMap 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ => op (mulInvariantExp (t • ξ)) • x) ⟨0, 1⟩ =
      ⟨x, rightFundamentalVectorField (IB.prod IG) ξ x⟩ := by
  have : LieGroup IG 1 G := LieGroup.of_le (I := IG) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)
  exact TauCeti.tangentMap_op_mulInvariantExp_smul_zero
    (mdifferentiableAt_orbit (n := 1) one_ne_zero x 1) ξ

end Real

end TauCeti.PrincipalBundle
