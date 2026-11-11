/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import TauCeti.Geometry.Manifold.DerivationBundle
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Lie algebroids

A Lie algebroid over a real manifold `M` is a smooth real vector bundle `V → M` together with a
smooth fibrewise linear anchor `ρ : V → TM` and an `ℝ`-bilinear Lie bracket on the smooth sections
of `V` satisfying the Leibniz rule `[a, f • b] = f • [a, b] + (ρ(a) f) • b`.

`TauCeti.LieAlgebroid` bundles the anchor, the bracket and these laws. The anchor intertwines the
bracket of sections with the Lie bracket of vector fields; this is not assumed but derived from
the Jacobi identity and the Leibniz rule (`TauCeti.LieAlgebroid.anchor_bracket`), on a
finite-dimensional Hausdorff base where smooth sections and smooth functions separate points.

The smooth sections of a Lie algebroid `A` form the type synonym `TauCeti.LieAlgebroid.Sections A`.
It carries the module structures over `ℝ` and over the smooth functions `C^∞⟮I, M; ℝ⟯` of the
underlying sections, the Lie bracket of `A`, and the action of sections on functions by
differentiation along the anchor. These make `(C^∞⟮I, M; ℝ⟯, Sections A)` a Lie–Rinehart algebra
over `ℝ`. Since the synonym is indexed by `A`, two Lie algebroid structures on one bundle give
different section types, and their brackets cannot form instance diamonds.

## Main definitions

* `TauCeti.LieAlgebroid`: a Lie algebroid structure on a smooth real vector bundle.
* `TauCeti.LieAlgebroid.anchorField`: the vector field `ρ(a)` of a smooth section `a`.
* `TauCeti.LieAlgebroid.anchorDeriv`: the derivative `ρ(a) f` of a smooth function along `ρ(a)`.
* `TauCeti.LieAlgebroid.Sections`: the smooth sections of a Lie algebroid, with its Lie bracket.

## Main results

* `TauCeti.LieAlgebroid.bracket_smul_right`: the Leibniz rule for sections.
* `TauCeti.LieAlgebroid.anchorDeriv_bracket`: `ρ([a, b]) f = ρ(a) (ρ(b) f) - ρ(b) (ρ(a) f)`.
* `TauCeti.LieAlgebroid.anchor_bracket`: the anchor maps brackets of sections to Lie brackets of
  vector fields.
* `TauCeti.LieAlgebroid.Sections.instLieRinehartAlgebra`: the sections of a Lie algebroid form a
  Lie–Rinehart algebra over the smooth functions.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Chapter 3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107.
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (I F V) in
/-- A Lie algebroid structure on a smooth real vector bundle `V → M`: a smooth fibrewise linear
anchor `ρ : V → TM` and an `ℝ`-bilinear Lie bracket on the smooth sections of `V` satisfying the
Leibniz rule `[a, f • b] = f • [a, b] + (ρ(a) f) • b`. That the anchor intertwines the brackets is
a consequence, `TauCeti.LieAlgebroid.anchor_bracket`. -/
@[ext]
structure LieAlgebroid where
  /-- The anchor, a smooth bundle map from `V` to the tangent bundle of `M`. -/
  anchor : Cₛ^∞⟮I; F →L[ℝ] E, fun x ↦ V x →L[ℝ] TangentSpace I x⟯
  /-- The Lie bracket of smooth sections. -/
  bracket : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯
  /-- The bracket is alternating. -/
  bracket_self (a : Cₛ^∞⟮I; F, V⟯) : bracket a a = 0
  /-- The Jacobi identity, in the form of the Leibniz rule of a Lie ring. -/
  bracket_bracket (a b c : Cₛ^∞⟮I; F, V⟯) :
    bracket a (bracket b c) = bracket (bracket a b) c + bracket b (bracket a c)
  /-- The Leibniz rule: the coefficient of the second section is differentiated along the anchor
  of the first. -/
  bracket_smul_apply (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    bracket a (f • b) x = f x • bracket a b x + mvfderiv I f x (anchor x (a x)) • b x

namespace LieAlgebroid

variable (A : LieAlgebroid I F V)

/-- The anchor applied to smooth sections, a map to smooth vector fields which is linear over the
smooth functions. -/
def anchorField : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun a :=
    { toFun x := A.anchor x (a x)
      contMDiff_toFun := A.anchor.contMDiff.clm_bundle_apply a.contMDiff }
  map_add' a b := by ext x; simp
  map_smul' f a := by ext x; simp

@[simp]
theorem anchorField_apply (a : Cₛ^∞⟮I; F, V⟯) (x : M) :
    A.anchorField a x = A.anchor x (a x) := (rfl)

/-- The derivative `ρ(a) f` of a smooth function `f` along the anchor of a smooth section `a`. -/
def anchorDeriv (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ mvfderiv I f x (A.anchor x (a x)),
    contMDiffOn_univ.1 <| f.contMDiff.contMDiffOn.contMDiffOn_mvfderiv_apply isOpen_univ
      (A.anchorField a).contMDiff.contMDiffOn (by simp)⟩

@[simp]
theorem anchorDeriv_apply (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    A.anchorDeriv a f x = mvfderiv I f x (A.anchor x (a x)) := (rfl)

/-- The derivative along the anchor of the zero section vanishes. -/
@[simp]
theorem anchorDeriv_zero_left (f : C^∞⟮I, M; ℝ⟯) : A.anchorDeriv 0 f = 0 := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffSection.coe_zero, Pi.zero_apply, map_zero,
    ContMDiffMap.coe_zero]

/-- The derivative of a constant function along the anchor vanishes. -/
@[simp]
theorem anchorDeriv_const_right (a : Cₛ^∞⟮I; F, V⟯) (c : ℝ) :
    A.anchorDeriv a (ContMDiffMap.const c) = 0 := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffMap.coe_zero, Pi.zero_apply]
  rw [ContMDiffMap.const, ContMDiffMap.coeFn_mk, mvfderiv_const, _root_.zero_apply]

/-- The derivative of the zero function along the anchor vanishes. -/
@[simp]
theorem anchorDeriv_zero_right (a : Cₛ^∞⟮I; F, V⟯) : A.anchorDeriv a 0 = 0 :=
  A.anchorDeriv_const_right a 0

/-- The derivative of the constant function one along the anchor vanishes. -/
@[simp]
theorem anchorDeriv_one_right (a : Cₛ^∞⟮I; F, V⟯) : A.anchorDeriv a 1 = 0 :=
  A.anchorDeriv_const_right a 1

/-- The derivative of a scalar constant function along the anchor vanishes. -/
@[simp]
theorem anchorDeriv_algebraMap_right (a : Cₛ^∞⟮I; F, V⟯) (c : ℝ) :
    A.anchorDeriv a (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c) = 0 :=
  A.anchorDeriv_const_right a c

/-- The derivative along the anchor is additive in the section. -/
@[simp]
theorem anchorDeriv_add_left (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv (a + b) f = A.anchorDeriv a f + A.anchorDeriv b f := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffSection.coe_add, Pi.add_apply, map_add,
    ContMDiffMap.coe_add]

/-- The derivative along the anchor is linear over smooth functions in the section. -/
@[simp]
theorem anchorDeriv_smul_left (g : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv (g • a) f = g * A.anchorDeriv a f := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffSection.smul_apply, map_smul, smul_eq_mul,
    ContMDiffMap.coe_mul, Pi.mul_apply]

/-- The derivative along the anchor is homogeneous in the section. -/
@[simp]
theorem anchorDeriv_const_smul_left (c : ℝ) (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv (c • a) f = c • A.anchorDeriv a f := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffSection.coe_smul, Pi.smul_apply, map_smul,
    ContMDiffMap.coe_smul]

/-- The derivative along the anchor is additive in the function. -/
@[simp]
theorem anchorDeriv_add_right (a : Cₛ^∞⟮I; F, V⟯) (f g : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv a (f + g) = A.anchorDeriv a f + A.anchorDeriv a g := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffMap.coe_add, Pi.add_apply,
    mvfderiv_add (f.contMDiff.mdifferentiableAt (by simp))
      (g.contMDiff.mdifferentiableAt (by simp)), _root_.add_apply]

/-- The derivative along the anchor is homogeneous in the function. -/
@[simp]
theorem anchorDeriv_const_smul_right (a : Cₛ^∞⟮I; F, V⟯) (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv a (c • f) = c • A.anchorDeriv a f := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    mvfderiv_const_smul_field, _root_.smul_apply]

/-- The product rule `ρ(a) (f * g) = f * ρ(a) g + ρ(a) f * g`. -/
@[simp]
theorem anchorDeriv_mul_right (a : Cₛ^∞⟮I; F, V⟯) (f g : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv a (f * g) = f * A.anchorDeriv a g + A.anchorDeriv a f * g := by
  ext x
  simp only [anchorDeriv_apply, ContMDiffMap.coe_mul, ContMDiffMap.coe_add, Pi.mul_apply,
    Pi.add_apply, mvfderiv_mul (f.contMDiff.mdifferentiableAt (by simp))
      (g.contMDiff.mdifferentiableAt (by simp)), _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- The Leibniz rule `[a, f • b] = f • [a, b] + (ρ(a) f) • b`. -/
@[simp]
theorem bracket_smul_right (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket a (f • b) = f • A.bracket a b + A.anchorDeriv a f • b := by
  ext x
  simp [A.bracket_smul_apply]

section Separation

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- The anchor intertwines the bracket of sections with the commutator of derivations:
`ρ([a, b]) f = ρ(a) (ρ(b) f) - ρ(b) (ρ(a) f)`. -/
theorem anchorDeriv_bracket (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.anchorDeriv (A.bracket a b) f =
      A.anchorDeriv a (A.anchorDeriv b f) - A.anchorDeriv b (A.anchorDeriv a f) := by
  -- Expanding the Jacobi identity for `a`, `b` and `f • c` by the Leibniz rule leaves
  -- `(ρ([a, b]) f - ρ(a) (ρ(b) f) + ρ(b) (ρ(a) f)) • c = 0` for every section `c`. Smooth
  -- sections take every value of the fibre, so the coefficient vanishes wherever the fibre is
  -- nonzero; where the fibre is zero every anchor term vanishes.
  have key (c : Cₛ^∞⟮I; F, V⟯) : (A.anchorDeriv (A.bracket a b) f -
      (A.anchorDeriv a (A.anchorDeriv b f) - A.anchorDeriv b (A.anchorDeriv a f))) • c = 0 := by
    have h := A.bracket_bracket a b (f • c)
    simp only [bracket_smul_right, map_add] at h
    linear_combination (norm := module) -h + f • A.bracket_bracket a b c
  rw [← sub_eq_zero]
  ext x
  rcases subsingleton_or_nontrivial (V x) with hV | hV
  · -- Every anchor term vanishes at a point where the fibre is zero.
    have h0 (v : V x) : v = 0 := Subsingleton.elim v 0
    simp only [ContMDiffMap.coe_sub, ContMDiffMap.coe_zero, Pi.sub_apply, Pi.zero_apply,
      anchorDeriv_apply, h0 (a x), h0 (b x), h0 (A.bracket a b x), map_zero, sub_self]
  · obtain ⟨v, hv⟩ := exists_ne (0 : V x)
    obtain ⟨c, hc, hcx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
    have h := congr($(key ⟨c, hc⟩) x)
    rw [ContMDiffSection.smul_apply] at h
    exact (smul_eq_zero.1 h).resolve_right (by simpa [hcx] using hv)

/-- The anchor maps the bracket of two sections to the Lie bracket of their anchor vector fields:
`ρ([a, b]) = [ρ(a), ρ(b)]`. -/
theorem anchor_bracket (a b : Cₛ^∞⟮I; F, V⟯) (x : M) :
    A.anchor x (A.bracket a b x) = mlieBracket I (A.anchorField a) (A.anchorField b) x := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  refine tangentToPointDerivation_injective x (Derivation.ext fun (f : C^∞⟮I, M; ℝ⟯) ↦ ?_)
  refine (tangentToPointDerivation_apply x _ f).trans <| Eq.trans ?_
    (tangentToPointDerivation_apply x _ f).symm
  rw [_root_.mvfderiv_mlieBracket f.contMDiff.contMDiffAt (by simp)
      ((A.anchorField a).contMDiff.mdifferentiableAt (by simp))
      ((A.anchorField b).contMDiff.mdifferentiableAt (by simp))]
  exact congr($(A.anchorDeriv_bracket a b f) x)

end Separation

/-! ### The Lie algebra of sections -/

/-- The smooth sections `Γ(A)` of a Lie algebroid `A`: a type synonym for the smooth sections of
the underlying bundle, carrying the Lie bracket of `A` and the action of sections on smooth
functions by differentiation along the anchor. It is indexed by `A`, so that different Lie
algebroid structures on one bundle have different section types. -/
def Sections (_A : LieAlgebroid I F V) : Type _ := Cₛ^∞⟮I; F, V⟯

namespace Sections

instance instAddCommGroup : AddCommGroup A.Sections :=
  inferInstanceAs (AddCommGroup Cₛ^∞⟮I; F, V⟯)

instance instModule : Module ℝ A.Sections := inferInstanceAs (Module ℝ Cₛ^∞⟮I; F, V⟯)

instance instModuleContMDiffMap : Module C^∞⟮I, M; ℝ⟯ A.Sections :=
  inferInstanceAs (Module C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)

instance instIsScalarTower : IsScalarTower ℝ C^∞⟮I, M; ℝ⟯ A.Sections :=
  inferInstanceAs (IsScalarTower ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)

instance instSMulCommClass : SMulCommClass ℝ C^∞⟮I, M; ℝ⟯ A.Sections :=
  inferInstanceAs (SMulCommClass ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)

end Sections

/-- The identification of the sections `Γ(A)` of a Lie algebroid with the smooth sections of its
underlying bundle. -/
def sectionsEquiv : A.Sections ≃ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯ := LinearEquiv.refl _ _

namespace Sections

/-- The Lie bracket of the sections of a Lie algebroid. -/
instance instLieRing : LieRing A.Sections where
  bracket s t := A.sectionsEquiv.symm (A.bracket (A.sectionsEquiv s) (A.sectionsEquiv t))
  add_lie s t u := by simp only [map_add, LinearMap.add_apply]
  lie_add s t u := by simp only [map_add]
  lie_self s := by simp only [A.bracket_self, map_zero]
  leibniz_lie s t u := by
    simp only [LinearEquiv.apply_symm_apply]
    rw [A.bracket_bracket, map_add]

end Sections

@[simp]
theorem sectionsEquiv_lie (s t : A.Sections) :
    A.sectionsEquiv ⁅s, t⁆ = A.bracket (A.sectionsEquiv s) (A.sectionsEquiv t) :=
  A.sectionsEquiv.apply_symm_apply _

namespace Sections

instance instLieAlgebra : LieAlgebra ℝ A.Sections where
  lie_smul c s t := A.sectionsEquiv.injective <| by
    rw [LinearMapClass.map_smul_of_tower A.sectionsEquiv c, sectionsEquiv_lie, sectionsEquiv_lie,
      LinearMapClass.map_smul_of_tower A.sectionsEquiv c, map_smul]

section Rinehart

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- Sections of a Lie algebroid act on smooth functions by differentiation along their anchor
vector fields, `⁅s, f⁆ = ρ(s) f`. -/
instance instLieRingModule : LieRingModule A.Sections C^∞⟮I, M; ℝ⟯ where
  bracket s f := A.anchorDeriv (A.sectionsEquiv s) f
  add_lie s t f := by rw [map_add, anchorDeriv_add_left]
  lie_add s f g := A.anchorDeriv_add_right _ f g
  leibniz_lie s t f := by
    have h := A.anchorDeriv_bracket (A.sectionsEquiv s) (A.sectionsEquiv t) f
    rw [← sectionsEquiv_lie] at h
    -- The goal is `h` rearranged, with each action of a section unfolded to `anchorDeriv`.
    exact sub_eq_iff_eq_add.1 h.symm

/-- A section acts on a smooth function by the derivative along its anchor. -/
theorem lie_def (s : A.Sections) (f : C^∞⟮I, M; ℝ⟯) :
    ⁅s, f⁆ = A.anchorDeriv (A.sectionsEquiv s) f := (rfl)

@[simp]
theorem lie_apply (s : A.Sections) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    ⁅s, f⁆ x = mvfderiv I f x (A.anchor x (A.sectionsEquiv s x)) := (rfl)

instance instLieModule : LieModule ℝ A.Sections C^∞⟮I, M; ℝ⟯ where
  smul_lie c s f := by
    rw [lie_def, lie_def, LinearMapClass.map_smul_of_tower, anchorDeriv_const_smul_left]
  lie_smul c s f := A.anchorDeriv_const_smul_right _ c f

instance instLieRinehartRing : LieRinehartRing C^∞⟮I, M; ℝ⟯ A.Sections where
  lie_smul_eq_mul' f g s := by
    rw [lie_def, lie_def, map_smul, anchorDeriv_smul_left]
  leibniz_mul_right' s f g := by
    rw [lie_def, lie_def, lie_def, anchorDeriv_mul_right, smul_eq_mul]
  leibniz_smul_right' s t f := A.sectionsEquiv.injective <| by
    rw [sectionsEquiv_lie, map_smul, bracket_smul_right, map_add, map_smul, map_smul,
      sectionsEquiv_lie, lie_def]

/-- The sections of a Lie algebroid form a Lie–Rinehart algebra over the smooth functions. -/
instance instLieRinehartAlgebra : LieRinehartAlgebra ℝ C^∞⟮I, M; ℝ⟯ A.Sections where

end Rinehart

end Sections

end LieAlgebroid

end TauCeti
