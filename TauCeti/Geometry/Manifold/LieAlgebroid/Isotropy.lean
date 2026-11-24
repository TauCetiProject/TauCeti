/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal

/-!
# Isotropy Lie algebras of a Lie algebroid

The isotropy of a Lie algebroid `A` with anchor `ρ` at a point `x` is the kernel
`𝔤_x = ker (ρ_x : A_x → T_x M)` of the anchor on the fibre over `x`
(`TauCeti.LieAlgebroid.isotropy`). It is a Lie algebra: for `v, w ∈ 𝔤_x`, the bracket `[v, w]` is
the value at `x` of the bracket `[a, b]` of any two smooth sections with `a(x) = v` and
`b(x) = w`.

The bracket of sections is not determined by values at a point: in the Leibniz rule
`[a, f • b] = f • [a, b] + (ρ(a) f) • b` the last term depends on the derivative of `f` along
`ρ(a(x))`. When `a(x)` lies in the kernel of the anchor this term vanishes at `x`, so `[a, b](x)`
depends only on `b(x)` (`TauCeti.LieAlgebroid.bracket_apply_congr_right`), and symmetrically
(`TauCeti.LieAlgebroid.bracket_apply_congr_left`). Since the anchor maps brackets of sections to
Lie brackets of vector fields, and the Lie bracket of two vector fields vanishing at `x` vanishes
at `x`, the bracket of two isotropy vectors is again isotropic. The Jacobi identity is inherited
from the sections.

Equivalently, the sections whose value at `x` is isotropic form a Lie subalgebra of `Γ(A)`
(`TauCeti.LieAlgebroid.isotropySections`), and evaluation at `x` is a surjective Lie algebra
homomorphism from it onto `𝔤_x` (`TauCeti.LieAlgebroid.isotropyEval`) whose kernel consists of the
sections vanishing at `x`.

For the tangent algebroid every isotropy algebra is zero, and the isotropy at `x` is the whole
fibre exactly when the anchor vanishes at `x`, as for a bundle of Lie algebras with zero anchor.

## Main definitions

* `TauCeti.LieAlgebroid.isotropy`: the isotropy subspace `ker ρ_x` at a point.
* `TauCeti.LieAlgebroid.instLieRingIsotropy`, `TauCeti.LieAlgebroid.instLieAlgebraIsotropy`: the
  isotropy Lie algebra at a point.
* `TauCeti.LieAlgebroid.isotropySections`: the Lie subalgebra of sections isotropic at a point.
* `TauCeti.LieAlgebroid.isotropyEval`: evaluation of such sections, a Lie algebra homomorphism.

## Main results

* `TauCeti.LieAlgebroid.bracket_apply_congr_left`, `TauCeti.LieAlgebroid.bracket_apply_congr_right`:
  `[a, b](x)` depends only on `a(x)` when `b(x)` is isotropic, and only on `b(x)` when `a(x)` is.
* `TauCeti.LieAlgebroid.coe_bracket_isotropy`: the isotropy bracket is computed by any extensions.
* `TauCeti.LieAlgebroid.isotropyEval_surjective`.

## References

* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107, Section 2.2 (isotropy Lie algebras).
* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Chapter 3.
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : LieAlgebroid I F V)

/-- The isotropy of a Lie algebroid at `x`: the kernel of the anchor `ρ_x : A_x → T_x M` on the
fibre over `x`. On a finite-rank bundle over a finite-dimensional Hausdorff base it is a Lie
algebra, `TauCeti.LieAlgebroid.instLieRingIsotropy`. -/
def isotropy (x : M) : Submodule ℝ (V x) :=
  LinearMap.ker ((A.anchor x : V x →L[ℝ] TangentSpace I x) : V x →ₗ[ℝ] TangentSpace I x)

/-- The isotropy subspace is the kernel of the anchor at the point. -/
theorem isotropy_def (x : M) : A.isotropy x = (A.anchor x).ker :=
  (rfl)

@[simp]
theorem mem_isotropy_iff {x : M} {v : V x} : v ∈ A.isotropy x ↔ A.anchor x v = 0 :=
  LinearMap.mem_ker

/-- The anchor vanishes on every isotropy vector. -/
@[simp]
theorem anchor_coe_isotropy {x : M} (v : A.isotropy x) : A.anchor x v = 0 :=
  A.mem_isotropy_iff.mp v.property

/-- The isotropy at `x` is zero exactly when the anchor at `x` is injective. -/
theorem isotropy_eq_bot_iff {x : M} : A.isotropy x = ⊥ ↔ Function.Injective (A.anchor x) := by
  rw [isotropy_def]
  exact LinearMap.ker_eq_bot

/-- The isotropy at `x` is the whole fibre exactly when the anchor vanishes at `x`. -/
@[simp]
theorem isotropy_eq_top_iff {x : M} : A.isotropy x = ⊤ ↔ A.anchor x = 0 := by
  rw [Submodule.eq_top_iff', ContinuousLinearMap.ext_iff]
  simp only [mem_isotropy_iff, zero_apply]

/-- Every isotropy space of the tangent algebroid is zero, since its anchor is the identity. -/
@[simp]
theorem isotropy_tangent [FiniteDimensional ℝ E] (x : M) : (tangent I M).isotropy x = ⊥ := by
  ext v
  simp only [mem_isotropy_iff, tangent_anchor_apply, Submodule.mem_bot]

section Bracket

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- The bracket of two sections whose values at `x` are isotropic is isotropic at `x`. -/
theorem bracket_apply_mem_isotropy {x : M} {a b : Cₛ^∞⟮I; F, V⟯} (ha : a x ∈ A.isotropy x)
    (hb : b x ∈ A.isotropy x) : A.bracket a b x ∈ A.isotropy x := by
  rw [mem_isotropy_iff] at ha hb ⊢
  rw [A.anchor_bracket]
  exact mlieBracket_eq_zero_of_eq_zero ((A.anchorField_apply a x).trans ha)
    ((A.anchorField_apply b x).trans hb)

variable [FiniteDimensional ℝ F]

/-- If `a` vanishes at `x` and `b(x)` is isotropic, then `[a, b]` vanishes at `x`. -/
theorem bracket_apply_eq_zero_of_apply_eq_zero_left {x : M} {a b : Cₛ^∞⟮I; F, V⟯}
    (ha : a x = 0) (hb : b x ∈ A.isotropy x) : A.bracket a b x = 0 := by
  rw [mem_isotropy_iff] at hb
  refine Submodule.smul_induction_on (p := fun u ↦ A.bracket u b x = 0)
    (mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero ha) ?_ ?_
  · intro f hf u _
    rw [A.bracket_swap, ContMDiffSection.coe_neg, Pi.neg_apply, neg_eq_zero, A.bracket_smul_apply,
      mem_smoothVanishingIdeal_iff.mp hf, hb, map_zero]
    simp
  · intro u₁ u₂ h₁ h₂
    simp [h₁, h₂]

/-- If `a(x)` is isotropic and `b` vanishes at `x`, then `[a, b]` vanishes at `x`. -/
theorem bracket_apply_eq_zero_of_apply_eq_zero_right {x : M} {a b : Cₛ^∞⟮I; F, V⟯}
    (ha : a x ∈ A.isotropy x) (hb : b x = 0) : A.bracket a b x = 0 := by
  rw [A.bracket_swap]
  simp [A.bracket_apply_eq_zero_of_apply_eq_zero_left hb ha]

/-- If `b(x)` is isotropic, then `[a, b](x)` depends only on the value `a(x)`. -/
theorem bracket_apply_congr_left {x : M} {a a' b : Cₛ^∞⟮I; F, V⟯} (h : a x = a' x)
    (hb : b x ∈ A.isotropy x) : A.bracket a b x = A.bracket a' b x := by
  have h₀ := A.bracket_apply_eq_zero_of_apply_eq_zero_left
    (a := a - a') (by simp [h]) hb
  simpa [sub_eq_zero] using h₀

/-- If `a(x)` is isotropic, then `[a, b](x)` depends only on the value `b(x)`. -/
theorem bracket_apply_congr_right {x : M} {a b b' : Cₛ^∞⟮I; F, V⟯} (ha : a x ∈ A.isotropy x)
    (h : b x = b' x) : A.bracket a b x = A.bracket a b' x := by
  rw [A.bracket_swap a b, A.bracket_swap a b']
  simp [A.bracket_apply_congr_left h ha]

/-- The value at `x` of the bracket of two sections with isotropic values at `x` depends only on
these values: the **bracket of extensions** is independent of the extensions chosen. -/
theorem bracket_apply_congr {x : M} {a a' b b' : Cₛ^∞⟮I; F, V⟯} (ha : a x = a' x)
    (hb : b x = b' x) (ha₀ : a x ∈ A.isotropy x) (hb₀ : b x ∈ A.isotropy x) :
    A.bracket a b x = A.bracket a' b' x :=
  (A.bracket_apply_congr_left ha hb₀).trans (A.bracket_apply_congr_right (ha ▸ ha₀) hb)

/-! ### The isotropy Lie algebra -/

private def isotropyExtension {x : M} (v : A.isotropy x) : Cₛ^∞⟮I; F, V⟯ :=
  (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x (v : V x)).choose

omit [FiniteDimensional ℝ F] in
private theorem isotropyExtension_apply {x : M} (v : A.isotropy x) :
    isotropyExtension A v x = v := by
  simpa [isotropyExtension] using
    (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x (v : V x)).choose_spec

omit [FiniteDimensional ℝ F] in
private theorem isotropyExtension_apply_mem {x : M} (v : A.isotropy x) :
    isotropyExtension A v x ∈ A.isotropy x := by
  simpa only [isotropyExtension_apply] using v.property

/-- The bracket of the isotropy Lie algebra at `x`: the value at `x` of the bracket of chosen
smooth sections through the two isotropy vectors. By `TauCeti.LieAlgebroid.bracket_apply_congr`
any other choice gives the same value (`TauCeti.LieAlgebroid.coe_bracket_isotropy`). -/
instance instBracketIsotropy (x : M) : Bracket (A.isotropy x) (A.isotropy x) where
  -- The data unfolds `isotropyExtension` by hand: the module system forbids a private
  -- declaration in the data of a public instance, outside tactic blocks. The tactic membership
  -- proofs use `isotropyExtension_apply_mem`, whose statement is definitionally the required one.
  bracket v w :=
    ⟨A.bracket (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x (v : V x)).choose
      (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x (w : V x)).choose x,
      A.bracket_apply_mem_isotropy (by exact isotropyExtension_apply_mem A v)
        (by exact isotropyExtension_apply_mem A w)⟩

/-- The bracket of the isotropy Lie algebra at `x` is the value at `x` of the bracket of any two
smooth sections through the two isotropy vectors. -/
theorem coe_bracket_isotropy {x : M} {v w : A.isotropy x} {a b : Cₛ^∞⟮I; F, V⟯} (ha : a x = v)
    (hb : b x = w) : ((⁅v, w⁆ : A.isotropy x) : V x) = A.bracket a b x := by
  exact A.bracket_apply_congr (a := isotropyExtension A v) (b := isotropyExtension A w)
    ((isotropyExtension_apply A v).trans ha.symm)
    ((isotropyExtension_apply A w).trans hb.symm)
    (isotropyExtension_apply_mem A v) (isotropyExtension_apply_mem A w)

/-- The **isotropy Lie algebra** of a Lie algebroid at `x`, with the bracket
`TauCeti.LieAlgebroid.coe_bracket_isotropy` of isotropy vectors. Its Jacobi identity is that of the
bracket of sections. -/
instance instLieRingIsotropy (x : M) : LieRing (A.isotropy x) where
  add_lie v₁ v₂ w := by
    have ha₁ := isotropyExtension_apply A v₁
    have ha₂ := isotropyExtension_apply A v₂
    have hb := isotropyExtension_apply A w
    ext
    simp [A.coe_bracket_isotropy ha₁ hb, A.coe_bracket_isotropy ha₂ hb,
      A.coe_bracket_isotropy (v := v₁ + v₂)
        (a := isotropyExtension A v₁ + isotropyExtension A v₂)
        (by simp [ha₁, ha₂]) hb]
  lie_add v w₁ w₂ := by
    have ha := isotropyExtension_apply A v
    have hb₁ := isotropyExtension_apply A w₁
    have hb₂ := isotropyExtension_apply A w₂
    ext
    simp [A.coe_bracket_isotropy ha hb₁, A.coe_bracket_isotropy ha hb₂,
      A.coe_bracket_isotropy (w := w₁ + w₂)
        (b := isotropyExtension A w₁ + isotropyExtension A w₂)
        ha (by simp [hb₁, hb₂])]
  lie_self v := by
    have ha := isotropyExtension_apply A v
    ext
    simp [A.coe_bracket_isotropy ha ha, A.bracket_self]
  leibniz_lie u v w := by
    have ha := isotropyExtension_apply A u
    have hb := isotropyExtension_apply A v
    have hc := isotropyExtension_apply A w
    ext
    simp [A.coe_bracket_isotropy ha (A.coe_bracket_isotropy hb hc).symm,
      A.coe_bracket_isotropy (A.coe_bracket_isotropy ha hb).symm hc,
      A.coe_bracket_isotropy hb (A.coe_bracket_isotropy ha hc).symm,
      A.bracket_bracket (isotropyExtension A u) (isotropyExtension A v) (isotropyExtension A w)]

/-- The isotropy Lie algebra at `x` is a Lie algebra over `ℝ`. -/
instance instLieAlgebraIsotropy (x : M) : LieAlgebra ℝ (A.isotropy x) where
  lie_smul c v w := by
    have ha := isotropyExtension_apply A v
    have hb := isotropyExtension_apply A w
    ext
    simp [A.coe_bracket_isotropy ha hb,
      A.coe_bracket_isotropy (w := c • w) (b := c • isotropyExtension A w) ha (by simp [hb])]

end Bracket

/-! ### Isotropic sections -/

section Sections

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- The sections of a Lie algebroid whose value at `x` lies in the isotropy at `x`, a Lie
subalgebra of the sections. -/
def isotropySections (x : M) : LieSubalgebra ℝ A.Sections where
  carrier := {s | A.sectionsEquiv s x ∈ A.isotropy x}
  add_mem' {s t} hs ht := by
    simpa using (A.isotropy x).add_mem hs ht
  zero_mem' := by
    simp
  smul_mem' c s hs := by
    simpa [LinearMapClass.map_smul_of_tower A.sectionsEquiv c] using
      Submodule.smul_mem (A.isotropy x) c hs
  lie_mem' {s t} hs ht := by
    rw [Set.mem_ofPred_eq] at hs ht ⊢
    rw [sectionsEquiv_lie]
    exact A.bracket_apply_mem_isotropy hs ht

@[simp]
theorem mem_isotropySections_iff {x : M} {s : A.Sections} :
    s ∈ A.isotropySections x ↔ A.sectionsEquiv s x ∈ A.isotropy x :=
  Iff.rfl

variable [FiniteDimensional ℝ F]

/-- Evaluation at `x` of the sections isotropic at `x`, a Lie algebra homomorphism onto the
isotropy Lie algebra at `x`. -/
def isotropyEval (x : M) : A.isotropySections x →ₗ⁅ℝ⁆ A.isotropy x where
  toFun s := ⟨A.sectionsEquiv s x, s.property⟩
  map_add' s t := by
    ext
    simp only [AddMemClass.coe_add, map_add, ContMDiffSection.coe_add, Pi.add_apply]
  map_smul' c s := by
    ext
    simp only [RingHom.id_apply, SetLike.val_smul,
      LinearMapClass.map_smul_of_tower A.sectionsEquiv c, ContMDiffSection.coe_smul, Pi.smul_apply]
  map_lie' {s t} := by
    ext
    rw [A.coe_bracket_isotropy rfl rfl]
    simp only [LieSubalgebra.coe_bracket, sectionsEquiv_lie]

@[simp]
theorem coe_isotropyEval_apply {x : M} (s : A.isotropySections x) :
    (A.isotropyEval x s : V x) = A.sectionsEquiv s x :=
  (rfl)

/-- Every isotropy vector is the value of an isotropic section. -/
theorem isotropyEval_surjective (x : M) : Function.Surjective (A.isotropyEval x) := by
  intro v
  refine ⟨⟨A.sectionsEquiv.symm (isotropyExtension A v), ?_⟩, Subtype.ext ?_⟩
  · simp [mem_isotropySections_iff, isotropyExtension_apply]
  · simp [isotropyExtension_apply]

/-- An isotropic section evaluates to zero exactly when it vanishes at `x`. -/
@[simp]
theorem isotropyEval_apply_eq_zero_iff {x : M} {s : A.isotropySections x} :
    A.isotropyEval x s = 0 ↔ A.sectionsEquiv s x = 0 := by
  rw [← Submodule.coe_eq_zero, coe_isotropyEval_apply]

end Sections

end LieAlgebroid

end TauCeti
