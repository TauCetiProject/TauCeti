/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Nonsqueezing.ProductCurve

/-!
# Pseudoholomorphic spheres in `S² × S²` for the product structure

Let `S² = OnePoint ℂ` be the Riemann sphere with its Fubini–Study form `ω_FS` of total area one
(`OnePoint.integralTopForm_fubiniStudyForm`), and give `S² × S²` the split form
`ω_{a,b} = pr₁^*(a • ω_FS) + pr₂^*(b • ω_FS)`. The two **ruling classes** are
`A = [S² × pt]` and `B = [pt × S²]`, of areas `a` and `b`. This file computes the areas of
surfaces in `S² × S²` and identifies the pseudoholomorphic spheres of the two ruling classes for
the product `J₀ = i × i` of the complex structures of the factors.

**Areas.** For a smooth map `u : C → S × N` from a compact oriented boundaryless surface to a
product of two connected oriented boundaryless surfaces, and compactly supported two-forms `σ`
and `τ`, the degree formula applied to each component gives
`∫_C u^*(pr₁^*σ + pr₂^*τ) = deg(pr₁ ∘ u) ∫_S σ + deg(pr₂ ∘ u) ∫_N τ`
(`TauCeti.integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul`). On `S² × S²` the area of
`u` is therefore `deg(pr₁ ∘ u) a + deg(pr₂ ∘ u) b`
(`TauCeti.integralTopForm_mpullback_prod_fubiniStudyForm`). In the equal-area case `a = b` every
area is an integer multiple of `a`, so a positive area is at least `a`
(`TauCeti.le_integralTopForm_mpullback_prod_smul_fubiniStudyForm`): the ruling classes have the
minimum positive area. This is the area gap which prevents the spheres of the ruling classes
from bubbling.

**Pseudoholomorphic spheres.** A `J₀`-holomorphic sphere `u : S² → S² × S²` has holomorphic
components, so both degrees are nonnegative, and each vanishes exactly when its component is
constant. Hence:

* for `a, b ≥ 0`, a nonconstant `J₀`-holomorphic sphere has area at least `min a b`
  (`TauCeti.min_le_integralTopForm_mpullback_prod_fubiniStudyForm`), and for `a, b > 0` it has
  area zero exactly when it is constant
  (`TauCeti.integralTopForm_mpullback_prod_fubiniStudyForm_eq_zero_iff`);
* the `J₀`-holomorphic spheres with component degrees `(1, 0)`, the class `A`, are exactly the
  maps `z ↦ (g • z, w)` for a Möbius transformation `g` and a point `w`
  (`TauCeti.degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff`), and those of class `B` are
  exactly the maps `z ↦ (w, g • z)`
  (`TauCeti.degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff`);
* for equal areas `a = b ≠ 0`, the `J₀`-holomorphic spheres of area `a` are exactly the spheres
  of these two forms (`TauCeti.integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_iff`).

**Leaves.** The image of `z ↦ (g • z, w)` is the horizontal leaf `S² × {w}`
(`TauCeti.range_smul_prodMk_const`), and that of `z ↦ (w, g • z)` the vertical leaf `{w} × S²`
(`TauCeti.range_const_prodMk_smul`); both hold for any group action. So two spheres of one ruling
class have equal or disjoint images, every point of `S² × S²` lies on the image of a sphere of
each class, and a sphere of class `A` meets a sphere of class `B` in exactly one point
(`TauCeti.range_smul_prodMk_const_inter_range_const_prodMk_smul`). These are the two rulings of
`S² × S²` for `J₀`, the standard seeds from which Gromov's argument continues the rulings to an
arbitrary tame almost complex structure.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §2.4 (the rulings of `S² × S²` and its symplectomorphism group).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.4 (the rulings of `S² × S²`).
-/

public section

noncomputable section

open Module Set
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### The area of a surface in a product of surfaces -/

section Surface

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] [BoundarylessManifold I C] [CompactSpace C] [T2Space C]
  {E₁ H₁ S : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {J : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace S] [ChartedSpace H₁ S]
  [IsManifold J ∞ S] [BoundarylessManifold J S] [T2Space S] [SigmaCompactSpace S]
  [ConnectedSpace S]
  {E₂ H₂ N : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {K : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace N] [ChartedSpace H₂ N]
  [IsManifold K ∞ N] [BoundarylessManifold K N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N]

/-- **The area of a surface in a product of two surfaces.** For a smooth map `u : C → S × N` from
a compact oriented boundaryless surface to a product of two connected oriented boundaryless
surfaces, and compactly supported two-forms `σ` on `S` and `τ` on `N`,
`∫_C u^*(pr₁^*σ + pr₂^*τ) = deg(pr₁ ∘ u) ∫_S σ + deg(pr₂ ∘ u) ∫_N τ`. -/
theorem integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul
    (o : Manifold.Orientation I C (Fin 2)) (o₁ : Manifold.Orientation J S (Fin 2))
    (o₂ : Manifold.Orientation K N (Fin 2)) {σ : SmoothTwoForm J S} {τ : SmoothTwoForm K N}
    (hσ : IsCompact (_root_.tsupport (α := E₁ [⋀^Fin 2]→L[ℝ] ℝ) σ.val))
    (hτ : IsCompact (_root_.tsupport (α := E₂ [⋀^Fin 2]→L[ℝ] ℝ) τ.val))
    {u : C → S × N} (hu : ContMDiff I (J.prod K) ∞ u) :
    integralTopForm o (SmoothForm.mpullback u hu (σ.prod τ)).val =
      degree o o₁ (Prod.fst ∘ u) * integralTopForm o₁ σ.val +
        degree o o₂ (Prod.snd ∘ u) * integralTopForm o₂ τ.val := by
  rw [integralTopForm_mpullback_prod, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  congr 1
  · exact integralTopForm_mpullback_eq_degree_mul o o₁ (contMDiff_fst.comp hu)
      (contMDiff_fst.comp hu).continuous.isProperMap (SmoothForm.isSmoothForm _) hσ
  · exact integralTopForm_mpullback_eq_degree_mul o o₂ (contMDiff_snd.comp hu)
      (contMDiff_snd.comp hu).continuous.isProperMap (SmoothForm.isSmoothForm _) hτ

end Surface

/-! ### Areas in `S² × S²` -/

section Area

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] [BoundarylessManifold I C] [CompactSpace C] [T2Space C]
  (o : Manifold.Orientation I C (Fin 2)) {u : C → OnePoint ℂ × OnePoint ℂ}
  (hu : ContMDiff I (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ u)

/-- **The area of a surface in `S² × S²`.** For a smooth map `u` from a compact oriented
boundaryless surface to `S² × S²`, the area for the split form
`pr₁^*(a • ω_FS) + pr₂^*(b • ω_FS)` is `deg(pr₁ ∘ u) a + deg(pr₂ ∘ u) b`, for the canonical
orientation of the Riemann sphere. -/
theorem integralTopForm_mpullback_prod_fubiniStudyForm (a b : ℝ) :
    integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val =
      degree o ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.fst ∘ u) * a +
        degree o ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (Prod.snd ∘ u) * b := by
  have hc (c : ℝ) : IsCompact (_root_.tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ)
      (c • OnePoint.fubiniStudyForm).val) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  rw [integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul o _ _ (hc a) (hc b) hu,
    SmoothForm.smul_toRoughForm, SmoothForm.smul_toRoughForm, integralTopForm_smul,
    integralTopForm_smul, OnePoint.integralTopForm_fubiniStudyForm, mul_one, mul_one]

/-- **Areas in equal-area `S² × S²` are integer multiples of `a`.** For a smooth map `u` from a
compact oriented boundaryless surface to `S² × S²` with the split form
`pr₁^*(a • ω_FS) + pr₂^*(a • ω_FS)`, the area of `u` is `(deg(pr₁ ∘ u) + deg(pr₂ ∘ u)) a`. -/
theorem exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_intCast_mul (a : ℝ) :
    ∃ m : ℤ, integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val = m * a := by
  rw [integralTopForm_mpullback_prod_fubiniStudyForm o hu a a, ← add_mul, ← Int.cast_add]
  exact ⟨_, rfl⟩

/-- **The minimum positive area of equal-area `S² × S²`.** For a smooth map `u` from a compact
oriented boundaryless surface to `S² × S²` with the split form
`pr₁^*(a • ω_FS) + pr₂^*(a • ω_FS)`, a positive area is at least `a`: it is a positive integer
multiple of `a`. The two ruling classes `[S² × pt]` and `[pt × S²]` attain it. -/
theorem le_integralTopForm_mpullback_prod_smul_fubiniStudyForm {a : ℝ}
    (hpos : 0 < integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val) :
    a ≤ integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val := by
  obtain ⟨m, hm⟩ := exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_intCast_mul o hu a
  rw [hm] at hpos ⊢
  rcases le_or_gt a 0 with ha | ha
  · exact ha.trans hpos.le
  · have hm0 : (0 : ℤ) < m := by exact_mod_cast pos_of_mul_pos_left hpos ha.le
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    exact le_mul_of_one_le_left ha.le hm1

end Area

/-! ### The pseudoholomorphic spheres for the product structure -/

section Holomorphic

variable {u : OnePoint ℂ → OnePoint ℂ × OnePoint ℂ}
  (hu : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ u)
  (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
    ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))) u)
include hhol

/-- The first component of a pseudoholomorphic sphere in `S² × S²` is holomorphic. -/
private theorem mdifferentiable_fst_comp :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Prod.fst ∘ u) :=
  isPseudoholomorphic_ofComplexManifold_iff.1
    (SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.1 hhol).1

/-- The second component of a pseudoholomorphic sphere in `S² × S²` is holomorphic. -/
private theorem mdifferentiable_snd_comp :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Prod.snd ∘ u) :=
  isPseudoholomorphic_ofComplexManifold_iff.1
    (SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.1 hhol).2

/-- **The spheres of class `A`.** A map `u : S² → S² × S²`, pseudoholomorphic for the product
of the complex structures of the two factors, has component degrees `(1, 0)` exactly when
it is `z ↦ (g • z, w)` for a Möbius transformation `g` and a point `w`. -/
theorem degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff :
    degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (Prod.fst ∘ u) = 1 ∧
    degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (Prod.snd ∘ u) = 0 ↔
      ∃ (g : GL (Fin 2) ℂ) (w : OnePoint ℂ), u = fun z ↦ (g • z, w) := by
  have h₁ := MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul
    (mdifferentiable_fst_comp hhol)
  rw [h₁, (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, hc⟩
    exact ⟨g, (u OnePoint.infty).2,
      funext fun z ↦ Prod.ext (congrFun hg z) (hc z OnePoint.infty)⟩
  · rintro ⟨g, w, rfl⟩
    exact ⟨⟨g, rfl⟩, fun _ _ ↦ rfl⟩

/-- **The spheres of class `B`.** A map `u : S² → S² × S²`, pseudoholomorphic for the product
of the complex structures of the two factors, has component degrees `(0, 1)` exactly when
it is `z ↦ (w, g • z)` for a point `w` and a Möbius transformation `g`. -/
theorem degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff :
    degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (Prod.fst ∘ u) = 0 ∧
    degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (Prod.snd ∘ u) = 1 ↔
      ∃ (w : OnePoint ℂ) (g : GL (Fin 2) ℂ), u = fun z ↦ (w, g • z) := by
  have h₂ := MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul
    (mdifferentiable_snd_comp hhol)
  rw [(mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff, h₂]
  constructor
  · rintro ⟨hc, ⟨g, hg⟩⟩
    exact ⟨(u OnePoint.infty).1, g,
      funext fun z ↦ Prod.ext (hc z OnePoint.infty) (congrFun hg z)⟩
  · rintro ⟨w, g, rfl⟩
    exact ⟨fun _ _ ↦ rfl, ⟨g, rfl⟩⟩

include hu in
/-- The area of a pseudoholomorphic sphere in `S² × S²` is `m a + n b` for the nonnegative
component degrees `m` and `n`, which both vanish exactly when the sphere is constant. -/
private theorem exists_integralTopForm_mpullback_prod_fubiniStudyForm_eq (a b : ℝ) :
    ∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ ((m = 0 ∧ n = 0) ↔ ∀ z z', u z = u z') ∧
      integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (SmoothForm.mpullback u hu
          ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val =
        m * a + n * b := by
  refine ⟨_, _, (mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_nonneg,
    (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_nonneg, ?_,
    integralTopForm_mpullback_prod_fubiniStudyForm _ hu a b⟩
  rw [(mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff,
    (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff]
  exact ⟨fun h z z' ↦ Prod.ext (h.1 z z') (h.2 z z'),
    fun h ↦ ⟨fun z z' ↦ congrArg Prod.fst (h z z'), fun z z' ↦ congrArg Prod.snd (h z z')⟩⟩

include hu in
/-- **Nonconstant pseudoholomorphic spheres in `S² × S²` have area at least `min a b`.** For
`a, b ≥ 0`, a nonconstant smooth map `u : S² → S² × S²`, pseudoholomorphic for the product of the
complex structures of the two factors, has area at least `min a b` for the split form
`pr₁^*(a • ω_FS) + pr₂^*(b • ω_FS)`. -/
theorem min_le_integralTopForm_mpullback_prod_fubiniStudyForm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hne : ∃ z z', u z ≠ u z') :
    min a b ≤ integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val := by
  obtain ⟨m, n, hm, hn, hzero, harea⟩ :=
    exists_integralTopForm_mpullback_prod_fubiniStudyForm_eq hu hhol a b
  have hmn : 1 ≤ m ∨ 1 ≤ n := by
    by_contra h
    obtain ⟨z, z', hzz'⟩ := hne
    exact hzz' (hzero.1 ⟨by omega, by omega⟩ z z')
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  rw [harea]
  rcases hmn with h | h
  · have h' : (1 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith [min_le_left a b]
  · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [min_le_right a b]

include hu in
/-- **Pseudoholomorphic spheres of area zero are constant.** For `a, b > 0`, a smooth map
`u : S² → S² × S²`, pseudoholomorphic for the product of the complex structures of the two
factors, has area zero for the split form `pr₁^*(a • ω_FS) + pr₂^*(b • ω_FS)` exactly when it is
constant. -/
theorem integralTopForm_mpullback_prod_fubiniStudyForm_eq_zero_iff {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val = 0 ↔
      ∀ z z', u z = u z' := by
  obtain ⟨m, n, hm, hn, hzero, harea⟩ :=
    exists_integralTopForm_mpullback_prod_fubiniStudyForm_eq hu hhol a b
  rw [harea, ← hzero]
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · intro h
    have hma : (m : ℝ) * a = 0 := by nlinarith [mul_nonneg hm' ha.le, mul_nonneg hn' hb.le]
    have hnb : (n : ℝ) * b = 0 := by nlinarith [mul_nonneg hm' ha.le, mul_nonneg hn' hb.le]
    exact ⟨by exact_mod_cast (mul_eq_zero.1 hma).resolve_right ha.ne',
      by exact_mod_cast (mul_eq_zero.1 hnb).resolve_right hb.ne'⟩
  · rintro ⟨rfl, rfl⟩
    simp

include hu in
/-- **The pseudoholomorphic spheres of minimal area in equal-area `S² × S²`.** For `a ≠ 0`, a
smooth map `u : S² → S² × S²`, pseudoholomorphic for the product of the complex structures of the
two factors, has area `a` for the split form `pr₁^*(a • ω_FS) + pr₂^*(a • ω_FS)` exactly when it
is `z ↦ (g • z, w)` or `z ↦ (w, g • z)` for a Möbius transformation `g` and a point `w`: a sphere
of one of the two ruling classes. -/
theorem integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_iff {a : ℝ} (ha : a ≠ 0) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val = a ↔
      (∃ (g : GL (Fin 2) ℂ) (w : OnePoint ℂ), u = fun z ↦ (g • z, w)) ∨
        ∃ (w : OnePoint ℂ) (g : GL (Fin 2) ℂ), u = fun z ↦ (w, g • z) := by
  rw [← degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff hhol,
    ← degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff hhol,
    integralTopForm_mpullback_prod_fubiniStudyForm _ hu a a, ← add_mul, mul_eq_right₀ ha]
  have hm := (mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_nonneg
  have hn := (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_nonneg
  constructor
  · intro h
    have h' : degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.fst ∘ u) +
      degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (Prod.snd ∘ u) = 1 := by exact_mod_cast h
    omega
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> simp [h₁, h₂]

end Holomorphic

/-! ### The two rulings -/

section Ruling

variable {G X M : Type*} [Group G] [MulAction G X]

/-- The image of the sphere `z ↦ (g • z, w)` of class `A` is the horizontal leaf `S² × {w}`. More
generally, for a group `G` acting on `X`, the image of `x ↦ (g • x, w)` is `X × {w}`. -/
@[simp]
theorem range_smul_prodMk_const (g : G) (w : M) :
    range (fun x : X ↦ (g • x, w)) = univ ×ˢ {w} := by
  ext ⟨x, y⟩
  simp only [mem_range, Prod.mk.injEq, mem_prod, mem_univ, mem_singleton_iff, true_and]
  exact ⟨fun ⟨_, _, h⟩ ↦ h.symm, fun h ↦ ⟨g⁻¹ • x, smul_inv_smul g x, h.symm⟩⟩

/-- The image of the sphere `z ↦ (w, g • z)` of class `B` is the vertical leaf `{w} × S²`. More
generally, for a group `G` acting on `X`, the image of `x ↦ (w, g • x)` is `{w} × X`. -/
@[simp]
theorem range_const_prodMk_smul (w : M) (g : G) :
    range (fun x : X ↦ (w, g • x)) = {w} ×ˢ univ := by
  ext ⟨x, y⟩
  simp only [mem_range, Prod.mk.injEq, mem_prod, mem_univ, mem_singleton_iff, and_true]
  exact ⟨fun ⟨_, h, _⟩ ↦ h.symm, fun h ↦ ⟨g⁻¹ • y, h.symm, smul_inv_smul g y⟩⟩

/-- **A sphere of class `A` meets a sphere of class `B` in exactly one point.** The images of
`z ↦ (g • z, w)` and `z ↦ (w', h • z)` meet exactly in `(w', w)`; this holds for any group acting
on `X` in place of the Möbius group acting on the Riemann sphere. -/
theorem range_smul_prodMk_const_inter_range_const_prodMk_smul (g h : G) (w w' : X) :
    range (fun x : X ↦ (g • x, w)) ∩ range (fun x : X ↦ (w', h • x)) = {(w', w)} := by
  rw [range_smul_prodMk_const, range_const_prodMk_smul, prod_inter_prod, univ_inter,
    inter_univ, singleton_prod_singleton]

end Ruling

section Smooth

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H' M]

/-- The maps `z ↦ (w, g • z)` from the Riemann sphere to `M × S²` are smooth. -/
theorem contMDiff_const_prodMk_smul (w : M) (g : GL (Fin 2) ℂ) :
    ContMDiff 𝓘(ℝ, ℂ) (I'.prod 𝓘(ℝ, ℂ)) ∞ (fun z : OnePoint ℂ ↦ (w, g • z)) :=
  -- The Möbius action is holomorphic, hence smooth for the underlying real structure.
  haveI := ContMDiffConstSMul.restrictScalars ℝ
    (inferInstance : ContMDiffConstSMul 𝓘(ℂ) ∞ (GL (Fin 2) ℂ) (OnePoint ℂ))
  contMDiff_const.prodMk (contMDiff_const_smul g)

/-- The maps `z ↦ (w, g • z)` from the Riemann sphere to `M × S²` are pseudoholomorphic for the
product of any almost complex structure `L` on `M` and the complex structure of the sphere. -/
theorem isPseudoholomorphic_const_prodMk_smul [FiniteDimensional ℝ F] [IsManifold I' ∞ M]
    (L : SmoothAlmostComplexStructure I' M) (w : M) (g : GL (Fin 2) ℂ) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (L.prod (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)))
      (fun z : OnePoint ℂ ↦ (w, g • z)) :=
  SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.2
    ⟨isPseudoholomorphic_const _ _ w,
      isPseudoholomorphic_ofComplexManifold_iff.2
        ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) g).mdifferentiable (by simp))⟩

end Smooth

end TauCeti
