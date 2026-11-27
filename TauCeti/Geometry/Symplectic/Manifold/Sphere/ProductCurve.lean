/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.MappingDegree
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.RiemannSphere
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Prod.Area
import TauCeti.Algebra.Order.Ring.IntMul

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
(`TauCeti.integralTopForm_mpullback_prod_eq_degree_mul_add_degree_mul`, in
`TauCeti.Geometry.Symplectic.Manifold.Prod.Area`). On `S² × S²` the area of `u` is
therefore `deg(pr₁ ∘ u) a + deg(pr₂ ∘ u) b`
(`TauCeti.integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_degree_mul_add_degree_mul`). In
the equal-area case `a = b` every area is an integer multiple of `a`, so a positive area is at
least `a`
(`TauCeti.le_integralTopForm_mpullback_prod_smul_fubiniStudyForm`). For `a > 0` the ruling
classes, of area `a`, therefore have the minimum positive area. This is the area gap which
prevents the spheres of the ruling classes from bubbling.

**Pseudoholomorphic spheres.** A `J₀`-holomorphic sphere `u : S² → S² × S²` has holomorphic
components, so both degrees are nonnegative, and each vanishes exactly when its component is
constant. Hence:

* for `a, b ≥ 0`, a nonconstant `J₀`-holomorphic sphere has area at least `min a b`
  (`TauCeti.min_le_integralTopForm_mpullback_prod_smul_fubiniStudyForm`), and for `a, b > 0` it
  has area zero exactly when it is constant
  (`TauCeti.integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_zero_iff`);
* the `J₀`-holomorphic spheres with component degrees `(1, 0)`, the class `A`, are exactly the
  maps `z ↦ (g • z, w)` for a Möbius transformation `g` and a point `w`
  (`TauCeti.degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul`), and those of
  class `B` are exactly the maps `z ↦ (w, g • z)`
  (`TauCeti.degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff_exists_smul`);
* for equal areas `a = b ≠ 0`, the `J₀`-holomorphic spheres of area `a` are exactly the spheres
  of these two forms
  (`TauCeti.integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_iff_exists_smul_or_exists_smul`).

The maps `z ↦ (g • z, w)` and `z ↦ (w, g • z)` are themselves smooth and pseudoholomorphic
(`TauCeti.contMDiff_smul_prodMk_const`, `TauCeti.isPseudoholomorphic_smul_prodMk_const`,
`TauCeti.contMDiff_const_prodMk_smul`, `TauCeti.isPseudoholomorphic_const_prodMk_smul`, stated for
any target `M` in place of the other factor).

**Leaves.** Since a Möbius transformation is surjective (`MulAction.surjective`), the image of
`z ↦ (g • z, w)` is the horizontal leaf `S² × {w}` and that of `z ↦ (w, g • z)` the vertical leaf
`{w} × S²` (`Set.range_prodMk_const`, `Set.range_const_prodMk`). So two spheres of one ruling
class have equal or disjoint images, every point of `S² × S²` lies on the image of a sphere of
each class, and a sphere of class `A` meets a sphere of class `B` in exactly one point
(`Set.range_prodMk_const_inter_range_const_prodMk`). These are the two rulings of
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
theorem integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_degree_mul_add_degree_mul
    (a b : ℝ) :
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
  rw [integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_degree_mul_add_degree_mul o hu a a,
    ← add_mul, ← Int.cast_add]
  exact ⟨_, rfl⟩

/-- **A positive area of equal-area `S² × S²` is at least `a`.** For a smooth map `u` from a
compact oriented boundaryless surface to `S² × S²` with the split form
`pr₁^*(a • ω_FS) + pr₂^*(a • ω_FS)`, a positive area is at least `a`, whatever the sign of `a`:
it is a positive integer multiple of `a`. For `a > 0` the bound is attained by the spheres of the
ruling classes `[S² × pt]` and `[pt × S²]`
(`integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_iff_exists_smul_or_exists_smul`, with
`isPseudoholomorphic_smul_prodMk_const` and `isPseudoholomorphic_const_prodMk_smul`), so it is
then the minimum positive area. -/
theorem le_integralTopForm_mpullback_prod_smul_fubiniStudyForm {a : ℝ}
    (hpos : 0 < integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val) :
    a ≤ integralTopForm o (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val := by
  obtain ⟨m, hm⟩ :=
    exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_intCast_mul o hu a
  rw [hm] at hpos ⊢
  exact le_intCast_mul_of_mul_pos hpos

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
theorem degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul :
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
theorem degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff_exists_smul :
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
private theorem exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq (a b : ℝ) :
    ∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ ((m = 0 ∧ n = 0) ↔ ∀ z z', u z = u z') ∧
      integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (SmoothForm.mpullback u hu
          ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val =
        m * a + n * b := by
  refine ⟨_, _, (mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_nonneg,
    (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_nonneg, ?_,
    integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_degree_mul_add_degree_mul _ hu a b⟩
  rw [(mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff,
    (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_eq_zero_iff]
  exact ⟨fun h z z' ↦ Prod.ext (h.1 z z') (h.2 z z'),
    fun h ↦ ⟨fun z z' ↦ congrArg Prod.fst (h z z'), fun z z' ↦ congrArg Prod.snd (h z z')⟩⟩

include hu in
/-- **Nonconstant pseudoholomorphic spheres in `S² × S²` have area at least `min a b`.** For
`a, b ≥ 0`, a nonconstant smooth map `u : S² → S² × S²`, pseudoholomorphic for the product of the
complex structures of the two factors, has area at least `min a b` for the split form
`pr₁^*(a • ω_FS) + pr₂^*(b • ω_FS)`. -/
theorem min_le_integralTopForm_mpullback_prod_smul_fubiniStudyForm {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hne : ∃ z z', u z ≠ u z') :
    min a b ≤ integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val := by
  obtain ⟨m, n, hm, hn, hzero, harea⟩ :=
    exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq hu hhol a b
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
theorem integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_zero_iff {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (b • OnePoint.fubiniStudyForm))).val = 0 ↔
      ∀ z z', u z = u z' := by
  obtain ⟨m, n, hm, hn, hzero, harea⟩ :=
    exists_integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq hu hhol a b
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
theorem integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_iff_exists_smul_or_exists_smul
    {a : ℝ} (ha : a ≠ 0) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu
        ((a • OnePoint.fubiniStudyForm).prod (a • OnePoint.fubiniStudyForm))).val = a ↔
      (∃ (g : GL (Fin 2) ℂ) (w : OnePoint ℂ), u = fun z ↦ (g • z, w)) ∨
        ∃ (w : OnePoint ℂ) (g : GL (Fin 2) ℂ), u = fun z ↦ (w, g • z) := by
  rw [← degree_fst_comp_eq_one_and_degree_snd_comp_eq_zero_iff_exists_smul hhol,
    ← degree_fst_comp_eq_zero_and_degree_snd_comp_eq_one_iff_exists_smul hhol,
    integralTopForm_mpullback_prod_smul_fubiniStudyForm_eq_degree_mul_add_degree_mul _ hu a a,
    ← add_mul, mul_eq_right₀ ha]
  have hm := (mdifferentiable_fst_comp hhol).degree_reindex_complexManifoldOrientation_nonneg
  have hn := (mdifferentiable_snd_comp hhol).degree_reindex_complexManifoldOrientation_nonneg
  constructor
  · intro h
    norm_cast at h
    omega
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> simp [h₁, h₂]

end Holomorphic

section Smooth

variable {F H' M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H' M]

/-- The maps `z ↦ (g • z, t)` from the Riemann sphere to `S² × M` are smooth. -/
theorem contMDiff_smul_prodMk_const (g : GL (Fin 2) ℂ) (t : M) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod I') ∞ (fun z : OnePoint ℂ ↦ (g • z, t)) :=
  -- The Möbius action is holomorphic, hence smooth for the underlying real structure.
  haveI := ContMDiffConstSMul.restrictScalars ℝ
    (inferInstance : ContMDiffConstSMul 𝓘(ℂ) ∞ (GL (Fin 2) ℂ) (OnePoint ℂ))
  (contMDiff_const_smul g).prodMk contMDiff_const

/-- The maps `z ↦ (g • z, t)` from the Riemann sphere to `S² × M` are pseudoholomorphic for the
product of the complex structure of the sphere and any almost complex structure `L` on `M`. -/
theorem isPseudoholomorphic_smul_prodMk_const [FiniteDimensional ℝ F] [IsManifold I' ∞ M]
    (L : SmoothAlmostComplexStructure I' M) (g : GL (Fin 2) ℂ) (t : M) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).prod L)
      (fun z : OnePoint ℂ ↦ (g • z, t)) :=
  SmoothAlmostComplexStructure.isPseudoholomorphic_prod_iff.2
    ⟨isPseudoholomorphic_ofComplexManifold_iff.2
      ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) g).mdifferentiable (by simp)),
      isPseudoholomorphic_const _ _ t⟩

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
