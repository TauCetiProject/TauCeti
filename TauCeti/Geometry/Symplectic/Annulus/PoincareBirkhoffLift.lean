/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Geometry.Symplectic.Annulus.DensityNormalization
public import TauCeti.Geometry.Symplectic.Shear

/-!
# Lifts of area-preserving annulus maps with a boundary twist

The strict annulus fixed-point theorem (the Poincaré–Birkhoff theorem) concerns a smooth
diffeomorphism `f` of the closed annulus `(ℝ / ℤ) × [0, 1]` which preserves a smooth positive area
form `ρ dx ∧ dy` and each boundary circle, and which displaces the two boundary circles strictly
in opposite directions. In the coordinates of the strip `ℝ × [0, 1]` covering the annulus, the
predicate `TauCeti.IsPoincareBirkhoffLift ρ F` records these hypotheses for a lift `F` of `f`,
given as an open partial homeomorphism of the plane:

* the density `ρ` is smooth, positive and `1`-periodic in `x` on the strip;
* `F` is smooth with smooth inverse, its source and target contain the strip, and `F` and its
  inverse map the strip into itself;
* `F` commutes with the deck translation `(x, y) ↦ (x + 1, y)` on the strip;
* `F` preserves `ρ dx ∧ dy`: `ρ(F p) det DF_p = ρ(p)` on the strip;
* `F` preserves both boundary lines, and moves the lower one strictly to the left and the upper
  one strictly to the right: `F(x, 0) = (X₀, 0)` with `X₀ < x`, and `F(x, 1) = (X₁, 1)` with
  `x < X₁`.

The theorem asserts two fixed points of `F` in the half-open fundamental domain
`[0, 1) × (0, 1)` of the interior of the annulus, which are then distinct points of the annulus.
This file reduces it to the standard area form `dx ∧ dy`. Let `Φ` be the density normalization
`TauCeti.stripDensityNormalization ρ`, an orientation-preserving diffeomorphism of a neighbourhood
of the strip which maps the strip onto itself, commutes with the deck translation, fixes both
boundary lines, preserves the order of first coordinates and pulls `a dx ∧ dy` back to
`ρ dx ∧ dy` for a constant `a > 0`. Then:

* the conjugate `Φ ∘ F ∘ Φ⁻¹` (`TauCeti.IsPoincareBirkhoffLift.conj`) is a Poincaré–Birkhoff
  lift for the constant density `1`
  (`TauCeti.IsPoincareBirkhoffLift.isPoincareBirkhoffLift_one_conj`);
* `Φ` maps the fixed points of `F` in `[0, 1) × (0, 1)` bijectively onto those of the conjugate
  (`TauCeti.IsPoincareBirkhoffLift.bijOn_stripDensityNormalization_fixedPoints`).

So the theorem for the standard area form implies it for every density
(`TauCeti.IsPoincareBirkhoffLift.exists_ne_fixedPoints_of_forall_one`). The normalization is built
from integrals of `ρ`, and its smoothness along the boundary lines of the strip uses smoothness of
`ρ` on a neighbourhood of them; so the reduction takes `ρ` smooth on the whole plane. The predicate
only reads `ρ` on the strip (`TauCeti.IsPoincareBirkhoffLift.congr_density`), so any smooth
extension of a density given on the strip can be used.

The affine twist `(x, y) ↦ (x + y - 1 / 2, y)` is a Poincaré–Birkhoff lift for the constant
density (`TauCeti.isPoincareBirkhoffLift_linearPlaneShear_trans_addRight`).

## References

* P. Le Calvez and J. Wang, *Some remarks on the Poincaré–Birkhoff theorem*, Proc. Amer. Math.
  Soc. 138 (2010), 703–715, Theorem 1.
* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff

namespace TauCeti

/-- `F` is a **Poincaré–Birkhoff lift** for the density `ρ`: the lift to the strip `ℝ × [0, 1]` of a
smooth diffeomorphism of the closed annulus `(ℝ / ℤ) × [0, 1]` which preserves the smooth positive
area form `ρ dx ∧ dy` and each boundary circle, and which displaces the lower boundary line strictly
to the left and the upper one strictly to the right. These are the hypotheses of the strict annulus
fixed-point theorem. -/
structure IsPoincareBirkhoffLift (ρ : ℝ × ℝ → ℝ) (F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) :
    Prop where
  contDiffOn_density : ContDiffOn ℝ ∞ ρ (univ ×ˢ Icc 0 1)
  density_pos : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, 0 < ρ (x, y)
  density_add_one : ∀ x, ∀ y ∈ Icc (0 : ℝ) 1, ρ (x + 1, y) = ρ (x, y)
  subset_source : univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.source
  subset_target : univ ×ˢ Icc (0 : ℝ) 1 ⊆ F.target
  contDiffOn : ContDiffOn ℝ ∞ F F.source
  contDiffOn_symm : ContDiffOn ℝ ∞ F.symm F.target
  mapsTo : MapsTo F (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1)
  mapsTo_symm : MapsTo F.symm (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1)
  add_fst : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, F (p + (1, 0)) = F p + (1, 0)
  density_mul_det : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, ρ (F p) * (fderiv ℝ F p).det = ρ p
  snd_apply_mk_zero : ∀ x, (F (x, 0)).2 = 0
  fst_apply_mk_zero_lt : ∀ x, (F (x, 0)).1 < x
  snd_apply_mk_one : ∀ x, (F (x, 1)).2 = 1
  lt_fst_apply_mk_one : ∀ x, x < (F (x, 1)).1

namespace IsPoincareBirkhoffLift

variable {ρ ρ' : ℝ × ℝ → ℝ} {F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}

/-- The predicate only reads the density on the strip. -/
theorem congr_density (hF : IsPoincareBirkhoffLift ρ F) (h : EqOn ρ' ρ (univ ×ˢ Icc 0 1)) :
    IsPoincareBirkhoffLift ρ' F where
  __ := hF
  contDiffOn_density := hF.contDiffOn_density.congr h
  density_pos x y hy := (h (mk_mem_prod (mem_univ x) hy)).symm ▸ hF.density_pos x y hy
  density_add_one x y hy := by
    rw [h (mk_mem_prod (mem_univ _) hy), h (mk_mem_prod (mem_univ _) hy),
      hF.density_add_one x y hy]
  density_mul_det p hp := by
    rw [h (hF.mapsTo hp), h hp, hF.density_mul_det p hp]

/-- The conjugate `Φ ∘ F ∘ Φ⁻¹` of a Poincaré–Birkhoff lift `F` by the density normalization `Φ` of
its density, an open partial homeomorphism of the plane. -/
def conj (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).symm.trans
    (F.trans (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos))

/-- The conjugate `Φ ∘ F ∘ Φ⁻¹` as a composite. -/
@[simp]
theorem coe_conj (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) :
    ⇑(hF.conj hρ₁) = stripDensityNormalization ρ ∘ F ∘
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).symm := by
  rw [conj, OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans,
    coe_stripDensityNormalizationOpenPartialHomeomorph, comp_assoc]

/-- The inverse of the conjugate `Φ ∘ F ∘ Φ⁻¹` is `Φ ∘ F⁻¹ ∘ Φ⁻¹`. -/
@[simp]
theorem coe_conj_symm (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) :
    ⇑(hF.conj hρ₁).symm = stripDensityNormalization ρ ∘ F.symm ∘
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).symm := by
  rw [conj, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.symm_symm, coe_stripDensityNormalizationOpenPartialHomeomorph]

/-- The source of the conjugate `Φ ∘ F ∘ Φ⁻¹`: the points of the target of `Φ` which `Φ⁻¹` sends
into the source of `F`, and then `F` into the source of `Φ`. -/
theorem conj_source (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) :
    (hF.conj hρ₁).source =
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).target ∩
        (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).symm ⁻¹'
          (F.source ∩ F ⁻¹' stripDensityNormalizationSource ρ) := by
  rw [conj, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, stripDensityNormalizationOpenPartialHomeomorph_source]

/-- The target of the conjugate `Φ ∘ F ∘ Φ⁻¹`: the points of the target of `Φ` which `Φ⁻¹` sends
into the target of `F`, and then `F⁻¹` into the source of `Φ`. -/
theorem conj_target (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) :
    (hF.conj hρ₁).target =
      (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).target ∩
        (stripDensityNormalizationOpenPartialHomeomorph hρ₁ hF.density_pos).symm ⁻¹'
          (F.target ∩ F.symm ⁻¹' stripDensityNormalizationSource ρ) := by
  rw [conj, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target, stripDensityNormalizationOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.coe_trans_symm, preimage_comp, preimage_inter, inter_assoc]

/-- On a boundary line `y = c` preserved by `F` and by `Φ`, where `Φ(x, c) = (u(x), c)`, the
conjugate `Φ ∘ F ∘ Φ⁻¹` sends `(u(x), c)` to `(u(X), c)`, where `F(x, c) = (X, c)`. -/
private theorem conj_apply_mk (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hΦc : ∀ x, (stripDensityNormalization ρ (x, c)).2 = c)
    (hFc : ∀ x, (F (x, c)).2 = c) (x : ℝ) :
    hF.conj hρ₁ (stripAreaFraction ρ x, c) = (stripAreaFraction ρ (F (x, c)).1, c) := by
  have h : (stripAreaFraction ρ x, c) = stripDensityNormalization ρ (x, c) :=
    Prod.ext (stripDensityNormalization_fst (x, c)).symm (hΦc x).symm
  obtain ⟨X, hX⟩ : ∃ X, F (x, c) = (X, c) := ⟨_, Prod.ext rfl (hFc x)⟩
  rw [coe_conj, comp_apply, comp_apply, h,
    stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply
      (univ_prod_Icc_subset_stripDensityNormalizationSource hF.density_pos
        (mk_mem_prod (mem_univ x) hc)), hX]
  exact Prod.ext (stripDensityNormalization_fst (X, c)) (hΦc X)

/-- The conjugate `Φ ∘ F ∘ Φ⁻¹` commutes with the deck translation on the strip. -/
private theorem conj_add_fst (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ) {q : ℝ × ℝ}
    (hq : q ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    hF.conj hρ₁ (q + (1, 0)) = hF.conj hρ₁ q + (1, 0) := by
  have hc := hρ₁.continuous.continuousOn (s := univ ×ˢ Icc 0 1)
  have ha := (annulusArea_pos_of_forall hc hF.density_pos).ne'
  rw [coe_conj, comp_apply, comp_apply, comp_apply, comp_apply,
    stripDensityNormalizationOpenPartialHomeomorph_symm_add_fst hF.density_add_one hq.2,
    hF.add_fst _ (mapsTo_stripDensityNormalizationOpenPartialHomeomorph_symm hF.density_add_one hq),
    stripDensityNormalization_add_fst hc hF.density_add_one ha
      (hF.mapsTo (mapsTo_stripDensityNormalizationOpenPartialHomeomorph_symm hF.density_add_one
        hq)).2]

/-- The conjugate `Φ ∘ F ∘ Φ⁻¹` preserves `dx ∧ dy` on the strip. -/
private theorem det_fderiv_conj (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ)
    {q : ℝ × ℝ} (hq : q ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    (fderiv ℝ (hF.conj hρ₁) q).det = 1 := by
  obtain ⟨p, hp, rfl⟩ := (bijOn_stripDensityNormalization hρ₁.continuous.continuousOn
    hF.density_add_one hF.density_pos).surjOn hq
  have hFp : DifferentiableAt ℝ F p :=
    (hF.contDiffOn.contDiffAt (F.open_source.mem_nhds (hF.subset_source hp))).differentiableAt
      (by simp)
  rw [coe_conj, det_fderiv_stripDensityNormalization_comp_comp_symm hρ₁ hF.density_pos
    (univ_prod_Icc_subset_stripDensityNormalizationSource hF.density_pos hp) hFp,
    hF.density_mul_det p hp, div_self (hF.density_pos p.1 p.2 hp.2).ne']

/-- The conjugate `Φ ∘ F ∘ Φ⁻¹` and its inverse are smooth on their domains, for a density smooth
on the plane. -/
private theorem contDiffOn_conj (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ)
    (hρ : ContDiff ℝ ∞ ρ) :
    ContDiffOn ℝ ∞ (hF.conj hρ₁) (hF.conj hρ₁).source ∧
      ContDiffOn ℝ ∞ (hF.conj hρ₁).symm (hF.conj hρ₁).target := by
  have hΦ := contDiff_stripDensityNormalization_of_forall hρ hF.density_pos
  have hΦsymm :=
    contDiffOn_stripDensityNormalizationOpenPartialHomeomorph_symm hρ₁ hF.density_pos hρ
  constructor
  · -- The conjugate is `Φ ∘ (F ∘ Φ⁻¹)`, with `Φ` smooth on the plane.
    rw [coe_conj, conj_source]
    exact hΦ.comp_contDiffOn (hF.contDiffOn.comp (hΦsymm.mono inter_subset_left)
      fun q hq ↦ hq.2.1)
  · -- The inverse of the conjugate is `Φ ∘ (F⁻¹ ∘ Φ⁻¹)`.
    rw [coe_conj_symm, conj_target]
    exact hΦ.comp_contDiffOn (hF.contDiffOn_symm.comp (hΦsymm.mono inter_subset_left)
      fun q hq ↦ hq.2.1)

/-- **Reduction to the standard area form.** Conjugating a Poincaré–Birkhoff lift for a density
`ρ`, smooth on the plane, by the density normalization `Φ` of `ρ` gives a Poincaré–Birkhoff lift
`Φ ∘ F ∘ Φ⁻¹` for the constant density `1`. -/
theorem isPoincareBirkhoffLift_one_conj (hF : IsPoincareBirkhoffLift ρ F) (hρ₁ : ContDiff ℝ 1 ρ)
    (hρ : ContDiff ℝ ∞ ρ) :
    IsPoincareBirkhoffLift (fun _ ↦ 1) (hF.conj hρ₁) := by
  have hc := hρ₁.continuous.continuousOn (s := univ ×ˢ Icc 0 1)
  have hbij := bijOn_stripDensityNormalization hc hF.density_add_one hF.density_pos
  have hS := univ_prod_Icc_subset_stripDensityNormalizationSource hF.density_pos
  have hT := univ_prod_Icc_subset_stripDensityNormalizationOpenPartialHomeomorph_target
    (hρ₁ := hρ₁) (hpos := hF.density_pos) hF.density_add_one
  have hsymm := mapsTo_stripDensityNormalizationOpenPartialHomeomorph_symm (hρ₁ := hρ₁)
    (hpos := hF.density_pos) hF.density_add_one
  have hs := stripColumnMean_pos_of_forall hc hF.density_pos
  have hu := stripAreaFraction_strictMono hc hs
  have hsurj := stripAreaFraction_surjective hc hF.density_add_one
    (annulusArea_pos_of_forall hc hF.density_pos).ne'
  have h0 := conj_apply_mk hF hρ₁ (left_mem_Icc.2 zero_le_one)
    stripDensityNormalization_snd_mk_zero hF.snd_apply_mk_zero
  have h1 := conj_apply_mk hF hρ₁ (right_mem_Icc.2 zero_le_one)
    (fun x ↦ stripDensityNormalization_snd_mk_one (hs x).ne') hF.snd_apply_mk_one
  refine
    { contDiffOn_density := contDiffOn_const
      density_pos := fun _ _ _ ↦ one_pos
      density_add_one := fun _ _ _ ↦ rfl
      subset_source := fun q hq ↦ ?_
      subset_target := fun q hq ↦ ?_
      contDiffOn := (contDiffOn_conj hF hρ₁ hρ).1
      contDiffOn_symm := (contDiffOn_conj hF hρ₁ hρ).2
      mapsTo := fun q hq ↦ by
        rw [coe_conj]; exact hbij.mapsTo (hF.mapsTo (hsymm hq))
      mapsTo_symm := fun q hq ↦ by
        rw [coe_conj_symm]; exact hbij.mapsTo (hF.mapsTo_symm (hsymm hq))
      add_fst := fun q hq ↦ conj_add_fst hF hρ₁ hq
      density_mul_det := fun q hq ↦ by simpa using det_fderiv_conj hF hρ₁ hq
      snd_apply_mk_zero := fun x' ↦ by obtain ⟨x, rfl⟩ := hsurj x'; rw [h0]
      fst_apply_mk_zero_lt := fun x' ↦ by
        obtain ⟨x, rfl⟩ := hsurj x'; rw [h0]; exact hu (hF.fst_apply_mk_zero_lt x)
      snd_apply_mk_one := fun x' ↦ by obtain ⟨x, rfl⟩ := hsurj x'; rw [h1]
      lt_fst_apply_mk_one := fun x' ↦ by
        obtain ⟨x, rfl⟩ := hsurj x'; rw [h1]; exact hu (hF.lt_fst_apply_mk_one x) }
  · rw [conj_source]
    exact ⟨hT hq, hF.subset_source (hsymm hq), hS (hF.mapsTo (hsymm hq))⟩
  · rw [conj_target]
    exact ⟨hT hq, hF.subset_target (hsymm hq), hS (hF.mapsTo_symm (hsymm hq))⟩

/-- **Fixed points under the reduction.** The density normalization `Φ` maps the fixed points of a
Poincaré–Birkhoff lift `F` in the fundamental domain `[0, 1) × (0, 1)` bijectively onto the fixed
points of the conjugate `Φ ∘ F ∘ Φ⁻¹` there. -/
theorem bijOn_stripDensityNormalization_fixedPoints (hF : IsPoincareBirkhoffLift ρ F)
    (hρ₁ : ContDiff ℝ 1 ρ) :
    BijOn (stripDensityNormalization ρ) (fixedPoints F ∩ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
      (fixedPoints (hF.conj hρ₁) ∩ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hbij := bijOn_stripDensityNormalization hρ₁.continuous.continuousOn hF.density_add_one
    hF.density_pos
  have hD : Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ⊆ univ ×ˢ Icc 0 1 :=
    fun p hp ↦ ⟨mem_univ _, Ioo_subset_Icc_self hp.2⟩
  have hiff {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :=
    stripDensityNormalization_mem_Ico_prod_Ioo_iff hρ₁.continuous.continuousOn hF.density_pos
      hp.2
  have hS := univ_prod_Icc_subset_stripDensityNormalizationSource hF.density_pos
  refine ⟨fun p ⟨hfix, hp⟩ ↦ ⟨?_, (hiff (hD hp)).2 hp⟩,
    hbij.injOn.mono fun p hp ↦ hD hp.2, fun q ⟨hfix, hq⟩ ↦ ?_⟩
  · -- `Φ ∘ F ∘ Φ⁻¹` fixes `Φ(p)`, since `Φ⁻¹(Φ(p)) = p` and `F(p) = p`.
    rw [mem_fixedPoints_iff, coe_conj, comp_apply, comp_apply,
      stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply (hS (hD hp)),
      mem_fixedPoints_iff.1 hfix]
  · -- `p = Φ⁻¹(q)` lies in the strip, and `Φ(F(p)) = q = Φ(p)` with `Φ` injective there.
    obtain ⟨p, hp, rfl⟩ := hbij.surjOn (hD hq)
    refine ⟨p, ⟨mem_fixedPoints_iff.2 ?_, (hiff hp).1 hq⟩, rfl⟩
    have h := mem_fixedPoints_iff.1 hfix
    rw [coe_conj, comp_apply, comp_apply,
      stripDensityNormalizationOpenPartialHomeomorph_symm_apply_apply (hS hp)] at h
    exact hbij.injOn (hF.mapsTo hp) hp h

/-- **The strict annulus fixed-point theorem reduces to the standard area form.** If every
Poincaré–Birkhoff lift for the constant density `1` has two fixed points in the fundamental domain
`[0, 1) × (0, 1)`, then so does every Poincaré–Birkhoff lift for a density smooth on the plane. -/
theorem exists_ne_fixedPoints_of_forall_one (hF : IsPoincareBirkhoffLift ρ F)
    (hρ : ContDiff ℝ ∞ ρ)
    (h : ∀ G : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), IsPoincareBirkhoffLift (fun _ ↦ 1) G →
      ∃ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∃ q ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        p ≠ q ∧ G p = p ∧ G q = q) :
    ∃ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∃ q ∈ Ico (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      p ≠ q ∧ F p = p ∧ F q = q := by
  have hρ₁ : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  obtain ⟨p, hp, q, hq, hpq, hpG, hqG⟩ := h _ (hF.isPoincareBirkhoffLift_one_conj hρ₁ hρ)
  have hbij := hF.bijOn_stripDensityNormalization_fixedPoints hρ₁
  obtain ⟨p', ⟨hp'F, hp'⟩, rfl⟩ := hbij.surjOn ⟨hpG, hp⟩
  obtain ⟨q', ⟨hq'F, hq'⟩, rfl⟩ := hbij.surjOn ⟨hqG, hq⟩
  exact ⟨p', hp', q', hq', fun h ↦ hpq (congrArg _ h), hp'F, hq'F⟩

end IsPoincareBirkhoffLift

/-! ### An example -/

/-- The affine twist `(x, y) ↦ (x + y - 1 / 2, y)`, the shear `(x, y) ↦ (x + y, y)` followed by a
translation, is a Poincaré–Birkhoff lift for the constant density `1`: it preserves `dx ∧ dy`, and
moves the line `y = 0` by `-1 / 2` and the line `y = 1` by `1 / 2`. -/
theorem isPoincareBirkhoffLift_linearPlaneShear_trans_addRight :
    IsPoincareBirkhoffLift (fun _ ↦ 1)
      (linearPlaneShear.toHomeomorph.trans
        (Homeomorph.addRight ((-2⁻¹ : ℝ), (0 : ℝ)))).toOpenPartialHomeomorph := by
  set G := (linearPlaneShear.toHomeomorph.trans
    (Homeomorph.addRight ((-2⁻¹ : ℝ), (0 : ℝ)))).toOpenPartialHomeomorph with hG
  have happly (p : ℝ × ℝ) : G p = (p.1 + p.2 - 2⁻¹, p.2) := by
    simp [hG, sub_eq_add_neg]
  have hsymm (p : ℝ × ℝ) : G.symm p = (p.1 - p.2 + 2⁻¹, p.2) := by
    rw [eq_comm, G.eq_symm_apply (by simp [hG]) (by simp [hG]), happly]
    refine Prod.ext ?_ rfl
    dsimp only
    ring
  have hcoe : ⇑G = fun p : ℝ × ℝ ↦ (p.1 + p.2 - 2⁻¹, p.2) := funext happly
  have hcoe_symm : ⇑G.symm = fun p : ℝ × ℝ ↦ (p.1 - p.2 + 2⁻¹, p.2) := funext hsymm
  have hderiv (p : ℝ × ℝ) : fderiv ℝ G p = (linearPlaneShear : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) := by
    have : ⇑G = fun q ↦ linearPlaneShear q + ((-2⁻¹ : ℝ), (0 : ℝ)) := by
      funext q
      rw [happly, linearPlaneShear_apply, Prod.mk_add_mk, add_zero, sub_eq_add_neg]
    rw [this]
    exact (linearPlaneShear.hasFDerivAt.add_const _).fderiv
  refine
    { contDiffOn_density := contDiffOn_const
      density_pos := fun _ _ _ ↦ one_pos
      density_add_one := fun _ _ _ ↦ rfl
      subset_source := by simp [hG]
      subset_target := by simp [hG]
      contDiffOn := by rw [hcoe]; fun_prop
      contDiffOn_symm := by rw [hcoe_symm]; fun_prop
      mapsTo := fun p hp ↦ by simpa [happly] using hp
      mapsTo_symm := fun p hp ↦ by simpa [hsymm] using hp
      add_fst := fun p _ ↦ Prod.ext (by simp [happly]; ring) (by simp [happly])
      density_mul_det := fun p _ ↦ ?_
      snd_apply_mk_zero := fun x ↦ by simp [happly]
      fst_apply_mk_zero_lt := fun x ↦ by simp [happly]
      snd_apply_mk_one := fun x ↦ by simp [happly]
      lt_fst_apply_mk_one := fun x ↦ by simp [happly]; linarith }
  rw [hderiv, ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp

end TauCeti
