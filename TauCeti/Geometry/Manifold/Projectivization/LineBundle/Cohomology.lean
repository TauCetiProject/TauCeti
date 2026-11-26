/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Normalize
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Twist
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Cech
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum
import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import TauCeti.Topology.Separation.Hausdorff
import TauCeti.Topology.Sheaves.Cech.Functoriality

/-!
# The first cohomology of `𝒪(k)` and of split bundles on the complex projective line

This file proves that the first Čech cohomology of the sheaf of holomorphic sections of the line
bundle `𝒪(k)` (`Projectivization.twistCore k`) on the complex projective line
`ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` vanishes for `k ≥ -1`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le`). This is
the vanishing `H¹(ℂℙ¹, 𝒪(k)) = 0` that makes a holomorphic sphere `u` with
`u* TX ≅ 𝒪(a₁) ⊕ ⋯ ⊕ 𝒪(aₘ)`, all `aᵢ ≥ -1`, a regular sphere: for a line in `ℂPⁿ`,
`u* TℂPⁿ ≅ 𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹`.

The proof compares `𝒪(k)` with the divisor sheaf `𝒪(k [∞])` of the Riemann sphere `OnePoint ℂ`,
whose cohomology is known from Riemann–Roch on `ℙ¹`
(`TauCeti.RiemannSurface.isZero_divisorCechCohomology_one_sphere_of_neg_one_le_degree`), along
the identification `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℂℙ¹`, `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`. The coordinate changes of `𝒪(k)` are `[v] ↦ (v i / v j) ^ k`, so a section with
coordinate `g(t)` in the frame of the chart `1` has coordinate `t⁻ᵏ g(t)` in the frame of the
chart `0`, whose coordinate is `w = t⁻¹`. This coordinate is holomorphic at `[1 : 0]`, where
`w = 0`, exactly when `g` has a pole of order at most `k` at `∞`, which is the condition defining
`𝒪(k [∞])`. Thus reading a section of `𝒪(k)` in the frame of the chart `1` identifies the sheaf of
holomorphic sections of `𝒪(k)` with `𝒪(k [∞])` (`Projectivization.twistCoreDivisorHom`, an
isomorphism of presheaves by `Projectivization.isIso_twistCoreDivisorHom`). The coordinate of a
divisor section in the frame of the chart `0` is defined at `∞` by filling the removable
singularity of `t⁻ᵏ g(t)` (`TauCeti.RiemannSurface.toDivisorSection`). Čech cohomology is
carried along the isomorphism by `TopCat.Hom.epi_cechCohomologyPullback`, and `𝒪(k [∞])` has
degree `k`.

The argument uses no Serre duality: it computes `H¹(ℂℙ¹, 𝒪(k))` from the divisor sheaves of the
Riemann sphere, whose first cohomology vanishes in degree at least `-1`.

**Split bundles.** On `ℂℙⁿ`, the sheaf of holomorphic sections of a split bundle `⨁ₗ 𝒪(k l)`
(`Projectivization.twistSumCore k`) is the biproduct of the sheaves of holomorphic sections of the
summands `𝒪(k l)` (`Projectivization.twistSumSectionBiconeIsBilimit`), with the projections onto
and the inclusions of the summands. Čech cohomology is an additive functor of the sheaf, so
`Hⁱ(ℂℙⁿ, ⨁ₗ 𝒪(k l))` vanishes when every `Hⁱ(ℂℙⁿ, 𝒪(k l))` does. On `ℂℙ¹` this gives
`H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` when every `k l ≥ -1`. Applied to the splitting
`ℓ* TℂPᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ` along the coordinate line `ℓ`, this gives `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`, in
`TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent.Cohomology`).

## Main declarations

* `Projectivization.projectiveLineToSphere`: the identification of `ℂℙ¹` with the Riemann sphere,
  as a morphism of topological spaces.
* `Projectivization.twistCoreDivisorHom`: the morphism from `𝒪(k [∞])` to the pushforward of the
  sheaf of holomorphic sections of `𝒪(k)`; `Projectivization.isIso_twistCoreDivisorHom`: it is
  an isomorphism. It is computed in the frame of the chart `1` by
  `Projectivization.twistCoreDivisorHom_app_apply_of_mem_affineOpen_one`, in the frame of the
  chart `0` by
  `Projectivization.twistTransition_smul_twistCoreDivisorHom_app_apply_of_mem_affineOpen_zero`,
  and its inverse by `Projectivization.inv_twistCoreDivisorHom_app_apply`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le`:
  `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`.
* `Projectivization.twistSumSectionProj`, `Projectivization.twistSumSectionSingle` and
  `Projectivization.twistSumSectionBicone`: the projections onto and inclusions of the summands
  of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` on `ℂℙⁿ`;
  `Projectivization.twistSumSectionBiconeIsBilimit`: they form a biproduct.
* `Projectivization.isZero_holomorphicSectionCechCohomology_twistSumCore`: `Hⁱ(ℂℙⁿ, ⨁ₗ 𝒪(k l))`
  vanishes when every `Hⁱ(ℂℙⁿ, 𝒪(k l))` does.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`:
  `H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` when every `k l ≥ -1`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §§16–17 and §29.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the regularity of lines.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Filter Function OnePoint Opposite Set
open TopologicalSpace Topology
open TauCeti TauCeti.RiemannSurface TauCeti.AlgebraicGeometry
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable (k : ℤ)

/-- The coordinate in the frame of the chart `j` of a function `s` read as a section of `𝒪(k)` on
the projective line. -/
private def coord (j : Fin 2) (s : ℙ ℂ (Fin 2 → ℂ) → ℂ) (x : ℙ ℂ (Fin 2 → ℂ)) : ℂ :=
  twistTransition k ((twistCore (𝕜 := ℂ) (n := 1) k).indexAt x) j x * s x

private theorem contMDiff_mk_iff {W : Opens (ℙ ℂ (Fin 2 → ℂ))}
    (s : (x : W) → (twistCore (𝕜 := ℂ) (n := 1) k).Fiber x) :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) (𝓘(ℂ, Fin 1 → ℂ).prod 𝓘(ℂ)) ω
        (fun x : W ↦ TotalSpace.mk' ℂ (x : ℙ ℂ (Fin 2 → ℂ)) (s x)) ↔
      ∀ j, ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω
        (coord k j (Subtype.val.extend (fun x : W ↦ (s x : ℂ)) 0)) (W ∩ affineOpen j) := by
  set t : ℙ ℂ (Fin 2 → ℂ) → ℂ := Subtype.val.extend (fun x : W ↦ (s x : ℂ)) 0
  have hst : (fun x : W ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := 1) k).Fiber)
      (x : ℙ ℂ (Fin 2 → ℂ)) (s x)) = fun x : W ↦ TotalSpace.mk' ℂ (x : ℙ ℂ (Fin 2 → ℂ)) (t x) := by
    funext x
    have he : t x = s x := Function.extend_val_apply x.property
    exact congrArg (TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := 1) k).Fiber) _) he.symm
  rw [hst]
  refine Iff.trans ?_ (contMDiffOn_section_twistCore_iff k t W.isOpen)
  exact ⟨fun h x hx ↦ (contMDiffAt_subtype_iff (U := W) (x := ⟨x, hx⟩)
      (f := fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := 1) k).Fiber) x (t x))).1
        (h ⟨x, hx⟩) |>.contMDiffWithinAt,
    fun h x ↦ (contMDiffAt_subtype_iff
      (f := fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := 1) k).Fiber) x (t x))).2
        ((h x x.property).contMDiffAt (W.isOpen.mem_nhds x.property))⟩

/-! ### The projective line and the Riemann sphere -/

/-- Near `∞`, the points of the Riemann sphere are finite and nonzero. -/
private theorem eventually_ne_infty_and_ne_zero :
    ∀ᶠ z in 𝓝[≠] (∞ : OnePoint ℂ), z ≠ (∞ : OnePoint ℂ) ∧ z ≠ ((0 : ℂ) : OnePoint ℂ) :=
  (eventually_mem_nhdsWithin (a := (∞ : OnePoint ℂ))).and
    (nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show (∞ : OnePoint ℂ) ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) from
        by simp [infty_ne_coe])))

/-! ### The coordinate at infinity -/

/-- The coordinate in the frame of the chart `0` of the section of `𝒪(k)` with coordinate `g` in
the frame of the chart `1`, read on the Riemann sphere: the product of `g` with the `k`-th power of
the inverted coordinate, with its removable singularity at `∞` filled. -/
private def lowerCoord (g : OnePoint ℂ → ℂ) : OnePoint ℂ → ℂ :=
  toDivisorSection 0 fun y ↦ invChart y ^ k * g y

/-- The divisor `k [∞]` has coefficient `k` at `∞`. -/
private theorem zsmul_ofPoint_apply_infty :
    (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) (∞ : OnePoint ℂ) = k := by
  have h := WeilDivisor.coeff_ofPoint_self (∞ : OnePoint ℂ)
  simp only [WeilDivisor.coeff] at h
  simp [h]

/-- The divisor `k [∞]` has coefficient `0` away from `∞`. -/
private theorem zsmul_ofPoint_apply_of_ne {y : OnePoint ℂ} (hy : y ≠ (∞ : OnePoint ℂ)) :
    (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) y = 0 := by
  have h := WeilDivisor.coeff_ofPoint_of_ne hy
  simp only [WeilDivisor.coeff] at h
  simp [h]

/-- For a local section `g` of `𝒪(k [∞])` at a point `y ≠ 0`, the coordinate at infinity is a
holomorphic local function at `y`. -/
private theorem isDivisorSectionAt_lowerCoord {g : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (hg : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) :
    IsDivisorSectionAt 0 (lowerCoord k g) y := by
  have hm : MeromorphicAt ((fun y ↦ invChart y ^ k) * g) y :=
    (meromorphicAt_invChart_zpow hy k).mul hg.meromorphicAt
  refine isDivisorSectionAt_toDivisorSection hm ?_
  have ho := hg.neg_le_meromorphicOrderAt
  -- read the product pointwise as a product of functions, the form of `meromorphicOrderAt_mul`
  change _ ≤ meromorphicOrderAt ((fun y ↦ invChart y ^ k) * g) y
  rw [meromorphicOrderAt_mul (meromorphicAt_invChart_zpow hy k) hg.meromorphicAt]
  simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
  induction y using OnePoint.rec with
  | infty =>
    rw [zsmul_ofPoint_apply_infty] at ho
    rw [meromorphicOrderAt_invChart_zpow_infty]
    calc (0 : WithTop ℤ) = (k : WithTop ℤ) + ((-k : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
      _ ≤ _ := add_le_add_right ho _
  | coe t =>
    rw [zsmul_ofPoint_apply_of_ne k (coe_ne_infty t)] at ho
    rw [meromorphicOrderAt_invChart_zpow_coe (by simpa using hy), zero_add]
    simpa using ho

private theorem contMDiffAt_lowerCoord {g : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (hg : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (lowerCoord k g) y :=
  (isDivisorSectionAt_lowerCoord k hg hy).contMDiffAt (by simp)

private theorem lowerCoord_eventuallyEq {g : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (hg : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) :
    lowerCoord k g =ᶠ[𝓝[≠] y] fun y ↦ invChart y ^ k * g y :=
  toDivisorSection_eventuallyEq 0 ((meromorphicAt_invChart_zpow hy k).mul hg.meromorphicAt)

/-- The coordinate at infinity only depends on the punctured germ. -/
private theorem lowerCoord_congr {g g' : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (h : g =ᶠ[𝓝[≠] y] g') : lowerCoord k g y = lowerCoord k g' y :=
  toDivisorSection_congr_nhdsNE (by filter_upwards [h] with z hz; rw [hz])

/-- At a finite point `y ≠ 0` where `g` is continuous, the coordinate at infinity is
`(y⁻¹)^k g y`. -/
private theorem lowerCoord_apply {g : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (hg : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) (hy' : y ≠ (∞ : OnePoint ℂ)) (hc : ContinuousAt g y) :
    lowerCoord k g y = invChart y ^ k * g y := by
  refine ContinuousAt.eq_of_eventuallyEq_nhdsNE (contMDiffAt_lowerCoord k hg hy).continuousAt
    (ContinuousAt.mul ?_ hc) (lowerCoord_eventuallyEq k hg hy)
  have hs : y ∈ (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).source := by
    simpa [invChart_source] using hy
  exact (invChart.continuousAt hs).zpow₀ k (Or.inl (invChart_ne_zero hy' hy))

private theorem lowerCoord_add {g₁ g₂ : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (h₁ : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g₁ y)
    (h₂ : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g₂ y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) :
    lowerCoord k (g₁ + g₂) y = lowerCoord k g₁ y + lowerCoord k g₂ y := by
  refine ContinuousAt.eq_of_eventuallyEq_nhdsNE
    (contMDiffAt_lowerCoord k (h₁.add h₂) hy).continuousAt
    ((contMDiffAt_lowerCoord k h₁ hy).continuousAt.add
      (contMDiffAt_lowerCoord k h₂ hy).continuousAt) ?_
  filter_upwards [lowerCoord_eventuallyEq k (h₁.add h₂) hy, lowerCoord_eventuallyEq k h₁ hy,
    lowerCoord_eventuallyEq k h₂ hy] with z hz hz₁ hz₂
  simp only [Pi.add_apply, hz, hz₁, hz₂, mul_add]

private theorem lowerCoord_smul {g : OnePoint ℂ → ℂ} {y : OnePoint ℂ}
    (hg : IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) g y)
    (hy : y ≠ ((0 : ℂ) : OnePoint ℂ)) (c : ℂ) :
    lowerCoord k (c • g) y = c * lowerCoord k g y := by
  refine ContinuousAt.eq_of_eventuallyEq_nhdsNE
    (contMDiffAt_lowerCoord k (hg.const_smul c) hy).continuousAt
    (continuousAt_const.mul (contMDiffAt_lowerCoord k hg hy).continuousAt) ?_
  filter_upwards [lowerCoord_eventuallyEq k (hg.const_smul c) hy,
    lowerCoord_eventuallyEq k hg hy] with z hz hz'
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hz, hz']
  ring

/-! ### The comparison morphism -/

/-- The identification of the projective line `ℙ ℂ (Fin 2 → ℂ)` with the Riemann sphere
`OnePoint ℂ`, `[t : 1] ↦ t` and `[1 : 0] ↦ ∞`, as a morphism of topological spaces. -/
def projectiveLineToSphere : TopCat.of (ℙ ℂ (Fin 2 → ℂ)) ⟶ TopCat.of (OnePoint ℂ) :=
  TopCat.ofHom ⟨(equivProjectivization ℂ).symm, contMDiff_equivProjectivization_symm.continuous⟩

/-- The identification of `ℂℙ¹` with the Riemann sphere is the inverse of
`OnePoint.equivProjectivization`. -/
@[simp]
theorem projectiveLineToSphere_apply (x : ℙ ℂ (Fin 2 → ℂ)) :
    projectiveLineToSphere x = (equivProjectivization ℂ).symm x :=
  (rfl)

/-- A point of `ℂℙ¹` lies in the inverse image of an open set `U` of the Riemann sphere exactly
when the corresponding point of the sphere lies in `U`. -/
@[simp]
theorem mem_map_projectiveLineToSphere {U : Opens (OnePoint ℂ)} {x : ℙ ℂ (Fin 2 → ℂ)} :
    x ∈ (Opens.map projectiveLineToSphere).obj U ↔ (equivProjectivization ℂ).symm x ∈ U :=
  Iff.rfl

open Classical in
/-- The section of `𝒪(k)` attached to a section `g` of `𝒪(k [∞])` over `U`: its coordinate in the
frame of the chart `1` is `g`, and its coordinate in the frame of the chart `0` is
`lowerCoord k g`. -/
private def sectionFun {U : Opens (OnePoint ℂ)}
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    (x : ℙ ℂ (Fin 2 → ℂ)) : ℂ :=
  if x ∈ affineOpen 1 then
    twistTransition k 1 ((twistCore (𝕜 := ℂ) (n := 1) k).indexAt x) x *
      Subtype.val.extend g.val 0 ((equivProjectivization ℂ).symm x)
  else lowerCoord k (Subtype.val.extend g.val 0) ((equivProjectivization ℂ).symm x)

variable {k}

private theorem coord_one_sectionFun {U : Opens (OnePoint ℂ)}
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    {x : ℙ ℂ (Fin 2 → ℂ)} (hx : x ∈ affineOpen 1) :
    coord k 1 (sectionFun k g) x =
      Subtype.val.extend g.val 0 ((equivProjectivization ℂ).symm x) := by
  rw [coord, sectionFun]
  simp only [hx, ↓reduceIte]
  rw [← mul_assoc, twistTransition_mul_twistTransition k 1 1 (mem_affineOpen_twistCore_indexAt k x),
    twistTransition_self k hx, one_mul]

/-- A section `g` of `𝒪(k [∞])` is holomorphic at the finite points of its domain. -/
private theorem contMDiffAt_extend {U : Opens (OnePoint ℂ)}
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U) {y : OnePoint ℂ}
    (hyU : y ∈ U) (hy : y ≠ (∞ : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val.extend g.val 0) y :=
  (isDivisorSectionAt_extend g.property ⟨y, hyU⟩).contMDiffAt
    (zsmul_ofPoint_apply_of_ne k hy).le

private theorem coord_zero_sectionFun {U : Opens (OnePoint ℂ)}
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    {x : ℙ ℂ (Fin 2 → ℂ)} (hx : x ∈ affineOpen 0) (hxU : (equivProjectivization ℂ).symm x ∈ U) :
    coord k 0 (sectionFun k g) x =
      lowerCoord k (Subtype.val.extend g.val 0) ((equivProjectivization ℂ).symm x) := by
  set y := (equivProjectivization ℂ).symm x with hy
  have hxy : x = equivProjectivization ℂ y := by rw [hy, Equiv.apply_symm_apply]
  by_cases hx1 : x ∈ affineOpen 1
  · have hyi : y ≠ (∞ : OnePoint ℂ) := by
      rwa [hxy, equivProjectivization_mem_affineOpen_one_iff] at hx1
    have hy0 : y ≠ ((0 : ℂ) : OnePoint ℂ) := by
      rwa [hxy, equivProjectivization_mem_affineOpen_zero_iff] at hx
    rw [coord, sectionFun]
    simp only [hx1, ↓reduceIte]
    rw [← mul_assoc,
      twistTransition_mul_twistTransition k 1 0 (mem_affineOpen_twistCore_indexAt k x),
      lowerCoord_apply k (isDivisorSectionAt_extend g.property ⟨y, hxU⟩) hy0 hyi
        (contMDiffAt_extend g hxU hyi).continuousAt]
    rw [hxy, twistTransition_one_zero_equivProjectivization k y hyi, Equiv.symm_apply_apply]
  · rw [coord, sectionFun]
    simp only [hx1, ↓reduceIte]
    rw [indexAt_twistCore_eq_zero_of_notMem k hx1, twistTransition_self k hx, one_mul]

private theorem sectionFun_contMDiff {U : Opens (OnePoint ℂ)}
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U) :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) (𝓘(ℂ, Fin 1 → ℂ).prod 𝓘(ℂ)) ω
      (fun x : (Opens.map projectiveLineToSphere).obj U ↦
        TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := 1) k).Fiber)
          (x : ℙ ℂ (Fin 2 → ℂ)) (sectionFun k g x)) := by
  rw [contMDiff_mk_iff k (fun x : (Opens.map projectiveLineToSphere).obj U ↦ sectionFun k g x)]
  have hext : ∀ x ∈ (Opens.map projectiveLineToSphere).obj U,
      Subtype.val.extend (fun x : (Opens.map projectiveLineToSphere).obj U ↦ sectionFun k g x) 0 x
        = sectionFun k g x := fun _ hx ↦ Function.extend_val_apply hx
  have hsymm : ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (equivProjectivization ℂ).symm :=
    contMDiff_equivProjectivization_symm
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · refine ContMDiffOn.congr (f := lowerCoord k (Subtype.val.extend g.val 0) ∘
      (equivProjectivization ℂ).symm) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · have hy0 : (equivProjectivization ℂ).symm x ≠ ((0 : ℂ) : OnePoint ℂ) := by
        rw [← equivProjectivization_mem_affineOpen_zero_iff, Equiv.apply_symm_apply]
        exact hx.2
      exact ((contMDiffAt_lowerCoord k (isDivisorSectionAt_extend g.property ⟨_, hx.1⟩)
        hy0).comp x (hsymm x)).contMDiffWithinAt
    · simp only [coord, hext x hx.1, Function.comp_apply]
      exact coord_zero_sectionFun g hx.2 hx.1
  · refine ContMDiffOn.congr (f := Subtype.val.extend g.val 0 ∘
      (equivProjectivization ℂ).symm) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · have hyi : (equivProjectivization ℂ).symm x ≠ (∞ : OnePoint ℂ) := by
        rw [← equivProjectivization_mem_affineOpen_one_iff, Equiv.apply_symm_apply]
        exact hx.2
      exact ((contMDiffAt_extend g hx.1 hyi).comp x (hsymm x)).contMDiffWithinAt
    · simp only [coord, hext x hx.1, Function.comp_apply]
      exact coord_one_sectionFun g hx.2

/-- The point of the Riemann sphere corresponding to a point outside `U₁` is not `0`. -/
private theorem symm_ne_zero_of_notMem_affineOpen_one {x : ℙ ℂ (Fin 2 → ℂ)}
    (hx : x ∉ affineOpen 1) : (equivProjectivization ℂ).symm x ≠ ((0 : ℂ) : OnePoint ℂ) := by
  rw [(equivProjectivization_symm_eq_infty_iff _).2 hx]
  exact infty_ne_coe _

private theorem sectionFun_add {U : Opens (OnePoint ℂ)}
    (g₁ g₂ : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    (x : ℙ ℂ (Fin 2 → ℂ)) (hxU : (equivProjectivization ℂ).symm x ∈ U) :
    sectionFun k (g₁ + g₂) x = sectionFun k g₁ x + sectionFun k g₂ x := by
  have he := Function.extend_add (Subtype.val : U → OnePoint ℂ) g₁.val g₂.val 0 0
  rw [add_zero] at he
  rw [sectionFun, sectionFun, sectionFun, Submodule.coe_add, he]
  split_ifs with hx1
  · rw [Pi.add_apply, mul_add]
  · exact lowerCoord_add k (isDivisorSectionAt_extend g₁.property ⟨_, hxU⟩)
      (isDivisorSectionAt_extend g₂.property ⟨_, hxU⟩) (symm_ne_zero_of_notMem_affineOpen_one hx1)

private theorem sectionFun_smul {U : Opens (OnePoint ℂ)} (c : ℂ)
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    (x : ℙ ℂ (Fin 2 → ℂ)) (hxU : (equivProjectivization ℂ).symm x ∈ U) :
    sectionFun k (c • g) x = c * sectionFun k g x := by
  have he := Function.extend_smul c (Subtype.val : U → OnePoint ℂ) g.val 0
  rw [smul_zero] at he
  rw [sectionFun, sectionFun, Submodule.coe_smul, he]
  split_ifs with hx1
  · rw [Pi.smul_apply, smul_eq_mul]
    ring
  · exact lowerCoord_smul k (isDivisorSectionAt_extend g.property ⟨_, hxU⟩)
      (symm_ne_zero_of_notMem_affineOpen_one hx1) c

variable (k) in
/-- The component over `U` of the comparison morphism: the holomorphic section of `𝒪(k)` over the
inverse image of `U` attached to a section of `𝒪(k [∞])` over `U`. -/
private def compLinearMap (U : Opens (OnePoint ℂ)) :
    (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op U) →ₗ[ℂ]
      (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
        (op ((Opens.map projectiveLineToSphere).obj U)) where
  toFun g := holomorphicSectionSheaf.ofContMDiff
    (fun x ↦ sectionFun k (divisorSheafSectionsEquiv _ U g) x) (sectionFun_contMDiff _)
  map_add' g₁ g₂ := holomorphicSectionSheaf.ext fun x ↦ by
    rw [holomorphicSectionSheaf.add_apply]
    -- `erw`: `sectionFun` is `ℂ`-valued, while `ofContMDiff_apply` is stated for sections of the
    -- fibers `(twistCore k).Fiber x`, which are `ℂ` only after unfolding `Fiber`
    erw [holomorphicSectionSheaf.ofContMDiff_apply, holomorphicSectionSheaf.ofContMDiff_apply,
      holomorphicSectionSheaf.ofContMDiff_apply]
    rw [_root_.map_add]
    exact sectionFun_add _ _ x x.property
  map_smul' c g := holomorphicSectionSheaf.ext fun x ↦ by
    rw [holomorphicSectionSheaf.smul_apply]
    -- `erw`: as in `map_add'`, the fibers of `twistCore k` are `ℂ` only after unfolding
    erw [holomorphicSectionSheaf.ofContMDiff_apply, holomorphicSectionSheaf.ofContMDiff_apply]
    rw [_root_.map_smul]
    exact sectionFun_smul c _ x x.property

private theorem compLinearMap_apply {U : Opens (OnePoint ℂ)}
    (g : (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op U))
    (x : (Opens.map projectiveLineToSphere).obj U) :
    compLinearMap k U g x = sectionFun k (divisorSheafSectionsEquiv _ U g) x :=
  holomorphicSectionSheaf.ofContMDiff_apply _ _ x

/-- Restricting a section of `𝒪(k [∞])` does not change the attached section of `𝒪(k)`. -/
private theorem sectionFun_restrict {U V : Opens (OnePoint ℂ)} (h : V ≤ U)
    (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    (g' : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) V)
    (hg : g'.val = g.val ∘ Opens.inclusion h)
    (x : ℙ ℂ (Fin 2 → ℂ)) (hxV : (equivProjectivization ℂ).symm x ∈ V) :
    sectionFun k g' x = sectionFun k g x := by
  have heq : Subtype.val.extend g'.val 0 =ᶠ[𝓝 ((equivProjectivization ℂ).symm x)]
      Subtype.val.extend g.val 0 := by
    filter_upwards [V.isOpen.mem_nhds hxV] with z hz
    rw [Function.extend_val_apply (g := g'.val) hz, Function.extend_val_apply (g := g.val) (h hz),
      hg]
    rfl
  rw [sectionFun, sectionFun]
  split_ifs
  · rw [heq.self_of_nhds]
  · exact lowerCoord_congr k (heq.filter_mono nhdsWithin_le_nhds)

variable (k) in
/-- **The comparison morphism.** A section of the divisor sheaf `𝒪(k [∞])` over an open set `U` of
the Riemann sphere, read as the coordinate in the frame of the chart `1`, is a holomorphic section
of `𝒪(k)` over the corresponding open set of `ℂℙ¹`: this is a morphism from `𝒪(k [∞])` to the
pushforward of the sheaf of holomorphic sections of `𝒪(k)` along the identification of `ℂℙ¹`
with the Riemann sphere. It is an isomorphism (`Projectivization.isIso_twistCoreDivisorHom`). -/
def twistCoreDivisorHom : (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj ⟶
    (TopCat.Presheaf.pushforward (ModuleCat.{0} ℂ) projectiveLineToSphere).obj
      (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj where
  app U := ModuleCat.ofHom (compLinearMap k U.unop)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply holomorphicSectionSheaf.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply]
    rw [compLinearMap_apply, TopCat.Presheaf.pushforward_obj_map, holomorphicSectionSheaf.map_apply,
      compLinearMap_apply]
    exact sectionFun_restrict i.unop.le _ _ (divisorSheafSectionsEquiv_map _ i.unop g) x x.property

/-- The component of `Projectivization.twistCoreDivisorHom` at `U` is `compLinearMap k U`. -/
private theorem twistCoreDivisorHom_app_apply {U : Opens (OnePoint ℂ)}
    (g : (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op U)) :
    (twistCoreDivisorHom k).app (op U) g = compLinearMap k U g :=
  rfl

/-- On `U₁`, the section of `𝒪(k)` attached by `Projectivization.twistCoreDivisorHom` to a section
`g` of `𝒪(k [∞])` is `g` read in the frame of the chart `1`: its value is `g` at the corresponding
point of the Riemann sphere, multiplied by the transition from the chart `1` to the preferred
chart. -/
theorem twistCoreDivisorHom_app_apply_of_mem_affineOpen_one {U : Opens (OnePoint ℂ)}
    (g : (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op U))
    {x : ℙ ℂ (Fin 2 → ℂ)} (hxU : x ∈ (Opens.map projectiveLineToSphere).obj U)
    (hx : x ∈ affineOpen 1) :
    holomorphicSectionSheaf.toFun 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber
        ((twistCoreDivisorHom k).app (op U) g) ⟨x, hxU⟩ =
      twistTransition k 1 ((twistCore (𝕜 := ℂ) (n := 1) k).indexAt x) x *
        (divisorSheafSectionsEquiv _ U g).val
          ⟨(equivProjectivization ℂ).symm x, mem_map_projectiveLineToSphere.1 hxU⟩ := by
  rw [twistCoreDivisorHom_app_apply, compLinearMap_apply, sectionFun, ite_eq_left hx,
    Function.extend_val_apply (mem_map_projectiveLineToSphere.1 hxU)]

private theorem compLinearMap_injective (U : Opens (OnePoint ℂ)) :
    Function.Injective (compLinearMap k U) := by
  refine (injective_iff_map_eq_zero _).2 fun g hg ↦ ?_
  set g' := divisorSheafSectionsEquiv _ U g with hg'
  have hfin : ∀ y ∈ U, y ≠ (∞ : OnePoint ℂ) → Subtype.val.extend g'.val 0 y = 0 := by
    intro y hy hyi
    have hx1 : equivProjectivization ℂ y ∈ affineOpen 1 :=
      (equivProjectivization_mem_affineOpen_one_iff y).2 hyi
    have hxU : equivProjectivization ℂ y ∈ (Opens.map projectiveLineToSphere).obj U := by
      rw [mem_map_projectiveLineToSphere, Equiv.symm_apply_apply]
      exact hy
    have h0 : sectionFun k g' (equivProjectivization ℂ y) = 0 := by
      have h : compLinearMap k U g ⟨_, hxU⟩ =
          (0 : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ
            (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
              (op ((Opens.map projectiveLineToSphere).obj U))) ⟨_, hxU⟩ := by
        rw [hg]
      rwa [compLinearMap_apply, holomorphicSectionSheaf.zero_apply] at h
    have h := coord_one_sectionFun g' hx1
    rw [coord, h0, mul_zero, Equiv.symm_apply_apply] at h
    exact h.symm
  apply (divisorSheafSectionsEquiv _ U).injective
  rw [map_zero]
  apply Subtype.ext
  funext ⟨y, hy⟩
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
  rw [← hg', ← Function.extend_val_apply (g := g'.val) (j := 0) hy]
  by_cases hyi : y = (∞ : OnePoint ℂ)
  · subst hyi
    by_cases hk : 0 < k
    · rw [Function.extend_val_apply (g := g'.val) hy]
      exact apply_eq_zero_of_mem_divisorSections g'.property
        (by rw [zsmul_ofPoint_apply_infty]; exact hk)
    · have hc := ((isDivisorSectionAt_extend g'.property ⟨_, hy⟩).contMDiffAt
        (by rw [zsmul_ofPoint_apply_infty]; omega)).continuousAt
      refine ContinuousAt.eq_of_eventuallyEq_nhdsNE hc (continuousAt_const (y := (0 : ℂ))) ?_
      filter_upwards [eventually_ne_infty_and_ne_zero,
        nhdsWithin_le_nhds (U.isOpen.mem_nhds hy)] with z hz hzU
      exact hfin z hzU hz.1
  · exact hfin y hy hyi

/-! ### Surjectivity -/

section Surjective

variable {U : Opens (OnePoint ℂ)} {t : ℙ ℂ (Fin 2 → ℂ) → ℂ}

/-- The two coordinates of a holomorphic section of `𝒪(k)` over the inverse image of `U`, read on
the Riemann sphere, are holomorphic where they are defined. -/
private theorem contMDiffAt_coord_comp
    (hs : ∀ j, ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (coord k j t)
      ((Opens.map projectiveLineToSphere).obj U ∩ affineOpen j))
    (j : Fin 2) {y : OnePoint ℂ} (hy : y ∈ U) (hj : equivProjectivization ℂ y ∈ affineOpen j) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coord k j t ∘ equivProjectivization ℂ) y := by
  have hmem : equivProjectivization ℂ y ∈
      ((Opens.map projectiveLineToSphere).obj U : Set (ℙ ℂ (Fin 2 → ℂ))) ∩ affineOpen j :=
    ⟨SetLike.mem_coe.2 (mem_map_projectiveLineToSphere.2 (by rwa [Equiv.symm_apply_apply])), hj⟩
  exact ((hs j _ hmem).contMDiffAt ((((Opens.map projectiveLineToSphere).obj U).isOpen.inter
    (isOpen_affineOpen j)).mem_nhds hmem)).comp y contMDiff_equivProjectivization.contMDiffAt

/-- At a finite nonzero point, the coordinate of a section in the frame of the chart `1` is the
coordinate in the frame of the chart `0` times the `(-k)`-th power of the inverted coordinate. -/
private theorem coord_one_equivProjectivization (t : ℙ ℂ (Fin 2 → ℂ) → ℂ) {y : OnePoint ℂ}
    (hyi : y ≠ (∞ : OnePoint ℂ)) (hy0 : y ≠ ((0 : ℂ) : OnePoint ℂ)) :
    coord k 1 t (equivProjectivization ℂ y) =
      invChart y ^ (-k) * coord k 0 t (equivProjectivization ℂ y) := by
  have h0 := (equivProjectivization_mem_affineOpen_zero_iff y).2 hy0
  rw [coord, coord, ← twistTransition_mul_twistTransition k _ 1 h0,
    twistTransition_zero_one_equivProjectivization k y hyi, mul_assoc]

/-- The coordinate in the frame of the chart `1` of a holomorphic section of `𝒪(k)`, read on the
Riemann sphere and normalized, is a section of `𝒪(k [∞])`. -/
private theorem isDivisorSectionAt_coord_one
    (hs : ∀ j, ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (coord k j t)
      ((Opens.map projectiveLineToSphere).obj U ∩ affineOpen j))
    {y : OnePoint ℂ} (hy : y ∈ U) :
    IsDivisorSectionAt (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
      (toDivisorSection (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
        (coord k 1 t ∘ equivProjectivization ℂ)) y := by
  induction y using OnePoint.rec with
  | infty =>
    have h0 := (isDivisorSectionAt_iff_of_eq_zero (D := (0 : WeilDivisor (OnePoint ℂ)))
      (by simp)).2 (contMDiffAt_coord_comp hs 0 hy
        ((equivProjectivization_mem_affineOpen_zero_iff _).2 (infty_ne_coe 0)))
    have hm := (meromorphicAt_invChart_zpow (infty_ne_coe 0) (-k)).mul h0.meromorphicAt
    have hev : coord k 1 t ∘ equivProjectivization ℂ =ᶠ[𝓝[≠] (∞ : OnePoint ℂ)]
        (fun z ↦ invChart z ^ (-k)) * (coord k 0 t ∘ equivProjectivization ℂ) := by
      filter_upwards [eventually_ne_infty_and_ne_zero] with z hz
      exact coord_one_equivProjectivization t hz.1 hz.2
    refine isDivisorSectionAt_toDivisorSection (hm.congr hev.symm) ?_
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_mul
      (meromorphicAt_invChart_zpow (infty_ne_coe 0) (-k)) h0.meromorphicAt,
      meromorphicOrderAt_invChart_zpow_infty, zsmul_ofPoint_apply_infty]
    have h0' := h0.neg_le_meromorphicOrderAt
    simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero, WithTop.coe_zero] at h0'
    calc ((-k : ℤ) : WithTop ℤ) = ((-k : ℤ) : WithTop ℤ) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add_right h0' _
  | coe z =>
    have h := (isDivisorSectionAt_iff_of_eq_zero (D := (0 : WeilDivisor (OnePoint ℂ)))
      (by simp)).2 (contMDiffAt_coord_comp hs 1 hy
        ((equivProjectivization_mem_affineOpen_one_iff _).2 (coe_ne_infty z)))
    refine isDivisorSectionAt_toDivisorSection h.meromorphicAt ?_
    rw [zsmul_ofPoint_apply_of_ne k (coe_ne_infty z)]
    simpa using h.neg_le_meromorphicOrderAt

/-- At a finite point, the normalized coordinate in the frame of the chart `1` is that
coordinate. -/
private theorem toDivisorSection_coord_one_apply
    (hs : ∀ j, ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (coord k j t)
      ((Opens.map projectiveLineToSphere).obj U ∩ affineOpen j))
    {y : OnePoint ℂ} (hy : y ∈ U) (hyi : y ≠ (∞ : OnePoint ℂ)) :
    toDivisorSection (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
      (coord k 1 t ∘ equivProjectivization ℂ) y = coord k 1 t (equivProjectivization ℂ y) := by
  rw [toDivisorSection_apply, zsmul_ofPoint_apply_of_ne k hyi]
  simp only [le_refl, ↓reduceIte]
  rw [sphereMap_of_continuousAt (contMDiffAt_coord_comp hs 1 hy
    ((equivProjectivization_mem_affineOpen_one_iff y).2 hyi)).continuousAt, affineChart_coe]
  rfl

/-- At `∞`, the coordinate at infinity of the normalized coordinate in the frame of the chart `1`
is the coordinate in the frame of the chart `0`. -/
private theorem lowerCoord_coord_one_infty
    (hs : ∀ j, ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (coord k j t)
      ((Opens.map projectiveLineToSphere).obj U ∩ affineOpen j))
    (hUi : (∞ : OnePoint ℂ) ∈ U) (g : divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U)
    (hg : ∀ y ∈ U, Subtype.val.extend g.val 0 y = toDivisorSection
      (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) (coord k 1 t ∘ equivProjectivization ℂ) y) :
    lowerCoord k (Subtype.val.extend g.val 0) (∞ : OnePoint ℂ) =
      coord k 0 t (equivProjectivization ℂ (∞ : OnePoint ℂ)) := by
  have hdiv := isDivisorSectionAt_extend g.property ⟨_, hUi⟩
  refine ContinuousAt.eq_of_eventuallyEq_nhdsNE
    (contMDiffAt_lowerCoord k hdiv (infty_ne_coe 0)).continuousAt
    (contMDiffAt_coord_comp hs 0 hUi ((equivProjectivization_mem_affineOpen_zero_iff _).2
      (infty_ne_coe 0))).continuousAt ?_
  filter_upwards [lowerCoord_eventuallyEq k hdiv (infty_ne_coe 0),
    eventually_ne_infty_and_ne_zero, nhdsWithin_le_nhds (U.isOpen.mem_nhds hUi)]
    with z hz hz' hzU
  rw [hz, hg z hzU, toDivisorSection_coord_one_apply hs hzU hz'.1,
    coord_one_equivProjectivization t hz'.1 hz'.2, ← mul_assoc,
    ← zpow_add₀ (invChart_ne_zero hz'.1 hz'.2), add_neg_cancel, zpow_zero, one_mul]
  rfl

/-- The coordinates of a holomorphic section `s` of `𝒪(k)` over the inverse image of `U` are
holomorphic on the standard charts. -/
private theorem contMDiffOn_coord_extend
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
      (op ((Opens.map projectiveLineToSphere).obj U))) (j : Fin 2) :
    ContMDiffOn 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω
      (coord k j (Subtype.val.extend
        (fun x : (Opens.map projectiveLineToSphere).obj U ↦ (s x : ℂ)) 0))
      ((Opens.map projectiveLineToSphere).obj U ∩ affineOpen j) :=
  (contMDiff_mk_iff k (fun x : (Opens.map projectiveLineToSphere).obj U ↦ s x)).1
    (holomorphicSectionSheaf.contMDiff s) j

variable (k) in
/-- The section of `𝒪(k [∞])` attached to a holomorphic section `s` of `𝒪(k)` over the inverse
image of `U`: the coordinate of `s` in the frame of the chart `1`, read on the Riemann sphere and
normalized. -/
private def divisorSectionOf
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
      (op ((Opens.map projectiveLineToSphere).obj U))) :
    divisorSections (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) U :=
  ⟨toDivisorSection (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
      (coord k 1 (Subtype.val.extend
        (fun x : (Opens.map projectiveLineToSphere).obj U ↦ (s x : ℂ)) 0) ∘
          equivProjectivization ℂ) ∘ Subtype.val,
    comp_val_mem_divisorSections fun _ hy ↦
      isDivisorSectionAt_coord_one (contMDiffOn_coord_extend s) hy⟩

private theorem divisorSectionOf_val_apply
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
      (op ((Opens.map projectiveLineToSphere).obj U))) (y : U) :
    (divisorSectionOf k s).val y = toDivisorSection (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
      (coord k 1 (Subtype.val.extend
        (fun x : (Opens.map projectiveLineToSphere).obj U ↦ (s x : ℂ)) 0) ∘
          equivProjectivization ℂ) y :=
  rfl

/-- The section of `𝒪(k [∞])` attached to `s` is sent back to `s`. -/
private theorem compLinearMap_symm_divisorSectionOf
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
      (op ((Opens.map projectiveLineToSphere).obj U))) :
    compLinearMap k U ((divisorSheafSectionsEquiv _ U).symm (divisorSectionOf k s)) = s := by
  set t : ℙ ℂ (Fin 2 → ℂ) → ℂ := Subtype.val.extend
    (fun x : (Opens.map projectiveLineToSphere).obj U ↦ (s x : ℂ)) 0
  have hs := contMDiffOn_coord_extend s
  have htx : ∀ x : (Opens.map projectiveLineToSphere).obj U, t x = s x := fun x ↦
    Function.extend_val_apply x.property
  set g := divisorSectionOf k s
  have hext : ∀ y ∈ U, Subtype.val.extend g.val 0 y = toDivisorSection
      (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) (coord k 1 t ∘ equivProjectivization ℂ) y :=
    fun y hy ↦ Function.extend_val_apply hy
  refine holomorphicSectionSheaf.ext fun x ↦ ?_
  rw [compLinearMap_apply, LinearEquiv.apply_symm_apply, sectionFun]
  have hyU : (equivProjectivization ℂ).symm x ∈ U := x.property
  have hxy : equivProjectivization ℂ ((equivProjectivization ℂ).symm x) = x :=
    Equiv.apply_symm_apply _ _
  split_ifs with hx1
  · have hyi : (equivProjectivization ℂ).symm x ≠ (∞ : OnePoint ℂ) := by
      rw [← equivProjectivization_mem_affineOpen_one_iff, hxy]
      exact hx1
    rw [hext _ hyU, toDivisorSection_coord_one_apply hs hyU hyi, hxy, coord, ← mul_assoc,
      twistTransition_mul_twistTransition k _ _ hx1,
      twistTransition_self k (mem_affineOpen_twistCore_indexAt k (x : ℙ ℂ (Fin 2 → ℂ))), one_mul]
    exact htx x
  · have hyi := (equivProjectivization_symm_eq_infty_iff _).2 hx1
    have hxi : equivProjectivization ℂ (∞ : OnePoint ℂ) = x := by
      rw [← hyi]
      exact hxy
    have hx0 : (x : ℙ ℂ (Fin 2 → ℂ)) ∈ affineOpen 0 := by
      rw [← hxi]
      exact (equivProjectivization_mem_affineOpen_zero_iff _).2 (infty_ne_coe 0)
    rw [hyi, lowerCoord_coord_one_infty hs (hyi ▸ hyU) g hext, hxi, coord,
      indexAt_twistCore_eq_zero_of_notMem k hx1, twistTransition_self k hx0, one_mul]
    exact htx x

private theorem compLinearMap_surjective (U : Opens (OnePoint ℂ)) :
    Function.Surjective (compLinearMap k U) :=
  fun s ↦ ⟨_, compLinearMap_symm_divisorSectionOf s⟩

end Surjective

/-- The comparison morphism `Projectivization.twistCoreDivisorHom k` is an isomorphism: the sheaf
of holomorphic sections of `𝒪(k)` on `ℂℙ¹` is the divisor sheaf `𝒪(k [∞])` of the Riemann
sphere, transported along the identification of the two. -/
instance isIso_twistCoreDivisorHom : IsIso (twistCoreDivisorHom k) := by
  have : ∀ U, IsIso ((twistCoreDivisorHom k).app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨compLinearMap_injective U.unop, compLinearMap_surjective U.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- On `U₀`, the coordinate in the frame of the chart `0` of the section of `𝒪(k)` attached by
`Projectivization.twistCoreDivisorHom` to a section `g` of `𝒪(k [∞])` is `t⁻ᵏ g(t)` read on the
Riemann sphere, with its removable singularity at `∞` filled by
`TauCeti.RiemannSurface.toDivisorSection`. -/
theorem twistTransition_smul_twistCoreDivisorHom_app_apply_of_mem_affineOpen_zero
    {U : Opens (OnePoint ℂ)}
    (g : (divisorSheaf (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op U))
    {x : ℙ ℂ (Fin 2 → ℂ)} (hxU : x ∈ (Opens.map projectiveLineToSphere).obj U)
    (hx : x ∈ affineOpen 0) :
    twistTransition k ((twistCore (𝕜 := ℂ) (n := 1) k).indexAt x) 0 x •
        holomorphicSectionSheaf.toFun 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber
          ((twistCoreDivisorHom k).app (op U) g) ⟨x, hxU⟩ =
      toDivisorSection 0
        (fun y ↦ invChart y ^ k * Subtype.val.extend (divisorSheafSectionsEquiv _ U g).val 0 y)
        ((equivProjectivization ℂ).symm x) := by
  have h := coord_zero_sectionFun (divisorSheafSectionsEquiv _ U g) hx hxU
  rw [coord] at h
  rw [twistCoreDivisorHom_app_apply, compLinearMap_apply]
  -- the fiber `(twistCore k).Fiber x` is `ℂ`, on which the scalar action of `ℂ` is multiplication
  exact h

/-- The inverse of `Projectivization.twistCoreDivisorHom` reads a holomorphic section `s` of `𝒪(k)`
in the frame of the chart `1`: the section of `𝒪(k [∞])` it gives is the coordinate of `s` in
that frame, read on the Riemann sphere, with its removable singularities filled by
`TauCeti.RiemannSurface.toDivisorSection`. -/
theorem inv_twistCoreDivisorHom_app_apply {U : Opens (OnePoint ℂ)}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := 1) k).Fiber).obj.obj
      (op ((Opens.map projectiveLineToSphere).obj U))) (y : U) :
    (divisorSheafSectionsEquiv _ U ((inv (twistCoreDivisorHom k)).app (op U) s)).val y =
      toDivisorSection (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ))
        (fun z ↦ twistTransition k
          ((twistCore (𝕜 := ℂ) (n := 1) k).indexAt (equivProjectivization ℂ z)) 1
            (equivProjectivization ℂ z) *
          Subtype.val.extend (fun x : (Opens.map projectiveLineToSphere).obj U ↦
            (holomorphicSectionSheaf.toFun 𝓘(ℂ, Fin 1 → ℂ) ℂ
              (twistCore (𝕜 := ℂ) (n := 1) k).Fiber s x : ℂ)) 0 (equivProjectivization ℂ z)) y := by
  have h : (inv (twistCoreDivisorHom k)).app (op U) s =
      (divisorSheafSectionsEquiv _ U).symm (divisorSectionOf k s) := by
    conv_lhs => rw [← compLinearMap_symm_divisorSectionOf s, ← twistCoreDivisorHom_app_apply]
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app,
      ConcreteCategory.id_apply]
  rw [h, LinearEquiv.apply_symm_apply, divisorSectionOf_val_apply]
  simp only [coord, Function.comp_def]

variable (k) in
/-- **`H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`.** The first Čech cohomology of the sheaf of holomorphic
sections of the line bundle `𝒪(k)` on the complex projective line vanishes for `k ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le (hk : -1 ≤ k) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := 1) k).Fiber 1) := by
  have hdeg : -1 ≤ WeilDivisor.degree (k • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) := by
    rw [map_zsmul, WeilDivisor.degree_ofPoint, smul_eq_mul, mul_one]
    exact hk
  have hind : Topology.IsInducing (equivProjectivization ℂ).symm := by
    simpa [Diffeomorph.coe_toHomeomorph] using
      (diffeomorphProjectivization ℂ ω).symm.toHomeomorph.isInducing
  -- a local instance: the global one is indexed at the presheaf category of the comparison
  -- morphism, which instance search does not match against the lemma's statement
  have : IsIso (twistCoreDivisorHom k) := isIso_twistCoreDivisorHom
  have := TopCat.Hom.epi_cechCohomologyPullback projectiveLineToSphere 1 (twistCoreDivisorHom k)
    hind (equivProjectivization ℂ).symm.surjective
  exact (isZero_divisorCechCohomology_one_sphere_of_neg_one_le_degree hdeg).of_epi
    (TopCat.Hom.cechCohomologyPullback projectiveLineToSphere 1 (twistCoreDivisorHom k))

/-! ### Split bundles -/

section Sum

variable {n : ℕ} {κ : Type} [Fintype κ] (k : κ → ℤ)

/-- The projection of the sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` onto the sheaf of
holomorphic sections of its summand `𝒪(k l)`, taking a section to its component `l`. -/
def twistSumSectionProj (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.proj (R := ℂ) (φ := fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_apply k l)

/-- The projection onto the summand `l` takes the value `v` of a section at a point to its
component `v l`. -/
@[simp]
theorem twistSumSectionProj_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber).obj.obj U) (x : ↥(unop U)) :
    (twistSumSectionProj k l).hom.app U s x = (s x : κ → ℂ) l :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

variable [DecidableEq κ]

/-- The inclusion of the sheaf of holomorphic sections of the summand `𝒪(k l)` into the sheaf of
holomorphic sections of `⨁ₗ 𝒪(k l)`, placing a section in the summand `l`. -/
def twistSumSectionSingle (l : κ) :
    holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber ⟶
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber :=
  holomorphicSectionSheaf.homOfLinearMap (fun _ ↦ LinearMap.single ℂ (fun _ : κ ↦ ℂ) l)
    (contMDiff_twistSumCore_single k l)

/-- The inclusion of the summand `l` takes the value `c` of a section at a point to the vector
`Pi.single l c`. -/
@[simp]
theorem twistSumSectionSingle_app_apply (l : κ)
    {U : (Opens (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber).obj.obj U) (x : ↥(unop U)) :
    ((twistSumSectionSingle k l).hom.app U s x : κ → ℂ) = Pi.single l (s x : ℂ) :=
  holomorphicSectionSheaf.homOfLinearMap_app_apply _ _ s x

@[reassoc (attr := simp)]
theorem twistSumSectionSingle_twistSumSectionProj (l : κ) :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l = 𝟙 _ := by
  refine holomorphicSectionSheaf.hom_ext fun U s x ↦ ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply, twistSumSectionProj_app_apply, twistSumSectionSingle_app_apply]
  exact Pi.single_eq_same (M := fun _ : κ ↦ ℂ) _ _

@[reassoc (attr := simp)]
theorem twistSumSectionSingle_twistSumSectionProj_of_ne {l l' : κ} (h : l ≠ l') :
    twistSumSectionSingle (n := n) k l ≫ twistSumSectionProj k l' = 0 := by
  refine holomorphicSectionSheaf.hom_ext fun U s x ↦ ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply, twistSumSectionProj_app_apply, twistSumSectionSingle_app_apply]
  -- `simp` evaluates the zero morphism to the zero of the fibre `(twistCore (k l')).Fiber x`,
  -- which is the zero of `ℂ` by definition
  exact (Pi.single_eq_of_ne' (M := fun _ : κ ↦ ℂ) h _).trans (by simp; rfl)

/-- The projections onto and inclusions of the summands of `⨁ₗ 𝒪(k l)` add up to the identity of
its sheaf of holomorphic sections. -/
theorem sum_twistSumSectionProj_twistSumSectionSingle :
    ∑ l, twistSumSectionProj (n := n) k l ≫ twistSumSectionSingle k l = 𝟙 _ := by
  refine holomorphicSectionSheaf.hom_ext fun U s x ↦ ?_
  rw [holomorphicSectionSheaf.sum_hom_app_apply]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply, twistSumSectionProj_app_apply, twistSumSectionSingle_app_apply]
  exact Finset.univ_sum_single (s x : κ → ℂ)

variable (n) in
/-- The sheaf of holomorphic sections of `⨁ₗ 𝒪(k l)` on `ℂℙⁿ`, with the projections onto and the
inclusions of the sheaves of holomorphic sections of the summands `𝒪(k l)`, as a bicone. -/
-- Exposed so that the cone point is visibly the sheaf of the split bundle, as for
-- `TauCeti.holomorphicSectionSheaf.prodBicone`.
@[expose, simps]
def twistSumSectionBicone :
    Bicone (fun l ↦
      holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) ℂ (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber) where
  pt := holomorphicSectionSheaf 𝓘(ℂ, Fin n → ℂ) (κ → ℂ) (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber
  «π» := twistSumSectionProj k
  ι := twistSumSectionSingle k
  ι_π l l' := by
    split_ifs with h
    · subst h
      exact twistSumSectionSingle_twistSumSectionProj k l
    · exact twistSumSectionSingle_twistSumSectionProj_of_ne k h

variable (n) in
/-- **The sheaf of sections of a split bundle is a biproduct.** The sheaf of holomorphic sections
of `⨁ₗ 𝒪(k l)` on `ℂℙⁿ` is the biproduct of the sheaves of holomorphic sections of the summands
`𝒪(k l)`. -/
def twistSumSectionBiconeIsBilimit : (twistSumSectionBicone n k).IsBilimit :=
  isBilimitOfTotal _ (sum_twistSumSectionProj_twistSumSectionSingle (n := n) k)

omit [DecidableEq κ] in
/-- **The cohomology of a split bundle vanishes when that of each summand does.** If the Čech
cohomology `Hⁱ(ℂℙⁿ, 𝒪(k l))` vanishes for every `l`, then so does `Hⁱ(ℂℙⁿ, ⨁ₗ 𝒪(k l))`. -/
theorem isZero_holomorphicSectionCechCohomology_twistSumCore {i : ℕ}
    (h : ∀ l, IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (k l)).Fiber i)) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin n → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := n) k).Fiber i) := by
  classical
  -- Čech cohomology of the underlying presheaf is an additive functor, so it preserves the
  -- biproduct `twistSumSectionBicone`, a limit of the zero objects `Hⁱ(ℂℙⁿ, 𝒪(k l))`.
  exact (isBilimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology _) _ ⋙
    Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) (ModuleCat.{0} ℂ) i)
    (twistSumSectionBiconeIsBilimit n k)).isLimit.isZero_pt (Functor.isZero _ fun l ↦ h l.as)

end Sum

/-- **`H¹(ℂℙ¹, ⨁ₗ 𝒪(k l)) = 0` for `k l ≥ -1`.** The first Čech cohomology of the sheaf of
holomorphic sections of a split bundle `⨁ₗ 𝒪(k l)` on the complex projective line vanishes when
every `k l ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    {κ : Type} [Fintype κ] {k : κ → ℤ} (hk : ∀ l, -1 ≤ k l) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (κ → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := 1) k).Fiber 1) :=
  isZero_holomorphicSectionCechCohomology_twistSumCore k fun l ↦
    isZero_holomorphicSectionCechCohomology_one_twistCore_of_neg_one_le (k l) (hk l)

end Projectivization
