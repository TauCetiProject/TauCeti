/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Scalar

/-!
# The line bundles `𝒪(k)` on the projective line

For an integer `k`, the line bundle `𝒪(k)` on the projective line `OnePoint 𝕜` is glued from the
trivial lines over the two charts of `OnePoint 𝕜` along the transition function `z ↦ z⁻ᵏ` on the
overlap. It is the Mathlib vector-bundle core `OnePoint.twistCore k`, with model fibre `𝕜` and
charts indexed by the points of `OnePoint 𝕜`, the chart at `x` being the base set of the
preferred manifold chart at `x`. It is an analytic vector bundle
(`OnePoint.isContMDiff_twistCore`); for `𝕜 = ℂ` it is a holomorphic line bundle on the Riemann
sphere.

## Conventions

A section `s` of `𝒪(k)` is a function `OnePoint 𝕜 → 𝕜`. At a finite point `z` its value is its
coordinate in the affine frame, and at `∞` its coordinate in the inverted frame. At a finite
point `z ≠ 0` the two coordinates are related by `s_∞ = z⁻ᵏ s_aff`. So a section is
`s_aff(z) = f(z)` in the affine coordinate and `s_∞(w) = wᵏ f(w⁻¹)` in the inverted
coordinate `w = z⁻¹`, and the polynomials of degree at most `k` are sections. With this convention
the tangent bundle of the projective line is `𝒪(2)`, the canonical bundle is `𝒪(-2)`, and the
section `z` of `𝒪(1)` vanishes exactly once, at `0` (`OnePoint.contMDiff_identitySection` and
`OnePoint.identitySection_eq_zero_iff`).

## Main declarations

* `OnePoint.twistTransition k x y p`: the scalar transition function of `𝒪(k)` from the chart
  at `x` to the chart at `y`, evaluated at `p`.
* `OnePoint.twistCore k`: the vector-bundle core of `𝒪(k)`.
* `OnePoint.isContMDiff_twistCore`: `𝒪(k)` is an analytic line bundle.
* `OnePoint.twistTransition_add` and `OnePoint.twistTransition_neg`: the transitions of
  `𝒪(k + l)` and `𝒪(-k)` are the products and the inverses of those of `𝒪(k)` and `𝒪(l)`.
* `OnePoint.twistTransition_zero`: `𝒪(0)` has trivial transitions.
* `OnePoint.contMDiff_section_twistCore_iff`: a section of `𝒪(k)` is `C^n` exactly when its
  affine coordinate is `C^n` off `∞` and its inverted coordinate is `C^n` off `0`.
* `OnePoint.monomialSection k j`: the section `zʲ` of `𝒪(k)` for `j ≤ k`, which is analytic
  (`OnePoint.contMDiff_monomialSection`).
* `OnePoint.identitySection`: the section `z` of `𝒪(1)`, analytic with a single zero, at `0`.
* `OnePoint.monomialSection_zero_zero_ne_zero`: the section `1` of `𝒪(0)` vanishes nowhere.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §29.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace OnePoint

variable {𝕜 : Type*}

/-- The frame weight of a chart index: `1` for the inverted chart, preferred at `∞`, and `0` for
the affine chart, preferred at the finite points. -/
def twistIndex (x : OnePoint 𝕜) : ℤ :=
  x.elim 1 fun _ ↦ 0

@[simp]
theorem twistIndex_infty : twistIndex (∞ : OnePoint 𝕜) = 1 :=
  (rfl)

@[simp]
theorem twistIndex_coe (z : 𝕜) : twistIndex (z : OnePoint 𝕜) = 0 :=
  (rfl)

variable [NontriviallyNormedField 𝕜]

/-- The scalar transition function of `𝒪(k)` from the chart at `x` to the chart at `y`, at the
point `p`: it is `z⁻ᵏ` from the affine chart to the inverted chart at the finite point `z`, its
inverse in the other direction, and `1` between charts of the same kind. -/
def twistTransition (k : ℤ) (x y p : OnePoint 𝕜) : 𝕜 :=
  affineChart p ^ (k * (twistIndex x - twistIndex y))

/-- The defining formula of the transition of `𝒪(k)`, through the frame weights. -/
theorem twistTransition_def (k : ℤ) (x y p : OnePoint 𝕜) :
    twistTransition k x y p = affineChart p ^ (k * (twistIndex x - twistIndex y)) :=
  (rfl)

/-- Between two affine charts the transition of `𝒪(k)` is `1`. -/
@[simp]
theorem twistTransition_coe_coe (k : ℤ) (z w : 𝕜) (p : OnePoint 𝕜) :
    twistTransition k (z : OnePoint 𝕜) (w : OnePoint 𝕜) p = 1 := by
  simp [twistTransition]

/-- From the affine chart to the inverted chart the transition of `𝒪(k)` is `z⁻ᵏ`. -/
@[simp]
theorem twistTransition_coe_infty (k : ℤ) (z : 𝕜) (p : OnePoint 𝕜) :
    twistTransition k (z : OnePoint 𝕜) (∞ : OnePoint 𝕜) p = affineChart p ^ (-k) := by
  simp [twistTransition]

/-- From the inverted chart to the affine chart the transition of `𝒪(k)` is `zᵏ`. -/
@[simp]
theorem twistTransition_infty_coe (k : ℤ) (z : 𝕜) (p : OnePoint 𝕜) :
    twistTransition k (∞ : OnePoint 𝕜) (z : OnePoint 𝕜) p = affineChart p ^ k := by
  simp [twistTransition]

@[simp]
theorem twistTransition_self (k : ℤ) (x p : OnePoint 𝕜) : twistTransition k x x p = 1 := by
  simp [twistTransition]

/-- `𝒪(0)` has trivial transition functions. -/
@[simp]
theorem twistTransition_zero (x y p : OnePoint 𝕜) : twistTransition 0 x y p = 1 := by
  simp [twistTransition]

/-- The transition of `𝒪(-k)` is the inverse of the transition of `𝒪(k)`. -/
theorem twistTransition_neg (k : ℤ) (x y p : OnePoint 𝕜) :
    twistTransition (-k) x y p = (twistTransition k x y p)⁻¹ := by
  simp [twistTransition, neg_mul, zpow_neg]

variable [ProperSpace 𝕜]

/-- If the affine coordinate of `p` vanishes, that is `p = 0` or `p = ∞`, then every chart whose
domain contains `p` has the same frame weight as the preferred chart at `p`. -/
theorem twistIndex_eq_of_affineChart_eq_zero {x p : OnePoint 𝕜}
    (hp : p ∈ (chartAt 𝕜 x).source) (h0 : affineChart p = 0) :
    twistIndex x = twistIndex p := by
  induction x using OnePoint.rec with
  | infty =>
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z =>
      simp only [affineChart_coe] at h0
      subst h0
      simp at hp
  | coe z =>
    induction p using OnePoint.rec with
    | infty => simp at hp
    | coe w => rfl

/-- The transition of `𝒪(k + l)` is the product of the transitions of `𝒪(k)` and `𝒪(l)`, on the
overlap of the two charts. -/
theorem twistTransition_add (k l : ℤ) {x y p : OnePoint 𝕜} (hx : p ∈ (chartAt 𝕜 x).source)
    (hy : p ∈ (chartAt 𝕜 y).source) :
    twistTransition (k + l) x y p = twistTransition k x y p * twistTransition l x y p := by
  by_cases h0 : affineChart p = 0
  · simp [twistTransition, twistIndex_eq_of_affineChart_eq_zero hx h0,
      twistIndex_eq_of_affineChart_eq_zero hy h0]
  · simp only [twistTransition]
    rw [← zpow_add₀ h0]
    ring_nf

/-- The transition functions of `𝒪(k)` satisfy the cocycle identity on triple overlaps. -/
theorem twistTransition_mul_twistTransition (k : ℤ) {x y z p : OnePoint 𝕜}
    (hx : p ∈ (chartAt 𝕜 x).source) (hy : p ∈ (chartAt 𝕜 y).source)
    (hz : p ∈ (chartAt 𝕜 z).source) :
    twistTransition k y z p * twistTransition k x y p = twistTransition k x z p := by
  by_cases h0 : affineChart p = 0
  · simp [twistTransition, twistIndex_eq_of_affineChart_eq_zero hx h0,
      twistIndex_eq_of_affineChart_eq_zero hy h0, twistIndex_eq_of_affineChart_eq_zero hz h0]
  · simp only [twistTransition]
    rw [← zpow_add₀ h0]
    ring_nf

/-- The transition functions of `𝒪(k)` are analytic on the chart overlaps. -/
theorem contMDiffOn_twistTransition (k : ℤ) (x y : OnePoint 𝕜) :
    ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) ω (twistTransition k x y)
      ((chartAt 𝕜 x).source ∩ (chartAt 𝕜 y).source) := by
  intro p ⟨hx, hy⟩
  by_cases h0 : affineChart p = 0
  · -- Near a chart overlap point with vanishing affine coordinate the two charts have the same
    -- frame weight, so the transition is constantly `1`.
    have hxy : twistIndex x = twistIndex y := by
      rw [twistIndex_eq_of_affineChart_eq_zero hx h0, twistIndex_eq_of_affineChart_eq_zero hy h0]
    exact (contMDiffWithinAt_const (c := (1 : 𝕜))).congr (fun q _ ↦ by simp [twistTransition, hxy])
      (by simp [twistTransition, hxy])
  · have hp : p ≠ (∞ : OnePoint 𝕜) := by rintro rfl; exact h0 affineChart_infty
    have hchart : ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) ω (affineChart : OnePoint 𝕜 → 𝕜) p :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Or.inl rfl))
        (by simpa using hp)
    have hpow : ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) ω
        (fun u : 𝕜 ↦ u ^ (k * (twistIndex x - twistIndex y))) (affineChart p) :=
      (((analyticAt_id).zpow h0).contDiffAt).contMDiffAt
    exact (hpow.comp p hchart).contMDiffWithinAt

/-- The line bundle `𝒪(k)` on the projective line `OnePoint 𝕜`, as a Mathlib vector-bundle core
with model fibre `𝕜`. Its charts are indexed by the points of `OnePoint 𝕜`; the chart at `x` is
trivial over the domain of the preferred manifold chart at `x`, and the coordinate change from
the chart at `x` to the chart at `y` is multiplication by `twistTransition k x y`. -/
def twistCore (k : ℤ) : VectorBundleCore 𝕜 (OnePoint 𝕜) 𝕜 (OnePoint 𝕜) where
  baseSet x := (chartAt 𝕜 x).source
  isOpen_baseSet x := (chartAt 𝕜 x).open_source
  indexAt := id
  mem_baseSet_at := mem_chart_source 𝕜
  coordChange x y p := ContinuousLinearMap.lsmul 𝕜 𝕜 (twistTransition k x y p)
  coordChange_self x p _ v := by simp
  continuousOn_coordChange x y :=
    (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).continuous.comp_continuousOn
      (contMDiffOn_twistTransition k x y).continuousOn
  coordChange_comp x y z p hp v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_assoc]
    rw [twistTransition_mul_twistTransition k hp.1.1 hp.1.2 hp.2]

theorem twistCore_baseSet (k : ℤ) (x : OnePoint 𝕜) :
    (twistCore k).baseSet x = (chartAt 𝕜 x).source :=
  (rfl)

@[simp]
theorem twistCore_localTriv_baseSet (k : ℤ) (x : OnePoint 𝕜) :
    ((twistCore k).localTriv x).baseSet = (chartAt 𝕜 x).source :=
  (rfl)

@[simp]
theorem twistCore_indexAt (k : ℤ) (x : OnePoint 𝕜) : (twistCore k).indexAt x = x :=
  (rfl)

@[simp]
theorem twistCore_coordChange_apply (k : ℤ) (x y p : OnePoint 𝕜) (v : 𝕜) :
    (twistCore k).coordChange x y p v = twistTransition k x y p * v :=
  (rfl)

/-- **`𝒪(k)` is an analytic line bundle.** Its transition functions are analytic, so for
`𝕜 = ℂ` it is a holomorphic line bundle on the Riemann sphere. -/
instance isContMDiff_twistCore (k : ℤ) : (twistCore (𝕜 := 𝕜) k).IsContMDiff 𝓘(𝕜) ω :=
  (VectorBundleCore.isContMDiff_iff_contMDiffOn_coordChange_one _).2 fun x y ↦
    (contMDiffOn_twistTransition k x y).congr fun p _ ↦ by simp

/-! ### Sections -/

/-- In the chart at `y`, a section `s` of `𝒪(k)` has the coordinate
`twistTransition k p y p * s p` at `p`. -/
theorem twistCore_localTriv_apply (k : ℤ) (y : OnePoint 𝕜) (s : OnePoint 𝕜 → 𝕜)
    (p : OnePoint 𝕜) :
    ((twistCore k).localTriv y ⟨p, s p⟩).2 = twistTransition k p y p * s p :=
  (rfl)

variable {n : ℕ∞ω}

/-- **Sections of `𝒪(k)` in the two charts.** A section `s` of `𝒪(k)` is `C^n` exactly when its
affine coordinate `s` is `C^n` off `∞` and its inverted coordinate
`p ↦ twistTransition k p ∞ p * s p` (which is `z⁻ᵏ s z` at a finite point `z ≠ 0` and `s ∞`
at `∞`) is `C^n` off `0`. -/
theorem contMDiff_section_twistCore_iff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) :
    ContMDiff 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜)) n
        (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore k).Fiber) p (s p)) ↔
      ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) n s {(∞ : OnePoint 𝕜)}ᶜ ∧
        ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) n (fun p ↦ twistTransition k p (∞ : OnePoint 𝕜) p * s p)
          {((0 : 𝕜) : OnePoint 𝕜)}ᶜ := by
  have h0 : MemTrivializationAtlas ((twistCore (𝕜 := 𝕜) k).localTriv ((0 : 𝕜) : OnePoint 𝕜)) :=
    ⟨⟨_, rfl⟩⟩
  have hinf : MemTrivializationAtlas ((twistCore (𝕜 := 𝕜) k).localTriv (∞ : OnePoint 𝕜)) :=
    ⟨⟨_, rfl⟩⟩
  let s' : ∀ p, (twistCore (𝕜 := 𝕜) k).Fiber p := s
  have hcov : ({(∞ : OnePoint 𝕜)}ᶜ ∪ {((0 : 𝕜) : OnePoint 𝕜)}ᶜ : Set (OnePoint 𝕜)) = univ := by
    rw [← compl_inter, eq_univ_iff_forall]
    intro p ⟨h1, h2⟩
    exact infty_ne_coe 0 (h1.symm.trans h2)
  have e0 := ((twistCore (𝕜 := 𝕜) k).localTriv ((0 : 𝕜) : OnePoint 𝕜)).contMDiffOn_section_iff
    (IB := 𝓘(𝕜)) (n := n) (s := s') (a := {(∞ : OnePoint 𝕜)}ᶜ) isClosed_infty.isOpen_compl
    fun p hp ↦ by simpa using hp
  have einf := ((twistCore (𝕜 := 𝕜) k).localTriv (∞ : OnePoint 𝕜)).contMDiffOn_section_iff
    (IB := 𝓘(𝕜)) (n := n) (s := s') (a := {((0 : 𝕜) : OnePoint 𝕜)}ᶜ)
    isClosed_singleton.isOpen_compl
    fun p hp ↦ by simpa using hp
  have hs0 : ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) n
      (fun p ↦ (((twistCore k).localTriv ((0 : 𝕜) : OnePoint 𝕜)) ⟨p, s p⟩).2)
        {(∞ : OnePoint 𝕜)}ᶜ ↔ ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) n s {(∞ : OnePoint 𝕜)}ᶜ := by
    refine contMDiffOn_congr fun p hp ↦ ?_
    induction p using OnePoint.rec with
    | infty => exact absurd rfl hp
    | coe z => rw [twistCore_localTriv_apply, twistTransition_coe_coe, one_mul]
  rw [← contMDiffOn_univ, ← hcov, contMDiffOn_union_iff_of_isOpen isClosed_infty.isOpen_compl
    isClosed_singleton.isOpen_compl, e0, einf, hs0]
  simp only [s', twistCore_localTriv_apply]

/-! ### Monomial sections -/

/-- The section `zʲ` of `𝒪(k)`: its affine coordinate is `zʲ`, and its value at `∞` is `1` if
`j = k` and `0` otherwise. For `j ≤ k` this is the value at `0` of `wᵏ⁻ʲ` in the inverted
coordinate `w = z⁻¹`, and the section is global (`OnePoint.contMDiff_monomialSection`). -/
def monomialSection (k j : ℕ) (p : OnePoint 𝕜) : 𝕜 :=
  p.elim (if j = k then 1 else 0) (· ^ j)

omit [ProperSpace 𝕜] in
@[simp]
theorem monomialSection_coe (k j : ℕ) (z : 𝕜) : monomialSection k j (z : OnePoint 𝕜) = z ^ j :=
  (rfl)

omit [ProperSpace 𝕜] in
@[simp]
theorem monomialSection_infty (k j : ℕ) :
    monomialSection k j (∞ : OnePoint 𝕜) = if j = k then 1 else 0 :=
  (rfl)

/-- Off `0`, the inverted coordinate of the section `zʲ` of `𝒪(k)` is `wᵏ⁻ʲ` in the inverted
coordinate `w`. -/
theorem twistTransition_mul_monomialSection {k j : ℕ} (hj : j ≤ k) {p : OnePoint 𝕜}
    (hp : p ≠ ((0 : 𝕜) : OnePoint 𝕜)) :
    twistTransition (k : ℤ) p (∞ : OnePoint 𝕜) p * monomialSection k j p =
      invChart p ^ (k - j) := by
  induction p using OnePoint.rec with
  | infty =>
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simp [twistTransition]
    · simp [twistTransition, hlt.ne, Nat.sub_ne_zero_of_lt hlt]
  | coe z =>
    have hz : z ≠ 0 := fun h ↦ hp (by rw [h])
    simp only [twistTransition, twistIndex_coe, twistIndex_infty, affineChart_coe,
      monomialSection_coe, invChart_coe, inv_pow]
    rw [← zpow_natCast z j, ← zpow_add₀ hz, ← zpow_natCast, Nat.cast_sub hj, ← zpow_neg]
    ring_nf

/-- **The monomial sections are global.** For `j ≤ k` the section `zʲ` of `𝒪(k)` is analytic
on the whole projective line. -/
theorem contMDiff_monomialSection {k j : ℕ} (hj : j ≤ k) :
    ContMDiff 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜)) ω
      (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore (k : ℤ)).Fiber) p
        (monomialSection (𝕜 := 𝕜) k j p)) := by
  rw [contMDiff_section_twistCore_iff]
  constructor
  · have h : ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) ω (fun p ↦ chartAt 𝕜 ((0 : 𝕜) : OnePoint 𝕜) p ^ j)
        (chartAt 𝕜 ((0 : 𝕜) : OnePoint 𝕜)).source :=
      (contDiff_id.pow j).contMDiff.comp_contMDiffOn contMDiffOn_chart
    refine (h.congr fun p hp ↦ ?_).mono fun p hp ↦ by simpa using hp
    induction p using OnePoint.rec with
    | infty => simp at hp
    | coe z => simp
  · have h : ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) ω (fun p ↦ chartAt 𝕜 (∞ : OnePoint 𝕜) p ^ (k - j))
        (chartAt 𝕜 (∞ : OnePoint 𝕜)).source :=
      (contDiff_id.pow (k - j)).contMDiff.comp_contMDiffOn contMDiffOn_chart
    refine (h.congr fun p hp ↦ ?_).mono fun p hp ↦ by simpa using hp
    have hp' : p ≠ ((0 : 𝕜) : OnePoint 𝕜) := by simpa using hp
    rw [twistTransition_mul_monomialSection hj hp', chartAt_infty]

/-- The section `z` of `𝒪(1)`: its affine coordinate is `z`, and its inverted coordinate is
constantly `1`. -/
abbrev identitySection : OnePoint 𝕜 → 𝕜 :=
  monomialSection 1 1

/-- The section `z` of `𝒪(1)` is analytic on the whole projective line. -/
theorem contMDiff_identitySection :
    ContMDiff 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜)) ω
      (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore (1 : ℤ)).Fiber) p
        (identitySection (𝕜 := 𝕜) p)) := by
  exact_mod_cast contMDiff_monomialSection (𝕜 := 𝕜) (le_refl 1)

omit [ProperSpace 𝕜] in
/-- The section `z` of `𝒪(1)` vanishes exactly at `0`; in particular it does not vanish at
`∞`, where its inverted coordinate is `1`. -/
theorem identitySection_eq_zero_iff {p : OnePoint 𝕜} :
    identitySection p = 0 ↔ p = ((0 : 𝕜) : OnePoint 𝕜) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp

omit [ProperSpace 𝕜] in
/-- The section `1` of `𝒪(0)`, which is the monomial section `z⁰`, vanishes nowhere; so `𝒪(0)` is
the trivial line bundle. -/
theorem monomialSection_zero_zero_ne_zero (p : OnePoint 𝕜) : monomialSection 0 0 p ≠ 0 := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp

end OnePoint
