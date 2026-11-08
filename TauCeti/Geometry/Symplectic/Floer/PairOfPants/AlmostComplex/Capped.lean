/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Floer.ComparisonFamily
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Almost complex structures on the capped pair of pants

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz (PSS) plane to each of the three ends of a pair of pants. The result is
a sphere with three poles, which in the coordinate `w` of `ℂ` are `0`, `1` and `∞`, the punctures
of the pair of pants `S = ℂ ∖ {0, 1}`. A one-parameter family of Floer problems on this sphere
starts at the unperturbed problem for a domain-independent compatible structure `J₀` and ends
at broken configurations with three long necks. This file constructs the almost complex
structures of that family as instances of the end-weighted structure
`TauCeti.Floer.endWeightedAlmostComplex`, like the pair-of-pants structure
`TauCeti.Floer.pairOfPantsAlmostComplex`.

Fix an `ω`-compatible base structure `J₀` and period-one families `J_q(t, x)` of `ω`-tame
structures on the three ends. On the end `q`, with cylinder coordinates `(s_q, t_q)` and signed
longitudinal coordinate `σ_q = ±s_q`, the end structure is switched on along `1 ≤ σ_q ≤ 2`, kept
along a neck `2 ≤ σ_q ≤ L + 2`, and switched off again along `L + 2 ≤ σ_q ≤ L + 3` towards the
pole. The whole datum is moreover moved along the segment from `J₀` by a cutoff `β(r)`. Thus
`TauCeti.Floer.cappedAlmostComplex h₀ J hJ r L` is the inverse Cayley transform, relative to `J₀`,
of

`β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J_q(t_q, x))`,

where `β` is the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. At most one term
of the sum is nonzero at each point, and the Cayley balls of tame and of compatible structures
are convex and contain `0 = cayley J₀`, so the structure is tame, and compatible when the end
structures are (`TauCeti.Floer.tames_cappedAlmostComplex`,
`TauCeti.Floer.compatible_cappedAlmostComplex`).

* It is `J₀` for `r ≤ 0` (`TauCeti.Floer.cappedAlmostComplex_of_nonpos`), and it does not depend
  on `r ≥ 1` (`TauCeti.Floer.cappedAlmostComplex_of_one_le`).
* It is `J₀` outside the compact truncation `S_{L + 3}` of the pair of pants
  (`TauCeti.Floer.cappedAlmostComplex_eq_base_of_notMem_truncation`), hence near the three poles
  (`TauCeti.Floer.eventually_cappedAlmostComplex_eq_base_of_eq_zero_or_eq_one`,
  `TauCeti.Floer.eventually_cocompact_cappedAlmostComplex_eq_base`): it extends by `J₀` to the
  closed sphere.
* For `r ≥ 1` it is the pair-of-pants structure wherever every `σ_q ≤ L + 2`, in particular on
  the truncation `S_{L + 2}` (`TauCeti.Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex`),
  and it is the end structure `J_q(t)` along the neck `2 ≤ σ_q ≤ L + 2`
  (`TauCeti.Floer.cappedAlmostComplex_cylindricalEndLift_of_mem_Icc`).
* Beyond the neck it is the structure for `L = 0` translated by `L` along the end
  (`TauCeti.Floer.cappedAlmostComplex_cylindricalEndLift_add_endSign_mul`), so the PSS plane
  pieces do not depend on the neck length.
* It is smooth jointly in `r`, `L`, the point `w ∈ ℂ`, including the poles `0` and `1`, and the
  parameter `x` (`TauCeti.Floer.contMDiff_cappedAlmostComplex`).

The comparison family is `TauCeti.Floer.cappedComparisonAlmostComplex h₀ J hJ R`, the structure
with `r = 3R - 1` and the neck length `L = TauCeti.Floer.comparisonNeckLength R` of the family of
Hamiltonian data `TauCeti.Floer.cutoffNeckFamily`. It is the domain-independent `J₀` for
`R ≤ 1/3`, in particular at `R = 0`; it is constant, without necks, on the collar
`2/3 ≤ R ≤ 3/2`; it has necks of length `R - 1` for `R ≥ 2`; and it is smooth in `R`. The
structure is switched on during `1/3 ≤ R ≤ 2/3`, where the cutoff
`TauCeti.Floer.comparisonCutoff` of the Hamiltonian data also uses `β(3R - 1)`.

The structures act on a fixed symplectic vector space `(V, ω)` and may depend on a point `x` of
a manifold `M`, for instance a target point when `V` is a model fiber.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures, and Section 12.1, on the PSS isomorphism.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the contractibility of the spaces of tame and compatible structures.
-/

public noncomputable section

open Set Real Filter Manifold Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

/-! ### The weights on the ends -/

section Weight

variable {q : Puncture} {L : ℝ} {w : ℂ}

/-- Where the weight of the end `q` is nonzero, the point lies on the part `1 < σ_q < L + 3` of
that end. -/
private theorem one_lt_and_lt_of_weight_ne_zero
    (h : smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      smoothTransition (L + 3 - q.endSign * (q.endCoord w).re) ≠ 0) :
    1 < q.endSign * (q.endCoord w).re ∧ q.endSign * (q.endCoord w).re < L + 3 := by
  refine ⟨lt_of_not_ge fun h' => h ?_, lt_of_not_ge fun h' => h ?_⟩
  · rw [smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · have h₂ : L + 3 - q.endSign * (q.endCoord w).re ≤ 0 := by linarith
    rw [smoothTransition.zero_of_nonpos h₂, mul_zero]

/-- Where the weight of some end is nonzero, the point lies in the truncation `S_{L + 3}`. -/
private theorem mem_truncation_of_weight_ne_zero
    (h : smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      smoothTransition (L + 3 - q.endSign * (q.endCoord w).re) ≠ 0) :
    w ∈ truncation (L + 3) := by
  obtain ⟨h₁, h₂⟩ := one_lt_and_lt_of_weight_ne_zero h
  obtain ⟨hw₀, hw₁⟩ := q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos (by linarith)
  refine mem_truncation.2 ⟨hw₀, hw₁, fun r => ?_⟩
  by_cases hr : q = r
  · exact hr ▸ h₂.le
  · linarith [endSign_mul_re_endCoord_nonpos hr (w := w) (by linarith)]

private theorem weight_mem_Icc :
    smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      smoothTransition (L + 3 - q.endSign * (q.endCoord w).re) ∈ Icc (0 : ℝ) 1 :=
  unitInterval.mul_mem ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

private theorem weight_eq_zero_of_notMem_truncation (hw : w ∉ truncation (L + 3)) :
    smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      smoothTransition (L + 3 - q.endSign * (q.endCoord w).re) = 0 :=
  by_contra fun h => hw (mem_truncation_of_weight_ne_zero h)

end Weight

/-! ### The capped structure -/

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The domain-dependent almost complex structure on the pair of pants capped by three PSS
planes along necks of length `L`, moved along the segment from `J₀` by the cutoff `β(r)`. It is
given by families `J q t x` of `ω`-tame structures on the three ends, relative to an
`ω`-compatible base structure `J₀`. It is the end-weighted structure
`TauCeti.Floer.endWeightedAlmostComplex` with the weights `β(r) β(σ_q - 1) β(L + 3 - σ_q)`, so at
`w ∈ ℂ` and `x ∈ M` it is the inverse Cayley transform, relative to `J₀`, of
`β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J q (t_q(w)) x)`, where `(s_q, t_q)` are the
coordinates of the end `q`, `σ_q = ±s_q(w)` and `β` is the smooth transition function. -/
def cappedAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (r L : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  endWeightedAlmostComplex h₀ J hJ
    (fun q w => smoothTransition r * (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      smoothTransition (L + 3 - q.endSign * (q.endCoord w).re)))
    (fun _ _ => unitInterval.mul_mem ⟨smoothTransition.nonneg r, smoothTransition.le_one r⟩
      weight_mem_Icc)
    (fun _ _ hq => zero_lt_one.trans (one_lt_and_lt_of_weight_ne_zero (right_ne_zero_of_mul hq)).1)
    w x

variable {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {r L : ℝ}

/-- The capped structure is tamed by `ω`. -/
theorem tames_cappedAlmostComplex (h₀ : ω.Compatible J₀) (r L : ℝ) (w : ℂ) (x : M) :
    ω.Tames (cappedAlmostComplex h₀ J hJ r L w x) :=
  tames_endWeightedAlmostComplex h₀ w x

/-- The Cayley transform of the capped structure, relative to `J₀`, is
`β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J q (t_q(w)) x)`. This characterizes the
structure, since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_cappedAlmostComplex (h₀ : ω.Compatible J₀) (r L : ℝ) (w : ℂ) (x : M) :
    J₀.cayley (cappedAlmostComplex h₀ J hJ r L w x) =
      smoothTransition r • ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
        smoothTransition (L + 3 - q.endSign * (q.endCoord w).re)) •
        J₀.cayley (J q (q.endCoord w).im x) := by
  simp only [cappedAlmostComplex, cayley_endWeightedAlmostComplex, Finset.smul_sum, smul_smul]

/-- The capped structure is `ω`-compatible when the structures on the ends are. -/
theorem compatible_cappedAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (r L : ℝ) (w : ℂ) (x : M) :
    ω.Compatible (cappedAlmostComplex h₀ J hJ r L w x) :=
  compatible_endWeightedAlmostComplex h₀ hJc w x

/-- For `r ≤ 0` the capped structure is the domain-independent base structure `J₀`. -/
theorem cappedAlmostComplex_of_nonpos (h₀ : ω.Compatible J₀) (hr : r ≤ 0) (L : ℝ) (w : ℂ)
    (x : M) : cappedAlmostComplex h₀ J hJ r L w x = J₀ := by
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L w x) h₀.tames ?_
  rw [cayley_cappedAlmostComplex, smoothTransition.zero_of_nonpos hr, zero_smul,
    AlmostComplexStructure.cayley_self]

/-- The capped structure does not depend on `r ≥ 1`. -/
theorem cappedAlmostComplex_of_one_le (h₀ : ω.Compatible J₀) (hr : 1 ≤ r) (L : ℝ) :
    cappedAlmostComplex h₀ J hJ r L = cappedAlmostComplex h₀ J hJ 1 L := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L w x)
    (tames_cappedAlmostComplex h₀ 1 L w x) ?_
  rw [cayley_cappedAlmostComplex, cayley_cappedAlmostComplex, smoothTransition.one_of_one_le hr,
    smoothTransition.one_of_one_le le_rfl]

/-- **The structure is `J₀` near the poles.** Outside the compact truncation `S_{L + 3}` of the
pair of pants, the capped structure is the base structure `J₀`. -/
theorem cappedAlmostComplex_eq_base_of_notMem_truncation (h₀ : ω.Compatible J₀) (r : ℝ)
    {w : ℂ} (hw : w ∉ truncation (L + 3)) (x : M) :
    cappedAlmostComplex h₀ J hJ r L w x = J₀ := by
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L w x) h₀.tames ?_
  rw [cayley_cappedAlmostComplex, AlmostComplexStructure.cayley_self]
  simp [weight_eq_zero_of_notMem_truncation hw]

/-- **The structure is `J₀` near the poles `0` and `1`.** -/
theorem eventually_cappedAlmostComplex_eq_base_of_eq_zero_or_eq_one (h₀ : ω.Compatible J₀)
    (r : ℝ) {c : ℂ} (hc : c = 0 ∨ c = 1) :
    ∀ᶠ w in 𝓝 c, ∀ x : M, cappedAlmostComplex h₀ J hJ r L w x = J₀ := by
  filter_upwards [(isCompact_truncation (L + 3)).isClosed.isOpen_compl.mem_nhds
    (notMem_truncation_of_eq_zero_or_eq_one hc _)] with w hw x
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ r hw x

/-- **The structure is `J₀` near the pole `∞`.** -/
theorem eventually_cocompact_cappedAlmostComplex_eq_base (h₀ : ω.Compatible J₀) (r : ℝ) :
    ∀ᶠ w in cocompact ℂ, ∀ x : M, cappedAlmostComplex h₀ J hJ r L w x = J₀ := by
  filter_upwards [(isCompact_truncation (L + 3)).compl_mem_cocompact] with w hw x
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ r hw x

variable {q : Puncture}

/-- **The structure on an end.** If `J q` has period one in `t`, then on the part `±s > 0` of the
end `q`, the Cayley transform of the capped structure at the point with end coordinates
`z = s + i t` is `β(r) β(±s - 1) β(L + 3 ∓ s) • cayley (J q t x)`. -/
theorem cayley_cappedAlmostComplex_cylindricalEndLift_of_pos (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) (r L : ℝ) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : M) :
    J₀.cayley (cappedAlmostComplex h₀ J hJ r L (q.cylindricalEndLift z) x) =
      (smoothTransition r * (smoothTransition (q.endSign * z.re - 1) *
        smoothTransition (L + 3 - q.endSign * z.re))) • J₀.cayley (J q z.im x) := by
  rw [cappedAlmostComplex,
    cayley_endWeightedAlmostComplex_cylindricalEndLift_of_pos h₀ hJp hz,
    re_endCoord_cylindricalEndLift]

/-- **The neck.** If `J q` has period one in `t` and `r ≥ 1`, then on the part
`2 ≤ ±s ≤ L + 2` of the end `q`, the capped structure at the point with end coordinates
`z = s + i t` is `J q t x`. -/
theorem cappedAlmostComplex_cylindricalEndLift_of_mem_Icc (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) (hr : 1 ≤ r) {z : ℂ}
    (hz : q.endSign * z.re ∈ Icc 2 (L + 2)) (x : M) :
    cappedAlmostComplex h₀ J hJ r L (q.cylindricalEndLift z) x = J q z.im x := by
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L _ x) (hJ q z.im x) ?_
  rw [cayley_cappedAlmostComplex_cylindricalEndLift_of_pos h₀ hJp r L (by linarith [hz.1]),
    smoothTransition.one_of_one_le hr, smoothTransition.one_of_one_le (by linarith [hz.1]),
    smoothTransition.one_of_one_le (by linarith [hz.2])]
  simp

/-- **The PSS plane pieces do not depend on the neck length.** If `J q` has period one in `t`,
then beyond the neck of length `L ≥ 0` the capped structure on the end `q` is the structure with
`L = 0` translated by `L` along the end. -/
theorem cappedAlmostComplex_cylindricalEndLift_add_endSign_mul (h₀ : ω.Compatible J₀)
    (hJp : Function.Periodic (J q) 1) (r : ℝ) (hL : 0 ≤ L) {z : ℂ}
    (hz : 2 ≤ q.endSign * z.re) (x : M) :
    cappedAlmostComplex h₀ J hJ r L (q.cylindricalEndLift (z + ↑(q.endSign * L))) x =
      cappedAlmostComplex h₀ J hJ r 0 (q.cylindricalEndLift z) x := by
  have hs : q.endSign * q.endSign = 1 := by
    rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> rw [h] <;> norm_num
  have hre : q.endSign * (z + ↑(q.endSign * L)).re = q.endSign * z.re + L := by
    rw [Complex.add_re, Complex.ofReal_re, mul_add, ← mul_assoc, hs, one_mul]
  have h₁ : 1 ≤ q.endSign * z.re - 1 := by linarith
  have h₁L : 1 ≤ q.endSign * z.re + L - 1 := by linarith
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L _ x)
    (tames_cappedAlmostComplex h₀ r 0 _ x) ?_
  rw [cayley_cappedAlmostComplex_cylindricalEndLift_of_pos h₀ hJp r L (by rw [hre]; linarith),
    cayley_cappedAlmostComplex_cylindricalEndLift_of_pos h₀ hJp r 0 (by linarith), hre,
    smoothTransition.one_of_one_le h₁L, smoothTransition.one_of_one_le h₁,
    Complex.add_im, Complex.ofReal_im, add_zero]
  ring_nf

/-- **The structure is the pair-of-pants structure up to the necks.** For `r ≥ 1`, at points where
the signed longitudinal coordinate of every end is at most `L + 2`, such as the points of the
truncation `S_{L + 2}`, the capped structure is the pair-of-pants structure. -/
theorem cappedAlmostComplex_eq_pairOfPantsAlmostComplex (h₀ : ω.Compatible J₀) (hr : 1 ≤ r)
    {w : ℂ} (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L + 2) (x : M) :
    cappedAlmostComplex h₀ J hJ r L w x = pairOfPantsAlmostComplex h₀ J hJ w x := by
  refine h₀.eq_of_cayley_eq (tames_cappedAlmostComplex h₀ r L w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_cappedAlmostComplex, cayley_pairOfPantsAlmostComplex,
    smoothTransition.one_of_one_le hr, one_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : 1 ≤ L + 3 - q.endSign * (q.endCoord w).re := by linarith [hw q]
  rw [smoothTransition.one_of_one_le hq, mul_one]

end Algebraic

/-! ### Smoothness -/

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- Near the center of the end `q`, the weight of the end `q` vanishes, locally uniformly in the
neck length. -/
private theorem eventually_weight_eq_zero (q : Puncture) (L₀ : ℝ) :
    ∀ᶠ p : ℂ × ℝ in 𝓝 (q.endCenter, L₀),
      smoothTransition (q.endSign * (q.endCoord p.1).re - 1) *
        smoothTransition (p.2 + 3 - q.endSign * (q.endCoord p.1).re) = 0 := by
  have hT : Tendsto (fun p : ℂ × ℝ => (p.1, p.2 + 3)) (𝓝 (q.endCenter, L₀))
      (𝓝 (q.endCenter, L₀ + 3)) :=
    (continuous_fst.prodMk (continuous_snd.add continuous_const)).tendsto _
  filter_upwards [hT.eventually (eventually_notMem_truncation q.endCenter_eq_zero_or_eq_one _)]
    with p hp
  exact weight_eq_zero_of_notMem_truncation hp

/-- The term of the end `q` in the Cayley coordinate of the capped structure is smooth jointly in
the neck length `L`, the point `w ∈ ℂ` and the parameter `x`, also at the center of the end, where
it vanishes nearby. -/
private theorem contMDiffAt_weight_smul_cayley (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Tames (J q t x)) {n : ℕ∞} (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap))
    (q : Puncture) (w : ℂ) (r L : ℝ) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × ((ℝ × ℝ) × M) =>
        (smoothTransition (q.endSign * (q.endCoord p.1).re - 1) *
          smoothTransition (p.2.1.2 + 3 - q.endSign * (q.endCoord p.1).re)) •
        LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.1).im p.2.2)))
      (w, (r, L), x) := by
  -- The parameters `r` and `L` as functions on the total space.
  have hpar : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ × ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) => p.2.1) (w, (r, L), x) :=
    contMDiffAt_fst.comp _ contMDiffAt_snd
  by_cases hw : w = q.endCenter
  · -- Near the center of the end, its weight vanishes identically.
    subst hw
    refine contMDiffAt_const (c := (0 : V →L[ℝ] V)).congr_of_eventuallyEq ?_
    have hproj : Tendsto (fun p : ℂ × ((ℝ × ℝ) × M) => (p.1, p.2.1.2))
        (𝓝 (q.endCenter, (r, L), x)) (𝓝 (q.endCenter, L)) :=
      (continuous_fst.prodMk
        (continuous_snd.comp (continuous_fst.comp continuous_snd))).tendsto _
    filter_upwards [hproj.eventually (eventually_weight_eq_zero q L)] with p hp
    simp [hp]
  -- Away from the center, the weight and the Cayley transform of the end structure, read at
  -- the angular coordinate, are smooth.
  have hσ : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) => q.endSign * (q.endCoord p.1).re) (w, (r, L), x) :=
    ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := fun w => q.endSign * (q.endCoord w).re) _
      (contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).contMDiffAt contMDiffAt_fst
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) n
      (fun p : ℝ × (ℝ × ℝ) =>
        smoothTransition (p.1 - 1) * smoothTransition (p.2.2 + 3 - p.1)) := by
    have h : ContMDiff 𝓘(ℝ, ℝ × (ℝ × ℝ)) 𝓘(ℝ, ℝ) n
        (fun p : ℝ × (ℝ × ℝ) =>
          smoothTransition (p.1 - 1) * smoothTransition (p.2.2 + 3 - p.1)) :=
      ((smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const)).mul
        (smoothTransition.contDiff.comp
          (((contDiff_snd.comp contDiff_snd).add contDiff_const).sub contDiff_fst))).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hP : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) =>
        smoothTransition (q.endSign * (q.endCoord p.1).re - 1) *
          smoothTransition (p.2.1.2 + 3 - q.endSign * (q.endCoord p.1).re)) (w, (r, L), x) :=
    hF.contMDiffAt.comp _ (hσ.prodMk hpar)
  have hFp : Function.Periodic
      (fun t (p : (ℝ × ℝ) × M) => LinearMap.toContinuousLinearMap (J₀.cayley (J q t p.2))) 1 :=
    fun t => by simp only [hJp q t]
  have hK : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × ((ℝ × ℝ) × M) =>
        LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.1).im p.2.2)))
      (w, (r, L), x) :=
    q.contMDiffAt_comp_im_endCoord hFp
      ((h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J q p.1 p.2)
        (fun p => hJ q p.1 p.2) (hJs q)).comp
        (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))) hw ((r, L), x)
  exact hP.smul hK

/-- **The structure is smooth.** For families `J q t x` of `ω`-tame structures which have period
one in `t` and are `C^n` on `ℝ × M`, the capped structure is `C^n` jointly in the cutoff
parameter `r`, the neck length `L`, the point `w ∈ ℂ`, including the poles `0` and `1`, and the
parameter `x`. -/
theorem contMDiff_cappedAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × ((ℝ × ℝ) × M) => LinearMap.toContinuousLinearMap
        (cappedAlmostComplex h₀ J hJ p.2.1.1 p.2.1.2 p.1 p.2.2).toLinearMap) := by
  rintro ⟨w, ⟨r, L⟩, x⟩
  refine contMDiffAt_endWeightedAlmostComplex h₀ (w := Prod.fst)
    (x := fun p : ℂ × ((ℝ × ℝ) × M) => p.2.2) ?_
  -- Each term of the Cayley transform is `β(r)` times the smooth term of its end.
  have hr : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) => smoothTransition p.2.1.1) (w, (r, L), x) :=
    (smoothTransition.contDiff.comp contDiff_fst).contMDiff.contMDiffAt.comp _
      (contMDiffAt_fst.comp _ contMDiffAt_snd)
  refine contMDiffAt_finsetSum fun q _ => ?_
  exact (hr.smul (contMDiffAt_weight_smul_cayley h₀ hJ hJp hJs q w r L x)).congr_of_eventuallyEq
    (.of_forall fun _ => mul_smul _ _ _)

end Smooth

/-! ### The comparison family -/

section Family

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The comparison family of almost complex structures on the three-pole sphere: the capped
structure with cutoff parameter `3R - 1` and the neck length
`L = TauCeti.Floer.comparisonNeckLength R`. It is the domain-independent `J₀` for `R ≤ 1/3`, is
switched on for `1/3 ≤ R ≤ 2/3`, and its necks grow without bound as `R → ∞`. -/
def cappedComparisonAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (R : ℝ) : ℂ → M → AlmostComplexStructure V :=
  cappedAlmostComplex h₀ J hJ (3 * R - 1) (comparisonNeckLength R)

variable {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {R : ℝ}

theorem cappedComparisonAlmostComplex_def (h₀ : ω.Compatible J₀) (R : ℝ) :
    cappedComparisonAlmostComplex h₀ J hJ R =
      cappedAlmostComplex h₀ J hJ (3 * R - 1) (comparisonNeckLength R) :=
  (rfl)

/-- For `R ≤ 1/3`, in particular at the start `R = 0` of the family, the structure is the
domain-independent base structure `J₀`. -/
theorem cappedComparisonAlmostComplex_of_le (h₀ : ω.Compatible J₀) (hR : R ≤ 1 / 3) (w : ℂ)
    (x : M) : cappedComparisonAlmostComplex h₀ J hJ R w x = J₀ :=
  cappedAlmostComplex_of_nonpos h₀ (by linarith) _ w x

/-- The family is constant on the collar `2/3 ≤ R ≤ 3/2`, where the structure is fully switched
on and has no necks. -/
theorem cappedComparisonAlmostComplex_of_mem_Icc (h₀ : ω.Compatible J₀)
    (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    cappedComparisonAlmostComplex h₀ J hJ R = cappedAlmostComplex h₀ J hJ 1 0 := by
  rw [cappedComparisonAlmostComplex_def, comparisonNeckLength_of_le hR.2,
    cappedAlmostComplex_of_one_le h₀ (by linarith [hR.1])]

/-- For `R ≥ 2` the structure is fully switched on and has necks of length `R - 1`. -/
theorem cappedComparisonAlmostComplex_of_two_le (h₀ : ω.Compatible J₀) (hR : 2 ≤ R) :
    cappedComparisonAlmostComplex h₀ J hJ R = cappedAlmostComplex h₀ J hJ 1 (R - 1) := by
  rw [cappedComparisonAlmostComplex_def, comparisonNeckLength_of_ge hR,
    cappedAlmostComplex_of_one_le h₀ (by linarith)]

end Family

section FamilySmooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The comparison family is smooth** jointly in the family parameter `R`, the point `w ∈ ℂ`
and the parameter `x`. -/
theorem contMDiff_cappedComparisonAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × (ℝ × M) => LinearMap.toContinuousLinearMap
        (cappedComparisonAlmostComplex h₀ J hJ p.2.1 p.1 p.2.2).toLinearMap) := by
  have hr : ContDiff ℝ n fun R : ℝ => 3 * R - 1 := by fun_prop
  have hrL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) n fun R => (3 * R - 1, comparisonNeckLength R) :=
    (hr.prodMk contDiff_comparisonNeckLength).contMDiff
  have hg : ContMDiff (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) n
      fun p : ℂ × (ℝ × M) => (p.1, ((3 * p.2.1 - 1, comparisonNeckLength p.2.1), p.2.2)) :=
    contMDiff_fst.prodMk ((hrL.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd))
  -- Unfold the family before comparing the two functions: unifying them up to definitional
  -- equality, with the family folded, does not terminate in reasonable time.
  convert (contMDiff_cappedAlmostComplex (hJ := hJ) h₀ hJp hJs).comp hg using 1
  funext p
  simp only [Function.comp_apply, cappedComparisonAlmostComplex_def]

end FamilySmooth

end TauCeti.Floer
