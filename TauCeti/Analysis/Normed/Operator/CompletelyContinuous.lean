/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.FiniteRank
public import TauCeti.Analysis.Normed.Operator.RingOpNorm
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Normed.Operator.Surjective

/-!
# Completely continuous operators over a coefficient ring

A continuous linear map `u : M →L[R] N` between seminormed modules over a ring `R` is
*completely continuous* (`ContinuousLinearMap.IsCompletelyContinuous`) if it can be approximated
uniformly by continuous maps of finite rank: for every `ε > 0` there is a continuous `v` whose
range lies in a finitely generated submodule (`LinearMap.IsFiniteRank`) with
`‖u x - v x‖ ≤ ε * ‖x‖` for all `x`. These are the operators of Serre's and Coleman's
Fredholm theory over Banach algebras such as affinoid algebras, where the scalar ring is not a
field and finite rank must be read relative to that ring.

The approximation is phrased through uniform bounds rather than through the operator norm, so
that the definition carries no junk value over scalar rings where continuous maps need not be
bounded. Over Tate scalars (`TauCeti.NormedRing.IsTate`), in particular over every nontrivially
normed field, it is approximation in the operator norm `ContinuousLinearMap.ringOpNorm`
(`ContinuousLinearMap.isCompletelyContinuous_iff_ringOpNorm`).

Over Tate scalars complete continuity is also a condition on lattices rather than norms: for a
bounded neighbourhood `M₀` of zero in the source, such as a bounded open lattice, `u` is
completely continuous exactly when for every neighbourhood `V` of zero in the target some
continuous map `g` of finite rank satisfies `(u - g)(M₀) ⊆ V`. This is the form in which complete
continuity is stated for Banach modules given by lattices rather than by norms. The condition
involves only the set `M₀` and the neighbourhoods of zero in the target, so different bounded open
lattices give the same notion, and so do equivalent norms (complete continuity is invariant under
continuous linear equivalences).

Completely continuous maps are closed under addition, scalar multiplication and uniform
approximation, under composition on either side with bounded continuous linear maps, and over
Tate scalars under composition on either side with arbitrary continuous linear maps. The
identity of a complete normed module is completely continuous exactly when the module is finitely
generated: an approximant of finite rank within distance `1 / 2` of the identity is surjective
(`TauCeti.surjective_of_norm_sub_apply_le`), so its range, which lies in a finitely generated
submodule, is everything. Consequently a completely continuous `u` with `(1 - u) ^ n = 0` forces
the module to be finitely generated.

## Main definitions

* `ContinuousLinearMap.IsCompletelyContinuous`: uniform approximability by continuous linear maps
  of finite rank, characterized by `ContinuousLinearMap.isCompletelyContinuous_iff`.

## Main results

* `LinearMap.IsFiniteRank.isCompletelyContinuous`: continuous maps of finite rank are completely
  continuous.
* `ContinuousLinearMap.isCompletelyContinuous_of_forall_approx`,
  `ContinuousLinearMap.isCompletelyContinuous_of_tendsto`,
  `ContinuousLinearMap.isClosed_setOf_isCompletelyContinuous`: complete continuity is closed under
  uniform approximation, under operator-norm limits over Tate scalars, and is a closed condition
  over a nontrivially normed field.
* `ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo`,
  `Filter.HasBasis.isCompletelyContinuous_iff_forall_mapsTo`: the lattice
  criterion over Tate scalars, for a bounded neighbourhood of zero in the source and all (or a
  basis of) neighbourhoods of zero in the target.
* `ContinuousLinearMap.IsCompletelyContinuous.clm_comp`,
  `ContinuousLinearMap.IsCompletelyContinuous.comp_clm`: the ideal property over Tate scalars,
  and `ContinuousLinearEquiv.comp_isCompletelyContinuous_iff`,
  `ContinuousLinearEquiv.isCompletelyContinuous_comp_iff`: invariance under continuous
  linear equivalences, hence under equivalent norms.
* `ContinuousLinearMap.IsCompletelyContinuous.clm_comp_of_bound`,
  `ContinuousLinearMap.IsCompletelyContinuous.comp_clm_of_bound`: composition on either side with
  a bounded continuous linear map, over any ring.
* `ContinuousLinearMap.isCompletelyContinuous_id_iff`: the identity of a complete normed module is
  completely continuous if and only if the module is finitely generated.
* `ContinuousLinearMap.IsCompletelyContinuous.finite_of_one_sub_pow_eq_zero`: a completely
  continuous `u` with `(1 - u) ^ n = 0` forces the module to be finitely generated.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

section Ring

variable {R M N : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]

/-- A continuous linear map `u` is **completely continuous** if it is a uniform limit of
continuous linear maps of finite rank: for every `ε > 0` there is a continuous linear `v` whose
range lies in a finitely generated submodule with `‖u x - v x‖ ≤ ε * ‖x‖` for every `x`. -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : M →L[R] N, (v : M →ₗ[R] N).IsFiniteRank ∧
    ∀ x, ‖u x - v x‖ ≤ ε * ‖x‖

/-- Unfolding `ContinuousLinearMap.IsCompletelyContinuous`: `u` is completely continuous iff for
every `ε > 0` some continuous linear map of finite rank is uniformly `ε`-close to `u`. -/
theorem isCompletelyContinuous_iff {u : M →L[R] N} :
    u.IsCompletelyContinuous ↔ ∀ ε : ℝ, 0 < ε → ∃ v : M →L[R] N,
      (v : M →ₗ[R] N).IsFiniteRank ∧ ∀ x, ‖u x - v x‖ ≤ ε * ‖x‖ :=
  Iff.rfl

/-- A continuous linear map of finite rank is completely continuous. -/
theorem _root_.LinearMap.IsFiniteRank.isCompletelyContinuous {u : M →L[R] N}
    (hu : (u : M →ₗ[R] N).IsFiniteRank) : u.IsCompletelyContinuous :=
  fun ε hε ↦ ⟨u, hu, fun x ↦ by rw [sub_self, norm_zero]; positivity⟩

@[simp]
theorem isCompletelyContinuous_zero : (0 : M →L[R] N).IsCompletelyContinuous :=
  LinearMap.IsFiniteRank.zero.isCompletelyContinuous

/-- Every continuous linear map into a finitely generated module is completely continuous. -/
theorem isCompletelyContinuous_of_finite [Module.Finite R N] (u : M →L[R] N) :
    u.IsCompletelyContinuous :=
  LinearMap.IsFiniteRank.of_finite_rng.isCompletelyContinuous

/-- **Complete continuity is closed under uniform approximation.** A continuous linear map that
is, for every `ε > 0`, uniformly `ε`-close to a completely continuous map is completely
continuous. -/
theorem isCompletelyContinuous_of_forall_approx {u : M →L[R] N}
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : M →L[R] N, v.IsCompletelyContinuous ∧
      ∀ x, ‖u x - v x‖ ≤ ε * ‖x‖) :
    u.IsCompletelyContinuous := by
  intro ε hε
  obtain ⟨v, hv, huv⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨w, hw, hvw⟩ := hv (ε / 2) (half_pos hε)
  refine ⟨w, hw, fun x ↦ ?_⟩
  calc ‖u x - w x‖ ≤ ‖u x - v x‖ + ‖v x - w x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 * ‖x‖ + ε / 2 * ‖x‖ := add_le_add (huv x) (hvw x)
    _ = ε * ‖x‖ := by ring

theorem IsCompletelyContinuous.add {u u' : M →L[R] N} (hu : u.IsCompletelyContinuous)
    (hu' : u'.IsCompletelyContinuous) : (u + u').IsCompletelyContinuous := by
  intro ε hε
  obtain ⟨v, hv, huv⟩ := hu (ε / 2) (half_pos hε)
  obtain ⟨v', hv', huv'⟩ := hu' (ε / 2) (half_pos hε)
  refine ⟨v + v', by simpa using hv.add hv', fun x ↦ ?_⟩
  calc ‖(u + u') x - (v + v') x‖ = ‖(u x - v x) + (u' x - v' x)‖ := by
        rw [add_apply, add_apply, add_sub_add_comm]
    _ ≤ ‖u x - v x‖ + ‖u' x - v' x‖ := norm_add_le _ _
    _ ≤ ε / 2 * ‖x‖ + ε / 2 * ‖x‖ := add_le_add (huv x) (huv' x)
    _ = ε * ‖x‖ := by ring

theorem IsCompletelyContinuous.neg {u : M →L[R] N} (hu : u.IsCompletelyContinuous) :
    (-u).IsCompletelyContinuous := by
  intro ε hε
  obtain ⟨v, hv, huv⟩ := hu ε hε
  refine ⟨-v, by simpa using hv.neg, fun x ↦ ?_⟩
  rw [neg_apply, neg_apply, neg_sub_neg, norm_sub_rev]
  exact huv x

/-- Complete continuity is invariant under negation. -/
@[simp]
theorem IsCompletelyContinuous.neg_iff {u : M →L[R] N} :
    (-u).IsCompletelyContinuous ↔ u.IsCompletelyContinuous :=
  ⟨fun hu ↦ by simpa using hu.neg, IsCompletelyContinuous.neg⟩

theorem IsCompletelyContinuous.sub {u u' : M →L[R] N} (hu : u.IsCompletelyContinuous)
    (hu' : u'.IsCompletelyContinuous) : (u - u').IsCompletelyContinuous :=
  sub_eq_add_neg u u' ▸ hu.add hu'.neg

theorem IsCompletelyContinuous.smul {S : Type*} [SeminormedRing S] [DistribMulAction S N]
    [IsBoundedSMul S N] [SMulCommClass R S N] {u : M →L[R] N} (hu : u.IsCompletelyContinuous)
    (c : S) : (c • u).IsCompletelyContinuous := by
  intro ε hε
  obtain ⟨v, hv, huv⟩ := hu (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨c • v, by simpa using hv.smul c, fun x ↦ ?_⟩
  calc ‖(c • u) x - (c • v) x‖ = ‖c • (u x - v x)‖ := by rw [smul_apply, smul_apply, smul_sub]
    _ ≤ ‖c‖ * ‖u x - v x‖ := norm_smul_le _ _
    _ ≤ (‖c‖ + 1) * (ε / (‖c‖ + 1) * ‖x‖) :=
        mul_le_mul (by linarith) (huv x) (norm_nonneg _) (by positivity)
    _ = ε * ‖x‖ := by field_simp

/-- A completely continuous map is approximated on every bounded set `M₀` by continuous maps of
finite rank, up to an arbitrary neighbourhood `V` of zero: some `g` of finite rank maps `M₀` into
`V` after subtraction from `u`. -/
theorem IsCompletelyContinuous.exists_isFiniteRank_mapsTo {u : M →L[R] N}
    (hu : u.IsCompletelyContinuous) {M₀ : Set M} (hM₀ : Bornology.IsBounded M₀) {V : Set N}
    (hV : V ∈ 𝓝 0) :
    ∃ g : M →L[R] N, (g : M →ₗ[R] N).IsFiniteRank ∧ Set.MapsTo (u - g) M₀ V := by
  obtain ⟨C, hC⟩ := hM₀.exists_norm_le
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  have hD : 0 < |C| + 1 := by positivity
  obtain ⟨g, hg, hug⟩ := hu (δ / (|C| + 1)) (div_pos hδ hD)
  refine ⟨g, hg, fun x hx ↦ hδV ?_⟩
  rw [mem_ball_zero_iff, sub_apply]
  calc ‖u x - g x‖ ≤ δ / (|C| + 1) * ‖x‖ := hug x
    _ < δ / (|C| + 1) * (|C| + 1) := by
        gcongr
        exact (hC x hx).trans_lt ((le_abs_self C).trans_lt (lt_add_one _))
    _ = δ := div_mul_cancel₀ δ hD.ne'

/-- Postcomposing a completely continuous map with a continuous linear map bounded by `C`, that is
with `‖g y‖ ≤ C * ‖y‖`, gives a completely continuous map. Over Tate scalars every continuous
linear map is bounded (`ContinuousLinearMap.IsCompletelyContinuous.clm_comp`). -/
theorem IsCompletelyContinuous.clm_comp_of_bound {P : Type*} [SeminormedAddCommGroup P]
    [Module R P] {u : M →L[R] N} (hu : u.IsCompletelyContinuous) (g : N →L[R] P) {C : ℝ}
    (hg : ∀ y, ‖g y‖ ≤ C * ‖y‖) : (g.comp u).IsCompletelyContinuous := by
  intro ε hε
  have hD : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hg' (y : N) : ‖g y‖ ≤ max C 1 * ‖y‖ :=
    (hg y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨v, hv, huv⟩ := hu (ε / max C 1) (div_pos hε hD)
  refine ⟨g.comp v, by simpa using hv.comp_left (g : N →ₗ[R] P), fun x ↦ ?_⟩
  calc ‖g.comp u x - g.comp v x‖ = ‖g (u x - v x)‖ := by rw [comp_apply, comp_apply, map_sub]
    _ ≤ max C 1 * ‖u x - v x‖ := hg' _
    _ ≤ max C 1 * (ε / max C 1 * ‖x‖) := by gcongr; exact huv x
    _ = ε * ‖x‖ := by field_simp

/-- Precomposing a completely continuous map with a continuous linear map bounded by `C`, that is
with `‖f x‖ ≤ C * ‖x‖`, gives a completely continuous map. Over Tate scalars every continuous
linear map is bounded (`ContinuousLinearMap.IsCompletelyContinuous.comp_clm`). -/
theorem IsCompletelyContinuous.comp_clm_of_bound {L : Type*} [SeminormedAddCommGroup L]
    [Module R L] {u : M →L[R] N} (hu : u.IsCompletelyContinuous) (f : L →L[R] M) {C : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖) : (u.comp f).IsCompletelyContinuous := by
  intro ε hε
  have hD : 0 < max C 1 := lt_max_of_lt_right one_pos
  have hf' (x : L) : ‖f x‖ ≤ max C 1 * ‖x‖ :=
    (hf x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨v, hv, huv⟩ := hu (ε / max C 1) (div_pos hε hD)
  refine ⟨v.comp f, by simpa using hv.comp_right (f : L →ₗ[R] M), fun x ↦ ?_⟩
  calc ‖u.comp f x - v.comp f x‖ ≤ ε / max C 1 * ‖f x‖ := huv (f x)
    _ ≤ ε / max C 1 * (max C 1 * ‖x‖) := by gcongr; exact hf' x
    _ = ε * ‖x‖ := by field_simp

end Ring

section Tate

open scoped TauCeti.RingOpNorm

variable {R L M N P : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup L] [Module R L] [IsBoundedSMul R L]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [SeminormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- Over Tate scalars, a continuous linear map is completely continuous if and only if it is a
limit of continuous maps of finite rank in the operator norm. -/
theorem isCompletelyContinuous_iff_ringOpNorm {u : M →L[R] N} :
    u.IsCompletelyContinuous ↔
      ∀ ε : ℝ, 0 < ε → ∃ v : M →L[R] N, (v : M →ₗ[R] N).IsFiniteRank ∧ ‖u - v‖ < ε := by
  refine ⟨fun hu ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · obtain ⟨v, hv, huv⟩ := hu (ε / 2) (half_pos hε)
    exact ⟨v, hv, (ringOpNorm_le_bound _ (half_pos hε).le (by simpa using huv)).trans_lt
      (half_lt_self hε)⟩
  · obtain ⟨v, hv, huv⟩ := h ε hε
    exact ⟨v, hv, fun x ↦ by simpa using le_of_ringOpNorm_le (u - v) huv.le x⟩

/-- Over Tate scalars, an operator-norm limit of completely continuous maps is completely
continuous. -/
theorem isCompletelyContinuous_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : M →L[R] N} {v : ι → M →L[R] N} (h : Tendsto (fun i ↦ ‖u - v i‖) l (𝓝 0))
    (hv : ∀ᶠ i in l, (v i).IsCompletelyContinuous) : u.IsCompletelyContinuous :=
  isCompletelyContinuous_of_forall_approx fun ε hε ↦
    have ⟨i, hvi, hi⟩ := (hv.and (h.eventually (gt_mem_nhds hε))).exists
    ⟨v i, hvi, fun x ↦ by simpa using le_of_ringOpNorm_le _ hi.le x⟩

/-- **The lattice criterion for complete continuity.** Over Tate scalars, let `M₀` be a bounded
neighbourhood of zero in `M`, such as a bounded open lattice. A continuous linear map `u` is
completely continuous if and only if for every neighbourhood `V` of zero in `N` some continuous
map `g` of finite rank satisfies `(u - g)(M₀) ⊆ V`.

The condition only involves the neighbourhoods of zero in `N` and the set `M₀`, so replacing `M₀`
by another bounded neighbourhood of zero does not change it. -/
theorem isCompletelyContinuous_iff_forall_mapsTo {u : M →L[R] N} {M₀ : Set M} (hM₀ : M₀ ∈ 𝓝 0)
    (hbdd : Bornology.IsBounded M₀) :
    u.IsCompletelyContinuous ↔ ∀ V ∈ 𝓝 (0 : N),
      ∃ g : M →L[R] N, (g : M →ₗ[R] N).IsFiniteRank ∧ Set.MapsTo (u - g) M₀ V := by
  refine ⟨fun hu V hV ↦ hu.exists_isFiniteRank_mapsTo hbdd hV, fun h ↦ ?_⟩
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  obtain ⟨r, hr, hrM₀⟩ := Metric.mem_nhds_iff.mp hM₀
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr ϖ.norm_lt_one
  have hϖ : 0 < ‖(ϖ.unit : R)‖ ^ ((k : ℤ) + 1) := zpow_pos ϖ.norm_pos _
  refine isCompletelyContinuous_iff_ringOpNorm.mpr fun ε hε ↦ ?_
  -- Approximate `u` within `ε / 2 * ‖ϖ‖ ^ (k + 1)` on the ball of radius `r > ‖ϖ‖ ^ k`; rescaling
  -- by powers of `ϖ` turns this into the operator-norm bound `‖u - g‖ ≤ ε / 2`.
  obtain ⟨g, hg, hug⟩ := h _ (Metric.ball_mem_nhds 0 (mul_pos (half_pos hε) hϖ))
  refine ⟨g, hg, ?_⟩
  have hle := ϖ.ringOpNorm_le_of_forall_norm_lt (u - g) k (by rwa [zpow_natCast])
    (mul_pos (half_pos hε) hϖ).le fun x hx ↦
      (mem_ball_zero_iff.mp (hug (hrM₀ (mem_ball_zero_iff.mpr hx)))).le
  rw [mul_inv_cancel_right₀ hϖ.ne'] at hle
  exact hle.trans_lt (half_lt_self hε)

/-- The lattice criterion `ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo` with the
neighbourhoods of zero in `N` restricted to a basis, such as a basis of open lattices. -/
theorem _root_.Filter.HasBasis.isCompletelyContinuous_iff_forall_mapsTo {ι : Sort*} {p : ι → Prop}
    {V : ι → Set N} (hV : (𝓝 (0 : N)).HasBasis p V) {u : M →L[R] N} {M₀ : Set M}
    (hM₀ : M₀ ∈ 𝓝 0) (hbdd : Bornology.IsBounded M₀) :
    u.IsCompletelyContinuous ↔ ∀ i, p i →
      ∃ g : M →L[R] N, (g : M →ₗ[R] N).IsFiniteRank ∧ Set.MapsTo (u - g) M₀ (V i) := by
  rw [ContinuousLinearMap.isCompletelyContinuous_iff_forall_mapsTo hM₀ hbdd]
  exact hV.forall_iff fun _ _ hst ⟨g, hg, hug⟩ ↦ ⟨g, hg, hug.mono_right hst⟩

omit [IsBoundedSMul R M] in
/-- Over Tate scalars, postcomposing a completely continuous map with a continuous linear map
gives a completely continuous map. -/
theorem IsCompletelyContinuous.clm_comp {u : M →L[R] N} (hu : u.IsCompletelyContinuous)
    (g : N →L[R] P) : (g.comp u).IsCompletelyContinuous :=
  have ⟨_, _, hg⟩ := ringOpNorm_bound g
  hu.clm_comp_of_bound g hg

omit [IsBoundedSMul R N] in
/-- Over Tate scalars, precomposing a completely continuous map with a continuous linear map
gives a completely continuous map. -/
theorem IsCompletelyContinuous.comp_clm {u : M →L[R] N} (hu : u.IsCompletelyContinuous)
    (f : L →L[R] M) : (u.comp f).IsCompletelyContinuous :=
  have ⟨_, _, hf⟩ := ringOpNorm_bound f
  hu.comp_clm_of_bound f hf

omit [IsBoundedSMul R M] in
/-- Over Tate scalars, complete continuity is unchanged by postcomposition with a continuous linear
equivalence; in particular it does not depend on the choice of an equivalent norm on the
target. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_isCompletelyContinuous_iff (e : N ≃L[R] P)
    {u : M →L[R] N} :
    ((e : N →L[R] P).comp u).IsCompletelyContinuous ↔ u.IsCompletelyContinuous :=
  ⟨fun h ↦ by simpa [← comp_assoc] using h.clm_comp (e.symm : P →L[R] N), fun h ↦ h.clm_comp _⟩

omit [IsBoundedSMul R N] in
/-- Over Tate scalars, complete continuity is unchanged by precomposition with a continuous linear
equivalence; in particular it does not depend on the choice of an equivalent norm on the
source. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.isCompletelyContinuous_comp_iff (e : L ≃L[R] M)
    {u : M →L[R] N} :
    (u.comp (e : L →L[R] M)).IsCompletelyContinuous ↔ u.IsCompletelyContinuous :=
  ⟨fun h ↦ by simpa [comp_assoc] using h.comp_clm (e.symm : M →L[R] L), fun h ↦ h.comp_clm _⟩

end Tate

/-- Over a nontrivially normed field, the completely continuous maps form a closed subset of the
space of continuous linear maps. -/
theorem isClosed_setOf_isCompletelyContinuous {K M N : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup M] [NormedSpace K M] [SeminormedAddCommGroup N] [NormedSpace K N] :
    IsClosed {u : M →L[K] N | u.IsCompletelyContinuous} := by
  refine isClosed_of_closure_subset fun u hu ↦ isCompletelyContinuous_of_forall_approx fun ε hε ↦ ?_
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu ε hε
  rw [dist_eq_norm] at huv
  exact ⟨v, hv, fun x ↦ by simpa [dist_eq_norm] using (u - v).le_of_opNorm_le huv.le x⟩

section Complete

variable {R M : Type*} [Ring R] [NormedAddCommGroup M] [Module R M] [CompleteSpace M]

/-- **The identity criterion.** The identity of a complete normed module is completely continuous
if and only if the module is finitely generated. -/
theorem isCompletelyContinuous_id_iff :
    (ContinuousLinearMap.id R M).IsCompletelyContinuous ↔ Module.Finite R M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isCompletelyContinuous_of_finite _⟩
  obtain ⟨v, hvQ, hv⟩ := h (1 / 2) one_half_pos
  obtain ⟨Q, hQ, hvQ⟩ := LinearMap.isFiniteRank_iff.mp hvQ
  have hrange : LinearMap.range (v : M →ₗ[R] M) = ⊤ :=
    LinearMap.range_eq_top.mpr (TauCeti.surjective_of_norm_sub_apply_le one_half_lt_one hv)
  exact ⟨eq_top_iff.mpr (hrange.ge.trans hvQ) ▸ hQ⟩

end Complete

section TateComplete

variable {R M : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]

/-- Over Tate scalars, a completely continuous endomorphism `u` of a complete normed module with
`(1 - u) ^ n = 0` forces the module to be finitely generated, since `u` then has the right
inverse `∑_{k < n} (1 - u) ^ k`. -/
theorem IsCompletelyContinuous.finite_of_one_sub_pow_eq_zero {u : M →L[R] M}
    (hu : u.IsCompletelyContinuous) {n : ℕ} (hn : (1 - u) ^ n = 0) : Module.Finite R M := by
  have h : u * ∑ k ∈ Finset.range n, (1 - u) ^ k = 1 := by
    simpa [hn] using mul_neg_geom_sum (1 - u) n
  rw [← isCompletelyContinuous_id_iff, ← one_def, ← h]
  exact hu.comp_clm _

end TateComplete

end ContinuousLinearMap
