/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal
public import TauCeti.Analysis.Normed.Module.Residue

/-!
# Serre's theorem: orthonormal bases are lifts of residue bases

Let `R` be an ultrametric seminormed commutative ring with a multiplicative pseudo-uniformiser
`ϖ`, and let `M` be an ultrametric seminormed `R`-module with contractive scalar action. Suppose
that the norms of `R` and of `M` take their values in `‖ϖ‖ ^ ℤ ∪ {0}`; this is the condition
`zpowCeil ‖ϖ‖ ‖x‖ = ‖x‖` of `TauCeti.zpowCeil`. When the norm of `R` satisfies it, rounding the
norm of a module up (`TauCeti.zpowCeilAddGroupNorm`) gives a bounded-equivalent norm satisfying it
as well. Write `R⁰` and `M⁰` for the closed unit balls, `R~ = R⁰ ⧸ R⁰⁰` for the residue ring and
`M~ = TauCeti.ResidueModule R M` for the residue module. Under the condition on the norms,
`R⁰⁰ • M⁰ = ϖM⁰` is the open unit ball of `M` (`TauCeti.mem_unitBallIdeal_smul_top_iff`), and
likewise `R⁰⁰ = ϖR⁰`, so that `R~ = R⁰ ⧸ ϖR⁰` and `M~ = M⁰ ⧸ ϖM⁰`.

Serre's theorem compares orthonormal families of `M` with bases of `M~`. For a family
`e : I → M⁰` with residues `ē i = ResidueModule.mk (e i)`:

* `e` is orthonormal exactly when the residues `ē` are linearly independent over `R~`
  (`TauCeti.ResidueModule.linearIndependent_mk_iff`). Orthonormal families always have
  independent residues, without the condition on the norms.
* if the residues span `M~`, then `e` has dense span
  (`TauCeti.ResidueModule.dense_span_of_span_mk_eq_top`). The proof is successive
  approximation: a vector of `M⁰` agrees with a combination of the `e i` modulo `ϖM⁰`, the error
  is `ϖ` times a vector of `M⁰`, and iterating approximates the vector modulo `ϖ ^ k M⁰` for
  every `k`. For an orthonormal family the converse holds, without the
  condition on the norms (`TauCeti.ResidueModule.span_mk_eq_top_of_isOrthonormalFamily`), so
  that the two are equivalent (`TauCeti.ResidueModule.span_mk_eq_top_iff`).

Thus `e` is an orthonormal basis exactly when `ē` is a basis of `M~`
(`TauCeti.ResidueModule.isOrthonormalBasis_iff`); the residues of an orthonormal basis form a
basis without the condition on the norms
(`TauCeti.ResidueModule.linearIndependent_mk_and_span_mk_eq_top`), and in particular any lift
of a basis of `M~` to `M⁰` is an orthonormal basis of `M`
(`TauCeti.ResidueModule.isOrthonormalBasis_of_basis`). No completeness is needed for these
statements. Over a complete ring and for a complete module, where
orthonormal bases are the same as linear isometries with model spaces `C₀(I, R)`, this shows that
`M` is orthonormalisable exactly when its residue module is free
(`TauCeti.isONable_iff_free_residueModule`).

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §2.
-/

public section

namespace TauCeti

/-- Scaling by `u ^ n` and then by `u ^ m` cancels when `m + n = 0`. -/
private theorem zpow_smul_zpow_smul_of_add_eq_zero {R M : Type*} [Monoid R] [MulAction R M]
    (u : Rˣ) {m n : ℤ} (hmn : m + n = 0) (x : M) :
    ((u ^ m : Rˣ) : R) • ((u ^ n : Rˣ) : R) • x = x := by
  rw [smul_smul, ← Units.val_mul, ← zpow_add, hmn, zpow_zero, Units.val_one, one_smul]

variable {R M I : Type*} [SeminormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module R M] [IsBoundedSMul R M]

namespace ResidueModule

/-- The residue of a finite combination of vectors of the closed unit ball with coefficients in
the closed unit ball of `R` is the combination of their residues. -/
private theorem mk_sum_smul (e : I → unitClosedBallSubmodule R M) (s : Finset I)
    (a : I → Subring.unitClosedBall R) :
    mk (∑ i ∈ s, a i • e i) = ∑ i ∈ s, Ideal.Quotient.mk (unitBallIdeal R) (a i) • mk (e i) := by
  simp [map_sum]

/-- **Orthonormal families have independent residues.** -/
theorem linearIndependent_mk_of_isOrthonormalFamily {e : I → unitClosedBallSubmodule R M}
    (he : IsOrthonormalFamily R fun i ↦ (e i : M)) :
    LinearIndependent (Subring.unitClosedBall R ⧸ unitBallIdeal R) (mk ∘ e) := by
  refine linearIndependent_iff'.2 fun s g hg i hi ↦ ?_
  choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have h0 : mk (∑ i ∈ s, a i • e i) = 0 := by
    simpa only [mk_sum_smul, ha, Function.comp_apply] using hg
  rw [mk_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hlt := norm_lt_one_of_mem_unitBallIdeal_smul_top h0
  rw [Submodule.coe_sum] at hlt
  simp only [Submodule.coe_smul, Subring.smul_def] at hlt
  rw [← ha i, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallIdeal]
  exact (he.norm_le_norm_sum_smul (fun i ↦ (a i : R)) hi).trans_lt hlt

variable (ϖ : NormedRing.PseudoUniformizer R)

/-- If the residues of a family of the closed unit ball are independent, then a combination of
the family with coefficients in the closed unit ball of `R`, one of norm one, has norm at least
one. -/
private theorem one_le_norm_sum_smul (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖)
    {e : I → unitClosedBallSubmodule R M}
    (hli : LinearIndependent (Subring.unitClosedBall R ⧸ unitBallIdeal R) (mk ∘ e))
    {s : Finset I} {b : I → Subring.unitClosedBall R} {j : I} (hj : j ∈ s)
    (hbj : ‖(b j : R)‖ = 1) :
    1 ≤ ‖∑ i ∈ s, (b i : R) • (e i : M)‖ := by
  by_contra! hlt
  have h0 : mk (∑ i ∈ s, b i • e i) = 0 := by
    rw [mk_eq_zero_iff ϖ hM, Submodule.coe_sum]
    simpa only [Submodule.coe_smul, Subring.smul_def] using hlt
  rw [mk_sum_smul] at h0
  have := linearIndependent_iff'.1 hli s (fun i ↦ Ideal.Quotient.mk _ (b i)) h0 j hj
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_unitBallIdeal, hbj] at this
  exact lt_irrefl _ this

/-- **Serre: orthonormality is independence of the residues.** For norms with values in
`‖ϖ‖ ^ ℤ ∪ {0}`, a family of the closed unit ball is orthonormal exactly when its residues are
linearly independent over the residue ring. -/
theorem linearIndependent_mk_iff (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) {e : I → unitClosedBallSubmodule R M} :
    LinearIndependent (Subring.unitClosedBall R ⧸ unitBallIdeal R) (mk ∘ e) ↔
      IsOrthonormalFamily R fun i ↦ (e i : M) := by
  refine ⟨fun hli ↦ isOrthonormalFamily_def.2 fun s a ↦ le_antisymm ?_ ?_,
    linearIndependent_mk_of_isOrthonormalFamily⟩
  · -- The ultrametric upper bound.
    refine (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans (Finset.sup_mono_fun fun i _ ↦ ?_)
    refine (nnnorm_smul_le _ _).trans (mul_le_of_le_one_right' ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact mem_unitClosedBallSubmodule.mp (e i).2
  -- For the lower bound, rescale the coefficients so that their largest norm is one.
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup s hs fun i ↦ ‖a i‖₊
  rw [hjsup, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  rcases (norm_nonneg (a j)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  set c := ‖(ϖ.unit : R)‖
  obtain ⟨n, hn⟩ := ((zpowCeil_eq_self_iff ϖ.norm_pos ϖ.norm_lt_one (norm_nonneg _)).mp
    (hR (a j))).resolve_left hpos.ne'
  -- The coefficients `b i = ϖ ^ (-n) * a i` lie in the unit ball, and `‖b j‖ = 1`.
  have hnorm_b (i : I) : ‖((ϖ.unit ^ (-n) : Rˣ) : R) * a i‖ = c ^ (-n) * ‖a i‖ := by
    rw [← smul_eq_mul, ϖ.norm_zpow_smul]
  have hb (i : I) (hi : i ∈ s) : ‖((ϖ.unit ^ (-n) : Rˣ) : R) * a i‖ ≤ 1 := by
    have hai : ‖a i‖ ≤ c ^ n := by
      rw [hn, ← coe_nnnorm, ← coe_nnnorm, NNReal.coe_le_coe, ← hjsup]
      exact Finset.le_sup (f := fun i ↦ ‖a i‖₊) hi
    rw [hnorm_b, zpow_neg]
    exact inv_mul_le_one_of_le₀ hai (zpow_nonneg ϖ.norm_pos.le n)
  have hbj : ‖((ϖ.unit ^ (-n) : Rˣ) : R) * a j‖ = 1 := by
    rw [hnorm_b, ← hn, zpow_neg, inv_mul_cancel₀ (zpow_pos ϖ.norm_pos n).ne']
  let b (i : I) : Subring.unitClosedBall R :=
    if hi : i ∈ s then ⟨((ϖ.unit ^ (-n) : Rˣ) : R) * a i, Subring.mem_unitClosedBall.mpr (hb i hi)⟩
    else 0
  have hb_coe {i : I} (hi : i ∈ s) : (b i : R) = ((ϖ.unit ^ (-n) : Rˣ) : R) * a i := by
    simp [b, hi]
  -- By independence of the residues, the combination `∑ b i • e i` has norm one.
  have hx := one_le_norm_sum_smul ϖ hM hli hj (b := b) (by rw [hb_coe hj, hbj])
  have hsum : ∑ i ∈ s, a i • (e i : M) =
      ((ϖ.unit ^ n : Rˣ) : R) • ∑ i ∈ s, (b i : R) • (e i : M) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hb_coe hi, mul_smul, zpow_smul_zpow_smul_of_add_eq_zero ϖ.unit (add_neg_cancel n)]
  rw [hsum, ϖ.norm_zpow_smul, hn]
  exact le_mul_of_one_le_right (norm_nonneg _) hx

/-- **Successive approximation.** If the residues of a family of the closed unit ball span the
residue module, then every vector of the closed unit ball is approximated by combinations of the
family to within `‖ϖ‖ ^ k`, for every `k`. -/
private theorem exists_mem_span_norm_sub_le (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖)
    {e : I → unitClosedBallSubmodule R M}
    (hspan : Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤)
    {x : M} (hx : ‖x‖ ≤ 1) (k : ℕ) :
    ∃ s ∈ Submodule.span R (Set.range fun i ↦ (e i : M)), ‖x - s‖ ≤ ‖(ϖ.unit : R)‖ ^ k := by
  set V := Submodule.span R (Set.range fun i ↦ (e i : M))
  set c := ‖(ϖ.unit : R)‖
  -- One step: a vector of the unit ball agrees with a combination modulo `ϖM⁰`.
  have step (y : M) (hy : ‖y‖ ≤ 1) : ∃ t ∈ V, ‖y - t‖ ≤ c := by
    let y₀ : unitClosedBallSubmodule R M := ⟨y, mem_unitClosedBallSubmodule.mpr hy⟩
    have hmem : mk y₀ ∈
        Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) :=
      hspan ▸ Submodule.mem_top
    obtain ⟨g, hg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
    choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (g i)
    refine ⟨∑ i ∈ g.support, (a i : R) • (e i : M),
      Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    have heq : mk y₀ = mk (∑ i ∈ g.support, a i • e i) := by
      rw [← hg, mk_sum_smul, Finsupp.sum]
      simp only [ha, Function.comp_apply]
    rw [mk_eq_mk_iff ϖ hM, Submodule.coe_sum] at heq
    simp only [Submodule.coe_smul, Subring.smul_def] at heq
    exact le_of_zpowCeil_eq_self_of_lt_one ϖ.norm_pos ϖ.norm_lt_one (hM _) heq
  induction k with
  | zero => exact ⟨0, V.zero_mem, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨s, hs, hxs⟩ := ih
    -- Rescale the error `x - s` into the unit ball and approximate it again.
    set y := ((ϖ.unit ^ (-(k : ℤ)) : Rˣ) : R) • (x - s)
    have hy : ‖y‖ ≤ 1 := by
      rw [ϖ.norm_zpow_smul, zpow_neg, zpow_natCast]
      exact inv_mul_le_one_of_le₀ hxs (pow_nonneg ϖ.norm_pos.le k)
    obtain ⟨t, ht, hyt⟩ := step y hy
    refine ⟨s + ((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • t, V.add_mem hs (V.smul_mem _ ht), ?_⟩
    have hxst : x - (s + ((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • t) =
        ((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • (y - t) := by
      rw [smul_sub, zpow_smul_zpow_smul_of_add_eq_zero ϖ.unit (add_neg_cancel (k : ℤ))]
      abel
    rw [hxst, ϖ.norm_zpow_smul, zpow_natCast, pow_succ]
    exact mul_le_mul_of_nonneg_left hyt (pow_nonneg ϖ.norm_pos.le k)

/-- **Lifts of a spanning family of residues have dense span.** If the residues of a family of
the closed unit ball span the residue module, for a norm with values in `‖ϖ‖ ^ ℤ ∪ {0}`, then the
family spans a dense submodule. -/
theorem dense_span_of_span_mk_eq_top (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖)
    {e : I → unitClosedBallSubmodule R M}
    (hspan : Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤) :
    Dense (Submodule.span R (Set.range fun i ↦ (e i : M)) : Set M) := by
  set V := Submodule.span R (Set.range fun i ↦ (e i : M))
  set c := ‖(ϖ.unit : R)‖
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro x _
  -- Vectors of the unit ball lie in the closure, by successive approximation.
  have hball (y : M) (hy : ‖y‖ ≤ 1) : y ∈ V.topologicalClosure := by
    refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε ϖ.norm_lt_one
    obtain ⟨s, hs, hys⟩ := exists_mem_span_norm_sub_le ϖ hM hspan hy k
    exact ⟨s, hs, ((dist_eq_norm y s).trans_le hys).trans_lt hk⟩
  -- A general vector is a power of `ϖ⁻¹` times a vector of the unit ball.
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (by positivity : 0 < ‖x‖ + 1))
    ϖ.norm_lt_one
  have hy : ‖((ϖ.unit ^ (k : ℤ) : Rˣ) : R) • x‖ ≤ 1 := by
    rw [ϖ.norm_zpow_smul, zpow_natCast]
    calc c ^ k * ‖x‖ ≤ c ^ k * (‖x‖ + 1) := by gcongr; linarith
      _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have := V.topologicalClosure.smul_mem ((ϖ.unit ^ (-(k : ℤ)) : Rˣ) : R) (hball _ hy)
  rwa [zpow_smul_zpow_smul_of_add_eq_zero ϖ.unit (neg_add_cancel (k : ℤ))] at this

include ϖ in
/-- **Orthonormal families with dense span have spanning residues.** If an orthonormal family of
the closed unit ball has dense span, then its residues span the residue module. This needs only a
multiplicative pseudo-uniformiser `ϖ`, with no condition on the values of the norms. -/
theorem span_mk_eq_top_of_isOrthonormalFamily {e : I → unitClosedBallSubmodule R M}
    (he : IsOrthonormalFamily R fun i ↦ (e i : M))
    (hdense : Dense (Submodule.span R (Set.range fun i ↦ (e i : M)) : Set M)) :
    Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨x, rfl⟩ := mk_surjective z
  -- Approximate `x` to within distance less than `‖ϖ‖` by a finite combination `∑ g i • e i`.
  obtain ⟨_, hsV, hxs⟩ := Metric.mem_closure_iff.mp (hdense.closure_eq ▸ Set.mem_univ (x : M)) _
    ϖ.norm_pos
  obtain ⟨g, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hsV
  rw [dist_eq_norm, Finsupp.sum] at hxs
  set s := ∑ i ∈ g.support, g i • (e i : M)
  -- By orthonormality the coefficients of `s` lie in the unit ball, since `‖s‖ ≤ 1`.
  have hs : ‖s‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x : M) (-((x : M) - s))
    rw [← sub_eq_add_neg, sub_sub_cancel, norm_neg] at this
    exact this.trans (max_le (mem_unitClosedBallSubmodule.mp x.2) (hxs.le.trans ϖ.norm_lt_one.le))
  have hg (i : I) : ‖g i‖ ≤ 1 := by
    by_cases hi : i ∈ g.support
    · exact (he.norm_le_norm_sum_smul g hi).trans hs
    · simp [Finsupp.notMem_support_iff.mp hi]
  let a (i : I) : Subring.unitClosedBall R := ⟨g i, Subring.mem_unitClosedBall.mpr (hg i)⟩
  -- So `x` has the residue of the combination `∑ a i • e i` of the unit ball, as the difference
  -- is `ϖ` times a vector of the unit ball.
  have hxy : mk x = mk (∑ i ∈ g.support, a i • e i) := by
    rw [mk_apply, mk_apply, Submodule.Quotient.eq]
    refine mem_unitBallIdeal_smul_top_of_norm_le ϖ ?_
    rw [Submodule.coe_sub, Submodule.coe_sum]
    simpa only [Submodule.coe_smul, Subring.smul_def, a] using hxs.le
  rw [hxy, mk_sum_smul]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Serre: dense span is spanning residues.** An orthonormal family of the closed unit ball has
dense span exactly when its residues span the residue module, for a norm with values in
`‖ϖ‖ ^ ℤ ∪ {0}`. -/
theorem span_mk_eq_top_iff (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖)
    {e : I → unitClosedBallSubmodule R M} (he : IsOrthonormalFamily R fun i ↦ (e i : M)) :
    Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤ ↔
      Dense (Submodule.span R (Set.range fun i ↦ (e i : M)) : Set M) :=
  ⟨dense_span_of_span_mk_eq_top ϖ hM, span_mk_eq_top_of_isOrthonormalFamily ϖ he⟩

include ϖ in
/-- **Orthonormal bases have residues forming a basis.** The residues of an orthonormal basis of
the closed unit ball are linearly independent over the residue ring and span the residue module.
This needs only a multiplicative pseudo-uniformiser `ϖ`, with no condition on the values of the
norms. -/
theorem linearIndependent_mk_and_span_mk_eq_top {e : I → unitClosedBallSubmodule R M}
    (he : IsOrthonormalBasis R fun i ↦ (e i : M)) :
    LinearIndependent (Subring.unitClosedBall R ⧸ unitBallIdeal R) (mk ∘ e) ∧
      Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤ :=
  ⟨linearIndependent_mk_of_isOrthonormalFamily he.isOrthonormalFamily,
    span_mk_eq_top_of_isOrthonormalFamily ϖ he.isOrthonormalFamily he.dense_span⟩

/-- **Serre's theorem.** For norms with values in `‖ϖ‖ ^ ℤ ∪ {0}`, a family of the closed unit
ball is an orthonormal basis exactly when its residues are a basis of the residue module: they are
linearly independent over the residue ring and span. -/
theorem isOrthonormalBasis_iff (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) {e : I → unitClosedBallSubmodule R M} :
    IsOrthonormalBasis R (fun i ↦ (e i : M)) ↔
      LinearIndependent (Subring.unitClosedBall R ⧸ unitBallIdeal R) (mk ∘ e) ∧
        Submodule.span (Subring.unitClosedBall R ⧸ unitBallIdeal R) (Set.range (mk ∘ e)) = ⊤ :=
  ⟨linearIndependent_mk_and_span_mk_eq_top ϖ, fun ⟨hli, hspan⟩ ↦
    ⟨(linearIndependent_mk_iff ϖ hR hM).1 hli, dense_span_of_span_mk_eq_top ϖ hM hspan⟩⟩

/-- **Lifts of a residue basis are an orthonormal basis.** For norms with values in
`‖ϖ‖ ^ ℤ ∪ {0}`, any family of the closed unit ball whose residues form a basis `b` of the residue
module is an orthonormal basis. -/
theorem isOrthonormalBasis_of_basis (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖)
    (b : Module.Basis I (Subring.unitClosedBall R ⧸ unitBallIdeal R) (ResidueModule R M))
    {e : I → unitClosedBallSubmodule R M} (he : ∀ i, mk (e i) = b i) :
    IsOrthonormalBasis R fun i ↦ (e i : M) := by
  have hb : mk ∘ e = b := funext he
  exact (isOrthonormalBasis_iff ϖ hR hM).2 ⟨hb ▸ b.linearIndependent, hb ▸ b.span_eq⟩

end ResidueModule

/-- **Serre's criterion for orthonormalisability.** Over a complete ultrametric normed
commutative ring with a multiplicative pseudo-uniformiser `ϖ`, let `M` be a complete ultrametric
module with contractive scalar action. If the norms of the ring and of `M` take their values in
`‖ϖ‖ ^ ℤ ∪ {0}`, then `M` is orthonormalisable exactly when its residue module is free over the
residue ring. -/
theorem isONable_iff_free_residueModule {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] [CompleteSpace R] {M : Type u} [NormedAddCommGroup M] [IsUltrametricDist M]
    [Module R M] [IsBoundedSMul R M] [CompleteSpace M] (ϖ : NormedRing.PseudoUniformizer R)
    (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖)
    (hM : ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖) :
    IsONable R M ↔
      Module.Free (Subring.unitClosedBall R ⧸ unitBallIdeal R) (ResidueModule R M) := by
  rw [isONable_iff_exists_isOrthonormalBasis]
  constructor
  · rintro ⟨I, e, he⟩
    let e₀ (i : I) : unitClosedBallSubmodule R M :=
      ⟨e i, mem_unitClosedBallSubmodule.mpr (he.isOrthonormalFamily.norm_apply_eq_one i).le⟩
    obtain ⟨hli, hspan⟩ := (ResidueModule.isOrthonormalBasis_iff (e := e₀) ϖ hR hM).1 he
    exact Module.Free.of_basis (Module.Basis.mk hli hspan.ge)
  · intro
    let b := Module.Free.chooseBasis (Subring.unitClosedBall R ⧸ unitBallIdeal R)
      (ResidueModule R M)
    choose e he using fun i ↦ ResidueModule.mk_surjective (b i)
    exact ⟨_, _, ResidueModule.isOrthonormalBasis_of_basis ϖ hR hM b he⟩

end TauCeti
