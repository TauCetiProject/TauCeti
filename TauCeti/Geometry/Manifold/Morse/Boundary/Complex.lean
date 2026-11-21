/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Differential

/-!
# The mod-two Morse complex and Morse homology

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` an
adapted pseudo-gradient satisfying the Morse–Smale condition. The mod-two Morse boundary
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary` counts trajectories between critical
points of consecutive index and squares to zero
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_comp_morseBoundary`). This file grades
it by the Morse index and packages it as a chain complex of `ZMod 2`-vector spaces indexed by `ℕ`,
the **mod-two Morse complex** `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`, whose
homology is the mod-two Morse homology of `(f, X)`.

The chains of degree `k` are the chains supported on the critical points of index `k`
(`TauCeti.morseChainPiece`), a vector space of dimension `cₖ`, the number of critical points of
index `k` (`TauCeti.IsMorse.finrank_morseChainPiece`). The boundary lowers the index by one, so it
restricts to maps from degree `k + 1` to degree `k`.

The rest of the file reads off the numerical consequences. Write `bₖ` for the dimension of the
`k`-th Morse homology.

* **Weak and strong Morse inequalities.** `bₖ ≤ cₖ`, and
  `bₖ - bₖ₋₁ + ⋯ ± b₀ ≤ cₖ - cₖ₋₁ + ⋯ ± c₀`, from the general inequalities for chain complexes of
  vector spaces (`ChainComplex.sum_range_neg_one_pow_mul_finrank_homology_le`).
* **Euler's equality and the Morse polynomial identity.** The complex vanishes above degree `n`,
  since every index is at most `n`, so its homology does too, `∑ (-1)ⁱ bᵢ = ∑ (-1)ⁱ cᵢ`, and
  `∑ cᵢ tⁱ = ∑ bᵢ tⁱ + (1 + t) Q(t)` with `Q` having natural number coefficients.
* **The extreme degrees.** If `M` is nonempty, the Morse homology is nonzero in degrees `0` and
  `n`. In degree `n` the fundamental chain, the sum of the critical points of index `n`, is a
  nonzero cycle, and nothing of degree `n + 1` bounds it. In degree `0` the augmentation, which
  adds the coefficients of the critical points of index `0`, vanishes on boundaries
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseAugmentation_morseBoundary`) and is nonzero
  on the minimum of `f`.

The same inequalities hold for the singular homology of `M`
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_le`), but they are proved
there through a CW model and the sublevel sets of `f`, not through trajectories; the
identification of Morse homology with singular homology is not proved here.

## Main definitions

* `TauCeti.morseChainPiece I f k`: the mod-two chains supported on the critical points of index `k`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryPiece`: the Morse boundary from
  degree `k + 1` to degree `k`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`: the mod-two Morse complex.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `finrank_homology_morseComplex_le`: the weak Morse inequalities.
* `sum_range_neg_one_pow_mul_finrank_homology_morseComplex_le`: the strong Morse inequalities.
* `sum_range_neg_one_pow_mul_finrank_homology_morseComplex`: Euler's equality.
* `exists_sum_range_monomial_eq_add_mul`: the Morse polynomial identity.
* `isZero_homology_morseComplex_of_finrank_lt`: Morse homology vanishes above the dimension.
* `finrank_homology_morseComplex_zero_pos`, `finrank_homology_morseComplex_finrank_pos`: Morse
  homology is nonzero in degrees `0` and `n`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and its homology).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5 (the Morse inequalities).
-/

public section

open CategoryTheory Limits Module Polynomial Set
open scoped Manifold ContDiff

universe u

namespace TauCeti

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

/-! ### Chains of a fixed index -/

variable (I f) in
/-- The mod-two Morse chains of degree `k`: the chains supported on the critical points of `f` of
Morse index `k`. -/
noncomputable def morseChainPiece (k : ℕ) : Submodule (ZMod 2) (criticalPoints I f →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {p | manifoldMorseIndex I f p = k}

/-- A chain has degree `k` exactly when it vanishes at the critical points of index other than
`k`. -/
theorem mem_morseChainPiece {k : ℕ} {c : criticalPoints I f →₀ ZMod 2} :
    c ∈ morseChainPiece I f k ↔ ∀ p : criticalPoints I f, manifoldMorseIndex I f p ≠ k → c p = 0 :=
  Finsupp.mem_supported' _ _

/-- A multiple of a critical point is a chain of degree its index. -/
theorem single_mem_morseChainPiece (p : criticalPoints I f) (a : ZMod 2) :
    Finsupp.single p a ∈ morseChainPiece I f (manifoldMorseIndex I f p) :=
  Finsupp.single_mem_supported _ _ rfl

/-- There are no chains of degree above the dimension of the model space. -/
theorem morseChainPiece_eq_bot_of_finrank_lt {k : ℕ}
    (hk : finrank ℝ E < k) : morseChainPiece I f k = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Submodule.mem_bot]
  ext p
  exact mem_morseChainPiece.1 hc p (manifoldMorseIndex_le_finrank.trans_lt hk).ne

variable [IsManifold I 1 M] [CompactSpace M]

/-- The chains of each degree of a Morse function on a compact manifold form a finite-dimensional
space. -/
theorem IsMorse.finite_morseChainPiece (hf : IsMorse I f) (k : ℕ) :
    Module.Finite (ZMod 2) (morseChainPiece I f k) :=
  haveI := hf.finite_criticalPoints.to_subtype
  inferInstance

/-- **The chains of degree `k` have dimension `cₖ`**, the number of critical points of index
`k`. -/
theorem IsMorse.finrank_morseChainPiece (hf : IsMorse I f) (k : ℕ) :
    finrank (ZMod 2) (morseChainPiece I f k) = (criticalCount I f k).toNat := by
  classical
  have := hf.finite_criticalPoints.fintype
  have himage : ((↑) : criticalPoints I f → M) '' {p | manifoldMorseIndex I f p = k} =
      {x ∈ criticalPoints I f | manifoldMorseIndex I f x = k} := by
    ext x
    exact ⟨fun ⟨p, hp, hpx⟩ ↦ hpx ▸ ⟨p.2, hp⟩, fun ⟨hx, hk⟩ ↦ ⟨⟨x, hx⟩, hk, rfl⟩⟩
  rw [morseChainPiece, (Finsupp.supportedEquivFinsupp _).finrank_eq, finrank_finsupp_self,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, criticalCount_def, ← himage,
    Subtype.val_injective.encard_image, ncard_def]

end

/-! ### The Morse complex -/

section MorseComplex

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The fundamental chain, the sum of the critical points of top index, is a chain of top
degree. -/
theorem morseFundamentalChain_mem_morseChainPiece (hf : IsMorse 𝓘(ℝ, E) f) :
    morseFundamentalChain hf ∈ morseChainPiece 𝓘(ℝ, E) f (finrank ℝ E) :=
  mem_morseChainPiece.2 fun p hp ↦ by simp [hp]

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The Morse boundary lowers the degree by one.** -/
theorem morseBoundary_mem_morseChainPiece {k : ℕ} {c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2}
    (hc : c ∈ morseChainPiece 𝓘(ℝ, E) f (k + 1)) :
    h.morseBoundary hf c ∈ morseChainPiece 𝓘(ℝ, E) f k := by
  rw [mem_morseChainPiece] at hc ⊢
  intro q hq
  rw [h.morseBoundary_apply hf]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  dsimp only
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = k + 1
  · rw [h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf (p := p) (q := q) (by omega),
      mul_zero]
  · rw [hc p hp, zero_mul]

/-- The mod-two Morse boundary from the chains of degree `k + 1` to those of degree `k`. -/
noncomputable def morseBoundaryPiece (k : ℕ) :
    morseChainPiece 𝓘(ℝ, E) f (k + 1) →ₗ[ZMod 2] morseChainPiece 𝓘(ℝ, E) f k :=
  (h.morseBoundary hf).restrict fun _ ↦ h.morseBoundary_mem_morseChainPiece hf

/-- The Morse boundary of a chain of degree `k + 1` is its total Morse boundary. -/
@[simp]
theorem coe_morseBoundaryPiece_apply (k : ℕ) (c : morseChainPiece 𝓘(ℝ, E) f (k + 1)) :
    (h.morseBoundaryPiece hf k c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) =
      h.morseBoundary hf c :=
  (rfl)

/-- The graded Morse boundary squares to zero. -/
@[simp]
theorem morseBoundaryPiece_comp_morseBoundaryPiece (k : ℕ) :
    h.morseBoundaryPiece hf k ∘ₗ h.morseBoundaryPiece hf (k + 1) = 0 := by
  ext c : 2
  simp

/-- **The mod-two Morse complex** of a Morse–Smale adapted pseudo-gradient of a Morse function on a
compact manifold: in degree `k` the chains supported on the critical points of index `k`, with the
trajectory-counting boundary. -/
-- Exposed: the statement of `morseComplex_d` needs the terms of the complex definitionally.
@[expose]
noncomputable def morseComplex : ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  ChainComplex.of (fun k ↦ ModuleCat.of (ZMod 2) (morseChainPiece 𝓘(ℝ, E) f k))
    (fun k ↦ ModuleCat.ofHom (h.morseBoundaryPiece hf k))
    fun k ↦ ModuleCat.hom_ext (h.morseBoundaryPiece_comp_morseBoundaryPiece hf k)

/-- The term of degree `k` of the Morse complex is the space of chains of degree `k`. -/
@[simp]
theorem morseComplex_X (k : ℕ) :
    (h.morseComplex hf).X k = ModuleCat.of (ZMod 2) (morseChainPiece 𝓘(ℝ, E) f k) :=
  (rfl)

/-- The differential of the Morse complex is the graded Morse boundary. -/
@[simp]
theorem morseComplex_d (k : ℕ) :
    (h.morseComplex hf).d (k + 1) k = ModuleCat.ofHom (h.morseBoundaryPiece hf k) := by
  simp [morseComplex]

/-- The terms of the Morse complex are finite-dimensional. -/
theorem finite_morseComplex_X (k : ℕ) : Module.Finite (ZMod 2) ((h.morseComplex hf).X k) :=
  hf.finite_morseChainPiece k

/-- The term of degree `k` of the Morse complex has dimension `cₖ`, the number of critical points
of index `k`. -/
theorem finrank_morseComplex_X (k : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).X k) = (criticalCount 𝓘(ℝ, E) f k).toNat :=
  hf.finrank_morseChainPiece k

/-- The Morse complex vanishes above the dimension of the manifold. -/
theorem isZero_morseComplex_X_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero ((h.morseComplex hf).X k) := by
  rw [ModuleCat.isZero_iff_subsingleton, morseComplex_X, morseChainPiece_eq_bot_of_finrank_lt hk]
  infer_instance

/-- **Morse homology vanishes above the dimension of the manifold.** -/
theorem isZero_homology_morseComplex_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero ((h.morseComplex hf).homology k) :=
  (((h.morseComplex hf).exactAt_iff k).2 (ShortComplex.exact_of_isZero_X₂ _
    (h.isZero_morseComplex_X_of_finrank_lt hf hk))).isZero_homology

/-! ### The Morse inequalities -/

/-- **The weak Morse inequalities.** The `k`-th mod-two Morse homology has dimension at most the
number of critical points of index `k`. -/
theorem finrank_homology_morseComplex_le (k : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology k) ≤ (criticalCount 𝓘(ℝ, E) f k).toNat := by
  have := h.finite_morseComplex_X hf k
  rw [← h.finrank_morseComplex_X hf k]
  exact (h.morseComplex hf).finrank_homology_le_finrank_X k

/-- **The strong Morse inequalities.** Write `bᵢ` for the dimension of the `i`-th mod-two Morse
homology and `cᵢ` for the number of critical points of index `i`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex_le (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank (ZMod 2) ((h.morseComplex hf).homology i) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  simpa only [h.finrank_morseComplex_X hf] using
    (h.morseComplex hf).sum_range_neg_one_pow_mul_finrank_homology_le n
      fun i _ ↦ h.finite_morseComplex_X hf i

/-- The differential of the Morse complex out of a degree above the dimension vanishes. -/
private theorem morseComplex_d_eq_zero {n : ℕ} (hn : finrank ℝ E ≤ n) :
    (h.morseComplex hf).d (n + 1) n = 0 :=
  (h.isZero_morseComplex_X_of_finrank_lt hf (Nat.lt_succ_of_le hn)).eq_of_src _ _

/-- **Euler's equality.** Write `bᵢ` for the dimension of the `i`-th mod-two Morse homology and
`cᵢ` for the number of critical points of index `i`. Then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ` for
every `n` at least the dimension of the manifold. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_morseComplex {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank (ZMod 2) ((h.morseComplex hf).homology i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, E) f i).toNat := by
  simpa only [h.finrank_morseComplex_X hf] using
    ((h.morseComplex hf).sum_range_finrank_X_eq_sum_range_finrank_homology
      (fun i _ ↦ h.finite_morseComplex_X hf i) (h.morseComplex_d_eq_zero hf hn)).symm

/-- **The Morse polynomial identity.** Write `bᵢ` for the dimension of the `i`-th mod-two Morse
homology and `cᵢ` for the number of critical points of index `i`. For every `n` at least the
dimension of the manifold, `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with
natural number coefficients. -/
theorem exists_sum_range_monomial_eq_add_mul {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (criticalCount 𝓘(ℝ, E) f i).toNat =
      ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank (ZMod 2) ((h.morseComplex hf).homology i)) +
        (1 + Polynomial.X) * Q := by
  simp_rw [← h.finrank_morseComplex_X hf]
  exact ⟨_, (h.morseComplex hf).sum_range_monomial_finrank_X_eq
    (fun i _ ↦ h.finite_morseComplex_X hf i) (h.morseComplex_d_eq_zero hf hn)⟩

/-! ### The extreme degrees -/

/-- A chain of degree `k` whose Morse boundary vanishes is a cycle of the Morse complex. -/
private theorem morseComplex_d_apply_eq_zero {k j : ℕ} (c : morseChainPiece 𝓘(ℝ, E) f k)
    (hc : h.morseBoundary hf c = 0) : ((h.morseComplex hf).d k j).hom c = 0 := by
  by_cases hkj : k = j + 1
  · subst hkj
    rw [morseComplex_d]
    exact Subtype.ext hc
  · rw [(h.morseComplex hf).shape _ _ (by simpa [eq_comm] using hkj)]
    rfl

/-- **Morse homology is nonzero in the top degree.** On a nonempty manifold of dimension `n`, the
`n`-th mod-two Morse homology is nonzero: the fundamental chain is a nonzero cycle, and the Morse
complex vanishes in degree `n + 1`. -/
theorem finrank_homology_morseComplex_finrank_pos [Nonempty M] :
    0 < finrank (ZMod 2) ((h.morseComplex hf).homology (finrank ℝ E)) := by
  set K := h.morseComplex hf
  set n := finrank ℝ E
  have : Module.Finite (ZMod 2) (K.sc n).X₂ := h.finite_morseComplex_X hf n
  -- `f` has a critical point `x` of top index, at a maximum, where the fundamental chain is `1`.
  have hcount := hf.criticalCount_finrank_ne_zero
  rw [criticalCount_def] at hcount
  obtain ⟨x, hx, hxn⟩ := nonempty_of_encard_ne_zero hcount
  let c : morseChainPiece 𝓘(ℝ, E) f n :=
    ⟨morseFundamentalChain hf, morseFundamentalChain_mem_morseChainPiece hf⟩
  have hc : c ≠ 0 := fun hc0 ↦ by
    have h1 := congrArg (fun c : morseChainPiece 𝓘(ℝ, E) f n ↦
      (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) ⟨x, hx⟩) hc0
    simp [c, hxn] at h1
  have hcyc : c ∈ LinearMap.ker (K.sc n).g.hom :=
    h.morseComplex_d_apply_eq_zero hf c (h.morseBoundary_morseFundamentalChain hf)
  -- Nothing of degree `n + 1` bounds it, so the homology is the space of cycles.
  have hf0 : (K.sc n).f = 0 :=
    (h.isZero_morseComplex_X_of_finrank_lt hf (by rw [ChainComplex.prev]; omega)).eq_of_src _ _
  have hkey := (K.sc n).finrank_homology_add_finrank_range_f
  rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot, add_zero] at hkey
  -- The homology of `K` in degree `n` is by definition that of the short complex `K.sc n`.
  change 0 < finrank (ZMod 2) (K.sc n).homology
  rw [hkey]
  exact Module.finrank_pos_iff_exists_ne_zero.2
    ⟨⟨c, hcyc⟩, fun h0 ↦ hc (congrArg Subtype.val h0)⟩

/-- **Morse homology is nonzero in degree `0`.** On a nonempty manifold, the `0`-th mod-two Morse
homology is nonzero: the augmentation vanishes on boundaries and is nonzero on a minimum of `f`. -/
theorem finrank_homology_morseComplex_zero_pos [Nonempty M] :
    0 < finrank (ZMod 2) ((h.morseComplex hf).homology 0) := by
  have := h.finite_morseComplex_X hf 0
  -- `f` has a critical point `x` of index `0`, at a minimum.
  have hcount := criticalCount_zero_ne_zero (I := 𝓘(ℝ, E)) (hf.contMDiff.of_le (by norm_cast))
  rw [criticalCount_def] at hcount
  obtain ⟨x, hx, hx0⟩ := nonempty_of_encard_ne_zero hcount
  -- The boundaries of degree `0` are a proper subspace: the augmentation vanishes on them, but
  -- not on the minimum `x`.
  let p : morseChainPiece 𝓘(ℝ, E) f 0 :=
    ⟨Finsupp.single ⟨x, hx⟩ 1, hx0 ▸ single_mem_morseChainPiece ⟨x, hx⟩ 1⟩
  have hne : LinearMap.range ((h.morseComplex hf).d 1 0).hom ≠ ⊤ := fun htop ↦ by
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1 htop p
    rw [morseComplex_d] at hy
    -- A chain of degree `1` is a pair of a chain and a proof of its degree.
    obtain ⟨y, hy1⟩ := y
    have h1 := h.morseAugmentation_morseBoundary hf y
    have h2 : h.morseBoundary hf y = Finsupp.single ⟨x, hx⟩ 1 := congrArg Subtype.val hy
    rw [h2] at h1
    simp [hx0] at h1
  have h0 := (h.morseComplex hf).finrank_X_zero
  have hlt := Submodule.finrank_lt hne
  omega

end IsAdaptedPseudoGradient.IsMorseSmale

end MorseComplex

end TauCeti
