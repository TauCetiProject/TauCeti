/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Geometry.Manifold.Morse.Generic.Inequalities
import Mathlib.Order.Interval.Set.Union
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.Topology.VectorBundle.Thom.TwistedHomology

/-!
# The Morse–Bott inequalities

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i a : S a → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), and let `r a` be the index
of the piece `S a`, the Morse index of `f` at its points. Let `K` be a field whose only unit is `1`,
that is `𝔽₂`. Write `bⱼ = dim Hⱼ(M; K)` and let

`cⱼ = ∑ₐ b_{j - r a}(S a; K)`,

the sum running over the pieces of index `r a ≤ j`: `cⱼ` is the coefficient of `tʲ` in the
Morse–Bott polynomial `∑ₐ t^{r a} P_{S a}(t)`. This file proves the **Morse–Bott inequalities**
for `b` and `c`: the weak inequalities `bⱼ ≤ cⱼ`, the strong inequalities
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, Euler's equality in degrees at least `dim M`, and the
polynomial identity `∑ⱼ cⱼ tʲ = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)` with `Q` having natural number
coefficients. For a Morse function every piece is a point of index the Morse index, so `cⱼ` is the
number of critical points of index `j`, and these are the Morse inequalities over `𝔽₂`.

Over `𝔽₂` no orientation of the negative normal bundles is needed. Over another field the
contribution of a piece is its homology twisted by the orientation local system of its negative
normal bundle. Over a field `K` in which `2` is invertible, such as `ℚ`, let `g a` be smooth fibre
metrics on the normal bundles of the pieces, let `ν⁻ a` be the negative normal bundle of `S a`
relative to `g a`, and let `o(ν⁻ a)` be its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`). This file proves the same inequalities
and identity for the counts

`c′ⱼ = ∑ₐ dim H_{j - r a}(S a; o(ν⁻ a) ⊗ K)`

of the orientation-twisted Betti numbers of the pieces
(`TauCeti.IsMorseBottFamily.twistedBettiNumber`), with no orientation of the negative normal
bundles. For instance, over `ℚ`, a critical circle of index `1` whose negative normal bundle is a
Möbius line has `dim H₀(S¹; o(ν⁻) ⊗ ℚ) = 0`
(`TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo`), so it contributes
nothing in degree `1`, where its untwisted Betti number `b₀(S¹) = 1` would contribute `t`.

The proof follows Bott. Cut the values of `f` at regular values `s 0 < ⋯ < s (N + 1)` so that each
band `f⁻¹[s j, s (j + 1)]` contains at most one critical value. The Morse–Bott inequalities are then
the inequalities of this filtration by sublevels
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff` and
its companions), once the homology of each band is computed:

* crossing a critical level `c` deformation retracts the upper sublevel onto the lower one with the
  negative disc bundles `D a ε` of the pieces on that level attached
  (`TauCeti.IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`), so the
  homology of the band is the direct sum of the homologies of the pairs `(D a ε, S a ε)`
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles`);
* each `(D a ε, S a ε)` has the homology of the Thom pair of the negative normal bundle `ν⁻ a` of
  `S a` (`SmoothEmbedding.IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap`),
  a vector bundle of rank `r a`.

So over any field `K`, `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim Hₙ(ν⁻ a, (ν⁻ a)₀; K)` over the pieces
on the only critical level `c ∈ (a, b)` of the band
(`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair`).
Over `𝔽₂` the homology of each Thom pair is that of `S a` shifted by `r a`
(`TauCeti.finrank_singularHomology_thomPair_of_subsingleton_units`), so
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r a}(S a; K)` over those pieces of index at most `n`
(`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum`). Only the twisted count
needs `2` invertible: the twisted Thom isomorphism
(`VectorBundleOrientationCover.finrank_singularHomology_thomPair_eq_finrank_twistedHomology`)
computes each Thom pair from the twisted homology of its piece instead, so
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim H_{n - r a}(S a; o(ν⁻ a) ⊗ K)`
(`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber`).
Summing over the bands counts every piece once.

The homology Thom isomorphisms (`TauCeti.homologyThomIso` and its twisted form) need the model
fibre `Fin r → ℝ` of the negative normal bundle in the universe of its base, so the manifolds, their
models and the coefficient field here live in `Type`.

## Main results

* `finrank_singularHomology_negativeDiscSpherePair`, in the namespace
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`: for a Morse–Bott submanifold of
  index `r`, `dim Hₙ(D_ε, S_ε; 𝔽₂) = b_{n - r}(S; 𝔽₂)` if `r ≤ n`, and `0` otherwise.
* `TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum`: the dimension of the
  homology of a band with a single critical value, over `𝔽₂`.
* `TauCeti.IsMorseBottFamily.bettiNumber_le_sum`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum` and
  `TauCeti.IsMorseBottFamily.exists_sum_range_monomial_sum_eq_add_mul`: the weak and strong
  Morse–Bott inequalities, Euler's equality and the Morse–Bott polynomial identity over `𝔽₂`.
* `TauCeti.IsMorseBottFamily.twistedBettiNumber`: the orientation-twisted Betti number
  `dim Hₚ(S a; o(ν⁻ a) ⊗ K)` of a piece.
* `TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber`: the
  dimension of the homology of a band with a single critical value, over a field in which `2` is
  invertible.
* `TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber` and
  `TauCeti.IsMorseBottFamily.exists_sum_range_monomial_sum_twistedBettiNumber_eq_add_mul`: the weak
  and strong Morse–Bott inequalities, Euler's equality and the Morse–Bott polynomial identity over
  a field in which `2` is invertible, with orientation-twisted Betti numbers.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12 (the Thom isomorphism and twisted coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set Topology
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

namespace TauCeti

/-! ### The contribution of one Morse–Bott submanifold -/

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E : Type} {H M E' H' P : Type*} {S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- The negative normal spaces of a Morse–Bott submanifold of constant index `r`, relative to a
smooth fibre metric, have continuous local frames of size `r`. -/
private theorem hasLocalSubbundleFrames_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  exact (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ hfs.contMDiffAt.of_le (by simp)) hdim g hr).hasLocalSubbundleFrames

/-- **The mod `2` homology of the negative disc bundle of a Morse–Bott submanifold.** Let `i` be a
nondegenerate critical submanifold of a smooth function `f`, with Morse index `r` at every point,
and let `g` be a smooth fibre metric on its normal bundle. Let `K` be a field whose only unit is
`1`, such as `ZMod 2`. For `ε > 0`, the negative disc bundle `D_ε` relative to `g`, taken
relative to its boundary `S_ε`, has `dim Hₙ(D_ε, S_ε; K) = b_{n - r}(S; K)` when `r ≤ n`, and `0`
when `n < r`: it has the homology of the Thom pair of the negative normal bundle, a vector bundle of
rank `r`, whose mod `2` homology is that of `S` shifted by `r`, with no orientation needed. -/
theorem finrank_singularHomology_negativeDiscSpherePair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) {ε : ℝ} (hε : 0 < ε) (K : Type) [Field K]
    [Subsingleton Kˣ] (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    finrank K ((h.negativeDiscSpherePair hn P g.toRiemannianMetric ε).singularHomology
        (ModuleCat.of K K) n : ModuleCat K) =
      if r ≤ n then bettiNumber K S (n - r) else 0 := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have hV := h.hasLocalSubbundleFrames_negativeNormalSpace hn hfs hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  -- The negative disc-sphere pair has the homology of the Thom pair of the negative normal bundle.
  rw [(@asIso _ _ _ _ _ (h.isIso_singularHomologyMap_negativeDiscThomPairMap hn
    g.toRiemannianMetric r hdim hV hε (ModuleCat.of K K) n)).toLinearEquiv.finrank_eq]
  exact finrank_singularHomology_thomPair_eq_ite _ _ (finrank_fin_fun ℝ) _
    (fun p ↦ finrank_singularHomology_thomPair_of_subsingleton_units _ _ p _
      (by rw [finrank_fin_fun])) n

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### The homology of a band with a single critical value -/

section Level

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsMorseBottFamily

section TwistedBettiNumber

variable (h : IsMorseBottFamily i f) {r : ι → ℕ} (K : Type) [Field K]
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))

/-- The **orientation-twisted Betti number** `dim Hₚ(S j; o(ν⁻ j) ⊗ K)` of a piece of a Morse–Bott
family: the dimension of the homology of the piece `S j` with coefficients in the orientation local
system `o(ν⁻ j) ⊗ K` of its negative normal bundle `ν⁻ j`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`). Here `ν⁻ j` is the vector bundle of rank
`r j` formed by the negative normal spaces relative to the fibre metric `g j`, with the local frames
`hV j`. This is the contribution of the piece to the Morse–Bott inequalities over a field in which
`2` is invertible
(`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber`). -/
def twistedBettiNumber (j : ι) (p : ℕ) : ℕ :=
  letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  letI := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  letI := (hV j).fiberBundle
  haveI := (hV j).vectorBundle
  finrank K (LocalCoefficientSystem.twistedHomology
    (VectorBundleOrientationCover.signLocalSystem (Fin (r j) → ℝ)
      (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) K ((Fintype.card_fin _).trans (finrank_fin_fun ℝ).symm)) p)

theorem twistedBettiNumber_def (j : ι) (p : ℕ) :
    h.twistedBettiNumber hn K hdim g hV j p =
      letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI := (hV j).fiberBundle
      haveI := (hV j).vectorBundle
      finrank K (LocalCoefficientSystem.twistedHomology
        (VectorBundleOrientationCover.signLocalSystem (Fin (r j) → ℝ)
          (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) K ((Fintype.card_fin _).trans (finrank_fin_fun ℝ).symm))
        p) :=
  (rfl)

end TwistedBettiNumber

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] (h : IsMorseBottFamily i f) {r : ι → ℕ}
  (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j) (K : Type) [Field K]

include h

variable (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)

include hr in
open scoped Classical in
/-- **The dimension of the homology of a critical band of a Morse–Bott function is the sum over the
pieces on its level of the dimensions of the homology of their Thom pairs.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, with Morse
index `r j` along the piece `S j`, let `g j` be smooth fibre metrics on the normal bundles of the
pieces, and let `ν⁻ j` be the negative normal bundle of `S j` relative to `g j`. Let `K` be a field
and let `a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim Hₙ(ν⁻ j, (ν⁻ j)₀; K)`, the sum running over the pieces on the
level `f = c`. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) :=
      fun j ↦ subbundleTopology (P j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j : {j // ∀ s, f (i j s) = c}, finrank K ((thomPair (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
        ).singularHomology (ModuleCat.of K K) n : ModuleCat K) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  -- The band has the homology of the sum of the Thom pairs of the pieces on the level `c`, a
  -- finite-dimensional space, so each summand is finite-dimensional.
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn hac hcb hcrit hdim g
    hr (ModuleCat.of K K) n
  let V (j : {j // ∀ s, f (i j s) = c}) : ModuleCat K := (thomPair (Fin (r j) → ℝ) fun s ↦
    (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
    ).singularHomology (ModuleCat.of K K) n
  let e' := e ≪≫ (biproduct.isoCoproduct V).symm
  have := finite_singularHomology_sublevelPair_of_criticalValue (ModuleCat.of K K) h.contMDiff
    h.contMDiff.continuous.isProperMap hac hcb hcrit n
  have := Module.Finite.equiv e'.toLinearEquiv
  have := ModuleCat.finite_of_finite_biproduct V
  rw [e'.toLinearEquiv.finrank_eq, ModuleCat.finrank_biproduct]

variable (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))

include hV in
open scoped Classical in
/-- **The homology of a critical band from the homology of the Thom pairs of its pieces.** Under
the hypotheses of
`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair`, with the
negative normal bundles `ν⁻ j` of ranks `r j` given by the local frames `hV j`, suppose
`dim H_{r j + p}(ν⁻ j, (ν⁻ j)₀; K) = d j p` for every piece `j` and every `p`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ d j (n - r j)`, the sum running over the pieces on the level
`f = c` of index at most `n`. -/
private theorem finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair (d : ι → ℕ → ℕ)
    (hd : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      ∀ j p, finrank K ((thomPair (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
        ).singularHomology (ModuleCat.of K K) (r j + p) : ModuleCat K) = d j p)
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, d j (n - r j) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ (j : ι) := (hV j).fiberBundle
  have (j : ι) := (hV j).vectorBundle
  -- The frames have size the dimension of the negative normal spaces, which is the index.
  have hr (j : ι) (s : S j) : manifoldMorseIndex I f (i j s) = r j := by
    rw [← (h.isNondegenerateCriticalSubmanifold j).finrank_negativeNormalSpace hn
      (g j).toRiemannianMetric, (hV j).finrank_eq, Fintype.card_fin]
  rw [h.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair hn hr K hdim g hac hcb hcrit
    n]
  -- Each Thom pair has the homology `d j` shifted by the index, and none below the index.
  have hV' (j : {j // ∀ s, f (i j s) = c}) := finrank_singularHomology_thomPair_eq_ite _ _
    (finrank_fin_fun ℝ) (d j) (hd j) n
  simp only [hV']
  rw [← Finset.filter_filter, Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun j ↦ by simp) fun j ↦ if r j ≤ n then d j (n - r j) else 0).symm

include hr in
open scoped Classical in
/-- **The mod `2` homology of a critical band of a Morse–Bott function.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece
`S j` having index `r j`, and let `K` be a field whose only unit is `1`, such as `ZMod 2`. Let
`a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`, the sum running over the pieces on the
level `f = c` of index at most `n`. If `c` is not a critical value, the sum is empty. -/
theorem finrank_singularHomology_sublevelPair_eq_sum [Subsingleton Kˣ] {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have (j : ι) : CompactSpace (S j) :=
    h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  -- Fix the model fibres of the normal bundles and smooth fibre metrics on them.
  have hdim (j : ι) : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j)))) =
      finrank ℝ E - finrank ℝ (E' j) := finrank_euclideanSpace_fin
  let g (j : ι) := ((i j).nonempty_contMDiffRiemannianMetric_normalSpace hn (hdim j)).some
  let _ (j : ι) := (i j).normalSpaceFiberBundle hn (hdim j)
  let _ (j : ι) := (i j).normalSpaceVectorBundle hn (hdim j)
  let _ (j : ι) := subbundleTopology (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j))))
    (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  have hV (j : ι) :=
    (h.isNondegenerateCriticalSubmanifold j).hasLocalSubbundleFrames_negativeNormalSpace hn
      h.contMDiff (hdim j) (g j) (hr j)
  let _ (j : ι) := (hV j).fiberBundle
  have (j : ι) := (hV j).vectorBundle
  -- Each Thom pair has the mod `2` homology of its piece shifted by the index.
  exact h.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair hn K hdim g hV
    (fun j ↦ bettiNumber K (S j))
    (fun j p ↦ finrank_singularHomology_thomPair_of_subsingleton_units _ _ p _
      (by rw [finrank_fin_fun]))
    hac hcb hcrit n

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [∀ j, FiniteDimensional ℝ (E' j)]
  [T2Space M] [SecondCountableTopology M] [∀ j, (J j).Boundaryless] in
open scoped Classical in
/-- **A cut of the values of a Morse–Bott function.** On a compact manifold the values of a
Morse–Bott function can be cut at values `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`, regular from `s 1` on, with
`s 0 < f ≤ s (N + 1)`, such that each band `[s j, s (j + 1)]` has at most one critical value, lying
strictly inside it. If every band with a single critical value `c` has homology of dimension
`∑ d j (n - r j)` in degree `n`, over the pieces on the level `c` with `r j ≤ n`, then summing over
the bands the dimensions of their homology counts the contribution `d p (n - r p)` of every piece
once. -/
private theorem exists_cut_sum_finrank_sublevelPair (d : ι → ℕ → ℕ)
    (hd : ∀ {a b c : ℝ} (hac : a < c) (hcb : c < b),
      (∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) → ∀ n,
        finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
          ModuleCat K) = ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, d j (n - r j)) :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1))) ∧
      ∀ n, ∑ j ∈ Finset.range (N + 1),
          finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
        ∑ p with r p ≤ n, d p (n - r p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨a, ha, ⟨q₀, hq₀⟩, ⟨q₁, hq₁⟩⟩ := exists_isCriticalBandCut_of_finite_image_criticalPoints
    h.contMDiff.continuous (h.finite_image_criticalPoints hn)
  -- Reindex the cut by `ℕ`, starting at `q₀`.
  let s (j : ℕ) : ℝ := a (q₀ + j)
  have hs : Monotone s := fun j k hjk ↦ ha.monotone (by simpa using hjk)
  have hband (j : ℕ) : ∃ c ∈ Ioo (s j) (s (j + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (s j) (s (j + 1)) → f x = c := by
    simpa [s, ← add_assoc] using (ha.isCriticalBand (q₀ + j)).exists_mem_Ioo_forall_eq
  choose c hc hcrit using hband
  set N := (max q₁ (q₀ + 1) - q₀ - 1).toNat
  have hs₀ (x : M) : s 0 < f x := by simpa [s] using hq₀ x
  have hsN (x : M) : f x ≤ s (N + 1) := (hq₁ x).trans (ha.monotone (by simp only [N]; omega))
  refine ⟨s, hs, N, hs₀, hsN, fun j _ ↦ ?_, fun n ↦ ?_⟩
  · -- A cut value is not a critical value, since the critical value of its band is inside it.
    refine isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hx, hxs⟩ ↦ ?_
    have := hcrit j x hx ⟨hxs ▸ hs j.le_succ, hxs.le⟩
    linarith [(hc j).2]
  rw [Finset.sum_congr rfl fun j _ ↦ hd (hc j).1 (hc j).2 (hcrit j) n]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- The piece `p` lies on the critical level of exactly one band, `j₀`.
  obtain ⟨t₀⟩ := h.nonempty p
  have hv := (h.isNondegenerateCriticalSubmanifold p).mem_criticalPoints t₀
  have hfp (t : S p) : f (i p t) = f (i p t₀) := h.subsingleton_image_range hn p
    (mem_image_of_mem f (mem_range_self t)) (mem_image_of_mem f (mem_range_self t₀))
  obtain ⟨j₀, hj₀, hlt, hle⟩ := mem_iUnion₂.1
    (Ioc_subset_biUnion_Ioc (N + 1) s ⟨hs₀ (i p t₀), hsN (i p t₀)⟩)
  have hcj₀ : f (i p t₀) = c j₀ := hcrit j₀ _ hv ⟨hlt.le, hle⟩
  have hlevel (j : ℕ) : (∀ t, f (i p t) = c j) ↔ j = j₀ := by
    refine ⟨fun hj ↦ ?_, fun hj t ↦ hj ▸ (hfp t).trans hcj₀⟩
    have hcj := (hj t₀).symm.trans hcj₀
    rcases Nat.lt_trichotomy j j₀ with hlt' | rfl | hlt'
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).2, (hc j₀).1]
    · rfl
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).1, (hc j₀).2]
  rw [Finset.sum_eq_single_of_mem j₀ hj₀
    fun j _ hj ↦ ite_eq_right fun hpj ↦ hj ((hlevel j).1 hpj.1)]
  simp [(hlevel j₀).2 rfl]

include hr in
/-- **The weak Morse–Bott inequalities over `𝔽₂`.** Let the family `i j : S j → M` exhibit `f` as
a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having index `r j`, and
let `K` be a field whose only unit is `1`, such as `ZMod 2`. Then
`bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces of index at most `n`. -/
theorem bettiNumber_le_sum [Subsingleton Kˣ] (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    fun hac hcb hcrit n ↦ h.finrank_singularHomology_sublevelPair_eq_sum hr K hac hcb hcrit n
  rw [bettiNumber_def, ← hsum]
  exact finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (ModuleCat.of K K) h.contMDiff
    hs hs₀ hsN hreg n

include hr in
/-- **The strong Morse–Bott inequalities over `𝔽₂`.** Let the family `i j : S j → M` exhibit `f`
as a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having index `r j`,
and let `K` be a field whose only unit is `1`, such as `ZMod 2`. Write `bₖ = bₖ(M; K)` and
`cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`, the coefficient of `tᵏ` in the
Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum [Subsingleton Kˣ] (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    fun hac hcb hcrit n ↦ h.finrank_singularHomology_sublevelPair_eq_sum hr K hac hcb hcrit n
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg n

include hr in
/-- **Euler's equality for a Morse–Bott function over `𝔽₂`.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum [Subsingleton Kˣ] {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    fun hac hcb hcrit n ↦ h.finrank_singularHomology_sublevelPair_eq_sum hr K hac hcb hcrit n
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn

include hr in
/-- **The Morse–Bott polynomial identity over `𝔽₂`.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients: the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)` exceeds the Poincaré
polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul [Subsingleton Kˣ] {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    fun hac hcb hcrit n ↦ h.finrank_singularHomology_sublevelPair_eq_sum hr K hac hcb hcrit n
  obtain ⟨Q, hQ, -⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn
  simp only [← bettiNumber_def, hsum] at hQ
  exact ⟨Q, hQ⟩

/-! ### Coefficients twisted by the orientations of the negative normal bundles -/

section Twisted

variable [Invertible (2 : K)]

open scoped Classical in
/-- **The homology of a critical band of a Morse–Bott function over a field in which `2` is
invertible.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact
boundaryless manifold, let `g j` be smooth fibre metrics on the normal bundles of the pieces, and
suppose the negative normal spaces of `S j` relative to `g j` have continuous local frames of size
`r j`, so that they form the negative normal bundle `ν⁻ j` of rank `r j`, the index of `S j`. Let
`K` be a field in which `2` is invertible, such as `ℚ`, and let `a < c < b` be such that `c` is the
only critical value of `f` in `[a, b]`. Then `dim Hₙ({f ≤ b}, {f ≤ a}; K)` is the sum of the
orientation-twisted Betti numbers `dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces on the level
`f = c` of index at most `n`. No orientation of the negative normal bundles is assumed. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, h.twistedBettiNumber hn K hdim g hV j (n - r j) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, FiberBundle (Fin (r j) → ℝ) fun s ↦
      (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    fun j ↦ (hV j).fiberBundle
  have (j : ι) : VectorBundle ℝ (Fin (r j) → ℝ) fun s ↦
      (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    (hV j).vectorBundle
  -- By the twisted Thom isomorphism, each Thom pair has the twisted homology of its piece shifted
  -- by the index.
  refine h.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair hn K hdim g hV
    (h.twistedBettiNumber hn K hdim g hV) (fun j p ↦ ?_) hac hcb hcrit n
  rw [twistedBettiNumber_def]
  exact VectorBundleOrientationCover.finrank_singularHomology_thomPair_eq_finrank_twistedHomology
    _ _ _ K (by rw [finrank_fin_fun])

/-- **The weak Morse–Bott inequalities over a field in which `2` is invertible.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, with
negative normal bundles `ν⁻ j` of ranks `r j` relative to smooth fibre metrics `g j`, and let `K` be
a field in which `2` is invertible, such as `ℚ`. Then
`bₙ(M; K) ≤ ∑ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`, the sum running over the pieces of index at most
`n`. No orientation of the negative normal bundles is assumed. -/
theorem bettiNumber_le_sum_twistedBettiNumber (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, h.twistedBettiNumber hn K hdim g hV p (n - r p) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    (h.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber hn K hdim g hV)
  rw [bettiNumber_def, ← hsum]
  exact finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (ModuleCat.of K K) h.contMDiff
    hs hs₀ hsN hreg n

/-- **The strong Morse–Bott inequalities over a field in which `2` is invertible.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, with
negative normal bundles `ν⁻ j` of ranks `r j` relative to smooth fibre metrics `g j`, and let `K` be
a field in which `2` is invertible, such as `ℚ`. Write `bₖ = bₖ(M; K)` and
`cₖ = ∑ dim H_{k - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces of index at most `k`, the coefficient of
`tᵏ` in the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t; o(ν⁻ j) ⊗ K)` of the twisted Poincaré
polynomials of the pieces. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. No orientation of the
negative normal bundles is assumed. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, h.twistedBettiNumber hn K hdim g hV p (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    (h.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber hn K hdim g hV)
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg n

/-- **Euler's equality for a Morse–Bott function over a field in which `2` is invertible.** Under
the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber`, for
every `n` at least the dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, h.twistedBettiNumber hn K hdim g hV p (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    (h.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber hn K hdim g hV)
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn

/-- **The Morse–Bott polynomial identity over a field in which `2` is invertible.** Under the
hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber`, for
every `n` at least the dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a
polynomial `Q` with natural number coefficients: the Morse–Bott polynomial
`∑ⱼ t^{r j} P_{S j}(t; o(ν⁻ j) ⊗ K)` exceeds the Poincaré polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_twistedBettiNumber_eq_add_mul {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, h.twistedBettiNumber hn K hdim g hV p (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair K _
    (h.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber hn K hdim g hV)
  obtain ⟨Q, hQ, -⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn
  simp only [← bettiNumber_def, hsum] at hQ
  exact ⟨Q, hQ⟩

end Twisted

end IsMorseBottFamily

end Level

end TauCeti
