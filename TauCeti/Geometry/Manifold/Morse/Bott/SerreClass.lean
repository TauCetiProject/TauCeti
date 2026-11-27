/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.TwistedHomology
import TauCeti.CategoryTheory.ObjectProperty.Extensions

/-!
# The homology of a Morse–Bott manifold modulo a Serre class

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i j : S j → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), let `g j` be smooth fibre
metrics on their normal bundles, and let the negative normal spaces relative to `g j` form the
negative normal bundle `ν⁻ j`, of rank `r j`, the index of the piece, with orientation local system
`o(ν⁻ j)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). Let `K` be any commutative
ring, for instance `ℤ`, and let `Q` be a Serre class of `K`-modules: a class containing `0` and
closed under submodules, quotients and extensions, such as the zero modules, the torsion abelian
groups, or the abelian groups killed by a power of a fixed integer.

If for every piece of index `r j ≤ n` the twisted homology `H_{n - r j}(S j; o(ν⁻ j) ⊗ K)` lies in
`Q`, then so does `Hₙ(M; K)`
(`TauCeti.IsMorseBottFamily.prop_singularHomology_of_forall_prop_twistedHomology`). In particular
`Hₙ(M; K) = 0` when all these twisted homology groups vanish
(`TauCeti.IsMorseBottFamily.isZero_singularHomology_of_forall_isZero_twistedHomology`). No
orientation of the negative normal bundles is assumed and `2` need not be invertible in `K`.

This is the integral counterpart of the weak Morse–Bott inequalities over a field
(`TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`), which bound `dim Hₙ(M; K)` by
the dimensions of the same twisted homology groups. Over `ℤ` dimensions are not available, and the
finite filtration of `M` by sublevels instead controls `Hₙ(M; ℤ)` modulo a class of abelian groups:
cut the values of `f` so that each band `f⁻¹[s j, s (j + 1)]` contains one critical value
(`TauCeti.exists_monotone_isCriticalBand_of_finite_image_criticalPoints`). By Bott's theorem the
relative homology across that level is the coproduct of the twisted homology groups of its pieces,
shifted by their indices
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology`),
which lies in `Q`. The long exact sequences of the triples of sublevels then put `Hₙ(M; K)` in `Q`
(`TauCeti.prop_singularHomology_of_forall_prop_sublevelPair`).

The twist matters. On the real projective plane, the function
`[x : y : z] ↦ (x² + y²) / (x² + y² + z²)` has a minimum at `[0 : 0 : 1]` and a critical circle of
index `1` whose negative normal bundle is a Möbius line, so that `H₀(S¹; o(ν⁻)) ≅ ℤ/2` and
`H₁(S¹; o(ν⁻)) = 0`. In degree `1` the pieces contribute only the torsion group `ℤ/2`, and indeed
`H₁(ℝℙ²; ℤ) ≅ ℤ/2` is torsion; the untwisted homology `H₀(S¹; ℤ) ≅ ℤ` of the circle is not. In
degree `2` they contribute `H₁(S¹; o(ν⁻)) = 0` and `H₂(pt; ℤ) = 0`, so the vanishing statement
gives `H₂(ℝℙ²; ℤ) = 0`, which the untwisted group `H₁(S¹; ℤ) ≅ ℤ` would not.

## Main results

In the namespace `TauCeti.IsMorseBottFamily`:

* `prop_singularHomology_of_forall_prop_twistedHomology`: `Hₙ(M; K)` lies in a Serre class as
  soon as the twisted homology of every piece in the complementary degree does.
* `isZero_singularHomology_of_forall_isZero_twistedHomology`: `Hₙ(M; K)` vanishes as soon as the
  twisted homology of every piece in the complementary degree does.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set
open TauCeti.LocalCoefficientSystem TauCeti.VectorBundleOrientationCover
open scoped ContDiff Manifold

namespace TauCeti.IsMorseBottFamily

universe u

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SecondCountableTopology M] {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type u}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)]
  [∀ j, FiniteDimensional ℝ (P j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  (hn : (∞ : ℕ∞ω) ≠ 0) (h : IsMorseBottFamily i f)
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
  {κ : ι → Type u} [∀ j, Fintype (κ j)]
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (κ j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
  (K : Type u) [CommRing K]

/-- **The homology of a Morse–Bott manifold modulo a Serre class.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, let `g j`
be smooth fibre metrics on the normal bundles of the pieces, and let the negative normal spaces
relative to `g j` have continuous local frames indexed by a finite type `κ j`, so that they form the
negative normal bundle `ν⁻ j` of rank `|κ j|`, the index of the piece. Let `K` be a commutative
ring, for instance `ℤ`, and `Q` a Serre class of `K`-modules, for instance the torsion abelian
groups. If `H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K)` lies in `Q` for every piece of index `|κ j| ≤ n`, where
`o(ν⁻ j)` is the orientation local system of `ν⁻ j`, then `Hₙ(M; K)` lies in `Q`. No orientation
of the bundles `ν⁻ j` is assumed. -/
theorem prop_singularHomology_of_forall_prop_twistedHomology
    (Q : ObjectProperty (ModuleCat.{u} K)) [Q.IsSerreClass] (n : ℕ)
    (hQ : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      haveI : ∀ j, VectorBundle ℝ (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).vectorBundle
      ∀ j, Fintype.card (κ j) ≤ n → Q (twistedHomology (signLocalSystem (κ j → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) K
        ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
        (n - Fintype.card (κ j)))) :
    Q (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} K) n).obj
      (ModuleCat.of K K)).obj (TopCat.of M)) := by
  -- Cut the values of `f` into bands with one critical value each.
  obtain ⟨s, N, hs, hs₀, hsN, hcut, -⟩ :=
    exists_monotone_isCriticalBand_of_finite_image_criticalPoints h.contMDiff.continuous
      (h.finite_image_criticalPoints hn)
  refine prop_singularHomology_of_forall_prop_sublevelPair (ModuleCat.of K K) Q hs hs₀ hsN n
    fun j _ ↦ ?_
  -- The homology across the critical level `c` of a band is the coproduct of the twisted
  -- homologies of the pieces on that level, each of which lies in `Q`.
  obtain ⟨c, hc, hcrit⟩ := (hcut j).exists_mem_Ioo_forall_eq
  have := h.finite_subtype_of_forall_apply_eq (hcut j).isCompact (Ioo_subset_Icc_self hc)
    (p := fun j' ↦ (∀ t, f (i j' t) = c) ∧ Fintype.card (κ j') ≤ n) fun _ ↦ And.left
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology hn hc.1 hc.2
    (hcut j).isCompact hcrit hdim g hV K n
  exact Q.prop_of_iso e.symm (Q.prop_coproduct fun j' ↦ hQ j'.val j'.property.2)

/-- **Vanishing of the homology of a Morse–Bott manifold.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.prop_singularHomology_of_forall_prop_twistedHomology`, if
`H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K) = 0` for every piece of index `|κ j| ≤ n`, then
`Hₙ(M; K) = 0`, over every commutative ring `K`, `ℤ` included. -/
theorem isZero_singularHomology_of_forall_isZero_twistedHomology (n : ℕ)
    (hz : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      haveI : ∀ j, VectorBundle ℝ (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).vectorBundle
      ∀ j, Fintype.card (κ j) ≤ n → IsZero (twistedHomology (signLocalSystem (κ j → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) K
        ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
        (n - Fintype.card (κ j)))) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} K) n).obj
      (ModuleCat.of K K)).obj (TopCat.of M)) :=
  h.prop_singularHomology_of_forall_prop_twistedHomology hn hdim g hV K IsZero n hz

end TauCeti.IsMorseBottFamily
