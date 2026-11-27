/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Pair
public import TauCeti.Geometry.Manifold.TangentCone.Prod

/-!
# The Morse–Smale condition for a one-parameter family of pairs

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M` of dimension `n`, with
pseudo-gradients `X₀` and `X₁` adapted to them, and let `Φ : ℝ → M → M` be a family of maps. For
points `a` and `b`, the **parametrized intersection**
(`TauCeti.IsAdaptedPseudoGradient.parametrizedPairSlice`) is the set of pairs `(λ, y)` with
`λ ∈ [0, 1]`, `y ∈ W^u_{X₀}(a)` and `Φ λ y ∈ W^s_{X₁}(b)`. When each `Φ λ` is a diffeomorphism,
`(Φ λ)⁻¹ (W^s_{X₁}(b))` is the stable manifold of `(Φ λ)⁻¹ b` for the pullback `(Φ λ)^* X₁`, so
its slice at `λ` is an intersection for the pair `(X₀, (Φ λ)^* X₁)`, as for a single continuation;
for the transition maps of a
one-parameter family of continuations, the parametrized intersections record the trajectories that
the digon homotopy between the two continuations counts
(`TauCeti.IsContinuationFamily.eventually_bijOn_morseDigonSlice`).

The family is **Morse–Smale** (`TauCeti.IsAdaptedPseudoGradient.IsParametrizedMorseSmalePair`)
when the map `(λ, y) ↦ Φ λ y`, restricted to `ℝ × W^u_{X₀}(a)`, is transverse to `W^s_{X₁}(b)` at
every point of the parametrized intersection: the image of `ℝ × T_y W^u_{X₀}(a)` under its
derivative and the tangent space of `W^s_{X₁}(b)` span the tangent space of `M`. This is the
transversality condition of a one-parameter family. The pairs `(X₀, (Φ λ)^* X₁)` need not be
Morse–Smale, since the derivative in the parameter direction contributes, and the parametrized
intersection has expected dimension `ind a - ind b + 1`, one more than for a single pair. For a
Morse–Smale family, with `(λ, y) ↦ Φ λ y` differentiable, and Morse–Smale pseudo-gradients `X₀` and
`X₁`:

* **Index bound.** The parametrized intersection is empty unless `ind b ≤ ind a + 1`
  (`IsParametrizedMorseSmalePair.manifoldMorseIndex_le_add_one`,
  `IsParametrizedMorseSmalePair.parametrizedPairSlice_eq_empty`).
* **Rigidity.** When `ind b = ind a + 1` it is discrete
  (`IsParametrizedMorseSmalePair.isDiscrete_parametrizedPairSlice`). At an accumulation point the
  set would have a nonzero tangent vector (`TauCeti.mtangentConeAt_nonempty_of_properSpace`),
  lying in `ℝ × T_y W^u_{X₀}(a)` and carried by the derivative into `T W^s_{X₁}(b)`. But
  transversality makes the derivative followed by the quotient by `T W^s_{X₁}(b)` onto, from a
  space of dimension `1 + ind a` to one of dimension `ind b`, hence injective when the two agree.
* **Breaking.** A limit of points of the parametrized intersection from `p` to `q` lies in the
  parametrized intersection from `a` to `b`, where `a = p` or `ind a < ind p`, and `b = q` or
  `ind q < ind b` (`exists_mem_parametrizedPairSlice_of_mem_closure`).
* **Finiteness.** Hence when `ind q = ind p + 1` the parametrized intersection is closed in the
  compact space `[0, 1] × M`, and finite
  (`IsParametrizedMorseSmalePair.finite_parametrizedPairSlice`).
* **One-dimensional ends.** When `ind q = ind p`, the closure of the parametrized intersection adds
  only once-broken configurations: a trajectory of `X₀` from `p` to a critical point `a` with
  `ind a + 1 = ind q`, followed by a point of the parametrized intersection from `a` to `q`, or a
  point of the parametrized intersection from `p` to a critical point `b` with `ind b = ind p + 1`,
  followed by a trajectory of `X₁` from `b` to `q`
  (`IsParametrizedMorseSmalePair.closure_parametrizedPairSlice_subset`).

For the transition maps of a family of continuations, the finiteness is that of the rigid digon
trajectories, so that the coefficients of the mod-two digon homotopy count finite sets.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `parametrizedPairSlice`: the parametrized intersection of `W^u_{X₀}(a)` with the preimages of
  `W^s_{X₁}(b)` under `Φ λ`, `λ ∈ [0, 1]`.
* `IsParametrizedMorseSmalePair`: the Morse–Smale condition for the family.
* `IsParametrizedMorseSmalePair.manifoldMorseIndex_le_add_one` and
  `IsParametrizedMorseSmalePair.parametrizedPairSlice_eq_empty`: the index rises by at most one.
* `IsParametrizedMorseSmalePair.isDiscrete_parametrizedPairSlice`: rigid parametrized intersections
  are discrete.
* `exists_mem_parametrizedPairSlice_of_mem_closure`: limits of points of a parametrized
  intersection break.
* `IsParametrizedMorseSmalePair.isClosed_parametrizedPairSlice` and
  `IsParametrizedMorseSmalePair.finite_parametrizedPairSlice`: rigid parametrized intersections are
  closed and finite.
* `IsParametrizedMorseSmalePair.closure_parametrizedPairSlice_subset`: the limits of points of a
  one-dimensional parametrized intersection break at most once.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (homotopic continuations, and the transversality of the
  one-parameter family, under which the trajectories of index `-1` appear at isolated parameters).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {Φ : ℝ → M → M} {a b p q : M}
  {z : ℝ × M}

namespace IsAdaptedPseudoGradient

/-- **The parametrized intersection** of the unstable manifold of `a` for `X₀` with the preimages
of the stable manifold of `b` for `X₁` under a family of maps `Φ λ`: the pairs `(λ, y)` with
`λ ∈ [0, 1]`, `y ∈ W^u_{X₀}(a)` and `Φ λ y ∈ W^s_{X₁}(b)`. -/
def parametrizedPairSlice (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (Φ : ℝ → M → M) (a b : M) : Set (ℝ × M) :=
  {z | z.1 ∈ Icc 0 1 ∧ z.2 ∈ hX₀.flow.unstableSet a ∧ Φ z.1 z.2 ∈ hX₁.flow.stableSet b}

/-- Membership in a parametrized intersection. -/
@[simp]
theorem mem_parametrizedPairSlice {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} :
    z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b ↔
      z.1 ∈ Icc 0 1 ∧ z.2 ∈ hX₀.flow.unstableSet a ∧ Φ z.1 z.2 ∈ hX₁.flow.stableSet b :=
  Iff.rfl

/-- **The Morse–Smale condition for a one-parameter family of pairs.** At every point `z = (λ, y)`
of every parametrized intersection `hX₀.parametrizedPairSlice hX₁ Φ a b`, the derivative of
`(λ, y) ↦ Φ λ y` carries `ℝ × T_y W^u_{X₀}(a)` onto a subspace which, together with the tangent
space of `W^s_{X₁}(b)` at `Φ λ y`, spans the tangent space of `M`. -/
def IsParametrizedMorseSmalePair (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (Φ : ℝ → M → M) : Prop :=
  ∀ ⦃a b : M⦄ ⦃z : ℝ × M⦄, z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b →
    (((⊤ : Submodule ℝ ℝ).prod
        (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) z.2))).map
          (mfderiv (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z).toLinearMap : Submodule ℝ E) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) (Φ z.1 z.2)) = ⊤

/-- The unfolding of `TauCeti.IsAdaptedPseudoGradient.IsParametrizedMorseSmalePair`. -/
theorem isParametrizedMorseSmalePair_iff {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} :
    IsParametrizedMorseSmalePair hX₀ hX₁ Φ ↔
      ∀ ⦃a b : M⦄ ⦃z : ℝ × M⦄, z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b →
        (((⊤ : Submodule ℝ ℝ).prod
            (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) z.2))).map
              (mfderiv (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z).toLinearMap : Submodule ℝ E) ⊔
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) (Φ z.1 z.2)) = ⊤ :=
  Iff.rfl

/-- A limit `z` of points of the parametrized intersection from `p` to `q` has its point in the
closure of `W^u_{X₀}(p)` and its image under `(λ, y) ↦ Φ λ y` in the closure of `W^s_{X₁}(q)`. -/
private theorem mem_closure_of_mem_closure_parametrizedPairSlice
    {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
    (hΦ : Continuous (uncurry Φ)) (hz : z ∈ closure (hX₀.parametrizedPairSlice hX₁ Φ p q)) :
    z.2 ∈ closure (hX₀.flow.unstableSet p) ∧ uncurry Φ z ∈ closure (hX₁.flow.stableSet q) :=
  ⟨map_mem_closure continuous_snd hz fun w (hw : w ∈ hX₀.parametrizedPairSlice hX₁ Φ p q) ↦
      hw.2.1,
    map_mem_closure hΦ hz fun w (hw : w ∈ hX₀.parametrizedPairSlice hX₁ Φ p q) ↦ hw.2.2⟩

/-- **Limits of points of a parametrized intersection break.** Let `X₀` and `X₁` be Morse–Smale,
and `(λ, y) ↦ Φ λ y` continuous. A limit `z` of points of the parametrized intersection from `p` to
`q` lies in the parametrized intersection from `a` to `b` for points `a` and `b` with `a = p` or
`ind a < ind p`, and `b = q` or `ind q < ind b`, the indices being taken for `f₀` at `a`, `p` and
for `f₁` at `b`, `q`. -/
theorem exists_mem_parametrizedPairSlice_of_mem_closure {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hΦ : Continuous (uncurry Φ))
    (hz : z ∈ closure (hX₀.parametrizedPairSlice hX₁ Φ p q)) :
    ∃ a b, z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b ∧
      (a = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f₀ a < manifoldMorseIndex 𝓘(ℝ, E) f₀ p) ∧
      (b = q ∨ manifoldMorseIndex 𝓘(ℝ, E) f₁ q < manifoldMorseIndex 𝓘(ℝ, E) f₁ b) := by
  -- The parameter stays in `[0, 1]`, the point in the closure of `W^u_{X₀}(p)`, and its image in
  -- the closure of `W^s_{X₁}(q)`.
  have hz₁ : z.1 ∈ Icc 0 1 :=
    closure_minimal (fun w (hw : w ∈ hX₀.parametrizedPairSlice hX₁ Φ p q) ↦ hw.1)
      (isClosed_Icc.preimage continuous_fst) hz
  obtain ⟨hzu, hzs⟩ := mem_closure_of_mem_closure_parametrizedPairSlice hΦ hz
  -- The backward orbit of `z.2` for `X₀` and the forward orbit of `Φ z.1 z.2` for `X₁` converge
  -- to critical points.
  obtain ⟨a, -, hya⟩ := hX₀.exists_tendsto_atBot z.2
  obtain ⟨b, -, hyb⟩ := hX₁.exists_tendsto_atTop (Φ z.1 z.2)
  have hya : z.2 ∈ hX₀.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : Φ z.1 z.2 ∈ hX₁.flow.stableSet b := Flow.mem_stableSet.2 hyb
  refine ⟨a, b, ⟨hz₁, hya, hyb⟩, or_iff_not_imp_left.2 fun hap ↦ ?_,
    or_iff_not_imp_left.2 fun hbq ↦ ?_⟩
  · exact h₀.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf₀ hap
      ⟨z.2, hzu, hya⟩
  · exact h₁.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf₁ hbq
      ⟨_, hzs, hyb⟩

namespace IsParametrizedMorseSmalePair

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}

/-- **The pointwise elimination rule for `IsParametrizedMorseSmalePair`.** At a point `z` of a
parametrized intersection from `a` to `b`, the derivative of `(λ, y) ↦ Φ λ y` carries
`ℝ × T W^u_{X₀}(a)` onto a subspace which, with the tangent space of `W^s_{X₁}(b)`, spans the
tangent space of `M`. -/
theorem map_sup_span_mtangentConeAt_eq_top (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hz : z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b) :
    (((⊤ : Submodule ℝ ℝ).prod
        (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) z.2))).map
          (mfderiv (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z).toLinearMap : Submodule ℝ E) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) (Φ z.1 z.2)) = ⊤ :=
  h hz

/-- The space `ℝ × T_y W^u(a)` has dimension `1 + ind a`. -/
private theorem finrank_prod_span_mtangentConeAt_unstableSet (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {y : M} (hy : y ∈ hX₀.flow.unstableSet a) :
    Module.finrank ℝ ((⊤ : Submodule ℝ ℝ).prod
        (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y))) =
      1 + manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_top,
    Module.finrank_self, hX₀.finrank_span_mtangentConeAt_unstableSet hf₀ hy]

/-- The quotient of `E` by `T_y W^s(b)` has dimension `ind b`. -/
private theorem finrank_quotient_span_mtangentConeAt_stableSet {y : M}
    (hy : y ∈ hX₁.flow.stableSet b) :
    Module.finrank ℝ (E ⧸ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y)) =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b := by
  have hS := hX₁.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hy
  have hQ := Submodule.finrank_quotient_add_finrank
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y))
  omega

/-- A linear map restricted to `W`, followed by the quotient by `S`, is onto when the image of `W`
and `S` span the target. -/
private theorem surjective_mkQ_comp_comp_subtype {R F G : Type*} [Ring R] [AddCommGroup F]
    [Module R F] [AddCommGroup G] [Module R G] {d : F →ₗ[R] G} {W : Submodule R F}
    {S : Submodule R G}
    (h : W.map d ⊔ S = ⊤) : Surjective (S.mkQ ∘ₗ d ∘ₗ W.subtype) :=
  LinearMap.range_eq_top.1 <| by
    simpa [LinearMap.range_comp, Submodule.map_mkQ_eq_top, sup_comm] using h

/-- Transversality makes the derivative of `(λ, y) ↦ Φ λ y` on `ℝ × T W^u(a)`, followed by the
quotient by `T W^s(b)`, onto. -/
private theorem surjective_mkQ_comp_mfderiv_comp_subtype
    (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hz : z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b) :
    Surjective
      ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) (Φ z.1 z.2))).mkQ ∘ₗ
        ((mfderiv (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z).toLinearMap : ℝ × E →ₗ[ℝ] E) ∘ₗ
        ((⊤ : Submodule ℝ ℝ).prod
          (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) z.2))).subtype) :=
  surjective_mkQ_comp_comp_subtype (h.map_sup_span_mtangentConeAt_eq_top hz)

/-- **The index rises by at most one along a Morse–Smale family.** If the parametrized
intersection from `a` to `b` is nonempty, then the index of `b` for `f₁` is at most the index of
`a` for `f₀` plus one. -/
theorem manifoldMorseIndex_le_add_one (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hz : z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b ≤ manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 := by
  -- The quotient of `E` by `T W^s(b)`, of dimension `ind b`, is the image of `ℝ × T W^u(a)`, of
  -- dimension `1 + ind a`.
  have hle := LinearMap.finrank_le_finrank_of_surjective
    (surjective_mkQ_comp_mfderiv_comp_subtype h hz)
  rw [finrank_quotient_span_mtangentConeAt_stableSet hz.2.2,
    finrank_prod_span_mtangentConeAt_unstableSet hf₀ hz.2.1] at hle
  omega

/-- **The parametrized intersection is empty when the index rises by more than one.** -/
theorem parametrizedPairSlice_eq_empty (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hab : manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 < manifoldMorseIndex 𝓘(ℝ, E) f₁ b) :
    hX₀.parametrizedPairSlice hX₁ Φ a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hz ↦ (h.manifoldMorseIndex_le_add_one hf₀ hz).not_gt hab

/-- **Rigid points of a Morse–Smale family are isolated.** If the index of `b` for `f₁` is at least
the index of `a` for `f₀` plus one, and `(λ, y) ↦ Φ λ y` is differentiable at a point `z` of the
parametrized intersection from `a` to `b`, then `z` is not an accumulation point of that
intersection. -/
theorem not_accPt_parametrizedPairSlice (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ b)
    (hz : z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b)
    (hΦ : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z) :
    ¬AccPt z (Filter.principal (hX₀.parametrizedPairSlice hX₁ Φ a b)) := by
  intro hacc
  set D := hX₀.parametrizedPairSlice hX₁ Φ a b
  let d : ℝ × E →ₗ[ℝ] E := (mfderiv (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z).toLinearMap
  set W := (⊤ : Submodule ℝ ℝ).prod
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) z.2))
  set S := Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) (Φ z.1 z.2))
  -- A nonzero tangent vector `v` of `D` at `z` lies in `ℝ × T W^u(a)` and is carried into
  -- `T W^s(b)`.
  obtain ⟨v, hv, hv0⟩ := mtangentConeAt_nonempty_of_properSpace (I := 𝓘(ℝ).prod 𝓘(ℝ, E)) hacc
  have hvW : v ∈ W := by
    have hD : D ⊆ univ ×ˢ hX₀.flow.unstableSet a := fun w hw ↦ ⟨trivial, hw.2.1⟩
    exact Submodule.mem_prod.2 ⟨trivial,
      Submodule.subset_span (mtangentConeAt_prod_subset (mtangentConeAt_mono hD z hv)).2⟩
  have hvS : d v ∈ S := by
    have hD : uncurry Φ '' D ⊆ hX₁.flow.stableSet b := by
      rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2
    exact Submodule.subset_span (mtangentConeAt_mono hD _
      (hΦ.hasMFDerivAt.hasMFDerivWithinAt.mapsTo_mtangentConeAt hv))
  -- The derivative followed by the quotient by `T W^s(b)` is onto from `W`, by transversality, and
  -- the two spaces have the same dimension, so it is injective.
  let g : W →ₗ[ℝ] E ⧸ S := S.mkQ ∘ₗ d ∘ₗ W.subtype
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (E ⧸ S) := by
    have hle := h.manifoldMorseIndex_le_add_one hf₀ hz
    rw [finrank_prod_span_mtangentConeAt_unstableSet hf₀ hz.2.1,
      finrank_quotient_span_mtangentConeAt_stableSet hz.2.2]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    (surjective_mkQ_comp_mfderiv_comp_subtype h hz)
  have hgv : g ⟨v, hvW⟩ = 0 := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hvS
  exact hv0 (congrArg Subtype.val (hinj (hgv.trans (map_zero g).symm)))

/-- **Rigid parametrized intersections are discrete.** For a Morse–Smale family with
`(λ, y) ↦ Φ λ y` differentiable at the points of the parametrized intersection from `a` to `b`, if
the index of `b` for `f₁` is at least the index of `a` for `f₀` plus one, then this parametrized
intersection is discrete. By `parametrizedPairSlice_eq_empty` it is empty unless the index rises by
exactly one. -/
theorem isDiscrete_parametrizedPairSlice (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hΦ : ∀ z ∈ hX₀.parametrizedPairSlice hX₁ Φ a b,
      MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ) z)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ b) :
    IsDiscrete (hX₀.parametrizedPairSlice hX₁ Φ a b) :=
  isDiscrete_iff_discreteTopology.2 <| discreteTopology_of_noAccPts fun z hz ↦
    h.not_accPt_parametrizedPairSlice hf₀ hind hz (hΦ z hz)

/-- **Rigid parametrized intersections are closed.** For a Morse–Smale family of Morse–Smale
pseudo-gradients, with `(λ, y) ↦ Φ λ y` continuous, if the index of `q` for `f₁` is at least the
index of `p` for `f₀` plus one, then the parametrized intersection from `p` to `q` is closed. -/
theorem isClosed_parametrizedPairSlice (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hΦ : Continuous (uncurry Φ))
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    IsClosed (hX₀.parametrizedPairSlice hX₁ Φ p q) := by
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  -- A limit can break neither at the source nor at the target: either would make the index rise by
  -- more than one between its ends.
  obtain ⟨a, b, hz', hap, hbq⟩ :=
    exists_mem_parametrizedPairSlice_of_mem_closure h₀ h₁ hf₀ hf₁ hΦ hz
  have hba := h.manifoldMorseIndex_le_add_one hf₀ hz'
  obtain rfl : a = p := hap.resolve_right fun hlt ↦ by rcases hbq with rfl | hbq <;> omega
  obtain rfl : b = q := hbq.resolve_right fun hlt ↦ by omega
  exact hz'

/-- **Rigid parametrized intersections are finite.** For a Morse–Smale family of Morse–Smale
pseudo-gradients, with `(λ, y) ↦ Φ λ y` differentiable, if the index of `q` for `f₁` is at least
the index of `p` for `f₀` plus one, then the parametrized intersection from `p` to `q` is finite.
For the transition maps of a family of continuations, these are the trajectories of index `-1`
counted by the digon homotopy. -/
theorem finite_parametrizedPairSlice (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hΦ : MDifferentiable (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (uncurry Φ))
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    (hX₀.parametrizedPairSlice hX₁ Φ p q).Finite :=
  ((isCompact_Icc.prod isCompact_univ).of_isClosed_subset
    (h.isClosed_parametrizedPairSlice h₀ h₁ hf₀ hf₁ hΦ.continuous hind)
    fun _ hz ↦ ⟨hz.1, trivial⟩).finite
      (h.isDiscrete_parametrizedPairSlice hf₀ (fun z _ ↦ hΦ z) hind)

/-- **The ends of one-dimensional parametrized intersections are once broken.** Let the family be
Morse–Smale, `X₀` and `X₁` Morse–Smale, `(λ, y) ↦ Φ λ y` continuous, and `ind p = ind q`, for `f₀`
at `p` and `f₁` at `q`. Besides the parametrized intersection from `p` to `q` itself, whose points
with `λ = 0` or `λ = 1` lie on its edges, its closure meets only

* the parametrized intersections from `a` to `q`, for the points `a` with `ind a + 1 = ind q`
  reached by a trajectory of `X₀` from `p`, and
* the parametrized intersections from `p` to `b`, for the points `b` with `ind b = ind p + 1` from
  which a trajectory of `X₁` runs to `q`.

For the transition maps of a family of continuations, these are the digon trajectories broken at
the source and at the target. -/
theorem closure_parametrizedPairSlice_subset (h : IsParametrizedMorseSmalePair hX₀ hX₁ Φ)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hΦ : Continuous (uncurry Φ))
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    closure (hX₀.parametrizedPairSlice hX₁ Φ p q) ⊆
      hX₀.parametrizedPairSlice hX₁ Φ p q ∪
        (⋃ a ∈ {a | manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q ∧
            (hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a).Nonempty},
          hX₀.parametrizedPairSlice hX₁ Φ a q) ∪
        (⋃ b ∈ {b | manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 ∧
            (hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet q).Nonempty},
          hX₀.parametrizedPairSlice hX₁ Φ p b) := by
  intro z hz
  obtain ⟨a, b, hz', hap, hbq⟩ :=
    exists_mem_parametrizedPairSlice_of_mem_closure h₀ h₁ hf₀ hf₁ hΦ hz
  have hba := h.manifoldMorseIndex_le_add_one hf₀ hz'
  obtain ⟨hzu, hzs⟩ := mem_closure_of_mem_closure_parametrizedPairSlice hΦ hz
  simp only [mem_union, mem_iUnion₂, mem_ofPred_eq, exists_prop]
  -- At most one end breaks, since the index can only drop at the source and rise at the target,
  -- and it rises by at most one along the family.
  rcases hap with rfl | hap
  · rcases hbq with rfl | hbq
    · exact Or.inl (Or.inl hz')
    · have hbq' : b ≠ q := by rintro rfl; omega
      refine Or.inr ⟨b, ⟨by omega, ?_⟩, hz'⟩
      exact h₁.nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet
        hf₁ hbq' (by omega) ⟨_, hzs, hz'.2.2⟩
  · rcases hbq with rfl | hbq
    · have hap' : a ≠ p := by rintro rfl; omega
      refine Or.inl (Or.inr ⟨a, ⟨by omega, ?_⟩, hz'⟩)
      exact h₀.nonempty_unstableSet_inter_stableSet_of_mem_closure_unstableSet_inter_unstableSet
        hf₀ hap' (by omega) ⟨z.2, hzu, hz'.2.1⟩
    · omega

end IsParametrizedMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti
