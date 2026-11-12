/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension

/-!
# Manifolds abundant with 2-spheres

Let `Q` be a closed `n`-manifold, and let `ev : Map(S², Q) → Q` be evaluation at the north pole
of the sphere, with fibre the based mapping space `Map_*(S², Q) = Ω²Q` and with the section
`σ : Q → Map(S², Q)` by constant spheres. Barraud, Damian, Humilière and Oancea call `Q`
**abundant with 2-spheres** if some class `α ∈ Hₖ(Map(S², Q))`

1. lives over the fundamental class of `Q`, that is, its image under the shriek map
   `j_! : Hₖ(Map(S², Q)) → Hₖ₋ₙ(Ω²Q)` of the inclusion `j` of the base point is nonzero, and
2. either has degree `k > n`, or has degree `k = n` and `j_! α` stays nonzero in the reduced
   homology `H₀(Ω²Q, pt)`

(their Definition 6.11). Their Theorem 6.12 (Theorem H) shows that the π₁-sensitive
Hofer–Zehnder capacity of the unit codisc bundle of an abundant manifold is finite.

As in `TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver`, this file states the
definition topologically (`TauCeti.IsAbundantWithTwoSpheres`): the shriek map `j_!` is replaced
by the localization `Hₖ(Map(S², Q)) → Hₖ(Map(S², Q), Map(S², Q) ∖ ev⁻¹(b))` at the fibre over
the base point `b`, which it equals up to an identification of the target with `Hₖ₋ₙ(Ω²Q)`
(their Lemma 2.9). The kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)` is the image of `H₀(pt)`, which is the
image under `j_!` of the classes `σ_* γ` of constant spheres (their Proposition 2.12 applied to
`σ`). So the second condition in degree `n` says that the localization of `α` is not the
localization of a class of constant spheres; this form does not depend on the identification.

The first step of the proof of Theorem 6.12 replaces `α`, in degree `n`, by
`α - σ_* ev_* α`. This file proves that step and its converse: on a compact connected manifold,
`Q` is abundant with 2-spheres exactly when some class of degree at least `n` lives over the
fundamental class and is killed by evaluation
(`TauCeti.isAbundantWithTwoSpheres_iff_exists_homologyMap_eval_eq_zero`). In the proof of
Theorem 6.12 such a class is the input of the source's Proposition 6.7, which bounds the capacity;
there `ev_* α = 0` is how the vanishing of `i_{Q*} α ∈ H_*(Q)` is verified. The key point is
that evaluation detects constant spheres: if the localizations of `σ_* γ` and of a class `β`
agree, then `γ = ev_* β` (`TauCeti.eq_homologyMap_eval_of_fiberLocalization_eq`), since
localization is injective on the top homology of a compact connected manifold.

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres R n b`: the `n`-manifold `Q` is abundant with 2-spheres at
  `b`, with coefficients in `R`; the source's notion is the case `R = ℤ`.

## Main results

* `TauCeti.homologyMap_eval_homologyMap_const`: `ev_* σ_* γ = γ`.
* `TauCeti.eq_homologyMap_eval_of_fiberLocalization_eq`: evaluation detects the localizations of
  constant maps in the top degree.
* `TauCeti.livesOverFundamentalClass_sub_iff`: in degree `n`, the second condition holds exactly
  when `α - σ_* ev_* α` lives over the fundamental class.
* `TauCeti.isAbundantWithTwoSpheres_iff_exists_homologyMap_eval_eq_zero`: abundance through
  classes of degree at least `n` living over the fundamental class and killed by evaluation.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.7 and 6.11, Proposition 2.12
  and the proof of Theorem 6.12.
-/

public section

noncomputable section

open CategoryTheory

universe w

namespace TauCeti

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ) {Q : Type w} [TopologicalSpace Q]
  {B : Type} [TopologicalSpace B]

/-- **Evaluation is a left inverse of the constant maps on homology**: for the section
`σ : Q → Map(B, Q)` by constant maps and evaluation `ev` at a point `x₀` of `B`, `ev_* σ_* γ = γ`.
-/
@[simp]
theorem homologyMap_eval_homologyMap_const (x₀ : B) {k : ℕ}
    (γ : ((TopCat.toSSet.obj (TopCat.of Q)).homology R k : ModuleCat.{w} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval x₀))) R k).hom
      ((SSet.homologyMap (TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R k).hom γ) = γ := by
  rw [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp, ← TopCat.ofHom_comp,
    mappingSpaceEval_comp_const']
  -- `TopCat.ofHom (ContinuousMap.id Q)` is the identity of `TopCat.of Q`, and the homology of
  -- `TopCat.toSSet.obj (TopCat.of Q)` is read as `SSet.homology`, only up to unfolding.
  erw [TopCat.ofHom_id, TopCat.toSSet.map_id, SSet.homologyMap_id]
  rfl

/-- **Evaluation identifies the local classes of constant maps.** If the localization at the fibre
over `b` of evaluation at `x₀` of the class `σ_* γ` of constant maps agrees with that of a class
`β` of `Map(B, Q)`, then the localizations of `γ` and of `ev_* β` at `b` agree. -/
theorem fiberLocalization_id_eq_of_fiberLocalization_eq {x₀ : B} (b : Q) {k : ℕ}
    {γ : ((TopCat.toSSet.obj (TopCat.of Q)).homology R k : ModuleCat.{w} Λ)}
    {β : ((TopCat.toSSet.obj (TopCat.of C(B, Q))).homology R k : ModuleCat.{w} Λ)}
    (h : (fiberLocalization R (mappingSpaceEval x₀) b k).hom
        ((SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R k).hom γ) =
      (fiberLocalization R (mappingSpaceEval x₀) b k).hom β) :
    (fiberLocalization R (id : Q → Q) b k).hom γ =
      (fiberLocalization R (id : Q → Q) b k).hom
        ((SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (mappingSpaceEval x₀))) R k).hom β) := by
  -- Evaluation is a map over `Q` from `ev` to the identity, so it commutes with localization.
  have hev := homologyMap_comp_fiberLocalization R (mappingSpaceEval (X := Q) x₀)
    (p := mappingSpaceEval x₀) (p' := id) (Function.id_comp _) b k
  have h₁ := congr($hev β)
  have h₂ := congr($hev ((SSet.homologyMap (TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R k).hom γ))
  simp only [ModuleCat.comp_apply, homologyMap_eval_homologyMap_const] at h₁ h₂
  rw [h₁, h₂, h]

/-- **Evaluation detects constant maps in the top degree.** Let `Q` be a compact connected
Hausdorff space modelled on a real normed space of finite dimension `n`. If the localization at
the fibre over `b` of evaluation at `x₀` of the class `σ_* γ ∈ Hₙ(Map(B, Q))` of constant maps
agrees with that of a class `β`, then `γ = ev_* β`. -/
theorem eq_homologyMap_eval_of_fiberLocalization_eq {x₀ : B} [FiniteDimensional ℝ V] [T2Space Q]
    [CompactSpace Q] [ConnectedSpace Q] [ChartedSpace V Q] {n : ℕ}
    (hn : Module.finrank ℝ V = n) (b : Q)
    {γ : ((TopCat.toSSet.obj (TopCat.of Q)).homology R n : ModuleCat.{w} Λ)}
    {β : ((TopCat.toSSet.obj (TopCat.of C(B, Q))).homology R n : ModuleCat.{w} Λ)}
    (h : (fiberLocalization R (mappingSpaceEval x₀) b n).hom
        ((SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R n).hom γ) =
      (fiberLocalization R (mappingSpaceEval x₀) b n).hom β) :
    γ = (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (mappingSpaceEval x₀))) R n).hom β :=
  fiberLocalization_id_injective R hn b (fiberLocalization_id_eq_of_fiberLocalization_eq R b h)

/-- A space `Q` is **abundant with 2-spheres** in dimension `n` at `b`, with coefficients in `R`,
if some class `α ∈ Hₖ(Map(S², Q); R)` lives over the fundamental class of `Q` at `b` for
evaluation at the north pole, and either `k > n`, or `k = n` and the localization of `α` at the
fibre over `b` is not the localization of a class `σ_* γ` of constant spheres.

This is Definition 6.11 of Barraud–Damian–Humilière–Oancea (Definition 1.7 in their
introduction) for `R = ℤ` and a closed connected oriented `n`-manifold `Q`, with the shriek map to
the fibre replaced by the localization at the fibre, as in
`TauCeti.LivesOverFundamentalClass`. The kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)` is the shriek image
of the constant spheres, so the second alternative is their condition that the shriek image
`j_! α ∈ H₀(Ω²Q)` stays nonzero in reduced homology; this uses the orientation, through which
`j_!` maps `Hₙ(Q)` onto `H₀(pt)`. On a compact connected manifold the definition is
characterized by `TauCeti.isAbundantWithTwoSpheres_iff_exists_homologyMap_eval_eq_zero`. -/
def IsAbundantWithTwoSpheres (n : ℕ) (b : Q) : Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
      ModuleCat.{w} Λ)),
    LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) b α ∧
      (n < k ∨ k = n ∧
        ∀ γ : ((TopCat.toSSet.obj (TopCat.of Q)).homology R k : ModuleCat.{w} Λ),
          (fiberLocalization R (mappingSpaceEval Sphere2.north) b k).hom
              ((SSet.homologyMap (TopCat.toSSet.map
                (TopCat.ofHom (ContinuousMap.const' : C(Q, C(Sphere2, Q))))) R k).hom γ) ≠
            (fiberLocalization R (mappingSpaceEval Sphere2.north) b k).hom α)

/-- A class of degree above the dimension that lives over the fundamental class makes `Q`
abundant with 2-spheres. -/
theorem IsAbundantWithTwoSpheres.of_lt {n : ℕ} {b : Q} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) b α)
    (hk : n < k) : IsAbundantWithTwoSpheres R n b :=
  ⟨k, α, hα, .inl hk⟩

variable [FiniteDimensional ℝ V] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [ChartedSpace V Q]

/-- **The reduced-homology condition in the top degree** (from the proof of
Barraud–Damian–Humilière–Oancea, Theorem 6.12, where `B = S²`). On a compact connected manifold
of dimension `n`, the localization of `α ∈ Hₙ(Map(B, Q))` at the fibre over `b` of evaluation at
`x₀` is not the localization of a class of constant maps exactly when `α - σ_* ev_* α` lives over
the fundamental class. -/
theorem livesOverFundamentalClass_sub_iff (x₀ : B) {n : ℕ} (hn : Module.finrank ℝ V = n) (b : Q)
    (α : ((TopCat.toSSet.obj (TopCat.of C(B, Q))).homology R n : ModuleCat.{w} Λ)) :
    LivesOverFundamentalClass R (mappingSpaceEval x₀) b
        (α - (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R n).hom
          ((SSet.homologyMap (TopCat.toSSet.map
            (TopCat.ofHom (mappingSpaceEval x₀))) R n).hom α)) ↔
      ∀ γ : ((TopCat.toSSet.obj (TopCat.of Q)).homology R n : ModuleCat.{w} Λ),
        (fiberLocalization R (mappingSpaceEval x₀) b n).hom
            ((SSet.homologyMap (TopCat.toSSet.map
              (TopCat.ofHom (ContinuousMap.const' : C(Q, C(B, Q))))) R n).hom γ) ≠
          (fiberLocalization R (mappingSpaceEval x₀) b n).hom α := by
  rw [livesOverFundamentalClass_iff, map_sub, sub_ne_zero]
  constructor
  · intro h γ hγ
    rw [← eq_homologyMap_eval_of_fiberLocalization_eq R hn b hγ, hγ] at h
    exact h rfl
  · exact fun h ↦ (h _).symm

/-- **Abundance through classes killed by evaluation** (the first step of the proof of
Barraud–Damian–Humilière–Oancea, Theorem 6.12, and its converse). A compact connected manifold
`Q` of dimension `n` is abundant with 2-spheres at `b` exactly when some class
`α ∈ Hₖ(Map(S², Q))` of degree `k ≥ n` lives over the fundamental class at `b` and has
`ev_* α = 0`. In degree `n` such a class is obtained from a class `α` as in the definition by
replacing it with `α - σ_* ev_* α`; above degree `n` the homology of `Q` vanishes. -/
theorem isAbundantWithTwoSpheres_iff_exists_homologyMap_eval_eq_zero {n : ℕ}
    (hn : Module.finrank ℝ V = n) (b : Q) :
    IsAbundantWithTwoSpheres R n b ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
          ModuleCat.{w} Λ)),
        n ≤ k ∧ LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) b α ∧
          (SSet.homologyMap (TopCat.toSSet.map
            (TopCat.ofHom (mappingSpaceEval Sphere2.north))) R k).hom α = 0 := by
  constructor
  · rintro ⟨k, α, hα, hk | ⟨rfl, hk⟩⟩
    · -- Above the dimension the homology of `Q` vanishes.
      have hQ := isZero_singularHomology_of_compactSpace R (M := Q) hn hk
      exact ⟨k, α, hk.le, hα, (ModuleCat.isZero_iff_subsingleton.1 hQ).elim _ _⟩
    · -- In the dimension, subtract the constant spheres over `ev_* α`.
      refine ⟨_, _, le_rfl, (livesOverFundamentalClass_sub_iff R Sphere2.north hn b α).2 hk, ?_⟩
      rw [map_sub, homologyMap_eval_homologyMap_const, sub_self]
  · rintro ⟨k, α, hk, hα, hev⟩
    rcases hk.lt_or_eq with hk | rfl
    · exact .of_lt R hα hk
    · refine ⟨_, α, hα, .inr ⟨rfl, fun γ hγ ↦ (livesOverFundamentalClass_iff R _ b α).1 hα ?_⟩⟩
      rw [← hγ, eq_homologyMap_eval_of_fiberLocalization_eq R hn b hγ, hev, map_zero, map_zero]

end TauCeti
