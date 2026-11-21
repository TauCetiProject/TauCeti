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
# Manifolds abundant with two-spheres

Let `Q` be a closed connected oriented `n`-manifold and let `ev : Map(S², Q) → Q` be evaluation
at the north pole of `S²`, the evaluation fibration with fibre `Ω²Q` over a base point `b`.
Barraud, Damian, Humilière and Oancea call `Q` **abundant with 2-spheres** (their Definition 6.11
and Definition 1.7) if some class `α ∈ Hₖ(Map(S², Q); ℤ)` satisfies:

1. `α` lives over the fundamental class of `Q`, that is its shriek `j_! α ∈ Hₖ₋ₙ(Ω²Q)` under the
   inclusion `j` of `b` is nonzero;
2. either `k > n`, or `k = n` and the image of `j_! α` in `H₀(Ω²Q, pt)` is nonzero.

Their Theorem 6.12 (Theorem H of the introduction) shows that the `π₁`-sensitive
Hofer–Zehnder capacity of the unit codisc bundle `D*Q` of such a manifold is finite.

This file states the definition in the chart-free form of
`TauCeti.LivesOverFundamentalClass` (`TauCeti.IsAbundantWithTwoSpheres`). The shriek map is the
localization `Hₖ(E) → Hₖ(E, E ∖ F)` at the fibre `F = ev⁻¹(b)` followed by an identification
`Hₖ(E, E ∖ F) ≅ Hₖ₋ₙ(F)` that depends on a chart at `b`
(`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), so the
first condition is that the localization of `α` is nonzero. For the second condition in degree
`n`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)` is spanned by the class of the constant sphere at `b`.
The constant spheres `c : Q → Map(S², Q)` are a section of `ev`, so they map the pair
`(Q, Q ∖ {b})` to `(E, E ∖ F)`, and the local homology `Hₙ(Q, Q ∖ {b}) ≅ H₀(pt)` goes under the
chart identifications onto that span: this is the square of the source's proof of Theorem 6.12,
the naturality of the shriek map (their Proposition 2.12) for the map of fibrations `c` from the
identity of `Q` to `ev`. So the second condition in degree `n` says that the localization of `α`
does not lie in the image of `c_* : Hₙ(Q, Q ∖ {b}) → Hₙ(E, E ∖ F)`.

The definition only uses the space `Q`, a point `b` and the dimension `n`; it is meant for closed
connected oriented `n`-manifolds, where it is the source's definition. Coefficients are the
integers, written `ULift ℤ` as for the integral fundamental classes of
`TauCeti.HomologicalOrientation`.

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres Q n b`: `Q` is abundant with 2-spheres at `b`, in
  dimension `n`, characterized by `TauCeti.isAbundantWithTwoSpheres_iff`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_of_lt`: a class of degree above `n` living over the
  fundamental class witnesses abundance.
* `TauCeti.isAbundantWithTwoSpheres_of_eq`: so does a class of degree `n` living over the
  fundamental class whose localization is not that of a constant sphere class.
* `TauCeti.fiberLocalization_mem_range_localHomologyMap_const'_iff`: the localization of a class
  `α` of `Map(B, X)` is that of a class of constant maps exactly when `α - ρ_* α` does not live over
  the fundamental class, where `ρ` sends a map to the constant map at its value at the base point.
* `TauCeti.IsAbundantWithTwoSpheres.homeomorph`: abundance is invariant under homeomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.7, 2.3 and 6.11,
  Proposition 2.12 and Theorem 6.12.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

section ConstantMaps

universe w

variable {Λ : Type*} [Ring Λ] (R : ModuleCat.{w} Λ) {B X : Type w} [TopologicalSpace B]
  [TopologicalSpace X] (b₀ : B) (x : X)

/-- **Localizations of classes of constant maps.** For evaluation `ev : Map(B, X) → X` at `b₀`,
let `ρ = const ∘ ev` send a map to the constant map at its value at `b₀`. The localization of a
class `α ∈ Hₖ(Map(B, X))` at the fibre over `x` lies in the image of the local homology
`Hₖ(X, X ∖ {x})` under the constant maps exactly when `α - ρ_* α` does not live over the
fundamental class at `x`. Indeed `ρ` lies over `X` and fixes the constant maps, and its effect on
localizations factors through `ev`. -/
theorem fiberLocalization_mem_range_localHomologyMap_const'_iff {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of C(B, X))).homology R k : ModuleCat.{w} Λ)) :
    (fiberLocalization R (mappingSpaceEval b₀) x k).hom α ∈
        LinearMap.range (localHomologyMap R ContinuousMap.const'
          (const'_preimage_mappingSpaceEval_preimage_subset b₀ x) k).hom ↔
      ¬LivesOverFundamentalClass R (mappingSpaceEval b₀) x
        (α - (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const'.comp (mappingSpaceEval b₀)))) R k).hom α) := by
  have hρ : mappingSpaceEval b₀ ∘ (ContinuousMap.const'.comp (mappingSpaceEval (X := X) b₀)) =
      mappingSpaceEval b₀ := funext fun _ ↦ by simp
  -- `ρ` lies over `X`, so it acts on localizations through the map `ρ_*` of local homology,
  -- which is `const_* ∘ ev_*` and fixes the image of `const_*`.
  have h₁ := ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization R
    (ContinuousMap.const'.comp (mappingSpaceEval b₀)) hρ x k) α
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h₁
  have h₂ := localHomologyMap_comp R (mappingSpaceEval b₀) ContinuousMap.const' subset_rfl
    (const'_preimage_mappingSpaceEval_preimage_subset b₀ x) k
  have h₃ : localHomologyMap R ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset b₀ x) k ≫
        localHomologyMap R (ContinuousMap.const'.comp (mappingSpaceEval b₀))
          (by rw [← Set.preimage_comp, hρ]) k =
      localHomologyMap R ContinuousMap.const'
        (const'_preimage_mappingSpaceEval_preimage_subset b₀ x) k := by
    rw [localHomologyMap_comp]
    exact localHomologyMap_congr R (ContinuousMap.ext fun _ ↦ by simp) _ k
  rw [livesOverFundamentalClass_iff, not_not, map_sub, sub_eq_zero, h₁]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy, ← ModuleCat.comp_apply, h₃]
  · intro h
    rw [h, ← h₂, ModuleCat.comp_apply]
    exact ⟨_, rfl⟩

end ConstantMaps

variable (Q : Type) [TopologicalSpace Q]

/-- A space `Q` is **abundant with 2-spheres** at `b`, in dimension `n`
(Barraud–Damian–Humilière–Oancea, Definition 6.11), if some integral class
`α ∈ Hₖ(Map(S², Q); ℤ)` lives over the fundamental class of `Q` at `b` for evaluation at the
north pole, and either `n < k`, or `k = n` and the localization of `α` at the fibre over `b` is
not in the image of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres.

For a closed connected oriented `n`-manifold this is the source's definition: the localization
at the fibre is the chart-free form of their shriek map `j_! : Hₖ(Map(S², Q)) → Hₖ₋ₙ(Ω²Q)`, and
in degree `n` the image of the local homology is the span of the class of the constant sphere in
`H₀(Ω²Q)`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)`. -/
def IsAbundantWithTwoSpheres (n : ℕ) (b : Q) : Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
        α ∧
      (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
        (mappingSpaceEval Sphere2.north) b k).hom α ∉
          LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
            (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom)

/-- Unfolding `IsAbundantWithTwoSpheres`: some class of `Hₖ(Map(S², Q); ℤ)` lives over the
fundamental class at `b`, and either `n < k`, or `k = n` and its localization at the fibre over `b`
is not in the image of the local homology of `Q` at `b` under the constant spheres. -/
theorem isAbundantWithTwoSpheres_iff (n : ℕ) (b : Q) :
    IsAbundantWithTwoSpheres Q n b ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
        LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b α ∧
          (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b k).hom α ∉
              LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
                ContinuousMap.const'
                  (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom) :=
  Iff.rfl

variable {Q}

/-- **Abundance from a class of degree above the dimension.** If a class
`α ∈ Hₖ(Map(S², Q); ℤ)` with `n < k` lives over the fundamental class at `b`, then `Q` is
abundant with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_lt {n k : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α) (hk : n < k) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨k, α, hα, Or.inl hk⟩

/-- **Abundance from a class in the dimension.** If a class `α ∈ Hₙ(Map(S², Q); ℤ)` lives over
the fundamental class at `b` and its localization at the fibre over `b` is not the image of a
class of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres, then `Q` is abundant
with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_eq {n : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α)
    (hc : ∀ β, (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) n).hom β ≠
        (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
          n).hom α) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨n, α, hα, Or.inr ⟨rfl, fun ⟨β, hβ⟩ ↦ hc β hβ⟩⟩

/-- **Abundance is invariant under homeomorphisms.** If `Q` is abundant with 2-spheres at `b` in
dimension `n`, and `e : Q ≃ₜ Q'`, then `Q'` is abundant with 2-spheres at `e b` in dimension `n`:
composing with `e` carries a witness for `Q` to a witness for `Q'`. -/
theorem IsAbundantWithTwoSpheres.homeomorph {Q' : Type} [TopologicalSpace Q'] {n : ℕ} {b : Q}
    (h : IsAbundantWithTwoSpheres Q n b) (e : Q ≃ₜ Q') : IsAbundantWithTwoSpheres Q' n (e b) := by
  obtain ⟨k, α, hα, hk⟩ := (isAbundantWithTwoSpheres_iff Q n b).1 h
  let H : C(C(Sphere2, Q), C(Sphere2, Q')) :=
    ⟨fun f ↦ (e : C(Q, Q')).comp f, ContinuousMap.continuous_postcomp _⟩
  let H' : C(C(Sphere2, Q'), C(Sphere2, Q)) :=
    ⟨fun f ↦ (e.symm : C(Q', Q)).comp f, ContinuousMap.continuous_postcomp _⟩
  have hH : H'.comp H = ContinuousMap.id _ :=
    ContinuousMap.ext fun f ↦ ContinuousMap.ext fun s ↦ by simp [H, H']
  -- Composing with `e` lies over `e`, and the fibre of `e ∘ ev` over `e b` is that of `ev`
  -- over `b`.
  have hlo : ∀ β : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ),
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north)
          (e b) ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom H))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom β) ↔
        LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
          (mappingSpaceEval Sphere2.north) b β := fun β ↦
    (livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id _ H H' hH
      (p := e ∘ mappingSpaceEval Sphere2.north) (funext fun f ↦ by simp [H])
      (funext fun f ↦ by simp [H'])).trans
      (livesOverFundamentalClass_congr _ (Set.ext fun f ↦ by simp) β)
  rcases hk with hk | ⟨rfl, hk⟩
  · exact isAbundantWithTwoSpheres_of_lt ((hlo α).2 hα) hk
  · refine (isAbundantWithTwoSpheres_iff _ _ _).2
      ⟨_, _, (hlo α).2 hα, Or.inr ⟨rfl, ?_⟩⟩
    rw [fiberLocalization_mem_range_localHomologyMap_const'_iff, not_not] at hk ⊢
    -- Composing with `e` commutes with sending maps to constant maps.
    have hcomm : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom H))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k ≫ SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
          (ContinuousMap.const'.comp (mappingSpaceEval (X := Q') Sphere2.north))))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k =
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
          (ContinuousMap.const'.comp (mappingSpaceEval (X := Q) Sphere2.north))))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k ≫ SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom H))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k :=
      homologyMap_toSSet_ofHom_comp_comm _ _
        (ContinuousMap.ext fun f ↦ ContinuousMap.ext fun s ↦ by simp [H])
    rw [← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply, ← map_sub]
    exact (hlo _).2 hk

end TauCeti
