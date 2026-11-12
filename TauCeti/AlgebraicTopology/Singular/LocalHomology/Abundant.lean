/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension

/-!
# Manifolds abundant with 2-spheres

Let `Q` be a space modelled on a real normed space of dimension `n`, and let
`ev : Map(S², Q) → Q` be evaluation at the north pole of `S²`, with the constant spheres
`σ : Q → Map(S², Q)` as a section. Barraud, Damian, Humilière and Oancea call a closed connected
oriented manifold `Q` **abundant with 2-spheres** if some class `α ∈ H_*(Map(S², Q))`
(i) lives over the fundamental class of `Q`, that is `j_! α ≠ 0` for the shriek map
`j_! : H_*(Map(S², Q)) → H_{*-n}(Ω²Q)` of the inclusion `j` of the base point, and
(ii) either has degree `> n`, or has degree `n` and `j_! α` stays nonzero in
`H₀(Ω²Q, pt)` (their Definition 6.11). Under this hypothesis they prove that the `π₁`-sensitive
Hofer–Zehnder capacity of the unit codisc bundle `D*Q` is finite (their Theorem 6.12).

This file states the definition chart-free, with coefficients in an arbitrary module `R`
(`TauCeti.IsAbundantWithTwoSpheres`). Condition (i) is `TauCeti.LivesOverFundamentalClass` for
`ev`, which asks the localization `H_*(Map(S², Q)) → H_*(Map(S², Q), Map(S², Q) ∖ Ω²Q)` at the
fibre over the base point to be nonzero. Condition (ii) in degree `n` is phrased as: the class
`α - σ_* ev_* α` lives over the fundamental class. This is the source's condition: the shriek
map is natural for maps of fibrations (their Proposition 2.12), so `j_! σ_* = (σ|_pt)_* j_!`
sends `H_n(Q)` into the classes of the constant sphere in `H₀(Ω²Q)`, and `ev_*` reads `j_! α`
through the augmentation `H₀(Ω²Q) → H₀(pt)`. Hence `j_!(α - σ_* ev_* α)` is the reduced part of
`j_! α`, which vanishes exactly when the image of `j_! α` in `H₀(Ω²Q, pt)` does. In degrees
above `n` the subtracted class lies in `H_k(Q) = 0`, so the condition reads the same in every
degree. Neither condition uses an orientation of `Q`, and none is assumed.

The first step of the proof of Theorem 6.12 is purely topological: abundance supplies a class
living over the fundamental class whose image under evaluation at **every** point of `S²` is
zero (`TauCeti.IsAbundantWithTwoSpheres.exists_forall_homologyMap_eq_zero`). This is the class
the source feeds into its criterion `ker i_{Q*} ⊄ ker j_!` (their Proposition 6.7), the vanishing
of `i_{Q*}` being read off from evaluations at two points of `S²`. Conversely any class living
over the fundamental class and killed by `ev_*` witnesses abundance
(`TauCeti.isAbundantWithTwoSpheres_iff`). If the constant spheres are a homotopy inverse of
evaluation, as for a point, `Q` is not abundant
(`TauCeti.not_isAbundantWithTwoSpheres_of_homotopic`).

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres R n x`: `Q` is abundant with 2-spheres at the base point `x`,
  with coefficients in `R`.

## Main results

* `TauCeti.homologyMap_mappingSpaceEval_homologyMap_const'`: constant maps induce a right inverse of
  evaluation on homology.
* `TauCeti.homologyMap_mappingSpaceEval_eq_of_joined`: evaluations at joined points of a locally
  compact source induce the same map on homology.
* `TauCeti.isAbundantWithTwoSpheres_of_finrank_lt`,
  `TauCeti.isAbundantWithTwoSpheres_of_homologyMap_eq_zero`: the two ways of exhibiting
  abundance.
* `TauCeti.isAbundantWithTwoSpheres_iff`: on a compact space, abundance is the existence of a
  class living over the fundamental class and killed by evaluation.
* `TauCeti.IsAbundantWithTwoSpheres.exists_forall_homologyMap_eq_zero`: such a class is killed by
  evaluation at every point of `S²`.
* `TauCeti.not_isAbundantWithTwoSpheres_of_homotopic`,
  `TauCeti.not_isAbundantWithTwoSpheres_of_subsingleton`: obstructions to abundance.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.3 (Definition 1.7 = Definition 6.11,
  the proof of Theorem 6.12) and §2.4 (Proposition 2.12).
-/

public section

noncomputable section

open CategoryTheory Module Metric

universe w

namespace TauCeti

variable {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ)

/-! ### Evaluation on homology -/

section Evaluation

variable {B : Type} {X : Type w} [TopologicalSpace B] [TopologicalSpace X]

/-- **Constant maps split evaluation on homology.** The map induced on singular homology by the
constant maps `X → Map(B, X)` is a right inverse of the map induced by evaluation at `b`. -/
@[simp]
theorem homologyMap_mappingSpaceEval_homologyMap_const' (b : B) (k : ℕ)
    (a : ((TopCat.toSSet.obj (TopCat.of X)).homology R k : ModuleCat.{w} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval (X := X) b))) R k).hom
        ((SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const' : C(X, C(B, X))))) R k).hom a) = a := by
  rw [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
    ← TopCat.ofHom_comp, mappingSpaceEval_comp_const', TopCat.ofHom_id,
    CategoryTheory.Functor.map_id, SSet.homologyMap_id]
  rfl

/-- **Evaluations at joined points agree on homology.** For a locally compact space `B` and
points `b₀`, `b₁` joined by a path, evaluations `Map(B, X) → X` at `b₀` and at `b₁` are homotopic,
so they induce the same map on singular homology. -/
theorem homologyMap_mappingSpaceEval_eq_of_joined [LocallyCompactSpace B] {b₀ b₁ : B}
    (h : Joined b₀ b₁) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval (X := X) b₀))) R k =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (mappingSpaceEval (X := X) b₁))) R k :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (mappingSpaceEvalHomotopy h.somePath) R k

end Evaluation

/-! ### Abundance -/

section Abundant

variable {Q : Type w} [TopologicalSpace Q] (n : ℕ)

/-- A space `Q` of dimension `n` is **abundant with 2-spheres** at `x`, with coefficients in `R`,
if some class `α ∈ H_k(Map(S², Q); R)` lives over the fundamental class at `x` for evaluation
`ev : Map(S², Q) → Q` at the north pole, and either `k > n` or the class `α - σ_* ev_* α` also
lives over the fundamental class, where `σ : Q → Map(S², Q)` is the section by constant spheres.

This is Definition 6.11 of Barraud–Damian–Humilière–Oancea, stated without the shriek map: for
`k = n` the second condition says that the image of `j_! α` in `H₀(Ω²Q, pt)` is nonzero (see the
module docstring). The source states it for closed connected oriented `n`-manifolds and integer
coefficients. The definition records only the dimension `n`, and the results below assume that
`Q` is a compact Hausdorff space modelled on a real normed space of dimension `n`; no orientation
is used. -/
def IsAbundantWithTwoSpheres (x : Q) : Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
      ModuleCat.{w} Λ)),
    LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α ∧
      (n < k ∨ LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x
        (α - (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.const' : C(Q, C(Sphere2, Q))))) R k).hom
            ((SSet.homologyMap (TopCat.toSSet.map
              (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom α)))

variable {R n} {x : Q} {k : ℕ}
  {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k : ModuleCat.{w} Λ)}

/-- **Abundance from a class of high degree.** A class of degree above the dimension living over
the fundamental class witnesses abundance with 2-spheres. -/
theorem isAbundantWithTwoSpheres_of_lt
    (hα : LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α)
    (hk : n < k) : IsAbundantWithTwoSpheres R n x :=
  ⟨k, α, hα, .inl hk⟩

/-- **Abundance from a class killed by evaluation.** A class living over the fundamental class
whose image under evaluation at the north pole vanishes witnesses abundance with 2-spheres. -/
theorem isAbundantWithTwoSpheres_of_homologyMap_eq_zero
    (hα : LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α)
    (h : (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom α = 0) :
    IsAbundantWithTwoSpheres R n x :=
  ⟨k, α, hα, .inr (by rwa [h, map_zero, sub_zero])⟩

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V Q] [T2Space Q] [CompactSpace Q] (hn : finrank ℝ V = n)

include hn in
/-- Evaluation kills the homology of `Map(S², Q)` above the dimension of a compact space `Q`
modelled on `V`, since `H_k(Q) = 0` there. -/
private theorem homologyMap_mappingSpaceEval_eq_zero_of_lt (hk : n < k)
    (a : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k : ModuleCat.{w} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom a = 0 :=
  have : Subsingleton ((TopCat.toSSet.obj (TopCat.of Q)).homology R k : ModuleCat.{w} Λ) :=
    ModuleCat.isZero_iff_subsingleton.1 (isZero_singularHomology_of_compactSpace R (M := Q) hn hk)
  Subsingleton.elim _ _

include hn in
/-- **Abundance supplies a class killed by evaluation.** On a compact Hausdorff space modelled on
a finite-dimensional space, abundance with 2-spheres gives a class living over the fundamental
class whose image under evaluation at the north pole vanishes: the class `α - σ_* ev_* α`, which
is `α` itself in degrees above the dimension. -/
theorem IsAbundantWithTwoSpheres.exists_homologyMap_eq_zero (h : IsAbundantWithTwoSpheres R n x) :
    ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
        ModuleCat.{w} Λ)),
      LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α ∧
        (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom α = 0 := by
  obtain ⟨k, α, hα, hk | hα'⟩ := h
  · exact ⟨k, α, hα, homologyMap_mappingSpaceEval_eq_zero_of_lt hn hk α⟩
  · exact ⟨k, _, hα', by rw [map_sub, homologyMap_mappingSpaceEval_homologyMap_const', sub_self]⟩

include hn in
/-- **Abundance as a class killed by evaluation.** A compact Hausdorff space modelled on a
finite-dimensional space is abundant with 2-spheres at `x` exactly when some class of
`H_*(Map(S², Q); R)` lives over the fundamental class at `x` and is killed by evaluation at the
north pole. -/
theorem isAbundantWithTwoSpheres_iff :
    IsAbundantWithTwoSpheres R n x ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
          ModuleCat.{w} Λ)),
        LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α ∧
          (SSet.homologyMap (TopCat.toSSet.map
            (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom α = 0 :=
  ⟨IsAbundantWithTwoSpheres.exists_homologyMap_eq_zero hn,
    fun ⟨_, _, hα, h⟩ ↦ isAbundantWithTwoSpheres_of_homologyMap_eq_zero hα h⟩

include hn in
/-- **Abundance supplies a class killed by every evaluation.** On a compact Hausdorff space
modelled on a finite-dimensional space, abundance with 2-spheres gives a class of
`H_*(Map(S², Q); R)` living over the fundamental class whose image under evaluation at every
point of `S²` vanishes. This is the class of the proof of Theorem 6.12 of
Barraud–Damian–Humilière–Oancea, which compares the evaluations at two points of `S²`. -/
theorem IsAbundantWithTwoSpheres.exists_forall_homologyMap_eq_zero
    (h : IsAbundantWithTwoSpheres R n x) :
    ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
        ModuleCat.{w} Λ)),
      LivesOverFundamentalClass R (mappingSpaceEval Sphere2.north) x α ∧
        ∀ z : Sphere2, (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (mappingSpaceEval (X := Q) z))) R k).hom α = 0 := by
  obtain ⟨k, α, hα, h0⟩ := h.exists_homologyMap_eq_zero hn
  have : PathConnectedSpace Sphere2 := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) 0 zero_le_one)
  refine ⟨k, α, hα, fun z ↦ ?_⟩
  rwa [← homologyMap_mappingSpaceEval_eq_of_joined R (PathConnectedSpace.joined Sphere2.north z)]

include hn in
/-- **An obstruction to abundance.** If the constant spheres are a homotopy inverse of
evaluation at the north pole, a compact Hausdorff space modelled on a finite-dimensional space is
not abundant with 2-spheres: every class of `Map(S², Q)` is then `σ_* ev_*` of itself. -/
theorem not_isAbundantWithTwoSpheres_of_homotopic
    (h : (ContinuousMap.const' : C(Q, C(Sphere2, Q))).comp (mappingSpaceEval Sphere2.north)
      |>.Homotopic (ContinuousMap.id _)) :
    ¬IsAbundantWithTwoSpheres R n x := by
  have hid (k : ℕ) (a : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology R k :
      ModuleCat.{w} Λ)) :
      (SSet.homologyMap (TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.const' : C(Q, C(Sphere2, Q))))) R k).hom
          ((SSet.homologyMap (TopCat.toSSet.map
            (TopCat.ofHom (mappingSpaceEval (X := Q) Sphere2.north))) R k).hom a) = a := by
    rw [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
      ← TopCat.ofHom_comp]
    calc _ = (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.id C(Sphere2, Q)))) R k).hom a :=
          -- `SSet.homologyMap (TopCat.toSSet.map f)` unfolds to the homology map of the singular
          -- chains of `f`, the form in which homotopy invariance is stated.
          congrArg (fun φ ↦ φ.hom a)
            (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
              (f := TopCat.ofHom _) (g := TopCat.ofHom (ContinuousMap.id C(Sphere2, Q))) h.some R k)
      _ = a := by
          rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id, SSet.homologyMap_id]
          rfl
  rintro ⟨k, α, hα, hk | hα'⟩
  · have h0 : α = 0 := by
      rw [← hid k α, homologyMap_mappingSpaceEval_eq_zero_of_lt hn hk, map_zero]
    exact not_livesOverFundamentalClass_zero R _ x k (h0 ▸ hα)
  · rw [hid, sub_self] at hα'
    exact not_livesOverFundamentalClass_zero R _ x k hα'

include hn in
/-- **A point is not abundant with 2-spheres.** On a subsingleton compact Hausdorff space
modelled on a finite-dimensional space, evaluation at the north pole and the constant spheres
are inverse homeomorphisms. -/
theorem not_isAbundantWithTwoSpheres_of_subsingleton [Subsingleton Q] :
    ¬IsAbundantWithTwoSpheres R n x :=
  have h : (ContinuousMap.const' : C(Q, C(Sphere2, Q))).comp (mappingSpaceEval Sphere2.north) =
      ContinuousMap.id _ :=
    ContinuousMap.ext fun _ ↦ ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _
  not_isAbundantWithTwoSpheres_of_homotopic hn (h ▸ .refl _)

end Abundant

end TauCeti
