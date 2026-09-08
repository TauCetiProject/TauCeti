/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# The universal property of profinite completion

This file restates the categorical universal property of Mathlib's profinite completion for
unbundled groups and continuous monoid homomorphisms. It also proves that the canonical map from
a finite group to its profinite completion is bijective, and exposes the projections of the
profinite completion onto the finite quotients it is the limit of.

The correspondence is obtained from `ProfiniteGrp.ProfiniteCompletion.homEquiv`; the finite-group
result uses its canonical map's dense range and Mathlib's residual-finiteness criterion. The
projections are the components of Mathlib's explicit limit cone.
-/

public section

namespace TauCeti

open CategoryTheory

namespace ProfiniteCompletion

universe u v

variable (G : Type u) [Group G]
variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [TotallyDisconnectedSpace P]

/-- Continuous homomorphisms from the profinite completion of `G` to a profinite group `P`
correspond to abstract homomorphisms from `G` to `P`. -/
noncomputable def continuousMonoidHomEquiv :
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) ≃ (G →* P) :=
  (ConcreteCategory.homEquiv (C := ProfiniteGrp)).symm |>.trans
    (ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of G) (ProfiniteGrp.of P)) |>.trans
      (ConcreteCategory.homEquiv (C := GrpCat))

/-- The unbundled profinite-completion correspondence restricts a continuous homomorphism along
the canonical map. -/
@[simp]
theorem continuousMonoidHomEquiv_apply
    (f : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) (g : G) :
    continuousMonoidHomEquiv G P f g =
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) :=
  -- Mathlib has no propositional forward computation rule for `homEquiv`; isolate its
  -- definitional reduction through both concrete-category equivalences in this opaque theorem.
  (rfl)

/-- The continuous lift of an abstract homomorphism agrees with it on the original group. -/
@[simp]
theorem continuousMonoidHomEquiv_symm_apply_etaFn (f : G →* P) (g : G) :
    (continuousMonoidHomEquiv G P).symm f
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = f g := by
  rw [← continuousMonoidHomEquiv_apply, Equiv.apply_symm_apply]

/-- Two continuous homomorphisms from a profinite completion to a Hausdorff topological group
agree if they agree on the canonical dense image of the original group. -/
@[ext]
theorem continuousMonoidHom_ext
    {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* Q}
    (h : ∀ x : G,
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x) =
        g (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x)) : f = g := by
  apply DFunLike.coe_injective
  exact (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    f.continuous_toFun g.continuous_toFun (funext h)

/-- The canonical map from a finite group to its profinite completion is bijective. -/
theorem etaFn_bijective_of_finite [Finite G] :
    Function.Bijective (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G)) := by
  refine ⟨(ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (G := GrpCat.of G)).2 inferInstance, ?_⟩
  intro x
  have hx : x ∈ closure (Set.range
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G))) := by
    rw [(ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).closure_range]
    exact Set.mem_univ x
  rw [(Set.finite_range _).isClosed.closure_eq] at hx
  exact hx

/-- The projection from the profinite completion of `G` onto its finite quotient indexed by the
finite-index normal subgroup `H`. -/
@[expose]
def coordinateHom (H : FiniteIndexNormalSubgroup G) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* G ⧸ H.toSubgroup := by
  let f := ((ProfiniteGrp.limitCone
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G))).π.app H).hom
    |>.toMonoidHom
  -- The finite-quotient object hides its underlying quotient group.
  change ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* G ⧸ H.toSubgroup at f
  exact f

/-- The projection onto the finite quotient by `H` evaluates the underlying compatible family of
cosets at `H`. -/
theorem coordinateHom_apply (H : FiniteIndexNormalSubgroup G)
    (x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    coordinateHom G H x = x.val H :=
  -- `limitCone` projects a compatible family of cosets to its `H`-th component by definition.
  rfl

/-- The `H`-coordinate of the canonical image of `g` is its coset modulo `H`. -/
@[simp]
theorem coordinateHom_etaFn (H : FiniteIndexNormalSubgroup G) (g : G) :
    coordinateHom G H (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      QuotientGroup.mk g := by
  rw [coordinateHom_apply]
  -- `etaFn g` is the constant family of cosets of `g`.
  rfl

/-- The projection onto a finite quotient is continuous, that quotient carrying the discrete
topology. -/
theorem continuous_coordinateHom (H : FiniteIndexNormalSubgroup G) :
    @Continuous (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
      (G ⧸ H.toSubgroup) inferInstance ⊥ (coordinateHom G H) :=
  -- The finite-quotient object hides its discrete underlying quotient group.
  ((ProfiniteGrp.limitCone
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G))).π.app H).hom.continuous_toFun

end ProfiniteCompletion

end TauCeti
