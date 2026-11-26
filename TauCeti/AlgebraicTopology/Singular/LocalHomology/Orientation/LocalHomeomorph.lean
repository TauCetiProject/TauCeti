/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalHomeomorph
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Transport

/-!
# Local orientations along local homeomorphisms

A local homeomorphism `π : M → N`, such as a covering map, identifies the integral local
homology of `M` at `x` with that of `N` at `π x` (`TauCeti.localHomologyIsoOfIsLocalHomeomorph`),
and so identifies the local orientations of `M` at `x` with those of `N` at `π x`
(`IsLocalHomeomorph.localOrientationEquiv`). For Hausdorff spaces modelled on the same
finite-dimensional real normed space these identifications intertwine the transport of local
orientations along paths
(`IsLocalHomeomorph.localOrientationEquiv_localOrientationTransport`): transporting a local
orientation of `M` along a path and reading it in `N` is reading it in `N` and transporting it
along the image path. This is how orientations of a covering space are compared with transport of
local orientations in the base, as for the orientation double cover of a manifold.

## Main definitions

* `IsLocalHomeomorph.localOrientationEquiv`: the local orientations of `M` at `x` correspond to
  those of `N` at `π x`.

## Main results

* `IsLocalHomeomorph.localOrientationEquiv_trans`: the correspondence restricted along an open
  embedding.
* `IsLocalHomeomorph.localOrientationEquiv_eq_isOpenEmbedding_localOrientationEquiv`: for an
  open embedding it is the correspondence of local orientations by excision.
* `IsLocalHomeomorph.localOrientationEquiv_localOrientationTransport`: the correspondence
  intertwines the transport of local orientations along path classes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3: local orientations, their transport, and the orientation double cover.
-/

public section

noncomputable section

open CategoryTheory Topology TauCeti

universe w

namespace IsLocalHomeomorph

variable {M N : Type w} [TopologicalSpace M] [TopologicalSpace N] [T1Space M] [T1Space N]
  {π : M → N}

/-- A local homeomorphism `π : M → N` of `T₁` spaces identifies the local orientations of `M` at
`x` in degree `d` with those of `N` at `π x`, through the isomorphism of integral local homology
induced by `π`. -/
def localOrientationEquiv (hπ : IsLocalHomeomorph π) (x : M) (d : ℕ) :
    LocalOrientation M x d ≃ LocalOrientation N (π x) d :=
  LocalOrientation.equivOfIso
    (localHomologyIsoOfIsLocalHomeomorph (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      hπ x d)

/-- On local homology classes, the correspondence of local orientations is the local homology
isomorphism of `π`. -/
@[simp]
lemma coe_localOrientationEquiv (hπ : IsLocalHomeomorph π) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    (hπ.localOrientationEquiv x d z).val =
      (localHomologyIsoOfIsLocalHomeomorph (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hπ x d).hom z.val :=
  LocalOrientation.coe_equivOfIso _ z

/-- The inverse correspondence acts on local homology classes by the inverse isomorphism. -/
@[simp]
lemma coe_localOrientationEquiv_symm (hπ : IsLocalHomeomorph π) (x : M) {d : ℕ}
    (z : LocalOrientation N (π x) d) :
    ((hπ.localOrientationEquiv x d).symm z).val =
      (localHomologyIsoOfIsLocalHomeomorph (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) hπ x d).inv z.val :=
  LocalOrientation.coe_equivOfIso_symm _ z

/-- The correspondence of local orientations commutes with reversal. -/
@[simp]
lemma localOrientationEquiv_neg (hπ : IsLocalHomeomorph π) (x : M) {d : ℕ}
    (z : LocalOrientation M x d) :
    hπ.localOrientationEquiv x d (-z) = -hπ.localOrientationEquiv x d z :=
  LocalOrientation.equivOfIso_neg _ z

/-- **The correspondence of local orientations along an open embedding.** For an open embedding
`j : W → M` such that `π ∘ j` is an open embedding, the correspondence of local orientations of
`j` at `w`, followed by that of `π` at `j w`, is the correspondence of `π ∘ j` at `w`. -/
@[simp]
lemma localOrientationEquiv_trans (hπ : IsLocalHomeomorph π) {W : Type w} [TopologicalSpace W]
    {j : W → M} (hj : IsOpenEmbedding j) (hπj : IsOpenEmbedding (π ∘ j)) (w : W) (d : ℕ) :
    (hj.localOrientationEquiv w d).trans (hπ.localOrientationEquiv (j w) d) =
      hπj.localOrientationEquiv w d :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [Equiv.trans_apply, coe_localOrientationEquiv, IsOpenEmbedding.coe_localOrientationEquiv,
      IsOpenEmbedding.coe_localOrientationEquiv, ← ConcreteCategory.comp_apply, ← Iso.trans_hom,
      localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph]

/-- For an open embedding, the correspondence of local orientations of `π` as a local
homeomorphism is its correspondence as an open embedding. -/
lemma localOrientationEquiv_eq_isOpenEmbedding_localOrientationEquiv
    (hπ : IsLocalHomeomorph π) (hπ' : IsOpenEmbedding π) (x : M) (d : ℕ) :
    hπ.localOrientationEquiv x d = hπ'.localOrientationEquiv x d :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [coe_localOrientationEquiv, IsOpenEmbedding.coe_localOrientationEquiv,
      localHomologyIsoOfIsLocalHomeomorph_eq_localHomologyIsoOfIsOpenEmbedding _ hπ hπ']

variable [T2Space M] [T2Space N] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] [ChartedSpace E N]

/-- **Local homeomorphisms intertwine the transport of local orientations.** Reading the
transport of a local orientation of `M` along a path class in `N` is transporting its reading in
`N` along the image path class. -/
theorem localOrientationEquiv_localOrientationTransport (hπ : IsLocalHomeomorph π) {d : ℕ}
    {x y : FundamentalGroupoid M} (f : x ⟶ y) (z : LocalOrientation M x.as d) :
    hπ.localOrientationEquiv y.as d (localOrientationTransport M E d f z) =
      localOrientationTransport N E d ((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map f)
        (hπ.localOrientationEquiv x.as d z) := by
  -- On local homology classes this is the naturality of the transport, evaluated at `z`. The
  -- objects of the two sides agree only up to unfolding `FundamentalGroupoid.map`, so the
  -- steps are chained by `Eq.trans` rather than rewritten.
  set F := FundamentalGroupoid.map ⟨π, hπ.continuous⟩
  apply Subtype.ext
  refine ((coe_localOrientationEquiv hπ y.as _).trans
    (congrArg _ (coe_localOrientationTransport M E d f z))).trans ?_
  refine Eq.trans ?_ ((coe_localOrientationTransport N E d (F.map f) _).trans
    (congrArg _ (coe_localOrientationEquiv hπ x.as z))).symm
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom
      (localHomologyTransport_comp_localHomologyIsoOfIsLocalHomeomorph_hom (A := ModuleCat.{w} ℤ)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (E := E) hπ d f) z.val).trans
      (ConcreteCategory.comp_apply _ _ _))

end IsLocalHomeomorph
