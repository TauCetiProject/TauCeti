/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup
public import TauCeti.AlgebraicGeometry.FiniteEtale.Splitting

/-!
# Splitting the nodes and branches of a proper nodal curve

Let `X` be a proper nodal curve over a field `K`. Its singular subscheme `Sing(X/K)` is finite
étale over `K`, and its branch scheme `E` is finite étale of rank two over `Sing(X/K)`
(`AlgebraicGeometry.Scheme.finrank_branchSchemeToSingularLocus`). After one finite Galois
extension `L / K`, both become disjoint unions of rational points: the singular subscheme of the
base change `X_L` is `Spec (Fin n → L)`, a labelling of the `n` nodes, and its branch scheme is
`Spec (Fin 2 → Fin n → L)` over it, two copies of the nodes. So every node of `X_L` is a rational
point with two rational branches, labelled by `Fin 2`, and the pairing involution exchanging the
two branches through each node is the swap of the two copies.

The splitting applies to every chosen base change of the curve: the singular subscheme and the
branch scheme commute with the flat base change `Spec L → Spec K`
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`,
`AlgebraicGeometry.Scheme.exists_isPullback_branchSchemeToSingularLocus`). Once nodes and branches
are split over `L`, the branch scheme is the trivial double cover of the singular subscheme
(`AlgebraicGeometry.Scheme.Hom.exists_split_of_finrank_eq`).

This labels nodes and branches only. Splitting the geometric components is not asserted here.

## Main results

* `AlgebraicGeometry.Scheme.exists_split_branchScheme`: over one finite Galois extension of the
  base field, the nodes of a proper nodal curve split into rational points and its branch scheme
  into two copies of them.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
* The Stacks Project, Tag 0C58 (families of nodal curves).
* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **The nodes and branches of a proper nodal curve split over one finite Galois extension.**
There are a finite Galois extension `L / K` and `n : ℕ` such that, for every base change `X'` of
the curve to `L`, the singular subscheme of `X'` is `Spec (Fin n → L)` as a scheme over `L`, and
the branch scheme of `X'` is `Spec (Fin 2 → Fin n → L)` as a scheme over the singular subscheme,
through the diagonal inclusion of `Fin n → L` into `Fin 2 → Fin n → L`. Thus the nodes are `n`
rational points, each with two rational branches indexed by `Fin 2`, and swapping the two indices
is the pairing involution of the branches. This includes the smooth case `n = 0`. -/
theorem exists_split_branchScheme {K : Type u} [Field K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      ∀ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of L))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
          (Spec.algebraMap K L)),
        letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of L)) :=
          (MorphismProperty.of_isPullback H hnodal).syntomic
        ∃ (e : (X'.singularLocus L).subscheme ≅ Spec (.of (Fin n → L)))
          (e' : X'.branchScheme L ≅ Spec (.of (Fin 2 → Fin n → L))),
          e.hom ≫ Spec.algebraMap L (Fin n → L) =
              (X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L)) ∧
            e'.hom ≫ Spec.algebraMap (Fin n → L) (Fin 2 → Fin n → L) =
              X'.branchSchemeToSingularLocus L ≫ e.hom := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  -- Split the nodes and the branches of `X` over one finite Galois extension `L`.
  obtain ⟨L, _, _, _, _, n, m, ⟨eS⟩, ⟨eB⟩⟩ := Scheme.Hom.exists_split_of_isFinite_of_etale₂
    ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K)))
    (X.branchSchemeToSingularLocus K ≫ (X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K)))
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, ?_⟩
  intro X' _ g H
  have hnodal' := MorphismProperty.of_isPullback H hnodal
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of L)) := hnodal'.syntomic
  have := X'.isFinite_branchSchemeToSingularLocus hnodal'
  have := X'.etale_branchSchemeToSingularLocus hnodal'
  -- The nodes and branches of `X'` are the base changes of those of `X`, hence split over `L`.
  have Hbase := (Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H
  obtain ⟨f, Hbr⟩ := Scheme.exists_isPullback_branchSchemeToSingularLocus H
  let e := Hbase.isoPullback ≪≫ (Over.forget _).mapIso eS
  let eE := (Hbr.paste_vert Hbase).isoPullback ≪≫ (Over.forget _).mapIso eB
  have he : e.hom ≫ Spec.algebraMap L (Fin n → L) =
      (X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L)) := by
    have := Over.w eS.hom
    simp only [Over.mk_hom] at this
    simp [e, this]
  have hE : eE.hom ≫ Spec.algebraMap L (Fin m → L) = X'.branchSchemeToSingularLocus L ≫
      e.hom ≫ Spec.algebraMap L (Fin n → L) := by
    have := Over.w eB.hom
    simp only [Over.mk_hom] at this
    simp [eE, this, he]
  -- Every node has two branches, so the branch scheme is two copies of the nodes.
  obtain ⟨e', he'⟩ := Scheme.Hom.exists_split_of_finrank_eq _
    (X'.finrank_branchSchemeToSingularLocus hnodal') e eE hE
  exact ⟨e, e', he, he'⟩

end AlgebraicGeometry.Scheme
