/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup
public import TauCeti.AlgebraicGeometry.FiniteEtale.Splitting
public import TauCeti.AlgebraicGeometry.IrreducibleComponents.Geometric

/-!
# Splitting the nodes, branches and geometric components of a proper nodal curve

Let `X` be a proper nodal curve over a field `K`. Its singular subscheme `Sing(X/K)` is finite
étale over `K`, and its branch scheme `E` is finite étale of rank two over `Sing(X/K)`
(`AlgebraicGeometry.Scheme.finrank_branchSchemeToSingularLocus`). After one finite Galois
extension `L / K`, both become disjoint unions of rational points: the singular subscheme of the
base change `X_L` is `Spec (Fin n → L)`, a labelling of the `n` nodes, and its branch scheme is
`Spec (Fin 2 → Fin n → L)` over it, two copies of the nodes. So every node of `X_L` is a rational
point with two rational branches, labelled by `Fin 2`, and the pairing involution exchanging the
two branches through each node is the swap of the two copies. These labels persist over every
further field extension of `L`.

The splitting applies to every chosen base change of the curve: the singular subscheme and the
branch scheme commute with the flat base change `Spec L → Spec K`
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`,
`AlgebraicGeometry.Scheme.exists_isPullback_branchSchemeToSingularLocus`). Once nodes and branches
are split over `L`, the branch scheme is the trivial double cover of the singular subscheme
(`AlgebraicGeometry.Scheme.Hom.exists_split_of_finrank_eq`).

After a further finite separable extension, the irreducible components of the curve become
geometrically irreducible
(`AlgebraicGeometry.Scheme.Hom.exists_forall_bijOn_preimage_irreducibleComponents`), so one finite
separable extension labels the nodes, the branches with their pairing, and the geometric
components at once.

## Main results

* `AlgebraicGeometry.Scheme.exists_split_branchScheme`: over one finite Galois extension of the
  base field and every extension of it, the nodes of a proper nodal curve split into rational
  points and its branch scheme into two copies of them.
* `AlgebraicGeometry.Scheme.exists_split_branchScheme_irreducibleComponents`: over one finite
  separable extension, the nodes and branches split and every irreducible component is
  geometrically irreducible.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
* The Stacks Project, Tag 0C58 (families of nodal curves).
* The Stacks Project, Tag 03QR (schemes étale over a point).
* The Stacks Project, Section 33.8, *Geometrically irreducible schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **The nodes and branches of a proper nodal curve split over one finite Galois extension.**
There are a finite Galois extension `L / K` and `n : ℕ` such that, for every field extension
`F / L` and every base change `X'` of the curve to `F`, the singular subscheme of `X'` is
`Spec (Fin n → F)` as a scheme over `F`, and the branch scheme of `X'` is
`Spec (Fin 2 → Fin n → F)` as a scheme over the singular subscheme, through the diagonal inclusion
of `Fin n → F` into `Fin 2 → Fin n → F`. Thus the nodes are `n` rational points, each with two
rational branches indexed by `Fin 2`, and swapping the two indices is the pairing involution of
the branches. This includes the smooth case `n = 0`. -/
theorem exists_split_branchScheme {K : Type u} [Field K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      ∀ (F : Type u) [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
        (X' : Scheme.{u}) (_ : X'.Over (Spec (.of F))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of F)) (X ↘ Spec (.of K))
          (Spec.algebraMap K F)),
        letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of F)) :=
          (MorphismProperty.of_isPullback H hnodal).syntomic
        ∃ (e : (X'.singularLocus F).subscheme ≅ Spec (.of (Fin n → F)))
          (e' : X'.branchScheme F ≅ Spec (.of (Fin 2 → Fin n → F))),
          e.hom ≫ Spec.algebraMap F (Fin n → F) =
              (X'.singularLocus F).subschemeι ≫ (X' ↘ Spec (.of F)) ∧
            e'.hom ≫ Spec.algebraMap (Fin n → F) (Fin 2 → Fin n → F) =
              X'.branchSchemeToSingularLocus F ≫ e.hom := by
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
  intro F _ _ _ _ X' _ g H
  have hnodal' := MorphismProperty.of_isPullback H hnodal
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of F)) := hnodal'.syntomic
  have := X'.isFinite_branchSchemeToSingularLocus hnodal'
  have := X'.etale_branchSchemeToSingularLocus hnodal'
  -- The nodes and branches of `X'` are base changes along `Spec F ⟶ Spec L` of those of the
  -- base change of `X` to `L`, hence split over `F`.
  have hKF : Spec.algebraMap K F = Spec.algebraMap L F ≫ Spec.algebraMap K L := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have Hbase := (Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H
  obtain ⟨f, Hbr⟩ := Scheme.exists_isPullback_branchSchemeToSingularLocus H
  have Hbr' := Hbr.paste_vert Hbase
  rw [hKF] at Hbase Hbr'
  have hS := Over.w eS.hom
  have hB := Over.w eB.hom
  simp only [Over.mk_hom] at hS hB
  obtain ⟨e, he⟩ := Scheme.Hom.exists_split_of_isPullback
    (IsPullback.of_right' Hbase (IsPullback.of_hasPullback _ _)) ((Over.forget _).mapIso eS) hS
  obtain ⟨eE, hE⟩ := Scheme.Hom.exists_split_of_isPullback
    (IsPullback.of_right' Hbr' (IsPullback.of_hasPullback _ _)) ((Over.forget _).mapIso eB) hB
  -- Every node has two branches, so the branch scheme is two copies of the nodes.
  obtain ⟨e', he'⟩ := Scheme.Hom.exists_split_of_finrank_eq _
    (X'.finrank_branchSchemeToSingularLocus hnodal') e eE (by simp [he, hE])
  exact ⟨e, e', he, he'⟩

/-- **Nodes, branches and geometric components of a proper nodal curve split over one finite
separable extension.** There are a finite separable extension `L / K` and `n : ℕ` such that every
base change `X'` of the curve to `L` satisfies:
* the singular subscheme of `X'` is `Spec (Fin n → L)` over `L`, and the branch scheme of `X'` is
  `Spec (Fin 2 → Fin n → L)` over the singular subscheme, so the `n` nodes are labelled rational
  points, each with two rational branches labelled by `Fin 2`, the pairing involution of the
  branches being the swap of the two indices;
* every irreducible component of `X'` is geometrically irreducible: for every field extension
  `M / L` and every base change `h : X'' ⟶ X'` of `Spec M ⟶ Spec L`, the map `Z ↦ h ⁻¹' Z` is a
  bijection from the irreducible components of `X'` onto those of `X''`. Thus the irreducible
  components of `X'` label the geometric components of the curve. -/
theorem exists_split_branchScheme_irreducibleComponents {K : Type u} [Field K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L) (n : ℕ),
      ∀ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of L))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
          (Spec.algebraMap K L)),
        (letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of L)) :=
          (MorphismProperty.of_isPullback H hnodal).syntomic
        ∃ (e : (X'.singularLocus L).subscheme ≅ Spec (.of (Fin n → L)))
          (e' : X'.branchScheme L ≅ Spec (.of (Fin 2 → Fin n → L))),
          e.hom ≫ Spec.algebraMap L (Fin n → L) =
              (X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L)) ∧
            e'.hom ≫ Spec.algebraMap (Fin n → L) (Fin 2 → Fin n → L) =
              X'.branchSchemeToSingularLocus L ≫ e.hom) ∧
        ∀ (M : Type u) [Field M] [Algebra L M] {X'' : Scheme.{u}} {h : X'' ⟶ X'}
          {q : X'' ⟶ Spec (.of M)}, IsPullback h q (X' ↘ Spec (.of L)) (Spec.algebraMap L M) →
          Set.BijOn (h ⁻¹' ·) (irreducibleComponents X') (irreducibleComponents X'') := by
  -- Split the nodes and branches over a finite Galois `L₁ / K`, then the geometric components
  -- of the base change `X₁` of `X` to `L₁` over a finite separable `L / L₁`.
  obtain ⟨L₁, _, _, _, _, n, hsplit⟩ := exists_split_branchScheme X hnodal
  let f₁ := pullback.snd (X ↘ Spec (.of K)) (Spec.algebraMap K L₁)
  obtain ⟨L, _, _, _, _, hcomp⟩ := f₁.exists_forall_bijOn_preimage_irreducibleComponents
  let _ : Algebra K L := ((algebraMap L₁ L).comp (algebraMap K L₁)).toAlgebra
  have : IsScalarTower K L₁ L := .of_algebraMap_eq' rfl
  have : Module.Finite K L := .trans L₁ L
  have : Algebra.IsSeparable K L := .trans K L₁ L
  -- Every base change of `X` to `L` is a base change of `X₁` along `Spec L ⟶ Spec L₁`.
  have hKL : Spec.algebraMap K L = Spec.algebraMap L₁ L ≫ Spec.algebraMap K L₁ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have H₁ {X' : Scheme.{u}} {fX : X' ⟶ Spec (.of L)} {g : X' ⟶ X}
      (H : IsPullback g fX (X ↘ Spec (.of K)) (Spec.algebraMap K L)) :
      ∃ p₁ : X' ⟶ pullback (X ↘ Spec (.of K)) (Spec.algebraMap K L₁),
        IsPullback p₁ fX f₁ (Spec.algebraMap L₁ L) := by
    rw [hKL] at H
    exact ⟨_, IsPullback.of_right' H (IsPullback.of_hasPullback _ _)⟩
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n,
    fun X' _ g H ↦ ⟨hsplit L X' _ g H, fun M _ _ X'' h q HM ↦ ?_⟩⟩
  obtain ⟨p₁, H'⟩ := H₁ H
  exact hcomp H' M HM

end AlgebraicGeometry.Scheme
