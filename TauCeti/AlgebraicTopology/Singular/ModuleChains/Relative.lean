/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap
public import TauCeti.Topology.Category.TopPair

/-!
# Relative singular chains of a pair of `G`-spaces as a complex of representations

Let a group `G` act continuously on both spaces of a topological pair `(X, A)` so that the
embedding `A ⟶ X` is equivariant. Pushing chains forward along the embedding is then a chain map
`C(A; k) ⟶ C(X; k)` of complexes of representations of `G` (`TopPair.singularChainsRepι`, an
instance of `TauCeti.singularChainsRepResMap`), and its cokernel is the relative singular chain
complex of the pair as a chain complex of representations (`TopPair.singularChainsRep`).

The inclusion `C(A; k) ⟶ C(X; k)` is split in every degree by an equivariant retraction, which
keeps the singular simplices of `X` lying in `A` and kills the others: the action permutes the
simplices lying in `A` among themselves, since it preserves the image of the embedding
(`TopPair.isSplitMono_singularChainsRepι_f`). So the relative chains are a retract of the
chains of `X` in every degree, and when `G` acts freely on `X` they are projective
representations (`TopPair.projective_singularChainsRep_X`), as the absolute chains are
(`TauCeti.projective_singularChainsRep_X`).

These complexes are the relative form of the geometric resolutions of group homology: for a pair of
free `G`-spaces covering a pair `(B, A)`, the coinvariants of the relative chains with coefficients
in a representation `D` are the relative chains of `(B, A)` twisted by the local system associated
to `D` (`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`, in
`TauCeti.AlgebraicTopology.Singular.Twisted.QuotientCovering`).

## Main definitions

* `TopPair.singularChainsRepι`: the equivariant inclusion of the chains of the subspace.
* `TopPair.singularChainsRep`: the relative singular chains of a pair of `G`-spaces, as a chain
  complex of representations of `G`.
* `TopPair.singularChainsRepπ`: the quotient map from the equivariant chains of the ambient space.

## Main results

* `TopPair.isSplitMono_singularChainsRepι_f`: the inclusion of the chains of the subspace is split
  in every degree.
* `TopPair.projective_singularChainsRep_X`: for a free action on the ambient space, the terms are
  projective.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections I.4 and II.4.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti
open scoped Simplicial

universe u

namespace TopPair

variable (P : TopPair.{u}) (k : Type u) [CommRing k] (G : Type u) [Group G]
  [MulAction G P.fst] [MulAction G P.snd]

section Retraction

variable {G}

omit [MulAction G P.fst] [MulAction G P.snd] in
open Classical in
/-- The retraction of the singular chains of the ambient space of a pair onto those of the
subspace: it keeps the simplices lying in the subspace and kills the others. -/
private def chainsRetraction (n : ℕ) :
    ((singularChains k).obj P.fst).X n →ₗ[k] ((singularChains k).obj P.snd).X n :=
  chainsDesc (k := k) fun σ ↦
    if h : σ ∈ Set.range ((_root_.TopCat.toSSet.map P.map).app _) then
      simplexChain (k := k) h.choose 1 else 0

omit [MulAction G P.fst] [MulAction G P.snd] in
private theorem chainsRetraction_simplexChain_of_mem {n : ℕ}
    (τ : (_root_.TopCat.toSSet.obj P.snd) _⦋n⦌) :
    chainsRetraction P k n
      (simplexChain (k := k) ((_root_.TopCat.toSSet.map P.map).app _ τ) 1) =
        simplexChain (k := k) τ 1 := by
  have h : (_root_.TopCat.toSSet.map P.map).app _ τ ∈
      Set.range ((_root_.TopCat.toSSet.map P.map).app _) := ⟨τ, rfl⟩
  have : Mono P.map := (TopCat.mono_iff_injective _).2 P.isEmbedding_map.injective
  rw [chainsRetraction, chainsDesc_simplexChain_one, dite_eq_left_of_eq_true (eq_true h),
    (mono_iff_injective ((_root_.TopCat.toSSet.map P.map).app _)).1 inferInstance h.choose_spec]

omit [MulAction G P.fst] [MulAction G P.snd] in
private theorem chainsRetraction_simplexChain_of_notMem {n : ℕ}
    {σ : (_root_.TopCat.toSSet.obj P.fst) _⦋n⦌}
    (hσ : σ ∉ Set.range ((_root_.TopCat.toSSet.map P.map).app _)) :
    chainsRetraction P k n (simplexChain (k := k) σ 1) = 0 := by
  rw [chainsRetraction, chainsDesc_simplexChain_one, dite_eq_right_of_eq_false (eq_false hσ)]

variable [ContinuousConstSMul G P.fst] [ContinuousConstSMul G P.snd]
  (hP : ∀ (g : G) x, P.map (g • x) = g • P.map x)

variable (G) in
/-- The equivariant chain map pushing the singular chains of the subspace of a pair of `G`-spaces
forward to the ambient space, along the equivariant embedding. -/
def singularChainsRepι :
    TauCeti.singularChainsRep k P.snd G ⟶ TauCeti.singularChainsRep k P.fst G :=
  singularChainsRepResMap k (φ := MonoidHom.id G) P.map hP

/-- The inclusion of the chains of the subspace is the equivariant push-forward along the
embedding, read as a chain map into the restriction of the equivariant chains along the identity
of `G`. -/
theorem singularChainsRepι_def :
    P.singularChainsRepι k G hP = singularChainsRepResMap k (φ := MonoidHom.id G) P.map hP :=
  (rfl)

/-- The inclusion of the chains of the subspace pushes chains forward along the embedding. -/
@[simp]
theorem singularChainsRepι_f_hom_apply (n : ℕ) (c : ((singularChains k).obj P.snd).X n) :
    ((P.singularChainsRepι k G hP).f n).hom c = ((singularChains k).map P.map).f n c :=
  singularChainsRepResMap_f_hom_apply k P.map hP n c

/-- The retraction of `chainsRetraction` is equivariant. -/
private def chainsRetractionRep (n : ℕ) :
    (singularChainsRep k P.fst G).X n ⟶ (singularChainsRep k P.snd G).X n :=
  Rep.ofHom
    { toLinearMap := chainsRetraction P k n
      isIntertwining' g := singularChains_linearMap_ext fun σ ↦ by
        simp only [LinearMap.comp_apply, singularChainsRepresentation_simplexChain]
        by_cases hσ : σ ∈ Set.range ((_root_.TopCat.toSSet.map P.map).app _)
        · obtain ⟨τ, rfl⟩ := hσ
          rw [← MonoidHom.id_apply G g, ← TopCat.toSSet_map_app_smul P.map hP,
            chainsRetraction_simplexChain_of_mem, chainsRetraction_simplexChain_of_mem,
            singularChainsRepresentation_simplexChain, MonoidHom.id_apply]
        · -- A translate of a simplex leaving the subspace leaves it too.
          have hgσ : g • σ ∉ Set.range ((_root_.TopCat.toSSet.map P.map).app _) := by
            rintro ⟨τ, hτ⟩
            refine hσ ⟨g⁻¹ • τ, ?_⟩
            rw [TopCat.toSSet_map_app_smul (φ := MonoidHom.id G) P.map hP, hτ, MonoidHom.id_apply,
              inv_smul_smul]
          rw [chainsRetraction_simplexChain_of_notMem P k hσ,
            chainsRetraction_simplexChain_of_notMem P k hgσ, map_zero] }

/-- **The chains of the subspace split off equivariantly.** For a pair of `G`-spaces with an
equivariant embedding, pushing singular `n`-chains forward from the subspace to the ambient space
is a split monomorphism of representations of `G`. -/
theorem isSplitMono_singularChainsRepι_f (n : ℕ) :
    IsSplitMono ((P.singularChainsRepι k G hP).f n) :=
  .mk' ⟨chainsRetractionRep P k hP n, by
    have h : chainsRetraction P k n ∘ₗ (((singularChains k).map P.map).f n).hom = LinearMap.id :=
      singularChains_linearMap_ext fun τ ↦ (congrArg (chainsRetraction P k n)
        (singularChains_map_f_simplexChain P.map τ 1)).trans
          (chainsRetraction_simplexChain_of_mem P k τ)
    ext c
    exact (congrArg (chainsRetraction P k n)
      (P.singularChainsRepι_f_hom_apply k hP n c)).trans (LinearMap.congr_fun h c)⟩

end Retraction

variable [ContinuousConstSMul G P.fst] [ContinuousConstSMul G P.snd]
  (hP : ∀ (g : G) x, P.map (g • x) = g • P.map x)

/-- **The relative singular chains of a pair of `G`-spaces**, as a chain complex of
representations of `G`: the cokernel of the equivariant chain map pushing chains forward along the
embedding of the subspace. -/
def singularChainsRep : ChainComplex (Rep.{u} k G) ℕ :=
  cokernel (P.singularChainsRepι k G hP)

/-- The quotient map from the equivariant singular chains of the ambient space onto the relative
chains. -/
def singularChainsRepπ : TauCeti.singularChainsRep k P.fst G ⟶ P.singularChainsRep k G hP :=
  cokernel.π _

instance epi_singularChainsRepπ : Epi (P.singularChainsRepπ k G hP) := coequalizer.π_epi

/-- The chains of the subspace vanish in the relative chains. -/
@[reassoc (attr := simp)]
theorem singularChainsRepι_comp_singularChainsRepπ :
    P.singularChainsRepι k G hP ≫ P.singularChainsRepπ k G hP = 0 :=
  cokernel.condition _

/-- The relative chains are the cokernel of the inclusion of the chains of the subspace. -/
def isColimitCokernelCoforkSingularChainsRep :
    IsColimit (CokernelCofork.ofπ (P.singularChainsRepπ k G hP)
      (P.singularChainsRepι_comp_singularChainsRepπ k G hP)) :=
  cokernelIsCokernel _

/-- **The relative chains of a free pair are projective.** If `G` acts freely on the ambient
space, each term of the relative singular chain complex is a projective representation, a retract
of the free representation on the singular simplices of the ambient space. -/
instance projective_singularChainsRep_X [IsCancelSMul G P.fst] (n : ℕ) :
    Projective ((P.singularChainsRep k G hP).X n) := by
  have := P.isSplitMono_singularChainsRepι_f k hP n
  let b := binaryBiconeOfIsSplitMonoOfCokernel
    (cokernelIsCokernel ((P.singularChainsRepι k G hP).f n))
  have : Projective b.pt :=
    inferInstanceAs (Projective ((TauCeti.singularChainsRep k P.fst G).X n))
  have : Projective (cokernel ((P.singularChainsRepι k G hP).f n)) :=
    b.retract_right.projective
  exact Projective.of_iso (PreservesCokernel.iso (HomologicalComplex.eval _ _ n) _).symm this

end TopPair
