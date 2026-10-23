/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Contractible
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.Topology.Category.TopCat.Action

/-!
# The singular chains of a contractible free `G`-space as a projective resolution

Let a monoid `G` act on a space `E` by continuous maps. Pushing singular chains forward along the
translations `g • ·` makes each group of singular `n`-chains of `E` with coefficients in a
commutative ring `k` a representation of `G` (`TauCeti.singularChainsRepresentation`), and the
singular boundary is equivariant, so the singular chains form a chain complex of representations
(`TauCeti.singularChainsRep`). Forgetting the action gives back the singular chain complex
(`TauCeti.singularChainsRepForget₂Iso`), and the sum of the coefficients of a `0`-chain is an
augmentation onto the trivial representation (`TauCeti.singularChainsRepAugmentation`).

The `n`-chains are the permutation representation of `G` on the singular `n`-simplices
(`TauCeti.singularChainsEquivOfMulAction`). If `G` is a group acting freely on `E`, it acts
freely on singular simplices, since a simplex is moved off itself already at one point; so each
term is a free representation, in particular a projective one
(`TauCeti.projective_singularChainsRep_X`). If `E` is moreover contractible, the augmented
singular chain complex is exact (`TauCeti.quasiIso_singularChainsAugmentation`), and the singular
chains of `E` are a projective resolution of the trivial representation
(`TauCeti.singularChainsResolution`). For the total space of a free cover with contractible total
space, such as the universal cover of a `K(G, 1)` CW complex, this resolution computes the group
homology of `G`.

## Main definitions

* `TauCeti.singularChainsRepresentation`: the action of `G` on singular `n`-chains.
* `TauCeti.singularChainsRep`: the singular chain complex of `E`, as a chain complex of
  representations of `G`.
* `TauCeti.singularChainsRepAugmentation`: its augmentation onto the trivial representation.
* `TauCeti.singularChainsEquivOfMulAction`: the `n`-chains are the permutation representation on
  singular `n`-simplices.
* `TauCeti.singularChainsResolution`: for a free action on a contractible space, the projective
  resolution of the trivial representation by the singular chains.

## Main results

* `TauCeti.projective_singularChainsRep_X`: for a free action, the terms are projective.
* `TauCeti.quasiIso_singularChainsRepAugmentation`: for contractible `E`, the augmentation is a
  quasi-isomorphism.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace TauCeti

section Equivariant

variable (k : Type u) [CommRing k] (E : TopCat.{u}) (G : Type u) [Monoid G] [MulAction G E]
  [ContinuousConstSMul G E]

/-- The action of `G` on the singular `n`-chains of a `G`-space `E`: `g` acts by pushing chains
forward along the translation `g • ·`. -/
def singularChainsRepresentation (n : ℕ) :
    Representation k G (((singularChains k).obj E).X n) where
  toFun g := (((singularChains k).map
    (TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩)).f n).hom
  map_one' := by
    have : TopCat.ofHom ⟨((1 : G) • · : E → E), continuous_const_smul 1⟩ = 𝟙 E :=
      ConcreteCategory.hom_ext _ _ fun x ↦ one_smul G x
    rw [this, CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    have : TopCat.ofHom ⟨((g * h) • · : E → E), continuous_const_smul (g * h)⟩ =
        TopCat.ofHom ⟨(h • · : E → E), continuous_const_smul h⟩ ≫
          TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩ :=
      ConcreteCategory.hom_ext _ _ fun x ↦ mul_smul g h x
    rw [this, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      Module.End.mul_eq_comp]

variable {k E G}

/-- An element `g` acts on singular `n`-chains by the chain map of the translation `g • ·`. -/
lemma singularChainsRepresentation_apply (n : ℕ) (g : G) :
    singularChainsRepresentation k E G n g = (((singularChains k).map
      (TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩)).f n).hom :=
  (rfl)

/-- An element `g` sends the chain of a simplex `σ` to the chain of the translated simplex
`g • σ`. -/
@[simp]
theorem singularChainsRepresentation_simplexChain {n : ℕ} (g : G)
    (σ : (TopCat.toSSet.obj E) _⦋n⦌) (a : k) :
    singularChainsRepresentation k E G n g (simplexChain σ a) = simplexChain (g • σ) a := by
  rw [singularChainsRepresentation_apply, singularChains_map_f_simplexChain,
    TauCeti.TopCat.toSSetObj_smul_def]

variable (k E G)

/-- The singular boundary is `G`-equivariant, so it is a morphism of representations. -/
def singularChainsRepDifferential (n : ℕ) :
    Rep.of (singularChainsRepresentation k E G (n + 1)) ⟶
      Rep.of (singularChainsRepresentation k E G n) :=
  Rep.ofHom
    { toLinearMap := (((singularChains k).obj E).d (n + 1) n).hom
      isIntertwining' g := LinearMap.ext fun x ↦ ConcreteCategory.congr_hom (((singularChains k).map
        (TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩)).comm (n + 1) n) x }

/-- The equivariant singular boundary is the singular boundary. -/
@[simp]
lemma singularChainsRepDifferential_hom_apply (n : ℕ) (c : ((singularChains k).obj E).X (n + 1)) :
    (singularChainsRepDifferential k E G n).hom c = ((singularChains k).obj E).d (n + 1) n c :=
  (rfl)

/-- **The singular chains of a `G`-space as a chain complex of representations of `G`**: in
degree `n` it is the representation `TauCeti.singularChainsRepresentation` on the singular
`n`-chains, and its differential is the singular boundary. -/
-- The body is exposed, as for Mathlib's `Rep.standardComplex`, so that its terms are the
-- representations `TauCeti.singularChainsRepresentation` by definition; `singularChainsRep_d` and
-- the comparison with the singular chains of the orbit space rely on this.
@[expose]
def singularChainsRep : ChainComplex (Rep.{u} k G) ℕ :=
  ChainComplex.of (fun n ↦ Rep.of (singularChainsRepresentation k E G n))
    (singularChainsRepDifferential k E G) fun n ↦ by
      ext x
      exact ConcreteCategory.congr_hom (((singularChains k).obj E).d_comp_d (n + 2) (n + 1) n) x

/-- The terms of the equivariant singular chain complex are the representations
`TauCeti.singularChainsRepresentation`. -/
@[simp]
lemma singularChainsRep_X (n : ℕ) :
    (singularChainsRep k E G).X n = Rep.of (singularChainsRepresentation k E G n) :=
  (rfl)

/-- The differentials of the equivariant singular chain complex are the singular boundaries. -/
@[simp]
lemma singularChainsRep_d (n : ℕ) :
    (singularChainsRep k E G).d (n + 1) n = singularChainsRepDifferential k E G n :=
  ChainComplex.of_d (fun n ↦ Rep.of (singularChainsRepresentation k E G n))
    (singularChainsRepDifferential k E G) n

/-- **Forgetting the action of `G`, the equivariant singular chain complex is the singular chain
complex** of `E`: the components of this isomorphism are identities. -/
def singularChainsRepForget₂Iso :
    ((forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (singularChainsRep k E G) ≅ (singularChains k).obj E :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i j (h : j + 1 = i) ↦ by
    subst h
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d, singularChainsRep_d]
    -- `forget₂` sends `singularChainsRepDifferential` to its underlying linear map
    -- (`Rep.forget₂_moduleCat_map`), the singular boundary; the components are identities between
    -- objects that agree only by definition (`singularChainsRep_X`), so this closes by `rfl`.
    rfl

/-- The components of `TauCeti.singularChainsRepForget₂Iso` are identities. -/
@[simp]
lemma singularChainsRepForget₂Iso_hom_f (n : ℕ) :
    (singularChainsRepForget₂Iso k E G).hom.f n = 𝟙 _ :=
  (rfl)

/-- The augmentation of the singular `0`-chains of `E`, the sum of the coefficients, as a
morphism to the trivial representation: pushing chains forward preserves the augmentation. -/
def singularAugmentRep :
    Rep.of (singularChainsRepresentation k E G 0) ⟶ Rep.trivial k G k :=
  Rep.ofHom
    { toLinearMap := singularAugment k E
      isIntertwining' g := LinearMap.ext fun x ↦ singularAugment_map
        (TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩) x }

/-- The underlying linear map of `TauCeti.singularAugmentRep` is the augmentation. -/
@[simp]
lemma singularAugmentRep_hom_toLinearMap :
    (singularAugmentRep k E G).hom.toLinearMap = singularAugment k E :=
  (rfl)

/-- The **augmentation** of the equivariant singular chains: the chain map to the trivial
representation, placed in degree `0`, that sums the coefficients of a `0`-chain. -/
def singularChainsRepAugmentation :
    singularChainsRep k E G ⟶ (ChainComplex.single₀ (Rep.{u} k G)).obj (Rep.trivial k G k) :=
  ((singularChainsRep k E G).toSingle₀Equiv _).symm
    ⟨singularAugmentRep k E G, by
      ext x
      exact singularAugment_d E x⟩

/-- In degree `0` the equivariant augmentation is `TauCeti.singularAugmentRep`. -/
@[simp]
lemma singularChainsRepAugmentation_f_zero :
    (singularChainsRepAugmentation k E G).f 0 = singularAugmentRep k E G :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmented singular chain complex of a contractible `G`-space is exact**: forgetting the
action, the augmentation is that of the singular chains of `E`. -/
instance quasiIso_singularChainsRepAugmentation [ContractibleSpace E] :
    QuasiIso (singularChainsRepAugmentation k E G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat k)),
    quasiIso_iff_of_arrow_mk_iso _ (singularChainsAugmentation k E) ?_]
  · infer_instance
  · refine Arrow.isoMk' _ _ (singularChainsRepForget₂Iso k E G)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    ext : 1
    simp only [HomologicalComplex.comp_f, singularChainsRepForget₂Iso_hom_f,
      singularChainsAugmentation_f_zero, Functor.mapHomologicalComplex_map_f,
      singularChainsRepAugmentation_f_zero]
    -- Both sides are the augmentation: `forget₂` sends `singularAugmentRep` to its underlying
    -- linear map (`Rep.forget₂_moduleCat_map`), and the remaining transports between the objects
    -- of the two complexes in degree `0` are identities by definition.
    rfl

/-- **The singular `n`-chains are the permutation representation on singular `n`-simplices**:
the chain of a simplex `σ` with coefficient `a` corresponds to `a` times the basis vector of `σ`,
and `G` acts on simplices by translation (`TauCeti.TopCat.mulActionToSSetObj`). -/
def singularChainsEquivOfMulAction (n : ℕ) :
    (singularChainsRepresentation k E G n).Equiv
      (Representation.ofMulAction k G ((TopCat.toSSet.obj E) _⦋n⦌)) :=
  .mk ((singularChainsLinearEquivFinsupp k E n).trans (MonoidAlgebra.coeffLinearEquiv k).symm)
    fun g ↦ singularChains_linearMap_ext fun σ ↦ by simp

end Equivariant

section Free

variable (k : Type u) [CommRing k] (E : TopCat.{u}) (G : Type u) [Group G] [MulAction G E]
  [ContinuousConstSMul G E] [IsCancelSMul G E]

/-- **The singular chains of a free `G`-space are free representations**: each term of the
equivariant singular chain complex is the permutation representation of a free action, on the
singular simplices (`TauCeti.TopCat.isCancelSMul_toSSetObj`), and so it is projective. -/
instance projective_singularChainsRep_X (n : ℕ) : Projective ((singularChainsRep k E G).X n) :=
  Projective.of_iso (Rep.mkIso (singularChainsEquivOfMulAction k E G n)).symm inferInstance

/-- **The singular chains of a contractible free `G`-space are a projective resolution** of the
trivial representation of `G` over `k`: `G` acts freely on singular simplices, so the terms are
free over the group ring, and the augmented singular chain complex of a contractible space is
exact. -/
-- The body is exposed, as for Mathlib's `Rep.standardResolution`, so that the complex of the
-- resolution is the equivariant singular chain complex by definition; the comparison of its
-- coinvariants with the singular chains of an orbit space is stated for that complex.
@[expose]
def singularChainsResolution [ContractibleSpace E] :
    ProjectiveResolution (Rep.trivial k G k) where
  complex := singularChainsRep k E G
  π := singularChainsRepAugmentation k E G

/-- The complex of `TauCeti.singularChainsResolution` is the equivariant singular chain
complex. -/
@[simp]
lemma singularChainsResolution_complex [ContractibleSpace E] :
    (singularChainsResolution k E G).complex = singularChainsRep k E G :=
  (rfl)

/-- The augmentation of `TauCeti.singularChainsResolution` is that of the equivariant singular
chains. -/
@[simp]
lemma singularChainsResolution_π [ContractibleSpace E] :
    (singularChainsResolution k E G).π = singularChainsRepAugmentation k E G :=
  (rfl)

end Free

end TauCeti
