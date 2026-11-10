/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.NormShell
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.OrthogonalGroup

/-!
# Orthogonal sums of root lattices and their glue words

A reducible simply-laced root system is a finite family `t : ι → DynkinType` of valid simply-laced
components; for an ordered list of components, `ι = Fin n` and the order of the components is the
order of the coordinates.  Its root lattice is the orthogonal sum
`⊥ i, (t i).rootLattice` (`TauCeti.IntegralLattice.pi`), and a glue word records one label of the
glue alphabet `(t i).glueAlphabet` per component (Conway--Sloane, Chapter 4 §3 and
Chapter 16 §1).

This file shows that the orthogonal sum of root lattices is even and positive definite, of rank
`∑ i, rank (t i)`, and identifies the orthogonal sum of the glue alphabets with the actual
discriminant quadratic module of the orthogonal sum of root lattices
(`TauCeti.DynkinType.glueWordIsometry`).  The identification acts componentwise by the
single-component isometries `TauCeti.DynkinType.glueAlphabetIsometry`
(`TauCeti.DynkinType.discriminantGroupPiEquiv_glueWordIsometry`), so a glue word is a coordinate
description of a class in the discriminant group.  The identification is natural under componentwise
isometries of the root lattices and under permutations of the components
(`TauCeti.DynkinType.discriminantQuadraticIsometry_pi_glueWordIsometry`,
`TauCeti.DynkinType.discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry`), so glue words
may be transported along either change of coordinates; when all components have the same type,
the two combine to signed permutations of the components
(`TauCeti.DynkinType.discriminantQuadraticIsometry_signedPerm_glueWordIsometry`).
Isotropic and Lagrangian subgroups of glue words correspond to those of the discriminant group by
`TauCeti.FiniteQuadraticModule.Isometry.isIsotropic_map_iff` and
`TauCeti.FiniteQuadraticModule.Isometry.isLagrangian_map_iff`.

## Main declarations

* `TauCeti.DynkinType.isEven_pi_rootLattice`, `TauCeti.DynkinType.isPosDef_pi_rootLattice`,
  `TauCeti.DynkinType.finrank_pi_rootLattice`: the orthogonal sum of root lattices is even,
  positive definite, and of rank the sum of the ranks.
* `TauCeti.DynkinType.glueWordIsometry`: the isometry from the orthogonal sum of glue alphabets
  to the discriminant quadratic module of the orthogonal sum of root lattices.
* `TauCeti.DynkinType.discriminantQuadraticIsometry_pi_glueWordIsometry`,
  `TauCeti.DynkinType.discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry`: naturality of
  the glue-word isometry under componentwise isometries and permutations of the components.
* `TauCeti.DynkinType.discriminantQuadraticIsometry_signedPerm_glueWordIsometry`: naturality of
  the glue-word isometry under signed permutations of identical components.
* `TauCeti.DynkinType.piGlueAlphabetCongr`: the glue words of a family of components equal to a
  reindexing of `t`.
* `TauCeti.DynkinType.piGlueAlphabetCongr_refl`, `TauCeti.DynkinType.piGlueAlphabetCongr_trans`:
  reindexing glue words along the identity is the identity, and along a composite is reindexing
  along each factor in turn.
* `TauCeti.DynkinType.isNondegenerate_pi_glueAlphabet`,
  `TauCeti.DynkinType.natCard_pi_glueAlphabet`: the module of glue words is nondegenerate, of
  order `∏ i, |det (t i).cartanMatrix|`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3, and
  Chapter 16, §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- The orthogonal sum of the root lattices of simply-laced components is even. -/
theorem isEven_pi_rootLattice : (pi fun i ↦ (t i).rootLattice (ht i)).IsEven :=
  isEven_pi fun i ↦ (t i).isEven_rootLattice (ht i)

/-- The orthogonal sum of the root lattices of simply-laced components is positive definite. -/
theorem isPosDef_pi_rootLattice : (pi fun i ↦ (t i).rootLattice (ht i)).IsPosDef :=
  (isPosDef_pi_iff _).mpr fun i ↦ (t i).isPosDef_rootLattice (ht i)

/-- The rank of the orthogonal sum of the root lattices of simply-laced components is the sum of
the ranks of the components. -/
theorem finrank_pi_rootLattice :
    Module.finrank ℤ (pi fun i ↦ (t i).rootLattice (ht i)) = ∑ i, (t i).rank := by
  simp only [finrank_pi, finrank_rootLattice]

/-- The roots of a finite orthogonal sum of ADE root lattices span its carrier. -/
theorem span_vectorsOfNorm_two_pi_rootLattice :
    Submodule.span ℤ
        ((fun x : pi fun i ↦ (t i).rootLattice (ht i) ↦
          (x : ∀ i, Fin (t i).rank → ℚ)) ''
          (pi fun i ↦ (t i).rootLattice (ht i)).vectorsOfNorm 2) =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier :=
  span_image_vectorsOfNorm_pi_eq _ fun i ↦ (t i).span_vectorsOfNorm_two_rootLattice (ht i)

/-- **Glue words are the discriminant classes of an orthogonal sum of root lattices.**  For a
finite family of valid simply-laced components, this is the isometry from the orthogonal sum of
the glue alphabets to the discriminant quadratic module of the orthogonal sum of the root
lattices, acting on each component by `TauCeti.DynkinType.glueAlphabetIsometry`. -/
noncomputable def glueWordIsometry (hv : ∀ i, (t i).Valid) :
    FiniteQuadraticModule.Isometry (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))
      ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantQuadraticModule
        (isEven_pi_rootLattice t ht)) :=
  discriminantQuadraticIsometryPiOfIsometry _ fun i ↦ (t i).glueAlphabetIsometry (hv i) (ht i)

/-- The glue-word isometry sends a word to the class whose component in the discriminant group
of each root lattice is the image of the corresponding label. -/
@[simp]
theorem discriminantGroupPiEquiv_glueWordIsometry (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    discriminantGroupPiEquiv _ (glueWordIsometry t ht hv w) i =
      (t i).glueAlphabetIsometry (hv i) (ht i) (w i) := by
  rw [glueWordIsometry]
  exact discriminantGroupPiEquiv_discriminantQuadraticIsometryPiOfIsometry _ _ w i

/-- The module of glue words of a finite family of valid simply-laced components is
nondegenerate. -/
theorem isNondegenerate_pi_glueAlphabet (hv : ∀ i, (t i).Valid) :
    (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsNondegenerate :=
  (FiniteQuadraticModule.isNondegenerate_pi_iff _).mpr fun i ↦
    (t i).isNondegenerate_glueAlphabet (hv i) (ht i)

/-- The module of glue words of a finite family of valid simply-laced components has order
`∏ i, |det (t i).cartanMatrix|`, the discriminant of the orthogonal sum of root lattices. -/
theorem natCard_pi_glueAlphabet (hv : ∀ i, (t i).Valid) :
    Nat.card (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) =
      ∏ i, (t i).cartanMatrix.det.natAbs := by
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ (t i).natCard_glueAlphabet (hv i) (ht i)

/-! ## Naturality of glue words

A componentwise isometry of root lattices, and a permutation of the components, act on glue words
and on discriminant classes compatibly with `TauCeti.DynkinType.glueWordIsometry`. -/

/-- **Naturality of glue words under componentwise isometries.**  Let `f i` be isometries from the
root lattices of the components `t i` to those of `s i`, and `g i` maps of glue labels compatible
with them through the component glue isometries.  Then the orthogonal sum of the `f i` carries the
discriminant class of a glue word `w` to the class of the word `i ↦ g i (w i)`. -/
theorem discriminantQuadraticIsometry_pi_glueWordIsometry (hv : ∀ i, (t i).Valid)
    {s : ι → DynkinType} {hs : ∀ i, (s i).IsSimplyLaced} (hvs : ∀ i, (s i).Valid)
    (f : ∀ i, IntegralLattice.Isometry ((t i).rootLattice (ht i)) ((s i).rootLattice (hs i)))
    (g : ∀ i, (t i).glueAlphabet (ht i) → (s i).glueAlphabet (hs i))
    (h : ∀ i x, (s i).glueAlphabetIsometry (hvs i) (hs i) (g i x) =
      (f i).discriminantQuadraticIsometry ((t i).isEven_rootLattice (ht i))
        ((t i).glueAlphabetIsometry (hv i) (ht i) x))
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (Isometry.pi f).discriminantQuadraticIsometry (isEven_pi_rootLattice t ht)
        (glueWordIsometry t ht hv w) =
      glueWordIsometry s hs hvs fun i ↦ g i (w i) :=
  discriminantQuadraticIsometry_pi_discriminantQuadraticIsometryPiOfIsometry _ _ f g h w

/-- **Naturality of glue words under permutations of the components.**  For an equivalence
`σ : κ ≃ ι`, reindexing the orthogonal sum of root lattices carries the discriminant class of a
glue word `w` of the reindexed components `k ↦ t (σ k)` to the class of the reindexed word, whose
label in position `σ k` is `w k`. -/
theorem discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry (hv : ∀ i, (t i).Valid)
    {κ : Type*} [Fintype κ] (σ : κ ≃ ι) (w : ∀ k, (t (σ k)).glueAlphabet (ht (σ k))) :
    (Isometry.piCongrLeft (fun i ↦ (t i).rootLattice (ht i)) σ).discriminantQuadraticIsometry
        (isEven_pi_rootLattice (fun k ↦ t (σ k)) fun k ↦ ht (σ k))
        (glueWordIsometry (fun k ↦ t (σ k)) (fun k ↦ ht (σ k)) (fun k ↦ hv (σ k)) w) =
      glueWordIsometry t ht hv (Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) σ w) :=
  discriminantQuadraticIsometry_piCongrLeft_discriminantQuadraticIsometryPiOfIsometry
    (fun i ↦ (t i).rootLattice (ht i)) (fun i ↦ (t i).glueAlphabetIsometry (hv i) (ht i)) σ w

section SignedPermutation

variable {T : DynkinType} {hT : T.IsSimplyLaced} (hvT : T.Valid)

/-- **Naturality of glue words under signed permutations of identical components.**  Let all
components have the same type `T`.  Multiplying component `i` of the orthogonal sum of root
lattices by the sign `u i` and then moving it to position `σ i` carries the discriminant class of
a glue word `w` to the class of the word whose label in position `j` is
`u (σ.symm j) • w (σ.symm j)`. -/
theorem discriminantQuadraticIsometry_signedPerm_glueWordIsometry (u : ι → ℤˣ)
    (σ : Equiv.Perm ι) (w : ∀ _ : ι, T.glueAlphabet hT) :
    ((Isometry.pi fun i ↦ Isometry.unitsSMul (u i) (T.rootLattice hT)).trans
        (Isometry.piCongrLeft (fun _ ↦ T.rootLattice hT) σ)).discriminantQuadraticIsometry
        (isEven_pi_rootLattice _ _) (glueWordIsometry (fun _ ↦ T) (fun _ ↦ hT) (fun _ ↦ hvT) w) =
      glueWordIsometry (fun _ ↦ T) (fun _ ↦ hT) (fun _ ↦ hvT)
        fun j ↦ u (σ.symm j) • w (σ.symm j) := by
  -- The signs act first, componentwise, and the permutation then moves the components.
  have h1 := (Isometry.discriminantQuadraticIsometry_apply _ (isEven_pi_rootLattice _ _)
    _).symm.trans (discriminantQuadraticIsometry_pi_glueWordIsometry (fun _ ↦ T)
      (fun _ ↦ hT) (fun _ ↦ hvT) (fun _ ↦ hvT)
      (fun i ↦ Isometry.unitsSMul (u i) (T.rootLattice hT))
      (fun i x ↦ u i • x) (fun i x ↦ by
        refine Eq.trans ?_ ((Isometry.discriminantQuadraticIsometry_apply _ _ _).trans
          (Isometry.discriminantGroupEquiv_unitsSMul_apply (u i) _ _)).symm
        exact map_zsmul (T.glueAlphabetIsometry hvT hT) (u i : ℤ) x) w)
  have h2 := (Isometry.discriminantQuadraticIsometry_apply _ (isEven_pi_rootLattice _ _)
    _).symm.trans (discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry (fun _ ↦ T)
      (fun _ ↦ hT) (fun _ ↦ hvT) σ (fun i ↦ u i • w i))
  refine (Isometry.discriminantQuadraticIsometry_apply _ _ _).trans ?_
  rw [Isometry.discriminantGroupEquiv_trans]
  refine (LinearEquiv.trans_apply _).trans ?_
  rw [h1]
  refine h2.trans (congrArg _ (funext fun j ↦ ?_))
  obtain ⟨k, rfl⟩ := σ.surjective j
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

end SignedPermutation

section OfEq

variable {κ : Type*} [Fintype κ] {s : κ → DynkinType} {hs : ∀ k, (s k).IsSimplyLaced}
  (σ : κ ≃ ι) (h : ∀ k, t (σ k) = s k)

/-- **Glue words of an equal family of components.**  If the components `s k` are the components
`t (σ k)` for an equivalence `σ : κ ≃ ι`, a glue word `w` of `t` gives the glue word of `s` whose
label in position `k` is the label `w (σ k)`, read in the equal alphabet of `s k`.  This is an
isometry of the modules of glue words. -/
noncomputable def piGlueAlphabetCongr :
    FiniteQuadraticModule.Isometry (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))
      (FiniteQuadraticModule.pi fun k ↦ (s k).glueAlphabet (hs k)) :=
  (QuadraticMap.IsometryEquiv.piCongrLeft (fun i ↦ ((t i).glueAlphabet (ht i)).quadratic)
      σ).symm.trans
    (QuadraticMap.IsometryEquiv.pi fun k ↦
      FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_congr (h k) (ht (σ k)) (hs k)))

/-- The glue word of the equal family `s` reads its label in position `k` from position `σ k`. -/
@[simp]
theorem piGlueAlphabetCongr_apply (w : ∀ i, (t i).glueAlphabet (ht i)) (k : κ) :
    piGlueAlphabetCongr t ht σ h w k =
      FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_congr (h k) (ht (σ k)) (hs k))
        (w (σ k)) := by
  conv_rhs => rw [← (QuadraticMap.IsometryEquiv.piCongrLeft
    (fun i ↦ ((t i).glueAlphabet (ht i)).quadratic) σ).apply_symm_apply w]
  rw [QuadraticMap.IsometryEquiv.piCongrLeft_apply_apply]
  -- `QuadraticMap.IsometryEquiv.pi` acts coordinatewise by definition.
  rfl

/-- Reindexing glue words along the identity equivalence is the identity. -/
@[simp]
theorem piGlueAlphabetCongr_refl (h : ∀ i, t (Equiv.refl ι i) = t i) :
    piGlueAlphabetCongr t ht (Equiv.refl ι) h (hs := ht) = QuadraticMap.IsometryEquiv.refl _ := by
  refine DFunLike.ext _ _ fun w ↦ funext fun i ↦ ?_
  rw [piGlueAlphabetCongr_apply, FiniteQuadraticModule.Isometry.ofEq_apply]
  -- A cast along an equality of a type with itself is the identity.
  exact cast_eq _ _

/-- Reindexing glue words along `σ` and then along `τ` is reindexing along `τ.trans σ`. -/
theorem piGlueAlphabetCongr_trans {μ : Type*} [Fintype μ] {u : μ → DynkinType}
    {hu : ∀ m, (u m).IsSimplyLaced} (τ : μ ≃ κ) (h' : ∀ m, s (τ m) = u m) :
    (piGlueAlphabetCongr t ht σ h).trans (piGlueAlphabetCongr s hs τ h' (hs := hu)) =
      piGlueAlphabetCongr t ht (τ.trans σ) fun m ↦
        (congrArg t (τ.trans_apply σ m)).trans ((h (τ m)).trans (h' m)) := by
  refine DFunLike.ext _ _ fun w ↦ funext fun m ↦ ?_
  rw [QuadraticMap.IsometryEquiv.trans_apply, piGlueAlphabetCongr_apply, piGlueAlphabetCongr_apply,
    piGlueAlphabetCongr_apply, FiniteQuadraticModule.Isometry.ofEq_apply,
    FiniteQuadraticModule.Isometry.ofEq_apply, FiniteQuadraticModule.Isometry.ofEq_apply, cast_cast]
  -- `τ.trans σ` applies `τ` and then `σ` by definition.
  rfl

end OfEq

end TauCeti.DynkinType
