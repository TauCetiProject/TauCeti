/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Sequence
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic
-- Non-public: the extension of a linear functional from a subspace is used only inside proofs.
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The almost-split sequence of the `A₂` quiver

The `A₂` quiver `• → •` is the generalized Kronecker quiver on a one-element arrow type, and it has
exactly three indecomposable representations: the two vertex simples `S₁ = (k → 0)` and
`S₂ = (0 → k)` and the vertex projective `P₁ = (k →^{id} k)`, classified in
`TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable`. This file builds the short exact
sequence

`0 ⟶ S₂ ⟶ P₁ ⟶ S₁ ⟶ 0`

joining them and proves that it is an **almost-split (Auslander--Reiten) sequence**: its inclusion
is left almost split and its projection is right almost split. By the uniqueness theorem
`CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso` every almost-split sequence ending at `S₁`
is isomorphic to it, so `S₂` is the Auslander--Reiten translate of `S₁` and the Auslander--Reiten
quiver of the `A₂` quiver is the three-vertex mesh `S₂ → P₁ → S₁`.

Both lifting properties come out of a single computation at each end, and neither needs a
finiteness hypothesis. A morphism `M ⟶ S₁` is a pair consisting of a linear functional on the
vertex space of `M` at the source and the zero map at the target; it splits exactly when that
functional is nonzero somewhere on the kernel of the arrow
(`TauCeti.isSplitEpi_iff_exists_of_hom_simpleRep_src`), and when it is not, the functional kills
that kernel and hence extends along the arrow, which is precisely a factorization through
`P₁ ↠ S₁`. Dually a morphism `S₂ ⟶ M` is a vector of the vertex space of `M` at the target; it
splits exactly when that vector misses the image of the arrow
(`TauCeti.isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt`), and when it does not, a preimage of
it under the arrow is what a factorization through `S₂ ↪ P₁` needs at the source.

## Main definitions

* `TauCeti.kroneckerProjSrcEquiv` and `TauCeti.kroneckerProjTgtEquiv`: the two vertex spaces of
  `P₁` as the base field, the trivial path and the arrow being their basis vectors.
* `TauCeti.kroneckerSimpleTgtToIndecProjRep`: the inclusion `S₂ ↪ P₁`.
* `TauCeti.kroneckerArSequence`: the short complex `0 ⟶ S₂ ⟶ P₁ ⟶ S₁ ⟶ 0`.

## Main results

* `TauCeti.isSplitEpi_iff_exists_of_hom_simpleRep_src` and
  `TauCeti.isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt`: **the two splitting criteria** at the
  two ends of the sequence.
* `TauCeti.indecProjRep_map_arrowPath_injective` and
  `TauCeti.indecProjRep_map_arrowPath_surjective`: **the arrow acts invertibly on `P₁`**.
* `TauCeti.shortExact_kroneckerArSequence`: **the sequence is short exact**, the inclusion being a
  kernel of the projection.
* `TauCeti.isLeftAlmostSplit_kroneckerArSequence_f` and
  `TauCeti.isRightAlmostSplit_kroneckerArSequence_g`: **its two maps are almost split** on the
  corresponding sides.
* `TauCeti.isAlmostSplit_kroneckerArSequence`: **the sequence is almost split.**

## Implementation notes

The lifting quantifiers of `TauCeti.IsLeftAlmostSplit` and `TauCeti.IsRightAlmostSplit` range over
*all* representations of the quiver, with no finite-dimensionality restriction; the implementation
notes of `TauCeti/CategoryTheory/AlmostSplit/Basic.lean` record that this is a strictly stronger
condition than the one an Auslander--Reiten theory over a finite-dimensional algebra asks for, and
that the general existence theorem fails in that form. Nothing is lost by proving the stronger
statement here: the two criteria above hold for an arbitrary representation, because the extension
of a linear functional from a subspace and the existence of a functional separating a vector from
a subspace are available over a field in any dimension.

## References

This supplies the Auslander--Reiten half of the "`A₂` quiver" worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose acceptance criterion
asks for the AR quiver of `A₂` to be "the three-vertex mesh `S₂ → P₁ → S₁` with `τ S₁ = S₂`", and
builds on the Layer 6 machinery of that roadmap; its path-algebra half is
`TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular` and its classification half is
`TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable`. See Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. IV, and Schiffler,
*Quiver Representations*, Ch. 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type)

/-! ### The two vertex spaces of `P₁` -/

/-- The vector space `(P₁)₁` that the projective `P₁` of the `A₂` quiver puts at the source is a
line: the trivial path is its only basis vector. -/
noncomputable def kroneckerProjSrcEquiv :
    (indecProjRep k (Quiver.Kronecker A) src).obj src ≃ₗ[k] k :=
  (indecProjRepBasis k src src).repr.trans (Finsupp.uniqueLinearEquiv k k Quiver.Path.nil)

variable [Unique A]

/-- The vector space `(P₁)₂` that the projective `P₁` of the `A₂` quiver puts at the target is a
line: the single arrow is its only basis vector. -/
noncomputable def kroneckerProjTgtEquiv :
    (indecProjRep k (Quiver.Kronecker A) src).obj tgt ≃ₗ[k] k :=
  (indecProjRepBasis k src tgt).repr.trans (Finsupp.uniqueLinearEquiv k k (arrowPath default))

variable {k A}

omit [Unique A] in
/-- The identification of `(P₁)₁` with the base field sends its basis vector to `1`. -/
@[simp]
theorem kroneckerProjSrcEquiv_basis (p : Quiver.Path (src : Quiver.Kronecker A) src) :
    kroneckerProjSrcEquiv k A (indecProjRepBasis k src src p) = 1 := by
  rw [kroneckerProjSrcEquiv]
  simp [Subsingleton.elim p Quiver.Path.nil]

/-- The identification of `(P₁)₂` with the base field sends its basis vector to `1`. -/
@[simp]
theorem kroneckerProjTgtEquiv_basis (p : Quiver.Path (src : Quiver.Kronecker A) tgt) :
    kroneckerProjTgtEquiv k A (indecProjRepBasis k src tgt p) = 1 := by
  rw [kroneckerProjTgtEquiv]
  simp [Subsingleton.elim p (arrowPath default)]

/-- **The arrow of the `A₂` quiver acts on `P₁` by the identity**, read through the two
identifications of its vertex spaces with the base field. -/
@[simp]
theorem kroneckerProjTgtEquiv_map (a : A)
    (x : (indecProjRep k (Quiver.Kronecker A) src).obj src) :
    kroneckerProjTgtEquiv k A ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath a) x)
      = kroneckerProjSrcEquiv k A x := by
  have h : (kroneckerProjTgtEquiv k A).toLinearMap ∘ₗ
      ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath a)).hom
        = (kroneckerProjSrcEquiv k A).toLinearMap :=
    Module.Basis.ext (indecProjRepBasis k src src) fun p ↦ by
      simp [indecProjRep_map_basis]
  exact LinearMap.congr_fun h x

/-! ### Two helpers -/

omit [Unique A] in
/-- Two equal morphisms of modules agree on every element. The analogue for a general concrete
category, `CategoryTheory.ConcreteCategory.congr_fun`, is not available in the pinned Mathlib. -/
private theorem congr_hom_apply {M N : ModuleCat.{u} k} {f g : M ⟶ N} (h : f = g) (x : M) :
    f x = g x := by
  rw [h]

omit [Unique A] in
/-- A zero object of `ModuleCat` has only the zero element. -/
private theorem eq_zero_of_isZero {M : ModuleCat.{u} k} (h : IsZero M) (x : M) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero h).elim x 0

/-! ### The two maps of the sequence -/

variable (k A) in
/-- **The inclusion `S₂ ↪ P₁`** of the vertex simple at the target of the `A₂` quiver into the
vertex projective at its source: the zero map at the source, and the identification of the two
lines at the target. -/
noncomputable def kroneckerSimpleTgtToIndecProjRep :
    simpleRep k (Quiver.Kronecker A) tgt ⟶ indecProjRep k (Quiver.Kronecker A) src :=
  kroneckerHom 0
    (ModuleCat.ofHom ((kroneckerProjTgtEquiv k A).symm.toLinearMap ∘ₗ
      (simpleRepSelfEquiv k tgt).toLinearMap))
    fun _ ↦ (isZero_simpleRep_obj src_ne_tgt).eq_of_src _ _

/-- At the source, the inclusion `S₂ ↪ P₁` is the zero map, its source vertex space being zero. -/
@[simp]
theorem kroneckerSimpleTgtToIndecProjRep_app_src :
    (kroneckerSimpleTgtToIndecProjRep k A).app src = 0 :=
  kroneckerHom_app_src _ _ _

/-- At the target, the inclusion `S₂ ↪ P₁` identifies the two lines. -/
@[simp]
theorem kroneckerSimpleTgtToIndecProjRep_app_tgt :
    (kroneckerSimpleTgtToIndecProjRep k A).app tgt
      = ModuleCat.ofHom ((kroneckerProjTgtEquiv k A).symm.toLinearMap ∘ₗ
        (simpleRepSelfEquiv k tgt).toLinearMap) :=
  kroneckerHom_app_tgt _ _ _

/-- The value of the inclusion `S₂ ↪ P₁` at the target, on an element. -/
theorem kroneckerSimpleTgtToIndecProjRep_app_tgt_apply
    (x : (simpleRep k (Quiver.Kronecker A) tgt).obj tgt) :
    (kroneckerSimpleTgtToIndecProjRep k A).app tgt x
      = (kroneckerProjTgtEquiv k A).symm (simpleRepSelfEquiv k tgt x) := by
  rw [kroneckerSimpleTgtToIndecProjRep_app_tgt]
  rfl

/-! ### The sequence -/

variable (k A) in
/-- **The Auslander--Reiten sequence of the `A₂` quiver** `0 ⟶ S₂ ⟶ P₁ ⟶ S₁ ⟶ 0`. -/
-- The second map repeats the construction of `indecProjRepToSimpleRep`, which asks for a base field
-- in the universe `max v w` of the vertices and the arrows, hence `k : Type` for the small vertex
-- and arrow types here, whereas this file takes `k : Type u`.
-- `@[expose]` is needed by the *statements* of `kroneckerArSequence_f` and `kroneckerArSequence_g`
-- below: they compare a morphism of `(kroneckerArSequence k A).X₁ ⟶ (kroneckerArSequence k A).X₂`
-- with one of `S₂ ⟶ P₁`, and those hom-types agree only once the body reduces.
@[expose] noncomputable def kroneckerArSequence : ShortComplex (QuiverRep k (Quiver.Kronecker A)) :=
  ShortComplex.mk (kroneckerSimpleTgtToIndecProjRep k A)
    (indecProjRepHom src (simpleRep k (Quiver.Kronecker A) src) (simpleRepGenerator k src))
    (by
      refine kroneckerRep_hom_ext ?_ ?_
      · refine ((NatTrans.comp_app _ _ _).trans ?_).trans (NatTrans.app_zero _).symm
        rw [kroneckerSimpleTgtToIndecProjRep_app_src, zero_comp]
      · exact (isZero_simpleRep_obj src_ne_tgt.symm).eq_of_tgt _ _)

/-- The left-hand end of the sequence is the vertex simple at the target. -/
@[simp]
theorem kroneckerArSequence_X₁ :
    (kroneckerArSequence k A).X₁ = simpleRep k (Quiver.Kronecker A) tgt := rfl

/-- The middle term of the sequence is the vertex projective at the source. -/
@[simp]
theorem kroneckerArSequence_X₂ :
    (kroneckerArSequence k A).X₂ = indecProjRep k (Quiver.Kronecker A) src := rfl

/-- The right-hand end of the sequence is the vertex simple at the source. -/
@[simp]
theorem kroneckerArSequence_X₃ :
    (kroneckerArSequence k A).X₃ = simpleRep k (Quiver.Kronecker A) src := rfl

/-- The first map of the sequence is the inclusion `S₂ ↪ P₁`. -/
@[simp]
theorem kroneckerArSequence_f :
    (kroneckerArSequence k A).f = kroneckerSimpleTgtToIndecProjRep k A := rfl

/-- The second map of the sequence is the morphism the universal property of `P₁` attaches to the
generator of the line `(S₁)₁`. -/
@[simp]
theorem kroneckerArSequence_g :
    (kroneckerArSequence k A).g
      = indecProjRepHom src (simpleRep k (Quiver.Kronecker A) src) (simpleRepGenerator k src) :=
  rfl

/-! ### The arrow acts invertibly on `P₁` -/

/-- **The arrow of the `A₂` quiver acts injectively on `P₁`.** -/
theorem indecProjRep_map_arrowPath_injective (a : A) :
    Function.Injective ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath a)).hom :=
  fun x y h ↦ (kroneckerProjSrcEquiv k A).injective
    ((kroneckerProjTgtEquiv_map a x).symm.trans
      ((congrArg (⇑(kroneckerProjTgtEquiv k A)) h).trans (kroneckerProjTgtEquiv_map a y)))

/-- **The arrow of the `A₂` quiver acts surjectively on `P₁`.** -/
theorem indecProjRep_map_arrowPath_surjective (a : A) :
    Function.Surjective ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath a)).hom := by
  intro y
  refine ⟨(kroneckerProjSrcEquiv k A).symm (kroneckerProjTgtEquiv k A y),
    (kroneckerProjTgtEquiv k A).injective ?_⟩
  rw [kroneckerProjTgtEquiv_map, LinearEquiv.apply_symm_apply]

/-- **The projection `P₁ ↠ S₁` is the identification of the two lines at the source**, read through
`TauCeti.simpleRepSelfEquiv` and `TauCeti.kroneckerProjSrcEquiv`. -/
theorem simpleRepSelfEquiv_kroneckerArSequence_g_app_src
    (y : (indecProjRep k (Quiver.Kronecker A) src).obj src) :
    simpleRepSelfEquiv k src ((kroneckerArSequence k A).g.app src y)
      = kroneckerProjSrcEquiv k A y := by
  have h : (simpleRepSelfEquiv k src).toLinearMap ∘ₗ ((kroneckerArSequence k A).g.app src).hom
      = (kroneckerProjSrcEquiv k A).toLinearMap :=
    Module.Basis.ext (indecProjRepBasis k src src) fun p ↦ by
      rw [Subsingleton.elim p Quiver.Path.nil]
      have h1 : (kroneckerArSequence k A).g.app src (indecProjRepBasis k src src Quiver.Path.nil)
          = simpleRepGenerator k src :=
        indecProjRepHom_app_nil src (simpleRep k (Quiver.Kronecker A) src)
          (simpleRepGenerator k src)
      exact ((congrArg (⇑(simpleRepSelfEquiv k src)) h1).trans
        (simpleRepSelfEquiv_apply_generator k src)).trans
        (kroneckerProjSrcEquiv_basis Quiver.Path.nil).symm
  exact LinearMap.congr_fun h y

/-! ### When a morphism at either end of the sequence splits -/

variable {Z : QuiverRep k (Quiver.Kronecker A)}

/-- **A morphism into the vertex simple `S₁` of the `A₂` quiver splits exactly when it is nonzero
somewhere on the kernel of the arrow.** A section of such a morphism is a vector of the source
vertex space killed by the arrow, on which the morphism does not vanish. -/
theorem isSplitEpi_iff_exists_of_hom_simpleRep_src
    (ψ : Z ⟶ simpleRep k (Quiver.Kronecker A) src) :
    IsSplitEpi ψ ↔ ∃ x : Z.obj src,
      Z.map (arrowPath (default : A)) x = 0 ∧ ψ.app src x ≠ 0 := by
  constructor
  · rintro ⟨⟨σ, hσ⟩⟩
    have hz : (simpleRep k (Quiver.Kronecker A) src).map (arrowPath (default : A))
        (simpleRepGenerator k src) = 0 :=
      eq_zero_of_isZero (isZero_simpleRep_obj src_ne_tgt.symm) _
    have hnat : σ.app tgt ((simpleRep k (Quiver.Kronecker A) src).map (arrowPath (default : A))
          (simpleRepGenerator k src))
        = Z.map (arrowPath (default : A)) (σ.app src (simpleRepGenerator k src)) :=
      congr_hom_apply (σ.naturality (arrowPath (default : A))) (simpleRepGenerator k src)
    have hid : σ.app src ≫ ψ.app src = 𝟙 ((simpleRep k (Quiver.Kronecker A) src).obj src) :=
      (NatTrans.comp_app σ ψ src).symm.trans
        ((congrArg (fun e : simpleRep k (Quiver.Kronecker A) src ⟶
          simpleRep k (Quiver.Kronecker A) src ↦ e.app src) hσ).trans (NatTrans.id_app _ _))
    refine ⟨σ.app src (simpleRepGenerator k src),
      hnat.symm.trans ((congrArg _ hz).trans (map_zero _)), fun h ↦ ?_⟩
    exact simpleRepGenerator_ne_zero k src
      ((congr_hom_apply hid (simpleRepGenerator k src)).symm.trans h)
  · rintro ⟨x, hx, hψ⟩
    have hc0 : simpleRepSelfEquiv k src (ψ.app src x) ≠ 0 := fun h ↦
      hψ ((simpleRepSelfEquiv k src).injective (h.trans (map_zero _).symm))
    refine IsSplitEpi.mk' ⟨kroneckerHom
      (ModuleCat.ofHom (LinearMap.toSpanSingleton k (Z.obj src) x ∘ₗ
        ((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ • (simpleRepSelfEquiv k src).toLinearMap)))
      0 ?_, ?_⟩
    · intro a
      obtain rfl : a = default := Unique.eq_default a
      refine comp_zero.trans (ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)).symm
      -- Element-level form of an equation of `ModuleCat` morphisms, reached by `change` and not
      -- by `rw`/`simp`: the type of the element and the domain of the composite agree only
      -- after unfolding the unexposed `simpleRep`, so the pattern of a rewrite is not
      -- type-correct at `implicit` transparency and nothing matches the subterm (`rw` fails
      -- with “Did not find an occurrence of the pattern”). Every other `change` below is this
      -- same step, at the vertex spaces of `simpleRep`, of `indecProjRep`, or of both.
      change Z.map (arrowPath (default : A))
        (((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y) • x) = 0
      have hsm : Z.map (arrowPath (default : A))
            (((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y) • x)
          = ((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y)
            • Z.map (arrowPath (default : A)) x := map_smul _ _ _
      exact hsm.trans ((congrArg (fun z ↦ ((simpleRepSelfEquiv k src (ψ.app src x))⁻¹
        * simpleRepSelfEquiv k src y) • z) hx).trans (smul_zero _))
    · refine kroneckerRep_hom_ext ?_ ((isZero_simpleRep_obj src_ne_tgt.symm).eq_of_src _ _)
      refine (NatTrans.comp_app _ _ _).trans (Eq.trans ?_ (NatTrans.id_app _ _).symm)
      rw [kroneckerHom_app_src]
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (ψ.app src) (((simpleRepSelfEquiv k src (ψ.app src x))⁻¹
        * simpleRepSelfEquiv k src y) • x) = y
      have hsm : (ψ.app src) (((simpleRepSelfEquiv k src (ψ.app src x))⁻¹
            * simpleRepSelfEquiv k src y) • x)
          = ((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y)
            • (ψ.app src) x := map_smul _ _ _
      refine (simpleRepSelfEquiv k src).injective
        ((congrArg (⇑(simpleRepSelfEquiv k src)) hsm).trans ?_)
      have hsm' : simpleRepSelfEquiv k src
            (((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y)
              • (ψ.app src) x)
          = ((simpleRepSelfEquiv k src (ψ.app src x))⁻¹ * simpleRepSelfEquiv k src y)
            • simpleRepSelfEquiv k src ((ψ.app src) x) := map_smul _ _ _
      refine hsm'.trans ?_
      rw [smul_eq_mul]
      field_simp

/-- **A morphism out of the vertex simple `S₂` of the `A₂` quiver splits exactly when it misses the
image of the arrow.** A retraction of such a morphism is a linear functional killing that image and
not the image of the generator. -/
theorem isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt
    (ψ : simpleRep k (Quiver.Kronecker A) tgt ⟶ Z) :
    IsSplitMono ψ ↔ ψ.app tgt (simpleRepGenerator k tgt)
      ∉ LinearMap.range (Z.map (arrowPath (default : A))).hom := by
  constructor
  · rintro ⟨⟨r, hr⟩⟩ ⟨w, hw⟩
    have hid : ψ.app tgt ≫ r.app tgt = 𝟙 ((simpleRep k (Quiver.Kronecker A) tgt).obj tgt) :=
      (NatTrans.comp_app ψ r tgt).symm.trans
        ((congrArg (fun e : simpleRep k (Quiver.Kronecker A) tgt ⟶
          simpleRep k (Quiver.Kronecker A) tgt ↦ e.app tgt) hr).trans (NatTrans.id_app _ _))
    have hnat : r.app tgt (Z.map (arrowPath (default : A)) w)
        = (simpleRep k (Quiver.Kronecker A) tgt).map (arrowPath (default : A)) (r.app src w) :=
      congr_hom_apply (r.naturality (arrowPath (default : A))) w
    refine simpleRepGenerator_ne_zero (Q := Quiver.Kronecker A) k tgt ?_
    refine (congr_hom_apply hid (simpleRepGenerator k tgt)).symm.trans ?_
    refine ((congrArg (fun z ↦ r.app tgt z) hw).symm.trans hnat).trans ?_
    exact (congrArg _ (eq_zero_of_isZero (isZero_simpleRep_obj src_ne_tgt) _)).trans (map_zero _)
  · intro hv
    obtain ⟨θ, hθ, hsub⟩ := Submodule.exists_le_ker_of_notMem hv
    refine IsSplitMono.mk' ⟨kroneckerHom 0
      (ModuleCat.ofHom ((simpleRepSelfEquiv k tgt).symm.toLinearMap ∘ₗ
        ((θ (ψ.app tgt (simpleRepGenerator k tgt)))⁻¹ • θ))) ?_, ?_⟩
    · intro a
      obtain rfl : a = default := Unique.eq_default a
      refine Eq.trans ?_ zero_comp.symm
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      have hker : θ (Z.map (arrowPath (default : A)) y) = 0 :=
        hsub (LinearMap.mem_range_self _ y)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (simpleRepSelfEquiv k tgt).symm
        ((θ (ψ.app tgt (simpleRepGenerator k tgt)))⁻¹ • θ
          (Z.map (arrowPath (default : A)) y)) = 0
      rw [hker, smul_zero, map_zero]
    · refine kroneckerRep_hom_ext ((isZero_simpleRep_obj src_ne_tgt).eq_of_src _ _) ?_
      refine (NatTrans.comp_app _ _ _).trans (Eq.trans ?_ (NatTrans.id_app _ _).symm)
      rw [kroneckerHom_app_tgt]
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      obtain ⟨c, rfl⟩ := exists_eq_smul_simpleRepGenerator k y
      have h1 : (ψ.app tgt) (c • simpleRepGenerator k tgt)
          = c • (ψ.app tgt) (simpleRepGenerator k tgt) := map_smul _ _ _
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (simpleRepSelfEquiv k tgt).symm
        ((θ (ψ.app tgt (simpleRepGenerator k tgt)))⁻¹ • θ
          (ψ.app tgt (c • simpleRepGenerator k tgt))) = c • simpleRepGenerator k tgt
      refine (simpleRepSelfEquiv k tgt).injective ?_
      rw [LinearEquiv.apply_symm_apply, map_smul, simpleRepSelfEquiv_apply_generator, h1, map_smul]
      simp only [smul_eq_mul, mul_one]
      field_simp

/-! ### The sequence is almost split -/

variable (k A) in
/-- **The projection `P₁ ↠ S₁` of the `A₂` quiver is right almost split**: it is not a split
epimorphism, and every morphism into `S₁` that is not a split epimorphism factors through it.  By
`TauCeti.isSplitEpi_iff_exists_of_hom_simpleRep_src` the latter means that the functional it is at
the source kills the kernel of the arrow, and a functional killing that kernel extends along the
arrow to the target vertex space. -/
theorem isRightAlmostSplit_kroneckerArSequence_g :
    IsRightAlmostSplit (kroneckerArSequence k A).g := by
  refine isRightAlmostSplit_iff.mpr ⟨fun hs ↦ ?_, fun W ψ hψ ↦ ?_⟩
  · obtain ⟨x, hx, hne⟩ := (isSplitEpi_iff_exists_of_hom_simpleRep_src _).mp hs
    exact hne ((congrArg _ (indecProjRep_map_arrowPath_injective default
      (hx.trans (map_zero _).symm))).trans (map_zero _))
  · have hker0 : ∀ x : W.obj src, W.map (arrowPath (default : A)) x = 0 → ψ.app src x = 0 := by
      intro x hx
      by_contra hne
      exact hψ ((isSplitEpi_iff_exists_of_hom_simpleRep_src ψ).mpr ⟨x, hx, hne⟩)
    have hker : LinearMap.ker (W.map (arrowPath (default : A))).hom ≤
        LinearMap.ker ((simpleRepSelfEquiv k src).toLinearMap ∘ₗ (ψ.app src).hom) := by
      intro x hx
      refine LinearMap.mem_ker.mpr ?_
      have h0 : ψ.app src x = 0 := hker0 x (LinearMap.mem_ker.mp hx)
      exact (congrArg (⇑(simpleRepSelfEquiv k src)) h0).trans (map_zero _)
    -- A functional killing the kernel of the arrow factors through it: descend it to the
    -- quotient by that kernel, read that quotient as the range of the arrow, and extend the
    -- resulting functional on the range to the whole target vertex space.
    obtain ⟨θ, hθ⟩ : ∃ θ : W.obj tgt →ₗ[k] k, ∀ x,
        θ ((W.map (arrowPath (default : A))).hom x)
          = ((simpleRepSelfEquiv k src).toLinearMap ∘ₗ (ψ.app src).hom) x := by
      obtain ⟨θ, hθ⟩ := ((LinearMap.ker (W.map (arrowPath (default : A))).hom).liftQ
        ((simpleRepSelfEquiv k src).toLinearMap ∘ₗ (ψ.app src).hom) hker ∘ₗ
        (W.map (arrowPath (default : A))).hom.quotKerEquivRange.symm.toLinearMap).exists_extend
      exact ⟨θ, fun x ↦ by
        simpa using LinearMap.congr_fun hθ
          ⟨(W.map (arrowPath (default : A))).hom x, LinearMap.mem_range_self _ x⟩⟩
    refine ⟨kroneckerHom
      (ModuleCat.ofHom ((kroneckerProjSrcEquiv k A).symm.toLinearMap ∘ₗ
        ((simpleRepSelfEquiv k src).toLinearMap ∘ₗ (ψ.app src).hom)))
      (ModuleCat.ofHom ((kroneckerProjTgtEquiv k A).symm.toLinearMap ∘ₗ θ)) ?_, ?_⟩
    · intro a
      obtain rfl : a = default := Unique.eq_default a
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (kroneckerProjTgtEquiv k A).symm (θ (W.map (arrowPath (default : A)) x))
        = (indecProjRep k (Quiver.Kronecker A) src).map (arrowPath (default : A))
          ((kroneckerProjSrcEquiv k A).symm (simpleRepSelfEquiv k src (ψ.app src x)))
      refine (kroneckerProjTgtEquiv k A).injective ?_
      rw [LinearEquiv.apply_symm_apply, hθ, kroneckerProjTgtEquiv_map,
        LinearEquiv.apply_symm_apply]
      rfl
    · refine kroneckerRep_hom_ext ?_ ((isZero_simpleRep_obj src_ne_tgt.symm).eq_of_tgt _ _)
      refine (NatTrans.comp_app _ _ _).trans ?_
      rw [kroneckerHom_app_src]
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (kroneckerArSequence k A).g.app src
          ((kroneckerProjSrcEquiv k A).symm (simpleRepSelfEquiv k src (ψ.app src x)))
        = ψ.app src x
      refine (simpleRepSelfEquiv k src).injective ?_
      rw [simpleRepSelfEquiv_kroneckerArSequence_g_app_src, LinearEquiv.apply_symm_apply]

variable (k A) in
/-- **The inclusion `S₂ ↪ P₁` of the `A₂` quiver is left almost split**: it is not a split
monomorphism, and every morphism out of `S₂` that is not a split monomorphism factors through it.
By `TauCeti.isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt` the latter means that the image of
the generator lies in the image of the arrow, and a preimage of it is exactly what the factoring
morphism needs at the source vertex. -/
theorem isLeftAlmostSplit_kroneckerArSequence_f :
    IsLeftAlmostSplit (kroneckerArSequence k A).f := by
  refine isLeftAlmostSplit_iff.mpr ⟨fun hs ↦ ?_, fun W ψ hψ ↦ ?_⟩
  · exact (isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt _).mp hs
      (LinearMap.mem_range.mpr (indecProjRep_map_arrowPath_surjective default _))
  · have hv : ψ.app tgt (simpleRepGenerator k tgt)
        ∈ LinearMap.range (W.map (arrowPath (default : A))).hom := by
      by_contra h
      exact hψ ((isSplitMono_iff_notMem_range_of_hom_simpleRep_tgt ψ).mpr h)
    obtain ⟨w, hw⟩ := hv
    refine ⟨kroneckerHom
      (ModuleCat.ofHom (LinearMap.toSpanSingleton k (W.obj src) w ∘ₗ
        (kroneckerProjSrcEquiv k A).toLinearMap))
      (ModuleCat.ofHom (LinearMap.toSpanSingleton k (W.obj tgt)
        (ψ.app tgt (simpleRepGenerator k tgt)) ∘ₗ (kroneckerProjTgtEquiv k A).toLinearMap))
      ?_, ?_⟩
    · intro a
      obtain rfl : a = default := Unique.eq_default a
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change kroneckerProjTgtEquiv k A
            ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath (default : A)) y)
            • ψ.app tgt (simpleRepGenerator k tgt)
          = W.map (arrowPath (default : A)) (kroneckerProjSrcEquiv k A y • w)
      have hA : kroneckerProjTgtEquiv k A
          ((indecProjRep k (Quiver.Kronecker A) src).map (arrowPath (default : A)) y)
          = kroneckerProjSrcEquiv k A y := kroneckerProjTgtEquiv_map default y
      have hB : W.map (arrowPath (default : A)) (kroneckerProjSrcEquiv k A y • w)
          = kroneckerProjSrcEquiv k A y • W.map (arrowPath (default : A)) w := map_smul _ _ _
      exact (congrArg (fun t : k ↦ t • ψ.app tgt (simpleRepGenerator k tgt)) hA).trans
        (hB.trans (congrArg (fun z ↦ kroneckerProjSrcEquiv k A y • z) hw)).symm
    · refine kroneckerRep_hom_ext ((isZero_simpleRep_obj src_ne_tgt).eq_of_src _ _) ?_
      refine (NatTrans.comp_app _ _ _).trans ?_
      rw [kroneckerArSequence_f, kroneckerSimpleTgtToIndecProjRep_app_tgt, kroneckerHom_app_tgt]
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      obtain ⟨c, rfl⟩ := exists_eq_smul_simpleRepGenerator k y
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change kroneckerProjTgtEquiv k A ((kroneckerProjTgtEquiv k A).symm
            (simpleRepSelfEquiv k tgt (c • simpleRepGenerator k tgt)))
            • ψ.app tgt (simpleRepGenerator k tgt)
          = ψ.app tgt (c • simpleRepGenerator k tgt)
      have h1 : ψ.app tgt (c • simpleRepGenerator k tgt)
          = c • ψ.app tgt (simpleRepGenerator k tgt) := map_smul _ _ _
      have h2 : simpleRepSelfEquiv k (tgt : Quiver.Kronecker A)
          (c • simpleRepGenerator k tgt) = c := by
        rw [map_smul, simpleRepSelfEquiv_apply_generator, smul_eq_mul, mul_one]
      exact (congrArg (fun t : k ↦ t • ψ.app tgt (simpleRepGenerator k tgt))
        ((LinearEquiv.apply_symm_apply _ _).trans h2)).trans h1.symm

/-- **The inclusion `S₂ ↪ P₁` is a monomorphism**: it is injective at the target, and the vertex
space of `S₂` at the source is zero. -/
instance mono_kroneckerArSequence_f : Mono (kroneckerArSequence k A).f := by
  constructor
  intro W u v huv
  refine kroneckerRep_hom_ext ((isZero_simpleRep_obj src_ne_tgt).eq_of_tgt _ _) ?_
  have h : u.app tgt ≫ (kroneckerArSequence k A).f.app tgt
      = v.app tgt ≫ (kroneckerArSequence k A).f.app tgt :=
    (NatTrans.comp_app u _ tgt).symm.trans
      ((congrArg (fun e : W ⟶ (kroneckerArSequence k A).X₂ ↦ e.app tgt) huv).trans
        (NatTrans.comp_app v _ tgt))
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine (simpleRepSelfEquiv k tgt).injective ((kroneckerProjTgtEquiv k A).symm.injective ?_)
  exact (kroneckerSimpleTgtToIndecProjRep_app_tgt_apply _).symm.trans
    ((congr_hom_apply h x).trans (kroneckerSimpleTgtToIndecProjRep_app_tgt_apply _))

/-- **The projection `P₁ ↠ S₁` is an epimorphism**: it is surjective at the source, and the vertex
space of `S₁` at the target is zero. -/
instance epi_kroneckerArSequence_g : Epi (kroneckerArSequence k A).g := by
  constructor
  intro W u v huv
  refine kroneckerRep_hom_ext ?_ ((isZero_simpleRep_obj src_ne_tgt.symm).eq_of_src _ _)
  have h : (kroneckerArSequence k A).g.app src ≫ u.app src
      = (kroneckerArSequence k A).g.app src ≫ v.app src :=
    (NatTrans.comp_app _ u src).symm.trans
      ((congrArg (fun e : (kroneckerArSequence k A).X₂ ⟶ W ↦ e.app src) huv).trans
        (NatTrans.comp_app _ v src))
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  obtain ⟨y, rfl⟩ : ∃ y, (kroneckerArSequence k A).g.app src y = z :=
    ⟨(kroneckerProjSrcEquiv k A).symm (simpleRepSelfEquiv k src z),
      (simpleRepSelfEquiv k src).injective (by
        rw [simpleRepSelfEquiv_kroneckerArSequence_g_app_src, LinearEquiv.apply_symm_apply])⟩
  exact congr_hom_apply h y

variable (k A) in
/-- **The sequence `0 ⟶ S₂ ⟶ P₁ ⟶ S₁ ⟶ 0` of the `A₂` quiver is short exact.** Its first map is a
kernel of its second: a morphism into `P₁` killed by `P₁ ↠ S₁` vanishes at the source, because the
projection is injective there, and is therefore carried by the line at the target alone. -/
theorem shortExact_kroneckerArSequence : (kroneckerArSequence k A).ShortExact where
  exact := by
    refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ ?_)
    intro W u hu
    have husrc : ∀ x : W.obj src, u.app src x = 0 := by
      intro x
      have hc : u.app src ≫ (kroneckerArSequence k A).g.app src = 0 :=
        (NatTrans.comp_app u _ src).symm.trans
          ((congrArg (fun e : W ⟶ (kroneckerArSequence k A).X₃ ↦ e.app src) hu).trans
            (NatTrans.app_zero _))
      have h1 : (kroneckerArSequence k A).g.app src (u.app src x) = 0 := congr_hom_apply hc x
      have h2 : kroneckerProjSrcEquiv k A (u.app src x) = 0 :=
        (simpleRepSelfEquiv_kroneckerArSequence_g_app_src (u.app src x)).symm.trans
          ((congrArg (⇑(simpleRepSelfEquiv k src)) h1).trans (map_zero _))
      exact (kroneckerProjSrcEquiv k A).injective (h2.trans (map_zero _).symm)
    refine ⟨kroneckerHom 0
      (ModuleCat.ofHom ((simpleRepSelfEquiv k tgt).symm.toLinearMap ∘ₗ
        (kroneckerProjTgtEquiv k A).toLinearMap ∘ₗ (u.app tgt).hom)) ?_, ?_⟩
    · intro a
      obtain rfl : a = default := Unique.eq_default a
      refine Eq.trans ?_ zero_comp.symm
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
      -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
      change (simpleRepSelfEquiv k tgt).symm (kroneckerProjTgtEquiv k A
        (u.app tgt (W.map (arrowPath (default : A)) x))) = 0
      have hnat : u.app tgt (W.map (arrowPath (default : A)) x)
          = (indecProjRep k (Quiver.Kronecker A) src).map (arrowPath (default : A))
            (u.app src x) := congr_hom_apply (u.naturality (arrowPath (default : A))) x
      have h3 : u.app tgt (W.map (arrowPath (default : A)) x) = 0 :=
        hnat.trans ((congrArg _ (husrc x)).trans (map_zero _))
      exact (congrArg
        (fun z ↦ (simpleRepSelfEquiv k tgt).symm (kroneckerProjTgtEquiv k A z)) h3).trans
        ((congrArg (⇑(simpleRepSelfEquiv k tgt).symm)
          (map_zero (kroneckerProjTgtEquiv k A))).trans (map_zero _))
    · refine kroneckerRep_hom_ext ?_ ?_
      · refine (NatTrans.comp_app _ _ _).trans ?_
        rw [kroneckerHom_app_src, zero_comp]
        exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ (husrc x).symm)
      · refine (NatTrans.comp_app _ _ _).trans ?_
        rw [kroneckerHom_app_tgt, kroneckerArSequence_f,
          kroneckerSimpleTgtToIndecProjRep_app_tgt]
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        -- `change`: element-level form of a `ModuleCat` composite, out of reach of `rw`/`simp`
        -- (see the note in `isSplitEpi_iff_exists_of_hom_simpleRep_src`).
        change (kroneckerProjTgtEquiv k A).symm (simpleRepSelfEquiv k tgt
            ((simpleRepSelfEquiv k tgt).symm (kroneckerProjTgtEquiv k A (u.app tgt x))))
          = u.app tgt x
        rw [LinearEquiv.apply_symm_apply]
        exact (kroneckerProjTgtEquiv k A).symm_apply_apply _

variable (k A) in
/-- **The sequence `0 ⟶ S₂ ⟶ P₁ ⟶ S₁ ⟶ 0` is an almost-split sequence of the `A₂` quiver.** It is
short exact, its inclusion is left almost split and its projection is right almost split, so it is
an Auslander--Reiten sequence ending at the vertex simple `S₁`; by
`CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso` it is unique up to isomorphism among the
almost-split sequences ending at `S₁`, and `S₂` is therefore the Auslander--Reiten translate of
`S₁`. -/
theorem isAlmostSplit_kroneckerArSequence : (kroneckerArSequence k A).IsAlmostSplit where
  shortExact := shortExact_kroneckerArSequence k A
  isLeftAlmostSplit_f := isLeftAlmostSplit_kroneckerArSequence_f k A
  isRightAlmostSplit_g := isRightAlmostSplit_kroneckerArSequence_g k A

end TauCeti
