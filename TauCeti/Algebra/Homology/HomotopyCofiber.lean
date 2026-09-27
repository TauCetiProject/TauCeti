/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.OneObject

/-!
# Mapping cones of split monomorphisms, and maps of mapping cones

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short complex of homological complexes which is split in the
category of complexes: the retraction `r : X₂ ⟶ X₁` of `f` and the section `s : X₃ ⟶ X₂` of `g`
are chain maps. Then the mapping cone `homotopyCofiber f` of `f` is homotopy equivalent to the
cokernel `X₃`. The map from the cone is `homotopyCofiber.desc f g`, which exists because
`f ≫ g = 0`, and its homotopy inverse is `s` followed by the inclusion `homotopyCofiber.inr f` of
`X₂` into the cone. One composite is `s ≫ g = 𝟙`, and the other is homotopic to the identity
through the homotopy which sends the `X₂`-summand of the cone to its `X₁`-summand by `-r`.

We assume, as Mathlib's `homotopyCofiber.inrCompHomotopy` does, that every index of the complex
shape is the target of some relation. This holds for `ComplexShape.up ℤ`, `ComplexShape.down ℤ`
and the one-object shape `ComplexShape.refl Unit`.

The motivating example is multiplication by `X - a` on the polynomial extension `A[X] ⊗[A] K` of
a complex `K` of `A`-modules, split by division by `X - a` and by the constant polynomials (see
`TauCeti.Algebra.Homology.PolynomialExtension`). This is how the stabilization invariance of grid
homology compares a grid complex with the mapping cone of `V₁ - V₂`.

Conversely, a one-object complex (over the shape `ComplexShape.refl Unit`) whose object splits as
a direct sum `K ⊕ L`, with `L` a subcomplex, is the mapping cone of the component `K ⟶ L` of its
differential. This is how the unblocked complex of a stabilized grid diagram is presented as a
mapping cone.

Finally, a morphism of arrows `α` from `φ : F ⟶ G` to `φ' : F' ⟶ G'` induces a map of mapping
cones `homotopyCofiber.mapArrowHom φ φ' _ α`. If both components of `α` are
quasi-isomorphisms, so is the induced map of cones. For grid stabilization, this transfers a
quasi-isomorphism on the off-center states to the comparison map for the whole stabilized
complex.

## Main definitions

* `CategoryTheory.ShortComplex.Splitting.homotopyCofiberHomotopyEquiv`: the homotopy equivalence
  between the mapping cone of `S.f` and `S.X₃` for a split short complex of complexes `S`.
* `HomologicalComplex.homotopyCofiber.isoOfSplitting`: a one-object complex with a block
  lower-triangular differential is isomorphic to the mapping cone of its off-diagonal block.

## Main results

* `CategoryTheory.ShortComplex.Splitting.quasiIso_homotopyCofiberDesc`: the map from the mapping
  cone of `S.f` to `S.X₃` induced by `S.g` is a quasi-isomorphism.
* `HomologicalComplex.homotopyCofiber.inr_mapArrowHom`,
  `HomologicalComplex.homotopyCofiber.inrX_mapArrowHom_f`,
  `HomologicalComplex.homotopyCofiber.inlX_mapArrowHom_f`: the components of a map of cones.
* `HomologicalComplex.homotopyCofiber.quasiIso_mapArrowHom`: a map of mapping cones induced by
  quasi-isomorphisms is a quasi-isomorphism.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 1.5.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, Section 5.2.
-/

public section

open CategoryTheory Category HomologicalComplex

namespace CategoryTheory.ShortComplex.Splitting

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι} [DecidableRel c.Rel]
  {S : ShortComplex (HomologicalComplex C c)} (σ : S.Splitting) [HasHomotopyCofiber S.f]
  (hc : ∀ j, ∃ i, c.Rel i j)

/-- For a short complex of complexes `S` split by chain maps, the mapping cone of `S.f` is
homotopy equivalent to `S.X₃`. The map from the cone is induced by `S.g`, and its homotopy inverse
is the section `σ.s` followed by the inclusion of `S.X₂` into the cone. -/
noncomputable def homotopyCofiberHomotopyEquiv :
    _root_.HomotopyEquiv (homotopyCofiber S.f) S.X₃ where
  hom := homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero)
  inv := σ.s ≫ homotopyCofiber.inr S.f
  homotopyInvHomId := _root_.Homotopy.ofEq (by simp)
  -- On the `X₂`-summand of the cone, the homotopy is `-r` into the `X₁`-summand.
  homotopyHomInvId.hom i j := if hij : c.Rel j i then
      -(homotopyCofiber.sndX S.f i ≫ σ.r.f i ≫ homotopyCofiber.inlX S.f i j hij) else 0
  homotopyHomInvId.zero _ _ hij := dite_eq_right hij
  homotopyHomInvId.comm j := by
    obtain ⟨i, hij⟩ := hc j
    have hfr (k : ι) : S.f.f k ≫ σ.r.f k = 𝟙 _ := by
      rw [← comp_f, σ.f_r, id_f]
    have hrf : σ.r.f j ≫ S.f.f j = 𝟙 _ - S.g.f j ≫ σ.s.f j := by
      simpa using congrArg (fun φ ↦ φ.f j) σ.r_f
    rw [prevD_eq _ hij, dite_eq_left hij]
    by_cases hj : c.Rel j (c.next j)
    · rw [dNext_eq _ hj, dite_eq_left hj]
      apply homotopyCofiber.ext_from_X S.f (c.next j) j hj
      · simp [homotopyCofiber.desc_f _ _ _ _ _ hj, homotopyCofiber.d_sndX_assoc _ _ _ hj,
          reassoc_of% hfr]
      · simp [homotopyCofiber.desc_f _ _ _ _ _ hj, homotopyCofiber.inlX_d S.f i j _ hij hj,
          homotopyCofiber.d_sndX_assoc _ _ _ hj, reassoc_of% hrf]
    · rw [dNext_eq_zero _ _ hj, zero_add]
      apply homotopyCofiber.ext_from_X' S.f j hj
      simp [homotopyCofiber.desc_f' _ _ _ _ hj, homotopyCofiber.inlX_d' S.f i j hij hj,
        reassoc_of% hrf]

/-- The map from the mapping cone in `homotopyCofiberHomotopyEquiv` is induced by `S.g`. -/
@[simp]
theorem homotopyCofiberHomotopyEquiv_hom :
    (σ.homotopyCofiberHomotopyEquiv hc).hom =
      homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero) :=
  (rfl)

/-- The homotopy inverse in `homotopyCofiberHomotopyEquiv` is the section `σ.s` followed by the
inclusion of `S.X₂` into the mapping cone. -/
@[simp]
theorem homotopyCofiberHomotopyEquiv_inv :
    (σ.homotopyCofiberHomotopyEquiv hc).inv = σ.s ≫ homotopyCofiber.inr S.f :=
  (rfl)

include σ hc in
/-- For a short complex of complexes `S` split by chain maps, the map from the mapping cone of
`S.f` to `S.X₃` induced by `S.g` is a quasi-isomorphism. -/
theorem quasiIso_homotopyCofiberDesc [∀ i, (homotopyCofiber S.f).HasHomology i]
    [∀ i, S.X₃.HasHomology i] :
    _root_.QuasiIso (homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero)) :=
  σ.homotopyCofiberHomotopyEquiv_hom hc ▸ (σ.homotopyCofiberHomotopyEquiv hc).quasiIso_hom

end CategoryTheory.ShortComplex.Splitting

/-! ### Mapping cones of one-object complexes -/

namespace HomologicalComplex.homotopyCofiber

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {K L M : HomologicalComplex C (ComplexShape.refl Unit)} (φ : K ⟶ L)
  {inr : L.X () ⟶ M.X ()} {fst : M.X () ⟶ K.X ()} {w : inr ≫ fst = 0}
  (σ : (ShortComplex.mk inr fst w).Splitting)
  (hs : σ.s ≫ M.d () () = φ.f () ≫ inr - K.d () () ≫ σ.s)
  (hr : inr ≫ M.d () () = L.d () () ≫ inr)

/-- **A triangular one-object complex is a mapping cone.** Let `M` be a one-object complex whose
object is split as `M.X () = K.X () ⊕ L.X ()` by `σ`, with `inr` and `σ.s` the inclusions of the
summands, in such a way that `L.X ()` is a subcomplex (`hr`) and the differential of `M` restricted
to `K.X ()` is `φ - d_K` in block form (`hs`). Then `M` is the mapping cone of `φ`.

The sign in `hs` is that of Mathlib's `homotopyCofiber`, whose differential is `-d_K` on the
`K`-summand; over a ring of characteristic two it disappears. -/
noncomputable def isoOfSplitting : homotopyCofiber φ ≅ M :=
  Hom.isoOfComponents
    (fun _ =>
      { hom := fstX φ () () (ComplexShape.refl_rel ()) ≫ σ.s + sndX φ () ≫ inr
        inv := fst ≫ inlX φ () () (ComplexShape.refl_rel ()) + σ.r ≫ inrX φ ()
        hom_inv_id := by
          have hsg : σ.s ≫ fst = 𝟙 _ := σ.s_g
          have hsr : σ.s ≫ σ.r = 0 := σ.s_r
          have hfr : inr ≫ σ.r = 𝟙 _ := σ.f_r
          apply ext_from_X φ () () (ComplexShape.refl_rel ()) <;>
            simp [reassoc_of% hsg, reassoc_of% hsr, reassoc_of% hfr, reassoc_of% w]
        inv_hom_id := by
          simpa [add_comm] using σ.id })
    (by
      rintro ⟨⟩ ⟨⟩ -
      -- The components are those of the map `homotopyCofiber.desc φ inr σ.s`, a chain map.
      let α : L ⟶ M := { f _ := inr, comm' := fun _ _ _ => hr }
      let h : Homotopy (φ ≫ α) 0 :=
        { hom _ _ := σ.s
          zero _ _ hij := absurd (ComplexShape.refl_rel ()) hij
          comm _ := by
            rw [dNext_eq _ (ComplexShape.refl_rel ()), prevD_eq _ (ComplexShape.refl_rel ()), hs]
            simp [α] }
      dsimp only
      rw [← desc_f φ α h () () (ComplexShape.refl_rel ())]
      exact (desc φ α h).comm () ())

/-- On the cone, `isoOfSplitting` is `σ.s` on the `K`-summand and `inr` on the `L`-summand. -/
@[simp]
theorem isoOfSplitting_hom_f :
    (isoOfSplitting φ σ hs hr).hom.f () =
      fstX φ () () (ComplexShape.refl_rel ()) ≫ σ.s + sndX φ () ≫ inr :=
  (rfl)

/-- The inverse of `isoOfSplitting` sends `M` into the cone through `fst` and the retraction
`σ.r`. -/
@[simp]
theorem isoOfSplitting_inv_f :
    (isoOfSplitting φ σ hs hr).inv.f () =
      fst ≫ inlX φ () () (ComplexShape.refl_rel ()) + σ.r ≫ inrX φ () :=
  (rfl)

end HomologicalComplex.homotopyCofiber

/-! ### Maps of mapping cones -/

namespace HomologicalComplex.homotopyCofiber

open Limits ZeroObject

section MapArrowHom

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G F' G' : HomologicalComplex C c} (φ : F ⟶ G) (φ' : F' ⟶ G') [HasHomotopyCofiber φ]
  [HasHomotopyCofiber φ'] (hc : ∀ j, ∃ i, c.Rel i j) (α : Arrow.mk φ ⟶ Arrow.mk φ')

/-- The map of cones induced by a morphism of arrows `α` restricts to `α.right` on the inclusion
of the target. -/
@[reassoc (attr := simp)]
lemma inr_mapArrowHom : inr φ ≫ mapArrowHom φ φ' hc α = α.right ≫ inr φ' := by
  simp [mapArrowHom]

/-- On the summand `G` of the mapping cone, the map of cones induced by a morphism of arrows `α`
is `α.right`. -/
@[reassoc (attr := simp)]
lemma inrX_mapArrowHom_f (i : ι) :
    inrX φ i ≫ (mapArrowHom φ φ' hc α).f i = α.right.f i ≫ inrX φ' i := by
  simp [mapArrowHom]

/-- On the summand `F` of the mapping cone, the map of cones induced by a morphism of arrows `α`
is `α.left`. -/
@[reassoc (attr := simp)]
lemma inlX_mapArrowHom_f (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ (mapArrowHom φ φ' hc α).f j = α.left.f i ≫ inlX φ' i j hij := by
  simp [mapArrowHom, inrCompHomotopy_hom _ _ _ _ hij]

end MapArrowHom

section QuasiIso

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G F' G' : HomologicalComplex C c} (φ : F ⟶ G) (φ' : F' ⟶ G') (hc : ∀ j, ∃ i, c.Rel i j)

/-- The projection of the mapping cone of `φ : F ⟶ G` onto the mapping cone of `F ⟶ 0`, which
forgets the summand `G`. -/
private noncomputable abbrev toCone₀ : homotopyCofiber φ ⟶ homotopyCofiber (0 : F ⟶ 0) :=
  mapArrowHom φ 0 hc (Arrow.homMk (𝟙 F) 0)

/-- The degreewise split short exact sequence `G ⟶ homotopyCofiber φ ⟶ homotopyCofiber (F ⟶ 0)`
of a mapping cone. -/
private noncomputable abbrev coneShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (inr φ) (toCone₀ φ hc) (by ext i; simp)

private lemma coneShortComplex_shortExact : (coneShortComplex φ hc).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  have h₀ : IsZero ((0 : HomologicalComplex C c).X i) :=
    (eval C c i).map_isZero (Limits.isZero_zero _)
  by_cases hi : c.Rel i (c.next i)
  · refine ShortComplex.Splitting.shortExact
      { r := sndX φ i
        s := fstX (0 : F ⟶ 0) i _ hi ≫ inlX φ _ i hi
        f_r := by simp
        s_g := ext_from_X (0 : F ⟶ 0) _ i hi (by simp) (h₀.eq_of_src _ _)
        id := ext_from_X φ _ i hi (by simp) (by simp) }
  · have hz : IsZero ((homotopyCofiber (0 : F ⟶ 0)).X i) :=
      isZero_X (0 : F ⟶ 0) i h₀ fun j hij => absurd (c.next_eq' hij ▸ hij) hi
    refine ShortComplex.Splitting.shortExact
      { r := sndX φ i
        s := 0
        f_r := by simp
        s_g := hz.eq_of_src _ _
        id := by simpa using sndX_inrX φ i hi }

/-- The mapping cone of an identity map is acyclic, so the map of cones of identities induced by
any map is a quasi-isomorphism. -/
private lemma quasiIso_mapArrowHom_id (a : F ⟶ F') :
    QuasiIso (mapArrowHom (𝟙 F) (𝟙 F') hc (Arrow.homMk a a)) := by
  -- The cone of `𝟙 F` is homotopy equivalent to `0`, the cokernel of the split mono `𝟙 F`.
  let e (K : HomologicalComplex C c) : _root_.HomotopyEquiv (homotopyCofiber (𝟙 K)) 0 :=
    ShortComplex.Splitting.homotopyCofiberHomotopyEquiv (S := ShortComplex.mk (𝟙 K) 0 (by simp))
      { r := 𝟙 K
        s := 0
        s_g := (Limits.isZero_zero _).eq_of_src _ _ } hc
  have : QuasiIso (mapArrowHom (𝟙 F) (𝟙 F') hc (Arrow.homMk a a) ≫ (e F').hom) := by
    rw [(Limits.isZero_zero _).eq_of_tgt (_ ≫ (e F').hom) (e F).hom]
    infer_instance
  exact quasiIso_of_comp_right _ (e F').hom

/-- **Maps of mapping cones preserve quasi-isomorphisms.** If a morphism of arrows `α` from
`φ : F ⟶ G` to `φ' : F' ⟶ G'` consists of quasi-isomorphisms, the induced map of mapping cones
`homotopyCofiber φ ⟶ homotopyCofiber φ'` is a quasi-isomorphism. -/
lemma quasiIso_mapArrowHom (α : Arrow.mk φ ⟶ Arrow.mk φ') [QuasiIso α.left]
    [QuasiIso α.right] : QuasiIso (mapArrowHom φ φ' hc α) := by
  -- Compare the sequences `G ⟶ homotopyCofiber φ ⟶ homotopyCofiber (F ⟶ 0)` of `φ` and `φ'`.
  -- Their third terms are compared through the same sequences for `𝟙 F` and `𝟙 F'`, whose middle
  -- terms are acyclic.
  let τ₃ := mapArrowHom (0 : F ⟶ 0) (0 : F' ⟶ 0) hc (Arrow.homMk α.left 0)
  have h₃ : QuasiIso τ₃ := by
    have := quasiIso_mapArrowHom_id hc α.left
    refine HomologySequence.quasiIso_τ₃
      (S₁ := coneShortComplex (𝟙 F) hc) (S₂ := coneShortComplex (𝟙 F') hc)
      { τ₁ := α.left
        τ₂ := mapArrowHom (𝟙 F) (𝟙 F') hc (Arrow.homMk α.left α.left)
        τ₃ := τ₃
        comm₁₂ := by simp
        comm₂₃ := by
          simp only [τ₃, ← mapArrowHom_comp]
          congr 1
          ext <;> simp }
      (coneShortComplex_shortExact _ hc) (coneShortComplex_shortExact _ hc) inferInstance this
  exact HomologySequence.quasiIso_τ₂
    (S₁ := coneShortComplex φ hc) (S₂ := coneShortComplex φ' hc)
    { τ₁ := α.right
      τ₂ := mapArrowHom φ φ' hc α
      τ₃ := τ₃
      comm₁₂ := by simp
      comm₂₃ := by
        simp only [τ₃, ← mapArrowHom_comp]
        congr 1
        ext <;> simp }
    (coneShortComplex_shortExact φ hc) (coneShortComplex_shortExact φ' hc) inferInstance h₃

end QuasiIso

end HomologicalComplex.homotopyCofiber
