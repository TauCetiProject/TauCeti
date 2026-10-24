/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.AdditiveClosure.Basic
public import TauCeti.CategoryTheory.DG.Twisted.Basic

/-!
# Extensions of twisted objects

Let `P` and `Q` be twisted objects of the additive closure of a differential graded category `E`,
and let `g : Q ⟶ P` be a closed morphism of degree one of twisted objects.  The **extension**
`TauCeti.DGTwistedObject.extension P Q g` is the twisted object `(P ⊕ Q, δ)` whose underlying
object is the direct sum `P ⊕ Q` in the additive closure and whose twisting matrix `δ` has the
twists `δ_P` and `δ_Q` on the diagonal blocks, `g` in the block from `Q` to `P`, and zero in the
block from `P` to `Q`.  Blockwise, the Maurer–Cartan equation `d δ = dgComp δ δ` is the
Maurer–Cartan equations of `δ_P` and `δ_Q` together with `d g = dgComp δ_Q g + dgComp g δ_P`, and
the last equation says exactly that `g` is closed for the twisted differential
(`TauCeti.DGTwistedObject.dgDifferential_extensionTwist`).

The extension comes with inclusions `TauCeti.DGTwistedObject.extensionInl`,
`TauCeti.DGTwistedObject.extensionInr` and projections `TauCeti.DGTwistedObject.extensionFst`,
`TauCeti.DGTwistedObject.extensionSnd` of degree zero satisfying the biproduct equations.  The
inclusion of `P` and the projection onto `Q` are closed, so `P ⟶ extension P Q g ⟶ Q` is a
sequence of closed degree-zero morphisms with zero composite, split as graded objects.  The
splitting need not be closed: the differential of the inclusion of `Q` is `g` followed by the
inclusion of `P`, and the differential of the projection onto `P` is minus the projection onto `Q`
followed by `g`.

If `g` is invertible, with inverse `g' : P ⟶ Q` of degree `-1`, the extension is contractible:
minus the projection onto `P`, followed by `g'` and the inclusion of `Q`, is a degree `-1`
endomorphism whose differential is the identity, so the extension is a zero object of the
homotopy category.

The extension depends only on the homotopy class of `g`, up to isomorphism in the homotopy
category.  If `g - g' = d k` for a degree-zero morphism `k : Q ⟶ P`, then the identity on the
summands together with `k` in the block from `Q` to `P` is a closed morphism
`extension P Q g ⟶ extension P Q g'`, with inverse the same construction for `-k`.

With `Q` the shift `P'⟦1⟧` of a twisted object `P'` and `g` the degree-one morphism
`P'⟦1⟧ ⟶ P' ⟶ P` underlying a closed degree-zero morphism `u : P' ⟶ P`, the extension is the
cone of `u`, the basic construction of the pretriangulated envelope of Bondal and Kapranov; see
`TauCeti/CategoryTheory/DG/Twisted/Cone.lean`.

## Main definitions

* `TauCeti.DGTwistedObject.extensionTwist`: the block twisting matrix of an extension.
* `TauCeti.DGTwistedObject.extension`: the extension of `Q` by `P` along `g`.
* `TauCeti.DGTwistedObject.extensionInl`, `TauCeti.DGTwistedObject.extensionInr`,
  `TauCeti.DGTwistedObject.extensionFst`, `TauCeti.DGTwistedObject.extensionSnd`: the inclusions
  of and projections to the two summands.
* `TauCeti.DGTwistedObject.extensionHomOfHomotopy`: the morphism of extensions induced by a
  degree-zero morphism `k : Q ⟶ P`.
* `TauCeti.DGTwistedObject.extensionIsoOfHomotopy`: the isomorphism in the homotopy category
  between extensions along homotopic morphisms.

## Main results

* `TauCeti.DGTwistedObject.dgDifferential_extensionTwist`: the Maurer–Cartan equation.
* `TauCeti.DGTwistedObject.dgDifferential_extensionInl`,
  `TauCeti.DGTwistedObject.dgDifferential_extensionSnd`: the inclusion of `P` and the projection
  onto `Q` are closed.
* `TauCeti.DGTwistedObject.dgDifferential_extensionInr`,
  `TauCeti.DGTwistedObject.dgDifferential_extensionFst`: the differentials of the other two
  structure maps.
* `TauCeti.DGTwistedObject.dgComp_extensionInl_extensionSnd` and the other biproduct equations:
  the composite `P ⟶ extension P Q g ⟶ Q` vanishes, and the inclusions and projections exhibit
  the extension as the direct sum of `P` and `Q` as a graded object.
* `TauCeti.DGTwistedObject.dgDifferential_neg_dgComp_extensionFst_extensionInr` and
  `TauCeti.DGTwistedObject.isZero_of_extension`: an extension along an invertible morphism is
  contractible.
* `TauCeti.DGTwistedObject.extensionHomOfHomotopy_zero`: the zero morphism induces the identity.
* `TauCeti.DGTwistedObject.dgDifferential_extensionHomOfHomotopy` and
  `TauCeti.DGTwistedObject.dgComp_extensionHomOfHomotopy_neg`: the morphism induced by a homotopy
  `k` from `g` to `g'` is closed, and the morphisms induced by `k` and `-k` are mutually inverse.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

namespace DGTwistedObject

variable (R : Type v) [CommRing R] {E : Type u} [DGCategory R E]

open DGAdditiveClosure (dgHom_ext)

/- `matrixEquiv` is a local name for `TauCeti.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `TauCeti.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

/-! ### Matrix entries of morphisms of twisted objects of the additive closure -/

variable {R} in
/-- Morphisms of twisted objects of the additive closure are determined by their matrix
entries. -/
private theorem dgHom_ext' {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    {f f' : DGHom R n M N}
    (h : ∀ i j, matrixEquiv R _ _ n (dgHomEquiv R M N n f) i j =
      matrixEquiv R _ _ n (dgHomEquiv R M N n f') i j) :
    f = f' :=
  (dgHomEquiv R M N n).injective (dgHom_ext R h)

variable {R} in
/-- The twisted differential of a morphism of twisted objects of the additive closure,
entrywise. -/
private theorem dgDifferential_apply {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (f : DGHom R n M N) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ (n + 1) (dgHomEquiv R M N (n + 1) (dgDifferential R n f)) i j =
      dgDifferential R n (matrixEquiv R _ _ n (dgHomEquiv R M N n f) i j) +
        n.negOnePow • ∑ k, dgComp R (matrixEquiv R _ _ n (dgHomEquiv R M N n f) i k)
          (matrixEquiv R _ _ 1 N.twist k j) rfl -
        ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
          (matrixEquiv R _ _ n (dgHomEquiv R M N n f) k j)
          (add_comm 1 n) := by
  rw [dgHomEquiv_dgDifferential]
  simp only [map_sub, map_add, map_zsmul_unit, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp]

variable {R} in
/-- Composition of twisted objects of the additive closure, entrywise. -/
private theorem dgComp_apply {L M N : DGTwistedObject R (DGAdditiveClosure E)} {p q n : ℤ}
    (f : DGHom R p L M) (f' : DGHom R q M N) (h : p + q = n) (i : L.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ n (dgHomEquiv R L N n (dgComp R f f' h)) i j =
      ∑ k, dgComp R (matrixEquiv R _ _ p (dgHomEquiv R L M p f) i k)
        (matrixEquiv R _ _ q (dgHomEquiv R M N q f') k j) h := by
  rw [dgHomEquiv_dgComp, DGAdditiveClosure.dgHomEquiv_dgComp]

/-- The identity of a twisted object of the additive closure, entrywise. -/
private theorem dgId_apply (M : DGTwistedObject R (DGAdditiveClosure E)) (i j : M.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R M M 0 (dgId R M)) i j =
      matrixEquiv R _ _ 0 (dgId R M.obj) i j := by
  rw [dgHomEquiv_dgId]

variable {R} in
/-- The twisted differential of a degree-zero morphism of twisted objects of the additive
closure, entrywise. -/
private theorem dgDifferential_apply_zero {M N : DGTwistedObject R (DGAdditiveClosure E)}
    (f : DGHom R 0 M N) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ 1 (dgHomEquiv R M N 1 (dgDifferential R 0 f)) i j =
      ((dgHomComplex R (M.obj.X i) (N.obj.X j)).d 0 1).hom
          (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) i j) +
        ∑ k, dgComp R (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) i k)
          (matrixEquiv R _ _ 1 N.twist k j) (zero_add 1) -
        ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
          (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) k j) (add_zero 1) := by
  have h := dgDifferential_apply f i j
  rw [Int.negOnePow_zero, one_smul] at h
  -- `h` is the claim up to the definitional equality of the degrees `0 + 1` and `1`.
  exact h

/-- The entries of the identity of an object of the additive closure are closed, with the
differential written in degree `1` rather than `0 + 1`. -/
private theorem d_zero_one_dgHomEquiv_dgId (M : DGAdditiveClosure E) (i j : M.ι) :
    ((dgHomComplex R (M.X i) (M.X j)).d 0 1).hom (matrixEquiv R _ _ 0 (dgId R M) i j) = 0 :=
  DGAdditiveClosure.dgDifferential_dgHomEquiv_dgId R M i j

/-- The Maurer–Cartan equation of a twisted object of the additive closure, entrywise. -/
private theorem dgDifferential_twist_apply (M : DGTwistedObject R (DGAdditiveClosure E))
    (i j : M.obj.ι) :
    dgDifferential R 1 (matrixEquiv R _ _ 1 M.twist i j) =
      ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
      (matrixEquiv R _ _ 1 M.twist k j) rfl := by
  rw [← DGAdditiveClosure.dgHomEquiv_dgDifferential, dgDifferential_twist,
    DGAdditiveClosure.dgHomEquiv_dgComp]

variable {R} in
/-- A closed degree-one morphism `g : Q ⟶ P` of twisted objects of the additive closure,
entrywise: `d g = dgComp δ_Q g + dgComp g δ_P`. -/
private theorem dgDifferential_apply_of_closed {P Q : DGTwistedObject R (DGAdditiveClosure E)}
    {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) (i : Q.obj.ι) (j : P.obj.ι) :
    dgDifferential R 1 (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j) =
      ∑ k, dgComp R (matrixEquiv R _ _ 1 Q.twist i k)
          (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) k j) rfl +
        ∑ k, dgComp R (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i k)
          (matrixEquiv R _ _ 1 P.twist k j) rfl := by
  have h := dgDifferential_apply g i j
  rw [hg, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Int.negOnePow_one, Units.neg_smul,
    one_smul] at h
  rw [← sub_eq_zero, ← h.symm]
  abel

/-! ### The twisting matrix of an extension -/

/-- The twisting matrix of an extension: `δ_P` and `δ_Q` on the diagonal blocks, `g` in the
block from `Q` to `P`, and zero in the block from `P` to `Q`. -/
private noncomputable def extensionTwistMatrix (P Q : DGTwistedObject R (DGAdditiveClosure E))
    (g : DGHom R 1 Q P) :
    ∀ i j : (P.obj.sum Q.obj).ι, DGHom R 1 ((P.obj.sum Q.obj).X i) ((P.obj.sum Q.obj).X j)
  | .inl i, .inl j => matrixEquiv R _ _ 1 P.twist i j
  | .inl _, .inr _ => 0
  | .inr i, .inl j => matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j
  | .inr i, .inr j => matrixEquiv R _ _ 1 Q.twist i j

/-- The **twisting matrix of an extension** of `Q` by `P` along a degree-one morphism
`g : Q ⟶ P`: the degree-one endomorphism of `P ⊕ Q` with the twists of `P` and `Q` on the
diagonal blocks, `g` in the block from `Q` to `P`, and zero in the block from `P` to `Q`. -/
noncomputable def extensionTwist (P Q : DGTwistedObject R (DGAdditiveClosure E))
    (g : DGHom R 1 Q P) : DGHom R 1 (P.obj.sum Q.obj) (P.obj.sum Q.obj) :=
  (matrixEquiv R _ _ 1).symm (extensionTwistMatrix R P Q g)

section extensionTwist

variable (P Q : DGTwistedObject R (DGAdditiveClosure E)) (g : DGHom R 1 Q P)

/-- The block of the twisting matrix of an extension on the summands of `P` is the twist of
`P`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inl i) (.inl j) =
      matrixEquiv R _ _ 1 P.twist i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension from the summands of `P` to those of `Q`
vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inl i) (.inr j) = 0 :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension from the summands of `Q` to those of `P` is
`g`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inr i) (.inl j) =
      matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension on the summands of `Q` is the twist of
`Q`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inr i) (.inr j) =
      matrixEquiv R _ _ 1 Q.twist i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

end extensionTwist

variable {R} in
/-- The twisting matrix of an extension along a closed morphism satisfies the Maurer–Cartan
equation. -/
theorem dgDifferential_extensionTwist {P Q : DGTwistedObject R (DGAdditiveClosure E)}
    {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) :
    dgDifferential R 1 (extensionTwist R P Q g) =
      dgComp R (extensionTwist R P Q g) (extensionTwist R P Q g) rfl :=
  dgHom_ext R fun i j ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp,
      Fintype.sum_sum_type]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [↓dgHomEquiv_extensionTwist_inl_inl, ↓dgHomEquiv_extensionTwist_inl_inr,
        ↓dgHomEquiv_extensionTwist_inr_inl, ↓dgHomEquiv_extensionTwist_inr_inr, zero_dgComp,
        dgComp_zero, map_zero, Finset.sum_const_zero, add_zero, zero_add]
    · exact dgDifferential_twist_apply R P i j
    · rw [dgDifferential_apply_of_closed hg]
      exact add_comm _ _
    · exact dgDifferential_twist_apply R Q i j

/-! ### The extension -/

variable {R} in
/-- The **extension** of `Q` by `P` along a closed degree-one morphism `g : Q ⟶ P` of twisted
objects of the additive closure: the twisted object `(P ⊕ Q, δ)` whose twisting matrix has the
twists of `P` and `Q` on the diagonal and `g` in the block from `Q` to `P`.  Its Maurer–Cartan
equation is `TauCeti.DGTwistedObject.dgDifferential_extensionTwist`. -/
-- This is reducible so that the underlying object of the extension is reducibly `P ⊕ Q` and its
-- twist reducibly `TauCeti.DGTwistedObject.extensionTwist`, whose entry lemmas then apply.
noncomputable abbrev extension (P Q : DGTwistedObject R (DGAdditiveClosure E)) (g : DGHom R 1 Q P)
    (hg : dgDifferential R 1 g = 0) : DGTwistedObject R (DGAdditiveClosure E) where
  obj := P.obj.sum Q.obj
  twist := extensionTwist R P Q g
  dgDifferential_twist := dgDifferential_extensionTwist hg

section twist

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/- The entries of the twist of an extension, stated with the twist written as a projection of the
extension, the form in which it appears in the matrix entries of morphisms out of and into the
extension; `simp` does not see through this projection to the entry lemmas of
`TauCeti.DGTwistedObject.extensionTwist`. -/

@[simp↓]
theorem dgHomEquiv_twist_extension_inl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inl i) (.inl j) =
      matrixEquiv R _ _ 1 P.twist i j :=
  dgHomEquiv_extensionTwist_inl_inl R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inl i) (.inr j) = 0 :=
  dgHomEquiv_extensionTwist_inl_inr R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inr i) (.inl j) =
      matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j :=
  dgHomEquiv_extensionTwist_inr_inl R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inr i) (.inr j) =
      matrixEquiv R _ _ 1 Q.twist i j :=
  dgHomEquiv_extensionTwist_inr_inr R P Q g i j

end twist

/-! ### The structure maps of an extension -/

section structureMaps

variable (P Q : DGTwistedObject R (DGAdditiveClosure E))

/-- The matrix of the inclusion of `P` into `P ⊕ Q`. -/
private noncomputable def inlMatrix :
    ∀ (i : P.obj.ι) (k : (P.obj.sum Q.obj).ι), DGHom R 0 (P.obj.X i) ((P.obj.sum Q.obj).X k)
  | i, .inl j => matrixEquiv R _ _ 0 (dgId R P.obj) i j
  | _, .inr _ => 0

/-- The matrix of the inclusion of `Q` into `P ⊕ Q`. -/
private noncomputable def inrMatrix :
    ∀ (i : Q.obj.ι) (k : (P.obj.sum Q.obj).ι), DGHom R 0 (Q.obj.X i) ((P.obj.sum Q.obj).X k)
  | _, .inl _ => 0
  | i, .inr j => matrixEquiv R _ _ 0 (dgId R Q.obj) i j

/-- The matrix of the projection of `P ⊕ Q` onto `P`. -/
private noncomputable def fstMatrix :
    ∀ (k : (P.obj.sum Q.obj).ι) (j : P.obj.ι), DGHom R 0 ((P.obj.sum Q.obj).X k) (P.obj.X j)
  | .inl i, j => matrixEquiv R _ _ 0 (dgId R P.obj) i j
  | .inr _, _ => 0

/-- The matrix of the projection of `P ⊕ Q` onto `Q`. -/
private noncomputable def sndMatrix :
    ∀ (k : (P.obj.sum Q.obj).ι) (j : Q.obj.ι), DGHom R 0 ((P.obj.sum Q.obj).X k) (Q.obj.X j)
  | .inl _, _ => 0
  | .inr i, j => matrixEquiv R _ _ 0 (dgId R Q.obj) i j

variable {P Q} {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0)

/-- The inclusion `P ⟶ extension P Q g` of the first summand, a closed morphism of degree
zero. -/
noncomputable def extensionInl : DGHom R 0 P (extension P Q g hg) :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (inlMatrix R P Q))

/-- The inclusion `Q ⟶ extension P Q g` of the second summand, a morphism of degree zero which
need not be closed: its differential is `g` followed by the inclusion of `P`. -/
noncomputable def extensionInr : DGHom R 0 Q (extension P Q g hg) :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (inrMatrix R P Q))

/-- The projection `extension P Q g ⟶ P` onto the first summand, a morphism of degree zero
which need not be closed: its differential is minus the projection onto `Q` followed by `g`. -/
noncomputable def extensionFst : DGHom R 0 (extension P Q g hg) P :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (fstMatrix R P Q))

/-- The projection `extension P Q g ⟶ Q` onto the second summand, a closed morphism of degree
zero. -/
noncomputable def extensionSnd : DGHom R 0 (extension P Q g hg) Q :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (sndMatrix R P Q))

/-- Entries of a morphism of twisted objects defined from its matrix. -/
private theorem dgHomEquiv_symm_symm_apply {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (F : ∀ i j, DGHom R n (M.obj.X i) (N.obj.X j)) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ n
      (dgHomEquiv R M N n ((dgHomEquiv R M N n).symm ((matrixEquiv R _ _ n).symm F))) i j =
        F i j := by
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The block of the inclusion of `P` into an extension on the summands of `P` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionInl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInl R hg)) i (.inl j) =
      matrixEquiv R _ _ 0 (dgId R P.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := P) (N := (extension P Q g hg)) (inlMatrix R P Q) i (Sum.inl j)

/-- The block of the inclusion of `P` into an extension to the summands of `Q` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionInl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInl R hg)) i (.inr j) = 0 :=
  dgHomEquiv_symm_symm_apply R (M := P) (N := (extension P Q g hg)) (inlMatrix R P Q) i (Sum.inr j)

/-- The block of the inclusion of `Q` into an extension to the summands of `P` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionInr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInr R hg)) i (.inl j) = 0 :=
  dgHomEquiv_symm_symm_apply R (M := Q) (N := (extension P Q g hg)) (inrMatrix R P Q) i (Sum.inl j)

/-- The block of the inclusion of `Q` into an extension on the summands of `Q` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionInr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInr R hg)) i (.inr j) =
      matrixEquiv R _ _ 0 (dgId R Q.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := Q) (N := (extension P Q g hg)) (inrMatrix R P Q) i (Sum.inr j)

/-- The block of the projection of an extension onto `P` on the summands of `P` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionFst_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionFst R hg)) (.inl i) j =
      matrixEquiv R _ _ 0 (dgId R P.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := P) (fstMatrix R P Q) (Sum.inl i) j

/-- The block of the projection of an extension onto `P` from the summands of `Q` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionFst_inr (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionFst R hg)) (.inr i) j = 0 :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := P) (fstMatrix R P Q) (Sum.inr i) j

/-- The block of the projection of an extension onto `Q` from the summands of `P` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionSnd_inl (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionSnd R hg)) (.inl i) j = 0 :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := Q) (sndMatrix R P Q) (Sum.inl i) j

/-- The block of the projection of an extension onto `Q` on the summands of `Q` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionSnd_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionSnd R hg)) (.inr i) j =
      matrixEquiv R _ _ 0 (dgId R Q.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := Q) (sndMatrix R P Q) (Sum.inr i) j

end structureMaps

/-! ### Differentials of the structure maps -/

section differentials

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/-- The inclusion of `P` into an extension is closed. -/
@[simp↓]
theorem dgDifferential_extensionInl : dgDifferential R 0 (extensionInl R hg) = 0 :=
  dgHom_ext' (n := 1) fun i k ↦ by
    rw [dgDifferential_apply_zero, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply,
      Fintype.sum_sum_type]
    rcases k with j | j <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The projection of an extension onto `Q` is closed. -/
@[simp↓]
theorem dgDifferential_extensionSnd : dgDifferential R 0 (extensionSnd R hg) = 0 :=
  dgHom_ext' (n := 1) fun k j ↦ by
    rw [dgDifferential_apply_zero, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply,
      Fintype.sum_sum_type]
    rcases k with i | i <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The differential of the inclusion of `Q` into an extension along `g` is `g` followed by the
inclusion of `P`. -/
theorem dgDifferential_extensionInr :
    dgDifferential R 0 (extensionInr R hg) = dgComp R g (extensionInl R hg) (add_zero 1) :=
  dgHom_ext' (n := 1) fun i k ↦ by
    rw [dgDifferential_apply_zero, dgComp_apply, Fintype.sum_sum_type]
    rcases k with j | j <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The differential of the projection of an extension along `g` onto `P` is minus the
projection onto `Q` followed by `g`. -/
theorem dgDifferential_extensionFst :
    dgDifferential R 0 (extensionFst R hg) = -dgComp R (extensionSnd R hg) g (zero_add 1) :=
  dgHom_ext' (n := 1) fun k j ↦ by
    rw [dgDifferential_apply_zero, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, dgComp_apply,
      Fintype.sum_sum_type]
    rcases k with i | i <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

end differentials

/-! ### The biproduct equations -/

section biproduct

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/-- The inclusion of `P` into an extension followed by the projection onto `P` is the
identity. -/
@[simp↓]
theorem dgComp_extensionInl_extensionFst :
    dgComp R (extensionInl R hg) (extensionFst R hg) (add_zero 0) = dgId R P :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, dgId_apply, Fintype.sum_sum_type]
    simp [-DGCategoryData.dgId_toDGCategory]

/-- The inclusion of `P` into an extension followed by the projection onto `Q` vanishes. -/
@[simp↓]
theorem dgComp_extensionInl_extensionSnd :
    dgComp R (extensionInl R hg) (extensionSnd R hg) (add_zero 0) = 0 :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Fintype.sum_sum_type]
    simp

/-- The inclusion of `Q` into an extension followed by the projection onto `P` vanishes. -/
@[simp↓]
theorem dgComp_extensionInr_extensionFst :
    dgComp R (extensionInr R hg) (extensionFst R hg) (add_zero 0) = 0 :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Fintype.sum_sum_type]
    simp

/-- The inclusion of `Q` into an extension followed by the projection onto `Q` is the
identity. -/
@[simp↓]
theorem dgComp_extensionInr_extensionSnd :
    dgComp R (extensionInr R hg) (extensionSnd R hg) (add_zero 0) = dgId R Q :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, dgId_apply, Fintype.sum_sum_type]
    simp [-DGCategoryData.dgId_toDGCategory]

/-- **An extension is the direct sum of `P` and `Q` as a graded object**: the projections
followed by the inclusions sum to the identity. -/
theorem dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr :
    dgComp R (extensionFst R hg) (extensionInl R hg) (add_zero 0) +
      dgComp R (extensionSnd R hg) (extensionInr R hg) (add_zero 0) = dgId R _ :=
  dgHom_ext' fun a b ↦ by
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, dgComp_apply, dgComp_apply, dgId_apply]
    rcases a with i | i <;> rcases b with j | j
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inl]
      simp [-DGCategoryData.dgId_toDGCategory]
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inr]
      simp
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inl]
      simp
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inr]
      simp [-DGCategoryData.dgId_toDGCategory]

end biproduct

/-! ### Extensions along invertible morphisms are contractible -/

section contractible

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0) {g' : DGHom R (-1) P Q}

/-- **The contracting homotopy of an extension along an invertible morphism**: if the closed
degree-one morphism `g : Q ⟶ P` has an inverse `g' : P ⟶ Q` of degree `-1`, then the differential
of minus the projection onto `P`, followed by `g'` and the inclusion of `Q`, is the identity of the
extension. -/
theorem dgDifferential_neg_dgComp_extensionFst_extensionInr
    (hgg' : dgComp R g g' (add_neg_cancel 1) = dgId R Q)
    (hg'g : dgComp R g' g (neg_add_cancel 1) = dgId R P) :
    dgDifferential R (-1)
        (-dgComp R (dgComp R (extensionFst R hg) g' (zero_add (-1))) (extensionInr R hg)
          (add_zero (-1))) =
      dgId R (extension P Q g hg) := by
  -- The inverse pairs cancel inside the two terms produced by the Leibniz rule.
  have hsnd : dgComp R (dgComp R (extensionSnd R hg) g (zero_add 1)) g' (add_neg_cancel 1) =
      extensionSnd R hg := by
    rw [dgComp_assoc R _ g g' (zero_add 1) (add_neg_cancel 1) (by omega), hgg', dgComp_dgId]
  have hfst : dgComp R (dgComp R (extensionFst R hg) g' (zero_add (-1)))
      (dgComp R g (extensionInl R hg) (add_zero 1)) (neg_add_cancel 1) =
      dgComp R (extensionFst R hg) (extensionInl R hg) (add_zero 0) := by
    rw [dgComp_assoc R _ g' _ (zero_add (-1)) (neg_add_cancel 1) (by omega),
      ← dgComp_assoc R g' g _ (neg_add_cancel 1) (add_zero 1) (by omega), hg'g, dgId_dgComp]
  -- Expand by the Leibniz rule; `g'` is closed, being inverse to the closed morphism `g`.
  rw [map_neg, dgDifferential_dgComp, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionInr, dgDifferential_eq_zero_of_dgComp_eq_dgId R hg _ hgg' hg'g]
  simp only [dgComp_zero, smul_zero, add_zero, neg_dgComp, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, hsnd, hfst]
  rw [← dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr R hg]
  abel

/-- **An extension along an invertible morphism is contractible**: if the closed degree-one
morphism `g : Q ⟶ P` has an inverse of degree `-1`, then the extension of `Q` by `P` along `g` is
a zero object of the homotopy category. -/
theorem isZero_of_extension (hgg' : dgComp R g g' (add_neg_cancel 1) = dgId R Q)
    (hg'g : dgComp R g' g (neg_add_cancel 1) = dgId R P) :
    Limits.IsZero (DGHomotopyCategory.of R (extension P Q g hg)) :=
  (DGHomotopyCategory.isZero_of_iff_dgId_mem_dgBoundaries R _).mpr
    ((mem_dgBoundaries R).mpr
      ⟨_, dgDifferential_neg_dgComp_extensionFst_extensionInr R hg hgg' hg'g⟩)

end contractible

/-! ### Extensions along homotopic morphisms are isomorphic -/

section homotopy

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g g' : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0) (hg' : dgDifferential R 1 g' = 0)

/-- The degree-zero morphism `extension P Q g ⟶ extension P Q g'` induced by a degree-zero
morphism `k : Q ⟶ P`: the identity on the summands `P` and `Q`, together with `k` in the block
from `Q` to `P`.  It is closed when `d k = g - g'`
(`TauCeti.DGTwistedObject.dgDifferential_extensionHomOfHomotopy`). -/
noncomputable def extensionHomOfHomotopy (k : DGHom R 0 Q P) :
    DGHom R 0 (extension P Q g hg) (extension P Q g' hg') :=
  dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
    dgComp R (extensionSnd R hg) (extensionInr R hg') (add_zero 0) +
    dgComp R (extensionSnd R hg) (dgComp R k (extensionInl R hg') (add_zero 0)) (add_zero 0)

theorem extensionHomOfHomotopy_def (k : DGHom R 0 Q P) :
    extensionHomOfHomotopy R hg hg' k =
      dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
        dgComp R (extensionSnd R hg) (extensionInr R hg') (add_zero 0) +
        dgComp R (extensionSnd R hg) (dgComp R k (extensionInl R hg') (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The morphism of extensions induced by the zero morphism is the identity. -/
@[simp]
theorem extensionHomOfHomotopy_zero :
    extensionHomOfHomotopy R hg hg 0 = dgId R (extension P Q g hg) := by
  rw [extensionHomOfHomotopy_def, zero_dgComp, dgComp_zero, add_zero,
    dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr]

/-- **The morphism of extensions induced by a homotopy is closed**: if `d k = g - g'`, then the
differential of `TauCeti.DGTwistedObject.extensionHomOfHomotopy` vanishes. -/
theorem dgDifferential_extensionHomOfHomotopy {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    dgDifferential R 0 (extensionHomOfHomotopy R hg hg' k) = 0 := by
  rw [extensionHomOfHomotopy_def, map_add, map_add, dgDifferential_dgComp, dgDifferential_dgComp,
    dgDifferential_dgComp, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgDifferential_extensionInl, dgDifferential_extensionInr, hk,
    neg_dgComp, dgComp_assoc R _ g _ (zero_add 1) (add_zero 1) (by omega), sub_eq_add_neg,
    add_dgComp, neg_dgComp]
  simp only [dgComp_zero, zero_dgComp, smul_zero, add_zero, zero_add, Int.negOnePow_zero,
    one_smul, dgComp_add, dgComp_neg]
  abel

/-- Composition of the degree-zero morphisms of a sequence of extensions is associative. -/
private theorem dgComp_assoc_zero {X Y Z W : DGTwistedObject R (DGAdditiveClosure E)}
    (f : DGHom R 0 X Y) (f' : DGHom R 0 Y Z) (f'' : DGHom R 0 Z W) :
    dgComp R (dgComp R f f' (add_zero 0)) f'' (add_zero 0) =
      dgComp R f (dgComp R f' f'' (add_zero 0)) (add_zero 0) :=
  dgComp_assoc R f f' f'' (add_zero 0) (add_zero 0) (add_zero _)

/-- **The morphisms of extensions induced by `k` and `-k` are mutually inverse.** -/
theorem dgComp_extensionHomOfHomotopy_neg (k : DGHom R 0 Q P) :
    dgComp R (extensionHomOfHomotopy R hg hg' k) (extensionHomOfHomotopy R hg' hg (-k))
      (add_zero 0) = dgId R (extension P Q g hg) := by
  -- Reassociated biproduct equations of `extension P Q g'`.
  have hll {Z : DGTwistedObject R (DGAdditiveClosure E)} (x : DGHom R 0 P Z) :
      dgComp R (extensionInl R hg') (dgComp R (extensionFst R hg') x (add_zero 0)) (add_zero 0) =
        x := by
    rw [← dgComp_assoc_zero, dgComp_extensionInl_extensionFst, dgId_dgComp]
  have hlr {Z : DGTwistedObject R (DGAdditiveClosure E)} (x : DGHom R 0 Q Z) :
      dgComp R (extensionInl R hg') (dgComp R (extensionSnd R hg') x (add_zero 0)) (add_zero 0) =
        0 := by
    rw [← dgComp_assoc_zero, dgComp_extensionInl_extensionSnd, zero_dgComp]
  have hrl {Z : DGTwistedObject R (DGAdditiveClosure E)} (x : DGHom R 0 P Z) :
      dgComp R (extensionInr R hg') (dgComp R (extensionFst R hg') x (add_zero 0)) (add_zero 0) =
        0 := by
    rw [← dgComp_assoc_zero, dgComp_extensionInr_extensionFst, zero_dgComp]
  have hrr {Z : DGTwistedObject R (DGAdditiveClosure E)} (x : DGHom R 0 Q Z) :
      dgComp R (extensionInr R hg') (dgComp R (extensionSnd R hg') x (add_zero 0)) (add_zero 0) =
        x := by
    rw [← dgComp_assoc_zero, dgComp_extensionInr_extensionSnd, dgId_dgComp]
  simp only [extensionHomOfHomotopy_def, add_dgComp, dgComp_add, neg_dgComp, dgComp_neg,
    dgComp_assoc_zero, hll, hlr, hrl, hrr, dgComp_zero, add_zero]
  rw [← dgComp_extensionFst_extensionInl_add_dgComp_extensionSnd_extensionInr R hg]
  abel

variable {hg hg'} in
/-- **Extensions along homotopic morphisms are isomorphic**: if `g - g' = d k` for a degree-zero
morphism `k : Q ⟶ P`, then `extension P Q g` and `extension P Q g'` are isomorphic in the
homotopy category, through the morphisms induced by `k` and `-k`. -/
noncomputable def extensionIsoOfHomotopy {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    DGHomotopyCategory.of R (extension P Q g hg) ≅ DGHomotopyCategory.of R (extension P Q g' hg')
    where
  hom := DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg hg' k)
    ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg hg' hk))
  inv := DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg' hg (-k))
    ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg' hg
      (by rw [map_neg, hk, neg_sub])))
  hom_inv_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgComp_extensionHomOfHomotopy_neg,
      DGHomotopyCategory.homOf_dgId]
  inv_hom_id := by
    have h := dgComp_extensionHomOfHomotopy_neg R hg' hg (-k)
    rw [neg_neg] at h
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, h, DGHomotopyCategory.homOf_dgId]

variable {hg hg'} in
@[simp]
theorem extensionIsoOfHomotopy_hom {k : DGHom R 0 Q P} (hk : dgDifferential R 0 k = g - g') :
    (extensionIsoOfHomotopy R (hg := hg) (hg' := hg') hk).hom =
      DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg hg' k)
        ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg hg' hk)) :=
  (rfl)

variable {hg hg'} in
@[simp]
theorem extensionIsoOfHomotopy_inv {k : DGHom R 0 Q P} (hk : dgDifferential R 0 k = g - g') :
    (extensionIsoOfHomotopy R (hg := hg) (hg' := hg') hk).inv =
      DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg' hg (-k))
        ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg' hg
          (by rw [map_neg, hk, neg_sub]))) :=
  (rfl)

end homotopy

end DGTwistedObject

end TauCeti
