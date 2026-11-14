/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

import TauCeti.Algebra.Coalgebra.MonoidAlgebra

/-!
# Group-like elements of monoid algebras

The standard basis elements of a monoid algebra over a commutative semiring are group-like and
span the whole algebra. Over a commutative ring with connected prime spectrum, these are exactly
the group-like elements. The proof of the classification compares coefficients in the group-like
comultiplication identity. Connectedness makes every idempotent coefficient zero or one, and the
counit condition excludes the zero element.

Consequently, a bialgebra morphism between monoid algebras over such a base uniquely
recovers the monoid homomorphism on their standard basis indices. This gives a two-sided
inverse to `MonoidAlgebra.mapDomainBialgHom` on the corresponding hom-sets.

## Main declarations

* `MonoidAlgebra.isGroupLikeElem_iff_eq_single`: classification of group-like elements in a
  monoid algebra over a connected base (with additive counterpart
  `AddMonoidAlgebra.isGroupLikeElem_iff_eq_single`).
* `TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top`: the group-like elements span every monoid
  algebra.
* `TauCeti.MonoidAlgebra.groupLikeEquiv`: the group-like elements are multiplicatively equivalent
  to the index monoid.
* `TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage`: recover the monoid homomorphism inducing a
  bialgebra morphism between monoid algebras over a connected base.
* `TauCeti.MonoidAlgebra.mapDomainBialgHom_surjective`: every bialgebra morphism between monoid
  algebras over a connected base is induced by a monoid homomorphism.
-/

public section

universe u v w t

namespace MonoidAlgebra

/-- Over a commutative ring with connected prime spectrum, the group-like elements
of a monoid algebra are exactly its standard basis elements, with a unique basis
index. -/
@[to_additive (dont_translate := R) isGroupLikeElem_iff_eq_single
/-- Over a commutative ring with connected prime spectrum, the group-like elements
of an additive monoid algebra are exactly its standard basis elements, with a unique
basis index. -/]
theorem isGroupLikeElem_iff_eq_single {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type v}
    (x : MonoidAlgebra R H) :
    IsGroupLikeElem R x ↔ ∃! h : H, x = single h 1 := by
  classical
  let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  constructor
  · intro hx
    have hcoeff (g h : H) :
        (if g = h then x.coeff g else 0) = x.coeff g * x.coeff h := by
      have hcomul := congrArg
        (fun y : TensorProduct R (MonoidAlgebra R H) (MonoidAlgebra R H) =>
          (tensorEquiv R y).coeff (g, h)) hx.comul_eq_tmul_self
      rw [tensorEquiv_comul_apply] at hcomul
      simpa using hcomul
    have hcoeff_zero_or_one (g : H) : x.coeff g = 0 ∨ x.coeff g = 1 := by
      apply IsIdempotentElem.eq_zero_or_eq_one_of_preconnectedSpace
      exact isIdempotentElem_iff.mpr (by simpa using (hcoeff g g).symm)
    have hx_coeff_ne : x.coeff ≠ 0 := by
      intro hzero
      apply hx.ne_zero
      apply coeff_injective
      simpa using hzero
    obtain ⟨h, hh⟩ := Finsupp.support_nonempty_iff.mpr hx_coeff_ne
    have hh_one : x.coeff h = 1 :=
      (hcoeff_zero_or_one h).resolve_left (Finsupp.mem_support_iff.mp hh)
    have hx_single : x = single h 1 := by
      apply MonoidAlgebra.ext
      ext k
      by_cases hk : k = h
      · subst k
        simp [hh_one]
      · have hk_zero : x.coeff k = 0 := by
          have horth := hcoeff k h
          rw [ite_eq_right hk, hh_one, mul_one] at horth
          exact horth.symm
        simp [hk, hk_zero]
    refine ⟨h, hx_single, ?_⟩
    intro h' hx_single'
    exact single_left_injective (R := R) (M := H) one_ne_zero (hx_single'.symm.trans hx_single)
  · rintro ⟨h, rfl, -⟩
    exact isGroupLikeElem_single_one (R := R) (A := R) h

end MonoidAlgebra

open MonoidAlgebra

namespace TauCeti

namespace MonoidAlgebra

variable (R : Type u)

/-- The group-like elements of a monoid algebra span the whole algebra: every standard basis
element is group-like, and the standard basis spans. -/
@[simp]
theorem groupLikeSetSpan_eq_top [CommSemiring R] (G : Type v) :
    Subcoalgebra.groupLikeSetSpan (R := R) (C := MonoidAlgebra R G) Set.univ = ⊤ := by
  rw [Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  have hrange : Set.range (GroupLike.val (R := R) (A := MonoidAlgebra R G)) =
      {x : MonoidAlgebra R G | IsGroupLikeElem R x} :=
    Set.ext fun x ↦
      ⟨fun ⟨g, hg⟩ ↦ hg ▸ g.isGroupLikeElem_val, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact span_isGroupLikeElem

/-- The group-like elements of a monoid algebra over a connected base are its standard basis
elements, multiplicatively identified with the index monoid. -/
noncomputable def groupLikeEquiv [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H] :
    GroupLike R (MonoidAlgebra R H) ≃* H where
  toFun x := Classical.choose
    (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val)
  invFun h := ⟨single h 1, isGroupLikeElem_single_one (R := R) (A := R) h⟩
  left_inv x := by
    apply GroupLike.val_injective
    exact (Classical.choose_spec
      (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val)).1.symm
  right_inv h := by
    let hx : IsGroupLikeElem R (single h (1 : R)) :=
      isGroupLikeElem_single_one (R := R) (A := R) h
    exact (Classical.choose_spec
      ((single h (1 : R)).isGroupLikeElem_iff_eq_single.mp hx)).2 h rfl |>.symm
  map_mul' x y := by
    let hx := Classical.choose_spec
      (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val)
    let hy := Classical.choose_spec
      (y.val.isGroupLikeElem_iff_eq_single.mp y.isGroupLikeElem_val)
    have hxy : (x * y).val = single
        (Classical.choose (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val) *
          Classical.choose (y.val.isGroupLikeElem_iff_eq_single.mp y.isGroupLikeElem_val))
        1 := by
      calc
        (x * y).val = x.val * y.val := GroupLike.val_mul x y
        _ = single
              (Classical.choose
                (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val)) 1 *
            single
              (Classical.choose
                (y.val.isGroupLikeElem_iff_eq_single.mp y.isGroupLikeElem_val)) 1 :=
          congrArg₂ (· * ·) hx.1 hy.1
        _ = _ := by simp
    exact ((Classical.choose_spec
      ((x * y).val.isGroupLikeElem_iff_eq_single.mp
        (x * y).isGroupLikeElem_val)).2 _ hxy).symm

/-- The standard basis index recovered from a group-like element is characterized by its
underlying value. -/
@[simp]
theorem groupLikeEquiv_apply_eq_iff [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (x : GroupLike R (MonoidAlgebra R H)) (h : H) :
    groupLikeEquiv (R := R) x = h ↔ x.val = single h 1 := by
  let hx := Classical.choose_spec
    (x.val.isGroupLikeElem_iff_eq_single.mp x.isGroupLikeElem_val)
  constructor
  · rintro rfl
    exact hx.1
  · exact fun hsingle ↦ (hx.2 h hsingle).symm

/-- Evaluating `groupLikeEquiv` on a standard basis element recovers its index. -/
@[simp]
theorem groupLikeEquiv_mk_single [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (h : H) (hx : IsGroupLikeElem R (single h (1 : R))) :
    groupLikeEquiv (R := R) ⟨single h 1, hx⟩ = h :=
  (groupLikeEquiv_apply_eq_iff R ⟨single h 1, hx⟩ h).mpr rfl

/-- Scaling the standard basis element at `groupLikeEquiv x` gives the scalar multiple of `x`. -/
@[simp]
theorem single_groupLikeEquiv [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (x : GroupLike R (MonoidAlgebra R H)) (r : R) :
    single (groupLikeEquiv (R := R) x) r = r • x.val := by
  have hx : x.val = single (groupLikeEquiv (R := R) x) 1 :=
    (groupLikeEquiv_apply_eq_iff R x _).mp rfl
  rw [hx, smul_single, smul_eq_mul, mul_one]

/-- The inverse image of an index under `groupLikeEquiv` is the corresponding standard basis
element. -/
@[simp]
theorem val_groupLikeEquiv_symm [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H] (h : H) :
    ((groupLikeEquiv (R := R) (H := H)).symm h).val = single h 1 :=
  (rfl)

/-- Recover the monoid homomorphism inducing a bialgebra morphism between monoid
algebras over a base with connected prime spectrum. -/
noncomputable def mapDomainBialgHomPreimage [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) : G →* H :=
  (groupLikeEquiv (R := R) (H := H)).toMonoidHom.comp
    (F.mapGroupLike.comp
      (groupLikeEquiv (R := R) (H := G)).symm.toMonoidHom)

/-- The recovered monoid homomorphism takes `g` to `h` exactly when the bialgebra
morphism takes the corresponding standard basis element to the standard basis element
indexed by `h`. -/
theorem mapDomainBialgHomPreimage_apply_eq_iff [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) (h : H) :
    mapDomainBialgHomPreimage R F g = h ↔ F (single g 1) = single h 1 := by
  simp only [mapDomainBialgHomPreimage, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    groupLikeEquiv_apply_eq_iff, BialgHom.val_mapGroupLike, val_groupLikeEquiv_symm]

/-- Each standard basis element indexed by the recovered monoid homomorphism agrees with the
image of the original basis element under the bialgebra morphism. -/
@[simp]
theorem single_mapDomainBialgHomPreimage [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) (g : G) (r : R) :
    single (mapDomainBialgHomPreimage R F g) r = F (single g r) := by
  have h1 : F (single g 1) = single (mapDomainBialgHomPreimage R F g) 1 :=
    (mapDomainBialgHomPreimage_apply_eq_iff R F g _).mp rfl
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul, h1]

/-- Mapping the domain by the recovered monoid homomorphism gives the original
bialgebra morphism. -/
@[simp]
theorem mapDomainBialgHom_mapDomainBialgHomPreimage [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    mapDomainBialgHom R (mapDomainBialgHomPreimage R F) = F := by
  ext; simp

/-- Over a nontrivial base, distinct monoid homomorphisms induce distinct bialgebra
morphisms between monoid algebras. -/
theorem mapDomainBialgHom_injective [CommSemiring R] [Nontrivial R]
    {G : Type v} {H : Type w} [Monoid G] [Monoid H] :
    Function.Injective (mapDomainBialgHom R :
      (G →* H) → (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)) := by
  intro φ ψ h
  ext g
  apply single_left_injective (R := R) (M := H) one_ne_zero
  calc
    single (φ g) 1 = mapDomainBialgHom R φ (single g 1) :=
      (mapDomain_single (R := R) (f := φ)).symm
    _ = mapDomainBialgHom R ψ (single g 1) := by rw [h]
    _ = single (ψ g) 1 := mapDomain_single

/-- Recovering from the bialgebra morphism induced by a monoid homomorphism returns
that monoid homomorphism. -/
@[simp]
theorem mapDomainBialgHomPreimage_mapDomainBialgHom [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H] (φ : G →* H) :
    mapDomainBialgHomPreimage R (mapDomainBialgHom R φ) = φ := by
  ext g
  apply (mapDomainBialgHomPreimage_apply_eq_iff R _ g _).mpr
  exact mapDomain_single

/-- The monoid homomorphism recovered from the identity bialgebra morphism is the identity. -/
@[simp]
theorem mapDomainBialgHomPreimage_id [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} [Monoid G] :
    mapDomainBialgHomPreimage R (BialgHom.id R (MonoidAlgebra R G)) = MonoidHom.id G := by
  rw [← mapDomainBialgHom_id (R := R) (M := G), mapDomainBialgHomPreimage_mapDomainBialgHom]

/-- Recovering the underlying monoid homomorphism respects composition of bialgebra morphisms. -/
@[simp]
theorem mapDomainBialgHomPreimage_comp [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w} {I : Type t}
    [Monoid G] [Monoid H] [Monoid I]
    (F : MonoidAlgebra R H →ₐc[R] MonoidAlgebra R I)
    (F' : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    mapDomainBialgHomPreimage R (F.comp F') =
      (mapDomainBialgHomPreimage R F).comp (mapDomainBialgHomPreimage R F') := by
  rw [← mapDomainBialgHomPreimage_mapDomainBialgHom R
      ((mapDomainBialgHomPreimage R F).comp (mapDomainBialgHomPreimage R F')),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainBialgHomPreimage,
    mapDomainBialgHom_mapDomainBialgHomPreimage]

/-- Every bialgebra morphism between monoid algebras over a base with connected prime
spectrum is induced by a monoid homomorphism. -/
theorem mapDomainBialgHom_surjective [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H] :
    Function.Surjective (mapDomainBialgHom R :
      (G →* H) → (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)) := by
  intro F
  exact ⟨mapDomainBialgHomPreimage R F, mapDomainBialgHom_mapDomainBialgHomPreimage R F⟩

end MonoidAlgebra

end TauCeti
