/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Corestriction in negative Tate degrees

Let `f : H → G` be a homomorphism of finite groups and let `M` be a `G`-representation. In
every Tate degree at most `-2`, Mathlib identifies Tate cohomology with ordinary group homology:

`Ĥ⁻ⁿ⁻¹(G, M) ≃ Hₙ(G, M)` for `n > 0`.

Ordinary group homology is covariant in the group, so `f` gives
corestriction

`Ĥ⁻ⁿ⁻¹(H, M) ⟶ Ĥ⁻ⁿ⁻¹(G, M)`.

This file packages that composite in every such degree and proves that transport back through
the Tate comparison is exactly Mathlib's group-homology map. The construction is a natural
transformation in the coefficient representation. Degree `-2`, which corresponds to first group
homology and hence to the abelianization for trivial integral coefficients, is exported under the
separate name `HNegTwoCor` for the low-degree Artin--Tate applications. Its interaction with the
low-degree homology comparison is recorded explicitly.

This construction treats degrees at most `-2` via group homology; positive degrees instead require
a cohomological corestriction construction.

## Main definitions

* `TauCeti.TateCohomology.negSuccCorNatTrans`: corestriction along a group homomorphism in degree
  `-(n+1)`, natural in the
  coefficient representation, for `n > 0`.
* `TauCeti.TateCohomology.negSuccCor`: its value on one representation.
* `TauCeti.TateCohomology.HNegTwoCor`: the degree-`-2` specialization.

## Main results

* `TauCeti.TateCohomology.negSuccCor_comp_negSuccIso_hom`: negative corestriction agrees
  with ordinary group-homology corestriction through `TauCeti.TateCohomology.negSuccIso`.
* `TauCeti.TateCohomology.map_comp_negSuccCor`: negative corestriction is natural in its
  coefficients.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {R G H : Type u} [CommRing R] [Group G] [Group H] [Fintype G] [Fintype H]

/-- **Corestriction along a homomorphism in Tate degree `-(n+1)`**, natural in the coefficient
representation, where `n > 0`. Through Mathlib's negative-degree Tate comparison this is the
ordinary covariant map on `n`th group homology induced by the homomorphism. -/
def negSuccCorNatTrans (f : H →* G) (n : ℕ) [NeZero n] :
    Rep.resFunctor f ⋙
        tateCohomologyFunctor (R := R) (G := H) (Int.negSucc n) ⟶
      tateCohomologyFunctor (R := R) (G := G) (Int.negSucc n) :=
  Functor.whiskerLeft _ (TateCohomology.isoGroupHomology _ n (Int.negSucc_eq n)).hom ≫
    groupHomology.coresNatTrans R f n ≫
      (TateCohomology.isoGroupHomology _ n (Int.negSucc_eq n)).inv

/-- Corestriction along `f : H → G` in Tate degree `-(n+1)`, where `n > 0`. -/
def negSuccCor (M : Rep R G) (f : H →* G) (n : ℕ) [NeZero n] :
    tateCohomology (Rep.res f M) (Int.negSucc n) ⟶
      tateCohomology M (Int.negSucc n) :=
  (negSuccCorNatTrans f n).app M

/-- Negative-degree Tate corestriction is the ordinary group-homology map through
`TauCeti.TateCohomology.negSuccIso`. -/
-- The right side is stated through `groupHomology.map`, the `simp` normal form of
-- `(groupHomology.coresNatTrans R f n).app M`.
@[reassoc (attr := simp)]
theorem negSuccCor_comp_negSuccIso_hom (M : Rep R G) (f : H →* G) (n : ℕ) [NeZero n] :
    negSuccCor M f n ≫ (negSuccIso M n).hom =
      (negSuccIso (Rep.res f M) n).hom ≫ groupHomology.map f (𝟙 (Rep.res f M)) n := by
  simp only [negSuccIso_hom]
  -- `negSuccCor` unfolds definitionally to `hom ≫ cores ≫ inv`, so cancelling the comparison
  -- isomorphism holds by `rfl`; `simp` does not perform this cancellation here.
  exact (Iso.eq_comp_inv _).1 (by rfl)

/-- Negative-degree Tate corestriction is natural in the coefficient representation. -/
-- Stated with `Rep.resMap f φ`, the form to which `simp` reduces `(Rep.resFunctor f).map φ`
-- before looking a term up, so that this lemma and `map_comp_HNegTwoCor` fire.
@[reassoc (attr := simp)]
theorem map_comp_negSuccCor {M N : Rep R G} (f : H →* G) (n : ℕ) [NeZero n] (φ : M ⟶ N) :
    (tateCohomologyFunctor (Int.negSucc n)).map (Rep.resMap f φ) ≫ negSuccCor N f n =
      negSuccCor M f n ≫ (tateCohomologyFunctor (Int.negSucc n)).map φ :=
  (negSuccCorNatTrans f n).naturality φ

/-- Corestriction along a group homomorphism in degree `-2` Tate cohomology. Under the comparison
with group homology, this is the induced map on first homology. -/
def HNegTwoCor (M : Rep R G) (f : H →* G) :
    tateCohomology (Rep.res f M) (-2) ⟶ tateCohomology M (-2) :=
  negSuccCor M f 1

/-- Degree-`-2` corestriction is natural in the coefficient representation. -/
@[reassoc (attr := simp)]
theorem map_comp_HNegTwoCor {M N : Rep R G} (f : H →* G) (φ : M ⟶ N) :
    (tateCohomologyFunctor (-2)).map (Rep.resMap f φ) ≫ HNegTwoCor N f =
      HNegTwoCor M f ≫ (tateCohomologyFunctor (-2)).map φ :=
  map_comp_negSuccCor f 1 φ

/-- Degree-`-2` corestriction agrees with the map induced on first group homology. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegTwoCor_comp_isoGroupHomology_hom (M : Rep R G) (f : H →* G) :
    HNegTwoCor M f ≫
        (TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app M =
      (TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app (Rep.res f M) ≫
        (groupHomology.coresNatTrans R f 1).app M := by
  have h := negSuccCor_comp_negSuccIso_hom M f 1
  simp only [negSuccIso_hom] at h
  -- `h` is stated in degree `Int.negSucc 1` and through `groupHomology.map`; both agree with this
  -- statement's `-2` and `coresNatTrans` definitionally.
  exact h

end TauCeti.TateCohomology
