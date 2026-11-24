/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Biproduct

/-!
# The topological `K⁰` group of a space

For a topological space `X` and a nontrivially normed field `𝕜`, `TauCeti.TopologicalKZero 𝕜 X`
is the Grothendieck group of finite-rank `𝕜`-vector bundles over `X` under Whitney sum: the split
Grothendieck group `TauCeti.SplitK0` of the category `TauCeti.FiniteRankAtlas 𝕜 X` of
variable-rank bundle atlases, whose binary biproduct is the Whitney sum. For a compact Hausdorff
`X` this is the usual complex `K⁰(X)` when `𝕜 = ℂ` and the real `KO⁰(X)` when `𝕜 = ℝ`. Here `X` is
an arbitrary topological space, with no compactness or separation hypothesis; over such a base
the Grothendieck group of bundles need not agree with other descriptions of `K⁰(X)`. The rank of a
bundle is only required to be locally constant, so it may be unbounded on a noncompact or
disconnected base. Over real or complex scalars the group lives in the universe of `X`.

The general theory of split `K₀` applies verbatim: every class is a difference `[E] - [F]`
(`TauCeti.SplitK0.exists_eq_sub`), additive homomorphisms out of `K⁰` are the isomorphism-invariant
Whitney-additive invariants of bundles (`TauCeti.SplitK0.liftEquiv`), and `K⁰` is the group
completion of the monoid of isomorphism classes of bundles
(`TauCeti.SplitK0.grothendieckAddGroupEquiv`). This file adds the statements specific to bundles.

## Main definitions

* `TauCeti.TopologicalKZero 𝕜 X`: the topological `K⁰` of `X` with scalars `𝕜`.
* `TauCeti.TopologicalKZero.rankHom`: the rank homomorphism to locally constant integer-valued
  functions, `[E] ↦ rank E`.
* `TauCeti.TopologicalKZero.trivialHom`: its splitting, sending a locally constant `r` to the
  difference of the classes of the trivial bundles of ranks `max r 0` and `max (-r) 0`.
* `TauCeti.TopologicalKZero.rankAddEquiv`: over a base with at most one point, `K⁰` is the group
  of locally constant integer-valued functions, and `TauCeti.TopologicalKZero.rankAddEquivInt`:
  over a point it is `ℤ`.

## Main results

* `TauCeti.TopologicalKZero.of_eq_of_iff`: `[E] = [F]` exactly when `E ⊕ G ≅ F ⊕ G` for some
  bundle `G`, and `TauCeti.TopologicalKZero.of_sub_of_eq_of_sub_of_iff`: the pair relation,
  `[E] - [F] = [E'] - [F']` exactly when `E ⊕ F' ⊕ G ≅ E' ⊕ F ⊕ G` for some bundle `G`.
* `TauCeti.TopologicalKZero.rankHom_trivialHom`: `trivialHom` is a section of `rankHom`, so the
  rank homomorphism is surjective, with no bounded-rank hypothesis.
* `TauCeti.TopologicalKZero.instSubsingletonOfIsEmpty`: over the empty space `K⁰` is trivial.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017), §2.1, pp. 39–40, for the pair
  description of `K(X)` over a compact Hausdorff base and its equality criterion by a common
  trivial summand; over an arbitrary base the criterion here uses an arbitrary common summand.
* M. F. Atiyah, *K-Theory*, W. A. Benjamin (1967), §2.1, for `K(X)` as the group completion of the
  monoid of isomorphism classes of bundles under Whitney sum.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- The topological `K⁰` of `X` with scalars `𝕜`: the split Grothendieck group of finite-rank
`𝕜`-vector bundles over `X`, presented by the variable-rank atlases `FiniteRankAtlas 𝕜 X`, with
`[E ⊕ F] = [E] + [F]` for the Whitney sum. For a compact Hausdorff `X` it is the usual `K⁰(X)`
when `𝕜 = ℂ` and `KO⁰(X)` when `𝕜 = ℝ`. -/
abbrev TopologicalKZero : Type (max u v) :=
  SplitK0.{max u v} (FiniteRankAtlas 𝕜 X)

namespace TopologicalKZero

open FiniteRankAtlas

variable {𝕜 X}

/-- The class of a Whitney sum is the sum of the classes. -/
@[simp]
theorem of_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (SplitK0.of (whitneySum A D) : TopologicalKZero 𝕜 X) = SplitK0.of A + SplitK0.of D := by
  rw [← SplitK0.of_congr (biprodIsoWhitneySum A D), SplitK0.of_biprod]

/-- Two bundles have the same class in `K⁰` exactly when they become isomorphic after adding a
common bundle `G`, which need not be trivial. -/
theorem of_eq_of_iff {A D : FiniteRankAtlas 𝕜 X} :
    (SplitK0.of A : TopologicalKZero 𝕜 X) = SplitK0.of D ↔
      ∃ G, Nonempty (whitneySum A G ≅ whitneySum D G) := by
  rw [SplitK0.of_eq_of_iff]
  exact exists_congr fun G =>
    ((biprodIsoWhitneySum A G).isoCongr (biprodIsoWhitneySum D G)).nonempty_congr

/-- The pair relation: two formal differences of bundles agree in `K⁰`,
`[E] - [F] = [E'] - [F']`, exactly when `E ⊕ F' ⊕ G ≅ E' ⊕ F ⊕ G` for some bundle `G`. -/
theorem of_sub_of_eq_of_sub_of_iff {E F E' F' : FiniteRankAtlas 𝕜 X} :
    (SplitK0.of E - SplitK0.of F : TopologicalKZero 𝕜 X) = SplitK0.of E' - SplitK0.of F' ↔
      ∃ G, Nonempty (whitneySum (whitneySum E F') G ≅ whitneySum (whitneySum E' F) G) := by
  have e (A D G : FiniteRankAtlas 𝕜 X) : (A ⊞ D) ⊞ G ≅ whitneySum (whitneySum A D) G :=
    biprodIsoWhitneySum _ G ≪≫ whitneyMapIso (biprodIsoWhitneySum A D) (Iso.refl G)
  rw [SplitK0.of_sub_of_eq_of_sub_of_iff]
  exact exists_congr fun G => ((e E F' G).isoCongr (e E' F G)).nonempty_congr

section Rank

/-- The rank of a bundle, as a locally constant integer-valued function, is an isomorphism
invariant which is additive on Whitney sums. -/
private noncomputable def rankInvariant :
    SplitK0.AdditiveInvariant (FiniteRankAtlas 𝕜 X) (LocallyConstant X ℤ) where
  obj A := A.rank.map (↑)
  map_iso _ _ e := by rw [e.finiteRankAtlas_rank_eq]
  map_biprod A D := by
    ext x
    simp only [rank_biprod, LocallyConstant.map_apply, Function.comp_apply,
      LocallyConstant.coe_add, Pi.add_apply, Nat.cast_add]

variable (𝕜 X) in
/-- The rank homomorphism `K⁰(X) → LocallyConstant X ℤ`, sending the class of a bundle to its
locally constant rank. No bound on the rank is imposed. -/
noncomputable def rankHom : TopologicalKZero 𝕜 X →+ LocallyConstant X ℤ :=
  SplitK0.lift rankInvariant

/-- The rank homomorphism sends the class of a bundle to its rank. -/
@[simp]
theorem rankHom_of (A : FiniteRankAtlas 𝕜 X) :
    rankHom 𝕜 X (SplitK0.of A) = A.rank.map (↑) :=
  SplitK0.lift_of _ A

/-- Pointwise form of `TauCeti.TopologicalKZero.rankHom_of`. -/
theorem rankHom_of_apply (A : FiniteRankAtlas 𝕜 X) (x : X) :
    rankHom 𝕜 X (SplitK0.of A) x = A.rank x := by
  rw [rankHom_of, LocallyConstant.map_apply, Function.comp_apply]

/-- The class of the trivial bundle of a locally constant natural-number rank, as an additive
homomorphism: trivial bundles add their ranks under Whitney sum. -/
private noncomputable def trivialNatHom : LocallyConstant X ℕ →+ TopologicalKZero 𝕜 X where
  toFun r := SplitK0.of (trivial 𝕜 X r)
  map_zero' := SplitK0.of_eq_zero_of_isZero isZero_trivial_zero
  map_add' r s := by rw [← of_whitneySum, SplitK0.of_congr (trivialAddIso r s)]

variable (𝕜 X) in
/-- The splitting of the rank homomorphism by trivial bundles: a locally constant `r` goes to
`[trivial (max r 0)] - [trivial (max (-r) 0)]`, the difference of the trivial bundles of the
positive and negative parts of `r`. -/
noncomputable def trivialHom : LocallyConstant X ℤ →+ TopologicalKZero 𝕜 X where
  toFun r := trivialNatHom (r.map Int.toNat) - trivialNatHom ((-r).map Int.toNat)
  map_zero' := by
    rw [neg_zero, sub_self]
  map_add' r s := by
    rw [sub_add_sub_comm, sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, ← map_add,
      ← map_add]
    congr 1
    ext x
    simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.map_apply,
      Function.comp_apply, LocallyConstant.coe_neg, Pi.neg_apply]
    omega

/-- The defining formula of `TauCeti.TopologicalKZero.trivialHom`. -/
theorem trivialHom_apply (r : LocallyConstant X ℤ) :
    trivialHom 𝕜 X r = SplitK0.of (trivial 𝕜 X (r.map Int.toNat)) -
      SplitK0.of (trivial 𝕜 X ((-r).map Int.toNat)) := (rfl)

/-- On a natural-number rank, `trivialHom` is the class of the trivial bundle of that rank. -/
@[simp]
theorem trivialHom_map_natCast (r : LocallyConstant X ℕ) :
    trivialHom 𝕜 X (r.map (↑)) = SplitK0.of (trivial 𝕜 X r) := by
  have h₁ : (r.map ((↑) : ℕ → ℤ)).map Int.toNat = r := by
    ext x
    simp only [LocallyConstant.map_apply, Function.comp_apply, Int.toNat_natCast]
  have h₂ : (-r.map ((↑) : ℕ → ℤ)).map Int.toNat = 0 := by
    ext x
    simp only [LocallyConstant.map_apply, Function.comp_apply, LocallyConstant.coe_neg,
      Pi.neg_apply, LocallyConstant.coe_zero, Pi.zero_apply]
    omega
  rw [trivialHom_apply, h₁, h₂]
  exact sub_eq_self.2 (SplitK0.of_eq_zero_of_isZero isZero_trivial_zero)

/-- `trivialHom` is a section of the rank homomorphism. -/
@[simp]
theorem rankHom_trivialHom (r : LocallyConstant X ℤ) :
    rankHom 𝕜 X (trivialHom 𝕜 X r) = r := by
  ext x
  rw [trivialHom_apply, map_sub, LocallyConstant.coe_sub, Pi.sub_apply, rankHom_of_apply,
    rankHom_of_apply]
  simp only [rank_trivial, LocallyConstant.map_apply, Function.comp_apply,
    LocallyConstant.coe_neg, Pi.neg_apply]
  omega

/-- The rank homomorphism is surjective onto all locally constant integer-valued functions,
bounded or not. -/
theorem rankHom_surjective : Function.Surjective (rankHom 𝕜 X) :=
  fun r => ⟨trivialHom 𝕜 X r, rankHom_trivialHom r⟩

/-- The splitting of the rank homomorphism by trivial bundles is injective. -/
theorem trivialHom_injective : Function.Injective (trivialHom 𝕜 X) :=
  Function.LeftInverse.injective (g := rankHom 𝕜 X) rankHom_trivialHom

end Rank

section Subsingleton

variable [Subsingleton X]

/-- Over a base with at most one point every bundle is trivial, so `trivialHom` is surjective. -/
theorem trivialHom_surjective : Function.Surjective (trivialHom 𝕜 X) :=
  SplitK0.surjective_of_forall_of_mem_range fun A =>
    ⟨A.rank.map (↑), by rw [trivialHom_map_natCast, SplitK0.of_congr (isoTrivialOfSubsingleton A)]⟩

/-- Over a base with at most one point, a class in `K⁰` is determined by its rank. -/
theorem rankHom_injective : Function.Injective (rankHom 𝕜 X) := by
  intro a b h
  obtain ⟨a, rfl⟩ := trivialHom_surjective (𝕜 := 𝕜) a
  obtain ⟨b, rfl⟩ := trivialHom_surjective (𝕜 := 𝕜) b
  rw [rankHom_trivialHom, rankHom_trivialHom] at h
  rw [h]

variable (𝕜 X) in
/-- Over a base with at most one point, the rank identifies `K⁰` with the locally constant
integer-valued functions. -/
noncomputable def rankAddEquiv : TopologicalKZero 𝕜 X ≃+ LocallyConstant X ℤ :=
  AddEquiv.ofBijective (rankHom 𝕜 X) ⟨rankHom_injective, rankHom_surjective⟩

@[simp]
theorem rankAddEquiv_apply (a : TopologicalKZero 𝕜 X) : rankAddEquiv 𝕜 X a = rankHom 𝕜 X a :=
  (rfl)

@[simp]
theorem rankAddEquiv_symm_apply (r : LocallyConstant X ℤ) :
    (rankAddEquiv 𝕜 X).symm r = trivialHom 𝕜 X r :=
  (rankAddEquiv 𝕜 X).symm_apply_eq.2 (rankHom_trivialHom r).symm

end Subsingleton

/-- Over the empty space every bundle is zero, so `K⁰` is trivial. -/
instance instSubsingletonOfIsEmpty [IsEmpty X] : Subsingleton (TopologicalKZero 𝕜 X) :=
  have : Subsingleton (LocallyConstant X ℤ) := ⟨fun _ _ => LocallyConstant.ext isEmptyElim⟩
  (rankAddEquiv 𝕜 X).toEquiv.subsingleton

section Unique

variable [Unique X]

variable (𝕜 X) in
/-- Over a point, `K⁰` is `ℤ`, by the rank of a bundle. -/
noncomputable def rankAddEquivInt : TopologicalKZero 𝕜 X ≃+ ℤ :=
  (rankAddEquiv 𝕜 X).trans
    { toFun r := r default
      invFun n := LocallyConstant.const X n
      left_inv r := LocallyConstant.ext fun x => by
        rw [Subsingleton.elim x default, LocallyConstant.coe_const, Function.const_apply]
      right_inv _ := (rfl)
      map_add' _ _ := (rfl) }

theorem rankAddEquivInt_apply (a : TopologicalKZero 𝕜 X) :
    rankAddEquivInt 𝕜 X a = rankHom 𝕜 X a default :=
  (rfl)

@[simp]
theorem rankAddEquivInt_of (A : FiniteRankAtlas 𝕜 X) :
    rankAddEquivInt 𝕜 X (SplitK0.of A) = A.rank default := by
  rw [rankAddEquivInt_apply, rankHom_of_apply]

@[simp]
theorem rankAddEquivInt_symm_apply (n : ℤ) :
    (rankAddEquivInt 𝕜 X).symm n = trivialHom 𝕜 X (LocallyConstant.const X n) := by
  rw [AddEquiv.symm_apply_eq, rankAddEquivInt_apply, rankHom_trivialHom,
    LocallyConstant.coe_const, Function.const_apply]

end Unique

end TopologicalKZero

end TauCeti
