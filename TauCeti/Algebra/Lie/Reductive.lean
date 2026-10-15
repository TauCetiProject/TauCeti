/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
-- `TauCeti.Algebra.Lie.Solvable.Basic` is imported publicly because it supplies
-- `LieAlgebra.HasTrivialRadical`, which is a hypothesis of the reductivity criterion below, and
-- `LieIdeal.eq_bot_of_le_of_isSolvable`, which proves it.
public import TauCeti.Algebra.Lie.Solvable.Basic
public import TauCeti.Algebra.Lie.Weights.Central
-- `TauCeti.Algebra.Lie.LeviDecomposition.Abelian` supplies Weyl's theorem in the form used for the
-- structure theorem: a central ideal with Killing quotient has a complementary ideal. Through it
-- comes `LieIdeal.quotientEquivOfIsCompl`, which identifies the derived ideal with `L ⧸ Z(L)`.
public import TauCeti.Algebra.Lie.LeviDecomposition.Abelian
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Reductive Lie algebras: the structure theorem

A finite-dimensional Lie algebra `L` over a field of characteristic zero is **reductive** when its
solvable radical is its centre, Mathlib's `LieAlgebra.HasCentralRadical`. This file proves that a
reductive Lie algebra is spanned by its centre and its derived ideal,

`center K L ⊔ ⁅L, L⁆ = ⊤`  (`TauCeti.sup_center_derivedSeries_eq_top`),

and draws the consequences the representation theory of a reductive Lie algebra runs on: the
derived ideal is perfect, equivariance of a linear map may be tested on the centre and on the
derived ideal, and a finite-dimensional irreducible module over `L` stays irreducible over the
derived ideal (`TauCeti.isIrreducible_restrict_derivedSeries`).

It also proves the converse criterion. If the derived ideal `⁅L, L⁆` has **no nonzero solvable
ideals** (`LieAlgebra.HasTrivialRadical`, which a semisimple Lie algebra has) then `L` is
reductive (`TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries`) and every solvable
ideal, the centre among them, meets `⁅L, L⁆` only in `⊥`
(`TauCeti.inf_derivedSeries_eq_bot_of_isSolvable`). That much is elementary and much cheaper than
the spanning half: it holds over any commutative ring and needs no Killing form, no
characteristic-zero hypothesis, no finite dimension and no Noetherian hypothesis.

Over a field of characteristic zero and in finite dimension, where the spanning half is available,
the two combine into a direct sum

`L = Z(L) ⊕ ⁅L, L⁆`

(`TauCeti.isCompl_center_derivedSeries_of_hasTrivialRadical_derivedSeries`), which therefore
carries those hypotheses even though the criterion itself does not.

Conversely, a reductive Lie algebra is that direct sum, and its derived ideal is semisimple
(`TauCeti.isCompl_center_derivedSeries` and `TauCeti.isKilling_derivedSeries`). Together with the
criterion this is the **structure theorem for reductive Lie algebras**
(`TauCeti.hasCentralRadical_iff_isCompl_center_derivedSeries`): in characteristic zero and finite
dimension, `L` is reductive exactly when `L = Z(L) ⊕ ⁅L, L⁆` with `⁅L, L⁆` semisimple.

## The argument for the criterion

For a solvable ideal `J` the bracket `⁅L, J⁆` lies in `J`, because that is an ideal, and in
`⁅L, L⁆`, because every bracket does. The intersection `J ⊓ ⁅L, L⁆` is a solvable ideal of `L`
inside `⁅L, L⁆`, hence — read as an ideal of the Lie algebra `⁅L, L⁆` through `LieIdeal.restrict`
of `TauCeti/Algebra/Lie/Solvable.lean` — a solvable ideal of an algebra with trivial radical, so
it vanishes. An element of `J` therefore brackets to zero against everything: it is central. The
radical is the supremum of the solvable ideals, so it is central too — that is reductivity, and no
finiteness hypothesis is needed because the radical itself never has to be solvable. The centre is
one of those solvable ideals, so it meets `⁅L, L⁆` trivially, which is directness of the sum.

## The argument for the spanning half

Everything comes from the Killing form `κ` and its orthogonal complements
(`LieIdeal.killingCompl`). Cartan's criterion, in the form
`LieAlgebra.killingCompl_top_le_radical`, says that the radical of `κ` is contained in the solvable
radical; for a reductive `L` that radical is the centre, and the reverse inclusion is immediate
because a central element has vanishing adjoint action. So the radical of `κ` is the centre
(`TauCeti.killingCompl_top_eq_center`).

The derived ideal has the *same* orthogonal complement
(`TauCeti.killingCompl_derivedSeries_eq_center`). Indeed the invariance `κ ⁅x, y⁆ z = κ x ⁅y, z⁆`
turns "`x` is orthogonal to every bracket" into "`⁅y, x⁆` is orthogonal to everything", that is
into `⁅y, x⁆ ∈ center K L` for every `y`. The elements with that property are the normalizer of the
centre, an ideal whose derived ideal is central and therefore abelian: it is a solvable ideal, so
reductivity puts it back inside the centre. This is `TauCeti.normalizer_center_eq_center`.

Two subspaces of a finite-dimensional space with the same orthogonal complement for a symmetric
form need not be equal — but they are if both contain the radical of the form, and the dimension
formula `LinearMap.BilinForm.finrank_add_finrank_orthogonal` makes that precise. Applied to
`center K L ⊔ ⁅L, L⁆`, whose orthogonal complement is the centre by the two computations above and
which contains the centre for trivial reasons, it forces that ideal to be everything.

## The argument for the direct sum

The centre is the solvable radical, so `L ⧸ Z(L)` has trivial radical and is Killing by Cartan's
criterion (`TauCeti.isKilling_quotient_center`). Weyl's theorem for the adjoint action of
`L ⧸ Z(L)` then complements the centre by an ideal `J` (`LieIdeal.exists_isCompl_of_le_center`).
A bracket `⁅x, z + j⁆` with `z` central and `j ∈ J` equals `⁅x, j⁆ ∈ J`, so `⁅L, L⁆ ≤ J` and the
derived ideal meets the centre trivially. This is the one place where complete reducibility enters;
the elementary Killing-form argument above gives only the span. Being a complement of the centre,
the derived ideal is isomorphic to `L ⧸ Z(L)`, hence Killing and semisimple.

## Main results

* `TauCeti.normalizer_center_eq_center`: over a reductive Lie algebra the centre is its own
  normalizer, because the normalizer is a solvable ideal
  (`TauCeti.isSolvable_normalizer_center`).
* `TauCeti.killingCompl_top_eq_center` and `TauCeti.killingCompl_derivedSeries_eq_center`: the
  radical of the Killing form and the orthogonal complement of the derived ideal are both the
  centre.
* `TauCeti.sup_center_derivedSeries_eq_top`: **the centre and the derived ideal span**,
  `center K L ⊔ ⁅L, L⁆ = ⊤`, with `TauCeti.exists_mem_center_add_mem_derivedSeries` its
  elementwise form.
* `TauCeti.lie_derivedSeries_derivedSeries_eq_self`: **the derived ideal is perfect.**
* `TauCeti.map_lie_of_forall_center_of_forall_derivedSeries` and
  `TauCeti.lieModuleEquivOfCenterOfDerivedSeries`: a linear map equivariant for the centre and for
  the derived ideal is equivariant for `L`, so a derived-ideal equivalence between modules on which
  the centre acts by the same scalars is an `L`-equivalence.
* `TauCeti.isIrreducible_restrict_derivedSeries`: **a finite-dimensional irreducible module over a
  reductive Lie algebra restricts to an irreducible module over the derived ideal**, over an
  algebraically closed field.
* `TauCeti.inf_derivedSeries_eq_bot_of_isSolvable` and `TauCeti.le_center_of_isSolvable`: when
  the derived ideal has trivial radical, **every solvable ideal is central**, meeting the derived
  ideal only in `⊥`.
* `TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries`: **a Lie algebra whose derived
  ideal has trivial radical is reductive**, with
  `TauCeti.radical_le_center_of_hasTrivialRadical_derivedSeries` the inclusion it rests on.
* `TauCeti.isCompl_center_derivedSeries_of_hasTrivialRadical_derivedSeries`: **such a Lie algebra
  is the direct sum of its centre and its derived ideal**, over a field of characteristic zero and
  in finite dimension.
* `TauCeti.center_inf_derivedSeries_eq_bot` and `TauCeti.isCompl_center_derivedSeries`: **a
  reductive Lie algebra is the direct sum of its centre and its derived ideal.**
* `TauCeti.isKilling_quotient_center` and `TauCeti.isKilling_derivedSeries`: the quotient by the
  centre and the derived ideal of a reductive Lie algebra are Killing, hence semisimple.
* `TauCeti.hasCentralRadical_iff_isCompl_center_derivedSeries`: **the structure theorem**, `L` is
  reductive if and only if `L = Z(L) ⊕ ⁅L, L⁆` with `⁅L, L⁆` semisimple.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6.4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5 and §6.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w'

/-! ### The centre is its own normalizer -/

section Normalizer

variable (K : Type u) (L : Type v) [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The elements `x` for which `⁅y, x⁆` is central for every `y` — that is, the normalizer of the
centre — form a **solvable** ideal: its derived ideal is central, hence abelian. -/
theorem isSolvable_normalizer_center :
    LieAlgebra.IsSolvable ((LieAlgebra.center K L).normalizer) := by
  have hle : ⁅(LieAlgebra.center K L).normalizer, (LieAlgebra.center K L).normalizer⁆ ≤
      LieAlgebra.center K L :=
    (LieSubmodule.lie_le_iff _ _ _).2 fun x _ y hy ↦
      (LieSubmodule.mem_normalizer _ y).1 hy x
  have hcentral : ⁅LieAlgebra.center K L, LieAlgebra.center K L⁆ = (⊥ : LieIdeal K L) :=
    le_bot_iff.1 <| (LieSubmodule.lie_le_iff _ _ _).2 fun x hx y _ ↦ by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L x).1 hx y, neg_zero]
      exact LieSubmodule.zero_mem _
  refine LieAlgebra.IsSolvable.mk (R := K) (k := 2)
    ((LieIdeal.derivedSeries_eq_bot_iff _ 2).2 ?_)
  rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    ← le_bot_iff, ← hcentral]
  exact LieSubmodule.mono_lie hle hle

variable [IsNoetherian K L] [LieAlgebra.HasCentralRadical K L]

/-- **Over a reductive Lie algebra the centre is its own normalizer.** The normalizer is a solvable
ideal by `TauCeti.isSolvable_normalizer_center`, hence lies in the radical, which is the centre. -/
theorem normalizer_center_eq_center :
    (LieAlgebra.center K L).normalizer = LieAlgebra.center K L := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  have h := (LieIdeal.solvable_iff_le_radical K L (LieAlgebra.center K L).normalizer).1
    (isSolvable_normalizer_center K L)
  rwa [LieAlgebra.radical_eq_center] at h

/-- A convenient elementwise form of `TauCeti.normalizer_center_eq_center`: over a reductive Lie
algebra, if every bracket `⁅y, x⁆` is central, then `x` itself is central. -/
theorem mem_center_of_forall_lie_mem_center {x : L}
    (h : ∀ y : L, ⁅y, x⁆ ∈ LieAlgebra.center K L) : x ∈ LieAlgebra.center K L :=
  normalizer_center_eq_center K L ▸ (LieSubmodule.mem_normalizer _ x).2 h

end Normalizer

/-! ### The Killing form sees only the centre -/

section KillingCompl

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]

/-- **For a reductive Lie algebra the radical of the Killing form is the centre.** One inclusion is
Cartan's criterion `LieAlgebra.killingCompl_top_le_radical` together with reductivity; the other
holds because a central element acts by zero. -/
theorem killingCompl_top_eq_center :
    LieIdeal.killingCompl K L ⊤ = LieAlgebra.center K L := by
  refine le_antisymm ?_ fun z hz ↦ ?_
  · simpa [LieAlgebra.radical_eq_center] using LieAlgebra.killingCompl_top_le_radical K L
  · refine (LieIdeal.mem_killingCompl K L ⊤).2 fun y _ ↦ ?_
    have hz' : LieAlgebra.ad K L z = 0 := by
      ext w
      rw [LieAlgebra.ad_apply, ← lie_skew, (LieModule.mem_maxTrivSubmodule K L L z).1 hz w]
      simp
    rw [LieModule.traceForm_comm, killingForm_apply_apply, hz']
    simp

variable {K L}

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L] in
/-- An element orthogonal to the derived ideal brackets into the radical of the Killing form: this
is the invariance `κ ⁅x, y⁆ z = κ x ⁅y, z⁆` read from right to left. -/
theorem lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries {x : L}
    (hx : x ∈ LieIdeal.killingCompl K L (derivedSeries K L 1)) (y : L) :
    ⁅y, x⁆ ∈ LieIdeal.killingCompl K L ⊤ := by
  refine (LieIdeal.mem_killingCompl K L ⊤).2 fun z _ ↦ ?_
  have hyz : ⁅z, y⁆ ∈ derivedSeries K L 1 :=
    LieSubmodule.lie_mem_lie (LieSubmodule.mem_top z) (LieSubmodule.mem_top y)
  have hinv := LieModule.traceForm_apply_lie_apply K L L z y x
  rw [← hinv]
  exact (LieIdeal.mem_killingCompl K L _).1 hx _ hyz

variable (K L)

/-- **The derived ideal of a reductive Lie algebra has the centre as its orthogonal complement.**
Nothing beyond the radical of the Killing form is orthogonal to the derived ideal: an element
orthogonal to it normalizes the centre by
`TauCeti.lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries`, hence is central. -/
theorem killingCompl_derivedSeries_eq_center :
    LieIdeal.killingCompl K L (derivedSeries K L 1) = LieAlgebra.center K L := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · refine mem_center_of_forall_lie_mem_center K L fun y ↦ ?_
    rw [← killingCompl_top_eq_center K L]
    exact lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries hx y
  · rw [← killingCompl_top_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y _ ↦
      (LieIdeal.mem_killingCompl K L ⊤).1 hx y (LieSubmodule.mem_top y)

/-- The orthogonal complement of the centre together with the derived ideal is again the centre:
it is squeezed between the complements of the derived ideal and of the whole algebra, which
`TauCeti.killingCompl_derivedSeries_eq_center` and `TauCeti.killingCompl_top_eq_center` identify
with one another. -/
theorem killingCompl_sup_center_derivedSeries_eq_center :
    LieIdeal.killingCompl K L (LieAlgebra.center K L ⊔ derivedSeries K L 1)
      = LieAlgebra.center K L := by
  refine le_antisymm ?_ ?_
  · rw [← killingCompl_derivedSeries_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y hy ↦
      (LieIdeal.mem_killingCompl K L _).1 hx y (le_sup_right (α := LieIdeal K L) hy)
  · rw [← killingCompl_top_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y _ ↦
      (LieIdeal.mem_killingCompl K L ⊤).1 hx y (LieSubmodule.mem_top y)

end KillingCompl

/-! ### The centre and the derived ideal span -/

section Span

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]

/-- **The centre and the derived ideal of a reductive Lie algebra span it**: `L = Z(L) + ⁅L, L⁆`.

The ideal `center K L ⊔ ⁅L, L⁆` and the whole algebra have the same orthogonal complement for the
Killing form, namely the centre, and both contain the radical of that form. The dimension formula
`LinearMap.BilinForm.finrank_add_finrank_orthogonal` then equates their dimensions. -/
theorem sup_center_derivedSeries_eq_top :
    LieAlgebra.center K L ⊔ derivedSeries K L 1 = (⊤ : LieIdeal K L) := by
  have hrefl : (killingForm K L).IsRefl := (LieModule.traceForm_isSymm K L L).isRefl
  set Z : Submodule K L := LieSubmodule.toSubmodule (LieAlgebra.center K L) with hZ
  set U : Submodule K L :=
    LieSubmodule.toSubmodule (LieAlgebra.center K L ⊔ derivedSeries K L 1) with hU
  have hZU : Z ≤ U := by
    rw [hZ, hU, LieSubmodule.sup_toSubmodule]
    exact le_sup_left
  have hortho : (killingForm K L).orthogonal U = Z := by
    rw [hU, hZ, ← LieIdeal.toSubmodule_killingCompl,
      killingCompl_sup_center_derivedSeries_eq_center K L]
  have htop : (killingForm K L).orthogonal ⊤ = Z := by
    rw [hZ, ← LieSubmodule.top_toSubmodule (R := K) (L := L) (M := L),
      ← LieIdeal.toSubmodule_killingCompl, killingCompl_top_eq_center K L]
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (B := killingForm K L) hrefl U
  rw [hortho, htop, inf_eq_right.2 hZU] at hdim
  rw [← LieSubmodule.toSubmodule_eq_top, ← hU]
  exact Submodule.eq_top_of_finrank_eq (by omega)

/-- Every element of a reductive Lie algebra is a central element plus an element of the derived
ideal. -/
theorem exists_mem_center_add_mem_derivedSeries (x : L) :
    ∃ z ∈ LieAlgebra.center K L, ∃ d ∈ derivedSeries K L 1, z + d = x := by
  have hx : x ∈ (LieAlgebra.center K L ⊔ derivedSeries K L 1 : LieIdeal K L) := by
    rw [sup_center_derivedSeries_eq_top K L]
    exact LieSubmodule.mem_top x
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule] at hx
  exact Submodule.mem_sup.1 hx

/-- **The derived ideal of a reductive Lie algebra is perfect**: `⁅⁅L, L⁆, ⁅L, L⁆⁆ = ⁅L, L⁆`. A
central element contributes nothing to a bracket, so writing both arguments of a generating bracket
of `⁅L, L⁆` as a central element plus an element of `⁅L, L⁆` leaves only the brackets of the derived
ideal with itself. -/
theorem lie_derivedSeries_derivedSeries_eq_self :
    ⁅derivedSeries K L 1, derivedSeries K L 1⁆ = derivedSeries K L 1 := by
  refine le_antisymm (LieSubmodule.lie_le_right _ _) ?_
  have hDtop : derivedSeries K L 1 = ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := rfl
  rw [hDtop]
  refine (LieSubmodule.lie_le_iff _ _ _).2 fun y _ z _ ↦ ?_
  obtain ⟨zy, hzy, dy, hdy, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L y
  obtain ⟨zz, hzz, dz, hdz, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L z
  have hzy0 : ∀ w : L, ⁅zy, w⁆ = 0 := fun w ↦ by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L zy).1 hzy w, neg_zero]
  have hzz0 : ∀ w : L, ⁅w, zz⁆ = 0 := (LieModule.mem_maxTrivSubmodule K L L zz).1 hzz
  rw [add_lie, hzy0, lie_add, hzz0, zero_add, zero_add]
  exact LieSubmodule.lie_mem_lie hdy hdz

end Span

/-! ### Triviality of the radical of the derived ideal is a criterion for reductivity -/

section Criterion

variable (K : Type u) (L : Type v) [CommRing K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.HasTrivialRadical K (derivedSeries K L 1)]

/-- **A solvable ideal meets the derived ideal trivially** when the derived ideal has no nonzero
solvable ideals. The intersection is a solvable ideal of `L` lying inside `⁅L, L⁆`, so it is an
ideal of `⁅L, L⁆` (`LieIdeal.restrict`) that `LieAlgebra.HasTrivialRadical` kills.

The derived ideal is spelled `⁅⊤, ⊤⁆` rather than `derivedSeries K L 1` so that the left-hand
side is in simp-normal form; the two are definitionally equal. -/
@[simp]
theorem inf_derivedSeries_eq_bot_of_isSolvable (J : LieIdeal K L) [LieAlgebra.IsSolvable ↥J] :
    J ⊓ ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = ⊥ := by
  -- Instance synthesis does not unfold `⁅⊤, ⊤⁆` to `derivedSeries K L 1`, so the section's
  -- `LieAlgebra.HasTrivialRadical K (derivedSeries K L 1)` is invisible to the goal as stated;
  -- converting to that spelling first is what lets the two steps below find it.
  change J ⊓ derivedSeries K L 1 = ⊥
  have : LieAlgebra.IsSolvable ↥(J ⊓ derivedSeries K L 1) :=
    LieAlgebra.le_solvable_ideal_solvable inf_le_left inferInstance
  exact LieIdeal.eq_bot_of_le_of_isSolvable inf_le_right

/-- **Every solvable ideal is central** when the derived ideal has no nonzero solvable ideals.

The bracket `⁅L, J⁆` lands in `J`, because that is an ideal, and in `⁅L, L⁆`, because every
bracket does; so it lands in their intersection, which is `⊥` by
`TauCeti.inf_derivedSeries_eq_bot_of_isSolvable`. An element of `J` therefore has vanishing
bracket with everything, which is membership in the centre. -/
theorem le_center_of_isSolvable (J : LieIdeal K L) [LieAlgebra.IsSolvable ↥J] :
    J ≤ LieAlgebra.center K L := by
  have hle : ⁅(⊤ : LieIdeal K L), J⁆ ≤ ⊥ := by
    rw [← inf_derivedSeries_eq_bot_of_isSolvable K L J]
    exact le_inf (LieSubmodule.lie_le_right _ _) (LieSubmodule.mono_lie le_rfl le_top)
  intro x hx
  refine (LieModule.mem_maxTrivSubmodule K L L x).2 fun y => ?_
  have hxy : ⁅y, x⁆ ∈ (⊥ : LieIdeal K L) :=
    hle (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) hx)
  rwa [LieSubmodule.mem_bot] at hxy

/-- **The radical of a Lie algebra whose derived ideal has trivial radical is central.**

The radical is the supremum of the solvable ideals, and `TauCeti.le_center_of_isSolvable` puts
each of them inside the centre.  Passing through the supremum this way avoids any finiteness
hypothesis: the radical itself never has to be solvable. -/
theorem radical_le_center_of_hasTrivialRadical_derivedSeries :
    LieAlgebra.radical K L ≤ LieAlgebra.center K L :=
  sSup_le fun J hJ => @le_center_of_isSolvable K L _ _ _ _ J hJ

/-- **A Lie algebra whose derived ideal has trivial radical is reductive.**

This is the converse direction of the structure theorem for reductive Lie algebras, and it needs
no field of characteristic zero, no finite dimension and no Noetherian hypothesis. Nor does it
need the centre and the derived ideal to be complementary: triviality of the radical of `⁅L, L⁆`
alone forces `radical K L = center K L`. Complementarity is a further consequence, but only over
a field of characteristic zero and in finite dimension, where the spanning half
`TauCeti.sup_center_derivedSeries_eq_top` is available
(`TauCeti.isCompl_center_derivedSeries_of_hasTrivialRadical_derivedSeries`). -/
theorem hasCentralRadical_of_hasTrivialRadical_derivedSeries :
    LieAlgebra.HasCentralRadical K L :=
  LieAlgebra.hasCentralRadical_of_radical_le K L
    (radical_le_center_of_hasTrivialRadical_derivedSeries K L)

end Criterion

section Complement

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K (derivedSeries K L 1)]

/-- **A Lie algebra whose derived ideal has trivial radical is the direct sum of its centre and
that ideal**: `L = Z(L) ⊕ ⁅L, L⁆`, over a field of characteristic zero and in finite dimension.

Reductivity comes from `TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries`, which needs
neither hypothesis; the sum comes from `TauCeti.sup_center_derivedSeries_eq_top`, which is where
both of them are spent; and the directness comes from
`TauCeti.inf_derivedSeries_eq_bot_of_isSolvable` applied to the centre, which is abelian and
therefore a solvable ideal. -/
theorem isCompl_center_derivedSeries_of_hasTrivialRadical_derivedSeries :
    IsCompl (LieAlgebra.center K L) (derivedSeries K L 1) := by
  have := hasCentralRadical_of_hasTrivialRadical_derivedSeries K L
  exact ⟨disjoint_iff.mpr (inf_derivedSeries_eq_bot_of_isSolvable K L _),
    codisjoint_iff.mpr (sup_center_derivedSeries_eq_top K L)⟩

end Complement

/-! ### The structure theorem -/

section Structure

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L]

section Reductive

variable [LieAlgebra.HasCentralRadical K L]

variable {K L} in
/-- **The quotient of a reductive Lie algebra by its centre has nondegenerate Killing form.** The
centre is the solvable radical, the quotient by the radical has trivial radical
(`LieAlgebra.hasTrivialRadical_quotient_radical`), and Cartan's criterion
`LieAlgebra.HasTrivialRadical.instIsKilling` makes it Killing. -/
instance isKilling_quotient_center : LieAlgebra.IsKilling K (L ⧸ LieAlgebra.center K L) := by
  rw [← LieAlgebra.radical_eq_center]
  infer_instance

/-- **The centre of a reductive Lie algebra meets its derived ideal trivially.**

Weyl's theorem complements the centre by an ideal `J` (`LieIdeal.exists_isCompl_of_le_center`,
which applies because `L ⧸ Z(L)` is Killing). A bracket `⁅x, z + j⁆` with `z` central and `j ∈ J`
is `⁅x, j⁆ ∈ J`, so the derived ideal lies in `J`, which meets the centre only in `⊥`. -/
theorem center_inf_derivedSeries_eq_bot :
    LieAlgebra.center K L ⊓ derivedSeries K L 1 = ⊥ := by
  obtain ⟨J, hJ⟩ := (LieAlgebra.center K L).exists_isCompl_of_le_center le_rfl
  have hD : derivedSeries K L 1 ≤ J := by
    refine (LieSubmodule.lie_le_iff _ _ _).2 fun x _ y _ ↦ ?_
    have hy : y ∈ (LieAlgebra.center K L ⊔ J : LieIdeal K L) :=
      hJ.sup_eq_top ▸ LieSubmodule.mem_top y
    obtain ⟨z, hz, j, hj, rfl⟩ := (LieSubmodule.mem_sup _ _ _).1 hy
    rw [lie_add, (LieModule.mem_maxTrivSubmodule K L L z).1 hz x, zero_add]
    exact J.lie_mem hj
  exact le_bot_iff.1 ((inf_le_inf_left _ hD).trans hJ.inf_eq_bot.le)

/-- **A reductive Lie algebra is the direct sum of its centre and its derived ideal**:
`L = Z(L) ⊕ ⁅L, L⁆`. The two span by `TauCeti.sup_center_derivedSeries_eq_top` and meet trivially
by `TauCeti.center_inf_derivedSeries_eq_bot`. -/
theorem isCompl_center_derivedSeries :
    IsCompl (LieAlgebra.center K L) (derivedSeries K L 1) :=
  ⟨disjoint_iff.2 (center_inf_derivedSeries_eq_bot K L),
    codisjoint_iff.2 (sup_center_derivedSeries_eq_top K L)⟩

variable {K L} in
/-- **The derived ideal of a reductive Lie algebra has nondegenerate Killing form**, and is
therefore semisimple (`LieAlgebra.IsKilling.instSemisimple`). Being a complement of the centre, it
is isomorphic to `L ⧸ Z(L)` (`LieIdeal.quotientEquivOfIsCompl`), which is Killing by
`TauCeti.isKilling_quotient_center`. -/
instance isKilling_derivedSeries : LieAlgebra.IsKilling K (derivedSeries K L 1) :=
  LieAlgebra.isKilling_of_equiv <|
    (LieAlgebra.center K L).quotientEquivOfIsCompl (derivedSeries K L 1).toLieSubalgebra <| by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.isCompl_toSubmodule]
      exact isCompl_center_derivedSeries K L

end Reductive

/-- **The structure theorem for reductive Lie algebras.** Over a field of characteristic zero, a
finite-dimensional Lie algebra is reductive (its solvable radical is its centre) if and only if it
is the direct sum of its centre and its derived ideal, with the derived ideal semisimple.

Both conjuncts are needed for the reverse implication to be a characterization of the right
class: the semidirect product `sl₂ ⋉ K²` with the standard module has trivial centre and is its
own derived ideal, so it satisfies the first conjunct without being reductive. The reverse
implication itself only uses the second conjunct, through
`TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries`. -/
theorem hasCentralRadical_iff_isCompl_center_derivedSeries :
    LieAlgebra.HasCentralRadical K L ↔
      IsCompl (LieAlgebra.center K L) (derivedSeries K L 1) ∧
        LieAlgebra.IsSemisimple K (derivedSeries K L 1) :=
  ⟨fun _ ↦ ⟨isCompl_center_derivedSeries K L, inferInstance⟩,
    fun ⟨_, _⟩ ↦ hasCentralRadical_of_hasTrivialRadical_derivedSeries K L⟩

end Structure

/-! ### Modules over a reductive Lie algebra -/

section Modules

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {N : Type w'} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

omit [LieModule K L M] [LieModule K L N] in
/-- **Equivariance is tested on the centre and on the derived ideal.** A linear map between
`L`-modules commuting with the action of every central element and of every element of `⁅L, L⁆`
commutes with the action of `L`, because those two ideals span
(`TauCeti.sup_center_derivedSeries_eq_top`). -/
theorem map_lie_of_forall_center_of_forall_derivedSeries (f : M →ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, f ⁅z, m⁆ = ⁅z, f m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, f ⁅d, m⁆ = ⁅d, f m⁆) (x : L) (m : M) :
    f ⁅x, m⁆ = ⁅x, f m⁆ := by
  obtain ⟨z, hz, d, hd, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L x
  rw [add_lie, map_add, hZ z hz, hD d hd, add_lie]

/-- A linear equivalence which is equivariant for the derived ideal and for the centre is an
equivalence of `L`-modules. This is the dictionary through which the representation theory of the
derived ideal — the semisimple part — reaches `L`: the centre contributes only the scalars recorded
by `TauCeti.centralWeight`. -/
def lieModuleEquivOfCenterOfDerivedSeries (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) :
    M ≃ₗ⁅K, L⁆ N where
  __ := e
  map_lie' {x m} :=
    map_lie_of_forall_center_of_forall_derivedSeries K L (e : M →ₗ[K] N) hZ hD x m

omit [LieModule K L M] [LieModule K L N] in
@[simp]
theorem lieModuleEquivOfCenterOfDerivedSeries_apply (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) (m : M) :
    lieModuleEquivOfCenterOfDerivedSeries K L e hZ hD m = e m :=
  (rfl)

omit [LieModule K L M] [LieModule K L N] in
@[simp]
theorem lieModuleEquivOfCenterOfDerivedSeries_symm_apply (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) (n : N) :
    (lieModuleEquivOfCenterOfDerivedSeries K L e hZ hD).symm n = e.symm n :=
  (rfl)

variable (M) [IsAlgClosed K] [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

/-- **The semisimple part acts irreducibly.** A finite-dimensional irreducible module over a
reductive Lie algebra, over an algebraically closed field, restricts to an irreducible module over
the derived ideal.

The centre acts by scalars (`TauCeti.exists_centralWeight_of_isIrreducible`), so every subspace of
`M` is stable under it; since the centre and the derived ideal span, a submodule for the derived
ideal is already a submodule for `L`. Algebraic closedness is essential and not a convenience: over
`ℝ` the one-dimensional abelian Lie algebra acting on `ℝ²` by the rotation generator is
irreducible, is its own centre, and has zero derived ideal.

Together with the central weight, this shows that every finite-dimensional irreducible determines
an irreducible restricted module and a functional on the centre; reconstruction and uniqueness are
not asserted here. -/
theorem isIrreducible_restrict_derivedSeries :
    LieModule.IsIrreducible K (derivedSeries K L 1) M :=
  isIrreducible_of_sup_center_eq_top K L M (derivedSeries K L 1) <| by
    have h := congrArg LieSubmodule.toSubmodule (sup_center_derivedSeries_eq_top K L)
    rw [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule] at h
    rw [← h, sup_comm]
    rfl

end Modules

end TauCeti
