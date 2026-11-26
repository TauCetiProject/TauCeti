/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.LocallyConstant
import TauCeti.RingTheory.Idempotents.Prime
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The rank decomposition of a finite projective module

Let `P` be a finitely generated projective module over a commutative ring `R`. Its rank
`Module.rankAtStalk P` is a locally constant function on `Spec R` with finitely many values, but
it need not be constant: over `R = k × k` the module `k × k²` has rank `1` at one point and `2` at
the other. This file splits `P` into pieces of constant rank, characterizes connectedness of
`Spec R` by constancy of ranks, and constructs a finite projective module of any prescribed
locally constant rank.

* **Rank pieces.** For an idempotent `e` and any `R`-module `M`, the piece `e • M` has the rank of
  `M` on the basic open set of `e` and rank `0` elsewhere (`Module.rankAtStalk_smul_top`); in
  particular `R e` has rank the indicator of that set. For each value `n` of the rank of `P`, the
  fibre idempotent `eₙ` of the rank function (`PrimeSpectrum.fiberIdempotent`) cuts out the clopen
  locus where `P` has rank `n`. The piece `eₙ • P` is a direct summand of `P`, hence finite
  projective, of rank `n` there and `0` elsewhere, and `P` is the internal direct sum of these
  pieces.
* **Connectedness.** A nontrivial commutative ring has connected spectrum exactly when every finite
  projective module has constant rank.
* **Clopen gluing.** Every locally constant function `f : Spec R → ℕ` is the rank of a finite
  projective module: `PrimeSpectrum.clopenGlued f` is the product, over the values `n` of `f`, of
  `n` copies of `R eₙ`, a module free of rank one on the fibre `f ⁻¹' {n}` and zero elsewhere. The
  constant function `n` gives `Rⁿ`.

Finite projective modules over a commutative ring are the finitely presented flat ones, which is
the form in which Mathlib states local constancy of the rank
(`Module.isLocallyConstant_rankAtStalk`); the rank pieces are stated in that form. The rank fibres
are clopen but need not be connected; no decomposition of `Spec R` into connected components is
used.

## Main declarations

* `Module.rankAtStalk_smul_top`: the rank of the piece cut out by an idempotent.
* `Module.rankAtStalk_smul_top_fiberIdempotent_rankAtStalk`: the piece of `P` at the rank value
  `n` has rank `n` where `P` has rank `n`, and rank `0` elsewhere.
* `Module.isInternal_smul_top_fiberIdempotent_rankAtStalk`: `P` is the internal direct sum of its
  rank pieces.
* `PrimeSpectrum.connectedSpace_iff_forall_exists_rankAtStalk_eq`: for a nontrivial ring, `Spec R`
  is connected exactly when every finite projective module has constant rank.
* `PrimeSpectrum.clopenGlued`, `PrimeSpectrum.rankAtStalk_clopenGlued`: the clopen-glued module of
  a locally constant function `f` is finite projective of rank `f`;
  `PrimeSpectrum.nonempty_linearEquiv_clopenGlued_const`: for constant `n` it is `Rⁿ`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, the
  discussion of the rank of a projective module, pp. 71–72.
-/

public section

open scoped Pointwise

open PrimeSpectrum

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section Piece

variable {e : R}

open scoped Classical in
/-- **The rank of the piece cut out by an idempotent**: at a prime `p`, the piece `e • M` has the
rank of `M` if `e ∉ p`, that is on the basic open set of `e`, and rank `0` otherwise. -/
theorem rankAtStalk_smul_top (he : IsIdempotentElem e) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) ↥(e • (⊤ : Submodule R M)) p =
      if e ∈ p.asIdeal then 0 else rankAtStalk M p := by
  split_ifs with hp
  · have := he.subsingleton_localizedModule_smul_top (M := M) hp
    exact finrank_zero_of_subsingleton
  -- Otherwise `1 - e ∈ p`, so the complementary piece `(1 - e) • M` vanishes at `p`.
  have := he.one_sub.subsingleton_localizedModule_smul_top (M := M)
    (he.one_sub_mem_iff_notMem.2 hp)
  rw [← congrFun (rankAtStalk_eq_of_equiv (Submodule.prodEquivOfIsCompl _ _
    (he.isCompl_smul_top_one_sub_smul_top (S := R) (M := M)))) p,
    rankAtStalk_prod_of_subsingleton]

end Piece

section RankPiece

variable [Module.FinitePresentation R M] [Module.Flat R M]

open scoped Classical in
/-- **The rank pieces have constant rank on their locus**: the piece of a finitely presented flat
module `M` cut out by the fibre idempotent of its rank at `n` has rank `n` where `M` has rank `n`,
and rank `0` elsewhere. -/
theorem rankAtStalk_smul_top_fiberIdempotent_rankAtStalk (n : ℕ) (p : PrimeSpectrum R) :
    rankAtStalk (R := R)
        ↥(fiberIdempotent (isLocallyConstant_rankAtStalk (R := R) (M := M)) n •
          (⊤ : Submodule R M)) p =
      if rankAtStalk (R := R) M p = n then n else 0 := by
  rw [rankAtStalk_smul_top (isIdempotentElem_fiberIdempotent _ n), fiberIdempotent_mem_iff]
  by_cases h : rankAtStalk (R := R) M p = n <;> simp [h]

/-- **The rank decomposition**: over a finite set `s` of ranks containing every rank of a finitely
presented flat module `M`, `M` is the internal direct sum of its rank pieces, the pieces cut out by
the fibre idempotents of its rank. -/
theorem isInternal_smul_top_fiberIdempotent_rankAtStalk {s : Finset ℕ}
    (hs : Set.range (rankAtStalk (R := R) M) ⊆ s) :
    DirectSum.IsInternal fun n : s ↦
      fiberIdempotent (isLocallyConstant_rankAtStalk (R := R) (M := M)) n • (⊤ : Submodule R M) :=
  isInternal_smul_top_fiberIdempotent _ M hs

end RankPiece

end Module

namespace PrimeSpectrum

universe u

variable {R : Type u} [CommRing R]

/-- **Connectedness of the spectrum through ranks**: the prime spectrum of a nontrivial commutative
ring `R` is connected exactly when every finitely generated projective `R`-module has constant
rank. The modules are quantified in the universe of `R`, which contains the witnesses `R e`, for
idempotents `e`, of the converse. -/
theorem connectedSpace_iff_forall_exists_rankAtStalk_eq [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M],
        ∃ n : ℕ, ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p = n := by
  refine ⟨fun _ M _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · have := Module.finitePresentation_of_projective R M
    exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).exists_eq_const.imp
      fun _ h p ↦ congrFun h p
  refine connectedSpace_iff_clopen.2 ⟨inferInstance, fun s hs ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := isClopen_iff.1 hs
  -- The rank of `R e` is `1` on the basic open set of `e` and `0` off it; it is constant only if
  -- that set is empty or everything.
  have := he.projective_smul_top (S := R) (M := R)
  obtain ⟨n, hn⟩ := h ↥(e • (⊤ : Submodule R R))
  have key (p : PrimeSpectrum R) : p ∈ (basicOpen e : Set (PrimeSpectrum R)) ↔ n = 1 := by
    have := (hn p).symm.trans (Module.rankAtStalk_smul_top he p)
    rw [SetLike.mem_coe, mem_basicOpen]
    split_ifs at this <;> simp_all
  by_cases hn1 : n = 1
  · exact Or.inr (Set.eq_univ_of_forall fun p ↦ (key p).2 hn1)
  · exact Or.inl (Set.eq_empty_of_forall_notMem fun p hp ↦ hn1 ((key p).1 hp))

section ClopenGlued

/-- **The clopen-glued module** of a locally constant function `f : Spec R → ℕ`: the product, over
the finitely many values `n` of `f`, of `n` copies of the principal ideal `R eₙ` of the fibre
idempotent `eₙ` of `f` at `n`. On the fibre `f ⁻¹' {n}` it is free of rank `n`; it is finite
projective (`PrimeSpectrum.projective_clopenGlued`) of rank `f`
(`PrimeSpectrum.rankAtStalk_clopenGlued`). -/
abbrev clopenGlued (f : LocallyConstant (PrimeSpectrum R) ℕ) : Type u :=
  Π n : f.range_finite.toFinset,
    Fin n → ↥(fiberIdempotent f.isLocallyConstant (n : ℕ) • (⊤ : Submodule R R))

variable (f : LocallyConstant (PrimeSpectrum R) ℕ)

/-- The clopen-glued module is projective: each factor `R eₙ` is a direct summand of `R`. It is
finite as a finite product of cyclic modules. -/
instance projective_clopenGlued : Module.Projective R (clopenGlued f) :=
  inferInstance

/-- **Every locally constant rank is realized**: the clopen-glued module of a locally constant
function `f : Spec R → ℕ` has rank `f`. -/
@[simp]
theorem rankAtStalk_clopenGlued : Module.rankAtStalk (R := R) (clopenGlued f) = f := by
  classical
  ext p
  have : Nontrivial R := nonempty_iff_nontrivial.mp ⟨p⟩
  simp_rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype,
    Module.rankAtStalk_smul_top (isIdempotentElem_fiberIdempotent _ _), Module.rankAtStalk_self,
    Pi.one_apply, fiberIdempotent_mem_iff]
  have hp : f p ∈ f.range_finite.toFinset := by simp
  rw [Finset.sum_eq_single_of_mem ⟨f p, hp⟩ (Finset.mem_univ _) fun n _ hn ↦ by
    simp [Ne.symm (Subtype.coe_injective.ne hn)]]
  simp

/-- **A constant rank glues to a free module**: the clopen-glued module of the constant function
`n` is isomorphic to `Rⁿ`. -/
theorem nonempty_linearEquiv_clopenGlued_const (n : ℕ) :
    Nonempty (clopenGlued (.const (PrimeSpectrum R) n) ≃ₗ[R] (Fin n → R)) := by
  cases subsingleton_or_nontrivial R
  · exact ⟨.ofSubsingleton _ _⟩
  -- The only value is `n`, and its fibre idempotent is `1`.
  have hval (m : (LocallyConstant.const (PrimeSpectrum R) n).range_finite.toFinset) :
      (m : ℕ) = n := by
    obtain ⟨p, hp⟩ := (Set.Finite.mem_toFinset _).mp m.property
    simpa using hp.symm
  have : Unique ((LocallyConstant.const (PrimeSpectrum R) n).range_finite.toFinset) :=
    { default := ⟨n, by simp⟩
      uniq := fun m ↦ Subtype.ext (hval m) }
  have h1 : fiberIdempotent (LocallyConstant.const (PrimeSpectrum R) n).isLocallyConstant
      ((default : (LocallyConstant.const (PrimeSpectrum R) n).range_finite.toFinset) : ℕ) = 1 :=
    (fiberIdempotent_eq_one_iff _).2 fun _ ↦ (hval default).symm
  exact ⟨LinearEquiv.piUnique R _ ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ ↦ LinearEquiv.ofEq _ _ (by rw [h1, one_smul]) ≪≫ₗ
      Submodule.topEquiv) ≪≫ₗ LinearEquiv.funCongrLeft R R (finCongr (hval default)).symm⟩

end ClopenGlued

end PrimeSpectrum
