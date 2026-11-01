/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Unfold
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Periodic projective resolutions

Let `Q` be a `ZMod n`-indexed complex and `j` an integer. Unfolding `Q` along the integers and
keeping the degrees at most `j` gives the chain complex

`⋯ ⟶ Q^(j-2) ⟶ Q^(j-1) ⟶ Q^j`

with `Q^j` in homological degree `0` (`TauCeti.PeriodicComplex.resolutionComplex`). Its terms
and differentials repeat with period `n`. It only depends on the residue of `j` modulo `n`
(`TauCeti.PeriodicComplex.resolutionComplexIsoOfEq`), and dropping its first `m` terms with
Mathlib's `ChainComplex.truncate` gives the complex attached to `j - m`
(`TauCeti.PeriodicComplex.truncateIterateResolutionComplexIso`). In particular, dropping the
first `n` terms gives back the same complex
(`TauCeti.PeriodicComplex.resolutionComplexPeriodIso`).

Let `i + 1 = i'` be consecutive residues, with `i'` the residue of `j`. If `Q` is acyclic with
projective terms and `ε : Q^i' ⟶ M` is a cokernel of the differential `Q^i ⟶ Q^i'`, this
complex is a projective resolution of `M` (`TauCeti.PeriodicComplex.projectiveResolution`): a
periodic projective resolution with period `n` and empty preperiod. For example, the reduction
of a matrix factorization modulo a non-zero-divisor potential is a two-periodic projective
resolution of its cokernel (Eisenbud, Section 5).

## Main definitions

* `TauCeti.PeriodicComplex.resolutionComplex`: the unfolded complex in degrees at most `j`,
  indexed homologically by `ℕ`.
* `TauCeti.PeriodicComplex.projectiveResolution`: the projective resolution of a cokernel of
  `Q^i ⟶ Q^i'`, for an acyclic periodic complex of projectives `Q`.
* `ChainComplex.HasPeriodicTail`: a chain complex has a periodic tail of period `n` after a
  preperiod of `p` terms.

## Main results

* `TauCeti.PeriodicComplex.resolutionComplex_d`: the differential into degree `k` is the cyclic
  differential `Q^(j-k-1) ⟶ Q^(j-k)`.
* `TauCeti.PeriodicComplex.truncateIterateResolutionComplexIso`: dropping `m` terms shifts `j`
  down by `m`.
* `TauCeti.PeriodicComplex.resolutionComplexPeriodIso`: the complex is periodic of period `n`.
* `TauCeti.PeriodicComplex.projectiveResolution_π_f_zero`: the augmentation is `ε`.
* `ChainComplex.HasPeriodicTail.mono`, `ChainComplex.HasPeriodicTail.of_iso`: a periodic tail
  persists after longer preperiods and along isomorphisms.
* `ChainComplex.HasPeriodicTail.nonempty_truncate_iterate_iso`: after its preperiod, a complex
  with a periodic tail repeats itself.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), Sections 3.1–3.2.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] {n : ℕ}

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- The chain complex `⋯ ⟶ Q^(j-2) ⟶ Q^(j-1) ⟶ Q^j` obtained by unfolding a `ZMod n`-indexed
complex `Q` along the integers and keeping the degrees at most `j`, indexed homologically so that
`Q^j` lies in degree `0`. -/
@[expose]
def resolutionComplex (Q : HomologicalComplex C (ComplexShape.up (ZMod n))) (j : ℤ) :
    ChainComplex C ℕ :=
  ((unfoldFunctor C n).obj Q).restriction (ComplexShape.embeddingUpIntLE j)

variable (Q : HomologicalComplex C (ComplexShape.up (ZMod n))) (j : ℤ)

/-- The term of `TauCeti.PeriodicComplex.resolutionComplex Q j` in degree `k` is the term of `Q`
at the residue of `j - k`. -/
@[simp]
theorem resolutionComplex_X (k : ℕ) :
    (resolutionComplex Q j).X k = Q.X ((j - k : ℤ) : ZMod n) :=
  (rfl)

/-- The differential of `TauCeti.PeriodicComplex.resolutionComplex Q j` into degree `k` is the
cyclic differential between the residues of `j - (k + 1)` and `j - k`. -/
@[simp]
theorem resolutionComplex_d (k : ℕ) :
    (resolutionComplex Q j).d (k + 1) k =
      Q.d ((j - (k + 1 : ℕ) : ℤ) : ZMod n) ((j - k : ℤ) : ZMod n) :=
  unfoldFunctor_obj_d_of_add_one_eq C n Q
    (show j - ((k + 1 : ℕ) : ℤ) + 1 = j - k by omega)

/-- `TauCeti.PeriodicComplex.resolutionComplex Q j` only depends on the residue of `j`
modulo `n`. -/
def resolutionComplexIsoOfEq {j j' : ℤ} (h : (j : ZMod n) = (j' : ZMod n)) :
    resolutionComplex Q j ≅ resolutionComplex Q j' :=
  Hom.isoOfComponents (fun k ↦ Q.XIsoOfEq (show ((j - k : ℤ) : ZMod n) = ((j' - k : ℤ) : ZMod n)
      by push_cast; rw [h]))
    (by
      rintro _ k rfl
      rw [resolutionComplex_d, resolutionComplex_d]
      exact (Q.XIsoOfEq_hom_comp_d _ _).trans (Q.d_comp_XIsoOfEq_hom _ _).symm)

/-- Dropping the first term of `TauCeti.PeriodicComplex.resolutionComplex Q j` gives the
complex attached to `j - 1`. -/
def truncateResolutionComplexIso :
    ChainComplex.truncate.obj (resolutionComplex Q j) ≅ resolutionComplex Q (j - 1) :=
  Hom.isoOfComponents (fun k ↦ Q.XIsoOfEq
      (show ((j - (k + 1 : ℕ) : ℤ) : ZMod n) = ((j - 1 - k : ℤ) : ZMod n) from
        congrArg _ (by omega)))
    (by
      rintro _ k rfl
      change _ ≫ (resolutionComplex Q (j - 1)).d (k + 1) k =
        (resolutionComplex Q j).d (k + 1 + 1) (k + 1) ≫ _
      rw [resolutionComplex_d, resolutionComplex_d]
      exact (Q.XIsoOfEq_hom_comp_d _ _).trans (Q.d_comp_XIsoOfEq_hom _ _).symm)

/-- Dropping the first `m` terms of `TauCeti.PeriodicComplex.resolutionComplex Q j` gives the
complex attached to `j - m`. -/
def truncateIterateResolutionComplexIso : ∀ m : ℕ,
    ChainComplex.truncate.obj^[m] (resolutionComplex Q j) ≅ resolutionComplex Q (j - m)
  | 0 => resolutionComplexIsoOfEq Q (by simp)
  | m + 1 => eqToIso (Function.iterate_succ_apply' _ m _) ≪≫
      ChainComplex.truncate.mapIso (truncateIterateResolutionComplexIso m) ≪≫
      truncateResolutionComplexIso Q (j - m) ≪≫ resolutionComplexIsoOfEq Q (congrArg _ (by omega))

/-- **Periodicity.** Dropping the first `n` terms of
`TauCeti.PeriodicComplex.resolutionComplex Q j` gives back the same complex. -/
def resolutionComplexPeriodIso :
    ChainComplex.truncate.obj^[n] (resolutionComplex Q j) ≅ resolutionComplex Q j :=
  truncateIterateResolutionComplexIso Q j n ≪≫ resolutionComplexIsoOfEq Q (by simp)

variable {j} {i i' : ZMod n}

/-- The term in degree `0` of `TauCeti.PeriodicComplex.resolutionComplex Q j` is `Q^i'`, for
the residue `i'` of `j`. -/
def resolutionComplexXZeroIso (hj : (j : ZMod n) = i') :
    (resolutionComplex Q j).X 0 ≅ Q.X i' :=
  Q.XIsoOfEq (by simpa using hj)

/-- The term in degree `1` of `TauCeti.PeriodicComplex.resolutionComplex Q j` is `Q^i`, for the
residue `i' = i + 1` of `j`. -/
private def resolutionComplexXOneIso (hj : (j : ZMod n) = i') (hi : i + 1 = i') :
    (resolutionComplex Q j).X 1 ≅ Q.X i :=
  Q.XIsoOfEq (show ((j - (1 : ℕ) : ℤ) : ZMod n) = i by
    push_cast; rw [hj, ← hi, add_sub_cancel_right])

/-- The differential into degree `0` of `TauCeti.PeriodicComplex.resolutionComplex Q j` is the
cyclic differential `Q^i ⟶ Q^i'`, for the residue `i' = i + 1` of `j`. -/
@[reassoc]
private theorem resolutionComplex_d_one_zero_comp_xZeroIso_hom (hj : (j : ZMod n) = i')
    (hi : i + 1 = i') :
    (resolutionComplex Q j).d 1 0 ≫ (resolutionComplexXZeroIso Q hj).hom =
      (resolutionComplexXOneIso Q hj hi).hom ≫ Q.d i i' := by
  rw [resolutionComplex_d]
  exact (Q.d_comp_XIsoOfEq_hom _ _).trans (Q.XIsoOfEq_hom_comp_d _ _).symm

/-- An augmentation `ε` killing the cyclic differential `Q^i ⟶ Q^i'` kills the differential
into degree `0` of `TauCeti.PeriodicComplex.resolutionComplex Q j`, for the residue
`i' = i + 1` of `j`. -/
theorem resolutionComplex_d_one_zero_comp (hj : (j : ZMod n) = i') (hi : i + 1 = i') {M : C}
    (ε : Q.X i' ⟶ M) (hε : Q.d i i' ≫ ε = 0) :
    (resolutionComplex Q j).d 1 0 ≫ (resolutionComplexXZeroIso Q hj).hom ≫ ε = 0 := by
  rw [resolutionComplex_d_one_zero_comp_xZeroIso_hom_assoc Q hj hi, hε, comp_zero]

end HasZeroMorphisms

section ProjectiveResolution

variable [Abelian C] (Q : HomologicalComplex C (ComplexShape.up (ZMod n))) [∀ i, Projective (Q.X i)]
  (hQ : Q.Acyclic) (j : ℤ) {i i' : ZMod n} (hj : (j : ZMod n) = i') (hi : i + 1 = i') {M : C}
  (ε : Q.X i' ⟶ M) (hε : Q.d i i' ≫ ε = 0) (hε' : IsColimit (CokernelCofork.ofπ ε hε))

include hQ hi hε' in
/-- **Periodic projective resolutions.** Let `Q` be an acyclic `ZMod n`-indexed complex of
projective objects, let `i + 1 = i'` be consecutive residues and let `ε : Q^i' ⟶ M` be a
cokernel of the differential `Q^i ⟶ Q^i'`. For an integer `j` with residue `i'`, the complex
`⋯ ⟶ Q^(j-2) ⟶ Q^(j-1) ⟶ Q^j ⟶ M` is a projective resolution of `M`. Its complex is
`TauCeti.PeriodicComplex.resolutionComplex Q j`, which is periodic of period `n`
(`TauCeti.PeriodicComplex.resolutionComplexPeriodIso`). -/
@[expose]
def projectiveResolution : ProjectiveResolution M where
  complex := resolutionComplex Q j
  projective k := inferInstanceAs (Projective (Q.X _))
  π := ((resolutionComplex Q j).toSingle₀Equiv M).symm
    ⟨(resolutionComplexXZeroIso Q hj).hom ≫ ε, resolutionComplex_d_one_zero_comp Q hj hi ε hε⟩
  quasiIso := by
    constructor
    rintro (_ | k)
    · have : Epi ε := epi_of_isColimit_cofork hε'
      rw [ChainComplex.quasiIsoAt₀_iff]
      refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ⟨?_, ?_⟩
      · exact (resolutionComplex Q j).shape _ _ (by simp)
      · rfl
      · rfl
      · refine ShortComplex.exact_of_iso
          (ShortComplex.isoMk (resolutionComplexXOneIso Q hj hi).symm
            (resolutionComplexXZeroIso Q hj).symm (Iso.refl M) ?_ ?_)
          ((ShortComplex.mk _ _ hε).exact_of_g_is_cokernel hε')
        · dsimp
          rw [Iso.inv_comp_eq, ← resolutionComplex_d_one_zero_comp_xZeroIso_hom_assoc,
            Iso.hom_inv_id, Category.comp_id]
        · simp [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
      · dsimp
        rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        infer_instance
    · rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp)]
      have hp : (ComplexShape.up ℤ).prev (j - (k + 1 : ℕ)) = j - (k + 2 : ℕ) :=
        (ComplexShape.up ℤ).prev_eq' (by simp; omega)
      have hn : (ComplexShape.up ℤ).next (j - (k + 1 : ℕ)) = j - k :=
        (ComplexShape.up ℤ).next_eq' (by simp; omega)
      refine (ShortComplex.exact_iff_of_iso (restriction.sc'Iso ((unfoldFunctor C n).obj Q)
        (ComplexShape.embeddingUpIntLE j) (k + 2) (k + 1) k rfl rfl rfl hp hn)).2 ?_
      exact (exactAt_iff' _ _ _ _ hp hn).1 ((unfoldFunctor_exactAt_iff C n Q _).2 (hQ _))

/-- The complex of `TauCeti.PeriodicComplex.projectiveResolution` is
`TauCeti.PeriodicComplex.resolutionComplex Q j`. -/
@[simp]
theorem projectiveResolution_complex :
    (projectiveResolution Q hQ j hj hi ε hε hε').complex = resolutionComplex Q j :=
  (rfl)

/-- The augmentation of `TauCeti.PeriodicComplex.projectiveResolution` is `ε`. -/
@[simp]
theorem projectiveResolution_π_f_zero :
    (projectiveResolution Q hQ j hj hi ε hε hε').π.f 0 = (resolutionComplexXZeroIso Q hj).hom ≫ ε :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end ProjectiveResolution

end TauCeti.PeriodicComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Dropping the first `m` terms of isomorphic complexes gives isomorphic complexes. -/
private def truncateIterateMapIso {K L : ChainComplex C ℕ} (e : K ≅ L) :
    ∀ m : ℕ, truncate.obj^[m] K ≅ truncate.obj^[m] L
  | 0 => e
  | m + 1 => truncateIterateMapIso (truncate.mapIso e) m

/-- A chain complex `K` has a periodic tail of period `n` after a preperiod of `p` terms if
dropping its first `p` terms leaves the unfolding of a `ZMod n`-indexed complex in the degrees
at most some integer `j`, as in `TauCeti.PeriodicComplex.resolutionComplex`. -/
def HasPeriodicTail (K : ChainComplex C ℕ) (n p : ℕ) : Prop :=
  ∃ (Q : HomologicalComplex C (ComplexShape.up (ZMod n))) (j : ℤ),
    Nonempty (truncate.obj^[p] K ≅ TauCeti.PeriodicComplex.resolutionComplex Q j)

variable {K L : ChainComplex C ℕ} {n p q : ℕ}

/-- The unfolding of a periodic complex in degrees at most `j` is periodic from the start. -/
theorem _root_.TauCeti.PeriodicComplex.resolutionComplex_hasPeriodicTail
    (Q : HomologicalComplex C (ComplexShape.up (ZMod n))) (j : ℤ) :
    (TauCeti.PeriodicComplex.resolutionComplex Q j).HasPeriodicTail n 0 :=
  ⟨Q, j, ⟨Iso.refl _⟩⟩

/-- Having a periodic tail is invariant under isomorphism of complexes. -/
theorem HasPeriodicTail.of_iso (h : K.HasPeriodicTail n p) (e : K ≅ L) :
    L.HasPeriodicTail n p := by
  obtain ⟨Q, j, ⟨e'⟩⟩ := h
  exact ⟨Q, j, ⟨(truncateIterateMapIso e p).symm ≪≫ e'⟩⟩

/-- A periodic tail after `p` terms is also a periodic tail after any `q ≥ p` terms. -/
theorem HasPeriodicTail.mono (h : K.HasPeriodicTail n p) (hpq : p ≤ q) :
    K.HasPeriodicTail n q := by
  obtain ⟨Q, j, ⟨e⟩⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hpq
  rw [HasPeriodicTail, Function.iterate_add_apply]
  exact ⟨Q, j - d, ⟨truncateIterateMapIso e d ≪≫
    TauCeti.PeriodicComplex.truncateIterateResolutionComplexIso Q j d⟩⟩

/-- **Eventual periodicity.** If `K` has a periodic tail of period `n` after `p` terms, then
dropping `n` further terms gives back the complex obtained by dropping the first `p` terms. -/
theorem HasPeriodicTail.nonempty_truncate_iterate_iso (h : K.HasPeriodicTail n p) :
    Nonempty (truncate.obj^[n] (truncate.obj^[p] K) ≅ truncate.obj^[p] K) := by
  obtain ⟨Q, j, ⟨e⟩⟩ := h
  exact ⟨truncateIterateMapIso e n ≪≫
    TauCeti.PeriodicComplex.resolutionComplexPeriodIso Q j ≪≫ e.symm⟩

end ChainComplex
