/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Chain.Complex

/-!
# The bigraded simply blocked grid complex

Setting one variable `V_i` to zero preserves the bigrading of the unblocked grid complex.
The surviving monomial `V^e x` has bidegree `(M_O(x) - 2 |e|, A(x) - |e|)`.
The homogeneous pieces are submodules over the ground ring, since the remaining variables
have degree `(-2, -1)`. The differential has degree `(-1, 0)`, giving a Maslov-indexed
chain complex for each Alexander degree.

As for the unblocked grading, an odd number of components makes the Alexander grading
integral. The construction is the simply blocked complex for a knot; for a link it is
only a one-variable specialization, since the simply blocked link theory requires one
blocked marking on each component.

The homogeneous pieces are obtained from the existing unblocked pieces using the inclusion
of the surviving polynomial variables. Specialization is homogeneous and surjective on
each piece, allowing the unblocked grading-change theorem to descend directly.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6,
particularly Definition 4.6.12.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

private noncomputable def liftHat (R : Type*) [CommSemiring R] (i : Fin n) :
    GridChainHat R n i →ₗ[R] GridChainMinus R n :=
  Finsupp.mapRange.linearMap (MvPolynomial.rename Subtype.val).toLinearMap

private theorem liftHat_apply (R : Type*) [CommSemiring R] (i : Fin n)
    (c : GridChainHat R n i) (x : GridState n) :
    liftHat R i c x = MvPolynomial.rename Subtype.val (c x) := (rfl)

private theorem specialization_liftHat (R : Type*) [CommSemiring R] (i : Fin n)
    (c : GridChainHat R n i) :
    simplyBlockedSpecialization R i (liftHat R i c) = c := by
  apply Finsupp.ext
  intro x
  rw [simplyBlockedSpecialization_apply, liftHat_apply, killCompl_rename_app]

/-- The homogeneous piece of the specialization `V_i = 0` in bidegree `g`, over the
ground semiring. A chain belongs to this piece exactly when including its surviving
variables in the full polynomial ring gives an unblocked chain of bidegree `g`. -/
noncomputable def bigradedChainHatPiece (R : Type*) [CommSemiring R] (i : Fin n)
    (g : ℤ × ℤ) : Submodule R (GridChainHat R n i) :=
  (G.bigradedChainMinusPiece R g).comap (liftHat R i)

/-- A specialized chain is homogeneous exactly when all its surviving monomials have
the prescribed bidegree. -/
@[simp]
theorem mem_bigradedChainHatPiece {R : Type*} [CommSemiring R] {i : Fin n}
    {g : ℤ × ℤ} {c : GridChainHat R n i} :
    c ∈ G.bigradedChainHatPiece R i g ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support,
        G.bidegree x - (2 * (e.degree : ℤ), (e.degree : ℤ)) = g := by
  classical
  simp only [bigradedChainHatPiece, Submodule.mem_comap, mem_bigradedChainMinusPiece,
    liftHat_apply, support_rename_of_injective Subtype.val_injective, Finset.mem_image,
    forall_exists_index, and_imp]
  constructor
  · intro h x e he
    simpa only [Prod.ext_iff, monomialBidegree_fst, monomialBidegree_snd,
      Prod.fst_sub, Prod.snd_sub, bidegree_fst, bidegree_snd, Finsupp.degree_mapDomain]
      using h x _ e he rfl
  · rintro h x _ e he rfl
    simpa only [Prod.ext_iff, monomialBidegree_fst, monomialBidegree_snd,
      Prod.fst_sub, Prod.snd_sub, bidegree_fst, bidegree_snd, Finsupp.degree_mapDomain]
      using h x e he

/-- Specialization at `V_i = 0` preserves bidegrees. -/
theorem simplyBlockedSpecialization_mem_bigradedChainHatPiece {R : Type*} [CommSemiring R]
    (i : Fin n) {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    simplyBlockedSpecialization R i c ∈ G.bigradedChainHatPiece R i g := by
  rw [mem_bigradedChainHatPiece]
  intro x e he
  rw [simplyBlockedSpecialization_apply, support_killCompl, Finset.mem_preimage] at he
  simpa only [Prod.ext_iff, monomialBidegree_fst, monomialBidegree_snd,
    Prod.fst_sub, Prod.snd_sub, bidegree_fst, bidegree_snd, Finsupp.degree_mapDomain]
    using (G.mem_bigradedChainMinusPiece.mp hc) x _ he

/-- Every homogeneous specialized chain lifts to an unblocked chain of the same bidegree. -/
theorem mem_bigradedChainHatPiece_iff_exists {R : Type*} [CommSemiring R]
    {i : Fin n} {g : ℤ × ℤ} {c : GridChainHat R n i} :
    c ∈ G.bigradedChainHatPiece R i g ↔
      ∃ b ∈ G.bigradedChainMinusPiece R g, simplyBlockedSpecialization R i b = c := by
  constructor
  · intro hc
    exact ⟨liftHat R i c, hc, specialization_liftHat R i c⟩
  · rintro ⟨b, hb, rfl⟩
    exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i hb

/-- A monomial multiple of a state is homogeneous of its expected bidegree. -/
theorem single_monomial_mem_bigradedChainHatPiece (R : Type*) [CommSemiring R]
    (i : Fin n) (x : GridState n) (e : {c : Fin n // c ≠ i} →₀ ℕ) (a : R) :
    (Finsupp.single x (monomial e a) : GridChainHat R n i) ∈
      G.bigradedChainHatPiece R i
        (G.bidegree x - (2 * (e.degree : ℤ), (e.degree : ℤ))) := by
  rw [mem_bigradedChainHatPiece]
  intro y d hd
  by_cases h : y = x
  · subst y
    rw [Finsupp.single_eq_same] at hd
    rw [Finset.mem_singleton.mp (support_monomial_subset hd)]
  · simp [Finsupp.single_eq_of_ne h] at hd

/-- The simply blocked differential lowers Maslov degree by one and preserves Alexander degree.
This homogeneity holds for the unsigned map over any commutative semiring. -/
theorem simplyBlockedDifferential_mem_bigradedChainHatPiece {R : Type*} [CommSemiring R]
    {i : Fin n} {g : ℤ × ℤ} {c : GridChainHat R n i}
    (hc : c ∈ G.bigradedChainHatPiece R i g) :
    G.1.simplyBlockedDifferential R i c ∈ G.bigradedChainHatPiece R i (g - (1, 0)) := by
  obtain ⟨b, hb, rfl⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [← GridDiagram.simplyBlockedSpecialization_unblockedDifferential]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.unblockedDifferential_mem_bigradedChainMinusPiece hb)

/-- Multiplication by a surviving variable lowers bidegree by `(2, 1)`. -/
theorem X_smul_mem_bigradedChainHatPiece {R : Type*} [CommSemiring R]
    {i : Fin n} (j : {c : Fin n // c ≠ i}) {g : ℤ × ℤ} {c : GridChainHat R n i}
    (hc : c ∈ G.bigradedChainHatPiece R i g) :
    (X j : MvPolynomial {c : Fin n // c ≠ i} R) • c ∈
      G.bigradedChainHatPiece R i (g - (2, 1)) := by
  have h := G.X_smul_mem_bigradedChainMinusPiece j.val hc
  rw [bigradedChainHatPiece, Submodule.mem_comap]
  -- The inclusion is linear over the ground ring and renames polynomial scalars.
  convert h using 1
  apply Finsupp.ext
  intro x
  simp only [liftHat_apply, Finsupp.smul_apply, smul_eq_mul, map_mul, rename_X]

/-- The homogeneous pieces span the entire specialized chain module. -/
theorem iSup_bigradedChainHatPiece_eq_top (R : Type*) [CommSemiring R] (i : Fin n) :
    ⨆ g, G.bigradedChainHatPiece R i g = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  have hc : liftHat R i c ∈ ⨆ g, G.bigradedChainMinusPiece R g := by
    rw [G.iSup_bigradedChainMinusPiece_eq_top R]
    trivial
  suffices simplyBlockedSpecialization R i (liftHat R i c) ∈
      ⨆ g, G.bigradedChainHatPiece R i g by
    rwa [specialization_liftHat] at this
  refine Submodule.iSup_induction _
    (motive := fun b => simplyBlockedSpecialization R i b ∈
      ⨆ g, G.bigradedChainHatPiece R i g) hc
    (fun g b hb => ?_) ?_ (fun b c hb hc => ?_)
  · exact Submodule.mem_iSup_of_mem g
      (G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i hb)
  · simp only [map_zero, Submodule.zero_mem]
  · rw [map_add]
    exact Submodule.add_mem _ hb hc

/-- The homogeneous pieces of the specialized chain module are independent. -/
theorem iSupIndep_bigradedChainHatPiece (R : Type*) [CommSemiring R] (i : Fin n) :
    iSupIndep (G.bigradedChainHatPiece R i) := by
  intro g
  rw [Submodule.disjoint_def]
  intro c hc hc'
  have hle : (⨆ g' ≠ g, G.bigradedChainHatPiece R i g') ≤
      (⨆ g' ≠ g, G.bigradedChainMinusPiece R g').comap (liftHat R i) :=
    iSup₂_le fun g' hg' => Submodule.comap_mono (le_iSup₂_of_le g' hg' le_rfl)
  have hz := (Submodule.disjoint_def.mp (G.iSupIndep_bigradedChainMinusPiece R g))
    (liftHat R i c) hc (hle hc')
  have := congrArg (simplyBlockedSpecialization R i) hz
  rw [specialization_liftHat, map_zero] at this
  exact this

/-- The specialized chain module is the internal direct sum of its homogeneous pieces. -/
theorem isInternal_bigradedChainHatPiece (R : Type*) [CommRing R] (i : Fin n) :
    DirectSum.IsInternal (G.bigradedChainHatPiece R i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_bigradedChainHatPiece R i) (G.iSup_bigradedChainHatPiece_eq_top R i)

/-- The simply blocked differential between consecutive Maslov degrees at fixed Alexander degree. -/
noncomputable def gradedSimplyBlockedDifferential (R : Type*) [CommSemiring R]
    (i : Fin n) (a m : ℤ) :
    G.bigradedChainHatPiece R i (m + 1, a) →ₗ[R] G.bigradedChainHatPiece R i (m, a) :=
  ((G.1.simplyBlockedDifferential R i).restrictScalars R).restrict fun c hc => by
    simpa using G.simplyBlockedDifferential_mem_bigradedChainHatPiece hc

/-- Inclusion of a homogeneous piece intertwines the graded and total differentials. -/
@[simp]
theorem coe_gradedSimplyBlockedDifferential (R : Type*) [CommSemiring R]
    (i : Fin n) (a m : ℤ) (c : G.bigradedChainHatPiece R i (m + 1, a)) :
    (G.gradedSimplyBlockedDifferential R i a m c : GridChainHat R n i) =
      G.1.simplyBlockedDifferential R i c := (rfl)

variable (R : Type*) [CommRing R] [CharP R 2]

/-- Consecutive graded simply blocked differentials compose to zero in characteristic two. -/
theorem gradedSimplyBlockedDifferential_comp_eq_zero (i : Fin n) (a m : ℤ) :
    (G.gradedSimplyBlockedDifferential R i a m).comp
      (G.gradedSimplyBlockedDifferential R i a (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    coe_gradedSimplyBlockedDifferential, ZeroMemClass.coe_zero]
  exact LinearMap.congr_fun (G.1.simplyBlockedDifferential_comp_self_eq_zero R i) c

/-- The Maslov-graded specialization `V_i = 0` in Alexander degree `a`.
For a knot grid this is the graded simply blocked complex. -/
noncomputable def gradedSimplyBlockedComplex (i : Fin n) (a : ℤ) :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (G.bigradedChainHatPiece R i (m, a)))
    (fun m => ModuleCat.ofHom (G.gradedSimplyBlockedDifferential R i a m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, G.gradedSimplyBlockedDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

/-- The objects of the graded specialization are its homogeneous chain modules. -/
@[simp]
theorem gradedSimplyBlockedComplex_X (i : Fin n) (a m : ℤ) :
    (G.gradedSimplyBlockedComplex R i a).X m =
      ModuleCat.of R (G.bigradedChainHatPiece R i (m, a)) := (rfl)

/-- The consecutive differential of the graded complex is the restriction of the total map. -/
@[simp]
theorem gradedSimplyBlockedComplex_d (i : Fin n) (a m : ℤ) :
    (G.gradedSimplyBlockedComplex R i a).d (m + 1) m =
      eqToHom (G.gradedSimplyBlockedComplex_X R i a (m + 1)) ≫
        ModuleCat.ofHom (G.gradedSimplyBlockedDifferential R i a m) ≫
          eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm := by
  simp only [gradedSimplyBlockedComplex, ChainComplex.of_d]
  -- The object identifications act as identity maps on homogeneous chains.
  ext c
  rfl

end TauCeti.OddComponentGridDiagram
