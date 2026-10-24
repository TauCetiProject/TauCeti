/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Basic
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Borel.ProjectiveOrbit
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Dimension
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Solvable.Derived.Series
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Characteristic

/-!
# Conjugacy of Borel subgroups

Any two Borel subgroups of a finite-type affine group over an algebraically closed field
are conjugate by a rational point. The ambient group may be disconnected or nonreduced,
and the result holds in every characteristic.

For a smooth connected group, induction on Lie dimension proves the theorem. A solvable
group is its own unique Borel subgroup. Otherwise the closed-projective-orbit criterion
supplies a proper closed subgroup containing conjugates of every Borel candidate. Taking
its reduction and identity component retains these containments and produces a smooth
connected group of strictly smaller dimension. Conjugacy there transfers to the original
group. Finally the reduced identity component handles an arbitrary ambient group.

The proof combines the proper-subgroup construction in `Borel.ProjectiveOrbit`,
`HopfIdeal.finrank_quotientLie_lt`, and the closed-subgroup transfers in
`Borel.Conjugacy.Basic`. The reduction is realized using `HopfIdeal.vanishingIdeal` and
rational point separation.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.6.
-/

public section

open WithConv

namespace TauCeti.HopfIdeal

open geometricallySolvablePointsCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The proper subgroup in the closed-orbit argument can be chosen smooth and connected,
while retaining containment of conjugates of all Borel subgroups. -/
private theorem exists_proper_smooth_connected_of_not_isSolvable
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k))) :
    ∃ P : HopfIdeal k H, P ≠ ⊥ ∧
      Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H P) ∧
      geometricallyConnectedCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient H P).obj ∧
      ∀ B : HopfIdeal k H, IsBorelOverAlgClosed k H B →
        ∃ g : WithConv (H →ₐ[k] k), P ≤ B.conjugate g := by
  obtain ⟨D, hD, hcontain⟩ :=
    exists_ne_bot_forall_isBorelCandidate_exists_conjugate_le_of_not_isSolvable hH
  let S := CommHopfAlgCat.quotientPointsSubgroup H.obj D (CommAlgCat.of k k)
  let N := vanishingIdeal S
  have hDN : D ≤ N := (le_vanishingIdeal_iff S D).mpr le_rfl
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H N) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  refine ⟨N.identityComponent, ?_, N.smooth_identityComponent,
    N.geometricallyConnected_identityComponent, ?_⟩
  · intro hP
    exact hD (le_bot_iff.mp (hP ▸ hDN.trans N.le_identityComponent))
  · intro B hB
    obtain ⟨g, hg⟩ := hcontain B ((isBorelOverAlgClosed_iff _ _ _).mp hB).2.prop
    have hBg := hB.conjugate g⁻¹
    have hDB : D ≤ B.conjugate g⁻¹ := by
      simpa using conjugate_mono g⁻¹ hg
    let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H (B.conjugate g⁻¹)) :=
      (smoothCommHopfAlgProperty_iff _).mp
        ((isBorelOverAlgClosed_iff _ _ _).mp hBg).2.prop.smooth
    let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient H (B.conjugate g⁻¹)) :=
      isReduced_of_smooth k _
    have hNB : N ≤ B.conjugate g⁻¹ :=
      le_of_quotientPointsSubgroup_le (K := k)
        ((CommHopfAlgCat.quotientPointsSubgroup_antitone H.obj (CommAlgCat.of k k) hDB).trans
          ((le_vanishingIdeal_iff S N).mp le_rfl))
    exact ⟨g⁻¹, identityComponent_le_of_le hNB
      ((isBorelOverAlgClosed_iff _ _ _).mp hBg).2.prop.geometricallyConnected⟩

/-- Conjugacy in smooth connected groups, with a bound for induction on Lie dimension. -/
private theorem exists_conjugate_eq_of_smooth_connected (n : ℕ) :
    ∀ (H : FiniteTypeCommHopfAlgCat.{u, u} k),
      Algebra.Smooth k H → geometricallyConnectedCommHopfAlgProperty k H.obj →
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤ n →
      ∀ I J : HopfIdeal k H,
        IsBorelOverAlgClosed k H I → IsBorelOverAlgClosed k H J →
        ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hsm hconn hdim I J hI hJ
    let _ : Algebra.Smooth k H := hsm
    let _ : IsReduced H := isReduced_of_smooth k H
    let _ : IrreducibleSpace (PrimeSpectrum H) := hconn.irreducibleSpace k H.obj
    by_cases hsolv : Group.IsSolvable (WithConv (H →ₐ[k] k))
    · have hgeo : geometricallySolvablePointsCommHopfAlgProperty k H.obj :=
        (iff_exists_derivedSeriesDefiningIdeal_eq_augmentation H.obj).mpr
          (H.obj.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation.mp hsolv)
      have hbot : IsBorelCandidate k H ⊥ :=
        ((isSolvableRadicalCandidate_bot_iff H).mpr ⟨hconn, hsm, hgeo⟩).isBorelCandidate
      have hIbot : I = ⊥ := le_bot_iff.mp
        (((isBorelOverAlgClosed_iff _ _ _).mp hI).2.le_of_le hbot bot_le)
      have hJbot : J = ⊥ := le_bot_iff.mp
        (((isBorelOverAlgClosed_iff _ _ _).mp hJ).2.le_of_le hbot bot_le)
      exact ⟨1, by simp [hIbot, hJbot]⟩
    · obtain ⟨P, hP, hPsm, hPconn, hcontain⟩ :=
        exists_proper_smooth_connected_of_not_isSolvable H hsolv
      let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H P) := hPsm
      have hlt := (P.finrank_quotientLie_lt hconn hP).trans_le hdim
      obtain ⟨g, hg⟩ := hcontain I hI
      obtain ⟨h, hh⟩ := hcontain J hJ
      obtain ⟨a, ha⟩ := exists_conjugate_eq_of_isBorelOverAlgClosed_of_quotient P
        (ih _ hlt _ hPsm hPconn le_rfl) (hI.conjugate g) (hJ.conjugate h) hg hh
      exact ⟨h⁻¹ * a * g, by
        have heq := congrArg (fun B : HopfIdeal k H ↦ B.conjugate h⁻¹) ha
        simpa [conjugate_mul, mul_assoc] using heq⟩

/-- **Borel conjugacy.** Any two Borel subgroups of a finite-type affine group over an
algebraically closed field are conjugate by a rational point. The ambient group need not
be smooth, reduced, or connected. -/
theorem IsBorelOverAlgClosed.exists_conjugate_eq
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k H I) (hJ : IsBorelOverAlgClosed k H J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  apply exists_conjugate_eq_of_isBorelOverAlgClosed_of_smooth_connected _ hI hJ
  intro K hsm hconn
  exact exists_conjugate_eq_of_smooth_connected _ K hsm hconn le_rfl

end TauCeti.HopfIdeal
