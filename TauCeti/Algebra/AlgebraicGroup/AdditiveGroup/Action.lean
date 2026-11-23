/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.Algebra.Polynomial.AlgebraMap
import TauCeti.Algebra.Coalgebra.Convolution
import TauCeti.Algebra.Polynomial.Degree.Comp
import TauCeti.Algebra.Polynomial.Eval.Naturality

/-!
# Actions of reduced affine groups on the additive group by automorphisms are through characters

Let `H` be a commutative Hopf algebra over `R`, so that `A ↦ (H →ₐ[R] A)` is the functor of
points of the affine group `Spec H`. An action of `Spec H` on the affine line `𝔸¹` fixing the
origin is a family of actions of the groups of points `H →ₐ[R] A` on the commutative
`R`-semialgebras `A`, natural in `A` and fixing `0`. Every action of `Spec H` on the additive group
`𝔾ₐ` by group automorphisms gives one, since `𝔾ₐ(A) = A`
(`TauCeti.AdditiveGroup.gaPointsMulEquiv`).

When `H` is reduced, every such action is linear and given by a unique character of `Spec H`:
there is a unique group-like element `χ` of `H` with `g • a = g(χ) * a` for every `A`, every
point `g : H →ₐ[R] A` and every `a ∈ A`. Conversely every group-like element defines such an
action, the points action on the one-dimensional comodule `TauCeti.Comodule.groupLike`
(`TauCeti.Comodule.endOfPoint_groupLike`). Thus a torus, or any smooth affine group over a field,
acting on `𝔾ₐ` by group automorphisms acts through a character; this is how a torus acts by
conjugation on a one-dimensional vector subgroup, such as a root group.

The proof is by the Yoneda lemma (`Polynomial.eq_aevalTower_of_naturality`). The action is
determined by the polynomial `F ∈ H[X]` obtained by letting the universal point `H → H[X]` act on
the universal element `X`: the action of `g` on `a` is the evaluation of `F`, with coefficients
pushed along `g`, at `a`. The action of the
inverse universal point provides a right compositional inverse of `F`, so `F` has degree at most
one over the reduced ring `H` (`Polynomial.natDegree_le_one_of_comp_eq_X_left`); it has no
constant term since the action fixes `0`. Its linear coefficient is the character `χ`, and the
action axioms at the universal points make it group-like.

Reducedness of `H` is necessary. Over a field `k` of characteristic `p > 0`, the group `μₚ`, with
nonreduced coordinate ring `k[t]/(t^p - 1)`, acts on `𝔾ₐ` by the automorphisms
`a ↦ ζ a + (ζ - 1) a^p`, which are not linear.

## Main results

* `TauCeti.AdditiveGroup.existsUnique_groupLike_act_eq_mul_of_naturality`: a natural action of
  an affine group with reduced coordinate ring on `𝔸¹` fixing the origin is multiplication by the
  values of a unique group-like element.
* `TauCeti.AdditiveGroup.existsUnique_groupLike_mulAut_act_eq_mul_of_naturality`: the same for a
  natural action on `𝔾ₐ` by group automorphisms, read on the parameters of the points of `𝔾ₐ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 21.11 and the proof of Theorem 16.33.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open Polynomial WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v

variable {R : Type u} {H : Type v} [CommSemiring R] [CommRing H] [HopfAlgebra R H]

/-- The universal point of `H` with values in `H[X]`: the inclusion of the constants. -/
private noncomputable abbrev univPoint : WithConv (H →ₐ[R] H[X]) :=
  toConv (IsScalarTower.toAlgHom R H H[X])

/-- **Actions of reduced affine groups on `𝔸¹` fixing the origin are through characters.** Let
`H` be a commutative Hopf algebra over `R` with reduced underlying ring, and let the groups of
points `H →ₐ[R] A` act on the commutative `R`-semialgebras `A`, naturally in `A` and fixing `0`.
Then there is a unique group-like element `χ` of `H` such that every point `g` acts by
multiplication by `g χ`.

Every action of `Spec H` on the additive group `𝔾ₐ` by group automorphisms gives such a family
(`TauCeti.AdditiveGroup.existsUnique_groupLike_mulAut_act_eq_mul_of_naturality`). Reducedness
cannot be dropped: `μₚ` acts nonlinearly on `𝔾ₐ` in characteristic `p`. -/
theorem existsUnique_groupLike_act_eq_mul_of_naturality [IsReduced H]
    (act : ∀ (A : Type v) [CommSemiring A] [Algebra R A], WithConv (H →ₐ[R] A) → A → A)
    (act_mapValue : ∀ (A B : Type v) [CommSemiring A] [Algebra R A] [CommSemiring B]
      [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (a : A),
      φ (act A g a) = act B (AlgHom.mapValue φ g) (φ a))
    (act_one : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (a : A), act A 1 a = a)
    (act_mul : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g h : WithConv (H →ₐ[R] A))
      (a : A), act A (g * h) a = act A g (act A h a))
    (act_zero : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A)),
      act A g 0 = 0) :
    ∃! χ : GroupLike R H,
      ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A)) (a : A),
        act A g a = g.ofConv χ * a := by
  -- The polynomial `F` of the action: the universal point acting on the universal element.
  obtain ⟨F, hF⟩ : ∃ F : H[X], act H[X] univPoint X = F := ⟨_, rfl⟩
  have act_eq : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A))
      (a : A), act A g a = aevalTower g.ofConv a F := by
    intro A _ _ g a
    rw [← hF, ← toConv_ofConv g]
    exact eq_aevalTower_of_naturality (fun A _ _ g a => act A (toConv g) a)
      (fun A B _ _ _ _ φ g a => by rw [act_mapValue, AlgHom.mapValue_apply, ofConv_toConv])
      A g.ofConv a
  -- At the universal point, evaluating `F` is composing with `F`.
  have act_univPoint : ∀ y : H[X], act H[X] univPoint y = F.comp y := fun y => by
    rw [act_eq, comp_eq_aevalTower (R := R), ofConv_toConv]
  -- The inverse universal point provides a right compositional inverse of `F`.
  have hcomp : F.comp (act H[X] univPoint⁻¹ X) = X := by
    rw [← act_univPoint, ← act_mul, mul_inv_cancel, act_one]
  have hdeg : F.natDegree ≤ 1 := natDegree_le_one_of_comp_eq_X_left hcomp
  -- The action fixes `0`, so `F` has no constant term.
  have hcoeff0 : F.coeff 0 = 0 := by
    have h := act_univPoint 0
    rw [act_zero, comp_zero, eq_comm, C_eq_zero] at h
    rw [coeff_zero_eq_eval_zero, h]
  set χ := F.coeff 1
  have hFχ : F = C χ * X := by
    rw [eq_X_add_C_of_natDegree_le_one hdeg, hcoeff0, map_zero, add_zero]
  have act_eq_mul : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A))
      (a : A), act A g a = g.ofConv χ * a := by
    intro A _ _ g a
    rw [act_eq, hFχ, map_mul, aevalTower_C, aevalTower_X]
  -- Evaluating the action at `1` for the universal `H`-valued point `AlgHom.id R H` recovers `χ`.
  have act_id_one : act H (toConv (AlgHom.id R H)) 1 = χ := by
    rw [act_eq_mul, ofConv_toConv, AlgHom.id_apply, mul_one]
  have hχ : IsGroupLikeElem R χ := by
    refine ⟨?_, ?_⟩
    · -- The identity point acts trivially, so `algebraMap R H (ε χ) = 1`.
      have h := act_eq_mul H 1 1
      rw [act_one, mul_one, AlgHom.convOne_apply] at h
      exact Bialgebra.algebraMap_injective H (by rw [← h, map_one])
    · -- The action axiom at the two tensor-factor points of `H ⊗[R] H`, whose convolution
      -- product is the comultiplication point, gives `Δ χ = χ ⊗ χ`.
      have h := act_mul (H ⊗[R] H) (toConv Algebra.TensorProduct.includeLeft)
        (toConv Algebra.TensorProduct.includeRight) 1
      rw [← Bialgebra.comulPoint_eq_include_mul, act_eq_mul, act_eq_mul, act_eq_mul, mul_one,
        mul_one, ofConv_toConv, ofConv_toConv, ofConv_toConv, Bialgebra.comulAlgHom_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
      exact h
  refine ⟨⟨χ, hχ⟩, act_eq_mul, fun χ' hχ' => GroupLike.val_injective ?_⟩
  have h := hχ' H (toConv (AlgHom.id R H)) 1
  rwa [act_id_one, ofConv_toConv, AlgHom.id_apply, mul_one, eq_comm] at h

/-- **Actions of reduced affine groups on `𝔾ₐ` by group automorphisms are through characters.**
Let `H` be a commutative Hopf algebra over `R` with reduced underlying ring, and let the groups of
points `H →ₐ[R] A` act on the groups of points of `𝔾ₐ = Spec (SymmetricAlgebra R R)` by group
automorphisms, naturally in `A`. Then there is a unique group-like element `χ` of `H` such that
every point `g` acts on the parameter `a ∈ A` of a point of `𝔾ₐ`
(`TauCeti.AdditiveGroup.gaPointsMulEquiv`) by multiplication by `g χ`. -/
theorem existsUnique_groupLike_mulAut_act_eq_mul_of_naturality [IsReduced H]
    (act : ∀ (A : Type v) [CommSemiring A] [Algebra R A],
      WithConv (H →ₐ[R] A) →* MulAut (WithConv (SymmetricAlgebra R R →ₐ[R] A)))
    (act_mapValue : ∀ (A B : Type v) [CommSemiring A] [Algebra R A] [CommSemiring B]
      [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A))
      (x : WithConv (SymmetricAlgebra R R →ₐ[R] A)),
      AlgHom.mapValue φ (act A g x) = act B (AlgHom.mapValue φ g) (AlgHom.mapValue φ x)) :
    ∃! χ : GroupLike R H,
      ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A))
        (x : WithConv (SymmetricAlgebra R R →ₐ[R] A)),
        gaPointsMulEquiv (act A g x) =
          Multiplicative.ofAdd (g.ofConv χ * Multiplicative.toAdd (gaPointsMulEquiv x)) := by
  -- Transport the action to the parameters of the points of `𝔾ₐ`. For a semiring `A` the
  -- monoid `Multiplicative A` is not a group, so this is done by conjugating with
  -- `gaPointsMulEquiv` rather than through `MulAut.congr`.
  let act' : ∀ (A : Type v) [CommSemiring A] [Algebra R A], WithConv (H →ₐ[R] A) → A → A :=
    fun A _ _ g a => Multiplicative.toAdd
      (gaPointsMulEquiv (act A g (gaPointsMulEquiv.symm (Multiplicative.ofAdd a))))
  have act'_eq : ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g : WithConv (H →ₐ[R] A))
      (x : WithConv (SymmetricAlgebra R R →ₐ[R] A)),
      gaPointsMulEquiv (act A g x) =
        Multiplicative.ofAdd (act' A g (Multiplicative.toAdd (gaPointsMulEquiv x))) := by
    intro A _ _ g x
    simp only [act', ofAdd_toAdd, MulEquiv.symm_apply_apply]
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_groupLike_act_eq_mul_of_naturality act'
    (fun A B _ _ _ _ φ g a => by
      simp only [act', ← toAdd_gaPointsMulEquiv_mapValue, act_mapValue,
        mapValue_gaPointsMulEquiv_symm_apply, toAdd_ofAdd])
    (fun A _ _ a => by
      simp only [act', map_one, MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd])
    (fun A _ _ g h a => by
      simp only [act', map_mul, MulAut.mul_apply, MulEquiv.symm_apply_apply, ofAdd_toAdd])
    (fun A _ _ g => by
      simp only [act', ofAdd_zero, map_one, toAdd_one])
  refine ⟨χ, fun A _ _ g x => by rw [act'_eq, hχ], fun χ' hχ' => huniq χ' fun A _ _ g a => ?_⟩
  have h := hχ' A g (gaPointsMulEquiv.symm (Multiplicative.ofAdd a))
  simp only [act', h, MulEquiv.apply_symm_apply, toAdd_ofAdd]

end AdditiveGroup

end TauCeti
