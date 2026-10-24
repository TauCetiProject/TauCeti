/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.DotOrbit
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Translation
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
-- Non-public: an element of `S(H)` is determined by its values over the infinite field `K`, used
-- only in the comparison with the invariants of the coroot representation.
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# The linear Harish-Chandra projection and the Weyl invariants

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its root system, with Weyl
vector `ρ`. The Harish-Chandra projection `TauCeti.hcProjection b : Z(U(L)) →ₐ[K] S(H)` reads the
central character `χ_λ` as the polynomial function `λ ↦ χ_λ(z)` on the weights, and these functions
are invariant under the **dot action** `w · λ = w(λ + ρ) - ρ` of the Weyl group
(`TauCeti.hcProjection_mem_dotInvariants`). This file passes to the **linear** normalization, in
which the invariance is under the ordinary linear action of the Weyl group on the weights.

The passage is translation by `-ρ`, `TauCeti.SymmetricAlgebra.translation`, the automorphism of
`S(H)` with `(translation μ p)(λ) = p(λ + μ)`. Since `w · (λ - ρ) = w λ - ρ`, translation by `-ρ`
carries the dot-invariants `S(H)^{W·}` (`TauCeti.dotInvariants`) onto the linear invariants
`S(H)^W` (`TauCeti.linearInvariants`), the polynomial functions `p` with `p(w λ) = p(λ)`; this is
`TauCeti.dotInvariantsEquivLinearInvariants`. Like the dot-invariants, `S(H)^W` is defined by
evaluation at the weights; since the action is now linear, it is also the invariant subalgebra of
the action of the Weyl group on `H`, the coroot space
(`TauCeti.linearInvariants_eq_symmetricAlgebraInvariants`). The **linear Harish-Chandra
projection**

`TauCeti.hcProjectionLinear b = translation (-ρ) ∘ hcProjection b : Z(U(L)) →ₐ[K] S(H)`

therefore lands in `S(H)^W`, and the central character is its value at the `ρ`-shifted weight:

`χ_λ(z) = (hcProjection b z)(λ) = (hcProjectionLinear b z)(λ + ρ)`.

These two equations fix the sign of the shift. The linear normalization is the one in which the
Harish-Chandra isomorphism `Z(U(L)) ≃ S(H)^W` is compared with the Chevalley restriction theorem
for `S(L)^L`: there the Weyl group acts linearly, so this is the form in which the two are matched.
That the projection is onto, and so an isomorphism onto the invariants, is not proved here.

## Main definitions

* `TauCeti.linearInvariants H`: the Weyl invariants `S(H)^W`, the elements `p` of `S(H)` with
  `p(w λ) = p(λ)` for every Weyl group element `w` and weight `λ`.
* `TauCeti.dotInvariantsEquivLinearInvariants b`: translation by `-ρ`, as an algebra isomorphism
  from the dot-invariants onto the Weyl invariants.
* `TauCeti.hcProjectionLinear b`: the linear Harish-Chandra projection
  `Z(U(L)) →ₐ[K] S(H)`, the Harish-Chandra projection followed by translation by `-ρ`.

## Main results

* `TauCeti.linearInvariants_eq_symmetricAlgebraInvariants`: the Weyl invariants are the invariants
  of the coroot representation `RootPairing.weylGroupCorootRep` on `H`.
* `TauCeti.translation_neg_weylVector_mem_linearInvariants_iff`: translation by `-ρ` takes an
  element of `S(H)` to a Weyl invariant exactly when the element is dot-invariant.
* `TauCeti.lift_hcProjectionLinear` and `TauCeti.lift_add_weylVector_hcProjectionLinear`: the
  value of the linear projection at `λ` is the central character of `λ - ρ`; equivalently,
  `χ_λ(z)` is its value at `λ + ρ`.
* `TauCeti.hcProjectionLinear_mem_linearInvariants`: the linear projection takes values in the
  Weyl invariants.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3, where
  the Harish-Chandra homomorphism is the projection followed by the translation by `-ρ`.
* J. E. Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category `O`*, Chapter 1,
  on Harish-Chandra's theorem.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module TauCeti.SymmetricAlgebra

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-! ### The Weyl invariants -/

variable (H) in
/-- **The Weyl invariants** `S(H)^W`: the elements `p` of the symmetric algebra `S(H)`, read as
polynomial functions on the weights `H*`, with `p(w lam) = p(lam)` for every Weyl group element `w`
and every weight `lam`, where `w lam` is the linear action. -/
noncomputable def linearInvariants : Subalgebra K (_root_.SymmetricAlgebra K H) where
  carrier := {p | ∀ (w : (IsKilling.rootSystem H).weylGroup) (lam : Dual K H),
    _root_.SymmetricAlgebra.lift (w • lam) p = _root_.SymmetricAlgebra.lift lam p}
  mul_mem' hp hq w lam := by simp only [map_mul, hp w lam, hq w lam]
  add_mem' hp hq w lam := by simp only [map_add, hp w lam, hq w lam]
  algebraMap_mem' r w lam := by simp only [AlgHom.commutes]

/-- Membership in the Weyl invariants: `p(w lam) = p(lam)` for every Weyl group element `w` and
every weight `lam`. -/
@[simp]
theorem mem_linearInvariants_iff {p : _root_.SymmetricAlgebra K H} :
    p ∈ linearInvariants H ↔ ∀ (w : (IsKilling.rootSystem H).weylGroup) (lam : Dual K H),
      _root_.SymmetricAlgebra.lift (w • lam) p = _root_.SymmetricAlgebra.lift lam p :=
  Iff.rfl

/-! ### Comparison with the invariants of the coroot representation -/

/-- The linear action of a Weyl group element `w` on a weight is the transpose of the action of its
opposite on `H`, the coroot space of the root system: `(w lam) h = lam (w h)`. The two actions are
Mathlib's actions of the automorphisms of a root pairing, through `weightEquiv` on weights and
`coweightEquiv` on coweights, so this is their transposition law
`RootPairing.Equiv.toLinearMap_weightEquiv`, read through the defining equations of those actions
and the evaluation pairing of `LieAlgebra.IsKilling.rootSystem H` (Mathlib states no separate
lemma unfolding either action). -/
private theorem smul_apply_eq_apply_op_smul (w : (IsKilling.rootSystem H).weylGroup)
    (lam : Dual K H) (h : H) :
    (w • lam) h = lam ((⟨MulOpposite.op (w : (IsKilling.rootSystem H).Aut), w.2⟩ :
      (IsKilling.rootSystem H).weylGroup.op) • h) :=
  RootPairing.Equiv.toLinearMap_weightEquiv (w : (IsKilling.rootSystem H).Aut) lam h

/-- **The Weyl invariants are the invariants of the coroot representation**: `S(H)^W`, defined by
evaluation at the weights, is the invariant subalgebra of `S(H)` under the representation
`RootPairing.weylGroupCorootRep` of the Weyl group on `H`. In particular it inherits the
invariant-theoretic API of `Representation.symmetricAlgebraInvariants`, such as its homogeneity. -/
theorem linearInvariants_eq_symmetricAlgebraInvariants :
    linearInvariants H =
      (IsKilling.rootSystem H).weylGroupCorootRep.symmetricAlgebraInvariants := by
  -- evaluating the coroot translate by `w` at `lam` is evaluating at the weight translate `w lam`
  have key (w : (IsKilling.rootSystem H).weylGroup) (lam : Dual K H)
      (p : _root_.SymmetricAlgebra K H) :
      _root_.SymmetricAlgebra.lift lam
          ((IsKilling.rootSystem H).weylGroupCorootRep.symmetricAlgebra
            ⟨MulOpposite.op (w : (IsKilling.rootSystem H).Aut), w.2⟩ p) =
        _root_.SymmetricAlgebra.lift (w • lam) p := by
    rw [Representation.symmetricAlgebra_apply, ← AlgHom.comp_apply]
    congr 1
    refine _root_.SymmetricAlgebra.algHom_ext <| LinearMap.ext fun h ↦ ?_
    simp [RootPairing.weylGroupCorootRep, smul_apply_eq_apply_op_smul]
  ext p
  rw [mem_linearInvariants_iff, Representation.mem_symmetricAlgebraInvariants]
  refine ⟨fun hp g ↦ ?_, fun hp w lam ↦ ?_⟩
  · obtain ⟨g, hg⟩ := g
    exact eq_of_forall_lift_apply_eq fun lam ↦ (key ⟨g.unop, hg⟩ lam p).trans (hp _ lam)
  · rw [← key, hp]

/-! ### From dot-invariants to Weyl invariants -/

variable (b : (IsKilling.rootSystem H).Base)

/-- **Translation by `-ρ` turns dot-invariance into Weyl invariance**: `translation (-ρ) p` is a
Weyl invariant exactly when `p` is dot-invariant. The reason is the identity
`w · (lam - ρ) = w lam - ρ`. -/
theorem translation_neg_weylVector_mem_linearInvariants_iff {p : _root_.SymmetricAlgebra K H} :
    translation (-weylVector (IsKilling.rootSystem H) b) p ∈ linearInvariants H ↔
      p ∈ dotInvariants b := by
  simp only [mem_linearInvariants_iff, mem_dotInvariants_iff, lift_translation,
    Algebra.linearMap_self, LinearMap.id_comp, ← sub_eq_add_neg]
  refine ⟨fun h w lam ↦ ?_, fun h w lam ↦ ?_⟩
  · simpa [dotAction_def] using h w (lam + weylVector (IsKilling.rootSystem H) b)
  · simpa [dotAction_def] using h w (lam - weylVector (IsKilling.rootSystem H) b)

/-- Translation by `-ρ` carries the dot-invariants onto the Weyl invariants. -/
theorem map_translation_neg_weylVector_dotInvariants :
    (dotInvariants b).map
        (translation (-weylVector (IsKilling.rootSystem H) b) :
          _root_.SymmetricAlgebra K H →ₐ[K] _root_.SymmetricAlgebra K H) =
      linearInvariants H := by
  ext q
  refine ⟨?_, fun hq ↦ ⟨(translation (-weylVector (IsKilling.rootSystem H) b)).symm q, ?_, ?_⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact (translation_neg_weylVector_mem_linearInvariants_iff b).2 hp
  · exact (translation_neg_weylVector_mem_linearInvariants_iff b).1 <| by
      rwa [AlgEquiv.apply_symm_apply]
  · exact AlgEquiv.apply_symm_apply _ q

/-- **The dot-invariants are isomorphic to the Weyl invariants**, by translation by `-ρ`:
`p ↦ (lam ↦ p(lam - ρ))`. -/
noncomputable def dotInvariantsEquivLinearInvariants :
    dotInvariants b ≃ₐ[K] linearInvariants H :=
  ((translation (-weylVector (IsKilling.rootSystem H) b)).subalgebraMap (dotInvariants b)).trans
    (Subalgebra.equivOfEq _ _ (map_translation_neg_weylVector_dotInvariants b))

/-- The isomorphism from the dot-invariants to the Weyl invariants is translation by `-ρ`. -/
@[simp]
theorem coe_dotInvariantsEquivLinearInvariants_apply (p : dotInvariants b) :
    (dotInvariantsEquivLinearInvariants b p : _root_.SymmetricAlgebra K H) =
      translation (-weylVector (IsKilling.rootSystem H) b) p :=
  (rfl)

/-- The inverse isomorphism, from the Weyl invariants to the dot-invariants, is translation by
`ρ`. -/
@[simp]
theorem coe_dotInvariantsEquivLinearInvariants_symm_apply (q : linearInvariants H) :
    ((dotInvariantsEquivLinearInvariants b).symm q : _root_.SymmetricAlgebra K H) =
      translation (weylVector (IsKilling.rootSystem H) b) q := by
  have h := congrArg Subtype.val ((dotInvariantsEquivLinearInvariants b).apply_symm_apply q)
  rw [coe_dotInvariantsEquivLinearInvariants_apply] at h
  rw [← h, translation_translation, neg_add_cancel, translation_zero]
  rfl

/-! ### The linear Harish-Chandra projection -/

/-- **The linear Harish-Chandra projection** `Z(U(L)) →ₐ[K] S(H)`: the Harish-Chandra projection
`TauCeti.hcProjection b` followed by translation by `-ρ`, so that its value at a central element
`z` is the polynomial function `lam ↦ χ_{lam - ρ}(z)` (`TauCeti.lift_hcProjectionLinear`). It
takes values in the Weyl invariants (`TauCeti.hcProjectionLinear_mem_linearInvariants`). -/
noncomputable def hcProjectionLinear :
    Subalgebra.center K (U L) →ₐ[K] _root_.SymmetricAlgebra K H :=
  (translation (-weylVector (IsKilling.rootSystem H) b)).toAlgHom.comp (hcProjection b)

/-- The linear Harish-Chandra projection is the Harish-Chandra projection translated by `-ρ`. -/
theorem hcProjectionLinear_apply (z : Subalgebra.center K (U L)) :
    hcProjectionLinear b z =
      translation (-weylVector (IsKilling.rootSystem H) b) (hcProjection b z) :=
  (rfl)

/-- **The value of the linear Harish-Chandra projection** at a weight `lam` is the central
character of `lam - ρ`. -/
@[simp]
theorem lift_hcProjectionLinear (lam : Dual K H) (z : Subalgebra.center K (U L)) :
    _root_.SymmetricAlgebra.lift lam (hcProjectionLinear b z) =
      vermaCentralCharacter b (lam - weylVector (IsKilling.rootSystem H) b) z := by
  rw [hcProjectionLinear_apply, lift_translation, Algebra.linearMap_self, LinearMap.id_comp,
    ← sub_eq_add_neg, lift_hcProjection]

/-- **The central character through the linear Harish-Chandra projection**: `χ_lam(z)` is the
value of `hcProjectionLinear b z` at `lam + ρ`. -/
theorem lift_add_weylVector_hcProjectionLinear (lam : Dual K H) (z : Subalgebra.center K (U L)) :
    _root_.SymmetricAlgebra.lift (lam + weylVector (IsKilling.rootSystem H) b)
        (hcProjectionLinear b z) =
      vermaCentralCharacter b lam z := by
  rw [lift_hcProjectionLinear, add_sub_cancel_right]

/-- **The linear Harish-Chandra projection takes values in the Weyl invariants.** -/
theorem hcProjectionLinear_mem_linearInvariants (z : Subalgebra.center K (U L)) :
    hcProjectionLinear b z ∈ linearInvariants H :=
  (translation_neg_weylVector_mem_linearInvariants_iff b).2 (hcProjection_mem_dotInvariants z)

end TauCeti
