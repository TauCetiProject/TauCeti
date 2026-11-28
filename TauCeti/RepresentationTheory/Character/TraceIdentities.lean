/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Semisimplification
public import TauCeti.RepresentationTheory.OfGL
import TauCeti.LinearAlgebra.Matrix.Trace.Realization
import TauCeti.RingTheory.TraceFunctional.Newton
import TauCeti.RingTheory.TraceFunctional.Identities
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import TauCeti.RingTheory.TraceFunctional.Semisimple

/-!
# Semisimple realization from all trace identities

Over an algebraically closed field of characteristic zero, every function on a group satisfying
all polynomial identities among traces of homomorphisms to `GL n k`, for any finite index type
`n`, is the character of a semisimple representation on `n → k`. Empty index types are allowed.
The hypothesis includes all trace identities; this is weaker than reconstructing a representation
from just the pseudocharacter relations.

The proof extends the function to the group algebra and quotients by the trace-pairing kernel.
Evaluation minors bound the dimension of this quotient. Integral Newton polynomials detect
square-zero elements and give natural multiplicities on idempotents. A Wedderburn decomposition
then realizes the trace, and semisimplification supplies native representation semisimplicity.

## Main results

* `TauCeti.exists_isSemisimpleRepresentation_character_eq_of_trace_identities` gives a native
  semisimple representation on `n → k` with the prescribed character.
* `TauCeti.exists_gl_trace_eq_of_trace_identities` gives the corresponding homomorphism to
  `GL n k`, using the same finite index type as the trace identities hypothesis.

## Provenance

The reconstruction adapts `New.exists_rep_of_trace_identities`, `New.linearExtension`,
`New.eval_linearExtension_eq_zero` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC).
The trace radical and quotient trace use `LinearMap.traceRadical` and `LinearMap.quotientTrace`.
The native semisimplification interface is new here.

## References

* R. Taylor, *Galois representations associated to Siegel modular forms of low weight*,
  Duke Math. J. 63 (1991), Theorem 1.
* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

noncomputable section

open Matrix Submodule Fintype Set Algebra Pi Units LinearMap Ideal.Quotient MvPolynomial
open MonoidAlgebra Module
open scoped MonoidAlgebra

namespace TauCeti

variable {k G n : Type*}

section

variable [CommSemiring k] [Monoid G] [Fintype n] [DecidableEq n]

/-- The linear form on `k[G]` that extends `T : G → k`. -/
private noncomputable def linearExtension (T : G → k) : k[G] →ₗ[k] k :=
  Finsupp.linearCombination k T ∘ₗ (coeffLinearEquiv k).toLinearMap

-- `MonoidAlgebra.of` simplifies to `single`, so use that normal form for the generator rule.
omit [Monoid G] in
@[simp]
private lemma linearExtension_of (T : G → k) (g : G) :
    linearExtension T (MonoidAlgebra.single g (1 : k)) = T g := by
  simp [linearExtension]

/-- If `T : G → k` obeys every polynomial identity among traces of homomorphisms `G →* GL n k`, then
its linear extension to `k[G]` obeys every polynomial identity among traces of algebra maps
`k[G] →ₐ[k] Matrix n n k`. -/
private lemma eval_linearExtension_eq_zero {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g : G ↦ (x g).val.trace) B = 0) → eval T B = 0)
    (B : MvPolynomial k[G] k)
    (hB : ∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) :
    eval (linearExtension T) B = 0 := by
  let S : k[G] →ₗ[k] MvPolynomial G k :=
    Finsupp.linearCombination k X ∘ₗ (coeffLinearEquiv k).toLinearMap
  have hT : (aeval T).toLinearMap ∘ₗ S = linearExtension T := by
    have hX : ⇑(aeval T).toLinearMap ∘ (X : G → MvPolynomial G k) = T :=
      funext fun g ↦ aeval_X T g
    rw [← LinearMap.comp_assoc, ← Finsupp.linearCombination_linear_comp, hX]
    rfl
  have hρ (ρ : G →* GL n k) :
      (aeval fun g ↦ (ρ g).val.trace).toLinearMap ∘ₗ S =
        traceLinearMap n k k ∘ₗ
          (MonoidAlgebra.lift k (Matrix n n k) G
            ((Units.coeHom (Matrix n n k)).comp ρ)).toLinearMap := by
    ext g
    simp [S]
  have hcomp (f : G → k) :
      eval ((aeval f).toLinearMap ∘ₗ S) B = eval f (aeval S B) := by
    simpa only [LinearMap.coe_comp, Function.comp_def, AlgHom.toLinearMap_apply,
      aeval_eq_eval] using (comp_aeval_apply S (aeval f) B).symm
  rw [← hT, hcomp]
  refine h_identities _ fun ρ ↦ ?_
  rw [← hcomp, hρ]
  simpa only [LinearMap.coe_comp, Function.comp_def, AlgHom.toLinearMap_apply,
    traceLinearMap_apply] using hB (MonoidAlgebra.lift k (Matrix n n k) G
      ((Units.coeHom (Matrix n n k)).comp ρ))

end

variable [Field k] [Group G] [Fintype n] [DecidableEq n]

private lemma exists_matrix_trace [IsAlgClosed k] [CharZero k] {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ r : G →* GL n k, ∀ g, (r g).val.trace = T g := by
  classical
  let t : k[G] →ₗ[k] k := linearExtension T
  have h_alg : ∀ B : MvPolynomial k[G] k,
      (∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x ↦ (ρ x).trace) B = 0) → eval t B = 0 :=
    eval_linearExtension_eq_zero h_identities
  have t_comm (x y : k[G]) : t (x * y) = t (y * x) := by
    simpa [trace_mul_comm (m := n) (n := n), sub_eq_zero] using h_alg (X (x * y - y * x))
  let I : Ideal k[G] := t.traceRadical t_comm
  let τ : k[G] ⧸ I →ₗ[k] k := t.quotientTrace t_comm
  have hτ (x : k[G]) : τ (mk I x) = t x := t.quotientTrace_mk t_comm x
  have τ_nat (l : k) (x : k[G] ⧸ I) (hx : x * x = l • x) :
      ∃ j : ℕ, j ≤ Fintype.card n ∧ τ x = j * l :=
    τ.exists_nat_mul_of_integralNewtonPolynomial_eq_zero hx
      (t.eval_integralNewtonPolynomial_quotientTrace_eq_zero t_comm h_alg x)
  have : Module.Finite k (k[G] ⧸ I) :=
    t.finite_quotient_traceRadical_of_trace_identities t_comm h_alg
  have : IsArtinianRing (k[G] ⧸ I) := IsArtinianRing.of_finite k _
  have : IsSemisimpleRing (k[G] ⧸ I) :=
    t.isSemisimpleRing_quotient_traceRadical t_comm fun x hx ↦ by
      obtain ⟨j, -, hj⟩ := τ_nat 0 x (by simpa using hx)
      simpa using hj
  have hτone : τ 1 = Fintype.card n := by
    have h := h_alg (X 1 - ∑ _ : n, 1) fun ρ ↦ by simp
    rw [t.quotientTrace_one t_comm]
    simpa [sub_eq_zero] using h
  obtain ⟨m, d, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (k[G] ⧸ I)
  obtain ⟨φ, hφ⟩ := (τ.comp e.symm.toLinearMap).exists_algHom_trace_eq_pi_matrix
    (N := n)
    (fun x y ↦ by simpa using t.quotientTrace_mul_comm t_comm (e.symm x) (e.symm y)) (fun _ ↦ 0)
    (fun i ↦ by
      have hi : IsIdempotentElem (Pi.single i
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : k)) :
            Π j, Matrix (Fin (d j)) (Fin (d j)) k) := by
        simp [IsIdempotentElem, ← Pi.single_mul]
      obtain ⟨j, -, hj⟩ := τ_nat 1 _ (by simpa using (hi.map e.symm).eq)
      exact ⟨j, by simpa using hj⟩)
    (by simpa using hτone)
  let φ' := φ.comp e.toAlgHom
  have hφ' (x : k[G] ⧸ I) : (φ' x).trace = τ x := by simpa [φ'] using hφ (e x)
  let r := MonoidHom.toHomUnits
    (φ'.toMonoidHom.comp ((mk I).toMonoidHom.comp (MonoidAlgebra.of k G)))
  refine ⟨r, fun g ↦ ?_⟩
  simpa [r, hτ, t] using hφ' (mk I (MonoidAlgebra.of k G g))

/-- A function satisfying every polynomial identity among traces of homomorphisms to `GL n k`
is the character of a semisimple representation on `n → k`. The finite type `n` may be empty. -/
theorem exists_isSemisimpleRepresentation_character_eq_of_trace_identities
    [IsAlgClosed k] [CharZero k] {T : G → k}
    (h : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ ρ : Representation k G (n → k), ρ.IsSemisimpleRepresentation ∧ ρ.character = T := by
  classical
  obtain ⟨r, hr⟩ := exists_matrix_trace h
  let ρ := Representation.ofGL r
  have hchar : ρ.character = T := by
    ext g
    simpa [ρ, Representation.character, Matrix.trace_toLin'_eq] using hr g
  let σ := ρ.semisimplification
  have hdim : Module.finrank k (TauCeti.semisimplification k[G] ρ.asModule) = Fintype.card n := by
    apply Nat.cast_injective (R := k)
    have hc := congrFun ρ.char_semisimplification 1
    simpa [Representation.char_one, ρ] using hc
  let e : TauCeti.semisimplification k[G] ρ.asModule ≃ₗ[k] (n → k) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let σ' : Representation k G (n → k) := (e.conjAlgEquiv k).toMonoidHom.comp σ
  have he : σ.Equiv σ' := .mk e fun g ↦ by
    ext v
    simp [σ', LinearEquiv.conjAlgEquiv_apply]
  refine ⟨σ', he.toIntertwiningMap.isSemisimpleRepresentation_of_surjective
    he.toLinearEquiv.surjective, ?_⟩
  simpa only [← Representation.char_iso he, σ, ρ.char_semisimplification] using hchar

/-- Matrix form of semisimple realization from all polynomial trace identities. Semisimplicity
is expressed using the associated native representation on `n → k`, for any finite type `n`. -/
theorem exists_gl_trace_eq_of_trace_identities [IsAlgClosed k] [CharZero k] {T : G → k}
    (h : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ r : G →* GL n k,
      (Representation.ofGL r).IsSemisimpleRepresentation ∧ ∀ g, (r g).val.trace = T g := by
  classical
  obtain ⟨ρ, hρ, hchar⟩ := exists_isSemisimpleRepresentation_character_eq_of_trace_identities h
  let r := (Units.map (LinearMap.toMatrixAlgEquiv (Pi.basisFun k n)).toMonoidHom).comp
    ρ.asGroupHom
  have heq : Representation.ofGL r = ρ := by
    ext g v i
    simp [r, Representation.ofGL_apply, LinearMap.toMatrixAlgEquiv_apply,
      Representation.asGroupHom_apply]
  refine ⟨r, heq ▸ hρ, fun g ↦ ?_⟩
  have hg := congrFun hchar g
  simpa [← heq, Representation.character, Matrix.trace_toLin'_eq] using hg

end TauCeti
