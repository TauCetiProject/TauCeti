/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Semisimplification
public import TauCeti.RepresentationTheory.OfGL
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.Matrix.Charpoly.IntegralNewton
import TauCeti.RingTheory.Semisimple.Trace.Realization
import TauCeti.LinearAlgebra.LinearIndependent.Evaluation
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Semisimple realization from all trace identities

Over an algebraically closed field of characteristic zero, every function on a group satisfying
all polynomial identities among traces of representations of dimension `n` is the character of
a semisimple representation of that dimension. The hypothesis includes all trace identities;
this is weaker than reconstructing a representation from just the pseudocharacter relations.

The proof extends the function to the group algebra and quotients by the trace-pairing kernel.
Evaluation minors bound the dimension of this quotient. Integral Newton polynomials detect
square-zero elements and give natural multiplicities on idempotents. A Wedderburn decomposition
then realizes the trace, and semisimplification supplies native representation semisimplicity.

## Provenance

The reconstruction adapts `New.exists_rep_of_trace_identities`, `New.linearExtension`,
`New.eval_linearExtension_eq_zero`, `New.pairingKernel` and
`New.finite_quotient_pairingKernel` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). `isSemisimpleRing_traceQuotient` adapts the radical argument
of `New.exists_wedderburn` in
`src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean` in the same source.
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

variable {k G n : Type*} [Field k] [Group G] [Fintype n] [DecidableEq n]

/-- The linear form on `k[G]` that extends `T : G → k`. -/
private noncomputable def linearExtension (T : G → k) : k[G] →ₗ[k] k :=
  (aeval T).toLinearMap ∘ₗ Finsupp.lift _ k G X ∘ₗ (coeffLinearEquiv k).toLinearMap

/-- If `T : G → k` obeys every polynomial identity among traces of homomorphisms `G →* GL n k`, then
its linear extension to `k[G]` obeys every polynomial identity among traces of algebra maps
`k[G] →ₐ[k] Matrix n n k`. -/
private lemma eval_linearExtension_eq_zero {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g : G ↦ (x g).val.trace) B = 0) → eval T B = 0)
    (B : MvPolynomial k[G] k)
    (hB : ∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) :
    eval (linearExtension T) B = 0 := by
  -- Apply `h_identities` to `B` with each variable `X (∑ c g • g)` replaced by `∑ c g • X g`.
  refine (comp_aeval_apply _ (aeval T) B).symm.trans
    (h_identities _ fun ρ ↦ (comp_aeval_apply _ (aeval fun g : G ↦ (ρ g).val.trace) B).trans ?_)
  simpa [Finsupp.sum, lift_apply] using
    hB (MonoidAlgebra.lift k (Matrix n n k) G ((Units.coeHom (Matrix n n k)).comp ρ))

/-- The kernel of the pairing `(x, y) ↦ t (x * y)` on `k[G]`, for a linear form `t` with
`t (x * y) = t (y * x)`; this symmetry makes the kernel a left ideal. -/
private def pairingKernel (t : k[G] →ₗ[k] k) (t_comm : ∀ x y : k[G], t (x * y) = t (y * x)) :
    Ideal k[G] :=
  { toAddSubmonoid := ((mul k k[G]).compr₂ t).ker.toAddSubmonoid
    smul_mem' := fun a x hx ↦ by simp_all [t_comm a, DFunLike.ext_iff, mul_assoc] }

/-- Let `t` be a linear form on `k[G]` that obeys every polynomial identity among traces of algebra
maps `k[G] → Matrix n n k`. Then the quotient of `k[G]` by the kernel of the pairing `t (x * y)` is
finite-dimensional: for `card n ^ 2 + 1` elements `s i`, independent modulo the kernel, the forms
`y ↦ t (s i * y)` would be independent, but their minors `det (t (s i * b j))` are polynomial
identities among traces, and these vanish since the `ρ (s i)` are dependent in every `ρ`. -/
private lemma finite_quotient_pairingKernel (t : k[G] →ₗ[k] k)
    (t_comm : ∀ x y : k[G], t (x * y) = t (y * x)) [hI : (pairingKernel t t_comm).IsTwoSided]
    (h_alg : ∀ B : MvPolynomial k[G] k,
      (∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) → eval t B = 0) :
    Module.Finite k (k[G] ⧸ pairingKernel t t_comm) := by
  let N : ℕ := Fintype.card n * Fintype.card n + 1
  refine rank_lt_aleph0_iff.mp (not_le.mp fun h_inf ↦ ?_)
  obtain ⟨s, hs⟩ : ∃ s : Fin N → k[G], LinearIndependent k (mk (pairingKernel t t_comm) ∘ s) :=
    mk_surjective.comp_left.exists.mp (le_rank_iff.mp (Cardinal.aleph0_le.mp h_inf N))
  have h_ltoFun : LinearMap.ker (ltoFun k k[G] k k) = ⊥ := by aesop
  have h_indep : LinearIndependent k fun (i : Fin N) (y : k[G]) ↦ t (s i * y) :=
    (hs.map' _ (ker_liftQ_eq_bot' _ _ rfl)).map' (ltoFun k k[G] k k) h_ltoFun
  have h_dep (ρ : k[G] →ₐ[k] Matrix n n k) :
      ¬LinearIndependent k fun (i : Fin N) (A : Matrix n n k) ↦ (ρ (s i) * A).trace := by
    intro h
    have hle := (LinearIndependent.of_comp (v := fun i ↦ ρ (s i))
      (pi fun A ↦ traceLinearMap n k k ∘ₗ mulRight k A) h).fintype_card_le_finrank
    simp only [finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin] at hle
    omega
  refine det_eval_eq_zero_iff_not_linearIndependent.mp (fun b ↦ ?_) h_indep
  -- the minor `det (t (s i * b j))` is `t` at a polynomial that vanishes on traces
  have h_det_zero : eval t (of fun i j ↦ X (s i * b j) : Matrix (Fin N) (Fin N) _)ᵀ.det = 0 := by
    refine h_alg _ fun ρ ↦ ?_
    simpa [det_apply, Function.flip_def] using det_eval_eq_zero_iff_not_linearIndependent.mpr
      (h_dep ρ) (ρ ∘ b)
  simpa [det_apply, Function.flip_def] using h_det_zero

private lemma isSemisimpleRing_traceQuotient (t : k[G] →ₗ[k] k)
    (t_comm : ∀ x y : k[G], t (x * y) = t (y * x))
    [hI : (pairingKernel t t_comm).IsTwoSided]
    [Module.Finite k (k[G] ⧸ pairingKernel t t_comm)]
    (τ : k[G] ⧸ pairingKernel t t_comm →ₗ[k] k)
    (hτ : ∀ x, τ (mk (pairingKernel t t_comm) x) = t x)
    (τ_nat : ∀ (l : k) (x : k[G] ⧸ pairingKernel t t_comm),
      (∀ m : ℕ, x ^ (m + 1) = l ^ m • x) → ∃ j : ℕ, τ x = j * l) :
    IsSemisimpleRing (k[G] ⧸ pairingKernel t t_comm) := by
  classical
  let I := pairingKernel t t_comm
  have hzero (x : k[G] ⧸ I) (hx : ∀ y, x * y * x = 0) : x = 0 := by
    obtain ⟨x, rfl⟩ := mk_surjective (I := I) x
    refine eq_zero_iff_mem.mpr ?_
    ext g
    have hsq (m : ℕ) :
        (mk I x * mk I (.single g 1)) ^ (m + 1) =
          (0 : k) ^ m • (mk I x * mk I (.single g 1)) := by
      cases m <;> simp_all [pow_succ', ← mul_assoc]
    obtain ⟨j, hj⟩ := τ_nat 0 (mk I x * mk I (.single g 1)) hsq
    simpa [I, ← map_mul, hτ, LinearMap.compr₂_apply, MonoidAlgebra.lsingle_apply] using hj
  have : IsArtinianRing (k[G] ⧸ I) := IsArtinianRing.of_finite k _
  have : IsNoetherianRing (k[G] ⧸ I) := isNoetherian_of_tower k inferInstance
  have hrad : Ring.jacobson (k[G] ⧸ I) = ⊥ := by
    refine (eq_bot_or_exists_atom_le (Ring.jacobson (k[G] ⧸ I))).resolve_right
      fun ⟨J, hatom, hJ⟩ ↦ ?_
    have kills : Ring.jacobson (k[G] ⧸ I) • J = ⊥ :=
      hatom.lt_iff.1 (FG.of_finite.jacobson_smul_lt hatom.ne_bot)
    apply hatom.ne_bot
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    exact hzero x fun y ↦ kills.le (smul_mem_smul
      (Ideal.mul_mem_right y _ (hJ hx)) hx)
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hrad

private lemma exists_matrix_trace [IsAlgClosed k] [CharZero k] {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ r : G →* GL (Fin (Fintype.card n)) k, ∀ g, (r g).val.trace = T g := by
  classical
  let t : k[G] →ₗ[k] k := linearExtension T
  have h_alg : ∀ B : MvPolynomial k[G] k,
      (∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x ↦ (ρ x).trace) B = 0) → eval t B = 0 :=
    eval_linearExtension_eq_zero h_identities
  have t_comm (x y : k[G]) : t (x * y) = t (y * x) := by
    simpa [trace_mul_comm (m := n) (n := n), sub_eq_zero] using h_alg (X (x * y - y * x))
  let I : Ideal k[G] := pairingKernel t t_comm
  have hI : I.IsTwoSided := ⟨by simp_all [I, pairingKernel, mul_assoc, DFunLike.ext_iff]⟩
  let τ : k[G] ⧸ I →ₗ[k] k := liftQ _ t fun x hx ↦ by
    simpa using LinearMap.congr_fun hx 1
  have hτ (x : k[G]) : τ (mk I x) = t x := rfl
  have τ_nat (l : k) (x : k[G] ⧸ I) (hx : ∀ m : ℕ, x ^ (m + 1) = l ^ m • x) :
      ∃ j : ℕ, τ x = j * l := by
    obtain ⟨x, rfl⟩ := mk_surjective (I := I) x
    have hz : eval t (rename (fun i : ℕ ↦ x ^ i)
        (integralNewtonPolynomial (Fintype.card n + 1) 1)) = 0 := by
      refine h_alg _ fun ρ ↦ ?_
      simpa [eval_rename, Function.comp_def] using
        (ρ x).eval_integralNewtonPolynomial_trace_pow_eq_zero_of_splits (IsAlgClosed.splits _)
    rw [eval_rename] at hz
    exact τ.exists_nat_mul_of_integralNewtonPolynomial_eq_zero hx hz
  have : Module.Finite k (k[G] ⧸ I) := finite_quotient_pairingKernel t t_comm h_alg
  have : IsSemisimpleRing (k[G] ⧸ I) :=
    isSemisimpleRing_traceQuotient t t_comm τ hτ τ_nat
  have hτone : τ 1 = Fintype.card n := by
    have h := h_alg (X 1 - ∑ _ : n, 1) fun ρ ↦ by simp
    rw [← map_one (mk I), hτ]
    simpa [sub_eq_zero] using h
  obtain ⟨m, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (k[G] ⧸ I)
  have := hd
  obtain ⟨φ, hφ⟩ := (τ.comp e.symm.toLinearMap).exists_algHom_trace_eq_pi_matrix
    (fun x y ↦ by simpa using (e.symm x).ind₂ t_comm (e.symm y))
    (fun i ↦ by
      have hi : IsIdempotentElem (Pi.single i
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : k)) :
            Π j, Matrix (Fin (d j)) (Fin (d j)) k) := by
        simp [IsIdempotentElem, ← Pi.single_mul]
      simpa using τ_nat 1 _ (by simp [(hi.map e.symm).pow_succ_eq]))
    (by simpa using hτone)
  let φ' := φ.comp e.toAlgHom
  have hφ' (x : k[G] ⧸ I) : (φ' x).trace = τ x := by simpa [φ'] using hφ (e x)
  let r := MonoidHom.toHomUnits
    (φ'.toMonoidHom.comp ((mk I).toMonoidHom.comp (MonoidAlgebra.of k G)))
  refine ⟨r, fun g ↦ ?_⟩
  simpa [r, hτ, t, linearExtension] using hφ' (mk I (MonoidAlgebra.of k G g))

/-- A function satisfying every polynomial identity among traces in dimension `n` is the
character of a semisimple representation on `kⁿ`. No positivity assumption on `n` is needed. -/
theorem exists_isSemisimpleRepresentation_character_eq_of_trace_identities
    [IsAlgClosed k] [CharZero k] {n : ℕ} {T : G → k}
    (h : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL (Fin n) k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ ρ : Representation k G (Fin n → k), ρ.IsSemisimpleRepresentation ∧ ρ.character = T := by
  classical
  obtain ⟨r, hr⟩ := exists_matrix_trace h
  let ρ := Representation.ofGL r
  have hchar : ρ.character = T := by
    ext g
    simpa [ρ, Representation.character, Matrix.trace_toLin'_eq] using hr g
  let σ := ρ.semisimplification
  have hdim : Module.finrank k (TauCeti.semisimplification k[G] ρ.asModule) = n := by
    apply Nat.cast_injective (R := k)
    have hc := congrFun ρ.char_semisimplification 1
    simpa [Representation.char_one, ρ] using hc
  let e : TauCeti.semisimplification k[G] ρ.asModule ≃ₗ[k] (Fin n → k) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let σ' : Representation k G (Fin n → k) := (e.conjAlgEquiv k).toMonoidHom.comp σ
  have he : σ.Equiv σ' := .mk e fun g ↦ by
    ext v
    simp [σ', LinearEquiv.conjAlgEquiv_apply]
  exact ⟨σ', he.toIntertwiningMap.isSemisimpleRepresentation_of_surjective
    he.toLinearEquiv.surjective,
    (Representation.char_iso he).symm.trans (ρ.char_semisimplification.trans hchar)⟩

/-- Matrix form of semisimple realization from all polynomial trace identities. Semisimplicity
is expressed using the associated native representation on `kⁿ`. -/
theorem exists_gl_trace_eq_of_trace_identities [IsAlgClosed k] [CharZero k] {n : ℕ} {T : G → k}
    (h : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL (Fin n) k, eval (fun g ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ r : G →* GL (Fin n) k,
      (Representation.ofGL r).IsSemisimpleRepresentation ∧ ∀ g, (r g).val.trace = T g := by
  classical
  obtain ⟨ρ, hρ, hchar⟩ := exists_isSemisimpleRepresentation_character_eq_of_trace_identities h
  let r := (Units.map (LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))).toMonoidHom).comp
    ρ.asGroupHom
  have heq : Representation.ofGL r = ρ := by
    ext g v i
    simp [r, Representation.ofGL_apply, LinearMap.toMatrixAlgEquiv_apply,
      Representation.asGroupHom_apply]
  refine ⟨r, heq ▸ hρ, fun g ↦ ?_⟩
  have hg := congrFun hchar g
  simpa [← heq, Representation.character, Matrix.trace_toLin'_eq] using hg

end TauCeti
