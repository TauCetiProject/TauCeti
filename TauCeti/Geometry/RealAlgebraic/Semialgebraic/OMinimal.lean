/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sign
public import TauCeti.Data.Finset.Max
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.ModelTheory.OMinimal.Basic

/-!
# The semialgebraic o-minimal structure

Over a real closed field `R` whose semialgebraic sets are closed under coordinate projection, the
semialgebraic sets are the definable sets of an o-minimal structure,
`TauCeti.OMinimalStructure.semialgebraic R`. For `R = ℝ` projection closure is the
Tarski–Seidenberg theorem, the instance `TauCeti.HasSemialgebraicProjections ℝ` proved by
cylindrical algebraic decomposition, so the semialgebraic sets form an o-minimal structure on `ℝ`.

The one-variable condition is `TauCeti.isSemialgebraic_fin_one_iff`: a subset of `R` is
semialgebraic exactly when it is a finite union of points and open intervals with endpoints in
`R ∪ {±∞}`. A semialgebraic subset of `R` is a sign condition on finitely many polynomials, and
between consecutive roots of these polynomials their signs are constant. Over `ℚ` the
one-variable condition fails: `{x | x ^ 2 < 2}` is semialgebraic but its endpoints `±√2` are not
rational.

## Main results

* `TauCeti.isSemialgebraic_fin_one_iff`: the semialgebraic subsets of `Fin 1 → R` are the finite
  unions of points and open intervals.
* `TauCeti.OMinimalStructure.semialgebraic`: the o-minimal structure of semialgebraic sets.
* `TauCeti.OMinimalStructure.definable_semialgebraic_iff`: its definable sets are the semialgebraic
  sets.

## References

L. van den Dries, *Tame Topology and o-minimal Structures*, London Mathematical Society Lecture
Note Series 248, Cambridge University Press, 1998, Chapter 2.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {R : Type*}

/-- A finite union of points and open intervals of `R`, with endpoints in `R ∪ {±∞}`, is a
semialgebraic subset of `Fin 1 → R`. -/
theorem isSemialgebraic_setOf_mem_or_exists_lt_lt [CommRing R] [LinearOrder R]
    [IsOrderedAddMonoid R] (F : Finset R) (J : Finset (WithBot R × WithTop R)) :
    IsSemialgebraic {x : Fin 1 → R |
      x 0 ∈ F ∨ ∃ p ∈ J, p.1 < (x 0 : WithBot R) ∧ (x 0 : WithTop R) < p.2} := by
  have hlow (a : WithBot R) : IsSemialgebraic {x : Fin 1 → R | a < (x 0 : WithBot R)} := by
    cases a with
    | bot => simp
    | coe a => simpa using isSemialgebraic_eval_lt (C a : MvPolynomial (Fin 1) R) (X 0)
  have hupp (b : WithTop R) : IsSemialgebraic {x : Fin 1 → R | (x 0 : WithTop R) < b} := by
    cases b with
    | top => simp
    | coe b => simpa using isSemialgebraic_eval_lt (X 0 : MvPolynomial (Fin 1) R) (C b)
  have : {x : Fin 1 → R |
      x 0 ∈ F ∨ ∃ p ∈ J, p.1 < (x 0 : WithBot R) ∧ (x 0 : WithTop R) < p.2} =
      (⋃ t ∈ (F : Set R), {x | eval x (X 0 - C t) = 0}) ∪
        ⋃ p ∈ (J : Set (WithBot R × WithTop R)),
          {x : Fin 1 → R | p.1 < (x 0 : WithBot R)} ∩ {x | (x 0 : WithTop R) < p.2} := by
    ext x
    simp only [mem_ofPred_eq, Prod.exists]
    simp [sub_eq_zero, and_left_comm]
  rw [this]
  exact (IsSemialgebraic.biUnion F.finite_toSet fun t _ => isSemialgebraic_eval_eq_zero _).union
    (IsSemialgebraic.biUnion J.finite_toSet fun p _ => (hlow p.1).inter (hupp p.2))

section RealClosed

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Semialgebraic subsets of `R`.** Over a real closed field, a subset of `Fin 1 → R` is
semialgebraic if and only if it is a finite union of points and open intervals with endpoints in
`R ∪ {−∞}` and `R ∪ {+∞}`. -/
theorem isSemialgebraic_fin_one_iff {s : Set (Fin 1 → R)} :
    IsSemialgebraic s ↔ ∃ (F : Finset R) (J : Finset (WithBot R × WithTop R)),
      s = {x | x 0 ∈ F ∨ ∃ p ∈ J, p.1 < (x 0 : WithBot R) ∧ (x 0 : WithTop R) < p.2} := by
  classical
  refine ⟨fun hs => ?_, fun ⟨F, J, hs⟩ => hs ▸ isSemialgebraic_setOf_mem_or_exists_lt_lt F J⟩
  obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
  -- Write each `p i` as a univariate polynomial `q i`, and let `Z` be their roots.
  obtain ⟨q, hq⟩ : ∃ q : Fin m → Polynomial R, ∀ i (x : Fin 1 → R),
      eval x (p i) = (q i).eval (x 0) :=
    ⟨fun i => uniqueAlgEquiv R (Fin 1) (p i), fun i x => by
      simpa using (eval₂_uniqueAlgEquiv (f := p i) (φ := RingHom.id R) (a := x)).symm⟩
  let Z : Finset R := Finset.univ.biUnion fun i => (q i).roots.toFinset
  -- On an interval meeting no root, the signs of the `p i` are constant.
  have hsign {t u : R} (htu : ∀ z ∈ Z, z ∉ uIcc t u) (i : Fin m) :
      SignType.sign ((q i).eval u) = SignType.sign ((q i).eval t) := by
    by_cases hqi : q i = 0
    · simp [hqi]
    exact ((q i).sign_eval_eq_of_forall_mem_uIcc fun y hy hy0 =>
      htu y (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp [hqi, hy0]⟩) hy).symm
  set s := {x : Fin 1 → R | Φ fun i => SignType.sign (eval x (p i))}
  have hconst (t : R) : (fun _ => t : Fin 1 → R) ∈ s ↔ Φ fun i => SignType.sign ((q i).eval t) := by
    simp [s, hq]
  have hx (x : Fin 1 → R) : (fun _ => x 0 : Fin 1 → R) = x := funext (Fin.forall_fin_one.2 rfl)
  refine ⟨Z.filter fun t => (fun _ => t : Fin 1 → R) ∈ s,
    ((insert ⊥ (Z.image (↑))) ×ˢ (insert ⊤ (Z.image (↑)))).filter fun p =>
      ∀ t : R, p.1 < t → (t : WithTop R) < p.2 → (fun _ => t : Fin 1 → R) ∈ s, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_product, mem_ofPred_eq, Prod.exists]
  constructor
  · intro hxs
    by_cases hZ : x 0 ∈ Z
    · exact Or.inl ⟨hZ, (hx x).symm ▸ hxs⟩
    obtain ⟨a, ha, b, hb, hat, htb, hab⟩ := Finset.exists_lt_lt_forall_notMem_uIcc hZ
    refine Or.inr ⟨a, b, ⟨⟨ha, hb⟩, fun u hau hub => ?_⟩, hat, htb⟩
    rw [hconst, funext (hsign (hab u hau hub))]
    simpa [s, hq] using hxs
  · rintro (⟨-, h⟩ | ⟨a, b, ⟨-, h⟩, hat, htb⟩)
    · exact hx x ▸ h
    · exact hx x ▸ h _ hat htb

end RealClosed

namespace OMinimalStructure

variable (R) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  [HasSemialgebraicProjections R]

/-- **The semialgebraic o-minimal structure.** Over a real closed field whose semialgebraic sets
are closed under coordinate projection, such as `ℝ` by the Tarski–Seidenberg theorem, the
semialgebraic sets form an o-minimal structure. -/
noncomputable def semialgebraic : OMinimalStructure R where
  Definable' _ s := IsSemialgebraic s
  isSetAlgebra' _ := isSetAlgebra_setOf_isSemialgebraic
  definable_setOf_tail_mem' hs := hs.preimage_tail
  definable_setOf_init_mem' hs := hs.preimage_comp Fin.castSucc
  definable_setOf_eq' _ i j := by simpa using isSemialgebraic_eval_eq (X i : MvPolynomial _ R) (X j)
  definable_setOf_lt' := by simpa using isSemialgebraic_eval_lt (X 0 : MvPolynomial (Fin 2) R) (X 1)
  definable_image_tail' hs := HasSemialgebraicProjections.isSemialgebraic_image_tail hs
  definable_one_iff' := isSemialgebraic_fin_one_iff

variable {R} in
/-- The definable sets of the semialgebraic o-minimal structure are the semialgebraic sets. -/
@[simp]
theorem definable_semialgebraic_iff {n : ℕ} {s : Set (Fin n → R)} :
    (semialgebraic R).Definable n s ↔ IsSemialgebraic s :=
  (semialgebraic R).definable_def

end OMinimalStructure

end TauCeti
