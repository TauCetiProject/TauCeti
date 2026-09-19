/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.PrimeKernel
-- Proof-only: rationality of torsion over an algebraically closed base.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.AlgClosed
-- Proof-only: `sepDeg [n] = n ²` for `n` invertible in the base field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# The kernel of `[n]` has `n ²` points

`Isogeny.ker` counts only the base field's points, so its order equals the degree exactly when the
geometric kernel is **rational** and the isogeny is **separable**: an inseparable isogeny has
strictly fewer geometric kernel points than its degree even over an algebraically closed field.
Separability of `[n]` is `n` being invertible in the base. Rationality is the other hypothesis, and
it is the one that decides how general the statement is.

So the count is proved once with rationality as a hypothesis, and a closure assumption enters only
in a corollary. An algebraically closed base gives rationality outright — no extension of it
carries new torsion — which is `card_ker_mulByIntIsogeny` below. Keeping the hypothesis explicit is
what lets the count be read at a base where the torsion is rational for some other reason, without
the argument being repeated.

The count is made on embeddings, as for `1 − π_q`: an isogeny here has no map on points. Two
embeddings of `K(W)` over the pulled-back field move the tautological point of `[n]`, which is
`n` times the generic point, to the same place, so the two images of the generic point differ by an
`n`-torsion point — and rationality is exactly what puts that difference in the kernel. An embedding
is determined by where it sends the generic point, so that assignment is injective into the kernel,
and the separable degree is the number of embeddings.

The extension rationality is needed over is `AlgebraicClosure W.FunctionField`, because
`Field.Emb K L` is `L →ₐ[K] AlgebraicClosure K`: the embeddings being counted land in the algebraic
closure of the pulled-back field, so that is where the torsion difference lives.

## Main results

* `TauCeti.Isogeny.card_ker_mulByIntIsogeny_of_torsion_rational`: **`#ker [n] = n ²`** whenever the
  geometric `n`-torsion is rational and `n` is invertible.
* `TauCeti.Isogeny.card_ker_mulByIntIsogeny`: the same over an algebraically closed field.
* `TauCeti.Isogeny.card_ker_mulByPrimeIsogeny_of_torsion_rational`: the same at a prime, as `ℓ ²`
  rather than `(ℓ : ℤ).natAbs ^ 2`.
* `TauCeti.Isogeny.card_ker_mulByPrimeIsogeny`: its algebraically closed corollary.

The three steps of the argument sketched above — the torsion difference, its rationality, and the
resulting bound on embeddings — are `private`; nothing outside this module uses them.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

omit [DecidableEq F] in
/-- **Two homomorphisms agreeing on the pulled-back field move the generic point by an `n`-torsion
difference.** Their images of the tautological point of `[n]` agree, and that point is `n` times
the generic point. -/
private theorem zsmul_map_sub_map_genericPoint_eq_zero {Ω : Type*} [Field Ω] [DecidableEq Ω]
    [Algebra F Ω] {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (σ τ : W.FunctionField →ₐ[F] Ω)
    (h : ∀ z ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange, σ z = τ z) :
    n • (Point.map σ (genericPoint W) - Point.map τ (genericPoint W)) = 0 := by
  have hmem : ∀ x : W.CoordinateRing,
      (mulByIntIsogeny W hn).pullback x ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange := fun x ↦
    AlgHom.mem_fieldRange.2 ⟨algebraMap W.CoordinateRing W.FunctionField x,
      (mulByIntIsogeny W hn).fieldPullback_algebraMap x⟩
  have key := CoordinatePullback.map_tautologicalPoint_eq_of_apply_eq
    (mulByIntIsogeny W hn).pullback σ τ (h _ (hmem _)) (h _ (hmem _))
  rw [mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, map_zsmul, map_zsmul] at key
  rw [zsmul_sub, key, sub_self]

omit [DecidableEq F] [W.IsElliptic] in
/-- A division polynomial that does not vanish forces a nonzero index: `ψ₀ = 0`. -/
private theorem ne_zero_of_psiFunctionField_ne_zero {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    n ≠ 0 := by
  rintro rfl
  exact hn (by simp [psiFunctionField_def, WeierstrassCurve.ψ_zero])

/-- **That difference is the image of a rational point** as soon as the `n`-torsion over `Ω` is
rational, the difference being `n`-torsion. Rationality is the only thing the count needs of the
base field, so it is taken as a hypothesis rather than inferred from a closure assumption: see
`card_ker_mulByIntIsogeny_of_torsion_rational`. -/
private theorem mem_range_baseChange_sub_map_genericPoint_mulByInt
    {Ω : Type*} [Field Ω] [DecidableEq Ω] [Algebra F Ω] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0)
    (hrat : ∀ P : (W.baseChange Ω).toAffine.Point, n • P = 0 →
      P ∈ Set.range (Point.baseChange (W' := W) F Ω))
    (σ τ : W.FunctionField →ₐ[F] Ω)
    (h : ∀ z ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange, σ z = τ z) :
    Point.map σ (genericPoint W) - Point.map τ (genericPoint W) ∈
      Set.range (Point.baseChange (W' := W) F Ω) :=
  hrat _ (zsmul_map_sub_map_genericPoint_eq_zero W hn σ τ h)

open scoped Classical in
/-- **There are at most as many embeddings of `K(W)` over the pulled-back field as kernel
points**, each embedding being determined by the rational point it moves the generic point by. -/
private theorem card_emb_mulByIntIsogeny_le_card_ker {n : ℤ}
    (hn : psiFunctionField W n ≠ 0)
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point, n • P = 0 →
      P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField))) :
    Nat.card (Field.Emb (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField) ≤
      Nat.card (mulByIntIsogeny W hn).ker := by
  classical
  set L := (mulByIntIsogeny W hn).fieldPullback.fieldRange with hL
  have hagree : ∀ σ τ : Field.Emb L W.FunctionField, ∀ z ∈ L,
      (σ.restrictScalars F) z = (τ.restrictScalars F) z := by
    intro σ τ z hz
    simpa using (σ.commutes ⟨z, hz⟩).trans (τ.commutes ⟨z, hz⟩).symm
  obtain ⟨σ₀⟩ : Nonempty (Field.Emb L W.FunctionField) := inferInstance
  choose f hf using fun σ : Field.Emb L W.FunctionField ↦
    mem_range_baseChange_sub_map_genericPoint_mulByInt W hn hrat (σ.restrictScalars F)
      (σ₀.restrictScalars F) (hagree σ σ₀)
  have hker : ∀ σ : Field.Emb L W.FunctionField, f σ ∈ (mulByIntIsogeny W hn).ker := by
    intro σ
    refine (mem_ker_mulByIntIsogeny_iff W hn).2 ?_
    have hz : (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)) (n • f σ) = 0 := by
      rw [map_zsmul, hf σ]
      exact zsmul_map_sub_map_genericPoint_eq_zero W hn _ _ (hagree σ σ₀)
    exact Point.map_injective (W' := W) (f := Algebra.ofId F (AlgebraicClosure W.FunctionField))
      (hz.trans (map_zero _).symm)
  refine Nat.card_le_card_of_injective (fun σ ↦ (⟨f σ, hker σ⟩ : (mulByIntIsogeny W hn).ker)) ?_
  intro σ τ hst
  exact AlgHom.restrictScalars_injective F
    (eq_of_baseChange_eq_sub_map_genericPoint W (fun σ : Field.Emb L W.FunctionField ↦
      σ.restrictScalars F) (σ₀.restrictScalars F) hf (congrArg Subtype.val hst))

open scoped Classical in
/-- **`#ker [n] = n ²` whenever the geometric `n`-torsion is rational**, for `n` invertible.

`Isogeny.ker` counts the base field's points, so the count is the degree exactly when the kernel is
rational and the isogeny separable. Both obstructions are hypotheses here: rationality is `hrat`,
separability is `hchar`. An algebraically closed base supplies the first for free, which is
`card_ker_mulByIntIsogeny`. -/
theorem card_ker_mulByIntIsogeny_of_torsion_rational {n : ℤ} {hn : psiFunctionField W n ≠ 0}
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point, n • P = 0 →
      P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2 := by
  have hge : (mulByIntIsogeny W hn).separableDegree ≤ Nat.card (mulByIntIsogeny W hn).ker := by
    rw [separableDegree_def, Field.finSepDegree]
    exact card_emb_mulByIntIsogeny_le_card_ker W hn hrat
  have hle := card_ker_le_separableDegree (mulByIntIsogeny W hn)
  have := le_antisymm hle hge
  rw [this, separableDegree_mulByIntIsogeny W hchar]

open scoped Classical in
/-- **`#ker [n] = n ²`** over an algebraically closed field, for `n` invertible there: no extension
of an algebraically closed field carries new torsion, which is the rationality the count needs. -/
theorem card_ker_mulByIntIsogeny [IsAlgClosed F] {n : ℤ} {hn : psiFunctionField W n ≠ 0}
    (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2 :=
  card_ker_mulByIntIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero
      (ne_zero_of_psiFunctionField_ne_zero W hn) hP) hchar

open scoped Classical in
/-- **`#E[ℓ] = ℓ ²` whenever the geometric `ℓ`-torsion is rational**, for a prime `ℓ` invertible in
the base: the integer count read at `n = ℓ`, where `natAbs` is the identity. -/
theorem card_ker_mulByPrimeIsogeny_of_torsion_rational {l : ℕ} [hl : Fact l.Prime]
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      (l : ℤ) • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (l : F) ≠ 0) :
    Nat.card (mulByPrimeIsogeny W l).ker = l ^ 2 := by
  rw [card_ker_mulByIntIsogeny_of_torsion_rational W hrat (by simpa using hchar),
    Int.natAbs_natCast]

-- Not `@[simp]`: `mulByPrimeIsogeny` is an `abbrev`, so `simp` sees through it to
-- `card_ker_mulByIntIsogeny` and `simpNF` rejects the pair as duplicates.
/-- **`#E[ℓ] = ℓ ²`**, for a prime `ℓ` invertible in an algebraically closed base field. -/
theorem card_ker_mulByPrimeIsogeny [IsAlgClosed F] {l : ℕ} [hl : Fact l.Prime]
    (hchar : (l : F) ≠ 0) :
    Nat.card (mulByPrimeIsogeny W l).ker = l ^ 2 := by
  rw [card_ker_mulByIntIsogeny W (by simpa using hchar), Int.natAbs_natCast]

end TauCeti.Isogeny

end
