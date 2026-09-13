/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.AlgClosed
-- Proof-only: `sepDeg [n] = n ²` for `n` invertible in the base field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# The kernel of `[n]` has `n ²` points over an algebraically closed field

`Isogeny.ker` counts only the base field's points, so its order equals the degree exactly when the
geometric kernel is rational. Over an algebraically closed field it is, and `[n]` is separable as
soon as `n` is invertible there, so the two obstructions both vanish and `#ker [n] = n ²`.

The count is made on embeddings, as for `1 − π_q`: an isogeny here has no map on points. Two
embeddings of `K(W)` over the pulled-back field move the tautological point of `[n]`, which is
`n` times the generic point, to the same place, so the two images of the generic point differ by an
`n`-torsion point — and over an algebraically closed base a torsion point is rational. An embedding
is determined by where it sends the generic point, so that assignment is injective into the kernel,
and the separable degree is the number of embeddings.

## Main results

* `TauCeti.Isogeny.zsmul_map_sub_map_genericPoint_eq_zero`: two homomorphisms agreeing on the
  pulled-back field move the generic point by an `n`-torsion difference.
* `TauCeti.Isogeny.mem_range_baseChange_sub_map_genericPoint_mulByInt`: that difference is the
  image of a rational point.
* `TauCeti.Isogeny.card_emb_mulByIntIsogeny_le_card_ker`: hence there are at most as many
  embeddings as kernel points.
* `TauCeti.Isogeny.card_ker_mulByIntIsogeny`: **`#ker [n] = n ²`**.

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
theorem zsmul_map_sub_map_genericPoint_eq_zero {Ω : Type*} [Field Ω] [DecidableEq Ω]
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
  have hd : n • (Point.map σ (genericPoint W) - Point.map τ (genericPoint W)) =
      n • Point.map σ (genericPoint W) - n • Point.map τ (genericPoint W) := by module
  rw [hd, key, sub_self]

/-- **That difference is the image of a rational point**, the base field being algebraically
closed and the difference `n`-torsion. -/
theorem mem_range_baseChange_sub_map_genericPoint_mulByInt [IsAlgClosed F]
    {Ω : Type*} [Field Ω] [DecidableEq Ω] [Algebra F Ω] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (hn0 : n ≠ 0) (σ τ : W.FunctionField →ₐ[F] Ω)
    (h : ∀ z ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange, σ z = τ z) :
    Point.map σ (genericPoint W) - Point.map τ (genericPoint W) ∈
      Set.range (Point.baseChange (W' := W) F Ω) :=
  W.mem_range_baseChange_of_zsmul_eq_zero hn0
    (zsmul_map_sub_map_genericPoint_eq_zero W hn σ τ h)

/-- **There are at most as many embeddings of `K(W)` over the pulled-back field as kernel
points**, each embedding being determined by the rational point it moves the generic point by. -/
theorem card_emb_mulByIntIsogeny_le_card_ker [IsAlgClosed F] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (hn0 : n ≠ 0) :
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
    mem_range_baseChange_sub_map_genericPoint_mulByInt W hn hn0 (σ.restrictScalars F)
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

/-- **`#ker [n] = n ²`** over an algebraically closed field, for `n` invertible there. -/
theorem card_ker_mulByIntIsogeny [IsAlgClosed F] {n : ℤ} {hn : psiFunctionField W n ≠ 0}
    (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2 := by
  have hn0 : n ≠ 0 := fun h ↦ hchar (by rw [h]; exact Int.cast_zero)
  have hge : (mulByIntIsogeny W hn).separableDegree ≤ Nat.card (mulByIntIsogeny W hn).ker := by
    rw [separableDegree_def, Field.finSepDegree]
    exact card_emb_mulByIntIsogeny_le_card_ker W hn hn0
  have hle := card_ker_le_separableDegree (mulByIntIsogeny W hn)
  have := le_antisymm hle hge
  rw [this, separableDegree_mulByIntIsogeny W hchar]

end TauCeti.Isogeny

end
