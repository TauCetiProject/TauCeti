/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Equiv

/-!
# Number-field descent and Galois moduli descent for algebraic Belyi pairs

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over an algebraically closed field `k` of
characteristic zero, such as `ℂ` or `AlgebraicClosure ℚ`. Building on the pointed model
`TauCeti.AlgebraicBelyiPair.pointedModel` and Köck's bounded-degree descent theorem
`TauCeti.AlgebraicBelyiPair.IsoClass.exists_relfinrank_fieldOfModuli_le_degree_and_isDefinedOver`
from `TauCeti.FieldTheory.FunctionField.Belyi.CoefficientDescent`, this file establishes two
consequences of Köck's Theorem 2.2:

* **Number-field descent when the field of moduli is finite over `ℚ`:** whenever the field of moduli
  `M(X)` is finite-dimensional over `ℚ`, `X` admits a model over a number field `K ⊆ k` containing
  `M(X)` of degree `[K : ℚ] ≤ [M(X) : ℚ] · [F : k(t)]`
  (`TauCeti.AlgebraicBelyiPair.exists_model_of_finiteDimensional_fieldOfModuli`).
* **Galois moduli descent:** when `F / k(t)` is Galois, `Gal(F / k(t))` acts transitively on the
  fibre over any rational point `t = q`, so every semilinear automorphism of `X` can be composed
  with a deck transformation to fix a chosen place `P` over `t = q`. Thus the pointed stabilizer and
  pointed field of moduli agree with the full stabilizer and field of moduli, and `X` admits a model
  over its field of moduli `M(X)` itself (`TauCeti.AlgebraicBelyiPair.modelOfIsGalois`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois`).

## Main definitions

* `TauCeti.AlgebraicBelyiPair.modelOfIsGalois`: over an algebraically closed field `k`, a model of a
  Galois Belyi pair `X` over its field of moduli.

## Main results

* `TauCeti.AlgebraicBelyiPair.exists_model_of_finiteDimensional_fieldOfModuli` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.exists_isDefinedOver_of_finiteDimensional_fieldOfModuli`:
  number-field descent when the field of moduli is finite over `ℚ`.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizer_eq_stabilizer_of_isGalois` and
  `TauCeti.AlgebraicBelyiPair.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois`: for a Galois
  Belyi pair, the pointed stabilizer and pointed field of moduli at a rational place agree with the
  full stabilizer and field of moduli.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli_of_isGalois`: **Köck,
  Theorem 2.2 (Galois case)** — over an algebraically closed field of characteristic zero, every
  Galois Belyi pair is defined over its field of moduli.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (2.2) Theorem.
-/

public section

open Polynomial IntermediateField

namespace TauCeti.AlgebraicBelyiPair

universe u

variable {k : Type u} [Field k] [CharZero k]

/-! ### Number-field descent when the field of moduli is finite over `ℚ` -/

section NumberField

variable (X : AlgebraicBelyiPair k)

/-- If the field of moduli of `X` is finite over `ℚ`, then `X` has a model over a number field `K`
inside `k` containing its field of moduli with `[K : ℚ] ≤ [M(X) : ℚ] · [X : k(t)]`. -/
theorem exists_model_of_finiteDimensional_fieldOfModuli [IsAlgClosed k]
    [FiniteDimensional ℚ (IsoClass.mk X).fieldOfModuli] :
    ∃ K : IntermediateField ℚ k,
      (IsoClass.mk X).fieldOfModuli ≤ K ∧
      FiniteDimensional ℚ K ∧
      Module.finrank ℚ K ≤
        Module.finrank ℚ (IsoClass.mk X).fieldOfModuli * Module.finrank (RatFunc k) X ∧
      Nonempty (Model K X) := by
  obtain ⟨K, hle, hpos, hdeg, hK⟩ :=
    IsoClass.exists_relfinrank_fieldOfModuli_le_degree_and_isDefinedOver (IsoClass.mk X)
  rw [IsoClass.degree_mk] at hdeg
  rw [IsoClass.isDefinedOver_mk_iff] at hK
  have hmul := (IntermediateField.finrank_bot_mul_relfinrank hle).symm
  have hKpos : 0 < Module.finrank ℚ K := by
    rw [hmul]
    exact Nat.mul_pos Module.finrank_pos hpos
  exact ⟨K, hle, Module.finite_of_finrank_pos hKpos, hmul ▸ Nat.mul_le_mul_left _ hdeg, hK⟩

end NumberField

namespace IsoClass

/-- Over an algebraically closed field `k` of characteristic zero, any isomorphism class `c` whose
field of moduli is finite over `ℚ` is defined over a number field `K ⊆ k` containing
`c.fieldOfModuli` of degree `[K : ℚ] ≤ [c.fieldOfModuli : ℚ] · c.degree`. -/
theorem exists_isDefinedOver_of_finiteDimensional_fieldOfModuli [IsAlgClosed k]
    (c : IsoClass k) [FiniteDimensional ℚ c.fieldOfModuli] :
    ∃ K : IntermediateField ℚ k,
      c.fieldOfModuli ≤ K ∧
      FiniteDimensional ℚ K ∧
      Module.finrank ℚ K ≤ Module.finrank ℚ c.fieldOfModuli * c.degree ∧
      c.IsDefinedOver K := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨K, hle, hfin, hdeg, hM⟩ := X.exists_model_of_finiteDimensional_fieldOfModuli
  exact ⟨K, hle, hfin, by simpa only [degree_mk] using hdeg, isDefinedOver_mk_iff.mpr hM⟩

end IsoClass

/-! ### Galois Belyi pairs descend to their field of moduli -/

section Galois

variable (X : AlgebraicBelyiPair k)

/-- For a Galois Belyi pair `X / k(t)`, the pointed stabilizer at any place `P` over a rational
point `t = q` (`q ∈ ℚ`) equals the full stabilizer of the isomorphism class of `X`: any semilinear
automorphism moves `P` to another place over `t = q`, and `Gal(X / k(t))` acts transitively on that
fibre. -/
theorem pointedStabilizer_eq_stabilizer_of_isGalois [IsGalois (RatFunc k) X]
    {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedStabilizer P = MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
  refine le_antisymm (X.pointedStabilizer_le_stabilizer P) fun g hg ↦ ?_
  rw [← X.map_snd_semilinearAut] at hg
  obtain ⟨p, hp, hpg⟩ := hg
  rw [MonoidHom.coe_snd] at hpg
  subst hpg
  let p₀ : semilinearAut X := ⟨p, hp⟩
  have hres : (p₀ • P).restrict k (RatFunc k) = P.restrict k (RatFunc k) := by
    rw [restrict_smul, hPa, Place.equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C,
      map_ratCast]
  obtain ⟨σ, hσ⟩ := Place.exists_smul_eq_of_restrict_eq hres
  refine mem_pointedStabilizer_iff.mpr ⟨p.fst.trans σ.toRingEquiv, fun r ↦ ?_, fun z ↦ ?_⟩
  · rw [RingEquiv.trans_apply, mem_semilinearAut_iff.mp hp, AlgEquiv.coe_toRingEquiv, σ.commutes]
  · rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, ← hσ, Place.valuation_smul_apply,
      valuation_smul_apply p₀ P z, hσ]

/-- For a Galois Belyi pair `X / k(t)`, the pointed field of moduli at any place over `t = q`
(`q ∈ ℚ`) coincides with the field of moduli of `X`. -/
theorem pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois [IsGalois (RatFunc k) X]
    {P : Place k X} {q : ℚ}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    X.pointedFieldOfModuli P = (IsoClass.mk X).fieldOfModuli := by
  rw [pointedFieldOfModuli_def, IsoClass.fieldOfModuli_def,
    X.pointedStabilizer_eq_stabilizer_of_isGalois hPa]

/-- **Köck, Theorem 2.2 (Galois model).** Over any algebraically closed field `k` of characteristic
zero, every Galois Belyi pair `X` admits a model over its field of moduli. -/
noncomputable def modelOfIsGalois [IsAlgClosed k] [IsGalois (RatFunc k) X] :
    Model (IsoClass.mk X).fieldOfModuli X :=
  let h := X.exists_restrict_eq_and_degree_eq_one
    (Place.adicOfIrreducible (irreducible_X_sub_C ((2 : ℚ) : k)))
  have h20 : ((2 : ℚ) : k) ≠ 0 := by norm_num
  have h21 : ((2 : ℚ) : k) ≠ 1 := by norm_num
  Eq.rec (motive := fun (L : IntermediateField ℚ k) _ ↦ Model L X)
    (X.pointedModel h20 h21 h.choose_spec.left h.choose_spec.right)
    (X.pointedFieldOfModuli_eq_fieldOfModuli_of_isGalois h.choose_spec.left)

end Galois

namespace IsoClass

/-- **Köck, Theorem 2.2 (Galois case).** Over any algebraically closed field `k` of characteristic
zero (such as `ℂ` or `AlgebraicClosure ℚ`), every Galois Belyi pair is defined over its field of
moduli. -/
theorem isDefinedOver_fieldOfModuli_of_isGalois [IsAlgClosed k] (X : AlgebraicBelyiPair k)
    [IsGalois (RatFunc k) X] :
    (mk X).IsDefinedOver (mk X).fieldOfModuli :=
  isDefinedOver_mk_iff.mpr ⟨X.modelOfIsGalois⟩

end IsoClass

end TauCeti.AlgebraicBelyiPair
