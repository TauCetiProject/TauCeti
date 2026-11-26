/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.LinearAlgebra.TensorProduct.Pi
public import TauCeti.RingTheory.DiscreteValuationRing.EigenvalueLifting
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Checks for the Deligne–Serre eigenvalue lifting lemma

`TauCeti.exists_valuationSubring_forall_baseChange_apply_eq_smul` lifts a residual eigenvalue
system of commuting operators on a finite free module `M` over a DVR `O` to a common eigenvector in
`V ⊗[O] M`, for a DVR `V` dominating `O` in a finite extension `L` of the fraction field `K`. The
checks below show, on `M = O²` with a uniformizer `ϖ`, that two strengthenings of its conclusion
are false.

* *The residual eigenvector need not lift.* The operator `[[0, ϖ], [0, 0]]` reduces to zero, so
  `e₂` is a residual eigenvector with eigenvalue `0`. Over every domain in which `ϖ` is nonzero,
  every eigenvector of this operator lies on the line of `e₁`. So no lifted eigenvector reduces
  to `e₂`, and the eigenvector which the lifting lemma produces from `e₂` lies on the line of
  `e₁`, although its eigenvalue does reduce to `0`.
* *The fraction field must be extended.* The companion operator `[[0, ϖ], [1, 0]]` squares to
  `ϖ`, so each of its eigenvalues `c` over a domain satisfies `c ^ 2 = ϖ`. A uniformizer has no
  square root in `K`, so this operator has no nonzero eigenvector over `K`, although its
  reduction has the eigenvector `e₂`. Over any ring containing a square root `α` of `ϖ`, the
  vector `(α, 1)` is an eigenvector with eigenvalue `α`. For `O = 𝔽₂⟦t⟧` and `ϖ = t`, every field
  over `K` in which the operator has an eigenvector is an inseparable extension of `K`: the
  eigenvalue is a square root of `t`, which is purely inseparable over `K` but not in `K`. So the
  lifting lemma cannot assert that `L / K` is separable.

Vectors of `A ⊗[O] O²` are read in coordinates through `TensorProduct.piScalarRight`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, Lemme 6.11 and its proof.
-/

public noncomputable section

open IntermediateField IsLocalRing Matrix PowerSeries TensorProduct

namespace TauCeti.EigenvalueLiftingChecks

variable {O : Type*} [CommRing O]

section Nilpotent

variable (ϖ : O)

/-- If `ϖ` lies in the maximal ideal of the local ring `O`, then `[[0, ϖ], [0, 0]]` reduces to
zero, so every vector of `κ ⊗[O] O²`, in particular `e₂`, is a residual eigenvector with
eigenvalue `0`. -/
theorem nilpotent_baseChange_residueField_eq_zero [IsLocalRing O] (hϖ : ϖ ∈ maximalIdeal O) :
    (toLin' !![0, ϖ; 0, 0]).baseChange (ResidueField O) = 0 := by
  have h : !![0, ϖ; 0, 0] = ϖ • !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, map_smul, LinearMap.baseChange_smul]
  ext x
  simp [← algebraMap_smul (ResidueField O) ϖ, (residue_eq_zero_iff ϖ).2 hϖ]

/-- Over an `O`-algebra `A` without zero divisors in which `ϖ` is nonzero, every eigenvector of
`[[0, ϖ], [0, 0]]` lies on the line of `e₁`, whatever its eigenvalue: its second coordinate
vanishes. -/
theorem piScalarRight_one_eq_zero_of_nilpotent_baseChange_eq_smul {A : Type*} [CommRing A]
    [NoZeroDivisors A] [Algebra O A] (hϖ : algebraMap O A ϖ ≠ 0) {c : A} {v : A ⊗[O] (Fin 2 → O)}
    (hv : (toLin' !![0, ϖ; 0, 0]).baseChange A v = c • v) :
    piScalarRight O A A (Fin 2) v 1 = 0 := by
  -- The coordinates of `[[0, ϖ], [0, 0]] v` are `(ϖ v₁, 0)`.
  have key (w : A ⊗[O] (Fin 2 → O)) :
      piScalarRight O A A (Fin 2) ((toLin' !![0, ϖ; 0, 0]).baseChange A w) 0 =
          algebraMap O A ϖ * piScalarRight O A A (Fin 2) w 1 ∧
        piScalarRight O A A (Fin 2) ((toLin' !![0, ϖ; 0, 0]).baseChange A w) 1 = 0 := by
    induction w using TensorProduct.inductionOn with
    | tmul a x =>
      simp [Algebra.smul_def, dotProduct, Fin.sum_univ_two]
      ring
    | add v w hv hw => simp only [map_add, Pi.add_apply, hv.1, hw.1, hv.2, hw.2, mul_add, add_zero,
        and_self]
  -- So `c v₁ = 0` and `ϖ v₁ = c v₀`; if `c = 0`, then `ϖ v₁ = 0`.
  obtain ⟨h0, h1⟩ := key v
  simp only [hv, map_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero] at h0 h1
  rcases h1 with rfl | h1
  · simpa [hϖ, eq_comm] using h0
  · exact h1

/-- *Failure of prescribed eigenvector lifting*: over an `O`-algebra `A` that is a domain in which
`ϖ` is nonzero, no eigenvector of `[[0, ϖ], [0, 0]]` reduces to `e₂` along an `O`-algebra map
`φ : A → B` to a nontrivial ring, although `e₁` is an eigenvector with eigenvalue `0`. -/
example {A B : Type*} [CommRing A] [IsDomain A] [Algebra O A] [CommRing B] [Nontrivial B]
    [Algebra O B] (φ : A →ₐ[O] B) (hϖ : algebraMap O A ϖ ≠ 0) :
    (¬ ∃ (c : A) (v : A ⊗[O] (Fin 2 → O)),
      (toLin' !![0, ϖ; 0, 0]).baseChange A v = c • v ∧
        φ.toLinearMap.rTensor _ v = 1 ⊗ₜ Pi.single 1 1) ∧
      (toLin' !![0, ϖ; 0, 0]).baseChange A (1 ⊗ₜ Pi.single 0 1) =
        (0 : A) • (1 ⊗ₜ[O] (Pi.single 0 1 : Fin 2 → O)) := by
  have he₁ : toLin' !![0, ϖ; 0, 0] (Pi.single 0 1 : Fin 2 → O) = 0 := by
    ext i
    fin_cases i <;> simp
  refine ⟨?_, by simp [he₁]⟩
  rintro ⟨c, v, hv, hred⟩
  have := congr_arg (fun w ↦ piScalarRight O B B (Fin 2) w 1) hred
  rw [piScalarRight_rTensor A, Function.comp_apply,
    piScalarRight_one_eq_zero_of_nilpotent_baseChange_eq_smul ϖ hϖ hv] at this
  simp at this

/-- The lifting lemma applied to the residual eigenvector `e₂` of `[[0, ϖ], [0, 0]]`, for a
uniformizer `ϖ` of a DVR: the lifted eigenvalue reduces to the residual eigenvalue `0`, but the
lifted eigenvector lies on the line of `e₁`, so it does not reduce to `e₂`. -/
example [IsDomain O] [IsDiscreteValuationRing O] (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] (hϖ : Irreducible ϖ) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (V : ValuationSubring L) (_ : Algebra O V)
      (b : V) (f' : V ⊗[O] (Fin 2 → O)), f' ≠ 0 ∧
        (toLin' !![0, ϖ; 0, 0]).baseChange V f' = b • f' ∧ residue V b = 0 ∧
        piScalarRight O V V (Fin 2) f' 1 = 0 := by
  have h0 := nilpotent_baseChange_residueField_eq_zero ϖ hϖ.not_isUnit
  obtain ⟨L, V, _, j, -, -, hinj, -, -, -, -, b, f', hf', hb⟩ :=
    exists_valuationSubring_forall_baseChange_apply_eq_smul K
      (fun _ : Unit ↦ toLin' !![0, ϖ; 0, 0]) (fun _ _ ↦ Commute.refl _) (fun _ ↦ 0) _
      (one_tmul_single_ne_zero 1) (fun _ ↦ by simp [h0])
  have hϖV : algebraMap O V ϖ ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap O V), hinj.eq_iff]
    exact hϖ.ne_zero
  exact ⟨L, V, _, b (), f', hf', (hb ()).1, by simp [(hb ()).2],
    piScalarRight_one_eq_zero_of_nilpotent_baseChange_eq_smul ϖ hϖV (hb ()).1⟩

end Nilpotent

section Companion

variable (ϖ : O)

/-- The companion operator `[[0, ϖ], [1, 0]]` squares to `ϖ`. -/
theorem companion_mul_self :
    (toLin' !![0, ϖ; 1, 0] * toLin' !![0, ϖ; 1, 0] : Module.End O (Fin 2 → O)) = ϖ • 1 := by
  have h : !![0, ϖ; 1, 0] * !![0, ϖ; 1, 0] = ϖ • (1 : Matrix (Fin 2) (Fin 2) O) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Module.End.mul_eq_comp, ← toLin'_mul, h, map_smul, toLin'_one, Module.End.one_eq_id]

/-- The companion operator `[[0, ϖ], [1, 0]]` sends `e₁` to `e₂`. -/
private theorem companion_single_zero :
    toLin' !![0, ϖ; 1, 0] (Pi.single 0 1 : Fin 2 → O) = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp

/-- The companion operator `[[0, ϖ], [1, 0]]` sends `e₂` to `ϖ e₁`. -/
private theorem companion_single_one :
    toLin' !![0, ϖ; 1, 0] (Pi.single 1 1 : Fin 2 → O) = ϖ • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp

/-- Every eigenvalue `c` of the companion operator `[[0, ϖ], [1, 0]]` over an `O`-algebra `A`
that is a domain satisfies `c ^ 2 = ϖ`. -/
theorem sq_eq_of_companion_baseChange_eq_smul {A : Type*} [CommRing A] [IsDomain A] [Algebra O A]
    {c : A} {v : A ⊗[O] (Fin 2 → O)} (hv0 : v ≠ 0)
    (hv : (toLin' !![0, ϖ; 1, 0]).baseChange A v = c • v) :
    c ^ 2 = algebraMap O A ϖ := by
  have h := congr_arg (· v) (congr_arg (LinearMap.baseChange A) (companion_mul_self ϖ))
  simp only [LinearMap.baseChange_mul, LinearMap.baseChange_smul, LinearMap.baseChange_one,
    mul_apply_eq_comp, hv, map_smul, LinearMap.smul_apply, one_apply_eq_self,
    ← algebraMap_smul A ϖ v, smul_smul] at h
  rw [sq]
  exact smul_left_injective A hv0 h

/-- If `ϖ` lies in the maximal ideal of the local ring `O`, then the reduction of the companion
operator `[[0, ϖ], [1, 0]]` has the eigenvector `e₂` with eigenvalue `0`. -/
theorem companion_baseChange_residueField_one_tmul_single_one [IsLocalRing O]
    (hϖ : ϖ ∈ maximalIdeal O) :
    (toLin' !![0, ϖ; 1, 0]).baseChange (ResidueField O) (1 ⊗ₜ Pi.single 1 1) =
      (0 : ResidueField O) • (1 ⊗ₜ[O] (Pi.single 1 1 : Fin 2 → O)) := by
  rw [LinearMap.baseChange_tmul, companion_single_one, ← smul_tmul,
    ← algebraMap_smul (ResidueField O) ϖ]
  simp [ResidueField.algebraMap_eq, (residue_eq_zero_iff ϖ).2 hϖ]

/-- *Necessity of a fraction-field extension*: for an irreducible element `ϖ` of an integrally
closed domain `O`, such as a uniformizer of a DVR, the companion operator `[[0, ϖ], [1, 0]]` has
no nonzero eigenvector over the fraction field `K` of `O`, since `ϖ` has no square root in `K`. -/
theorem not_exists_companion_baseChange_fractionRing_eq_smul [IsIntegrallyClosed O]
    (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] (hϖ : Irreducible ϖ) :
    ¬ ∃ (c : K) (v : K ⊗[O] (Fin 2 → O)), v ≠ 0 ∧
      (toLin' !![0, ϖ; 1, 0]).baseChange K v = c • v := by
  rintro ⟨c, v, hv0, hv⟩
  exact hϖ.not_isSquare_algebraMap K
    ⟨c, by rw [← sq_eq_of_companion_baseChange_eq_smul ϖ hv0 hv, sq]⟩

/-- Over an `O`-algebra `A` containing a square root `α` of `ϖ`, the vector `(α, 1)` is an
eigenvector of the companion operator `[[0, ϖ], [1, 0]]` with eigenvalue `α`, and it is nonzero
when `A` is nontrivial. -/
example {A : Type*} [CommRing A] [Nontrivial A] [Algebra O A] {α : A}
    (hα : α ^ 2 = algebraMap O A ϖ) :
    α ⊗ₜ[O] (Pi.single 0 1 : Fin 2 → O) + 1 ⊗ₜ Pi.single 1 1 ≠ 0 ∧
      (toLin' !![0, ϖ; 1, 0]).baseChange A (α ⊗ₜ Pi.single 0 1 + 1 ⊗ₜ Pi.single 1 1) =
        α • (α ⊗ₜ[O] (Pi.single 0 1 : Fin 2 → O) + 1 ⊗ₜ Pi.single 1 1) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa using
      congr_arg (fun w ↦ piScalarRight O A A (Fin 2) w 1) h
  · simp only [map_add, LinearMap.baseChange_tmul, companion_single_zero, companion_single_one,
      ← smul_tmul, ← algebraMap_smul A ϖ, ← hα]
    simp [smul_tmul', sq, add_comm]

/-- *An inseparable instance of the lifting*: let `ϖ` be an irreducible element of an
integrally closed domain `O` of characteristic two, with fraction field `K`. No eigenvalue of the
companion operator `[[0, ϖ], [1, 0]]` over a field `L` containing `K` is separable over `K`: it is
a square root of `ϖ` outside `K`. -/
theorem not_isSeparable_of_companion_baseChange_eq_smul [IsIntegrallyClosed O]
    [CharP O 2] (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] (hϖ : Irreducible ϖ)
    {L : Type*} [Field L] [Algebra O L] [Algebra K L] [IsScalarTower O K L] {c : L}
    {v : L ⊗[O] (Fin 2 → O)} (hv0 : v ≠ 0)
    (hv : (toLin' !![0, ϖ; 1, 0]).baseChange L v = c • v) :
    ¬ IsSeparable K c := by
  have : CharP K 2 := charP_of_injective_algebraMap (IsFractionRing.injective O K) 2
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hc := sq_eq_of_companion_baseChange_eq_smul ϖ hv0 hv
  rw [IsScalarTower.algebraMap_apply O K L] at hc
  -- A separable `c` with `c ^ 2 ∈ K` generates `K⟮c⟯ = K⟮c ^ 2⟯ = K`, so `c ∈ K`.
  intro hsep
  have h := adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable K L hsep 2
  rw [hc, adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ _)] at h
  obtain ⟨y, rfl⟩ := mem_bot.1 (h ▸ mem_adjoin_simple_self K c)
  rw [← map_pow, (algebraMap K L).injective.eq_iff] at hc
  exact hϖ.not_isSquare_algebraMap K ⟨y, by rw [← hc, sq]⟩

/-- For `O = 𝔽₂⟦t⟧` and `ϖ = t`, an eigenvalue `c` of the companion operator `[[0, t], [1, 0]]`
over a field `L` containing the fraction field `K` generates a nontrivial purely inseparable
extension `K⟮c⟯` of `K`, and `L / K` is not separable. -/
example (K : Type*) [Field K] [Algebra (ZMod 2)⟦X⟧ K] [IsFractionRing (ZMod 2)⟦X⟧ K]
    {L : Type*} [Field L] [Algebra (ZMod 2)⟦X⟧ L] [Algebra K L] [IsScalarTower (ZMod 2)⟦X⟧ K L]
    {c : L} {v : L ⊗[(ZMod 2)⟦X⟧] (Fin 2 → (ZMod 2)⟦X⟧)} (hv0 : v ≠ 0)
    (hv : (toLin' !![0, X; 1, 0]).baseChange L v = c • v) :
    IsPurelyInseparable K K⟮c⟯ ∧ K⟮c⟯ ≠ ⊥ ∧ ¬ Algebra.IsSeparable K L := by
  have : CharP (ZMod 2)⟦X⟧ 2 := charP_of_injective_algebraMap C_injective 2
  have : CharP K 2 := charP_of_injective_algebraMap (IsFractionRing.injective (ZMod 2)⟦X⟧ K) 2
  have hc := sq_eq_of_companion_baseChange_eq_smul X hv0 hv
  rw [IsScalarTower.algebraMap_apply (ZMod 2)⟦X⟧ K L] at hc
  have hsep := not_isSeparable_of_companion_baseChange_eq_smul X K irreducible_X hv0 hv
  refine ⟨(isPurelyInseparable_adjoin_simple_iff_pow_mem K L 2).2 ⟨1, _, by simpa using hc.symm⟩,
    fun h ↦ ?_, fun _ ↦ hsep (Algebra.IsSeparable.isSeparable K c)⟩
  obtain ⟨y, rfl⟩ := mem_bot.1 (h ▸ mem_adjoin_simple_self K c)
  exact hsep (isSeparable_algebraMap y)

/-- The lifting lemma applied to the residual eigenvector `e₂` of `[[0, ϖ], [1, 0]]`, for a
uniformizer `ϖ` of a DVR `O` with fraction field `K`: the lifted eigenvalue `b` is a square root of
`ϖ`, so the finite extension `L` of `K` containing it is not `K` itself. -/
example [IsDomain O] [IsDiscreteValuationRing O] (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] (hϖ : Irreducible ϖ) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (V : ValuationSubring L) (_ : Algebra O V)
      (b : V), (b : L) ^ 2 = algebraMap K L (algebraMap O K ϖ) ∧
        (b : L) ∉ (algebraMap K L).range ∧ residue V b = 0 := by
  have hres := companion_baseChange_residueField_one_tmul_single_one ϖ hϖ.not_isUnit
  obtain ⟨L, V, _, j, -, -, -, -, hcompat, -, -, b, f', hf', hb⟩ :=
    exists_valuationSubring_forall_baseChange_apply_eq_smul K
      (fun _ : Unit ↦ toLin' !![0, ϖ; 1, 0]) (fun _ _ ↦ Commute.refl _) (fun _ ↦ 0) _
      (one_tmul_single_ne_zero 1) (fun _ ↦ hres)
  have hb2 : (b () : L) ^ 2 = algebraMap K L (algebraMap O K ϖ) := by
    rw [← hcompat, ← sq_eq_of_companion_baseChange_eq_smul ϖ hf' (hb ()).1]
    norm_cast
  refine ⟨L, V, ‹_›, b (), hb2, ?_, by simp [(hb ()).2]⟩
  rintro ⟨y, hy⟩
  rw [← hy, ← map_pow, (algebraMap K L).injective.eq_iff] at hb2
  exact hϖ.not_isSquare_algebraMap K ⟨y, by rw [← hb2, sq]⟩

end Companion

end TauCeti.EigenvalueLiftingChecks

end
