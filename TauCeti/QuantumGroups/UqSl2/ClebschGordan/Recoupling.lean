/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Projection
public import TauCeti.Algebra.Bialgebra.Module.Pi
public import TauCeti.LinearAlgebra.Pi

/-!
# Recoupling three signed ladder modules

There are two normalized decompositions of a triple tensor product: first decompose the
left pair, or first decompose the right pair. This file constructs both as actual module
isomorphisms, using the existing normalized Clebsch–Gordan maps at each vertex.
`clebschGordanRecouplingEquiv` changes between their channel coordinates through the
coproduct tensor associator. Its coordinate formula composes inclusions on one side with
projections on the other, without choosing any additional normalizations.

This is the module-level change of decomposition underlying the quantum 6j symbols.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII,
  for Clebsch–Gordan decompositions and recoupling.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

variable (q : ℂ) [Fact (q ≠ 0)] (m n p : ℕ) (ε δ ζ : ℤˣ)

/-- Channel coordinates obtained by coupling `L_m^ε` with `L_n^δ` first, and then with
`L_p^ζ`. The first channel has highest weight `m + n - 2i`. -/
abbrev ClebschGordanLeft :=
  ∀ i : Fin (min m n + 1),
    ∀ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)

/-- Channel coordinates obtained by coupling `L_n^δ` with `L_p^ζ` first, and then with
`L_m^ε`. The first channel has highest weight `n + p - 2i`. -/
abbrev ClebschGordanRight :=
  ∀ i : Fin (min n p + 1),
    ∀ j : Fin (min m (n + p - 2 * (i : ℕ)) + 1),
      LadderModule q (m + (n + p - 2 * (i : ℕ)) - 2 * (j : ℕ)) (ε * (δ * ζ))

variable {q m n p ε δ ζ}

/-- The normalized decomposition of the left-associated triple tensor product. -/
def clebschGordanLeftEquiv (hq : IsGenericQuantumParameter q) :
    ClebschGordanLeft q m n p ε δ ζ ≃ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ) :=
  (LinearEquiv.piCongrRight fun _ => clebschGordanEquiv hq).trans
    ((piLeft ℂ (UqSl2 q)
      (fun i : Fin (min m n + 1) => LadderModule q (m + n - 2 * (i : ℕ)) (ε * δ))
      (LadderModule q p ζ)).symm.trans
        (tensorCongr ℂ (UqSl2 q) (clebschGordanEquiv hq) (LinearEquiv.refl _ _)))

/-- The normalized decomposition of the right-associated triple tensor product. -/
def clebschGordanRightEquiv (hq : IsGenericQuantumParameter q) :
    ClebschGordanRight q m n p ε δ ζ ≃ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)) :=
  (LinearEquiv.piCongrRight fun _ => clebschGordanEquiv hq).trans
    ((piRight ℂ (UqSl2 q)
      (fun i : Fin (min n p + 1) => LadderModule q (n + p - 2 * (i : ℕ)) (δ * ζ))
      (LadderModule q m ε)).symm.trans
        (tensorCongr ℂ (UqSl2 q) (LinearEquiv.refl _ _) (clebschGordanEquiv hq)))

/-- On one left channel the decomposition is the composite of its two normalized
Clebsch–Gordan inclusions, tensoring the first inclusion with the identity. -/
@[simp] theorem clebschGordanLeftEquiv_single (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftEquiv hq (Pi.single i (Pi.single j x)) =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanInclusion hq j x) := by
  simp only [clebschGordanLeftEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_single, clebschGordanEquiv_single,
    piLeft_symm_single, tensorCongr_apply]
  rw [← LinearMap.comp_apply, ← tensorMap_comp, clebschGordanEquiv_comp_single]
  simp

/-- On one right channel the decomposition is the composite of its two normalized
Clebsch–Gordan inclusions, tensoring the identity on `L_m^ε` with the right-pair inclusion. -/
@[simp] theorem clebschGordanRightEquiv_single (hq : IsGenericQuantumParameter q)
    (i : Fin (min n p + 1)) (j : Fin (min m (n + p - 2 * (i : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (i : ℕ)) - 2 * (j : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightEquiv hq (Pi.single i (Pi.single j x)) =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq i)
        (clebschGordanInclusion hq j x) := by
  simp only [clebschGordanRightEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_single, clebschGordanEquiv_single,
    piRight_symm_single, tensorCongr_apply]
  rw [← LinearMap.comp_apply, ← tensorMap_comp, clebschGordanEquiv_comp_single]
  simp

/-- Right-associated channel extraction is the composite of the two binary projections. -/
@[simp] theorem clebschGordanRightEquiv_symm_apply (hq : IsGenericQuantumParameter q)
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)))
    (i : Fin (min n p + 1)) (j : Fin (min m (n + p - 2 * (i : ℕ)) + 1)) :
    (clebschGordanRightEquiv hq).symm x i j =
      clebschGordanProjection hq j
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq i) x) := by
  induction x using Tensor.inductionOn with
  | htmul a b =>
    simp [clebschGordanRightEquiv, piRight_apply,
      clebschGordanProjection_apply]
  | hadd x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Left-associated channel extraction is the composite of the two binary projections. -/
@[simp] theorem clebschGordanLeftEquiv_symm_apply (hq : IsGenericQuantumParameter q)
    (x : Tensor ℂ (UqSl2 q)
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) (LadderModule q p ζ))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    (clebschGordanLeftEquiv hq).symm x i j =
      clebschGordanProjection hq j
        (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id x) := by
  induction x using Tensor.inductionOn with
  | htmul a b =>
    simp [clebschGordanLeftEquiv, piLeft_apply,
      clebschGordanProjection_apply]
  | hadd x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Change from left-pair-first to right-pair-first Clebsch–Gordan coordinates, through
the actual coproduct tensor associator. All three signs and highest weights are arbitrary. -/
def clebschGordanRecouplingEquiv (hq : IsGenericQuantumParameter q) :
    ClebschGordanLeft q m n p ε δ ζ ≃ₗ[UqSl2 q] ClebschGordanRight q m n p ε δ ζ :=
  (clebschGordanLeftEquiv hq).trans
    ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)).trans
      (clebschGordanRightEquiv hq).symm)

/-- Recoupling followed by the right decomposition is the reassociated left decomposition. -/
@[simp] theorem clebschGordanRightEquiv_recoupling (hq : IsGenericQuantumParameter q)
    (x : ClebschGordanLeft q m n p ε δ ζ) :
    clebschGordanRightEquiv hq (clebschGordanRecouplingEquiv hq x) =
      assoc ℂ (UqSl2 q) _ _ _ (clebschGordanLeftEquiv hq x) := by
  simp [clebschGordanRecouplingEquiv]

/-- Inverse recoupling followed by the left decomposition undoes reassociation of the right
decomposition. -/
@[simp] theorem clebschGordanLeftEquiv_recoupling_symm (hq : IsGenericQuantumParameter q)
    (x : ClebschGordanRight q m n p ε δ ζ) :
    clebschGordanLeftEquiv hq ((clebschGordanRecouplingEquiv hq).symm x) =
      (assoc ℂ (UqSl2 q) _ _ _).symm (clebschGordanRightEquiv hq x) := by
  simp [clebschGordanRecouplingEquiv]

/-- A recoupling coordinate is obtained by including its left channel, reassociating, and
then projecting onto the right channel. This fixes the normalization of every entry. -/
theorem clebschGordanRecouplingEquiv_single_apply (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)) r s =
      clebschGordanProjection hq s
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r)
          (assoc ℂ (UqSl2 q) _ _ _
            (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
              (clebschGordanInclusion hq j x)))) := by
  simp only [clebschGordanRecouplingEquiv, LinearEquiv.trans_apply,
    clebschGordanLeftEquiv_single, clebschGordanRightEquiv_symm_apply]

/-- An inverse recoupling coordinate is obtained by including its right channel, undoing
reassociation, and then projecting onto the left channel. -/
theorem clebschGordanRecouplingEquiv_symm_single_apply (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    (clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)) i j =
      clebschGordanProjection hq j
        (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id
          ((assoc ℂ (UqSl2 q) _ _ _).symm
            (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
              (clebschGordanInclusion hq s x)))) := by
  simp only [clebschGordanRecouplingEquiv, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    clebschGordanRightEquiv_single, clebschGordanLeftEquiv_symm_apply]

end TauCeti.UqSl2
