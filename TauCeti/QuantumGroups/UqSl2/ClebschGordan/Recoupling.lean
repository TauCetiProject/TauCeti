/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Projection
public import TauCeti.Algebra.Bialgebra.Module.Pi
public import TauCeti.LinearAlgebra.Pi

import TauCeti.Algebra.BigOperators.Pi

/-!
# Recoupling three signed ladder modules

There are two normalized decompositions of a triple tensor product `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` at a
generic parameter `q`: first decompose the left pair (`clebschGordanLeftEquiv`), or first decompose
the right pair (`clebschGordanRightEquiv`). `clebschGordanRecouplingEquiv` changes between their
channel coordinates through the coproduct tensor associator `BialgebraModule.assoc`, without
choosing any additional normalizations beyond `clebschGordanInclusion`.

## Main definitions and results

* `clebschGordanLeftInclusion`, `clebschGordanRightInclusion`, `clebschGordanLeftProjection`,
  `clebschGordanRightProjection`: normalized triple-product channel inclusions and projections.
* `recouplingHom`, `invRecouplingHom`: channel-to-channel recoupling intertwiners through `assoc`
  and `assoc.symm`.
* `recouplingCoeff`, `invRecouplingCoeff`: Schur scalars of `recouplingHom` and `invRecouplingHom`,
  governing their action on every ladder vector `v_l` (`recouplingHom_vec`, `invRecouplingHom_vec`)
  and vanishing on mismatched channel weights.
* `assoc_clebschGordanLeftInclusion_vec`, `assoc_symm_clebschGordanRightInclusion_vec`: explicit
  triple-product expansions of `assoc` and `assoc.symm` on every channel ladder vector `v_l`.
* `sum_invRecouplingCoeff_mul_recouplingCoeff`, `sum_recouplingCoeff_mul_invRecouplingCoeff`:
  channel-summed orthogonality of `recouplingCoeff` and `invRecouplingCoeff`.

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

/-! ### Triple-product channel inclusions, projections, and recoupling intertwiners -/

/-- Inclusion of the `(i, j)` left-associated channel into `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
def clebschGordanLeftInclusion (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ) :=
  (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id).comp
    (clebschGordanInclusion hq j)

/-- Definitional composite formula for `clebschGordanLeftInclusion`. -/
theorem clebschGordanLeftInclusion_def (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j =
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id).comp
        (clebschGordanInclusion hq j) := (rfl)

/-- Inclusion of the `(r, s)` right-associated channel into `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
def clebschGordanRightInclusion (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)).comp
    (clebschGordanInclusion hq s)

/-- Definitional composite formula for `clebschGordanRightInclusion`. -/
theorem clebschGordanRightInclusion_def (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s =
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)).comp
        (clebschGordanInclusion hq s) := (rfl)

/-- Projection of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` onto its `(i, j)` left-associated channel. -/
def clebschGordanLeftProjection (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (clebschGordanProjection hq j).comp
    (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id)

/-- Definitional composite formula for `clebschGordanLeftProjection`. -/
theorem clebschGordanLeftProjection_def (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftProjection (ε := ε) (δ := δ) (ζ := ζ) hq i j =
      (clebschGordanProjection hq j).comp
        (tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id) := (rfl)

/-- Projection of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)` onto its `(r, s)` right-associated channel. -/
def clebschGordanRightProjection (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (clebschGordanProjection hq s).comp
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r))

/-- Definitional composite formula for `clebschGordanRightProjection`. -/
theorem clebschGordanRightProjection_def (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightProjection (ε := ε) (δ := δ) (ζ := ζ) hq r s =
      (clebschGordanProjection hq s).comp
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r)) := (rfl)

/-- `clebschGordanLeftInclusion` agrees with `clebschGordanLeftEquiv` on a single channel. -/
theorem clebschGordanLeftInclusion_eq_single (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftInclusion hq i j x = clebschGordanLeftEquiv hq (Pi.single i (Pi.single j x)) :=
  (clebschGordanLeftEquiv_single hq i j x).symm

/-- `clebschGordanRightInclusion` agrees with `clebschGordanRightEquiv` on a single channel. -/
theorem clebschGordanRightInclusion_eq_single (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightInclusion hq r s x =
      clebschGordanRightEquiv hq (Pi.single r (Pi.single s x)) :=
  (clebschGordanRightEquiv_single hq r s x).symm

/-- `clebschGordanLeftProjection` extracts `(i, j)` of `(clebschGordanLeftEquiv).symm`. -/
theorem clebschGordanLeftProjection_eq_symm (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
      (LadderModule q p ζ)) :
    clebschGordanLeftProjection hq i j x = (clebschGordanLeftEquiv hq).symm x i j :=
  (clebschGordanLeftEquiv_symm_apply hq x i j).symm

/-- `clebschGordanRightProjection` extracts `(r, s)` of `(clebschGordanRightEquiv).symm`. -/
theorem clebschGordanRightProjection_eq_symm (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ))) :
    clebschGordanRightProjection hq r s x = (clebschGordanRightEquiv hq).symm x r s :=
  (clebschGordanRightEquiv_symm_apply hq x r s).symm

/-- `clebschGordanLeftInclusion` sends `v₀` to the left-coupled `α₀ = 1` highest-weight vector. -/
@[simp] theorem clebschGordanLeftInclusion_vec_zero (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0) =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanVector q (m + n - 2 * (i : ℕ)) (ε * δ) p ζ j) := by
  simp [clebschGordanLeftInclusion]

/-- `clebschGordanRightInclusion` sends `v₀` to the right-coupled `α₀ = 1` highest-weight vector. -/
@[simp] theorem clebschGordanRightInclusion_vec_zero (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ 0) =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
        (clebschGordanVector q m ε (n + p - 2 * (r : ℕ)) (δ * ζ) s) := by
  simp [clebschGordanRightInclusion]

/-- On an outer `j = 0` channel, `clebschGordanLeftInclusion` sends `v₀` to `w_i ⊗ v₀`. -/
theorem clebschGordanLeftInclusion_zero_vec_zero (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) :
    clebschGordanLeftInclusion (p := p) (ε := ε) (δ := δ) (ζ := ζ) hq i 0 (vec q _ _ 0) =
      tmul ℂ (UqSl2 q) (clebschGordanVector q m ε n δ i) (vec q p ζ 0) := by
  rw [clebschGordanLeftInclusion_vec_zero]; simp

/-- On an outer `s = 0` channel, `clebschGordanRightInclusion` sends `v₀` to `v₀ ⊗ w_r`. -/
theorem clebschGordanRightInclusion_zero_vec_zero (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) :
    clebschGordanRightInclusion (m := m) (ε := ε) (δ := δ) (ζ := ζ) hq r 0 (vec q _ _ 0) =
      tmul ℂ (UqSl2 q) (vec q m ε 0) (clebschGordanVector q n δ p ζ r) := by
  rw [clebschGordanRightInclusion_vec_zero]; simp

/-- `clebschGordanLeftInclusion` sends `v_l` to the normalized `F`-ladder string of `v₀`. -/
theorem clebschGordanLeftInclusion_vec (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℕ) :
    clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ l) =
      (∏ c ∈ Finset.range l, quantumInteger q (c + 1))⁻¹ •
        f q ^ l • clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0) := by
  conv_lhs => rw [clebschGordanLeftInclusion, LinearMap.comp_apply, clebschGordanInclusion_vec,
    LinearMap.map_smul_of_tower, map_smul]
  rw [clebschGordanLeftInclusion_vec_zero]

/-- `clebschGordanRightInclusion` sends `v_l` to the normalized `F`-ladder string of `v₀`. -/
theorem clebschGordanRightInclusion_vec (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℕ) :
    clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ l) =
      (∏ c ∈ Finset.range l, quantumInteger q (c + 1))⁻¹ •
        f q ^ l • clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ 0) := by
  conv_lhs => rw [clebschGordanRightInclusion, LinearMap.comp_apply, clebschGordanInclusion_vec,
    LinearMap.map_smul_of_tower, map_smul]
  rw [clebschGordanRightInclusion_vec_zero]

/-- Left channel projection is a left inverse to left channel inclusion. -/
@[simp] theorem clebschGordanLeftProjection_inclusion_self (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftProjection hq i j (clebschGordanLeftInclusion hq i j x) = x := by
  rw [clebschGordanLeftInclusion_eq_single, clebschGordanLeftProjection_eq_symm,
    LinearEquiv.symm_apply_apply]; simp

/-- Right channel projection is a left inverse to right channel inclusion. -/
@[simp] theorem clebschGordanRightProjection_inclusion_self (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightProjection hq r s (clebschGordanRightInclusion hq r s x) = x := by
  rw [clebschGordanRightInclusion_eq_single, clebschGordanRightProjection_eq_symm,
    LinearEquiv.symm_apply_apply]; simp

/-- Distinct left-associated channels are annihilated by `clebschGordanLeftProjection`. -/
@[simp] theorem clebschGordanLeftProjection_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {i₁ i₂ : Fin (min m n + 1)} {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)}
    {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)}
    (h : (i₁ : ℕ) ≠ (i₂ : ℕ) ∨ (j₁ : ℕ) ≠ (j₂ : ℕ))
    (x : LadderModule q (m + n - 2 * (i₂ : ℕ) + p - 2 * (j₂ : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanLeftProjection hq i₁ j₁ (clebschGordanLeftInclusion hq i₂ j₂ x) = 0 := by
  rw [clebschGordanLeftInclusion_eq_single, clebschGordanLeftProjection_eq_symm,
    LinearEquiv.symm_apply_apply]
  by_cases hi : i₁ = i₂
  · subst hi; simp [Pi.single_eq_of_ne (fun hj : j₁ = j₂ => by subst hj; simp at h)]
  · simp [Pi.single_eq_of_ne hi]

/-- Distinct right-associated channels are annihilated by `clebschGordanRightProjection`. -/
@[simp] theorem clebschGordanRightProjection_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {r₁ r₂ : Fin (min n p + 1)} {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)}
    {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)}
    (h : (r₁ : ℕ) ≠ (r₂ : ℕ) ∨ (s₁ : ℕ) ≠ (s₂ : ℕ))
    (x : LadderModule q (m + (n + p - 2 * (r₂ : ℕ)) - 2 * (s₂ : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRightProjection hq r₁ s₁ (clebschGordanRightInclusion hq r₂ s₂ x) = 0 := by
  rw [clebschGordanRightInclusion_eq_single, clebschGordanRightProjection_eq_symm,
    LinearEquiv.symm_apply_apply]
  by_cases hr : r₁ = r₂
  · subst hr; simp [Pi.single_eq_of_ne (fun hs : s₁ = s₂ => by subst hs; simp at h)]
  · simp [Pi.single_eq_of_ne hr]

/-- Composing a left channel projection with its left channel inclusion gives `LinearMap.id`. -/
@[simp] theorem clebschGordanLeftProjection_comp_inclusion_self (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    (clebschGordanLeftProjection (ε := ε) (δ := δ) (ζ := ζ) hq i j).comp
      (clebschGordanLeftInclusion hq i j) = LinearMap.id :=
  LinearMap.ext (clebschGordanLeftProjection_inclusion_self hq i j)

/-- Composing a right channel projection with its right channel inclusion gives `LinearMap.id`. -/
@[simp] theorem clebschGordanRightProjection_comp_inclusion_self (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    (clebschGordanRightProjection (ε := ε) (δ := δ) (ζ := ζ) hq r s).comp
      (clebschGordanRightInclusion hq r s) = LinearMap.id :=
  LinearMap.ext (clebschGordanRightProjection_inclusion_self hq r s)

/-- Composing a left channel projection with a distinct left channel inclusion gives `0`. -/
@[simp] theorem clebschGordanLeftProjection_comp_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {i₁ i₂ : Fin (min m n + 1)} {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)}
    {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)}
    (h : (i₁ : ℕ) ≠ (i₂ : ℕ) ∨ (j₁ : ℕ) ≠ (j₂ : ℕ)) :
    (clebschGordanLeftProjection (ε := ε) (δ := δ) (ζ := ζ) hq i₁ j₁).comp
      (clebschGordanLeftInclusion hq i₂ j₂) = 0 :=
  LinearMap.ext (clebschGordanLeftProjection_inclusion_of_ne hq h)

/-- Composing a right channel projection with a distinct right channel inclusion gives `0`. -/
@[simp] theorem clebschGordanRightProjection_comp_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {r₁ r₂ : Fin (min n p + 1)} {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)}
    {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)}
    (h : (r₁ : ℕ) ≠ (r₂ : ℕ) ∨ (s₁ : ℕ) ≠ (s₂ : ℕ)) :
    (clebschGordanRightProjection (ε := ε) (δ := δ) (ζ := ζ) hq r₁ s₁).comp
      (clebschGordanRightInclusion hq r₂ s₂) = 0 :=
  LinearMap.ext (clebschGordanRightProjection_inclusion_of_ne hq h)

/-- Channel-to-channel recoupling intertwiner `(i, j) → (r, s)` through `BialgebraModule.assoc`. -/
def recouplingHom (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (clebschGordanRightProjection hq r s).comp
    ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
      (LadderModule q p ζ)).toLinearMap.comp (clebschGordanLeftInclusion hq i j))

/-- Definitional composite formula for `recouplingHom`. -/
theorem recouplingHom_def (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s =
      (clebschGordanRightProjection hq r s).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).toLinearMap.comp (clebschGordanLeftInclusion hq i j)) := (rfl)

/-- Inverse recoupling intertwiner `(r, s) → (i, j)` through `(BialgebraModule.assoc).symm`. -/
def invRecouplingHom (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (clebschGordanLeftProjection hq i j).comp
    ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
      (LadderModule q p ζ)).symm.toLinearMap.comp (clebschGordanRightInclusion hq r s))

/-- Definitional composite formula for `invRecouplingHom`. -/
theorem invRecouplingHom_def (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j =
      (clebschGordanLeftProjection hq i j).comp ((assoc ℂ (UqSl2 q) (LadderModule q m ε)
        (LadderModule q n δ) (LadderModule q p ζ)).symm.toLinearMap.comp
          (clebschGordanRightInclusion hq r s)) := (rfl)

/-- `recouplingHom` agrees with coordinate `(r, s)` of `clebschGordanRecouplingEquiv`. -/
theorem recouplingHom_apply (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    recouplingHom hq i j r s x =
      clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)) r s :=
  (clebschGordanRecouplingEquiv_single_apply hq i j r s x).symm

/-- `invRecouplingHom` agrees with coordinate `(i, j)` of `(clebschGordanRecouplingEquiv).symm`. -/
theorem invRecouplingHom_apply (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    invRecouplingHom hq r s i j x =
      (clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)) i j :=
  (clebschGordanRecouplingEquiv_symm_single_apply hq i j r s x).symm

/-! ### Recoupling scalars, basis expansions, and channel orthogonality -/

section RecouplingScalars

omit [Fact (q ≠ 0)]

/-- Scalar recoupling coefficient from left channel `(i, j)` to right channel `(r, s)`. -/
def recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) : ℂ :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  schurScalar (recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s)

/-- Definitional Schur-scalar formula for `recouplingCoeff`. -/
theorem recouplingCoeff_def [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingCoeff hq ε δ ζ i j r s =
      schurScalar (recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s) := (rfl)

/-- Inverse scalar recoupling coefficient from right channel `(r, s)` to left channel `(i, j)`. -/
def invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) : ℂ :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  schurScalar (invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j)

/-- Definitional Schur-scalar formula for `invRecouplingCoeff`. -/
theorem invRecouplingCoeff_def [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingCoeff hq ε δ ζ r s i j =
      schurScalar (invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j) := (rfl)

/-- Congruence of `recouplingCoeff` along equality of underlying natural-number indices. -/
theorem recouplingCoeff_congr (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i₁ i₂ : Fin (min m n + 1)} {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)}
    {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)} {r₁ r₂ : Fin (min n p + 1)}
    {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)} {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)}
    (hi : (i₁ : ℕ) = (i₂ : ℕ)) (hj : (j₁ : ℕ) = (j₂ : ℕ))
    (hr : (r₁ : ℕ) = (r₂ : ℕ)) (hs : (s₁ : ℕ) = (s₂ : ℕ)) :
    recouplingCoeff hq ε δ ζ i₁ j₁ r₁ s₁ = recouplingCoeff hq ε δ ζ i₂ j₂ r₂ s₂ := by
  obtain rfl := Fin.ext hi; obtain rfl := Fin.ext hj
  obtain rfl := Fin.ext hr; obtain rfl := Fin.ext hs; rfl

/-- Congruence of `invRecouplingCoeff` along equality of underlying natural-number indices. -/
theorem invRecouplingCoeff_congr (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {r₁ r₂ : Fin (min n p + 1)} {s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1)}
    {s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)} {i₁ i₂ : Fin (min m n + 1)}
    {j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1)} {j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)}
    (hr : (r₁ : ℕ) = (r₂ : ℕ)) (hs : (s₁ : ℕ) = (s₂ : ℕ))
    (hi : (i₁ : ℕ) = (i₂ : ℕ)) (hj : (j₁ : ℕ) = (j₂ : ℕ)) :
    invRecouplingCoeff hq ε δ ζ r₁ s₁ i₁ j₁ = invRecouplingCoeff hq ε δ ζ r₂ s₂ i₂ j₂ := by
  obtain rfl := Fin.ext hr; obtain rfl := Fin.ext hs
  obtain rfl := Fin.ext hi; obtain rfl := Fin.ext hj; rfl

/-- `recouplingCoeff` vanishes when the left and right channels have distinct total weights. -/
theorem recouplingCoeff_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {r : Fin (min n p + 1)}
    {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    (hne : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) ≠ m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) :
    recouplingCoeff hq ε δ ζ i j r s = 0 :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩; schurScalar_eq_zero_of_ne hq (.inl hne) _

/-- `invRecouplingCoeff` vanishes when the right and left channels have distinct total weights. -/
theorem invRecouplingCoeff_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {i : Fin (min m n + 1)}
    {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    (hne : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) ≠ m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) :
    invRecouplingCoeff hq ε δ ζ r s i j = 0 :=
  letI : Fact (q ≠ 0) := ⟨hq.ne_zero⟩; schurScalar_eq_zero_of_ne hq (.inl hne) _

/-- `recouplingCoeff` vanishes when the right outer coupling to `k` is inadmissible. -/
theorem recouplingCoeff_eq_zero_of_not_channel_right (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {r : Fin (min n p + 1)}
    {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {k : ℕ}
    (hk : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = k)
    (hnot : ¬ IsClebschGordanChannel m (n + p - 2 * (r : ℕ)) k) :
    recouplingCoeff hq ε δ ζ i j r s = 0 :=
  recouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hnot (isClebschGordanChannel_def.mpr ⟨s, heq.symm.trans hk⟩)

/-- `recouplingCoeff` vanishes off the unique right outer index `hmv.index` for total weight `k`. -/
theorem recouplingCoeff_eq_zero_of_ne_index_right (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {r : Fin (min n p + 1)}
    {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {k : ℕ}
    (hk : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = k)
    (hmv : IsClebschGordanChannel m (n + p - 2 * (r : ℕ)) k) (hs : s ≠ hmv.index) :
    recouplingCoeff hq ε δ ζ i j r s = 0 :=
  recouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hs (hmv.index_eq_of_eq (heq.symm.trans hk)).symm

/-- `recouplingCoeff` vanishes when the left outer coupling to `k` is inadmissible. -/
theorem recouplingCoeff_eq_zero_of_not_channel_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {r : Fin (min n p + 1)}
    {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {k : ℕ}
    (hk : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k)
    (hnot : ¬ IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k) :
    recouplingCoeff hq ε δ ζ i j r s = 0 :=
  recouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hnot (isClebschGordanChannel_def.mpr ⟨j, heq.trans hk⟩)

/-- `recouplingCoeff` vanishes off the unique left outer index `hup.index` for total weight `k`. -/
theorem recouplingCoeff_eq_zero_of_ne_index_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {r : Fin (min n p + 1)}
    {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {k : ℕ}
    (hk : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k)
    (hup : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k) (hj : j ≠ hup.index) :
    recouplingCoeff hq ε δ ζ i j r s = 0 :=
  recouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hj (hup.index_eq_of_eq (heq.trans hk)).symm

/-- `invRecouplingCoeff` vanishes when the left outer coupling to `k` is inadmissible. -/
theorem invRecouplingCoeff_eq_zero_of_not_channel_left (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {k : ℕ}
    (hk : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k)
    (hnot : ¬ IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k) :
    invRecouplingCoeff hq ε δ ζ r s i j = 0 :=
  invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hnot (isClebschGordanChannel_def.mpr ⟨j, heq.symm.trans hk⟩)

/-- `invRecouplingCoeff` vanishes off the unique left outer index `hup.index` for weight `k`. -/
theorem invRecouplingCoeff_eq_zero_of_ne_index_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)} {i : Fin (min m n + 1)}
    {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)} {k : ℕ}
    (hk : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k)
    (hup : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k) (hj : j ≠ hup.index) :
    invRecouplingCoeff hq ε δ ζ r s i j = 0 :=
  invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ fun heq =>
    hj (hup.index_eq_of_eq (heq.symm.trans hk)).symm

end RecouplingScalars

/-- `recouplingHom` acts on every ladder vector `v_l` by multiplication by `recouplingCoeff`. -/
@[simp] theorem recouplingHom_vec (hq : IsGenericQuantumParameter q) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    recouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq i j r s (vec q _ _ l) =
      recouplingCoeff hq ε δ ζ i j r s • vec q _ _ l :=
  apply_vec_eq_schurScalar_smul hq _ l

/-- `invRecouplingHom` acts on every ladder vector `v_l` by `invRecouplingCoeff`. -/
@[simp] theorem invRecouplingHom_vec (hq : IsGenericQuantumParameter q) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    invRecouplingHom (ε := ε) (δ := δ) (ζ := ζ) hq r s i j (vec q _ _ l) =
      invRecouplingCoeff hq ε δ ζ r s i j • vec q _ _ l :=
  apply_vec_eq_schurScalar_smul hq _ l

/-- Action of `clebschGordanRecouplingEquiv` on every ladder vector `v_l` of a left channel. -/
@[simp] theorem clebschGordanRecouplingEquiv_single_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (r : Fin (min n p + 1))
    (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq
        (Pi.single i (Pi.single j (vec q _ _ l))) r s =
      recouplingCoeff hq ε δ ζ i j r s • vec q _ _ l := by
  rw [← recouplingHom_apply, recouplingHom_vec]

/-- Action of `(clebschGordanRecouplingEquiv).symm` on every `v_l` of a right channel. -/
@[simp] theorem clebschGordanRecouplingEquiv_symm_single_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (i : Fin (min m n + 1))
    (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm
        (Pi.single r (Pi.single s (vec q _ _ l))) i j =
      invRecouplingCoeff hq ε δ ζ r s i j • vec q _ _ l := by
  rw [← invRecouplingHom_apply, invRecouplingHom_vec]

/-- Operator-level expansion of `assoc` composed with `clebschGordanLeftInclusion`. -/
theorem assoc_comp_clebschGordanLeftInclusion (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).toLinearMap.comp (clebschGordanLeftInclusion hq i j) =
      ∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        (clebschGordanRightInclusion hq r s).comp (recouplingHom hq i j r s) := by
  ext x; rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    clebschGordanLeftInclusion_eq_single, ← clebschGordanRightEquiv_recoupling hq]
  conv_lhs => rw [← Finset.univ_sum_single_single
    (clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)))]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    ← clebschGordanRightInclusion_eq_single, recouplingHom_apply]

/-- Operator-level inverse expansion of `assoc.symm` composed with `clebschGordanRightInclusion`. -/
theorem assoc_symm_comp_clebschGordanRightInclusion (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
        (LadderModule q p ζ)).symm.toLinearMap.comp (clebschGordanRightInclusion hq r s) =
      ∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        (clebschGordanLeftInclusion hq i j).comp (invRecouplingHom hq r s i j) := by
  ext x; rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    clebschGordanRightInclusion_eq_single, ← clebschGordanLeftEquiv_recoupling_symm hq]
  conv_lhs => rw [← Finset.univ_sum_single_single
    ((clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)))]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    ← clebschGordanLeftInclusion_eq_single, invRecouplingHom_apply]

/-- **Triple-product recoupling expansion.** Under `BialgebraModule.assoc`, every `v_l` of left
channel `(i, j)` expands in the right-channel `v_l` with coefficients `recouplingCoeff`. -/
theorem assoc_clebschGordanLeftInclusion_vec (hq : IsGenericQuantumParameter q)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (l : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)
        (clebschGordanLeftInclusion hq i j (vec q _ _ l)) =
      ∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        recouplingCoeff hq ε δ ζ i j r s • clebschGordanRightInclusion hq r s (vec q _ _ l) := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.sum_apply,
    recouplingHom_vec, LinearMap.map_smul_of_tower] using LinearMap.congr_fun
    (assoc_comp_clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j) (vec q _ _ l)

/-- **Inverse triple-product recoupling expansion.** Under `(BialgebraModule.assoc).symm`, every
`v_l` of right channel `(r, s)` expands in the left-channel `v_l` via `invRecouplingCoeff`. -/
theorem assoc_symm_clebschGordanRightInclusion_vec (hq : IsGenericQuantumParameter q)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (l : ℤ) :
    (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)).symm
        (clebschGordanRightInclusion hq r s (vec q _ _ l)) =
      ∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        invRecouplingCoeff hq ε δ ζ r s i j • clebschGordanLeftInclusion hq i j (vec q _ _ l) := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.sum_apply,
    invRecouplingHom_vec, LinearMap.map_smul_of_tower] using LinearMap.congr_fun
    (assoc_symm_comp_clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s) (vec q _ _ l)

omit [Fact (q ≠ 0)] in
/-- Channel-summed left orthogonality of `invRecouplingCoeff` and `recouplingCoeff`. -/
theorem sum_invRecouplingCoeff_mul_recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i₁ i₂ : Fin (min m n + 1)) (j₁ : Fin (min (m + n - 2 * (i₁ : ℕ)) p + 1))
    (j₂ : Fin (min (m + n - 2 * (i₂ : ℕ)) p + 1)) :
    (∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
      invRecouplingCoeff hq ε δ ζ r s i₁ j₁ * recouplingCoeff hq ε δ ζ i₂ j₂ r s) =
      if (i₁ : ℕ) = (i₂ : ℕ) ∧ (j₁ : ℕ) = (j₂ : ℕ) then 1 else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have h := congrArg (fun y => clebschGordanLeftProjection hq i₁ j₁
      ((assoc ℂ (UqSl2 q) _ _ _).symm y))
    (assoc_clebschGordanLeftInclusion_vec (ε := ε) (δ := δ) (ζ := ζ) hq i₂ j₂ 0)
  have hinv (r) (s) : clebschGordanLeftProjection hq i₁ j₁ ((assoc ℂ (UqSl2 q) _ _ _).symm
        (clebschGordanRightInclusion (ε := ε) (δ := δ) (ζ := ζ) hq r s (vec q _ _ 0))) =
      invRecouplingCoeff hq ε δ ζ r s i₁ j₁ • vec q _ _ 0 := by
    simpa [invRecouplingHom_def] using
      invRecouplingHom_vec (ε := ε) (δ := δ) (ζ := ζ) hq r s i₁ j₁ 0
  simp only [LinearEquiv.symm_apply_apply, map_sum, LinearMap.map_smul_of_tower,
    LinearMapClass.map_smul_of_tower (assoc ℂ (UqSl2 q) _ _ _).symm, hinv, smul_smul,
    mul_comm (recouplingCoeff _ _ _ _ _ _ _ _), ← Finset.sum_smul] at h
  refine smul_left_injective ℂ (by simp : vec q _ _ 0 ≠ 0) (h.symm.trans ?_)
  dsimp only
  split_ifs with hij
  · obtain rfl := Fin.ext hij.1; obtain rfl := Fin.ext hij.2
    rw [clebschGordanLeftProjection_inclusion_self, one_smul]
  · rw [clebschGordanLeftProjection_inclusion_of_ne hq (not_and_or.mp hij), zero_smul]

omit [Fact (q ≠ 0)] in
/-- Channel-summed right orthogonality of `recouplingCoeff` and `invRecouplingCoeff`. -/
theorem sum_recouplingCoeff_mul_invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r₁ r₂ : Fin (min n p + 1)) (s₁ : Fin (min m (n + p - 2 * (r₁ : ℕ)) + 1))
    (s₂ : Fin (min m (n + p - 2 * (r₂ : ℕ)) + 1)) :
    (∑ i : Fin (min m n + 1), ∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
      recouplingCoeff hq ε δ ζ i j r₁ s₁ * invRecouplingCoeff hq ε δ ζ r₂ s₂ i j) =
      if (r₁ : ℕ) = (r₂ : ℕ) ∧ (s₁ : ℕ) = (s₂ : ℕ) then 1 else 0 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have h := congrArg (fun y => clebschGordanRightProjection hq r₁ s₁ (assoc ℂ (UqSl2 q) _ _ _ y))
    (assoc_symm_clebschGordanRightInclusion_vec (ε := ε) (δ := δ) (ζ := ζ) hq r₂ s₂ 0)
  have hrec (i) (j) : clebschGordanRightProjection hq r₁ s₁ (assoc ℂ (UqSl2 q) _ _ _
        (clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0))) =
      recouplingCoeff hq ε δ ζ i j r₁ s₁ • vec q _ _ 0 := by
    simpa [recouplingHom_def] using recouplingHom_vec (ε := ε) (δ := δ) (ζ := ζ) hq i j r₁ s₁ 0
  simp only [LinearEquiv.apply_symm_apply, map_sum, LinearMap.map_smul_of_tower,
    LinearMapClass.map_smul_of_tower (assoc ℂ (UqSl2 q) _ _ _), hrec, smul_smul,
    mul_comm (invRecouplingCoeff _ _ _ _ _ _ _ _), ← Finset.sum_smul] at h
  refine smul_left_injective ℂ (by simp : vec q _ _ 0 ≠ 0) (h.symm.trans ?_)
  dsimp only
  split_ifs with hrs
  · obtain rfl := Fin.ext hrs.1; obtain rfl := Fin.ext hrs.2
    rw [clebschGordanRightProjection_inclusion_self, one_smul]
  · rw [clebschGordanRightProjection_inclusion_of_ne hq (not_and_or.mp hrs), zero_smul]

end TauCeti.UqSl2
