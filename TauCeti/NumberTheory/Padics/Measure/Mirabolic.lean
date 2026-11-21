/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Affine.Topology
public import TauCeti.NumberTheory.Padics.MirabolicPsiModule
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi

/-!
# Measures on `ℤ_p` as a `(P(ℤ_p), ψ)`-module

The mirabolic group `P(ℤ_p) = ℤ_p ⋊ ℤ_pˣ`, realised as `TauCeti.AffineGroup ℤ_[p]`, acts on
`ℤ_p` by the affine maps `x ↦ b + a x`, hence on measures on `ℤ_p` by pushforward. Together with
the operator `ψ` (restriction to `pℤ_p` followed by `p x ↦ x`), this makes the measures on `ℤ_p`
a `(P(ℤ_p), ψ)`-module: pushing forward along `x ↦ p b + a x` and then applying `ψ` is the same
as applying `ψ` and then pushing forward along `x ↦ b + a x`. This is the basic example of
Colmez's construction `M ⊠ ℚ_p`, which for this module plays the role of the measures on `ℚ_p`:
the Dirac measure at `x ∈ ℚ_p` has coordinates the Dirac measures at `p^n x` (or `0` when
`p^n x ∉ ℤ_p`), and `P(ℚ_p)` acts on these through its affine action on `ℚ_p`.

## Main definitions

* `AbstractMeasure.affineRep`: the representation of `P(ℤ_p)` on measures by pushforward.
* `AbstractMeasure.mirabolicPsiModule`: measures on `ℤ_p` as a `(P(ℤ_p), ψ)`-module.
* `AbstractMeasure.diracQp`: the Dirac measure at a point of `ℚ_p`, as an element of
  `D(ℤ_p) ⊠ ℚ_p`.

## Main results

* `AbstractMeasure.psiMeasure_comp_affineRep`: `ψ ∘ (p b, a) = (b, a) ∘ ψ` on measures.
* `AbstractMeasure.boxtimesRep_diracQp`: `g ∈ P(ℚ_p)` sends the Dirac measure at `x` to the
  Dirac measure at `g • x`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §5 and §I.3.3.
-/

public noncomputable section

open ContinuousMap TauCeti
open scoped AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

variable {R : Type*} [NormedCommRing R]

variable (p R) in
/-- The representation of `P(ℤ_p)` on measures on `ℤ_p` by pushforward along the affine maps
`x ↦ b + a x`. -/
def affineRep : Representation R (AffineGroup ℤ_[p]) D(ℤ_[p], R) where
  toFun g := map (g.toContinuousMap)
  map_one' := by
    ext μ f
    simp only [map_apply, one_apply_eq_self]
    congr 1
    ext x
    simp
  map_mul' g h := by
    ext μ f
    simp only [map_apply, mul_apply_eq_comp]
    congr 1
    ext x
    simp [mul_smul]

/-- `(b, a) ∈ P(ℤ_p)` sends `μ` to its pushforward along `x ↦ b + a x`. -/
theorem affineRep_apply (g : AffineGroup ℤ_[p]) (μ : D(ℤ_[p], R)) :
    affineRep p R g μ = map (g.toContinuousMap) μ :=
  (rfl)

/-- `(b, a) ∈ P(ℤ_p)` sends the Dirac measure at `x` to the Dirac measure at `b + a x`. -/
@[simp]
theorem affineRep_dirac (g : AffineGroup ℤ_[p]) (x : ℤ_[p]) :
    affineRep p R g (dirac R x) = dirac R (g • x) := by
  rw [affineRep_apply, map_dirac, AffineGroup.toContinuousMap_apply]

local instance : ContinuousMul C(ℤ_[p], R) :=
  ContinuousMap.instContinuousMulOfLocallyCompactSpace

/-- **`ψ ∘ (p b, a) = (b, a) ∘ ψ` on measures**: restricting the pushforward along
`x ↦ p b + a x` to `pℤ_p` and transporting by `p x ↦ x` is the pushforward along `x ↦ b + a x`
of `ψ μ`. -/
theorem psiMeasure_comp_affineRep (b : ℤ_[p]) (a : ℤ_[p]ˣ) :
    psiMeasure ∘ₗ affineRep p R ⟨.ofAdd ((p : ℤ_[p]) * b), a⟩ =
      affineRep p R ⟨.ofAdd b, a⟩ ∘ₗ psiMeasure := by
  ext μ f
  simp only [LinearMap.comp_apply, psiMeasure_apply, affineRep_apply, map_apply]
  congr 1
  ext x
  simp only [ContinuousMap.mul_apply, comp_apply, AffineGroup.toContinuousMap_apply,
    AffineGroup.smul_def, toAdd_ofAdd]
  by_cases hx : (p : ℤ_[p]) ∣ x
  · obtain ⟨y, rfl⟩ := hx
    have hy : (p : ℤ_[p]) * b + a * (p * y) = p * (b + a * y) := by ring
    rw [hy, pMultiplesIndicator_eq_one (dvd_mul_right _ _),
      pMultiplesIndicator_eq_one (dvd_mul_right _ _), PadicInt.divideByP_mul,
      PadicInt.divideByP_mul]
  · have hx' : ¬(p : ℤ_[p]) ∣ (p : ℤ_[p]) * b + a * x := fun h ↦
      hx ((Units.dvd_mul_left (u := a)).mp ((dvd_add_right (dvd_mul_right _ b)).mp h))
    rw [pMultiplesIndicator_eq_zero hx, pMultiplesIndicator_eq_zero hx', zero_mul, zero_mul]

variable (p R) in
/-- Measures on `ℤ_p`, with the affine pushforward action of `P(ℤ_p)` and the operator `ψ`, form
a `(P(ℤ_p), ψ)`-module. -/
def mirabolicPsiModule : MirabolicPsiModule p R D(ℤ_[p], R) where
  ρ := affineRep p R
  ψ := psiMeasure
  ψ_comp_ρ := psiMeasure_comp_affineRep

@[simp]
theorem mirabolicPsiModule_ρ : (mirabolicPsiModule p R).ρ = affineRep p R :=
  (rfl)

@[simp]
theorem mirabolicPsiModule_ψ : (mirabolicPsiModule p R).ψ = psiMeasure :=
  (rfl)

/-! ### Dirac measures on `ℚ_p` -/

variable (R) in
/-- The coordinates of the Dirac measure at `x ∈ ℚ_p`: the `n`-th is the Dirac measure at
`p^n x` if `p^n x ∈ ℤ_p`, and `0` otherwise. -/
private def diracSeq (x : ℚ_[p]) (n : ℕ) : D(ℤ_[p], R) :=
  if h : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 then dirac R (Padic.lift _ h) else 0

private theorem diracSeq_of_norm_le_one {x : ℚ_[p]} {n : ℕ} (h : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    diracSeq R x n = dirac R (Padic.lift _ h) := by
  rw [diracSeq, dite_eq_left_of_eq_true (eq_true h)]

private theorem diracSeq_of_not_norm_le_one {x : ℚ_[p]} {n : ℕ} (h : ¬‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    diracSeq R x n = 0 := by
  rw [diracSeq, dite_eq_right_of_eq_false (eq_false h)]

private theorem diracSeq_mem_boxtimesQp (x : ℚ_[p]) :
    diracSeq R x ∈ (mirabolicPsiModule p R).boxtimesQp := by
  refine (MirabolicPsiModule.mem_boxtimesQp _).mpr fun n ↦ ?_
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hnorm : ‖(p : ℚ_[p]) ^ (n + 1) * x‖ = (p : ℝ)⁻¹ * ‖(p : ℚ_[p]) ^ n * x‖ := by
    rw [pow_succ', mul_assoc, norm_mul, Padic.norm_p]
  rw [mirabolicPsiModule_ψ]
  by_cases h0 : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1
  · have h1 : ‖(p : ℚ_[p]) ^ (n + 1) * x‖ ≤ 1 := by
      rw [hnorm]
      calc (p : ℝ)⁻¹ * ‖(p : ℚ_[p]) ^ n * x‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr
        _ ≤ 1 := by
          rw [mul_one]
          exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)
    have hpn : Padic.lift _ h1 = (p : ℤ_[p]) * Padic.lift _ h0 :=
      PadicInt.ext (by simp [pow_succ', mul_assoc])
    rw [diracSeq_of_norm_le_one h1, diracSeq_of_norm_le_one h0, hpn, psiMeasure_dirac_mul]
  · rw [diracSeq_of_not_norm_le_one h0]
    by_cases h1 : ‖(p : ℚ_[p]) ^ (n + 1) * x‖ ≤ 1
    · rw [diracSeq_of_norm_le_one h1, psiMeasure_dirac_of_not_dvd]
      rintro ⟨y, hy⟩
      refine h0 ?_
      have hy' : (p : ℚ_[p]) ^ n * x = y := by
        have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hy
        simp only [PadicInt.coe_lift, PadicInt.coe_mul, PadicInt.coe_natCast, pow_succ',
          mul_assoc] at this
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp) this
      rw [hy']
      exact PadicInt.norm_le_one y
    · rw [diracSeq_of_not_norm_le_one h1, map_zero]

variable (R) in
/-- The Dirac measure at `x ∈ ℚ_p`, as an element of `D(ℤ_p) ⊠ ℚ_p`. -/
def diracQp (x : ℚ_[p]) : (mirabolicPsiModule p R).boxtimesQp :=
  ⟨diracSeq R x, diracSeq_mem_boxtimesQp x⟩

/-- If `p^n x ∈ ℤ_p`, the `n`-th coordinate of the Dirac measure at `x ∈ ℚ_p` is the Dirac
measure at `p^n x ∈ ℤ_p`. -/
theorem coe_diracQp_of_norm_le_one {x : ℚ_[p]} {n : ℕ} (h : ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    (diracQp R x : ℕ → D(ℤ_[p], R)) n = dirac R (Padic.lift _ h) :=
  diracSeq_of_norm_le_one h

/-- If `p^n x ∉ ℤ_p`, the `n`-th coordinate of the Dirac measure at `x ∈ ℚ_p` vanishes. -/
theorem coe_diracQp_of_not_norm_le_one {x : ℚ_[p]} {n : ℕ} (h : ¬‖(p : ℚ_[p]) ^ n * x‖ ≤ 1) :
    (diracQp R x : ℕ → D(ℤ_[p], R)) n = 0 :=
  diracSeq_of_not_norm_le_one h

/-- **`P(ℚ_p)` acts on Dirac measures through its affine action on `ℚ_p`**: `(a b; 0 1)` sends
the Dirac measure at `x` to the Dirac measure at `a x + b`. -/
theorem boxtimesRep_diracQp (g : AffineGroup ℚ_[p]) (x : ℚ_[p]) :
    (mirabolicPsiModule p R).boxtimesRep g (diracQp R x) = diracQp R (g • x) := by
  refine Subtype.ext (funext fun n ↦ ?_)
  obtain ⟨m, l, h, hnm, hh⟩ := AffineGroup.exists_map_eq_padicPhi_pow_mul_mul_inv_pow g n
  rw [MirabolicPsiModule.boxtimesRep_apply_coe _ _ hnm hh,
    ← MirabolicPsiModule.ψ_pow_sub_boxtimesQp_coe (diracQp R (g • x)) hnm]
  congr 1
  -- `h` sends `p^l x` to `p^m (g x)`.
  have hsmul : AffineGroup.map PadicInt.Coe.ringHom h • ((p : ℚ_[p]) ^ l * x) =
      (p : ℚ_[p]) ^ m * (g • x) := by
    rw [hh, ← AffineGroup.padicPhi_pow_smul, ← AffineGroup.padicPhi_pow_smul, mul_smul,
      mul_smul, inv_smul_smul]
  have hiff := AffineGroup.norm_map_smul_le_one_iff h ((p : ℚ_[p]) ^ l * x)
  rw [hsmul] at hiff
  rw [mirabolicPsiModule_ρ]
  by_cases hl : ‖(p : ℚ_[p]) ^ l * x‖ ≤ 1
  · rw [coe_diracQp_of_norm_le_one hl, coe_diracQp_of_norm_le_one (hiff.mpr hl),
      affineRep_dirac]
    congr 1
    refine PadicInt.ext ?_
    rw [PadicInt.coe_lift, ← PadicInt.Coe.ringHom_apply, ← AffineGroup.map_smul,
      PadicInt.Coe.ringHom_apply, PadicInt.coe_lift]
    exact hsmul
  · rw [coe_diracQp_of_not_norm_le_one hl,
      coe_diracQp_of_not_norm_le_one (fun h' ↦ hl (hiff.mp h')), map_zero]

end AbstractMeasure
