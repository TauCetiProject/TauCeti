/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.NikulinDecomposition
public import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The `p`-adic realization discriminant of a Nikulin decomposition

Given a Nikulin generator decomposition `D` of a finite quadratic module `A` and a prime `p`, the
minimal `p`-adic lattice realizations of the `p`-primary generators in `D` assemble into a `p`-adic
lattice `K(q_p)` of rank `l(A_p)` whose Gram determinant is the product of their
`realizationDet`s.

This file defines `NikulinDecomposition.padicDiscriminant D p` as the square class of that integer
product in `ℚ_[p]ˣ / (ℚ_[p]ˣ)²` and establishes its structural properties:

* `NikulinDecomposition.padicRealizationDet_ne_zero` and
  `NikulinDecomposition.padicDiscriminant_eq_squareClass`: the product of `realizationDet`s is
  nonzero for every admissible decomposition, so the totalizing `d = 0` branch is never taken.
* `NikulinDecomposition.padicDiscriminant_primaryComponent`: passing from `D` to the induced
  decomposition `D.primaryComponent hp` of `primaryComponent A p` leaves `padicDiscriminant`
  unchanged.
* `NikulinDecomposition.padicDiscriminant_eq_zero_of_not_dvd_natCard`: at every prime `p ∤ #A`,
  `D.padicDiscriminant p = 0`.
* `NikulinDecomposition.exists_padicIntUnit_mul_natCard_primaryComponent` and
  `NikulinDecomposition.exists_padicIntUnit_mul_natCard`: `D.padicDiscriminant p` is represented by
  a `p`-adic integer unit multiple of `Nat.card (primaryComponent A p)`, and likewise of
  `Nat.card A`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979), Theorems 1.9.1 and 1.10.1.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u

/-- Integer product of the minimal realization determinants of the `p`-primary generators in `D`. -/
@[expose] def NikulinDecomposition.padicRealizationDet {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) (p : ℕ) : ℤ :=
  ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod

/-- **Nikulin's `discr K(q_p)`, read off a generator decomposition.** The orthogonal sum of the
minimal realizations of the `p`-primary generators of `D` is a `p`-adic lattice `K(q_p)` of rank
`l(A_p)`; its discriminant is the square class of the product of their `realizationDet`s in
`ℚ_[p]ˣ / (ℚ_[p]ˣ)²` (the `d = 0` branch only makes the function total). -/
@[expose] noncomputable def NikulinDecomposition.padicDiscriminant {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) (p : ℕ) [Fact p.Prime] : TauCeti.SquareClassGroup ℚ_[p] :=
  let d : ℤ := ((D.generators.filter fun g ↦ g.prime = p).map
    NikulinGenerator.realizationDet).prod
  if h : d = 0 then TauCeti.squareClass (1 : ℚ_[p]ˣ)
  else TauCeti.squareClass (Units.mk0 (d : ℚ_[p]) (Int.cast_ne_zero.mpr h))

namespace NikulinDecomposition

section AnyNat

variable {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)

private theorem prod_realizationDet_ne_zero {gs : List NikulinGenerator}
    (hadm : ∀ g ∈ gs, g.IsAdmissible) :
    (gs.map NikulinGenerator.realizationDet).prod ≠ 0 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_ne_zero (hadm g List.mem_cons_self).realizationDet_ne_zero
        (ih fun x hx ↦ hadm x (List.mem_cons_of_mem g hx))

/-- The integer product `D.padicRealizationDet p` is nonzero for every `p`. -/
theorem padicRealizationDet_ne_zero (p : ℕ) : D.padicRealizationDet p ≠ 0 :=
  prod_realizationDet_ne_zero fun g hg ↦ D.admissible g (List.mem_of_mem_filter hg)

private theorem prod_realizationDet_eq_prod_unitCoeff_mul_prod_natCard
    (gs : List NikulinGenerator) :
    (gs.map NikulinGenerator.realizationDet).prod =
      (gs.map NikulinGenerator.unitCoeff).prod *
        ((gs.map fun g ↦ Nat.card g.toFiniteQuadraticModule).prod : ℤ) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons, ih,
        NikulinGenerator.realizationDet_eq_unitCoeff_mul_natCard, Nat.cast_mul]
      ring

/-- At a prime `p`, `D.padicRealizationDet p` factors as the product of the `p`-primary unit
coefficients times `Nat.card (primaryComponent A p)`. -/
theorem padicRealizationDet_eq_prod_unitCoeff_mul_natCard_primaryComponent {p : ℕ} (hp : p.Prime) :
    D.padicRealizationDet p =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.unitCoeff).prod *
        (Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℤ) := by
  rw [padicRealizationDet, prod_realizationDet_eq_prod_unitCoeff_mul_prod_natCard,
    ← NikulinDecomposition.primaryComponent_generators D hp, (D.primaryComponent hp).natCard_eq]

private theorem isCoprime_prod_unitCoeff {gs : List NikulinGenerator} {p : ℕ}
    (hadm : ∀ g ∈ gs, g.IsAdmissible) (hprime : ∀ g ∈ gs, g.prime = p) :
    IsCoprime (p : ℤ) (gs.map NikulinGenerator.unitCoeff).prod := by
  induction gs with
  | nil => exact isCoprime_one_right
  | cons g gs ih =>
      rw [List.map_cons, List.prod_cons]
      have hg : IsCoprime (p : ℤ) g.unitCoeff :=
        hprime g List.mem_cons_self ▸ (hadm g List.mem_cons_self).isCoprime_prime_unitCoeff
      exact hg.mul_right (ih (fun x hx ↦ hadm x (List.mem_cons_of_mem g hx))
        (fun x hx ↦ hprime x (List.mem_cons_of_mem g hx)))

/-- The product of `unitCoeff` over the `p`-primary generators of `D` is coprime to `p`. -/
theorem isCoprime_prime_prod_unitCoeff (p : ℕ) :
    IsCoprime (p : ℤ)
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.unitCoeff).prod :=
  isCoprime_prod_unitCoeff
    (fun g hg ↦ D.admissible g (List.mem_of_mem_filter hg))
    (fun _ hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2)

/-- If `p` does not divide `Nat.card A`, then `D` contains no `p`-primary generators. -/
theorem filter_prime_eq_nil_of_not_dvd_natCard {p : ℕ} (hndvd : ¬ p ∣ Nat.card A) :
    (D.generators.filter fun g ↦ g.prime = p) = [] := by
  rw [List.filter_eq_nil_iff]
  intro g hg
  rw [decide_eq_true_iff]
  rintro rfl
  apply hndvd
  have hg_adm := D.admissible g hg
  obtain ⟨n, hn⟩ := g.exists_pow_natCard
  have hn_pos : 0 < n := by
    have h1 : 1 < Nat.card g.toFiniteQuadraticModule :=
      ((NikulinGenerator.isAdmissible_iff g).mp hg_adm).2
    rw [hn] at h1
    exact Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h1
  have hdvd_g : g.prime ∣ Nat.card g.toFiniteQuadraticModule := by
    rw [hn]
    exact dvd_pow_self g.prime hn_pos.ne'
  have hdvd_prod : Nat.card g.toFiniteQuadraticModule ∣
      (D.generators.map fun x ↦ Nat.card x.toFiniteQuadraticModule).prod :=
    List.dvd_prod (List.mem_map_of_mem hg)
  rw [D.natCard_eq]
  exact hdvd_g.trans hdvd_prod

end AnyNat

section Padic

variable {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) (p : ℕ) [Fact p.Prime]

/-- Unfolded square-class formula for `D.padicDiscriminant p`: the `d = 0` fallback is never
used. -/
theorem padicDiscriminant_eq_squareClass :
    D.padicDiscriminant p =
      TauCeti.squareClass (Units.mk0 (D.padicRealizationDet p : ℚ_[p])
        (Int.cast_ne_zero.mpr (D.padicRealizationDet_ne_zero p))) := by
  have hne : D.padicRealizationDet p ≠ 0 := D.padicRealizationDet_ne_zero p
  -- Align the `let d` binding in `padicDiscriminant` with `padicRealizationDet`.
  change (if h : D.padicRealizationDet p = 0 then TauCeti.squareClass (1 : ℚ_[p]ˣ)
    else TauCeti.squareClass (Units.mk0 (D.padicRealizationDet p : ℚ_[p])
      (Int.cast_ne_zero.mpr h))) = _
  simp only [hne, ↓reduceDIte]

/-- Filtering `D` to the `p`-primary component preserves `padicDiscriminant p`. -/
@[simp]
theorem padicDiscriminant_primaryComponent :
    (D.primaryComponent (Fact.out : p.Prime)).padicDiscriminant p = D.padicDiscriminant p := by
  rw [padicDiscriminant_eq_squareClass, padicDiscriminant_eq_squareClass]
  congr 1
  ext
  simp only [Units.val_mk0, Int.cast_inj]
  unfold padicRealizationDet
  rw [NikulinDecomposition.primaryComponent_generators, List.filter_filter]
  simp only [Bool.and_self]

/-- At any prime `p` not dividing `Nat.card A`, the local realization discriminant is trivial in
`SquareClassGroup ℚ_[p]`. -/
theorem padicDiscriminant_eq_zero_of_not_dvd_natCard (hndvd : ¬ p ∣ Nat.card A) :
    D.padicDiscriminant p = 0 := by
  have hd1 : D.padicRealizationDet p = 1 := by
    rw [padicRealizationDet, D.filter_prime_eq_nil_of_not_dvd_natCard hndvd]
    rfl
  rw [D.padicDiscriminant_eq_squareClass p]
  have hu : Units.mk0 (D.padicRealizationDet p : ℚ_[p])
      (Int.cast_ne_zero.mpr (D.padicRealizationDet_ne_zero p)) = 1 := by
    ext
    simp [hd1]
  rw [hu, TauCeti.squareClass_one]

/-- **`p`-adic unit-ratio formula on the `p`-primary component**: `D.padicDiscriminant p` is the
square class of `u * Nat.card (primaryComponent A p)` for a `p`-adic integer unit `u : ℤ_[p]ˣ`
(explicitly, the product of the `p`-primary generator `unitCoeff`s). -/
theorem exists_padicIntUnit_mul_natCard_primaryComponent :
    ∃ (u : ℤ_[p]ˣ) (w : ℚ_[p]ˣ),
      (w : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) *
        (Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℚ_[p]) ∧
      TauCeti.squareClass w = D.padicDiscriminant p := by
  have hp : p.Prime := Fact.out
  set c : ℤ :=
    ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.unitCoeff).prod
  have hndvd : ¬ (p : ℤ) ∣ c :=
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mp (D.isCoprime_prime_prod_unitCoeff p)
  obtain ⟨u, hu⟩ := (PadicInt.isUnit_intCast_iff (p := p) (z := c)).mpr hndvd
  let w : ℚ_[p]ˣ := Units.mk0 (D.padicRealizationDet p : ℚ_[p])
    (Int.cast_ne_zero.mpr (D.padicRealizationDet_ne_zero p))
  refine ⟨u, w, ?_, (D.padicDiscriminant_eq_squareClass p).symm⟩
  have hdet := D.padicRealizationDet_eq_prod_unitCoeff_mul_natCard_primaryComponent hp
  have hucast : ((u : ℤ_[p]) : ℚ_[p]) = (c : ℚ_[p]) := by
    rw [hu]
    exact PadicInt.coe_intCast c
  -- Unfold `(w : ℚ_[p])` to `(D.padicRealizationDet p : ℚ_[p])`.
  change (D.padicRealizationDet p : ℚ_[p]) = _
  rw [hdet, Int.cast_mul, Int.cast_natCast, hucast]

/-- **`p`-adic unit-ratio formula against the global module order**: `D.padicDiscriminant p` is the
square class of `u * Nat.card A` for a `p`-adic integer unit `u : ℤ_[p]ˣ`, since the index
`[A : primaryComponent A p]` is coprime to `p` and therefore a unit in `ℤ_[p]`. -/
theorem exists_padicIntUnit_mul_natCard :
    ∃ (u : ℤ_[p]ˣ) (w : ℚ_[p]ˣ),
      (w : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (Nat.card A : ℚ_[p]) ∧
      TauCeti.squareClass w = D.padicDiscriminant p := by
  have hp : p.Prime := Fact.out
  obtain ⟨u₀, w, hw, hsq⟩ := D.exists_padicIntUnit_mul_natCard_primaryComponent p
  set idx : ℕ := (AddCommGroup.primaryComponent A p).index
  have hcop : idx.Coprime p := TauCeti.AddCommGroup.coprime_index_primaryComponent p
  have hndvd : ¬ p ∣ idx := hp.coprime_iff_not_dvd.mp hcop.symm
  obtain ⟨v, hv⟩ := (PadicInt.isUnit_natCast_iff (p := p) (n := idx)).mpr hndvd
  refine ⟨u₀ * v⁻¹, w, ?_, hsq⟩
  have hcard : (Nat.card A : ℚ_[p]) =
      (Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℚ_[p]) * (idx : ℚ_[p]) := by
    have hc : Nat.card (AddCommGroup.primaryComponent A p) * idx = Nat.card A :=
      (AddCommGroup.primaryComponent A p).card_mul_index
    exact_mod_cast hc.symm
  have hvcast : ((v : ℤ_[p]) : ℚ_[p]) = (idx : ℚ_[p]) := by
    rw [hv]
    exact PadicInt.coe_natCast idx
  have hvinv : (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (idx : ℚ_[p]) = 1 := by
    rw [← hvcast, ← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  rw [Units.val_mul, PadicInt.coe_mul, hcard, hw]
  calc ((u₀ : ℤ_[p]) : ℚ_[p]) * (Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℚ_[p])
      = ((u₀ : ℤ_[p]) : ℚ_[p]) *
          ((((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (idx : ℚ_[p])) *
          (Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℚ_[p]) := by
        rw [hvinv, mul_one]
    _ = ((u₀ : ℤ_[p]) : ℚ_[p]) * (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          ((Nat.card (FiniteQuadraticModule.primaryComponent A p) : ℚ_[p]) * (idx : ℚ_[p])) := by
        ring

end Padic

end NikulinDecomposition

-- Concrete check: the rank-two hyperbolic generator `u^{(2)}(2)` has `2`-adic realization
-- determinant `-4 = (-1) * 2²`, whose square class in `ℚ_[2]` equals the square class of `-1`.
section CheckDyadicU

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example :
    let g : NikulinGenerator := .dyadicU 1
    let D : NikulinDecomposition (orthogonalSumNikulinGenerators [g]) :=
      { generators := [g]
        admissible := fun x hx ↦ by
          rw [List.mem_singleton.mp hx]
          exact Nat.one_pos
        isometry := QuadraticMap.IsometryEquiv.refl _ }
    D.padicDiscriminant 2 = TauCeti.squareClass (-1 : ℚ_[2]ˣ) := by
  intro g D
  rw [D.padicDiscriminant_eq_squareClass 2, TauCeti.squareClass_eq_iff_isSquare_mul]
  refine ⟨Units.mk0 (2 : ℚ_[2]) (by norm_num), ?_⟩
  ext
  simp only [Units.val_mul, Units.val_mk0, Units.val_neg, Units.val_one]
  have hdet : D.padicRealizationDet 2 = -4 := rfl
  rw [hdet]
  norm_num

end CheckDyadicU

end TauCeti.FiniteQuadraticModule
