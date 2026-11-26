/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.Data.ZMod.RingHoms
public import TauCeti.LinearAlgebra.Matrix.Range
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Algebra.Module.Submodule.Map
public import TauCeti.Data.ZMod.PiReduction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Integral and p-adic sublattices modulo a prime power

Sublattices of `ℤⁿ` containing `pᵏ ℤⁿ` and sublattices of `ℤ_pⁿ` containing `pᵏ ℤ_pⁿ`
have the same finite description: submodules of `(ℤ/pᵏ)ⁿ`. This gives an order isomorphism,
compatible with the inclusion of integral vectors into p-adic vectors. In particular it
preserves flags and the number of intermediate lattices. The additive quotients are identified
by the inclusion of integral vectors, and the p-adic lattice is the p-adic span of its integral
points. These finite correspondences are the lattice-counting input to comparisons of
integral and p-adic double-coset products.

The order and quotient isomorphisms allow any coordinate type. Finiteness of the coordinate
type is needed for the span identification and the finiteness of the intervals.
The exponent zero is included.

For finite coordinates `Fin n`, we also specialize the correspondence to column sublattices
`intSublattice` and `padicSublattice` of `n × n` matrices over `ℤ` and `ℤ_p`:
* `TauCeti.pPowerSublatticeEquiv_intSublattice`,
  `TauCeti.pPowerSublatticeEquiv_symm_padicSublattice`: compatibility of
  `pPowerSublatticeEquiv` with scalar extension of matrix column sublattices.
* `TauCeti.intermediateSublatticeOrderIso`: order isomorphism between intermediate `ℤ`-sublattices
  `intSublattice n C ≤ L ≤ intSublattice n A` and intermediate `ℤ_p`-sublattices between their
  completions when `det C ∣ p ^ k` and `det A ∣ p ^ k`.
* `TauCeti.exists_det_eq_pow_and_intSublattice_eq`,
  `TauCeti.exists_det_eq_pow_and_mul_eq_map`: every `ℤ`-sublattice containing `p ^ k • ℤ^n` (and
  hence every nonsingular `ℤ_p`-matrix up to right multiplication by `GL_n(ℤ_p)`) comes from an
  integer matrix `D` with `det D = p ^ m` (`m : ℕ`).

## References

* J. A. Rhodes and T. R. Shemanske, *Bruhat–Tits buildings and Hecke operators*,
  12 June 1998 author manuscript, §3.1 Proposition 3.2 and §3.2 Lemma 3.3.
  The bounded lattice correspondence here supplies the intermediate-lattice comparison.
-/

public noncomputable section

namespace TauCeti

section General

variable (ι : Type*) (p k : ℕ) [Fact p.Prime]

/-- The coordinatewise inclusion of integral vectors into p-adic integral vectors. -/
def intVectorToPadic : (ι → ℤ) →ₗ[ℤ] (ι → ℤ_[p]) :=
  (Int.castAddHom ℤ_[p]).toIntLinearMap.compLeft ι

@[simp]
theorem intVectorToPadic_apply (x : ι → ℤ) (i : ι) :
    intVectorToPadic ι p x i = (x i : ℤ_[p]) := (rfl)

/-- Coordinatewise reduction of integral vectors modulo `pᵏ`. -/
def intVectorReduction : (ι → ℤ) →ₛₗ[Int.castRingHom (ZMod (p ^ k))] (ι → ZMod (p ^ k)) where
  __ := ZMod.piReduction ι (p ^ k)
  map_smul' _ _ := by ext; simp

omit [Fact p.Prime] in
/-- Integral reduction modulo `pᵏ` is the coordinatewise reduction `ZMod.piReduction ι (p ^ k)`. -/
theorem coe_intVectorReduction : ⇑(intVectorReduction ι p k) = ⇑(ZMod.piReduction ι (p ^ k)) :=
  (rfl)

/-- Coordinatewise reduction of p-adic integral vectors modulo `pᵏ`. -/
def padicVectorReduction : (ι → ℤ_[p]) →ₛₗ[PadicInt.toZModPow (p := p) k] (ι → ZMod (p ^ k)) where
  toFun x i := PadicInt.toZModPow k (x i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Fact p.Prime] in
@[simp]
theorem intVectorReduction_apply (x : ι → ℤ) (i : ι) :
    intVectorReduction ι p k x i = (x i : ZMod (p ^ k)) := by
  rw [coe_intVectorReduction, ZMod.piReduction_apply]

@[simp]
theorem padicVectorReduction_apply (x : ι → ℤ_[p]) (i : ι) :
    padicVectorReduction ι p k x i = PadicInt.toZModPow k (x i) := (rfl)

omit [Fact p.Prime] in
/-- Integral vectors surject onto the finite residue vectors. -/
theorem intVectorReduction_surjective : Function.Surjective (intVectorReduction ι p k) := by
  rw [coe_intVectorReduction]
  exact ZMod.piReduction_surjective ι (p ^ k)

/-- P-adic integral vectors surject onto the finite residue vectors. -/
theorem padicVectorReduction_surjective : Function.Surjective (padicVectorReduction ι p k) :=
  Function.Surjective.piMap fun _ ↦ ZMod.ringHom_surjective (PadicInt.toZModPow k)

/-- Reduction commutes with the inclusion of integral vectors into p-adic vectors. -/
@[simp]
theorem padicVectorReduction_intVectorToPadic (x : ι → ℤ) :
    padicVectorReduction ι p k (intVectorToPadic ι p x) = intVectorReduction ι p k x := by
  ext; simp

/-- Reduction and integral inclusion commute as `ℤ`-linear maps. -/
@[simp]
theorem padicVectorReduction_comp_intVectorToPadic :
    (padicVectorReduction ι p k).toAddMonoidHom.toIntLinearMap.comp (intVectorToPadic ι p) =
      (intVectorReduction ι p k).toAddMonoidHom.toIntLinearMap := by
  ext x i
  simp

omit [Fact p.Prime] in
/-- The kernel of integral reduction consists exactly of the multiples of `pᵏ`. -/
theorem mem_ker_intVectorReduction_iff (x : ι → ℤ) :
    x ∈ LinearMap.ker (intVectorReduction ι p k) ↔ ∃ y : ι → ℤ, x = (p : ℤ) ^ k • y := by
  rw [LinearMap.mem_ker, coe_intVectorReduction, ← AddMonoidHom.mem_ker, ← Nat.cast_pow]
  exact ZMod.mem_ker_piReduction_iff ι (p ^ k) x

/-- The kernel of p-adic reduction consists exactly of the multiples of `pᵏ`. -/
theorem mem_ker_padicVectorReduction_iff (x : ι → ℤ_[p]) :
    x ∈ LinearMap.ker (padicVectorReduction ι p k) ↔ ∃ y : ι → ℤ_[p], x = (p : ℤ_[p]) ^ k • y := by
  have h (i : ι) : PadicInt.toZModPow k (x i) = 0 ↔ ∃ y, x i = (p : ℤ_[p]) ^ k * y := by
    rw [PadicInt.toZModPow_eq_zero_iff_dvd, dvd_def]
  rw [LinearMap.mem_ker, funext_iff]
  simp only [padicVectorReduction_apply, Pi.zero_apply, h]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

/-- Sublattices of `ℤⁿ` containing `pᵏ ℤⁿ`, expressed as the interval above the reduction
kernel, correspond to sublattices of `ℤ_pⁿ` containing `pᵏ ℤ_pⁿ`. Both correspondences use the
same submodule of `(ℤ/pᵏ)ⁿ`. -/
def pPowerSublatticeEquiv :
    Set.Ici (LinearMap.ker (intVectorReduction ι p k)) ≃o
      Set.Ici (LinearMap.ker (padicVectorReduction ι p k)) :=
  (LinearMap.submoduleComapOrderIsoOfSurjective (intVectorReduction ι p k)
    (intVectorReduction_surjective ι p k)).symm.trans
      (LinearMap.submoduleComapOrderIsoOfSurjective (padicVectorReduction ι p k)
        (padicVectorReduction_surjective ι p k))

/-- Membership in the p-adic sublattice is tested in the common finite residue module. -/
theorem mem_pPowerSublatticeEquiv_iff
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) (x : ι → ℤ_[p]) :
    x ∈ (pPowerSublatticeEquiv ι p k L).val ↔
      padicVectorReduction ι p k x ∈ L.val.map (intVectorReduction ι p k) := by
  simp only [pPowerSublatticeEquiv, OrderIso.trans_apply,
    LinearMap.coe_submoduleComapOrderIsoOfSurjective,
    LinearMap.submoduleComapOrderIsoOfSurjective_symm_apply, Submodule.mem_comap]

/-- On integral vectors the corresponding p-adic sublattice has exactly the original
membership condition. In particular, taking integral points recovers the integral lattice. -/
@[simp]
theorem intVectorToPadic_mem_pPowerSublatticeEquiv_iff
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) (x : ι → ℤ) :
    intVectorToPadic ι p x ∈ (pPowerSublatticeEquiv ι p k L).val ↔ x ∈ L.val := by
  rw [mem_pPowerSublatticeEquiv_iff, padicVectorReduction_intVectorToPadic,
    ← Submodule.mem_comap, Submodule.comap_map_eq_self L.property]

/-- Taking integral vectors is the inverse of the prime-power sublattice correspondence. -/
@[simp]
theorem mem_pPowerSublatticeEquiv_symm_iff
    (P : Set.Ici (LinearMap.ker (padicVectorReduction ι p k))) (x : ι → ℤ) :
    x ∈ ((pPowerSublatticeEquiv ι p k).symm P).val ↔ intVectorToPadic ι p x ∈ P.val := by
  rw [← intVectorToPadic_mem_pPowerSublatticeEquiv_iff ι p k
    ((pPowerSublatticeEquiv ι p k).symm P), OrderIso.apply_symm_apply]

/-- The corresponding lattices have canonically isomorphic `ℤ`-linear quotients. This preserves
indices and, for finite coordinate sets, the elementary divisors of the finite abelian quotients.
No finiteness assumption is needed to construct the isomorphism. -/
def pPowerSublatticeQuotientEquiv
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) :
    ((ι → ℤ) ⧸ L.val) ≃ₗ[ℤ]
      ((ι → ℤ_[p]) ⧸ (pPowerSublatticeEquiv ι p k L).val.restrictScalars ℤ) := by
  let P := (pPowerSublatticeEquiv ι p k L).val
  let φ := (P.restrictScalars ℤ).mkQ ∘ₗ intVectorToPadic ι p
  have hker : LinearMap.ker φ = L.val := by
    ext x
    simp [φ, P, intVectorToPadic_mem_pPowerSublatticeEquiv_iff]
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨x, rfl⟩ := (P.restrictScalars ℤ).mkQ_surjective a
    obtain ⟨z, hz⟩ := intVectorReduction_surjective ι p k (padicVectorReduction ι p k x)
    refine ⟨z, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq _).mpr
    apply (pPowerSublatticeEquiv ι p k L).property
    rw [LinearMap.mem_ker, map_sub, padicVectorReduction_intVectorToPadic, hz, sub_self]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)

/-- The quotient comparison is induced by the usual inclusion of integral vectors into
p-adic vectors. -/
@[simp]
theorem pPowerSublatticeQuotientEquiv_apply_mk
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) (x : ι → ℤ) :
    pPowerSublatticeQuotientEquiv ι p k L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (intVectorToPadic ι p x) := by
  simp only [pPowerSublatticeQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x

/-- For finitely many coordinates, the correspondence is the usual extension of scalars:
the corresponding p-adic lattice is the p-adic span of the integral lattice. -/
theorem pPowerSublatticeEquiv_eq_span [Finite ι]
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) :
    (pPowerSublatticeEquiv ι p k L).val = Submodule.span ℤ_[p]
      (intVectorToPadic ι p '' (L.val : Set (ι → ℤ))) := by
  classical
  let := Fintype.ofFinite ι
  let S := Submodule.span ℤ_[p]
    (intVectorToPadic ι p '' (L.val : Set (ι → ℤ)))
  have hcast (x : ι → ℤ) (hx : x ∈ L.val) : intVectorToPadic ι p x ∈ S :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have hker : LinearMap.ker (padicVectorReduction ι p k) ≤ S := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_ker_padicVectorReduction_iff ι p k x).mp hx
    have hsingle (i : ι) : (p : ℤ) ^ k • Pi.single i 1 ∈ L.val :=
      L.property ((mem_ker_intVectorReduction_iff ι p k _).mpr ⟨Pi.single i 1, rfl⟩)
    have heq : (p : ℤ_[p]) ^ k • y = ∑ i, y i •
        intVectorToPadic ι p ((p : ℤ) ^ k • Pi.single i 1) := by
      ext j
      simp [Pi.single_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem S fun i _ ↦ S.smul_mem (y i) (hcast _ (hsingle i))
  refine le_antisymm (fun x hx ↦ ?_)
    (Submodule.span_le.mpr (Set.image_subset_iff.mpr fun z hz ↦
      (intVectorToPadic_mem_pPowerSublatticeEquiv_iff ι p k L z).mpr hz))
  obtain ⟨z, hz, hzx⟩ := (mem_pPowerSublatticeEquiv_iff ι p k L x).mp hx
  have hdiff : x - intVectorToPadic ι p z ∈
      LinearMap.ker (padicVectorReduction ι p k) := by
    rw [LinearMap.mem_ker, map_sub, padicVectorReduction_intVectorToPadic, ← hzx, sub_self]
  simpa using S.add_mem (hker hdiff) (hcast z hz)

/-- There are finitely many integral sublattices containing a fixed prime-power multiple
of the standard lattice. -/
instance [Finite ι] : Finite (Set.Ici (LinearMap.ker (intVectorReduction ι p k))) :=
  Finite.of_equiv (Submodule (ZMod (p ^ k)) (ι → ZMod (p ^ k)))
    (LinearMap.submoduleComapOrderIsoOfSurjective (intVectorReduction ι p k)
      (intVectorReduction_surjective ι p k)).toEquiv

/-- There are finitely many p-adic sublattices containing a fixed prime-power multiple
of the standard lattice. -/
instance [Finite ι] : Finite (Set.Ici (LinearMap.ker (padicVectorReduction ι p k))) :=
  Finite.of_equiv (Submodule (ZMod (p ^ k)) (ι → ZMod (p ^ k)))
    (LinearMap.submoduleComapOrderIsoOfSurjective (padicVectorReduction ι p k)
      (padicVectorReduction_surjective ι p k)).toEquiv

end General

section Matrix

variable (n p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- The `ℤ`-sublattice of `ℤ^n` spanned by the columns of `A : Matrix (Fin n) (Fin n) ℤ`. -/
def intSublattice (A : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.range A.mulVecLin

omit [Fact p.Prime] in
/-- Defining equation for `intSublattice`. -/
theorem intSublattice_def (A : Matrix (Fin n) (Fin n) ℤ) :
    intSublattice n A = LinearMap.range A.mulVecLin := (rfl)

/-- The `ℤ_p`-sublattice of `ℤ_p^n` spanned by the columns of `B : Matrix (Fin n) (Fin n) ℤ_[p]`. -/
def padicSublattice (B : Matrix (Fin n) (Fin n) ℤ_[p]) :
    Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
  LinearMap.range B.mulVecLin

/-- Defining equation for `padicSublattice`. -/
theorem padicSublattice_def (B : Matrix (Fin n) (Fin n) ℤ_[p]) :
    padicSublattice n p B = LinearMap.range B.mulVecLin := (rfl)

omit [Fact p.Prime] in
/-- Two positive-determinant integer matrices generate the same `ℤ`-sublattice if and only if they
lie in the same right `SL_n(ℤ)`-coset. -/
theorem intSublattice_eq_iff_exists_sl {A₁ A₂ : Matrix (Fin n) (Fin n) ℤ}
    (h₁ : 0 < A₁.det) (h₂ : 0 < A₂.det) :
    intSublattice n A₁ = intSublattice n A₂ ↔
      ∃ σ : Matrix.SpecialLinearGroup (Fin n) ℤ, A₁ * (σ : Matrix (Fin n) (Fin n) ℤ) = A₂ := by
  rw [intSublattice_def, intSublattice_def, Matrix.range_mulVecLin_eq_iff h₁.ne' h₂.ne']
  refine ⟨?_, fun ⟨σ, hσ⟩ ↦ ⟨σ.toGL, hσ⟩⟩
  rintro ⟨U, rfl⟩
  have hunit : IsUnit (↑U : Matrix (Fin n) (Fin n) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit
  rw [Matrix.det_mul] at h₂
  have hdet : (↑U : Matrix (Fin n) (Fin n) ℤ).det = 1 :=
    (Int.isUnit_iff.mp hunit).resolve_right fun hneg ↦ by rw [hneg] at h₂; linarith
  exact ⟨⟨↑U, hdet⟩, rfl⟩

omit [Fact p.Prime] in
/-- If `A.det ∣ p ^ k`, then `intSublattice n A` contains `p ^ k • ℤ^n` (the kernel of reduction
modulo `p ^ k`). -/
theorem ker_intVectorReduction_le_intSublattice {A : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hA : A.det ∣ (p : ℤ) ^ k) :
    LinearMap.ker (intVectorReduction (Fin n) p k) ≤ intSublattice n A := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_ker_intVectorReduction_iff (Fin n) p k x).mp hx
  exact Matrix.smul_mem_range_mulVecLin_of_det_dvd hA y

/-- If `A.det ∣ p ^ k`, then `padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))` contains
`p ^ k • ℤ_p^n` (the kernel of `p`-adic reduction modulo `p ^ k`). -/
theorem ker_padicVectorReduction_le_padicSublattice_map {A : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hA : A.det ∣ (p : ℤ) ^ k) :
    LinearMap.ker (padicVectorReduction (Fin n) p k) ≤
      padicSublattice n p (A.map (Int.castRingHom ℤ_[p])) := by
  have hB : (A.map (Int.castRingHom ℤ_[p])).det ∣ (p : ℤ_[p]) ^ k := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using (Int.castRingHom ℤ_[p]).map_dvd hA
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_ker_padicVectorReduction_iff (Fin n) p k x).mp hx
  exact Matrix.smul_mem_range_mulVecLin_of_det_dvd hB y

/-- Every nonsingular `B ∈ M_n(ℤ_p)` defines a `ℤ_p`-sublattice containing
`p ^ v(det B) • ℤ_p^n`. -/
theorem ker_padicVectorReduction_le_padicSublattice {B : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hB : B.det ≠ 0) :
    LinearMap.ker (padicVectorReduction (Fin n) p B.det.valuation) ≤
      padicSublattice n p B := by
  intro x hx
  obtain ⟨y, rfl⟩ :=
    (mem_ker_padicVectorReduction_iff (Fin n) p B.det.valuation x).mp hx
  exact Matrix.smul_mem_range_mulVecLin_of_det_dvd (PadicInt.dvd_pow_valuation hB) y

/-- **Sublattice completion** (Rhodes–Shemanske, *Bruhat–Tits buildings and Hecke operators*,
§3.1 Proposition 3.2): under `TauCeti.pPowerSublatticeEquiv`, any `ℤ`-sublattice
`intSublattice n A` containing `p ^ k • ℤ^n` maps to the `ℤ_p`-sublattice
`padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))`. -/
theorem pPowerSublatticeEquiv_intSublattice {A : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hker : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ intSublattice n A) :
    (pPowerSublatticeEquiv (Fin n) p k ⟨intSublattice n A, hker⟩).val =
      padicSublattice n p (A.map (Int.castRingHom ℤ_[p])) := by
  rw [pPowerSublatticeEquiv_eq_span]
  set B := A.map (Int.castRingHom ℤ_[p])
  have hcompat (v : Fin n → ℤ) :
      intVectorToPadic (Fin n) p (A.mulVec v) =
        B.mulVec (intVectorToPadic (Fin n) p v) := by
    ext i; simp [B, Matrix.mulVec, dotProduct]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨intVectorToPadic (Fin n) p v, (hcompat v).symm⟩
  · rintro _ ⟨w, rfl⟩
    have hw : w = ∑ j : Fin n, w j • intVectorToPadic (Fin n) p (Pi.single j 1) := by
      ext i; simp [Pi.single_apply]
    rw [Matrix.mulVecLin_apply, hw, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [Matrix.mulVec_smul, ← hcompat]
    exact Submodule.smul_mem _ (w j)
      (Submodule.subset_span ⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, rfl⟩)

/-- Inverse of `pPowerSublatticeEquiv_intSublattice`: applying `(pPowerSublatticeEquiv _ p k).symm`
to `padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))` recovers `intSublattice n A`. -/
theorem pPowerSublatticeEquiv_symm_padicSublattice {A : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hker : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ intSublattice n A)
    (hkerP : LinearMap.ker (padicVectorReduction (Fin n) p k) ≤
      padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))) :
    ((pPowerSublatticeEquiv (Fin n) p k).symm
      ⟨padicSublattice n p (A.map (Int.castRingHom ℤ_[p])), hkerP⟩).val = intSublattice n A := by
  have heq : (⟨padicSublattice n p (A.map (Int.castRingHom ℤ_[p])), hkerP⟩ :
      Set.Ici (LinearMap.ker (padicVectorReduction (Fin n) p k))) =
      pPowerSublatticeEquiv (Fin n) p k ⟨intSublattice n A, hker⟩ :=
    Subtype.ext (pPowerSublatticeEquiv_intSublattice n p hker).symm
  exact (congrArg (fun X ↦ ((pPowerSublatticeEquiv (Fin n) p k).symm X).val) heq).trans
    (congrArg Subtype.val
      ((pPowerSublatticeEquiv (Fin n) p k).symm_apply_apply ⟨intSublattice n A, hker⟩))

/-- **Intermediate-lattice correspondence** (Rhodes–Shemanske, *Bruhat–Tits buildings and Hecke
operators*, §3.2 Lemma 3.3): for `p`-primary integer matrices `C` and `A` with `det C ∣ p ^ k` and
`det A ∣ p ^ k`, `TauCeti.pPowerSublatticeEquiv` restricts to an order isomorphism between
`ℤ`-sublattices `intSublattice n C ≤ L ≤ intSublattice n A` and `ℤ_p`-sublattices between their
completions. -/
def intermediateSublatticeOrderIso {A C : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hC : C.det ∣ (p : ℤ) ^ k) (hA : A.det ∣ (p : ℤ) ^ k) :
    {L : Submodule ℤ (Fin n → ℤ) // intSublattice n C ≤ L ∧ L ≤ intSublattice n A} ≃o
      {M : Submodule ℤ_[p] (Fin n → ℤ_[p]) //
        padicSublattice n p (C.map (Int.castRingHom ℤ_[p])) ≤ M ∧
          M ≤ padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))} where
  toFun L :=
    ⟨(pPowerSublatticeEquiv (Fin n) p k
        ⟨L.val, (ker_intVectorReduction_le_intSublattice n p hC).trans L.property.1⟩).val,
      by
        rw [← pPowerSublatticeEquiv_intSublattice n p
            (ker_intVectorReduction_le_intSublattice n p hC),
          ← pPowerSublatticeEquiv_intSublattice n p
            (ker_intVectorReduction_le_intSublattice n p hA)]
        exact ⟨(pPowerSublatticeEquiv (Fin n) p k).monotone L.property.1,
          (pPowerSublatticeEquiv (Fin n) p k).monotone L.property.2⟩⟩
  invFun M :=
    ⟨((pPowerSublatticeEquiv (Fin n) p k).symm
        ⟨M.val, (ker_padicVectorReduction_le_padicSublattice_map n p hC).trans M.property.1⟩).val,
      by
        rw [← pPowerSublatticeEquiv_symm_padicSublattice n p
            (ker_intVectorReduction_le_intSublattice n p hC)
            (ker_padicVectorReduction_le_padicSublattice_map n p hC),
          ← pPowerSublatticeEquiv_symm_padicSublattice n p
            (ker_intVectorReduction_le_intSublattice n p hA)
            (ker_padicVectorReduction_le_padicSublattice_map n p hA)]
        exact ⟨(pPowerSublatticeEquiv (Fin n) p k).symm.monotone M.property.1,
          (pPowerSublatticeEquiv (Fin n) p k).symm.monotone M.property.2⟩⟩
  left_inv L := by
    apply Subtype.ext; dsimp only
    exact congrArg Subtype.val ((pPowerSublatticeEquiv (Fin n) p k).symm_apply_apply
      ⟨L.val, (ker_intVectorReduction_le_intSublattice n p hC).trans L.property.1⟩)
  right_inv M := by
    apply Subtype.ext; dsimp only
    exact congrArg Subtype.val ((pPowerSublatticeEquiv (Fin n) p k).apply_symm_apply
      ⟨M.val, _⟩)
  map_rel_iff' {L₁ L₂} :=
    (pPowerSublatticeEquiv (Fin n) p k).map_rel_iff
      (a := ⟨L₁.val, _⟩) (b := ⟨L₂.val, _⟩)

/-- Coercing `intermediateSublatticeOrderIso n p hC hA L` to a `ℤ_p`-submodule applies
`TauCeti.pPowerSublatticeEquiv`. -/
@[simp]
theorem coe_intermediateSublatticeOrderIso {A C : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hC : C.det ∣ (p : ℤ) ^ k) (hA : A.det ∣ (p : ℤ) ^ k)
    (L : {L : Submodule ℤ (Fin n → ℤ) // intSublattice n C ≤ L ∧ L ≤ intSublattice n A}) :
    (intermediateSublatticeOrderIso n p hC hA L : Submodule ℤ_[p] (Fin n → ℤ_[p])) =
      (pPowerSublatticeEquiv (Fin n) p k
        ⟨L.val, (ker_intVectorReduction_le_intSublattice n p hC).trans L.property.1⟩).val := (rfl)

/-- Coercing `(intermediateSublatticeOrderIso n p hC hA).symm M` to a `ℤ`-submodule applies
`(TauCeti.pPowerSublatticeEquiv (Fin n) p k).symm`. -/
@[simp]
theorem coe_intermediateSublatticeOrderIso_symm {A C : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hC : C.det ∣ (p : ℤ) ^ k) (hA : A.det ∣ (p : ℤ) ^ k)
    (M : {M : Submodule ℤ_[p] (Fin n → ℤ_[p]) //
      padicSublattice n p (C.map (Int.castRingHom ℤ_[p])) ≤ M ∧
        M ≤ padicSublattice n p (A.map (Int.castRingHom ℤ_[p]))}) :
    ((intermediateSublatticeOrderIso n p hC hA).symm M : Submodule ℤ (Fin n → ℤ)) =
      ((pPowerSublatticeEquiv (Fin n) p k).symm
        ⟨M.val,
          (ker_padicVectorReduction_le_padicSublattice_map n p hC).trans M.property.1⟩).val :=
  (rfl)

private theorem finrank_eq_of_ker_intVectorReduction_le {k : ℕ}
    {L : Submodule ℤ (Fin n → ℤ)}
    (hL : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ L) :
    Module.finrank ℤ L = Module.finrank ℤ (Fin n → ℤ) := by
  set K := LinearMap.ker (intVectorReduction (Fin n) p k)
  have hpk : (p : ℤ) ^ k ≠ 0 :=
    pow_ne_zero k (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let φ : (Fin n → ℤ) →ₗ[ℤ] K :=
    { toFun := fun y ↦ ⟨(p : ℤ) ^ k • y,
        (mem_ker_intVectorReduction_iff (Fin n) p k _).mpr ⟨y, rfl⟩⟩
      map_add' := fun x y ↦ Subtype.ext (smul_add _ x y)
      map_smul' := fun r x ↦ Subtype.ext (smul_comm _ r x) }
  have hbij : Function.Bijective φ :=
    ⟨fun x y hxy ↦ funext fun i ↦ mul_left_cancel₀ hpk (congr_fun (congrArg Subtype.val hxy) i),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨y, rfl⟩ := (mem_ker_intVectorReduction_iff (Fin n) p k x).mp hx
        exact ⟨y, rfl⟩⟩
  have hK : Module.finrank ℤ K = Module.finrank ℤ (Fin n → ℤ) :=
    (LinearEquiv.ofBijective φ hbij).finrank_eq.symm
  exact le_antisymm L.finrank_le (hK ▸ Submodule.finrank_mono hL)

private theorem exists_matrix_intSublattice_eq {k : ℕ} {L : Submodule ℤ (Fin n → ℤ)}
    (hL : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ L) :
    ∃ (D₀ : Matrix (Fin n) (Fin n) ℤ) (m : ℕ),
      D₀.det ≠ 0 ∧ D₀.det.natAbs = p ^ m ∧ intSublattice n D₀ = L := by
  classical
  have hrank := finrank_eq_of_ker_intVectorReduction_le n p hL
  let bL := Submodule.smithNormalFormBotBasis (Pi.basisFun ℤ (Fin n)) hrank
  let D₀ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (bL j : Fin n → ℤ) i
  have hmulVec (v : Fin n → ℤ) : D₀.mulVec v = ∑ j : Fin n, v j • (bL j : Fin n → ℤ) := by
    ext i; simp [D₀, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : intSublattice n D₀ = L := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, hmulVec]
      exact Submodule.sum_mem L fun j _ ↦ L.smul_mem (v j) (bL j).property
    · intro x hx
      refine ⟨bL.repr ⟨x, hx⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, hmulVec]
      have hsum := congrArg L.subtype (bL.sum_repr ⟨x, hx⟩)
      rw [map_sum] at hsum
      simpa only [LinearMap.map_smul, Submodule.coe_subtype] using hsum
  obtain ⟨C, hDC⟩ := Matrix.exists_mul_eq_of_range_le
    (L := D₀) (L' := (p : ℤ) ^ k • (1 : Matrix (Fin n) (Fin n) ℤ)) fun j ↦ by
      have hcol : ((p : ℤ) ^ k • (1 : Matrix (Fin n) (Fin n) ℤ)).col j =
          (p : ℤ) ^ k • Pi.single j 1 := by
        ext i
        rw [Matrix.col_apply, Matrix.smul_apply, Matrix.one_apply, Pi.smul_apply, Pi.single_apply]
      rw [hcol, ← intSublattice_def, hrange]
      exact hL ((mem_ker_intVectorReduction_iff (Fin n) p k _).mpr ⟨Pi.single j 1, rfl⟩)
  obtain ⟨m, -, hm⟩ :=
    Matrix.exists_natAbs_det_eq_pow_of_mul_eq_pow_smul_one (Fact.out : p.Prime) hDC
  have hne : D₀.det ≠ 0 :=
    Int.natAbs_ne_zero.mp (hm ▸ pow_ne_zero m (Fact.out : p.Prime).ne_zero)
  exact ⟨D₀, m, hne, hm, hrange⟩

/-- Every `ℤ`-sublattice of `ℤ^n` containing `p ^ k • ℤ^n` is `intSublattice n D` for an integer
matrix `D` whose determinant is a power `p ^ m` (`m : ℕ`). -/
theorem exists_det_eq_pow_and_intSublattice_eq {k : ℕ} {L : Submodule ℤ (Fin n → ℤ)}
    (hL : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ L) :
    ∃ (D : Matrix (Fin n) (Fin n) ℤ) (m : ℕ),
      D.det = (p : ℤ) ^ m ∧ intSublattice n D = L := by
  obtain ⟨D₀, m, hne, hm, hrange⟩ := exists_matrix_intSublattice_eq n p hL
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso; simp [Matrix.det_isEmpty] at hneg
    · have : NeZero n := ⟨hn.ne'⟩
      let U : GL (Fin n) ℤ := diagGL fun i : Fin n ↦ if i = 0 then (-1 : ℤˣ) else 1
      have hUdet : (↑U : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
        rw [diagGL_coe, Matrix.det_diagonal, Finset.prod_eq_single (0 : Fin n)]
        · simp
        · exact fun i _ hi ↦ by simp [hi]
        · exact fun h ↦ absurd (Finset.mem_univ (0 : Fin n)) h
      refine ⟨D₀ * (↑U : Matrix (Fin n) (Fin n) ℤ), m, ?_, ?_⟩
      · rw [Matrix.det_mul, hUdet, mul_neg_one]
        have habs : (D₀.det.natAbs : ℤ) = -D₀.det := Int.ofNat_natAbs_of_nonpos hneg.le
        rw [← habs, hm, Nat.cast_pow]
      · rw [intSublattice_def]
        exact (Matrix.range_mulVecLin_mul_unit D₀ U).trans hrange
  · refine ⟨D₀, m, ?_, hrange⟩
    have habs : (D₀.det.natAbs : ℤ) = D₀.det := Int.natAbs_of_nonneg hpos.le
    rw [← habs, hm, Nat.cast_pow]

/-- **Every finite-index `ℤ_p`-sublattice comes from a `p`-primary integer matrix**
(Rhodes–Shemanske, *Bruhat–Tits buildings and Hecke operators*, §3.1 Proposition 3.2): for every
nonsingular `B ∈ M_n(ℤ_p)` there exist `D ∈ M_n(ℤ)`, `m : ℕ`, and `U ∈ GL_n(ℤ_p)` with
`det D = p ^ m` and `B * U = D.map (Int.castRingHom ℤ_[p])`. -/
theorem exists_det_eq_pow_and_mul_eq_map (B : Matrix (Fin n) (Fin n) ℤ_[p]) (hB : B.det ≠ 0) :
    ∃ (D : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (U : GL (Fin n) ℤ_[p]),
      D.det = (p : ℤ) ^ m ∧
        B * (↑U : Matrix (Fin n) (Fin n) ℤ_[p]) = D.map (Int.castRingHom ℤ_[p]) := by
  let k := B.det.valuation
  let M₀ : Set.Ici (LinearMap.ker (padicVectorReduction (Fin n) p k)) :=
    ⟨padicSublattice n p B, ker_padicVectorReduction_le_padicSublattice n p hB⟩
  let L := (pPowerSublatticeEquiv (Fin n) p k).symm M₀
  obtain ⟨D, m, hDdet, hDL⟩ := exists_det_eq_pow_and_intSublattice_eq n p L.property
  have hkerD : LinearMap.ker (intVectorReduction (Fin n) p k) ≤ intSublattice n D :=
    hDL ▸ L.property
  have hpadic : padicSublattice n p B = padicSublattice n p (D.map (Int.castRingHom ℤ_[p])) := by
    calc padicSublattice n p B
        = (pPowerSublatticeEquiv (Fin n) p k L).val :=
          congrArg Subtype.val
            ((pPowerSublatticeEquiv (Fin n) p k).apply_symm_apply M₀).symm
      _ = padicSublattice n p (D.map (Int.castRingHom ℤ_[p])) := by
          have hL_eq : L = ⟨intSublattice n D, hkerD⟩ := Subtype.ext hDL.symm
          rw [hL_eq, pPowerSublatticeEquiv_intSublattice]
  have hDpadic_ne : (D.map (Int.castRingHom ℤ_[p])).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hDdet, map_pow, map_natCast]
    exact pow_ne_zero m (NeZero.ne (p : ℤ_[p]))
  obtain ⟨U, hBU⟩ := (Matrix.range_mulVecLin_eq_iff hB hDpadic_ne).mp hpadic
  exact ⟨D, m, U, hDdet, hBU⟩

end Matrix

end TauCeti
