/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

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

## References

* J. A. Rhodes and T. R. Shemanske, *Rationality theorems for Hecke operators on GL_n*, §2.
-/

public noncomputable section

namespace TauCeti

variable (ι : Type*) (p k : ℕ) [Fact p.Prime]

/-- Coordinatewise reduction of integral vectors modulo `pᵏ`. -/
def intVectorReduction : (ι → ℤ) →ₛₗ[Int.castRingHom (ZMod (p ^ k))] (ι → ZMod (p ^ k)) where
  toFun x i := x i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Coordinatewise reduction of p-adic integral vectors modulo `pᵏ`. -/
def padicVectorReduction : (ι → ℤ_[p]) →ₛₗ[PadicInt.toZModPow (p := p) k] (ι → ZMod (p ^ k)) where
  toFun x i := PadicInt.toZModPow k (x i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Fact p.Prime] in
@[simp]
theorem intVectorReduction_apply (x : ι → ℤ) (i : ι) :
    intVectorReduction ι p k x i = (x i : ZMod (p ^ k)) := (rfl)

@[simp]
theorem padicVectorReduction_apply (x : ι → ℤ_[p]) (i : ι) :
    padicVectorReduction ι p k x i = PadicInt.toZModPow k (x i) := (rfl)

omit [Fact p.Prime] in
/-- Integral vectors surject onto the finite residue vectors. -/
theorem intVectorReduction_surjective : Function.Surjective (intVectorReduction ι p k) := by
  intro x
  choose y hy using fun i ↦ ZMod.intCast_surjective (x i)
  exact ⟨y, funext hy⟩

/-- P-adic integral vectors surject onto the finite residue vectors. -/
theorem padicVectorReduction_surjective : Function.Surjective (padicVectorReduction ι p k) := by
  intro x
  exact ⟨fun i ↦ (x i).val, by ext; simp⟩

/-- Reduction commutes with the inclusion of integral vectors into p-adic vectors. -/
@[simp]
theorem padicVectorReduction_intCast (x : ι → ℤ) :
    padicVectorReduction ι p k (fun i ↦ (x i : ℤ_[p])) = intVectorReduction ι p k x := by
  ext; simp

omit [Fact p.Prime] in
/-- The kernel of integral reduction consists exactly of the multiples of `pᵏ`. -/
theorem mem_ker_intVectorReduction_iff (x : ι → ℤ) :
    x ∈ LinearMap.ker (intVectorReduction ι p k) ↔ ∃ y : ι → ℤ, x = (p : ℤ) ^ k • y := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [intVectorReduction_apply, Pi.zero_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i ↦ by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

/-- The kernel of p-adic reduction consists exactly of the multiples of `pᵏ`. -/
theorem mem_ker_padicVectorReduction_iff (x : ι → ℤ_[p]) :
    x ∈ LinearMap.ker (padicVectorReduction ι p k) ↔ ∃ y : ι → ℤ_[p], x = (p : ℤ_[p]) ^ k • y := by
  have h (i : ι) : PadicInt.toZModPow k (x i) = 0 ↔ ∃ y, x i = (p : ℤ_[p]) ^ k * y := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    rfl
  rw [LinearMap.mem_ker, funext_iff]
  simp only [padicVectorReduction_apply, Pi.zero_apply, h]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩

local instance : RingHomSurjective (Int.castRingHom (ZMod (p ^ k))) :=
  ⟨ZMod.intCast_surjective⟩

local instance : RingHomSurjective (PadicInt.toZModPow (p := p) k) :=
  ⟨ZMod.ringHom_surjective _⟩

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
    x ∈ (pPowerSublatticeEquiv ι p k L).1 ↔
      padicVectorReduction ι p k x ∈ L.1.map (intVectorReduction ι p k) := by
  simp only [pPowerSublatticeEquiv, OrderIso.trans_apply,
    LinearMap.coe_submoduleComapOrderIsoOfSurjective,
    LinearMap.submoduleComapOrderIsoOfSurjective_symm_apply, Submodule.mem_comap]

/-- On integral vectors the corresponding p-adic sublattice has exactly the original
membership condition. In particular, taking integral points recovers the integral lattice. -/
@[simp]
theorem intCast_mem_pPowerSublatticeEquiv_iff
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) (x : ι → ℤ) :
    (fun i ↦ (x i : ℤ_[p])) ∈ (pPowerSublatticeEquiv ι p k L).1 ↔ x ∈ L.1 := by
  rw [mem_pPowerSublatticeEquiv_iff, padicVectorReduction_intCast]
  exact (congrArg (fun S : Submodule ℤ (ι → ℤ) ↦ x ∈ S)
    (Submodule.comap_map_eq_self L.2)).to_iff

/-- Taking integral vectors is the inverse of the prime-power sublattice correspondence. -/
@[simp]
theorem mem_pPowerSublatticeEquiv_symm_iff
    (P : Set.Ici (LinearMap.ker (padicVectorReduction ι p k))) (x : ι → ℤ) :
    x ∈ ((pPowerSublatticeEquiv ι p k).symm P).1 ↔ (fun i ↦ (x i : ℤ_[p])) ∈ P.1 := by
  rw [← intCast_mem_pPowerSublatticeEquiv_iff ι p k
    ((pPowerSublatticeEquiv ι p k).symm P), OrderIso.apply_symm_apply]

/-- The corresponding lattices have canonically isomorphic additive quotients. This preserves
indices and, for finite coordinate sets, the elementary divisors of the finite abelian quotients.
No finiteness assumption is needed to construct the isomorphism. -/
def pPowerSublatticeQuotientEquiv
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) :
    ((ι → ℤ) ⧸ L.1) ≃+ ((ι → ℤ_[p]) ⧸ (pPowerSublatticeEquiv ι p k L).1) := by
  let f : (ι → ℤ) →ₗ[ℤ] (ι → ℤ_[p]) := LinearMap.pi fun i ↦
    (Int.castAddHom ℤ_[p]).toIntLinearMap.comp (LinearMap.proj i)
  let P := (pPowerSublatticeEquiv ι p k L).1
  let g := L.1.mapQ (P.restrictScalars ℤ) f fun x hx ↦
    (intCast_mem_pPowerSublatticeEquiv_iff ι p k L x).mpr hx
  have hg (x : ι → ℤ) : g (L.1.mkQ x) =
      (P.restrictScalars ℤ).mkQ (fun i ↦ (x i : ℤ_[p])) := rfl
  refine AddEquiv.ofBijective g.toAddMonoidHom ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero g).mpr fun a ha ↦ ?_
    obtain ⟨x, rfl⟩ := L.1.mkQ_surjective a
    rw [hg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (intCast_mem_pPowerSublatticeEquiv_iff ι p k L x).mp ha
  · intro a
    obtain ⟨x, rfl⟩ := (P.restrictScalars ℤ).mkQ_surjective a
    obtain ⟨z, hz⟩ := intVectorReduction_surjective ι p k (padicVectorReduction ι p k x)
    refine ⟨L.1.mkQ z, ?_⟩
    refine (hg z).trans ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq _).mpr
    apply (pPowerSublatticeEquiv ι p k L).2
    rw [LinearMap.mem_ker, map_sub, padicVectorReduction_intCast, hz, sub_self]

/-- The quotient comparison is induced by the usual inclusion of integral vectors into
p-adic vectors. -/
@[simp]
theorem pPowerSublatticeQuotientEquiv_apply_mk
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) (x : ι → ℤ) :
    pPowerSublatticeQuotientEquiv ι p k L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (fun i ↦ (x i : ℤ_[p])) :=
  (rfl)

/-- For finitely many coordinates, the correspondence is the usual extension of scalars:
the corresponding p-adic lattice is the p-adic span of the integral lattice. -/
theorem pPowerSublatticeEquiv_eq_span [Finite ι]
    (L : Set.Ici (LinearMap.ker (intVectorReduction ι p k))) :
    (pPowerSublatticeEquiv ι p k L).1 = Submodule.span ℤ_[p]
      ((fun x : ι → ℤ ↦ fun i ↦ (x i : ℤ_[p])) '' (L.1 : Set (ι → ℤ))) := by
  classical
  let := Fintype.ofFinite ι
  let S := Submodule.span ℤ_[p]
    ((fun x : ι → ℤ ↦ fun i ↦ (x i : ℤ_[p])) '' (L.1 : Set (ι → ℤ)))
  have hcast (x : ι → ℤ) (hx : x ∈ L.1) : (fun i ↦ (x i : ℤ_[p])) ∈ S :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have hker : LinearMap.ker (padicVectorReduction ι p k) ≤ S := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_ker_padicVectorReduction_iff ι p k x).mp hx
    have hsingle (i : ι) : (p : ℤ) ^ k • Pi.single i 1 ∈ L.1 :=
      L.2 ((mem_ker_intVectorReduction_iff ι p k _).mpr ⟨Pi.single i 1, rfl⟩)
    have heq : (p : ℤ_[p]) ^ k • y = ∑ i, y i •
        (fun j ↦ (((p : ℤ) ^ k • Pi.single i 1 : ι → ℤ) j : ℤ_[p])) := by
      ext j
      simp [Pi.single_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem S fun i _ ↦ S.smul_mem (y i) (hcast _ (hsingle i))
  refine le_antisymm (fun x hx ↦ ?_)
    (Submodule.span_le.mpr (Set.image_subset_iff.mpr fun z hz ↦
      (intCast_mem_pPowerSublatticeEquiv_iff ι p k L z).mpr hz))
  obtain ⟨z, hz, hzx⟩ := (mem_pPowerSublatticeEquiv_iff ι p k L x).mp hx
  have hdiff : x - (fun i ↦ (z i : ℤ_[p])) ∈
      LinearMap.ker (padicVectorReduction ι p k) := by
    rw [LinearMap.mem_ker, map_sub, padicVectorReduction_intCast, ← hzx, sub_self]
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

end TauCeti
