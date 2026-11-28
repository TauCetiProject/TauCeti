/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Length of linear maps from a torsion module to a principal quotient

Over an integral domain `O`, if `d ∣ a` with `a ≠ 0`, then `Hom_O(O / d, O / a)` is isomorphic
to `O / d` (via evaluation at `1` and multiplication by `a / d`), so both have the same
`O`-module length (`TauCeti.length_linearMap_quotSpan_of_dvd`).

When `O` is a principal ideal domain, the structure theorem for finitely generated torsion
modules decomposes any finitely generated `O`-module `Q` annihilated by `a ≠ 0` into cyclic
quotients `O / d_i` with `d_i ∣ a`, yielding `length O (Q →ₗ[O] O ⧸ Ideal.span {a}) = length O Q`
(`TauCeti.length_linearMap_quotSpan`).

## Main results

* `TauCeti.length_linearMap_quotSpan_of_dvd`: for `d ∣ a ≠ 0` in an integral domain `O`,
  `Module.length O ((O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})) =
   Module.length O (O ⧸ Ideal.span {d})`.
* `TauCeti.length_linearMap_quotSpan`: over a PID `O`, any finitely generated `O`-module `Q`
  annihilated by `a ≠ 0` satisfies
  `Module.length O (Q →ₗ[O] (O ⧸ Ideal.span {a})) = Module.length O Q`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/General/Algebra/SharpMinors.lean`
(`New.Selmer.length_linearMap_quotSpan_of_dvd`, `New.Selmer.length_linearMap_quotSpan`).
-/

public section

namespace TauCeti

open Module Submodule

variable {O : Type*} [CommRing O] [IsDomain O]

/-- In an integral domain `O`, if `d ∣ a` with `a ≠ 0`, then the module of `O`-linear maps
`(O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})` has the same length as `O ⧸ Ideal.span {d}`. -/
theorem length_linearMap_quotSpan_of_dvd {a d : O} (ha : a ≠ 0) (hd : d ∣ a) :
    Module.length O ((O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})) =
      Module.length O (O ⧸ Ideal.span {d}) := by
  obtain ⟨c, rfl⟩ := hd
  have h_mul_le : Ideal.span {d} ≤
      Submodule.comap (LinearMap.lsmul O O c) (Ideal.span {d * c}) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr (by simp [mul_comm]))
  let mulC : (O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {d * c}) :=
    Submodule.mapQ _ _ (LinearMap.lsmul O O c) h_mul_le
  let φ : O →ₗ[O] (O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {d * c}) :=
    LinearMap.toSpanSingleton O _ mulC
  have hφ (t : O) : φ t 1 = Ideal.Quotient.mk (Ideal.span {d * c}) (t * c) :=
    congrArg (Ideal.Quotient.mk _) (by simp)
  have h_ext {g g' : (O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {d * c})}
      (h_one : g 1 = g' 1) : g = g' :=
    Submodule.linearMap_qext _ (LinearMap.ext_ring h_one)
  have h_ker : LinearMap.ker φ = Ideal.span {d} := by
    ext t
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton,
      ← mul_dvd_mul_iff_right (right_ne_zero_of_mul ha),
      ← Ideal.Quotient.eq_zero_iff_dvd, ← hφ]
    exact ⟨fun h ↦ by rw [h, LinearMap.zero_apply], fun h ↦ h_ext h⟩
  have h_surj : Function.Surjective φ := fun g ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g 1)
    have h_zero : Ideal.Quotient.mk (Ideal.span {d * c}) (d * y) = 0 := by
      have h1 : d • (1 : O ⧸ Ideal.span {d}) = 0 := by
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_dvd]
      change d • Ideal.Quotient.mk (Ideal.span {d * c}) y = 0
      rw [hy, ← map_smul, h1, map_zero]
    obtain ⟨t, rfl⟩ : c ∣ y := by
      rwa [Ideal.Quotient.eq_zero_iff_dvd, mul_dvd_mul_iff_left (left_ne_zero_of_mul ha)] at h_zero
    exact ⟨t, h_ext (by rw [hφ, mul_comm t, hy])⟩
  exact ((Submodule.quotEquivOfEq _ _ h_ker.symm).trans
    (φ.quotKerEquivOfSurjective h_surj)).length_eq.symm

/-- Over a principal ideal domain `O`, a finitely generated `O`-module `Q` annihilated by `a ≠ 0`
has the same length as `Q →ₗ[O] (O ⧸ Ideal.span {a})`. -/
theorem length_linearMap_quotSpan [IsPrincipalIdealRing O] {Q : Type*} [AddCommGroup Q]
    [Module O Q] [Module.Finite O Q] {a : O} (ha : a ≠ 0) (h_kill : ∀ x : Q, a • x = 0) :
    Module.length O (Q →ₗ[O] (O ⧸ Ideal.span {a})) = Module.length O Q := by
  classical
  have h_torsion : Module.IsTorsion O Q :=
    fun x ↦ ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h_kill x⟩
  obtain ⟨ι, _, p, -, n, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion h_torsion
  let d (i : ι) : O := p i ^ n i
  let e' : Q ≃ₗ[O] ∀ i, O ⧸ Ideal.span {d i} := e.trans DFinsupp.linearEquivFunOnFintype
  have h_dvd (i : ι) : d i ∣ a := by
    have h_one : a • (1 : O ⧸ Ideal.span {d i}) = 0 := by
      simpa using congrFun (congrArg e' (h_kill (e'.symm (Pi.single i 1)))) i
    simpa [← Ideal.Quotient.eq_zero_iff_dvd, Algebra.smul_def] using h_one
  calc Module.length O (Q →ₗ[O] (O ⧸ Ideal.span {a}))
      = Module.length O (∀ i, (O ⧸ Ideal.span {d i}) →ₗ[O] (O ⧸ Ideal.span {a})) :=
        ((LinearMap.lsum O _ O).trans (e'.symm.congrLeft _ O)).length_eq.symm
    _ = Module.length O Q := by
      simp [e'.length_eq, Module.length_pi_of_fintype,
        length_linearMap_quotSpan_of_dvd ha (h_dvd _)]

end TauCeti
