/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Base
public import TauCeti.LinearAlgebra.RootSystem.Dominance

/-!
# Positive cones and integral root dominance on direct sums of root pairings

The positive root cone and integral root dominance relation on both finite external direct sums
(`RootPairing.pi P`) and finite internal direct sums (`RootPairing.internalDirectSum hEi hEt P`)
decompose coordinatewise along the summands.

## Main results

* `RootPairing.mem_posRootCone_pi_iff`: membership in `TauCeti.posRootCone (pi P) (Base.pi b)` is
  coordinatewise membership in `TauCeti.posRootCone (P c) (b c)`.
* `RootPairing.rootLE_pi_iff`: integral root dominance on `RootPairing.pi P` is coordinatewise
  integral root dominance.
* `RootPairing.mem_posRootCone_internalDirectSum_iff` and
  `RootPairing.rootLE_internalDirectSum_iff`: the corresponding decompositions for
  `RootPairing.internalDirectSum hEi hEt P` along `TauCeti.internalProjection`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* M. Rapoport, *A positivity property of the Satake isomorphism*, Manuscripta Math. 101 (2000),
  153–166.
-/

public section

open Submodule TauCeti

namespace RootPairing

section External

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {P : ∀ c, RootPairing (ι c) R (M c) (N c)}

/-- **The positive root cone of a finite direct sum decomposes coordinatewise.** -/
theorem mem_posRootCone_pi_iff (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ TauCeti.posRootCone (pi P) (Base.pi b) ↔
      ∀ c, x c ∈ TauCeti.posRootCone (P c) (b c) := by
  rw [TauCeti.mem_posRootCone_iff_mem_span, Base.support_pi, Finset.coe_sigma, Finset.coe_univ]
  simpa only [← TauCeti.mem_posRootCone_iff_mem_span] using
    mem_span_pi_root_image_iff P ℕ (fun c ↦ (b c).support) x

/-- **Integral root dominance on a finite direct sum is coordinatewise integral root dominance.** -/
theorem rootLE_pi_iff (b : ∀ c, (P c).Base) (x y : ∀ c, M c) :
    (pi P).rootLE (Base.pi b) x y ↔ ∀ c, (P c).rootLE (b c) (x c) (y c) := by
  simpa [rootLE_iff_sub_mem_posRootCone] using mem_posRootCone_pi_iff b (y - x)

end External

section Internal

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {P : ∀ c, RootPairing (ι c) R (E c) (N c)}

/-- **The positive root cone of a finite internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_posRootCone_internalDirectSum_iff (b : ∀ c, (P c).Base) (x : M) :
    x ∈ posRootCone (internalDirectSum hEi hEt P) (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ posRootCone (P c) (b c) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  have h := e.rootLE_weightMap_iff (b := Base.pi b) (Base.internalDirectSum hEi hEt b)
    (fun s ↦ by simp [e]) 0 (e.weightEquiv.symm x)
  simp only [map_zero, Equiv.weightMap_weightEquiv_symm, rootLE_zero_left_iff] at h
  rw [h, mem_posRootCone_pi_iff]
  simp [e]

/-- **Integral root dominance on a finite internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem rootLE_internalDirectSum_iff (b : ∀ c, (P c).Base) (x y : M) :
    (internalDirectSum hEi hEt P).rootLE (Base.internalDirectSum hEi hEt b) x y ↔
      ∀ c, (P c).rootLE (b c) (internalProjection hEi hEt c x)
        (internalProjection hEi hEt c y) := by
  simpa [rootLE_iff_sub_mem_posRootCone, map_sub] using
    mem_posRootCone_internalDirectSum_iff (hEi := hEi) (hEt := hEt) b (y - x)

end Internal

end RootPairing
