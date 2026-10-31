/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Smooth base change preserves integral closedness

If `R` is integrally closed in an `R`-algebra `B` and `S` is a smooth `R`-algebra, then `S` is
integrally closed in `S ⊗[R] B`. This is the form of Mathlib's theorem that smooth base change
commutes with integral closure (`TensorProduct.toIntegralClosure_bijective_of_smooth`, Stacks
0CBF) used to show that étale algebras over normal domains are normal: for `B` the fraction field
of an integrally closed domain `R`, `S` is integrally closed in its generic fibre.

## Main results

* `TauCeti.Algebra.Smooth.isIntegrallyClosedIn_tensorProduct`: a smooth algebra `S` over `R` is
  integrally closed in `S ⊗[R] B` whenever `R` is integrally closed in `B`. It is an instance.
* `IsIntegral.exists_includeRight_eq`: the same with the factors in the other order: every element
  of `B ⊗[R] S` integral over `R` comes from `S`.

## References

* [Stacks Project, Lemma 10.147.5](https://stacks.math.columbia.edu/tag/0CBF).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Common/EtaleNormal.lean`: `Algebra.Smooth.isIntegrallyClosedIn_tensorProduct`
  generalizes its `Pcf.Stacks.isIntegrallyClosedIn_tensor_fractionRing_of_smooth` from the
  fraction field of an integrally closed domain to any algebra in which `R` is integrally closed.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.Smooth

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
  [IsIntegrallyClosedIn R B]

/-- A smooth `R`-algebra `S` is integrally closed in `S ⊗[R] B` whenever `R` is integrally closed
in `B`. -/
instance isIntegrallyClosedIn_tensorProduct [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  obtain ⟨hRB, hint⟩ := isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn R B›
  rw [isIntegrallyClosedIn_iff]
  refine ⟨?_, fun {x} hx ↦ ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := S) (A := S) hRB
  · obtain ⟨w, hw⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := B)).2 ⟨x, hx⟩
    -- `toIntegralClosure` is `Algebra.TensorProduct.map` of the integral-closure inclusion,
    -- corestricted to `integralClosure S (S ⊗[R] B)`; `Subtype.val` undoes the corestriction.
    have hx' : x = Algebra.TensorProduct.map (AlgHom.id R S) (integralClosure R B).val w :=
      (congrArg Subtype.val hw).symm
    rw [hx']
    clear hw hx'
    induction w with
    | tmul a b =>
      obtain ⟨r, hr⟩ := hint b.2
      refine ⟨r • a, ?_⟩
      simp [← hr, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one r,
        TensorProduct.smul_tmul]
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁⟩ := h₁
      obtain ⟨s₂, hs₂⟩ := h₂
      exact ⟨s₁ + s₂, by rw [map_add, hs₁, hs₂, map_add]⟩

end TauCeti.Algebra.Smooth

namespace IsIntegral

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
  [IsIntegrallyClosedIn R B]

/-- Every element of `B ⊗[R] S` that is integral over `R` comes from the smooth `R`-algebra `S`,
when `R` is integrally closed in `B`. This is
`TauCeti.Algebra.Smooth.isIntegrallyClosedIn_tensorProduct` with the factors in the other order. -/
theorem exists_includeRight_eq [Algebra.Smooth R S] {z : B ⊗[R] S} (hz : IsIntegral R z) :
    ∃ s : S, Algebra.TensorProduct.includeRight s = z := by
  let σ := Algebra.TensorProduct.comm R B S
  obtain ⟨s, hs⟩ := (isIntegrallyClosedIn_iff.mp
    (inferInstance : IsIntegrallyClosedIn S (S ⊗[R] B))).2 ((hz.map σ).tower_top (A := S))
  refine ⟨s, σ.injective ?_⟩
  simpa [σ, Algebra.TensorProduct.algebraMap_apply] using hs

end IsIntegral
