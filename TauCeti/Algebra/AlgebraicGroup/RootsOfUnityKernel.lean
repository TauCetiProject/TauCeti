/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnityInclusion

/-!
# `μ_n` is the kernel of the `n`th power endomorphism of `𝔾ₘ`

The group scheme of `n`th roots of unity `μ_n = D(ℤ/n)` sits inside the multiplicative group
`𝔾ₘ = D(ℤ)` through the inclusion `TauCeti.RootsOfUnityGroup.inclusion`, the contravariant
image of the quotient `ℤ ↠ ℤ/n`. On the other side, `TauCeti.DiagonalizableGroup.powEnd n` is
the `n`th power endomorphism `u ↦ u ^ n` of `𝔾ₘ`. This file identifies `μ_n` with the kernel of
that endomorphism: on every commutative `R`-algebra `A`, the image of `μ_n(A) → 𝔾ₘ(A)` is
exactly the set of points killed by the `n`th power, so `μ_n` is the (scheme-theoretic) kernel
`ker(𝔾ₘ --u ↦ uⁿ--> 𝔾ₘ)`.

The mechanism is the worked-example points dictionary. A point of `𝔾ₘ = D(Multiplicative ℤ)` is
determined by the unit it reads off on the generator `Multiplicative.ofAdd 1`
(`DiagonalizableGroup.pointsMulEquiv_ext`). The `n`th power endomorphism raises that unit to the
`n`th power (`DiagonalizableGroup.pointsMulEquiv_powEnd`), while an included `μ_n`-point reads off
the underlying unit of an `n`th root of unity
(`RootsOfUnityGroup.charOfPoint_inclusion_ofAdd_one`), whose `n`th power is `1`. Conversely a
`𝔾ₘ`-point read off as a unit `u` with `u ^ n = 1` is `u ∈ rootsOfUnity n A`, hence the image of
the `μ_n`-point attached to it.

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 4: "`μ_n = D(ℤ/n)`", "`𝔾_m = D(ℤ)`", and
the diagonalizable anti-equivalence `M ↦ D(M)`), assembling the `μ_n` inclusion
`TauCeti.RootsOfUnityGroup.inclusion` and the power endomorphism
`TauCeti.DiagonalizableGroup.powEnd` of the character/cocharacter file into the classical
description of `μ_n` as a kernel.

## Main results

* `TauCeti.RootsOfUnityGroup.powEnd_comp_inclusion`: the `n`th power endomorphism annihilates
  `μ_n`, i.e. `powEnd n ∘ inclusion n` is trivial.
* `TauCeti.RootsOfUnityGroup.mem_range_inclusion`: a `𝔾ₘ`-point killed by the `n`th power lies
  in the image of the `μ_n` inclusion.
* `TauCeti.RootsOfUnityGroup.range_inclusion`: the image of `μ_n ↪ 𝔾ₘ` is the kernel of the
  `n`th power endomorphism of `𝔾ₘ`.

## References

The `μ_n` inclusion and `𝔾ₘ` points calculation are Tau Ceti's
`TauCeti.RootsOfUnityGroup.inclusion` and `TauCeti.RootsOfUnityGroup.pointsMulEquiv`; the power
endomorphism of `𝔾ₘ` is `TauCeti.DiagonalizableGroup.powEnd`. The subgroup of `n`th roots of
unity and `mem_rootsOfUnity` are Mathlib's (`Mathlib.RingTheory.RootsOfUnity.Basic`), and the
one-generator extensionality `MonoidHom.ext_mint` is from `Mathlib.Data.Int.Cast.Lemmas`.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The `n`th power endomorphism of `𝔾ₘ` annihilates `μ_n`.** Composing the power endomorphism
`DiagonalizableGroup.powEnd n` after the inclusion `μ_n ↪ 𝔾ₘ` is the trivial homomorphism of
group functors: every `μ_n`-point maps to a root of unity, whose `n`th power is `1`. -/
theorem powEnd_comp_inclusion (n : ℕ) :
    (DiagonalizableGroup.powEnd (R := R) (A := A) (n : ℤ)).comp (inclusion n) = 1 := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, MonoidHom.one_apply]
  apply DiagonalizableGroup.pointsMulEquiv_ext
  rw [DiagonalizableGroup.pointsMulEquiv_powEnd, DiagonalizableGroup.pointsMulEquiv_apply,
    charOfPoint_inclusion_ofAdd_one, map_one, MonoidHom.one_apply, zpow_natCast]
  exact (mem_rootsOfUnity n _).mp (SetLike.coe_mem (pointsMulEquiv (R := R) (A := A) n f))

/-- The `n`th power endomorphism annihilates every `μ_n`-point, in element form. -/
theorem powEnd_inclusion (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    DiagonalizableGroup.powEnd (R := R) (A := A) (n : ℤ) (inclusion n f) = 1 := by
  have := DFunLike.congr_fun (powEnd_comp_inclusion (R := R) (A := A) n) f
  simpa using this

/-- **A `𝔾ₘ`-point killed by the `n`th power lies in the image of `μ_n`.** If the `n`th power
endomorphism sends `g` to the identity, then `g` reads off a unit `u` with `u ^ n = 1`, i.e. an
`n`th root of unity, and `g` is the image of the `μ_n`-point attached to it. -/
theorem mem_range_inclusion (n : ℕ)
    {g : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)}
    (hg : DiagonalizableGroup.powEnd (R := R) (A := A) (n : ℤ) g = 1) :
    g ∈ Set.range (inclusion (R := R) (A := A) n) := by
  have hun : DiagonalizableGroup.pointsMulEquiv g (Multiplicative.ofAdd (1 : ℤ)) ^ n = 1 := by
    have h1 :
        DiagonalizableGroup.pointsMulEquiv g (Multiplicative.ofAdd (1 : ℤ)) ^ (n : ℤ) = 1 := by
      rw [← DiagonalizableGroup.pointsMulEquiv_powEnd, hg, map_one, MonoidHom.one_apply]
    rwa [zpow_natCast] at h1
  refine ⟨(pointsMulEquiv (R := R) (A := A) n).symm
      ⟨DiagonalizableGroup.pointsMulEquiv g (Multiplicative.ofAdd (1 : ℤ)),
        (mem_rootsOfUnity n _).mpr hun⟩, ?_⟩
  apply DiagonalizableGroup.pointsMulEquiv_ext
  rw [DiagonalizableGroup.pointsMulEquiv_apply, charOfPoint_inclusion_ofAdd_one,
    MulEquiv.apply_symm_apply]

/-- **`μ_n` is the kernel of the `n`th power endomorphism of `𝔾ₘ`.** The image of the inclusion
`μ_n ↪ 𝔾ₘ` on points equals the set of points killed by the `n`th power endomorphism
`DiagonalizableGroup.powEnd n`: a `𝔾ₘ`-point comes from `μ_n` exactly when its `n`th power is
trivial. This realizes `μ_n = ker(𝔾ₘ --u ↦ uⁿ--> 𝔾ₘ)` on the functor of points. -/
theorem range_inclusion (n : ℕ) :
    Set.range (inclusion (R := R) (A := A) n) =
      {g | DiagonalizableGroup.powEnd (R := R) (A := A) (n : ℤ) g = 1} := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    exact powEnd_inclusion n f
  · exact fun hg => mem_range_inclusion n hg

end RootsOfUnityGroup

end TauCeti
