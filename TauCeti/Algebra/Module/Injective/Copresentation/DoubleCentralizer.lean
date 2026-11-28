/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Injective

/-!
# The double centralizer property from an injective copresentation

Let `Q` be an injective module over a ring `Γ`, with endomorphism ring `B = Module.End Γ Q`
acting on `Q` by evaluation. Suppose that `Γ` has an exact sequence `0 → Γ → Q → Qᶥ`, that is,
an injective map `f : Γ → Q` whose range is the kernel of a map `g : Q → Qᶥ`. Then the action map
`Γ → Module.End B Q` is bijective (`TauCeti.toModuleEnd_moduleEnd_bijective_of_exact`): `Γ` is
recovered as the ring of `B`-linear endomorphisms of `Q`. This is the **double centralizer
property** of `Q`.

For an Artin algebra `Γ` of dominant dimension at least two, the two terms of the copresentation
`0 → Γ → I₀ → I₁` by projective-injective modules give such a sequence for `Q = I₀ × I₁`. This is
the step of the converse of the Morita-Tachikawa correspondence that recovers `Γ` as an
endomorphism ring (`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`).

## Implementation notes

Let `φ` be `B`-linear. The coordinates of `g` lie in `B`, so `φ` commutes with them and maps
`f 1` into `ker g = range f`, say `φ (f 1) = f γ = γ • f 1`. For `x : Q`, injectivity of `Q`
extends `1 ↦ x` along `f` to an endomorphism `k` of `Q` with `k (f 1) = x`; since `φ` commutes
with `k`, this gives `φ x = γ • x`. Injectivity of the action map is injectivity of `f`.

## Main results

* `TauCeti.toModuleEnd_moduleEnd_bijective_of_exact`: **the double centralizer property of an
  injective copresentation**.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5.
-/

public section

namespace TauCeti

universe u v

/-- **The double centralizer property of an injective copresentation.** Let `Q` be an injective
`Γ`-module with an exact sequence `0 → Γ → Q → Qᶥ`, given by an injective `f` and a `g` with
`range f = ker g`. Then the action map `Γ → Module.End B Q`, for `B = Module.End Γ Q`, is
bijective. -/
theorem toModuleEnd_moduleEnd_bijective_of_exact {Γ : Type u} [Ring Γ] {Q : Type v}
    [AddCommGroup Q] [Module Γ Q] [Module.Injective Γ Q] {ι : Type*} {f : Γ →ₗ[Γ] Q}
    {g : Q →ₗ[Γ] ι → Q} (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Bijective (Module.toModuleEnd (Module.End Γ Q) Q (S := Γ)) := by
  have : Small.{v} Γ := small_of_injective hf
  have hf1 (γ : Γ) : f γ = γ • f 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  refine ⟨fun a b h ↦ hf ?_, fun φ ↦ ?_⟩
  · simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, ← hf1] using
      LinearMap.congr_fun h (f 1)
  -- `φ` commutes with the coordinates of `g`, so `φ (f 1)` lies in `ker g = range f`.
  obtain ⟨γ, hγ⟩ := (hfg (φ (f 1))).1 <| funext fun i ↦ by
    simpa [Module.End.smul_def, hfg.apply_apply_eq_zero] using
      (φ.map_smul (LinearMap.proj i ∘ₗ g) (f 1)).symm
  refine ⟨γ, LinearMap.ext fun x ↦ ?_⟩
  -- Extend `1 ↦ x` along `f` to an endomorphism `k` of `Q`, which `φ` commutes with.
  obtain ⟨k, hk⟩ := Module.Injective.extension_property Γ Q Γ Q f hf
    (LinearMap.toSpanSingleton Γ Q x)
  have hx : k (f 1) = x := by simpa using LinearMap.congr_fun hk 1
  have h1 : φ x = k (f γ) := by
    rw [hγ, ← hx]
    exact φ.map_smul k (f 1)
  rw [h1, hf1, map_smul, hx, Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply]

end TauCeti
