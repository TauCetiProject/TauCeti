/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RingTheory.Idempotents.Module

/-!
# Corners of simple modules

Let `e` be an idempotent of a ring `A` and let `V` be a simple `A`-module. The piece `eV` is a
module over the corner ring `eAe` (`IsIdempotentElem.instModuleCornerSmulTop`). This file proves
that this corner module is simple as soon as it is nonzero, and that it determines `V`: two simple
`A`-modules whose nonzero corners at `e` are isomorphic over `eAe` are isomorphic over `A`.

Simplicity needs no complement and no finiteness. A nonzero `w ∈ eV` generates `V` over `A`, so
every `u ∈ eV` is `a w` for some `a : A`, and multiplying back by `e` gives `u = (e a e) w`.

For the second statement fix `v ≠ 0` in `eV` with image `v'` in `eV'`. If `a v = 0` but
`a v' ≠ 0`, simplicity of `V'` gives `b` with `b a v' = v'`. The corner element `e b a e` then
kills `v` and fixes `v'`, which is impossible since the isomorphism carries one to the other.
So `a v ↦ a v'` is a well-defined nonzero homomorphism `V → V'`, hence an isomorphism by Schur's
lemma.

A nondegenerate module over a nonunital ring `H` is a unital module over its unitization, and the
corner of the unitization at an idempotent of `H` consists of the elements `e h e` (with `h` in
the unitization), so the results apply to idempotented algebras through their unitizations.

## Main results

* `IsIdempotentElem.isSimpleModule_corner_smul_top`: **if `V` is simple and `eV ≠ 0`, then `eV`
  is a simple `eAe`-module.**
* `IsIdempotentElem.isSimpleModule_corner_smul_top_iff`: for simple `V`, the corner `eV` is a
  simple `eAe`-module exactly when it is nonzero.
* `IsIdempotentElem.nonempty_linearEquiv_of_corner`: simple `A`-modules with isomorphic nonzero
  corners at `e` are isomorphic.

## References

* J. A. Green, *Polynomial Representations of `GL_n`*, Lecture Notes in Math. 830, §6.2.
* D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math. 33,
  Part 1 (1979), Theorem 1 and its proof, pp. 179-180.
-/

public section

open scoped Pointwise

namespace IsIdempotentElem

variable {S A V : Type*} [Ring S] [Ring A] [AddCommGroup V] [Module S V] [Module A V]
  [SMulCommClass A S V] {e : A} (he : IsIdempotentElem e)

include he in
/-- An element `w` fixed by an idempotent `e` satisfies `a • w = (e * a * e) • w` whenever
`a • w` is itself fixed by `e`. -/
private theorem compress_smul_eq {w u : V} (hw : e • w = w) (hu : e • u = u) {a : A}
    (ha : a • w = u) : (he.compress a).val • w = u := by
  rw [val_compress, mul_smul, mul_smul, hw, ha, hu]

/-- **The corner of a simple module is simple.** If `V` is a simple `A`-module and the piece `eV`
is nonzero, then `eV` is a simple module over the corner ring `eAe`. -/
theorem isSimpleModule_corner_smul_top [IsSimpleModule A V]
    (h : e • (⊤ : Submodule S V) ≠ ⊥) :
    IsSimpleModule he.Corner ↥(e • (⊤ : Submodule S V)) := by
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨Submodule.nontrivial_iff_ne_bot.mpr h, fun w hw u ↦ ?_⟩
  have hw' : (w : V) ≠ 0 := fun h₀ ↦ hw (Subtype.ext h₀)
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hw' (u : V)
  exact ⟨he.compress a, Subtype.ext (he.compress_smul_eq
    (he.smul_eq_self_of_mem_smul_top w.property) (he.smul_eq_self_of_mem_smul_top u.property) ha)⟩

/-- For a simple `A`-module `V`, the corner `eV` is a simple `eAe`-module exactly when it is
nonzero. -/
theorem isSimpleModule_corner_smul_top_iff [IsSimpleModule A V] :
    IsSimpleModule he.Corner ↥(e • (⊤ : Submodule S V)) ↔ e • (⊤ : Submodule S V) ≠ ⊥ :=
  ⟨fun _ ↦ Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial he.Corner _),
    he.isSimpleModule_corner_smul_top⟩

variable {V' : Type*} [AddCommGroup V'] [Module S V'] [Module A V'] [SMulCommClass A S V']

/-- If `φ : eV ≃ eV'` is an isomorphism of corner modules, `V'` is simple and `v ∈ eV`, then
every `a : A` killing `v` kills `φ v`. -/
private theorem smul_eq_zero_of_linearEquiv_corner [IsSimpleModule A V']
    (φ : ↥(e • (⊤ : Submodule S V)) ≃ₗ[he.Corner] ↥(e • (⊤ : Submodule S V')))
    (v : ↥(e • (⊤ : Submodule S V))) (hv : v ≠ 0) {a : A} (ha : a • (v : V) = 0) :
    a • (φ v : V') = 0 := by
  by_contra hne
  obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective A hne (φ v : V')
  simp only [LinearMap.toSpanSingleton_apply, smul_smul] at hb
  have hv' := he.smul_eq_self_of_mem_smul_top (φ v).property
  have h₁ : (he.compress (b * a) • v : ↥(e • (⊤ : Submodule S V))) = 0 := by
    apply Subtype.ext
    rw [Corner.coe_smul, val_compress, mul_smul, mul_smul,
      he.smul_eq_self_of_mem_smul_top v.property, mul_smul, ha, smul_zero, smul_zero,
      ZeroMemClass.coe_zero]
  have h₂ : (he.compress (b * a) • φ v : ↥(e • (⊤ : Submodule S V'))) = φ v :=
    Subtype.ext (he.compress_smul_eq hv' hv' hb)
  rw [← map_smul, h₁, map_zero] at h₂
  exact hv ((LinearEquiv.map_eq_zero_iff φ).mp h₂.symm)

/-- **A simple module is determined by its nonzero corner.** Two simple `A`-modules whose
corners at an idempotent `e` are nonzero and isomorphic over `eAe` are isomorphic over `A`. -/
theorem nonempty_linearEquiv_of_corner [IsSimpleModule A V] [IsSimpleModule A V']
    (h : e • (⊤ : Submodule S V) ≠ ⊥)
    (φ : ↥(e • (⊤ : Submodule S V)) ≃ₗ[he.Corner] ↥(e • (⊤ : Submodule S V'))) :
    Nonempty (V ≃ₗ[A] V') := by
  obtain ⟨v₀, hv₀, hv₀ne⟩ := (Submodule.ne_bot_iff _).mp h
  set v : ↥(e • (⊤ : Submodule S V)) := ⟨v₀, hv₀⟩
  have hv : v ≠ 0 := fun h₀ ↦ hv₀ne (congrArg Subtype.val h₀)
  have hsurj := IsSimpleModule.toSpanSingleton_surjective A (M := V) hv₀ne
  have hle : LinearMap.ker (LinearMap.toSpanSingleton A V v₀) ≤
      LinearMap.ker (LinearMap.toSpanSingleton A V' (φ v : V')) := fun a ha ↦
    he.smul_eq_zero_of_linearEquiv_corner φ v hv ha
  let f : V →ₗ[A] V' := (LinearMap.toSpanSingleton A V v₀).liftOfSurjective hsurj
    ⟨LinearMap.toSpanSingleton A V' (φ v : V'), hle⟩
  have hf : f v₀ = (φ v : V') := by
    simpa using LinearMap.equivOfSurjective_apply hsurj hle (m := (1 : A))
  have hf0 : f ≠ 0 := fun h₀ ↦ by
    rw [h₀, LinearMap.zero_apply, eq_comm, ZeroMemClass.coe_eq_zero,
      LinearEquiv.map_eq_zero_iff] at hf
    exact hv hf
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf0)⟩

end IsIdempotentElem
