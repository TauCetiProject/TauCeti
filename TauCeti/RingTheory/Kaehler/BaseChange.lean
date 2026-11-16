/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Ranges and splittings of base-change maps for Kähler differentials

This file identifies the base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` with the `liftBaseChange`
of `KaehlerDifferential.map R R A B`. It then records reusable consequences of the
Jacobi–Zariski sequence:
* the base-change map onto `Ω[B⁄R]` is surjective exactly when `Ω[B⁄A]` vanishes, and if
  `Ω[A⁄R]` is spanned by a set `s` then its range is spanned by the image of `s`;
* when `B` is formally smooth over `A`, `H¹(L_{B/A})` vanishes so the first map
  `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is injective and the short exact sequence
  `0 → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` splits as a `B`-module direct sum.

## Main results

* `TauCeti.mapBaseChange_eq_liftBaseChange`
* `TauCeti.subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top`
* `TauCeti.range_mapBaseChange_eq_span_image`
* `TauCeti.mapBaseChange_injective_of_formallySmooth`
* `TauCeti.exists_kaehlerDifferentialProdEquiv`
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential TensorProduct

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is the `B`-linear extension of the
`A`-linear map `KaehlerDifferential.map R R A B : Ω[A⁄R] → Ω[B⁄R]`. -/
theorem mapBaseChange_eq_liftBaseChange :
    mapBaseChange R A B = (map R R A B).liftBaseChange B := by
  ext; simp

/-- In a tower `R → A → B`, the first map in the Jacobi–Zariski sequence is surjective
exactly when the relative differential module `Ω[B⁄A]` vanishes. -/
theorem subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top :
    Subsingleton Ω[B⁄A] ↔ (mapBaseChange R A B).range = ⊤ := by
  -- The range of `mapBaseChange` is the kernel of `map R A B B : Ω[B⁄R] → Ω[B⁄A]`. That map
  -- is surjective, so it vanishes exactly when its range `⊤` is `⊥`, i.e. when `Ω[B⁄A]` is
  -- trivial.
  rw [range_mapBaseChange, LinearMap.ker_eq_top, ← LinearMap.range_eq_bot,
    LinearMap.range_eq_top.mpr (map_surjective R A B)]
  grind [subsingleton_iff_bot_eq_top, Submodule.subsingleton_iff]

/-- If `Ω[A⁄R]` is spanned by `s`, then the range of the base-change map to `Ω[B⁄R]` is
spanned by the image of `s`. -/
theorem range_mapBaseChange_eq_span_image {s : Set Ω[A⁄R]} (hs : Submodule.span A s = ⊤) :
    (mapBaseChange R A B).range = Submodule.span B (map R R A B '' s) := by
  rw [mapBaseChange_eq_liftBaseChange, LinearMap.range_liftBaseChange, LinearMap.range_eq_map,
    ← hs, ← Submodule.span_image, Submodule.span_span_of_tower]

/-- In a tower `R → A → B` with `B` formally smooth over `A`, the Jacobi–Zariski base-change map
`B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]` is injective because `H¹(L_{B/A})` is trivial. -/
theorem mapBaseChange_injective_of_formallySmooth [Algebra.FormallySmooth A B] :
    Function.Injective (mapBaseChange R A B) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem ⊥

/-- In a tower `R → A → B` with `B` formally smooth over `A`, the short exact Jacobi–Zariski
sequence `0 → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` splits, yielding a `B`-linear equivalence
`Ω[B⁄R] ≃ₗ[B] (B ⊗[A] Ω[A⁄R]) × Ω[B⁄A]` compatible with `mapBaseChange` and `map`. -/
theorem exists_kaehlerDifferentialProdEquiv [Algebra.FormallySmooth A B] :
    ∃ e : Ω[B⁄R] ≃ₗ[B] (B ⊗[A] Ω[A⁄R]) × Ω[B⁄A],
      mapBaseChange R A B = e.symm.toLinearMap ∘ₗ LinearMap.inl B (B ⊗[A] Ω[A⁄R]) Ω[B⁄A] ∧
      map R A B B = LinearMap.snd B (B ⊗[A] Ω[A⁄R]) Ω[B⁄A] ∘ₗ e.toLinearMap := by
  -- `Ω[B⁄A]` is projective since `B` is formally smooth over `A`, splitting the surjection `map`.
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (map R A B B) LinearMap.id
    (map_surjective R A B)
  obtain ⟨e, he⟩ := (exact_mapBaseChange_map R A B).splitSurjectiveEquiv
    (mapBaseChange_injective_of_formallySmooth R A B) ⟨l, hl⟩
  exact ⟨e, he⟩

end TauCeti
