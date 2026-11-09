/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Opposite
public import TauCeti.LinearAlgebra.Exact

/-!
# Reflexivity of kernels and cokernels

For a left module `X` over a possibly noncommutative ring `A`, evaluation
`TauCeti.opDualEval A X : X ⟶ X**` maps `X` to the `A`-valued dual of its right dual `X*`. A
module is reflexive when this map is bijective; finitely generated projective modules are
reflexive (`TauCeti.opDualEval_bijective`).

This file proves two diagram-chasing criteria, used for totally reflexive modules.

* If `0 ⟶ X ⟶ Y ⟶ Z` is exact, every functional on `X` extends to `Y`, `Y` is reflexive and
  evaluation on `Z` is injective, then `X` is reflexive.
* If `X ⟶ Y ⟶ Z ⟶ 0` is exact, the dual map `Y* ⟶ X*` is surjective, every functional on `Z*`
  extends to `Y*`, evaluation on `X` is surjective and `Y` is reflexive, then `Z` is reflexive.

## Main results

* `TauCeti.opDualEval_bijective_of_exact`: reflexivity passes to kernels.
* `TauCeti.opDualEval_bijective_of_exact_of_surjective`: reflexivity passes to cokernels.
-/

public section

namespace TauCeti

section Reflexive

variable (A : Type*) [Ring A] {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
  [Module A Y] [AddCommGroup Z] [Module A Z]

/-- **Reflexivity passes to kernels.** Let `0 ⟶ X ⟶ Y ⟶ Z` be exact, with every functional on `X`
extending to `Y`. If evaluation into the opposite double dual is bijective for `Y` and injective
for `Z`, then it is bijective for `X`. -/
theorem opDualEval_bijective_of_exact {ι : X →ₗ[A] Y} {g : Y →ₗ[A] Z}
    (hι : Function.Injective ι) (hexact : Function.Exact ι g)
    (hext : Function.Surjective (ι.lcomp Aᵐᵒᵖ A)) (hY : Function.Bijective (opDualEval A Y))
    (hZ : Function.Injective (opDualEval A Z)) : Function.Bijective (opDualEval A X) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ hι (hY.1 ?_), fun χ ↦ ?_⟩
  · -- Every functional on `Y` vanishes at `ι x`, since it restricts to a functional on `X`.
    ext ψ
    simpa using LinearMap.congr_fun hx (ψ ∘ₗ ι)
  · -- `χ` composed with restriction is evaluation at some `y`, and `g y = 0` since `g ∘ ι = 0`.
    obtain ⟨y, hy⟩ := hY.2 (χ ∘ₗ ι.lcomp Aᵐᵒᵖ A)
    have hgy : g y = 0 := hZ <| by
      ext ψ
      have h := LinearMap.congr_fun hy (ψ ∘ₗ g)
      have hz : (ψ ∘ₗ g) ∘ₗ ι = 0 := by
        ext x
        simp [hexact.apply_apply_eq_zero]
      simp only [opDualEval_apply, LinearMap.comp_apply, LinearMap.lcomp_apply'] at h
      simp [h, hz]
    obtain ⟨x, rfl⟩ := (hexact y).1 hgy
    refine ⟨x, LinearMap.ext fun φ ↦ ?_⟩
    obtain ⟨ψ, rfl⟩ := hext φ
    simpa using LinearMap.congr_fun hy ψ

/-- **Reflexivity passes to cokernels.** Let `X ⟶ Y ⟶ Z ⟶ 0` be exact, with the dual map
`Y* ⟶ X*` surjective and every functional on `Z*` extending to `Y*`. If evaluation into the
opposite double dual is surjective for `X` and bijective for `Y`, then it is bijective for `Z`. -/
theorem opDualEval_bijective_of_exact_of_surjective {j : X →ₗ[A] Y} {q : Y →ₗ[A] Z}
    (hexact : Function.Exact j q) (hq : Function.Surjective q)
    (hj : Function.Surjective (j.lcomp Aᵐᵒᵖ A))
    (hext : Function.Surjective ((q.lcomp Aᵐᵒᵖ A).lcomp A A))
    (hX : Function.Surjective (opDualEval A X)) (hY : Function.Bijective (opDualEval A Y)) :
    Function.Bijective (opDualEval A Z) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun χ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := hq z
    -- Evaluation at `y` vanishes on the image of `q*`, which is the kernel of `j*`.
    have hy : (q.lcomp Aᵐᵒᵖ A).lcomp A A (opDualEval A Y y) = 0 := by
      rw [← opDualEval_naturality, hz]
    obtain ⟨ρ, hρ⟩ := ((hexact.lcomp_of_surjective (T := Aᵐᵒᵖ) A hq).lcomp_of_surjective
      (T := A) A hj (opDualEval A Y y)).1 hy
    obtain ⟨x, rfl⟩ := hX ρ
    have hjx : opDualEval A Y (j x) = opDualEval A Y y := by
      rw [opDualEval_naturality, ← hρ, LinearMap.lcomp_apply']
    rw [← hY.1 hjx, hexact.apply_apply_eq_zero]
  · obtain ⟨χ', hχ'⟩ := hext χ
    obtain ⟨y, rfl⟩ := hY.2 χ'
    refine ⟨q y, ?_⟩
    rw [opDualEval_naturality, hχ']

end Reflexive

end TauCeti
