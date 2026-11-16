/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Prod

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# The generic full-Cartan Lie carrier

Both `Matrix.FullShellLieAlgebra` and `RootPairing.ChevalleyLieAlgebra` realize a `ℤ`-Lie algebra on
`Y × (Φ →₀ ℤ)` for an abelian Cartan group `Y` (retaining central directions and torsion with no
chosen splitting) and root index type `Φ`. This file factors out `TauCeti.FullCartan Y Φ`, `cartan`,
`root`, `linearMap_ext`, `bracketBilin`, and generator-reduction Lie axioms (`bracketBilin_skew`,
`bracketBilin_self`, `bracketBilin_jacobi`, `bracketBilin_leibniz`).

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 1.
-/

public section

namespace TauCeti

/-- **Generic full-Cartan Lie carrier** `Y × (Φ →₀ ℤ)` combining an abelian Cartan group `Y` with
one free `ℤ`-line for each root index in `Φ`. -/
@[expose] def FullCartan (Y Φ : Type*) : Type _ := Y × (Φ →₀ ℤ)

namespace FullCartan

variable (Y Φ : Type*) [AddCommGroup Y]

noncomputable instance instAddCommGroup : AddCommGroup (FullCartan Y Φ) :=
  inferInstanceAs (AddCommGroup (Y × (Φ →₀ ℤ)))

/-- Identification of `FullCartan Y Φ` with its underlying product `Y × (Φ →₀ ℤ)`. -/
noncomputable def equivProd : FullCartan Y Φ ≃ₗ[ℤ] Y × (Φ →₀ ℤ) := LinearEquiv.refl ℤ _

/-- The Cartan generator `H_y` of `y : Y`, as a `ℤ`-linear embedding into `FullCartan Y Φ`. -/
noncomputable def cartan : Y →ₗ[ℤ] FullCartan Y Φ :=
  (equivProd Y Φ).symm.toLinearMap ∘ₗ LinearMap.inl ℤ Y (Φ →₀ ℤ)

/-- The root generator `e_a` attached to `a : Φ`. -/
noncomputable def root (a : Φ) : FullCartan Y Φ := (equivProd Y Φ).symm (0, Finsupp.single a 1)

variable {Y Φ}

@[simp] theorem equivProd_cartan (y : Y) : equivProd Y Φ (cartan Y Φ y) = (y, 0) := by simp [cartan]

@[simp] theorem equivProd_root (a : Φ) : equivProd Y Φ (root Y Φ a) = (0, Finsupp.single a 1) := by
  simp [root]

/-- The Cartan embedding `cartan Y Φ` is injective. -/
theorem cartan_injective : Function.Injective (cartan Y Φ) := fun _ _ h ↦ by
  simpa using congrArg (fun u ↦ (equivProd Y Φ u).1) h

/-- Every root generator `root Y Φ a` is nonzero. -/
theorem root_ne_zero (a : Φ) : root Y Φ a ≠ 0 := fun h ↦ by
  simpa using congrArg (fun u ↦ (equivProd Y Φ u).2 a) h

/-- Two `ℤ`-linear maps out of `FullCartan Y Φ` agree once they agree on all Cartan and root
generators. -/
theorem linearMap_ext {N : Type*} [AddCommGroup N] {f g : FullCartan Y Φ →ₗ[ℤ] N}
    (hc : ∀ y, f (cartan Y Φ y) = g (cartan Y Φ y))
    (hr : ∀ a, f (root Y Φ a) = g (root Y Φ a)) : f = g := by
  have key : f ∘ₗ (equivProd Y Φ).symm.toLinearMap = g ∘ₗ (equivProd Y Φ).symm.toLinearMap :=
    LinearMap.prod_ext (LinearMap.ext hc) (Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring (hr a))
  simpa using congr($key ∘ₗ (equivProd Y Φ).toLinearMap)

private noncomputable def cartanAction (w : Φ → Y →ₗ[ℤ] ℤ) :
    Y →ₗ[ℤ] (Φ →₀ ℤ) →ₗ[ℤ] FullCartan Y Φ :=
  (Finsupp.linearCombination ℤ fun b ↦ (w b).smulRight (root Y Φ b)).flip

private noncomputable def rootPart (rb : Φ → Φ → FullCartan Y Φ) :
    (Φ →₀ ℤ) →ₗ[ℤ] (Φ →₀ ℤ) →ₗ[ℤ] FullCartan Y Φ :=
  Finsupp.linearCombination ℤ fun a ↦ Finsupp.linearCombination ℤ fun b ↦ rb a b

/-- **The `ℤ`-bilinear bracket on `FullCartan Y Φ`** determined by root weights `w : Φ → Y →ₗ[ℤ] ℤ`
and a root-generator bracket `rb : Φ → Φ → FullCartan Y Φ`: `⁅H_y, H_z⁆ = 0`,
`⁅H_y, e_b⁆ = w b y • e_b`, `⁅e_a, H_z⁆ = -(w a z • e_a)`, and `⁅e_a, e_b⁆ = rb a b`. -/
noncomputable def bracketBilin (w : Φ → Y →ₗ[ℤ] ℤ) (rb : Φ → Φ → FullCartan Y Φ) :
    FullCartan Y Φ →ₗ[ℤ] FullCartan Y Φ →ₗ[ℤ] FullCartan Y Φ :=
  let fst := LinearMap.fst ℤ Y (Φ →₀ ℤ) ∘ₗ (equivProd Y Φ).toLinearMap
  let snd := LinearMap.snd ℤ Y (Φ →₀ ℤ) ∘ₗ (equivProd Y Φ).toLinearMap
  (cartanAction w).compl₁₂ fst snd - ((cartanAction w).compl₁₂ fst snd).flip +
    (rootPart rb).compl₁₂ snd snd

@[simp] theorem bracketBilin_cartan_cartan (w : Φ → Y →ₗ[ℤ] ℤ) (rb : Φ → Φ → FullCartan Y Φ)
    (y z : Y) : bracketBilin w rb (cartan Y Φ y) (cartan Y Φ z) = 0 := by simp [bracketBilin]

@[simp] theorem bracketBilin_cartan_root (w : Φ → Y →ₗ[ℤ] ℤ) (rb : Φ → Φ → FullCartan Y Φ) (y : Y)
    (b : Φ) : bracketBilin w rb (cartan Y Φ y) (root Y Φ b) = w b y • root Y Φ b := by
  simp [bracketBilin, cartanAction]

@[simp] theorem bracketBilin_root_cartan (w : Φ → Y →ₗ[ℤ] ℤ) (rb : Φ → Φ → FullCartan Y Φ) (a : Φ)
    (z : Y) : bracketBilin w rb (root Y Φ a) (cartan Y Φ z) = -(w a z • root Y Φ a) := by
  simp [bracketBilin, cartanAction]

@[simp] theorem bracketBilin_root_root (w : Φ → Y →ₗ[ℤ] ℤ) (rb : Φ → Φ → FullCartan Y Φ) (a b : Φ) :
    bracketBilin w rb (root Y Φ a) (root Y Φ b) = rb a b := by simp [bracketBilin, rootPart]

attribute [irreducible] bracketBilin

variable {w : Φ → Y →ₗ[ℤ] ℤ} {rb : Φ → Φ → FullCartan Y Φ}

/-- Antisymmetry of `bracketBilin w rb` once `rb` is antisymmetric on root generators. -/
theorem bracketBilin_skew (hswap : ∀ a b, rb b a = -rb a b) (x y : FullCartan Y Φ) :
    bracketBilin w rb y x = -bracketBilin w rb x y := by
  have key : (bracketBilin w rb).flip = -bracketBilin w rb :=
    linearMap_ext (fun _ ↦ linearMap_ext (by simp) (by simp))
      fun a ↦ linearMap_ext (by simp) fun b ↦ by simp [hswap a b]
  simpa using congr($key x y)

/-- Alternation `bracketBilin w rb x x = 0` once `rb` is antisymmetric and vanishes on repeated
root generators (allowing `2`-torsion in `Y`). -/
theorem bracketBilin_self (hswap : ∀ a b, rb b a = -rb a b) (hself : ∀ a, rb a a = 0)
    (x : FullCartan Y Φ) : bracketBilin w rb x x = 0 := by
  let q : FullCartan Y Φ →+ FullCartan Y Φ :=
    { toFun u := bracketBilin w rb u u, map_zero' := by simp
      map_add' u v := by
        simp only [map_add, LinearMap.add_apply, bracketBilin_skew hswap u v]; abel }
  exact congr($(linearMap_ext (f := q.toIntLinearMap) (g := 0) (by simp [q])
    fun a ↦ by simp [q, hself a]) x)

section Jacobi

variable (hswap : ∀ a b, rb b a = -rb a b)
  (hweight : ∀ y a b, bracketBilin w rb (cartan Y Φ y) (rb a b) = (w a y + w b y) • rb a b)
  (hjacobi : ∀ a b c, bracketBilin w rb (root Y Φ a) (rb b c) +
    bracketBilin w rb (root Y Φ b) (rb c a) + bracketBilin w rb (root Y Φ c) (rb a b) = 0)
include hswap hweight hjacobi

private theorem jacobi_gen_gen (u v : Y ⊕ Φ) (z : FullCartan Y Φ) :
    let gen := Sum.elim (cartan Y Φ) (root Y Φ)
    bracketBilin w rb (gen u) (bracketBilin w rb (gen v) z) +
      bracketBilin w rb (gen v) (bracketBilin w rb z (gen u)) +
      bracketBilin w rb z (bracketBilin w rb (gen u) (gen v)) = 0 := by
  intro gen
  have key : bracketBilin w rb (gen u) ∘ₗ bracketBilin w rb (gen v) +
      bracketBilin w rb (gen v) ∘ₗ (bracketBilin w rb).flip (gen u) +
      (bracketBilin w rb).flip (bracketBilin w rb (gen u) (gen v)) = 0 := by
    refine linearMap_ext (fun y ↦ ?_) fun c ↦ ?_ <;>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
        LinearMap.zero_apply] <;>
      rcases u with y₁ | a <;> rcases v with y₂ | b <;>
      simp only [gen, Sum.elim_inl, Sum.elim_inr, bracketBilin_cartan_cartan,
        bracketBilin_cartan_root, bracketBilin_root_cartan, bracketBilin_root_root, hweight,
        map_smul, map_neg, map_zero]
    all_goals try module
    · rw [hswap a b]; module
    · rw [hswap b c]; module
    · rw [hswap a c]; module
    · exact hjacobi a b c
  simpa using congr($key z)

/-- **Generator reduction for the Jacobi identity on `FullCartan Y Φ`.** -/
theorem bracketBilin_jacobi (x y z : FullCartan Y Φ) :
    bracketBilin w rb x (bracketBilin w rb y z) + bracketBilin w rb y (bracketBilin w rb z x) +
      bracketBilin w rb z (bracketBilin w rb x y) = 0 := by
  let gen := Sum.elim (cartan Y Φ) (root Y Φ)
  have h₂ (u : Y ⊕ Φ) (y z : FullCartan Y Φ) :
      bracketBilin w rb (gen u) (bracketBilin w rb y z) +
        bracketBilin w rb y (bracketBilin w rb z (gen u)) +
        bracketBilin w rb z (bracketBilin w rb (gen u) y) = 0 := by
    have key : bracketBilin w rb (gen u) ∘ₗ (bracketBilin w rb).flip z +
        (bracketBilin w rb).flip (bracketBilin w rb z (gen u)) +
        bracketBilin w rb z ∘ₗ bracketBilin w rb (gen u) = 0 :=
      linearMap_ext (fun y ↦ by simpa using jacobi_gen_gen hswap hweight hjacobi u (.inl y) z)
        fun b ↦ by simpa using jacobi_gen_gen hswap hweight hjacobi u (.inr b) z
    simpa [add_rotate] using congr($key y)
  have key : (bracketBilin w rb).flip (bracketBilin w rb y z) +
      bracketBilin w rb y ∘ₗ bracketBilin w rb z +
      bracketBilin w rb z ∘ₗ (bracketBilin w rb).flip y = 0 :=
    linearMap_ext (fun x ↦ by simpa [gen] using h₂ (.inl x) y z)
      fun a ↦ by simpa [gen] using h₂ (.inr a) y z
  simpa [add_rotate] using congr($key x)

/-- The Leibniz form of the Jacobi identity for `bracketBilin w rb`. -/
theorem bracketBilin_leibniz (x y z : FullCartan Y Φ) :
    bracketBilin w rb x (bracketBilin w rb y z) =
      bracketBilin w rb (bracketBilin w rb x y) z +
        bracketBilin w rb y (bracketBilin w rb x z) := by
  rw [bracketBilin_skew hswap z (bracketBilin w rb x y), bracketBilin_skew hswap z x, map_neg,
    ← sub_eq_zero, ← bracketBilin_jacobi hswap hweight hjacobi x y z]; abel

end Jacobi

end FullCartan

end TauCeti
