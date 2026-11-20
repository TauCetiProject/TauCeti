/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Topology
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Exponentials of compatible nilpotent endomorphisms

A compatible family of nilpotent endomorphisms of a tower of rational modules exponentiates
to a linear automorphism of its limit. Each coordinate is the finite exponential at that
level. Nilpotence bounds may grow with the level, so the induced endomorphism on the limit
need not be nilpotent. The automorphism preserves and reflects every projection kernel and
is continuous for the inverse limit topology. Intertwining morphisms of towers commute
with these automorphisms.

This is the compatible-family construction used for completed filtered Lie module actions
in §0.6 of the ScatteringDiagrams roadmap. It uses `Module.End.locallyNilpotentExp` and
`ModuleTower.limEquivOfIso`. Adapted from the completion construction in
`Mei/Algebra/Lie/Filtered/Module.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite Topology

variable {R : Type*} [Ring R] (F : ModuleTower R)
  [∀ n : ℕ, Module ℚ (F.obj (op n))]
  (D : ∀ n : ℕ, Module.End R (F.obj (op n))) (hD : ∀ n, IsNilpotent (D n))
  (hcompat : ∀ {n k : ℕ} (h : n ≤ k), Function.Semiconj (F.transitionOfLE h) (D k) (D n))

/-- The finite exponentials form an automorphism of the tower. -/
def expIso : F ≅ F :=
  NatIso.ofComponents
    (fun n ↦ ((D n.unop).locallyNilpotentExp (hD n.unop).exists_pow_apply_eq_zero).toModuleIso)
    (by
      intro n k f
      ext x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
        map_hom_eq_transitionOfLE] using
        (Module.End.map_locallyNilpotentExp (D n.unop) _ _
          (F.transitionOfLE (leOfHom f.unop)) (hcompat _) x).symm)

/-- The exponential on the limit of a tower, defined by its finite-level exponentials. -/
def limExp : F.lim ≃ₗ[R] F.lim :=
  limEquivOfIso (F.expIso D hD hcompat)

/-- A projection computes the exponential at the corresponding finite level. -/
@[simp]
theorem coe_limExp_apply (x : F.lim) (n : ℕ) :
    (F.limExp D hD hcompat x : F.Product) n = IsNilpotent.exp (D n) ((x : F.Product) n) := by
  rw [← F.limπ_apply, ← F.limπ_apply]
  rw [limExp, limEquivOfIso_apply, ← LinearMap.comp_apply, limπ_comp_limMap]
  simp only [LinearMap.comp_apply, expIso, NatIso.ofComponents_hom_app,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (D n) (hD n)) _

/-- The inverse is computed by exponentiating the negative endomorphism at each level. -/
@[simp]
theorem coe_limExp_symm_apply (x : F.lim) (n : ℕ) :
    ((F.limExp D hD hcompat).symm x : F.Product) n =
      IsNilpotent.exp (-D n) ((x : F.Product) n) := by
  rw [← F.limπ_apply, ← F.limπ_apply]
  rw [limExp, limEquivOfIso_symm_apply, ← LinearMap.comp_apply, limπ_comp_limMap]
  simp only [LinearMap.comp_apply, expIso, NatIso.ofComponents_inv_app,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  rw [Module.End.locallyNilpotentExp_symm]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (-D n) (hD n).neg) _

/-- Exponentiation preserves and reflects the filtration by projection kernels. -/
theorem limExp_mem_ker_limπ_iff (x : F.lim) (n : ℕ) :
    F.limExp D hD hcompat x ∈ LinearMap.ker (F.limπ n) ↔
      x ∈ LinearMap.ker (F.limπ n) := by
  simp only [LinearMap.mem_ker, limπ_apply, coe_limExp_apply]
  rw [← Module.End.locallyNilpotentExp_eq_exp (D n) (hD n), LinearEquiv.coe_coe,
    EmbeddingLike.map_eq_zero_iff]

/-- The completed exponential is continuous for the inverse limit topology. -/
theorem continuous_limExp : Continuous (F.limExp D hD hcompat) := by
  apply continuous_of_tendsto_nhds_zero (F.limExp D hD hcompat).toLinearMap
  exact (F.hasBasis_nhds_zero.tendsto_iff F.hasBasis_nhds_zero).2 fun n _ ↦
    ⟨n, trivial, fun x hx ↦ (F.limExp_mem_ker_limπ_iff D hD hcompat x n).2 hx⟩

variable {F} {G : ModuleTower R} [∀ n : ℕ, Module ℚ (G.obj (op n))]
  (E : ∀ n : ℕ, Module.End R (G.obj (op n))) (hE : ∀ n, IsNilpotent (E n))
  (hcompatE : ∀ {n k : ℕ} (h : n ≤ k), Function.Semiconj (G.transitionOfLE h) (E k) (E n))

/-- A morphism intertwining the levelwise endomorphisms intertwines the completed exponentials. -/
theorem limMap_limExp (f : F ⟶ G)
    (hf : ∀ n, Function.Semiconj (f.app (op n)).hom (D n) (E n)) (x : F.lim) :
    limMap f (F.limExp D hD hcompat x) = G.limExp E hE hcompatE (limMap f x) := by
  apply G.lim_ext
  intro n
  have hπ (y : F.lim) : G.limπ n (limMap f y) = (f.app (op n)).hom (F.limπ n y) :=
    LinearMap.congr_fun (limπ_comp_limMap f n) y
  rw [hπ]
  simp only [limπ_apply, coe_limExp_apply]
  rw [← G.limπ_apply, hπ]
  simpa only [limπ_apply] using
    Module.End.map_exp (D n) (hD n) (hE n) (f.app (op n)).hom (hf n) (F.limπ n x)

end TauCeti.ModuleTower
