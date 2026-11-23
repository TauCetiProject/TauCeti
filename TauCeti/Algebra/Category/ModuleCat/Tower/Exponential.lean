/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Topology
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Exponentials of compatible locally nilpotent endomorphisms

A compatible family of locally nilpotent endomorphisms of a tower of rational modules
exponentiates to a linear automorphism of its limit. Each coordinate is the locally finite
exponential at that level. The nilpotence bound may depend on both the vector and the level.
The automorphism preserves and reflects every projection kernel and is continuous for the
inverse limit topology. Intertwining morphisms of towers commute with these automorphisms.
For uniformly nilpotent level maps, the coordinate formulas specialize to `IsNilpotent.exp`.

This compatible-family construction uses `Module.End.locallyNilpotentExp` and
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
  (D : ∀ n : ℕ, Module.End R (F.obj (op n))) (hD : ∀ n x, ∃ k, (D n ^ k) x = 0)
  (hcompat : ∀ {n k : ℕ} (h : n ≤ k), Function.Semiconj (F.transitionOfLE h) (D k) (D n))

/-- The finite exponentials form an automorphism of the tower. -/
def expIso : F ≅ F :=
  NatIso.ofComponents
    (fun n ↦ ((D n.unop).locallyNilpotentExp (hD n.unop)).toModuleIso)
    (by
      intro n k f
      ext x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
        map_hom_eq_transitionOfLE] using
        (Module.End.map_locallyNilpotentExp (D n.unop) _ _
          (F.transitionOfLE (leOfHom f.unop)) (hcompat _) x).symm)

/-- The forward component is the locally finite exponential of the level endomorphism. -/
@[simp]
theorem expIso_hom_app_apply (n : ℕ) (x : F.obj (op n)) :
    ((F.expIso D hD hcompat).hom.app (op n)).hom x = (D n).locallyNilpotentExp (hD n) x := by
  simp only [expIso, NatIso.ofComponents_hom_app, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The inverse component is the inverse locally finite exponential at that level. -/
@[simp]
theorem expIso_inv_app_apply (n : ℕ) (x : F.obj (op n)) :
    ((F.expIso D hD hcompat).inv.app (op n)).hom x =
      ((D n).locallyNilpotentExp (hD n)).symm x := by
  simp only [expIso, NatIso.ofComponents_inv_app, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The exponential on the limit of a tower, defined by its levelwise exponentials. -/
def limExp : F.lim ≃ₗ[R] F.lim :=
  limEquivOfIso (F.expIso D hD hcompat)

/-- A projection computes the locally finite exponential at the corresponding level. -/
@[simp]
theorem coe_limExp_apply (x : F.lim) (n : ℕ) :
    (F.limExp D hD hcompat x : F.Product) n =
      (D n).locallyNilpotentExp (hD n) ((x : F.Product) n) := by
  rw [← F.limπ_apply, ← F.limπ_apply]
  rw [limExp, limEquivOfIso_apply, ← LinearMap.comp_apply, limπ_comp_limMap]
  exact F.expIso_hom_app_apply D hD hcompat n _

/-- An inverse projection computes the inverse locally finite exponential at that level. -/
@[simp]
theorem coe_limExp_symm_apply (x : F.lim) (n : ℕ) :
    ((F.limExp D hD hcompat).symm x : F.Product) n =
      ((D n).locallyNilpotentExp (hD n)).symm ((x : F.Product) n) := by
  rw [← F.limπ_apply, ← F.limπ_apply]
  rw [limExp, limEquivOfIso_symm_apply, ← LinearMap.comp_apply, limπ_comp_limMap]
  exact F.expIso_inv_app_apply D hD hcompat n _

/-- At a nilpotent level the forward component is the finite exponential. -/
theorem expIso_hom_app_apply_of_isNilpotent (n : ℕ) (hn : IsNilpotent (D n))
    (x : F.obj (op n)) :
    ((F.expIso D hD hcompat).hom.app (op n)).hom x = IsNilpotent.exp (D n) x := by
  rw [expIso_hom_app_apply]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (D n) hn) x

/-- At a nilpotent level the inverse component is the finite exponential of the negative map. -/
theorem expIso_inv_app_apply_of_isNilpotent (n : ℕ) (hn : IsNilpotent (D n))
    (x : F.obj (op n)) :
    ((F.expIso D hD hcompat).inv.app (op n)).hom x = IsNilpotent.exp (-D n) x := by
  rw [expIso_inv_app_apply, Module.End.locallyNilpotentExp_symm]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (-D n) hn.neg) x

/-- At a nilpotent level the limit's coordinate is the finite exponential. -/
theorem coe_limExp_apply_of_isNilpotent (x : F.lim) (n : ℕ) (hn : IsNilpotent (D n)) :
    (F.limExp D hD hcompat x : F.Product) n = IsNilpotent.exp (D n) ((x : F.Product) n) := by
  rw [coe_limExp_apply]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (D n) hn) _

/-- At a nilpotent level the inverse coordinate is the exponential of the negative map. -/
theorem coe_limExp_symm_apply_of_isNilpotent (x : F.lim) (n : ℕ) (hn : IsNilpotent (D n)) :
    ((F.limExp D hD hcompat).symm x : F.Product) n =
      IsNilpotent.exp (-D n) ((x : F.Product) n) := by
  rw [coe_limExp_symm_apply, Module.End.locallyNilpotentExp_symm]
  exact LinearMap.congr_fun (Module.End.locallyNilpotentExp_eq_exp (-D n) hn.neg) _

/-- Exponentiation preserves and reflects the filtration by projection kernels. -/
theorem limExp_mem_ker_limπ_iff (x : F.lim) (n : ℕ) :
    F.limExp D hD hcompat x ∈ LinearMap.ker (F.limπ n) ↔
      x ∈ LinearMap.ker (F.limπ n) := by
  simp only [LinearMap.mem_ker, limπ_apply, coe_limExp_apply]
  exact EmbeddingLike.map_eq_zero_iff

/-- The completed exponential is continuous for the inverse limit topology. -/
theorem continuous_limExp : Continuous (F.limExp D hD hcompat) := by
  apply continuous_of_tendsto_nhds_zero (F.limExp D hD hcompat).toLinearMap
  exact (F.hasBasis_nhds_zero.tendsto_iff F.hasBasis_nhds_zero).2 fun n _ ↦
    ⟨n, trivial, fun x hx ↦ (F.limExp_mem_ker_limπ_iff D hD hcompat x n).2 hx⟩

variable {F} {G : ModuleTower R} [∀ n : ℕ, Module ℚ (G.obj (op n))]
  (E : ∀ n : ℕ, Module.End R (G.obj (op n))) (hE : ∀ n x, ∃ k, (E n ^ k) x = 0)
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
    Module.End.map_locallyNilpotentExp (D n) (hD n) (hE n) (f.app (op n)).hom (hf n) (F.limπ n x)

end TauCeti.ModuleTower
