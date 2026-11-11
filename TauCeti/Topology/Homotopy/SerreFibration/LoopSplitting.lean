/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopProduct
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# Splitting the loop space of the base of a Serre fibration

Let `p : E → B` be a Serre fibration, `e` a point of its fibre over `b`, and `φ` a homeomorphism
from that fibre to a space `F`, sending `e` to `f₀`. Given a based map `j : F → Ω B b`, the
**loop product** (`TauCeti.TopCat.loopProduct`) is the map

`F × Ω E e → Ω B b`, `(z, γ) ↦ j z ⋀ p ∘ γ`,

the concatenation of the loop `j z` with the image of `γ`. This file shows that it induces a
bijection on the homotopy group `π_n`, `n ≥ 1`, as soon as

* the fibre inclusion induces the trivial map `π_(n+1)(F) → π_(n+1)(E)`, and
* `j` splits the boundary map in degree `n`: the composite
  `π_n(F) → π_n(Ω B b) ≅ π_(n+1)(B) → π_n(F)` of the map induced by `j`, the loop-space shift
  `HomotopyGroup.loopSpaceOptionMulEquiv` and the boundary map of the fibration is bijective

(`TauCeti.TopCat.bijective_homotopyGroupMap_loopProduct`). This is the homotopy-group form of the
classical splitting `Ω B ≃ F × Ω E` of the loop space of the base of a fibration whose fibre
inclusion is null-homotopic.

The argument is the exact homotopy sequence of `p`
(`TauCeti.Topology.Homotopy.SerreFibration.Exact`), read through the loop-space shift. Under the
shift the map induced by `p ∘ -` on `π_n(Ω E e)` is `p_* : π_(n+1)(E) → π_(n+1)(B)`. It is
injective because the fibre inclusion is trivial on `π_(n+1)`
(`TauCeti.TopCat.injective_homotopyGroupMap_loopSpaceMap`), the boundary map vanishes on its
image, and its image is the kernel of the boundary map
(`TauCeti.TopCat.exists_homotopyGroupMap_loopSpaceMap_eq_iff`). Since the loop product induces
`(a, c) ↦ j_* a * (p ∘ -)_* c` (`HomotopyGroup.map_hmul_comp_prodMap`), the splitting gives the
bijection.

## Main declarations

* `TauCeti.TopCat.loopSpaceMap`: the map `Ω E e → Ω B b`, `γ ↦ p ∘ γ`.
* `TauCeti.TopCat.loopProduct`: the loop product `(z, γ) ↦ j z ⋀ p ∘ γ`.
* `TauCeti.TopCat.bijective_homotopyGroupMap_loopProduct`: the loop product induces a bijection on
  `π_n`, `n ≥ 1`, when the fibre inclusion is trivial on `π_(n+1)` and `j` splits the boundary
  map on `π_n`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.41 (the exact
  homotopy sequence of a fibration) and Section 4.2 (the loop space of the base of a fibration).
-/

public section

noncomputable section

open CategoryTheory Set
open scoped Topology.Homotopy HSpaces

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {F : Type*} [TopologicalSpace F] {f₀ : F}

variable (p) in
/-- The map `Ω E e → Ω B b`, `γ ↦ p ∘ γ`, induced on loop spaces by `p`, for `e` in the fibre over
`b`. -/
def loopSpaceMap (e : p.fiber b) : C(Ω E e.1, Ω B b) where
  toFun γ := (γ.map p.hom.continuous).cast (mem_singleton_iff.1 e.2).symm
    (mem_singleton_iff.1 e.2).symm
  continuous_toFun := continuous_induced_rng.2 <|
    (ContinuousMap.continuous_postcomp p.hom).comp continuous_induced_dom

@[simp]
theorem loopSpaceMap_apply (e : p.fiber b) (γ : Ω E e.1) (t : unitInterval) :
    loopSpaceMap p e γ t = p (γ t) :=
  (rfl)

@[simp]
theorem loopSpaceMap_refl (e : p.fiber b) : loopSpaceMap p e (Path.refl e.1) = Path.refl b :=
  Path.ext (funext fun _ ↦ mem_singleton_iff.1 e.2)

variable (p) in
/-- The **loop product** of a map `j : F → Ω B b`: the map `F × Ω E e → Ω B b` concatenating the
loop `j z` with the image `p ∘ γ` of a loop `γ` of `E` at `e`. -/
def loopProduct (e : p.fiber b) (j : C(F, Ω B b)) : C(F × Ω E e.1, Ω B b) :=
  HSpace.hmul.comp (j.prodMap (loopSpaceMap p e))

@[simp]
theorem loopProduct_apply (e : p.fiber b) (j : C(F, Ω B b)) (z : F) (γ : Ω E e.1) :
    loopProduct p e j (z, γ) = (j z).trans (loopSpaceMap p e γ) :=
  (rfl)

/-- The loop product of a based map `j` is based. -/
theorem loopProduct_apply_refl (e : p.fiber b) {j : C(F, Ω B b)} (hj : j f₀ = Path.refl b) :
    loopProduct p e j (f₀, Path.refl e.1) = Path.refl b := by
  rw [loopProduct_apply, hj, loopSpaceMap_refl, Path.refl_trans_refl]

variable {e : p.fiber b} {N : Type*} [DecidableEq N] [Nonempty N]

/-- Under the loop-space shift, the map induced by `p ∘ -` on `π_N(Ω E e)` is the map induced by
`p` on `π_(Option N)(E)`. -/
private theorem loopSpaceOptionMulEquiv_homotopyGroupMap_loopSpaceMap
    (c : HomotopyGroup N (Ω E e.1) (Path.refl e.1)) :
    HomotopyGroup.loopSpaceOptionMulEquiv
        (HomotopyGroup.map (loopSpaceMap p e) (loopSpaceMap_refl e) c) =
      HomotopyGroup.map p.hom (mem_singleton_iff.1 e.2)
        (HomotopyGroup.loopSpaceOptionMulEquiv c) :=
  p.hom.loopSpaceOptionMulEquiv_map (mem_singleton_iff.1 e.2) (loopSpaceMap p e)
    (loopSpaceMap_apply e) c

/-- **The loop map of a Serre fibration is injective on `π_n(Ω E)`** when the fibre inclusion
induces the trivial map on `π_(n+1)`. Indeed, under the loop-space shift the loop map is
`p_* : π_(n+1)(E) → π_(n+1)(B)`, whose kernel is the image of the fibre. -/
theorem injective_homotopyGroupMap_loopSpaceMap [Finite N] (hp : serreFibrations p)
    {φ : p.fiber b ≃ₜ F} (hφ : φ e = f₀) {i : C(F, E)} (hi : ∀ y, i y = (φ.symm y).1)
    (hi₀ : i f₀ = e.1)
    (hiN : ∀ c : HomotopyGroup (Option N) F f₀, HomotopyGroup.map i hi₀ c = 1) :
    Function.Injective (HomotopyGroup.map (N := N) (loopSpaceMap p e) (loopSpaceMap_refl e)) := by
  refine (injective_iff_map_eq_one
    (HomotopyGroup.mapHom (N := N) (loopSpaceMap p e) (loopSpaceMap_refl e))).2 fun c hc ↦ ?_
  rw [HomotopyGroup.mapHom_apply] at hc
  -- Shift to `π_(Option N)(E)`, where `p_* d = 1` puts `d` in the image of the fibre.
  apply HomotopyGroup.loopSpaceOptionMulEquiv.injective
  have hd := congrArg HomotopyGroup.loopSpaceOptionMulEquiv hc
  rw [loopSpaceOptionMulEquiv_homotopyGroupMap_loopSpaceMap, map_one,
    _root_.HomotopyGroup.one_def] at hd
  obtain ⟨c', hc'⟩ := (mem_range_homotopyGroupMap_of_homeomorph_iff hp hφ hi hi₀).2 hd
  rw [← hc', hiN, map_one]

/-- **The image of the loop map of a Serre fibration** on `π_n(Ω E)` consists of the classes whose
shift to `π_(n+1)(B)` has trivial boundary. -/
theorem exists_homotopyGroupMap_loopSpaceMap_eq_iff [Finite N] (hp : serreFibrations p)
    {φ : p.fiber b ≃ₜ F} (hφ : φ e = f₀) (g : HomotopyGroup N (Ω B b) (Path.refl b)) :
    (∃ c, HomotopyGroup.map (loopSpaceMap p e) (loopSpaceMap_refl e) c = g) ↔
      fibrationBoundaryOfHomeomorph N hp φ hφ (HomotopyGroup.loopSpaceOptionMulEquiv g) = 1 := by
  rw [_root_.HomotopyGroup.one_def,
    ← mem_range_homotopyGroupMap_iff_fibrationBoundaryOfHomeomorph_eq hp hφ]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (loopSpaceOptionMulEquiv_homotopyGroupMap_loopSpaceMap c).symm⟩
  · rintro ⟨d, hd⟩
    refine ⟨HomotopyGroup.loopSpaceOptionMulEquiv.symm d,
      HomotopyGroup.loopSpaceOptionMulEquiv.injective ?_⟩
    rw [loopSpaceOptionMulEquiv_homotopyGroupMap_loopSpaceMap, MulEquiv.apply_symm_apply, hd]

/-- **The loop product splits `π_n(Ω B)`.** Let `p` be a Serre fibration, `φ` a homeomorphism
from its fibre over `b` to `F` sending `e` to `f₀`, and `i : F → E` the corresponding inclusion.
Let `j : F → Ω B b` be based. Suppose that `i` induces the trivial map on `π_(n+1)` and that the
composite `π_n(F) → π_n(Ω B b) ≅ π_(n+1)(B) → π_n(F)` of `j_*`, the loop-space shift and the
boundary map is bijective. Then the loop product `(z, γ) ↦ j z ⋀ p ∘ γ` induces a bijection
`π_n(F × Ω E e) → π_n(Ω B b)`; here `n ≥ 1` is the cardinality of `N`. -/
theorem bijective_homotopyGroupMap_loopProduct [Finite N] (hp : serreFibrations p)
    {φ : p.fiber b ≃ₜ F} (hφ : φ e = f₀) {i : C(F, E)} (hi : ∀ y, i y = (φ.symm y).1)
    (hi₀ : i f₀ = e.1)
    {j : C(F, Ω B b)} (hj : j f₀ = Path.refl b)
    (hiN : ∀ c : HomotopyGroup (Option N) F f₀, HomotopyGroup.map i hi₀ c = 1)
    (hjN : Function.Bijective fun a : HomotopyGroup N F f₀ ↦
      fibrationBoundaryOfHomeomorph N hp φ hφ
        (HomotopyGroup.loopSpaceOptionMulEquiv (HomotopyGroup.map j hj a))) :
    Function.Bijective
      (HomotopyGroup.map (N := N) (loopProduct p e j) (loopProduct_apply_refl e hj)) := by
  -- `δ` is the boundary map read on `π_n(Ω B b)`, `J` and `P` the maps induced by `j` and by
  -- `p ∘ -`.
  set δ : HomotopyGroup N (Ω B b) (Path.refl b) →* HomotopyGroup N F f₀ :=
    (fibrationBoundaryOfHomeomorphHom N hp φ hφ).comp
      HomotopyGroup.loopSpaceOptionMulEquiv.toMonoidHom with hδ
  set J := HomotopyGroup.mapHom (N := N) j hj
  set P := HomotopyGroup.mapHom (N := N) (loopSpaceMap p e) (loopSpaceMap_refl e)
  have hδ_apply (g) :
      δ g = fibrationBoundaryOfHomeomorph N hp φ hφ (HomotopyGroup.loopSpaceOptionMulEquiv g) := by
    rw [hδ, MonoidHom.comp_apply, coe_fibrationBoundaryOfHomeomorphHom, MulEquiv.coe_toMonoidHom]
  have hδJ : Function.Bijective (δ ∘ J) := by
    convert hjN using 1
    exact funext fun a ↦ hδ_apply _
  have hP : Function.Injective P := injective_homotopyGroupMap_loopSpaceMap hp hφ hi hi₀ hiN
  have hker (g) : (∃ c, P c = g) ↔ δ g = 1 := by
    rw [hδ_apply]
    exact exists_homotopyGroupMap_loopSpaceMap_eq_iff hp hφ g
  have hδP (c) : δ (P c) = 1 := (hker _).1 ⟨c, rfl⟩
  -- On a product class, the loop product induces `(a, c) ↦ J a * P c`.
  have hmap (a : HomotopyGroup N F f₀) (c : HomotopyGroup N (Ω E e.1) (Path.refl e.1)) :
      HomotopyGroup.map (loopProduct p e j) (loopProduct_apply_refl e hj)
        (HomotopyGroup.prod a c) = J a * P c :=
    HomotopyGroup.map_hmul_comp_prodMap j (loopSpaceMap p e) hj (loopSpaceMap_refl e) a c
  refine (Function.Bijective.of_comp_iff _
    (HomotopyGroup.prodEquiv f₀ (Path.refl e.1)).symm.bijective).1 ⟨fun ⟨a, c⟩ ⟨a', c'⟩ h ↦ ?_,
      fun g ↦ ?_⟩
  · simp only [Function.comp_apply, HomotopyGroup.prodEquiv_symm_apply, hmap] at h
    -- Applying `δ`, which kills the image of `P`, recovers `a`; then `P` is injective.
    have hδh := congrArg δ h
    rw [map_mul, map_mul, hδP, hδP, mul_one, mul_one] at hδh
    obtain rfl : a = a' := hδJ.1 hδh
    rw [hP (mul_left_cancel h)]
  · -- Choose `a` with `δ (J a) = δ g`; then `(J a)⁻¹ * g` has trivial boundary, so it is `P c`.
    obtain ⟨a, ha⟩ := hδJ.2 (δ g)
    obtain ⟨c, hc⟩ := (hker ((J a)⁻¹ * g)).2 (by
      rw [map_mul, map_inv, ← Function.comp_apply (f := δ), ha, inv_mul_cancel])
    refine ⟨(a, c), ?_⟩
    rw [Function.comp_apply, HomotopyGroup.prodEquiv_symm_apply, hmap, hc, mul_inv_cancel_left]

end TauCeti.TopCat
