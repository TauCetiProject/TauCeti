/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ApplyProdMk
public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic

/-!
# Relative lifting for Hurewicz fibrations

Let `A ⊆ Y` be the zero set of a continuous `u : Y → I`, and suppose that `A` is a strong
deformation retract of `Y`: there is a retraction `r : Y → A` and a homotopy from the identity of
`Y` to `r`, relative to `A`. Then a Hurewicz fibration `p : E → B` has the right lifting property
with respect to the inclusion `A → Y`: every commutative square from `A → Y` to `p` has a
diagonal filler, which restricts to the given map on `A` exactly
(`TauCeti.IsHurewiczFibration.zeroSetSDR_liftingInclusion`). No regular lifting function is
assumed, and no separation, CW or compact-generation hypothesis is imposed on `Y`.

The filler is obtained by a single homotopy lift. Writing `h` for the deformation, the homotopy
`(t, y) ↦ h (1 - min 1 (t / u y), y)` runs from the retraction to the point `y` by the time `u y`,
and is constant at the points of `A`; its continuity at `A` is the compactness argument
`ContinuousMap.continuous_apply_prodMk_of_fixed`. Lifting its image in `B` starting from the
given map composed with the retraction, and evaluating the lift at time `u y`, gives the filler.

Applied to the strong deformation retraction of the cylinder `I × X` onto `{0} × X ∪ I × A` of an
NDR pair `(X, A)` (`TauCeti.NDRPair.cylinderHomotopyRel`), this gives the relative homotopy
lifting property: a homotopy in `B` lifts, starting at a prescribed lift and agreeing on `A` with a
prescribed lift over `A` (`TauCeti.IsHurewiczFibration.exists_lift_of_ndrPair`). For instance,
when the basepoint of the parameter space forms an NDR pair with it, the lift can follow an
arbitrary prescribed track of the basepoint.

## Main results

* `TauCeti.IsHurewiczFibration.zeroSetSDR_liftingInclusion`: a Hurewicz fibration has the right
  lifting property with respect to the inclusion of the zero set of a control function which is a
  strong deformation retract.
* `TauCeti.IsHurewiczFibration.exists_lift_of_ndrPair`: the relative homotopy lifting property
  with respect to an NDR pair.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapters 6 and 7.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsHurewiczFibration

/-- **Fixed-data relative lifting.** Let `A ⊆ Y` be the zero set of a continuous `u : Y → I` and
a strong deformation retract of `Y`, with retraction `r`. Then a Hurewicz fibration `p` lifts every
commutative square from the inclusion `A → Y` to `p`: given `f : A → E` and `g : Y → B` with
`p ∘ f = g` on `A`, there is a lift `ℓ : Y → E` of `g` restricting to `f` on `A`. -/
theorem zeroSetSDR_liftingInclusion (hp : IsHurewiczFibration.{w} p) {Y : Type w}
    [TopologicalSpace Y] {A : Set Y} (u : C(Y, I)) (hu : ∀ y, u y = 0 ↔ y ∈ A) (r : C(Y, A))
    (hr : (ContinuousMap.id Y).HomotopicRel ((ContinuousMap.subtypeVal A).comp r) A)
    (f : C(A, E)) (g : C(Y, B)) (hfg : ∀ a, p (f a) = g a) :
    ∃ ℓ : C(Y, E), p ∘ ℓ = g ∧ ∀ a : A, ℓ a = f a := by
  have hr' (a : A) : r a = a := Subtype.ext (hr.fst_eq_snd a.2).symm
  obtain ⟨F⟩ := hr
  -- the homotopy `Φ (t, y) = F (1 - min 1 (t / u y), y)` from `r` to the point `y` at time `u y`
  let φ : I × Y → I := fun z ↦ σ (projIcc 0 1 zero_le_one ((z.1 : ℝ) / u z.2))
  have hφ (z : I × Y) (hz : z.2 ∉ A) : ContinuousAt φ z :=
    continuous_symm.continuousAt.comp
      (continuousAt_projIcc_div_of_notMem u hu continuous_fst continuous_snd hz)
  let Φ : C(I × Y, Y) :=
    ⟨fun z ↦ F.toContinuousMap (φ z, z.2),
      F.toContinuousMap.continuous_apply_prodMk_of_fixed (fun t _ hy ↦ F.eq_fst t hy)
        continuous_snd hφ⟩
  have hΦ₀ (y : Y) : Φ (0, y) = r y := by
    simp only [Φ, φ, ContinuousMap.coe_mk]
    simp
  have hΦu (y : Y) : Φ (u y, y) = y := by
    by_cases hy : y ∈ A
    · exact F.eq_fst _ hy
    · simp only [Φ, φ, ContinuousMap.coe_mk]
      simp [div_self ((coe_ne_zero_iff_notMem hu y).2 hy)]
  obtain ⟨L, hL, hL₀⟩ := hp.hasHomotopyLiftingProperty Y (f.comp r) (g.comp Φ) fun y ↦ by
    simp [hΦ₀, hfg]
  refine ⟨⟨fun y ↦ L (u y, y), by fun_prop⟩, funext fun y ↦ ?_, fun a ↦ ?_⟩
  · simpa [hΦu] using congrFun hL (u y, y)
  · have hua : u a = 0 := (hu a).2 a.2
    simp [hua, hL₀, hr']

/-- **Relative homotopy lifting for NDR pairs.** Let `(X, A)` be an NDR pair and `p` a Hurewicz
fibration. A homotopy `H : I × X → B` lifts to a homotopy `G : I × X → E` with prescribed initial
lift `f` and prescribed lift `g` over `I × A`, provided `f` and `g` agree at time `0`. -/
theorem exists_lift_of_ndrPair (hp : IsHurewiczFibration.{w} p) {X : Type w}
    [TopologicalSpace X] {A : Set X} (N : NDRPair A) (f : C(X, E)) (H : C(I × X, B))
    (hH : ∀ x, H (0, x) = p (f x)) (g : C(I × A, E)) (hg : ∀ t (a : A), p (g (t, a)) = H (t, a))
    (hgf : ∀ a : A, g (0, a) = f a) :
    ∃ G : C(I × X, E), p ∘ G = H ∧ (∀ x, G (0, x) = f x) ∧ ∀ t (a : A), G (t, a) = g (t, a) := by
  -- glue `f` and `g` to a map on `{0} × X ∪ I × A`, extended over the cylinder by the retraction
  obtain ⟨k, hk₀, hkA⟩ :=
    N.hasHomotopyExtensionProperty.exists_extension_of_isClosed N.isClosed f g hgf
  obtain ⟨G, hG, hGJ⟩ := hp.zeroSetSDR_liftingInclusion N.cylinderControl
    N.cylinderControl_eq_zero_iff N.cylinderRetraction ⟨N.cylinderHomotopyRel⟩
    (k.restrict (cylinderExtensionDomain A)) H fun ⟨⟨t, x⟩, hz⟩ ↦ by
      rcases mem_cylinderExtensionDomain_iff.1 hz with ht | hx
      · obtain rfl : t = 0 := ht
        simp [hk₀, hH]
      · simpa [hkA t ⟨x, hx⟩] using hg t ⟨x, hx⟩
  refine ⟨G, hG, fun x ↦ ?_, fun t a ↦ ?_⟩
  · simpa [hk₀] using hGJ ⟨(0, x), zero_mem_cylinderExtensionDomain x⟩
  · simpa [hkA] using hGJ ⟨(t, a), mem_cylinderExtensionDomain_of_mem a.2⟩

end IsHurewiczFibration

end TauCeti
