/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Order.Units
public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
public import TauCeti.Topology.PathSpace.Moore.FreeLoop

/-!
# The sign character of a double cover

Let `p : E → X` be a covering map whose fibres are the pairs `{e, σ e}` exchanged by a continuous
map `σ` over `X` without fixed points, such as the orientation double cover of a real vector
bundle with its deck involution. Monodromy commutes with `σ`, so the monodromy of a loop `g` at
`x` either fixes both points of the fibre over `x` or exchanges them, whichever point one starts
from. Recording this as `1` or `-1` is a character of the fundamental group,
`IsCoveringMap.signCharacter : π₁(X, x) →* ℤˣ`. For the orientation double cover of a vector
bundle `V` it is the orientation character: a loop has sign `1` exactly when transport along it
preserves the orientations of the fibre, that is, when `V` pulled back to the circle along the
loop is orientable. A continuous section of the cover makes the character trivial
(`IsCoveringMap.signCharacter_eq_one_of_section`).

The sign local system of the cover is the classical local system with this monodromy: transport
along a loop is multiplication by its sign (`IsCoveringMap.signLocalSystem_map_toArrow`).

On Moore loops the character gives `IsCoveringMap.loopSign`, read off from path lifting: a loop
has sign `1` when its lift starting at a point of the fibre closes up
(`IsCoveringMap.loopSign_eq_one_iff`). A free Moore loop has a sign at its own base point
(`IsCoveringMap.freeLoopSign`), and this sign is constant on the path components of the free loop
space (`IsCoveringMap.freeLoopSign_eq_of_joined`). For a path of free loops, lift the path of
base points, then lift every loop of the family from the lifted base point; by homotopy lifting
the endpoints of these lifts form a continuous lift of the path of base points, so it is either
the first lift or its image under `σ` throughout.

## Main definitions

* `IsCoveringMap.signCharacter`: the sign character `π₁(X, x) →* ℤˣ` of a double cover.
* `IsCoveringMap.loopSign`: the sign of a Moore loop.
* `IsCoveringMap.freeLoopSign`: the sign of a free Moore loop at its base point.

## Main results

* `IsCoveringMap.signCharacter_apply_eq_one_iff`,
  `IsCoveringMap.signCharacter_apply_eq_neg_one_iff`: the sign records whether monodromy fixes
  or exchanges the points of the fibre.
* `IsCoveringMap.signCharacter_eq`: the character does not depend on the point of the fibre.
* `IsCoveringMap.signLocalSystem_map_toArrow`: transport in the sign local system along a loop is
  multiplication by its sign.
* `IsCoveringMap.loopSign_eq_one_iff`: the sign of a Moore loop by path lifting.
* `IsCoveringMap.freeLoopSign_eq_of_joined`: the sign of free loops is constant on path
  components.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (the orientation local system).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1 (the orientation part of the
  local system `η` on the free loop space).
-/

public section

noncomputable section

open CategoryTheory TauCeti

namespace IsCoveringMap

universe u v w

section Character

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (hp : IsCoveringMap p) {σ : C(E, E)} (hσ : p ∘ σ = p) (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

omit [TopologicalSpace X] in
include hfix in
private theorem fiberMap_ne {x : X} (e : p ⁻¹' {x}) : Function.fiberMap σ hσ x e ≠ e := fun h ↦
  hfix e ((Function.fiberMap_apply_coe σ hσ x e).symm.trans (congrArg Subtype.val h))

omit [TopologicalSpace X] in
include hfib in
private theorem eq_or_eq_fiberMap {x : X} (e e' : p ⁻¹' {x}) :
    e' = e ∨ e' = Function.fiberMap σ hσ x e := by
  rcases hfib e e' (e'.2.trans e.2.symm) with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm))

omit [TopologicalSpace X] in
include hfix hfib in
private theorem fiberMap_fiberMap {x : X} (e : p ⁻¹' {x}) :
    Function.fiberMap σ hσ x (Function.fiberMap σ hσ x e) = e :=
  (eq_or_eq_fiberMap hσ hfib e _).resolve_right (fiberMap_ne hσ hfix _)

private theorem monodromyPerm_fiberMap {x : X} (g : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    hp.monodromyPerm x g (Function.fiberMap σ hσ x e) =
      Function.fiberMap σ hσ x (hp.monodromyPerm x g e) :=
  (hp.fiberMap_monodromy hp σ hσ g.asHom e).symm

private theorem neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by decide

open scoped Classical in
/-- **The sign character** of a double cover `p` whose fibres are the pairs `{e, σ e}`: a loop `g`
at `x` has sign `1` when its monodromy fixes the point `e` of the fibre over `x`, and `-1` when it
sends `e` to `σ e`. It does not depend on `e` (`IsCoveringMap.signCharacter_eq`). For the
orientation double cover of a vector bundle this is the orientation character of the bundle. -/
def signCharacter {x : X} (e : p ⁻¹' {x}) : FundamentalGroup X x →* ℤˣ where
  toFun g := if hp.monodromyPerm x g e = e then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Equiv.Perm.mul_apply]
    have hne := fiberMap_ne hσ hfix e
    rcases eq_or_eq_fiberMap hσ hfib e (hp.monodromyPerm x h e) with hh | hh
    · rw [hh]
      split_ifs <;> simp_all
    · rw [hh, monodromyPerm_fiberMap hp hσ]
      rcases eq_or_eq_fiberMap hσ hfib e (hp.monodromyPerm x g e) with hg | hg
      · rw [hg]
        split_ifs <;> simp_all
      · rw [hg, fiberMap_fiberMap hσ hfix hfib]
        split_ifs <;> simp_all

variable {x : X}

/-- A loop has sign `1` exactly when its monodromy fixes the chosen point of the fibre. -/
theorem signCharacter_apply_eq_one_iff (e : p ⁻¹' {x}) (g : FundamentalGroup X x) :
    hp.signCharacter hσ hfix hfib e g = 1 ↔ hp.monodromyPerm x g e = e := by
  simp only [signCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false neg_one_ne_one h

/-- A loop has sign `-1` exactly when its monodromy exchanges the points of the fibre. -/
theorem signCharacter_apply_eq_neg_one_iff (e : p ⁻¹' {x}) (g : FundamentalGroup X x) :
    hp.signCharacter hσ hfix hfib e g = -1 ↔
      hp.monodromyPerm x g e = Function.fiberMap σ hσ x e := by
  rcases Int.units_eq_one_or (hp.signCharacter hσ hfix hfib e g) with h | h
  · have hg := (hp.signCharacter_apply_eq_one_iff hσ hfix hfib e g).1 h
    rw [h, hg]
    exact iff_of_false neg_one_ne_one.symm (fiberMap_ne hσ hfix e).symm
  · refine iff_of_true h ?_
    refine (eq_or_eq_fiberMap hσ hfib e _).resolve_left fun hg ↦ neg_one_ne_one ?_
    rw [← h]
    exact (hp.signCharacter_apply_eq_one_iff hσ hfix hfib e g).2 hg

/-- The monodromy of a loop of sign `1` fixes every point of the fibre. -/
theorem monodromyPerm_apply_of_signCharacter_eq_one {e : p ⁻¹' {x}} {g : FundamentalGroup X x}
    (h : hp.signCharacter hσ hfix hfib e g = 1) (e' : p ⁻¹' {x}) :
    hp.monodromyPerm x g e' = e' := by
  have hg := (hp.signCharacter_apply_eq_one_iff hσ hfix hfib e g).1 h
  rcases eq_or_eq_fiberMap hσ hfib e e' with rfl | rfl
  · exact hg
  · rw [monodromyPerm_fiberMap hp hσ, hg]

/-- The monodromy of a loop of sign `-1` exchanges the two points of every fibre. -/
theorem monodromyPerm_apply_of_signCharacter_eq_neg_one {e : p ⁻¹' {x}}
    {g : FundamentalGroup X x} (h : hp.signCharacter hσ hfix hfib e g = -1) (e' : p ⁻¹' {x}) :
    hp.monodromyPerm x g e' = Function.fiberMap σ hσ x e' := by
  have hg := (hp.signCharacter_apply_eq_neg_one_iff hσ hfix hfib e g).1 h
  rcases eq_or_eq_fiberMap hσ hfib e e' with rfl | rfl
  · exact hg
  · rw [monodromyPerm_fiberMap hp hσ, hg]

/-- The sign character does not depend on the point of the fibre. -/
theorem signCharacter_eq (e e' : p ⁻¹' {x}) :
    hp.signCharacter hσ hfix hfib e = hp.signCharacter hσ hfix hfib e' := by
  ext g : 1
  rcases Int.units_eq_one_or (hp.signCharacter hσ hfix hfib e g) with h | h
  · rw [h, eq_comm, signCharacter_apply_eq_one_iff]
    exact hp.monodromyPerm_apply_of_signCharacter_eq_one hσ hfix hfib h e'
  · rw [h, eq_comm, signCharacter_apply_eq_neg_one_iff]
    exact hp.monodromyPerm_apply_of_signCharacter_eq_neg_one hσ hfix hfib h e'

/-- A continuous section makes the sign character trivial: for the orientation double cover, an
oriented bundle has trivial orientation character. -/
theorem signCharacter_eq_one_of_section {s : X → E} (hs : Continuous s)
    (hps : ∀ x, s x ∈ p ⁻¹' {x}) (e : p ⁻¹' {x}) : hp.signCharacter hσ hfix hfib e = 1 := by
  ext g : 1
  rw [hp.signCharacter_eq hσ hfix hfib e ⟨s x, hps x⟩, MonoidHom.one_apply,
    signCharacter_apply_eq_one_iff]
  exact hp.monodromy_section hs hps g.asHom

/-! ### Moore loops -/

/-- **The sign of a Moore loop** at `x`: the sign character of its class in the fundamental
group. -/
def loopSign (e : p ⁻¹' {x}) : MooreLoopSpace X x →* ℤˣ :=
  (hp.signCharacter hσ hfix hfib e).comp (MooreLoopSpace.fundamentalGroupHom x)

theorem loopSign_apply (e : p ⁻¹' {x}) (γ : MooreLoopSpace X x) :
    hp.loopSign hσ hfix hfib e γ =
      hp.signCharacter hσ hfix hfib e (MooreLoopSpace.fundamentalGroupHom x γ) :=
  (rfl)

/-- The sign of Moore loops does not depend on the point of the fibre. -/
theorem loopSign_eq (e e' : p ⁻¹' {x}) :
    hp.loopSign hσ hfix hfib e = hp.loopSign hσ hfix hfib e' := by
  rw [loopSign, loopSign, hp.signCharacter_eq hσ hfix hfib e e']

/-- **The sign of a Moore loop by path lifting**: it is `1` exactly when the lift of the loop
starting at a point `e` of the fibre returns to `e`. -/
theorem loopSign_eq_one_iff (e : p ⁻¹' {x}) (γ : MooreLoopSpace X x) :
    hp.loopSign hσ hfix hfib e γ = 1 ↔
      hp.liftPath γ.toPath e (γ.toPath.source.trans e.2.symm) 1 = e := by
  rw [loopSign_apply, MooreLoopSpace.fundamentalGroupHom_apply, map_inv, inv_eq_one,
    signCharacter_apply_eq_one_iff, ← Subtype.coe_inj]
  exact Iff.rfl

/-- Moore loops in the same path component have the same sign. -/
theorem loopSign_eq_of_joined (e : p ⁻¹' {x}) {γ δ : MooreLoopSpace X x} (h : Joined γ δ) :
    hp.loopSign hσ hfix hfib e γ = hp.loopSign hσ hfix hfib e δ := by
  rw [loopSign_apply, loopSign_apply, MooreLoopSpace.fundamentalGroupHom_eq_of_joined h]

/-! ### Free Moore loops -/

variable (hsurj : Function.Surjective p)

/-- **The sign of a free Moore loop**: the sign of the based loop at its own base point. It is
`1` exactly when the lift of the loop starting at a point of the fibre over its base point closes
up (`IsCoveringMap.freeLoopSign_eq_one_iff`). -/
def freeLoopSign (γ : MooreFreeLoopSpace X) : ℤˣ :=
  hp.loopSign hσ hfix hfib ⟨Function.surjInv hsurj γ.basepoint, Function.surjInv_eq hsurj _⟩
    γ.toLoop

/-- The sign of a free loop, computed from any point of the fibre over its base point. -/
theorem freeLoopSign_eq_loopSign (γ : MooreFreeLoopSpace X) (e : p ⁻¹' {γ.basepoint}) :
    hp.freeLoopSign hσ hfix hfib hsurj γ = hp.loopSign hσ hfix hfib e γ.toLoop := by
  rw [freeLoopSign, hp.loopSign_eq hσ hfix hfib _ e]

/-- The sign of a free loop is `1` exactly when its lift from a point `e` of the fibre over its
base point closes up. -/
theorem freeLoopSign_eq_one_iff (γ : MooreFreeLoopSpace X) (e : p ⁻¹' {γ.basepoint}) :
    hp.freeLoopSign hσ hfix hfib hsurj γ = 1 ↔
      hp.liftPath γ.toLoop.toPath e (γ.toLoop.toPath.source.trans e.2.symm) 1 = e := by
  rw [freeLoopSign_eq_loopSign hp hσ hfix hfib hsurj γ e, loopSign_eq_one_iff]

/-- **The sign of free loops is constant on path components** of the free loop space. Along a
path of free loops, the lifts of the loops starting over a lift of the path of base points end on
another continuous lift of that path, which is the first lift or its image under `σ`
throughout. -/
theorem freeLoopSign_eq_of_joined {γ δ : MooreFreeLoopSpace X} (h : Joined γ δ) :
    hp.freeLoopSign hσ hfix hfib hsurj γ = hp.freeLoopSign hσ hfix hfib hsurj δ := by
  obtain ⟨Γ⟩ := h
  -- Lift the path of base points.
  let β : C(unitInterval, X) := (MooreFreeLoopSpace.basepointMap X).comp Γ.toContinuousMap
  have hβs (s : unitInterval) : β s = (Γ s).basepoint := MooreFreeLoopSpace.basepointMap_apply _
  obtain ⟨e₀, he₀⟩ := hsurj γ.basepoint
  have hβ : β 0 = p e₀ := by rw [hβs, Γ.source, he₀]
  let f := hp.liftPath β e₀ hβ
  have hf (s : unitInterval) : p (f s) = (Γ s).basepoint :=
    (congr_fun (hp.liftPath_lifts β e₀ hβ) s).trans (hβs s)
  -- Lift the family of loops, starting over the lifted base points.
  let H : C(unitInterval × unitInterval, X) :=
    ⟨fun ts ↦ (Γ ts.2).toMoorePath.toUnitPath ts.1, by
      exact ContinuousEval.continuous_eval.comp
        (((MoorePath.continuous_toUnitPath.comp
          (MooreFreeLoopSpace.continuous_toMoorePath.comp Γ.continuous)).comp
            continuous_snd).prodMk continuous_fst)⟩
  have hH (t s : unitInterval) : H (t, s) = (Γ s).toMoorePath.toUnitPath t := rfl
  have H₀ (s : unitInterval) : H (0, s) = p (f s) := by
    rw [hf, hH]
    exact (MoorePath.toUnitPath_zero _).trans (Γ s).source_toMoorePath
  let G := hp.liftHomotopy H f H₀
  let g : C(unitInterval, E) := G.comp ⟨fun s ↦ (1, s), by fun_prop⟩
  -- The sign of each loop compares the end of its lift with its start.
  have key (s : unitInterval) : hp.freeLoopSign hσ hfix hfib hsurj (Γ s) = 1 ↔ g s = f s := by
    rw [hp.freeLoopSign_eq_one_iff hσ hfix hfib hsurj (Γ s) ⟨f s, hf s⟩]
    have hlift : G.comp ⟨fun t ↦ (t, s), by fun_prop⟩ =
        hp.liftPath (Γ s).toLoop.toPath (f s)
          ((Γ s).toLoop.toPath.source.trans (hf s).symm) := by
      refine (hp.eq_liftPath_iff' _).2 ⟨funext fun t ↦ ?_, hp.liftHomotopy_zero H f H₀ s⟩
      refine (congr_fun (hp.liftHomotopy_lifts H f H₀) (t, s)).trans ?_
      rw [hH, MoorePath.toUnitPath_apply]
      simp [MooreLoopSpace.toPath_apply]
    rw [← hlift]
    exact Iff.rfl
  -- The ends of the lifts form another lift of the path of base points.
  have hg : p ∘ g = p ∘ f := funext fun s ↦ by
    refine (congr_fun (hp.liftHomotopy_lifts H f H₀) (1, s)).trans ?_
    rw [Function.comp_apply, hf, hH]
    exact (MoorePath.toUnitPath_one _).trans
      ((Γ s).target_eq_source.trans (Γ s).source_toMoorePath)
  have h01 : hp.freeLoopSign hσ hfix hfib hsurj (Γ 0) =
      hp.freeLoopSign hσ hfix hfib hsurj (Γ 1) := by
    rcases hfib (f 0) (g 0) (congr_fun hg 0) with h0 | h0
    · have hgf := hp.eq_of_comp_eq g.continuous f.continuous hg 0 h0
      rw [(key 0).2 (congr_fun hgf 0), (key 1).2 (congr_fun hgf 1)]
    · have hgf := hp.eq_of_comp_eq g.continuous (σ.comp f).continuous
        (hg.trans (by rw [ContinuousMap.coe_comp, ← Function.comp_assoc, hσ])) 0 h0
      have hne (s : unitInterval) : hp.freeLoopSign hσ hfix hfib hsurj (Γ s) = -1 :=
        (Int.units_eq_one_or _).resolve_left fun hs ↦
          hfix (f s) ((congr_fun hgf s).symm.trans ((key s).1 hs))
      rw [hne, hne]
  simpa using h01

end Character

/-! ### The sign local system -/

section LocalSystem

variable {E : Type w} [TopologicalSpace E] {X : TopCat.{v}} {p : E → X} (hp : IsCoveringMap p)
  {σ : C(E, E)} (hσ : p ∘ σ = p) (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e) (R : Type u) [Ring R]

/-- **The monodromy of the sign local system** is the sign character: transport along a loop `g`
at `x` multiplies by the sign of `g`. -/
theorem signLocalSystem_map_toArrow {x : X} (e : p ⁻¹' {x}) (g : FundamentalGroup X x)
    (f : (hp.signLocalSystem R σ hσ).obj (FundamentalGroupoid.mk x)) :
    ((hp.signLocalSystem R σ hσ).map g.toArrow).hom f =
      ((hp.signCharacter hσ hfix hfib e g : ℤ)) • f := by
  apply (hp.signLocalSystemObjEquiv σ hσ _).injective
  apply Subtype.ext
  funext e'
  have hmap := hp.signLocalSystemObjEquiv_map_apply_monodromy σ hσ g.toArrow f e'
  rw [map_zsmul]
  rcases Int.units_eq_one_or (hp.signCharacter hσ hfix hfib e g) with h | h
  · have hfix' := hp.monodromyPerm_apply_of_signCharacter_eq_one hσ hfix hfib h e'
    rw [h, Units.val_one, one_smul]
    exact (congrArg _ hfix'.symm).trans hmap
  · have hneg := hp.monodromyPerm_apply_of_signCharacter_eq_neg_one hσ hfix hfib h e'
    rw [h, Units.val_neg, Units.val_one, neg_one_zsmul]
    have hsign := TauCeti.mem_signFiber_iff.1
      (hp.signLocalSystemObjEquiv σ hσ _ (((hp.signLocalSystem R σ hσ).map g.toArrow).hom f)).2 e'
    have h1 : (hp.signLocalSystemObjEquiv σ hσ _
        (((hp.signLocalSystem R σ hσ).map g.toArrow).hom f) : p ⁻¹' {x} → R)
          (Function.fiberMap σ hσ x e') =
        (hp.signLocalSystemObjEquiv σ hσ _ f : p ⁻¹' {x} → R) e' := by
      rw [← hmap]
      exact congrArg _ hneg.symm
    rw [Submodule.coe_neg, Pi.neg_apply, ← h1, hsign, neg_neg]

end LocalSystem

end IsCoveringMap
