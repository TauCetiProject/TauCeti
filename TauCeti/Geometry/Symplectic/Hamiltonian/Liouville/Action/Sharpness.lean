/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Topology.Order.Interval

/-!
# The hypotheses of the action–angle theorem cannot be dropped

The Liouville–Arnold theorem in action–angle form
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`) produces, around the connected
component `L` of a level `F⁻¹(F x)` of commuting integrals `F : M → ℝ^ι`, an open set `U ⊇ L`, an
open set `D` of actions, a map `Φ` into the cotangent bundle `T*Tⁿ` of the torus
`Tⁿ = ι → AddCircle p` and a function `h`, such that `Φ` maps `U` onto the covectors whose actions
`ξ(eᵢ)` lie in `D` and `F = h ∘ (actions of Φ)` on `U`. It assumes that `L` is compact and made of
regular points of `F`. This file shows that neither hypothesis can be removed.

The two clauses just quoted already force every level of `F` meeting `U` to contain a whole torus.
For `y ∈ U` with actions `a`, every covector with actions `a` over any point `θ` of the torus lies
in `Φ '' U`, and its preimages lie in the level of `y`, since `F` only depends on the actions. So
the torus `ι → AddCircle p` maps injectively into `U ∩ F⁻¹(F y)`
(`TauCeti.exists_injective_mem_preimage_of_image_eq`), and when `Φ` is moreover injective on the
open set `U` and a local diffeomorphism there, the angles `θ ∈ ℝ^ι ↦ Φ⁻¹(∑ⱼ aⱼ dθⱼ at [θ])` give a
continuous map into that level (`TauCeti.exists_continuous_mem_eq_actionAngleCover_of_image_eq`).

* **Regularity.** For the harmonic oscillator `H(q, p) = p² / (2m) + m ν² q² / 2` with `m ≠ 0` and
  `ν ≠ 0`, the level through the equilibrium `0` is the single point `0`
  (`TauCeti.preimage_oscillatorHamiltonian_zero`), which is compact but critical
  (`TauCeti.not_isRegularPoint_oscillatorHamiltonian_zero`). A level that is a single point
  cannot contain a circle, so the conclusion fails there
  (`TauCeti.not_exists_actionAngle_oscillatorHamiltonian_zero`).
* **Compactness.** For the momentum `f(q, p) = p` on `ℝ²`, every point is regular
  (`TauCeti.isRegularPoint_momentum`), and the level through `x` is the whole line `p = x.2`
  (`TauCeti.connectedComponentIn_preimage_momentum`), which is not compact
  (`TauCeti.not_isCompact_connectedComponentIn_preimage_momentum`). The conclusion fails at every
  point (`TauCeti.not_exists_actionAngle_momentum`): it would embed a circle continuously in a
  line, which is impossible (`ContinuousOn.apply_ne_apply_of_injOn_Ico`).

In both examples the other hypotheses hold: the integrals are smooth, a single function commutes
with itself (`TauCeti.SmoothTwoForm.poissonBracket_self`) and the plane has dimension `2 · 1`. The
statements below refute only the clauses of the conclusion that the arguments use, for any
two-form, so they also refute the full conclusion of `exists_actionAngle`.

## Main results

* `TauCeti.exists_mem_eq_actionAngleCover_of_image_eq`,
  `TauCeti.exists_injective_mem_preimage_of_image_eq`,
  `TauCeti.not_subsingleton_inter_preimage_of_image_eq`: an action–angle chart puts a whole torus
  in each level it meets.
* `TauCeti.exists_continuous_mem_eq_actionAngleCover_of_image_eq`: the same torus, parametrized
  continuously by its angles.
* `TauCeti.not_exists_actionAngle_oscillatorHamiltonian_zero`: no action–angle chart at the
  critical equilibrium of the oscillator.
* `TauCeti.not_exists_actionAngle_momentum`: no action–angle chart around the noncompact levels of
  `f(q, p) = p`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

/-! ### An action–angle chart puts a torus in each level -/

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} [Fact (0 < p)] {X β : Type*}
  {U : Set X} {D : Set (ι → ℝ)}
  {Φ : X → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
  {h : (ι → ℝ) → β} {F : X → β} {y : X}

/-- **Every covector with the actions of a point of `U` comes from the level of that point.** If
`Φ` maps `U` onto the covectors whose actions lie in `D`, and `F` is a function `h` of the actions
on `U`, then for `y ∈ U` with actions `a` and any angles `θ`, the covector `∑ⱼ aⱼ dθⱼ` at `[θ]` is
`Φ y'` for a point `y' ∈ U` of the level `F⁻¹(F y)`. -/
theorem exists_mem_eq_actionAngleCover_of_image_eq
    (hΦ : Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D})
    (hF : ∀ y ∈ U, F y = h (fun i ↦ (Φ y).snd (Pi.single i 1))) (hy : y ∈ U) (θ : ι → ℝ) :
    ∃ y' ∈ U, F y' = F y ∧
      Φ y' = CotangentBundle.actionAngleCover p (θ, fun i ↦ (Φ y).snd (Pi.single i 1)) := by
  set a : ι → ℝ := fun i ↦ (Φ y).snd (Pi.single i 1)
  have hκ : (fun i ↦ (CotangentBundle.actionAngleCover p (θ, a)).snd (Pi.single i 1)) = a :=
    funext fun i ↦ (CotangentBundle.torusActions_apply p _ i).symm.trans
      (congrFun (CotangentBundle.torusActions_actionAngleCover p (θ, a)) i)
  have ha : a ∈ D := by
    have h := mem_image_of_mem Φ hy
    rwa [hΦ] at h
  have hmem : CotangentBundle.actionAngleCover p (θ, a) ∈ Φ '' U := by
    rw [hΦ, mem_ofPred_eq, hκ]
    exact ha
  obtain ⟨y', hy', hΦy'⟩ := hmem
  refine ⟨y', hy', ?_, hΦy'⟩
  rw [hF y' hy', hF y hy, hΦy', hκ]

/-- **An action–angle chart puts a whole torus in each level it meets.** If `Φ` maps `U` onto the
covectors whose actions lie in `D`, and `F` is a function of the actions on `U`, then for `y ∈ U`
the torus `ι → AddCircle p` maps injectively into `U ∩ F⁻¹(F y)`, by a map `g` with `Φ (g θ)` a
covector over `θ`. -/
theorem exists_injective_mem_preimage_of_image_eq
    (hΦ : Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D})
    (hF : ∀ y ∈ U, F y = h (fun i ↦ (Φ y).snd (Pi.single i 1))) (hy : y ∈ U) :
    ∃ g : (ι → AddCircle p) → X, Injective g ∧
      ∀ θ, g θ ∈ U ∧ F (g θ) = F y ∧ (Φ (g θ)).proj = θ := by
  -- Lift each point of the torus to angles, and take the point of the level over it.
  choose t ht using fun θ : ι → AddCircle p ↦ QuotientAddGroup.mk_surjective.comp_left θ
  choose g hgU hgF hgΦ using fun θ ↦ exists_mem_eq_actionAngleCover_of_image_eq hΦ hF hy (t θ)
  have hproj (θ : ι → AddCircle p) : (Φ (g θ)).proj = θ := by
    rw [hgΦ, CotangentBundle.proj_actionAngleCover]
    exact ht θ
  refine ⟨g, fun θ θ' hθ ↦ ?_, fun θ ↦ ⟨hgU θ, hgF θ, hproj θ⟩⟩
  rw [← hproj θ, ← hproj θ', hθ]

/-- **A level that meets an action–angle chart is not a single point** when the torus has positive
dimension: it contains the injective image of the torus `ι → AddCircle p`. -/
theorem not_subsingleton_inter_preimage_of_image_eq [Nonempty ι]
    (hΦ : Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D})
    (hF : ∀ y ∈ U, F y = h (fun i ↦ (Φ y).snd (Pi.single i 1))) (hy : y ∈ U) :
    ¬(U ∩ F ⁻¹' {F y}).Subsingleton := by
  intro hsub
  obtain ⟨g, hg, hgU⟩ := exists_injective_mem_preimage_of_image_eq hΦ hF hy
  have hmem (θ : ι → AddCircle p) : g θ ∈ U ∩ F ⁻¹' {F y} := ⟨(hgU θ).1, (hgU θ).2.1⟩
  obtain ⟨θ, θ', hθθ'⟩ := exists_pair_ne (ι → AddCircle p)
  exact hθθ' (hg (hsub (hmem θ) (hmem θ')))

end Torus

section Continuous

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} [Fact (0 < p)] {β : Type*}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {U : Set M} {D : Set (ι → ℝ)}
  {Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
  {h : (ι → ℝ) → β} {F : M → β} {y : M}

/-- **An action–angle chart puts a continuously parametrized torus in each level it meets.** Let
`Φ` be injective on the open set `U` and a local diffeomorphism at each of its points, map `U` onto
the covectors whose actions lie in `D`, and turn `F` into a function of the actions on `U`. Then
for `y ∈ U` with actions `a` there is a continuous map `G` of the angles `θ ∈ ℝ^ι` into
`U ∩ F⁻¹(F y)` with `Φ (G θ)` the covector `∑ⱼ aⱼ dθⱼ` at `[θ]`. -/
theorem exists_continuous_mem_eq_actionAngleCover_of_image_eq (hU : IsOpen U) (hinj : InjOn Φ U)
    (hΦ : Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D})
    (hloc : ∀ y ∈ U, IsLocalDiffeomorphAt I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) n Φ y)
    (hF : ∀ y ∈ U, F y = h (fun i ↦ (Φ y).snd (Pi.single i 1))) (hy : y ∈ U) :
    ∃ G : (ι → ℝ) → M, Continuous G ∧ ∀ θ, G θ ∈ U ∧ F (G θ) = F y ∧
      Φ (G θ) = CotangentBundle.actionAngleCover p (θ, fun i ↦ (Φ y).snd (Pi.single i 1)) := by
  set κ : (ι → ℝ) → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
    fun θ ↦ CotangentBundle.actionAngleCover p (θ, fun i ↦ (Φ y).snd (Pi.single i 1))
  have hκ : Continuous κ :=
    (CotangentBundle.contMDiff_actionAngleCover (ι := ι) p).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hmem (θ : ι → ℝ) : κ θ ∈ Φ '' U := by
    obtain ⟨y', hy', -, hΦy'⟩ := exists_mem_eq_actionAngleCover_of_image_eq hΦ hF hy θ
    exact ⟨y', hy', hΦy'⟩
  have : Nonempty M := ⟨y⟩
  -- The inverse of `Φ` on `U` is continuous on `Φ '' U`, which contains the image of `κ`.
  refine ⟨invFunOn Φ U ∘ κ,
    ((IsLocalDiffeomorphOn.contMDiffOn_invFunOn (fun x ↦ hloc x x.property) hU
      hinj).continuousOn).comp_continuous hκ hmem, fun θ ↦ ?_⟩
  have hGU : invFunOn Φ U (κ θ) ∈ U := invFunOn_mem (hmem θ)
  have hGΦ : Φ (invFunOn Φ U (κ θ)) = κ θ := invFunOn_eq (hmem θ)
  refine ⟨hGU, ?_, hGΦ⟩
  obtain ⟨y', hy', hFy', hΦy'⟩ := exists_mem_eq_actionAngleCover_of_image_eq hΦ hF hy θ
  rw [comp_apply, hinj hGU hy' (hGΦ.trans hΦy'.symm), hFy']

end Continuous

/-! ### The critical equilibrium of the harmonic oscillator -/

section Oscillator

variable {m ν : ℝ}

/-- For nonzero mass and frequency, the level of the oscillator energy through the equilibrium
`0` is the single point `0`. -/
theorem preimage_oscillatorHamiltonian_zero (hm : m ≠ 0) (hν : ν ≠ 0) :
    (fun x ↦ fun _ : Fin 1 ↦ oscillatorHamiltonian m ν x) ⁻¹'
        {fun _ ↦ oscillatorHamiltonian m ν 0} = {0} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, funext_iff, Fin.forall_fin_one,
    oscillatorHamiltonian_zero]
  exact oscillatorHamiltonian_eq_zero_iff hm hν

/-- **The equilibrium of the oscillator is a critical point** of its energy, a quadratic form. -/
theorem not_isRegularPoint_oscillatorHamiltonian_zero :
    ¬IsRegularPoint 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 1 → ℝ)
      (fun x ↦ fun _ : Fin 1 ↦ oscillatorHamiltonian m ν x) 0 := by
  have hH : HasFDerivAt (oscillatorHamiltonian m ν) (0 : ℝ × ℝ →L[ℝ] ℝ) 0 := by
    simpa using hasFDerivAt_oscillatorHamiltonian m ν 0
  have hF : HasFDerivAt (fun x ↦ fun _ : Fin 1 ↦ oscillatorHamiltonian m ν x)
      (0 : ℝ × ℝ →L[ℝ] Fin 1 → ℝ) 0 :=
    hasFDerivAt_pi.2 fun _ ↦ by simpa using hH
  have hns : ¬Surjective (0 : ℝ × ℝ →L[ℝ] Fin 1 → ℝ) := fun hsurj ↦ by
    obtain ⟨v, hv⟩ := hsurj fun _ ↦ 1
    simpa using congrFun hv 0
  rw [isRegularPoint_iff_surjective_fderiv, hF.fderiv]
  exact hns

/-- **No action–angle chart at the critical equilibrium of the oscillator.** For nonzero mass and
frequency, there are no `U ∋ 0`, `D`, `Φ` into `T*(AddCircle p)` and `h` such that `Φ`
maps `U` onto the covectors whose actions lie in `D` and the energy is `h` of the actions on `U`:
the level through `0` is the single point `0`, while such a chart would put a circle in it. That
level is compact, but `0` is a critical point
(`TauCeti.not_isRegularPoint_oscillatorHamiltonian_zero`), so this shows that the regularity
hypothesis of `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle` cannot be dropped. -/
theorem not_exists_actionAngle_oscillatorHamiltonian_zero (hm : m ≠ 0) (hν : ν ≠ 0) (p : ℝ)
    [Fact (0 < p)] :
    ¬∃ (U : Set (ℝ × ℝ)) (D : Set (Fin 1 → ℝ))
      (Φ : ℝ × ℝ → CotangentBundle (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ))
        (Fin 1 → AddCircle p)) (h : (Fin 1 → ℝ) → Fin 1 → ℝ),
      0 ∈ U ∧ Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D} ∧
        ∀ y ∈ U, (fun _ ↦ oscillatorHamiltonian m ν y) = h (fun i ↦ (Φ y).snd (Pi.single i 1)) := by
  rintro ⟨U, D, Φ, h, h0, hΦ, hF⟩
  refine not_subsingleton_inter_preimage_of_image_eq hΦ hF h0 ?_
  rw [preimage_oscillatorHamiltonian_zero hm hν]
  exact subsingleton_singleton.anti inter_subset_right

end Oscillator

/-! ### The noncompact levels of the momentum -/

section Momentum

/-- Every point of the plane is a regular point of the momentum `(q, p) ↦ p`. -/
theorem isRegularPoint_momentum (x : ℝ × ℝ) :
    IsRegularPoint 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 1 → ℝ) (fun x : ℝ × ℝ ↦ fun _ : Fin 1 ↦ x.2) x := by
  have hF : HasFDerivAt (fun x : ℝ × ℝ ↦ fun _ : Fin 1 ↦ x.2)
      (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hasFDerivAt_pi.2 fun _ ↦ hasFDerivAt_snd
  have hsurj : Surjective (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    fun w ↦ ⟨(0, w 0), funext fun i ↦ by rw [Subsingleton.elim i 0]; simp⟩
  rw [isRegularPoint_iff_surjective_fderiv, hF.fderiv]
  exact hsurj

/-- The level of the momentum `(q, p) ↦ p` through `x` is connected: it is the whole line
`p = x.2`. -/
theorem connectedComponentIn_preimage_momentum (x : ℝ × ℝ) :
    connectedComponentIn ((fun x : ℝ × ℝ ↦ fun _ : Fin 1 ↦ x.2) ⁻¹' {fun _ ↦ x.2}) x =
      {y | y.2 = x.2} := by
  have hlevel : (fun x : ℝ × ℝ ↦ fun _ : Fin 1 ↦ x.2) ⁻¹' {fun _ ↦ x.2} =
      range fun q : ℝ ↦ (q, x.2) := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, funext_iff, Fin.forall_fin_one, mem_range]
    exact ⟨fun hy ↦ ⟨y.1, Prod.ext rfl hy.symm⟩, fun ⟨q, hq⟩ ↦ hq ▸ rfl⟩
  rw [hlevel, (isPreconnected_range (by fun_prop)).connectedComponentIn ⟨x.1, rfl⟩]
  ext y
  exact ⟨fun ⟨q, hq⟩ ↦ hq ▸ rfl, fun hy ↦ ⟨y.1, Prod.ext rfl hy.symm⟩⟩

/-- The level of the momentum `(q, p) ↦ p` through any point is not compact. -/
theorem not_isCompact_connectedComponentIn_preimage_momentum (x : ℝ × ℝ) :
    ¬IsCompact
      (connectedComponentIn ((fun x : ℝ × ℝ ↦ fun _ : Fin 1 ↦ x.2) ⁻¹' {fun _ ↦ x.2}) x) := by
  rw [connectedComponentIn_preimage_momentum]
  intro hK
  have himage : Prod.fst '' {y : ℝ × ℝ | y.2 = x.2} = univ :=
    eq_univ_of_forall fun q ↦ ⟨(q, x.2), rfl, rfl⟩
  exact noncompact_univ ℝ (himage ▸ hK.image continuous_fst)

/-- **No action–angle chart around the noncompact levels of the momentum.** For the momentum
`f(q, p) = p` on `ℝ²` and any `x`, there are no open `U ∋ x`, `D`, `Φ` into `T*(AddCircle p)`
injective on `U` and a local diffeomorphism at its points, and `h` such that `Φ` maps `U` onto the
covectors whose actions lie in `D` and `f` is `h` of the actions on `U`: such a chart would embed a
circle continuously in the line `p = x.2`. Every point is regular
(`TauCeti.isRegularPoint_momentum`), but the level through `x` is not compact
(`TauCeti.not_isCompact_connectedComponentIn_preimage_momentum`), so this shows that the
compactness hypothesis of `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle` cannot be
dropped. -/
theorem not_exists_actionAngle_momentum (x : ℝ × ℝ) (p : ℝ) [Fact (0 < p)] :
    ¬∃ (U : Set (ℝ × ℝ)) (D : Set (Fin 1 → ℝ))
      (Φ : ℝ × ℝ → CotangentBundle (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ))
        (Fin 1 → AddCircle p)) (h : (Fin 1 → ℝ) → Fin 1 → ℝ),
      IsOpen U ∧ x ∈ U ∧ InjOn Φ U ∧ Φ '' U = {z | (fun i ↦ z.snd (Pi.single i 1)) ∈ D} ∧
        (∀ y ∈ U, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ)
          ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
        ∀ y ∈ U, (fun _ ↦ y.2) = h (fun i ↦ (Φ y).snd (Pi.single i 1)) := by
  rintro ⟨U, D, Φ, h, hU, hx, hinj, hΦ, hloc, hF⟩
  obtain ⟨G, hG, hGU⟩ :=
    exists_continuous_mem_eq_actionAngleCover_of_image_eq hU hinj hΦ hloc hF hx
  have hp : 0 < p := Fact.out
  -- The position along the circle of angles `t ↦ [t]` in the level `p = x.2`.
  set f : ℝ → ℝ := fun t ↦ (G fun _ ↦ t).1
  have hf : Continuous f := continuous_fst.comp (hG.comp (continuous_pi fun _ ↦ continuous_id))
  -- Points of the level are determined by their position, and points of the circle by their
  -- angle in `[0, p)`.
  have hGeq {s t : ℝ} (hst : f s = f t) : G (fun _ ↦ s) = G fun _ ↦ t :=
    Prod.ext hst (by
      have hs := congrFun (hGU fun _ ↦ s).2.1 0
      have ht := congrFun (hGU fun _ ↦ t).2.1 0
      exact hs.trans ht.symm)
  have hproj (t : ℝ) : (Φ (G fun _ ↦ t)).proj = fun _ ↦ (t : AddCircle p) := by
    rw [(hGU _).2.2, CotangentBundle.proj_actionAngleCover]
  have hperiod : f 0 = f p := by
    refine congrArg Prod.fst (hinj (hGU _).1 (hGU _).1 ?_)
    rw [(hGU _).2.2, (hGU _).2.2, CotangentBundle.actionAngleCover_eq_actionAngleCover_iff]
    exact ⟨rfl, fun _ ↦ 1, funext fun _ ↦ by simp⟩
  refine hf.continuousOn.apply_ne_apply_of_injOn_Ico hp (fun s hs t ht hst ↦ ?_) hperiod
  have hcoe := congrFun ((hproj s).symm.trans ((congrArg (fun y ↦ (Φ y).proj) (hGeq hst)).trans
    (hproj t))) 0
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (by simpa using hs) (by simpa using ht)).1
    hcoe

end Momentum

end TauCeti
