/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.TietzeExtension
public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import Mathlib.Analysis.Complex.Tietze

/-!
# Character averages and local triviality of free torus actions

Let a compact group `T` act continuously on a space `X`. For a character `χ : T → 𝕊¹` and a
function `f : X → ℂ`, the *character average*
`F x = ∫ t, χ(t⁻¹) * f (t • x)`, against normalized Haar measure, is `χ`-equivariant:
`F (g • x) = χ g * F x`. It is continuous when `χ` and `f` are, and `F x = 1` when `f` restricts
to `χ` on the orbit of `x`.

When `T` is a torus, given with a continuous isomorphism `T ≃ (ι → 𝕊¹)` for a finite `ι`, and
`X` is normal and Hausdorff, this gives local triviality of the orbit projection near every orbit
with trivial stabilizers.
The orbit of such a point `x₀` is a closed copy of `T`. Extend each coordinate character from it
by the Tietze extension theorem, and average the extension against the same character. The
resulting functions `F_j` are nonzero near `x₀`, and their phases `F_j / |F_j|` assemble to a
continuous equivariant map `u` into `T` on a saturated open neighbourhood of `x₀`. Then
`TauCeti.orbitTrivialization` turns `u` into a principal `T`-bundle chart of `X → X ⧸ T`.
No local compactness of `X` is assumed.

This is the torus case of Gleason's averaging argument for local cross-sections of free actions
of compact Lie groups (A. M. Gleason, *Spaces with a compact Lie group of transformations*,
Proc. Amer. Math. Soc. 1 (1950), 35–43), where matrix coefficients of a faithful representation
are extended from an orbit and averaged; for a torus the coordinate characters suffice.

## Main definitions and results

* `TauCeti.characterAverage`: the character average `x ↦ ∫ t, χ(t⁻¹) * f (t • x)`.
* `TauCeti.characterAverage_smul`, `TauCeti.continuous_characterAverage` and
  `TauCeti.characterAverage_eq_one`: equivariance, continuity and normalization.
* `TauCeti.exists_continuousMap_apply_smul_eq_of_stabilizer_eq_bot`: a continuous function on a
  compact group extends from an orbit with trivial stabilizer to the whole normal space.
* `TauCeti.exists_continuousOn_smul_eq_mul_of_stabilizer_eq_bot`: near a point with trivial
  stabilizer, a torus action admits a continuous equivariant map to the torus on a saturated open
  neighbourhood.
* `TauCeti.exists_trivialization_of_stabilizer_eq_bot` and
  `TauCeti.exists_trivialization_of_forall_stabilizer_eq_bot`: the orbit projection of a torus
  action is locally trivial near such points, and everywhere for a free action.
-/

public section

open Bundle MeasureTheory MulAction Set Topology

namespace TauCeti

section Average

variable {T X : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [CompactSpace T]
  [MeasurableSpace T] [BorelSpace T] [MulAction T X]

/-- The average of `f` along `T`-orbits, twisted by a character `χ`:
`characterAverage χ f x = ∫ t, χ(t⁻¹) * f (t • x)` against normalized Haar measure on the
compact group `T`. It is `χ`-equivariant (`characterAverage_smul`). -/
noncomputable def characterAverage (χ : T →* Circle) (f : X → ℂ) (x : X) : ℂ :=
  ∫ t, (χ t⁻¹ : ℂ) * f (t • x) ∂haarProb T

/-- The character average is the Haar integral of the twisted function along the orbit. -/
theorem characterAverage_def (χ : T →* Circle) (f : X → ℂ) (x : X) :
    characterAverage χ f x = ∫ t, (χ t⁻¹ : ℂ) * f (t • x) ∂haarProb T :=
  (rfl)

/-- The character average transforms by the character: `F (g • x) = χ g * F x`. -/
@[simp]
theorem characterAverage_smul (χ : T →* Circle) (f : X → ℂ) (g : T) (x : X) :
    characterAverage χ f (g • x) = χ g * characterAverage χ f x := by
  rw [characterAverage_def, characterAverage_def, ← integral_const_mul,
    ← integral_mul_right_eq_self (fun t ↦ (χ g : ℂ) * ((χ t⁻¹ : ℂ) * f (t • x))) g]
  congr 1 with t
  simp [mul_smul, ← mul_assoc]

/-- The character average of `f` is `1` at a point on whose orbit `f` restricts to the
character. -/
theorem characterAverage_eq_one (χ : T →* Circle) {f : X → ℂ} {x : X}
    (hf : ∀ t : T, f (t • x) = χ t) : characterAverage χ f x = 1 := by
  simp [characterAverage_def, hf]

variable [TopologicalSpace X] [ContinuousSMul T X]

/-- The character average of a continuous function by a continuous character is continuous. -/
theorem continuous_characterAverage {χ : T →* Circle} (hχ : Continuous χ) {f : X → ℂ}
    (hf : Continuous f) : Continuous (characterAverage χ f) := by
  let k : C(X × T, ℂ) :=
    ⟨fun p ↦ (χ p.2⁻¹ : ℂ) * f (p.2 • p.1), by fun_prop⟩
  have hk : characterAverage χ f = fun x ↦ haarAverage T (𝕜 := ℂ) (k.curry x) :=
    funext fun x ↦ by simp [characterAverage_def, haarAverage_apply, k]
  rw [hk]
  exact (haarAverage T).continuous.comp k.curry.continuous

end Average

section Extension

universe u v

variable {T : Type*} {X : Type u} {Y : Type v} [Group T] [TopologicalSpace T] [CompactSpace T]
  [TopologicalSpace X] [NormalSpace X] [T2Space X] [MulAction T X] [ContinuousSMul T X]
  [TopologicalSpace Y] [TietzeExtension.{u, v} Y]

/-- A continuous function on a compact group extends from an orbit with trivial stabilizer to the
whole normal Hausdorff space: the orbit map identifies the group with a closed subset. -/
theorem exists_continuousMap_apply_smul_eq_of_stabilizer_eq_bot {x₀ : X}
    (hx₀ : stabilizer T x₀ = ⊥) (h : C(T, Y)) : ∃ f : C(X, Y), ∀ t : T, f (t • x₀) = h t := by
  have hinj : Function.Injective fun t : T ↦ t • x₀ := fun s t hst ↦ by
    have : t⁻¹ * s ∈ stabilizer T x₀ := by
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
      exact hst
    rw [hx₀, Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this.symm
  have hemb : IsClosedEmbedding fun t : T ↦ t • x₀ :=
    (continuous_id.smul continuous_const).isClosedEmbedding hinj
  obtain ⟨f, hf⟩ := ContinuousMap.exists_extension hemb h
  exact ⟨f, fun t ↦ DFunLike.congr_fun hf t⟩

end Extension

section Torus

variable {T X ι : Type*} [Group T] [TopologicalSpace T] [TopologicalSpace X] [MulAction T X]
  [ContinuousSMul T X] [Finite ι]

/-- Near a point `x₀` with trivial stabilizer, a continuous action of a torus
`T ≃ₜ* (ι → Circle)` on a normal Hausdorff space admits a continuous equivariant map `u` to `T`
on a `T`-invariant open neighbourhood `V` of `x₀`, normalized by `u x₀ = 1`. -/
theorem exists_continuousOn_smul_eq_mul_of_stabilizer_eq_bot [NormalSpace X] [T2Space X]
    (e : T ≃ₜ* (ι → Circle)) {x₀ : X} (hx₀ : stabilizer T x₀ = ⊥) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ (∀ g : T, ∀ x ∈ V, g • x ∈ V) ∧
      ∃ u : X → T, ContinuousOn u V ∧ u x₀ = 1 ∧ ∀ g : T, ∀ x ∈ V, u (g • x) = g * u x := by
  have : CompactSpace T := e.toHomeomorph.symm.compactSpace
  have : IsTopologicalGroup T := e.isInducing.isTopologicalGroup e.toMonoidHom
  borelize T
  -- The coordinate characters of the torus, extended from the orbit of `x₀` and averaged.
  let χ (j : ι) : T →* Circle := (Pi.evalMonoidHom (fun _ : ι ↦ Circle) j).comp (e : T →* _)
  have hχ (j : ι) : Continuous (χ j) := (continuous_apply j).comp e.continuous
  choose f hf using fun j ↦ exists_continuousMap_apply_smul_eq_of_stabilizer_eq_bot hx₀
    ((ContinuousMap.mk ((↑) : Circle → ℂ) continuous_subtype_val).comp ⟨χ j, hχ j⟩)
  let F (j : ι) : X → ℂ := characterAverage (χ j) (f j)
  have hF (j : ι) : Continuous (F j) := continuous_characterAverage (hχ j) (f j).continuous
  have hF₀ (j : ι) : F j x₀ = 1 := characterAverage_eq_one (χ j) (hf j)
  -- The phases `F j / ‖F j‖` of the averages assemble to the equivariant map.
  have hmem (z : ℂ) (hz : z ≠ 0) : z / ‖z‖ ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere, hz]
  let v (j : ι) (x : X) : Circle := if hx : F j x = 0 then 1 else ⟨F j x / ‖F j x‖, hmem _ hx⟩
  have hv_eq (j : ι) (x : X) (hx : F j x ≠ 0) : (v j x : ℂ) = F j x / ‖F j x‖ := by
    simp [v, hx]
  have hv (j : ι) : ContinuousOn (v j) {x | F j x ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun x : {x | F j x ≠ 0} ↦ (⟨F j x / ‖F j x‖, hmem _ x.2⟩ : Circle) :=
      Continuous.subtype_mk (((hF j).comp continuous_subtype_val).div (by fun_prop)
        fun x ↦ Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 x.2)) _
    exact hc.congr fun x ↦ by simp [v, domRestrict, x.2.out]
  let V : Set X := {x | ∀ j, F j x ≠ 0}
  have hV : V = ⋂ j, {x | F j x ≠ 0} := by ext; simp [V]
  have hVsmul (g : T) (x : X) (hx : x ∈ V) : g • x ∈ V := fun j ↦ by
    simpa [F, characterAverage_smul] using hx j
  have hv_smul (g : T) (x : X) (hx : x ∈ V) (j : ι) : v j (g • x) = χ j g * v j x := by
    ext
    rw [hv_eq j _ (hVsmul g x hx j), Circle.coe_mul, hv_eq j _ (hx j)]
    simp only [F, characterAverage_smul, norm_mul, Circle.norm_coe, one_mul, mul_div_assoc]
  refine ⟨V, hV ▸ isOpen_iInter_of_finite fun j ↦ isOpen_ne_fun (hF j) continuous_const,
    fun j ↦ by simp [hF₀], hVsmul, fun x ↦ e.symm fun j ↦ v j x, ?_, ?_, ?_⟩
  · exact e.symm.continuous.comp_continuousOn
      (continuousOn_pi.2 fun j ↦ (hv j).mono fun x hx ↦ hx j)
  · rw [map_eq_one_iff _ e.symm.injective]
    ext j
    simp [hv_eq j x₀ (by simp [hF₀]), hF₀]
  · intro g x hx
    apply e.injective
    ext1 j
    simp [hv_smul g x hx, χ]

/-- Near a point with trivial stabilizer, the orbit projection of a continuous torus action on a
normal Hausdorff space is locally trivial: it has a principal `T`-bundle chart whose base
contains the orbit of the point. -/
theorem exists_trivialization_of_stabilizer_eq_bot [NormalSpace X] [T2Space X]
    (e : T ≃ₜ* (ι → Circle)) {x₀ : X} (hx₀ : stabilizer T x₀ = ⊥) :
    ∃ φ : Trivialization T (Quotient.mk (orbitRel T X)), Quotient.mk _ x₀ ∈ φ.baseSet ∧
      ∀ g : T, ∀ x ∈ φ.source, φ (g • x) = ((φ x).1, g * (φ x).2) := by
  have : IsTopologicalGroup T := e.isInducing.isTopologicalGroup e.toMonoidHom
  obtain ⟨V, hVo, hx₀V, hVsmul, u, hu, -, hu_smul⟩ :=
    exists_continuousOn_smul_eq_mul_of_stabilizer_eq_bot e hx₀
  have hV : Quotient.mk (orbitRel T X) ⁻¹' (Quotient.mk _ '' V) = V := by
    refine Subset.antisymm (fun x ⟨y, hy, hyx⟩ ↦ ?_) (subset_preimage_image _ _)
    obtain ⟨g, rfl⟩ : ∃ g : T, g • x = y := Quotient.exact hyx
    simpa using hVsmul g⁻¹ _ hy
  refine ⟨orbitTrivialization (Quotient.mk _ '' V) (isOpenMap_quotient_mk'_mul V hVo) u
    (by rwa [hV]) (by rwa [hV]), ?_, fun g x hx ↦ orbitTrivialization_apply_smul g ?_⟩
  · rw [orbitTrivialization_baseSet]
    exact mem_image_of_mem _ hx₀V
  · rwa [Trivialization.mem_source, orbitTrivialization_baseSet] at hx

/-- The orbit projection of a free continuous torus action on a normal Hausdorff space is
locally trivial: every orbit lies in the base of a principal `T`-bundle chart. -/
theorem exists_trivialization_of_forall_stabilizer_eq_bot [NormalSpace X] [T2Space X]
    (e : T ≃ₜ* (ι → Circle)) (hfree : ∀ x : X, stabilizer T x = ⊥)
    (y : Quotient (orbitRel T X)) :
    ∃ φ : Trivialization T (Quotient.mk (orbitRel T X)), y ∈ φ.baseSet ∧
      ∀ g : T, ∀ x ∈ φ.source, φ (g • x) = ((φ x).1, g * (φ x).2) := by
  obtain ⟨φ, hφ, hφ_smul⟩ := exists_trivialization_of_stabilizer_eq_bot e (hfree y.out)
  exact ⟨φ, by rwa [Quotient.out_eq] at hφ, hφ_smul⟩

end Torus

end TauCeti
