/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading

/-!
# Trilinear maps of families of Novikov series

On finite unions of torsors, completed combinations are given by their coordinates relative to
reference generators (`NovikovModule.coordinates`), and bilinear maps over the Novikov ring by
matrices of Novikov series (`NovikovModule.novikovProductOfMatrix`). This file adds the
three-input counterpart: a family `K` of Novikov series indexed by three input orbits and an
output orbit defines a trilinear map over the Novikov ring, given in the reference coordinates by
`K(a, b, c)ₗ = ∑ᵢ ∑ⱼ ∑ₖ aᵢ bⱼ cₖ Kᵢⱼₖₗ`. Every trilinear map over the Novikov ring arises this way,
and homogeneous entries give a fixed degree shift. In Floer theory such a family counts the rigid
elements of a one-parameter family of four-punctured spheres, and its trilinear map is the
homotopy between the two bracketings of the product
(`NovikovModule.novikovProductOfMatrix_assoc_sub_eq_add`).

## Main results

* `NovikovModule.novikovTrilinearOfMatrix`: the trilinear map of a family of Novikov series.
* `NovikovModule.coordinates_novikovTrilinearOfMatrix`: its matrix formula.
* `NovikovModule.eq_novikovTrilinearOfMatrix`: every Novikov-trilinear map is the trilinear map
  of a family.
* `NovikovModule.novikovTrilinearOfMatrix_mem_gradeBy`: homogeneous entries give a degree shift.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule


variable {R H ι₁ ι₂ ι₃ ι₀ : Type*} [CommSemiring R] [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₃ : ι₃ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₃ k)]
  [∀ l, AddTorsor H (P₀ l)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₃ : (Σ k, P₃ k) → ℝ} {F₀ : (Σ l, P₀ l) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₃ : ∀ k h (p : P₃ k), F₃ ⟨k, h +ᵥ p⟩ = F₃ ⟨k, p⟩ - N h)
  (hF₀ : ∀ l h (p : P₀ l), F₀ ⟨l, h +ᵥ p⟩ = F₀ ⟨l, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₃ : ∀ k, P₃ k) (r₀ : ∀ l, P₀ l)
  [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₀]
  (K : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R H N)

/-- **The Novikov-trilinear map of a family of Novikov series.** For finitely many orbits and
reference generators `r₁`, `r₂`, `r₃` and `r₀`, a family `K` of Novikov series indexed by three
input orbits and an output orbit defines a trilinear map over the Novikov ring for the module
structures of `TauCeti.NovikovModule.module`. In the reference coordinates it is
`K(a, b, c)ₗ = ∑ᵢ ∑ⱼ ∑ₖ aᵢ bⱼ cₖ Kᵢⱼₖₗ` (`NovikovModule.coordinates_novikovTrilinearOfMatrix`).
In Floer theory `K` counts the rigid elements of a one-parameter family of four-punctured spheres,
and the trilinear map is the homotopy between the two bracketings of the product. -/
def novikovTrilinearOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    letI := module (R := R) hF₃
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovModule R F₃ →ₗ[NovikovSeries R H N] NovikovModule R F₀ :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₂
  letI := module (R := R) hF₃
  letI := module (R := R) hF₀
  ∑ i, ∑ j, ∑ k, ∑ l, ((basis hF₁ r₁).coord i).smulRight (((basis hF₂ r₂).coord j).smulRight
    (((basis hF₃ r₃).coord k).smulRight (K i j k l • basis hF₀ r₀ l)))

/-- **The matrix formula for the trilinear map of a family.** In the coordinates relative to the
reference generators, `K(a, b, c)ₗ = ∑ᵢ ∑ⱼ ∑ₖ aᵢ bⱼ cₖ Kᵢⱼₖₗ`. -/
theorem coordinates_novikovTrilinearOfMatrix (a : NovikovModule R F₁) (b : NovikovModule R F₂)
    (c : NovikovModule R F₃) (l : ι₀) :
    coordinates hF₀ r₀ (novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K a b c) l =
      ∑ i, ∑ j, ∑ k, coordinates hF₁ r₁ a i * coordinates hF₂ r₂ b j *
        coordinates hF₃ r₃ c k * K i j k l := by
  classical
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₃
  let := module (R := R) hF₀
  rw [← basis_repr_apply hF₀ r₀]
  simp [novikovTrilinearOfMatrix, LinearMap.sum_apply, map_sum, Finsupp.single_apply, mul_assoc]

/-- The trilinear map of a family on three reference basis vectors has the `(i, j, k)` entries of
the family as its coordinates: `K(eᵢ, eⱼ, eₖ) = ∑ₗ Kᵢⱼₖₗ eₗ`. -/
@[simp]
theorem coordinates_novikovTrilinearOfMatrix_basis (i : ι₁) (j : ι₂) (k : ι₃) (l : ι₀) :
    coordinates hF₀ r₀ (novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K
      (basis hF₁ r₁ i) (basis hF₂ r₂ j) (basis hF₃ r₃ k)) l = K i j k l := by
  classical
  simp [coordinates_novikovTrilinearOfMatrix, Pi.single_apply]

/-- **Every Novikov-trilinear map is the trilinear map of a family.** A trilinear map over the
Novikov ring between finitely generated completed modules is the trilinear map of the family of
coordinates of its values on the reference basis vectors. -/
theorem eq_novikovTrilinearOfMatrix (B :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    letI := module (R := R) hF₃
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovModule R F₃ →ₗ[NovikovSeries R H N] NovikovModule R F₀) :
    B = novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ (fun i j k l =>
      coordinates hF₀ r₀ (B (basis hF₁ r₁ i) (basis hF₂ r₂ j) (basis hF₃ r₃ k)) l) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₃
  let := module (R := R) hF₀
  refine (basis hF₁ r₁).ext fun i => (basis hF₂ r₂).ext fun j => (basis hF₃ r₃).ext fun k => ?_
  refine (coordinates hF₀ r₀).injective (funext fun l => ?_)
  rw [coordinates_novikovTrilinearOfMatrix_basis]

/-- **Degree of the trilinear map of a family.** Let the generators be graded by functions `dₗ`
that change by `δ h` under the translation by `h`. If every entry `Kᵢⱼₖₗ` is homogeneous of the
degree `d₁ (r₁ i) + d₂ (r₂ j) + d₃ (r₃ k) + ε - d₀ (r₀ l)`, then the trilinear map shifts degrees
by `ε`: it sends combinations of degrees `e₁`, `e₂`, `e₃` to a combination of degree
`e₁ + e₂ + e₃ + ε`. -/
theorem novikovTrilinearOfMatrix_mem_gradeBy {D : Type*} [AddCommGroup D] (δ : H →+ D)
    {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ j, P₂ j) → D} {d₃ : (Σ k, P₃ k) → D}
    {d₀ : (Σ l, P₀ l) → D}
    (hd₁ : ∀ i h (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
    (hd₂ : ∀ j h (p : P₂ j), d₂ ⟨j, h +ᵥ p⟩ = δ h + d₂ ⟨j, p⟩)
    (hd₃ : ∀ k h (p : P₃ k), d₃ ⟨k, h +ᵥ p⟩ = δ h + d₃ ⟨k, p⟩)
    (hd₀ : ∀ l h (p : P₀ l), d₀ ⟨l, h +ᵥ p⟩ = δ h + d₀ ⟨l, p⟩) {ε : D}
    (hK : ∀ i j k l, K i j k l ∈ NovikovSeries.gradeBy R N δ
      (d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩ + d₃ ⟨k, r₃ k⟩ + ε - d₀ ⟨l, r₀ l⟩))
    {e₁ e₂ e₃ : D} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ e₁)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ e₂)
    {c : NovikovModule R F₃} (hc : c ∈ gradeBy R F₃ d₃ e₃) :
    novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ K a b c ∈
      gradeBy R F₀ d₀ (e₁ + e₂ + e₃ + ε) := by
  rw [mem_gradeBy_iff_coordinates hF₁ δ hd₁ r₁] at ha
  rw [mem_gradeBy_iff_coordinates hF₂ δ hd₂ r₂] at hb
  rw [mem_gradeBy_iff_coordinates hF₃ δ hd₃ r₃] at hc
  rw [mem_gradeBy_iff_coordinates hF₀ δ hd₀ r₀]
  intro l
  rw [coordinates_novikovTrilinearOfMatrix]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun k _ => ?_
  convert SetLike.mul_mem_graded (SetLike.mul_mem_graded (SetLike.mul_mem_graded (ha i) (hb j))
    (hc k)) (hK i j k l) using 2
  abel

end NovikovModule

end TauCeti
