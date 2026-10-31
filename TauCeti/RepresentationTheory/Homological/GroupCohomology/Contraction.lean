/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Contractions of inhomogeneous cochains from operators lowering the degree

Let `A` be a `k`-linear representation of a group `G`, and let
`h n : Cⁿ⁺¹(G, A) → Cⁿ(G, A)` be linear maps between the inhomogeneous cochains satisfying
$$h \circ d = d \circ h + (-1)^n \text{ on } (n + 1)\text{-cochains}, \qquad
  h \circ d = P - 1 \text{ on } 0\text{-cochains}$$
for an endomorphism `P` of the `0`-cochains. Then `P` is a cochain map when placed in degree `0`
(`TauCeti.groupCohomology.comp_d_zero_eq_zero`), and with the sign `(-1)^(n+1)` on the component
of degree `n + 1 → n`, the maps `h` form a homotopy from the identity of
`inhomogeneousCochains A` to it. Every positive-degree cocycle `f` is the coboundary of
`(-1)^(n+1) h f`.

This is the formal part shared by the contractions that insert a last argument: averaging over a
finite group (`TauCeti.inhomogeneousCochains.averageLast`) and weighting by a cutoff function
(`TauCeti.inhomogeneousCochains.cutoffLast`).

## Main declarations

* `TauCeti.inhomogeneousCochains.d_smul_of_d_comp_eq`: the explicit primitive of a
  positive-degree cocycle.
* `TauCeti.groupCohomology.ofDegreeZero`: an endomorphism of the `0`-cochains whose composite with
  the differential vanishes, as an endomorphism of `inhomogeneousCochains A`.
* `TauCeti.groupCohomology.homotopyOfDCompEq`: the homotopy from the identity to
  `TauCeti.groupCohomology.ofDegreeZero`.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti.inhomogeneousCochains

open _root_.inhomogeneousCochains

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

/-- **The explicit primitive of a positive-degree cocycle.** If `h ∘ d = d ∘ h + (-1)^n` on
`(n + 1)`-cochains, then an `(n + 1)`-cocycle `f` is the coboundary of `(-1)^(n+1) • h f`. -/
theorem d_smul_of_d_comp_eq {n : ℕ}
    {h : ∀ m : ℕ, ModuleCat.of k ((Fin (m + 1) → G) → A) ⟶ ModuleCat.of k ((Fin m → G) → A)}
    (hd : d A (n + 1) ≫ h (n + 1) = h n ≫ d A n + (-1 : k) ^ n • 𝟙 _)
    {f : ModuleCat.of k ((Fin (n + 1) → G) → A)} (hf : (d A (n + 1)).hom f = 0) :
    (d A n).hom ((-1 : k) ^ (n + 1) • (h n).hom f) = f := by
  have hdf := congr($(hd).hom f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hf, map_zero, ModuleCat.hom_add,
    ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at hdf
  have hsign : (-1 : k) ^ (n + 1) * (-1) ^ n = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨n, by ring⟩
  rw [map_smul, eq_neg_of_add_eq_zero_left hdf.symm, smul_neg, smul_smul, hsign, neg_one_smul,
    neg_neg]

end TauCeti.inhomogeneousCochains

namespace TauCeti.groupCohomology

open _root_.groupCohomology _root_.inhomogeneousCochains

variable {k G : Type u} [CommRing k] [Group G] {A : Rep.{u} k G}
variable {P : ModuleCat.of k ((Fin 0 → G) → A) ⟶ ModuleCat.of k ((Fin 0 → G) → A)}

/-- An endomorphism `P` of the `0`-cochains with `P ≫ d = 0`, placed in degree `0`, as an
endomorphism of the complex of inhomogeneous cochains: it is `P` on `0`-cochains and zero in
positive degrees. -/
def ofDegreeZero (P : ModuleCat.of k ((Fin 0 → G) → A) ⟶ ModuleCat.of k ((Fin 0 → G) → A))
    (hP : P ≫ d A 0 = 0) : inhomogeneousCochains A ⟶ inhomogeneousCochains A where
  f
    | 0 => P
    | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rcases i with _ | i
    · rw [inhomogeneousCochains.d_def]
      exact hP.trans Limits.comp_zero.symm
    · simp

/-- In degree `0`, `TauCeti.groupCohomology.ofDegreeZero P hP` is `P`. -/
@[simp]
theorem ofDegreeZero_f_zero (hP : P ≫ d A 0 = 0) : (ofDegreeZero P hP).f 0 = P :=
  (rfl)

/-- In positive degrees, `TauCeti.groupCohomology.ofDegreeZero P hP` is zero. -/
@[simp]
theorem ofDegreeZero_f_succ (hP : P ≫ d A 0 = 0) (n : ℕ) : (ofDegreeZero P hP).f (n + 1) = 0 :=
  (rfl)

variable {h : ∀ n : ℕ, ModuleCat.of k ((Fin (n + 1) → G) → A) ⟶ ModuleCat.of k ((Fin n → G) → A)}
variable (hd : ∀ n : ℕ, d A (n + 1) ≫ h (n + 1) = h n ≫ d A n + (-1 : k) ^ n • 𝟙 _)
  (hd₀ : d A 0 ≫ h 0 = P - 𝟙 _)

include hd hd₀ in
/-- If `h ∘ d = d ∘ h + (-1)^n` on positive-degree cochains and `h ∘ d = P - 1` on
`0`-cochains, then the composite of `P` with the differential vanishes. -/
theorem comp_d_zero_eq_zero : P ≫ d A 0 = 0 := by
  have hP : P = d A 0 ≫ h 0 + 𝟙 _ := by rw [hd₀, sub_add_cancel]
  have h₁ := congr(d A 0 ≫ $(hd 0))
  rw [← Category.assoc, inhomogeneousCochains.d_comp_d, Limits.zero_comp, pow_zero, one_smul,
    Preadditive.comp_add, Category.comp_id] at h₁
  rw [hP, Preadditive.add_comp, Category.assoc, Category.id_comp,
    eq_neg_of_add_eq_zero_left h₁.symm, neg_add_cancel]

/-- The components `(-1)^(j+1) • h j` of the homotopy, from degree `j + 1` to degree `j`. -/
private def homotopyOfDCompEqHom (i j : ℕ) (hji : (ComplexShape.up ℕ).Rel j i) :
    (inhomogeneousCochains A).X i ⟶ (inhomogeneousCochains A).X j :=
  ((inhomogeneousCochains A).XIsoOfEq hji.symm).hom ≫ ((-1 : k) ^ (j + 1) • h j)

include hd hd₀ in
private theorem sub_ofDegreeZero_eq_nullHomotopicMap' :
    𝟙 _ - ofDegreeZero P (comp_d_zero_eq_zero hd hd₀) =
      Homotopy.nullHomotopicMap' (homotopyOfDCompEqHom (h := h)) := by
  ext n : 1
  rcases n with _ | n
  · -- Degree `0` has no incoming differential, so only `d ≫ h` contributes.
    have r₁₀ : (ComplexShape.up ℕ).Rel 0 1 := rfl
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right r₁₀ (fun l ↦ by simp),
      inhomogeneousCochains.d_def]
    simp [homotopyOfDCompEqHom, hd₀]
  · have r₂₁ : (ComplexShape.up ℕ).Rel n (n + 1) := rfl
    have r₁₀ : (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) := rfl
    rw [Homotopy.nullHomotopicMap'_f r₂₁ r₁₀, inhomogeneousCochains.d_def,
      inhomogeneousCochains.d_def]
    have hsign : (-1 : k) ^ (n + 1 + 1) * (-1) ^ n = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    have hneg : (-1 : k) ^ (n + 1 + 1) = -(-1) ^ (n + 1) := by rw [pow_succ, mul_neg_one]
    simp only [homotopyOfDCompEqHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, Linear.smul_comp, Linear.comp_smul, hd, smul_add, smul_smul, hsign,
      one_smul, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply, ofDegreeZero_f_succ,
      sub_zero]
    rw [hneg, neg_smul]
    abel

/-- **The contraction defined by an operator lowering the degree.** If
`h ∘ d = d ∘ h + (-1)^n` on `(n + 1)`-cochains and `h ∘ d = P - 1` on `0`-cochains, then the
identity of the complex of inhomogeneous cochains is homotopic to `P` placed in degree `0`,
through the homotopy whose component from degree `n + 1` to degree `n` is `(-1)^(n+1) • h n`
(`TauCeti.groupCohomology.homotopyOfDCompEq_hom_succ`). -/
def homotopyOfDCompEq :
    Homotopy (𝟙 (inhomogeneousCochains A)) (ofDegreeZero P (comp_d_zero_eq_zero hd hd₀)) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_ofDegreeZero_eq_nullHomotopicMap' hd hd₀)).trans
      (Homotopy.nullHomotopy' _)

/-- The component of `TauCeti.groupCohomology.homotopyOfDCompEq` from degree `n + 1` to degree
`n` is `(-1)^(n+1) • h n`. -/
@[simp]
theorem homotopyOfDCompEq_hom_succ (n : ℕ) :
    (homotopyOfDCompEq hd hd₀).hom (n + 1) n = (-1 : k) ^ (n + 1) • h n := by
  simp [homotopyOfDCompEq, Homotopy.equivSubZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.nullHomotopy'_hom, homotopyOfDCompEqHom]

end TauCeti.groupCohomology
