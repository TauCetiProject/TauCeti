/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.Algebra.Homology.CochainComplex.OfDegreeZero

/-!
# Contractions of inhomogeneous cochains from operators lowering the degree

Let `A` be a `k`-linear representation of a group `G`, and let
`h n : Cⁿ⁺¹(G, A) → Cⁿ(G, A)` be linear maps between the inhomogeneous cochains satisfying
$$h \circ d = d \circ h + (-1)^n \text{ on } (n + 1)\text{-cochains}, \qquad
  h \circ d = P - 1 \text{ on } 0\text{-cochains}$$
for an endomorphism `P` of the `0`-cochains. The maps `(-1)^(n+1) • h n` then satisfy the
sign-free identities of `CochainComplex.homotopyOfDCompEq`. So `P` is a cochain map when placed in
degree `0` (`TauCeti.groupCohomology.comp_d_zero_eq_zero`), and the maps `(-1)^(n+1) • h n` form a
homotopy from the identity of `inhomogeneousCochains A` to it. Every positive-degree cocycle `f` is
the coboundary of `(-1)^(n+1) h f`.

This is the formal part shared by the contractions that insert a last argument: averaging over a
finite group (`TauCeti.inhomogeneousCochains.averageLast`) and weighting by a cutoff function
(`TauCeti.inhomogeneousCochains.cutoffLast`).

## Main declarations

* `TauCeti.inhomogeneousCochains.d_smul_of_d_comp_eq`: the explicit primitive of a
  positive-degree cocycle.
* `TauCeti.groupCohomology.homotopyOfDCompEq`: the homotopy from the identity to `P` placed in
  degree `0` by `CochainComplex.ofDegreeZero`.
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
variable {h : ∀ n : ℕ, ModuleCat.of k ((Fin (n + 1) → G) → A) ⟶ ModuleCat.of k ((Fin n → G) → A)}
variable (hd : ∀ n : ℕ, d A (n + 1) ≫ h (n + 1) = h n ≫ d A n + (-1 : k) ^ n • 𝟙 _)
  (hd₀ : d A 0 ≫ h 0 = P - 𝟙 _)

/-- If `h ∘ d = d ∘ h + (-1)^n` on `(n + 1)`-cochains, then the maps `(-1)^(m+1) • h m` satisfy
`d ∘ h + h ∘ d = 1` on `(n + 1)`-cochains, the identity of `CochainComplex.homotopyOfDCompEq`. -/
private theorem d_comp_smul_add_smul_comp_d {n : ℕ}
    (hd : d A (n + 1) ≫ h (n + 1) = h n ≫ d A n + (-1 : k) ^ n • 𝟙 _) :
    (inhomogeneousCochains A).d (n + 1) (n + 1 + 1) ≫ ((-1 : k) ^ (n + 1 + 1) • h (n + 1)) +
      ((-1 : k) ^ (n + 1) • h n) ≫ (inhomogeneousCochains A).d n (n + 1) = 𝟙 _ := by
  have hsign : (-1 : k) ^ (n + 1 + 1) * (-1) ^ n = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n + 1, by ring⟩
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def, Linear.comp_smul,
    Linear.smul_comp, hd, smul_add, smul_smul, hsign, one_smul, pow_succ (-1 : k) (n + 1),
    mul_neg_one, neg_smul]
  abel

include hd₀ in
/-- If `h ∘ d = P - 1` on `0`-cochains, then `-h ∘ d = 1 - P`, the identity of
`CochainComplex.homotopyOfDCompEq` in degree `0`. -/
private theorem d_comp_neg_one_pow_smul_zero :
    (inhomogeneousCochains A).d 0 1 ≫ ((-1 : k) ^ (0 + 1) • h 0) = 𝟙 _ - P := by
  rw [inhomogeneousCochains.d_def, Linear.comp_smul, hd₀, zero_add, pow_one, neg_one_smul,
    neg_sub]

include hd hd₀ in
/-- If `h ∘ d = d ∘ h + (-1)^n` on positive-degree cochains and `h ∘ d = P - 1` on
`0`-cochains, then the composite of `P` with the differential vanishes. -/
theorem comp_d_zero_eq_zero : P ≫ (inhomogeneousCochains A).d 0 1 = 0 :=
  CochainComplex.comp_d_zero_eq_zero_of_d_comp_eq (K := inhomogeneousCochains A)
    (h := fun m ↦ (-1 : k) ^ (m + 1) • h m)
    (fun n ↦ d_comp_smul_add_smul_comp_d (hd n))
    (d_comp_neg_one_pow_smul_zero hd₀)

/-- **The contraction defined by an operator lowering the degree.** If
`h ∘ d = d ∘ h + (-1)^n` on `(n + 1)`-cochains and `h ∘ d = P - 1` on `0`-cochains, then the
identity of the complex of inhomogeneous cochains is homotopic to `P` placed in degree `0`,
through the homotopy whose component from degree `n + 1` to degree `n` is `(-1)^(n+1) • h n`
(`TauCeti.groupCohomology.homotopyOfDCompEq_hom_succ`). -/
def homotopyOfDCompEq :
    Homotopy (𝟙 (inhomogeneousCochains A))
      ((inhomogeneousCochains A).ofDegreeZero P (comp_d_zero_eq_zero hd hd₀)) :=
  CochainComplex.homotopyOfDCompEq (K := inhomogeneousCochains A)
    (h := fun m ↦ (-1 : k) ^ (m + 1) • h m)
    (fun n ↦ d_comp_smul_add_smul_comp_d (hd n))
    (d_comp_neg_one_pow_smul_zero hd₀)

/-- The component of `TauCeti.groupCohomology.homotopyOfDCompEq` from degree `n + 1` to degree
`n` is `(-1)^(n+1) • h n`. -/
@[simp]
theorem homotopyOfDCompEq_hom_succ (n : ℕ) :
    (homotopyOfDCompEq hd hd₀).hom (n + 1) n = (-1 : k) ^ (n + 1) • h n :=
  CochainComplex.homotopyOfDCompEq_hom_succ (K := inhomogeneousCochains A)
    (h := fun m ↦ (-1 : k) ^ (m + 1) • h m) _ _ n

end TauCeti.groupCohomology
