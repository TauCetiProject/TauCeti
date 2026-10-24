/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Bilinear
public import TauCeti.RingTheory.NovikovSeries.Grading

/-!
# Homogeneous completed combinations and supported products

A degree function on lifted generators defines homogeneous pieces of a completed Novikov
module. These are ground-ring submodules, rather than a direct-sum decomposition of the whole
completion. In torsor coordinates the degree of a coefficient is the total degree minus the
degree of the reference lift. Consequently changing reference lifts preserves total degree,
and homogeneous Novikov scalars act by adding their degree.

A supported bilinear kernel with a fixed degree shift extends to a product with that same
shift on homogeneous completed combinations. Its coordinate matrix has the corresponding
reference-degree shifts. These results apply to the supported kernel construction of
`TauCeti.NovikovModule.kernelProduct`; they do not require discrete or injective periods.

The coordinate construction follows `TauCeti.NovikovModule.coordinates`, and the coefficient
pieces are `TauCeti.NovikovSeries.gradeBy`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

variable {R S D : Type*}

section Semiring

variable [Semiring R] {F : S → ℝ}

variable (R F) in
/-- Completed combinations supported on generators of degree `k`. An arbitrary completed
combination need not be a finite sum of such homogeneous combinations. -/
def gradeBy (d : S → D) (k : D) :
    Submodule R (NovikovModule R F) where
  carrier := {a | ∀ s, a.val s ≠ 0 → d s = k}
  zero_mem' := by simp
  add_mem' {a b} ha hb s hs := by
    by_cases h : a.val s = (0 : R)
    · exact hb s (by simpa [h] using hs)
    · exact ha s h
  smul_mem' r a ha s hs := ha s (fun h => hs (by simp [h]))

/-- Homogeneity means that every generator with nonzero coefficient has the stated degree. -/
@[simp]
theorem mem_gradeBy_iff {d : S → D} {k : D} {a : NovikovModule R F} :
    a ∈ gradeBy R F d k ↔ ∀ s, a.val s ≠ 0 → d s = k := Iff.rfl

/-- A homogeneous combination vanishes on generators of a different degree. -/
theorem val_eq_zero_of_mem_gradeBy {d : S → D} {k : D} {a : NovikovModule R F}
    (ha : a ∈ gradeBy R F d k) {s : S} (hs : d s ≠ k) : a.val s = 0 :=
  by_contra fun h => hs (ha s h)

/-- An affine reversal of generator degrees relabels the same homogeneous pieces. -/
@[simp]
theorem gradeBy_sub [AddCommGroup D] (d : S → D) (n k : D) :
    gradeBy R F (fun s => n - d s) k = gradeBy R F d (n - k) := by
  ext a
  simp only [mem_gradeBy_iff]
  constructor <;> intro ha s hs
  · simpa only [sub_sub_cancel] using congrArg (fun x => n - x) (ha s hs)
  · rw [ha s hs, sub_sub_cancel]

section Coordinates

variable {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*}
  [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
  [AddGroup D] (δ : H →+ D) {d : (Σ i, P i) → D}
  (hd : ∀ i h (p : P i), d ⟨i, h +ᵥ p⟩ = δ h + d ⟨i, p⟩)

include hd

/-- In any reference lifts, total degree `k` means that the coordinate in orbit `i` has
coefficient degree `k - d (r i)`. This characterizes the same piece for every choice of lifts. -/
theorem mem_gradeBy_iff_coordinates (r : ∀ i, P i) {k : D} {a : NovikovModule R F} :
    a ∈ gradeBy R F d k ↔
      ∀ i, coordinates hF r a i ∈ NovikovSeries.gradeBy R N δ (k - d ⟨i, r i⟩) := by
  simp only [mem_gradeBy_iff, NovikovSeries.mem_gradeBy_iff]
  constructor
  · intro ha i h hh
    have hm := ha ⟨i, h +ᵥ r i⟩
      (by simpa only [coordinates_coeff] using NovikovSeries.mem_support.mp hh)
    rw [hd] at hm
    exact eq_sub_iff_add_eq.mpr hm
  · intro ha ⟨i, p⟩ hp
    have hm := ha i (NovikovSeries.mem_support.mpr (show
      (coordinates hF r a i).coeff (p -ᵥ r i) ≠ 0 by simpa using hp))
    have he := hd i (p -ᵥ r i) (r i)
    rw [vsub_vadd] at he
    exact he.trans (eq_sub_iff_add_eq.mp hm)

/-- The basis vector of a chosen lift has precisely the degree of that lift. -/
theorem basis_mem_gradeBy (r : ∀ i, P i) (i : ι) :
    basis (R := R) hF r i ∈ gradeBy R F d (d ⟨i, r i⟩) := by
  classical
  rw [mem_gradeBy_iff_coordinates hF δ hd r]
  intro j
  rw [coordinates_basis]
  by_cases hij : i = j
  · subst j
    simpa only [Pi.single_eq_same, sub_self, ← NovikovSeries.single_zero_one, map_zero] using
      NovikovSeries.single_mem_gradeBy (N := N) δ (0 : H) (1 : R)
  · simp [Pi.single_eq_of_ne (Ne.symm hij)]

/-- A homogeneous Novikov scalar adds its degree to the total degree of a completed
combination, for the lift-independent Novikov module structure. -/
theorem smul_mem_gradeBy {j k : D} {b : NovikovSeries R H N} {a : NovikovModule R F}
    (hb : b ∈ NovikovSeries.gradeBy R N δ j) (ha : a ∈ gradeBy R F d k) :
    letI := module (R := R) hF
    b • a ∈ gradeBy R F d (j + k) := by
  let := module (R := R) hF
  let r := fun i => Classical.arbitrary (P i)
  rw [mem_gradeBy_iff_coordinates hF δ hd r] at ha ⊢
  intro i
  rw [coordinates_smul, Pi.smul_apply, smul_eq_mul]
  simpa only [add_sub_assoc] using SetLike.mul_mem_graded hb (ha i)

end Coordinates

end Semiring

section Kernel

variable [CommSemiring R] {S₁ S₂ S₀ : Type*}
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C : ℝ} {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  [Add D] {d₁ : S₁ → D} {d₂ : S₂ → D} {d₀ : S₀ → D} {ε : D}

/-- A supported kernel whose nonzero coefficients have degree shift `ε` gives a product
with the same shift on homogeneous completed inputs. -/
theorem kernelProduct_mem_gradeBy
    (hd : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂ + ε)
    {j k : D} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ d₁ j) (hb : b ∈ gradeBy R F₂ d₂ k) :
    kernelProduct hn hfin a b ∈ gradeBy R F₀ d₀ (j + k + ε) := by
  rw [mem_gradeBy_iff] at ha hb ⊢
  intro p₀ hp₀
  rw [kernelProduct_apply_val] at hp₀
  obtain ⟨⟨p₁, p₂⟩, hp⟩ : ∃ q : S₁ × S₂,
      a.val q.1 * b.val q.2 * n q.1 q.2 p₀ ≠ 0 := by
    by_contra! h
    exact hp₀ (finsum_eq_zero_of_forall_eq_zero h)
  rw [hd p₁ p₂ p₀ (right_ne_zero_of_mul hp),
    ha p₁ (left_ne_zero_of_mul (left_ne_zero_of_mul hp)),
    hb p₂ (right_ne_zero_of_mul (left_ne_zero_of_mul hp))]

end Kernel

section Matrix

variable [Semiring R] {H ι₁ ι₂ ι₀ : Type*} [AddGroup H] [Finite ι₀]
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ k, AddTorsor H (P₀ k)] {N : H →+ ℝ}
  {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  {n : (Σ i, P₁ i) → (Σ j, P₂ j) → (Σ k, P₀ k) → R}
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  [AddGroup D] (δ : H →+ D)
  {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ j, P₂ j) → D} {d₀ : (Σ k, P₀ k) → D}
  (hd₀ : ∀ k h (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)

include hd₀

/-- Each coordinate matrix entry of a kernel has coefficient degree equal to the sum of
its input reference degrees and its shift, minus its output reference degree. -/
theorem kernelMatrix_mem_gradeBy {ε : D}
    (hd : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂ + ε)
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k) (i : ι₁) (j : ι₂) (k : ι₀) :
    kernelMatrix hF₀ hfin r₁ r₂ r₀ i j k ∈ NovikovSeries.gradeBy R N δ
      (d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩ + ε - d₀ ⟨k, r₀ k⟩) := by
  rw [NovikovSeries.mem_gradeBy_iff]
  intro h hh
  have hm := hd ⟨i, r₁ i⟩ ⟨j, r₂ j⟩ ⟨k, h +ᵥ r₀ k⟩
    (by simpa only [kernelMatrix_coeff] using NovikovSeries.mem_support.mp hh)
  rw [hd₀] at hm
  exact eq_sub_iff_add_eq.mpr hm

end Matrix

end TauCeti.NovikovModule
