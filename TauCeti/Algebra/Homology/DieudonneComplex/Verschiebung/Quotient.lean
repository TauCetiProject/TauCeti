/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DieudonneComplex.Verschiebung.Filtration
import Mathlib.Tactic.Abel

/-!
# The finite Verschiebung quotients of a saturated Dieudonné complex

For a saturated Dieudonné complex `M` and `r : ℕ`, the quotients `W_r(M)ⁿ = Mⁿ / Nʳ Mⁿ` by the
Verschiebung filtration `Nʳ Mⁿ = im Vʳ + im (d Vʳ)` form a cochain complex `W_r(M)`, with
differential induced by `d`. (Here `W_r` is a quotient of a Dieudonné complex, not a ring of
truncated Witt vectors.) These complexes come with

* the projections `M → W_r(M)`, through which every map out of `M` vanishing on `Nʳ M` factors;
* the restriction cochain maps `R : W_{r+1}(M) → W_r(M)`, induced by the identity of `M`;
* the Frobenius `F : W_{r+1}(M)ⁿ → W_r(M)ⁿ` and the Verschiebung `V : W_r(M)ⁿ → W_{r+1}(M)ⁿ`,
  induced by `F` and `V` on `M`;
* the maps `W_r(f) : W_r(M) → W_r(N)` induced by morphisms `f : M → N`.

They satisfy `FV = VF = p`, `d F = p F d`, `V d = p d V`, `F d V = d`, `F` and `V` commute with
`R`, the kernel of `R` is the `p`-torsion, a class whose differential is divisible by `p` lies in
the image of `F`, and `pʳ` kills `W_r(M)`. These are the identities of a strict Dieudonné tower
`⋯ → W_2(M) → W_1(M) → W_0(M) = 0` (Bhatt–Lurie–Mathew, Definition 2.6.1), from which the strict
completion of `M` is built; for the saturated de Rham–Witt complex of an `𝔽_p`-algebra the
`W_r(M)` are the de Rham–Witt complexes of finite level.

## Main definitions

* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotient`: the cochain complex `W_r(M)`.
* `TauCeti.DieudonneComplex.IsSaturated.toVerschiebungQuotient`: the projection `M ⟶ W_r(M)`.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientLift` and
  `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientDesc`: the maps out of `W_r(M)ⁿ` and
  `W_r(M)` induced by maps out of `M` that vanish on the Verschiebung filtration.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientRestriction`: the restriction
  `W_{r+1}(M) ⟶ W_r(M)`.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientF` and
  `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientV`: the Frobenius and Verschiebung
  between the finite quotients.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientMap`: the cochain map
  `W_r(f) : W_r(M) ⟶ W_r(N)` induced by a morphism `f : M ⟶ N`.

## Main results

* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientF_verschiebungQuotientV_apply`,
  `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientV_verschiebungQuotientF_apply`:
  `FV = VF = p` on the finite quotients.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotientRestriction_f_apply_eq_zero_iff`:
  the kernel of the restriction is the `p`-torsion.
* `TauCeti.DieudonneComplex.IsSaturated.mem_range_verschiebungQuotientF`: a class of
  `W_r(M)` whose differential is divisible by `p` is in the image of `F`.
* `TauCeti.DieudonneComplex.IsSaturated.verschiebungQuotient_pow_smul_eq_zero`: `pʳ` kills
  `W_r(M)`.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Construction 2.5.1, Remarks 2.5.2 and 2.5.3, Definition 2.6.1 and the proof
  of Proposition 2.6.2.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

namespace DieudonneComplex

namespace IsSaturated

variable {p : ℕ} {M : DieudonneComplex.{u} p} (hM : M.IsSaturated)
include hM

section Quotient

/-- The finite Verschiebung quotient `W_r(M)`: the cochain complex `Mⁿ / Nʳ Mⁿ` with the
differential induced by `d`. -/
noncomputable def verschiebungQuotient (r : ℕ) : CochainComplex AddCommGrpCat.{u} ℤ where
  X n := AddCommGrpCat.of (M.X n ⧸ hM.verschiebungFiltration r n)
  d i j := AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (M.d i j).hom (hM.verschiebungFiltration_le_comap_d r i j)
  shape i j h := by
    ext x
    simp [M.shape i j h]
  d_comp_d' i j k _ _ := by
    ext x
    simp

/-- The projection `M ⟶ W_r(M)`. -/
noncomputable def toVerschiebungQuotient (r : ℕ) :
    M.toCochainComplex ⟶ hM.verschiebungQuotient r where
  f _ := AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)
  comm' _ _ _ := rfl

/-- The projection `Mⁿ → W_r(M)ⁿ` is surjective. -/
lemma toVerschiebungQuotient_f_surjective (r : ℕ) (n : ℤ) :
    Function.Surjective ((hM.toVerschiebungQuotient r).f n).hom :=
  QuotientAddGroup.mk'_surjective _

/-- The kernel of the projection `Mⁿ → W_r(M)ⁿ` is `Nʳ Mⁿ`. -/
@[simp]
lemma ker_toVerschiebungQuotient_f (r : ℕ) (n : ℤ) :
    ((hM.toVerschiebungQuotient r).f n).hom.ker = hM.verschiebungFiltration r n :=
  QuotientAddGroup.ker_mk' _

/-- The class of `x` in `W_r(M)ⁿ` vanishes iff `x ∈ Nʳ Mⁿ`. -/
@[simp]
lemma toVerschiebungQuotient_f_apply_eq_zero_iff {r : ℕ} {n : ℤ} {x : M.X n} :
    ((hM.toVerschiebungQuotient r).f n).hom x = 0 ↔ x ∈ hM.verschiebungFiltration r n :=
  QuotientAddGroup.eq_zero_iff x

/-- Two elements of `Mⁿ` have the same class in `W_r(M)ⁿ` iff their difference lies in
`Nʳ Mⁿ`. -/
lemma toVerschiebungQuotient_f_apply_eq_iff {r : ℕ} {n : ℤ} {x y : M.X n} :
    ((hM.toVerschiebungQuotient r).f n).hom x = ((hM.toVerschiebungQuotient r).f n).hom y ↔
      x - y ∈ hM.verschiebungFiltration r n := by
  rw [← sub_eq_zero, ← map_sub, toVerschiebungQuotient_f_apply_eq_zero_iff]

/-- The differential of `W_r(M)` on the class of `x` is the class of `d x`. -/
@[simp]
lemma verschiebungQuotient_d_toVerschiebungQuotient_f_apply (r : ℕ) {i j : ℤ} (x : M.X i) :
    ((hM.verschiebungQuotient r).d i j).hom (((hM.toVerschiebungQuotient r).f i).hom x) =
      ((hM.toVerschiebungQuotient r).f j).hom ((M.d i j).hom x) :=
  (rfl)

/-- Every class in `W_r(M)ⁿ` is killed by `pʳ`. -/
lemma verschiebungQuotient_pow_smul_eq_zero {r : ℕ} {n : ℤ} (y : (hM.verschiebungQuotient r).X n) :
    p ^ r • y = 0 := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  rw [← map_nsmul, toVerschiebungQuotient_f_apply_eq_zero_iff]
  exact hM.pow_smul_mem_verschiebungFiltration r x

/-- `W_0(M)` is zero. -/
instance (n : ℤ) : Subsingleton ((hM.verschiebungQuotient 0).X n) where
  allEq y z := by
    obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective 0 n y
    obtain ⟨x', rfl⟩ := hM.toVerschiebungQuotient_f_surjective 0 n z
    simp [toVerschiebungQuotient_f_apply_eq_iff]

end Quotient

section Desc

/-- A homomorphism `g` out of `Mⁿ` that vanishes on `Nʳ Mⁿ` descends to `W_r(M)ⁿ`. -/
noncomputable def verschiebungQuotientLift {A : Type*} [AddMonoid A] (r : ℕ) (n : ℤ)
    (g : M.X n →+ A) (hg : hM.verschiebungFiltration r n ≤ g.ker) :
    (hM.verschiebungQuotient r).X n →+ A :=
  QuotientAddGroup.lift _ g hg

/-- The lift of `g` sends the class of `x` to `g x`. -/
@[simp]
lemma verschiebungQuotientLift_apply {A : Type*} [AddMonoid A] (r : ℕ) {n : ℤ} (g : M.X n →+ A)
    (hg : hM.verschiebungFiltration r n ≤ g.ker) (x : M.X n) :
    hM.verschiebungQuotientLift r n g hg (((hM.toVerschiebungQuotient r).f n).hom x) = g x :=
  (rfl)

/-- The cochain map `W_r(M) ⟶ K` induced by a cochain map `g : M ⟶ K` that vanishes on the
Verschiebung filtration `Nʳ M`. -/
noncomputable def verschiebungQuotientDesc (r : ℕ) {K : CochainComplex AddCommGrpCat.{u} ℤ}
    (g : M.toCochainComplex ⟶ K) (hg : ∀ n, hM.verschiebungFiltration r n ≤ (g.f n).hom.ker) :
    hM.verschiebungQuotient r ⟶ K where
  f n := AddCommGrpCat.ofHom (hM.verschiebungQuotientLift r n (g.f n).hom (hg n))
  comm' i j _ := by
    ext y
    obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r i y
    exact ConcreteCategory.congr_hom (g.comm i j) x

/-- The descended cochain map sends the class of `x` to `g x`. -/
@[simp]
lemma verschiebungQuotientDesc_f_apply (r : ℕ) {K : CochainComplex AddCommGrpCat.{u} ℤ}
    (g : M.toCochainComplex ⟶ K) (hg : ∀ n, hM.verschiebungFiltration r n ≤ (g.f n).hom.ker)
    {n : ℤ} (x : M.X n) :
    ((hM.verschiebungQuotientDesc r g hg).f n).hom (((hM.toVerschiebungQuotient r).f n).hom x) =
      (g.f n).hom x :=
  (rfl)

@[reassoc (attr := simp)]
lemma toVerschiebungQuotient_comp_verschiebungQuotientDesc (r : ℕ)
    {K : CochainComplex AddCommGrpCat.{u} ℤ} (g : M.toCochainComplex ⟶ K)
    (hg : ∀ n, hM.verschiebungFiltration r n ≤ (g.f n).hom.ker) :
    hM.toVerschiebungQuotient r ≫ hM.verschiebungQuotientDesc r g hg = g :=
  (rfl)

/-- Cochain maps out of `W_r(M)` are determined by their composites with the projection
`M ⟶ W_r(M)`. -/
lemma verschiebungQuotient_hom_ext {r : ℕ} {K : CochainComplex AddCommGrpCat.{u} ℤ}
    {φ ψ : hM.verschiebungQuotient r ⟶ K}
    (h : hM.toVerschiebungQuotient r ≫ φ = hM.toVerschiebungQuotient r ≫ ψ) : φ = ψ := by
  ext n y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h n) x

end Desc

section Restriction

/-- The restriction `R : W_{r+1}(M) ⟶ W_r(M)`, induced by the identity of `M`. -/
noncomputable def verschiebungQuotientRestriction (r : ℕ) :
    hM.verschiebungQuotient (r + 1) ⟶ hM.verschiebungQuotient r where
  f n := AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (AddMonoidHom.id _)
      ((hM.verschiebungFiltration_succ_le r n).trans (AddSubgroup.comap_id _).ge)
  comm' i _ _ := by
    ext y
    obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) i y
    rfl

/-- The restriction sends the class of `x` at level `r + 1` to its class at level `r`. -/
@[simp]
lemma verschiebungQuotientRestriction_f_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    ((hM.verschiebungQuotientRestriction r).f n).hom
        (((hM.toVerschiebungQuotient (r + 1)).f n).hom x) =
      ((hM.toVerschiebungQuotient r).f n).hom x :=
  (rfl)

@[reassoc (attr := simp)]
lemma toVerschiebungQuotient_comp_verschiebungQuotientRestriction (r : ℕ) :
    hM.toVerschiebungQuotient (r + 1) ≫ hM.verschiebungQuotientRestriction r =
      hM.toVerschiebungQuotient r :=
  (rfl)

/-- The restriction `W_{r+1}(M)ⁿ → W_r(M)ⁿ` is surjective. -/
lemma verschiebungQuotientRestriction_f_surjective (r : ℕ) (n : ℤ) :
    Function.Surjective ((hM.verschiebungQuotientRestriction r).f n).hom := fun y ↦ by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  exact ⟨_, hM.verschiebungQuotientRestriction_f_apply r x⟩

/-- The kernel of the restriction `W_{r+1}(M)ⁿ → W_r(M)ⁿ` is the `p`-torsion. -/
lemma verschiebungQuotientRestriction_f_apply_eq_zero_iff {r : ℕ} {n : ℤ}
    {y : (hM.verschiebungQuotient (r + 1)).X n} :
    ((hM.verschiebungQuotientRestriction r).f n).hom y = 0 ↔ p • y = 0 := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) n y
  rw [verschiebungQuotientRestriction_f_apply, ← map_nsmul,
    toVerschiebungQuotient_f_apply_eq_zero_iff, toVerschiebungQuotient_f_apply_eq_zero_iff,
    smul_mem_verschiebungFiltration_succ_iff]

end Restriction

section Frobenius

/-- The Frobenius `F : W_{r+1}(M)ⁿ → W_r(M)ⁿ`, induced by the Frobenius of `M`. -/
noncomputable def verschiebungQuotientF (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotient (r + 1)).X n ⟶ (hM.verschiebungQuotient r).X n :=
  AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (M.F n).hom (hM.verschiebungFiltration_succ_le_comap_F r n)

/-- The Frobenius sends the class of `x` at level `r + 1` to the class of `F x` at level `r`. -/
@[simp]
lemma verschiebungQuotientF_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    (hM.verschiebungQuotientF r n).hom (((hM.toVerschiebungQuotient (r + 1)).f n).hom x) =
      ((hM.toVerschiebungQuotient r).f n).hom ((M.F n).hom x) :=
  (rfl)

/-- The Verschiebung `V : W_r(M)ⁿ → W_{r+1}(M)ⁿ`, induced by the Verschiebung of `M`. -/
noncomputable def verschiebungQuotientV (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotient r).X n ⟶ (hM.verschiebungQuotient (r + 1)).X n :=
  AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (hM.V n).hom (hM.verschiebungFiltration_le_comap_V r n)

/-- The Verschiebung sends the class of `x` at level `r` to the class of `V x` at level
`r + 1`. -/
@[simp]
lemma verschiebungQuotientV_apply (r : ℕ) {n : ℤ} (x : M.X n) :
    (hM.verschiebungQuotientV r n).hom (((hM.toVerschiebungQuotient r).f n).hom x) =
      ((hM.toVerschiebungQuotient (r + 1)).f n).hom ((hM.V n).hom x) :=
  (rfl)

/-- `d F = p F d` on the finite quotients. -/
lemma verschiebungQuotient_d_verschiebungQuotientF_apply (r : ℕ) {i j : ℤ}
    (y : (hM.verschiebungQuotient (r + 1)).X i) :
    ((hM.verschiebungQuotient r).d i j).hom ((hM.verschiebungQuotientF r i).hom y) =
      p • (hM.verschiebungQuotientF r j).hom (((hM.verschiebungQuotient (r + 1)).d i j).hom y) := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) i y
  simp [M.d_F_apply, ← map_nsmul]

/-- `V d = p d V` on the finite quotients. -/
lemma verschiebungQuotientV_verschiebungQuotient_d_apply (r : ℕ) {i j : ℤ}
    (y : (hM.verschiebungQuotient r).X i) :
    (hM.verschiebungQuotientV r j).hom (((hM.verschiebungQuotient r).d i j).hom y) =
      p • ((hM.verschiebungQuotient (r + 1)).d i j).hom ((hM.verschiebungQuotientV r i).hom y) := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r i y
  simp [V_d_apply, ← map_nsmul]

/-- `F d V = d` on the finite quotients. -/
@[simp]
lemma verschiebungQuotientF_d_verschiebungQuotientV_apply (r : ℕ) {i j : ℤ}
    (y : (hM.verschiebungQuotient r).X i) :
    (hM.verschiebungQuotientF r j).hom
        (((hM.verschiebungQuotient (r + 1)).d i j).hom ((hM.verschiebungQuotientV r i).hom y)) =
      ((hM.verschiebungQuotient r).d i j).hom y := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r i y
  simp

/-- `F V = p` on the finite quotients. -/
@[simp]
lemma verschiebungQuotientF_verschiebungQuotientV_apply (r : ℕ) {n : ℤ}
    (y : (hM.verschiebungQuotient r).X n) :
    (hM.verschiebungQuotientF r n).hom ((hM.verschiebungQuotientV r n).hom y) = p • y := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  simp [← map_nsmul]

/-- `V F = p` on the finite quotients. -/
@[simp]
lemma verschiebungQuotientV_verschiebungQuotientF_apply (r : ℕ) {n : ℤ}
    (y : (hM.verschiebungQuotient (r + 1)).X n) :
    (hM.verschiebungQuotientV r n).hom ((hM.verschiebungQuotientF r n).hom y) = p • y := by
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) n y
  simp [← map_nsmul]

/-- The Frobenius commutes with the restriction. -/
@[reassoc]
lemma verschiebungQuotientF_comp_verschiebungQuotientRestriction (r : ℕ) (n : ℤ) :
    hM.verschiebungQuotientF (r + 1) n ≫ (hM.verschiebungQuotientRestriction r).f n =
      (hM.verschiebungQuotientRestriction (r + 1)).f n ≫ hM.verschiebungQuotientF r n := by
  ext y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 2) n y
  rfl

/-- The Verschiebung commutes with the restriction. -/
@[reassoc]
lemma verschiebungQuotientV_comp_verschiebungQuotientRestriction (r : ℕ) (n : ℤ) :
    hM.verschiebungQuotientV (r + 1) n ≫ (hM.verschiebungQuotientRestriction (r + 1)).f n =
      (hM.verschiebungQuotientRestriction r).f n ≫ hM.verschiebungQuotientV r n := by
  ext y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) n y
  rfl

/-- A class of `W_r(M)ⁿ` whose differential is divisible by `p` is in the image of the Frobenius
`W_{r+1}(M)ⁿ → W_r(M)ⁿ`. -/
lemma mem_range_verschiebungQuotientF {r : ℕ} {n : ℤ} {y : (hM.verschiebungQuotient r).X n}
    (hy : ∃ z, p • z = ((hM.verschiebungQuotient r).d n (n + 1)).hom y) :
    y ∈ (hM.verschiebungQuotientF r n).hom.range := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  obtain ⟨w, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r (n + 1) z
  cases r with
  | zero => exact ⟨0, Subsingleton.elim _ _⟩
  | succ r =>
    -- Write `p • w - d x = Vʳ⁺¹ a + d (Vʳ⁺¹ b)`.
    rw [← map_nsmul, verschiebungQuotient_d_toVerschiebungQuotient_f_apply,
      toVerschiebungQuotient_f_apply_eq_iff, hM.mem_verschiebungFiltration_iff rfl] at hz
    obtain ⟨a, b, hab⟩ := hz
    -- Applying `d` gives `d (Vʳ⁺¹ a) = p • d w`, so `a = F a'`.
    obtain ⟨a', rfl⟩ := hM.mem_range_F_of_V_iterate_add_d_V_iterate_eq (c := -x)
      (by rw [hab, map_neg, sub_eq_add_neg])
    rw [hM.V_iterate_succ_F_apply] at hab
    -- Then `d (x + Vʳ⁺¹ b) = p • (w - Vʳ a')`, so `x + Vʳ⁺¹ b = F x'`.
    obtain ⟨x', hx'⟩ :=
      (hM.mem_range_F_iff (x := x + (⇑(hM.V n).hom)^[r + 1] b)).2
        ⟨w - (⇑(hM.V (n + 1)).hom)^[r] a', by
          rw [map_add, smul_sub, ← eq_sub_iff_add_eq.1 hab]
          abel⟩
    refine ⟨((hM.toVerschiebungQuotient (r + 2)).f n).hom x', ?_⟩
    rw [verschiebungQuotientF_apply, hx', toVerschiebungQuotient_f_apply_eq_iff,
      add_sub_cancel_left]
    exact hM.V_iterate_mem_verschiebungFiltration (r + 1) b

end Frobenius

section Functoriality

variable {N K : DieudonneComplex.{u} p} (hN : N.IsSaturated) (hK : K.IsSaturated)

/-- The cochain map `W_r(f) : W_r(M) ⟶ W_r(N)` induced by a morphism `f : M ⟶ N` of saturated
Dieudonné complexes. -/
noncomputable def verschiebungQuotientMap (f : M ⟶ N) (r : ℕ) :
    hM.verschiebungQuotient r ⟶ hN.verschiebungQuotient r where
  f n := AddCommGrpCat.ofHom <|
    QuotientAddGroup.map _ _ (f.hom.f n).hom (hM.verschiebungFiltration_le_comap hN f r n)
  comm' i j _ := by
    ext y
    obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r i y
    exact congrArg (QuotientAddGroup.mk' _) (ConcreteCategory.congr_hom (f.hom.comm i j) x)

/-- `W_r(f)` sends the class of `x` to the class of `f x`. -/
@[simp]
lemma verschiebungQuotientMap_f_apply (f : M ⟶ N) (r : ℕ) {n : ℤ} (x : M.X n) :
    ((hM.verschiebungQuotientMap hN f r).f n).hom (((hM.toVerschiebungQuotient r).f n).hom x) =
      ((hN.toVerschiebungQuotient r).f n).hom ((f.hom.f n).hom x) :=
  (rfl)

@[reassoc (attr := simp)]
lemma toVerschiebungQuotient_comp_verschiebungQuotientMap (f : M ⟶ N) (r : ℕ) :
    hM.toVerschiebungQuotient r ≫ hM.verschiebungQuotientMap hN f r =
      f.hom ≫ hN.toVerschiebungQuotient r :=
  (rfl)

@[simp]
lemma verschiebungQuotientMap_id (r : ℕ) :
    hM.verschiebungQuotientMap hM (𝟙 M) r = 𝟙 _ := by
  ext n y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  rfl

@[simp, reassoc]
lemma verschiebungQuotientMap_comp (f : M ⟶ N) (g : N ⟶ K) (r : ℕ) :
    hM.verschiebungQuotientMap hK (f ≫ g) r =
      hM.verschiebungQuotientMap hN f r ≫ hN.verschiebungQuotientMap hK g r := by
  ext n y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  rfl

/-- `W_r(f)` commutes with the restriction. -/
@[reassoc]
lemma verschiebungQuotientMap_comp_verschiebungQuotientRestriction (f : M ⟶ N) (r : ℕ) :
    hM.verschiebungQuotientMap hN f (r + 1) ≫ hN.verschiebungQuotientRestriction r =
      hM.verschiebungQuotientRestriction r ≫ hM.verschiebungQuotientMap hN f r := by
  ext n y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) n y
  rfl

/-- `W_r(f)` commutes with the Frobenius. -/
@[reassoc]
lemma verschiebungQuotientMap_f_comp_verschiebungQuotientF (f : M ⟶ N) (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotientMap hN f (r + 1)).f n ≫ hN.verschiebungQuotientF r n =
      hM.verschiebungQuotientF r n ≫ (hM.verschiebungQuotientMap hN f r).f n := by
  ext y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective (r + 1) n y
  simp [Hom.comm_F_apply]

/-- `W_r(f)` commutes with the Verschiebung. -/
@[reassoc]
lemma verschiebungQuotientMap_f_comp_verschiebungQuotientV (f : M ⟶ N) (r : ℕ) (n : ℤ) :
    (hM.verschiebungQuotientMap hN f r).f n ≫ hN.verschiebungQuotientV r n =
      hM.verschiebungQuotientV r n ≫ (hM.verschiebungQuotientMap hN f (r + 1)).f n := by
  ext y
  obtain ⟨x, rfl⟩ := hM.toVerschiebungQuotient_f_surjective r n y
  simp [Hom.comm_V_apply hM hN]

end Functoriality

end IsSaturated

end DieudonneComplex

end TauCeti
