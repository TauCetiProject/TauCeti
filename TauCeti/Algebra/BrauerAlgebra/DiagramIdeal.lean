/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import TauCeti.Algebra.BrauerAlgebra.Basic
public import TauCeti.Combinatorics.Brauer.PropagatingNumber

/-!
# The diagram ideals of the Brauer algebra

A Brauer diagram on `k` strands with propagating number `p` has `(k - p) / 2` caps along its
bottom row. For `j : ℕ`, the **diagram ideal** `I_j = TauCeti.BrauerAlgebra.diagramIdeal R δ k j`
of the Brauer algebra `B_k(δ)` is the span of the diagrams with at least `j` caps, that is, with
`propagatingNumber D + 2 * j ≤ k`. Stacking can only destroy through strands
(`TauCeti.BrauerDiagram.propagatingNumber_composeDiagram_le_left` and its mirror image), so these
spans absorb multiplication on both sides and are two-sided ideals. They form the decreasing
filtration

`B_k(δ) = I_0 ⊇ I_1 ⊇ I_2 ⊇ ⋯`, with `I_j = 0` once `2 * j > k`,

by which the trace filtration of the tensor power `V^{⊗k}` and the cell structure of the Brauer
algebra are organized.

The first step of the filtration splits off the symmetric group. A diagram lies outside `I_1`
exactly when it has no caps, that is, when it is a permutation diagram, and the
permutation diagrams multiply as the permutations do and close no loops. Reading off the
coefficients of the permutation diagrams is therefore an algebra map
`TauCeti.BrauerAlgebra.permProj : B_k(δ) → R[Sₖ]`. It is a retraction of the inclusion
`TauCeti.BrauerAlgebra.ofPerm` and its kernel is `I_1`, so that

`B_k(δ) / I_1 ≃ R[Sₖ]`

(`TauCeti.BrauerAlgebra.quotientDiagramIdealOneAlgEquiv`). Pulling back along `permProj` makes
every representation of `Sₖ`, in particular every Specht module, a representation of the Brauer
algebra on which the diagrams with a cap act by zero.

## Main definitions

* `TauCeti.BrauerAlgebra.diagramIdeal`: the two-sided ideal `I_j` spanned by the diagrams with at
  least `j` caps.
* `TauCeti.BrauerAlgebra.permProj`: the algebra map onto the group algebra of `Sₖ` reading off
  the coefficients of the permutation diagrams.
* `TauCeti.BrauerAlgebra.quotientDiagramIdealOneAlgEquiv`: the isomorphism `B_k(δ) / I_1 ≃ R[Sₖ]`.

## Main results

* `TauCeti.BrauerAlgebra.mem_diagramIdeal_iff` and
  `TauCeti.BrauerAlgebra.mem_diagramIdeal_iff_mem_span`: `I_j` consists of the elements supported
  on the diagrams with at least `j` caps, which is the span of those diagrams.
* `TauCeti.BrauerAlgebra.diagramIdeal_zero`, `TauCeti.BrauerAlgebra.diagramIdeal_antitone` and
  `TauCeti.BrauerAlgebra.diagramIdeal_eq_bot`: `I_0` is everything, the ideals decrease, and
  `I_j = 0` when `k < 2 * j`.
* `TauCeti.BrauerAlgebra.of_capCup_mem_diagramIdeal_one`: the cap-cup generators lie in `I_1`.
* `TauCeti.BrauerAlgebra.permProj_ofPerm`: `permProj` is a retraction of `ofPerm`.
* `TauCeti.BrauerAlgebra.ker_permProj`: the kernel of `permProj` is `I_1`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
* T. Halverson and T. N. Jacobson, *Set-partition tableaux and representations of diagram
  algebras*, Algebraic Combinatorics 3 (2020), 509-538, §2.4, for the ideals of a diagram algebra
  filtered by the propagating number.
-/

public section

namespace TauCeti

namespace BrauerAlgebra

open BrauerDiagram

/-! ### The diagram ideals -/

section Ideal

variable {R : Type*} [CommRing R] {δ : R} {k : ℕ}

/-- Stacking any diagrams above coefficients supported on the diagrams with at least `j` caps
keeps them supported there. -/
private theorem mulCoeff_mem_supported_right {j : ℕ} (f : BrauerDiagram k →₀ R)
    {g : BrauerDiagram k →₀ R}
    (hg : g ∈ Finsupp.supported R R {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k}) :
    mulCoeff δ f g ∈
      Finsupp.supported R R {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k} := by
  rw [Finsupp.supported_eq_span_single] at hg ⊢
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨D, hD, rfl⟩ := hg
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ h₁ h₂
    | single E a =>
      rw [mulCoeff_single_single, ← Finsupp.smul_single_one]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      have := propagatingNumber_composeDiagram_le_right E D
      simp only [Set.mem_ofPred_eq] at hD ⊢
      omega
  | zero => simp
  | add g₁ g₂ _ _ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  | smul r g _ h => simpa only [map_smul] using Submodule.smul_mem _ r h

/-- Stacking coefficients supported on the diagrams with at least `j` caps above any diagrams
keeps them supported there. -/
private theorem mulCoeff_mem_supported_left {j : ℕ} {f : BrauerDiagram k →₀ R}
    (hf : f ∈ Finsupp.supported R R {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k})
    (g : BrauerDiagram k →₀ R) :
    mulCoeff δ f g ∈
      Finsupp.supported R R {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k} := by
  rw [Finsupp.supported_eq_span_single] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨D, hD, rfl⟩ := hf
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    | single E a =>
      rw [mulCoeff_single_single, ← Finsupp.smul_single_one]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      have := propagatingNumber_composeDiagram_le_left D E
      simp only [Set.mem_ofPred_eq] at hD ⊢
      omega
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ h₁ h₂
  | smul r f _ h => simpa only [map_smul, LinearMap.smul_apply] using Submodule.smul_mem _ r h

variable (R δ k) in
/-- **The diagram ideal** `I_j` of the Brauer algebra: the elements supported on the diagrams
with at least `j` caps, `propagatingNumber D + 2 * j ≤ k`. It is a two-sided ideal because
stacking cannot raise the propagating number. -/
noncomputable def diagramIdeal (j : ℕ) : TwoSidedIdeal (BrauerAlgebra R δ k) :=
  .mk' {x | x.coeff ∈ Finsupp.supported R R {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k}}
    (by simp) (fun hx hy => by simpa using Submodule.add_mem _ hx hy)
    (fun hx => by
      simp only [Set.mem_ofPred_eq, coeff_neg] at hx ⊢
      exact Submodule.neg_mem _ hx)
    (fun hy => mulCoeff_mem_supported_right _ hy) (fun hx => mulCoeff_mem_supported_left hx _)

/-- An element lies in `I_j` exactly when every diagram in its support has at least `j` caps. -/
theorem mem_diagramIdeal_iff {j : ℕ} {x : BrauerAlgebra R δ k} :
    x ∈ diagramIdeal R δ k j ↔ ∀ D ∈ x.coeff.support, D.propagatingNumber + 2 * j ≤ k := by
  simp [diagramIdeal, Finsupp.mem_supported, Set.subset_def]

/-- **`I_j` is the span of the diagrams with at least `j` caps.** -/
theorem mem_diagramIdeal_iff_mem_span {j : ℕ} {x : BrauerAlgebra R δ k} :
    x ∈ diagramIdeal R δ k j ↔
      x ∈ Submodule.span R (of '' {D : BrauerDiagram k | D.propagatingNumber + 2 * j ≤ k}) := by
  have hof : ⇑(basis R δ k) = of := funext basis_apply
  rw [mem_diagramIdeal_iff, ← hof, (basis R δ k).mem_span_image, basis_repr, Set.subset_def]
  simp only [Finset.mem_coe, Set.mem_ofPred_eq]

/-- A diagram with at least `j` caps lies in `I_j`. -/
theorem of_mem_diagramIdeal {j : ℕ} {D : BrauerDiagram k}
    (hD : D.propagatingNumber + 2 * j ≤ k) : of D ∈ diagramIdeal R δ k j :=
  mem_diagramIdeal_iff_mem_span.mpr (Submodule.subset_span ⟨D, hD, rfl⟩)

/-- Over a nontrivial ring, a diagram lies in `I_j` exactly when it has at least `j` caps. -/
@[simp]
theorem of_mem_diagramIdeal_iff [Nontrivial R] {j : ℕ} {D : BrauerDiagram k} :
    of D ∈ diagramIdeal R δ k j ↔ D.propagatingNumber + 2 * j ≤ k := by
  simp [mem_diagramIdeal_iff]

/-- **A cap-cup generator lies in `I_1`**: it has exactly one cap. -/
theorem of_capCup_mem_diagramIdeal_one {a b : Fin k} (hab : a ≠ b) :
    of (capCup a b) ∈ diagramIdeal R δ k 1 :=
  of_mem_diagramIdeal <| by
    have := Fin.val_ne_of_ne hab
    rw [propagatingNumber_capCup hab]
    omega

variable (R δ k)

/-- **`I_0` is the whole Brauer algebra.** -/
@[simp]
theorem diagramIdeal_zero : diagramIdeal R δ k 0 = ⊤ :=
  eq_top_iff.mpr fun x _ => mem_diagramIdeal_iff.mpr fun D _ => by
    simpa using D.propagatingNumber_le

/-- **The diagram ideals decrease**: a diagram with at least `j'` caps has at least `j` caps for
`j ≤ j'`. -/
theorem diagramIdeal_antitone : Antitone (diagramIdeal R δ k) := fun _ _ hj _ hx =>
  mem_diagramIdeal_iff.mpr fun D hD => by
    have := mem_diagramIdeal_iff.mp hx D hD
    omega

/-- **`I_j = 0` once `2 * j > k`**: a diagram on `k` strands has at most `k / 2` caps. -/
theorem diagramIdeal_eq_bot {j : ℕ} (hj : k < 2 * j) : diagramIdeal R δ k j = ⊥ :=
  eq_bot_iff.mpr fun x hx => by
    rw [TwoSidedIdeal.mem_bot]
    refine ext <| Finsupp.ext fun D => by_contra fun hD => ?_
    have := mem_diagramIdeal_iff.mp hx D (Finsupp.mem_support_iff.mpr (by simpa using hD))
    omega

-- On one strand there is no room for a cap, and on two strands no room for two.
example : diagramIdeal R δ 1 1 = ⊥ := diagramIdeal_eq_bot R δ 1 (by norm_num)

example : diagramIdeal R δ 2 2 = ⊥ := diagramIdeal_eq_bot R δ 2 (by norm_num)

end Ideal

/-! ### The projection onto the group algebra of `Sₖ` -/

section Projection

variable {R : Type*} [CommSemiring R] {δ : R} {k : ℕ}

/-- The coefficients of the permutation diagrams in a single diagram: the group element of `σ`
for the permutation diagram of `σ`, and `0` for a diagram with a cap. -/
private noncomputable def permProjAux (D : BrauerDiagram k) :
    MonoidAlgebra R (Equiv.Perm (Fin k)) :=
  .ofCoeff
    (Finsupp.lcomapDomain (R := R) permToBrauer (permToBrauer_injective k) (Finsupp.single D 1))

private theorem coeff_permProjAux (D : BrauerDiagram k) (σ : Equiv.Perm (Fin k)) :
    (permProjAux (R := R) D).coeff σ = Finsupp.single D 1 (permToBrauer σ) := by
  simp [permProjAux]

private theorem permProjAux_permToBrauer (σ : Equiv.Perm (Fin k)) :
    permProjAux (R := R) (permToBrauer σ) = MonoidAlgebra.single σ 1 :=
  MonoidAlgebra.coeff_injective <| Finsupp.ext fun τ => by
    simp [coeff_permProjAux, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      (permToBrauer_injective k).eq_iff]

private theorem permProjAux_eq_zero {D : BrauerDiagram k}
    (hD : ∀ σ : Equiv.Perm (Fin k), D ≠ permToBrauer σ) : permProjAux (R := R) D = 0 :=
  MonoidAlgebra.coeff_injective <| Finsupp.ext fun σ => by
    simp [coeff_permProjAux, hD σ]

private theorem permProjAux_mul (D₁ D₂ : BrauerDiagram k) :
    permProjAux (R := R) D₁ * permProjAux D₂ =
      δ ^ middleLoopCount D₁ D₂ • permProjAux (composeDiagram D₁ D₂) := by
  by_cases h : ∃ ρ τ : Equiv.Perm (Fin k), D₁ = permToBrauer ρ ∧ D₂ = permToBrauer τ
  · obtain ⟨ρ, τ, rfl, rfl⟩ := h
    simp [permProjAux_permToBrauer, MonoidAlgebra.single_mul_single]
  · rw [permProjAux_eq_zero (D := composeDiagram D₁ D₂) fun σ hσ => h (by
      obtain ⟨ρ, τ, h₁, h₂, -⟩ := composeDiagram_eq_permToBrauer_iff.mp hσ
      exact ⟨ρ, τ, h₁, h₂⟩), smul_zero]
    by_cases h₁ : ∃ ρ : Equiv.Perm (Fin k), D₁ = permToBrauer ρ
    · obtain ⟨ρ, rfl⟩ := h₁
      rw [permProjAux_eq_zero (D := D₂) fun τ hτ => h ⟨ρ, τ, rfl, hτ⟩, mul_zero]
    · rw [permProjAux_eq_zero (D := D₁) fun ρ hρ => h₁ ⟨ρ, hρ⟩, zero_mul]

variable (R δ k) in
/-- **The projection onto the group algebra of `Sₖ`**: the algebra map reading off the
coefficients of the permutation diagrams. It kills every diagram with a cap, and it is a
retraction of `TauCeti.BrauerAlgebra.ofPerm` (`TauCeti.BrauerAlgebra.permProj_ofPerm`). -/
noncomputable def permProj : BrauerAlgebra R δ k →ₐ[R] MonoidAlgebra R (Equiv.Perm (Fin k)) :=
  lift permProjAux (permProjAux_permToBrauer 1) permProjAux_mul

/-- The projection sends the diagram of a permutation to the permutation. -/
@[simp]
theorem permProj_of_permToBrauer (σ : Equiv.Perm (Fin k)) :
    permProj R δ k (of (permToBrauer σ)) = MonoidAlgebra.single σ 1 := by
  rw [permProj, lift_of, permProjAux_permToBrauer]

/-- The projection kills every diagram that is not a permutation diagram. -/
theorem permProj_of_eq_zero {D : BrauerDiagram k}
    (hD : ∀ σ : Equiv.Perm (Fin k), D ≠ permToBrauer σ) : permProj R δ k (of D) = 0 := by
  rw [permProj, lift_of, permProjAux_eq_zero hD]

/-- The projection kills the cap-cup generators. -/
@[simp]
theorem permProj_of_capCup {a b : Fin k} (hab : a ≠ b) : permProj R δ k (of (capCup a b)) = 0 :=
  permProj_of_eq_zero (capCup_ne_permToBrauer hab)

/-- The coefficient of `σ` in the projection is the coefficient of the diagram of `σ`. -/
@[simp]
theorem coeff_permProj_apply (x : BrauerAlgebra R δ k) (σ : Equiv.Perm (Fin k)) :
    (permProj R δ k x).coeff σ = x.coeff (permToBrauer σ) := by
  obtain ⟨f, rfl⟩ := (coeffLinearEquiv R δ k).symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, MonoidAlgebra.coeff_zero, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  | add f g hf hg =>
    simp only [map_add, MonoidAlgebra.coeff_add, coeff_add, Finsupp.add_apply, hf, hg]
  | single D r =>
    rw [coeffLinearEquiv_symm_apply, ofCoeff_single, map_smul, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, permProj, lift_of, coeff_permProjAux]
    simp [Finsupp.single_apply]

/-- **`permProj` is a retraction of `ofPerm`**: the permutation diagrams of an element of the
group algebra carry its coefficients. -/
@[simp]
theorem permProj_ofPerm (x : MonoidAlgebra R (Equiv.Perm (Fin k))) :
    permProj R δ k (ofPerm R δ k x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single σ r => simp

variable (R δ k) in
/-- `permProj` composed with `ofPerm` is the identity. -/
theorem permProj_comp_ofPerm : (permProj R δ k).comp (ofPerm R δ k) = AlgHom.id R _ :=
  AlgHom.ext permProj_ofPerm

variable (R δ k) in
/-- The projection onto the group algebra of `Sₖ` is surjective. -/
theorem permProj_surjective : Function.Surjective (permProj R δ k) :=
  fun x => ⟨ofPerm R δ k x, permProj_ofPerm x⟩

end Projection

/-! ### The quotient by `I_1` -/

section Quotient

variable {R : Type*} [CommRing R] {δ : R} {k : ℕ}

/-- **An element lies in `I_1` exactly when it has no permutation diagrams in its support**, that
is, when its projection to the group algebra of `Sₖ` vanishes. -/
theorem mem_diagramIdeal_one_iff {x : BrauerAlgebra R δ k} :
    x ∈ diagramIdeal R δ k 1 ↔ permProj R δ k x = 0 := by
  simp only [mem_diagramIdeal_iff, mul_one, propagatingNumber_add_two_le_iff]
  refine ⟨fun h => MonoidAlgebra.coeff_injective <| Finsupp.ext fun σ => ?_,
    fun h D hD σ hσ => ?_⟩
  · rw [coeff_permProj_apply, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      ← Finsupp.notMem_support_iff]
    exact fun hσ => h _ hσ σ rfl
  · subst hσ
    exact Finsupp.mem_support_iff.mp hD (by
      rw [← coeff_permProj_apply (δ := δ), h, MonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply])

variable (R δ k) in
/-- **The kernel of the projection to the group algebra of `Sₖ` is `I_1`.** -/
theorem ker_permProj : TwoSidedIdeal.ker (permProj R δ k) = diagramIdeal R δ k 1 :=
  TwoSidedIdeal.ext fun _ => by rw [TwoSidedIdeal.mem_ker, mem_diagramIdeal_one_iff]

/-- Congruence modulo `I_1` is contained in the kernel congruence of `permProj`. -/
private theorem ringCon_diagramIdeal_one_le_ker :
    (diagramIdeal R δ k 1).ringCon ≤ RingCon.ker (permProj R δ k).toRingHom :=
  RingCon.le_def.mpr fun {x y} hxy => (RingCon.ker_apply _).mpr <| by
    rw [TwoSidedIdeal.rel_iff, mem_diagramIdeal_one_iff, map_sub, sub_eq_zero] at hxy
    exact hxy

variable (R δ k) in
/-- **The quotient of the Brauer algebra by `I_1` is the group algebra of `Sₖ`**: the projection
`TauCeti.BrauerAlgebra.permProj` descends to an isomorphism, with inverse induced by
`TauCeti.BrauerAlgebra.ofPerm`. -/
noncomputable def quotientDiagramIdealOneAlgEquiv :
    (diagramIdeal R δ k 1).ringCon.Quotient ≃ₐ[R] MonoidAlgebra R (Equiv.Perm (Fin k)) :=
  AlgEquiv.ofAlgHom
    ((diagramIdeal R δ k 1).ringCon.liftₐ (permProj R δ k) ringCon_diagramIdeal_one_le_ker)
    (((diagramIdeal R δ k 1).ringCon.mkₐ R).comp (ofPerm R δ k))
    (AlgHom.ext fun x => by simp)
    (RingCon.Quotient.hom_extₐ <| AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply, RingCon.mkₐ_apply, RingCon.liftₐ_mk, AlgHom.id_apply]
      rw [RingCon.eq, TwoSidedIdeal.rel_iff, mem_diagramIdeal_one_iff, map_sub, permProj_ofPerm,
        sub_self])

/-- The isomorphism `B_k(δ) / I_1 ≃ R[Sₖ]` sends the class of an element to its projection. -/
@[simp]
theorem quotientDiagramIdealOneAlgEquiv_mk (x : BrauerAlgebra R δ k) :
    quotientDiagramIdealOneAlgEquiv R δ k (x : (diagramIdeal R δ k 1).ringCon.Quotient) =
      permProj R δ k x := by
  rw [quotientDiagramIdealOneAlgEquiv, AlgEquiv.ofAlgHom_apply, RingCon.liftₐ_mk]

/-- The inverse of the isomorphism `B_k(δ) / I_1 ≃ R[Sₖ]` sends an element of the group algebra
to the class of its image under `ofPerm`. -/
@[simp]
theorem quotientDiagramIdealOneAlgEquiv_symm_apply (x : MonoidAlgebra R (Equiv.Perm (Fin k))) :
    (quotientDiagramIdealOneAlgEquiv R δ k).symm x =
      (ofPerm R δ k x : (diagramIdeal R δ k 1).ringCon.Quotient) := by
  rw [quotientDiagramIdealOneAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, AlgHom.comp_apply,
    RingCon.mkₐ_apply]

end Quotient

end BrauerAlgebra

end TauCeti
