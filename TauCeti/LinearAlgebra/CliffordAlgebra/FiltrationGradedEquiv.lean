/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ExteriorFiltration
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# The degree quotients of a Clifford filtration

Mathlib's `CliffordAlgebra.equivExterior` identifies a Clifford algebra with its exterior-algebra
model when `2` is invertible. This file proves that the equivalence respects the degree filtration,
then transports the zero-form calculation of each successive quotient to an arbitrary quadratic
form.

This is the degree-quotient part of the Layer 0 `filtrationGradedEquiv` target in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean#L62-L68).
It also identifies that equivalence with the leading-term map built in
`TauCeti.LinearAlgebra.CliffordAlgebra.Filtration`, which reaches the same target by a different
route, completing the bridge that file describes itself as having proved only half of. It does not
construct the total associated-graded algebra or prove multiplication compatibility.

## Main definitions

* `CliffordAlgebra.equivExteriorFiltration`: `equivExterior` restricted to one filtration
  step.
* `CliffordAlgebra.filtrationGradedEquiv`: the corresponding degree-quotient equivalence
  with the exterior power.

## Main results

* `CliffordAlgebra.equivExterior_mem_zero_form_filtration` and
  `CliffordAlgebra.equivExterior_symm_mem_filtration`: `equivExterior` and its inverse
  carry each Clifford filtration step to the corresponding zero-form step and back.
* `CliffordAlgebra.filtrationGradedEquiv_comp_filtrationLeadingTerm`: the graded
  equivalence inverts `Filtration.lean`'s leading-term map, so the two independent routes to the
  degree quotient are the same map, with
  `CliffordAlgebra.filtrationLeadingTerm_eq_filtrationGradedEquiv_symm` the map-level form.
* `CliffordAlgebra.prod_map_ι_ofFn_ne_zero`: a linearly independent finite family has a nonzero
  ordered product of Clifford generators.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The degree filtration".
* The identification of the associated graded of the Clifford filtration with the exterior algebra
  is the Clifford-algebra analogue of the Poincaré-Birkhoff-Witt theorem; see C. Chevalley, *The
  Algebraic Theory of Spinors* (1954), Chapter II, and H. B. Lawson and M.-L. Michelsohn, *Spin
  Geometry* (1989), Proposition I.1.2.
* The transport used here is Bourbaki's `λ_B`, Mathlib's `CliffordAlgebra.changeForm`: it is
  triangular with identity leading term rather than an antisymmetrisation, which is why the two
  routes agree on the nose with no scalar. See N. Bourbaki, *Algèbre* IX §9, and
  [grinberg_clifford_2016] as cited by Mathlib's `Contraction.lean`.
-/

public section


universe u v

namespace CliffordAlgebra

open TauCeti.Algebra TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- `equivExterior` restricted to a Clifford filtration step. -/
noncomputable def equivExteriorFiltration (k : ℕ) :
    filtration Q k ≃ₗ[R] filtration (0 : QuadraticForm R M) k :=
  (equivExterior Q).ofSubmodules _ _
    (changeFormEquiv_map_filtration Q changeForm.associated_neg_proof k)

/-- Coercing the restricted exterior equivalence is the ambient `equivExterior` map. -/
@[simp]
theorem coe_equivExteriorFiltration_apply (k : ℕ)
    (x : filtration Q k) :
    (equivExteriorFiltration Q k x : CliffordAlgebra (0 : QuadraticForm R M)) =
      equivExterior Q x := by
  simp only [equivExteriorFiltration, equivExterior, LinearEquiv.ofSubmodules_apply]

/-- Coercing the inverse restricted exterior equivalence is the ambient inverse map. -/
@[simp]
theorem coe_equivExteriorFiltration_symm_apply
    (k : ℕ) (x : filtration (0 : QuadraticForm R M) k) :
    ((equivExteriorFiltration Q k).symm x : CliffordAlgebra Q) = (equivExterior Q).symm x := by
  simp only [equivExteriorFiltration, equivExterior, LinearEquiv.ofSubmodules_symm_apply]

private theorem equivExteriorFiltration_map_previous
    (k : ℕ) :
    (previousRestricted (ι Q) (k + 1)).map
        (equivExteriorFiltration Q (k + 1)).toLinearMap =
      previousRestricted (ι (0 : QuadraticForm R M)) (k + 1) := by
  ext x
  rw [Submodule.mem_map_equiv, mem_previousRestricted_iff,
    mem_previousRestricted_iff, wordFiltrationPrevious_succ, wordFiltrationPrevious_succ]
  -- The two submodules are over filtration subtypes, so expose their ambient carrier predicates.
  change (changeFormEquiv changeForm.associated_neg_proof).symm
      (x : CliffordAlgebra (0 : QuadraticForm R M)) ∈ filtration Q k ↔
    (x : CliffordAlgebra (0 : QuadraticForm R M)) ∈ filtration (0 : QuadraticForm R M) k
  rw [← changeFormEquiv_map_filtration Q changeForm.associated_neg_proof k,
    Submodule.mem_map_equiv]

private noncomputable def equivExteriorFiltrationQuotient (k : ℕ) :
    GradedPiece (ι Q) (k + 1) ≃ₗ[R]
      GradedPiece (ι (0 : QuadraticForm R M)) (k + 1) :=
  Submodule.Quotient.equiv _ _ (equivExteriorFiltration Q (k + 1))
    (equivExteriorFiltration_map_previous Q k)

/-- `equivExterior` carries each Clifford filtration step into the corresponding zero-form step. -/
theorem equivExterior_mem_zero_form_filtration
    {k : ℕ} {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) :
    equivExterior Q x ∈ filtration (0 : QuadraticForm R M) k := by
  simpa only [coe_equivExteriorFiltration_apply] using
    (equivExteriorFiltration Q k ⟨x, hx⟩).property

/-- The inverse of `equivExterior` carries each zero-form filtration step back into the
corresponding Clifford step. -/
theorem equivExterior_symm_mem_filtration {k : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ filtration (0 : QuadraticForm R M) k) :
    (equivExterior Q).symm x ∈ filtration Q k := by
  simpa only [coe_equivExteriorFiltration_symm_apply] using
    ((equivExteriorFiltration Q k).symm ⟨x, hx⟩).property

/-- The successive degree quotient of a Clifford algebra is the corresponding exterior power. -/
noncomputable def filtrationGradedEquiv (k : ℕ) :
    GradedPiece (ι Q) (k + 1) ≃ₗ[R] ⋀[R]^(k + 1) M :=
  (equivExteriorFiltrationQuotient Q k).trans (zeroFormFiltrationQuotientEquivExteriorPower k)

/-- On quotient representatives, `filtrationGradedEquiv` first applies `equivExterior`. -/
@[simp]
theorem filtrationGradedEquiv_apply_mk (k : ℕ)
    (x : filtration Q (k + 1)) :
    filtrationGradedEquiv Q k (Submodule.Quotient.mk x) =
      zeroFormFiltrationQuotientEquivExteriorPower k
        (Submodule.Quotient.mk
          (⟨equivExterior Q x, equivExterior_mem_zero_form_filtration Q x.property⟩ :
            filtration (0 : QuadraticForm R M) (k + 1))) := by
  rw [filtrationGradedEquiv, LinearEquiv.trans_apply, equivExteriorFiltrationQuotient,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  apply congrArg (fun y => zeroFormFiltrationQuotientEquivExteriorPower k
    (Submodule.Quotient.mk y))
  exact Subtype.ext (coe_equivExteriorFiltration_apply Q (k + 1) x)

/-- The inverse graded equivalence sends an exterior element to the quotient class of its
preimage under `equivExterior`. -/
@[simp]
theorem filtrationGradedEquiv_symm_apply (k : ℕ)
    (x : ⋀[R]^(k + 1) M) :
    (filtrationGradedEquiv Q k).symm x =
      Submodule.Quotient.mk
        (⟨(equivExterior Q).symm x, equivExterior_symm_mem_filtration Q
            (ι_range_pow_le_filtration (0 : QuadraticForm R M) (k + 1) x.property)⟩ :
          filtration Q (k + 1)) := by
  rw [filtrationGradedEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    zeroFormFiltrationQuotientEquivExteriorPower_symm_apply,
    equivExteriorFiltrationQuotient, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext (coe_equivExteriorFiltration_symm_apply Q (k + 1) _)

/-- **The graded equivalence undoes the leading-term map.** Together with
`filtrationLeadingTerm_surjective`, which holds over any `CommRing`, this identifies the two
independent routes `Filtration.lean` and this file take to the degree-`k + 1` quotient. -/
theorem filtrationGradedEquiv_comp_filtrationLeadingTerm (k : ℕ) :
    (filtrationGradedEquiv Q k).toLinearMap ∘ₗ filtrationLeadingTerm Q k = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.id_coe, id_eq, filtrationLeadingTerm_apply_ιMulti, filtrationGradedEquiv_apply_mk]
  rw [← zeroFormFiltrationQuotientEquivExteriorPower_apply k (exteriorPower.ιMulti R (k + 1) v)]
  congr 1
  rw [Submodule.Quotient.eq, mem_previousRestricted_iff, wordFiltrationPrevious_succ]
  -- What remains is `changeForm`'s symbol computation at `Q' = 0`, read through `equivExterior`.
  simpa only [equivExterior, changeFormEquiv_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply, Function.comp_def, AddSubgroupClass.coe_sub,
    List.map_ofFn] using
    changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration Q
      (Q' := (0 : QuadraticForm R M)) changeForm.associated_neg_proof (List.ofFn v)
      (by simp)

/-- The pointwise form, which is the one `simp` can use. -/
@[simp]
theorem filtrationGradedEquiv_filtrationLeadingTerm
    (k : ℕ) (x : ⋀[R]^(k + 1) M) :
    filtrationGradedEquiv Q k (filtrationLeadingTerm Q k x) = x :=
  LinearMap.congr_fun (filtrationGradedEquiv_comp_filtrationLeadingTerm Q k) x

/-- The leading-term map is `filtrationGradedEquiv`'s inverse. -/
theorem filtrationLeadingTerm_eq_filtrationGradedEquiv_symm (k : ℕ) :
    filtrationLeadingTerm Q k = (filtrationGradedEquiv Q k).symm.toLinearMap := by
  rw [← LinearMap.comp_id (filtrationGradedEquiv Q k).symm.toLinearMap]
  exact (LinearEquiv.eq_toLinearMap_symm_comp _ _).2
    (filtrationGradedEquiv_comp_filtrationLeadingTerm Q k)

/-- An ordered product of Clifford generators from a linearly independent finite family is
nonzero, in every characteristic. This is the multiplicative PBW independence statement; the
proof successively contracts against coordinate functionals. -/
theorem prod_map_ι_ofFn_ne_zero {K : Type u} [Field K] [Module K M]
    (Q : QuadraticForm K M) {n : ℕ} (v : Fin n → M) (hv : LinearIndependent K v) :
    (List.ofFn ((ι Q) ∘ v)).prod ≠ 0 := by
  classical
  have hone : (1 : CliffordAlgebra Q) ≠ 0 := by
    obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (-Q)
    have hB' : B.toQuadraticMap = 0 - Q := by simpa using hB
    let _ : Nontrivial (CliffordAlgebra Q) :=
      (changeFormEquiv hB').symm.injective.nontrivial
    exact one_ne_zero
  induction n with
  | zero => simpa using hone
  | succ k ih =>
      let w : Fin k → M := fun i => v i.succ
      have hw : LinearIndependent K w := hv.comp Fin.succ (Fin.succ_injective k)
      have hv0 : v 0 ∉ Submodule.span K (Set.range w) := by
        have h := hv.notMem_span_image (s := Set.range (Fin.succ : Fin k → Fin (k + 1)))
          (x := 0) (by simp)
        have hrange : v '' Set.range (Fin.succ : Fin k → Fin (k + 1)) = Set.range w := by
          ext x
          constructor
          · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.succ, ⟨i, rfl⟩, rfl⟩
        rw [hrange] at h
        exact h
      obtain ⟨d, hd, hd_zero⟩ :=
        LinearMap.exists_extend_of_notMem
          (0 : Submodule.span K (Set.range w) →ₗ[K] K) hv0 1
      have hd_succ (i : Fin k) : d (w i) = 0 := by
        have h := LinearMap.congr_fun hd
          (⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩ :
            Submodule.span K (Set.range w))
        rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
        -- Remove the span-subtype coercion from the extension equation.
        change d (w i) = 0 at h
        exact h
      have hcontract (l : List M) (hl : ∀ x ∈ l, d x = 0) :
          contractLeft d (l.map (ι Q)).prod = 0 := by
        induction l with
        | nil => simp
        | cons x l ih =>
            rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, hl x List.mem_cons_self,
              zero_smul, zero_sub]
            simp only [ih (fun y hy => hl y (List.mem_cons_of_mem x hy)), mul_zero, neg_zero]
      intro hzero
      rw [List.ofFn_succ, List.prod_cons] at hzero
      simp only [Function.comp_apply] at hzero
      have hzero' := congrArg (contractLeft d) hzero
      rw [map_zero, contractLeft_ι_mul, hd_zero, one_smul] at hzero'
      have htail : contractLeft d (List.ofFn ((ι Q) ∘ w)).prod = 0 := by
        rw [← List.map_ofFn]
        apply hcontract
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hd_succ i
      -- Normalize the local tail abbreviation to the `List.ofFn` shape produced above.
      change contractLeft d (List.ofFn fun i => ι Q (v i.succ)).prod = 0 at htail
      rw [htail, mul_zero, sub_zero] at hzero'
      apply ih w hw
      -- Normalize the induction hypothesis's composed family to the same tail expression.
      change (List.ofFn fun i => ι Q (v i.succ)).prod = 0
      exact hzero'

end CliffordAlgebra
