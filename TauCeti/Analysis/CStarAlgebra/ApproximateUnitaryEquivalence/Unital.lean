/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import TauCeti.Algebra.Star.Hom
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Unital rigidity, conjugation stability, and commutative targets

For `⋆`-homomorphisms into a unital C⋆-algebra `B`, target-unitary approximate unitary equivalence
forces unit-preservation whenever either map sends a star projection (in particular `1`) to `1`,
because any unitary conjugate of the image projection remains a star projection and lies strictly
within distance `1` of `1`.

As consequences:

* `ApproximatelyUnitarilyEquivalent.map_one_eq_one_iff`: approximate unitary equivalence between
  unital C⋆-algebras preserves unitality (`φ 1 = 1 ↔ ψ 1 = 1`).
* `ApproximatelyUnitarilyEquivalent.left_map_one_eq_one_of_comp_id`: if `ψ.comp φ` is approximately
  unitarily equivalent to the identity on `A`, then `ψ (φ 1) = 1` and `ψ 1 = 1`; thus two-sided
  approximate inverses between unital C⋆-algebras are automatically unital.
* `ApproximatelyUnitarilyEquivalent.comp_conjStarAlgAut_comp`: postcomposing a unitary conjugate
  `Ad(v) ∘ φ` by a unit-preserving `⋆`-homomorphism `ψ` stays approximately unitarily equivalent to
  `ψ ∘ φ`.
* `ApproximatelyUnitarilyEquivalent.iff_eq_of_isMulCommutative`: into a commutative unital target,
  approximate unitary equivalence collapses to equality. In particular, the diagonal embedding
  `ℂ → ℂ × ℂ` and first projection `ℂ × ℂ → ℂ` satisfy `ψ ∘ φ = id` while `φ ∘ ψ` is not
  approximately unitarily equivalent to `id`, showing that one-sided approximate invertibility does
  not force isomorphism.
-/

public section

open scoped CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

section ConjugationAndCommutative

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Postcomposing `φ` with conjugation by a target unitary yields a map approximately unitarily
equivalent to `φ`. -/
theorem conjStarAlgAut_comp (φ : A →⋆ₙₐ[ℂ] B) (u : unitary B) :
    ApproximatelyUnitarilyEquivalent
      ((Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) φ :=
  (of_unitary u fun _ ↦ rfl).symm

/-- Conjugating `φ : A →⋆ₙₐ[ℂ] B` by a unitary of `B` before applying a unit-preserving map
`ψ : B →⋆ₙₐ[ℂ] C` yields a map approximately unitarily equivalent to `ψ.comp φ`. -/
theorem comp_conjStarAlgAut_comp [CStarAlgebra C] (φ : A →⋆ₙₐ[ℂ] B) {ψ : B →⋆ₙₐ[ℂ] C}
    (hψ : ψ 1 = 1) (v : unitary B) :
    ApproximatelyUnitarilyEquivalent
      (ψ.comp ((Unitary.conjStarAlgAut ℂ B v).toNonUnitalStarAlgHom.comp φ))
      (ψ.comp φ) := by
  simpa only [NonUnitalStarAlgHom.toNonUnitalStarAlgHom_toStarAlgHom] using
    (conjStarAlgAut_comp φ v).postcomp (ψ.toStarAlgHom hψ)

/-- Into a unital C⋆-algebra with commutative multiplication, approximate unitary equivalence
implies equality, since unitary conjugation is trivial. -/
theorem eq_of_isMulCommutative [IsMulCommutative B] {φ ψ : A →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent φ ψ) : φ = ψ := by
  rw [approximatelyUnitarilyEquivalent_def] at h
  ext a
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨u, hu⟩ := h {a} ε hε
  have hconj : (u : B) * φ a * star (u : B) = φ a := by
    rw [mul_comm' (u : B) (φ a), mul_assoc, Unitary.mul_star_self_of_mem u.prop, mul_one]
  rw [dist_eq_norm]
  exact (hconj ▸ hu a (Finset.mem_singleton_self a)).le

/-- Into a unital C⋆-algebra with commutative multiplication, approximate unitary equivalence is
equivalent to equality. -/
@[simp]
theorem iff_eq_of_isMulCommutative [IsMulCommutative B] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent φ ψ ↔ φ = ψ :=
  ⟨eq_of_isMulCommutative, fun h ↦ h ▸ refl φ⟩

end ConjugationAndCommutative

section ProjectionsAndUnits

/-- If `φ` is approximately unitarily equivalent to `ψ` and `ψ` sends a star projection `p` to `1`,
then `φ` also sends `p` to `1`. -/
theorem map_eq_one_of_isStarProjection {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
    {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) {p : A}
    (hp : IsStarProjection p) (hψ : ψ p = 1) : φ p = 1 := by
  rw [approximatelyUnitarilyEquivalent_def] at h
  obtain ⟨u, hu⟩ := h {p} 1 zero_lt_one
  let e := Unitary.conjStarAlgAut ℂ B u
  have hep : IsStarProjection (e (φ p)) := (hp.map φ).map e
  have hnorm : ‖e (φ p) - 1‖ < 1 := by
    simpa only [e, Unitary.conjStarAlgAut_apply, hψ] using hu p (Finset.mem_singleton_self p)
  exact e.injective ((hep.eq_one_of_norm_sub_one_lt_one hnorm).trans (map_one e).symm)

/-- Approximate unitary equivalence between unital C⋆-algebras transports `ψ 1 = 1` to `φ 1 = 1`. -/
theorem map_one_eq_one {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) (hψ : ψ 1 = 1) : φ 1 = 1 :=
  h.map_eq_one_of_isStarProjection (IsStarProjection.one A) hψ

/-- Approximate unitary equivalence between unital C⋆-algebras preserves unitality. -/
theorem map_one_eq_one_iff {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) : φ 1 = 1 ↔ ψ 1 = 1 :=
  ⟨h.symm.map_one_eq_one, h.map_one_eq_one⟩

/-- If `ψ.comp φ` is approximately unitarily equivalent to the identity on a unital C⋆-algebra `A`,
then `ψ (φ 1) = 1`. -/
theorem comp_map_one_eq_one_of_comp_id {A B : Type*} [CStarAlgebra A] [NonUnitalCStarAlgebra B]
    {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (h : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A)) :
    ψ (φ 1) = 1 :=
  h.map_one_eq_one rfl

/-- If `ψ.comp φ` is approximately unitarily equivalent to the identity on a unital C⋆-algebra `A`,
then the outer map `ψ : B →⋆ₙₐ[ℂ] A` from any unital C⋆-algebra `B` is unital (`ψ 1 = 1`). -/
theorem left_map_one_eq_one_of_comp_id {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (h : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A)) :
    ψ 1 = 1 := by
  have h1 : ψ (φ 1) = 1 := h.comp_map_one_eq_one_of_comp_id
  calc
    ψ 1 = ψ 1 * ψ (φ 1) := by rw [h1, mul_one]
    _ = ψ (1 * φ 1) := (map_mul ψ 1 (φ 1)).symm
    _ = 1 := by rw [one_mul, h1]

/-- If a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` is approximately unitarily equivalent to `φ` and
`φ.comp ψ` is approximately unitarily equivalent to the identity on `B`, then `θ.symm` is
approximately unitarily equivalent to `ψ`. -/
theorem symm_toNonUnitalStarAlgHom_of_comp_id {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {θ : A ≃⋆ₐ[ℂ] B} {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hθ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ)
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  have h := (((hθ.precomp ψ).trans hφψ).postcomp θ.symm.toStarAlgHom).symm
  have hL : θ.symm.toStarAlgHom.toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.id ℂ B) =
      θ.symm.toNonUnitalStarAlgHom := by
    ext b
    simp
  have hR : θ.symm.toStarAlgHom.toNonUnitalStarAlgHom.comp (θ.toNonUnitalStarAlgHom.comp ψ) =
      ψ := by
    ext b
    simp
  rwa [hL, hR] at h

/-- One-sided approximate invertibility does not imply two-sided approximate invertibility: the
diagonal map `φ = (StarAlgHom.ofId ℂ (ℂ × ℂ)).toNonUnitalStarAlgHom` and first projection
`ψ = NonUnitalStarAlgHom.fst ℂ ℂ ℂ` satisfy `ψ.comp φ = .id ℂ ℂ`, whereas `φ.comp ψ` is not
approximately unitarily equivalent to `.id ℂ (ℂ × ℂ)`. -/
theorem not_ofId_comp_fst_id :
    ¬ ApproximatelyUnitarilyEquivalent
      ((StarAlgHom.ofId ℂ (ℂ × ℂ)).toNonUnitalStarAlgHom.comp
        (NonUnitalStarAlgHom.fst ℂ ℂ ℂ))
      (NonUnitalStarAlgHom.id ℂ (ℂ × ℂ)) := by
  rw [iff_eq_of_isMulCommutative]
  intro h
  have h01 := congrArg Prod.snd congr($h (0, 1))
  simp at h01

end ProjectionsAndUnits

end TauCeti.ApproximatelyUnitarilyEquivalent
