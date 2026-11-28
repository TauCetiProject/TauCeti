/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.BilinearMap.IntLinear
import Mathlib.Order.Zorn

/-!
# Isotropic submodules of alternating maps with values in a module

A submodule `S` is isotropic for a sesquilinear map `B : M →ₛₗ[I₁] M →ₛₗ[I₂] P` when
`S ≤ S.orthogonalBilin B`. For an alternating `B` every isotropic submodule lies in a submodule
`L` equal to its own orthogonal complement: a maximal isotropic submodule containing `S` exists by
Zorn's lemma, and a vector `v` orthogonal to it can be adjoined, since `B v v = 0` and an
alternating map is reflexive. Neither finiteness nor nondegeneracy is needed, and the values may
lie in any module, not only in the ring of scalars. The case of scalar-valued bilinear forms,
`LinearMap.BilinForm.IsAlt.exists_le_eq_orthogonal`, is derived from it.

Read for `ℤ`-modules, this gives the statement for abelian groups: for a biadditive pairing
`b : A →+ A →+ P` with `b x x = 0` for all `x`, for instance a pairing of a finite abelian group
into `AddCircle (1 : ℚ)`, every set on which `b` vanishes lies in a subgroup that is its own
annihilator. An antisymmetric pairing on a group of odd order vanishes on the diagonal, so this
applies to it.

## Main results

* `LinearMap.IsAlt.sup_span_singleton_le_orthogonalBilin`: adjoining an orthogonal vector to an
  isotropic submodule keeps it isotropic.
* `LinearMap.IsAlt.exists_le_eq_orthogonalBilin`: every isotropic submodule of an alternating
  sesquilinear map lies in a submodule equal to its orthogonal complement.
* `AddMonoidHom.exists_subset_addSubgroup_mem_iff_forall_apply_eq_zero`: for a biadditive pairing
  vanishing on the diagonal, every set on which the pairing vanishes lies in a subgroup that is
  its own annihilator.
* `AddMonoidHom.apply_self_eq_zero_of_odd_card`: an antisymmetric biadditive pairing on a group of
  odd order vanishes on the diagonal.

## References

* The existence of such subgroups is used, as `New.Variety.exists_lagrangian`, in the folder
  `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open Submodule

namespace LinearMap.IsAlt

variable {R R₁ M P : Type*} [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M] [Module R₁ M]
  [AddCommMonoid P] [Module R P] {I₁ I₂ : R₁ →+* R} {B : M →ₛₗ[I₁] M →ₛₗ[I₂] P}

/-- Adjoining a vector orthogonal to an isotropic submodule keeps it isotropic, for an alternating
sesquilinear map. No nondegeneracy is needed. -/
theorem sup_span_singleton_le_orthogonalBilin (hB : B.IsAlt) {W : Submodule R₁ M}
    (hW : W ≤ W.orthogonalBilin B) {v : M} (hv : v ∈ W.orthogonalBilin B) :
    W ⊔ R₁ ∙ v ≤ (W ⊔ R₁ ∙ v).orthogonalBilin B := by
  have hspan : R₁ ∙ v ≤ W.orthogonalBilin B := span_le.mpr (by simpa using hv)
  rw [orthogonalBilin_sup]
  refine sup_le (le_inf hW fun w hw ↦ ?_) (le_inf hspan ?_)
  · -- `B` is reflexive without negation: `B (w + v) (w + v) = 0` expands to `B v w = 0`.
    simpa [hB w, hB v, hv w hw] using hB (w + v)
  · exact span_le.mpr (by simpa using hB v)

/-- **Isotropic submodules lie in self-orthogonal ones.** For an alternating sesquilinear map `B`
with values in any module, every submodule `S` with `S ≤ S.orthogonalBilin B` lies in a submodule
`L` with `L = L.orthogonalBilin B`. No finiteness or nondegeneracy is needed. -/
theorem exists_le_eq_orthogonalBilin (hB : B.IsAlt) {S : Submodule R₁ M}
    (hS : S ≤ S.orthogonalBilin B) : ∃ L, S ≤ L ∧ L = L.orthogonalBilin B := by
  -- The supremum of a nonempty chain of isotropic submodules is isotropic, since any two of its
  -- vectors lie in a common member of the chain.
  have hchain : ∀ c ⊆ {W | S ≤ W ∧ W ≤ W.orthogonalBilin B}, IsChain (· ≤ ·) c →
      ∀ W ∈ c, ∃ ub ∈ {W | S ≤ W ∧ W ≤ W.orthogonalBilin B}, ∀ W' ∈ c, W' ≤ ub := by
    intro c hcS hc W hW
    refine ⟨sSup c, ⟨(hcS hW).1.trans (le_sSup hW), fun y hy ↦ ?_⟩, fun _ ↦ le_sSup⟩
    refine mem_orthogonalBilin.mpr fun x hx ↦ ?_
    obtain ⟨W₁, hW₁, hx⟩ := (mem_sSup_of_directed ⟨W, hW⟩ hc.directedOn).mp hx
    obtain ⟨W₂, hW₂, hy⟩ := (mem_sSup_of_directed ⟨W, hW⟩ hc.directedOn).mp hy
    obtain ⟨W₃, hW₃, h₁, h₂⟩ := hc.directedOn W₁ hW₁ W₂ hW₂
    exact mem_orthogonalBilin.mp ((hcS hW₃).2 (h₂ hy)) x (h₁ hx)
  obtain ⟨L, hSL, ⟨-, hL⟩, hmax⟩ := zorn_le_nonempty₀ _ hchain S ⟨le_rfl, hS⟩
  refine ⟨L, hSL, le_antisymm hL fun v hv ↦ ?_⟩
  have hle : L ⊔ R₁ ∙ v ≤ L :=
    hmax ⟨hSL.trans le_sup_left, hB.sup_span_singleton_le_orthogonalBilin hL hv⟩ le_sup_left
  exact hle (mem_sup_right (mem_span_singleton_self v))

end LinearMap.IsAlt

namespace AddMonoidHom

variable {A P : Type*} [AddCommGroup A] [AddCommGroup P]

/-- **Isotropic sets lie in self-annihilating subgroups.** Let `b` be a biadditive pairing on an
abelian group `A` with `b x x = 0` for every `x`, for instance a pairing of a finite abelian group
into `AddCircle (1 : ℚ)`. Every set `s` on which `b` vanishes lies in a subgroup `H` equal to its
own annihilator: `x ∈ H` exactly when `b y x = 0` for all `y ∈ H`. No finiteness or nondegeneracy
is needed. -/
theorem exists_subset_addSubgroup_mem_iff_forall_apply_eq_zero (b : A →+ A →+ P)
    (hb : ∀ x, b x x = 0) {s : Set A} (hs : ∀ x ∈ s, ∀ y ∈ s, b x y = 0) :
    ∃ H : AddSubgroup A, s ⊆ H ∧ ∀ x, x ∈ H ↔ ∀ y ∈ H, b y x = 0 := by
  -- Apply the result to the pairing as a `ℤ`-bilinear map, which evaluates as `b`.
  have hS : span ℤ s ≤ (span ℤ s).orthogonalBilin b.toIntLinearMap₂ :=
    span_le.mpr fun y hy ↦ mem_orthogonalBilin_span.mpr fun x hx ↦ by
      simpa [toIntLinearMap₂_apply] using hs x hx y hy
  obtain ⟨L, hSL, hL⟩ := LinearMap.IsAlt.exists_le_eq_orthogonalBilin (B := b.toIntLinearMap₂)
    (fun x ↦ by simpa [toIntLinearMap₂_apply] using hb x) hS
  refine ⟨L.toAddSubgroup, fun x hx ↦ hSL (subset_span hx), fun x ↦ ?_⟩
  -- Membership in `L.toAddSubgroup` is membership in `L`, which is its own orthogonal complement.
  rw [Submodule.mem_toAddSubgroup, SetLike.ext_iff.mp hL x]
  simp [toIntLinearMap₂_apply]

/-- An antisymmetric biadditive pairing on a group of odd order vanishes on the diagonal: writing
`x = 2 • y`, possible since `2` is prime to the order, the value `b x x = 2 • 2 • b y y` vanishes
since `2 • b y y = 0`. Together with
`AddMonoidHom.exists_subset_addSubgroup_mem_iff_forall_apply_eq_zero` this shows that for such a
pairing every set on which it vanishes lies in a subgroup that is its own annihilator. -/
theorem apply_self_eq_zero_of_odd_card (b : A →+ A →+ P) (hb : ∀ x y, b y x = -b x y)
    (hA : Odd (Nat.card A)) (x : A) : b x x = 0 := by
  obtain ⟨y, rfl⟩ :=
    (Nat.Coprime.nsmul_right_bijective (G := A) (Nat.coprime_two_right.mpr hA)).surjective x
  have h2 : 2 • b y y = 0 := by
    rw [two_nsmul]
    exact add_eq_zero_iff_eq_neg.mpr (hb y y)
  rw [map_nsmul, map_nsmul, nsmul_apply, h2, nsmul_zero]

end AddMonoidHom
