/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.HeckeRing.Basic
import Mathlib.Tactic.Group

/-!
# Hecke sums on a representation of the monoid `Δ`

Let `(Δ, Γ₁, Γ₂)` be a Hecke triple in a group `G`, let `D = Γ₁ δ Γ₂` be a double coset with
chosen representative `δ = D.out`, let `ρ` be a representation of a submonoid `Δ' ≤ G` containing
`δ` and `Γ₂` on an `R`-module `V`, and let `q : V →ₗ[R] W` be a linear map. The decomposition
`Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` into right cosets with representatives `aᵥ = rightCosetRep D v` defines the
**Hecke sum**

`heckeSum D ρ q = ∑ᵥ q ∘ ρ(aᵥ) : V →ₗ[R] W`,

the sum over the chosen representatives. The two theorems of this file are Shimura's, §3.4,
transposed from functions to a representation:

* when `q` is `Γ₁`-invariant — `q ∘ ρ(γ₁) = q` for `γ₁ ∈ Γ₁` — the sum is **independent of the
  representatives** (`heckeSum_eq_sum_of_rightCosets`): any family `(aᵢ)` naming each right coset
  of `Γ₁ δ Γ₂` exactly once gives the same map;
* under the same hypothesis the sum is **`Γ₂`-invariant** (`heckeSum_comp_of_mem`):
  `heckeSum D ρ q ∘ ρ(γ) = heckeSum D ρ q` for `γ ∈ Γ₂`, because right multiplication by `γ`
  permutes the right cosets `Γ₁ aᵥ`.

The second statement is what lets the Hecke sum descend to the `Γ₂`-coinvariants of `V` when
`q` is the projection onto the `Γ₁`-coinvariants: a double coset then induces a map
`V_{Γ₂} → V_{Γ₁}`, the Hecke operator on coinvariants. That descent is carried out where the
coinvariants are, for the modular symbols in
`TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke`; here `q` is an arbitrary
`Γ₁`-invariant map so that the two theorems apply to coinvariants formed over any group whose
image in `G` is `Γ₁`.

The slash sums of `TauCeti.NumberTheory.ModularForms.HeckeSlash` are the same construction for
the right action of `GL(2, ℚ)` on functions `ℍ → ℂ`, where invariance under `Γ₁` is invariance of
the function itself and the sum acts on invariants rather than descending to coinvariants.

## Main definitions

* `HeckeCoset.heckeSum`: the sum `∑ᵥ q ∘ ρ(aᵥ)` over the chosen right-coset representatives.

## Main results

* `HeckeCoset.comp_eq_of_rightCoset_eq`: for `Γ₁`-invariant `q`, `q ∘ ρ(x)` depends only on the
  right coset `Γ₁ x`.
* `HeckeCoset.heckeSum_eq_sum_of_rightCosets`: the choice-free description of the Hecke sum.
* `HeckeCoset.heckeSum_comp_of_mem`: the Hecke sum of a `Γ₁`-invariant map is `Γ₂`-invariant.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, (3.4.1) and Proposition 3.37.
-/

public section

open DoubleCoset

open scoped Pointwise

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ Δ' : Submonoid G} {Γ₁ Γ₂ : Subgroup G} (D : HeckeCoset Δ Γ₁ Γ₂)
  {R V W : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  (ρ : Representation R Δ' V)

section Invariance

variable (hΓ₁ : Γ₁.toSubmonoid ≤ Δ') {q : V →ₗ[R] W}
  (hq : ∀ γ (hγ : γ ∈ Γ₁), q ∘ₗ ρ ⟨γ, hΓ₁ hγ⟩ = q)

include hΓ₁ hq in
/-- **For a `Γ₁`-invariant `q`, the map `q ∘ ρ(x)` depends only on the right coset `Γ₁ x`.** If
`Γ₁ x = Γ₁ y` then `y = (y x⁻¹) x` with `y x⁻¹ ∈ Γ₁`, and `q` does not see that factor.

This is the whole role invariance plays in the choice-freeness of the Hecke sum: everything else
is a comparison of two enumerations of the same set of cosets. -/
theorem comp_eq_of_rightCoset_eq {x y : G} (hx : x ∈ Δ') (hy : y ∈ Δ')
    (h : MulOpposite.op x • (Γ₁ : Set G) = MulOpposite.op y • (Γ₁ : Set G)) :
    q ∘ₗ ρ ⟨x, hx⟩ = q ∘ₗ ρ ⟨y, hy⟩ := by
  have hγ : y * x⁻¹ ∈ Γ₁ := (rightCoset_eq_iff Γ₁).mp h
  calc q ∘ₗ ρ ⟨x, hx⟩ = (q ∘ₗ ρ ⟨y * x⁻¹, hΓ₁ hγ⟩) ∘ₗ ρ ⟨x, hx⟩ := by rw [hq _ hγ]
    _ = q ∘ₗ ρ (⟨y * x⁻¹, hΓ₁ hγ⟩ * ⟨x, hx⟩) := by
      rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = q ∘ₗ ρ ⟨y, hy⟩ := by
      congr 2
      exact Subtype.ext (inv_mul_cancel_right y x)

end Invariance

variable (hD : (D.out : G) ∈ Δ') (hΓ₂ : Γ₂.toSubmonoid ≤ Δ') (q : V →ₗ[R] W)
  [Finite (DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹)]

/-- The enumeration `∑` needs, obtained from the `Finite` assumption by choice. The sum needs
its index type to be finite, and that is all it needs: a Hecke triple supplies this finiteness
(`IsHeckeTriple.commensurable_conjAct_inv_left`) but is strictly stronger, so the proposition
`Finite` is assumed directly and the `Fintype` the `∑` notation requires is installed once, as a
`local` `noncomputable` instance, exactly as in `ModularForms/HeckeSlash/Basic.lean`. -/
noncomputable local instance : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) := Fintype.ofFinite _

/-- **The Hecke sum of a double coset on a representation.** For `Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` with
`aᵥ = rightCosetRep D v`, this is `∑ᵥ q ∘ ρ(aᵥ) : V →ₗ[R] W`.

⚠ It is a sum over the *chosen* representatives `D.out` and `v.out`, and for an arbitrary `q` it
depends on them. For a `Γ₁`-invariant `q` it does not (`heckeSum_eq_sum_of_rightCosets`), and it
is then `Γ₂`-invariant (`heckeSum_comp_of_mem`).

The representatives act through `ρ` because they lie in `Δ'`: only the chosen `D.out` and `Γ₂`
are required to (`rightCosetRep_mem`), not the whole of `Δ`. -/
noncomputable def heckeSum : V →ₗ[R] W :=
  ∑ v, q ∘ₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩

/-- The defining equation of `heckeSum`. Since `heckeSum` is not `@[expose]`, a downstream module
rewrites with this instead of unfolding the body. -/
theorem heckeSum_def :
    heckeSum D ρ hD hΓ₂ q =
      ∑ v, q ∘ₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩ := (rfl)

/-- The Hecke sum, evaluated: `heckeSum D ρ q x = ∑ᵥ q (ρ(aᵥ) x)`. -/
theorem heckeSum_apply (x : V) :
    heckeSum D ρ hD hΓ₂ q x =
      ∑ v, q (ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩ x) := by
  simp only [heckeSum_def, LinearMap.sum_apply, LinearMap.comp_apply]

variable {q} (hΓ₁ : Γ₁.toSubmonoid ≤ Δ') (hq : ∀ γ (hγ : γ ∈ Γ₁), q ∘ₗ ρ ⟨γ, hΓ₁ hγ⟩ = q)

include hΓ₁ hq in
/-- **The Hecke sum of a `Γ₁`-invariant map is the sum over any decomposition of the double coset
into right cosets.** If the right cosets `Γ₁ aᵢ` are pairwise distinct and cover `Γ₁ D.out Γ₂`,
then `heckeSum D ρ q = ∑ᵢ q ∘ ρ(aᵢ)`.

So the map is attached to the double coset itself: the representatives `D.out` and `v.out` that
`heckeSum` happens to pick are one such family, and every other family gives the same map. The
hypothesis `ha` records that the family lies in the monoid `ρ` acts through; it is automatic
when the family lies in the double coset and `Γ₁ ≤ Δ'`. -/
theorem heckeSum_eq_sum_of_rightCosets {ι : Type*} [Fintype ι] (a : ι → G) (ha : ∀ i, a i ∈ Δ')
    (hcover : doubleCoset (D.out : G) Γ₁ Γ₂ = ⋃ i, MulOpposite.op (a i) • (Γ₁ : Set G))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (Γ₁ : Set G)) :
    heckeSum D ρ hD hΓ₂ q = ∑ i, q ∘ₗ ρ ⟨a i, ha i⟩ := by
  obtain ⟨φ, hbij, hφ⟩ := exists_bijective_rightCosetRep_smul_eq D a hcover hinj
  rw [heckeSum_def]
  exact (Fintype.sum_bijective φ hbij _ _ fun i ↦
    comp_eq_of_rightCoset_eq ρ hΓ₁ hq (ha i) _ (hφ i)).symm

include hΓ₁ hq in
/-- **The Hecke sum of a `Γ₁`-invariant map is `Γ₂`-invariant.** For `γ ∈ Γ₂`,
`heckeSum D ρ q ∘ ρ(γ) = heckeSum D ρ q`.

The proof is Shimura's (Proposition 3.37): right multiplication by `γ` permutes the right cosets
`Γ₁ aᵥ`, the permutation being `v ↦ γ⁻¹ • v` on the index `Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)`, and by
`comp_eq_of_rightCoset_eq` each summand only sees its coset. This is the hypothesis under which
the Hecke sum descends to the `Γ₂`-coinvariants of `V`. -/
theorem heckeSum_comp_of_mem {γ : G} (hγ : γ ∈ Γ₂) :
    heckeSum D ρ hD hΓ₂ q ∘ₗ ρ ⟨γ, hΓ₂ hγ⟩ = heckeSum D ρ hD hΓ₂ q := by
  -- Composing the `v`-th summand with `ρ(γ)` gives the summand at the permuted index.
  have hperm (v : DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) :
      (q ∘ₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩) ∘ₗ ρ ⟨γ, hΓ₂ hγ⟩ =
        q ∘ₗ ρ ⟨rightCosetRep D ((⟨γ, hγ⟩ : Γ₂)⁻¹ • v),
          rightCosetRep_mem D hD hΓ₂ _⟩ := by
    have hmem : rightCosetRep D v * γ ∈ Δ' :=
      mul_mem (rightCosetRep_mem D hD hΓ₂ v) (hΓ₂ hγ)
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul]
    refine comp_eq_of_rightCoset_eq ρ hΓ₁ hq hmem _ ((rightCoset_eq_iff Γ₁).mpr ?_)
    -- `aᵥ γ = δ (γ⁻¹ τᵥ)⁻¹` is a `Γ₁`-multiple of the representative of the class of `γ⁻¹ τᵥ`,
    -- which is the class `γ⁻¹ • v`.
    obtain ⟨γ₁, hγ₁, hsplit⟩ :=
      exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2)
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : G), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) = (⟨γ, hγ⟩ : Γ₂)⁻¹ • v :=
      MulAction.Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ₂)⁻¹ v
    have hrep : rightCosetRep D ((⟨γ, hγ⟩ : Γ₂)⁻¹ • v) = γ₁⁻¹ * (rightCosetRep D v * γ) := by
      rw [← hmk, rightCosetRep_def D v]
      have h2 : (D.out : G) * (v.out : G)⁻¹ * γ = (D.out : G) * (γ⁻¹ * (v.out : G))⁻¹ := by group
      rw [h2, hsplit]
      group
    rw [hrep, mul_inv_cancel_right]
    exact inv_mem hγ₁
  refine LinearMap.ext fun x ↦ ?_
  simp only [heckeSum_def, LinearMap.comp_apply, LinearMap.sum_apply]
  -- `MulAction.toPerm` of `γ⁻¹` is the reindexing bijection.
  exact Fintype.sum_equiv (MulAction.toPerm (⟨γ, hγ⟩ : Γ₂)⁻¹) _ _ fun v ↦ by
    simpa only [MulAction.toPerm_apply, LinearMap.comp_apply] using
      LinearMap.congr_fun (hperm v) x

end HeckeCoset

end
