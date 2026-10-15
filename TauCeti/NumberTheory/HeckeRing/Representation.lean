/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Coset
public import TauCeti.NumberTheory.HeckeRing.Basic

/-!
# Hecke sums on a representation of the monoid `Δ`

Let `D = Γ₁ δ Γ₂` be a double coset in a group `G` with finitely many right cosets of `Γ₁`,
with chosen representative `δ = D.out`. Let `ρ` be a representation of a submonoid `Δ' ≤ G`
containing `δ` and `Γ₂` on an `R`-module `V`. For semirings `R`, `S` and `σ : R →+* S`, let
`q : V →ₛₗ[σ] W` be a semilinear map to an `S`-module `W`. The decomposition
`Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` into right cosets with representatives `aᵥ = rightCosetRep D v` defines the
**Hecke sum**

`heckeSum D ρ q = ∑ᵥ q ∘ ρ(aᵥ) : V →ₛₗ[σ] W`,

the sum over the chosen representatives. Taking `S = R` and `σ = RingHom.id R` recovers
linear maps over `R`; allowing a different `S` also covers maps that extend or twist the
coefficients. The two invariance theorems are Shimura's, §3.4, transposed from functions to a
representation:

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
`TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Basic`; here `q` is an arbitrary
`Γ₁`-invariant map so that the two theorems apply to coinvariants formed over any group whose
image in `G` is `Γ₁`.

The slash sums of `TauCeti.NumberTheory.ModularForms.HeckeSlash` are the same construction for
the right action of `GL(2, ℚ)` on functions `ℍ → ℂ`, where invariance under `Γ₁` is invariance of
the function itself and the sum acts on invariants rather than descending to coinvariants.

## Main definitions

* `HeckeCoset.heckeSum`: the sum `∑ᵥ q ∘ ρ(aᵥ)` over the chosen right-coset representatives.

## Main results

* `Representation.comp_eq_of_rightCoset_eq` (in `RepresentationTheory/Coset.lean`): for
  `Γ₁`-invariant `q`, `q ∘ ρ(x)` depends only on the right coset `Γ₁ x`.
* `HeckeCoset.heckeSum_zero` and `HeckeCoset.heckeSum_add`: additivity in the target map.
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
  {R S V W : Type*} [Semiring R] [Semiring S] [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module S W] {σ : R →+* S}
  (ρ : Representation R Δ' V)

variable (hD : (D.out : G) ∈ Δ') (hΓ₂ : Γ₂.toSubmonoid ≤ Δ') (q : V →ₛₗ[σ] W)
  [Finite (DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹)]

/-- A chosen finite enumeration of the right-coset index. A Hecke triple supplies the
`Finite` assumption, but the sum needs only finiteness of this index. -/
noncomputable local instance : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) := Fintype.ofFinite _

/-- **The Hecke sum of a double coset on a representation.** For `Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` with
`aᵥ = rightCosetRep D v`, this is `∑ᵥ q ∘ ρ(aᵥ) : V →ₛₗ[σ] W`.

⚠ It is a sum over the *chosen* representatives `D.out` and `v.out`, and for an arbitrary `q` it
depends on them. For a `Γ₁`-invariant `q` it does not (`heckeSum_eq_sum_of_rightCosets`), and it
is then `Γ₂`-invariant (`heckeSum_comp_of_mem`).

The representatives act through `ρ` because they lie in `Δ'`: only the chosen `D.out` and `Γ₂`
are required to (`rightCosetRep_mem`), not the whole of `Δ`. -/
noncomputable def heckeSum : V →ₛₗ[σ] W :=
  ∑ v, q ∘ₛₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩

/-- The defining equation of `heckeSum`. Since `heckeSum` is not `@[expose]`, a downstream module
rewrites with this instead of unfolding the body. -/
theorem heckeSum_def :
    heckeSum D ρ hD hΓ₂ q =
      ∑ v, q ∘ₛₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩ := (rfl)

/-- The Hecke sum, evaluated: `heckeSum D ρ q x = ∑ᵥ q (ρ(aᵥ) x)`. -/
theorem heckeSum_apply (x : V) :
    heckeSum D ρ hD hΓ₂ q x =
      ∑ v, q (ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩ x) := by
  simp only [heckeSum_def, LinearMap.sum_apply, LinearMap.comp_apply]

/-- The Hecke sum of the zero map is zero. -/
@[simp]
theorem heckeSum_zero : heckeSum D ρ hD hΓ₂ (0 : V →ₛₗ[σ] W) = 0 := by
  ext x
  simp [heckeSum_apply]

/-- The Hecke sum is additive in the target map. -/
@[simp]
theorem heckeSum_add (q₁ q₂ : V →ₛₗ[σ] W) :
    heckeSum D ρ hD hΓ₂ (q₁ + q₂) = heckeSum D ρ hD hΓ₂ q₁ + heckeSum D ρ hD hΓ₂ q₂ := by
  ext x
  simp [heckeSum_apply, Finset.sum_add_distrib]

variable {q} (hΓ₁ : Γ₁.toSubmonoid ≤ Δ') (hq : ∀ γ (hγ : γ ∈ Γ₁), q ∘ₛₗ ρ ⟨γ, hΓ₁ hγ⟩ = q)

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
    heckeSum D ρ hD hΓ₂ q = ∑ i, q ∘ₛₗ ρ ⟨a i, ha i⟩ := by
  obtain ⟨φ, hbij, hφ⟩ := exists_bijective_rightCosetRep_smul_eq D a hcover hinj
  rw [heckeSum_def]
  exact (Fintype.sum_bijective φ hbij _ _ fun i ↦
    ρ.comp_eq_of_rightCoset_eq hΓ₁ hq (ha i) _ (hφ i)).symm

include hΓ₁ hq in
/-- **The Hecke sum of a `Γ₁`-invariant map is `Γ₂`-invariant.** For `γ ∈ Γ₂`,
`heckeSum D ρ q ∘ ρ(γ) = heckeSum D ρ q`.

This is the invariance needed to descend the sum to the `Γ₂`-coinvariants of `V`. -/
theorem heckeSum_comp_of_mem {γ : G} (hγ : γ ∈ Γ₂) :
    heckeSum D ρ hD hΓ₂ q ∘ₛₗ ρ ⟨γ, hΓ₂ hγ⟩ = heckeSum D ρ hD hΓ₂ q := by
  -- Composing the `v`-th summand with `ρ(γ)` gives the summand at the permuted index.
  have hperm (v : DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) :
      (q ∘ₛₗ ρ ⟨rightCosetRep D v, rightCosetRep_mem D hD hΓ₂ v⟩) ∘ₛₗ ρ ⟨γ, hΓ₂ hγ⟩ =
        q ∘ₛₗ ρ ⟨rightCosetRep D ((⟨γ, hγ⟩ : Γ₂)⁻¹ • v),
          rightCosetRep_mem D hD hΓ₂ _⟩ := by
    have hmem : rightCosetRep D v * γ ∈ Δ' :=
      mul_mem (rightCosetRep_mem D hD hΓ₂ v) (hΓ₂ hγ)
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul]
    refine ρ.comp_eq_of_rightCoset_eq hΓ₁ hq hmem _ ((rightCoset_eq_iff Γ₁).mpr ?_)
    -- `aᵥ γ = δ (γ⁻¹ τᵥ)⁻¹` is a `Γ₁`-multiple of the representative of the class of `γ⁻¹ τᵥ`,
    -- which is the class `γ⁻¹ • v`.
    obtain ⟨γ₁, hγ₁, hsplit⟩ :=
      exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2)
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : G), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹) = (⟨γ, hγ⟩ : Γ₂)⁻¹ • v :=
      MulAction.Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ₂)⁻¹ v
    have hprod : rightCosetRep D v * γ =
        γ₁ * rightCosetRep D ((⟨γ, hγ⟩ : Γ₂)⁻¹ • v) := by
      simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
    simpa [hprod, mul_inv_rev, mul_assoc] using inv_mem hγ₁
  refine LinearMap.ext fun x ↦ ?_
  simp only [heckeSum_def, LinearMap.comp_apply, LinearMap.sum_apply]
  -- `MulAction.toPerm` of `γ⁻¹` is the reindexing bijection.
  exact Fintype.sum_equiv (MulAction.toPerm (⟨γ, hγ⟩ : Γ₂)⁻¹) _ _ fun v ↦ by
    simpa only [MulAction.toPerm_apply, LinearMap.comp_apply] using
      LinearMap.congr_fun (hperm v) x

end HeckeCoset

end
